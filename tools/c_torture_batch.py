#!/usr/bin/env python3
"""Run the C torture manifest with a wall bound for every entry.

The Lean runner is deliberately deterministic but a CPU-bound reduction
cannot be pre-empted by Lean's cooperative tasks.  This controller therefore
keeps one already-built runner binary (no ``lake`` startup per row), invokes
its ``--only`` mode for each manifest entry, and uses a subprocess wall around
that child.  A killed child becomes a ``timeout`` row; malformed or missing
output becomes ``runner-error``.  Rows are emitted in manifest order.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / "extractors" / "c" / "extract.py"
SUBDIR = "gcc/testsuite/gcc.c-torture/execute"


def _why(entry: dict) -> str:
    return _compact(str(entry.get("why") or ""))


def _compact(detail: str) -> str:
    """Keep the one-line batch protocol even when clang emits a diagnostic."""
    return " ".join(detail.split())[:2000]


def _static_row(entry: dict) -> tuple[str, str, str]:
    status = entry.get("status", "")
    if status == "absent":
        return entry.get("name", ""), "not-fetched", ""
    if status == "rejected":
        return entry.get("name", ""), "not-parsed", _why(entry)
    if not entry.get("envelope"):
        return entry.get("name", ""), "runner-error", "manifest says parsed but names no envelope"
    envelope = Path(entry["envelope"])
    if envelope.is_file():
        try:
            data = json.loads(envelope.read_text())
        except (OSError, json.JSONDecodeError):
            return entry.get("name", ""), "not-ingested", "malformed parser envelope"
        if data.get("schema_version") != "c-0.1":
            return entry.get("name", ""), "not-ingested", "stale envelope schema"
        if data.get("language") != "c":
            return entry.get("name", ""), "not-ingested", "stale envelope language"
        if data.get("source_sha256") != entry.get("sha256"):
            return entry.get("name", ""), "not-ingested", "stale envelope source hash"
        expected = hashlib.sha256(EXTRACTOR.read_bytes()).hexdigest()
        if data.get("extractor_sha256") != expected:
            return entry.get("name", ""), "not-ingested", "stale envelope extractor hash"
    return "", "", ""


def _refresh_stale(entry: dict) -> bool:
    """Regenerate one stale envelope from the pinned external source cache."""
    envelope_name = entry.get("envelope")
    name = entry.get("name")
    if not envelope_name or not name:
        return False
    envelope = Path(envelope_name)
    source = envelope.parent.parent / "src" / name
    if not source.is_file():
        return False
    result = subprocess.run(
        [sys.executable, str(EXTRACTOR), str(source), "--source-name",
         "%s/%s" % (SUBDIR, name), "-o", str(envelope)],
        cwd=ROOT, capture_output=True, text=True, check=False)
    return result.returncode == 0


def _parse_child(name: str, stdout: str) -> tuple[str, str, str] | None:
    for line in stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) == 3 and parts[0] == name:
            return parts[0], parts[1], parts[2]
    return None


def run(manifest: Path, runner: str, fuel: int, timeout: float) -> int:
    try:
        data = json.loads(manifest.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"c_torture_batch: cannot read manifest: {exc}", file=sys.stderr)
        return 2

    tests = data.get("tests")
    if not isinstance(tests, list):
        print("c_torture_batch: manifest has no tests array", file=sys.stderr)
        return 2

    for entry in tests:
        if not isinstance(entry, dict):
            print("\t".join(("", "runner-error", "manifest test is not an object")))
            continue
        static = _static_row(entry)
        if static[1] == "not-ingested" and _refresh_stale(entry):
            static = _static_row(entry)
        if static[0]:
            print("\t".join(static), flush=True)
            continue
        name = str(entry.get("name") or "")
        try:
            proc = subprocess.run(
                [runner, "--only", name, str(manifest), str(fuel)],
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            print(f"{name}\ttimeout\tper-file wall timeout ({timeout:g}s)", flush=True)
            continue
        except OSError as exc:
            print(f"{name}\trunner-error\t{_compact(str(exc))}", flush=True)
            continue

        row = _parse_child(name, proc.stdout)
        if row is None:
            detail = _compact(proc.stderr) or "runner produced no row"
            print(f"{name}\trunner-error\t{detail}", flush=True)
        else:
            print("\t".join(row), flush=True)
    return 0


def self_test() -> int:
    import tempfile

    with tempfile.TemporaryDirectory(prefix="c-torture-batch-") as tmp:
        root = Path(tmp)
        manifest = root / "manifest.json"
        fake = root / "runner.py"
        fake.write_text(
            "#!/usr/bin/env python3\n"
            "import sys, time\n"
            "name = sys.argv[2]\n"
            "if name == 'slow.c': time.sleep(2)\n"
            "elif name == 'bad.c': print('not-a-row')\n"
            "else: print(name + '\\tpassed\\tok')\n"
        )
        fake.chmod(0o755)
        manifest.write_text(json.dumps({"tests": [
            {"name": "ok.c", "status": "parsed", "envelope": "ok"},
            {"name": "slow.c", "status": "parsed", "envelope": "slow"},
            {"name": "bad.c", "status": "parsed", "envelope": "bad"},
            {"name": "reject.c", "status": "rejected", "why": "clang rejected"},
        ]}))
        proc = subprocess.run(
            [sys.executable, __file__, str(manifest), "--runner", str(fake),
             "--timeout", "0.1"],
            capture_output=True, text=True, check=False,
        )
        expected = [
            "ok.c\tpassed\tok",
            "slow.c\ttimeout\tper-file wall timeout (0.1s)",
            "bad.c\trunner-error\trunner produced no row",
            "reject.c\tnot-parsed\tclang rejected",
        ]
        if proc.returncode or proc.stdout.splitlines() != expected:
            print("c_torture_batch --self-test: failed", file=sys.stderr)
            print(proc.stdout, file=sys.stderr)
            print(proc.stderr, file=sys.stderr)
            return 1
        stale = root / "stale.json"
        stale.write_text(json.dumps({
            "schema_version": "c-0.1",
            "source_sha256": "source",
            "extractor_sha256": "extractor",
        }))
        status = _static_row({
            "name": "stale.c", "status": "parsed", "sha256": "source",
            "envelope": str(stale),
        })
        if status != ("stale.c", "not-ingested", "stale envelope language"):
            print("c_torture_batch --self-test: missing language provenance was accepted",
                  file=sys.stderr)
            return 1

        # A stale parser stamp is regenerated from the cache's source path
        # before the child runner is allowed to see the envelope. Use a tiny
        # fake extractor so this instrument test remains independent of clang.
        cache = root / "cache" / "rev"
        source = cache / "src" / "refresh.c"
        envelope = cache / "env" / "refresh.json"
        source.parent.mkdir(parents=True)
        envelope.parent.mkdir(parents=True)
        source.write_text("int main(void) { return 0; }\n")
        fake_extractor = root / "fake_extract.py"
        fake_extractor.write_text(
            "import hashlib, json, pathlib, sys\n"
            "src = pathlib.Path(sys.argv[1])\n"
            "out = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])\n"
            "payload = {'schema_version':'c-0.1','language':'c',\n"
            " 'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),\n"
            " 'extractor_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}\n"
            "out.write_text(json.dumps(payload))\n")
        fake_extractor.chmod(0o755)
        envelope.write_text(json.dumps({'schema_version': 'c-0.1',
                                        'language': 'c',
                                        'source_sha256': 'stale',
                                        'extractor_sha256': 'stale'}))
        old_extractor = globals()['EXTRACTOR']
        globals()['EXTRACTOR'] = fake_extractor
        try:
            stale_entry = {'name': 'refresh.c', 'status': 'parsed',
                            'sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'envelope': str(envelope)}
            before = _static_row(stale_entry)
            refreshed = _refresh_stale(stale_entry)
            after = _static_row(stale_entry)
        finally:
            globals()['EXTRACTOR'] = old_extractor
        if before[1] != 'not-ingested' or not refreshed or after != ('', '', ''):
            print("c_torture_batch --self-test: stale envelope was not refreshed", file=sys.stderr)
            return 1
    print("c_torture_batch --self-test: ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", nargs="?")
    ap.add_argument("fuel", nargs="?", type=int, default=64)
    ap.add_argument("--runner", default=".lake/build/bin/c-torture-run")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()
    if not args.manifest:
        ap.error("manifest is required unless --self-test is used")
    if args.fuel < 0 or args.timeout <= 0:
        ap.error("fuel must be nonnegative and timeout must be positive")
    return run(Path(args.manifest), args.runner, args.fuel, args.timeout)


if __name__ == "__main__":
    raise SystemExit(main())
