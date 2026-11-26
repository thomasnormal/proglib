#!/usr/bin/env python3
"""Run the C torture manifest with a wall bound for every entry.

The Lean runner is deliberately deterministic but a CPU-bound reduction
cannot be pre-empted by Lean's cooperative tasks.  This controller therefore
keeps one already-built runner binary (no ``lake`` startup per row), invokes
its ``--only`` mode for each manifest entry, and uses a subprocess wall around
that child.  A wall-clock kill becomes a ``runner-error`` row.  Fuel exhaustion
reported by the child remains a ``timeout`` row.  Malformed or missing output
also becomes ``runner-error``. Rows are emitted in manifest order.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from c_corpus_fetch import ORACLE_TESTS_COMPILER

ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / "extractors" / "c" / "extract.py"
SUBDIR = "gcc/testsuite/gcc.c-torture/execute"
PIN = ROOT / "docs" / "c-torture-pin.json"


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


def _refresh_stale(entry: dict) -> tuple[bool, str]:
    """Regenerate one stale envelope from the pinned external source cache."""
    envelope_name = entry.get("envelope")
    name = entry.get("name")
    if not envelope_name or not name:
        return False, "manifest has no envelope or test name"
    envelope = Path(envelope_name)
    source = envelope.parent.parent / "src" / name
    if not source.is_file():
        return False, "source is unavailable for envelope refresh"
    result = subprocess.run(
        [sys.executable, str(EXTRACTOR), str(source), "--source-name",
         "%s/%s" % (SUBDIR, name), "-o", str(envelope)],
        cwd=ROOT, capture_output=True, text=True, check=False)
    if result.returncode == 0:
        return True, ""
    detail = _compact(result.stderr) or _compact(result.stdout)
    return False, detail or "extractor refused without a diagnostic"


def _canonicalize_envelope(entry: dict, manifest: Path) -> bool:
    """Use the manifest's cache root when a copied manifest has stale paths.

    Manifests are portable receipts, but their envelope field historically
    stored an absolute cache path.  A batch run copied to another approved
    cache therefore skipped the refresh path and handed a dead filename to the
    runner.  The test name and manifest location are the stable identity.
    """
    name = entry.get("name")
    if not name or not entry.get("envelope"):
        return False
    expected = manifest.parent / "env" / (name[:-2] + ".json")
    current = Path(entry["envelope"])
    source = manifest.parent / "src" / name
    # Prefer the manifest-local envelope whenever its source or envelope is
    # present, even if the historical absolute path still exists.  A stale
    # old-cache file must not prevent refresh from the copied manifest's
    # approved source cache.
    if (expected.exists() or source.is_file()) and current != expected:
        entry["envelope"] = str(expected)
        return True
    return False


def _augment_pinned_metadata(tests: list[dict]) -> bool:
    """Restore pinned oracle metadata missing from an older manifest.

    A replay manifest is an external receipt and may predate a metadata-only
    pin update.  The test name is already the manifest's stable identity, so
    the committed pin is the only approved source for filling this field.
    Return whether any entry changed so the runner can receive an augmented
    manifest without mutating the receipt on disk.
    """
    try:
        pinned = dict(json.loads(PIN.read_text()).get("oracle_tests_compiler", {}))
    except (OSError, json.JSONDecodeError):
        pinned = {}
    # The code table is the current source of truth used when a manifest is
    # generated.  Keep old copied manifests replayable even when their pin
    # receipt predates a metadata-only classification.
    pinned.update(ORACLE_TESTS_COMPILER)
    changed = False
    for entry in tests:
        if not isinstance(entry, dict):
            continue
        name = entry.get("name")
        if (isinstance(name, str) and name in pinned and
                not entry.get("oracle_tests_compiler")):
            entry["oracle_tests_compiler"] = pinned[name]
            changed = True
    return changed


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

    canonicalized = any(
        isinstance(entry, dict) and _canonicalize_envelope(entry, manifest)
        for entry in tests)
    augmented = _augment_pinned_metadata(tests)
    runner_manifest = manifest
    temporary_manifest = None
    if canonicalized or augmented:
        temporary_manifest = tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=manifest.parent,
            prefix=".c-torture-batch-", suffix=".json", delete=False)
        json.dump(data, temporary_manifest, indent=1)
        temporary_manifest.write("\n")
        temporary_manifest.close()
        runner_manifest = Path(temporary_manifest.name)

    try:
        for entry in tests:
            if not isinstance(entry, dict):
                print("\t".join(("", "runner-error", "manifest test is not an object")))
                continue
            static = _static_row(entry)
            if static[1] == "not-ingested":
                refreshed, refresh_detail = _refresh_stale(entry)
                if refreshed:
                    static = _static_row(entry)
                elif refresh_detail:
                    static = (static[0], static[1],
                              "%s; refresh failed: %s" % (static[2], refresh_detail))
            if static[0]:
                print("\t".join(static), flush=True)
                continue
            name = str(entry.get("name") or "")
            try:
                proc = subprocess.run(
                    [runner, "--only", name, str(runner_manifest), str(fuel)],
                    capture_output=True,
                    text=True,
                    timeout=timeout,
                    check=False,
                )
            except subprocess.TimeoutExpired:
                print(f"{name}\trunner-error\twall-clock kill after {timeout:g}s", flush=True)
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
    finally:
        if temporary_manifest is not None:
            Path(temporary_manifest.name).unlink(missing_ok=True)
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
            "slow.c\trunner-error\twall-clock kill after 0.1s",
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
            refreshed, refresh_detail = _refresh_stale(stale_entry)
            after = _static_row(stale_entry)
        finally:
            globals()['EXTRACTOR'] = old_extractor
        if (before[1] != 'not-ingested' or not refreshed or refresh_detail or
                after != ('', '', '')):
            print("c_torture_batch --self-test: stale envelope was not refreshed", file=sys.stderr)
            return 1

        copied = root / "copied" / "rev"
        copied_env = copied / "env" / "copied.json"
        copied_env.parent.mkdir(parents=True)
        copied_env.write_text(json.dumps({"schema_version": "c-0.1",
                                           "language": "c"}))
        old_env = root / "old" / "env" / "copied.json"
        old_env.parent.mkdir(parents=True)
        old_env.write_text(json.dumps({"schema_version": "c-0.1",
                                       "language": "c"}))
        copied_entry = {"name": "copied.c", "status": "parsed",
                        "sha256": "missing", "envelope": str(old_env)}
        _canonicalize_envelope(copied_entry, copied / "manifest.json")
        if copied_entry["envelope"] != str(copied_env):
            print("c_torture_batch --self-test: stale absolute envelope path was not relocated",
                  file=sys.stderr)
            return 1

        metadata_entry = {"name": "20230630-2.c"}
        if (not _augment_pinned_metadata([metadata_entry]) or
                metadata_entry.get("oracle_tests_compiler", {}).get("symbol") !=
                "scalar_storage_order"):
            print("c_torture_batch --self-test: pinned oracle metadata was not restored",
                  file=sys.stderr)
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
