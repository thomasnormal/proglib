#!/usr/bin/env python3
"""leanpy v0 — the script-corpus differential mode (docs/backlog.md).

Usage (any cwd; the script re-roots itself at the repo root):

    python3 harness/script_corpus.py [--scripts harness/scripts.json]
                                     [--no-build] [--runner CMD] [--fuel N]

For every corpus row ``{"file": ...}``:

  1. re-extracts the envelope (deterministic; extractors/python/extract.py)
     into the shared leanpy CACHE — never beside the source, which used to
     rewrite tracked envelopes on every run;
  2. runs the file under CPython (the pinned 3.9 oracle, ``default_oracle``)
     capturing stdout + exit code;
  3. runs the relation-derived runner in one batch over the envelopes;
  4. a relation refusal is reported as frontier telemetry, while every
     relation decision is compared with CPython.  A decided mismatch fails.

Completeness telemetry is the point: the summary reports the fraction of
the corpus completing and WHICH construct blocked each refusal.

Python 3.9 compatible.
"""

import argparse
import importlib.machinery
import importlib.util
import json
import os
import re
import subprocess
import tempfile
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _reexec_under_pinned_frontend():
    """RUN THE FRONTEND ON THE PINNED INTERPRETER (2026-08-15 fix).

    The ORACLE here has been pinned since 2026-08-13 (`default_oracle`
    below). The FRONTEND was not: extraction ran under `sys.executable`,
    so `python3 harness/script_corpus.py` parsed the corpus with whatever
    python3 the box has — 3.14 on this laptop — while comparing against a
    3.9 oracle. Same fix, same knobs, as `harness/leanpy_survey.py`:
    `LEANPY_FRONTEND` overrides, `LEANPY_NO_REEXEC=1` disables, and a
    missing pin WARNS LOUDLY and keeps going.
    """
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    want = os.environ.get("LEANPY_FRONTEND") or "python3.9"
    if sys.version_info[:2] == (3, 9) and not os.environ.get("LEANPY_FRONTEND"):
        return
    from shutil import which
    exe = which(want)
    if exe is None:
        print("harness/script_corpus.py: WARNING the pinned frontend %r is not "
              "installed; extracting with %s instead — the model may be shown a "
              "different program than the oracle runs"
              % (want, sys.version.split()[0]), file=sys.stderr)
        return
    if os.path.realpath(exe) == os.path.realpath(sys.executable):
        return
    os.environ["LEANPY_NO_REEXEC"] = "1"
    os.execv(exe, [exe, os.path.abspath(__file__)] + sys.argv[1:])


# Only as a script: an importer's argv is not ours to re-run.
if __name__ == "__main__":
    _reexec_under_pinned_frontend()

# tools/leanpy owns the ONE extraction path (cache-keyed by source,
# extractor and frontend family). Using it here is not a tidy-up: this
# harness used to run the extractor WITHOUT `--out`, which writes the
# envelope next to the source — so a routine corpus run rewrote 44 tracked
# `harness/scripts/*.json` files in place, under whatever interpreter
# launched it. Measured 2026-08-15: a full run left them all modified with
# nothing changed but `"version": "3.9.25"` -> `"3.14.5"`.
_path = os.path.join(REPO_ROOT, "tools", "leanpy")
_spec = importlib.util.spec_from_loader(
    "leanpy", importlib.machinery.SourceFileLoader("leanpy", _path))
leanpy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(leanpy)


TRACEBACK_CLASS = re.compile(r"^(?:[A-Za-z_][\w.]*\.)?([A-Za-z_]\w*)(?::.*)?$")


def exc_class(stderr):
    """The exception CLASS a died run reports, read off the last traceback
    line (CPython) or off the runner's own stderr (the Lean side prints the
    class name alone). CPython maps EVERY uncaught exception to exit 1, so
    without this the comparison could not tell two exceptions apart."""
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if not line:
            continue
        m = TRACEBACK_CLASS.match(line)
        return m.group(1) if m else None
    return None


def exc_line(stderr):
    """The last non-empty stderr line: CPython's `ClassName: message`, or
    the runner's own class(+message) line."""
    for line in reversed((stderr or "").splitlines()):
        line = line.strip()
        if line:
            return line
    return None


def default_oracle():
    """The PINNED reference interpreter (2026-08-13 fix). This corpus ran
    against `sys.executable` — whatever Python happened to launch the
    harness, which on this machine is 3.14 — while the model's tier is
    specified against CPython 3.9 (docs/backlog.md) and
    `harness/leanpy_survey.py` has always pinned it. Every "MATCH" was
    therefore measured against the wrong reference, and a real 3.9
    divergence or a fake 3.14 one could have appeared at any time; the
    exception-MESSAGE comparison added the same day is what made it
    visible (3.13+ appends `Did you mean: …?` to a NameError). The oracle
    is printed with every run for the same reason the survey prints it."""
    # AUDIT docs/quality-audit-2026-08-23.md §python: this fell back
    # python3.9 -> python3 -> sys.executable SILENTLY, which is the exact trap
    # the docstring above describes — a corpus comparing against 3.14 while
    # claiming the 3.9 pin, with every MATCH measured against the wrong
    # reference. The fallbacks stay (a box without the pin should still be
    # able to run this), but each degradation now SAYS so, in the same voice
    # the re-exec warning uses.
    for cand in ("python3.9", "python3"):
        try:
            if subprocess.run([cand, "-c", ""], capture_output=True).returncode == 0:
                if cand != "python3.9":
                    print("harness/script_corpus.py: WARNING the pinned oracle "
                          "'python3.9' is not installed; oracling against %r "
                          "instead — version drift will read as model "
                          "divergence" % cand, file=sys.stderr)
                return cand
        except OSError:
            continue
    print("harness/script_corpus.py: WARNING neither 'python3.9' nor 'python3' "
          "is runnable; oracling against %s (%s) — this is NOT the pinned "
          "reference" % (sys.executable, sys.version.split()[0]),
          file=sys.stderr)
    return sys.executable


ORACLE = os.environ.get("LEANPY_CPYTHON") or default_oracle()


def run_cpython(path):
    proc = subprocess.run(
        [ORACLE, path], cwd=REPO_ROOT, capture_output=True, text=True
    )
    return proc.stdout, proc.returncode, proc.stderr


def run_relation_batch(runner_cmd, jobs, fuel):
    """Run the relation-derived column once for the whole corpus."""
    fd, jobs_path = tempfile.mkstemp(prefix=".machine-script-jobs-", suffix=".jsonl")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            for path in jobs:
                stream.write(json.dumps({"path": path}) + "\n")
        command = list(runner_cmd) + ["--relation-script-batch", jobs_path]
        if fuel is not None:
            command += ["--fuel", str(fuel)]
        proc = subprocess.run(command, cwd=REPO_ROOT,
                              capture_output=True, text=True)
        results = []
        for line in proc.stdout.splitlines():
            if line.startswith("{"):
                result = json.loads(line)
                result["stdout_text"] = "".join(
                    chunk + "\n" for chunk in result.get("stdout", []))
                results.append(result)
        while len(results) < len(jobs):
            results.append({"status": "runner-error", "exit": 1})
        return results
    finally:
        os.unlink(jobs_path)


def main(argv=None):
    parser = argparse.ArgumentParser(prog="script_corpus.py")
    parser.add_argument("--scripts", default=os.path.join("harness", "scripts.json"))
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--runner", default="lake exe leanmodels-run")
    parser.add_argument("--fuel", type=int, default=None)
    opts = parser.parse_args(argv)

    os.chdir(REPO_ROOT)
    runner_cmd = opts.runner.split()

    # THE AMENDMENT 14 CONTRACT (tools/triad.sh 4d32526): the TENURE builds the
    # runner and exports LS_RUNNER_PREBUILT=1. A gate must never build the tree
    # — it defeats --build-target narrowing and surfaces an unrelated build
    # failure as a GATE failure, attributing the number to the wrong thing
    # (§5.4a). Unset, build ONLY the runner.
    if not opts.no_build and not os.environ.get("LS_RUNNER_PREBUILT"):
        if subprocess.run(["lake", "build", "leanmodels-run"], cwd=REPO_ROOT).returncode != 0:
            print("error: `lake build` failed", file=sys.stderr)
            return 2

    cache = leanpy.default_cache()
    os.makedirs(cache, exist_ok=True)

    with open(opts.scripts, "r", encoding="utf-8") as f:
        rows = json.load(f)

    relation_jobs = []
    relation_sources = []
    for row in rows:
        envelope = leanpy.envelope_for(row["file"], cache)
        if envelope is not None:
            relation_sources.append(row["file"])
            relation_jobs.append(envelope)
    relation_results = run_relation_batch(runner_cmd, relation_jobs, opts.fuel)
    relation_by_source = dict(zip(relation_sources, relation_results))

    failures = 0
    completed = 0
    relation_matched = relation_refused = relation_diverged = 0
    for row in rows:
        src = row["file"]
        json_path = leanpy.envelope_for(src, cache)
        if json_path is None:
            print("%-42s ERROR (extractor refused; see stderr above)" % src)
            failures += 1
            continue
        cout, ccode, cerr = run_cpython(src)
        relation = relation_by_source.get(src, {"status": "runner-error", "exit": 1})
        if relation.get("status") == "unsupported":
            relation_refused += 1
            print("%-42s REFUSED (%s)" % (src, relation.get("msg", "relation frontier")))
            continue

        relation_same = (
            relation.get("status") == ("ok" if ccode == 0 else "exn") and
            relation.get("exit") == ccode and
            relation.get("stdout_text", "") == cout and
            (ccode == 0 or relation.get("exn") == exc_class(cerr)))
        if relation_same:
            relation_matched += 1
            completed += 1
            print("%-42s MATCH   relation (exit %d, %d stdout bytes)"
                  % (src, ccode, len(cout)))
        else:
            relation_diverged += 1
            print("%-42s DIVERGE relation" % src)
            print("  cpython: exit %d, stdout %r" % (ccode, cout))
            print("  relation: %s" % json.dumps(relation, sort_keys=True))
            failures += 1

    total = len(rows)
    print("-" * 72)
    ver = subprocess.run([ORACLE, "-V"], capture_output=True, text=True)
    print("oracle: %s" % ((ver.stdout or ver.stderr).strip(),))
    print("interpreter: LeanModels/Python/Machine/Relation.lean")
    print("%d scripts: %d failed, %d completed-and-matched, %d relation-refused"
          % (total, failures, completed, relation_refused))
    print("relation: matched %d, refused %d, diverging %d" %
          (relation_matched, relation_refused, relation_diverged))
    relation_decided = relation_matched + relation_diverged
    print("MACHINE-REL scripts %d/%d (diverge %d)" %
          (relation_decided, total, relation_diverged))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
