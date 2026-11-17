#!/usr/bin/env python3
"""Measure MIR reachability and one Miri execution for the Rust stage-0 gate.

The extractor is the approved rustc_public driver.  Static sizes come from its
JSON envelope; dynamic counts come from Miri's structured interpreter trace
(the ``rustc_const_eval::interpret`` logger), sliced at the extracted entry
body.  No MIR text dump and no Rust source parser is used here.

The default run measures the checked-in corpus and writes one normalized JSON
report.  It runs each row under both Stacked Borrows and Tree Borrows.  The
Stacked Borrows trace is the canonical count; the Tree Borrows trace is kept
as a cross-check.  Construct-size rows only extract generated source and do
not run it, so their static MIR sizes are independent of runtime startup.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable


TOOLCHAIN = "nightly-2026-11-16"
TOOLCHAIN_TRIPLE = "nightly-2026-11-16-x86_64-unknown-linux-gnu"
RUSTC_VERSION = "1.102.0-nightly (5f4effd57 2026-11-13)"
CARGO_VERSION = "1.102.0-nightly (ede6cefea 2026-11-11)"
MIRI_VERSION = "0.1.0 (5f4effd579 2026-11-13)"
MIRI_FLAGS = (
    "-Zmiri-deterministic-concurrency",
    "-Zmiri-deterministic-floats",
    "-Zmiri-seed=0",
    "-Zmiri-num-cpus=1",
    "-Zmiri-isolation-error=abort",
)
TRACE_LOGGER = "rustc_const_eval::interpret=info"
STD_ROOTS = {
    "std",
    "core",
    "alloc",
    "compiler_builtins",
    "panic_unwind",
    "unwind",
}


class MeasurementError(RuntimeError):
    """A setup, extraction, trace, or oracle failure."""


@dataclass
class Invocation:
    token: int
    indent: int
    frame_name: str
    instance_id: str | None
    body: dict[str, Any] | None
    blocks: set[int] = field(default_factory=set)
    block_visits: int = 0
    statements: int = 0
    terminators: int = 0
    statement_sites: set[tuple[int, int]] = field(default_factory=set)
    statement_kinds: Counter[str] = field(default_factory=Counter)
    terminator_kinds: Counter[str] = field(default_factory=Counter)
    current_block: int | None = None
    remaining_statements: int | None = None
    next_statement: int = 0
    terminator_seen: bool = False


@dataclass
class TraceResult:
    root_found: bool
    invocations: list[Invocation]
    unmapped_frames: Counter[str]
    runtime_instance_ids: set[str]
    errors: list[str]


class Runner:
    def __init__(self, args: argparse.Namespace):
        self.repo_root = Path(__file__).resolve().parents[2]
        self.manifest_path = Path(args.manifest).resolve()
        self.manifest = json.loads(self.manifest_path.read_text(encoding="utf-8"))
        if self.manifest.get("schema") != "lean-surfaces.rust.mir-measurement-manifest.v0":
            raise MeasurementError("unsupported measurement manifest schema")
        self._check_manifest()
        self.work_root = Path(args.work_root or self._default_work_root()).resolve()
        self.work_root.mkdir(parents=True, exist_ok=True)
        self.extractor = Path(
            args.extractor
            or os.environ.get("RUST_MIR_EXTRACTOR", "")
            or self.work_root.parent / "rust-mir-extract"
        ).expanduser().resolve()
        self.timeout = args.timeout
        self.keep_work = args.keep_work
        self.models = ("stacked_borrows", "tree_borrows")
        self.toolchain_info = self._toolchain_info()
        self.sysroot = self._sysroot()
        if not self.extractor.is_file():
            raise MeasurementError(f"extractor does not exist: {self.extractor}")
        self._counter = 0

    def _check_manifest(self) -> None:
        programs = self.manifest.get("programs")
        if not isinstance(programs, list) or not programs:
            raise MeasurementError("manifest has no programs")
        ids = [row.get("id") for row in programs]
        if any(not isinstance(value, str) or not value for value in ids):
            raise MeasurementError("every manifest row needs a non-empty id")
        if len(set(ids)) != len(ids):
            raise MeasurementError("manifest ids are not unique")

    def _default_work_root(self) -> Path:
        lane_root = os.environ.get("RUST_LANE_ROOT")
        if not lane_root:
            raise MeasurementError("set RUST_LANE_ROOT or pass --work-root")
        return Path(lane_root) / "mir-measurement-work"

    @staticmethod
    def _required_environment() -> None:
        missing = [name for name in ("RUSTUP_HOME", "CARGO_HOME", "TMPDIR")
                   if not os.environ.get(name)]
        if missing:
            raise MeasurementError("missing lane-local environment: " + ", ".join(missing))

    @staticmethod
    def _capture(command: list[str], env: dict[str, str], cwd: Path | None = None,
                 timeout: float | None = None) -> tuple[int | None, str, str]:
        try:
            completed = subprocess.run(
                command,
                cwd=str(cwd) if cwd else None,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as error:
            stdout = error.stdout or ""
            stderr = error.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", "replace")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", "replace")
            return None, stdout, stderr
        return completed.returncode, completed.stdout, completed.stderr

    def _toolchain_info(self) -> dict[str, Any]:
        self._required_environment()
        rustup = shutil.which("rustup")
        if rustup is None:
            raise MeasurementError("rustup is not on PATH")
        env = os.environ.copy()
        rustc_status, rustc_out, rustc_err = self._capture(
            [rustup, "run", TOOLCHAIN, "rustc", "--version", "--verbose"], env, timeout=30)
        cargo_status, cargo_out, cargo_err = self._capture(
            [rustup, "run", TOOLCHAIN, "cargo", "--version"], env, timeout=30)
        miri_status, miri_out, miri_err = self._capture(
            [rustup, "run", TOOLCHAIN, "cargo", "miri", "--version"], env, timeout=30)
        if rustc_status != 0:
            raise MeasurementError("rustc version failed: " + rustc_err.strip())
        if cargo_status != 0:
            raise MeasurementError("cargo version failed: " + cargo_err.strip())
        if miri_status != 0:
            raise MeasurementError("miri version failed: " + miri_err.strip())
        if not rustc_out.startswith("rustc " + RUSTC_VERSION + "\n"):
            raise MeasurementError("unexpected rustc version: " + rustc_out.splitlines()[0])
        if not cargo_out.startswith("cargo " + CARGO_VERSION + "\n"):
            raise MeasurementError("unexpected cargo version: " + cargo_out.strip())
        if not miri_out.startswith("miri " + MIRI_VERSION + "\n"):
            raise MeasurementError("unexpected Miri version: " + miri_out.strip())
        return {
            "channel": TOOLCHAIN_TRIPLE,
            "rustc": rustc_out.strip(),
            "cargo": cargo_out.strip(),
            "miri": miri_out.strip(),
            "pinned_versions": {
                "rustc": RUSTC_VERSION,
                "cargo": CARGO_VERSION,
                "miri": MIRI_VERSION,
            },
        }

    def _sysroot(self) -> Path:
        configured = os.environ.get("MIRI_SYSROOT")
        if configured:
            candidate = Path(configured).expanduser()
        else:
            lane_root = os.environ.get("RUST_LANE_ROOT")
            if not lane_root:
                raise MeasurementError("set MIRI_SYSROOT or RUST_LANE_ROOT")
            candidate = Path(lane_root) / "miri-cache" / TOOLCHAIN_TRIPLE
        if not (candidate / "lib" / "rustlib").is_dir():
            raise MeasurementError("not a generated Miri sysroot: " + str(candidate))
        return candidate.resolve()

    def _env(self, target_dir: Path, model: str, trace: bool) -> dict[str, str]:
        env = os.environ.copy()
        env["MIRI_SYSROOT"] = str(self.sysroot)
        flags = list(MIRI_FLAGS)
        if model == "tree_borrows":
            flags.append("-Zmiri-tree-borrows")
        env["MIRIFLAGS"] = " ".join(flags)
        env["CARGO_TARGET_DIR"] = str(target_dir)
        env["CARGO_TERM_COLOR"] = "never"
        env["CARGO_INCREMENTAL"] = "0"
        env["RUST_BACKTRACE"] = "0"
        if trace:
            env["RUSTC_LOG"] = TRACE_LOGGER
        else:
            env.pop("RUSTC_LOG", None)
        toolchain_lib = Path(os.environ["RUSTUP_HOME"]) / "toolchains" / TOOLCHAIN_TRIPLE / "lib"
        old_ld = env.get("LD_LIBRARY_PATH")
        env["LD_LIBRARY_PATH"] = str(toolchain_lib) + ((":" + old_ld) if old_ld else "")
        return env

    @staticmethod
    def _partition(name: str, crate_name: str) -> str:
        if name == crate_name or name.startswith(crate_name + "::"):
            return "user"
        if name.split("::", 1)[0] in STD_ROOTS:
            return "std"
        return "other"

    @staticmethod
    def _kind(value: Any) -> str:
        if isinstance(value, str):
            return value
        if isinstance(value, dict) and len(value) == 1:
            return str(next(iter(value)))
        return "<unknown>"

    def _source_path(self, row: dict[str, Any]) -> Path:
        raw = Path(row["path"])
        candidate = (self.manifest_path.parent / raw).resolve()
        try:
            candidate.relative_to(self.manifest_path.parent.resolve())
        except ValueError as error:
            raise MeasurementError(f"manifest path escapes corpus: {raw}") from error
        if not candidate.is_file():
            raise MeasurementError("missing measurement source: " + str(raw))
        return candidate

    def _next_workspace(self, row_id: str) -> Path:
        self._counter += 1
        name = re.sub(r"[^A-Za-z0-9_]+", "_", row_id).strip("_")
        path = self.work_root / f"{self._counter:03d}_{name}"
        path.mkdir(parents=True, exist_ok=False)
        return path

    def _extract(self, source: Path, crate_name: str, edition: str,
                 workspace: Path) -> dict[str, Any]:
        envelope = workspace / "mir.json"
        binary = workspace / "program"
        env = self._env(workspace / "extract-target", "stacked_borrows", trace=False)
        command = [
            str(self.extractor),
            "--sysroot", str(self.sysroot),
            "--crate-name", crate_name,
            "--edition", edition,
            str(source),
            "--crate-type=bin",
            "-o", str(binary),
            "--rust-mir-output", str(envelope),
        ]
        status, stdout, stderr = self._capture(command, env, timeout=self.timeout)
        if status != 0:
            raise MeasurementError(
                f"extractor failed for {source.name} (status {status}):\n{stderr[-4000:]}"
            )
        try:
            report = json.loads(envelope.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise MeasurementError(f"extractor did not write JSON for {source.name}") from error
        if report.get("schema") != "lean-surfaces.rust.mir.v0":
            raise MeasurementError(f"unexpected extractor schema for {source.name}")
        return report

    def _static(self, report: dict[str, Any], crate_name: str) -> dict[str, Any]:
        instances = {item["id"]: item for item in report.get("instances", [])}
        bodies: dict[str, dict[str, Any]] = {
            item["instance"]: item["body"] for item in report.get("bodies", [])
        }
        if report.get("entry") not in bodies:
            raise MeasurementError("entry body is absent from extractor envelope")
        by_partition: dict[str, dict[str, int]] = {
            part: {"bodies": 0, "blocks": 0, "statements": 0, "terminators": 0}
            for part in ("user", "std", "other")
        }
        node_counts: Counter[str] = Counter()
        body_rows = []
        for instance_id, body in bodies.items():
            meta = instances.get(instance_id)
            if not meta:
                raise MeasurementError("body has no instance metadata")
            name = str(meta.get("name", instance_id))
            part = self._partition(name, crate_name)
            blocks = body.get("blocks", [])
            statement_count = sum(len(block.get("statements", [])) for block in blocks)
            terminator_count = len(blocks)
            by_partition[part]["bodies"] += 1
            by_partition[part]["blocks"] += len(blocks)
            by_partition[part]["statements"] += statement_count
            by_partition[part]["terminators"] += terminator_count
            for block in blocks:
                for statement in block.get("statements", []):
                    node_counts[self._kind(statement.get("kind"))] += 1
                node_counts["terminator." + self._kind(block.get("terminator", {}).get("kind"))] += 1
            body_rows.append({
                "id": instance_id,
                "name": name,
                "partition": part,
                "blocks": len(blocks),
                "statements": statement_count,
                "terminators": terminator_count,
            })
        body_rows.sort(key=lambda item: item["name"])
        return {
            "entry": report["entry"],
            "entry_name": instances[report["entry"]]["name"],
            "reachable": by_partition,
            "node_counts": dict(sorted(node_counts.items())),
            "bodies": body_rows,
            "instances": instances,
            "body_map": bodies,
        }

    @staticmethod
    def _frame_base(name: str) -> str:
        return name.split(" - shim", 1)[0].strip()

    def _trace_map(self, report: dict[str, Any], static: dict[str, Any], frame: str) -> str | None:
        instances: dict[str, dict[str, Any]] = static["instances"]
        body_map: dict[str, dict[str, Any]] = static["body_map"]
        base = self._frame_base(frame)
        exact = {item.get("name"): item_id for item_id, item in instances.items()}
        for candidate in (frame, base):
            if candidate in exact:
                return exact[candidate]
        body_names = [(item.get("name", ""), item_id) for item_id, item in instances.items()
                      if item_id in body_map]
        matches = [(name, item_id) for name, item_id in body_names
                   if name == base or name.endswith("::" + base)]
        if len(matches) == 1:
            return matches[0][1]
        return None

    @staticmethod
    def _finish_invocation(invocation: Invocation, errors: list[str]) -> None:
        if invocation.body is None:
            return
        if invocation.current_block is not None:
            if invocation.remaining_statements != 0:
                errors.append(
                    f"{invocation.frame_name}: block bb{invocation.current_block} ended with "
                    f"{invocation.remaining_statements} unlogged statement(s)"
                )
            if not invocation.terminator_seen:
                errors.append(f"{invocation.frame_name}: block bb{invocation.current_block} has no logged terminator")

    def _trace(self, trace_text: str, report: dict[str, Any], static: dict[str, Any]) -> TraceResult:
        frame_re = re.compile(r"^( *)rustc_const_eval::interpret::stack::frame frame=(.*)$")
        step_re = re.compile(r"^( *)INFO rustc_const_eval::interpret::step (.*)$")
        pop_re = re.compile(r"^( *)INFO rustc_const_eval::interpret::call popping stack frame")
        root_id = static["entry"]
        stack: list[Invocation] = []
        invocations: list[Invocation] = []
        unmapped = Counter()
        runtime_instance_ids: set[str] = set()
        errors: list[str] = []
        root_token: int | None = None
        next_token = 0

        def active() -> bool:
            return root_token is not None and any(item.token == root_token for item in stack)

        def finish_popped(item: Invocation) -> None:
            self._finish_invocation(item, errors)

        for raw_line in trace_text.splitlines():
            frame_match = frame_re.match(raw_line)
            if frame_match:
                indent = len(frame_match.group(1))
                frame_name = frame_match.group(2)
                while stack and stack[-1].indent >= indent:
                    finish_popped(stack.pop())
                instance_id = self._trace_map(report, static, frame_name)
                body = static["body_map"].get(instance_id) if instance_id else None
                next_token += 1
                invocation = Invocation(next_token, indent, frame_name, instance_id, body)
                stack.append(invocation)
                if instance_id:
                    runtime_instance_ids.add(instance_id)
                if instance_id == root_id and root_token is None:
                    root_token = invocation.token
                if active():
                    if body is not None:
                        invocations.append(invocation)
                    elif instance_id is None:
                        unmapped[frame_name] += 1
                continue
            if pop_re.match(raw_line):
                if stack:
                    finish_popped(stack.pop())
                if root_token is not None and not any(item.token == root_token for item in stack):
                    root_token = None
                continue
            step_match = step_re.match(raw_line)
            if not step_match or not stack or not active():
                continue
            invocation = stack[-1]
            text = step_match.group(2)
            if invocation.body is None:
                continue
            if text.startswith("// executing bb"):
                match = re.search(r"bb(\d+)", text)
                if not match:
                    errors.append(f"{invocation.frame_name}: malformed block marker")
                    continue
                block_index = int(match.group(1))
                blocks = invocation.body.get("blocks", [])
                if block_index >= len(blocks):
                    errors.append(f"{invocation.frame_name}: trace mentions missing bb{block_index}")
                    invocation.current_block = None
                    continue
                if invocation.current_block is not None:
                    self._finish_invocation(invocation, errors)
                block = blocks[block_index]
                invocation.current_block = block_index
                invocation.remaining_statements = len(block.get("statements", []))
                invocation.next_statement = 0
                invocation.terminator_seen = False
                invocation.blocks.add(block_index)
                invocation.block_visits += 1
                continue
            if invocation.current_block is None:
                # Miri can enter an extracted body once while checking a
                # function pointer or a constant before its runtime call.
                # That path has no block marker in the logger stream.  It is
                # outside the executable trace we count; the later runtime
                # invocation starts with an explicit `executing bb` marker.
                continue
            # This logger marker denotes a const-evaluation accounting event,
            # not a MIR statement or terminator.  It has no corresponding
            # node in the rustc_public body.
            if text == "ConstEvalCounter":
                continue
            block = invocation.body["blocks"][invocation.current_block]
            if invocation.remaining_statements and invocation.remaining_statements > 0:
                index = invocation.next_statement
                statements = block.get("statements", [])
                if index >= len(statements):
                    errors.append(f"{invocation.frame_name}: statement index overflow")
                else:
                    invocation.statement_sites.add((invocation.current_block, index))
                    invocation.statement_kinds[self._kind(statements[index].get("kind"))] += 1
                invocation.next_statement += 1
                invocation.remaining_statements -= 1
                invocation.statements += 1
            else:
                if invocation.terminator_seen:
                    errors.append(f"{invocation.frame_name}: two terminator steps in bb{invocation.current_block}")
                invocation.terminator_seen = True
                invocation.terminators += 1
                invocation.terminator_kinds[self._kind(block.get("terminator", {}).get("kind"))] += 1

        while stack:
            finish_popped(stack.pop())
        if root_token is None and not invocations:
            errors.append("entry body was not found in the Miri trace")
        return TraceResult(bool(invocations), invocations, unmapped, runtime_instance_ids, errors)

    @staticmethod
    def _partition_counts(invocations: Iterable[Invocation], static: dict[str, Any],
                          crate_name: str) -> dict[str, dict[str, int]]:
        result = {
            part: {"bodies": 0, "body_invocations": 0, "blocks": 0,
                   "block_visits": 0, "statements": 0, "statement_sites": 0,
                   "terminators": 0}
            for part in ("user", "std", "other")
        }
        grouped: dict[str, list[Invocation]] = defaultdict(list)
        for invocation in invocations:
            if invocation.instance_id:
                grouped[invocation.instance_id].append(invocation)
        for instance_id, rows in grouped.items():
            name = static["instances"][instance_id].get("name", instance_id)
            part = Runner._partition(name, crate_name)
            result[part]["bodies"] += 1
            result[part]["body_invocations"] += len(rows)
            result[part]["blocks"] += len(set().union(*(row.blocks for row in rows)))
            result[part]["block_visits"] += sum(row.block_visits for row in rows)
            result[part]["statements"] += sum(row.statements for row in rows)
            result[part]["statement_sites"] += len(set().union(*(row.statement_sites for row in rows)))
            result[part]["terminators"] += sum(row.terminators for row in rows)
        return result

    def _dynamic(self, trace: TraceResult, static: dict[str, Any], crate_name: str) -> dict[str, Any]:
        invocations = trace.invocations
        statement_kinds: Counter[str] = Counter()
        terminator_kinds: Counter[str] = Counter()
        blocks_by_body: dict[str, set[int]] = defaultdict(set)
        for invocation in invocations:
            if invocation.instance_id is not None:
                blocks_by_body[invocation.instance_id].update(invocation.blocks)
            statement_kinds.update(invocation.statement_kinds)
            terminator_kinds.update(invocation.terminator_kinds)
        executed_bodies = sorted(blocks_by_body)
        return {
            "executed": {
                "bodies": len(executed_bodies),
                "body_invocations": len(invocations),
                "blocks": sum(len(value) for value in blocks_by_body.values()),
                "block_visits": sum(item.block_visits for item in invocations),
                "statements": sum(item.statements for item in invocations),
                "statement_sites": len({
                    (item.instance_id, site)
                    for item in invocations if item.instance_id
                    for site in item.statement_sites
                }),
                "terminators": sum(item.terminators for item in invocations),
            },
            "by_partition": self._partition_counts(invocations, static, crate_name),
            "node_counts": {
                **{key: value for key, value in sorted(statement_kinds.items())},
                **{"terminator." + key: value for key, value in sorted(terminator_kinds.items())},
            },
            "executed_body_ids": executed_bodies,
            "executed_blocks_by_body": {
                key: sorted(value) for key, value in sorted(blocks_by_body.items())
            },
            "trace_unmapped_frames": dict(sorted(trace.unmapped_frames.items())),
            "trace_errors": trace.errors,
        }

    @staticmethod
    def _calls(report: dict[str, Any], dynamic: dict[str, Any], trace: TraceResult) -> dict[str, Any]:
        instances = {item["id"]: item for item in report.get("instances", [])}
        edges = {(caller, int(block)) for caller, blocks in dynamic["executed_blocks_by_body"].items()
                 for block in blocks}
        intrinsics: set[str] = set()
        foreign: set[str] = set()
        unresolved: list[dict[str, Any]] = []
        for call in report.get("calls", []):
            key = (call.get("caller"), int(call.get("block", -1)))
            if key not in edges:
                continue
            callee_id = call.get("callee")
            callee = instances.get(callee_id) if callee_id else None
            if callee and callee.get("intrinsic"):
                intrinsics.add(str(callee.get("name")))
            if callee and callee.get("foreign"):
                foreign.add(str(callee.get("name")))
            if not call.get("resolved", False):
                unresolved.append({
                    "caller": call.get("caller"),
                    "block": call.get("block"),
                    "reason": call.get("reason", "unresolved"),
                })
        for instance_id in trace.runtime_instance_ids:
            item = instances.get(instance_id)
            if item and item.get("intrinsic"):
                intrinsics.add(str(item.get("name")))
            if item and item.get("foreign"):
                foreign.add(str(item.get("name")))
        return {
            "intrinsics": sorted(intrinsics),
            "foreign_items": sorted(foreign),
            "unresolved_executed_calls": unresolved,
        }

    def _make_cargo_project(self, source: Path, edition: str, workspace: Path) -> Path:
        project = workspace / "cargo"
        (project / "src").mkdir(parents=True)
        shutil.copyfile(source, project / "src" / "main.rs")
        (project / "Cargo.toml").write_text(
            "[package]\nname = \"lean_surfaces_rust_measurement\"\n"
            "version = \"0.0.0\"\nedition = \"" + edition + "\"\n",
            encoding="utf-8",
        )
        return project

    @staticmethod
    def _verdict(status: int | None, stdout: str, stderr: str) -> str:
        if status is None:
            return "timeout"
        if status == 0:
            return "ok"
        if "Undefined Behavior:" in stderr:
            return "ub"
        if re.search(r"(?:thread '[^']+'|panicked at)", stderr):
            return "panic"
        if not re.search(r"(?m)^(?:error(?:\[[^]]+\])?:|error:|could not compile)", stderr):
            return "exit"
        return "tool_error"

    def _run_row(self, row: dict[str, Any]) -> dict[str, Any]:
        row_id = row["id"]
        source = self._source_path(row)
        edition = str(row.get("edition", "2024"))
        crate_name = "measure_" + re.sub(r"[^A-Za-z0-9_]", "_", row_id).lower()
        workspace = self._next_workspace(row_id)
        try:
            report = self._extract(source, crate_name, edition, workspace)
            static = self._static(report, crate_name)
            model_reports: dict[str, Any] = {}
            model_dynamic: dict[str, Any] = {}
            traces: dict[str, TraceResult] = {}
            for model in self.models:
                project = self._make_cargo_project(source, edition, workspace / ("run_" + model))
                target_dir = project.parent / "target"
                env = self._env(target_dir, model, trace=True)
                command = [
                    "rustup", "run", TOOLCHAIN, "cargo", "miri", "run",
                    "--manifest-path", str(project / "Cargo.toml"), "--offline", "--quiet",
                ]
                status, stdout, stderr = self._capture(command, env, cwd=project,
                                                       timeout=self.timeout)
                verdict = self._verdict(status, stdout, stderr)
                expected = row.get("expected_stdout", "")
                if verdict != "ok":
                    raise MeasurementError(f"{row_id} {model} verdict {verdict}; stderr tail:\n{stderr[-3000:]}")
                if stdout != expected:
                    raise MeasurementError(
                        f"{row_id} {model} stdout differs from manifest: {stdout!r} != {expected!r}"
                    )
                trace = self._trace(stderr, report, static)
                traces[model] = trace
                dynamic = self._dynamic(trace, static, crate_name)
                model_dynamic[model] = dynamic
                model_reports[model] = {
                    "model": model,
                    "flags": list(MIRI_FLAGS) + (["-Zmiri-tree-borrows"] if model == "tree_borrows" else []),
                    "exit_status": status,
                    "verdict": verdict,
                    "stdout": stdout,
                    "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
                    "stdout_bytes": len(stdout.encode()),
                }
                if trace.errors:
                    raise MeasurementError(f"{row_id} {model} trace errors: {trace.errors[:5]}")
            canonical = model_dynamic["stacked_borrows"]
            tree = model_dynamic["tree_borrows"]
            same_counts = canonical["executed"] == tree["executed"]
            calls = self._calls(report, canonical, traces["stacked_borrows"])
            result = {
                "id": row_id,
                "category": row["category"],
                "source": str(Path(row["path"])),
                "upstream_path": row.get("upstream_path"),
                "static": {
                    "entry_name": static["entry_name"],
                    "reachable": static["reachable"],
                    "node_counts": static["node_counts"],
                },
                "oracle": {"models": model_reports, "counts_equal_between_models": same_counts},
                "executed": canonical,
                "executed_tree_borrows": tree["executed"],
                "intrinsics_reached": calls["intrinsics"],
                "foreign_items_reached": calls["foreign_items"],
                "unresolved_executed_calls": calls["unresolved_executed_calls"],
            }
            if not same_counts:
                result["counts_difference"] = {
                    "stacked_borrows": canonical["executed"],
                    "tree_borrows": tree["executed"],
                }
            return result
        finally:
            if not self.keep_work:
                shutil.rmtree(workspace, ignore_errors=True)

    def _construct_source(self, kind: str, parameter: int) -> str:
        if kind == "or_pattern_guard":
            types = ", ".join(["u8"] * parameter) + ("," if parameter == 1 else "")
            zeros = ", ".join(["0u8"] * parameter) + ("," if parameter == 1 else "")
            pats = ", ".join(["0 | 1"] * parameter) + ("," if parameter == 1 else "")
            return (
                f"fn classify(value: ({types})) -> u8 {{\n"
                f"    match value {{ ({pats}) if true => 1, _ => 0 }}\n"
                f"}}\nfn main() {{ assert_eq!(classify(({zeros})), 1); }}\n"
            )
        if kind == "conditional_drops":
            declarations = "\n".join(f"    let d{index} = Dropper;" for index in range(parameter))
            moves = "\n".join(
                f"    if flag {{ std::mem::forget(d{index}); }}" for index in range(parameter)
            )
            return (
                "struct Dropper;\nimpl Drop for Dropper { fn drop(&mut self) {} }\n"
                "fn main() {\n    let flag = std::hint::black_box(true);\n"
                + declarations + "\n" + moves + "\n}\n"
            )
        if kind == "closures":
            declarations = "\n".join(
                f"    let c{index} = |value: i32| value + {index + 1};"
                for index in range(parameter)
            )
            calls = "\n".join(f"    value = c{index}(value);" for index in range(parameter))
            return "fn main() {\n    let mut value = 0i32;\n" + declarations + "\n" + calls + "\n    std::hint::black_box(value);\n}\n"
        if kind == "iterator_chain":
            maps = ".map(|value| value + 1)" * parameter
            return f"fn main() {{ let value = (0..1){maps}.fold(0, |a, b| a + b); assert_eq!(value, {parameter}); }}\n"
        raise MeasurementError("unknown construct kind: " + kind)

    def _construct_sizes(self) -> list[dict[str, Any]]:
        rows = []
        parameters = {
            "or_pattern_guard": range(1, 9),
            "conditional_drops": (1, 2, 4, 8, 16),
            "closures": (1, 2, 4, 8, 16),
            "iterator_chain": (1, 2, 4, 8, 16),
        }
        for kind, values in parameters.items():
            for parameter in values:
                row_id = f"construct_{kind}_{parameter}"
                workspace = self._next_workspace(row_id)
                source = workspace / "construct.rs"
                source.write_text(self._construct_source(kind, parameter), encoding="utf-8")
                try:
                    crate = "construct_" + kind + "_" + str(parameter)
                    report = self._extract(source, crate, "2024", workspace)
                    static = self._static(report, crate)
                    user = static["reachable"]["user"]
                    rows.append({
                        "construct": kind,
                        "parameter": parameter,
                        "user_bodies": user["bodies"],
                        "user_blocks": user["blocks"],
                        "user_statements": user["statements"],
                        "user_terminators": user["terminators"],
                        "node_counts": static["node_counts"],
                    })
                finally:
                    if not self.keep_work:
                        shutil.rmtree(workspace, ignore_errors=True)
        return rows

    def run(self, selected: set[str] | None, include_constructs: bool) -> dict[str, Any]:
        programs = self.manifest["programs"]
        if selected:
            programs = [row for row in programs if row["id"] in selected]
            missing = selected - {row["id"] for row in programs}
            if missing:
                raise MeasurementError("unknown row id(s): " + ", ".join(sorted(missing)))
        results = []
        for index, row in enumerate(programs, 1):
            print(f"[{index}/{len(programs)}] {row['id']}", file=sys.stderr)
            results.append(self._run_row(row))
        output = {
            "schema": "lean-surfaces.rust.mir-measurement.v0",
            "toolchain": self.toolchain_info,
            "extractor_schema": "lean-surfaces.rust.mir.v0",
            "extractor_flags": [
                "-Zalways-encode-mir", "-Zextra-const-ub-checks", "-Zmir-preserve-ub",
                "-Zmir-opt-level=0", "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
                "-Zmir-enable-passes=-ReferencePropagation,-GVN", "-Zdeduplicate-diagnostics=no",
            ],
            "trace": {
                "logger": TRACE_LOGGER,
                "root": "the extracted entry body, excluding std::rt launcher and cleanup",
                "count_rule": "unique body/block sites plus statement and block visits; loops count visits",
                "borrows": ["stacked_borrows", "tree_borrows"],
            },
            "manifest": {
                "schema": self.manifest["schema"],
                "rustc_revision": self.manifest.get("rustc_revision"),
                "program_count": len(results),
                "categories": dict(sorted(Counter(row["category"] for row in programs).items())),
            },
            "rows": results,
            "construct_sizes": [],
        }
        if include_constructs:
            output["construct_sizes"] = self._construct_sizes()
        return output


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--manifest", type=Path,
                        default=Path(__file__).with_name("measurement_manifest.json"))
    parser.add_argument("--output", type=Path,
                        help="write the normalized report to this path")
    parser.add_argument("--work-root", type=Path,
                        help="lane-local scratch root (default: $RUST_LANE_ROOT/mir-measurement-work)")
    parser.add_argument("--extractor", type=Path,
                        help="rustc_public extractor (default: $RUST_LANE_ROOT/rust-mir-extract)")
    parser.add_argument("--timeout", type=float, default=180.0,
                        help="seconds per extractor or Miri invocation")
    parser.add_argument("--only", nargs="*", metavar="ID",
                        help="measure only selected manifest ids")
    parser.add_argument("--no-constructs", action="store_true",
                        help="omit the static construct-size table")
    parser.add_argument("--keep-work", action="store_true",
                        help="retain lane-local temporary work for inspection")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        runner = Runner(args)
        report = runner.run(set(args.only) if args.only else None, not args.no_constructs)
        encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(encoded, encoding="utf-8")
        print(encoded, end="")
        return 0
    except (MeasurementError, OSError, subprocess.SubprocessError) as error:
        print(f"measure.py: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
