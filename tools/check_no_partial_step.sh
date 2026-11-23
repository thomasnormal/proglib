#!/usr/bin/env bash
set -eu
if rg -n '^partial def' LeanModels/Sv/Kernel/CoreMemExec.lean LeanModels/Sv/Kernel/CoreMemResume.lean; then
  echo 'partial def on the CoreMem instantiation/step path' >&2
  exit 1
fi
echo 'no partial defs on CoreMem instantiation/step path'
