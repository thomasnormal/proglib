#!/usr/bin/env bash
set -eu
if rg -n '^partial def|^private partial def' \
  LeanModels/Sv/Kernel/CoreMemExec.lean \
  LeanModels/Sv/Kernel/CoreMemResume.lean \
  LeanModels/Sv/Kernel/HierarchyCoreMem.lean \
  LeanModels/Sv/Kernel/HierarchyMemE.lean \
  LeanModels/Sv/Kernel/MemE.lean \
  LeanModels/Sv/Param2.lean \
  LeanModels/Sv/Kernel/AggregateBridge.lean; then
  echo 'partial def on the CoreMem instantiation/step path' >&2
  exit 1
fi
echo 'no partial defs on CoreMem instantiation/step path'
