import LeanModels.Python

open LeanModels LeanModels.Python

load_program dictcomp_lab from "Examples/python/dictcomp_lab/dictcomp_lab.json"

/-! The admitted one-clause/no-filter DictComp cases are checked against CPython 3.9.25. -/

#guard callFunction dictcomp_lab "from_range" #[.int 5, .int 3] 4096 matches
  .ok (.tuple #[.int 5, .int 9])
#guard callFunction dictcomp_lab "from_range" #[.int 2, .int 7] 4096 matches
  .ok (.tuple #[.int 2, .int (-1)])
#guard callFunction dictcomp_lab "duplicate_keys" #[.int 5] 4096 matches
  .ok (.tuple #[.int 4, .int 3])
#py_check dictcomp_lab.bad_pair() raises
  (.typeError "cannot convert dictionary update sequence element #0 to a sequence")
#py_check dictcomp_lab.bad_length() raises
  (.valueError "dictionary update sequence element #0 has length 1; 2 is required")
#guard callFunction dictcomp_lab "unhashable_key" #[] 4096 matches
  .exn (.typeError "unhashable type: 'list'")
