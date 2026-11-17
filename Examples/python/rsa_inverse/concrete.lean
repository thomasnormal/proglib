import LeanModels.Python
import LeanModels.Python.Monadic.Eval

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/python/rsa_inverse/rsa_inverse.json"

/-! Concrete CPython 3.9.25 witnesses for the vendored python-rsa helpers.
These are stateful interpreter runs, so they remain valid while the general
heapful `py_vcgen` call rule is parked. -/

theorem rsa_extended_gcd_concrete :
    (match callFunction rsa_inverse "extended_gcd"
      #[.int 12, .int 18] 4096 with
     | .ok (.tuple #[.int 6, .int 17, .int 1]) => true
     | _ => false) &&
    (match LeanModels.Python.Monadic.callInMono rsa_inverse 4096
        (initWorld rsa_inverse) "extended_gcd"
        #[.int 12, .int 18] with
     | .ok _ (.tuple #[.int 6, .int 17, .int 1]) => true
     | _ => false) = true := by
  native_decide

theorem rsa_inverse_concrete :
    (match callFunction rsa_inverse "inverse"
      #[.int 3, .int 7] 4096 with
     | .ok (.int 5) => true
     | _ => false) &&
    (match LeanModels.Python.Monadic.callInMono rsa_inverse 4096
        (initWorld rsa_inverse) "inverse"
        #[.int 3, .int 7] with
     | .ok _ (.int 5) => true
     | _ => false) = true := by
  native_decide

#print axioms rsa_extended_gcd_concrete
#print axioms rsa_inverse_concrete
