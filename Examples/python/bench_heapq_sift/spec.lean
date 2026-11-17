import Examples.python.bench_heapq_sift.proof

open LeanModels LeanModels.Python

load_program bench_heapq_sift from "Examples/python/bench_heapq_sift/bench_heapq_sift.json"

def siftupWorld : World :=
  { initWorld bench_heapq_sift with
    heap := #[.list #[.int 5, .int 1, .int 2, .int 7, .int 4, .int 3]] }

def siftdownWorld : World :=
  { initWorld bench_heapq_sift with
    heap := #[.list #[.int 1, .int 3, .int 2, .int 7, .int 4, .int 0]] }

theorem siftup_concrete :
    (match callIn bench_heapq_sift 4096 siftupWorld "_siftup" #[.ref 0, .int 0] with
     | .ok w .none => w.heap == #[.list #[.int 1, .int 4, .int 2, .int 7, .int 5, .int 3]]
     | _ => false) = true := by proofs

theorem siftdown_concrete :
    (match callIn bench_heapq_sift 4096 siftdownWorld "_siftdown"
        #[.ref 0, .int 0, .int 5] with
     | .ok w .none => w.heap == #[.list #[.int 0, .int 3, .int 1, .int 7, .int 4, .int 2]]
     | _ => false) = true := by proofs
