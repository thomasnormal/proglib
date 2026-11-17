# PY-REAL baseline

## 2026-11-16 refresh

The verified runner survey covered the current 183-module manifest and 1,542
public functions. It drove 8,677 calls: 138 were MATCH, one module was
INCOMPLETE (`fib`, with 1 of 8 calls completed and matching), and 44 modules
had no drivable call result. No DIVERGE was observed. The standard-library
wild sweep covered 166 files: 7 MATCH, 159 REFUSE, and 0 DIVERGE, TIMEOUT,
ORACLE, HUNG, or RUNNER failures.

The current sole-wall price from the standard-library sweep is:

| Wall | Sole | Present | Static nodes | Files |
|---|---:|---:|---:|---:|
| `import` | 20 | 150 | 807 | 139 |
| no static wall | 4 | 4 | — | — |
| `ImportFrom:accelerator-outside-domain` | 3 | 3 | 3 | 3 |
| `Starred:call` | 1 | 68 | 188 | 69 |
| `DictComp` | 1 | 18 | 22 | 18 |
| `class-creation` | 0 | 102 | — | — |
| `Set:display` | 0 | 27 | 63 | 27 |
| `Lambda` | 0 | 23 | 80 | 23 |
| `ImportFrom:accelerator-unmeasured` | 0 | 21 | 35 | 21 |
| `Delete` | 0 | 14 | 21 | 14 |
| `YieldFrom:delegation` | 0 | 12 | 32 | 13 |
| `ListComp` | 0 | 7 | 10 | 7 |

The next item is therefore the `import` wall: it is the only wall with twenty
sole blockers, while the survey does not yet claim function flips for those
stdlib files. The exact artifacts are `/tmp/ls-python-library-survey.json`
and `/tmp/ls-python-stdlib-survey.json`.

The focused function-level price used the nine sole-import modules that are in
the manifest (`_bootsubprocess`, `codeop`, `contextvars`, `fnmatch`, `linecache`,
`reprlib`, `struct`, `tty`, and `uu`). It covered 18 public functions and 112
calls: seven modules produced MATCH call results and two had no drivable calls;
no DIVERGE was observed. The other sole-import stdlib files are outside the
current manifest, so their function flips remain unmeasured rather than being
treated as zero.

The complete sole-wall price over the 14 sole-wall modules that are in the
manifest is 47 public functions and 161 calls:

| Sole wall | Modules | Public functions | Calls | Matching calls |
|---|---:|---:|---:|---:|
| `import` | 9 | 18 | 112 | 29 |
| `ImportFrom:accelerator-outside-domain` | 3 | 21 | 0 | 0 |
| `Starred:call` | 1 | 5 | 25 | 8 |
| `DictComp` | 1 | 3 | 24 | 16 |

There were no observed DIVERGEs in this focused run; 53 of the 161 calls
matched. The import wall remains
the largest measured sole wall by module count, but its function-level payoff
is limited by the 18 functions and by unmeasured sole-import files outside the
manifest.

The next semantic wall is `DictComp`, chosen by measured payoff over
`Starred:call`: `token.py` is its one sole-wall module, with 3 public functions,
24 driven calls, and 16 matches. The implementation price is a structured
`ast.DictComp` envelope and a direct comprehension semantic case with ordered
generator/filter evaluation and fresh comprehension scope; the extractor must
not lower it to a call or reparse source text. Differential rows must include
empty and nonempty iterables, filters, duplicate keys, and exceptions. The
measured Starred alternative is one sole-wall module with 5 public functions,
25 calls, and 8 matches, so it remains the fallback wall.

The DictComp structural sub-item is now landed while the extractor remains
loud: `Expr.dictComp` has synchronized AST, JSON, trunk/monadic evaluator, and
`Obs.lean` fuel/world-invariance cases, and both evaluators return the named
refusal. The CPython extractor still emits whole-node `DictComp` refusal, so no
real program has been admitted and no semantic flip is claimed. The direct
worker probe is parked at the shared proof boundary. A trunk worker compiles
for the one-clause/no-filter shape, but admitting it requires a new
`evalDictCompStep` fuel-monotonicity conjunct in `Obs.lean`'s fixed-order
mutual induction, plus the corresponding `PayloadBlind` arm. The monadic
continuation requires a new `Kont.dictComp` field and its own generated proof
bundle. No local shortcut or theorem weakening is sound. The extractor remains
loud, so no semantic flip is claimed before that bundle is priced and built.

The fallback `Starred:call` probe has now crossed its extractor boundary: the
extractor admits `ast.Starred` positional arguments into the existing synthetic
`<star-arg>` marker, while `**` keyword unpacking remains loud. The monadic
evaluator build remains green; the focused copyreg price (5 public functions,
25 calls, 8 matches) is the next differential check before claiming a wall flip.

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The full post-stall survey (141 pinned CPython 3.9.25 library rows, run 2026-11-12) has **13 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The targeted import refresh flipped `email.charset` from body REFUSED to VERIFIED with 24/24 matching calls; the call denominator is unchanged because those calls were already driven through the closed-function surface. The 13 VERIFIED modules are `email.charset`, `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The function-level scoreboard has **21 VERIFIED functions out of 540 modeled public functions**, with 503 matching calls among the function calls driven by this survey. A function is counted when at least one pinned CPython call returns normally and every driven call for that function matches; C-accelerator and unsafe-call entries are explicit skips and are outside the modeled-function denominator. A module-level refusal does not turn an independently matching function back into a potential flip. After the targeted import refresh, no remaining wall has a measured function flip; the next price is by newly agreed calls and module rows.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by function flips first, then newly agreed calls, with `sole` and `present` retained as context. The required stall-rule rerun used the complete 141-row survey JSON on 2026-11-12 with
`python3 harness/library_rank.py --provenance census:library --json /tmp/library-rank-current.json /tmp/library-current.json`.
The published figures were revalidated on 2026-11-15 against the post-opaque-import
survey artifact `/tmp/library-full-next.json`; the pre-refresh `/tmp/library-current.json`
artifact predates the `email.charset` flip and is not a comparable ranking input.
The price columns are measured surfaces, not promises: modules, public functions, driven calls, matched calls, rows that would become verified, and functions that would become verified if that wall alone were removed.

| Wall | Present | Sole | Modules | Public functions | Driven calls | Matched calls | Potential rows | Function flips |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `class-creation` | 62 | 0 | 62 | 282 | 2,015 | 183 | 1 | 0 |
| `definition-order` | 34 | 0 | 34 | 178 | 1,288 | 162 | 0 | 0 |
| `import` | 29 | 6 | 29 | 74 | 536 | 118 | 0 | 0 |
| `node:DictComp` | 1 | 1 | 1 | 3 | 24 | 16 | 0 | 0 |
| `accelerator-unmeasured` | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `accelerator-outside-domain` | 2 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| `frozenset` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `heap-plus` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `method call '.extend' on a list is outside the tier` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `try-except` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |

The measured opaque arm now admits the imports needed by `email.charset`; its three public functions are body- and call-verified. `rsa_inverse` remains a separate annotation-observation check. The next ranked wall remains `class-creation`, priced by its 183 newly matching calls and one potential whole-row verification; it has **0 function flips**. The three-item stall rule therefore requires a replan before another zero-flip semantic tier.

The remaining observed messages are one accelerator-domain wall, one heap `+` wall, one unsupported `try/except` wall, one missing `frozenset` builtin, and one list `.extend` wall. They remain recorded per module in the JSON result and are not silently omitted from the ranking.

The baseline command used pinned `python3.9`, fixed fuel (`200000` body, `10000` call), eight calls per public function, a 900-second body bound, and a 120-second per-module call bound. The complete run covered all 183 manifest and in-repo rows in one survey; its eight unfinished calls remain explicit and are not counted as agreement.
