# C translation-unit definition registry

The C frontend extracts one translation-unit set with Clang's parser. The
main source remains `translation_unit`. Function definitions whose parser
nodes come from included user headers are carried in `definition_registry`.
Each entry is the original `FunctionDecl` node, including its body, parser
declaration identity, parameter nodes, and parser-native type observations.
The registry is a field of the envelope, so one execution sees one coherent
set of source and header definitions.

Calls use Clang's `DeclRefExpr.decl_id` as the join key. The evaluator first
looks up that identity among source and registry definitions. It never matches
by function name or by a type spelling. A definition entry without a parser
identity, a duplicate identity, or a declaration whose definition is absent
from the set is a loud refusal.

This follows C23 §6.2.1p4, which gives a file-scope declaration scope to the
end of the translation unit, and §6.2.2p4–p5, which gives external and
internal linkage their identity and visibility rules. The registry retains
Clang's node-for-node AST. It does not inline, lower, or otherwise rewrite a
header body before evaluation. Header declarations without bodies remain in
the frontend's external-declaration evidence and are refused at a call site
unless a definition with the same parser identity is present.

The registry does not yet admit header-owned objects, record declarations,
or declarations from a separate translation-unit set. Such calls and layout
uses remain refused until their parser identities and corresponding layout
observations are carried in the same envelope. No oracle result is claimed
for a registry run until the approved structured-type plugin has been rebuilt
with dependency-file observations enabled.
