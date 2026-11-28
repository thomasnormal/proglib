# C union initialization contract

The C envelope retains Clang's `InitListExpr` nodes, their selected field
metadata, the union's declaration identity, and the parser-native record
layout. The evaluator uses that node and identity directly.

C23 §6.7.11p6 initializes a union from one initializer. A designated
initializer selects the named member, and a positional initializer selects
the first named member. Clang's selected field on a nested initializer is
the authoritative parser observation for anonymous unions. §6.7.11p11
zero-initializes an omitted object with static storage duration. For a union,
the first named member receives that zero initialization and the remaining
object bytes are initialized only where the parser layout identifies the
padding range. The evaluator recurses through nested record and union nodes,
so a selected member keeps its own parser type and extent.

Record layouts are joined by a stable traversal ordinal from the approved
Clang layout plugin to the corresponding complete `RecordDecl` in Clang's
AST dump. Process pointer addresses are not shared between plugin and dump
invocations. Source offsets remain diagnostic metadata and are only a
compatibility fallback for old probe output.

Reading an inactive union member remains a loud refusal under this item.
Admitting that operation requires the byte-representation and effective-type
contract. Empty unions with no named first member remain a loud refusal until
their C23 default-initialization and aggregate effective-type rules are
implemented together. No source rewrite or arbitrary active-member choice is
permitted.
