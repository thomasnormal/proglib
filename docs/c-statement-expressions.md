# GNU statement expressions

This slice models Clang's `StmtExpr` node directly. It follows the GNU C
statement-expression rule that the compound body executes in order and its
final expression statement supplies the value. The implementation does not
lower the node into a separate block or comma expression.

The extractor retains expression-only bodies as parser children. A body that
contains a declaration or a control statement is retained as `StmtExpr` with
an absent admitted body and remains a loud refusal. This preserves the scope
and control-flow boundary until those pieces have their own representation.

The focused ranked wall has six sole rows. `950906-1.c` is the expression-only
case. Its unchanged source was parsed by Clang 21.1.8, the parser-native body
was inserted into an audit envelope, and the model returned `0`, matching
Clang at O0, O2 and UBSan/ASan. The five other rows contain declarations or
control statements in the statement-expression body and remain refused.

The semantic boundary is the GNU extension documented by GCC, with Clang's
`StmtExpr` AST node as the approved parser representation. ISO C23 has no
standard statement-expression construct.
