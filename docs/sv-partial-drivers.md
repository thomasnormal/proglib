# Partial packed drivers

This note defines the proof boundary for a generated family of continuous
assignments to disjoint bits of one packed signal, such as
`assign next_vec[k] = in_vec[k]` in a symbolic generate-for loop.

## Certificate

A partial-driver certificate is source-shaped. It retains the parser-native
assignment targets and the generate header; it does not flatten the family or
rewrite the assignments into a whole-vector assignment. For each member it
records a statically evaluated bit window and proves:

- the target root is the same packed signal;
- every selected bit is in range;
- selected windows are pairwise disjoint, by induction over the generate index;
- no member has a dynamic index, aggregate or concatenation target; and
- no whole-signal, procedural, or other continuous driver competes for the
  same root.

The certificate is a language/design property, not an executor-fuel bound.
A non-affine or otherwise unresolved index is refused rather than guessed.

## Composition

The family composition updates only its certified bits. A packed net bit not
covered by a driver remains `z`; a covered bit is the four-state result of that
member's expression. Pairwise disjointness makes the composition independent
of source order, while preserving the exact four-state value of each expression.
The root remains one signal in the ordinary state; this is not a memory model
and does not introduce a second evaluator.

The settle theorem should expose the ordinary semantics directly:
`settleAssign` on the source-ordered family equals the partial-driver
composition on the root together with the existing settle result for unrelated
signals. It also supplies a frame equality outside the root. A generated loop
is handled by induction on its symbolic index range; it is never unrolled at a
fixed parameter.

Overlapping windows, dynamic indices, mixed whole/partial drivers, unresolved
bounds, and reads of a target that create a real dependency cycle remain
refusals. Output concatenations are a separate source-shaped certificate and
must not be silently lowered into this one.
