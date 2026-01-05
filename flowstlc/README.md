# FlowSTLC Lean 4 formalization

- `FlowSTLC/Grade.lean` defines the two-point order `Pub <= Sec`, meet as semiring addition, join as multiplication, and  proves the algebraic and order laws used by the calculus.
- `FlowSTLC/Core.lean` defines types, graded contexts, typing derivations, and total call-by-value evaluation. `Term Γ rho A` means that the term has type `A` under ordinary context `Γ` and graded usage context `rho`.
- `FlowSTLC/Metatheory.lean` proves preservation/progress for the intrinsic semantics, the binary fundamental theorem, strong normalization of the total semantics, and termination-insensitive non-interference for a secret input and public boxed base result.
- `FlowSTLC/Examples.lean` checks representative programs and proves that the approximation rule cannot turn an actual public use into a secret use.

Finite records are encoded as nested binary record products. This removes labels from the mechanization without changing the record metatheory.

## Representation choices

The formalization is intrinsically typed: a value of `Term Γ rho A` contains exactly a derivation of the corresponding typing judgment. Therefore an ill-typed program is not representable, and evaluation has result type `Val A` by construction. Variables use de Bruijn indices, so alpha-renaming and capture-avoiding substitution do not require separate trusted machinery.

The evaluator maps function terms to total Lean functions. For this recursion-free calculus, that gives a direct normalization result. Preservation and progress are stated for this total typed semantics rather than for a second, duplicated raw small-step syntax. The non-interference proof is not obtained merely from intrinsic typing: `fundamental` is a structural proof over
every typing constructor using an observer-indexed binary logical relation.

At base types, related public observations are equal. At `Box Sec A`, a public observer imposes no relation on the contents. Consequently, `termination_insensitive_noninterference` proves the report's claim. Since the formal evaluator is total, this mechanized core actually establishes equality of the two evaluated public base results, which is stronger than the report's
conditional "if both terminate" formulation.
