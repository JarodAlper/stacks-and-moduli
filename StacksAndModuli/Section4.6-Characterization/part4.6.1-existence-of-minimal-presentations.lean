module

/-!
# Existence of minimal presentations

This module covers `thm:minimal-presentations` (Theorem 4.6.1),
`rmk:miniversal-presentations` (Remark 4.6.2) and
`exer:existence-miniversal-presentations-non-noetherian` (Exercise 4.6.3) — the subsection
"Existence of minimal presentations" of §4.6 (Characterization of Deligne–Mumford stacks)
of *Stacks and Moduli* (neither
the section nor its subsections carries a `sec:` label).

All three items are recorded as LEDGER entries — this file contains no Lean declarations:
the statement of the Existence of Minimal Presentations theorem requires noetherian
algebraic stacks, finite type points of the topological space `|𝒳|`, the residual gerbe
at a point together with its locally closed immersion (§4.5), the dimension of stabilizer
groups, and smooth morphisms of stacks of a given relative dimension — none of which is
available yet. The equivalent characterizations that this theorem feeds into are
formalized in
`StacksAndModuli.«Section4.6-Characterization».«part4.6.2-equivalent-characterizations»`.

Main results: none yet — see the LEDGER comments in the section blocks
`ThmMinimalPresentations`, `RmkMiniversalPresentations` and
`ExerExistenceMiniversalPresentationsNonNoetherian`, and this folder's STATUS.md.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmMinimalPresentations

/- LEDGER — **Theorem 4.6.1** (`thm:minimal-presentations`, Existence of Minimal
Presentations): let `𝒳` be a noetherian algebraic stack and let `x ∈ |𝒳|` be a finite type point with smooth stabilizer
`G_x`. Then there exist a scheme `U`, a closed point `u ∈ U`, and a smooth morphism
`(U, u) → (𝒳, x)` of relative dimension `dim G_x` such that the square with vertices
`Spec κ(u)`, `U`, the residual gerbe `𝒢_x`, and `𝒳` is cartesian. In particular, if `G_x`
is finite and reduced, there is an étale morphism `(U, u) → (𝒳, x)` from a scheme.

The statement is blocked on:
- noetherian algebraic stacks (part 4.3.4 ledger: noetherianness requires
  quasi-separatedness, i.e. the separation properties of the diagonal, part 4.3.3 ledger);
- finite type points of the topological space `|𝒳|` (§4.4);
- well-definedness of the stabilizer `G_x` of a point of `|𝒳|` independently of the choice
  of a representative, together with its smoothness, finiteness, reducedness and dimension
  (`exer:stabilizer-properties`, part 4.3.4 ledger, itself blocked on the `Isom` presheaf
  of `exer:isom-presheaf`, §3.4 ledger);
- the residual gerbe `𝒢_x` and its locally closed immersion `𝒢_x ↪ 𝒳`
  (`prop:residual-gerbe-algebraic`, Proposition 4.5.16, and
  `exer:dimension-of-residual-gerbe`, Exercise 4.5.22);
- smooth morphisms of stacks of a given relative dimension (part 4.3.1 defers even the
  scheme-level `IsSmoothLocal` statement for `SmoothOfRelativeDimension`).

The proof additionally needs the Slicing Criterion for Flatness (`cor:slicing-flat`,
Corollary A.2.9; no regular-sequence flatness criterion exists in Mathlib) and smooth descent
of flatness and smoothness along presentations (part 4.3.1, deferred). See also Stacks
Project tag 06MC. -/

end ThmMinimalPresentations

section RmkMiniversalPresentations

/- LEDGER — **Remark 4.6.2** (`rmk:miniversal-presentations`): a smooth presentation
`p : U → 𝒳` is *miniversal* at `u ∈ U(k)` if `T_{U,u} → T_{𝒳,p(u)}` is an isomorphism of
`k`-vector spaces; the presentations produced by `thm:minimal-presentations` are miniversal
(`prop:miniverseal-and-dimension-of-smooth-stacks`, Proposition 4.7.6 — the label's
"miniverseal" typo is the book's). If the stabilizer `G_x` is not
smooth, a miniversal presentation still exists but its relative dimension is the dimension
of the Lie algebra of `G_x` rather than `dim G_x` (e.g. `𝔾_m → B μ_p` in characteristic
`p`), while the argument of `thm:minimal-presentations` still produces an fppf (but not
necessarily smooth) morphism `(U, u) → (𝒳, x)` with `𝒢_x ×_𝒳 U ≅ Spec κ(u)`, which is
moreover quasi-finite when `𝒳` has quasi-finite diagonal. Blocked on tangent spaces of
stacks (§4.7), on the items of the `thm:minimal-presentations` ledger above, and, for the
`B μ_p` example, on fppf quotient stacks (`prop:quotient-stacks-fppf-are-algebraic`,
Proposition 7.3.10; quotient stacks themselves are ledgered in §3.4/§3.5). See also Stacks
Project tag 06MC. -/

end RmkMiniversalPresentations

section ExerExistenceMiniversalPresentationsNonNoetherian

/- LEDGER — **Exercise 4.6.3** (`exer:existence-miniversal-presentations-non-noetherian`):
if `𝒳` is a possibly non-noetherian algebraic stack and `x ∈ |𝒳|` is a finite type point
with discrete and unramified stabilizer `G_x`, then there is an étale morphism
`(U, u) → (𝒳, x)` from a scheme `U` with `u ∈ U` a closed point. Blocked on the same items
as `thm:minimal-presentations` and on the non-noetherian residual gerbes of
`exer:non-noetherian-residual-gerbes-DM` (Exercise 4.5.18). See also Stacks Project
tag 06N3. -/

end ExerExistenceMiniversalPresentationsNonNoetherian
