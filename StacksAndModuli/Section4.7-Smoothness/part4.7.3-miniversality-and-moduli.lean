module

public import StacksAndModuli.«Section4.7-Smoothness».«part4.7.2-infinitesimal-lifting-criteria»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.4-algebraicity-of-mg»
public import StacksAndModuli.«Section4.5-Dimension».«part4.5.1-dimension»

/-!
# Miniversality and smoothness of moduli stacks

This module covers Proposition 4.7.6 (`prop:miniverseal-and-dimension-of-smooth-stacks`),
Proposition 4.7.7 (`prop:mg-is-smooth`), Proposition 4.7.9 (`prop:bun-is-smooth`), and
Exercise 4.7.10 (`exer:existence-of-vector-bundle`) of §4.7 (Smoothness and the
Infinitesimal Lifting Criterion) of *Stacks and Moduli*
(the section and its subsections carry no `sec:`
labels). The last three belong to the subsection "Smoothness of moduli stacks".

All four items are applications of the Infinitesimal Lifting Criteria (part 4.7.2) whose
prerequisites — tangent spaces and dimension of stacks (§4.5), residual gerbes and
minimal presentations (§4.6), the moduli stacks `𝓜_g` and `Coh_{r,d}(C)` (their
Chapter 3 constructions are not yet formalized; see STATUS.md), and deformation theory
(Appendix C.2) — are not yet formalized. Each label is therefore ledgered in its own
section below, with the intended formalization and its blockers recorded; the sections
will be populated once the prerequisites land. This file contains no Lean declarations
yet, only ledger comments; see this folder's STATUS.md for the per-label states.

**Proposition 4.7.7** (`prop:mg-is-smooth`) is stated here — `ℳ_g` is smooth over `Spec ℤ`,
of dimension `3g - 3` — now that `ℳ_g` exists (§4.1 part4.1.4). Both halves are recorded
obligations: they need the obstruction theory of Appendix C.2 and, for the dimension, the
computation `T_{ℳ_g,[C]} = H¹(C, T_C)` of §4.5.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropMiniversealAndDimensionOfSmoothStacks

/- LEDGER — **Proposition 4.7.6** (`prop:miniverseal-and-dimension-of-smooth-stacks`;
the label's spelling follows the book): let `𝒳` be a noetherian algebraic stack and
`x ∈ |𝒳|` a finite type
point with smooth stabilizer. A smooth morphism `f : (U, u) → (𝒳, x)` from a scheme with
`𝒢_x ×_𝒳 U ≅ Spec κ(u)` is miniversal at `u`, i.e. `T_{U,u} → T_{𝒳,f(u)}` is an
isomorphism of `κ(u)`-vector spaces; and if `𝒳` is smooth over a field `𝕜` and
`x ∈ 𝒳(L)` has smooth stabilizer, then `dim_x 𝒳 = dim T_{𝒳,x} - dim G_x`. Surjectivity
on tangent spaces follows from the smoothness criterion
(`AlgebraicGeometry.BasedFunctor.smooth_iff_nonempty_lifting_of_isSmallExtension`,
part 4.7.2) applied to the small extension `κ(u)[ε] → κ(u)`. Blocked on: tangent spaces
`T_{𝒳,x}` of stacks via dual-number points and the dimension `dim_x 𝒳` (§4.5; Mathlib's
`AlgebraicGeometry` has no scheme tangent spaces either, cf. Stacks 0DRN), residual
gerbes `𝒢_x` and `thm:minimal-presentations` (§4.6), stabilizer group algebraic spaces
`G_x` (§4.2, verified in parallel), and the topological-space dimension theory of
part 4.3.4. -/

end PropMiniversealAndDimensionOfSmoothStacks

section PropMgIsSmooth

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- **Proposition 4.7.7** (`prop:mg-is-smooth`): for `g ≥ 2` the moduli stack `ℳ_g` is
smooth over `Spec ℤ`.

The intended proof (deferred) combines the infinitesimal lifting criterion (part 4.7.2)
with deformation theory: lifting a square along a small extension `A → A₀` is extending a
family of curves `𝒞₀ → Spec A₀` over `Spec A`, and the obstruction lives in
`H²(C, T_C)`, which vanishes for a curve
(Appendix C.2). Cf. Stacks 0E6M. -/
theorem smooth_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedFunctor.Smooth
      (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g).toBase := by
  sorry

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- **Proposition 4.7.7** (`prop:mg-is-smooth`) (the dimension clause): `ℳ_g` has
dimension `3g - 3`.

The book states smoothness *of relative dimension* `3g - 3` over `Spec ℤ`; the dimension
of a prestack is §4.5's `BasedCategory.dim`, and over `Spec ℤ` the two agree. The value
comes from `T_{ℳ_g,[C]} = H¹(C, T_C)` and Riemann–Roch (Example 4.5.8),
both of which need the tangent sheaf `T_C` and hence the relative differentials that
Mathlib does not have. -/
theorem dim_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedCategory.dim (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g) =
      ((3 * (g : ℤ) - 3 : ℤ) : WithBot (WithTop ℤ)) := by
  sorry

end PropMgIsSmooth

section PropBunIsSmooth

/- LEDGER — **Proposition 4.7.9** (`prop:bun-is-smooth`): for a smooth, connected,
projective curve `C` over an
algebraically closed field `𝕜`, the algebraic stack `Coh_{r,d}(C)` of coherent sheaves of
rank `r` and degree `d` is smooth over `Spec 𝕜` of dimension `r²(g - 1)`. The proof
applies the smoothness criterion (to a non-quasi-compact stack): the obstruction to
extending a coherent sheaf `ℱ₀` on `C_{A₀}` to `C_A` lies in `Ext²_{𝒪_C}(F, F) = 0` on a
curve (`prop:higher-order-deformations-of-vector-bundles`, Appendix C.2), and
`T_{Coh,[F]} = Ext¹_{𝒪_C}(F, F)` has dimension `dim Aut(F) + r²(g-1)` by Riemann–Roch
(`ex:bunC-tangent-space`, §4.5). Blocked on: the moduli stack `Coh_{r,d}(C)` (its
Chapter 3 construction is not yet formalized, see STATUS.md), Ext groups of coherent
sheaves on schemes (absent from Mathlib), Appendix C.2
deformation theory, and §4.5 tangent spaces. Nonemptiness uses
`exer:existence-of-vector-bundle` below. -/

end PropBunIsSmooth

section ExerExistenceOfVectorBundle

/- LEDGER — **Exercise 4.7.10** (`exer:existence-of-vector-bundle`): on a smooth,
connected, projective curve,
for every line bundle `L` and rank `r > 0` there exists a vector bundle `E` of rank `r`
with `det E ≅ L` (e.g. `E = L ⊕ 𝒪^{r-1}`). Blocked on determinants of vector bundles on
schemes (top exterior powers of locally free `𝒪_X`-modules) and the vector-bundle API on
curves, none of which exist in Mathlib or the Chapter 3 files. -/

end ExerExistenceOfVectorBundle
