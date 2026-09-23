module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# The projective bundle of a vector bundle

The relative projective bundle `ℙ(E)` of a quasi-coherent vector bundle `E` on a
scheme `S`, in the Grothendieck convention: the functor of rank-one locally free
quotients of the pullback of `E`, i.e. the relative Grassmannian `Gr(1, E)`.  By
the proved relative Grassmannian theorem (Theorem 2.1.1,
`exists_grassmannianOverFunctor_representableBy`), it is representable by a
scheme strongly projective over `S`.  No relative `Proj` or graded symmetric
algebra is needed.

This discharges the "relative projective bundle `ℙ(E)`" prerequisite named in
the deferred obligations of the algebraicity of `ℳ_g` (Theorem 4.1.17) and in
the line-bundle propositions of §A.6.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (E : S.Modules)

/-- The projective bundle functor `ℙ(E)` of a sheaf of modules `E` on `S`
(Grothendieck convention): the functor on schemes over `S` of rank-one locally
free quotients of the pullback of `E` — the relative Grassmannian `Gr(1, E)`. -/
noncomputable abbrev projectiveBundleFunctor :=
  Modules.grassmannianOverFunctor 1 E

/-- The projective bundle of a quasi-coherent vector bundle is representable by a
scheme strongly projective over the base: the case `q = 1` of the relative
Grassmannian theorem. -/
theorem exists_projectiveBundleFunctor_representableBy [E.IsQuasicoherent]
    {n : ℕ} (hE : Modules.IsProjectiveOfRank n E) :
    ∃ P : Over S, Nonempty ((projectiveBundleFunctor E).RepresentableBy P) ∧
      IsStronglyProjective P.hom :=
  Scheme.exists_grassmannianOverFunctor_representableBy E 1 hE

end AlgebraicGeometry.Scheme.Modules
