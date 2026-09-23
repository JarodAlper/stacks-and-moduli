module

public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.API.ProjectiveSpaceTwistMultiplication

/-!
# The Quot-to-Grassmannian map, its underlying free map

For `F = 𝒪(-l)^{⊕r}` on `ℙⁿ_S` and a quotient `p : F ↠ Q`, the Grassmannian step of §2.4
attaches to `p` the map

`𝒪_S^m ⟶ π_*(Q(d))`,   `m = r · binom(n + d - l, n)`,

whose components are the images under `p(d)` of the degree-`(d-l)` monomial sections of
`F(d)`.  This file builds that map.

The three moves are: `Scheme.twistMonomialSection` (the monomials on any base, pulled back
from `ℙⁿ_ℤ`); `Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat`, which is
`F ⊗ 𝒪(d) ≅ ∐_r 𝒪(d-l)`, to place a monomial in a summand of `F(d)`; and
`Scheme.Modules.freeHomOfSections` to assemble the family into a map out of `𝒪_S^m`.  The
degree bookkeeping is carried by the hypothesis `he : (d : ℤ) - l = (e : ℤ)` rather than by
`Int.toNat`, so that no `eqToHom` survives into the statement.

Note that `Γ((pushforward π).obj (Q(d)), ⊤)` is *definitionally* `Γ(Q(d), ⊤)`, so the target
needs no comparison.

Main declarations:

* `AlgebraicGeometry.Scheme.twistedFreeMonomialSection`;
* `AlgebraicGeometry.Scheme.quotMonomialSection`;
* `AlgebraicGeometry.Scheme.quotGrassmannianFreeMap` and its factorization
  `…quotGrassmannianFreeMap_eq` through `π_*(F(d))`, which is the first step of the
  epimorphism argument.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The monomial global sections of `F(d)` for `F = 𝒪(-l)^{⊕r}`**, indexed by a summand
and a monomial of degree `e = d - l`. -/
def twistedFreeMonomialSection (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r))
    (i : Fin ((n + e).choose n)) :
    Γ(Scheme.projectiveSpaceOverTwistModule
      (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l))
      (d : ℤ), ⊤) :=
  Scheme.Modules.Hom.app
    (Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
      (J := ULift.{u} (Fin r)) n S l d).inv ⊤
    (Scheme.Modules.Hom.app
      (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n S ((d : ℤ) - l)) j) ⊤
      (he ▸ twistMonomialSection n S e i))

/-- The image in `Q(d)` of a monomial section of `F(d)`. -/
def quotMonomialSection (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (Scheme.projectiveSpaceOver n S).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r))
    (i : Fin ((n + e).choose n)) :
    Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤) :=
  Scheme.Modules.Hom.app
    (Scheme.Modules.tensorMapLeft p (Scheme.projectiveSpaceOverTwist n S (d : ℤ))) ⊤
    (twistedFreeMonomialSection n S l r d e he j i)

/-- **The map `𝒪_S^m ⟶ π_*(Q(d))` cut out by the monomial sections.**  This is the map whose
kernel is the point of the Grassmannian that `α` assigns to a Quot point. -/
def quotGrassmannianFreeMap (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (Scheme.projectiveSpaceOver n S).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    SheafOfModules.free (R := S.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶
      (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n S)).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)) :=
  Scheme.Modules.freeHomOfSections
    (fun x => quotMonomialSection n S l r p d e he x.1 x.2)

/-- **α's map factors through `π_*(F(d))`.** -/
lemma quotGrassmannianFreeMap_eq (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (Scheme.projectiveSpaceOver n S).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    quotGrassmannianFreeMap n S l r p d e he =
      Scheme.Modules.freeHomOfSections
          (M := (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n S)).obj
            (Scheme.projectiveSpaceOverTwistModule
              (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l))
              (d : ℤ)))
          (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) =>
            twistedFreeMonomialSection n S l r d e he x.1 x.2) ≫
        (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n S)).map
          (Scheme.Modules.tensorMapLeft p (Scheme.projectiveSpaceOverTwist n S (d : ℤ))) := by
  rw [Scheme.Modules.freeHomOfSections_comp]
  rfl

end AlgebraicGeometry.Scheme
