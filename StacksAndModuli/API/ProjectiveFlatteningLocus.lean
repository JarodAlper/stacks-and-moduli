module

public import StacksAndModuli.API.FiniteFunctorIntersection
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.DVRHilbertPolynomial
public import StacksAndModuli.API.PushforwardProjectiveRank

/-!
# The fixed-polynomial projective flattening functor

For a quasicoherent sheaf `Q` on `ℙⁿ_T`, this file packages the base-change-stable
condition that `Q` be flat over the varying base and have fibrewise Hilbert polynomial `P`.
This is the fibre condition in the Quot-to-Grassmannian construction.

The functor itself and its pullback law are unconditional.  Representability is reduced to
the precise finite-rank form of projective flattening used in the book: an identification
with finitely many flattening conditions for finite quasicoherent sheaves on `T`.  The
generic finite-intersection machinery then produces a representative immersed in `T`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningFunctor`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveFlatteningHasFiniteRankPresentation`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningRepresentableBy`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningRepresentative_hom_isImmersion`.
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

/-- Fibrewise Hilbert polynomial is invariant under isomorphism of sheaves. -/
theorem HasFiberwiseHilbertPolynomial.of_iso
    {n : ℕ} {T : Scheme.{u}}
    {Q Q' : (Scheme.projectiveSpaceOver n T).Modules}
    {P : Polynomial ℚ} (e : Q ≅ Q')
    (hQ : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    Scheme.HasFiberwiseHilbertPolynomial Q' P := by
  intro K hK s
  apply Scheme.HasHilbertPolynomialOver.iso
    ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n s)).mapIso e)
  exact hQ K hK s

namespace Modules

variable {T : Scheme.{u}} (n : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n T).Modules) (P : Polynomial ℚ)

/-- The pullback of a fixed sheaf on `ℙⁿ_T` to `ℙⁿ_A`, for `A ⟶ T`. -/
abbrev projectiveFamilyAt (A : Over T) : (Scheme.projectiveSpaceOver n A.left).Modules :=
  (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n A.hom)).obj Q

/-- Pullback of the family along a morphism in `Over T` agrees with the family obtained by
pulling back directly from `T`. -/
def projectiveFamilyPullbackIso {A B : Over T} (g : B ⟶ A) :
    (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g.left)).obj
        (projectiveFamilyAt n Q A) ≅
      projectiveFamilyAt n Q B :=
  (Scheme.Modules.pullbackComp
      (Scheme.projectiveSpaceOverMap n g.left)
      (Scheme.projectiveSpaceOverMap n A.hom)).app Q ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverMap_comp n g.left A.hom)).app Q ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg (Scheme.projectiveSpaceOverMap n) (Over.w g))).app Q

/-- The fixed-polynomial projective flattening functor.  Its value on `A ⟶ T` is a
singleton exactly when the pullback of `Q` to `ℙⁿ_A` is flat over `A` and has
fibrewise Hilbert polynomial `P`. -/
def projectiveFlatteningFunctor [Q.IsQuasicoherent] : (Over T)ᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1} (PLift
    ((projectiveFamilyAt n Q A.unop).FlatOver
        (Scheme.projectiveSpaceOverπ n A.unop.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A.unop) P))
  map {A B} g := ↾fun h => by
    let g' : B.unop ⟶ A.unop := g.unop
    have hflat : (projectiveFamilyAt n Q A.unop).FlatOver
        (Scheme.projectiveSpaceOverπ n A.unop.left) := h.down.down.1
    have hHP : Scheme.HasFiberwiseHilbertPolynomial
        (projectiveFamilyAt n Q A.unop) P := h.down.down.2
    haveI : (projectiveFamilyAt n Q A.unop).IsQuasicoherent := inferInstance
    have hflat' :
        ((Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverMap n g'.left)).obj
          (projectiveFamilyAt n Q A.unop)).FlatOver
            (Scheme.projectiveSpaceOverπ n B.unop.left) :=
      Scheme.Modules.FlatOver.pullback_of_isPullback
        (Scheme.projectiveSpaceOverMap n g'.left)
        (Scheme.projectiveSpaceOverπ n B.unop.left)
        (Scheme.projectiveSpaceOverπ n A.unop.left) g'.left
        (Scheme.isPullback_projectiveSpaceOverMap n g'.left).flip
        (projectiveFamilyAt n Q A.unop) hflat
    have hflat'' : (projectiveFamilyAt n Q B.unop).FlatOver
        (Scheme.projectiveSpaceOverπ n B.unop.left) :=
      Scheme.Modules.FlatOver.of_iso (projectiveFamilyPullbackIso n Q g') hflat'
    have hHP' : Scheme.HasFiberwiseHilbertPolynomial
        ((Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverMap n g'.left)).obj
          (projectiveFamilyAt n Q A.unop)) P :=
      Scheme.HasFiberwiseHilbertPolynomial.pullback g'.left hHP
    have hHP'' : Scheme.HasFiberwiseHilbertPolynomial
        (projectiveFamilyAt n Q B.unop) P :=
      Scheme.HasFiberwiseHilbertPolynomial.of_iso
        (projectiveFamilyPullbackIso n Q g') hHP'
    exact ⟨⟨hflat'', hHP''⟩⟩
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _

/-- The finite-rank form of projective flattening for `Q`: the flattening functor is a
finite conjunction of ordinary rank-flattening conditions on the base. -/
def ProjectiveFlatteningHasFiniteRankPresentation [Q.IsQuasicoherent] : Prop :=
  Nonempty (FiniteFlatRankPresentation (projectiveFlatteningFunctor n Q (P := P)))

variable [Q.IsQuasicoherent]
variable (h : ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P))

/-- The projective flattening locus supplied by a finite-rank presentation. -/
def projectiveFlatteningRepresentative : Over T :=
  (Classical.choice h).representative

/-- A finite-rank projective flattening presentation represents the flat,
fixed-Hilbert-polynomial condition. -/
def projectiveFlatteningRepresentableBy :
    (projectiveFlatteningFunctor n Q (P := P)).RepresentableBy
      (projectiveFlatteningRepresentative n Q (P := P) h) :=
  (Classical.choice h).representableBy

/-- The projective flattening representative is immersed in the base. -/
theorem projectiveFlatteningRepresentative_hom_isImmersion :
    IsImmersion (projectiveFlatteningRepresentative n Q (P := P) h).hom :=
  FiniteFlatRankPresentation.representative_hom_isImmersion (Classical.choice h)

end Modules

end AlgebraicGeometry.Scheme

end
