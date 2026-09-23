module

public import StacksAndModuli.API.FpqcMorphismPropertySieve
public import StacksAndModuli.API.RepresentableSheafProperty

/-!
# Refining the property of a representing morphism

Once a sheaf has been represented by a morphism satisfying a weaker property,
this file recovers a stronger property from its local representatives.  Yoneda
full faithfulness identifies the pullback of the global representative with each
local representative, after which ordinary morphism-property descent applies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Suppose representability by `Q` is local and every `J`-covering sieve detects
the stronger morphism property `P`.  If `P ≤ Q`, then representability by `P`
is local as well.

The point is that both the given local `P`-representative and the pullback of the
global `Q`-representative represent the same sheaf.  Yoneda full faithfulness
therefore identifies them in the over-category, allowing `P` to be transported
to the latter before applying the sieve descent hypothesis. -/
theorem representableByProperty_isLocal_of_le
    (J : GrothendieckTopology C)
    (P Q : MorphismProperty C)
    [P.RespectsIso] [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty Q) J]
    (hPQ : P ≤ Q)
    (hdesc : ∀ {S : C} (W : Over S) (R : Sieve S), R ∈ J S →
      (∀ (q : R.arrows.category),
        P ((Over.pullback q.obj.hom).obj W).hom) → P W.hom) :
    Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty P) J := by
  let RP := J.representableByProperty P
  let RQ := J.representableByProperty Q
  let F := J.pseudofunctorOver (Type v)
  letI : RP.IsClosedUnderMapObj := by
    dsimp [RP]
    infer_instance
  letI : RP.IsClosedUnderIsomorphisms := by
    dsimp [RP]
    infer_instance
  refine { of_sieve := ?_ }
  intro S R hR M hM
  have hMQ : ∀ q : R.arrows.category,
      RQ.prop _ ((F.map q.obj.hom.op.toLoc).toFunctor.obj M) := by
    intro q
    obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hM q
    exact ⟨Z, hPQ Z.hom hZ, ⟨eZ⟩⟩
  have hQ : RQ.prop _ M :=
    Pseudofunctor.ObjectProperty.IsLocal.of_sieve R hR M hMQ
  obtain ⟨W, -, ⟨eW⟩⟩ := hQ
  refine ⟨W, hdesc W R hR ?_, ⟨eW⟩⟩
  intro q
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hM q
  let ePull : CategoryTheory.yoneda.obj
        ((Over.pullback q.obj.hom).obj W) ≅
      ((F.map q.obj.hom.op.toLoc).toFunctor.obj M).obj :=
    (Over.mapPullbackAdj q.obj.hom).compYonedaIso.app W ≪≫
      Functor.isoWhiskerLeft (Over.map q.obj.hom).op eW
  let eOver : (Over.pullback q.obj.hom).obj W ≅ Z :=
    Yoneda.fullyFaithful.preimageIso (ePull ≪≫ eZ.symm)
  have hcomp : P (eOver.hom.left ≫ Z.hom) :=
    (P.cancel_left_of_respectsIso eOver.hom.left Z.hom).mpr hZ
  rw [eOver.hom.w] at hcomp
  exact hcomp

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Scheme

open CategoryTheory

/-- For schemes, the abstract refinement theorem follows from the standard
fpqc-sieve descent criterion for morphism properties. -/
theorem representableByProperty_isLocal_of_le_of_fpqc
    (J : GrothendieckTopology Scheme.{u})
    (P Q : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [Q.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty Q) J]
    (hJ : J ≤ fpqcTopology) (hPQ : P ≤ Q) :
    Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty P) J := by
  apply J.representableByProperty_isLocal_of_le P Q hPQ
  intro S W R hR hlocal
  apply MorphismProperty.of_fpqc_sieve (P := P) W.hom R (hJ S hR)
  intro U g hg
  let q : R.arrows.category := R.arrows.categoryMk g hg
  exact hlocal q

end AlgebraicGeometry.Scheme
