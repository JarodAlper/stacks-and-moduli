module

public import StacksAndModuli.API.PseudofunctorCore
public import StacksAndModuli.API.RepresentableSheafProperty
public import StacksAndModuli.API.ArrowCartesianProperty
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Stacks of locally representable sheaves

This module packages the categorical end of effective descent for geometric objects.
If representability by a pullback-stable morphism property `P` is local for a topology
`J`, then the pointwise groupoid of `P`-representable sheaves is a stack whenever sheaves
on the over-sites form a stack.  The universe-raised property
`representableByPropertyULift` is the version applicable to large sites such as schemes:
it represents a sheaf by the usual Yoneda presheaf followed by `uliftFunctor`.

The stack theorem's only geometric input is the locality instance
`Pseudofunctor.ObjectProperty.IsLocal (J.representableByProperty P) J`.
`HasEffectiveRepresentabilityULift` and
`isLocal_representableByPropertyULift_of_effectiveRepresentability` split that input into
existence of a global scheme representative and target-locality of its morphism property.
In particular, the theorem does not assert effective descent for arbitrary schemes: that
assertion is false even for the étale topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The property that a sheaf on the over-site of `X`, valued in a possibly larger
universe of types, is represented by a `P`-morphism to `X`.

The ordinary `representableByProperty` uses `Type v`, the universe of morphisms in `C`.
For a large category such as `Scheme.{u}`, the stack theorem for sheaves naturally uses
the larger universe containing the objects of the site.  This raised version bridges that
universe gap without changing the representing geometric object. -/
def representableByPropertyULift (J : GrothendieckTopology C)
    (P : MorphismProperty C) :
    (J.pseudofunctorOver (Type max v w)).ObjectProperty where
  prop X F := ∃ (Z : Over X.as.unop), P Z.hom ∧
    Nonempty (CategoryTheory.uliftYoneda.{w}.obj Z ≅ F.obj)

instance (J : GrothendieckTopology C) (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] :
    (J.representableByPropertyULift.{w} P).IsClosedUnderMapObj where
  map_obj hF f := by
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hF
    refine ⟨(Over.pullback f.as.unop).obj Z,
      P.pullback_snd Z.hom f.as.unop hZ, ?_⟩
    let e₁ := Functor.isoWhiskerRight
      ((Over.mapPullbackAdj f.as.unop).compYonedaIso.app Z)
      uliftFunctor.{w}
    exact ⟨e₁ ≪≫ Functor.isoWhiskerLeft (Over.map f.as.unop).op e⟩

instance (J : GrothendieckTopology C) (P : MorphismProperty C) :
    (J.representableByPropertyULift.{w} P).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := by
    constructor
    intro F G e hF
    obtain ⟨Z, hZ, ⟨eF⟩⟩ := hF
    exact ⟨Z, hZ, ⟨eF ≪≫ (sheafToPresheaf _ _).mapIso e⟩⟩

/-- Effective representability for sheaves which are locally represented by
`P`-morphisms, without requiring the descended representative itself to satisfy `P`.

This is the genuinely geometric half of effective descent.  The theorem below recovers
the property of the descended structure morphism separately, from locality of `P` at the
target. -/
def HasEffectiveRepresentabilityULift (K : Precoverage C)
    (P : MorphismProperty C) : Prop :=
  ∀ {S : C} (R : Presieve S), R ∈ K S →
    ∀ (M : Sheaf ((K.toGrothendieck).over S) (Type max v w)),
      (∀ ⦃X : C⦄ (f : X ⟶ S), R f →
        ((K.toGrothendieck).representableByPropertyULift.{w} P).prop
          (.mk (op X))
          ((((K.toGrothendieck).pseudofunctorOver (Type max v w)).map
            f.op.toLoc).toFunctor.obj M)) →
      ∃ Z : Over S, Nonempty (CategoryTheory.uliftYoneda.{w}.obj Z ≅ M.obj)

/-- Effective representability together with target-locality of `P` implies locality of
being represented by a `P`-morphism.

The proof compares a chosen local representative with the pullback of the descended
representative.  Full faithfulness of universe-raised Yoneda turns the resulting sheaf
isomorphism into an isomorphism in the over-category, so target-locality transfers `P`
to the descended structure morphism. -/
theorem isLocal_representableByPropertyULift_of_effectiveRepresentability
    (K : Precoverage C) (P : MorphismProperty C)
    [K.IsStableUnderComposition] [K.IsStableUnderBaseChange]
    [K.HasPullbacks] [K.HasIsos]
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget K]
    (hEffective : HasEffectiveRepresentabilityULift.{w} K P) :
    Pseudofunctor.ObjectProperty.IsLocal
      ((K.toGrothendieck).representableByPropertyULift.{w} P)
      K.toGrothendieck := by
  apply Pseudofunctor.ObjectProperty.IsLocal.of_precoverage
    ((K.toGrothendieck).representableByPropertyULift.{w} P) K
  intro S R hR M hM
  obtain ⟨Z, ⟨eZ⟩⟩ := hEffective R hR M hM
  refine ⟨Z, ?_, ⟨eZ⟩⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR
  intro X f _ hf
  obtain ⟨W, hW, ⟨eW⟩⟩ := hM f hf
  let e₁ := Functor.isoWhiskerRight
    ((Over.mapPullbackAdj f).compYonedaIso.app Z) uliftFunctor.{w}
  let ePull : CategoryTheory.uliftYoneda.{w}.obj ((Over.pullback f).obj Z) ≅
      ((((K.toGrothendieck).pseudofunctorOver (Type max v w)).map
        f.op.toLoc).toFunctor.obj M).obj :=
    e₁ ≪≫ Functor.isoWhiskerLeft (Over.map f).op eZ
  let eOver : (Over.pullback f).obj Z ≅ W :=
    (ULiftYoneda.fullyFaithful (Over X)).preimageIso (ePull ≪≫ eW.symm)
  let _ : IsIso eOver.hom.left := by
    change IsIso ((Over.forget X).map eOver.hom)
    infer_instance
  change P ((Over.pullback f).obj Z).hom
  rw [← eOver.hom.w, P.cancel_left_of_respectsIso]
  exact hW

/-- The pointwise groupoid of sheaves represented by `P`-morphisms is a stack once
representability by `P` is local.

This is the reusable categorical reduction behind moduli-stack descent arguments:
effective descent of the geometric objects is isolated in the
`Pseudofunctor.ObjectProperty.IsLocal` hypothesis, while descent of sheaves, passage to a
full subpseudofunctor, and passage to its pointwise core are formal. -/
theorem isStack_core_fullsubcategory_representableByProperty
    (J : GrothendieckTopology C) (P : MorphismProperty C)
    [P.IsStableUnderBaseChange]
    [(J.pseudofunctorOver (Type v)).IsStack J]
    [Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty P) J] :
    ((J.representableByProperty P).fullsubcategory).core.IsStack J := by
  let _ : (J.representableByProperty P).fullsubcategory.IsStack J :=
    Pseudofunctor.ObjectProperty.fullsubcategory_isStack
      (J.representableByProperty P)
  exact Pseudofunctor.core_isStack _

/-- Universe-raised version of
`isStack_core_fullsubcategory_representableByProperty`.

This is the form used on the big site of schemes: the ambient sheaf pseudofunctor can be
taken in a universe large enough to satisfy the sheaf-gluing theorem, while the local
representatives remain ordinary scheme morphisms. -/
theorem isStack_core_fullsubcategory_representableByPropertyULift
    (J : GrothendieckTopology C) (P : MorphismProperty C)
    [P.IsStableUnderBaseChange]
    [(J.pseudofunctorOver (Type max v w)).IsStack J]
    [Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByPropertyULift.{w} P) J] :
    ((J.representableByPropertyULift.{w} P).fullsubcategory).core.IsStack J := by
  let _ : (J.representableByPropertyULift.{w} P).fullsubcategory.IsStack J :=
    Pseudofunctor.ObjectProperty.fullsubcategory_isStack
      (J.representableByPropertyULift.{w} P)
  exact Pseudofunctor.core_isStack _

/-- The comparison statement which transfers the stack of `P`-representable sheaves
to the cartesian-arrow presentation of the same geometric objects.

Relative Yoneda identifies the total category of the pointwise core on the left with
`arrowCartesianProperty P`. Keeping that comparison as a predicate separates the general
sheaf-stack reduction from the scheme-specific construction of the equivalence. -/
def RepresentableSheafStackBridge (J : GrothendieckTopology C)
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] : Prop :=
  ((J.representableByPropertyULift.{w} P).fullsubcategory).core.IsStack J →
    BasedCategory.IsStack J (arrowCartesianProperty P)

/-- Local representability plus the relative-Yoneda stack bridge implies that cartesian
`P`-arrows form a stack. -/
theorem isStack_arrowCartesianProperty_of_representableByPropertyULift_isLocal
    (J : GrothendieckTopology C) (P : MorphismProperty C)
    [P.IsStableUnderBaseChange]
    [(J.pseudofunctorOver (Type max v w)).IsStack J]
    [Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByPropertyULift.{w} P) J]
    (hbridge : RepresentableSheafStackBridge.{w, v, u} J P) :
    BasedCategory.IsStack J (arrowCartesianProperty P) :=
  hbridge (J.isStack_core_fullsubcategory_representableByPropertyULift P)

end CategoryTheory.GrothendieckTopology
