module

public import StacksAndModuli.API.IrreducibleComponentGeometricGenus

/-!
# Normalization and irreducible-component coproducts

Mathlib defines the normalization of a scheme relative to a quasi-compact,
quasi-separated morphism.  This file proves that relative normalization commutes with
finite coproducts in the source.  It then applies that result to the normalization of a
reduced scheme in the product of its component function fields.

For an irreducible component `Z` of a reduced scheme `X`,
`relativeComponentNormalization X Z` is the normalization of `X` in the generic-point
stalk of `Z`.  Its normalization map factors through the reduced induced subscheme on
`Z`.  The generic stalk of this reduced component is canonically the ambient generic
stalk, so the relative component normalization agrees with the ordinary normalization of
the reduced component.  Taking the coproduct over all components recovers `X.normalization`.

## Main results

* `AlgebraicGeometry.IsIntegralHom.sigmaDesc_of_finite`: a finite coproduct of integral
  morphisms with common target is integral.
* `AlgebraicGeometry.Scheme.Hom.normalizationSigmaIso`: relative normalization commutes
  with finite coproducts in the source.
* `AlgebraicGeometry.Scheme.relativeComponentNormalizationIsoNormalizationInReducedComponent`:
  the relative component normalization may be computed after passing to the reduced
  induced component.
* `AlgebraicGeometry.Scheme.relativeComponentNormalizationIsoReducedComponentNormalization`:
  the relative component normalization is isomorphic to the ordinary normalization of
  the reduced induced component.
* `AlgebraicGeometry.Scheme.relativeComponentNormalizationSigmaIso`: the normalization
  in all component function fields is the coproduct of the componentwise relative
  normalizations.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The coproduct indexed by `Option α` is the coproduct of the `some` summands and
the `none` summand. -/
noncomputable def Scheme.sigmaOptionIso {α : Type u} (X : Option α → Scheme.{u}) :
    (∐ fun a : α ↦ X (some a)) ⨿ X none ≅ ∐ X where
  hom := coprod.desc
    (Sigma.desc fun a ↦ Sigma.ι X (some a))
    (Sigma.ι X none)
  inv := Sigma.desc fun o ↦ match o with
    | none => coprod.inr
    | some a => Sigma.ι (fun a : α ↦ X (some a)) a ≫ coprod.inl
  hom_inv_id := by
    apply coprod.hom_ext
    · apply Sigma.hom_ext
      intro a
      simp
    · simp
  inv_hom_id := by
    apply Sigma.hom_ext
    intro o
    cases o <;> simp

@[reassoc (attr := simp)]
lemma Scheme.sigmaOptionIso_inl_hom {α : Type u} (X : Option α → Scheme.{u}) :
    coprod.inl ≫ (Scheme.sigmaOptionIso X).hom =
      Sigma.desc (fun a ↦ Sigma.ι X (some a)) := by
  simp [Scheme.sigmaOptionIso]

@[reassoc (attr := simp)]
lemma Scheme.sigmaOptionIso_inr_hom {α : Type u} (X : Option α → Scheme.{u}) :
    coprod.inr ≫ (Scheme.sigmaOptionIso X).hom = Sigma.ι X none := by
  simp [Scheme.sigmaOptionIso]

/-- A finite coproduct of integral morphisms is integral. -/
theorem IsIntegralHom.sigmaDesc_of_finite {ι : Type u} [Finite ι]
    {X : ι → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsIntegralHom (f i)) : IsIntegralHom (Sigma.desc f) := by
  let P : Type u → Prop := fun ι ↦
    ∀ (X : ι → Scheme.{u}) (Y : Scheme.{u}) (f : ∀ i, X i ⟶ Y),
      (∀ i, IsIntegralHom (f i)) → IsIntegralHom (Sigma.desc f)
  refine Finite.induction_empty_option (P := P) (α := ι) ?_ ?_ ?_ X Y f hf
  · intro α β e hα X Y f hf
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsIntegralHom)
      (Sigma.reindex e X).hom]
    have heq : (Sigma.reindex e X).hom ≫ Sigma.desc f =
        Sigma.desc (fun a ↦ f (e a)) := by
      apply Sigma.hom_ext
      intro a
      calc
        Sigma.ι (X ∘ e) a ≫ (Sigma.reindex e X).hom ≫ Sigma.desc f =
            Sigma.ι X (e a) ≫ Sigma.desc f := by
          rw [← Category.assoc, Sigma.ι_reindex_hom]
        _ = f (e a) := Limits.Sigma.ι_desc f (e a)
        _ = Sigma.ι (X ∘ e) a ≫ Sigma.desc (fun a ↦ f (e a)) :=
          (Limits.Sigma.ι_desc (fun a : α ↦ f (e a)) a).symm
    rw [heq]
    exact hα (X ∘ e) Y (fun a ↦ f (e a)) (fun a ↦ hf (e a))
  · intro X Y f hf
    let _ : IsEmpty (∐ X : Scheme.{u}) :=
      ⟨fun x ↦ ((sigmaMk X).symm x).1.elim⟩
    infer_instance
  · intro α _ hα X Y f hf
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsIntegralHom)
      (Scheme.sigmaOptionIso X).hom]
    have heq : (Scheme.sigmaOptionIso X).hom ≫ Sigma.desc f =
        coprod.desc (Sigma.desc (fun a ↦ f (some a))) (f none) := by
      apply coprod.hom_ext
      · apply Sigma.hom_ext
        intro a
        simp
      · simp
    rw [heq]
    let _ : IsIntegralHom (Sigma.desc (fun a ↦ f (some a))) :=
      hα (fun a ↦ X (some a)) Y (fun a ↦ f (some a)) (fun a ↦ hf (some a))
    let _ : IsIntegralHom (f none) := hf none
    infer_instance

namespace Scheme.Hom

variable {A B : Scheme.{u}}

/-- The relative normalization map has the same closed image as the original morphism. -/
lemma closure_range_fromNormalization (f : A ⟶ B)
    [QuasiCompact f] [QuasiSeparated f] :
    closure (Set.range f.fromNormalization) = closure (Set.range f) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ closure (Set.range f.toNormalization) :=
      f.toNormalization.denseRange z
    have hz' : f.fromNormalization z ∈
        f.fromNormalization '' closure (Set.range f.toNormalization) :=
      ⟨z, hz, rfl⟩
    have h := image_closure_subset_closure_image
      f.fromNormalization.continuous hz'
    rw [← Set.range_comp] at h
    have hmaps : (⇑f.fromNormalization ∘ ⇑f.toNormalization) = ⇑f := by
      funext x
      change (f.toNormalization ≫ f.fromNormalization) x = f x
      rw [Scheme.Hom.toNormalization_fromNormalization]
    rwa [hmaps] at h
  · apply closure_mono
    rintro _ ⟨x, rfl⟩
    refine ⟨f.toNormalization x, ?_⟩
    change (f.toNormalization ≫ f.fromNormalization) x = f x
    rw [Scheme.Hom.toNormalization_fromNormalization]

variable {ι : Type u} [Finite ι] {X : ι → Scheme.{u}} {Y : Scheme.{u}}
variable (f : ∀ i, X i ⟶ Y)
variable [∀ i, QuasiCompact (f i)] [∀ i, QuasiSeparated (f i)]
variable [QuasiCompact (Sigma.desc f)] [QuasiSeparated (Sigma.desc f)]

/-- The map from the coproduct of the componentwise relative normalizations to the
relative normalization of the whole coproduct. -/
noncomputable def normalizationSigmaTo :
    (∐ fun i ↦ (f i).normalization) ⟶ (Sigma.desc f).normalization :=
  Sigma.desc fun i ↦
    (f i).normalizationDesc
      (Sigma.ι X i ≫ (Sigma.desc f).toNormalization)
      (Sigma.desc f).fromNormalization (by simp)

/-- The coproduct of the componentwise relative normalization maps. -/
noncomputable def sigmaNormalizationMap :
    (∐ fun i ↦ (f i).normalization) ⟶ Y :=
  Sigma.desc fun i ↦ (f i).fromNormalization

/-- The coproduct of the componentwise relative normalization maps is integral. -/
noncomputable instance sigmaNormalizationMap_isIntegral :
    IsIntegralHom (sigmaNormalizationMap f) :=
  IsIntegralHom.sigmaDesc_of_finite _ (fun _ ↦ inferInstance)

omit [Finite ι] [QuasiCompact (Sigma.desc f)]
    [QuasiSeparated (Sigma.desc f)] in
@[reassoc (attr := simp)]
lemma ι_sigmaNormalizationMap (i : ι) :
    Sigma.ι (fun i ↦ (f i).normalization) i ≫ sigmaNormalizationMap f =
      (f i).fromNormalization := by
  simp [sigmaNormalizationMap]

/-- The canonical map from the whole relative normalization to the coproduct of the
componentwise relative normalizations. -/
noncomputable def normalizationToSigma :
    (Sigma.desc f).normalization ⟶ ∐ fun i ↦ (f i).normalization := by
  exact (Sigma.desc f).normalizationDesc
    (Limits.Sigma.map fun i ↦ (f i).toNormalization)
    (sigmaNormalizationMap f) (by
      apply Sigma.hom_ext
      intro i
      simp [sigmaNormalizationMap])

omit [Finite ι] in
@[reassoc (attr := simp)]
lemma toNormalization_ι_normalizationSigmaTo (i : ι) :
    (f i).toNormalization ≫ Sigma.ι (fun i ↦ (f i).normalization) i ≫
      normalizationSigmaTo f =
    Sigma.ι X i ≫ (Sigma.desc f).toNormalization := by
  simp [normalizationSigmaTo]

omit [Finite ι] in
@[reassoc (attr := simp)]
lemma ι_normalizationSigmaTo_fromNormalization (i : ι) :
    Sigma.ι (fun i ↦ (f i).normalization) i ≫ normalizationSigmaTo f ≫
      (Sigma.desc f).fromNormalization =
    (f i).fromNormalization := by
  simp [normalizationSigmaTo]

omit [Finite ι] in
@[reassoc (attr := simp)]
lemma normalizationSigmaTo_fromNormalization :
    normalizationSigmaTo f ≫ (Sigma.desc f).fromNormalization =
      sigmaNormalizationMap f := by
  apply Sigma.hom_ext
  intro i
  simp

omit [Finite ι] in
@[reassoc (attr := simp)]
lemma sigmaMap_toNormalization_normalizationSigmaTo :
    Limits.Sigma.map (fun i ↦ (f i).toNormalization) ≫ normalizationSigmaTo f =
      (Sigma.desc f).toNormalization := by
  apply Sigma.hom_ext
  intro i
  simp

@[reassoc (attr := simp)]
lemma toNormalization_normalizationToSigma :
    (Sigma.desc f).toNormalization ≫ normalizationToSigma f =
      Limits.Sigma.map (fun i ↦ (f i).toNormalization) := by
  simp [normalizationToSigma]

@[reassoc (attr := simp)]
lemma normalizationToSigma_sigmaNormalizationMap :
    normalizationToSigma f ≫ sigmaNormalizationMap f =
      (Sigma.desc f).fromNormalization := by
  simp [normalizationToSigma]

/-- Relative normalization commutes with finite coproducts in the source. -/
noncomputable def normalizationSigmaIso :
    (∐ fun i ↦ (f i).normalization) ≅ (Sigma.desc f).normalization where
  hom := normalizationSigmaTo f
  inv := normalizationToSigma f
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    refine Scheme.Hom.normalization.hom_ext _ _ _
      (sigmaNormalizationMap f) ?_ ?_ ?_
    all_goals simp [Category.assoc]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _
      (Sigma.desc f).fromNormalization ?_ ?_ ?_
    all_goals simp [Category.assoc]

/-- Relative normalizations are isomorphic when their source morphisms differ by an
isomorphism. -/
noncomputable def normalizationIsoOfIsoSource
    {A A' B : Scheme.{u}} (g : A' ⟶ B) (f : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact f] [QuasiSeparated f]
    (e : A' ≅ A) (h : g = e.hom ≫ f) :
    g.normalization ≅ f.normalization where
  hom := g.normalizationDesc
    (e.hom ≫ f.toNormalization) f.fromNormalization (by simp [h])
  inv := f.normalizationDesc
    (e.inv ≫ g.toNormalization) g.fromNormalization (by
      simp [h, Category.assoc])
  hom_inv_id := by
    refine normalization.hom_ext _ _ _ g.fromNormalization ?_ ?_ ?_
    all_goals simp [Category.assoc]
  inv_hom_id := by
    refine normalization.hom_ext _ _ _ f.fromNormalization ?_ ?_ ?_
    all_goals simp [Category.assoc]

/-- The source-change isomorphism commutes with the relative normalization maps. -/
@[reassoc (attr := simp)]
lemma normalizationIsoOfIsoSource_hom_fromNormalization
    {A A' B : Scheme.{u}} (g : A' ⟶ B) (f : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact f] [QuasiSeparated f]
    (e : A' ≅ A) (h : g = e.hom ≫ f) :
    (normalizationIsoOfIsoSource g f e h).hom ≫ f.fromNormalization =
      g.fromNormalization := by
  simp [normalizationIsoOfIsoSource]

end Scheme.Hom

namespace Scheme

variable (X : Scheme.{u}) [IsReduced X]

/-- The kernel ideal sheaf of a quasi-compact morphism with reduced source is radical. -/
theorem Hom.radical_ker_eq_self_of_isReduced {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : f.ker.radical = f.ker := by
  ext U x
  rw [IdealSheafData.radical_ideal, Hom.ker_apply]
  constructor
  · rintro ⟨n, hn⟩
    rw [RingHom.mem_ker] at hn ⊢
    apply IsReduced.eq_zero _
    exact ⟨n, (map_pow (f.app U).hom x n).symm.trans hn⟩
  · intro hx
    exact ⟨1, by simpa using hx⟩

/-- The normalization of `X` in the function field of one irreducible component. -/
noncomputable abbrev relativeComponentNormalization
    (Z : irreducibleComponents X) : Scheme.{u} :=
  (X.fromSpecStalk Z.property.1.genericPoint).normalization

/-- The integral map from the relative normalization at one component to `X`. -/
noncomputable abbrev relativeComponentNormalizationMap
    (Z : irreducibleComponents X) : X.relativeComponentNormalization Z ⟶ X :=
  (X.fromSpecStalk Z.property.1.genericPoint).fromNormalization

/-- A relative component normalization is an integral scheme. -/
noncomputable instance relativeComponentNormalization_isIntegral
    (Z : irreducibleComponents X) :
    IsIntegral (X.relativeComponentNormalization Z) := by
  let _ : IsDomain (X.presheaf.stalk Z.property.1.genericPoint) :=
    (X.componentGenericStalk_isField Z).isDomain
  dsimp only [relativeComponentNormalization]
  infer_instance

/-- A relative component normalization inherits any specified map from `X`. -/
noncomputable instance relativeComponentNormalization_over
    {S : Scheme.{u}} [X.Over S] (Z : irreducibleComponents X) :
    (X.relativeComponentNormalization Z).Over S :=
  ⟨X.relativeComponentNormalizationMap Z ≫ (X ↘ S)⟩

/-- The relative component normalization map respects the inherited map to `S`. -/
@[simp]
lemma relativeComponentNormalizationMap_isOver
    {S : Scheme.{u}} [X.Over S] (Z : irreducibleComponents X) :
    (X.relativeComponentNormalizationMap Z).IsOver S :=
  ⟨rfl⟩

/-- A relative component normalization is universally closed over every base over
which `X` is universally closed. -/
noncomputable instance relativeComponentNormalization_universallyClosed
    {S : Scheme.{u}} [X.Over S] [UniversallyClosed (X ↘ S)]
    (Z : irreducibleComponents X) :
    UniversallyClosed (X.relativeComponentNormalization Z ↘ S) := by
  change UniversallyClosed
    (X.relativeComponentNormalizationMap Z ≫ (X ↘ S))
  infer_instance

/-- The generic-point morphism of an irreducible component is quasi-compact on a reduced
scheme. -/
instance componentFromSpecStalk_quasiCompact (Z : irreducibleComponents X) :
    QuasiCompact (X.fromSpecStalk Z.property.1.genericPoint) := by
  exact ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

/-- The generic-point morphism of an irreducible component is quasi-separated. -/
instance componentFromSpecStalk_quasiSeparated (Z : irreducibleComponents X) :
    QuasiSeparated (X.fromSpecStalk Z.property.1.genericPoint) := by
  infer_instance

/-- The closed image of a component generic-point morphism is that component. -/
lemma closure_range_componentFromSpecStalk (Z : irreducibleComponents X) :
    closure (Set.range (X.fromSpecStalk Z.property.1.genericPoint)) = Z.1 := by
  let _ : IsField (X.presheaf.stalk Z.property.1.genericPoint) :=
    X.componentGenericStalk_isField Z
  let _ : Subsingleton (Spec (X.presheaf.stalk Z.property.1.genericPoint)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr
      (X.componentGenericStalk_isField Z)
  have hrange : Set.range (X.fromSpecStalk Z.property.1.genericPoint) =
      {Z.property.1.genericPoint} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [show y = IsLocalRing.closedPoint
        (X.presheaf.stalk Z.property.1.genericPoint) from Subsingleton.elim _ _]
      exact Set.mem_singleton_iff.mpr Scheme.fromSpecStalk_closedPoint
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨IsLocalRing.closedPoint
        (X.presheaf.stalk Z.property.1.genericPoint),
          Scheme.fromSpecStalk_closedPoint⟩
  rw [hrange]
  exact Z.property.1.closure_genericPoint
    (isClosed_of_mem_irreducibleComponents Z.1 Z.property)

/-- The kernel support of a component-relative normalization map is the component. -/
lemma support_ker_relativeComponentNormalizationMap
    (Z : irreducibleComponents X) :
    (X.relativeComponentNormalizationMap Z).ker.support =
      X.irreducibleComponentClosed Z := by
  ext x
  change x ∈ ((X.relativeComponentNormalizationMap Z).ker.support : Set X) ↔
    x ∈ Z.1
  rw [Hom.support_ker]
  change x ∈ closure (Set.range
    (X.fromSpecStalk Z.property.1.genericPoint).fromNormalization) ↔ x ∈ Z.1
  rw [Hom.closure_range_fromNormalization,
    X.closure_range_componentFromSpecStalk Z]

/-- The kernel of a component-relative normalization map is the vanishing ideal of
that component. -/
lemma ker_relativeComponentNormalizationMap
    (Z : irreducibleComponents X) :
    (X.relativeComponentNormalizationMap Z).ker =
      IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z) := by
  calc
    (X.relativeComponentNormalizationMap Z).ker =
        (X.relativeComponentNormalizationMap Z).ker.radical :=
      (Hom.radical_ker_eq_self_of_isReduced
        (X.relativeComponentNormalizationMap Z)).symm
    _ = IdealSheafData.vanishingIdeal
        (X.relativeComponentNormalizationMap Z).ker.support :=
      (IdealSheafData.vanishingIdeal_support
        (I := (X.relativeComponentNormalizationMap Z).ker)).symm
    _ = IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z) := by
      rw [X.support_ker_relativeComponentNormalizationMap Z]

/-- The relative normalization in one component function field factors canonically
through the reduced induced component. -/
noncomputable def relativeComponentNormalizationToReducedComponent
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalization Z ⟶ X.reducedIrreducibleComponent Z :=
  IsClosedImmersion.lift (X.reducedIrreducibleComponentι Z)
    (X.relativeComponentNormalizationMap Z) (by
      dsimp only [reducedIrreducibleComponentι]
      rw [IdealSheafData.ker_subschemeι,
        X.ker_relativeComponentNormalizationMap Z])

@[reassoc (attr := simp)]
lemma relativeComponentNormalizationToReducedComponent_ι
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalizationToReducedComponent Z ≫
      X.reducedIrreducibleComponentι Z =
    X.relativeComponentNormalizationMap Z :=
  IsClosedImmersion.lift_fac _ _ _

/-- The factor from a component-relative normalization to the reduced induced
component is integral. -/
noncomputable instance relativeComponentNormalizationToReducedComponent_isIntegral
    (Z : irreducibleComponents X) :
    IsIntegralHom (X.relativeComponentNormalizationToReducedComponent Z) := by
  let _ : IsIntegralHom
      (X.relativeComponentNormalizationToReducedComponent Z ≫
        X.reducedIrreducibleComponentι Z) := by
    rw [X.relativeComponentNormalizationToReducedComponent_ι Z]
    infer_instance
  exact IsIntegralHom.of_comp _ (X.reducedIrreducibleComponentι Z)

/-- The component generic-point morphism factored through the reduced induced
component. -/
noncomputable def componentGenericToReducedComponent
    (Z : irreducibleComponents X) :
    Spec (X.presheaf.stalk Z.property.1.genericPoint) ⟶
      X.reducedIrreducibleComponent Z :=
  (X.fromSpecStalk Z.property.1.genericPoint).toNormalization ≫
    X.relativeComponentNormalizationToReducedComponent Z

@[reassoc (attr := simp)]
lemma componentGenericToReducedComponent_ι
    (Z : irreducibleComponents X) :
    X.componentGenericToReducedComponent Z ≫
      X.reducedIrreducibleComponentι Z =
    X.fromSpecStalk Z.property.1.genericPoint := by
  simp [componentGenericToReducedComponent]

/-- The component generic-point map into the reduced induced component is
quasi-compact. -/
noncomputable instance componentGenericToReducedComponent_quasiCompact
    (Z : irreducibleComponents X) :
    QuasiCompact (X.componentGenericToReducedComponent Z) := by
  dsimp only [componentGenericToReducedComponent]
  infer_instance

/-- The component generic-point map into the reduced induced component is
quasi-separated. -/
noncomputable instance componentGenericToReducedComponent_quasiSeparated
    (Z : irreducibleComponents X) :
    QuasiSeparated (X.componentGenericToReducedComponent Z) := by
  dsimp only [componentGenericToReducedComponent]
  infer_instance

/-- The canonical map from the relative component normalization to the normalization
of the reduced component in the same displayed generic-point morphism. -/
noncomputable def relativeComponentNormalizationToNormalizationInReducedComponent
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalization Z ⟶
      (X.componentGenericToReducedComponent Z).normalization :=
  (X.fromSpecStalk Z.property.1.genericPoint).normalizationDesc
    (X.componentGenericToReducedComponent Z).toNormalization
    ((X.componentGenericToReducedComponent Z).fromNormalization ≫
      X.reducedIrreducibleComponentι Z) (by simp)

/-- The canonical map back from the normalization of the reduced component in the
displayed ambient function field. -/
noncomputable def normalizationInReducedComponentToRelativeComponentNormalization
    (Z : irreducibleComponents X) :
    (X.componentGenericToReducedComponent Z).normalization ⟶
      X.relativeComponentNormalization Z :=
  (X.componentGenericToReducedComponent Z).normalizationDesc
    (X.fromSpecStalk Z.property.1.genericPoint).toNormalization
    (X.relativeComponentNormalizationToReducedComponent Z) rfl

@[reassoc (attr := simp)]
lemma toNormalization_relativeComponentNormalizationToNormalizationInReducedComponent
    (Z : irreducibleComponents X) :
    (X.fromSpecStalk Z.property.1.genericPoint).toNormalization ≫
      X.relativeComponentNormalizationToNormalizationInReducedComponent Z =
    (X.componentGenericToReducedComponent Z).toNormalization := by
  simp [relativeComponentNormalizationToNormalizationInReducedComponent]

@[reassoc (attr := simp)]
lemma relativeComponentNormalizationToNormalizationInReducedComponent_fromNormalization_ι
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
      (X.componentGenericToReducedComponent Z).fromNormalization ≫
        X.reducedIrreducibleComponentι Z =
    X.relativeComponentNormalizationMap Z := by
  simp [relativeComponentNormalizationToNormalizationInReducedComponent,
    relativeComponentNormalizationMap]

@[reassoc (attr := simp)]
lemma toNormalization_normalizationInReducedComponentToRelativeComponentNormalization
    (Z : irreducibleComponents X) :
    (X.componentGenericToReducedComponent Z).toNormalization ≫
      X.normalizationInReducedComponentToRelativeComponentNormalization Z =
    (X.fromSpecStalk Z.property.1.genericPoint).toNormalization := by
  simp [normalizationInReducedComponentToRelativeComponentNormalization]

@[reassoc (attr := simp)]
lemma normalizationInReducedComponentToRelativeComponentNormalization_toReducedComponent
    (Z : irreducibleComponents X) :
    X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
      X.relativeComponentNormalizationToReducedComponent Z =
    (X.componentGenericToReducedComponent Z).fromNormalization := by
  simp [normalizationInReducedComponentToRelativeComponentNormalization]

/-- Normalizing `X` in one component function field agrees with normalizing the
reduced induced component in that same displayed generic-point morphism. -/
noncomputable def relativeComponentNormalizationIsoNormalizationInReducedComponent
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalization Z ≅
      (X.componentGenericToReducedComponent Z).normalization where
  hom := X.relativeComponentNormalizationToNormalizationInReducedComponent Z
  inv := X.normalizationInReducedComponentToRelativeComponentNormalization Z
  hom_inv_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _
      (X.relativeComponentNormalizationMap Z) ?_ ?_ ?_
    · simp
    · calc
        X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
            X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
              X.relativeComponentNormalizationMap Z =
          X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
            X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
              (X.relativeComponentNormalizationToReducedComponent Z ≫
                X.reducedIrreducibleComponentι Z) :=
              congrArg (fun t ↦
                X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
                  X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫ t)
                (X.relativeComponentNormalizationToReducedComponent_ι Z).symm
        _ = X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
            (((X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
              X.relativeComponentNormalizationToReducedComponent Z) ≫
                X.reducedIrreducibleComponentι Z)) :=
          congrArg
            (fun t ↦ X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫ t)
            (Category.assoc _ _ _).symm
        _ = X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
            ((X.componentGenericToReducedComponent Z).fromNormalization ≫
              X.reducedIrreducibleComponentι Z) :=
          congrArg
            (fun t ↦ X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
              (t ≫ X.reducedIrreducibleComponentι Z))
            (X.normalizationInReducedComponentToRelativeComponentNormalization_toReducedComponent Z)
        _ = X.relativeComponentNormalizationMap Z :=
          X.relativeComponentNormalizationToNormalizationInReducedComponent_fromNormalization_ι Z
    · simp
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _
      (X.componentGenericToReducedComponent Z).fromNormalization ?_ ?_ ?_
    · simp
    · rw [← cancel_mono (X.reducedIrreducibleComponentι Z)]
      calc
        X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
            X.relativeComponentNormalizationToNormalizationInReducedComponent Z ≫
              (X.componentGenericToReducedComponent Z).fromNormalization ≫
                X.reducedIrreducibleComponentι Z =
          X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
            X.relativeComponentNormalizationMap Z :=
          congrArg
            (fun t ↦ X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫ t)
            (X.relativeComponentNormalizationToNormalizationInReducedComponent_fromNormalization_ι
              Z)
        _ = X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫
            X.relativeComponentNormalizationToReducedComponent Z ≫
              X.reducedIrreducibleComponentι Z :=
          congrArg
            (fun t ↦ X.normalizationInReducedComponentToRelativeComponentNormalization Z ≫ t)
            (X.relativeComponentNormalizationToReducedComponent_ι Z).symm
        _ = (X.componentGenericToReducedComponent Z).fromNormalization ≫
            X.reducedIrreducibleComponentι Z :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun t ↦ t ≫ X.reducedIrreducibleComponentι Z)
              (X.normalizationInReducedComponentToRelativeComponentNormalization_toReducedComponent
                Z))
    · simp

/-- The comparison with normalization inside the reduced component commutes with the
maps to that component. -/
@[reassoc (attr := simp)]
lemma relativeComponentNormalizationIsoNormalizationInReducedComponent_hom_fromNormalization
    (Z : irreducibleComponents X) :
    (X.relativeComponentNormalizationIsoNormalizationInReducedComponent Z).hom ≫
      (X.componentGenericToReducedComponent Z).fromNormalization =
        X.relativeComponentNormalizationToReducedComponent Z := by
  rw [← cancel_mono (X.reducedIrreducibleComponentι Z)]
  calc
    ((X.relativeComponentNormalizationIsoNormalizationInReducedComponent Z).hom ≫
        (X.componentGenericToReducedComponent Z).fromNormalization) ≫
          X.reducedIrreducibleComponentι Z =
      (X.relativeComponentNormalizationIsoNormalizationInReducedComponent Z).hom ≫
        (X.componentGenericToReducedComponent Z).fromNormalization ≫
          X.reducedIrreducibleComponentι Z := Category.assoc _ _ _
    _ = X.relativeComponentNormalizationMap Z :=
      X.relativeComponentNormalizationToNormalizationInReducedComponent_fromNormalization_ι Z
    _ = X.relativeComponentNormalizationToReducedComponent Z ≫
        X.reducedIrreducibleComponentι Z :=
      (X.relativeComponentNormalizationToReducedComponent_ι Z).symm

/-- The normalization in all component function fields is the finite coproduct of the
relative normalizations in the individual component function fields. -/
noncomputable def relativeComponentNormalizationSigmaIso
    [Finite (irreducibleComponents X)] :
    (∐ fun Z : irreducibleComponents X ↦ X.relativeComponentNormalization Z) ≅
      X.normalization := by
  let f := fun Z : irreducibleComponents X ↦
    X.fromSpecStalk Z.property.1.genericPoint
  let _ : QuasiCompact (Sigma.desc f) := by
    change QuasiCompact X.componentGenericMap
    infer_instance
  let _ : QuasiSeparated (Sigma.desc f) := by
    change QuasiSeparated X.componentGenericMap
    infer_instance
  change (∐ fun Z : irreducibleComponents X ↦ (f Z).normalization) ≅
    (Sigma.desc f).normalization
  exact Scheme.Hom.normalizationSigmaIso f

/-- The componentwise coproduct isomorphism commutes with the normalization maps to
`X`. -/
@[reassoc (attr := simp)]
lemma relativeComponentNormalizationSigmaIso_hom_normalizationMap
    [Finite (irreducibleComponents X)] :
    X.relativeComponentNormalizationSigmaIso.hom ≫ X.normalizationMap =
      Sigma.desc (fun Z : irreducibleComponents X ↦
        X.relativeComponentNormalizationMap Z) := by
  let f := fun Z : irreducibleComponents X ↦
    X.fromSpecStalk Z.property.1.genericPoint
  let _ : QuasiCompact (Sigma.desc f) := by
    change QuasiCompact X.componentGenericMap
    infer_instance
  let _ : QuasiSeparated (Sigma.desc f) := by
    change QuasiSeparated X.componentGenericMap
    infer_instance
  change (Hom.normalizationSigmaIso f).hom ≫
      (Sigma.desc f).fromNormalization =
    Sigma.desc (fun Z : irreducibleComponents X ↦
      (f Z).fromNormalization)
  exact Hom.normalizationSigmaTo_fromNormalization f

/-- On a component summand, the coproduct isomorphism followed by the normalization map
is the relative component normalization map. -/
@[reassoc (attr := simp)]
lemma ι_relativeComponentNormalizationSigmaIso_hom_normalizationMap
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    Sigma.ι (fun W : irreducibleComponents X ↦
      X.relativeComponentNormalization W) Z ≫
        X.relativeComponentNormalizationSigmaIso.hom ≫ X.normalizationMap =
    X.relativeComponentNormalizationMap Z := by
  rw [X.relativeComponentNormalizationSigmaIso_hom_normalizationMap]
  simp

/-- The inverse componentwise coproduct isomorphism carries the coproduct of the
component normalization maps to the normalization map of `X`. -/
@[reassoc (attr := simp)]
lemma relativeComponentNormalizationSigmaIso_inv_sigmaDesc
    [Finite (irreducibleComponents X)] :
    X.relativeComponentNormalizationSigmaIso.inv ≫
      Sigma.desc (fun Z : irreducibleComponents X ↦
        X.relativeComponentNormalizationMap Z) = X.normalizationMap := by
  calc
    X.relativeComponentNormalizationSigmaIso.inv ≫
        Sigma.desc (fun Z : irreducibleComponents X ↦
          X.relativeComponentNormalizationMap Z) =
      X.relativeComponentNormalizationSigmaIso.inv ≫
        (X.relativeComponentNormalizationSigmaIso.hom ≫
          X.normalizationMap) := congrArg
            (fun t ↦ X.relativeComponentNormalizationSigmaIso.inv ≫ t)
            X.relativeComponentNormalizationSigmaIso_hom_normalizationMap.symm
    _ = (X.relativeComponentNormalizationSigmaIso.inv ≫
        X.relativeComponentNormalizationSigmaIso.hom) ≫
          X.normalizationMap := (Category.assoc _ _ _).symm
    _ = X.normalizationMap := by simp

/-- The componentwise coproduct isomorphism, bundled over every base over which `X`
is given.  The source and target structure maps are induced by their maps to `X`. -/
noncomputable def relativeComponentNormalizationSigmaOverIso
    {S : Scheme.{u}} [X.Over S] [Finite (irreducibleComponents X)] :
    Over.mk (Sigma.desc fun Z : irreducibleComponents X ↦
      X.relativeComponentNormalizationMap Z ≫ (X ↘ S)) ≅
        Over.mk (X.normalizationMap ≫ (X ↘ S)) :=
  Over.isoMk X.relativeComponentNormalizationSigmaIso (by
    change X.relativeComponentNormalizationSigmaIso.hom ≫
        (X.normalizationMap ≫ (X ↘ S)) =
      Sigma.desc (fun Z : irreducibleComponents X ↦
        X.relativeComponentNormalizationMap Z ≫ (X ↘ S))
    rw [← Category.assoc,
      X.relativeComponentNormalizationSigmaIso_hom_normalizationMap]
    apply Sigma.hom_ext
    intro Z
    simp)

/-- An integral scheme has a unique irreducible component. -/
noncomputable instance irreducibleComponents_unique_of_isIntegral
    (C : Scheme.{u}) [IsIntegral C] : Unique (irreducibleComponents C) := by
  let Z : irreducibleComponents C := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton Set.univ⟩
  exact
    { default := Z
      uniq W := by
        apply Subtype.ext
        have hW : W.1 ∈ ({Set.univ} : Set (Set C)) := by
          rw [← irreducibleComponents_eq_singleton]
          exact W.2
        exact (Set.mem_singleton_iff.mp hW).trans rfl.symm }

omit [IsReduced X] in
/-- The generic point of a reduced induced component maps to the generic point of the
corresponding irreducible component of the ambient scheme. -/
lemma reducedIrreducibleComponentι_genericPoint
    (Z : irreducibleComponents X) :
    X.reducedIrreducibleComponentι Z
        (genericPoint (X.reducedIrreducibleComponent Z)) =
      Z.property.1.genericPoint := by
  have hC := (genericPoint_spec
    (X.reducedIrreducibleComponent Z)).image
      (X.reducedIrreducibleComponentι Z).continuous
  have himage : closure
      (X.reducedIrreducibleComponentι Z ''
        (Set.univ : Set (X.reducedIrreducibleComponent Z))) = Z.1 := by
    rw [Set.image_univ, X.range_reducedIrreducibleComponentι Z]
    exact (isClosed_of_mem_irreducibleComponents Z.1 Z.property).closure_eq
  have hi : IsGenericPoint
      (X.reducedIrreducibleComponentι Z
        (genericPoint (X.reducedIrreducibleComponent Z))) Z.1 := by
    rwa [himage] at hC
  exact hi.eq (Z.property.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z.1 Z.property))

/-- The ambient and reduced-component stalks at the corresponding generic points are
canonically isomorphic. -/
noncomputable def reducedIrreducibleComponentGenericStalkIso
    (Z : irreducibleComponents X) :
    X.presheaf.stalk Z.property.1.genericPoint ≅
      (X.reducedIrreducibleComponent Z).presheaf.stalk
        (genericPoint (X.reducedIrreducibleComponent Z)) := by
  have hfield : IsField (X.presheaf.stalk
      (X.reducedIrreducibleComponentι Z
        (genericPoint (X.reducedIrreducibleComponent Z)))) := by
    rw [X.reducedIrreducibleComponentι_genericPoint Z]
    exact X.componentGenericStalk_isField Z
  let _ : Field (X.presheaf.stalk
      (X.reducedIrreducibleComponentι Z
        (genericPoint (X.reducedIrreducibleComponent Z)))) :=
    hfield.toField
  let _ : IsIso ((X.reducedIrreducibleComponentι Z).stalkMap
      (genericPoint (X.reducedIrreducibleComponent Z))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨RingHom.injective _,
        (X.reducedIrreducibleComponentι Z).stalkMap_surjective _⟩
  exact X.presheaf.stalkCongr
      (.of_eq (X.reducedIrreducibleComponentι_genericPoint Z).symm) ≪≫
    asIso ((X.reducedIrreducibleComponentι Z).stalkMap
      (genericPoint (X.reducedIrreducibleComponent Z)))

/-- The spectra of the ambient and reduced-component function fields are canonically
isomorphic. -/
noncomputable def reducedIrreducibleComponentGenericSpecIso
    (Z : irreducibleComponents X) :
    Spec (X.presheaf.stalk Z.property.1.genericPoint) ≅
      Spec ((X.reducedIrreducibleComponent Z).presheaf.stalk
        (genericPoint (X.reducedIrreducibleComponent Z))) :=
  (Scheme.Spec.mapIso
    (X.reducedIrreducibleComponentGenericStalkIso Z).op).symm

/-- The generic-field spectrum isomorphism commutes with the displayed maps to the
reduced component. -/
@[reassoc]
lemma reducedIrreducibleComponentGenericSpecIso_hom_fromSpecStalk
    (Z : irreducibleComponents X) :
    (X.reducedIrreducibleComponentGenericSpecIso Z).hom ≫
        (X.reducedIrreducibleComponent Z).fromSpecStalk
          (genericPoint (X.reducedIrreducibleComponent Z)) =
      X.componentGenericToReducedComponent Z := by
  let η := genericPoint (X.reducedIrreducibleComponent Z)
  let s := (X.presheaf.stalkCongr
    (.of_eq (X.reducedIrreducibleComponentι_genericPoint Z).symm)).inv
  let m := (X.reducedIrreducibleComponentι Z).stalkMap η
  have hfield : IsField (X.presheaf.stalk
      (X.reducedIrreducibleComponentι Z η)) := by
    rw [X.reducedIrreducibleComponentι_genericPoint Z]
    exact X.componentGenericStalk_isField Z
  let _ : Field (X.presheaf.stalk
      (X.reducedIrreducibleComponentι Z η)) := hfield.toField
  let _ : IsIso m :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨RingHom.injective _,
        (X.reducedIrreducibleComponentι Z).stalkMap_surjective _⟩
  have hm : Spec.map m ≫ X.fromSpecStalk
      (X.reducedIrreducibleComponentι Z η) =
      (X.reducedIrreducibleComponent Z).fromSpecStalk η ≫
        X.reducedIrreducibleComponentι Z :=
    Scheme.SpecMap_stalkMap_fromSpecStalk
      (X.reducedIrreducibleComponentι Z)
  have hm' : inv (Spec.map m) ≫
      (X.reducedIrreducibleComponent Z).fromSpecStalk η ≫
        X.reducedIrreducibleComponentι Z =
      X.fromSpecStalk (X.reducedIrreducibleComponentι Z η) := by
    symm
    rw [IsIso.eq_inv_comp]
    exact hm
  have hs : Spec.map s ≫
      X.fromSpecStalk (X.reducedIrreducibleComponentι Z η) =
      X.fromSpecStalk Z.property.1.genericPoint := by
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (specializes_of_eq
        (X.reducedIrreducibleComponentι_genericPoint Z).symm)
  rw [← cancel_mono (X.reducedIrreducibleComponentι Z)]
  simp only [reducedIrreducibleComponentGenericSpecIso,
    reducedIrreducibleComponentGenericStalkIso, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    Iso.trans_inv, Spec.map_comp, asIso_inv, Spec.map_inv]
  change Spec.map s ≫ inv (Spec.map m) ≫
      (X.reducedIrreducibleComponent Z).fromSpecStalk η ≫
        X.reducedIrreducibleComponentι Z =
    X.componentGenericToReducedComponent Z ≫
      X.reducedIrreducibleComponentι Z
  rw [X.componentGenericToReducedComponent_ι Z]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ Spec.map s ≫ t) hm').trans hs)

/-- Normalizing the reduced component in the ambient component field agrees with
normalizing it in its intrinsic function field. -/
noncomputable def normalizationInReducedComponentIsoAtGenericPoint
    (Z : irreducibleComponents X) :
    (X.componentGenericToReducedComponent Z).normalization ≅
      ((X.reducedIrreducibleComponent Z).fromSpecStalk
        (genericPoint (X.reducedIrreducibleComponent Z))).normalization :=
  Hom.normalizationIsoOfIsoSource
    (X.componentGenericToReducedComponent Z)
    ((X.reducedIrreducibleComponent Z).fromSpecStalk
      (genericPoint (X.reducedIrreducibleComponent Z)))
    (X.reducedIrreducibleComponentGenericSpecIso Z)
    (X.reducedIrreducibleComponentGenericSpecIso_hom_fromSpecStalk Z).symm

/-- For an integral scheme, normalization in the stalk at its generic point agrees with
normalization in its one-component generic scheme. -/
noncomputable def normalizationAtGenericPointIso
    (C : Scheme.{u}) [IsIntegral C] :
    (C.fromSpecStalk (genericPoint C)).normalization ≅ C.normalization := by
  change C.relativeComponentNormalization default ≅ C.normalization
  exact (coproductUniqueIso (fun W : irreducibleComponents C ↦
    C.relativeComponentNormalization W)).symm ≪≫
      C.relativeComponentNormalizationSigmaIso

/-- The generic-point comparison commutes with the normalization maps. -/
@[reassoc (attr := simp)]
lemma normalizationAtGenericPointIso_hom_normalizationMap
    (C : Scheme.{u}) [IsIntegral C] :
    (normalizationAtGenericPointIso C).hom ≫ C.normalizationMap =
      (C.fromSpecStalk (genericPoint C)).fromNormalization := by
  change ((coproductUniqueIso (fun W : irreducibleComponents C ↦
      C.relativeComponentNormalization W)).symm ≪≫
        C.relativeComponentNormalizationSigmaIso).hom ≫ C.normalizationMap =
    (C.fromSpecStalk (genericPoint C)).fromNormalization
  simp
  rfl

/-- The relative normalization in one ambient component function field is isomorphic to
the ordinary normalization of that component with its reduced induced structure. -/
noncomputable def relativeComponentNormalizationIsoReducedComponentNormalization
    (Z : irreducibleComponents X) :
    X.relativeComponentNormalization Z ≅
      (X.reducedIrreducibleComponent Z).normalization :=
  X.relativeComponentNormalizationIsoNormalizationInReducedComponent Z ≪≫
    X.normalizationInReducedComponentIsoAtGenericPoint Z ≪≫
      normalizationAtGenericPointIso (X.reducedIrreducibleComponent Z)

/-- The comparison with the ordinary normalization commutes with the maps to the reduced
component. -/
@[reassoc (attr := simp)]
lemma relativeComponentNormalizationIsoReducedComponentNormalization_hom_normalizationMap
    (Z : irreducibleComponents X) :
    (X.relativeComponentNormalizationIsoReducedComponentNormalization Z).hom ≫
      (X.reducedIrreducibleComponent Z).normalizationMap =
        X.relativeComponentNormalizationToReducedComponent Z := by
  simp [relativeComponentNormalizationIsoReducedComponentNormalization,
    normalizationInReducedComponentIsoAtGenericPoint, Category.assoc]

/-- The comparison with the ordinary reduced-component normalization, bundled over a
common base. -/
noncomputable def relativeComponentNormalizationOverIsoReducedComponentNormalization
    {S : Scheme.{u}} [X.Over S] [IsNoetherian X]
    (Z : irreducibleComponents X) :
    (X.relativeComponentNormalization Z).asOver S ≅
      (X.reducedIrreducibleComponentNormalization Z).asOver S :=
  Over.isoMk
    (X.relativeComponentNormalizationIsoReducedComponentNormalization Z) (by
      change
        (X.relativeComponentNormalizationIsoReducedComponentNormalization Z).hom ≫
          ((X.reducedIrreducibleComponent Z).normalizationMap ≫
            X.reducedIrreducibleComponentι Z ≫ (X ↘ S)) =
        X.relativeComponentNormalizationMap Z ≫ (X ↘ S)
      rw [← Category.assoc,
        X.relativeComponentNormalizationIsoReducedComponentNormalization_hom_normalizationMap Z]
      simpa only [Category.assoc] using congrArg
        (fun t ↦ t ≫ (X ↘ S))
        (X.relativeComponentNormalizationToReducedComponent_ι Z))

end Scheme

end

end AlgebraicGeometry
