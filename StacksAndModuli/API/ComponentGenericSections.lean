module

public import StacksAndModuli.API.ReducedSchemeNormalization
public import StacksAndModuli.API.RelativeNormalizationDefectSupport
public import StacksAndModuli.API.SmoothComponentOpenIntegrallyClosed
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections of the component-generic scheme

Let `U` be a nonempty affine open of a reduced scheme, contained in an irreducible
component `Z`.  This file identifies the inverse image of `U` under the
component-generic map with the spectrum of the stalk at the generic point of `Z`.
On rings, this identifies its sections with the fraction field of `Γ(X, U)`.

The comparison supplies the integrally-closed-in hypothesis needed by relative
normalization on normal affine opens.  For a curve over a field, an affine open in
one component and in the smooth locus is normal, so the normalization map is an
isomorphism there and its structure-sheaf defect vanishes.

## Main results

* `AlgebraicGeometry.Scheme.componentGenericMap_preimage_eq_opensRange` identifies
  the inverse image of a component-open with the corresponding generic summand.
* `AlgebraicGeometry.Scheme.componentGenericPreimageSectionsAlgEquiv` identifies
  the resulting ring of sections with the generic stalk as an algebra.
* `AlgebraicGeometry.Scheme.componentGenericPreimageSections_isFractionRing`
  realizes those sections as the fraction field of the affine-open section ring.
* `AlgebraicGeometry.Scheme.normalizationMap_isIso_morphismRestrict_of_smoothComponentOpen`
  proves that normalization is an isomorphism on a smooth affine component-open of
  a reduced curve.
* `AlgebraicGeometry.Scheme.exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth`
  finds such an open around every formally smooth point.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A nonempty open contained in an irreducible component of a reduced scheme is
integral.  This typeclass-oriented form complements
`Opens.isIntegral_toScheme_of_nonempty_of_le_component`. -/
theorem isIntegral_open_of_nonempty_le_irreducibleComponent
    (X : Scheme.{u}) [IsReduced X] (Z : irreducibleComponents X)
    (U : X.Opens) [Nonempty U] (hUZ : (U : Set X) ⊆ Z.1) :
    IsIntegral U.toScheme := by
  have hUirreducible : IsIrreducible (U : Set X) := by
    constructor
    · let x : U := Classical.choice (inferInstance : Nonempty U)
      exact ⟨x.1, x.2⟩
    · exact Z.property.1.isPreirreducible.open_subset U.isOpen hUZ
  let _ : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hUirreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced U.toScheme

/-- The generic point of an irreducible component belongs to every nonempty open
contained in that component. -/
theorem genericPoint_mem_open_of_nonempty_le_component
    (X : Scheme.{u}) (Z : irreducibleComponents X) (U : X.Opens)
    [Nonempty U] (hUZ : (U : Set X) ⊆ Z.1) :
    Z.property.1.genericPoint ∈ U := by
  apply (Z.property.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z.1 Z.property) |>.mem_open_set_iff U.isOpen).mpr
  let x : U := Classical.choice (inferInstance : Nonempty U)
  exact ⟨x.1, hUZ x.2, x.2⟩

/-- Over a nonempty open contained in one irreducible component, the inverse image
under the component-generic map is exactly the corresponding coproduct summand. -/
theorem componentGenericMap_preimage_eq_opensRange
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    X.componentGenericMap ⁻¹ᵁ U =
      (Sigma.ι (fun W : irreducibleComponents X =>
        Spec (X.presheaf.stalk W.property.1.genericPoint)) Z).opensRange := by
  apply SetLike.ext'
  ext y
  constructor
  · intro hy
    obtain ⟨⟨W, z⟩, rfl⟩ := (sigmaMk (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint))).surjective y
    have hfield := X.componentGenericStalk_isField W
    let _ : Subsingleton (Spec (X.presheaf.stalk W.property.1.genericPoint)) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hfield
    have hz : z = IsLocalRing.closedPoint
        (X.presheaf.stalk W.property.1.genericPoint) := Subsingleton.elim _ _
    subst z
    have hmap : X.componentGenericMap
        (Sigma.ι (fun W : irreducibleComponents X =>
          Spec (X.presheaf.stalk W.property.1.genericPoint)) W
            (IsLocalRing.closedPoint _)) = W.property.1.genericPoint := by
      exact (congrArg (fun f : Spec (X.presheaf.stalk W.property.1.genericPoint) ⟶ X =>
        f (IsLocalRing.closedPoint _)) (X.sigmaι_componentGenericMap W)).trans
          Scheme.fromSpecStalk_closedPoint
    have hgenericU : W.property.1.genericPoint ∈ U := by
      change X.componentGenericMap
        ((sigmaMk (fun W : irreducibleComponents X =>
          Spec (X.presheaf.stalk W.property.1.genericPoint)))
            ⟨W, IsLocalRing.closedPoint _⟩) ∈ U at hy
      rw [sigmaMk_mk] at hy
      exact (congrArg (fun x : X => x ∈ U) hmap).mp hy
    have hgenericZ : W.property.1.genericPoint ∈ Z.1 := hUZ hgenericU
    have hWZ : W.1 ⊆ Z.1 := by
      rw [← W.property.1.closure_genericPoint
        (isClosed_of_mem_irreducibleComponents W.1 W.property)]
      exact closure_minimal (Set.singleton_subset_iff.mpr hgenericZ)
        (isClosed_of_mem_irreducibleComponents Z.1 Z.property)
    have hZW : Z.1 ⊆ W.1 := W.property.2 Z.property.1 hWZ
    have hW : W = Z := Subtype.ext (Set.Subset.antisymm hWZ hZW)
    subst W
    change _ ∈ Set.range (Sigma.ι (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint)) Z)
    simpa only [sigmaMk_mk] using
      (Set.mem_range_self (f := Sigma.ι (fun W : irreducibleComponents X =>
        Spec (X.presheaf.stalk W.property.1.genericPoint)) Z)
          (IsLocalRing.closedPoint (X.presheaf.stalk Z.property.1.genericPoint)))
  · intro hy
    obtain ⟨z, rfl⟩ := hy
    change X.componentGenericMap
      (Sigma.ι (fun W : irreducibleComponents X =>
        Spec (X.presheaf.stalk W.property.1.genericPoint)) Z z) ∈ U
    have hfield := X.componentGenericStalk_isField Z
    let _ : Subsingleton (Spec (X.presheaf.stalk Z.property.1.genericPoint)) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hfield
    have hz : z = IsLocalRing.closedPoint
        (X.presheaf.stalk Z.property.1.genericPoint) := Subsingleton.elim _ _
    subst z
    have hmap : X.componentGenericMap
        (Sigma.ι (fun W : irreducibleComponents X =>
          Spec (X.presheaf.stalk W.property.1.genericPoint)) Z
            (IsLocalRing.closedPoint _)) = Z.property.1.genericPoint := by
      exact (congrArg (fun f : Spec (X.presheaf.stalk Z.property.1.genericPoint) ⟶ X =>
        f (IsLocalRing.closedPoint _)) (X.sigmaι_componentGenericMap Z)).trans
          Scheme.fromSpecStalk_closedPoint
    apply (congrArg (fun x : X => x ∈ U) hmap).mpr
    exact genericPoint_mem_open_of_nonempty_le_component X Z U hUZ

/-- The inverse image of a nonempty component-open under the component-generic map
is isomorphic to the spectrum of the stalk at that component's generic point. -/
noncomputable def componentGenericPreimageIso
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    Spec (X.presheaf.stalk Z.property.1.genericPoint) ≅
      (X.componentGenericMap ⁻¹ᵁ U).toScheme :=
  (Sigma.ι (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint)) Z).isoOpensRange ≪≫
    X.componentGenericScheme.isoOfEq
      (componentGenericMap_preimage_eq_opensRange X Z U hUZ).symm

/-- The component-generic preimage isomorphism followed by the open inclusion is
the coproduct inclusion of the selected generic summand. -/
@[reassoc (attr := simp)]
theorem componentGenericPreimageIso_hom_ι
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    (componentGenericPreimageIso X Z U hUZ).hom ≫
        (X.componentGenericMap ⁻¹ᵁ U).ι =
      Sigma.ι (fun W : irreducibleComponents X =>
        Spec (X.presheaf.stalk W.property.1.genericPoint)) Z := by
  simp [componentGenericPreimageIso]

/-- Restricting the component-generic map along its preimage is, under
`componentGenericPreimageIso`, the canonical map from the selected generic stalk. -/
@[reassoc (attr := simp)]
theorem componentGenericPreimageIso_hom_resLE
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    (componentGenericPreimageIso X Z U hUZ).hom ≫
        X.componentGenericMap.resLE U
          (X.componentGenericMap ⁻¹ᵁ U) le_rfl =
      U.fromSpecStalkOfMem Z.property.1.genericPoint
        (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ) := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    componentGenericPreimageIso_hom_ι_assoc,
    X.sigmaι_componentGenericMap,
    U.fromSpecStalkOfMem_ι]

/-- Sections of the component-generic scheme over a nonempty component-open are
equivalent to the stalk at that component's generic point. -/
noncomputable def componentGenericPreimageSectionsRingEquiv
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U) ≃+*
      X.presheaf.stalk Z.property.1.genericPoint :=
  ((X.componentGenericMap ⁻¹ᵁ U).topIso.symm ≪≫
    asIso (componentGenericPreimageIso X Z U hUZ).hom.appTop ≪≫
    Scheme.ΓSpecIso (X.presheaf.stalk Z.property.1.genericPoint)).commRingCatIsoToRingEquiv

/-- The pullback on an open under the component-generic map factors through the
top-open comparison and the restricted morphism. -/
theorem componentGenericMap_app_comp_topIso_inv
    (X : Scheme.{u}) (U : X.Opens) :
    X.componentGenericMap.app U ≫
        (X.componentGenericMap ⁻¹ᵁ U).topIso.inv =
      U.topIso.inv ≫
        (X.componentGenericMap.resLE U
          (X.componentGenericMap ⁻¹ᵁ U) le_rfl).appTop := by
  rw [← cancel_epi U.topIso.hom]
  have h := (arrowResLEAppIso X.componentGenericMap U
    (X.componentGenericMap ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ X.componentGenericMap.appLE U
      (X.componentGenericMap ⁻¹ᵁ U) le_rfl =
    (X.componentGenericMap.resLE U
      (X.componentGenericMap ⁻¹ᵁ U) le_rfl).appTop ≫
        (X.componentGenericMap ⁻¹ᵁ U).topIso.hom at h
  simp only [Iso.hom_inv_id_assoc]
  rw [Scheme.Hom.app_eq_appLE]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The pullback on global sections along the map from a stalk spectrum agrees,
after the affine-spectrum comparison, with the germ map. -/
theorem topIso_inv_comp_fromSpecStalkOfMem_appTop_comp_ΓSpecIso
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U) :
    U.topIso.inv ≫ (U.fromSpecStalkOfMem x hx).appTop ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom =
      X.presheaf.germ U x hx := by
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(X, U)).hom]
  rw [← Scheme.Opens.toSpecΓ_appTop_assoc]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop]
  rw [U.fromSpecStalkOfMem_toSpecΓ]
  rw [Scheme.ΓSpecIso_naturality]

/-- On global sections, the restricted component-generic morphism followed by the
preimage isomorphism is the map from the selected generic stalk spectrum. -/
@[reassoc]
theorem componentGenericPreimageIso_resLE_appTop
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    (X.componentGenericMap.resLE U
        (X.componentGenericMap ⁻¹ᵁ U) le_rfl).appTop ≫
      (componentGenericPreimageIso X Z U hUZ).hom.appTop =
    (U.fromSpecStalkOfMem Z.property.1.genericPoint
      (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).appTop := by
  rw [← Scheme.Hom.comp_appTop]
  rw [componentGenericPreimageIso_hom_resLE]

/-- The ring equivalence from component-generic preimage sections to the generic
stalk intertwines the component-generic pullback with the germ map. -/
theorem componentGenericPreimageSectionsRingEquiv_comp_app
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    (componentGenericPreimageSectionsRingEquiv X Z U hUZ).toRingHom.comp
        (X.componentGenericMap.app U).hom =
      (X.presheaf.germ U Z.property.1.genericPoint
        (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom := by
  ext r
  change ((X.componentGenericMap.app U ≫
      (X.componentGenericMap ⁻¹ᵁ U).topIso.inv ≫
      (componentGenericPreimageIso X Z U hUZ).hom.appTop ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk Z.property.1.genericPoint)).hom) r) = _
  have hcat : X.componentGenericMap.app U ≫
        (X.componentGenericMap ⁻¹ᵁ U).topIso.inv ≫
        (componentGenericPreimageIso X Z U hUZ).hom.appTop ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk Z.property.1.genericPoint)).hom =
      X.presheaf.germ U Z.property.1.genericPoint
        (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ) := by
    rw [← Category.assoc, ← Category.assoc,
      componentGenericMap_app_comp_topIso_inv]
    simp only [Category.assoc]
    rw [componentGenericPreimageIso_resLE_appTop_assoc]
    exact topIso_inv_comp_fromSpecStalkOfMem_appTop_comp_ΓSpecIso
      X U Z.property.1.genericPoint
        (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)
  exact congrArg (fun q : Γ(X, U) ⟶
    X.presheaf.stalk Z.property.1.genericPoint => q r) hcat

/-- In an affine component-open of a reduced scheme, the selected component's
generic point corresponds to the zero prime ideal. -/
theorem primeIdealOf_componentGenericPoint_eq_bot
    (X : Scheme.{u}) [IsReduced X] (Z : irreducibleComponents X)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hUZ : (U : Set X) ⊆ Z.1) :
    (hU.primeIdealOf
      ⟨Z.property.1.genericPoint,
        genericPoint_mem_open_of_nonempty_le_component X Z U hUZ⟩).asIdeal = ⊥ := by
  let _ : IsIntegral U.toScheme :=
    isIntegral_open_of_nonempty_le_irreducibleComponent X Z U hUZ
  let _ : IsDomain Γ(X, U) :=
    U.topIso.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain Γ(U.toScheme, ⊤)
  let η : U := ⟨Z.property.1.genericPoint,
    genericPoint_mem_open_of_nonempty_le_component X Z U hUZ⟩
  have hηGeneric : IsGenericPoint η (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    apply Topology.IsInducing.subtypeVal.specializes_iff.mp
    exact (Z.property.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents Z.1 Z.property)).specializes (hUZ y.2)
  have hη : η = genericPoint U :=
    hηGeneric.eq (genericPoint_spec U)
  have hp : hU.isoSpec.hom η = (⊥ : PrimeSpectrum Γ(X, U)) := by
    rw [hη, genericPoint_eq_of_isOpenImmersion hU.isoSpec.hom,
      genericPoint_eq_bot_of_affine]
  exact congrArg PrimeSpectrum.asIdeal hp

/-- The stalk at the selected component's generic point is a fraction ring of the
section ring of any nonempty affine open contained in that component. -/
theorem componentGenericStalk_isFractionRing
    (X : Scheme.{u}) [IsReduced X] (Z : irreducibleComponents X)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hUZ : (U : Set X) ⊆ Z.1) :
    letI := (X.presheaf.germ U Z.property.1.genericPoint
      (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.presheaf.stalk Z.property.1.genericPoint) := by
  let _ : IsIntegral U.toScheme :=
    isIntegral_open_of_nonempty_le_irreducibleComponent X Z U hUZ
  let _ : IsDomain Γ(X, U) :=
    U.topIso.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain Γ(U.toScheme, ⊤)
  let η : U := ⟨Z.property.1.genericPoint,
    genericPoint_mem_open_of_nonempty_le_component X Z U hUZ⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf η
  have hloc := hU.isLocalization_stalk η
  change IsLocalization (nonZeroDivisors Γ(X, U))
    (X.presheaf.stalk Z.property.1.genericPoint)
  convert hloc using 1
  ext r
  rw [mem_nonZeroDivisors_iff_ne_zero]
  change r ≠ 0 ↔ r ∉ (hU.primeIdealOf η).asIdeal
  have hp := primeIdealOf_componentGenericPoint_eq_bot X Z U hU hUZ
  have hr : r ∈ (hU.primeIdealOf η).asIdeal ↔ r = 0 := by
    constructor
    · intro hr
      exact Ideal.mem_bot.mp
        ((congrArg (fun I : Ideal Γ(X, U) => r ∈ I) hp).mp hr)
    · rintro rfl
      exact (hU.primeIdealOf η).asIdeal.zero_mem
  exact (not_congr hr).symm

/-- The component-generic preimage section ring is equivalent, as an algebra over
the original open's section ring, to the selected component's generic stalk. -/
noncomputable def componentGenericPreimageSectionsAlgEquiv
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hUZ : (U : Set X) ⊆ Z.1) :
    letI := (X.componentGenericMap.app U).hom.toAlgebra
    letI := (X.presheaf.germ U Z.property.1.genericPoint
      (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom.toAlgebra
    Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.presheaf.stalk Z.property.1.genericPoint := by
  let _ := (X.componentGenericMap.app U).hom.toAlgebra
  let _ := (X.presheaf.germ U Z.property.1.genericPoint
    (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom.toAlgebra
  exact
  { componentGenericPreimageSectionsRingEquiv X Z U hUZ with
    commutes' := fun r => by
      change (componentGenericPreimageSectionsRingEquiv X Z U hUZ)
          ((X.componentGenericMap.app U).hom r) =
        (X.presheaf.germ U Z.property.1.genericPoint
          (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom r
      exact DFunLike.congr_fun
        (componentGenericPreimageSectionsRingEquiv_comp_app X Z U hUZ) r }

/-- Sections of the component-generic scheme over a nonempty affine
component-open form a fraction ring of the original section ring. -/
theorem componentGenericPreimageSections_isFractionRing
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (hUZ : (U : Set X) ⊆ Z.1) :
    letI := (X.componentGenericMap.app U).hom.toAlgebra
    IsFractionRing Γ(X, U)
      Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U) := by
  let _ := (X.componentGenericMap.app U).hom.toAlgebra
  let _ := (X.presheaf.germ U Z.property.1.genericPoint
    (genericPoint_mem_open_of_nonempty_le_component X Z U hUZ)).hom.toAlgebra
  let _ : IsFractionRing Γ(X, U) (X.presheaf.stalk Z.property.1.genericPoint) :=
    componentGenericStalk_isFractionRing X Z U hU hUZ
  exact IsFractionRing.of_algEquiv
    (componentGenericPreimageSectionsAlgEquiv X Z U hUZ).symm

/-- If the section ring of a nonempty affine component-open is integrally closed,
then it is integrally closed in the corresponding component-generic preimage
section ring. -/
theorem componentGenericPreimageSections_isIntegrallyClosedIn
    (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (hUZ : (U : Set X) ⊆ Z.1)
    [IsIntegrallyClosed Γ(X, U)] :
    letI := (X.componentGenericMap.app U).hom.toAlgebra
    IsIntegrallyClosedIn Γ(X, U)
      Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U) := by
  let _ := (X.componentGenericMap.app U).hom.toAlgebra
  let _ : IsFractionRing Γ(X, U)
      Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U) :=
    componentGenericPreimageSections_isFractionRing X Z U hU hUZ
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn
    Γ(X.componentGenericScheme, X.componentGenericMap ⁻¹ᵁ U)).mp inferInstance

/-- The normalization of a reduced scheme is an isomorphism over a nonempty affine
component-open whose section ring is integrally closed. -/
theorem normalizationMap_isIso_morphismRestrict_of_isIntegrallyClosed
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (hUZ : (U : Set X) ⊆ Z.1)
    [IsIntegrallyClosed Γ(X, U)] : IsIso (X.normalizationMap ∣_ U) := by
  let _ : IsSchemeTheoreticallyDominant X.componentGenericMap :=
    IsSchemeTheoreticallyDominant.of_isDominant X.componentGenericMap
  apply X.componentGenericMap.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosedIn
    hU (X.componentGenericMap.app_injective U)
  exact componentGenericPreimageSections_isIntegrallyClosedIn X Z U hU hUZ

/-- The cokernel of the normalization unit vanishes over a nonempty affine
component-open whose section ring is integrally closed. -/
theorem isZero_restrict_cokernel_normalizationUnit_of_isIntegrallyClosed
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)]
    (Z : irreducibleComponents X) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (hUZ : (U : Set X) ⊆ Z.1)
    [IsIntegrallyClosed Γ(X, U)] :
    IsZero ((Modules.restrictFunctor U.ι).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit
        X.normalizationMap.toRingCatSheafHom))) := by
  let _ : IsSchemeTheoreticallyDominant X.componentGenericMap :=
    IsSchemeTheoreticallyDominant.of_isDominant X.componentGenericMap
  apply X.componentGenericMap.isZero_restrict_cokernel_normalizationUnit_of_isIntegrallyClosedIn
    hU (X.componentGenericMap.app_injective U)
  exact componentGenericPreimageSections_isIntegrallyClosedIn X Z U hU hUZ

/-- The normalization of a reduced curve is an isomorphism over a nonempty affine
open contained in one irreducible component and in the smooth locus over a field. -/
theorem normalizationMap_isIso_morphismRestrict_of_smoothComponentOpen
    {K : Type u} [Field K] (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] (Z : irreducibleComponents X)
    (U : X.Opens) (hU : IsAffineOpen U) (hUnonempty : (U : Set X).Nonempty)
    (hUZ : (U : Set X) ⊆ Z.1) (hUsmooth : (U : Set X) ⊆ f.smoothLocus)
    (hdim : topologicalKrullDim X ≤ 1) : IsIso (X.normalizationMap ∣_ U) := by
  let _ : Nonempty U := by simpa using hUnonempty
  let _ : IsIntegrallyClosed Γ(X, U) :=
    IsAffineOpen.isIntegrallyClosed_sections_of_le_component_of_le_smoothLocus
      f hU hUnonempty Z hUZ hUsmooth hdim
  exact normalizationMap_isIso_morphismRestrict_of_isIntegrallyClosed X Z U hU hUZ

/-- The cokernel of the normalization unit vanishes over a nonempty affine open
contained in one component and in the smooth locus of a reduced curve over a field. -/
theorem isZero_restrict_cokernel_normalizationUnit_of_smoothComponentOpen
    {K : Type u} [Field K] (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] (Z : irreducibleComponents X)
    (U : X.Opens) (hU : IsAffineOpen U) (hUnonempty : (U : Set X).Nonempty)
    (hUZ : (U : Set X) ⊆ Z.1) (hUsmooth : (U : Set X) ⊆ f.smoothLocus)
    (hdim : topologicalKrullDim X ≤ 1) :
    IsZero ((Modules.restrictFunctor U.ι).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit
        X.normalizationMap.toRingCatSheafHom))) := by
  let _ : Nonempty U := by simpa using hUnonempty
  let _ : IsIntegrallyClosed Γ(X, U) :=
    IsAffineOpen.isIntegrallyClosed_sections_of_le_component_of_le_smoothLocus
      f hU hUnonempty Z hUZ hUsmooth hdim
  exact isZero_restrict_cokernel_normalizationUnit_of_isIntegrallyClosed X Z U hU hUZ

/-- Every formally smooth point of a reduced scheme of dimension at most one has an
affine neighbourhood over which normalization is an isomorphism. -/
theorem exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth
    {K : Type u} [Field K] (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] (x : X)
    (hx : (f.stalkMap x).hom.FormallySmooth)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsIso (X.normalizationMap ∣_ U) := by
  obtain ⟨U, hU, hxU, hUsub⟩ :=
    X.exists_affineOpen_mem_le_smoothPointComponent_inter_smoothLocus f x hx
  refine ⟨U, hU, hxU, ?_⟩
  apply normalizationMap_isIso_morphismRestrict_of_smoothComponentOpen
    X f (X.smoothPointComponent f x hx) U hU ⟨x, hxU⟩
  · exact fun y hy ↦ (hUsub hy).1
  · exact fun y hy ↦ (hUsub hy).2
  · exact hdim

/-- Every formally smooth point of a reduced scheme of dimension at most one has an
affine neighbourhood on which the cokernel of the normalization unit vanishes. -/
theorem exists_affineOpen_mem_isZero_normalizationDefect_of_formallySmooth
    {K : Type u} [Field K] (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] (x : X)
    (hx : (f.stalkMap x).hom.FormallySmooth)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsZero ((Modules.restrictFunctor U.ι).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit
          X.normalizationMap.toRingCatSheafHom))) := by
  obtain ⟨U, hU, hxU, hUsub⟩ :=
    X.exists_affineOpen_mem_le_smoothPointComponent_inter_smoothLocus f x hx
  refine ⟨U, hU, hxU, ?_⟩
  apply isZero_restrict_cokernel_normalizationUnit_of_smoothComponentOpen
    X f (X.smoothPointComponent f x hx) U hU ⟨x, hxU⟩
  · exact fun y hy ↦ (hUsub hy).1
  · exact fun y hy ↦ (hUsub hy).2
  · exact hdim

end AlgebraicGeometry.Scheme

end
