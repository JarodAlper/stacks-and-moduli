module

public import StacksAndModuli.API.CoreCoGrothendieckPrestack
public import StacksAndModuli.API.QuasicoherentObjectProperties
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Prestacks of quasi-coherent families

For a scheme `X` over `S`, this file constructs the pseudofunctors of quasi-coherent
modules on `X ×_S T` which are flat over `T`, and their coherent and vector-bundle
full subpseudofunctors.  Taking pointwise cores makes morphisms in each fiber precisely
isomorphisms of the corresponding module sheaves.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Send `T → S` to the fiber product `X ×_S T`. -/
noncomputable abbrev familySchemeFunctor {S : Scheme.{u}} (X : Over S) :
    Over S ⥤ Scheme.{u} :=
  Over.pullback X.hom ⋙ Over.forget X.left

/-- The quasicoherent-module pseudofunctor on the family of schemes `X ×_S T`. -/
noncomputable abbrev familyModulesPseudofunctor {S : Scheme.{u}} (X : Over S) :
    Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  Pseudofunctor.comp (familySchemeFunctor X).op.toPseudofunctor
    quasicoherentPseudofunctor

/-- Quasi-coherent modules on `X ×_S T` which are flat over `T`. -/
def flatFamilyProperty {S : Scheme.{u}} (X : Over S) :
    (familyModulesPseudofunctor X).ObjectProperty where
  prop T M := M.obj.FlatOver (pullback.fst T.as.unop.hom X.hom)

/-- A flat quasi-coherent family remains such after arbitrary base change. -/
instance flatFamilyProperty_isClosedUnderMapObj {S : Scheme.{u}} (X : Over S) :
    (flatFamilyProperty X).IsClosedUnderMapObj where
  map_obj {Y T M} hM g := by
    dsimp only [flatFamilyProperty] at hM ⊢
    change
      ((Modules.pullback ((Over.pullback X.hom).map g.as.unop).left).obj M.obj).FlatOver
        (pullback.fst T.as.unop.hom X.hom)
    letI : M.obj.IsQuasicoherent := M.property
    let G := ((Over.pullback X.hom).map g.as.unop).left
    let p' := pullback.fst T.as.unop.hom X.hom
    let p := pullback.fst Y.as.unop.hom X.hom
    let N := (Modules.pullback G).obj M.obj
    have H : IsPullback G p' p g.as.unop.left := overPullbackMap_isPullback g.as.unop
    intro U V hUV
    apply FlatOver.flat_sections_affine_of_pointwise_basicOpen p' N U V hUV
    intro q hqU
    obtain ⟨A, B, C, hA, hB, hBV, r, s, hrs, hqr⟩ :=
      exists_common_basicOpen_affineOpenPullbackMapOfIsPullback
        G p' p g.as.unop.left H U V q hqU (hUV hqU)
    refine ⟨r, hqr, ?_⟩
    let hsV : (Limits.pullback T.as.unop.hom X.hom).basicOpen s ≤ p' ⁻¹ᵁ V.1 := by
      intro y hy
      have hyRange := (Limits.pullback T.as.unop.hom X.hom).basicOpen_le s hy
      exact hBV ((opensRange_affineOpenPullbackMapOfIsPullback_le
        G p' p g.as.unop.left H A B C hA hB hyRange).2)
    have hflatS :
        letI := Module.compHom Γ(N, (Limits.pullback T.as.unop.hom X.hom).basicOpen s)
          (p'.appLE V.1 ((Limits.pullback T.as.unop.hom X.hom).basicOpen s) hsV).hom
        Module.Flat Γ(T.as.unop.left, V.1)
          Γ(N, (Limits.pullback T.as.unop.hom X.hom).basicOpen s) :=
      FlatOver.affineOpenPullback_ambient_basicOpen_of_le
        G p' p g.as.unop.left H hM A B V C hA hB hBV s
    let hrV : (Limits.pullback T.as.unop.hom X.hom).basicOpen r ≤ p' ⁻¹ᵁ V.1 :=
      ((Limits.pullback T.as.unop.hom X.hom).basicOpen_le r).trans hUV
    have htransport :
        let d' : Γ(T.as.unop.left, V.1) →+*
            Γ(Limits.pullback T.as.unop.hom X.hom,
              (Limits.pullback T.as.unop.hom X.hom).basicOpen r) :=
          hrs.symm ▸
            (p'.appLE V.1 ((Limits.pullback T.as.unop.hom X.hom).basicOpen s) hsV).hom
        letI := Module.compHom Γ(N,
          (Limits.pullback T.as.unop.hom X.hom).basicOpen r) d'
        Module.Flat Γ(T.as.unop.left, V.1)
          Γ(N, (Limits.pullback T.as.unop.hom X.hom).basicOpen r) :=
      Scheme.Modules.sections_flat_of_eq N _ _ hrs.symm
        (p'.appLE V.1 ((Limits.pullback T.as.unop.hom X.hom).basicOpen s) hsV).hom hflatS
    apply Module.Flat.compHom_congr
      (hrs.symm ▸ (p'.appLE V.1
        ((Limits.pullback T.as.unop.hom X.hom).basicOpen s) hsV).hom)
      (p'.appLE V.1 ((Limits.pullback T.as.unop.hom X.hom).basicOpen r) hrV).hom
    · exact Scheme.Hom.appLE_hom_transport p' V.1 _ _ hrs.symm hsV hrV
    · exact htransport

/-- Flatness and quasi-coherence of a family are invariant under isomorphism. -/
instance flatFamilyProperty_isClosedUnderIsomorphisms {S : Scheme.{u}} (X : Over S) :
    (flatFamilyProperty X).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms T := by
    constructor
    intro M N e hM
    dsimp only [flatFamilyProperty] at hM ⊢
    exact (FlatOver.iso_iff
      ((SheafOfModules.isQuasicoherent
        (Limits.pullback T.as.unop.hom X.hom).ringCatSheaf).ι.mapIso e)).mp hM

/-- The pointwise groupoid of flat quasi-coherent families. -/
noncomputable abbrev flatFamilyPseudofunctor {S : Scheme.{u}} (X : Over S) :=
  (flatFamilyProperty X).fullsubcategory.core

/-- The prestack of flat quasi-coherent families on `X`. -/
noncomputable abbrev flatFamilyPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (Pseudofunctor.CoGrothendieck.forget (flatFamilyPseudofunctor X))

/-- The coherent refinement of the flat-family property. -/
def coherentFamilyProperty {S : Scheme.{u}} (X : Over S) :
    (familyModulesPseudofunctor X).ObjectProperty where
  prop T M := (flatFamilyProperty X).prop T M ∧ M.obj.IsFinitePresentation

instance coherentFamilyProperty_isClosedUnderMapObj {S : Scheme.{u}} (X : Over S) :
    (coherentFamilyProperty X).IsClosedUnderMapObj where
  map_obj {Y T M} hM g := by
    dsimp only [coherentFamilyProperty] at hM ⊢
    refine ⟨Pseudofunctor.ObjectProperty.map_obj (P := flatFamilyProperty X) hM.1 g, ?_⟩
    letI : M.obj.IsQuasicoherent := M.property
    letI : M.obj.IsFinitePresentation := hM.2
    change ((Modules.pullback ((Over.pullback X.hom).map g.as.unop).left).obj M.obj).IsFinitePresentation
    infer_instance

instance coherentFamilyProperty_isClosedUnderIsomorphisms {S : Scheme.{u}} (X : Over S) :
    (coherentFamilyProperty X).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms T := by
    constructor
    intro M N e hM
    dsimp only [coherentFamilyProperty] at hM ⊢
    refine ⟨ObjectProperty.prop_of_iso (P := (flatFamilyProperty X).prop T) e hM.1, ?_⟩
    exact ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation
        (Limits.pullback T.as.unop.hom X.hom).ringCatSheaf)
      ((SheafOfModules.isQuasicoherent
        (Limits.pullback T.as.unop.hom X.hom).ringCatSheaf).ι.mapIso e) hM.2

/-- The pointwise groupoid of coherent flat families. -/
noncomputable abbrev coherentFamilyPseudofunctor {S : Scheme.{u}} (X : Over S) :=
  (coherentFamilyProperty X).fullsubcategory.core

/-- The prestack of coherent flat families on `X`. -/
noncomputable abbrev coherentFamilyPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (Pseudofunctor.CoGrothendieck.forget (coherentFamilyPseudofunctor X))

/-- The vector-bundle refinement of the flat-family property. -/
def vectorBundleFamilyProperty {S : Scheme.{u}} (X : Over S) :
    (familyModulesPseudofunctor X).ObjectProperty where
  prop T M := (flatFamilyProperty X).prop T M ∧ IsFiniteLocallyFree M.obj

instance vectorBundleFamilyProperty_isClosedUnderMapObj {S : Scheme.{u}} (X : Over S) :
    (vectorBundleFamilyProperty X).IsClosedUnderMapObj where
  map_obj {Y T M} hM g := by
    dsimp only [vectorBundleFamilyProperty] at hM ⊢
    refine ⟨Pseudofunctor.ObjectProperty.map_obj (P := flatFamilyProperty X) hM.1 g, ?_⟩
    letI : M.obj.IsQuasicoherent := M.property
    change IsFiniteLocallyFree
      ((Modules.pullback ((Over.pullback X.hom).map g.as.unop).left).obj M.obj)
    exact hM.2.pullback _

instance vectorBundleFamilyProperty_isClosedUnderIsomorphisms {S : Scheme.{u}} (X : Over S) :
    (vectorBundleFamilyProperty X).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms T := by
    constructor
    intro M N e hM
    dsimp only [vectorBundleFamilyProperty] at hM ⊢
    refine ⟨ObjectProperty.prop_of_iso (P := (flatFamilyProperty X).prop T) e hM.1, ?_⟩
    exact IsFiniteLocallyFree.of_iso
      ((SheafOfModules.isQuasicoherent
        (Limits.pullback T.as.unop.hom X.hom).ringCatSheaf).ι.mapIso e) hM.2

/-- The pointwise groupoid of vector-bundle families. -/
noncomputable abbrev vectorBundleFamilyPseudofunctor {S : Scheme.{u}} (X : Over S) :=
  (vectorBundleFamilyProperty X).fullsubcategory.core

/-- The prestack of vector-bundle families on `X`. -/
noncomputable abbrev vectorBundleFamilyPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (Pseudofunctor.CoGrothendieck.forget (vectorBundleFamilyPseudofunctor X))

end AlgebraicGeometry.Scheme.Modules
