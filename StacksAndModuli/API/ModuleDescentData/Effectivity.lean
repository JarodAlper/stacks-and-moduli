module

public import StacksAndModuli.API.ModuleDescentData.Comparison
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Carrier normalization for ordinary affine module descent data

This file normalizes the `Cat`-wrapped carrier of the canonical ordinary
singleton descent datum.  It is the remaining transport helper needed when
comparing this datum with the Beck comparison coalgebra.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The carrier of the canonical affine descent datum, normalized without an
opaque equality proof. -/
noncomputable def AffineStandardDescentData.ofModuleCarrierIso
    (M : ModuleCat A) :
    (AffineStandardDescentData.ofModule f M).obj default ≅
      (extendScalars f).obj M := by
  change (extendScalars f).obj M ≅ (extendScalars f).obj M
  exact Iso.refl _

@[simp]
lemma AffineStandardDescentData.ofModuleCarrierIso_hom
    (M : ModuleCat A) :
    (AffineStandardDescentData.ofModuleCarrierIso f M).hom =
      𝟙 ((extendScalars f).obj M) := by
  rfl

/-- The carrier identification is extension of scalars applied to an identity
morphism. This form interacts directly with compositor naturality. -/
lemma AffineStandardDescentData.ofModuleCarrierIso_hom_eq_map_id
    (M : ModuleCat A) :
    (AffineStandardDescentData.ofModuleCarrierIso f M).hom =
      (extendScalars f).map (𝟙 M) := by
  rw [AffineStandardDescentData.ofModuleCarrierIso_hom]
  exact ((extendScalars f).map_id M).symm

/-- The carrier identification intertwines the actual overlap morphism in the
canonical descent datum with its proof-normalized explicit form. -/
lemma AffineStandardDescentData.ofModule_overlap_comm
    (M : ModuleCat A) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (extendScalars l).map
          (AffineStandardDescentData.ofModuleCarrierIso f M).hom ≫
        AffineStandardDescentData.ofModuleOverlapHom f M =
      (AffineStandardDescentData.ofModule f M).overlapHom f ≫
        (extendScalars r).map
          (AffineStandardDescentData.ofModuleCarrierIso f M).hom := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let q : A →+* C := algebraMap A C
  rw [AffineStandardDescentData.ofModuleCarrierIso_hom_eq_map_id]
  unfold AffineStandardDescentData.ofModuleOverlapHom mapCompOverlap
  unfold AffineStandardDescentData.overlapHom
  rw [Pseudofunctor.DescentData.ofObj_hom]
  rw [mapComp'_inv_app_eq_of_proof_irrel _
      (doubleOpCompEq f l q (affineOverlapLeftRingHom_comp f)) M,
    mapComp'_hom_app_eq_of_proof_irrel _
      (doubleOpCompEq f r q (affineOverlapRightRingHom_comp f)) M]
  dsimp only
  exact mapCompOverlap_naturality f l r q
    (affineOverlapLeftRingHom_comp f)
    (affineOverlapRightRingHom_comp f) (𝟙 M)

/-- The coaction on the canonical ordinary descent datum agrees with the Beck
comparison coaction after the carrier identification. -/
lemma AffineStandardDescentData.ofModule_coaction_comm
    (M : ModuleCat A) :
    ((AffineStandardDescentData.toCoalgebra f).obj
        (AffineStandardDescentData.ofModule f M)).a ≫
        (extendRestrictScalarsAdj f).toComonad.map
          (AffineStandardDescentData.ofModuleCarrierIso f M).hom =
      (AffineStandardDescentData.ofModuleCarrierIso f M).hom ≫
        ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a := by
  dsimp only [AffineStandardDescentData.toCoalgebra,
    AffineStandardDescentData.toCoalgebraObj]
  rw [← AffineStandardDescentData.ofModuleOverlapCoaction]
  exact (overlap_comm_iff_coaction_comm f _ _
    (AffineStandardDescentData.ofModuleCarrierIso f M).hom
    ((AffineStandardDescentData.ofModule f M).overlapHom f)
    (AffineStandardDescentData.ofModuleOverlapHom f M)).mp
      (AffineStandardDescentData.ofModule_overlap_comm f M)

/-- The coalgebra attached to the canonical ordinary descent datum is the
Beck comparison coalgebra. -/
noncomputable def AffineStandardDescentData.ofModuleCoalgebraIsoComparison
    (M : ModuleCat A) :
    (AffineStandardDescentData.toCoalgebra f).obj
        (AffineStandardDescentData.ofModule f M) ≅
      (Comonad.comparison (extendRestrictScalarsAdj f)).obj M :=
  Comonad.Coalgebra.isoMk
    (AffineStandardDescentData.ofModuleCarrierIso f M)
    (AffineStandardDescentData.ofModule_coaction_comm f M)

/-- For a faithfully flat ring map, every Beck coalgebra comes from an
ordinary singleton affine descent datum. -/
theorem affineStandardToCoalgebra_essSurj
    (hf : f.FaithfullyFlat) :
    (AffineStandardDescentData.toCoalgebra f).EssSurj := by
  letI : (Comonad.comparison
      (extendRestrictScalarsAdj.{u, u, u} f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  refine ⟨fun D ↦ ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := Comonad.comparison
      (extendRestrictScalarsAdj.{u, u, u} f)) D
  exact ⟨AffineStandardDescentData.ofModule f M,
    ⟨AffineStandardDescentData.ofModuleCoalgebraIsoComparison f M ≪≫ e⟩⟩

/-- For a faithfully flat ring map, ordinary singleton affine descent data
are equivalent to Beck coalgebras. -/
theorem affineStandardToCoalgebra_isEquivalence
    (hf : f.FaithfullyFlat) :
    (AffineStandardDescentData.toCoalgebra f).IsEquivalence := by
  let hff := affineStandardToCoalgebraFullyFaithful f
  letI : (AffineStandardDescentData.toCoalgebra f).Full := hff.full
  letI : (AffineStandardDescentData.toCoalgebra f).Faithful := hff.faithful
  letI : (AffineStandardDescentData.toCoalgebra f).EssSurj :=
    affineStandardToCoalgebra_essSurj f hf
  exact Functor.IsEquivalence.mk

/-- The canonical functor from modules to ordinary singleton affine descent
data. -/
noncomputable abbrev affineStandardDescentFunctor :
    ModuleCat A ⥤ AffineStandardDescentData f :=
  extendScalarsPseudofunctorOpOp.toDescentData
    (fun _ : Unit ↦ (CommRingCat.ofHom f).op)

/-- After passage to Beck coalgebras, the canonical ordinary descent functor
is naturally isomorphic to the comonadic comparison functor. -/
noncomputable def affineStandardDescentToCoalgebraIsoComparison :
    affineStandardDescentFunctor f ⋙
        AffineStandardDescentData.toCoalgebra f ≅
      Comonad.comparison (extendRestrictScalarsAdj.{u, u, u} f) :=
  NatIso.ofComponents (fun M ↦ by
    change (AffineStandardDescentData.toCoalgebra f).obj
        (AffineStandardDescentData.ofModule f M) ≅
      (Comonad.comparison (extendRestrictScalarsAdj.{u, u, u} f)).obj M
    exact AffineStandardDescentData.ofModuleCoalgebraIsoComparison f M) (by
    intro M N h
    apply Comonad.Coalgebra.Hom.ext'
    change (extendScalars f).map h ≫
        (AffineStandardDescentData.ofModuleCarrierIso f N).hom =
      (AffineStandardDescentData.ofModuleCarrierIso f M).hom ≫
        (extendScalars f).map h
    rw [AffineStandardDescentData.ofModuleCarrierIso_hom_eq_map_id,
      AffineStandardDescentData.ofModuleCarrierIso_hom_eq_map_id,
      ← Functor.map_comp, ← Functor.map_comp]
    simp)

/-- Faithfully flat singleton affine module descent is effective. -/
theorem affineStandardDescentFunctor_isEquivalence
    (hf : f.FaithfullyFlat) :
    (affineStandardDescentFunctor f).IsEquivalence := by
  letI : (AffineStandardDescentData.toCoalgebra f).IsEquivalence :=
    affineStandardToCoalgebra_isEquivalence f hf
  letI : (Comonad.comparison
      (extendRestrictScalarsAdj.{u, u, u} f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  letI : (affineStandardDescentFunctor f ⋙
      AffineStandardDescentData.toCoalgebra f).IsEquivalence := by
    rw [Functor.isEquivalence_iff_of_iso
      (affineStandardDescentToCoalgebraIsoComparison f)]
    infer_instance
  exact Functor.isEquivalence_of_comp_right
    (affineStandardDescentFunctor f)
    (AffineStandardDescentData.toCoalgebra f)

/-- The equivalence implementing effective faithfully flat singleton affine
descent for modules. Its functor is definitionally the canonical descent-data
functor. -/
noncomputable def affineStandardDescentEquivalence
    (hf : f.FaithfullyFlat) :
    ModuleCat A ≌ AffineStandardDescentData f := by
  letI : (affineStandardDescentFunctor f).IsEquivalence :=
    affineStandardDescentFunctor_isEquivalence f hf
  exact (affineStandardDescentFunctor f).asEquivalence

end ModuleCat
