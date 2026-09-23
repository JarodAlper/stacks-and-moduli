module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Quasi-affine morphisms of schemes

This file provides the morphism-level companion of
`AlgebraicGeometry.Scheme.IsQuasiAffine`.  A morphism is quasi-affine when every base
change with affine target has quasi-affine source.  This test-scheme formulation is
equivalent to testing inverse images of affine opens and makes stability under arbitrary
base change formal by construction.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The auxiliary property that a morphism with affine target has quasi-affine source. -/
def quasiAffineOverAffine : MorphismProperty Scheme.{u} :=
  fun X Y _ => IsAffine Y → Scheme.IsQuasiAffine X

/-- A morphism `f : X ⟶ Y` of schemes is *quasi-affine* if every base change of `f`
whose target is affine has quasi-affine source.  Equivalently, the inverse image of every
affine open of `Y` is a quasi-affine scheme (Stacks 01SN). -/
def IsQuasiAffineHom : MorphismProperty Scheme.{u} :=
  (@quasiAffineOverAffine : MorphismProperty Scheme.{u}).universally

instance : (@IsQuasiAffineHom : MorphismProperty Scheme.{u}).RespectsIso := by
  rw [IsQuasiAffineHom]
  infer_instance

instance : (@IsQuasiAffineHom : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := by
  rw [IsQuasiAffineHom]
  infer_instance

/-- Affine morphisms of schemes are quasi-affine. -/
lemma isQuasiAffineHom_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    IsQuasiAffineHom f := by
  intro X' Y' i₁ i₂ f' h hY'
  let _ : IsAffine Y' := hY'
  let _ : IsAffineHom f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsAffineHom : MorphismProperty Scheme.{u})) h.flip (by infer_instance)
  let _ : IsAffine X' := isAffine_of_isAffineHom f'
  infer_instance

/-- A quasi-compact, locally finite-type, locally quasi-finite separated morphism is
quasi-affine.  This is the morphism-level form of the quasi-affine consequence of
Zariski's Main Theorem, and is stable under arbitrary base change by construction. -/
lemma isQuasiAffineHom_of_quasiCompact_locallyOfFiniteType_locallyQuasiFinite_isSeparated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f] : IsQuasiAffineHom f := by
  intro X' Y' i₁ i₂ f' h hY'
  letI : IsAffine Y' := hY'
  letI : QuasiCompact f' := MorphismProperty.of_isPullback
    (P := @QuasiCompact) h.flip inferInstance
  letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback
    (P := @LocallyOfFiniteType) h.flip inferInstance
  letI : LocallyQuasiFinite f' := MorphismProperty.of_isPullback
    (P := @LocallyQuasiFinite) h.flip inferInstance
  letI : IsSeparated f' := MorphismProperty.of_isPullback
    (P := @IsSeparated) h.flip inferInstance
  letI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  letI : IsAffine f'.normalization := isAffine_of_isAffineHom f'.fromNormalization
  exact Scheme.IsQuasiAffine.of_isImmersion f'.toNormalization

end AlgebraicGeometry
