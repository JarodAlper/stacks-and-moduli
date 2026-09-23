module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Normalization of reduced schemes

Mathlib constructs the normalization of a target `Y` *inside a supplied qcqs morphism*
`f : X ⟶ Y`. This file specializes that relative construction to the usual normalization
of a reduced scheme with finitely many irreducible components.

The supplied morphism is the canonical map

`(∐ Z : irreducibleComponents X, Spec ᵊ_{X,η_Z}) ⟶ X`,

where `η_Z` is the generic point of `Z`. For a reduced scheme each generic-point stalk is
a field. Finiteness of the component set makes the source finite and affine, hence the map
is quasi-compact and quasi-separated and Mathlib's relative normalization applies.

`normalizationPointsOver X x` is the honest point fibre of the resulting normalization
map. It is the eventual home for the branches over a node; no cardinality statement is
asserted here. Proving that a split node has exactly two such points still requires a local
comparison between normalization and completed local rings.

## Main definitions

* `AlgebraicGeometry.Scheme.componentGenericScheme`: the disjoint union of the spectra of
  the component generic-point stalks.
* `AlgebraicGeometry.Scheme.componentGenericMap`: its canonical map to the scheme.
* `AlgebraicGeometry.Scheme.normalization`: the normalization of a reduced scheme with
  finitely many irreducible components.
* `AlgebraicGeometry.Scheme.normalizationMap`: the integral normalization morphism.
* `AlgebraicGeometry.Scheme.normalizationPointsOver`: the type of points of the
  normalization over a specified point.

## Main results

* `AlgebraicGeometry.Scheme.componentGenericToNormalization_normalizationMap`: the
  component-generic map factors through the normalization map.
* `AlgebraicGeometry.Scheme.componentGenericMap_isDominant`: the component-generic map
  has dense range.
* `AlgebraicGeometry.Scheme.normalizationMap_isSchemeTheoreticallyDominant`: on a reduced
  scheme, the normalization map is scheme-theoretically dominant.
* `AlgebraicGeometry.Scheme.normalization_isReduced`: this normalization is reduced.
* `AlgebraicGeometry.Scheme.componentPointInNormalization_injective`: distinct
  irreducible components give distinct points of the normalization.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A Noetherian scheme has only finitely many irreducible components. -/
noncomputable instance irreducibleComponents_finite_of_isNoetherian
    (X : Scheme.{u}) [IsNoetherian X] : Finite (irreducibleComponents X) :=
  finite_irreducibleComponents_of_isNoetherian.to_subtype

/-- The disjoint union of the spectra of the stalks at the generic points of the
irreducible components of `X`. -/
noncomputable def componentGenericScheme (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun Z : irreducibleComponents X =>
    Spec (X.presheaf.stalk Z.property.1.genericPoint)

/-- The canonical map from `componentGenericScheme X` to `X`. -/
noncomputable def componentGenericMap (X : Scheme.{u}) :
    X.componentGenericScheme ⟶ X :=
  Sigma.desc fun Z : irreducibleComponents X =>
    X.fromSpecStalk Z.property.1.genericPoint

/-- On a component summand, `componentGenericMap` is the canonical map from the spectrum
of the stalk at that component's generic point. -/
@[reassoc (attr := simp)]
lemma sigmaι_componentGenericMap (X : Scheme.{u}) (Z : irreducibleComponents X) :
    Sigma.ι (fun W : irreducibleComponents X =>
        Spec (X.presheaf.stalk W.property.1.genericPoint)) Z ≫
      X.componentGenericMap = X.fromSpecStalk Z.property.1.genericPoint := by
  unfold componentGenericMap
  simp

/-- The component-generic map has dense range: its image contains the generic point of
every irreducible component. -/
instance componentGenericMap_isDominant (X : Scheme.{u}) :
    IsDominant X.componentGenericMap := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]
    exact Set.mem_univ x
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
  let Z' : irreducibleComponents X := ⟨Z, hZ⟩
  have hgeneric : Z'.property.1.genericPoint ∈ Set.range X.componentGenericMap := by
    let z := IsLocalRing.closedPoint (X.presheaf.stalk Z'.property.1.genericPoint)
    refine ⟨Sigma.ι (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint)) Z' z, ?_⟩
    change (Sigma.ι (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint)) Z' ≫
        X.componentGenericMap) z = Z'.property.1.genericPoint
    rw [X.sigmaι_componentGenericMap Z']
    exact Scheme.fromSpecStalk_closedPoint
  apply closure_mono (Set.singleton_subset_iff.mpr hgeneric)
  rw [Z'.property.1.closure_genericPoint
    (isClosed_of_mem_irreducibleComponents Z'.1 Z'.property)]
  exact hxZ

/-- The stalk at the generic point of an irreducible component of a reduced scheme is a
field. -/
lemma componentGenericStalk_isField (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) :
    IsField (X.presheaf.stalk Z.property.1.genericPoint) :=
  isField_stalk_of_closure_mem_irreducibleComponents X Z.property.1.genericPoint (by
    rw [Z.property.1.closure_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.property)]
    exact Z.property)

/-- The spectrum of a component generic-point stalk of a reduced scheme is finite. -/
noncomputable instance componentGenericSpec_finite (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) :
    Finite (Spec (X.presheaf.stalk Z.property.1.genericPoint)) := by
  let _ : Subsingleton (Spec (X.presheaf.stalk Z.property.1.genericPoint)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr
      (X.componentGenericStalk_isField Z)
  exact Finite.of_subsingleton

/-- The spectrum of a component generic-point stalk of a reduced scheme is reduced. -/
noncomputable instance componentGenericSpec_isReduced (X : Scheme.{u}) [IsReduced X]
    (Z : irreducibleComponents X) :
    IsReduced (Spec (X.presheaf.stalk Z.property.1.genericPoint)) := by
  infer_instance

/-- If `X` is reduced and has finitely many irreducible components, its
component-generic-point scheme is finite. -/
noncomputable instance componentGenericScheme_finite (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : Finite X.componentGenericScheme := by
  exact (sigmaMk _).finite_iff.mp inferInstance

/-- A finite coproduct of the affine component-generic spectra is affine. -/
instance componentGenericScheme_isAffine (X : Scheme.{u})
    [Finite (irreducibleComponents X)] : IsAffine X.componentGenericScheme := by
  unfold componentGenericScheme
  infer_instance

/-- The component-generic map of a reduced scheme with finitely many irreducible
components is quasi-compact. -/
instance componentGenericMap_quasiCompact (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : QuasiCompact X.componentGenericMap := by
  exact ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

/-- The component-generic map of a scheme with finitely many irreducible components is
quasi-separated. -/
instance componentGenericMap_quasiSeparated (X : Scheme.{u})
    [Finite (irreducibleComponents X)] : QuasiSeparated X.componentGenericMap := by
  infer_instance

/-- The component-generic-point scheme of a reduced scheme is reduced. -/
noncomputable instance componentGenericScheme_isReduced (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : IsReduced X.componentGenericScheme := by
  change IsReduced (∐ fun Z : irreducibleComponents X =>
    Spec (X.presheaf.stalk Z.property.1.genericPoint))
  apply +allowSynthFailures @IsReduced.of_openCover
    (𝒰 := sigmaOpenCover fun Z : irreducibleComponents X =>
      Spec (X.presheaf.stalk Z.property.1.genericPoint))
  exact fun Z => by
    rw [sigmaOpenCover_X]
    infer_instance

/-- The normalization of a reduced scheme with finitely many irreducible components.

This is Mathlib's relative normalization of `X` inside `componentGenericMap X`, namely
the integral closure of the structure sheaf in the product of the component function
fields. -/
noncomputable abbrev normalization (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : Scheme.{u} :=
  X.componentGenericMap.normalization

/-- The integral normalization morphism `normalization X ⟶ X`. -/
noncomputable abbrev normalizationMap (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : X.normalization ⟶ X :=
  X.componentGenericMap.fromNormalization

/-- The canonical map from the component-generic-point scheme into the normalization. -/
noncomputable abbrev componentGenericToNormalization (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : X.componentGenericScheme ⟶ X.normalization :=
  X.componentGenericMap.toNormalization

/-- The component-generic map factors as the map into the normalization followed by the
normalization morphism. -/
@[reassoc (attr := simp)]
lemma componentGenericToNormalization_normalizationMap (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] :
    X.componentGenericToNormalization ≫ X.normalizationMap = X.componentGenericMap :=
  Hom.toNormalization_fromNormalization X.componentGenericMap

/-- The normalization morphism is integral. -/
instance normalizationMap_isIntegral (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : IsIntegralHom X.normalizationMap := by
  infer_instance

/-- The normalization map of a reduced scheme is dominant. -/
instance normalizationMap_isDominant (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : IsDominant X.normalizationMap := by
  let _ : IsDominant
      (X.componentGenericToNormalization ≫ X.normalizationMap) := by
    rw [X.componentGenericToNormalization_normalizationMap]
    infer_instance
  exact IsDominant.of_comp X.componentGenericToNormalization X.normalizationMap

/-- The normalization map of a reduced scheme is scheme-theoretically dominant. In
particular, its pullback maps on sections are injective. -/
instance normalizationMap_isSchemeTheoreticallyDominant
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)] :
    IsSchemeTheoreticallyDominant X.normalizationMap :=
  IsSchemeTheoreticallyDominant.of_isDominant X.normalizationMap

/-- The normalization constructed from the component function fields is reduced. -/
instance normalization_isReduced (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] : IsReduced X.normalization := by
  infer_instance

/-- The point of the normalization induced by the generic point of an irreducible
component. -/
noncomputable def componentPointInNormalization (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) : X.normalization :=
  X.componentGenericToNormalization (Sigma.ι (fun W : irreducibleComponents X =>
    Spec (X.presheaf.stalk W.property.1.genericPoint)) Z
      (IsLocalRing.closedPoint (X.presheaf.stalk Z.property.1.genericPoint)))

/-- The normalization point induced by a component maps to that component's generic
point. -/
@[simp]
lemma normalizationMap_componentPointInNormalization (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    X.normalizationMap (X.componentPointInNormalization Z) =
      Z.property.1.genericPoint := by
  change (X.componentGenericToNormalization ≫ X.normalizationMap)
    (Sigma.ι (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint)) Z
        (IsLocalRing.closedPoint (X.presheaf.stalk Z.property.1.genericPoint))) = _
  rw [X.componentGenericToNormalization_normalizationMap]
  let z := IsLocalRing.closedPoint (X.presheaf.stalk Z.property.1.genericPoint)
  refine (congrArg (fun f : Spec (X.presheaf.stalk Z.property.1.genericPoint) ⟶ X => f z)
    (X.sigmaι_componentGenericMap Z)).trans ?_
  exact Scheme.fromSpecStalk_closedPoint

/-- Distinct irreducible components determine distinct points of the normalization. -/
lemma componentPointInNormalization_injective (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] :
    Function.Injective X.componentPointInNormalization := by
  intro Z W hZW
  apply Subtype.ext
  have hp : Z.property.1.genericPoint = W.property.1.genericPoint := by
    rw [← X.normalizationMap_componentPointInNormalization Z,
      ← X.normalizationMap_componentPointInNormalization W, hZW]
  calc
    Z.1 = closure {Z.property.1.genericPoint} :=
      (Z.property.1.closure_genericPoint
        (isClosed_of_mem_irreducibleComponents _ Z.property)).symm
    _ = closure {W.property.1.genericPoint} := by rw [hp]
    _ = W.1 := W.property.1.closure_genericPoint
      (isClosed_of_mem_irreducibleComponents _ W.property)

/-- The type of points of the normalization lying over `x : X`.

For a nodal curve, this is the canonical candidate for the set of branches over a node.
The theorem that it has cardinality two is deliberately not part of this definition. -/
noncomputable def normalizationPointsOver (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (x : X) : Type u :=
  {y : X.normalization // X.normalizationMap y = x}

/-- The underlying normalization point of an element of `normalizationPointsOver` is its
first component. -/
@[simp]
lemma normalizationPointsOver_mk_coe (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (x : X) (y : X.normalization)
    (hy : X.normalizationMap y = x) :
    ((⟨y, hy⟩ : X.normalizationPointsOver x) : X.normalization) = y :=
  rfl

end AlgebraicGeometry.Scheme
