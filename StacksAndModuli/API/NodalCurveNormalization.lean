module

public import StacksAndModuli.API.ReducedSchemeNormalization
public import StacksAndModuli.«Section6.2-Nodal».«part6.2.1-nodes»

/-!
# Normalization of a nodal curve

A nodal curve over an algebraically closed field is reduced and Noetherian. This file
specializes `AlgebraicGeometry.Scheme.normalization` to such a curve and packages the
required instances behind its nodality witness.

The construction is the normalization in the product of the function fields of the
irreducible components. Its map to the original curve is integral. The point fibre over
`x` is the eventual global model for the branches at `x`; comparison with the completed
local formal branches is developed separately.

## Main definitions

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationScheme`: the normalization of
  a nodal curve.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationMap`: its integral map to the
  curve.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationMapOver`: the same map bundled
  over the ground field.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationPointsOver`: the point fibre
  over a point of the curve.

## Main results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationMap_isIntegral`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationMap_isDominant`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationMap_isSchemeTheoreticallyDominant`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationScheme_isReduced`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The normalization of a nodal curve over an algebraically closed field.

The reducedness and finiteness of the irreducible-component set are consequences of the
nodal-curve hypothesis rather than additional inputs. -/
noncomputable def IsNodalCurveOver.normalizationScheme
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) : Scheme.{u} :=
  letI := h.isReduced
  letI := h.isNoetherian
  C.normalization

/-- The integral normalization morphism of a nodal curve. -/
noncomputable def IsNodalCurveOver.normalizationMap
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    h.normalizationScheme ⟶ C :=
  letI := h.isReduced
  letI := h.isNoetherian
  C.normalizationMap

/-- The normalization of a nodal curve inherits its structure morphism to the ground
field by composition with the normalization map. -/
noncomputable instance IsNodalCurveOver.normalizationScheme_over
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    h.normalizationScheme.Over (Spec (CommRingCat.of k)) :=
  ⟨h.normalizationMap ≫ (C ↘ Spec (CommRingCat.of k))⟩

/-- The normalization map commutes with the structure morphisms to the ground field. -/
@[reassoc (attr := simp)]
theorem IsNodalCurveOver.normalizationMap_over
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    h.normalizationMap ≫ (C ↘ Spec (CommRingCat.of k)) =
      h.normalizationScheme ↘ Spec (CommRingCat.of k) :=
  rfl

/-- The normalization map of a nodal curve, bundled as a morphism over the ground
field. -/
noncomputable def IsNodalCurveOver.normalizationMapOver
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    h.normalizationScheme.asOver (Spec (CommRingCat.of k)) ⟶
      C.asOver (Spec (CommRingCat.of k)) :=
  Over.homMk h.normalizationMap h.normalizationMap_over

/-- The normalization morphism of a nodal curve is integral. -/
theorem IsNodalCurveOver.normalizationMap_isIntegral
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    IsIntegralHom h.normalizationMap := by
  dsimp only [IsNodalCurveOver.normalizationMap]
  infer_instance

/-- The normalization morphism of a nodal curve has dense range. -/
theorem IsNodalCurveOver.normalizationMap_isDominant
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    IsDominant h.normalizationMap := by
  dsimp only [IsNodalCurveOver.normalizationMap]
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  infer_instance

/-- The normalization morphism of a nodal curve is scheme-theoretically dominant. Thus
its pullback maps on sections are injective. -/
theorem IsNodalCurveOver.normalizationMap_isSchemeTheoreticallyDominant
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    IsSchemeTheoreticallyDominant h.normalizationMap := by
  dsimp only [IsNodalCurveOver.normalizationMap]
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  infer_instance

/-- The normalization of a nodal curve is reduced. -/
theorem IsNodalCurveOver.normalizationScheme_isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    IsReduced h.normalizationScheme := by
  dsimp only [IsNodalCurveOver.normalizationScheme]
  infer_instance

/-- The type of points of the normalization of a nodal curve lying over `x`.

For a node, this is the canonical global candidate for its two branches. This definition
does not itself assert the comparison with the minimal primes of the completed local ring. -/
noncomputable def IsNodalCurveOver.normalizationPointsOver
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C) : Type u :=
  {y : h.normalizationScheme // h.normalizationMap y = x}

/-- The underlying normalization point of an element of the point fibre. -/
@[simp]
theorem IsNodalCurveOver.normalizationPointsOver_mk_coe
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C)
    (y : h.normalizationScheme) (hy : h.normalizationMap y = x) :
    ((⟨y, hy⟩ : h.normalizationPointsOver x) : h.normalizationScheme) = y :=
  rfl

end AlgebraicGeometry.Scheme
