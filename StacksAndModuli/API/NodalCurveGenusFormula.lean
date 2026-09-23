module

public import StacksAndModuli.API.NodalCurveNormalizationSmoothLocus
public import StacksAndModuli.API.NormalizationComponentCohomology
public import StacksAndModuli.API.NodalCurvePointSupport
public import StacksAndModuli.API.SheafCohomologyModuleLES
public import StacksAndModuli.API.StableMarkedGraph
public import StacksAndModuli.«Section6.1-Smooth».«part6.1.1-curves»

/-!
# The cohomological genus formula for a nodal curve

For the normalization `ν : C̃ ⟶ C` of a nodal curve, the classical normalization
sequence is

`0 ⟶ 𝒪_C ⟶ ν_* 𝒪_C̃ ⟶ Q ⟶ 0`.

Here `Q` is the defect of normality; for a split nodal curve it is one copy of the
residue field at every node.  This file packages the three sheaves and isolates the exact
cohomological data needed for the familiar formula

`g(C) = |E| + 1 - |V| + ∑_v g(C̃_v)`.

The final deduction is completely formal.  It applies the six-term cohomology sequence,
uses rank--nullity, and then uses connectedness of the supplied vertex-weighted graph to
make natural-number subtraction exact.  Scheme-theoretic dominance of the normalization
proves injectivity at the left end.  The local calculation of its defect, the cohomology
comparison with normalized components, and the remaining finiteness inputs are deliberately
exposed as named fields of `NormalizationCohomologyData` rather than hidden as axioms.
The connected proper curve's degree-zero structure cohomology is derived from the general
connected-reduced global-sections theorem.  Degree-zero cohomology of the normalization
pushforward is likewise derived from the componentwise normalization decomposition; the
caller need only identify the graph's vertex count with the number of components.

## Main definitions

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationPushforwardModule`: `ν_* 𝒪_C̃`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationUnit`: the map
  `𝒪_C ⟶ ν_* 𝒪_C̃`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationDefectModule`: its cokernel.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.NormalizationCohomologyData`: the geometric
  input to the genus formula, recorded with one field per required computation.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.NormalizationCohomologyData.of_nodeResidueSupportIso`:
  a comparison of the defect with the node residue module supplies all defect fields.

## Main results

* `AlgebraicGeometry.Scheme.Modules.genusOver_eq_graph_genus_of_normalizationCohomology`:
  the general six-term cohomological endgame.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationUnit_mono`: the structure sheaf
  embeds in its normalization pushforward.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationPushforward_h_zero_eq_componentCount`:
  degree-zero cohomology of the normalization pushforward counts components.
* `finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect`:
  finite-dimensional curve cohomology and vanishing defect cohomology imply finiteness
  for the normalization pushforward.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.genusOver_eq_graph_genus`: the endgame applied
  to the canonical normalization sequence of a nodal curve.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme

/-- The pushforward of the structure sheaf from the normalization of a nodal curve. -/
def IsNodalCurveOver.normalizationPushforwardModule
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) : C.Modules :=
  (Modules.pushforward h.normalizationMap).obj
    (structureModule h.normalizationScheme)

/-- Degree-zero cohomology of a proper nodal curve's normalization pushforward equals
the number of irreducible components. -/
theorem IsNodalCurveOver.normalizationPushforward_h_zero_eq_componentCount
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k) :
    Modules.h k h.normalizationPushforwardModule 0 =
      Nat.card (irreducibleComponents C) := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  exact AlgebraicGeometry.Scheme.normalizationPushforward_h_zero_eq_componentCount k C

/-- The canonical map from the structure sheaf of a nodal curve into the pushforward of
the structure sheaf of its normalization. -/
def IsNodalCurveOver.normalizationUnit
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    structureModule C ⟶ h.normalizationPushforwardModule :=
  SheafOfModules.unitToPushforwardObjUnit
    h.normalizationMap.toRingCatSheafHom

/-- The structure sheaf of a nodal curve embeds in the pushforward of the structure sheaf
of its normalization.

The normalization map is integral, hence quasi-compact, and is scheme-theoretically
dominant because the nodal curve is reduced.  Its maps on sections are therefore injective,
which is exactly monicity of the adjunction unit after forgetting the module structure. -/
theorem IsNodalCurveOver.normalizationUnit_mono
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    Mono h.normalizationUnit := by
  let _ : IsIntegralHom h.normalizationMap := h.normalizationMap_isIntegral
  let _ : QuasiCompact h.normalizationMap := by infer_instance
  let _ : IsSchemeTheoreticallyDominant h.normalizationMap :=
    h.normalizationMap_isSchemeTheoreticallyDominant
  apply Functor.mono_of_mono_map (SheafOfModules.forget C.ringCatSheaf)
  change Mono h.normalizationUnit.val
  apply PresheafOfModules.mono_of_injective
  intro U a b hab
  apply h.normalizationMap.app_injective U.unop
  change
    (h.normalizationMap.toRingCatSheafHom.hom.app U) a =
      (h.normalizationMap.toRingCatSheafHom.hom.app U) b at hab
  exact hab

/-- The defect-of-normality module of a nodal curve, defined as the cokernel of
`𝒪_C ⟶ ν_* 𝒪_C̃`. -/
abbrev IsNodalCurveOver.normalizationDefectModule
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) : C.Modules :=
  cokernel h.normalizationUnit

/-- The normalization-defect module of a nodal curve is supported at its split nodes. -/
theorem IsNodalCurveOver.normalizationDefectModule_stalkSupport_subset_splitNodeLocus
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    Modules.stalkSupport h.normalizationDefectModule ⊆
      {x : C | C.IsSplitNodeAt k x} :=
  h.normalizationDefect_stalkSupport_subset_splitNodeLocus

/-- The canonical complex `𝒪_C ⟶ ν_* 𝒪_C̃ ⟶ Q` attached to the
normalization of a nodal curve. -/
abbrev IsNodalCurveOver.normalizationComplex
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    ShortComplex C.Modules :=
  ShortComplex.mk h.normalizationUnit (cokernel.π h.normalizationUnit) (by simp)

/-- The canonical normalization complex of a nodal curve is short exact. -/
theorem IsNodalCurveOver.normalizationComplex_shortExact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    h.normalizationComplex.ShortExact := by
  let _ : Mono h.normalizationUnit := h.normalizationUnit_mono
  exact
    { exact := ShortComplex.exact_cokernel _
      mono_f := inferInstance
      epi_g := coequalizer.π_epi }

/-- If first cohomology of the curve is finite dimensional and first cohomology of the
normalization defect vanishes, then first cohomology of the normalization pushforward is
finite dimensional.

Indeed, the normalization long exact sequence makes the map from the curve term onto the
normalization-pushforward term surjective. -/
theorem
    IsNodalCurveOver.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) := by
  let _ : FiniteDimensional k
      (Modules.H (structureModule C) 1) := hcurve
  have hsurj : Function.Surjective
      (LinearMap.restrictScalars k
        (Modules.HMap h.normalizationUnit 1)) := by
    intro y
    exact ((Modules.exact_HMap_HMap h.normalizationComplex
      h.normalizationComplex_shortExact 1) y).mp
        (hdefect.elim _ _)
  exact Module.Finite.of_surjective
    (LinearMap.restrictScalars k
      (Modules.HMap h.normalizationUnit 1)) hsurj

namespace Modules

/-- The formal six-term-cohomology endgame for the genus formula.

The intended short exact sequence is
`0 ⟶ 𝒪_C ⟶ ν_* 𝒪_C̃ ⟶ Q ⟶ 0`.  The hypotheses say that

* `h⁰(𝒪_C) = 1`;
* `h⁰(ν_* 𝒪_C̃) = |V|` and `h¹(ν_* 𝒪_C̃) = ∑_v g(C̃_v)`;
* `h⁰(Q) = |E|` and `H¹(Q) = 0`.

Finite dimensionality of `H⁰(Q)` and `H¹(M)` is explicit because
`Module.finrank` does not satisfy rank--nullity on infinite-dimensional spaces.
Finite dimensionality of `H⁰(M)` follows from `h⁰(M) = |V| > 0`, and that of
`H¹(𝒪_C)` then follows formally from exactness and `H¹(Q) = 0`.
No geometric fact about normalization is used in this theorem. -/
theorem genusOver_eq_graph_genus_of_normalizationCohomology
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    {M Q : C.Modules} (i : structureModule C ⟶ M) (q : M ⟶ Q)
    (hiq : i ≫ q = 0)
    (hexact : (ShortComplex.mk i q hiq).ShortExact)
    (h_defect_H_one : Subsingleton (H Q 1))
    [FiniteDimensional k (H Q 0)] [FiniteDimensional k (H M 1)]
    (h_curve_h_zero : h k (structureModule C) 0 = 1)
    (h_normalization_h_zero : h k M 0 = G.vertexCount)
    (h_defect_h_zero : h k Q 0 = G.edgeCount)
    (h_normalization_h_one : h k M 1 = G.totalWeight) :
    genusOver k C = G.genus := by
  let S : ShortComplex C.Modules := ShortComplex.mk i q hiq
  let _ : FiniteDimensional k (H M 0) :=
    FiniteDimensional.of_finrank_pos (by
      rw [← h_def k M 0, h_normalization_h_zero]
      exact G.vertexCount_pos)
  let _ : Mono ((SheafOfModules.toSheaf C.ringCatSheaf).map i) :=
    (shortExact_map_toSheaf hexact).mono_f
  have hmiddle : Function.Surjective
      (LinearMap.restrictScalars k (HMap i 1)) := by
    intro y
    exact ((exact_HMap_HMap S hexact 1) y).mp
      (h_defect_H_one.elim _ _)
  let _ : FiniteDimensional k (H (structureModule C) 1) :=
    Module.Finite.of_exact
      (f := LinearMap.restrictScalars k (HDelta S hexact 0 1 rfl))
      (g := LinearMap.restrictScalars k (HMap i 1))
      (exact_HDelta_HMap S hexact 0 1 rfl) hmiddle
  have hlast : Function.Surjective
      (LinearMap.restrictScalars k (HMap q 1)) := by
    intro y
    exact ⟨0, h_defect_H_one.elim _ _⟩
  have hdim := Module.finrank_alternating_eq_zero_of_exact₆ (k := k)
    (a := LinearMap.restrictScalars k (HMap i 0))
    (b := LinearMap.restrictScalars k (HMap q 0))
    (c := LinearMap.restrictScalars k (HDelta S hexact 0 1 rfl))
    (d := LinearMap.restrictScalars k (HMap i 1))
    (e := LinearMap.restrictScalars k (HMap q 1))
    (injective_HMap_zero i)
    (exact_HMap_HMap S hexact 0)
    (exact_HMap_HDelta S hexact 0 1 rfl)
    (exact_HDelta_HMap S hexact 0 1 rfl)
    (exact_HMap_HMap S hexact 1)
    hlast
  dsimp only [S] at hdim
  have h_defect_h_one : Module.finrank k (H Q 1) = 0 := by
    let _ : Subsingleton (H Q 1) := h_defect_H_one
    exact Module.finrank_zero_of_subsingleton
  simp only [h_def] at h_curve_h_zero h_normalization_h_zero
  simp only [h_def] at h_defect_h_zero h_normalization_h_one
  rw [h_curve_h_zero, h_normalization_h_zero, h_defect_h_zero,
    h_normalization_h_one, h_defect_h_one] at hdim
  rw [genusOver_def, VertexWeightedMarkedGraph.genus_eq,
    VertexWeightedMarkedGraph.graphGenus_eq]
  have hvertices := G.vertexCount_le_edgeCount_add_one
  omega

end Modules

/-- The named geometric and finiteness inputs that turn the normalization sequence of a
nodal curve into the genus formula for a supplied vertex-weighted graph.

For the actual dual graph, `defect_h_zero` counts nodes and `normalization_h_one`
identifies the remaining cohomology with the sum of the component geometric genera.
Degree-zero cohomology of the normalization is computed automatically. -/
structure IsNodalCurveOver.NormalizationCohomologyData
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType) : Prop where
  /-- The defect-of-normality module has no first cohomology. -/
  defect_H_one_subsingleton : Subsingleton (Modules.H h.normalizationDefectModule 1)
  /-- Degree-zero cohomology of the defect module is finite dimensional. -/
  defect_H_zero_finiteDimensional :
    FiniteDimensional k (Modules.H h.normalizationDefectModule 0)
  /-- First cohomology of the normalization pushforward is finite dimensional. -/
  normalization_H_one_finiteDimensional :
    FiniteDimensional k (Modules.H h.normalizationPushforwardModule 1)
  /-- Global sections of the defect-of-normality module count the graph edges. -/
  defect_h_zero : Modules.h k h.normalizationDefectModule 0 = G.edgeCount
  /-- First cohomology of the normalization is the total geometric-genus weight. -/
  normalization_h_one :
    Modules.h k h.normalizationPushforwardModule 1 = G.totalWeight

/-- Comparing the normalization defect with one residue-field module at every node
implies that the defect has vanishing first cohomology. -/
theorem
    IsNodalCurveOver.subsingleton_H_normalizationDefectModule_one_of_nodeResidueSupportIso
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (e : h.normalizationDefectModule ≅ h.nodeResidueSupportModule) :
    Subsingleton (Modules.H h.normalizationDefectModule 1) := by
  let _ : Subsingleton (Modules.H h.nodeResidueSupportModule 1) :=
    h.subsingleton_H_nodeResidueSupportModule 0
  exact ⟨fun x y ↦ (Modules.HLinearEquivOfIso e 1).injective
    (Subsingleton.elim _ _)⟩

/-- A comparison between the normalization defect and the direct sum of residue-field
modules at the nodes automatically supplies every defect-side input to the genus formula.
Only the normalization's first-cohomology calculation remains to be provided. -/
theorem IsNodalCurveOver.NormalizationCohomologyData.of_nodeResidueSupportIso
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (e : h.normalizationDefectModule ≅ h.nodeResidueSupportModule)
    (normalization_H_one_finiteDimensional :
      FiniteDimensional k (Modules.H h.normalizationPushforwardModule 1))
    (normalization_h_one :
      Modules.h k h.normalizationPushforwardModule 1 = G.totalWeight) :
    h.NormalizationCohomologyData G := by
  let _ : FiniteDimensional k
      (Modules.H h.nodeResidueSupportModule 0) :=
    h.finiteDimensional_H_nodeResidueSupportModule_zero
  refine
    { defect_H_one_subsingleton := ?_
      defect_H_zero_finiteDimensional := ?_
      normalization_H_one_finiteDimensional :=
        normalization_H_one_finiteDimensional
      defect_h_zero := ?_
      normalization_h_one := normalization_h_one }
  · exact h.subsingleton_H_normalizationDefectModule_one_of_nodeResidueSupportIso e
  · exact Modules.finiteDimensional_H_of_iso k e.symm 0
  · exact (Modules.h_eq_of_iso k e 0).trans
      (h.h_nodeResidueSupportModule_zero.trans h_nodeCount)

/-- A nodal curve has the genus of a supplied vertex-weighted graph once its canonical
normalization sequence has the standard local and cohomological properties collected in
`NormalizationCohomologyData`. -/
theorem IsNodalCurveOver.genusOver_eq_graph_genus
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (D : h.NormalizationCohomologyData G) :
    genusOver k C = G.genus := by
  let _ : IsReduced C := h.isReduced
  let _ : FiniteDimensional k (Modules.H h.normalizationDefectModule 0) :=
    D.defect_H_zero_finiteDimensional
  let _ : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
    D.normalization_H_one_finiteDimensional
  apply Modules.genusOver_eq_graph_genus_of_normalizationCohomology G
    h.normalizationUnit (cokernel.π h.normalizationUnit) (by simp)
    h.normalizationComplex_shortExact D.defect_H_one_subsingleton
    (h_structureModule_zero_eq_one_of_isReduced_of_connected k C)
    (h.normalizationPushforward_h_zero_eq_componentCount.trans h_componentCount)
    D.defect_h_zero
    D.normalization_h_one

end AlgebraicGeometry.Scheme
