module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import StacksAndModuli.API.BaseChangePi
public import StacksAndModuli.API.SpecSections
public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.API.KernelBaseChange
public import StacksProject.Algebra.LociMaps.«lemma-cokernel-flat»
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Flat.LocallyFree
public import StacksAndModuli.API.FittingIdeal
public import StacksAndModuli.API.LocalSpanSelection
public import StacksAndModuli.API.FractionRingContraction
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Representability of the Grassmannian by a scheme

This module formalizes the first subsection ("Representability by a scheme") of
Section 2.2 (Projectivity of the Grassmannian) of Chapter 2 of *Stacks and Moduli*,
label `sec:grassmannian`: the chart
subfunctors `Gr_I ⊆ Gr(q, n)` (`eqn:GrI`), their representability by affine space
(`lem:grassmannian-open-representable`), the fact that they form a Zariski open cover
(`lem:grassmannian-open-subfunctor`), and the representability of `Gr(q, n)` by a scheme
(`prop:grassmannian-representable-scheme`), together with the unlabelled smoothness
exercise and the properness exercise (`exer:grassmannian-valuative-criterion`), proved
via the valuative criterion of properness.

In the kernel encoding of `Gr(q, n)` (a point is a quasi-coherent submodule sheaf
`K ⊆ O_T^{⊕n}` with rank-`q` locally free quotient), the chart condition "the composite
`O_T^{⊕I} → O_T^{⊕n} → O_T^{⊕n}/K` is an isomorphism" becomes: `K` is a complement of the
submodule of sections supported in the coordinates `I`.

Main book results:
- `AlgebraicGeometry.Scheme.grassmannianChart_representableBy_affineSpace`
  (`lem:grassmannian-open-representable`).
- `AlgebraicGeometry.Scheme.presheaf_isOpenImmersion_grassmannianChartι` and
  `AlgebraicGeometry.Scheme.isLocallySurjective_grassmannianChartι`
  (`lem:grassmannian-open-subfunctor`).
- `AlgebraicGeometry.Scheme.isRepresentable_grassmannianFunctor`
  (`prop:grassmannian-representable-scheme`).
- `AlgebraicGeometry.Scheme.isProper_of_grassmannianFunctor_representableBy`
  (`exer:grassmannian-valuative-criterion`): a representing Grassmannian is proper over
  `Spec ℤ`.
-/

@[expose] public section


section LemGrassmannianOpenRepresentable

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Limits

variable {T : Scheme.{u}} {n : ℕ}

/-- Background definition for Equation 2.2.1 (the chart condition, in the kernel encoding): let
`K ⊆ O_T^{⊕n}` be a quasi-coherent submodule sheaf and `I` a set of coordinates.
On every affine open, `K` is a complement of the submodule of sections supported in the
coordinates `I`. This is the chart condition cutting out the subfunctor `Gr_I ⊆ Gr(q, n)`:
it is equivalent to the composite `O_T^{⊕I} → O_T^{⊕n} → O_T^{⊕n}/K` being an
isomorphism. -/
def SubmoduleSheafData.IsComplementOfCoords (I : Finset (Fin n))
    (K : T.SubmoduleSheafData n) : Prop :=
  ∀ U : T.affineOpens,
    IsCompl (K.submodule U) (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)

/-- The zeroth Fitting ideal on an affine open of the cokernel of the coordinate map
indexed by `I`: the kernel datum is the submodule together with the vectors supported
in `I` (which form `Submodule.pi ↑(Iᶜ) ⊥`).

Stacks 07Z8/07ZA, sheaf-level packaging; §2.2 Equation 2.2.1. -/
noncomputable def SubmoduleSheafData.coordinateFittingIdealAt
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens) :
    Ideal Γ(T, U.1) :=
  (K.submodule U ⊔ Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
    (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1)))).fittingIdeal 0

/-- The coordinate Fitting ideal is the unit ideal exactly when the chosen coordinates
generate the quotient on that affine open. -/
theorem SubmoduleSheafData.coordinateFittingIdealAt_eq_top_iff
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens) :
    K.coordinateFittingIdealAt I U = ⊤ ↔
      Codisjoint (K.submodule U)
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1)))) := by
  rw [coordinateFittingIdealAt, Submodule.fittingIdeal_zero_eq_top_iff,
    codisjoint_iff]

/-- The coordinate Fitting ideal localizes: on a basic open it is the image ideal.
This is the compatibility that lets the non-generating locus glue to a closed subset
(Stacks 07ZD, sheaf form). -/
theorem SubmoduleSheafData.coordinateFittingIdealAt_basicOpen
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens)
    (f : Γ(T, U.1)) :
    K.coordinateFittingIdealAt I (T.affineBasicOpen f) =
      Ideal.map (T.presheaf.map (homOfLE (show (T.affineBasicOpen f).1 ≤ U.1 from
        T.basicOpen_le f)).op).hom (K.coordinateFittingIdealAt I U) := by
  set φ := (T.presheaf.map (homOfLE (show (T.affineBasicOpen f).1 ≤ U.1 from
    T.basicOpen_le f)).op).hom with hφ
  have hsub : K.submodule (T.affineBasicOpen f) ⊔
      Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(T, (T.affineBasicOpen f).1)
          Γ(T, (T.affineBasicOpen f).1))) =
      Submodule.span Γ(T, (T.affineBasicOpen f).1)
        ((fun w (i : Fin n) ↦ φ (w i)) ''
          (((K.submodule U ⊔ Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
            (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1)))) :
              Submodule Γ(T, U.1) (Fin n → Γ(T, U.1))) :
              Set (Fin n → Γ(T, U.1)))) := by
    rw [Submodule.span_image_piMap_sup]
    congr 1
    · exact (K.span_resPi_basicOpen U f).symm
    · exact (Submodule.span_image_piMap_piBot φ I).symm
  rw [coordinateFittingIdealAt, hsub, Submodule.fittingIdeal_span_image_map]
  rfl

/-- The open locus where the coordinates indexed by `I` generate the quotient: the union
of the basic opens of sections of the coordinate Fitting ideal.

Stacks 07ZD (the non-vanishing locus of `Fit₀` of the coordinate cokernel);
§2.2 Equation 2.2.1. -/
noncomputable def SubmoduleSheafData.coordinateChartOpen
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) : T.Opens :=
  ⨆ (U : T.affineOpens) (f : Γ(T, U.1)) (_ : f ∈ K.coordinateFittingIdealAt I U),
    (T.basicOpen f : T.Opens)

/-- Basic opens of Fitting-ideal sections are contained in the chart open. -/
theorem SubmoduleSheafData.basicOpen_le_coordinateChartOpen
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens)
    {f : Γ(T, U.1)} (hf : f ∈ K.coordinateFittingIdealAt I U) :
    T.basicOpen f ≤ K.coordinateChartOpen I := by
  refine le_trans (le_iSup (fun _ : f ∈ K.coordinateFittingIdealAt I U ↦
    (T.basicOpen f : T.Opens)) hf) ?_
  refine le_trans (le_iSup (fun g : Γ(T, U.1) ↦
    ⨆ (_ : g ∈ K.coordinateFittingIdealAt I U), (T.basicOpen g : T.Opens)) f) ?_
  exact le_iSup (fun V : T.affineOpens ↦ ⨆ (g : Γ(T, V.1))
    (_ : g ∈ K.coordinateFittingIdealAt I V), (T.basicOpen g : T.Opens)) U

/-- If the coordinates generate on an affine open, that open lies in the chart open. -/
theorem SubmoduleSheafData.le_coordinateChartOpen_of_codisjoint
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens)
    (h : Codisjoint (K.submodule U)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1))))) :
    U.1 ≤ K.coordinateChartOpen I := by
  have h1 : (1 : Γ(T, U.1)) ∈ K.coordinateFittingIdealAt I U := by
    rw [(K.coordinateFittingIdealAt_eq_top_iff I U).mpr h]
    trivial
  refine le_trans ?_ (K.basicOpen_le_coordinateChartOpen I U h1)
  rw [Scheme.basicOpen_one]

/-- Conversely, every point of the chart open has a basic-open neighbourhood on which
the chosen coordinates generate: the localized Fitting ideal contains the inverted
function, hence is the unit ideal. -/
theorem SubmoduleSheafData.exists_basicOpen_codisjoint_of_mem_coordinateChartOpen
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) {x : T}
    (hx : x ∈ K.coordinateChartOpen I) :
    ∃ (U : T.affineOpens) (f : Γ(T, U.1)), x ∈ T.basicOpen f ∧
      Codisjoint (K.submodule (T.affineBasicOpen f))
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          (fun _ ↦ (⊥ : Submodule Γ(T, (T.affineBasicOpen f).1)
            Γ(T, (T.affineBasicOpen f).1)))) := by
  rw [coordinateChartOpen] at hx
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp hU
  obtain ⟨hmem, hxf⟩ := TopologicalSpace.Opens.mem_iSup.mp hf
  refine ⟨U, f, hxf, ?_⟩
  rw [← K.coordinateFittingIdealAt_eq_top_iff I (T.affineBasicOpen f)]
  set φ := (T.presheaf.map (homOfLE (show (T.affineBasicOpen f).1 ≤ U.1 from
    T.basicOpen_le f)).op).hom with hφ
  letI : Algebra Γ(T, U.1) Γ(T, (T.affineBasicOpen f).1) := φ.toAlgebra
  haveI : IsLocalization.Away f Γ(T, (T.affineBasicOpen f).1) :=
    U.2.isLocalization_basicOpen f
  have hunit : IsUnit (φ f) :=
    IsLocalization.map_units Γ(T, (T.affineBasicOpen f).1)
      (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)
  have hmem' : φ f ∈ K.coordinateFittingIdealAt I (T.affineBasicOpen f) := by
    rw [K.coordinateFittingIdealAt_basicOpen I U f]
    exact Ideal.mem_map_of_mem φ hmem
  exact Ideal.eq_top_of_isUnit_mem _ hmem' hunit

/-- Codisjointness of the coordinates is implied by chart-open coverage: if an affine open
is contained in the chart open, the coordinates generate on it. The proof is ideal-theoretic:
the sections whose basic opens are chart-good cover `U`, hence generate the unit ideal; each
lies in the radical of the coordinate Fitting ideal by the localization criterion; so the
Fitting ideal is the unit ideal. -/
theorem SubmoduleSheafData.codisjoint_of_le_coordinateChartOpen
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens)
    (hU : U.1 ≤ K.coordinateChartOpen I) :
    Codisjoint (K.submodule U)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1)))) := by
  rw [← K.coordinateFittingIdealAt_eq_top_iff I U]
  set s : Set Γ(T, U.1) :=
    {h | K.coordinateFittingIdealAt I (T.affineBasicOpen h) = ⊤} with hs
  have hcover : ⨆ h : s, T.basicOpen (h : Γ(T, U.1)) = U.1 := by
    apply le_antisymm
    · exact iSup_le fun h ↦ T.basicOpen_le h.1
    · intro x hxU
      have hx := hU hxU
      obtain ⟨V, f, hxf, hcod⟩ :=
        K.exists_basicOpen_codisjoint_of_mem_coordinateChartOpen I hx
      obtain ⟨c₁, c₂, hc, hxc⟩ := exists_basicOpen_le_affine_inter U.2
        (T.affineBasicOpen f).2 x ⟨hxU, hxf⟩
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c₁, ?_⟩, hxc⟩
      show K.coordinateFittingIdealAt I (T.affineBasicOpen c₁) = ⊤
      have hcodc₂ : K.coordinateFittingIdealAt I (T.affineBasicOpen c₂) = ⊤ := by
        rw [K.coordinateFittingIdealAt_basicOpen I (T.affineBasicOpen f) c₂,
          (K.coordinateFittingIdealAt_eq_top_iff I (T.affineBasicOpen f)).mpr hcod,
          Ideal.map_top]
      have heq : T.affineBasicOpen c₁ = T.affineBasicOpen c₂ := Subtype.ext hc
      rw [heq]
      exact hcodc₂
  have hspan : Ideal.span s = ⊤ := (U.2.iSup_basicOpen_eq_self_iff).mp hcover
  have hsub : s ⊆ ((K.coordinateFittingIdealAt I U).radical : Set Γ(T, U.1)) := by
    intro h hh
    letI : Algebra Γ(T, U.1) Γ(T, (T.affineBasicOpen h).1) :=
      (T.presheaf.map (homOfLE (show (T.affineBasicOpen h).1 ≤ U.1 from
        T.basicOpen_le h)).op).hom.toAlgebra
    haveI : IsLocalization.Away h Γ(T, (T.affineBasicOpen h).1) :=
      U.2.isLocalization_basicOpen h
    have hmap : Ideal.map (algebraMap Γ(T, U.1) Γ(T, (T.affineBasicOpen h).1))
        (K.coordinateFittingIdealAt I U) = ⊤ := by
      rw [show algebraMap Γ(T, U.1) Γ(T, (T.affineBasicOpen h).1) =
          (T.presheaf.map (homOfLE (show (T.affineBasicOpen h).1 ≤ U.1 from
            T.basicOpen_le h)).op).hom from rfl,
        ← K.coordinateFittingIdealAt_basicOpen I U h]
      exact hh
    have hnd : ¬ Disjoint ((Submonoid.powers h : Submonoid Γ(T, U.1)) : Set Γ(T, U.1))
        ((K.coordinateFittingIdealAt I U) : Set Γ(T, U.1)) := by
      intro hd
      exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint
        (M := Submonoid.powers h) (S := Γ(T, (T.affineBasicOpen h).1))
        (K.coordinateFittingIdealAt I U)).mpr hd hmap
    obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.mp hnd
    obtain ⟨m, rfl⟩ := hy1
    exact ⟨m, hy2⟩
  have hle : (⊤ : Ideal Γ(T, U.1)) ≤ (K.coordinateFittingIdealAt I U).radical := by
    rw [← hspan]
    exact Ideal.span_le.mpr hsub
  exact Ideal.radical_eq_top.mp (top_le_iff.mp hle)

/-- View the Chapter 2 submodule-sheaf encoding as the equivalent `PiSubmoduleData` encoding,
so that the Fitting-ideal and support APIs apply. `PiSubmoduleData` and those APIs are
outstanding obligations (Fitting ideals: Stacks 07Z8–07ZD; loci of maps of finite projective
modules: Stacks 00O0). -/
lemma isCompl_span_image_pi_of_isCompl {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (I : Finset (Fin n)) {W : Submodule A (Fin n → A)}
    (h : IsCompl W (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    IsCompl
      (Submodule.span B ((fun w (i : Fin n) ↦ φ (w i)) '' (W : Set (Fin n → A))))
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
  classical
  -- For each `j ∈ Iᶜ` pick `w_j ∈ W` whose coordinates on `Iᶜ` are the delta at `j`.
  have hexists : ∀ j ∈ Iᶜ, ∃ w ∈ W, ∀ k ∈ Iᶜ, w k = if k = j then 1 else 0 := by
    intro j hj
    have htop : (Pi.single j 1 : Fin n → A) ∈
        W ⊔ Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) (fun _ ↦ (⊥ : Submodule A A)) := by
      rw [codisjoint_iff.mp h.codisjoint]; trivial
    obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp htop
    refine ⟨w, hw, fun k hk ↦ ?_⟩
    have hck : c k = 0 := hc k (by simpa using hk)
    have hk' := congrFun hwc k
    simp only [Pi.add_apply, hck, add_zero] at hk'
    rw [hk', Pi.single_apply]
  choose! wfun hwmem hwcoord using hexists
  -- Every element of `W` is the `A`-combination of the `w_j` with its own coordinates.
  have hcombo : ∀ w ∈ W, w = ∑ j ∈ Iᶜ, w j • wfun j := by
    intro w hw
    have hmemW : w - ∑ j ∈ Iᶜ, w j • wfun j ∈ W :=
      Submodule.sub_mem _ hw
        (Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ (hwmem j hj))
    have hmemC : w - ∑ j ∈ Iᶜ, w j • wfun j ∈
        Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) (fun _ ↦ (⊥ : Submodule A A)) := by
      intro k hk
      have hk' : k ∈ Iᶜ := by simpa using hk
      have hsum : (∑ j ∈ Iᶜ, w j • wfun j) k = w k := by
        rw [Finset.sum_apply]
        have : ∀ j ∈ Iᶜ, (w j • wfun j) k = if k = j then w j else 0 := by
          intro j hj
          rw [Pi.smul_apply, smul_eq_mul, hwcoord j hj k hk']
          by_cases hkj : k = j <;> simp [hkj]
        rw [Finset.sum_congr rfl this]
        simp [Finset.sum_ite_eq' Iᶜ k, hk']
      simp [Pi.sub_apply, hsum]
    have h0 := Submodule.disjoint_def.mp h.disjoint _ hmemW hmemC
    exact sub_eq_zero.mp h0
  constructor
  · -- disjointness after base change
    rw [Submodule.disjoint_def]
    intro v hv hvC
    -- every element of the span satisfies: it is the combination of `φ ∘ w_j` with its
    -- own coordinates
    have hgraph : ∀ u ∈ Submodule.span B
        ((fun w (i : Fin n) ↦ φ (w i)) '' (W : Set (Fin n → A))),
        u = ∑ j ∈ Iᶜ, u j • (fun i ↦ φ (wfun j i)) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu' =>
        obtain ⟨w, hw, rfl⟩ := hu'
        conv_lhs => rw [hcombo w hw]
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        simp [map_mul, hwcoord j hj]
      | zero => simp
      | add a b _ _ iha ihb =>
        conv_lhs => rw [iha, ihb]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Pi.add_apply, add_smul]
      | smul b a _ iha =>
        conv_lhs => rw [iha]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_smul]
    have hv' := hgraph v hv
    have hcoords : ∀ j ∈ Iᶜ, v j = 0 := fun j hj ↦ hvC j (by simpa using hj)
    rw [hv']
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [hcoords j hj, zero_smul]
  · -- codisjointness after base change
    rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hy : (∑ j ∈ Iᶜ, x j • (fun i ↦ φ (wfun j i))) ∈ Submodule.span B
        ((fun w (i : Fin n) ↦ φ (w i)) '' (W : Set (Fin n → A))) :=
      Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _
        (Submodule.subset_span ⟨wfun j, hwmem j hj, rfl⟩)
    have hxy : x - ∑ j ∈ Iᶜ, x j • (fun i ↦ φ (wfun j i)) ∈
        Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) (fun _ ↦ (⊥ : Submodule B B)) := by
      intro k hk
      have hk' : k ∈ Iᶜ := by simpa using hk
      have hsum : (∑ j ∈ Iᶜ, x j • (fun i ↦ φ (wfun j i))) k = x k := by
        rw [Finset.sum_apply]
        have : ∀ j ∈ Iᶜ, (x j • (fun i ↦ φ (wfun j i))) k
            = if k = j then x j else 0 := by
          intro j hj
          rw [Pi.smul_apply, smul_eq_mul]
          rw [show φ (wfun j k) = if k = j then 1 else 0 by
            rw [hwcoord j hj k hk']; by_cases hkj : k = j <;> simp [hkj]]
          by_cases hkj : k = j <;> simp [hkj]
        rw [Finset.sum_congr rfl this]
        simp [Finset.sum_ite_eq' Iᶜ k, hk']
      simp [Pi.sub_apply, hsum]
    have : x = (∑ j ∈ Iᶜ, x j • (fun i ↦ φ (wfun j i)))
        + (x - ∑ j ∈ Iᶜ, x j • (fun i ↦ φ (wfun j i))) := by abel
    rw [this]
    exact Submodule.add_mem_sup hy hxy
def coordinateGraph {R : Type*} [CommRing R] {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) : Submodule R (Fin n → R) where
  carrier := {v : Fin n → R | ∀ (i : Fin n) (hi : i ∈ I),
    v i = ∑ j : ↑(Iᶜ), a ⟨i, hi⟩ j * v j.1}
  zero_mem' := by
    intro i hi
    simp
  add_mem' := by
    intro x y hx hy i hi
    rw [Pi.add_apply, hx i hi, hy i hi]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro r x hx i hi
    rw [Pi.smul_apply, smul_eq_mul, hx i hi]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change r * (a ⟨i, hi⟩ j * x j.1) = a ⟨i, hi⟩ j * (r * x j.1)
    ring

@[simp]
lemma mem_coordinateGraph {R : Type*} [CommRing R] {n : ℕ} {I : Finset (Fin n)}
    {a : (i : ↑I) → (j : ↑(Iᶜ)) → R} {v : Fin n → R} :
    v ∈ coordinateGraph I a ↔ ∀ (i : Fin n) (hi : i ∈ I),
      v i = ∑ j : ↑(Iᶜ), a ⟨i, hi⟩ j * v j.1 :=
  Iff.rfl

/-- The rank-one coordinate functional with coefficient vector `c`. -/
def coordinateFunctional {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin n → R) : (Fin n → R) →ₗ[R] R where
  toFun v := ∑ k, c k * v k
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

/-- A linear functional on a finite product is the coordinate functional whose
coefficients are its values on the standard basis vectors. -/
lemma linearMap_eq_coordinateFunctional {R : Type*} [CommRing R] {n : ℕ}
    (f : (Fin n → R) →ₗ[R] R) :
    f = coordinateFunctional (fun i ↦ f (Pi.single i 1)) := by
  apply LinearMap.pi_ext
  intro i r
  have hsingle : Pi.single i r = r • Pi.single i 1 := by
    ext j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [hsingle, map_smul]
  simp only [coordinateFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [hji]
  · simp

/-- If one coefficient of a rank-one coordinate functional is `1`, its kernel is
the singleton chart graph whose remaining coefficients are the negatives of the
other functional coefficients. -/
lemma ker_coordinateFunctional_eq_coordinateGraph_singleton
    {R : Type*} [CommRing R] {n : ℕ} (c : Fin n → R) (s : Fin n)
    (hs : c s = 1) :
    LinearMap.ker (coordinateFunctional c) =
      coordinateGraph ({s} : Finset (Fin n))
        (fun _ j ↦ -c j.1) := by
  classical
  ext v
  simp only [LinearMap.mem_ker, mem_coordinateGraph]
  have hsplit := Finset.sum_add_sum_compl ({s} : Finset (Fin n))
    (fun k ↦ c k * v k)
  simp only [Finset.sum_singleton, hs, one_mul] at hsplit
  have hcomp (t : Fin n) :
      (∑ k ∈ ({t} : Finset (Fin n))ᶜ, c k * v k) =
        ∑ j : ↑(({t} : Finset (Fin n))ᶜ), c j.1 * v j.1 :=
    Finset.sum_subtype _ (fun _ ↦ Iff.rfl) _
  constructor
  · intro hv k hk
    obtain rfl := Finset.mem_singleton.mp hk
    change (∑ k, c k * v k) = 0 at hv
    rw [← hsplit] at hv
    rw [add_eq_zero_iff_eq_neg] at hv
    calc
      v k = -∑ l ∈ ({k} : Finset (Fin n))ᶜ, c l * v l := hv
      _ = ∑ j : ↑(({k} : Finset (Fin n))ᶜ), -c j.1 * v j.1 := by
        rw [hcomp]
        simp only [Finset.sum_neg_distrib, neg_mul]
  · intro hv
    have hscoord := hv s (Finset.mem_singleton_self s)
    change (∑ k, c k * v k) = 0
    rw [← hsplit, add_eq_zero_iff_eq_neg]
    calc
      v s = ∑ j : ↑(({s} : Finset (Fin n))ᶜ), -c j.1 * v j.1 := hscoord
      _ = -∑ k ∈ ({s} : Finset (Fin n))ᶜ, c k * v k := by
        rw [hcomp]
        simp only [Finset.sum_neg_distrib, neg_mul]

/-- The kernel of an arbitrary linear functional whose `s`th standard-basis value is
`1` is the singleton coordinate graph with the remaining negated basis values. -/
lemma ker_linearMap_eq_coordinateGraph_singleton
    {R : Type*} [CommRing R] {n : ℕ} (f : (Fin n → R) →ₗ[R] R) (s : Fin n)
    (hs : f (Pi.single s 1) = 1) :
    LinearMap.ker f = coordinateGraph ({s} : Finset (Fin n))
      (fun _ j ↦ -f (Pi.single j.1 1)) := by
  calc
    LinearMap.ker f = LinearMap.ker
        (coordinateFunctional (fun i ↦ f (Pi.single i 1))) :=
      congrArg LinearMap.ker (linearMap_eq_coordinateFunctional f)
    _ = _ := ker_coordinateFunctional_eq_coordinateGraph_singleton
      (fun i ↦ f (Pi.single i 1)) s hs

/-- A finite-free presentation of the unit sheaf with pivot coefficient `1` has the
expected singleton coordinate-graph kernel on affine global sections. -/
lemma Modules.FreeQuotient.ker_unitPresentationLinearMapPi_eq_coordinateGraph_singleton
    {R : CommRingCat.{u}} {n : ℕ}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) (s : Fin n)
    (hs : Modules.FreeQuotient.unitPresentationCoefficient π s = 1) :
    LinearMap.ker (Modules.FreeQuotient.unitPresentationLinearMapPi π) =
      coordinateGraph ({s} : Finset (Fin n))
        (fun _ j ↦ -Modules.FreeQuotient.unitPresentationCoefficient π j.1) :=
  ker_linearMap_eq_coordinateGraph_singleton
    (Modules.FreeQuotient.unitPresentationLinearMapPi π) s hs

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The affine coefficient of a unit-sheaf presentation is the corresponding global
section, transported back across the canonical affine unit-module isomorphism. -/
lemma Modules.FreeQuotient.unitPresentationCoefficient_eq_freeHomEquiv
    {R : CommRingCat.{u}} {n : ℕ}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) (i : Fin n) :
    Modules.FreeQuotient.unitPresentationCoefficient π i =
      (unitModuleSpecΓIso R).inv.hom
        (((SheafOfModules.unit (Spec R).ringCatSheaf).freeHomEquiv π
          (ULift.up i)).1 (op ⊤)) := by
  rw [Modules.FreeQuotient.unitPresentationCoefficient_eq]
  congr 1
  rw [unitModuleSpecΓIso_hom_one]
  simp only [map_one]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  change (SheafOfModules.ιFree (ULift.up i) ≫ π).val.app (op ⊤)
    (1 : Γ(Spec R, ⊤)) = _
  rw [← SheafOfModules.unitHomEquiv_apply_coe]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- If a generator of a finite-free presentation of the unit sheaf gives the unit
global section, its affine coefficient is `1`. -/
lemma Modules.FreeQuotient.unitPresentationCoefficient_eq_one
    {R : CommRingCat.{u}} {n : ℕ}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) (i : Fin n)
    (hi : ((SheafOfModules.unit (Spec R).ringCatSheaf).freeHomEquiv π
      (ULift.up i)).1 (op ⊤) = (1 : Γ(Spec R, ⊤))) :
    Modules.FreeQuotient.unitPresentationCoefficient π i = 1 := by
  rw [Modules.FreeQuotient.unitPresentationCoefficient_eq_freeHomEquiv, hi]
  have hone := unitModuleSpecΓIso_hom_one R
  simp only [map_one] at hone
  rw [← hone]
  exact (unitModuleSpecΓIso R).hom_inv_id_apply 1

/-- A coordinate graph is complementary to the coordinate summand supported on `I`.
This is the algebraic heart of the standard affine cover of the Grassmannian. -/
lemma isCompl_coordinateGraph {R : Type*} [CommRing R] {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    IsCompl (coordinateGraph I a)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro v hvGraph hvCoord
    rw [Submodule.mem_pi] at hvCoord
    funext i
    by_cases hi : i ∈ I
    · rw [(mem_coordinateGraph.mp hvGraph) i hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hjc : j.1 ∉ I := by simpa only [Finset.mem_compl] using j.2
      rw [(Submodule.mem_bot R).mp (hvCoord j.1 (by simp [hjc])), mul_zero]
    · exact (Submodule.mem_bot R).mp (hvCoord i (by simp [hi]))
  · rw [codisjoint_iff_le_sup]
    intro v hv
    let k : Fin n → R := fun i ↦ if hi : i ∈ I then
      ∑ j : ↑(Iᶜ), a ⟨i, hi⟩ j * v j.1 else v i
    have hk : k ∈ coordinateGraph I a := by
      rw [mem_coordinateGraph]
      intro i hi
      rw [show k i = ∑ j : ↑(Iᶜ), a ⟨i, hi⟩ j * v j.1 by simp [k, hi]]
      apply Finset.sum_congr rfl
      intro j hj
      have hjc : j.1 ∉ I := by simpa only [Finset.mem_compl] using j.2
      rw [show k j.1 = v j.1 by simp [k, hjc]]
    have hsub : v - k ∈
        Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          fun _ ↦ (⊥ : Submodule R R) := by
      rw [Submodule.mem_pi]
      intro i hi
      have hic : i ∈ Iᶜ := hi
      have hni : i ∉ I := Finset.mem_compl.mp hic
      rw [Submodule.mem_bot, Pi.sub_apply, show k i = v i by simp [k, hni], sub_self]
    exact Submodule.mem_sup.mpr ⟨k, hk, v - k, hsub, by abel⟩

/-- The standard graph vector associated to a complementary coordinate. -/
def coordinateGraphGenerator {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (j : ↑(Iᶜ)) :
    Fin n → R := fun i ↦ if hi : i ∈ I then a ⟨i, hi⟩ j else if i = j.1 then 1 else 0

lemma coordinateGraphGenerator_mem {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (j : ↑(Iᶜ)) :
    coordinateGraphGenerator I a j ∈ coordinateGraph I a := by
  classical
  rw [mem_coordinateGraph]
  intro i hi
  rw [show coordinateGraphGenerator I a j i = a ⟨i, hi⟩ j by
    simp [coordinateGraphGenerator, hi]]
  rw [Finset.sum_eq_single j]
  · have hjc : j.1 ∉ I := Finset.mem_compl.mp j.2
    simp [coordinateGraphGenerator, hjc]
  · intro k hk hkj
    have hkc : k.1 ∉ I := Finset.mem_compl.mp k.2
    simp [coordinateGraphGenerator, hkc, hkj]
  · simp

/-- Formation of a coordinate graph commutes with arbitrary extension of scalars.
Unlike complement preservation, this records the actual matrix of the resulting
complement and is therefore the localization identity needed by the chart sheaf. -/
lemma span_image_coordinateGraph {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    Submodule.span S ((fun v (i : Fin n) ↦ φ (v i)) ''
      (coordinateGraph I a : Set (Fin n → R))) =
      coordinateGraph I (fun i j ↦ φ (a i j)) := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨w, hw, rfl⟩
    change w ∈ coordinateGraph I a at hw
    change (fun i ↦ φ (w i)) ∈ coordinateGraph I (fun i j ↦ φ (a i j))
    rw [mem_coordinateGraph] at hw ⊢
    intro i hi
    rw [hw i hi, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
  · intro v hv
    rw [mem_coordinateGraph] at hv
    have hsum : v = ∑ j : ↑(Iᶜ), v j.1 •
        (fun i ↦ φ (coordinateGraphGenerator I a j i)) := by
      funext i
      by_cases hi : i ∈ I
      · rw [hv i hi, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        simp [coordinateGraphGenerator, hi, mul_comm]
      · have hic : i ∈ Iᶜ := Finset.mem_compl.mpr hi
        let j : ↑(Iᶜ) := ⟨i, hic⟩
        rw [Finset.sum_apply, Finset.sum_eq_single j]
        · simp [coordinateGraphGenerator, hi, j]
        · intro k hk hkj
          have hik : i ≠ k.1 := fun e ↦ hkj (Subtype.ext e.symm)
          simp [coordinateGraphGenerator, hi, hik]
        · simp
    rw [hsum]
    exact sum_mem fun j hj ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨coordinateGraphGenerator I a j,
        coordinateGraphGenerator_mem I a j, rfl⟩)

/-- Restrict a matrix of global functions to an open subscheme. -/
def restrictCoordinateMatrix (X : Scheme.{u}) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) (U : X.Opens) :
    (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, U) :=
  fun i j ↦ (X.presheaf.map (homOfLE le_top).op).hom (a i j)

lemma restrictCoordinateMatrix_res (X : Scheme.{u}) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) {U V : X.Opens} (hVU : V ≤ U)
    (i : ↑I) (j : ↑(Iᶜ)) :
    (X.presheaf.map (homOfLE hVU).op).hom (restrictCoordinateMatrix X I a U i j) =
      restrictCoordinateMatrix X I a V i j := by
  rw [restrictCoordinateMatrix, restrictCoordinateMatrix,
    ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Pullback of global coordinate functions agrees with the affine `appLE` map after
restriction to affine source and target opens. -/
lemma restrictCoordinateMatrix_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(Y, ⊤))
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (i : ↑I) (j : ↑(Iᶜ)) :
    (f.appLE V.1 U.1 hUV).hom (restrictCoordinateMatrix Y I a V.1 i j) =
      restrictCoordinateMatrix X I (fun i j ↦ f.appTop.hom (a i j)) U.1 i j := by
  rw [restrictCoordinateMatrix, restrictCoordinateMatrix,
    ← CommRingCat.comp_apply, f.map_appLE]
  rfl

/-- The quasi-coherent submodule datum on a scheme obtained as the graph of a matrix of
global functions.  Its localization axiom is the scalar-extension identity for
`coordinateGraph`. -/
def coordinateGraphData (X : Scheme.{u}) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) : X.SubmoduleSheafData n where
  submodule U := coordinateGraph I (restrictCoordinateMatrix X I a U.1)
  span_resPi_basicOpen U f := by
    let φ : Γ(X, U.1) →+* Γ(X, (X.affineBasicOpen f).1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    change Submodule.span _ ((fun v i ↦ φ (v i)) ''
      (coordinateGraph I (restrictCoordinateMatrix X I a U.1) :
        Set (Fin n → Γ(X, U.1)))) =
      coordinateGraph I (restrictCoordinateMatrix X I a (X.affineBasicOpen f).1)
    rw [span_image_coordinateGraph]
    congr 1
    funext i j
    exact restrictCoordinateMatrix_res X I a (X.basicOpen_le f) i j

lemma coordinateGraphData_submodule (X : Scheme.{u}) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) (U : X.affineOpens) :
    (coordinateGraphData X I a).submodule U =
      coordinateGraph I (restrictCoordinateMatrix X I a U.1) :=
  rfl

/-- A graph datum satisfies the Grassmannian chart complement condition. -/
lemma coordinateGraphData_isComplementOfCoords (X : Scheme.{u}) {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    (coordinateGraphData X I a).IsComplementOfCoords I := by
  intro U
  exact isCompl_coordinateGraph I (restrictCoordinateMatrix X I a U.1)

/-- On an affine source open mapping into an affine target open, pullback of a graph
datum is the graph of the pulled-back global matrix. -/
lemma coordinateGraphData_comap_submodule_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(Y, ⊤))
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ((coordinateGraphData Y I a).comap f).submodule U =
      coordinateGraph I
        (restrictCoordinateMatrix X I (fun i j ↦ f.appTop.hom (a i j)) U.1) := by
  rw [SubmoduleSheafData.comap_submodule_eq_span _ f hUV]
  change Submodule.span _ ((fun v i ↦ (f.appLE V.1 U.1 hUV).hom (v i)) ''
      (coordinateGraph I (restrictCoordinateMatrix Y I a V.1) :
        Set (Fin n → Γ(Y, V.1)))) = _
  rw [span_image_coordinateGraph]
  congr 1
  funext i j
  exact restrictCoordinateMatrix_appLE f I a U V hUV i j

/-- Two complements of the same submodule are equal if one is contained in the other. -/
lemma Submodule.eq_of_le_of_isCompl {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {W₁ W₂ C : Submodule R M} (h₁ : IsCompl W₁ C)
    (h₂ : IsCompl W₂ C) (hle : W₁ ≤ W₂) : W₁ = W₂ := by
  apply le_antisymm hle
  intro v hv₂
  have hvSup : v ∈ W₁ ⊔ C := by rw [h₁.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw₁, c, hc, hwc⟩ := Submodule.mem_sup.mp hvSup
  have hw₂ := hle hw₁
  have hc₂ : c ∈ W₂ := by
    have hc_eq : c = v - w := by rw [← hwc]; abel
    rw [hc_eq]
    exact Submodule.sub_mem _ hv₂ hw₂
  have hdis := h₂.disjoint
  rw [Submodule.disjoint_def] at hdis
  have hc0 := hdis c hc₂ hc
  rw [hc0, add_zero] at hwc
  rw [← hwc]
  exact hw₁

/-- The coordinate summand supported on `I` is the finite free module of functions on
`I`. -/
def coordinateSubmoduleEquiv {R : Type*} [CommRing R] {n : ℕ} (I : Finset (Fin n)) :
    (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
      (fun _ ↦ (⊥ : Submodule R R))) ≃ₗ[R] (↑I → R) where
  toFun v i := v.1 i.1
  invFun v := ⟨fun i ↦ if hi : i ∈ I then v ⟨i, hi⟩ else 0, by
    rw [Submodule.mem_pi]
    intro i hi
    have hic : i ∈ Iᶜ := hi
    have hni : i ∉ I := Finset.mem_compl.mp hic
    simp [hni]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · simp [hi]
    · have hic : i ∈ Iᶜ := Finset.mem_compl.mpr hi
      have hv := (Submodule.mem_pi.mp v.2) i hic
      rw [Submodule.mem_bot] at hv
      simp [hi, hv]
  right_inv v := by
    funext i
    simp [i.2]
  map_add' x y := by
    funext i
    rfl
  map_smul' r x := by
    funext i
    rfl

/-- If a submodule of `Rⁿ` is complementary to the coordinate summand supported on
`I`, then its quotient has rank `I.card` at every prime.  This is the rank calculation
behind the fact that the `I`-chart of `Gr(q,n)` can be nonempty only where `I.card = q`.
-/
lemma quotient_rankAtStalk_eq_card_of_isCompl {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule R (Fin n → R))
    (h : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        fun _ ↦ (⊥ : Submodule R R)))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk ((Fin n → R) ⧸ W) p = I.card := by
  let e : ((Fin n → R) ⧸ W) ≃ₗ[R] (↑I → R) :=
    W.quotientEquivOfIsCompl _ h ≪≫ₗ coordinateSubmoduleEquiv I
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  simp

/-- A rank-`q` Grassmannian point satisfying the `I`-chart condition over a nonempty
scheme necessarily has `I.card = q`. -/
lemma SubmoduleSheafData.IsComplementOfCoords.card_eq_of_quotientProjectiveOfRank
    {q : ℕ} {I : Finset (Fin n)} {K : T.SubmoduleSheafData n}
    (hI : K.IsComplementOfCoords I) (hK : K.QuotientProjectiveOfRank q) (x : T) :
    I.card = q := by
  obtain ⟨U, hxU, -, hrank⟩ := hK x
  let p : PrimeSpectrum Γ(T, U.1) := U.2.primeIdealOf ⟨x, hxU⟩
  rw [← hrank p]
  exact (quotient_rankAtStalk_eq_card_of_isCompl I (K.submodule U) (hI U) p).symm

/-- On an empty scheme every coordinate decomposition is complementary, since all
modules of sections are subsingletons. -/
lemma SubmoduleSheafData.isComplementOfCoords_of_isEmpty
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) [IsEmpty T] :
    K.IsComplementOfCoords I := by
  intro U
  let C : Submodule Γ(T, U.1) (Fin n → Γ(T, U.1)) :=
    Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥
  have hKbot : K.submodule U = ⊥ := by
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_bot]
      exact Subsingleton.elim v 0
    · exact bot_le
  have hCtop : C = ⊤ := by
    apply top_unique
    intro v hv
    rw [Submodule.mem_pi]
    intro i hi
    rw [Submodule.mem_bot]
    exact Subsingleton.elim (v i) 0
  rw [hKbot, show Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
    (fun _ ↦ (⊥ : Submodule Γ(T, U.1) Γ(T, U.1))) = ⊤ from hCtop]
  exact isCompl_bot_top

/-- If the coordinate set has the wrong cardinality, a Grassmannian point can satisfy
the chart condition only over an empty scheme. -/
lemma SubmoduleSheafData.isEmpty_of_isComplementOfCoords_of_card_ne
    {q : ℕ} {K : T.SubmoduleSheafData n} {I : Finset (Fin n)}
    (hK : K.QuotientProjectiveOfRank q) (hI : K.IsComplementOfCoords I)
    (hne : I.card ≠ q) : IsEmpty T :=
  ⟨fun x ↦ hne (hI.card_eq_of_quotientProjectiveOfRank hK x)⟩

/-- The coordinate summand maps to the quotient by a submodule. -/
def coordinateToQuotient {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule R (Fin n → R)) :
    (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
      (fun _ ↦ (⊥ : Submodule R R))) →ₗ[R] ((Fin n → R) ⧸ W) :=
  W.mkQ.comp (Submodule.subtype _)

@[simp]
lemma coordinateToQuotient_range {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule R (Fin n → R)) :
    LinearMap.range (coordinateToQuotient I W) =
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule R R))).map W.mkQ := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

/-- Membership in a coordinate-generation open is equivalent to surjectivity of the
localized selected-coordinate map on any affine neighbourhood of the point. -/
lemma isCompl_of_codisjoint_of_quotient_projective_rank
    {R : Type*} [CommRing R] {n q : ℕ} (I : Finset (Fin n))
    (W : Submodule R (Fin n → R)) (hcard : I.card = q)
    (hproj : Module.Projective R ((Fin n → R) ⧸ W))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ W) p = q)
    (hcodisjoint : Codisjoint W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
  let C : Submodule R (Fin n → R) :=
    Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥
  let φ : C →ₗ[R] ((Fin n → R) ⧸ W) := coordinateToQuotient I W
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W z
    rw [codisjoint_iff_le_sup] at hcodisjoint
    obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp
      (hcodisjoint (Submodule.mem_top (x := v)))
    refine ⟨⟨c, hc⟩, ?_⟩
    dsimp [φ, coordinateToQuotient]
    change W.mkQ c = W.mkQ v
    rw [← hwc, map_add, W.mkQ_apply, W.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero W).2 hw, zero_add]
  letI : Module.Projective R ((Fin n → R) ⧸ W) := hproj
  letI : Module.Free R C := Module.Free.of_equiv (coordinateSubmoduleEquiv I).symm
  letI : Module.Finite R C := Module.Finite.of_surjective
    (coordinateSubmoduleEquiv I).symm.toLinearMap
      (coordinateSubmoduleEquiv I).symm.surjective
  have hbij : Function.Bijective φ :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hsurj fun m _ ↦ by
      letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp
        ⟨⟨m, inferInstance⟩⟩
      rw [congrFun (Module.rankAtStalk_eq_of_equiv (coordinateSubmoduleEquiv I))
        ⟨m, inferInstance⟩]
      rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
      simp [hcard]
  refine ⟨?_, hcodisjoint⟩
  rw [Submodule.disjoint_def]
  intro v hvW hvC
  let c : C := ⟨v, hvC⟩
  have hc0 : φ c = φ 0 := by
    dsimp [φ, coordinateToQuotient]
    change W.mkQ v = 0
    exact (Submodule.Quotient.mk_eq_zero W).2 hvW
  have := hbij.1 hc0
  exact congrArg Subtype.val this

/-- On an affine where the Grassmannian quotient is projective of rank `q`, the
`q`-coordinate chart condition is equivalent to surjectivity of the coordinate map.
-/
lemma isCompl_iff_codisjoint_of_quotient_projective_rank
    {R : Type*} [CommRing R] {n q : ℕ} (I : Finset (Fin n))
    (W : Submodule R (Fin n → R)) (hcard : I.card = q)
    (hproj : Module.Projective R ((Fin n → R) ⧸ W))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ W) p = q) :
    IsCompl W
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) ↔
      Codisjoint W
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) :=
  ⟨IsCompl.codisjoint,
    isCompl_of_codisjoint_of_quotient_projective_rank I W hcard hproj hrank⟩

/-- For a finite-projective rank-`q` quotient, the coordinate chart condition is
equivalent to surjectivity of the selected-coordinate map to the quotient. -/
lemma coordinateToQuotient_surjective_iff_isCompl
    {R : Type*} [CommRing R] {n q : ℕ} (I : Finset (Fin n))
    (W : Submodule R (Fin n → R)) (hcard : I.card = q)
    (hproj : Module.Projective R ((Fin n → R) ⧸ W))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ W) p = q) :
    Function.Surjective (coordinateToQuotient I W) ↔
      IsCompl W
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
  rw [← LinearMap.range_eq_top, coordinateToQuotient_range,
    Submodule.map_mkQ_eq_top]
  constructor
  · intro hsup
    apply isCompl_of_codisjoint_of_quotient_projective_rank I W hcard hproj hrank
    rw [codisjoint_iff_le_sup, hsup]
  · intro h
    exact h.sup_eq_top

/-- A chart-valued submodule datum has full coordinate-generation locus. -/
lemma SubmoduleSheafData.isComplementOfCoords_of_forall_codisjoint
    {q : ℕ} {K : T.SubmoduleSheafData n} {I : Finset (Fin n)}
    (hcard : I.card = q) (hK : K.QuotientProjectiveOfRank q)
    (hcod : ∀ U : T.affineOpens, Codisjoint (K.submodule U)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    K.IsComplementOfCoords I := by
  intro U
  classical
  refine ⟨?_, hcod U⟩
  rw [Submodule.disjoint_def]
  intro v hvK hvC
  have hrefine : ∀ x : ↑U.1, ∃ (V : T.affineOpens)
      (f : Γ(T, U.1)) (g : Γ(T, V.1)),
      x.1 ∈ T.basicOpen f ∧ T.basicOpen f = T.basicOpen g ∧
      Module.Projective Γ(T, V.1) ((Fin n → Γ(T, V.1)) ⧸ K.submodule V) ∧
      ∀ p : PrimeSpectrum Γ(T, V.1),
        Module.rankAtStalk ((Fin n → Γ(T, V.1)) ⧸ K.submodule V) p = q := by
    intro x
    obtain ⟨V, hxV, hproj, hrank⟩ := hK x.1
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x.1 ⟨x.2, hxV⟩
    exact ⟨V, f, g, hxf, hfg, hproj, hrank⟩
  choose V f g hxf hfg hproj hrank using hrefine
  have hcover : U.1 ≤ iSup (fun x : ↑U.1 ↦ T.basicOpen (f x)) := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩
  funext ℓ
  refine T.sheaf.eq_of_locally_eq' (fun x : ↑U.1 ↦ T.basicOpen (f x)) U.1
    (fun x ↦ homOfLE (T.basicOpen_le (f x))) hcover (v ℓ) 0 fun x ↦ ?_
  let Wf := T.affineBasicOpen (f x)
  let Wg := T.affineBasicOpen (g x)
  have hW : Wf = Wg := Subtype.ext (hfg x)
  have hresK : T.resPi (T.basicOpen_le (f x)) n v ∈ K.submodule Wf := by
    rw [← K.span_resPi_basicOpen U (f x)]
    exact Submodule.subset_span ⟨v, hvK, rfl⟩
  have hresC : T.resPi (show (T.affineBasicOpen (f x)).1 ≤ U.1 from
      T.basicOpen_le (f x)) n v ∈
      Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(T, Wf.1) Γ(T, Wf.1))) := by
    rw [Submodule.mem_pi]
    intro i hi
    rw [Submodule.mem_bot]
    have h0 := (Submodule.mem_bot _).mp (Submodule.mem_pi.mp hvC i hi)
    exact (congrArg _ h0).trans (map_zero _)
  have hcompV : IsCompl (K.submodule (V x))
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) :=
    isCompl_of_codisjoint_of_quotient_projective_rank I (K.submodule (V x))
      hcard (hproj x) (hrank x) (hcod (V x))
  have hcompWg : IsCompl (K.submodule Wg)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
    rw [← K.span_resPi_basicOpen (V x) (g x)]
    exact isCompl_span_image_pi_of_isCompl
      ((T.presheaf.map (homOfLE (T.basicOpen_le (g x))).op).hom) I hcompV
  have hcompWf : IsCompl (K.submodule Wf)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
    exact hW.symm ▸ hcompWg
  have hd := hcompWf.disjoint
  rw [Submodule.disjoint_def] at hd
  have hv0 := hd _ hresK hresC
  have hℓ := congrFun hv0 ℓ
  rw [resPi_apply] at hℓ
  rw [map_zero]
  exact hℓ

/-- Codisjointness with the coordinate-supported complement transports along the
coordinatewise ring-equivalence image. -/
theorem _root_.Submodule.codisjoint_piBot_mapPiRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) {n : ℕ}
    {W : Submodule R (Fin n → R)} (I : Finset (Fin n))
    (h : Codisjoint W (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
      (fun _ ↦ (⊥ : Submodule R R)))) :
    Codisjoint (W.mapPiRingEquiv e)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule S S))) := by
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  have hv : (fun i ↦ e.symm (v i)) ∈
      W ⊔ Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule R R)) := by
    rw [codisjoint_iff.mp h]
    trivial
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hv
  refine Submodule.mem_sup.mpr ⟨fun i ↦ e (a i), ?_, fun i ↦ e (c i), ?_, ?_⟩
  · rw [Submodule.mem_mapPiRingEquiv]
    simpa using ha
  · intro j hj
    have h0 : c j = 0 := hc j hj
    simp [h0]
  · funext i
    have hi := congrFun hac i
    simp only [Pi.add_apply] at hi ⊢
    calc e (a i) + e (c i) = e (a i + c i) := (map_add e _ _).symm
      _ = e (e.symm (v i)) := by rw [hi]
      _ = v i := e.apply_symm_apply _

/-- Along an open immersion, the chart open of the pulled-back datum maps into the
preimage of the chart open: chart-goodness of the restricted datum is chart-goodness of
the original on the image. -/
theorem SubmoduleSheafData.coordinateChartOpen_comap_le
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (K.comap f).coordinateChartOpen I ≤ f ⁻¹ᵁ K.coordinateChartOpen I := by
  intro x hx
  obtain ⟨U, h, hxh, hcod⟩ :=
    (K.comap f).exists_basicOpen_codisjoint_of_mem_coordinateChartOpen I hx
  set V : Y.affineOpens :=
    ⟨f ''ᵁ (X.affineBasicOpen h).1,
      (X.affineBasicOpen h).2.image_of_isOpenImmersion f⟩ with hV
  set e := (f.appIso (X.affineBasicOpen h).1).commRingCatIsoToRingEquiv with he
  have hsub := K.submodule_comap_of_isOpenImmersion f (X.affineBasicOpen h)
  have hcodY : Codisjoint (K.submodule V)
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(Y, V.1) Γ(Y, V.1)))) := by
    have htrans := Submodule.codisjoint_piBot_mapPiRingEquiv e.symm I
      (W := (K.comap f).submodule (X.affineBasicOpen h)) hcod
    rw [hsub, Submodule.mapPiRingEquiv_symm_mapPiRingEquiv] at htrans
    exact htrans
  show f.base x ∈ K.coordinateChartOpen I
  refine K.le_coordinateChartOpen_of_codisjoint I V hcodY ?_
  exact ⟨x, hxh, rfl⟩

/-- Along an open immersion, the preimage of the chart open maps into the chart open of
the pulled-back datum: a chart-good point of `Y` in the image pulls back to a chart-good
basic open of `X` through the section isomorphism. -/
theorem SubmoduleSheafData.preimage_coordinateChartOpen_le_comap
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) [IsOpenImmersion f] :
    f ⁻¹ᵁ K.coordinateChartOpen I ≤ (K.comap f).coordinateChartOpen I := by
  intro x hx
  obtain ⟨V, g, hfxg, hcod⟩ :=
    K.exists_basicOpen_codisjoint_of_mem_coordinateChartOpen I hx
  have hxT : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at hxT
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp hxT
  set W : Y.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩ with hW
  obtain ⟨c₁, c₂, hcc, hfxc⟩ := exists_basicOpen_le_affine_inter W.2
    (Y.affineBasicOpen g).2 (f.base x) ⟨⟨x, hxU, rfl⟩, hfxg⟩
  have hcod₂ : K.coordinateFittingIdealAt I (Y.affineBasicOpen c₂) = ⊤ := by
    rw [K.coordinateFittingIdealAt_basicOpen I (Y.affineBasicOpen g) c₂,
      (K.coordinateFittingIdealAt_eq_top_iff I (Y.affineBasicOpen g)).mpr hcod,
      Ideal.map_top]
  have habo : Y.affineBasicOpen c₁ = Y.affineBasicOpen c₂ := Subtype.ext hcc
  have hcodW : Codisjoint (K.submodule (Y.affineBasicOpen c₁))
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(Y, (Y.affineBasicOpen c₁).1)
          Γ(Y, (Y.affineBasicOpen c₁).1)))) := by
    rw [← K.coordinateFittingIdealAt_eq_top_iff I (Y.affineBasicOpen c₁), habo]
    exact hcod₂
  set e := (f.appIso U.1).commRingCatIsoToRingEquiv with he
  have hC : f ''ᵁ X.basicOpen (e c₁) = Y.basicOpen c₁ := by
    rw [Scheme.image_basicOpen]
    exact congrArg Y.basicOpen (e.symm_apply_apply c₁)
  have himg : (⟨f ''ᵁ (X.affineBasicOpen (e c₁)).1,
      (X.affineBasicOpen (e c₁)).2.image_of_isOpenImmersion f⟩ : Y.affineOpens) =
      Y.affineBasicOpen c₁ := Subtype.ext hC
  have hsub := K.submodule_comap_of_isOpenImmersion f (X.affineBasicOpen (e c₁))
  have hcodX : Codisjoint ((K.comap f).submodule (X.affineBasicOpen (e c₁)))
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule Γ(X, (X.affineBasicOpen (e c₁)).1)
          Γ(X, (X.affineBasicOpen (e c₁)).1)))) := by
    rw [hsub]
    refine Submodule.codisjoint_piBot_mapPiRingEquiv _ I ?_
    rw [← himg] at hcodW
    exact hcodW
  have hxb : x ∈ X.basicOpen (e c₁) := by
    rw [← f.preimage_image_eq (X.basicOpen (e c₁)), hC]
    exact hfxc
  exact (K.comap f).le_coordinateChartOpen_of_codisjoint I
    (X.affineBasicOpen (e c₁)) hcodX hxb

/-- Along an open immersion, the chart open of the pulled-back datum is exactly the
preimage of the chart open. -/
theorem SubmoduleSheafData.coordinateChartOpen_comap
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (K.comap f).coordinateChartOpen I = f ⁻¹ᵁ K.coordinateChartOpen I :=
  le_antisymm (K.coordinateChartOpen_comap_le I f)
    (K.preimage_coordinateChartOpen_le_comap I f)

/-- Membership of a point of an affine open in a basic open is detected by the point's
prime ideal. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.mem_basicOpen_iff_notMem_primeIdealOf
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) (x : U) :
    ↑x ∈ X.basicOpen r ↔ r ∉ (hU.primeIdealOf x).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  have hx := hU.fromSpec_primeIdealOf x
  constructor
  · intro hmem
    change hU.fromSpec.base (hU.primeIdealOf x) ∈ X.basicOpen r
    rw [hx]
    exact hmem
  · intro hmem
    have hmem' : hU.fromSpec.base (hU.primeIdealOf x) ∈ X.basicOpen r := hmem
    rwa [hx] at hmem'

/-- The coordinate Fitting ideal is compatible with pullback along an **arbitrary**
morphism: over an affine open mapping into an affine open, the pulled-back Fitting ideal
is the image ideal (Stacks 07ZD, base-change form). This is where the presentation-free
Fitting formulation pays off: `comap_submodule_eq_span` exhibits the pulled-back kernel
datum as a coordinatewise-image span, and `fittingIdeal_span_image_map` applies to any
ring map. -/
theorem SubmoduleSheafData.coordinateFittingIdealAt_comap
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) {U' : X.affineOpens} {V : Y.affineOpens} (hle : U'.1 ≤ f ⁻¹ᵁ V.1) :
    (K.comap f).coordinateFittingIdealAt I U' =
      Ideal.map ((f.appLE V.1 U'.1 hle).hom) (K.coordinateFittingIdealAt I V) := by
  have happ : f.appPi V.1 hle n =
      fun w (i : Fin n) ↦ (f.appLE V.1 U'.1 hle).hom (w i) := by
    funext w i
    rw [Hom.appPi_apply]
    rfl
  rw [coordinateFittingIdealAt, coordinateFittingIdealAt,
    K.comap_submodule_eq_span f hle, happ,
    ← Submodule.span_image_piMap_piBot ((f.appLE V.1 U'.1 hle).hom) I,
    ← Submodule.span_image_piMap_sup, Submodule.fittingIdeal_span_image_map]

/-- Along an arbitrary morphism, the preimage of the chart open maps into the chart open
of the pulled-back datum. -/
theorem SubmoduleSheafData.preimage_le_comap_coordinateChartOpen
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) :
    f ⁻¹ᵁ K.coordinateChartOpen I ≤ (K.comap f).coordinateChartOpen I := by
  intro x hx
  obtain ⟨V, g, hfxg, hcod⟩ :=
    K.exists_basicOpen_codisjoint_of_mem_coordinateChartOpen I hx
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (f ⁻¹ᵁ Y.basicOpen g : X.Opens).1 from hfxg)
      (f ⁻¹ᵁ Y.basicOpen g).2
  have hle' : (⟨U', hU'⟩ : X.affineOpens).1 ≤ f ⁻¹ᵁ (Y.affineBasicOpen g).1 := hle
  have hFit : (K.comap f).coordinateFittingIdealAt I ⟨U', hU'⟩ = ⊤ := by
    rw [K.coordinateFittingIdealAt_comap I f (V := Y.affineBasicOpen g) hle',
      (K.coordinateFittingIdealAt_eq_top_iff I (Y.affineBasicOpen g)).mpr hcod,
      Ideal.map_top]
  exact (K.comap f).le_coordinateChartOpen_of_codisjoint I ⟨U', hU'⟩
    (((K.comap f).coordinateFittingIdealAt_eq_top_iff I ⟨U', hU'⟩).mp hFit) hxU'

/-- Along an arbitrary morphism, the chart open of the pulled-back datum maps into the
preimage of the chart open. The point is a Nakayama-flavoured prime argument: the induced
map on section rings pulls the point's prime back to the image point's prime
(`comap_primeIdealOf_appLE`), so a unit image ideal forces the Fitting ideal off the
image point's prime. -/
theorem SubmoduleSheafData.comap_coordinateChartOpen_le_preimage
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) :
    (K.comap f).coordinateChartOpen I ≤ f ⁻¹ᵁ K.coordinateChartOpen I := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((f ⁻¹ᵁ V) ⊓ (K.comap f).coordinateChartOpen I : X.Opens).1 from
        ⟨hfxV, hx⟩)
      ((f ⁻¹ᵁ V) ⊓ (K.comap f).coordinateChartOpen I).2
  have hleV : (⟨U', hU'⟩ : X.affineOpens).1 ≤ f ⁻¹ᵁ (⟨V, hV⟩ : Y.affineOpens).1 :=
    hle.trans fun _ hz ↦ hz.1
  have hlechart : (⟨U', hU'⟩ : X.affineOpens).1 ≤ (K.comap f).coordinateChartOpen I :=
    hle.trans fun _ hz ↦ hz.2
  have hFit : (K.comap f).coordinateFittingIdealAt I ⟨U', hU'⟩ = ⊤ :=
    ((K.comap f).coordinateFittingIdealAt_eq_top_iff I ⟨U', hU'⟩).mpr
      ((K.comap f).codisjoint_of_le_coordinateChartOpen I ⟨U', hU'⟩ hlechart)
  have hmap : Ideal.map ((f.appLE V U' hleV).hom)
      (K.coordinateFittingIdealAt I ⟨V, hV⟩) = ⊤ := by
    rw [← K.coordinateFittingIdealAt_comap I f hleV]
    exact hFit
  have hprime := IsAffineOpen.comap_primeIdealOf_appLE (f := f) V hV U' hU' hleV hxU'
  have hnotle : ¬ (K.coordinateFittingIdealAt I ⟨V, hV⟩ ≤
      (hV.primeIdealOf ⟨f.base x, hleV hxU'⟩).asIdeal) := by
    intro hcont
    have hcomap : (hV.primeIdealOf ⟨f.base x, hleV hxU'⟩).asIdeal =
        Ideal.comap (f.appLE V U' hleV).hom
          (hU'.primeIdealOf ⟨x, hxU'⟩).asIdeal := by
      rw [← hprime]
      rfl
    have htop : (⊤ : Ideal Γ(X, U')) ≤ (hU'.primeIdealOf ⟨x, hxU'⟩).asIdeal := by
      rw [← hmap]
      exact Ideal.map_le_iff_le_comap.mpr (hcomap ▸ hcont)
    exact (hU'.primeIdealOf ⟨x, hxU'⟩).isPrime.ne_top (top_le_iff.mp htop)
  obtain ⟨h, hhF, hhp⟩ := SetLike.not_le_iff_exists.mp hnotle
  change f.base x ∈ K.coordinateChartOpen I
  refine K.basicOpen_le_coordinateChartOpen I ⟨V, hV⟩ hhF ?_
  exact (hV.mem_basicOpen_iff_notMem_primeIdealOf h
    ⟨f.base x, hleV hxU'⟩).mpr hhp

/-- Along an arbitrary morphism, the chart open of the pulled-back datum is exactly the
preimage of the chart open (chart-goodness is stable under arbitrary base change; this is
the open-subfunctor property of the chart in pointwise form). -/
theorem SubmoduleSheafData.comap_coordinateChartOpen
    {X Y : Scheme.{u}} {n : ℕ} (K : Y.SubmoduleSheafData n) (I : Finset (Fin n))
    (f : X ⟶ Y) :
    (K.comap f).coordinateChartOpen I = f ⁻¹ᵁ K.coordinateChartOpen I :=
  le_antisymm (K.comap_coordinateChartOpen_le_preimage I f)
    (K.preimage_le_comap_coordinateChartOpen I f)

/-- Pointwise prime-ideal characterization of the chart open: a point of an affine open
lies in the chart open exactly when the coordinate Fitting ideal is not contained in the
point's prime. This is the Fitting-ideal form of "the chart open is the non-vanishing
locus of Fit₀" (Stacks 07ZD). -/
theorem SubmoduleSheafData.mem_coordinateChartOpen_iff_not_le
    (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (U : T.affineOpens) {x : T}
    (hx : x ∈ U.1) :
    x ∈ K.coordinateChartOpen I ↔
      ¬ (K.coordinateFittingIdealAt I U ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  constructor
  · intro hmem hle
    obtain ⟨V, g, hxg, hcod⟩ :=
      K.exists_basicOpen_codisjoint_of_mem_coordinateChartOpen I hmem
    obtain ⟨c₁, c₂, hcc, hxc⟩ := exists_basicOpen_le_affine_inter U.2
      (T.affineBasicOpen g).2 x ⟨hx, hxg⟩
    have hcod₂ : K.coordinateFittingIdealAt I (T.affineBasicOpen c₂) = ⊤ := by
      rw [K.coordinateFittingIdealAt_basicOpen I (T.affineBasicOpen g) c₂,
        (K.coordinateFittingIdealAt_eq_top_iff I (T.affineBasicOpen g)).mpr hcod,
        Ideal.map_top]
    have habo : T.affineBasicOpen c₁ = T.affineBasicOpen c₂ := Subtype.ext hcc
    have hcod₁ : K.coordinateFittingIdealAt I (T.affineBasicOpen c₁) = ⊤ := by
      rw [habo]
      exact hcod₂
    letI : Algebra Γ(T, U.1) Γ(T, (T.affineBasicOpen c₁).1) :=
      (T.presheaf.map (homOfLE (show (T.affineBasicOpen c₁).1 ≤ U.1 from
        T.basicOpen_le c₁)).op).hom.toAlgebra
    haveI : IsLocalization.Away c₁ Γ(T, (T.affineBasicOpen c₁).1) :=
      U.2.isLocalization_basicOpen c₁
    have hmap : Ideal.map (algebraMap Γ(T, U.1) Γ(T, (T.affineBasicOpen c₁).1))
        (K.coordinateFittingIdealAt I U) = ⊤ := by
      rw [show algebraMap Γ(T, U.1) Γ(T, (T.affineBasicOpen c₁).1) =
          (T.presheaf.map (homOfLE (show (T.affineBasicOpen c₁).1 ≤ U.1 from
            T.basicOpen_le c₁)).op).hom from rfl,
        ← K.coordinateFittingIdealAt_basicOpen I U c₁]
      exact hcod₁
    have hnd : ¬ Disjoint ((Submonoid.powers c₁ : Submonoid Γ(T, U.1)) : Set Γ(T, U.1))
        ((K.coordinateFittingIdealAt I U) : Set Γ(T, U.1)) := by
      intro hd
      exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint
        (M := Submonoid.powers c₁) (S := Γ(T, (T.affineBasicOpen c₁).1))
        (K.coordinateFittingIdealAt I U)).mpr hd hmap
    obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.mp hnd
    obtain ⟨m, rfl⟩ := hy1
    have hc₁p : c₁ ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
      (U.2.primeIdealOf ⟨x, hx⟩).isPrime.mem_of_pow_mem m (hle hy2)
    exact ((U.2.mem_basicOpen_iff_notMem_primeIdealOf c₁ ⟨x, hx⟩).mp hxc) hc₁p
  · intro hnle
    obtain ⟨h, hhF, hhp⟩ := SetLike.not_le_iff_exists.mp hnle
    exact K.basicOpen_le_coordinateChartOpen I U hhF
      ((U.2.mem_basicOpen_iff_notMem_primeIdealOf h ⟨x, hx⟩).mpr hhp)

/-- API lemma for Lemma 2.2.4 (the covering step, chart-open
form; Stacks 07ZD together with Nakayama). For a datum with rank-`q` projective
quotient, the coordinate chart opens over all `q`-element coordinate sets cover the base:
localizing at a point, the projective quotient becomes free of rank `q`, a basis can be
selected from among the standard generators, and the corresponding coordinate Fitting
ideal is then not contained in the point's prime, so some basic open through the point is
chart-good. -/
theorem SubmoduleSheafData.iSup_coordinateChartOpen_eq_top
    (q : ℕ) (K : T.SubmoduleSheafData n) (hK : K.QuotientProjectiveOfRank q) :
    ⨆ I : {I : Finset (Fin n) // I.card = q}, K.coordinateChartOpen I.1 = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  obtain ⟨U, hxU, hproj, hrank⟩ := hK x
  set p : PrimeSpectrum Γ(T, U.1) := U.2.primeIdealOf ⟨x, hxU⟩ with hp
  letI : Module.Projective Γ(T, U.1) ((Fin n → Γ(T, U.1)) ⧸ K.submodule U) := hproj
  haveI : Module.Finite Γ(T, U.1) ((Fin n → Γ(T, U.1)) ⧸ K.submodule U) :=
    Module.Finite.of_surjective (K.submodule U).mkQ (K.submodule U).mkQ_surjective
  obtain ⟨hfinN, hprojN, hrankN⟩ :=
    LinearMap.quotKer_baseChangePi_finite_projective_rank
      (S := Localization.AtPrime p.asIdeal) (K.submodule U).mkQ
      (K.submodule U).mkQ_surjective hrank
  set Wp : Submodule (Localization.AtPrime p.asIdeal)
      (Fin n → Localization.AtPrime p.asIdeal) :=
    LinearMap.ker (LinearMap.baseChangePi (Localization.AtPrime p.asIdeal)
      (K.submodule U).mkQ) with hWp
  haveI := hfinN
  haveI := hprojN
  haveI : Module.FinitePresentation (Localization.AtPrime p.asIdeal)
      ((Fin n → Localization.AtPrime p.asIdeal) ⧸ Wp) :=
    Module.finitePresentation_of_projective _ _
  have hvspan : Submodule.span (Localization.AtPrime p.asIdeal)
      (Set.range (fun i ↦ Wp.mkQ (Pi.single i 1))) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨w, rfl⟩ := Wp.mkQ_surjective z
    have hw : w = ∑ i, w i •
        (Pi.single i 1 : Fin n → Localization.AtPrime p.asIdeal) := by
      funext j
      simp [Pi.single_apply]
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨I, hIspan, hIcard⟩ :=
    IsLocalRing.exists_finset_span_image_eq_top_of_span_eq_top
      (fun i ↦ Wp.mkQ (Pi.single i 1)) hvspan
  have hcard : I.card = q := by
    haveI : Module.Free (Localization.AtPrime p.asIdeal)
        ((Fin n → Localization.AtPrime p.asIdeal) ⧸ Wp) :=
      Module.free_of_flat_of_isLocalRing
    have h4 := hrankN (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal))
    rw [Module.rankAtStalk_eq_finrank_of_free] at h4
    rw [hIcard]
    simpa using h4
  have hmap : Submodule.map Wp.mkQ
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)))) = ⊤ := by
    rw [Submodule.piBot_eq_span_single, Submodule.map_span]
    have h6 : Wp.mkQ ''
        ((fun i ↦ (Pi.single i 1 : Fin n → Localization.AtPrime p.asIdeal)) '' ↑I) =
        (fun i ↦ Wp.mkQ (Pi.single i 1)) '' ↑I := by
      rw [Set.image_image]
    rw [h6]
    exact hIspan
  have hsup : Wp ⊔ Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
      (fun _ ↦ (⊥ : Submodule (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal))) = ⊤ :=
    (Submodule.map_mkQ_eq_top Wp _).mp hmap
  have hWspan : Wp = Submodule.span (Localization.AtPrime p.asIdeal)
      ((fun w : Fin n → Γ(T, U.1) ↦ fun i ↦
          algebraMap Γ(T, U.1) (Localization.AtPrime p.asIdeal) (w i)) ''
        ((K.submodule U : Submodule Γ(T, U.1) (Fin n → Γ(T, U.1))) :
          Set (Fin n → Γ(T, U.1)))) := by
    rw [hWp]
    have h5 := LinearMap.ker_baseChangePi_eq_span (Localization.AtPrime p.asIdeal)
      (f := (K.submodule U).mkQ) (K.submodule U).mkQ_surjective
    rwa [Submodule.ker_mkQ] at h5
  have hFit : Ideal.map (algebraMap Γ(T, U.1) (Localization.AtPrime p.asIdeal))
      (K.coordinateFittingIdealAt I U) = ⊤ := by
    rw [coordinateFittingIdealAt,
      ← Submodule.fittingIdeal_span_image_map
        (algebraMap Γ(T, U.1) (Localization.AtPrime p.asIdeal)),
      Submodule.span_image_piMap_sup, Submodule.span_image_piMap_piBot,
      ← hWspan, Submodule.fittingIdeal_zero_eq_top_iff]
    exact hsup
  have hnd : ¬ Disjoint ((p.asIdeal.primeCompl : Submonoid Γ(T, U.1)) : Set Γ(T, U.1))
      ((K.coordinateFittingIdealAt I U) : Set Γ(T, U.1)) := by
    intro hd
    exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (K.coordinateFittingIdealAt I U)).mpr hd hFit
  obtain ⟨h, hh1, hh2⟩ := Set.not_disjoint_iff.mp hnd
  rw [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⟨I, hcard⟩, ?_⟩
  refine K.basicOpen_le_coordinateChartOpen I U hh2 ?_
  rw [hp] at hh1
  exact (U.2.mem_basicOpen_iff_notMem_primeIdealOf h ⟨x, hxU⟩).mpr hh1

/-- If the coordinates are a complement everywhere, the chart open is everything
(no rank hypothesis needed for this direction). -/
theorem SubmoduleSheafData.coordinateChartOpen_eq_top_of_isComplementOfCoords
    {K : T.SubmoduleSheafData n} {I : Finset (Fin n)}
    (h : K.IsComplementOfCoords I) :
    K.coordinateChartOpen I = ⊤ := by
  rw [eq_top_iff, ← iSup_affineOpens_eq_top T]
  exact iSup_le fun U ↦ K.le_coordinateChartOpen_of_codisjoint I U (h U).codisjoint

/-- **The chart-openness bridge**: for rank-`q` data and a `q`-element coordinate set,
the coordinates are a complement everywhere exactly when the chart open is everything.

Stacks 07ZD together with the projective-rank complement criterion; §2.2 Equation 2.2.1. -/
theorem SubmoduleSheafData.isComplementOfCoords_iff_coordinateChartOpen_eq_top_of_rank
    {q : ℕ} (K : T.SubmoduleSheafData n) (I : Finset (Fin n)) (hcard : I.card = q)
    (hK : K.QuotientProjectiveOfRank q) :
    K.IsComplementOfCoords I ↔ K.coordinateChartOpen I = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff, ← iSup_affineOpens_eq_top T]
    exact iSup_le fun U ↦ K.le_coordinateChartOpen_of_codisjoint I U (h U).codisjoint
  · intro h
    refine SubmoduleSheafData.isComplementOfCoords_of_forall_codisjoint hcard hK fun U ↦ ?_
    exact K.codisjoint_of_le_coordinateChartOpen I U (by rw [h]; exact le_top)

/-- The pullback of a rank-`q` datum along an arbitrary morphism is everywhere a
complement of a `q`-element coordinate set exactly when the morphism lands in the chart
open. This is the statement the open-subfunctor theorem consumes. -/
theorem SubmoduleSheafData.isComplementOfCoords_comap_iff_preimage_coordinateChartOpen_eq_top
    {X Y : Scheme.{u}} {n q : ℕ} {K : Y.SubmoduleSheafData n} {I : Finset (Fin n)}
    (hI : I.card = q) (hK : K.QuotientProjectiveOfRank q) (f : X ⟶ Y) :
    (K.comap f).IsComplementOfCoords I ↔ f ⁻¹ᵁ K.coordinateChartOpen I = ⊤ := by
  rw [(K.comap f).isComplementOfCoords_iff_coordinateChartOpen_eq_top_of_rank I hI
    (hK.comap f), K.comap_coordinateChartOpen I f]


/-- For a rank-`q` Grassmannian datum and a `q`-element coordinate set, the chart
condition is exactly that the coordinate-generation open is the whole base scheme. -/
noncomputable def coordinateGraphQuotientEquiv {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    ((Fin n → R) ⧸ coordinateGraph I a) ≃ₗ[R] (↑I → R) :=
  (coordinateGraph I a).quotientEquivOfIsCompl _ (isCompl_coordinateGraph I a) ≪≫ₗ
    coordinateSubmoduleEquiv I

/-- A coordinate graph has a finite projective quotient of rank `I.card`. -/
lemma coordinateGraph_quotient_projective_rank {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    Module.Projective R ((Fin n → R) ⧸ coordinateGraph I a) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk ((Fin n → R) ⧸ coordinateGraph I a) p = I.card := by
  let e := coordinateGraphQuotientEquiv I a
  haveI : Module.Free R ((Fin n → R) ⧸ coordinateGraph I a) :=
    Module.Free.of_equiv e.symm
  constructor
  · infer_instance
  · intro p
    letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩
    rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p]
    rw [Module.rankAtStalk_eq_finrank_of_free]
    simp

/-- A graph datum defines a point of the Grassmannian of rank `I.card` quotients. -/
lemma coordinateGraphData_quotientProjectiveOfRank (X : Scheme.{u}) {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    (coordinateGraphData X I a).QuotientProjectiveOfRank I.card := by
  intro x
  obtain ⟨U, hUaff, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens (U := ⊤) (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hUaff⟩, hxU, ?_, ?_⟩
  · exact (coordinateGraph_quotient_projective_rank I
      (restrictCoordinateMatrix X I a U)).1
  · exact (coordinateGraph_quotient_projective_rank I
      (restrictCoordinateMatrix X I a U)).2

/-- A coordinate graph remembers its matrix uniquely. -/
lemma coordinateGraph_injective {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) : Function.Injective
      (coordinateGraph I : ((i : ↑I) → (j : ↑(Iᶜ)) → R) →
        Submodule R (Fin n → R)) := by
  classical
  intro a b hab
  funext i j
  have hj := coordinateGraphGenerator_mem I a j
  rw [hab, mem_coordinateGraph] at hj
  have h := hj i.1 i.2
  rw [show coordinateGraphGenerator I a j i.1 = a i j by
    simp [coordinateGraphGenerator, i.2]] at h
  rw [Finset.sum_eq_single j] at h
  · have hjc : j.1 ∉ I := Finset.mem_compl.mp j.2
    simpa [coordinateGraphGenerator, hjc] using h
  · intro k hk hkj
    have hkj' : k.1 ≠ j.1 := fun e ↦ hkj (Subtype.ext e)
    have hkc : k.1 ∉ I := Finset.mem_compl.mp k.2
    simp [coordinateGraphGenerator, hkc, hkj']
  · simp

/-- The matrix associated to a complement of the coordinate summand, obtained by
projecting the standard complementary-coordinate vectors onto the complement. -/
noncomputable def coordinateGraphMatrix {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule R (Fin n → R))
    (h : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        fun _ ↦ (⊥ : Submodule R R))) :
    (i : ↑I) → (j : ↑(Iᶜ)) → R :=
  fun i j ↦ W.projection _ h (Pi.single j.1 1) i.1

lemma coordinateGraphMatrix_congr {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) {W W' : Submodule R (Fin n → R)} (h : W = W')
    (hW : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥))
    (hW' : IsCompl W'
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    coordinateGraphMatrix I W hW = coordinateGraphMatrix I W' hW' := by
  subst W'
  rfl

/-- Every complement of the chosen coordinate summand is the graph of its associated
matrix.  Together with `coordinateGraph_injective`, this classifies the affine chart
at the module level. -/
lemma coordinateGraph_coordinateGraphMatrix {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule R (Fin n → R))
    (h : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        fun _ ↦ (⊥ : Submodule R R))) :
    coordinateGraph I (coordinateGraphMatrix I W h) = W := by
  classical
  let C : Submodule R (Fin n → R) :=
    Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
      fun _ ↦ (⊥ : Submodule R R)
  let e : (Fin n → R) →ₗ[R] (Fin n → R) := W.projection C h
  have he_single_I : ∀ k : ↑I, e (Pi.single k.1 1) = 0 := by
    intro k
    apply Submodule.projection_apply_of_mem_right h
    rw [Submodule.mem_pi]
    intro j hj
    rw [Submodule.mem_bot]
    have hjc : j ∈ Iᶜ := hj
    have hji : j ≠ k.1 := by
      intro hjk
      have : k.1 ∈ Iᶜ := hjk ▸ hjc
      exact (Finset.mem_compl.mp this) k.2
    simp [hji]
  have hWle : W ≤ coordinateGraph I (coordinateGraphMatrix I W h) := by
    intro w hw
    rw [mem_coordinateGraph]
    intro i hi
    have hew : e w = w := Submodule.projection_apply_of_mem_left h hw
    have hexp := congrFun (LinearMap.pi_apply_eq_sum_univ e w) i
    rw [hew] at hexp
    rw [hexp]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_add_sum_compl I]
    have hzero : ∑ k ∈ I, w k * e (fun j ↦ if k = j then 1 else 0) i = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [show e (fun j ↦ if k = j then 1 else 0) = 0 by
        rw [show (fun j ↦ if k = j then (1 : R) else 0) = Pi.single k 1 by
          funext j
          simp [Pi.single_apply, eq_comm]]
        exact he_single_I ⟨k, hk⟩]
      simp
    rw [hzero, zero_add, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro j hj
    change w j.1 * e (fun k ↦ if j.1 = k then 1 else 0) i =
      W.projection C h (Pi.single j.1 1) i * w j.1
    rw [show (fun k ↦ if j.1 = k then (1 : R) else 0) = Pi.single j.1 1 by
      funext k
      simp [Pi.single_apply, eq_comm]]
    exact mul_comm _ _
  apply le_antisymm
  · intro v hv
    have hvSup : v ∈ W ⊔ C := by
      rw [h.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp hvSup
    have hwGraph := hWle hw
    have hcGraph : c ∈ coordinateGraph I (coordinateGraphMatrix I W h) := by
      have hc_eq : c = v - w := by rw [← hwc]; abel
      rw [hc_eq]
      exact Submodule.sub_mem _ hv hwGraph
    have hdis := (isCompl_coordinateGraph I (coordinateGraphMatrix I W h)).disjoint
    rw [Submodule.disjoint_def] at hdis
    have hc0 := hdis c hcGraph hc
    rw [hc0, add_zero] at hwc
    rw [← hwc]
    exact hw
  · exact hWle

@[simp]
lemma coordinateGraphMatrix_coordinateGraph {R : Type*} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    coordinateGraphMatrix I (coordinateGraph I a) (isCompl_coordinateGraph I a) = a := by
  apply coordinateGraph_injective I
  exact coordinateGraph_coordinateGraphMatrix I (coordinateGraph I a)
    (isCompl_coordinateGraph I a)

/-- On an affine scheme, the sheaf datum generated by a globally complementary
submodule is the coordinate-graph datum of its canonical matrix. -/
lemma ofAffineSubmodule_eq_coordinateGraphData {X : Scheme.{u}} [IsAffine X] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤)))
    (hW : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    SubmoduleSheafData.ofAffineSubmodule W =
      coordinateGraphData X I (coordinateGraphMatrix I W hW) := by
  apply SubmoduleSheafData.ext
  funext U
  let φ : Γ(X, ⊤) →+* Γ(X, U.1) :=
    (X.presheaf.map (homOfLE le_top).op).hom
  change Submodule.span Γ(X, U.1)
      ((fun v i ↦ φ (v i)) '' (W : Set (Fin n → Γ(X, ⊤)))) =
    coordinateGraph I
      (fun i j ↦ φ (coordinateGraphMatrix I W hW i j))
  let a := coordinateGraphMatrix I W hW
  have hgraph : coordinateGraph I a = W :=
    coordinateGraph_coordinateGraphMatrix I W hW
  conv_lhs => rw [← hgraph]
  exact span_image_coordinateGraph φ I a

/-- A globally complementary submodule on an affine scheme generates a sheaf datum
lying in the same standard Grassmannian chart. -/
lemma ofAffineSubmodule_isComplementOfCoords {X : Scheme.{u}} [IsAffine X] {n : ℕ}
    (I : Finset (Fin n)) (W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤)))
    (hW : IsCompl W
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥)) :
    (SubmoduleSheafData.ofAffineSubmodule W).IsComplementOfCoords I := by
  rw [ofAffineSubmodule_eq_coordinateGraphData I W hW]
  exact coordinateGraphData_isComplementOfCoords X I _

/-- The coordinate matrix of a chart-valued submodule datum on an affine open. -/
noncomputable def SubmoduleSheafData.coordinateMatrix {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (U : X.affineOpens) :
    (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, U.1) :=
  coordinateGraphMatrix I (K.submodule U) (hK U)

/-- Coordinate matrices restrict correctly from an affine open to a basic open. -/
lemma SubmoduleSheafData.coordinateMatrix_basicOpen {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (U : X.affineOpens) (f : Γ(X, U.1)) :
    let φ : Γ(X, U.1) →+* Γ(X, (X.affineBasicOpen f).1) :=
      (X.presheaf.map (homOfLE (show (X.affineBasicOpen f).1 ≤ U.1 from
        X.affineBasicOpen_le f)).op).hom
    K.coordinateMatrix I hK (X.affineBasicOpen f) =
      fun i j ↦ φ (K.coordinateMatrix I hK U i j) := by
  dsimp only
  apply coordinateGraph_injective I
  change coordinateGraph I
      (coordinateGraphMatrix I (K.submodule (X.affineBasicOpen f))
        (hK (X.affineBasicOpen f))) =
    coordinateGraph I (fun i j ↦
      (X.presheaf.map (homOfLE (X.affineBasicOpen_le f)).op).hom
        (coordinateGraphMatrix I (K.submodule U) (hK U) i j))
  rw [coordinateGraph_coordinateGraphMatrix]
  rw [← K.span_resPi_basicOpen U f]
  let φ : Γ(X, U.1) →+* Γ(X, (X.affineBasicOpen f).1) :=
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le f)).op).hom
  let a := coordinateGraphMatrix I (K.submodule U) (hK U)
  have hgraph : coordinateGraph I a = K.submodule U :=
    coordinateGraph_coordinateGraphMatrix I (K.submodule U) (hK U)
  change Submodule.span _ ((fun v i ↦ φ (v i)) ''
      (K.submodule U : Set (Fin n → Γ(X, U.1)))) =
    coordinateGraph I (fun i j ↦ φ (a i j))
  calc
    _ = Submodule.span _ ((fun v i ↦ φ (v i)) ''
        (coordinateGraph I a : Set (Fin n → Γ(X, U.1)))) := by rw [hgraph]
    _ = _ := span_image_coordinateGraph φ I a

lemma SubmoduleSheafData.coordinateMatrix_basicOpen_apply {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (U : X.affineOpens) (f : Γ(X, U.1))
    (i : ↑I) (j : ↑(Iᶜ)) :
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le f)).op).hom
        (K.coordinateMatrix I hK U i j) =
      K.coordinateMatrix I hK (X.affineBasicOpen f) i j := by
  exact congrFun (congrFun (K.coordinateMatrix_basicOpen I hK U f).symm i) j

/-- Coordinate matrices are compatible with equality transport of affine opens. -/
lemma SubmoduleSheafData.coordinateMatrix_eqToHom {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) {U V : X.affineOpens} (e : U = V)
    (i : ↑I) (j : ↑(Iᶜ)) :
    (X.presheaf.map (eqToHom (congrArg Subtype.val e)).op).hom
        (K.coordinateMatrix I hK V i j) = K.coordinateMatrix I hK U i j := by
  subst e
  simp

/-- The affine-local coordinate matrices of a chart-valued submodule datum agree on
pairwise intersections. -/
lemma SubmoduleSheafData.coordinateMatrix_isCompatible {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (i : ↑I) (j : ↑(Iᶜ)) :
    TopCat.Presheaf.IsCompatible X.sheaf.1 (fun U : X.affineOpens ↦ U.1)
      (fun U ↦ K.coordinateMatrix I hK U i j) := by
  classical
  intro U V
  have hrefine : ∀ z : ↥(U.1 ⊓ V.1), ∃ (f : Γ(X, U.1)) (g : Γ(X, V.1)),
      X.basicOpen f = X.basicOpen g ∧ z.1 ∈ X.basicOpen f := by
    intro z
    exact exists_basicOpen_le_affine_inter U.2 V.2 z.1 z.2
  choose f g hfg hz using hrefine
  have hcover : U.1 ⊓ V.1 ≤ iSup (fun z : ↥(U.1 ⊓ V.1) ↦ X.basicOpen (f z)) := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hz ⟨x, hx⟩⟩
  have hle : ∀ z : ↥(U.1 ⊓ V.1), X.basicOpen (f z) ≤ U.1 ⊓ V.1 := by
    intro z
    exact le_inf (X.basicOpen_le (f z))
      ((le_of_eq (hfg z)).trans (X.basicOpen_le (g z)))
  refine X.sheaf.eq_of_locally_eq'
    (fun z : ↥(U.1 ⊓ V.1) ↦ X.basicOpen (f z)) (U.1 ⊓ V.1)
    (fun z ↦ homOfLE (hle z)) hcover _ _ fun z ↦ ?_
  have hAff : X.affineBasicOpen (f z) = X.affineBasicOpen (g z) :=
    Subtype.ext (hfg z)
  have hleft :
      (X.presheaf.map (homOfLE (hle z)).op).hom
          ((X.presheaf.map (homOfLE inf_le_left).op).hom
            (K.coordinateMatrix I hK U i j)) =
        K.coordinateMatrix I hK (X.affineBasicOpen (f z)) i j := by
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    exact K.coordinateMatrix_basicOpen_apply I hK U (f z) i j
  have hright :
      (X.presheaf.map (homOfLE (hle z)).op).hom
          ((X.presheaf.map (homOfLE inf_le_right).op).hom
            (K.coordinateMatrix I hK V i j)) =
        K.coordinateMatrix I hK (X.affineBasicOpen (f z)) i j := by
    calc
      _ = (X.presheaf.map (eqToHom (congrArg Subtype.val hAff)).op).hom
          ((X.presheaf.map (homOfLE (X.affineBasicOpen_le (g z))).op).hom
            (K.coordinateMatrix I hK V i j)) := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp,
          ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
        rfl
      _ = (X.presheaf.map (eqToHom (congrArg Subtype.val hAff)).op).hom
          (K.coordinateMatrix I hK (X.affineBasicOpen (g z)) i j) := by
        exact congrArg (fun x : Γ(X, (X.affineBasicOpen (g z)).1) ↦
          (X.presheaf.map (eqToHom (congrArg Subtype.val hAff)).op).hom x)
            (K.coordinateMatrix_basicOpen_apply I hK V (g z) i j)
      _ = _ := K.coordinateMatrix_eqToHom I hK hAff i j
  change
    (X.presheaf.map (homOfLE (hle z)).op).hom
        ((X.presheaf.map (homOfLE inf_le_left).op).hom
          (K.coordinateMatrix I hK U i j)) =
      (X.presheaf.map (homOfLE (hle z)).op).hom
        ((X.presheaf.map (homOfLE inf_le_right).op).hom
          (K.coordinateMatrix I hK V i j))
  rw [hleft, hright]

/-- Affine opens cover a scheme, in the form needed by the unique-gluing API. -/
lemma affineOpens_iSup_eq_top (X : Scheme.{u}) :
    (⊤ : X.Opens) ≤ iSup (fun U : X.affineOpens ↦ U.1) := by
  intro x hx
  obtain ⟨U, hUaff, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens (U := ⊤) hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUaff⟩, hxU⟩

/-- The affine-local coordinate coefficient of a chart-valued datum glues uniquely to
a global function. -/
lemma SubmoduleSheafData.existsUnique_globalCoordinate {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (i : ↑I) (j : ↑(Iᶜ)) :
    ∃! s : Γ(X, ⊤), ∀ U : X.affineOpens,
      (X.presheaf.map (homOfLE le_top).op).hom s =
        K.coordinateMatrix I hK U i j := by
  exact X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.1) ⊤
    (fun U ↦ homOfLE le_top) (affineOpens_iSup_eq_top X)
    (fun U ↦ K.coordinateMatrix I hK U i j)
    (K.coordinateMatrix_isCompatible I hK i j)

/-- The global coordinate matrix extracted from a chart-valued submodule datum. -/
noncomputable def SubmoduleSheafData.globalCoordinateMatrix {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) :
    (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤) :=
  fun i j ↦ (K.existsUnique_globalCoordinate I hK i j).choose

lemma SubmoduleSheafData.globalCoordinateMatrix_congr
    {X : Scheme.{u}} {n : ℕ} {K L : X.SubmoduleSheafData n} (h : K = L)
    (I : Finset (Fin n)) (hK : K.IsComplementOfCoords I)
    (hL : L.IsComplementOfCoords I) :
    K.globalCoordinateMatrix I hK = L.globalCoordinateMatrix I hL := by
  subst L
  rfl

lemma SubmoduleSheafData.restrict_globalCoordinateMatrix {X : Scheme.{u}} {n : ℕ}
    (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) (U : X.affineOpens) (i : ↑I) (j : ↑(Iᶜ)) :
    (X.presheaf.map (homOfLE le_top).op).hom
        (K.globalCoordinateMatrix I hK i j) = K.coordinateMatrix I hK U i j :=
  (K.existsUnique_globalCoordinate I hK i j).choose_spec.1 U

/-- Reconstructing a chart-valued datum from its global coordinate matrix returns the
original datum. -/
lemma SubmoduleSheafData.coordinateGraphData_globalCoordinateMatrix
    {X : Scheme.{u}} {n : ℕ} (K : X.SubmoduleSheafData n) (I : Finset (Fin n))
    (hK : K.IsComplementOfCoords I) :
    coordinateGraphData X I (K.globalCoordinateMatrix I hK) = K := by
  apply SubmoduleSheafData.ext
  funext U
  change coordinateGraph I
      (restrictCoordinateMatrix X I (K.globalCoordinateMatrix I hK) U.1) = K.submodule U
  rw [← coordinateGraph_coordinateGraphMatrix I (K.submodule U) (hK U)]
  congr 1
  funext i j
  exact K.restrict_globalCoordinateMatrix I hK U i j

/-- Extracting the global matrix from a graph datum returns the original matrix. -/
lemma SubmoduleSheafData.globalCoordinateMatrix_coordinateGraphData
    (X : Scheme.{u}) {n : ℕ} (I : Finset (Fin n))
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    (coordinateGraphData X I a).globalCoordinateMatrix I
      (coordinateGraphData_isComplementOfCoords X I a) = a := by
  funext i j
  symm
  apply (coordinateGraphData X I a).existsUnique_globalCoordinate I
    (coordinateGraphData_isComplementOfCoords X I a) i j |>.choose_spec.2
  intro U
  change restrictCoordinateMatrix X I a U.1 i j =
    coordinateGraphMatrix I
      (coordinateGraph I (restrictCoordinateMatrix X I a U.1))
      (isCompl_coordinateGraph I (restrictCoordinateMatrix X I a U.1)) i j
  rw [coordinateGraphMatrix_coordinateGraph]

/-- On an affine scheme, the global chart matrix is the canonical graph matrix of
the submodule on global sections. -/
lemma SubmoduleSheafData.globalCoordinateMatrix_eq_coordinateGraphMatrix_top
    {X : Scheme.{u}} [IsAffine X] {n : ℕ} (K : X.SubmoduleSheafData n)
    (I : Finset (Fin n)) (hK : K.IsComplementOfCoords I) :
    K.globalCoordinateMatrix I hK =
      coordinateGraphMatrix I
        (K.submodule ⟨⊤, isAffineOpen_top X⟩) (hK ⟨⊤, isAffineOpen_top X⟩) := by
  apply coordinateGraph_injective I
  rw [coordinateGraph_coordinateGraphMatrix]
  have h := congrArg (fun L : X.SubmoduleSheafData n ↦
    L.submodule ⟨⊤, isAffineOpen_top X⟩)
      (K.coordinateGraphData_globalCoordinateMatrix I hK)
  have hres : restrictCoordinateMatrix X I (K.globalCoordinateMatrix I hK) ⊤ =
      K.globalCoordinateMatrix I hK := by
    funext i j
    change (X.presheaf.map (homOfLE le_top).op).hom
      (K.globalCoordinateMatrix I hK i j) = K.globalCoordinateMatrix I hK i j
    have he : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [he]
    have heop : (𝟙 (⊤ : X.Opens)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) :=
      Subsingleton.elim _ _
    rw [heop]
    exact DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (X.presheaf.map_id _)) _
  simpa [coordinateGraphData_submodule, hres] using h

/-- The chart condition is stable under pullback of quasi-coherent submodule sheaves. -/
lemma SubmoduleSheafData.IsComplementOfCoords.comap {X Y : Scheme.{u}} {I : Finset (Fin n)}
    {K : Y.SubmoduleSheafData n} (hK : K.IsComplementOfCoords I) (f : X ⟶ Y) :
    (K.comap f).IsComplementOfCoords I := by
  intro U'
  classical
  have hcov : ∀ x : ↥U'.1, ∃ (g : Γ(X, U'.1)) (V : Y.affineOpens),
      x.1 ∈ X.basicOpen g ∧ X.basicOpen g ≤ f ⁻¹ᵁ V.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨V, hVmem, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens (U := ⊤) (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨g, hgle, hxg⟩ := U'.2.exists_basicOpen_le
      (V := U'.1 ⊓ f ⁻¹ᵁ V) ⟨x, ⟨hx, hyV⟩⟩ hx
    rw [le_inf_iff] at hgle
    exact ⟨g, ⟨V, hVmem⟩, hxg, hgle.2⟩
  choose gg VV hxg hgV using hcov
  have hcover : U'.1 ≤ iSup (fun x : ↥U'.1 ↦ X.basicOpen (gg x)) := fun x hx ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxg _⟩
  have hloc : ∀ (W₀ : X.affineOpens) (V : Y.affineOpens) (hle : W₀.1 ≤ f ⁻¹ᵁ V.1),
      IsCompl ((K.comap f).submodule W₀)
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) := by
    intro W₀ V hle
    rw [K.comap_submodule_eq_span f (U' := W₀) (V := V) hle]
    exact isCompl_span_image_pi_of_isCompl ((f.appLE V.1 W₀.1 hle).hom) I (hK V)
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [Submodule.mem_pi] at h2
    funext ℓ
    refine X.sheaf.eq_of_locally_eq' (fun x : ↥U'.1 ↦ X.basicOpen (gg x)) U'.1
      (fun x ↦ homOfLE (X.basicOpen_le (gg x))) hcover (v ℓ) 0 fun x ↦ ?_
    have hres1 := K.resPi_mem_comapSubmodule_of_le f (U₀ := U')
      (W := X.affineBasicOpen (gg x)) (X.basicOpen_le (gg x)) h1
    have hres2 : X.resPi (X.basicOpen_le (gg x)) n v ∈
        Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          (fun _ ↦ (⊥ : Submodule Γ(X, X.basicOpen (gg x)) Γ(X, X.basicOpen (gg x)))) := by
      rw [Submodule.mem_pi]
      intro i hi
      rw [Submodule.mem_bot, resPi_apply,
        (Submodule.mem_bot _).mp (h2 i hi), map_zero]
    have h0 := (hloc (X.affineBasicOpen (gg x)) (VV x) (hgV x)).disjoint
    rw [Submodule.disjoint_def] at h0
    have hv0 := h0 _ hres1 hres2
    have hℓ := congrFun hv0 ℓ
    exact hℓ.trans (map_zero _).symm
  · rw [codisjoint_iff_le_sup]
    rintro v -
    have hdec : ∀ x : ↥U'.1, ∃ w,
        w ∈ (K.comap f).submodule (X.affineBasicOpen (gg x)) ∧
        X.resPi (show (X.affineBasicOpen (gg x)).1 ≤ U'.1 from
          X.basicOpen_le (gg x)) n v - w ∈
          Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
            (fun _ ↦ (⊥ : Submodule Γ(X, (X.affineBasicOpen (gg x)).1)
              Γ(X, (X.affineBasicOpen (gg x)).1))) := by
      intro x
      have hcd := (hloc (X.affineBasicOpen (gg x)) (VV x) (hgV x)).codisjoint
      rw [codisjoint_iff_le_sup] at hcd
      obtain ⟨w, hw, c, hc, hwc⟩ := Submodule.mem_sup.mp
        (hcd (Submodule.mem_top
          (x := X.resPi (show (X.affineBasicOpen (gg x)).1 ≤ U'.1 from
            X.basicOpen_le (gg x)) n v)))
      refine ⟨w, hw, ?_⟩
      rw [← hwc]
      simpa using hc
    choose w hwmem hwC using hdec
    have hres_sub : ∀ {U V : X.Opens} (h : V ≤ U) (a b : Fin n → Γ(X, U)),
        X.resPi h n (a - b) = X.resPi h n a - X.resPi h n b := by
      intro U V h a b
      funext i
      simp [resPi_apply, map_sub]
    have hagree : ∀ x y : ↥U'.1,
        X.resPi (X.basicOpen_le
          (((X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op) (gg y) :
            Γ(X, (X.affineBasicOpen (gg x)).1)))) n (w x) =
        X.resPi (show X.basicOpen
            (((X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op) (gg y) :
              Γ(X, (X.affineBasicOpen (gg x)).1))) ≤ (X.affineBasicOpen (gg y)).1 from
          (Scheme.basicOpen_res _ _ _).trans_le inf_le_right) n (w y) := by
      intro x y
      set cxy : Γ(X, (X.affineBasicOpen (gg x)).1) :=
        (X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op) (gg y) with hcxy
      have hle₁ : X.basicOpen cxy ≤ (X.affineBasicOpen (gg x)).1 := X.basicOpen_le _
      have hle₂ : X.basicOpen cxy ≤ (X.affineBasicOpen (gg y)).1 := by
        rw [show X.basicOpen cxy = X.basicOpen
          ((X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op) (gg y)) from rfl,
          Scheme.basicOpen_res]
        exact inf_le_right
      have hd1 : X.resPi hle₁ n (w x) - X.resPi hle₂ n (w y) ∈
          (K.comap f).submodule (X.affineBasicOpen cxy) :=
        Submodule.sub_mem _
          (K.resPi_mem_comapSubmodule_of_le f
            (U₀ := X.affineBasicOpen (gg x)) (W := X.affineBasicOpen cxy) hle₁
            (hwmem x))
          (K.resPi_mem_comapSubmodule_of_le f
            (U₀ := X.affineBasicOpen (gg y)) (W := X.affineBasicOpen cxy) hle₂
            (hwmem y))
      have hd2 : X.resPi hle₁ n (w x) - X.resPi hle₂ n (w y) ∈
          Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
            (fun _ ↦ (⊥ : Submodule Γ(X, X.basicOpen cxy) Γ(X, X.basicOpen cxy))) := by
        have hdiff : X.resPi hle₁ n (w x) - X.resPi hle₂ n (w y) =
            X.resPi hle₂ n (X.resPi (show (X.affineBasicOpen (gg y)).1 ≤ U'.1 from
              X.basicOpen_le (gg y)) n v - w y) -
            X.resPi hle₁ n (X.resPi (show (X.affineBasicOpen (gg x)).1 ≤ U'.1 from
              X.basicOpen_le (gg x)) n v - w x) := by
          rw [hres_sub, hres_sub]
          have hv : X.resPi hle₁ n (X.resPi (show (X.affineBasicOpen (gg x)).1 ≤ U'.1
              from X.basicOpen_le (gg x)) n v) =
              X.resPi hle₂ n (X.resPi (show (X.affineBasicOpen (gg y)).1 ≤ U'.1 from
                X.basicOpen_le (gg y)) n v) := by
            rw [resPi_resPi, resPi_resPi]
          rw [hv]
          abel
        rw [Submodule.mem_pi]
        intro i hi
        rw [Submodule.mem_bot, hdiff, Pi.sub_apply]
        have h2x := hwC x
        have h2y := hwC y
        rw [Submodule.mem_pi] at h2x h2y
        rw [resPi_apply, resPi_apply, (Submodule.mem_bot _).mp (h2x i hi),
          (Submodule.mem_bot _).mp (h2y i hi), map_zero, map_zero, sub_self]
      have h0 := (hloc (X.affineBasicOpen cxy) (VV x) (hle₁.trans (hgV x))).disjoint
      rw [Submodule.disjoint_def] at h0
      have h5 := h0 _ hd1 hd2
      exact sub_eq_zero.mp h5
    have hglue : ∀ ℓ : Fin n, ∃ s : Γ(X, U'.1), ∀ x : ↥U'.1,
        (X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op).hom s = w x ℓ := by
      intro ℓ
      have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1
          (fun x : ↥U'.1 ↦ X.basicOpen (gg x)) (fun x ↦ w x ℓ) := by
        intro x y
        have hle₀ : X.basicOpen (gg x) ⊓ X.basicOpen (gg y) ≤
            X.basicOpen (((X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op)
              (gg y) : Γ(X, (X.affineBasicOpen (gg x)).1))) :=
          le_of_eq (Scheme.basicOpen_res _ _ _).symm
        have h2 := congrFun (congrArg (X.resPi hle₀ n) (hagree x y)) ℓ
        exact ((presheaf_map_map_apply _ _ _ (w x ℓ)).symm.trans h2).trans
          (presheaf_map_map_apply _ _ _ (w y ℓ))
      obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing'
        (fun x : ↥U'.1 ↦ X.basicOpen (gg x)) U'.1
        (fun x ↦ homOfLE (X.basicOpen_le (gg x))) hcover (fun x ↦ w x ℓ) hcompat
      exact ⟨s, fun x ↦ hs x⟩
    choose s hs using hglue
    have hsmem : (fun ℓ ↦ s ℓ) ∈ (K.comap f).submodule U' := by
      refine K.mem_comapSubmodule_of_forall_res f (fun x : ↥U'.1 ↦ gg x) ?_ ?_
      · intro x hx
        exact ⟨⟨x, hx⟩, hxg _⟩
      · intro x
        rw [show X.resPi (X.basicOpen_le (gg x)) n (fun ℓ ↦ s ℓ) = w x from
          funext fun ℓ ↦ hs ℓ x]
        exact hwmem x
    refine Submodule.mem_sup.mpr ⟨fun ℓ ↦ s ℓ, hsmem, v - fun ℓ ↦ s ℓ, ?_, by abel⟩
    rw [Submodule.mem_pi]
    intro i hi
    rw [Submodule.mem_bot]
    refine X.sheaf.eq_of_locally_eq' (fun x : ↥U'.1 ↦ X.basicOpen (gg x)) U'.1
      (fun x ↦ homOfLE (X.basicOpen_le (gg x))) hcover _ 0 fun x ↦ ?_
    have hC := hwC x
    rw [Submodule.mem_pi] at hC
    have h3 := (Submodule.mem_bot _).mp (hC i hi)
    have h4 : (X.presheaf.map (homOfLE (X.basicOpen_le (gg x))).op).hom
        ((v - fun ℓ ↦ s ℓ) i) =
        (X.resPi (show (X.affineBasicOpen (gg x)).1 ≤ U'.1 from
          X.basicOpen_le (gg x)) n v - w x) i := by
      rw [Pi.sub_apply, Pi.sub_apply, map_sub]
      congr 1
      exact hs i x
    exact (h4.trans h3).trans (map_zero _).symm

/-- Pullback of a global coordinate graph is the graph of the pulled-back global
coordinate functions. -/
lemma coordinateGraphData_comap {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(Y, ⊤)) :
    (coordinateGraphData Y I a).comap f =
      coordinateGraphData X I (fun i j ↦ f.appTop.hom (a i j)) := by
  apply SubmoduleSheafData.ext
  funext U
  let L := coordinateGraphData X I (fun i j ↦ f.appTop.hom (a i j))
  have hcov : ∀ x ∈ U.1, ∃ (g : Γ(X, U.1)) (V : Y.affineOpens),
      x ∈ X.basicOpen g ∧ X.basicOpen g ≤ f ⁻¹ᵁ V.1 := by
    intro x hx
    obtain ⟨V, hVaff, hfxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens (U := ⊤) (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨g, hgle, hxg⟩ := U.2.exists_basicOpen_le
      (V := U.1 ⊓ f ⁻¹ᵁ V) ⟨x, hx, hfxV⟩ hx
    rw [le_inf_iff] at hgle
    exact ⟨g, ⟨V, hVaff⟩, hxg, hgle.2⟩
  have hle : ((coordinateGraphData Y I a).comap f).submodule U ≤ L.submodule U := by
    intro v hv
    apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    obtain ⟨g, V, hxg, hgV⟩ := hcov x hx
    refine ⟨g, hxg, ?_⟩
    have hres := (coordinateGraphData Y I a).resPi_mem_comapSubmodule_of_le f
      (U₀ := U) (W := X.affineBasicOpen g) (X.affineBasicOpen_le g) hv
    change X.resPi (X.affineBasicOpen_le g) n v ∈
      (((coordinateGraphData Y I a).comap f).submodule (X.affineBasicOpen g)) at hres
    rw [coordinateGraphData_comap_submodule_of_le f I a
      (X.affineBasicOpen g) V hgV] at hres
    change X.resPi (X.affineBasicOpen_le g) n v ∈
      Submodule.span Γ(X, (X.affineBasicOpen g).1)
        (X.resPi (X.affineBasicOpen_le g) n ''
          (L.submodule U : Set (Fin n → Γ(X, U.1))))
    rw [L.span_resPi_basicOpen U g]
    exact hres
  exact Submodule.eq_of_le_of_isCompl
    ((coordinateGraphData_isComplementOfCoords Y I a).comap f U)
    (coordinateGraphData_isComplementOfCoords X I
      (fun i j ↦ f.appTop.hom (a i j)) U) hle

variable (q : ℕ) (n : ℕ) (I : Finset (Fin n))

/-- **Equation 2.2.1** (`eqn:GrI`) (the implicit definition of the subfunctor `Gr_I`):
the chart subfunctor `Gr_I ⊆ Gr(q, n)` of the Grassmannian: the points `K` such that
the composite `O_T^{⊕I} → O_T^{⊕n} → O_T^{⊕n}/K` is an isomorphism, encoded by the
complement condition `IsComplementOfCoords`. -/
def grassmannianChart : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := {K : (grassmannianFunctor q n).obj T // K.1.IsComplementOfCoords I}
  map f := ↾fun K ↦ ⟨(grassmannianFunctor q n).map f K.1, K.2.comap f.unop⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun K ↦ Subtype.ext ?_
    change (grassmannianFunctor q n).map (𝟙 T) K.1 = K.1
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp u v := by
    refine ConcreteCategory.hom_ext _ _ fun K ↦ Subtype.ext ?_
    change (grassmannianFunctor q n).map (u ≫ v) K.1 =
      (grassmannianFunctor q n).map v ((grassmannianFunctor q n).map u K.1)
    rw [Functor.map_comp]
    rfl

/-- **Equation 2.2.3** (`eq:grassmannian-matrix`) (the matrix-to-quotient assignment): a
matrix of global functions gives the corresponding point of the standard Grassmannian
chart — the kernel encoding of the block-matrix quotient `(1 | f) : O_T^{⊕n} → O_T^{⊕q}`
of the book's proof of Lemma 2.2.2. -/
def coordinateMatrixChartPoint (X : Scheme.{u}) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    (grassmannianChart q n I).obj (op X) :=
  ⟨⟨coordinateGraphData X I a, by
      rw [← hI]
      exact coordinateGraphData_quotientProjectiveOfRank X I a⟩,
    coordinateGraphData_isComplementOfCoords X I a⟩

/-- Vectors indexed by the lifted product `I × Iᶜ` are the same as coordinate
matrices. -/
def coordinateVectorMatrixEquiv (R : Type*) :
    (ULift.{u} (↑I × ↑(Iᶜ)) → R) ≃ ((i : ↑I) → (j : ↑(Iᶜ)) → R) where
  toFun v i j := v (ULift.up (i, j))
  invFun a z := a z.down.1 z.down.2
  left_inv v := by funext z; cases z; rfl
  right_inv a := by funext i j; rfl

/-- Morphisms to affine space over the terminal scheme are identified with their
global coordinate functions. -/
noncomputable def affineSpaceTerminalHomEquiv (X : Scheme.{u})
    (m : Type u) :
    (X ⟶ AffineSpace m (⊤_ Scheme.{u})) ≃ (m → Γ(X, ⊤)) where
  toFun f := AffineSpace.homOverEquiv (S := ⊤_ Scheme.{u}) ⟨f, inferInstance⟩
  invFun v := (AffineSpace.homOverEquiv (S := ⊤_ Scheme.{u})).symm v |>.1
  left_inv f := by
    exact congrArg Subtype.val
      ((AffineSpace.homOverEquiv (S := ⊤_ Scheme.{u})).symm_apply_apply
        ⟨f, inferInstance⟩)
  right_inv v := (AffineSpace.homOverEquiv (S := ⊤_ Scheme.{u})).apply_symm_apply v

/-- The objectwise equivalence between matrices of global functions and the standard
Grassmannian chart. -/
noncomputable def coordinateMatrixChartEquiv (X : Scheme.{u}) (hI : I.card = q) :
    ((i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) ≃
      (grassmannianChart q n I).obj (op X) where
  toFun := coordinateMatrixChartPoint q n I X hI
  invFun K := K.1.1.globalCoordinateMatrix I K.2
  left_inv a := SubmoduleSheafData.globalCoordinateMatrix_coordinateGraphData X I a
  right_inv K := by
    apply Subtype.ext
    apply Subtype.ext
    exact K.1.1.coordinateGraphData_globalCoordinateMatrix I K.2

/-- Background definition for Equation 2.2.1 (the inclusion of the chart subfunctor): the
monomorphism of functors `Gr_I ⟶ Gr(q, n)`. -/
def grassmannianChartι : grassmannianChart.{u} q n I ⟶ grassmannianFunctor.{u} q n where
  app T := ↾fun K ↦ K.1

instance grassmannianChartι_mono : Mono (grassmannianChartι.{u} q n I) := by
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  intro T
  apply ConcreteCategory.mono_of_injective
  intro x y h
  exact Subtype.ext h

/-- Background definition for Lemma 2.2.2 (the explicit representation):
the representation of a standard Grassmannian chart by affine space, whose underlying
equivalence is the matrix map `φ` of Equation 2.2.3. -/
noncomputable def grassmannianChartAffineRepresentation (hI : I.card = q) :
    (grassmannianChart.{u} q n I).RepresentableBy
      (AffineSpace (ULift.{u} (↑I × ↑(Iᶜ))) (⊤_ Scheme.{u})) := by
  let m := ULift.{u} (↑I × ↑(Iᶜ))
  refine {
    homEquiv {X} := (affineSpaceTerminalHomEquiv X m).trans
      ((coordinateVectorMatrixEquiv n I Γ(X, ⊤)).trans
        (coordinateMatrixChartEquiv q n I X hI))
    homEquiv_comp := by
      intro X X' f g
      apply Subtype.ext
      apply Subtype.ext
      change coordinateGraphData X I
          (fun i j ↦ (f ≫ g).appTop.hom
            (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j)))) =
        (coordinateGraphData X' I
          (fun i j ↦ g.appTop.hom
            (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j))))).comap f
      rw [coordinateGraphData_comap]
      congr 1 }

/-- **Lemma 2.2.2** (`lem:grassmannian-open-representable`): for each subset
`I ⊆ {1, …, n}` of size `q`, the subfunctor `Gr_I` of `Gr(q, n)` is representable by the
affine space `𝔸^{I × Iᶜ}` (of dimension `q(n-q)`) over `Spec ℤ` (the terminal scheme). -/
theorem grassmannianChart_representableBy_affineSpace (hI : I.card = q) :
    Nonempty ((grassmannianChart.{u} q n I).RepresentableBy
      (AffineSpace (ULift.{u} (↑I × ↑(Iᶜ))) (⊤_ Scheme.{u}))) :=
  ⟨grassmannianChartAffineRepresentation q n I hI⟩

end AlgebraicGeometry.Scheme

end LemGrassmannianOpenRepresentable


section LemGrassmannianOpenSubfunctor

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (q n : ℕ)

/-- The open-immersion statement for a standard Grassmannian chart indexed by exactly
`q` coordinates. -/
theorem presheaf_isOpenImmersion_grassmannianChartι_of_card_eq
    (I : Finset (Fin n)) (hI : I.card = q) :
    MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (grassmannianChartι q n I) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let K : (grassmannianFunctor q n).obj (op T) := yonedaEquiv g
  let U : T.Opens := K.1.coordinateChartOpen I
  have hKU : (K.1.comap U.ι).IsComplementOfCoords I := by
    rw [K.1.isComplementOfCoords_comap_iff_preimage_coordinateChartOpen_eq_top
      hI K.2 U.ι]
    change U.ι ⁻¹ᵁ U = ⊤
    simp
  let kU : (grassmannianChart q n I).obj (op U.toScheme) :=
    ⟨⟨K.1.comap U.ι, K.2.comap U.ι⟩, hKU⟩
  let fst : yoneda.obj U.toScheme ⟶ grassmannianChart q n I :=
    yonedaEquiv.symm kU
  have hw : fst ≫ grassmannianChartι q n I = yoneda.map U.ι ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    dsimp [fst]
    rw [Equiv.apply_symm_apply]
    have hg : g.app (op U.toScheme) U.ι =
        (grassmannianFunctor q n).map U.ι.op K := by
      calc
        g.app (op U.toScheme) U.ι = yonedaEquiv (yoneda.map U.ι ≫ g) := by
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
        _ = (grassmannianFunctor q n).map U.ι.op K := by
          simpa [K] using (yonedaEquiv_naturality g U.ι).symm
    rw [hg]
    change kU.1 = (grassmannianFunctor q n).map U.ι.op K
    rfl
  refine ⟨U.toScheme, fst, U.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  intro Z
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app Z) hw, ?_, ?_⟩
  · intro a b hab
    apply (cancel_mono U.ι).mp
    exact hab.2
  · intro L a hLa
    have hcomp : (K.1.comap a).IsComplementOfCoords I := by
      have hg : g.app Z a = (grassmannianFunctor q n).map a.op K := by
        calc
          g.app Z a = yonedaEquiv (yoneda.map a ≫ g) := by
            rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
          _ = (grassmannianFunctor q n).map a.op K := by
            simpa [K] using (yonedaEquiv_naturality g a).symm
      have heq : (K.1.comap a) = L.1.1 := by
        rw [hg] at hLa
        exact congrArg (fun z : (grassmannianFunctor q n).obj Z ↦ z.1) hLa.symm
      rw [heq]
      exact L.2
    have hopen : a ⁻¹ᵁ U = ⊤ :=
      (K.1.isComplementOfCoords_comap_iff_preimage_coordinateChartOpen_eq_top
        hI K.2 a).mp hcomp
    have hrange : Set.range a.base ⊆ Set.range U.ι.base := by
      rintro _ ⟨z, rfl⟩
      refine ⟨⟨a.base z, ?_⟩, rfl⟩
      have : z ∈ a ⁻¹ᵁ U := hopen.symm ▸ trivial
      exact this
    let b : unop Z ⟶ U.toScheme := IsOpenImmersion.lift U.ι a hrange
    refine ⟨b, ?_, ?_⟩
    · apply Subtype.ext
      have hb := ConcreteCategory.congr_hom (NatTrans.congr_app hw Z) b
      change (fst.app Z b).1 = L.1
      change (fst.app Z b).1 = g.app Z (b ≫ U.ι) at hb
      rw [IsOpenImmersion.lift_fac U.ι a hrange] at hb
      change L.1 = g.app Z a at hLa
      exact hb.trans hLa.symm
    · exact IsOpenImmersion.lift_fac U.ι a hrange

/-- A standard chart indexed by the wrong number of coordinates is represented,
relative to the Grassmannian, by the empty open subscheme. -/
theorem presheaf_isOpenImmersion_grassmannianChartι_of_card_ne
    (I : Finset (Fin n)) (hI : I.card ≠ q) :
    MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (grassmannianChartι q n I) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let K : (grassmannianFunctor q n).obj (op T) := yonedaEquiv g
  let U : T.Opens := ⊥
  letI : IsEmpty U.toScheme := ⟨fun x ↦ x.2⟩
  have hKU : (K.1.comap U.ι).IsComplementOfCoords I :=
    (K.1.comap U.ι).isComplementOfCoords_of_isEmpty I
  let kU : (grassmannianChart q n I).obj (op U.toScheme) :=
    ⟨⟨K.1.comap U.ι, K.2.comap U.ι⟩, hKU⟩
  let fst : yoneda.obj U.toScheme ⟶ grassmannianChart q n I :=
    yonedaEquiv.symm kU
  have hw : fst ≫ grassmannianChartι q n I = yoneda.map U.ι ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    dsimp [fst]
    rw [Equiv.apply_symm_apply]
    have hg : g.app (op U.toScheme) U.ι =
        (grassmannianFunctor q n).map U.ι.op K := by
      calc
        g.app (op U.toScheme) U.ι = yonedaEquiv (yoneda.map U.ι ≫ g) := by
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
        _ = (grassmannianFunctor q n).map U.ι.op K := by
          simpa [K] using (yonedaEquiv_naturality g U.ι).symm
    rw [hg]
    change kU.1 = (grassmannianFunctor q n).map U.ι.op K
    rfl
  refine ⟨U.toScheme, fst, U.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  intro Z
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app Z) hw, ?_, ?_⟩
  · intro a b hab
    apply (cancel_mono U.ι).mp
    exact hab.2
  · intro L a hLa
    letI : IsEmpty Z.unop :=
      L.1.1.isEmpty_of_isComplementOfCoords_of_card_ne L.1.2 L.2 hI
    have hrange : Set.range a.base ⊆ Set.range U.ι.base := by
      rintro _ ⟨z, -⟩
      exact isEmptyElim z
    let b : Z.unop ⟶ U.toScheme := IsOpenImmersion.lift U.ι a hrange
    refine ⟨b, ?_, ?_⟩
    · apply Subtype.ext
      have hb := ConcreteCategory.congr_hom (NatTrans.congr_app hw Z) b
      change (fst.app Z b).1 = L.1
      change (fst.app Z b).1 = g.app Z (b ≫ U.ι) at hb
      rw [IsOpenImmersion.lift_fac U.ι a hrange] at hb
      change L.1 = g.app Z a at hLa
      exact hb.trans hLa.symm
    · exact IsOpenImmersion.lift_fac U.ι a hrange

/-- **Lemma 2.2.4** (`lem:grassmannian-open-subfunctor`, openness part): the inclusion
`Gr_I ⟶ Gr(q, n)` is relatively representable by open immersions: for every scheme `T`
and morphism `T → Gr(q, n)`, the fiber product `Gr_I ×_{Gr(q,n)} T` is representable by
an open subscheme of `T` (the chart open of the corresponding submodule datum). -/
theorem presheaf_isOpenImmersion_grassmannianChartι (I : Finset (Fin n)) :
    MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (grassmannianChartι q n I) := by
  by_cases hI : I.card = q
  · exact presheaf_isOpenImmersion_grassmannianChartι_of_card_eq q n I hI
  · exact presheaf_isOpenImmersion_grassmannianChartι_of_card_ne q n I hI

/-- **Lemma 2.2.4** (`lem:grassmannian-open-subfunctor`, covering part): the family of
chart subfunctors `Gr_I`, over all subsets `I` of size `q`, is jointly Zariski-locally
surjective onto `Gr(q, n)`: every point of `Gr(q, n)(T)` lies in some `Gr_I`
Zariski-locally on `T` (over a field, a surjection `κ^n ↠ Q` with `dim Q = q` has an
invertible `q × q` minor). -/
theorem isLocallySurjective_grassmannianChartι :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun I : {I : Finset (Fin n) // I.card = q} ↦
        grassmannianChartι.{u} q n I.1) := by
  refine ⟨?_⟩
  rintro T K
  let 𝒰 : T.OpenCover :=
    { I₀ := {I : Finset (Fin n) // I.card = q}
      X := fun I ↦ (K.1.coordinateChartOpen I.1).toScheme
      f := fun I ↦ (K.1.coordinateChartOpen I.1).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, fun I ↦ inferInstance⟩
        intro x
        have hx : x ∈ ⨆ I : {I : Finset (Fin n) // I.card = q},
            K.1.coordinateChartOpen I.1 := by
          rw [SubmoduleSheafData.iSup_coordinateChartOpen_eq_top q K.1 K.2]
          trivial
        rw [TopologicalSpace.Opens.mem_iSup] at hx
        obtain ⟨I, hxI⟩ := hx
        exact ⟨I, ⟨⟨x, hxI⟩, rfl⟩⟩ }
  refine Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.generate_le_iff]
  rintro X f ⟨I⟩
  let L : (grassmannianChart q n I.1).obj (Opposite.op (𝒰.X I)) :=
    ⟨⟨K.1.comap (𝒰.f I), K.2.comap (𝒰.f I)⟩,
      (K.1.isComplementOfCoords_comap_iff_preimage_coordinateChartOpen_eq_top
        I.2 K.2 (𝒰.f I)).2 (by
          change (K.1.coordinateChartOpen I.1).ι ⁻¹ᵁ
            K.1.coordinateChartOpen I.1 = ⊤
          simp)⟩
  refine ⟨(Limits.Sigma.ι (fun I : {I : Finset (Fin n) // I.card = q} ↦
    grassmannianChart.{u} q n I.1) I).app (op (𝒰.X I)) L, ?_⟩
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Limits.Sigma.ι_desc
      (fun I : {I : Finset (Fin n) // I.card = q} ↦ grassmannianChartι.{u} q n I.1) I)
    (op (𝒰.X I))) L
  exact (congrArg Subtype.val h).trans rfl

/-- The Grassmannian functor is a sheaf for the Zariski topology (quasi-coherent
submodule sheaves with locally free quotient glue). -/
theorem isSheaf_grassmannianFunctor :
    Presieve.IsSheaf Scheme.zariskiTopology.{u} (grassmannianFunctor q n) := by
  rw [Scheme.zariskiPrecoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨I, Y, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let 𝒰 : T.OpenCover :=
    { I₀ := I
      X := Y
      f := f
      mem₀ := hR }
  let K : ∀ i, (𝒰.X i).SubmoduleSheafData n := fun i ↦ (x i).1
  have hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b := by
    intro i j Z a b hab
    exact congrArg Subtype.val (hx i j Z a b hab)
  obtain ⟨L, hL⟩ :=
    SubmoduleSheafData.exists_submoduleSheafData_of_openCover 𝒰 K hcompat
  have hLrank : L.QuotientProjectiveOfRank q :=
    SubmoduleSheafData.QuotientProjectiveOfRank.of_comap_openCover L 𝒰
      (fun i ↦ hL i ▸ (x i).2)
  let t : (grassmannianFunctor q n).obj (op T) := ⟨L, hLrank⟩
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ?_⟩
  · exact Subtype.ext (hL i)
  · apply Subtype.ext
    apply SubmoduleSheafData.eq_of_comap_eq_openCover 𝒰
    intro i
    have ht'i := congrArg Subtype.val (ht' i)
    exact ht'i.trans (hL i).symm

end AlgebraicGeometry.Scheme

end LemGrassmannianOpenSubfunctor


section PropGrassmannianRepresentableScheme

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Finite-dimensional affine space is smooth over its base. -/
lemma smooth_affineSpace_over (m : Type u) [Finite m] (S : Scheme.{u}) :
    Smooth (AffineSpace.over (n := m) (S := S)).hom := by
  have hpoly : Smooth
      (specULiftZIsTerminal.from
        (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ))))) := by
    rw [show specULiftZIsTerminal.from
        (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (MvPolynomial m (ULift.{u} ℤ)))) by
        exact specULiftZIsTerminal.hom_ext _ _]
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    change (algebraMap (ULift.{u} ℤ) (MvPolynomial m (ULift.{u} ℤ))).Smooth
    rw [RingHom.smooth_algebraMap]
    exact { formallySmooth := inferInstance, finitePresentation := inferInstance }
  letI : Smooth
      (terminal.from (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ))))) := by
    letI : Smooth (specULiftZIsTerminal.from
        (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ))))) := hpoly
    letI : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
      isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
    rw [show terminal.from (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ)))) =
      specULiftZIsTerminal.from
          (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ)))) ≫
        terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) by
          exact terminalIsTerminal.hom_ext _ _]
    infer_instance
  change Smooth (pullback.fst (terminal.from S)
    (terminal.from (Spec (CommRingCat.of (MvPolynomial m (ULift.{u} ℤ))))))
  infer_instance

/-- A universe-compatible index type for the standard charts of `Gr(q,n)`. -/
abbrev grassmannianChartCoverIndex (q n : ℕ) :=
  ULift.{u} {I : Finset (Fin n) // I.card = q}

/-- The affine space representing one member of the standard Grassmannian chart
cover. -/
noncomputable abbrev grassmannianChartCoverScheme (q n : ℕ)
    (I : grassmannianChartCoverIndex.{u} q n) : Scheme.{u} :=
  AffineSpace (ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (⊤_ Scheme.{u})

/-- The explicit affine representation of one member of the standard chart cover. -/
noncomputable def grassmannianChartCoverRepresentation (q n : ℕ)
    (I : grassmannianChartCoverIndex.{u} q n) :
    (grassmannianChart.{u} q n I.down.1).RepresentableBy
      (grassmannianChartCoverScheme q n I) :=
  grassmannianChartAffineRepresentation q n I.down.1 I.down.2

/-- A represented standard chart mapped into the Grassmannian functor. -/
noncomputable def grassmannianRepresentableChartMap (q n : ℕ)
    (I : grassmannianChartCoverIndex.{u} q n) :
    yoneda.obj (grassmannianChartCoverScheme q n I) ⟶ grassmannianFunctor.{u} q n :=
  (grassmannianChartCoverRepresentation q n I).toIso.hom ≫
    grassmannianChartι q n I.down.1

/-- Each represented chart map is relatively representable by open immersions. -/
lemma presheaf_isOpenImmersion_grassmannianRepresentableChartMap
    (q n : ℕ) (I : grassmannianChartCoverIndex.{u} q n) :
    MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u})
      (grassmannianRepresentableChartMap q n I) := by
  rw [grassmannianRepresentableChartMap,
    (MorphismProperty.presheaf
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).cancel_left_of_respectsIso]
  exact presheaf_isOpenImmersion_grassmannianChartι q n I.down.1
--
-- /-- The coproduct of all represented standard charts mapping to `Gr(q,n)`. -/
noncomputable abbrev grassmannianRepresentableChartCoverMap (q n : ℕ) :
    (∐ fun I : grassmannianChartCoverIndex.{u} q n ↦
      yoneda.obj (grassmannianChartCoverScheme q n I)) ⟶ grassmannianFunctor.{u} q n :=
  Limits.Sigma.desc (grassmannianRepresentableChartMap q n)

noncomputable instance grassmannianRepresentableChartCoverMap_isLocallySurjective
    (q n : ℕ) : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (grassmannianRepresentableChartCoverMap.{u} q n) := by
  let ι₀ := {I : Finset (Fin n) // I.card = q}
  let ι := grassmannianChartCoverIndex.{u} q n
  let chartFamily (I : ι₀) := grassmannianChart.{u} q n I.1
  let chartMap (I : ι₀) := grassmannianChartι.{u} q n I.1
  let representedCharts : (∐ fun I : ι ↦
      yoneda.obj (grassmannianChartCoverScheme q n I)) ⟶
      ∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1 :=
    Limits.Sigma.map fun I ↦ (grassmannianChartCoverRepresentation q n I).toIso.hom
  letI : IsIso representedCharts := inferInstance
  have hrepresented : representedCharts ≫
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) =
      grassmannianRepresentableChartCoverMap q n := by
    apply Limits.Sigma.hom_ext
    intro I
    rw [← Category.assoc]
    rw [Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
      grassmannianRepresentableChartCoverMap, Limits.Sigma.ι_desc]
    rfl
  let reindexCharts : (∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1) ≅
      ∐ chartFamily := Limits.Sigma.reindex Equiv.ulift chartFamily
  have hreindex : reindexCharts.hom ≫ Limits.Sigma.desc chartMap =
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) := by
    refine Limits.Sigma.hom_ext _ _ fun I ↦ ?_
    rw [← Category.assoc, show
      Limits.Sigma.ι (fun I : ι ↦ grassmannianChart.{u} q n I.down.1) I ≫
          reindexCharts.hom = Limits.Sigma.ι chartFamily I.down by
        exact Limits.Sigma.ι_reindex_hom (f := chartFamily) Equiv.ulift I]
    simp [chartMap]
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc chartMap) := isLocallySurjective_grassmannianChartι q n
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology reindexCharts.hom :=
    inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (reindexCharts.hom ≫ Limits.Sigma.desc chartMap) := inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    hreindex ▸ inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology representedCharts :=
    inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (representedCharts ≫
        Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    inferInstance
  have hlocal : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (representedCharts ≫
        Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    inferInstance
  rw [hrepresented] at hlocal
  exact hlocal
--
/-- The scheme gluing datum obtained from the standard affine chart cover of the
Grassmannian. -/
noncomputable def grassmannianGlueData (q n : ℕ) : Scheme.GlueData :=
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨grassmannianFunctor q n,
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_grassmannianFunctor q n)⟩
  Scheme.LocalRepresentability.glueData (F := F)
    (f := grassmannianRepresentableChartMap q n)
    (presheaf_isOpenImmersion_grassmannianRepresentableChartMap q n)

/-- The canonical representation of `Gr(q,n)` by the scheme glued from its standard
affine charts. -/
noncomputable def grassmannianGluedRepresentation (q n : ℕ) :
    (grassmannianFunctor.{u} q n).RepresentableBy
      (grassmannianGlueData.{u} q n).glued := by
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨grassmannianFunctor q n,
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_grassmannianFunctor q n)⟩
  exact Scheme.LocalRepresentability.representableBy
    (F := F) (f := grassmannianRepresentableChartMap q n)
      (presheaf_isOpenImmersion_grassmannianRepresentableChartMap q n)

/-- The relative representative obtained by base-changing the absolute
Grassmannian from `Spec ℤ` to a scheme `S`. -/
noncomputable def grassmannianOverRepresentation (S : Scheme.{u}) (q n : ℕ) :
    Over S :=
  Over.mk (pullback.fst (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (grassmannianGlueData q n).glued))

/-- Maps over `S` to the base-changed Grassmannian are equivalent to
Grassmannian points on the source. -/
noncomputable def grassmannianOverHomEquiv (S : Scheme.{u}) (q n : ℕ)
    (T : Over S) :
    (T ⟶ Over.mk (pullback.fst (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (grassmannianGlueData q n).glued))) ≃
      ULift.{u + 1, u} ((grassmannianFunctor.{u} q n).obj (Opposite.op T.left)) where
  toFun k := ULift.up ((grassmannianGluedRepresentation q n).homEquiv
    (k.left ≫ pullback.snd _ _))
  invFun z := Over.homMk
    (pullback.lift T.hom
      ((grassmannianGluedRepresentation q n).homEquiv.symm z.down)
      (specULiftZIsTerminal.hom_ext _ _)) (by
        change pullback.lift T.hom
            ((grassmannianGluedRepresentation q n).homEquiv.symm z.down) _ ≫
          pullback.fst _ _ = T.hom
        exact pullback.lift_fst _ _ _)
  left_inv k := by
    ext
    change pullback.lift T.hom
      ((grassmannianGluedRepresentation q n).homEquiv.symm
        ((grassmannianGluedRepresentation q n).homEquiv
          (k.left ≫ pullback.snd _ _))) _ = k.left
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact (Over.w k).symm
    · rw [pullback.lift_snd]
      exact Equiv.symm_apply_apply _ _
  right_inv z := by
    refine ULift.ext _ _ ?_
    change (grassmannianGluedRepresentation q n).homEquiv
        (pullback.lift T.hom
          ((grassmannianGluedRepresentation q n).homEquiv.symm z.down)
          (specULiftZIsTerminal.hom_ext _ _) ≫ pullback.snd _ _) = z.down
    rw [pullback.lift_snd, Equiv.apply_symm_apply]

/-- The absolute Grassmannian functor, viewed on schemes over `S`, is represented
by the base change `S × Gr(q,n) → S`. -/
noncomputable def grassmannianFunctorOverRepresentableBy
    (S : Scheme.{u}) (q n : ℕ) :
    (Modules.grassmannianFunctorOver S q n).RepresentableBy
      (grassmannianOverRepresentation S q n) where
  homEquiv {T} := grassmannianOverHomEquiv S q n T
  homEquiv_comp {T T'} f g := by
    refine ULift.ext _ _ ?_
    change (grassmannianGluedRepresentation q n).homEquiv
        ((f ≫ g).left ≫ pullback.snd _ _) = _
    have h1 : ((f ≫ g).left ≫ pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (grassmannianGlueData q n).glued)) =
        f.left ≫ (g.left ≫ pullback.snd _ _) := by
      rw [Over.comp_left]
      exact Category.assoc _ _ _
    rw [h1, (grassmannianGluedRepresentation q n).homEquiv_comp
      f.left (g.left ≫ pullback.snd _ _)]
    rfl

/-- The relative Grassmannian of a canonical finite free sheaf is represented by
the base-changed absolute Grassmannian. -/
noncomputable def freeGrassmannianRepresentableBy
    (S : Scheme.{u}) (q n : ℕ) :
    (Modules.grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf)
        (ULift.{u} (Fin n)))).RepresentableBy
      (grassmannianOverRepresentation S q n) :=
  (grassmannianFunctorOverRepresentableBy S q n).ofIso
    (Modules.freeGrassmannianIsoGrassmannianFunctorOver q).symm

/-- Each map in the glued scheme's canonical open cover represents the corresponding
standard chart map into the Grassmannian functor. -/
lemma yoneda_map_grassmannianGlueData_openCover
    (q n : ℕ) (I : grassmannianChartCoverIndex.{u} q n) :
    yoneda.map ((grassmannianGlueData.{u} q n).openCover.f I) ≫
        (grassmannianGluedRepresentation q n).toIso.hom =
      grassmannianRepresentableChartMap q n I := by
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨grassmannianFunctor q n,
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_grassmannianFunctor q n)⟩
  exact Scheme.LocalRepresentability.yoneda_toGlued_yonedaGluedToSheaf
    (F := F) (f := grassmannianRepresentableChartMap q n)
    (presheaf_isOpenImmersion_grassmannianRepresentableChartMap q n) I

/-- **Proposition 2.2.5** (`prop:grassmannian-representable-scheme`): the functor
`Gr(q, n)`, sending a scheme `T` to the set of rank-`q` vector bundle quotients of
`O_T^{⊕n}` (encoded by their kernels), is representable by a scheme: it has a Zariski
open cover by the representable subfunctors `Gr_I`, and a Zariski sheaf with an open
cover by representables is representable. -/
theorem isRepresentable_grassmannianFunctor (q n : ℕ) :
    (grassmannianFunctor.{u} q n).IsRepresentable := by
  exact ⟨(grassmannianGlueData q n).glued,
    ⟨grassmannianGluedRepresentation q n⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- `Gr(q, n)` is smooth over `Spec ℤ` (of relative dimension `q(n-q)`; the dimension
statement awaits a notion of relative dimension). Stated for any scheme representing the
Grassmannian functor.

Source: *Stacks and Moduli*, Chapter 2, §2.2 (Projectivity of the Grassmannian), the
unlabelled easy exercise following Proposition 2.2.5 (smoothness of the Grassmannian). -/
theorem smooth_of_grassmannianFunctor_representableBy {q n : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P) :
    Smooth (specULiftZIsTerminal.from P) := by
  let ι₀ := {I : Finset (Fin n) // I.card = q}
  let ι := ULift.{u} ι₀
  let A (I : ι) : Scheme.{u} :=
    AffineSpace (ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (⊤_ Scheme.{u})
  let repr (I : ι) : (grassmannianChart.{u} q n I.down.1).RepresentableBy (A I) :=
    Classical.choice
      (grassmannianChart_representableBy_affineSpace q n I.down.1 I.down.2)
  let eChart (I : ι) : yoneda.obj (A I) ≅ grassmannianChart.{u} q n I.down.1 :=
    (repr I).toIso
  let f (I : ι) : yoneda.obj (A I) ⟶ grassmannianFunctor.{u} q n :=
    (eChart I).hom ≫ grassmannianChartι q n I.down.1
  have hf (I : ι) :
      MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u}) (f I) := by
    rw [show f I = (eChart I).hom ≫ grassmannianChartι q n I.down.1 from rfl,
      (MorphismProperty.presheaf
        (@IsOpenImmersion : MorphismProperty Scheme.{u})).cancel_left_of_respectsIso]
    exact presheaf_isOpenImmersion_grassmannianChartι q n I.down.1
  let mapCharts : (∐ fun I : ι ↦ yoneda.obj (A I)) ⟶
      ∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1 :=
    Limits.Sigma.map fun I ↦ (eChart I).hom
  letI : IsIso mapCharts := inferInstance
  have hfac : mapCharts ≫
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) =
      Limits.Sigma.desc f := by
    ext I
    simp [mapCharts, f]
  let chartFamily (I : ι₀) := grassmannianChart.{u} q n I.1
  let chartMap (I : ι₀) := grassmannianChartι.{u} q n I.1
  let reindexCharts : (∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1) ≅
      ∐ chartFamily := Limits.Sigma.reindex Equiv.ulift chartFamily
  have hreindex : reindexCharts.hom ≫ Limits.Sigma.desc chartMap =
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) := by
    refine Limits.Sigma.hom_ext _ _ fun I ↦ ?_
    rw [← Category.assoc, show
      Limits.Sigma.ι (fun I : ι ↦ grassmannianChart.{u} q n I.down.1) I ≫
          reindexCharts.hom = Limits.Sigma.ι chartFamily I.down by
        exact Limits.Sigma.ι_reindex_hom (f := chartFamily) (Equiv.ulift) I]
    simp [chartMap]
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc chartMap) := isLocallySurjective_grassmannianChartι q n
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology reindexCharts.hom :=
    inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (reindexCharts.hom ≫ Limits.Sigma.desc chartMap) := inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    hreindex ▸ inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology mapCharts := inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (mapCharts ≫ Limits.Sigma.desc
        (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    inferInstance
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) :=
    hfac ▸ inferInstance
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨grassmannianFunctor q n,
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_grassmannianFunctor q n)⟩
  let G := Scheme.LocalRepresentability.glueData (F := F) (f := f) hf
  have hG : Smooth (specULiftZIsTerminal.from G.glued) := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) G.openCover]
    intro I
    rw [Scheme.LocalRepresentability.glueData_openCover_map]
    rw [show Scheme.LocalRepresentability.toGlued hf I ≫
        specULiftZIsTerminal.from G.glued =
      specULiftZIsTerminal.from (A I) by
        exact specULiftZIsTerminal.hom_ext _ _]
    letI : Smooth (AffineSpace.over
        (n := ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (S := ⊤_ Scheme.{u})).hom :=
      smooth_affineSpace_over _ _
    letI : IsIso (specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
      isIso_of_isTerminal terminalIsTerminal specULiftZIsTerminal _
    rw [show specULiftZIsTerminal.from (A I) =
      (AffineSpace.over
          (n := ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (S := ⊤_ Scheme.{u})).hom ≫
        specULiftZIsTerminal.from (⊤_ Scheme.{u}) by
          exact specULiftZIsTerminal.hom_ext _ _]
    infer_instance
  let hGrep : (grassmannianFunctor.{u} q n).RepresentableBy G.glued :=
    Scheme.LocalRepresentability.representableBy (F := F) (f := f) hf
  let e : P ≅ G.glued := h.uniqueUpToIso hGrep
  have he : Smooth (e.hom ≫ specULiftZIsTerminal.from G.glued) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) _ _).2 hG
  rw [show e.hom ≫ specULiftZIsTerminal.from G.glued =
    specULiftZIsTerminal.from P by exact specULiftZIsTerminal.hom_ext _ _] at he
  exact he

end AlgebraicGeometry.Scheme

end PropGrassmannianRepresentableScheme


section ExerGrassmannianValuativeCriterion

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {n : ℕ}

/-- Transport of projectivity and constant stalk rank of the quotient across the
componentwise transport of a submodule of `A^n` along a ring equivalence. -/
lemma quotient_projective_rank_of_mapPiRingEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (N : Submodule A (Fin n → A)) {q : ℕ}
    (hproj : Module.Projective A ((Fin n → A) ⧸ N))
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk ((Fin n → A) ⧸ N) p = q) :
    Module.Projective B ((Fin n → B) ⧸ N.mapPiRingEquiv e) ∧
      ∀ p : PrimeSpectrum B,
        Module.rankAtStalk ((Fin n → B) ⧸ N.mapPiRingEquiv e) p = q := by
  let _ := RingHomInvPair.of_ringEquiv e
  let _ := RingHomInvPair.symm (e : A →+* B) (e.symm : B →+* A)
  let _ : Algebra A B := (e : A →+* B).toAlgebra
  let eQ : ((Fin n → A) ⧸ N) ≃ₛₗ[(e : A →+* B)] ((Fin n → B) ⧸ N.mapPiRingEquiv e) :=
    Submodule.Quotient.equiv _ _ (e.piSemilinearEquiv n) rfl
  have hfin : Module.Finite A ((Fin n → A) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  obtain ⟨_, h2, h3⟩ :=
    Module.finite_projective_rankAtStalk_of_semilinearEquiv e rfl eQ hfin hproj hrank
  exact ⟨h2, h3⟩

/-- Two quasi-coherent submodule data on an affine scheme agree as soon as their global
components agree. -/
lemma SubmoduleSheafData.eq_iff_submodule_top {X : Scheme.{u}} [IsAffine X]
    (K L : X.SubmoduleSheafData n) :
    K = L ↔ K.submodule ⟨⊤, isAffineOpen_top X⟩ = L.submodule ⟨⊤, isAffineOpen_top X⟩ := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← SubmoduleSheafData.ofAffineSubmodule_submodule K,
      ← SubmoduleSheafData.ofAffineSubmodule_submodule L, h]

/-- A submodule of the global sections of `O^{⊕n}` on an affine scheme whose quotient is
projective of constant rank `q` defines a rank-`q` locally free quotient datum. -/
lemma SubmoduleSheafData.quotientProjectiveOfRank_ofAffineSubmodule
    {X : Scheme.{u}} [IsAffine X] {q : ℕ}
    (W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤)))
    (hproj : Module.Projective Γ(X, ⊤) ((Fin n → Γ(X, ⊤)) ⧸ W))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk ((Fin n → Γ(X, ⊤)) ⧸ W) p = q) :
    (SubmoduleSheafData.ofAffineSubmodule W).QuotientProjectiveOfRank q := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top X⟩, trivial, ?_, ?_⟩
  · rw [SubmoduleSheafData.ofAffineSubmodule_submodule_top]
    exact hproj
  · rw [SubmoduleSheafData.ofAffineSubmodule_submodule_top]
    exact hrank

/-- The componentwise map on top sections induced by `Spec.map φ` is `φ` conjugated by
the global-sections isomorphisms. -/
lemma specMap_appPi_top {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (v : Fin n → Γ(Spec A, ⊤)) :
    (Spec.map φ).appPi ⊤ (by intro x _; trivial) n v =
      fun i ↦ (Scheme.ΓSpecIso B).inv.hom
        (φ.hom ((Scheme.ΓSpecIso A).hom.hom (v i))) := by
  funext i
  change ((Spec.map φ).appLE (⊤ : (Spec A).Opens) (⊤ : (Spec B).Opens) _).hom (v i) = _
  rw [show (Spec.map φ).appLE (⊤ : (Spec A).Opens) (⊤ : (Spec B).Opens)
      (by intro x _; trivial) = (Spec.map φ).app ⊤ by
    rw [(Spec.map φ).app_eq_appLE]
    congr 1]
  have h2 : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change ((Spec.map φ).appTop).hom (v i) = _
  rw [h2]
  rfl

/-- Bridging lemma: on top sections of spectra, the span of the pulled-back image of a
submodule datum equals a prescribed subspace iff the corresponding statement holds after
transport to the underlying rings along the global-sections isomorphisms. -/
lemma span_specMap_appPi_image_eq_iff {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (NΓ : Submodule Γ(Spec A, ⊤) (Fin n → Γ(Spec A, ⊤)))
    (WΓ : Submodule Γ(Spec B, ⊤) (Fin n → Γ(Spec B, ⊤))) :
    Submodule.span Γ(Spec B, ⊤)
        ((Spec.map φ).appPi ⊤
          (by intro x _; trivial) n '' (NΓ : Set (Fin n → Γ(Spec A, ⊤))))
        = WΓ ↔
      Submodule.span B
        ((fun (v : Fin n → A) i ↦ φ.hom (v i)) ''
          ((NΓ.mapPiRingEquiv
            (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv :
              Submodule A (Fin n → A)) : Set (Fin n → A))) =
        WΓ.mapPiRingEquiv
          (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv := by
  set eR := (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv with heR
  set eK := (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv with heK
  -- transport of the span across `eK`
  have hspan : (Submodule.span Γ(Spec B, ⊤)
      ((Spec.map φ).appPi ⊤ (by intro x _; trivial) n ''
        (NΓ : Set (Fin n → Γ(Spec A, ⊤))))).mapPiRingEquiv eK =
      Submodule.span B
        ((fun (v : Fin n → A) i ↦ φ.hom (v i)) ''
          ((NΓ.mapPiRingEquiv eR : Submodule A (Fin n → A)) : Set (Fin n → A))) := by
    rw [Submodule.mapPiRingEquiv_span]
    congr 1
    rw [← Set.image_comp]
    have hcoe : ((NΓ.mapPiRingEquiv eR : Submodule A (Fin n → A)) :
        Set (Fin n → A)) =
        (fun (w : Fin n → Γ(Spec A, ⊤)) i ↦ eR (w i)) ''
          (NΓ : Set (Fin n → Γ(Spec A, ⊤))) := by
      rw [Submodule.mapPiRingEquiv, Submodule.map_coe]
      rfl
    rw [hcoe, ← Set.image_comp]
    apply Set.image_congr
    intro v _
    funext i
    have happ := congrFun (specMap_appPi_top φ v) i
    change eK ((Spec.map φ).appPi ⊤ (by intro x _; trivial) n v i) =
      φ.hom (eR (v i))
    rw [happ]
    change eK (eK.symm (φ.hom (eR (v i)))) = φ.hom (eR (v i))
    rw [RingEquiv.apply_symm_apply]
  constructor
  · intro h
    rw [← hspan, h]
  · intro h
    have := hspan.trans h
    have hback := congrArg (fun U ↦ Submodule.mapPiRingEquiv eK.symm U) this
    simpa only [Submodule.mapPiRingEquiv_symm_mapPiRingEquiv] using hback

/-- Unfolding lemma: the Grassmannian functor acts on points by contraction of the
kernel datum. -/
lemma grassmannianFunctor_map_apply {q : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : (grassmannianFunctor.{u} q n).obj (op Y)) :
    (grassmannianFunctor.{u} q n).map f.op x = ⟨x.1.comap f, x.2.comap f⟩ :=
  rfl

/-- API lemma for Exercise 2.2.7 (the valuative
criterion): any scheme representing the Grassmannian functor satisfies the valuative
criterion over `Spec ℤ`. A `K`-point of `Gr(q, n)` is a subspace `W ⊆ K^n` of
codimension `q`; its unique extension to an `R`-point is the contraction
`N = W ∩ R^n`, whose quotient is finite free of rank `q` because it is a finitely
generated torsion-free module over a valuation ring. -/
theorem valuativeCriterion_of_grassmannianFunctor_representableBy {q n : ℕ}
    {P : Scheme.{u}} (h : (grassmannianFunctor.{u} q n).RepresentableBy P) :
    ValuativeCriterion (specULiftZIsTerminal.from P) := by
  intro S
  set φ : CommRingCat.of S.R ⟶ CommRingCat.of S.K :=
    CommRingCat.ofHom (algebraMap S.R S.K) with hφdef
  set eR := (Scheme.ΓSpecIso (CommRingCat.of S.R)).commRingCatIsoToRingEquiv with heR
  set eK := (Scheme.ΓSpecIso (CommRingCat.of S.K)).commRingCatIsoToRingEquiv with heK
  set xK := h.homEquiv S.i₁ with hxK
  set WΓ := xK.1.submodule ⟨⊤, isAffineOpen_top _⟩ with hWΓ
  set W : Submodule S.K (Fin n → S.K) := WΓ.mapPiRingEquiv eK with hW
  set N : Submodule S.R (Fin n → S.R) := W.comapPi with hN
  set NΓ : Submodule Γ(Spec (CommRingCat.of S.R), ⊤)
      (Fin n → Γ(Spec (CommRingCat.of S.R), ⊤)) := N.mapPiRingEquiv eR.symm with hNΓ
  have hNΓback : NΓ.mapPiRingEquiv eR = N := by
    rw [hNΓ, show eR = eR.symm.symm from (RingEquiv.symm_symm eR).symm]
    exact Submodule.mapPiRingEquiv_symm_mapPiRingEquiv eR.symm N
  have hmem : ∀ v : Fin n → S.R, v ∈ N ↔ (fun i ↦ algebraMap S.R S.K (v i)) ∈ W :=
    fun v ↦ Submodule.mem_comapPi W v
  -- the projectivity-and-rank package at the level of `S.K`
  have hprojΓK : Module.Projective Γ(Spec (CommRingCat.of S.K), ⊤)
      ((Fin n → Γ(Spec (CommRingCat.of S.K), ⊤)) ⧸ WΓ) :=
    xK.2.projective_affine ⟨⊤, isAffineOpen_top _⟩
  have hrankΓK : ∀ p, Module.rankAtStalk
      ((Fin n → Γ(Spec (CommRingCat.of S.K), ⊤)) ⧸ WΓ) p = q :=
    fun p ↦ xK.2.rankAtStalk_affine ⟨⊤, isAffineOpen_top _⟩ p
  obtain ⟨hprojK, hrankK⟩ :=
    quotient_projective_rank_of_mapPiRingEquiv eK WΓ hprojΓK hrankΓK
  have hq : Module.finrank S.K ((Fin n → S.K) ⧸ W) = q := by
    have h0 := hrankK ⟨⊥, Ideal.isPrime_bot⟩
    rwa [congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := S.K) (M := (Fin n → S.K) ⧸ W)) _] at h0
  -- the extension: contraction of `W` to `R^n`
  obtain ⟨hprojR, hrankR⟩ :=
    Submodule.quotient_projective_rankAtStalk_of_mem_iff hmem hq
  obtain ⟨hprojΓR, hrankΓR⟩ :=
    quotient_projective_rank_of_mapPiRingEquiv eR.symm N hprojR hrankR
  refine ⟨?_⟩
  set KR : (Spec (CommRingCat.of S.R)).SubmoduleSheafData n :=
    SubmoduleSheafData.ofAffineSubmodule NΓ with hKRdef
  have hKR : KR.QuotientProjectiveOfRank q :=
    SubmoduleSheafData.quotientProjectiveOfRank_ofAffineSubmodule NΓ hprojΓR hrankΓR
  set l : Spec (CommRingCat.of S.R) ⟶ P := h.homEquiv.symm ⟨KR, hKR⟩ with hl
  -- the lift restricts to the given `K`-point
  have hle : (⊤ : (Spec (CommRingCat.of S.K)).Opens) ≤
      (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S.R)).Opens) := by
    intro x _; trivial
  have hfacl : Spec.map φ ≫ l = S.i₁ := by
    apply h.homEquiv.injective
    rw [h.homEquiv_comp, hl, Equiv.apply_symm_apply, ← hxK]
    rw [grassmannianFunctor_map_apply]
    apply Subtype.ext
    change KR.comap (Spec.map φ) = xK.1
    rw [SubmoduleSheafData.eq_iff_submodule_top, ← hWΓ,
      KR.comap_submodule_eq_span (Spec.map φ)
        (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩) hle,
      hKRdef, SubmoduleSheafData.ofAffineSubmodule_submodule_top,
      span_specMap_appPi_image_eq_iff φ NΓ WΓ, hNΓback, hφdef]
    simp only [CommRingCat.hom_ofHom]
    exact Submodule.span_algebraMapPi_eq_of_mem_iff hmem
  -- uniqueness: any lift restricting to the `K`-point equals `l`
  have huniq : ∀ l' : Spec (CommRingCat.of S.R) ⟶ P, Spec.map φ ≫ l' = S.i₁ → l' = l := by
    intro l' hfac
    set Kl := h.homEquiv l' with hKl
    have hcomap : Kl.1.comap (Spec.map φ) = xK.1 := by
      have h1 : h.homEquiv (Spec.map φ ≫ l') = xK := by rw [hfac]
      rw [h.homEquiv_comp, ← hKl, grassmannianFunctor_map_apply] at h1
      exact congrArg Subtype.val h1
    set NlΓ := Kl.1.submodule ⟨⊤, isAffineOpen_top _⟩ with hNlΓ
    set Nl : Submodule S.R (Fin n → S.R) := NlΓ.mapPiRingEquiv eR with hNl
    -- the quotient by `Nl` is torsion free
    obtain ⟨hprojl, _⟩ := quotient_projective_rank_of_mapPiRingEquiv eR NlΓ
      (Kl.2.projective_affine ⟨⊤, isAffineOpen_top _⟩)
      (fun p ↦ Kl.2.rankAtStalk_affine ⟨⊤, isAffineOpen_top _⟩ p)
    have htf : Submodule.torsion S.R ((Fin n → S.R) ⧸ Nl) = ⊥ := by
      have _i1 := hprojl
      have _i2 : Module.Flat S.R ((Fin n → S.R) ⧸ Nl) := Module.Flat.of_projective
      exact Module.Flat.torsion_eq_bot
    -- `Nl` spans `W` over `K`
    have hspanl : Submodule.span S.K
        ((fun (v : Fin n → S.R) i ↦ algebraMap S.R S.K (v i)) ''
          (Nl : Set (Fin n → S.R))) = W := by
      have htop := (SubmoduleSheafData.eq_iff_submodule_top _ _).mp hcomap
      rw [Kl.1.comap_submodule_eq_span (Spec.map φ)
        (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩) hle] at htop
      rw [← hWΓ] at htop
      have hiff := (span_specMap_appPi_image_eq_iff φ NlΓ WΓ).mp htop
      rw [hφdef] at hiff
      simpa only [CommRingCat.hom_ofHom] using hiff
    -- conclude `Nl = N` by uniqueness of the saturated extension
    have hNlN : Nl = N := by
      ext v
      rw [Submodule.mem_iff_of_span_algebraMapPi_eq htf hspanl v, hmem v]
    -- transport back to the submodule datum and the morphism
    apply h.homEquiv.injective
    rw [hl, Equiv.apply_symm_apply, ← hKl]
    apply Subtype.ext
    change Kl.1 = KR
    rw [SubmoduleSheafData.eq_iff_submodule_top, hKRdef,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top, ← hNlΓ, hNΓ, ← hNlN, hNl,
      Submodule.mapPiRingEquiv_symm_mapPiRingEquiv]
  exact ⟨⟨⟨l, hfacl, specULiftZIsTerminal.hom_ext _ _⟩⟩,
    fun l' ↦ by
      apply CommSq.LiftStruct.ext
      exact huniq l'.l l'.fac_left⟩

/-- Finite-dimensional affine space is locally of finite type over its base. -/
lemma locallyOfFiniteType_affineSpace_over (m : Type u) [Finite m] (S : Scheme.{u}) :
    LocallyOfFiniteType (AffineSpace.over (n := m) (S := S)).hom := by
  have _i : LocallyOfFinitePresentation (AffineSpace.over (n := m) (S := S)).hom := by
    change LocallyOfFinitePresentation (𝔸(m; S) ↘ S)
    infer_instance
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- API lemma for Exercise 2.2.7 (finite type and
quasi-compactness): any scheme representing the Grassmannian functor is locally of
finite type over `Spec ℤ` and quasi-compact, because it is covered by the finitely
many standard charts, which are finite-dimensional affine spaces. -/
theorem locallyOfFiniteType_compactSpace_of_grassmannianFunctor_representableBy
    {q n : ℕ}
    {P : Scheme.{u}} (h : (grassmannianFunctor.{u} q n).RepresentableBy P) :
    LocallyOfFiniteType (specULiftZIsTerminal.from P) ∧ CompactSpace P := by
  let ι₀ := {I : Finset (Fin n) // I.card = q}
  let ι := ULift.{u} ι₀
  let A (I : ι) : Scheme.{u} :=
    AffineSpace (ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (⊤_ Scheme.{u})
  let repr (I : ι) : (grassmannianChart.{u} q n I.down.1).RepresentableBy (A I) :=
    Classical.choice
      (grassmannianChart_representableBy_affineSpace q n I.down.1 I.down.2)
  let eChart (I : ι) : yoneda.obj (A I) ≅ grassmannianChart.{u} q n I.down.1 :=
    (repr I).toIso
  let f (I : ι) : yoneda.obj (A I) ⟶ grassmannianFunctor.{u} q n :=
    (eChart I).hom ≫ grassmannianChartι q n I.down.1
  have hf (I : ι) :
      MorphismProperty.presheaf (@IsOpenImmersion : MorphismProperty Scheme.{u}) (f I) := by
    rw [show f I = (eChart I).hom ≫ grassmannianChartι q n I.down.1 from rfl,
      (MorphismProperty.presheaf
        (@IsOpenImmersion : MorphismProperty Scheme.{u})).cancel_left_of_respectsIso]
    exact presheaf_isOpenImmersion_grassmannianChartι q n I.down.1
  let mapCharts : (∐ fun I : ι ↦ yoneda.obj (A I)) ⟶
      ∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1 :=
    Limits.Sigma.map fun I ↦ (eChart I).hom
  have : IsIso mapCharts := inferInstance
  have hfac : mapCharts ≫
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) =
      Limits.Sigma.desc f := by
    ext I
    simp [mapCharts, f]
  let chartFamily (I : ι₀) := grassmannianChart.{u} q n I.1
  let chartMap (I : ι₀) := grassmannianChartι.{u} q n I.1
  let reindexCharts : (∐ fun I : ι ↦ grassmannianChart.{u} q n I.down.1) ≅
      ∐ chartFamily := Limits.Sigma.reindex Equiv.ulift chartFamily
  have hreindex : reindexCharts.hom ≫ Limits.Sigma.desc chartMap =
      Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1) := by
    refine Limits.Sigma.hom_ext _ _ fun I ↦ ?_
    rw [Limits.colimit.ι_desc]
    rw [← Category.assoc, show
      Limits.Sigma.ι (fun I : ι ↦ grassmannianChart.{u} q n I.down.1) I ≫
          reindexCharts.hom = Limits.Sigma.ι chartFamily I.down by
        exact Limits.Sigma.ι_reindex_hom (f := chartFamily) (Equiv.ulift) I]
    simp [chartMap]
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc chartMap) := isLocallySurjective_grassmannianChartι q n
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology reindexCharts.hom :=
    inferInstance
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (reindexCharts.hom ≫ Limits.Sigma.desc chartMap) := inferInstance
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    hreindex ▸ inferInstance
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology mapCharts := inferInstance
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (mapCharts ≫ Limits.Sigma.desc
        (fun I : ι ↦ grassmannianChartι.{u} q n I.down.1)) :=
    inferInstance
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) :=
    hfac ▸ inferInstance
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨grassmannianFunctor q n,
      (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_grassmannianFunctor q n)⟩
  let G := Scheme.LocalRepresentability.glueData (F := F) (f := f) hf
  have hG : LocallyOfFiniteType (specULiftZIsTerminal.from G.glued) := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) G.openCover]
    intro I
    rw [Scheme.LocalRepresentability.glueData_openCover_map]
    rw [show Scheme.LocalRepresentability.toGlued hf I ≫
        specULiftZIsTerminal.from G.glued =
      specULiftZIsTerminal.from (A I) by
        exact specULiftZIsTerminal.hom_ext _ _]
    have : LocallyOfFiniteType (AffineSpace.over
        (n := ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (S := ⊤_ Scheme.{u})).hom :=
      locallyOfFiniteType_affineSpace_over _ _
    have : IsIso (specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
      isIso_of_isTerminal terminalIsTerminal specULiftZIsTerminal _
    rw [show specULiftZIsTerminal.from (A I) =
      (AffineSpace.over
          (n := ULift.{u} (↑I.down.1 × ↑(I.down.1ᶜ))) (S := ⊤_ Scheme.{u})).hom ≫
        specULiftZIsTerminal.from (⊤_ Scheme.{u}) by
          exact specULiftZIsTerminal.hom_ext _ _]
    infer_instance
  let hGrep : (grassmannianFunctor.{u} q n).RepresentableBy G.glued :=
    Scheme.LocalRepresentability.representableBy (F := F) (f := f) hf
  let e : P ≅ G.glued := h.uniqueUpToIso hGrep
  have he : LocallyOfFiniteType (e.hom ≫ specULiftZIsTerminal.from G.glued) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) _ _).2 hG
  rw [show e.hom ≫ specULiftZIsTerminal.from G.glued =
    specULiftZIsTerminal.from P by exact specULiftZIsTerminal.hom_ext _ _] at he
  refine ⟨he, ?_⟩
  -- quasi-compactness: the glued scheme is covered by finitely many affine charts
  have : IsIso (specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal specULiftZIsTerminal _
  have : IsAffine (⊤_ Scheme.{u}) :=
    .of_isIso (specULiftZIsTerminal.from (⊤_ Scheme.{u}))
  have hcpt : ∀ I : ι, CompactSpace (G.openCover.X I) := by
    intro I
    change CompactSpace (A I)
    infer_instance
  have hglued : CompactSpace G.glued := by
    have := hcpt
    have : Finite G.openCover.I₀ := by
      change Finite ι
      infer_instance
    exact Scheme.OpenCover.compactSpace G.openCover
  exact Homeomorph.compactSpace (TopCat.homeoOfIso (asIso e.inv.base))

/-- **Exercise 2.2.7** (`exer:grassmannian-valuative-criterion`): the Grassmannian
`Gr(q, n) → Spec ℤ` is proper, stated for any scheme representing the Grassmannian
functor. Following the book's suggestion, the proof combines the valuative criterion
of properness (`valuativeCriterion_of_grassmannianFunctor_representableBy`) with
quasi-compactness, quasi-separatedness, and finite type of the structure morphism. -/
theorem isProper_of_grassmannianFunctor_representableBy {q n : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P) :
    IsProper (specULiftZIsTerminal.from P) := by
  obtain ⟨hlft, hcpt⟩ :=
    locallyOfFiniteType_compactSpace_of_grassmannianFunctor_representableBy h
  have := hlft
  have := hcpt
  -- the target is the spectrum of the noetherian ring `ULift ℤ`
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  -- hence the source is locally noetherian, quasi-separated, and noetherian
  have hln : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from P)
  have : IsNoetherian P := ⟨⟩
  have : QuasiCompact (specULiftZIsTerminal.from P) := inferInstance
  have : QuasiSeparated (specULiftZIsTerminal.from P) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)]
    infer_instance
  exact IsProper.of_valuativeCriterion _
    (valuativeCriterion_of_grassmannianFunctor_representableBy h)

end AlgebraicGeometry.Scheme

end ExerGrassmannianValuativeCriterion
