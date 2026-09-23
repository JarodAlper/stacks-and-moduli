module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace

/-!
# Finite closed subsets in dimension one

This file proves that a closed subset disjoint from a dense subset of a Noetherian
one-dimensional T₀ space is finite. The dense subset need not be open.

## Main result

* `Set.Finite.of_isClosed_disjoint_dense_of_topologicalKrullDim_le_one`: finiteness of the
  closed complement in dimension at most one.
* `Set.isClosed_singleton_of_mem_of_closed_disjoint_dense_of_dim_le_one`:
  every point of that complement is closed.
* `Set.finite_inter_closure_compl_of_isClosed_of_dim_le_one`: finiteness of the
  boundary of a closed subset.
-/

@[expose] public section

open Order TopologicalSpace

/-- Every point of a closed subset disjoint from a dense subset of a Noetherian
one-dimensional `T₀` space is closed. -/
theorem Set.isClosed_singleton_of_mem_of_closed_disjoint_dense_of_dim_le_one
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hUdense : Dense U) (hdisj : Disjoint Z U)
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hxZ : x ∈ Z) :
    IsClosed ({x} : Set X) := by
  let T : IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hTZ : (T : Set X) ⊆ Z :=
    closure_minimal (Set.singleton_subset_iff.mpr hxZ) hZ
  have hTmin_or_max : IsMin T ∨ IsMax T := by
    apply (Order.krullDim_le_one_iff.mp ?_) T
    exact hdim
  have hTnotmax : ¬ IsMax T := by
    intro hTmax
    have hTcomponent : (T : Set X) ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨T.isClosed, T.2⟩, ?_⟩
      intro B hB hTB
      exact hTmax (show T ≤ ⟨B, hB.2, hB.1⟩ from hTB)
    obtain ⟨o, hopen, hone, hoT⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
        (T : Set X) hTcomponent
    obtain ⟨y, hyo, hyU⟩ := hUdense.inter_open_nonempty o hopen hone
    exact Set.disjoint_left.1 hdisj (hTZ (hoT hyo)) hyU
  have hTmin : IsMin T := hTmin_or_max.resolve_right hTnotmax
  have hTsubsingleton : (T : Set X).Subsingleton := by
    apply minimal_nonempty_closed_subsingleton T.isClosed
    intro A hAT hAne hAclosed
    obtain ⟨y, hyA⟩ := hAne
    let Y : IrreducibleCloseds X :=
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hYT : Y ≤ T := by
      change closure {y} ⊆ (T : Set X)
      exact closure_minimal (Set.singleton_subset_iff.mpr (hAT hyA)) T.isClosed
    have hYT_eq : Y = T := hTmin.eq_of_le hYT
    have hclosure : closure {y} = (T : Set X) :=
      congrArg (fun V : IrreducibleCloseds X ↦ (V : Set X)) hYT_eq
    apply Set.Subset.antisymm hAT
    rw [← hclosure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyA) hAclosed
  have hclosure : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact Set.mem_singleton_iff.mpr
        (hTsubsingleton hy (subset_closure (Set.mem_singleton x)))
    · exact subset_closure
  rw [← hclosure]
  exact isClosed_closure

/-- In a Noetherian T₀ space of topological Krull dimension at most one, a closed
subset disjoint from a dense subset is finite. -/
theorem Set.Finite.of_isClosed_disjoint_dense_of_topologicalKrullDim_le_one
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hUdense : Dense U) (hdisj : Disjoint Z U)
    (hdim : topologicalKrullDim X ≤ 1) : Z.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hZU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZU]
  refine hSfinite.sUnion fun t htS ↦ ?_
  have htclosed : IsClosed t := hSclosed t htS
  have htirreducible : IsIrreducible t := hSirreducible t htS
  let T : IrreducibleCloseds X := ⟨t, htirreducible, htclosed⟩
  have htZ : t ⊆ Z := by
    intro x hx
    rw [hZU]
    exact Set.mem_sUnion_of_mem hx htS
  have hTmin_or_max : IsMin T ∨ IsMax T := by
    apply (Order.krullDim_le_one_iff.mp ?_) T
    exact hdim
  have hTnotmax : ¬ IsMax T := by
    intro hTmax
    have htcomponent : t ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨htclosed, htirreducible⟩, ?_⟩
      intro b hb htb
      let B : IrreducibleCloseds X := ⟨b, hb.2, hb.1⟩
      exact hTmax (show T ≤ B from htb)
    obtain ⟨o, hopen, hone, hot⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent t htcomponent
    obtain ⟨x, hxo, hxU⟩ := hUdense.inter_open_nonempty o hopen hone
    exact Set.disjoint_left.1 hdisj (htZ (hot hxo)) hxU
  have hTmin : IsMin T := hTmin_or_max.resolve_right hTnotmax
  have htsub : t.Subsingleton := by
    apply minimal_nonempty_closed_subsingleton htclosed
    intro a hat han hac
    obtain ⟨x, hxa⟩ := han
    let A : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAT : A ≤ T := by
      change closure {x} ⊆ t
      exact closure_minimal (Set.singleton_subset_iff.mpr (hat hxa)) htclosed
    have hATeq : A = T := hTmin.eq_of_le hAT
    have hclosure : closure {x} = t :=
      congrArg (fun V : IrreducibleCloseds X ↦ (V : Set X)) hATeq
    apply Set.Subset.antisymm hat
    rw [← hclosure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hxa) hac
  exact htsub.finite

/-- The boundary `Z ∩ closure Zᶜ` of a closed subset is finite in a Noetherian `T₀`
space of topological Krull dimension at most one. -/
theorem Set.finite_inter_closure_compl_of_isClosed_of_dim_le_one
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    {Z : Set X} (hZ : IsClosed Z) (hdim : topologicalKrullDim X ≤ 1) :
    (Z ∩ closure Zᶜ).Finite := by
  have hinterior : interior (Z ∩ closure Zᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzB : z ∈ Z ∩ closure Zᶜ := interior_subset hz
    obtain ⟨w, hwB, hwcompl⟩ :=
      mem_closure_iff.mp hzB.2 (interior (Z ∩ closure Zᶜ)) isOpen_interior hz
    exact hwcompl (interior_subset hwB).1
  exact Set.Finite.of_isClosed_disjoint_dense_of_topologicalKrullDim_le_one
    (hZ.inter isClosed_closure)
    (interior_eq_empty_iff_dense_compl.mp hinterior) disjoint_compl_right hdim
