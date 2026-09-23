module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Upper semicontinuity and local constancy are local properties

Both `UpperSemicontinuous` and `IsLocallyConstant` are conditions at each point, phrased
with the neighbourhood filter, so they can be checked on any open cover.  Mathlib states
the `…On`/`…WithinAt` variants but not the passage from an open subspace back to the
ambient space, which is what a proof "reduce to the affine case" needs: the statement is
verified on `V` viewed as a space in its own right, and must be concluded on `Y`.

* `upperSemicontinuousAt_of_subtype`, `upperSemicontinuous_of_forall_exists_isOpen`;
* `isLocallyConstant_of_forall_exists_isOpen`;
* `UpperSemicontinuous.isClosed_setOf_le` and `UpperSemicontinuous.isOpen_setOf_lt`, the
  superlevel and sublevel sets of an upper semicontinuous integer-valued function.

Composition with a continuous map — the other half of such a reduction, used to move a
statement along a homeomorphism such as `V ≃ₜ Spec Γ(Y, V)` — is already available as
`UpperSemicontinuous.comp` and `IsLocallyConstant.comp_continuous`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Filter Topology

universe u v

section Transport

variable {α : Type u} [TopologicalSpace α] {β : Type v}

/-- Upper semicontinuity at a point of an open set may be checked in the subspace. -/
theorem upperSemicontinuousAt_of_subtype [Preorder β] {g : α → β} {V : Set α}
    (hV : IsOpen V) {x : α} (hx : x ∈ V)
    (h : UpperSemicontinuousAt (fun v : V ↦ g v.1) ⟨x, hx⟩) :
    UpperSemicontinuousAt g x := by
  intro y hy
  have h1 : ∀ᶠ v in nhds (⟨x, hx⟩ : V), g v.1 < y := h y hy
  have h2 : ∀ᶠ z in Filter.map (Subtype.val : V → α) (nhds (⟨x, hx⟩ : V)), g z < y :=
    Filter.eventually_map.mpr h1
  rwa [hV.isOpenEmbedding_subtypeVal.map_nhds_eq] at h2

/-- **Upper semicontinuity is local.**  If every point has an open neighbourhood on which
the function is upper semicontinuous as a function on that subspace, then it is upper
semicontinuous. -/
theorem upperSemicontinuous_of_forall_exists_isOpen [Preorder β] {g : α → β}
    (h : ∀ x : α, ∃ (V : Set α) (_ : IsOpen V) (_ : x ∈ V),
      UpperSemicontinuous (fun v : V ↦ g v.1)) :
    UpperSemicontinuous g := by
  intro x
  obtain ⟨V, hV, hx, hg⟩ := h x
  exact upperSemicontinuousAt_of_subtype hV hx (hg ⟨x, hx⟩)

/-- **Local constancy is local.**  If every point has an open neighbourhood on which the
function is locally constant as a function on that subspace, then it is locally
constant. -/
theorem isLocallyConstant_of_forall_exists_isOpen {g : α → β}
    (h : ∀ x : α, ∃ (V : Set α) (_ : IsOpen V) (_ : x ∈ V),
      IsLocallyConstant (fun v : V ↦ g v.1)) :
    IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨V, hV, hx, hg⟩ := h x
  have h1 : ∀ᶠ v in nhds (⟨x, hx⟩ : V), g v.1 = g x := hg.eventually_eq ⟨x, hx⟩
  have h2 : ∀ᶠ z in Filter.map (Subtype.val : V → α) (nhds (⟨x, hx⟩ : V)), g z = g x :=
    Filter.eventually_map.mpr h1
  rwa [hV.isOpenEmbedding_subtypeVal.map_nhds_eq] at h2

/-- **The superlevel sets of an upper semicontinuous integer-valued function are closed.**
This is the form in which upper semicontinuity is applied: a condition `g ≥ c` cuts out a
closed subset. -/
theorem UpperSemicontinuous.isClosed_setOf_le {g : α → ℤ} (hg : UpperSemicontinuous g)
    (c : ℤ) : IsClosed {x : α | c ≤ g x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
  filter_upwards [hg x c hx] with z hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  exact hz

/-- **The sublevel sets of an upper semicontinuous integer-valued function are open.**
Together with `UpperSemicontinuous.isClosed_setOf_le` this is the pair of statements in which
upper semicontinuity is applied: `g ≥ c` is closed and `g ≤ c` is open. -/
theorem UpperSemicontinuous.isOpen_setOf_lt {g : α → ℤ} (hg : UpperSemicontinuous g) (c : ℤ) :
    IsOpen {x : α | g x < c} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  exact hg x c hx

end Transport
