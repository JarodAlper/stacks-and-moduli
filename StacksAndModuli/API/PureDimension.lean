module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension

/-!
# Pure-dimensional topological spaces and schemes

This file defines a topological space to be pure of dimension `d` when every
irreducible component has topological Krull dimension `d`.  It also supplies
transport across homeomorphisms and, for schemes, across isomorphisms.

## Main definitions and results

* `TopologicalSpace.IsPureOfDimension`: componentwise pure dimension.
* `TopologicalSpace.isPureOfDimension_of_irreducibleSpace`: irreducible spaces are pure.
* `TopologicalSpace.IsPureOfDimension.homeomorph`: homeomorphism invariance.
* `AlgebraicGeometry.Scheme.IsPureOfDimension.iso`: scheme-isomorphism invariance.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Set

universe u v

namespace TopologicalSpace

/-- A topological space is pure of dimension `d` if each of its irreducible
components has topological Krull dimension `d`. -/
def IsPureOfDimension (X : Type u) [TopologicalSpace X]
    (d : WithBot ℕ∞) : Prop :=
  ∀ Z : irreducibleComponents X, topologicalKrullDim Z.1 = d

/-- The set-indexed formulation of pure dimension. -/
theorem isPureOfDimension_iff {X : Type u} [TopologicalSpace X]
    {d : WithBot ℕ∞} :
    IsPureOfDimension X d ↔
      ∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = d := by
  constructor
  · intro h Z hZ
    exact h ⟨Z, hZ⟩
  · intro h Z
    exact h Z.1 Z.2

/-- Every irreducible component of a pure-dimensional space has the prescribed
topological Krull dimension. -/
theorem IsPureOfDimension.component {X : Type u} [TopologicalSpace X]
    {d : WithBot ℕ∞} (h : IsPureOfDimension X d) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim Z = d :=
  h ⟨Z, hZ⟩

/-- A componentwise dimension calculation proves pure dimension. -/
theorem isPureOfDimension_of_components {X : Type u} [TopologicalSpace X]
    {d : WithBot ℕ∞}
    (h : ∀ Z : Set X, Z ∈ irreducibleComponents X →
      topologicalKrullDim Z = d) :
    IsPureOfDimension X d :=
  isPureOfDimension_iff.mpr h

/-- An irreducible topological space is pure of its topological Krull dimension. -/
theorem isPureOfDimension_of_irreducibleSpace
    (X : Type u) [TopologicalSpace X] [IrreducibleSpace X] :
    IsPureOfDimension X (topologicalKrullDim X) := by
  intro Z
  have hZ : Z.1 = (Set.univ : Set X) := by
    have hmem : Z.1 ∈ ({Set.univ} : Set (Set X)) := by
      rw [← irreducibleComponents_eq_singleton]
      exact Z.2
    simpa only [Set.mem_singleton_iff] using hmem
  rw [hZ]
  exact IsHomeomorph.topologicalKrullDim_eq
    (Homeomorph.Set.univ X) (Homeomorph.Set.univ X).isHomeomorph

/-- Pure dimension is preserved by a homeomorphism. -/
theorem IsPureOfDimension.homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {d : WithBot ℕ∞}
    (hX : IsPureOfDimension X d) (e : X ≃ₜ Y) :
    IsPureOfDimension Y d := by
  intro Z
  have hnonempty : (Z.1 ∩ Set.range e).Nonempty := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨z, hz, e.surjective z⟩
  have hpre : e ⁻¹' Z.1 ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents Z.2 e.isOpenEmbedding hnonempty
  let eZ : (e ⁻¹' Z.1) ≃ₜ Z.1 :=
    e.isEmbedding.homeomorphOfSubsetRange (fun z _ ↦ e.surjective z)
  have hdim : topologicalKrullDim (e ⁻¹' Z.1) =
      topologicalKrullDim Z.1 :=
    IsHomeomorph.topologicalKrullDim_eq eZ eZ.isHomeomorph
  exact hdim.symm.trans (hX ⟨e ⁻¹' Z.1, hpre⟩)

/-- Two homeomorphic spaces are pure of the same dimension. -/
theorem isPureOfDimension_homeomorph_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {d : WithBot ℕ∞}
    (e : X ≃ₜ Y) :
    IsPureOfDimension X d ↔ IsPureOfDimension Y d :=
  ⟨fun h ↦ h.homeomorph e, fun h ↦ h.homeomorph e.symm⟩

end TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A scheme is pure of dimension `d` when its underlying topological space is. -/
abbrev IsPureOfDimension (X : Scheme.{u}) (d : WithBot ℕ∞) : Prop :=
  TopologicalSpace.IsPureOfDimension X d

/-- Pure dimension of schemes is preserved by an isomorphism. -/
theorem IsPureOfDimension.iso {X Y : Scheme.{u}}
    {d : WithBot ℕ∞} (hX : X.IsPureOfDimension d) (e : X ≅ Y) :
    Y.IsPureOfDimension d :=
  TopologicalSpace.IsPureOfDimension.homeomorph hX e.hom.homeomorph

/-- Isomorphic schemes are pure of the same dimension. -/
theorem isPureOfDimension_iso_iff {X Y : Scheme.{u}}
    {d : WithBot ℕ∞} (e : X ≅ Y) :
    X.IsPureOfDimension d ↔ Y.IsPureOfDimension d :=
  TopologicalSpace.isPureOfDimension_homeomorph_iff e.hom.homeomorph

end AlgebraicGeometry.Scheme
