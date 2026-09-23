module

public import StacksAndModuli.API.SmoothPointComponents

/-!
# Affine neighbourhoods inside one irreducible component

When a scheme has finitely many irreducible components, deleting every component other
than a selected component leaves an open subset contained in that component. A point that
belongs to no other component lies in this open and therefore admits an affine
neighbourhood contained in the selected component.

## Main definitions and results

* `AlgebraicGeometry.Scheme.exclusiveComponentOpen`: the complement of all components
  other than a selected one.
* `AlgebraicGeometry.Scheme.exists_affineOpen_mem_le_component_of_unique`: a point on a
  unique component has an affine neighbourhood inside that component.
* `AlgebraicGeometry.Scheme.exists_affineOpen_mem_le_componentAtOfIsDomainStalk`: the
  specialization to a point whose local ring is a domain.
* `AlgebraicGeometry.Scheme.exists_affineOpen_mem_le_smoothPointComponent`: the
  specialization to a formally smooth point over a field.
* `AlgebraicGeometry.Scheme.exists_affineOpen_mem_le_smoothPointComponent_inter_smoothLocus`:
  the affine neighbourhood may simultaneously be chosen inside the smooth locus.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The open subset of a component left after deleting every other irreducible
component. -/
noncomputable def exclusiveComponentOpen (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact (Set.toFinite (irreducibleComponents X)).sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩

/-- The component-exclusive open is contained in its selected component. -/
theorem exclusiveComponentOpen_le (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    (X.exclusiveComponentOpen Z : Set X) ⊆ Z.1 := by
  exact subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton
    (Set.toFinite (irreducibleComponents X)) Z.1 Z.2).le

/-- A point belonging to no other irreducible component lies in the
component-exclusive open. -/
theorem mem_exclusiveComponentOpen_of_unique (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) (x : X)
    (hunique : ∀ W : irreducibleComponents X, x ∈ W.1 → W = Z) :
    x ∈ X.exclusiveComponentOpen Z := by
  change x ∉ ⋃₀ (irreducibleComponents X \ {Z.1})
  intro hx
  obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp hx
  have hWirr : W ∈ irreducibleComponents X := hW.1
  let W' : irreducibleComponents X := ⟨W, hWirr⟩
  have hWZ : W' = Z := hunique W' hxW
  exact hW.2 (by
    simpa only [Set.mem_singleton_iff] using congrArg Subtype.val hWZ)

/-- A point lying on a unique irreducible component has an affine open
neighbourhood contained in that component. -/
theorem exists_affineOpen_mem_le_component_of_unique (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) (x : X)
    (hunique : ∀ W : irreducibleComponents X, x ∈ W.1 → W = Z) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ (U : Set X) ⊆ Z.1 := by
  have hx : x ∈ X.exclusiveComponentOpen Z :=
    X.mem_exclusiveComponentOpen_of_unique Z x hunique
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx
      (X.exclusiveComponentOpen Z).2
  exact ⟨U, hU, hxU, hUsub.trans (X.exclusiveComponentOpen_le Z)⟩

/-- A point with a domain stalk has an affine neighbourhood contained in its
canonical irreducible component. -/
theorem exists_affineOpen_mem_le_componentAtOfIsDomainStalk
    (X : Scheme.{u}) [Finite (irreducibleComponents X)] (x : X)
    [IsDomain (X.presheaf.stalk x)] :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (U : Set X) ⊆ (X.componentAtOfIsDomainStalk x).1 := by
  apply X.exists_affineOpen_mem_le_component_of_unique
  intro W hxW
  exact X.eq_of_mem_irreducibleComponents_of_isDomain_stalk x W
    (X.componentAtOfIsDomainStalk x) hxW
    (X.mem_componentAtOfIsDomainStalk x)

/-- A formally smooth point over a field has an affine neighbourhood contained in its
unique irreducible component. -/
theorem exists_affineOpen_mem_le_smoothPointComponent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    [Finite (irreducibleComponents X)] (x : X)
    (hx : (f.stalkMap x).hom.FormallySmooth) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (U : Set X) ⊆ (X.smoothPointComponent f x hx).1 := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field f x hx
  let _ : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain
  exact X.exists_affineOpen_mem_le_componentAtOfIsDomainStalk x

/-- A formally smooth point over a field has an affine neighbourhood contained both in
its unique irreducible component and in the smooth locus of the structure morphism. -/
theorem exists_affineOpen_mem_le_smoothPointComponent_inter_smoothLocus
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    [Finite (irreducibleComponents X)] (x : X)
    (hx : (f.stalkMap x).hom.FormallySmooth) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      (U : Set X) ⊆
        (X.smoothPointComponent f x hx).1 ∩ (f.smoothLocus : Set X) := by
  obtain ⟨U, hU, hxU, hU_component⟩ :=
    X.exists_affineOpen_mem_le_smoothPointComponent f x hx
  have hx_smooth : x ∈ f.smoothLocus := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hV_subset⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (⟨hxU, hx_smooth⟩ : x ∈ U ⊓ f.smoothLocus)
      (U ⊓ f.smoothLocus).2
  refine ⟨V, hV, hxV, ?_⟩
  intro y hy
  exact ⟨hU_component (hV_subset hy).1, (hV_subset hy).2⟩

end AlgebraicGeometry.Scheme
