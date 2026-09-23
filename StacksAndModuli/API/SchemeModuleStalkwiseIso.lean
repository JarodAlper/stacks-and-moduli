module

public import StacksAndModuli.API.SchemeModuleStalkSupport

/-!
# Detecting isomorphisms of scheme modules on stalks

A morphism of sheaves of modules on a scheme is an isomorphism if and only if its
underlying morphism of additive-group stalks is an isomorphism at every point.  If both
modules are supported in a prescribed subset, it is enough to check the points of that
subset: away from it both stalks are zero.

The statements require a single global module morphism.  A bare family of unrelated
stalk isomorphisms does not in general glue to a morphism of sheaves, so it cannot be used
as a replacement for that datum.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_iff_stalkFunctor_map_iso`: a module morphism is
  an isomorphism exactly when all its additive-group stalk maps are isomorphisms.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_stalkFunctor_map_iso_on_support`: if source
  and target are supported in `S`, it is enough to check stalks at points of `S`.
* `AlgebraicGeometry.Scheme.Modules.isoOfHomOfStalkwiseIsIso`: package a global morphism
  with stalkwise-isomorphism proofs as an isomorphism of modules.
* `AlgebraicGeometry.Scheme.Modules.isZero_iff_stalkSupport_eq_empty`: a scheme module is
  zero exactly when its stalk support is empty.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of scheme modules is an isomorphism if and only if its underlying
additive-group map is an isomorphism on every stalk. -/
theorem isIso_iff_stalkFunctor_map_iso (f : M ⟶ N) :
    IsIso f ↔
      ∀ x : X, IsIso
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
  constructor
  · intro hf x
    let _ : IsIso f := hf
    infer_instance
  · intro hf
    have hsheaf : IsIso
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) := by
      let _ : ∀ x : X, IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f).1) := hf
      exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f)
    let _ : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) :=
      hsheaf
    let _ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
      inferInstance
    exact isIso_of_reflects_iso f
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

/-- If the source and target of a module morphism are supported in `S`, then isomorphism
on stalks at the points of `S` implies that the morphism is an isomorphism globally. -/
theorem isIso_of_stalkFunctor_map_iso_on_support
    (f : M ⟶ N) (S : Set X)
    (hM : stalkSupport M ⊆ S) (hN : stalkSupport N ⊆ S)
    (hf : ∀ x ∈ S, IsIso
      ((toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    IsIso f := by
  rw [isIso_iff_stalkFunctor_map_iso]
  intro x
  by_cases hx : x ∈ S
  · exact hf x hx
  · have hxM : x ∉ stalkSupport M := fun hx' ↦ hx (hM hx')
    have hxN : x ∉ stalkSupport N := fun hx' ↦ hx (hN hx')
    have hMzero : IsZero
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M) := by
      simpa only [stalkSupport, Set.mem_ofPred_eq, not_not] using hxM
    have hNzero : IsZero
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj N) := by
      simpa only [stalkSupport, Set.mem_ofPred_eq, not_not] using hxN
    exact hMzero.isIso hNzero _

/-- It is enough to check a module morphism at points where either its source or target
has a nonzero stalk. -/
theorem isIso_of_stalkFunctor_map_iso_on_stalkSupport_union
    (f : M ⟶ N)
    (hf : ∀ x ∈ stalkSupport M ∪ stalkSupport N, IsIso
      ((toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    IsIso f :=
  isIso_of_stalkFunctor_map_iso_on_support f
    (stalkSupport M ∪ stalkSupport N) Set.subset_union_left
    Set.subset_union_right hf

/-- A scheme module is a zero object if and only if all its additive-group stalks are
zero, equivalently if its stalk support is empty. -/
theorem isZero_iff_stalkSupport_eq_empty (M : X.Modules) :
    IsZero M ↔ stalkSupport M = ∅ := by
  constructor
  · intro hzero
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (Functor.map_isZero
      (toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hzero)
  · intro hsupp
    let f : M ⟶ 0 := (isZero_zero X.Modules).from_ M
    have hf : IsIso f := by
      rw [isIso_iff_stalkFunctor_map_iso]
      intro x
      have hx : x ∉ stalkSupport M := by
        rw [hsupp]
        exact Set.notMem_empty x
      have hMzero : IsZero
          ((toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M) := by
        simpa only [stalkSupport, Set.mem_ofPred_eq, not_not] using hx
      exact hMzero.isIso
        (Functor.map_isZero
          (toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
          (isZero_zero X.Modules)) _
    let _ : IsIso f := hf
    exact (isZero_zero X.Modules).of_iso (asIso f)

/-- Package a global module morphism whose maps on all additive-group stalks are
isomorphisms as an isomorphism of scheme modules. -/
noncomputable def isoOfHomOfStalkwiseIsIso
    (f : M ⟶ N)
    (hf : ∀ x : X, IsIso
      ((toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    M ≅ N := by
  let _ : IsIso f := (isIso_iff_stalkFunctor_map_iso f).mpr hf
  exact asIso f

/-- Package a global module morphism supported in `S` whose stalk maps are isomorphisms
at the points of `S` as an isomorphism of scheme modules. -/
noncomputable def isoOfHomOfStalkwiseIsIsoOnSupport
    (f : M ⟶ N) (S : Set X)
    (hM : stalkSupport M ⊆ S) (hN : stalkSupport N ⊆ S)
    (hf : ∀ x ∈ S, IsIso
      ((toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    M ≅ N := by
  let _ : IsIso f :=
    isIso_of_stalkFunctor_map_iso_on_support f S hM hN hf
  exact asIso f

end AlgebraicGeometry.Scheme.Modules

end
