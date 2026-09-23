module

public import StacksAndModuli.API.CompletedLocalRingMap
public import StacksAndModuli.API.ComponentStalkKernel
public import StacksAndModuli.API.FlatMinimalPrimeExtension
public import StacksAndModuli.API.SplitNodeComponentCompletion
public import StacksAndModuli.API.SplitNodeIncidenceGraph

/-!
# Completed local branches of reduced irreducible components

This file proves that the completed local ring of a reduced irreducible
component at a split node is the corresponding formal-branch quotient, provided
the node is not a self-node of that component.

The key algebraic point avoids an excellence argument.  The kernel of the
component stalk map is a minimal prime of the ambient Noetherian local ring.  At
a non-self-node it has a unique minimal prime above it in the reduced completed
local ring.  Flatness of completion then identifies the extension of the stalk
prime with that completed minimal prime.  Exactness of completion identifies
this extension with the kernel of the map to the completed component stalk.

## Main results

* `AlgebraicGeometry.Scheme.exists_formalBranch_toStalkBranch_eq`: every stalk
  branch of a Noetherian local ring lifts to a formal branch.
* `AlgebraicGeometry.Scheme.reducedIrreducibleComponent_stalkBranchComponent_ker_eq`:
  the component attached to the component-stalk kernel is the original
  irreducible component.
* `IsSplitNodeAt.reducedComponent_completedLocalBranchTarget_of_not_selfNode`:
  a reduced component at a non-self split node is a completed formal-branch
  target.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every minimal prime of a Noetherian stalk is the contraction of a minimal
prime of its completed local ring. -/
theorem exists_formalBranch_toStalkBranch_eq
    (X : Scheme.{u}) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (p : minimalPrimes (X.presheaf.stalk x)) :
    ∃ b : X.FormalBranchesAt x, b.toStalkBranch = p := by
  have hinj : Function.Injective (X.toCompletedLocalRing x) := by
    intro a b hab
    apply AdicCompletion.of_injective
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)
    simpa only [X.toCompletedLocalRing_apply] using hab
  have hpmin : p.1 ∈
      ((⊥ : Ideal (X.completedLocalRing x)).comap
        (X.toCompletedLocalRing x)).minimalPrimes := by
    rw [Ideal.comap_bot_of_injective (X.toCompletedLocalRing x) hinj]
    exact p.2
  obtain ⟨Q, hQ, hQp⟩ :=
    Ideal.exists_minimalPrimes_comap_eq
      (X.toCompletedLocalRing x) p.1 hpmin
  refine ⟨⟨Q, hQ⟩, Subtype.ext ?_⟩
  exact hQp

/-- At a split node which is not a self-node of `Z`, at most one formal branch
is assigned to `Z`. -/
theorem SplitNodePoints.formalBranch_eq_of_component_eq_of_incidentComponents_ne_singleton
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (Z : irreducibleComponents X)
    (b c : X.FormalBranchesAt q.1)
    (hb : q.componentOfBranch b = Z)
    (hc : q.componentOfBranch c = Z)
    (hne : q.incidentComponents ≠ {Z}) :
    c = b := by
  by_contra hcb
  obtain ⟨e⟩ := q.2.nonempty_formalBranchesEquivFinTwo
  have hall : ∀ d : X.FormalBranchesAt q.1,
      q.componentOfBranch d = Z := by
    intro d
    have hed : e d = e b ∨ e d = e c := by
      have heb : e b ≠ e c := fun h ↦ hcb (e.injective h).symm
      omega
    rcases hed with hed | hed
    · rw [e.injective hed]
      exact hb
    · rw [e.injective hed]
      exact hc
  apply hne
  ext V
  rw [q.mem_incidentComponents_iff]
  constructor
  · rintro ⟨d, rfl⟩
    simp only [hall d, Set.mem_singleton_iff]
  · intro hV
    rw [Set.mem_singleton_iff] at hV
    subst V
    exact ⟨b, hb⟩

/-- The stalk branch cut out by the reduced-component inclusion is assigned
back to that irreducible component. -/
theorem reducedIrreducibleComponent_stalkBranchComponent_ker_eq
    (C : Scheme.{u}) (Z : irreducibleComponents C)
    (z : C.reducedIrreducibleComponent Z) :
    C.stalkBranchComponent (C.reducedIrreducibleComponentι Z z)
      ⟨RingHom.ker
          ((C.reducedIrreducibleComponentι Z).stalkMap z).hom,
        C.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes Z z⟩ =
      Z := by
  let Y := C.reducedIrreducibleComponent Z
  let i := C.reducedIrreducibleComponentι Z
  let p : Ideal (C.presheaf.stalk (i z)) :=
    RingHom.ker (i.stalkMap z).hom
  let q : minimalPrimes (C.presheaf.stalk (i z)) :=
    ⟨p, C.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes Z z⟩
  let ξ : Spec (Y.presheaf.stalk z) :=
    genericPoint (Spec (Y.presheaf.stalk z))
  let pPoint : Spec (C.presheaf.stalk (i z)) :=
    Spec.map (i.stalkMap z) ξ
  have hpPoint_asIdeal : pPoint.asIdeal = p := by
    change Ideal.comap (i.stalkMap z).hom
      (genericPoint (Spec (Y.presheaf.stalk z))).asIdeal = _
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have hpoints : C.stalkBranchPoint (i z) q = pPoint := by
    apply PrimeSpectrum.ext
    change q.1 = pPoint.asIdeal
    exact hpPoint_asIdeal.symm
  apply Subtype.ext
  change (C.stalkBranchComponent (i z) q).1 = Z.1
  rw [C.stalkBranchComponent_val, hpoints]
  change closure
    ({C.fromSpecStalk (i z) (Spec.map (i.stalkMap z) ξ)} : Set C) = Z.1
  rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]
  change closure ({i (Y.fromSpecStalk z ξ)} : Set C) = Z.1
  rw [show Y.fromSpecStalk z ξ = genericPoint Y from
    fromSpecStalk_genericPoint_of_isIntegral Y z]
  rw [i.map_genericPoint_eq_of_closure_range_eq_irreducibleComponent Z (by
    rw [C.range_reducedIrreducibleComponentι Z]
    exact
      (isClosed_of_mem_irreducibleComponents Z.1 Z.property).closure_eq)]
  exact Z.property.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z.1 Z.property) |>.def

/-- If exactly one formal branch contracts to the component-stalk kernel, then
the completed local ring of the reduced component is the corresponding
completed formal-branch target. -/
theorem IsSplitNodeAt.reducedComponent_completedLocalBranchTarget_of_uniqueBranch
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    (Z : irreducibleComponents C)
    (z : C.reducedIrreducibleComponent Z)
    (h : C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z z))
    (b : C.FormalBranchesAt (C.reducedIrreducibleComponentι Z z))
    (hb : (b.toStalkBranch : Ideal
      (C.presheaf.stalk (C.reducedIrreducibleComponentι Z z))) =
        RingHom.ker
          ((C.reducedIrreducibleComponentι Z).stalkMap z).hom)
    (hunique : ∀ q : C.FormalBranchesAt
      (C.reducedIrreducibleComponentι Z z),
        (q.toStalkBranch : Ideal
          (C.presheaf.stalk (C.reducedIrreducibleComponentι Z z))) =
            RingHom.ker
              ((C.reducedIrreducibleComponentι Z).stalkMap z).hom →
          q = b) :
    CompletedLocalBranchTargetOver k
      (C.reducedIrreducibleComponentι Z z) z := by
  let i := C.reducedIrreducibleComponentι Z
  let p : Ideal (C.presheaf.stalk (i z)) :=
    RingHom.ker (i.stalkMap z).hom
  have hi : Function.Surjective (i.stalkMap z) :=
    i.stalkMap_surjective z
  let _ : _root_.IsReduced (C.presheaf.stalk (i z)) :=
    IsSplitNodeAt.isReduced_stalk h
  let _ := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) (i z)
  obtain ⟨e⟩ := h
  let _ : _root_.IsReduced (C.completedLocalRing (i z)) :=
    isReduced_of_injective e e.injective
  have hp : p ∈ minimalPrimes (C.presheaf.stalk (i z)) :=
    C.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes Z z
  have hpmap : p.map (C.toCompletedLocalRing (i z)) = b.1 := by
    apply Ideal.map_eq_of_unique_minimalPrime_over_of_flat hp b.2
    · change b.1.comap (C.toCompletedLocalRing (i z)) = p
      simpa only [p, i, FormalBranchesAt.toStalkBranch_val] using hb
    · intro Q hQ hQp
      let q : C.FormalBranchesAt (i z) := ⟨Q, hQ⟩
      have hq : q = b := hunique q (by
        change Q.comap (C.toCompletedLocalRing (i z)) = p
        simpa only [p, i, toCompletedLocalRing] using hQp)
      exact congrArg Subtype.val hq
  let _ := completedLocalRingAlgebra
    (C ↘ Spec (CommRingCat.of k)) (i z)
  let _ := completedLocalRingAlgebra
    (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k)) z
  let f := i.completedLocalRingMapAlgHom
    (C ↘ Spec (CommRingCat.of k)) z hi
  refine ⟨f, ?_, ?_⟩
  · exact i.completedLocalRingMap_surjective z hi
  · change RingHom.ker (i.completedLocalRingMap z hi) ∈
      minimalPrimes (C.completedLocalRing (i z))
    rw [i.ker_completedLocalRingMap_eq z hi, hpmap]
    exact b.2

/-- At a split node which is not a self-node of `Z`, the completed local ring
of the reduced component `Z` is a completed formal-branch target. -/
theorem IsSplitNodeAt.reducedComponent_completedLocalBranchTarget_of_not_selfNode
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    (Z : irreducibleComponents C)
    (z : C.reducedIrreducibleComponent Z)
    (h : C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z z))
    (hne : SplitNodePoints.incidentComponents
      (⟨C.reducedIrreducibleComponentι Z z, h⟩ :
        C.SplitNodePoints k) ≠ {Z}) :
    CompletedLocalBranchTargetOver k
      (C.reducedIrreducibleComponentι Z z) z := by
  let i := C.reducedIrreducibleComponentι Z
  let x : C := i z
  let p : minimalPrimes (C.presheaf.stalk x) :=
    ⟨RingHom.ker (i.stalkMap z).hom,
      C.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes Z z⟩
  obtain ⟨b, hb⟩ := C.exists_formalBranch_toStalkBranch_eq x p
  apply h.reducedComponent_completedLocalBranchTarget_of_uniqueBranch Z z b
  · exact congrArg Subtype.val hb
  · intro c hc
    let q : C.SplitNodePoints k := ⟨x, h⟩
    apply
      q.formalBranch_eq_of_component_eq_of_incidentComponents_ne_singleton
        Z b c
    · change C.formalBranchComponent x b = Z
      change C.stalkBranchComponent x b.toStalkBranch = Z
      rw [hb]
      exact C.reducedIrreducibleComponent_stalkBranchComponent_ker_eq Z z
    · change C.formalBranchComponent x c = Z
      change C.stalkBranchComponent x c.toStalkBranch = Z
      have hcp : c.toStalkBranch = p := Subtype.ext hc
      rw [hcp]
      exact C.reducedIrreducibleComponent_stalkBranchComponent_ker_eq Z z
    · exact hne

end AlgebraicGeometry.Scheme

end

end
