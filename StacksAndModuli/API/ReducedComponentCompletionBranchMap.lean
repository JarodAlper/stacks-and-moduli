module

public import StacksAndModuli.API.ReducedComponentCompletionBranch

/-!
# The actual completed-local map to a component branch

At a split node which is not a self-node of a reduced irreducible component, the
kernel of the completed-local map induced by the component inclusion is a minimal
prime.  This strengthens the target-only `CompletedLocalBranchTargetOver` interface by
retaining the specific geometric map.

The distinction matters for intersection theory: to compute a scheme-theoretic
pullback one must know the kernels of the two inclusion-induced maps, rather than only
the isomorphism types of their targets.

## Main result

* `AlgebraicGeometry.Scheme.IsSplitNodeAt.
  reducedComponent_completedLocalRingMap_ker_mem_minimalPrimes_of_not_selfNode`:
  the actual completed component map cuts out one formal branch.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace IsSplitNodeAt

/-- At a non-self split node of a reduced irreducible component, the kernel of the
actual inclusion-induced map on completed local rings is a minimal prime of the
ambient completed local ring. -/
theorem reducedComponent_completedLocalRingMap_ker_mem_minimalPrimes_of_not_selfNode
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    (Z : irreducibleComponents C)
    (z : C.reducedIrreducibleComponent Z)
    (h : C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z z))
    (hne : SplitNodePoints.incidentComponents
      (⟨C.reducedIrreducibleComponentι Z z, h⟩ : C.SplitNodePoints k) ≠ {Z}) :
    RingHom.ker
        ((C.reducedIrreducibleComponentι Z).completedLocalRingMap z
          ((C.reducedIrreducibleComponentι Z).stalkMap_surjective z)) ∈
      minimalPrimes
        (C.completedLocalRing (C.reducedIrreducibleComponentι Z z)) := by
  let i := C.reducedIrreducibleComponentι Z
  let x : C := i z
  let p : minimalPrimes (C.presheaf.stalk x) :=
    ⟨RingHom.ker (i.stalkMap z).hom,
      C.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes Z z⟩
  obtain ⟨b, hb⟩ := C.exists_formalBranch_toStalkBranch_eq x p
  let _ : _root_.IsReduced (C.presheaf.stalk x) :=
    IsSplitNodeAt.isReduced_stalk h
  let _ := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
  let e := Classical.choice h
  let _ : _root_.IsReduced (C.completedLocalRing x) :=
    isReduced_of_injective e e.injective
  have hpmap : p.1.map (C.toCompletedLocalRing x) = b.1 := by
    apply Ideal.map_eq_of_unique_minimalPrime_over_of_flat p.2 b.2
    · change b.1.comap (C.toCompletedLocalRing x) = p
      simpa only [p, i, FormalBranchesAt.toStalkBranch_val] using
        congrArg Subtype.val hb
    · intro Q hQ hQp
      let c : C.FormalBranchesAt x := ⟨Q, hQ⟩
      have hc : c = b := by
        let q : C.SplitNodePoints k := ⟨x, h⟩
        apply
          q.formalBranch_eq_of_component_eq_of_incidentComponents_ne_singleton
            Z b c
        · change C.stalkBranchComponent x b.toStalkBranch = Z
          rw [hb]
          exact C.reducedIrreducibleComponent_stalkBranchComponent_ker_eq Z z
        · change C.stalkBranchComponent x c.toStalkBranch = Z
          have hcp : c.toStalkBranch = p := by
            apply Subtype.ext
            change Q.comap (C.toCompletedLocalRing x) = p
            simpa only [toCompletedLocalRing] using hQp
          rw [hcp]
          exact C.reducedIrreducibleComponent_stalkBranchComponent_ker_eq Z z
        · exact hne
      exact congrArg Subtype.val hc
  let hi : Function.Surjective (i.stalkMap z) := i.stalkMap_surjective z
  change RingHom.ker (i.completedLocalRingMap z hi) ∈
    minimalPrimes (C.completedLocalRing x)
  rw [i.ker_completedLocalRingMap_eq z hi, hpmap]
  exact b.2

end IsSplitNodeAt

end AlgebraicGeometry.Scheme

end
