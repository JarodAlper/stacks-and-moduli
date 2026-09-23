module

public import StacksAndModuli.API.NodeRingBranchQuotient

/-!
# Surjective targets of the standard node ring

A surjective algebra map out of the standard node ring whose kernel is a minimal prime
has target the one-variable power-series ring.  The result is also transported across an
arbitrary algebra equivalence with the node ring.

This packages the final commutative-algebra step in a component-through-a-node
calculation.  Its hypotheses isolate the remaining geometry: constructing the completed
component map and proving that its kernel is one formal branch.

## Main results

* `AlgebraicGeometry.Scheme.nodeRing_minimalPrime_eq_formalBranch`: every minimal prime
  of the standard node is one of its two intrinsic formal branches.
* `AlgebraicGeometry.Scheme.nonempty_nodeRingSurjectiveTargetAlgEquivPowerSeries`: a
  surjective minimal-prime quotient of the standard node is `k[[t]]`.
* `AlgebraicGeometry.Scheme.
    nonempty_nodeSurjectiveTargetAlgEquivPowerSeries_of_algEquiv`: the transported form
  for any algebra identified with the standard node.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped PowerSeries

universe u

namespace AlgebraicGeometry.Scheme

/-- Every minimal prime of the standard node ring is one of its two intrinsic formal
branches. -/
lemma nodeRing_minimalPrime_eq_formalBranch
    (k : Type u) [Field k] (p : Ideal (nodeRing k))
    (hp : p ∈ minimalPrimes (nodeRing k)) :
    p = (nodeRingFormalBranch k 0 : Ideal (nodeRing k)) ∨
      p = (nodeRingFormalBranch k 1 : Ideal (nodeRing k)) := by
  let q : minimalPrimes (nodeRing k) := ⟨p, hp⟩
  let E := Ideal.minimalPrimesQuotientEquiv (nodeIdeal k)
  rcases (mem_nodeIdeal_minimalPrimes_iff k (E q).1).mp (E q).2 with h | h
  · right
    apply Ideal.comap_injective_of_surjective
      (Ideal.Quotient.mk (nodeIdeal k)) Ideal.Quotient.mk_surjective
    change p.comap (Ideal.Quotient.mk (nodeIdeal k)) = _
    change p.comap (Ideal.Quotient.mk (nodeIdeal k)) = nodeAxisIdeal k 0 at h
    have hb :
        (nodeRingFormalBranch k 1 : Ideal (nodeRing k)).comap
            (Ideal.Quotient.mk (nodeIdeal k)) = nodeAxisIdeal k 0 := by
      change (E (E.symm
        ⟨nodeAxisIdeal k 0, nodeAxisIdeal_mem_minimalPrimes k 0⟩) :
          Ideal (MvPowerSeries (Fin 2) k)) = nodeAxisIdeal k 0
      exact congrArg Subtype.val
        (E.apply_symm_apply
          ⟨nodeAxisIdeal k 0, nodeAxisIdeal_mem_minimalPrimes k 0⟩)
    exact h.trans hb.symm
  · left
    apply Ideal.comap_injective_of_surjective
      (Ideal.Quotient.mk (nodeIdeal k)) Ideal.Quotient.mk_surjective
    change p.comap (Ideal.Quotient.mk (nodeIdeal k)) = _
    change p.comap (Ideal.Quotient.mk (nodeIdeal k)) = nodeAxisIdeal k 1 at h
    have hb :
        (nodeRingFormalBranch k 0 : Ideal (nodeRing k)).comap
            (Ideal.Quotient.mk (nodeIdeal k)) = nodeAxisIdeal k 1 := by
      change (E (E.symm
        ⟨nodeAxisIdeal k 1, nodeAxisIdeal_mem_minimalPrimes k 1⟩) :
          Ideal (MvPowerSeries (Fin 2) k)) = nodeAxisIdeal k 1
      exact congrArg Subtype.val
        (E.apply_symm_apply
          ⟨nodeAxisIdeal k 1, nodeAxisIdeal_mem_minimalPrimes k 1⟩)
    exact h.trans hb.symm

/-- The target of a surjective algebra map out of the standard node is `k[[t]]` when
its kernel is a minimal prime. -/
theorem nonempty_nodeRingSurjectiveTargetAlgEquivPowerSeries
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (f : nodeRing k →ₐ[k] B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ∈ minimalPrimes (nodeRing k)) :
    Nonempty (B ≃ₐ[k] PowerSeries k) := by
  rcases nodeRing_minimalPrime_eq_formalBranch k (RingHom.ker f) hker with h | h
  · exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
      ((Ideal.quotientEquivAlgOfEq k h).trans
        (nodeRingBranchQuotientAlgEquiv k 0))⟩
  · exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
      ((Ideal.quotientEquivAlgOfEq k h).trans
        (nodeRingBranchQuotientAlgEquiv k 1))⟩

/-- Transported form of `nonempty_nodeRingSurjectiveTargetAlgEquivPowerSeries`: a
surjective map from any algebra identified with the standard node has target `k[[t]]`
when its kernel is a minimal prime. -/
theorem nonempty_nodeSurjectiveTargetAlgEquivPowerSeries_of_algEquiv
    (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] nodeRing k) (f : A →ₐ[k] B)
    (hf : Function.Surjective f)
    (hker : RingHom.ker f ∈ minimalPrimes A) :
    Nonempty (B ≃ₐ[k] PowerSeries k) := by
  let g : nodeRing k →ₐ[k] B := f.comp e.symm.toAlgHom
  have hg : Function.Surjective g := hf.comp e.symm.surjective
  have hker' : RingHom.ker g ∈ minimalPrimes (nodeRing k) := by
    have h := (Ideal.minimalPrimesEquivOfRingEquiv e.toRingEquiv
      ⟨RingHom.ker f, hker⟩).2
    have hEq : RingHom.ker g = Ideal.map e.toRingEquiv (RingHom.ker f) := by
      change RingHom.ker (f.toRingHom.comp e.symm.toRingEquiv.toRingHom) = _
      rw [← RingHom.comap_ker]
      exact (Ideal.map_symm e.symm.toRingEquiv).symm
    rw [hEq]
    simpa only [Ideal.minimalPrimesEquivOfRingEquiv_apply] using h
  exact nonempty_nodeRingSurjectiveTargetAlgEquivPowerSeries k B g hg hker'

end AlgebraicGeometry.Scheme

end
