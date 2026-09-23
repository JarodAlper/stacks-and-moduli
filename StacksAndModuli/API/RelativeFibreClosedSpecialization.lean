module

public import StacksAndModuli.API.RegularSequenceClosedSpecialization
public import StacksAndModuli.API.RelativeFibreRegularSequenceLocusOver

/-!
# Closed specializations in relative fibres

Let `R → S` be a finite-type map and let `q ∈ Spec S`.  The residue fibre over the
contraction of `q` is a finite-type algebra over a field, hence Jacobson.  A principal-open
neighbourhood of the prime induced by `q` therefore contains a maximal specialization.
Transporting that point back through the standard fibre equivalence gives a specialization
of `q` in `Spec S` which is closed in the same residue fibre.

The same construction, applied to the open local regular-sequence locus in the fibre,
produces a closed specialization at which a relative-fibre regular sequence remains
regular.

Main declarations:

* `PrimeSpectrum.exists_specialization_closedInFibre_avoiding`;
* `Matrix.FiniteFreeComplex.exists_specialization_closedInFibre_isRelativeFibreRegularSequenceAt`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace PrimeSpectrum

/-- Maximality of the fibre prime can be checked after identifying the contracted prime
with an explicitly named base point. -/
theorem relativeFibrePrime_isMaximal_of_comap_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (p : PrimeSpectrum R)
    (hp : q.comap (algebraMap R S) = p)
    (hmax : ((PrimeSpectrum.preimageEquivFiber R S p) ⟨q, hp⟩).asIdeal.IsMaximal) :
    (relativeFibrePrime (R := R) q).asIdeal.IsMaximal := by
  subst p
  exact hmax

/-- A principal-open neighbourhood of a point in a finite-type relative spectrum contains
a specialization which is closed in the same residue fibre. -/
theorem exists_specialization_closedInFibre_avoiding
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal) :
    ∃ q' : PrimeSpectrum S,
      q ≤ q' ∧
      q'.comap (algebraMap R S) = q.comap (algebraMap R S) ∧
      g ∉ q'.asIdeal ∧
      (relativeFibrePrime (R := R) q').asIdeal.IsMaximal := by
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  let E := PrimeSpectrum.preimageOrderIsoFiber R S p
  let qInFibre : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := ⟨q, rfl⟩
  let qF : PrimeSpectrum T := relativeFibrePrime (R := R) q
  have hgF : Algebra.TensorProduct.includeRight g ∉ qF.asIdeal := by
    intro hmem
    apply hg
    rw [← relativeFibrePrime_comap_includeRight (R := R) q]
    exact hmem
  letI : Nontrivial T := qF.nontrivial
  letI : Algebra.FiniteType K T := inferInstance
  letI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  obtain ⟨m, hm, hqm, hgm⟩ :=
    Ideal.exists_isMaximal_over_notMem_of_isJacobsonRing qF.asIdeal hgF
  let mPoint : PrimeSpectrum T := ⟨m, hm.isPrime⟩
  let q'InFibre := E.symm mPoint
  let q' : PrimeSpectrum S := q'InFibre.1
  have hqq'InFibre : qInFibre ≤ q'InFibre := by
    rw [← E.le_iff_le]
    rw [show E qInFibre = qF by rfl,
      show E q'InFibre = mPoint by
        exact E.apply_symm_apply mPoint]
    exact hqm
  have hqq' : q ≤ q' := hqq'InFibre
  have hq'comap : q'.comap (algebraMap R S) = p := q'InFibre.2
  have hgq' : g ∉ q'.asIdeal := by
    intro hgq'
    apply hgm
    change Algebra.TensorProduct.includeRight g ∈ mPoint.asIdeal
    have hq'ideal : q'.asIdeal =
        mPoint.asIdeal.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] T).toRingHom := by
      rfl
    rw [hq'ideal] at hgq'
    exact hgq'
  have hpointP :
      (PrimeSpectrum.preimageEquivFiber R S p) ⟨q', hq'comap⟩ =
        mPoint := by
    change E ⟨q', hq'comap⟩ = mPoint
    rw [show (⟨q', hq'comap⟩ :
        PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) = q'InFibre by
      apply Subtype.ext
      rfl]
    exact E.apply_symm_apply mPoint
  have hclosed :
      (relativeFibrePrime (R := R) q').asIdeal.IsMaximal := by
    apply relativeFibrePrime_isMaximal_of_comap_eq q' p hq'comap
    rw [hpointP]
    exact hm
  exact ⟨q', hqq', hq'comap.trans rfl, hgq', hclosed⟩

end PrimeSpectrum

namespace Matrix.FiniteFreeComplex

/-- Relative-fibre regularity can be proved in the fibre over any explicitly named copy
of the contracted prime. -/
theorem isRelativeFibreRegularSequenceAt_of_comap_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} (q : PrimeSpectrum S) (p : PrimeSpectrum R)
    (hp : q.comap (algebraMap R S) = p) (f : Fin d → S)
    (hreg : RingTheory.Sequence.IsRegularAfterLocalizationAt
      (List.ofFn fun j ↦
        Algebra.TensorProduct.includeRight (f j))
      ((PrimeSpectrum.preimageEquivFiber R S p) ⟨q, hp⟩)) :
    IsRelativeFibreRegularSequenceAt (R := R) q f := by
  subst p
  exact
    (isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt
      (R := R) q f).mpr hreg

/-- Relative-fibre regularity descends from a specialization in the same fibre to a
generization containing the sequence. -/
theorem isRelativeFibreRegularSequenceAt_of_le_of_comap_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    {d : ℕ} {q q' : PrimeSpectrum S} (f : Fin d → S)
    (hqq' : q ≤ q')
    (hcomap : q'.comap (algebraMap R S) = q.comap (algebraMap R S))
    (hmem : ∀ i, f i ∈ q.asIdeal)
    (hreg : IsRelativeFibreRegularSequenceAt (R := R) q' f) :
    IsRelativeFibreRegularSequenceAt (R := R) q f := by
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  let rs : List S := List.ofFn f
  let qInFibre : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} :=
    ⟨q, rfl⟩
  let q'InFibre : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} :=
    ⟨q', hcomap⟩
  have hqzero : Ideal.ofList rs ≤ q.asIdeal :=
    Ideal.span_le.mpr <| List.forall_mem_ofFn_iff.mpr hmem
  have hq'zero : Ideal.ofList rs ≤ q'.asIdeal := hqzero.trans hqq'
  let qZ : Ideal.Fiber.fixedFibreZeroLocus p rs :=
    ⟨qInFibre, hqzero⟩
  let q'Z : Ideal.Fiber.fixedFibreZeroLocus p rs :=
    ⟨q'InFibre, hq'zero⟩
  have hspec : qZ ⤳ q'Z := by
    rw [subtype_specializes_iff, subtype_specializes_iff,
      ← PrimeSpectrum.le_iff_specializes]
    exact hqq'
  have hopen := isOpen_relativeFibreRegularSequenceLocusOver
    (R := R) p f
  have hq'L : q'Z ∈ relativeFibreRegularSequenceLocusOver
      (R := R) p f := by
    exact hreg
  exact hspec.mem_open hopen hq'L

/-- A relative-fibre regular sequence remains regular at some specialization which is
closed in the same residue fibre. -/
theorem exists_specialization_closedInFibre_isRelativeFibreRegularSequenceAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    {d : ℕ} (q : PrimeSpectrum S) (f : Fin d → S)
    (hmem : ∀ i, f i ∈ q.asIdeal)
    (hreg : IsRelativeFibreRegularSequenceAt (R := R) q f) :
    ∃ q' : PrimeSpectrum S,
      q ≤ q' ∧
      q'.comap (algebraMap R S) = q.comap (algebraMap R S) ∧
      IsRelativeFibreRegularSequenceAt (R := R) q' f ∧
      (PrimeSpectrum.relativeFibrePrime (R := R) q').asIdeal.IsMaximal := by
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  let E := PrimeSpectrum.preimageOrderIsoFiber R S p
  let qInFibre : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := ⟨q, rfl⟩
  let qF : PrimeSpectrum T := PrimeSpectrum.relativeFibrePrime (R := R) q
  let rs : List S := List.ofFn f
  let rsF : List T :=
    rs.map (Algebra.TensorProduct.includeRight : S →ₐ[R] T)
  have hmemF : ∀ x ∈ rsF, x ∈ qF.asIdeal := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    change Algebra.TensorProduct.includeRight s ∈ qF.asIdeal
    have hs' : s ∈ q.asIdeal := by
      rw [List.mem_ofFn', Set.mem_range] at hs
      obtain ⟨i, rfl⟩ := hs
      exact hmem i
    rw [← PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q] at hs'
    exact hs'
  have hregF : RingTheory.Sequence.IsRegularAfterLocalizationAt rsF qF := by
    have h :=
      (isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt
        (R := R) q f).mp hreg
    have hrsF :
        rsF = List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j) := by
      dsimp only [rsF, rs]
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      rfl
    rw [hrsF]
    exact h
  letI : Nontrivial T := qF.nontrivial
  letI : Algebra.FiniteType K T := inferInstance
  obtain ⟨m, hm, hqm, hregm⟩ :=
    RingTheory.Sequence.exists_isMaximal_specialization_isRegularAfterLocalizationAt
      K T rsF qF hmemF hregF
  let mPoint : PrimeSpectrum T := ⟨m, hm.isPrime⟩
  let q'InFibre := E.symm mPoint
  let q' : PrimeSpectrum S := q'InFibre.1
  have hqq'InFibre : qInFibre ≤ q'InFibre := by
    rw [← E.le_iff_le]
    rw [show E qInFibre = qF by rfl,
      show E q'InFibre = mPoint by
        exact E.apply_symm_apply mPoint]
    exact hqm
  have hqq' : q ≤ q' := hqq'InFibre
  have hq'comap : q'.comap (algebraMap R S) = p := q'InFibre.2
  have hpointP :
      (PrimeSpectrum.preimageEquivFiber R S p) ⟨q', hq'comap⟩ =
        mPoint := by
    change E ⟨q', hq'comap⟩ = mPoint
    rw [show (⟨q', hq'comap⟩ :
        PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) = q'InFibre by
      apply Subtype.ext
      rfl]
    exact E.apply_symm_apply mPoint
  have hreg' : IsRelativeFibreRegularSequenceAt (R := R) q' f := by
    apply isRelativeFibreRegularSequenceAt_of_comap_eq q' p hq'comap f
    have hrsF :
        rsF = List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j) := by
      dsimp only [rsF, rs]
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      rfl
    rw [hpointP]
    rw [← hrsF]
    exact hregm
  have hclosed :
      (PrimeSpectrum.relativeFibrePrime (R := R) q').asIdeal.IsMaximal := by
    apply PrimeSpectrum.relativeFibrePrime_isMaximal_of_comap_eq
      q' p hq'comap
    rw [hpointP]
    exact hm
  exact ⟨q', hqq', hq'comap.trans rfl, hreg', hclosed⟩

end Matrix.FiniteFreeComplex

end
