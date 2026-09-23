module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksAndModuli.API.RegularSequenceLocalizationLocus

/-!
# Regular sequences on fixed relative fibres

For a Noetherian ring `T`, this file upgrades openness of weak regularity after localization
to openness of the actual regular-sequence locus inside the sequence's zero locus.  It then
applies this result to the fibre ring `κ(p) ⊗[R] S` of a finite-type map `R → S`.

The standard homeomorphism between the set-theoretic fibre of `Spec S → Spec R` over `p`
and `Spec (κ(p) ⊗[R] S)` restricts to the two corresponding zero loci.  Transporting the
regular-sequence locus across that homeomorphism proves the fixed-contracted-prime version
of the topological conclusion in Stacks Project tag 00RA.

This does not prove 00RA itself: its relative open neighbourhood may contain points whose
contractions to `Spec R` differ from `p`.  Producing that neighbourhood uses the missing
equidimensional Cohen--Macaulay fibre and relative-dimension argument.

Main declarations:

* `RingTheory.Sequence.isOpen_regularAfterLocalizationOnZeroLocus`;
* `Ideal.Fiber.fixedFibreZeroLocusHomeomorph`;
* `Ideal.Fiber.isOpen_fixedFibreRegularSequenceLocus`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise TensorProduct

universe u v

namespace RingTheory.Sequence

variable {T : Type u} [CommRing T]

/-- Regularity of a sequence in the local ring at a prime. -/
def IsRegularAfterLocalizationAt (rs : List T) (q : PrimeSpectrum T) : Prop :=
  IsRegular (Localization.AtPrime q.asIdeal)
    (rs.map (algebraMap T (Localization.AtPrime q.asIdeal)))

/-- The regular-sequence locus, regarded as a subset of the sequence's zero locus. -/
def regularAfterLocalizationOnZeroLocus (rs : List T) :
    Set (PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set T)) :=
  {q | IsRegularAfterLocalizationAt rs q.1}

/-- On the zero locus, local regularity is equivalent to the tensor-model weak regularity
used by `isOpen_weaklyRegularAfterLocalizationLocus`. -/
theorem isRegularAfterLocalizationAt_iff_isWeaklyRegularAfterLocalizationAt
    (rs : List T) (q : PrimeSpectrum T)
    (hq : q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set T)) :
    IsRegularAfterLocalizationAt rs q ↔
      IsWeaklyRegularAfterLocalizationAt T rs q := by
  let Tq := Localization.AtPrime q.asIdeal
  let e := TensorProduct.AlgebraTensorModule.rid T Tq Tq
  have hmem : ∀ x ∈ rs.map (algebraMap T Tq),
      x ∈ IsLocalRing.maximalIdeal Tq := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Tq q.asIdeal]
    exact hq (Ideal.subset_span hr)
  change IsRegular Tq (rs.map (algebraMap T Tq)) ↔
    IsWeaklyRegular (Tq ⊗[T] T) (rs.map (algebraMap T Tq))
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem]
  exact (e.isWeaklyRegular_congr (rs.map (algebraMap T Tq))).symm

/-- Over a Noetherian ring, the local regular-sequence locus is open in the sequence's
zero locus. -/
theorem isOpen_regularAfterLocalizationOnZeroLocus
    [IsNoetherianRing T] (rs : List T) :
    IsOpen (regularAfterLocalizationOnZeroLocus rs) := by
  have hopen := isOpen_weaklyRegularAfterLocalizationLocus (M := T) rs
  have heq : regularAfterLocalizationOnZeroLocus rs =
      Subtype.val ⁻¹' weaklyRegularAfterLocalizationLocus T rs := by
    ext q
    exact isRegularAfterLocalizationAt_iff_isWeaklyRegularAfterLocalizationAt
      rs q.1 q.2
  rw [heq]
  exact hopen.preimage continuous_subtype_val

end RingTheory.Sequence

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre homeomorphism identifies the zero locus of a sequence with the zero locus of
its image in the fibre ring. -/
theorem fixedFibreZeroLocus_iff (p : PrimeSpectrum R) (rs : List S) :
    let e := PrimeSpectrum.preimageHomeomorphFiber R S p
    ∀ x, x.1 ∈ PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set S) ↔
      e x ∈ PrimeSpectrum.zeroLocus
        (Ideal.ofList (rs.map (Algebra.TensorProduct.includeRight :
          S →ₐ[R] p.asIdeal.Fiber S)) : Set (p.asIdeal.Fiber S)) := by
  dsimp only
  intro x
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  change Ideal.ofList rs ≤ x.1.asIdeal ↔
    Ideal.ofList (rs.map (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.asIdeal.Fiber S)) ≤ (e x).asIdeal
  let f : S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom
  have hmap : Ideal.ofList (rs.map (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.asIdeal.Fiber S)) = (Ideal.ofList rs).map f := by
    change Ideal.ofList (rs.map f) = (Ideal.ofList rs).map f
    exact (Ideal.map_ofList f rs).symm
  rw [hmap, Ideal.map_le_iff_le_comap]
  have h := e.left_inv x
  have hc := congrArg (fun y ↦ y.1.asIdeal) h
  exact iff_of_eq (congrArg (Ideal.ofList rs ≤ ·) hc.symm)

/-- The zero locus of a sequence inside the set-theoretic fibre over `p`. -/
def fixedFibreZeroLocus (p : PrimeSpectrum R) (rs : List S) :
    Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) :=
  {q | q.1 ∈ PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set S)}

/-- The homeomorphism from the sequence's zero locus in the set-theoretic fibre to the
corresponding zero locus in the spectrum of the fibre ring. -/
noncomputable def fixedFibreZeroLocusHomeomorph
    (p : PrimeSpectrum R) (rs : List S) :
    fixedFibreZeroLocus p rs ≃ₜ
      PrimeSpectrum.zeroLocus
        (Ideal.ofList (rs.map (Algebra.TensorProduct.includeRight :
          S →ₐ[R] p.asIdeal.Fiber S)) : Set (p.asIdeal.Fiber S)) :=
  (PrimeSpectrum.preimageHomeomorphFiber R S p).subtype
    (fixedFibreZeroLocus_iff p rs)

/-- The fixed-fibre regular-sequence locus, transported from the fibre ring. -/
def fixedFibreRegularSequenceLocus
    (p : PrimeSpectrum R) (rs : List S) :
    Set (fixedFibreZeroLocus p rs) :=
  (fixedFibreZeroLocusHomeomorph p rs) ⁻¹'
    RingTheory.Sequence.regularAfterLocalizationOnZeroLocus
      (rs.map (Algebra.TensorProduct.includeRight :
        S →ₐ[R] p.asIdeal.Fiber S))

@[simp]
theorem mem_fixedFibreRegularSequenceLocus
    (p : PrimeSpectrum R) (rs : List S) (q : fixedFibreZeroLocus p rs) :
    q ∈ fixedFibreRegularSequenceLocus p rs ↔
      RingTheory.Sequence.IsRegularAfterLocalizationAt
        (rs.map (Algebra.TensorProduct.includeRight :
          S →ₐ[R] p.asIdeal.Fiber S))
        (fixedFibreZeroLocusHomeomorph p rs q).1 :=
  Iff.rfl

/-- For a finite-type map, the regular-sequence locus on the spectrum of each fixed fibre
ring is open in the corresponding zero locus. -/
theorem isOpen_regularSequenceLocalizationLocus
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) (rs : List S) :
    IsOpen (RingTheory.Sequence.regularAfterLocalizationOnZeroLocus
      (rs.map (Algebra.TensorProduct.includeRight :
        S →ₐ[R] p.asIdeal.Fiber S))) := by
  letI : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing
      p.asIdeal.ResidueField (p.asIdeal.Fiber S)
  exact RingTheory.Sequence.isOpen_regularAfterLocalizationOnZeroLocus _

/-- For a finite-type map, regularity of a sequence is open on its zero locus inside each
fixed set-theoretic fibre. -/
theorem isOpen_fixedFibreRegularSequenceLocus
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) (rs : List S) :
    IsOpen (fixedFibreRegularSequenceLocus p rs) := by
  exact (isOpen_regularSequenceLocalizationLocus p rs).preimage
    (fixedFibreZeroLocusHomeomorph p rs).continuous

end Ideal.Fiber

end

end
