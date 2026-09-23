module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import StacksAndModuli.API.FiniteFreeComplexAssociatedPrimeExactness
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudLocalization
public import StacksAndModuli.API.FiniteFreeComplexPrincipalQuotient
public import StacksAndModuli.API.IdealRegularElementAssociatedPrimes
public import StacksAndModuli.API.IdealRegularSequencePrincipalQuotientLift

/-!
# The exact-to-grade Buchsbaum--Eisenbud implication

For a bounded exact finite free complex over a Noetherian ring, none of its expected-size
minor ideals is contained in an associated prime.  The product of all these ideals is
therefore contained in no associated prime, so it contains a regular element common to
every expected-size minor ideal.

If this common element is a unit, all the minor ideals are the unit ideal.  Otherwise,
reduce modulo the common regular element and delete the bottom term of the complex.
Exactness survives on this tail, and induction supplies the shorter regular sequences in
the quotient minor ideals.  Prepending the common element after lifting the quotient
sequences proves the required grade bounds over the original ring.

Main declarations:

* `Matrix.FiniteFreeComplex.ExpectedRanks.
  exists_isRegular_mem_minorIdeals_of_exact`;
* `Matrix.FiniteFreeComplex.
  buchsbaumEisenbudGrade_of_isExactInPositiveDegreesUpTo`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

namespace ExpectedRanks

/-- The expected-size minor ideals of a bounded exact finite free complex over a
Noetherian ring contain a common regular element. -/
theorem exists_isRegular_mem_minorIdeals_of_exact
    [IsNoetherianRing R]
    {C : FiniteFreeComplex R} {N : ℕ}
    (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    ∃ x : R, IsRegular x ∧
      ∀ i : ℕ, i < N →
        x ∈ Matrix.minorIdeal (C.differential i) (r.rank i) := by
  let I : ℕ → Ideal R :=
    fun i ↦ Matrix.minorIdeal (C.differential i) (r.rank i)
  let J : Ideal R := (Finset.range N).prod I
  have hJavoid : ∀ p ∈ associatedPrimes R R, ¬ J ≤ p := by
    intro p hp hJp
    letI : p.IsPrime := IsAssociatedPrime.isPrime hp
    change (Finset.range N).prod I ≤ p at hJp
    obtain ⟨i, hi, hIp⟩ :=
      ((inferInstance : p.IsPrime).prod_le).mp hJp
    let q : PrimeSpectrum R := ⟨p, inferInstance⟩
    have hiN : i < N := Finset.mem_range.mp hi
    apply r.minorIdeal_not_le_associatedPrime_of_exact
      hbounded hexact (Nat.le_of_lt hiN) q hp
    simpa only [I, q] using hIp
  obtain ⟨x, hxJ, hxsmul⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrime_not_le
      (M := R) J).mpr hJavoid
  have hxreg : IsRegular x :=
    (Commute.isRegular_iff (Commute.all x)).mpr hxsmul.isLeftRegular
  refine ⟨x, hxreg, ?_⟩
  intro i hi
  have hJle : J ≤ I i := by
    change (Finset.range N).prod I ≤ I i
    exact Ideal.prod_le_inf.trans
      (Finset.inf_le (b := i) (Finset.mem_range.mpr hi))
  exact hJle hxJ

end ExpectedRanks

/-- A bounded exact finite free complex over a Noetherian ring satisfies the
Buchsbaum--Eisenbud grade conditions for any system of expected ranks. -/
theorem buchsbaumEisenbudGrade_of_isExactInPositiveDegreesUpTo
    [IsNoetherianRing R]
    (C : FiniteFreeComplex R) {N : ℕ}
    (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    C.HasBuchsbaumEisenbudGrade r := by
  induction N generalizing R C with
  | zero =>
      intro i hi
      omega
  | succ N ih =>
      obtain ⟨x, hxreg, hxI⟩ :=
        r.exists_isRegular_mem_minorIdeals_of_exact hbounded hexact
      by_cases hxunit : IsUnit x
      · intro i hi
        dsimp only
        left
        exact Ideal.eq_top_of_isUnit_mem
          (Matrix.minorIdeal (C.differential i) (r.rank i)) (hxI i hi) hxunit
      · let q : R →+* R ⧸ Ideal.span {x} :=
          Ideal.Quotient.mk (Ideal.span {x})
        let Cq := C.map q
        let rq := r.map q
        have htailBounded : Cq.tail.IsBoundedAbove N :=
          (hbounded.map q).tail
        have htailExact :
            Cq.tail.IsExactInPositiveDegreesUpTo N := by
          exact hexact.map_principalQuotient_tail x hxreg
        have htailGrade :
            Cq.tail.HasBuchsbaumEisenbudGrade rq.tail := by
          exact ih (R := R ⧸ Ideal.span {x}) Cq.tail rq.tail
            htailBounded htailExact
        intro i hi
        dsimp only
        cases i with
        | zero =>
            right
            let f : Fin 1 → R := fun _ ↦ x
            refine ⟨f, fun _ ↦ hxI 0 hi, ?_⟩
            have hweak : RingTheory.Sequence.IsWeaklyRegular R [x] :=
              (RingTheory.Sequence.isWeaklyRegular_singleton_iff R x).mpr
                hxreg.isSMulRegular
            have hregular : RingTheory.Sequence.IsRegular R [x] := by
              refine ⟨hweak, ?_⟩
              simpa [Ideal.ofList_singleton] using
                (Ideal.span_singleton_ne_top hxunit).symm
            simpa [f] using hregular
        | succ i =>
            have hiN : i < N := by omega
            have htail := htailGrade i hiN
            let I : Ideal R := Matrix.minorIdeal
              (C.differential (i + 1)) (r.rank (i + 1))
            have hxI' : x ∈ I :=
              hxI (i + 1) (by omega)
            have htail' :
                I.map q = ⊤ ∨
                  ∃ g : Fin (i + 1) → R ⧸ Ideal.span {x},
                    (∀ j, g j ∈ I.map q) ∧
                      RingTheory.Sequence.IsRegular
                        (R ⧸ Ideal.span {x}) (List.ofFn g) := by
              simpa only [Cq, rq, I, tail_differential,
                map_differential, ExpectedRanks.tail_rank,
                ExpectedRanks.map_rank, Matrix.minorIdeal_map] using htail
            rcases htail' with htop | ⟨g, hgI, hgreg⟩
            · left
              have hker : RingHom.ker q ≤ I := by
                dsimp only [q]
                rw [Ideal.mk_ker]
                simpa [Ideal.span_le] using hxI'
              have hcomap := congrArg (Ideal.comap q) htop
              rw [Ideal.comap_map_of_surjective q
                    Ideal.Quotient.mk_surjective I,
                  Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
                  sup_eq_left.mpr hker] at hcomap
              exact hcomap
            · right
              exact
                Ideal.exists_family_mem_and_isRegular_succ_of_isRegular_map_quotient
                  I x hxI' hxreg g hgI hgreg

end Matrix.FiniteFreeComplex

end

end
