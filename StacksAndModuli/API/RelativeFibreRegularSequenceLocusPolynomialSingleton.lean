module

public import StacksAndModuli.API.PolynomialLocalizedResidueFibre
public import StacksAndModuli.API.RelativeFibreRegularSequenceLocusOver
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Singleton relative regular-sequence loci in polynomial algebras

For a polynomial `f ∈ A[xᵢ]` and a prime `q` containing `f`, regularity of the singleton
sequence `(f)` on the localized relative fibre at `q` is equivalent to nonvanishing of the
coefficientwise reduction of `f` over `κ(q ∩ A)`.  Equivalently, at least one coefficient of
`f` avoids `q ∩ A`.

The latter condition is the inverse image under `Spec A[xᵢ] → Spec A` of the open image of
`D(f)`.  It follows that the relative singleton regular-sequence locus is ambiently open on
`V(f)`.  Unlike the general relative regular-sequence openness theorem, this needs neither
Noetherian hypotheses nor finiteness of the variable type.

For a finite variable type, a relative-fibre regular sequence has length at most the number
of variables.  Thus, when there is at most one variable, the singleton calculation also
gives ambient openness for sequences of every finite length.

Main declarations:

* `isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_map_ne_zero`;
* `isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_mem_coefficientOpen`;
* `isOpen_relativeFibreRegularSequenceOnZeroLocus_fin_one_mvPolynomial`;
* `length_le_natCard_of_isRelativeFibreRegularSequenceAt_mvPolynomial`;
* `isOpen_relativeFibreRegularSequenceOnZeroLocus_mvPolynomial_of_natCard_le_one`.
-/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise TensorProduct

universe u

open PrimeSpectrum

namespace Matrix.FiniteFreeComplex

/-- At a prime containing `f`, relative-fibre regularity of the singleton `(f)` is
equivalent to nonvanishing of `f` after coefficientwise reduction to the residue field of
the contracted prime. -/
theorem isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_map_ne_zero
    {A σ : Type u} [CommRing A]
    (q : PrimeSpectrum (MvPolynomial σ A))
    (f : MvPolynomial σ A) (hf : f ∈ q.asIdeal) :
    IsRelativeFibreRegularSequenceAt (R := A) q (fun _ : Fin 1 ↦ f) ↔
      MvPolynomial.map
        (algebraMap A
          (q.comap (MvPolynomial.C : A →+* MvPolynomial σ A)).asIdeal.ResidueField) f ≠ 0 := by
  let S := MvPolynomial σ A
  let p := q.comap (MvPolynomial.C : A →+* S)
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  let qf : PrimeSpectrum T := PrimeSpectrum.relativeFibrePrime (R := A) q
  let P := MvPolynomial σ K
  let e : T ≃ₐ[K] P := MvPolynomial.algebraTensorAlgEquiv A K
  let qp : PrimeSpectrum P := MvPolynomial.residueFibrePrime q
  have hq : qf.asIdeal = qp.asIdeal.comap e.toRingEquiv.toRingHom := by
    exact (MvPolynomial.residueFibrePrime_comap_equiv q).symm
  let L := Localization.AtPrime qf.asIdeal
  let LP := Localization.AtPrime qp.asIdeal
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let eLoc : L ≃ₐ[K] LP := Localization.localAlgEquiv qf.asIdeal qp.asIdeal e hq
  letI : NoZeroDivisors L := eLoc.toMulEquiv.noZeroDivisors LP
  have heval :
      eLoc (algebraMap S L f) =
        algebraMap P LP (MvPolynomial.map (algebraMap A K) f) := by
    rw [IsScalarTower.algebraMap_apply S T L]
    change Localization.localRingHom qf.asIdeal qp.asIdeal e.toRingHom hq
        (algebraMap T L (Algebra.TensorProduct.includeRight f)) = _
    rw [Localization.localRingHom_to_map]
    change algebraMap P (Localization.AtPrime qp.asIdeal)
        ((MvPolynomial.algebraTensorAlgEquiv A K) (1 ⊗ₜ[A] f)) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp only [one_smul]
    change algebraMap P LP (MvPolynomial.map (algebraMap A K) f) =
      algebraMap P LP (MvPolynomial.map (algebraMap A K) f)
    rfl
  have hinc : Algebra.TensorProduct.includeRight f ∈ qf.asIdeal := by
    have hcomap :
        qf.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
      change (MvPolynomial.residueFibreTensorPrime q).asIdeal.comap
        Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal
      exact MvPolynomial.residueFibreTensorPrime_comap q
    have hf' : f ∈ qf.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
      rw [hcomap]
      exact hf
    exact hf'
  have hxmem : algebraMap S L f ∈ IsLocalRing.maximalIdeal L := by
    rw [IsScalarTower.algebraMap_apply S T L]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal qf.asIdeal L]
    exact Ideal.mem_map_of_mem _ hinc
  change RingTheory.Sequence.IsRegular L
      (List.ofFn fun _ : Fin 1 ↦ algebraMap S L f) ↔ _
  have hlist : (List.ofFn fun _ : Fin 1 ↦ algebraMap S L f) =
      [algebraMap S L f] := by
    rw [List.ofFn_succ]
    simp
  rw [hlist]
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal]
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    constructor
    · intro hreg hzero
      apply hreg.isLeftRegular.ne_zero
      apply eLoc.injective
      calc
        eLoc (algebraMap S L f) =
            algebraMap P LP (MvPolynomial.map (algebraMap A K) f) := heval
        _ = 0 := by rw [hzero, map_zero]
        _ = eLoc 0 := (map_zero eLoc).symm
    · intro hne
      have hpoly : MvPolynomial.map (algebraMap A K) f ≠ 0 := hne
      have hloc : algebraMap P LP (MvPolynomial.map (algebraMap A K) f) ≠ 0 :=
        fun hzero ↦ hpoly <|
          (map_eq_zero_iff (algebraMap P LP)
            (IsLocalization.injective LP qp.asIdeal.primeCompl_le_nonZeroDivisors)).mp hzero
      have hx : algebraMap S L f ≠ 0 := by
        intro hxzero
        apply hloc
        calc
          algebraMap P LP (MvPolynomial.map (algebraMap A K) f) =
              eLoc (algebraMap S L f) := heval.symm
          _ = eLoc 0 := congrArg eLoc hxzero
          _ = 0 := map_zero eLoc
      apply IsSMulRegular.of_right_eq_zero_of_smul
      intro y hy
      apply (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ?_).resolve_left hx
      change algebraMap S L f * y = 0 at hy
      exact hy
  · intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact hxmem

/-- On `V(f)`, singleton relative-fibre regularity is equivalent to the contracted prime
belonging to the open image of `D(f)` in the coefficient spectrum. -/
theorem isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_mem_coefficientOpen
    {A σ : Type u} [CommRing A]
    (f : MvPolynomial σ A)
    (q : PrimeSpectrum.zeroLocus (Set.range (fun _ : Fin 1 ↦ f))) :
    IsRelativeFibreRegularSequenceAt (R := A) q.1 (fun _ : Fin 1 ↦ f) ↔
      q.1.comap (MvPolynomial.C : A →+* MvPolynomial σ A) ∈
        PrimeSpectrum.comap (MvPolynomial.C : A →+* MvPolynomial σ A) ''
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (MvPolynomial σ A))) := by
  let p := q.1.comap (MvPolynomial.C : A →+* MvPolynomial σ A)
  have hf : f ∈ q.1.asIdeal := by
    exact (PrimeSpectrum.mem_zeroLocus q.1 _).mp q.2
      (Set.mem_range_self (0 : Fin 1))
  rw [isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_map_ne_zero q.1 f hf]
  have hcoeff :
      MvPolynomial.map (algebraMap A p.asIdeal.ResidueField) f ≠ 0 ↔
        ∃ i, MvPolynomial.coeff i f ∉ p.asIdeal := by
    change f ∉ RingHom.ker
      (MvPolynomial.map (algebraMap A p.asIdeal.ResidueField)) ↔ _
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField,
      MvPolynomial.mem_map_C_iff]
    push Not
    rfl
  rw [hcoeff]
  exact (MvPolynomial.mem_image_comap_C_basicOpen f p).symm

/-- For a polynomial algebra over an arbitrary commutative ring, the relative-fibre
regularity locus of the singleton `(f)` is open on `V(f)`. -/
theorem isOpen_relativeFibreRegularSequenceOnZeroLocus_fin_one_mvPolynomial
    {A σ : Type u} [CommRing A] (f : MvPolynomial σ A) :
    IsOpen {q : PrimeSpectrum.zeroLocus (Set.range (fun _ : Fin 1 ↦ f)) |
      IsRelativeFibreRegularSequenceAt (R := A) q.1 (fun _ : Fin 1 ↦ f)} := by
  let U : Set (PrimeSpectrum A) :=
    PrimeSpectrum.comap (MvPolynomial.C : A →+* MvPolynomial σ A) ''
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (MvPolynomial σ A)))
  have hU : IsOpen U := by
    exact MvPolynomial.isOpenMap_comap_C _ PrimeSpectrum.isOpen_basicOpen
  have hset :
      {q : PrimeSpectrum.zeroLocus (Set.range (fun _ : Fin 1 ↦ f)) |
        IsRelativeFibreRegularSequenceAt (R := A) q.1 (fun _ : Fin 1 ↦ f)} =
      (fun q : PrimeSpectrum.zeroLocus (Set.range (fun _ : Fin 1 ↦ f)) ↦
        q.1.comap (MvPolynomial.C : A →+* MvPolynomial σ A)) ⁻¹' U := by
    ext q
    exact
      isRelativeFibreRegularSequenceAt_fin_one_mvPolynomial_iff_mem_coefficientOpen f q
  rw [hset]
  exact hU.preimage <|
    (PrimeSpectrum.continuous_comap
      (MvPolynomial.C : A →+* MvPolynomial σ A)).comp continuous_subtype_val

/-- The length of a relative-fibre regular sequence in a finite-variable polynomial
algebra is at most the number of variables. -/
theorem length_le_natCard_of_isRelativeFibreRegularSequenceAt_mvPolynomial
    {A σ : Type u} [CommRing A] [Finite σ]
    {d : ℕ} (q : PrimeSpectrum (MvPolynomial σ A))
    (f : Fin d → MvPolynomial σ A)
    (hreg : IsRelativeFibreRegularSequenceAt (R := A) q f) :
    d ≤ Nat.card σ := by
  have length_le_dimension :
      ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
        (s : List B), RingTheory.Sequence.IsRegular B s →
          (s.length : WithBot ℕ∞) ≤ ringKrullDim B := by
    intro B _ _ _ s hs
    letI : Nontrivial (B ⧸ Ideal.ofList s) :=
      Ideal.Quotient.nontrivial_iff.mpr <| by
        intro htop
        apply hs.top_ne_smul
        rw [htop, Submodule.top_smul]
    have hquot_nonneg : 0 ≤ ringKrullDim (B ⧸ Ideal.ofList s) :=
      ringKrullDim_nonneg_of_nontrivial
    calc
      (s.length : WithBot ℕ∞) = 0 + s.length := by rw [zero_add]
      _ ≤ ringKrullDim (B ⧸ Ideal.ofList s) + s.length :=
        add_le_add_left hquot_nonneg s.length
      _ = ringKrullDim B :=
        ringKrullDim_add_length_eq_ringKrullDim_of_isRegular s hs
  let S := MvPolynomial σ A
  let p := q.comap (MvPolynomial.C : A →+* S)
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  let qf : PrimeSpectrum T := PrimeSpectrum.relativeFibrePrime (R := A) q
  let P := MvPolynomial σ K
  let qp : PrimeSpectrum P := MvPolynomial.residueFibrePrime q
  let e : T ≃ₐ[K] P := MvPolynomial.algebraTensorAlgEquiv A K
  have hq : qf.asIdeal = qp.asIdeal.comap e.toRingEquiv.toRingHom := by
    exact (MvPolynomial.residueFibrePrime_comap_equiv q).symm
  let L := Localization.AtPrime qf.asIdeal
  let LP := Localization.AtPrime qp.asIdeal
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let eLoc : L ≃ₐ[K] LP := Localization.localAlgEquiv qf.asIdeal qp.asIdeal e hq
  letI : IsNoetherianRing L :=
    isNoetherianRing_of_ringEquiv LP eLoc.toRingEquiv.symm
  let rs : List L := List.ofFn fun j ↦ algebraMap S L (f j)
  change RingTheory.Sequence.IsRegular L rs at hreg
  have hlength : (d : WithBot ℕ∞) ≤ ringKrullDim L := by
    simpa only [rs, List.length_ofFn] using length_le_dimension L rs hreg
  have hdimLP : ringKrullDim LP ≤ (Nat.card σ : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height qp.asIdeal LP]
    calc
      qp.asIdeal.height ≤ ringKrullDim P :=
        qp.asIdeal.height_le_ringKrullDim_of_isPrime
      _ = (Nat.card σ : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field, zero_add]
  have hdimL : ringKrullDim L ≤ (Nat.card σ : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv eLoc.toRingEquiv]
    exact hdimLP
  have hcast :
      ((d : ℕ∞) : WithBot ℕ∞) ≤
        ((Nat.card σ : ℕ∞) : WithBot ℕ∞) := by
    exact hlength.trans hdimL
  exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp hcast)

/-- If a polynomial algebra has at most one variable, every finite relative regular-sequence
locus is ambiently open on the corresponding zero locus. -/
theorem isOpen_relativeFibreRegularSequenceOnZeroLocus_mvPolynomial_of_natCard_le_one
    {A σ : Type u} [CommRing A] [Finite σ]
    {d : ℕ} (f : Fin d → MvPolynomial σ A) (hσ : Nat.card σ ≤ 1) :
    IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
      IsRelativeFibreRegularSequenceAt (R := A) q.1 f} := by
  by_cases hd0 : d = 0
  · subst d
    have hset :
        {q : PrimeSpectrum.zeroLocus (Set.range f) |
          IsRelativeFibreRegularSequenceAt (R := A) q.1 f} = Set.univ := by
      ext q
      simp only [IsRelativeFibreRegularSequenceAt, List.ofFn_zero]
      constructor
      · intro
        trivial
      · intro
        exact RingTheory.Sequence.IsRegular.nil _ _
    rw [hset]
    exact isOpen_univ
  by_cases hd1 : d = 1
  · subst d
    let g : MvPolynomial σ A := f 0
    have hf : f = fun _ : Fin 1 ↦ g := by
      funext i
      exact congrArg f (Fin.eq_zero i)
    rw [hf]
    exact isOpen_relativeFibreRegularSequenceOnZeroLocus_fin_one_mvPolynomial g
  · have hd2 : 2 ≤ d := by omega
    have hset :
        {q : PrimeSpectrum.zeroLocus (Set.range f) |
          IsRelativeFibreRegularSequenceAt (R := A) q.1 f} = ∅ := by
      ext q
      change IsRelativeFibreRegularSequenceAt (R := A) q.1 f ↔ False
      constructor
      · intro hreg
        have hdσ :=
          length_le_natCard_of_isRelativeFibreRegularSequenceAt_mvPolynomial q.1 f hreg
        omega
      · exact False.elim
    rw [hset]
    exact isOpen_empty

end Matrix.FiniteFreeComplex

end

end
