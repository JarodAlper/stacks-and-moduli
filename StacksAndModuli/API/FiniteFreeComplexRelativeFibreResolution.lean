module

public import StacksAndModuli.API.FiniteFreeComplexProjectiveDimension
public import StacksAndModuli.API.FiniteFreeComplexRelativeFibreBuchsbaumEisenbud
public import StacksAndModuli.API.PartialProjectiveResolutionFlat

/-!
# Relative-fibre exactness of a finite free resolution

For a bounded exact finite free complex, exactness on a relative fibre in every positive
degree is equivalent to exactness on that fibre of the canonical kernel presentation of its
degree-zero cokernel.  The reverse implication propagates coefficient-flatness from the
degree-zero differential cokernel through the successive short exact sequences of
differential cokernels.

This is the consumer bridge from the bounded Buchsbaum--Eisenbud openness theorem to the
kernel-pair exactness locus used by polynomial coefficient spreading.  It applies after a
partial resolution has been localized and its terminal syzygy has been made finite free.

Main declarations:

* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.
    isPartialProjectiveResolution_differentialCoker`;
* `Matrix.FiniteFreeComplex.
    relativeFibreExactInPositiveDegreesLocus_eq_ker_differential_zero`;
* `Matrix.FiniteFreeComplex.
    hasOpenRelativeFibreKernelExactLocus_of_buchsbaumEisenbudGrade`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace Matrix.FiniteFreeComplex

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R]

/-- The first `i + 1` short exact sequences of an exact finite free complex form a partial
projective resolution of its degree-zero differential cokernel, with the differential
cokernel in degree `i + 1` as final syzygy. -/
theorem
    IsExactInPositiveDegreesUpTo.isPartialProjectiveResolution_differentialCoker
    {C : FiniteFreeComplex R} {N i : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N) (hi : i < N) :
    Module.IsPartialProjectiveResolution R i
      (C.differentialCoker 0) (C.differentialCoker (i + 1)) := by
  induction i with
  | zero =>
      exact Module.IsPartialProjectiveResolution.zero
        (LinearMap.range (Matrix.toLin' (C.differential 0))).mkQ
        (Submodule.mkQ_surjective _)
        (C.differentialCokerToTerm 0)
        (C.differentialCokerToTerm_injective_of_exact (h 0 hi))
        (C.exact_differentialCokerToTerm_mkQ 0).linearMap_ker_eq.symm
  | succ i ih =>
      exact Module.IsPartialProjectiveResolution.succ
        (ih (by omega))
        (LinearMap.range (Matrix.toLin' (C.differential (i + 1)))).mkQ
        (Submodule.mkQ_surjective _)
        (C.differentialCokerToTerm (i + 1))
        (C.differentialCokerToTerm_injective_of_exact
          (h (i + 1) hi))
        (C.exact_differentialCokerToTerm_mkQ (i + 1)).linearMap_ker_eq.symm

/-- If the localized degree-zero differential cokernel of an exact finite free complex is
flat over an external coefficient ring, then every displayed localized differential
cokernel is flat over that coefficient ring. -/
theorem localizedTensorDifferentialCoker_flat_of_zero
    {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    (q : PrimeSpectrum S)
    (hflatZero : Module.Flat R
      (Localization.AtPrime q.asIdeal ⊗[S] (C.differentialCoker 0)))
    {i : ℕ} (hi : i ≤ N) :
    Module.Flat R
      (Localization.AtPrime q.asIdeal ⊗[S] (C.differentialCoker i)) := by
  cases i with
  | zero => exact hflatZero
  | succ i =>
      let Sq := Localization.AtPrime q.asIdeal
      letI : Module.Flat S Sq := IsLocalization.flat Sq q.asIdeal.primeCompl
      letI : Module.Flat R Sq := Module.Flat.trans R S Sq
      let K₀ := Sq ⊗[S] (C.differentialCoker 0)
      let Ki := Sq ⊗[S] (C.differentialCoker (i + 1))
      have hres : Module.IsPartialProjectiveResolution Sq i
          K₀ Ki :=
        (hexact.isPartialProjectiveResolution_differentialCoker
          (i := i) (by omega)).baseChange Sq
      let moduleZero : Module R K₀ := inferInstance
      let moduleFinal : Module R Ki := inferInstance
      have hmoduleZero :
          moduleZero = Module.compHom K₀ (algebraMap R Sq) := by
        apply Module.ext'
        intro a x
        exact (IsScalarTower.algebraMap_smul Sq a x).symm
      have hmoduleFinal :
          moduleFinal = Module.compHom Ki (algebraMap R Sq) := by
        apply Module.ext'
        intro a x
        exact (IsScalarTower.algebraMap_smul Sq a x).symm
      have hflatZeroComp : @Module.Flat R K₀ _ _
          (Module.compHom K₀ (algebraMap R Sq)) := by
        rw [← hmoduleZero]
        exact hflatZero
      have hflatFinalComp : @Module.Flat R Ki _ _
          (Module.compHom Ki (algebraMap R Sq)) :=
        hres.flat_final_of_flat hflatZeroComp
      rw [← hmoduleFinal] at hflatFinalComp
      exact hflatFinalComp

/-- For a bounded exact finite free complex, positive-degree exactness on the
localized relative fibre is equivalent to exactness of the canonical kernel presentation
of the degree-zero differential cokernel. -/
theorem isRelativeFibreExactInPositiveDegreesAt_iff_kernel_differential_zero
    {S : Type v} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    (q : PrimeSpectrum S) :
    ChainComplex.IsRelativeFibreExactInPositiveDegreesAt
        (R := R) C.toChainComplex q ↔
      LinearMap.IsRelativeFibreExactAt (R := R)
        (LinearMap.ker (Matrix.toLin' (C.differential 0))).subtype
        (Matrix.toLin' (C.differential 0)) q := by
  letI : Module.Free S S := Module.Free.self S
  letI : Module.Free S (Fin (C.termRank 0) → S) :=
    Module.Free.function (Fin (C.termRank 0)) S S
  letI : Module.Projective S (Fin (C.termRank 0) → S) :=
    Module.Projective.of_free
  let d₀ := Matrix.toLin' (C.differential 0)
  let d₁ := Matrix.toLin' (C.differential 1)
  constructor
  · intro h
    have hfibreZero : LinearMap.IsRelativeFibreExactAt (R := R) d₁ d₀ q := by
      have hdegree := h 1 (by omega)
      change LinearMap.IsRelativeFibreExactAt (R := R)
        (C.toChainComplex.d 2 1).hom (C.toChainComplex.d 1 0).hom q at hdegree
      simpa only [d₀, d₁, C.toChainComplex_d] using hdegree
    have hflatZero : Module.Flat R
        (Localization.AtPrime q.asIdeal ⊗[S] (C.differentialCoker 0)) :=
      Module.Flat.localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
        q d₁ d₀ (C.differential_comp 0) hfibreZero
    exact Module.Flat.isRelativeFibreExactAt_of_exact_of_localizedTensorCoker_flat
      q (LinearMap.ker d₀).subtype d₀
        (LinearMap.exact_subtype_ker_map d₀) hflatZero
  · intro hkernel i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    by_cases hjN : j < N
    · have hflatZero : Module.Flat R
          (Localization.AtPrime q.asIdeal ⊗[S] (C.differentialCoker 0)) :=
        (Module.Flat.isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact
          q (LinearMap.ker d₀).subtype d₀
            (LinearMap.exact_subtype_ker_map d₀)).mp hkernel
      have hflat : Module.Flat R
          (Localization.AtPrime q.asIdeal ⊗[S] (C.differentialCoker j)) :=
        C.localizedTensorDifferentialCoker_flat_of_zero N hexact q hflatZero
          (Nat.le_of_lt hjN)
      have hfibre : LinearMap.IsRelativeFibreExactAt (R := R)
          (Matrix.toLin' (C.differential (j + 1)))
          (Matrix.toLin' (C.differential j)) q :=
        Module.Flat.isRelativeFibreExactAt_of_exact_of_localizedTensorCoker_flat
          q (Matrix.toLin' (C.differential (j + 1)))
            (Matrix.toLin' (C.differential j)) (hexact j hjN) hflat
      dsimp only [ChainComplex.IsRelativeFibreExactAtDegree,
        LinearMap.IsRelativeFibreExactAt] at hfibre ⊢
      rw [show j + 1 - 1 = j by omega]
      simpa only [C.toChainComplex_X, C.toChainComplex_d] using hfibre
    · apply ChainComplex.isRelativeFibreExactAtDegree_of_isZero
      have hzero : C.termRank (j + 1) = 0 :=
        hbounded (j + 1) (by omega)
      letI : Subsingleton (C.toChainComplex.X (j + 1)) := by
        change Subsingleton (Fin (C.termRank (j + 1)) → S)
        rw [hzero]
        infer_instance
      exact ModuleCat.isZero_of_subsingleton _

/-- For a bounded exact finite free complex, the full positive-degree
relative-fibre exactness locus equals the relative-fibre exactness locus of the canonical
kernel presentation of its degree-zero differential. -/
theorem relativeFibreExactInPositiveDegreesLocus_eq_ker_differential_zero
    {S : Type v} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    ChainComplex.relativeFibreExactInPositiveDegreesLocus
        (R := R) C.toChainComplex =
      LinearMap.relativeFibreExactLocus (R := R)
        (LinearMap.ker (Matrix.toLin' (C.differential 0))).subtype
        (Matrix.toLin' (C.differential 0)) := by
  ext q
  exact C.isRelativeFibreExactInPositiveDegreesAt_iff_kernel_differential_zero
    N hbounded hexact q

/-- Fixed-sequence openness of the relative Buchsbaum--Eisenbud grade conditions makes the
relative-fibre exactness locus of the canonical degree-zero kernel presentation open for a
bounded exact finite free resolution. -/
theorem hasOpenRelativeFibreKernelExactLocus_of_buchsbaumEisenbudGrade
    {S : Type v} [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    (r : C.ExpectedRanks N)
    (hopen : ∀ (i : ℕ), i < N →
      ∀ (f : Fin (i + 1) → S),
        (∀ j, f j ∈ Matrix.minorIdeal (C.differential i) (r.rank i)) →
        IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
          IsRelativeFibreRegularSequenceAt (R := R) q.1 f}) :
    LinearMap.HasOpenRelativeFibreExactLocus (R := R)
      (LinearMap.ker (Matrix.toLin' (C.differential 0))).subtype
      (Matrix.toLin' (C.differential 0)) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  change IsOpen (LinearMap.relativeFibreExactLocus (R := R)
    (LinearMap.ker (Matrix.toLin' (C.differential 0))).subtype
    (Matrix.toLin' (C.differential 0)))
  rw [← C.relativeFibreExactInPositiveDegreesLocus_eq_ker_differential_zero
    N hbounded hexact]
  exact C.hasOpenRelativeFibreExactInPositiveDegreesLocus_of_buchsbaumEisenbudGrade
    N hbounded r hopen

end Matrix.FiniteFreeComplex

end

end
