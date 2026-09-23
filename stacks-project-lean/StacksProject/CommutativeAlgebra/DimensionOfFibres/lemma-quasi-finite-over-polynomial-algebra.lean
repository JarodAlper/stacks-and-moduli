module

public import StacksAndModuli.API.FibreAwayBaseChange
public import StacksAndModuli.API.FibreBasicOpenLift
public import StacksAndModuli.API.NoetherNormalizationDimension
public import StacksAndModuli.API.PolynomialFibreNormalizationQuasiFinite
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import StacksProject.CommutativeAlgebra.DimensionOfFibres.«definition-relative-dimension»

/-!
# Relative Noether normalization at a point

Stacks Project tag **00QE**, label `lemma-quasi-finite-over-polynomial-algebra`, in
`algebra.tex`, §`00QC` (Dimension of fibres).

At a point where a finite-type algebra has finite relative dimension `n`, one can shrink
the target to a principal neighbourhood which is quasi-finite over relative affine
`n`-space.  The proof first chooses a dimension-attaining principal open in the residue
fibre, applies dimension-indexed Noether normalization there, lifts its parameters, and
then spreads quasi-finiteness from the chosen point.  Two successive principal
localizations are combined into one before stating the result.

Main declaration:

* `Algebra.exists_notMem_quasiFinite_away_mvPolynomial_of_relativeKrullDimAt_eq`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Algebra

/-- **Lemma 10.125.2** (`00QE`,
`lemma-quasi-finite-over-polynomial-algebra`): if a finite-type algebra has relative
dimension `n` at `q`, some principal neighbourhood of `q` is quasi-finite over a
polynomial algebra in `n` variables over the coefficient ring. -/
@[stacks 00QE]
theorem exists_notMem_quasiFinite_away_mvPolynomial_of_relativeKrullDimAt_eq
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : Algebra.relativeKrullDimAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        f.toRingHom.QuasiFinite := by
  let p : Ideal R := (q.comap (algebraMap R S)).asIdeal
  let T := p.Fiber S
  let qF : PrimeSpectrum T := PrimeSpectrum.relativeFibrePrime (R := R) q
  have hdimF :
      topologicalKrullDimAtPoint (PrimeSpectrum T) qF = (n : WithBot ℕ∞) := by
    simpa only [Algebra.relativeKrullDimAt, PrimeSpectrum.relativeFibrePrime, p, T, qF]
      using hdim
  obtain ⟨g, hgq, hgdim⟩ :=
    PrimeSpectrum.relativeFibrePrime_exists_notMem_basicOpen_topologicalKrullDim_eq_atPoint
      (R := R) q
  have hdimOpen :
      topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g : T)) = (n : WithBot ℕ∞) := by
    exact hgdim.trans hdimF
  have hdimAway :
      ringKrullDim (p.Fiber (Localization.Away g)) = (n : WithBot ℕ∞) := by
    rw [Ideal.Fiber.ringKrullDim_away_eq_topologicalKrullDim_basicOpen]
    exact hdimOpen
  let Sg := Localization.Away g
  have hdisjoint : Disjoint (Submonoid.powers g : Set S) q.asIdeal := by
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgq
  let qgIdeal : Ideal Sg := q.asIdeal.map (algebraMap S Sg)
  have hqgPrime : qgIdeal.IsPrime := by
    dsimp only [qgIdeal]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers g) Sg q.asIdeal q.isPrime hdisjoint
  let qg : PrimeSpectrum Sg := ⟨qgIdeal, hqgPrime⟩
  have hqgUnder : qg.asIdeal.under S = q.asIdeal := by
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers g) Sg q.isPrime hdisjoint
  have hp : qg.asIdeal.under R = p := by
    rw [← Ideal.under_under (B := S), hqgUnder]
    rfl
  have hdimAway' :
      ringKrullDim ((qg.asIdeal.under R).Fiber Sg) = (n : WithBot ℕ∞) := by
    calc
      ringKrullDim ((qg.asIdeal.under R).Fiber Sg) =
          ringKrullDim (p.Fiber Sg) :=
        Ideal.Fiber.ringKrullDim_congr_ideal _ _ hp
      _ = (n : WithBot ℕ∞) := by simpa only [Sg] using hdimAway
  let qgF : PrimeSpectrum ((qg.asIdeal.under R).Fiber Sg) :=
    PrimeSpectrum.relativeFibrePrime (R := R) qg
  letI : Nontrivial ((qg.asIdeal.under R).Fiber Sg) := qgF.nontrivial
  obtain ⟨ν, hνinj, hνfinite⟩ :=
    NoetherNormalization.exists_finite_inj_algHom_of_fg_of_ringKrullDim_eq
      (qg.asIdeal.under R).ResidueField
      ((qg.asIdeal.under R).Fiber Sg) n hdimAway'
  obtain ⟨s, hs⟩ :=
    MvPolynomial.quasiFiniteAt_aeval_of_finite_fibre_normalization
      qg.asIdeal n ν hνinj hνfinite
  let A := MvPolynomial (Fin n) R
  let f : A →ₐ[R] Sg := MvPolynomial.aeval s
  letI : Algebra A Sg := f.toAlgebra
  letI : IsScalarTower R A Sg := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Algebra.FiniteType A Sg :=
    Algebra.FiniteType.of_restrictScalars_finiteType R A Sg
  haveI hqfAt : Algebra.QuasiFiniteAt A qg.asIdeal := hs
  obtain ⟨a, haqg, hqf⟩ :=
    Algebra.QuasiFiniteAt.exists_notMem_quasiFinite_away
      (R := A) (S := Sg) qg.asIdeal
  let z : S := (IsLocalization.Away.sec g a).1
  let h : S := g * z
  letI hlocalization : IsLocalization.Away h (Localization.Away a) := by
    exact IsLocalization.Away.mul_of_associated g z a
      (IsLocalization.Away.associated_sec_fst g a)
  let e : Localization.Away h ≃ₐ[S] Localization.Away a :=
    Localization.algEquiv _ _
  let φ : A →ₐ[R] Localization.Away h :=
    (e.symm.restrictScalars R).toAlgHom.comp
      (IsScalarTower.toAlgHom R A (Localization.Away a))
  have hφ : φ.toRingHom.QuasiFinite := by
    have he : e.symm.toRingEquiv.toRingHom.QuasiFinite :=
      RingHom.QuasiFinite.of_finite e.symm.toRingEquiv.finite
    have ha : (algebraMap A (Localization.Away a)).QuasiFinite :=
      RingHom.quasiFinite_algebraMap.mpr hqf
    exact he.comp ha
  refine ⟨h, ?_, φ, hφ⟩
  refine Ideal.IsPrime.mul_notMem q.isPrime hgq ?_
  intro hzq
  apply haqg
  rw [Ideal.mem_iff_of_associated
    (IsLocalization.Away.associated_sec_fst g a).symm]
  exact Ideal.mem_map_of_mem (algebraMap S Sg) hzq

end Algebra

end

end
