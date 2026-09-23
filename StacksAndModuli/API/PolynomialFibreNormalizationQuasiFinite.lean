module

public import StacksAndModuli.API.FibreNoetherNormalizationLift
public import StacksAndModuli.API.LocalizedRelativeFibrePushout
public import StacksAndModuli.API.RelativeFibreExactnessInterface
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Quasi-finiteness from a finite normalization of one coefficient fibre

Let `R[X] → S` be the polynomial map obtained by evaluating the variables at a finite
family `s : Fin n → S`, and let `q` be a prime of `S`.  If the induced map on the fibre
over `q ∩ R` is finite, then `R[X] → S` is quasi-finite at `q`.

The proof deliberately passes through Mathlib's weak quasi-finiteness criterion.  The
localized coefficient fibre is quasi-finite over the residue-field polynomial ring because
the given map is finite.  It is also quasi-finite over `R[X]`, since
`R[X] → κ(q ∩ R)[X]` is a base change of the quasi-finite residue-field map.  Finally,
the local fibre of `R[X] → S` is a quotient of this localized coefficient fibre.  This
avoids constructing and transporting an iterated residue-fibre equivalence.

Main declarations:

* `MvPolynomial.quasiFiniteAt_aeval_of_finite_fibre_map`;
* `MvPolynomial.quasiFiniteAt_aeval_of_finite_fibre_normalization`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace MvPolynomial

/-- Quasi-finiteness at a prime of a finite-type algebra spreads to a principal
neighbourhood in the target. -/
theorem _root_.Algebra.QuasiFiniteAt.exists_notMem_quasiFinite_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] :
    ∃ a ∉ q, Algebra.QuasiFinite R (Localization.Away a) := by
  obtain ⟨S', hS', a, ha, haway⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := R) q
  letI : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  haveI : Algebra.QuasiFinite R S' := inferInstance
  haveI : Algebra.QuasiFinite S' (Localization.Away a) := inferInstance
  haveI hsource : Algebra.QuasiFinite R (Localization.Away a) :=
    Algebra.QuasiFinite.trans R S' (Localization.Away a)
  have htarget : Algebra.QuasiFinite R (Localization.Away (a : S)) :=
    Algebra.QuasiFinite.of_surjective_algHom
      (Localization.awayMapₐ S'.val a) haway.2
  exact ⟨a, ha, htarget⟩

/-- If the coefficientwise residue-fibre map induced by evaluation is finite, evaluation
is quasi-finite at the chosen prime of the target. -/
theorem quasiFiniteAt_aeval_of_finite_fibre_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (n : ℕ) (s : Fin n → S)
    (g : MvPolynomial (Fin n) (q.under R).ResidueField →ₐ[(q.under R).ResidueField]
      (q.under R).Fiber S)
    (hg : g.Finite)
    (hcompat :
      (g.restrictScalars R).comp
          (MvPolynomial.mapAlgHom
            (R := R) (S₁ := R) (S₂ := (q.under R).ResidueField)
            (Algebra.ofId R (q.under R).ResidueField)) =
        (Algebra.TensorProduct.includeRight : S →ₐ[R] (q.under R).Fiber S).comp
          (MvPolynomial.aeval s)) :
    let f := MvPolynomial.aeval s
    letI : Algebra (MvPolynomial (Fin n) R) S := f.toAlgebra
    Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) q := by
  let A := MvPolynomial (Fin n) R
  let p := q.under R
  let K := p.ResidueField
  let B := MvPolynomial (Fin n) K
  let T := p.Fiber S
  let f : A →ₐ[R] S := MvPolynomial.aeval s
  let φ : A →ₐ[R] B :=
    MvPolynomial.mapAlgHom
      (R := R) (S₁ := R) (S₂ := K) (Algebra.ofId R K)
  letI : Algebra A S := f.toAlgebra
  letI : Algebra.FiniteType A S :=
    Algebra.FiniteType.of_restrictScalars_finiteType R A S
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B T := g.toAlgebra
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  letI : Algebra A T :=
    ((Algebra.TensorProduct.includeRight : S →ₐ[R] T).comp f).toAlgebra
  letI : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun x ↦
    DFunLike.congr_fun hcompat.symm x
  haveI hfinite : Module.Finite B T := hg
  haveI hqfBT : Algebra.QuasiFinite B T := inferInstance
  let qT : PrimeSpectrum T :=
    PrimeSpectrum.relativeFibrePrime (R := R) ⟨q, inferInstance⟩
  let L := Localization.AtPrime qT.asIdeal
  haveI hqfBL : Algebra.QuasiFinite B L := inferInstance
  haveI hqfRK : Algebra.QuasiFinite R K := inferInstance
  let e : (A ⊗[R] K) ≃ₐ[A] B :=
    { __ := (Algebra.TensorProduct.comm R A K).toRingEquiv.trans
          (MvPolynomial.algebraTensorAlgEquiv R K).toRingEquiv
      commutes' := fun x ↦ by
        change MvPolynomial.algebraTensorAlgEquiv R K (1 ⊗ₜ[R] x) = φ x
        simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, φ]
        rfl }
  haveI hqfTensor : Algebra.QuasiFinite A (A ⊗[R] K) := inferInstance
  haveI hqfAB : Algebra.QuasiFinite A B :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  haveI hqfAL : Algebra.QuasiFinite A L := Algebra.QuasiFinite.trans A B L
  let r : Ideal S :=
    qT.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  have hrq : r = q :=
    PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) ⟨q, inferInstance⟩
  haveI : r.IsPrime := Ideal.comap_isPrime _ _
  let Sr := Localization.AtPrime r
  haveI : qT.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr L :=
    Localization.AtPrime.algebraOfLiesOver r qT.asIdeal
  let I : Ideal Sr := p.map (algebraMap R Sr)
  let J : Ideal Sr := (r.under A).map (algebraMap A Sr)
  have hIJ : I ≤ J := by
    have hpA : p.map (algebraMap R A) ≤ r.under A := by
      rw [Ideal.map_le_iff_le_comap]
      change p ≤ (r.under A).under R
      rw [Ideal.under_under]
      simpa only [p, hrq] using (le_refl (q.under R))
    dsimp only [I, J]
    calc
      p.map (algebraMap R Sr) =
          p.map ((algebraMap A Sr).comp (algebraMap R A)) :=
        congrArg (fun h : R →+* Sr ↦ p.map h)
          (IsScalarTower.algebraMap_eq R A Sr)
      _ = (p.map (algebraMap R A)).map (algebraMap A Sr) :=
        (Ideal.map_map (algebraMap R A) (algebraMap A Sr)).symm
      _ ≤ (r.under A).map (algebraMap A Sr) := Ideal.map_mono hpA
  let Ip : Ideal Sr :=
    (p.map (algebraMap R S)).map (algebraMap S Sr)
  have hIpI : Ip = I := by
    dsimp only [Ip, I]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sr]
  let eLocal₀ :=
    Ideal.Fiber.localizationAlgEquivQuotientOverLocalizedSource p qT.asIdeal
  change L ≃ₐ[Sr] Sr ⧸ Ip at eLocal₀
  let eLocal : L ≃ₐ[Sr] Sr ⧸ I :=
    eLocal₀.trans (Ideal.quotientEquivAlgOfEq Sr hIpI)
  have hquot : I ≤ J.comap (AlgHom.id A Sr) := by
    intro x hx
    change x ∈ J
    exact hIJ hx
  let π : (Sr ⧸ I) →ₐ[A] (Sr ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id A Sr) hquot
  let Φ : L →ₐ[A] (Sr ⧸ J) :=
    π.comp (eLocal.restrictScalars A).toAlgHom
  have hΦ : Function.Surjective Φ := by
    exact (Ideal.quotientMap_surjective (f := AlgHom.id A Sr)
      (J := I) (I := J) (H := hquot)
      Function.surjective_id).comp eLocal.surjective
  haveI hweak : Algebra.WeaklyQuasiFiniteAt A r := by
    rw [Algebra.weaklyQuasiFiniteAt_iff]
    exact Algebra.QuasiFinite.of_surjective_algHom (S := L) (T := Sr ⧸ J) Φ hΦ
  have hqf : Algebra.QuasiFiniteAt A r :=
    Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt r
  simpa only [hrq] using hqf

/-- A finite injective Noether normalization of the coefficient fibre can first be rescaled
so that its parameters lift to `S`; the resulting evaluation map is quasi-finite at `q`. -/
theorem quasiFiniteAt_aeval_of_finite_fibre_normalization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (n : ℕ)
    (g : MvPolynomial (Fin n) (q.under R).ResidueField →ₐ[(q.under R).ResidueField]
      (q.under R).Fiber S)
    (hg_injective : Function.Injective g) (hg_finite : g.Finite) :
    ∃ s : Fin n → S,
      let f := MvPolynomial.aeval s
      letI : Algebra (MvPolynomial (Fin n) R) S := f.toAlgebra
      Algebra.QuasiFiniteAt (MvPolynomial (Fin n) R) q := by
  obtain ⟨s, c, g', hg'_injective, hg'_finite, hg'_eq, hg'_X, hcompat⟩ :=
    Ideal.Fiber.exists_lifted_finite_injective_mvPolynomial
      (q.under R) n g hg_injective hg_finite
  exact ⟨s, quasiFiniteAt_aeval_of_finite_fibre_map q n s g' hg'_finite hcompat⟩

end MvPolynomial

end

end
