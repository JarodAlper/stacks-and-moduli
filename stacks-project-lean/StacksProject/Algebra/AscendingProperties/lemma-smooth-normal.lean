module

public import StacksProject.Algebra.AscendingProperties.Normality
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.RingHom.Bijective

/-!
# Normality ascends along smooth ring maps

This file formalizes Stacks Project tag **033C**
(`algebra-lemma-smooth-normal`) from §`0336` (Ascending properties) of
`algebra.tex`.

The proof is local on the target.  After localizing the base and passing to a
standard-étale chart, smooth base change for integral closure identifies the
integral closure of the local target inside its generic fiber.  The generic
fiber is a reduced Artinian local ring, hence a field.  This proves that every
target stalk is an integrally closed domain, without a Noetherian hypothesis.
-/

@[expose] public noncomputable section

universe u

open Polynomial IsLocalRing
open scoped TensorProduct

/-- An idempotent in an algebra is integral over the base ring. -/
private lemma isIntegral_of_isIdempotentElem
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] (x : S) (hx : IsIdempotentElem x) : IsIntegral R x := by
  have hdeg : (X : R[X]).degree < (X ^ 2 : R[X]).degree := by simp
  have hmonic : (X ^ 2 - X : R[X]).Monic := (monic_X_pow 2).sub_of_left hdeg
  have hnat : (X ^ 2 - X : R[X]).natDegree = 2 :=
    (natDegree_sub_eq_left_of_natDegree_lt
      (by rw [natDegree_X, natDegree_X_pow]; omega)).trans
      (natDegree_X_pow (R := R) 2)
  refine IsIntegral.of_aeval_monic hmonic (by simp [hnat]) ?_
  convert isIntegral_zero (R := R)
  simpa [IsIdempotentElem, pow_two] using sub_eq_zero.mpr hx

/-- A reduced Artinian ring is local if the integral closure of a subring in it
is local. -/
private theorem isLocalRing_of_integralClosure_isLocal_of_isArtinian_of_isReduced
    (B C : Type u) [CommRing B] [Nontrivial B] [CommRing C] [Nontrivial C]
    [Algebra B C] [IsLocalRing (integralClosure B C)] [IsArtinianRing C]
    [IsReduced C] : IsLocalRing C := by
  classical
  letI : Nonempty (MaximalSpectrum C) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal C
    exact ⟨⟨m, hm⟩⟩
  have hsub : Subsingleton (MaximalSpectrum C) := ⟨by
    intro m n
    by_contra hmn
    let v : (i : MaximalSpectrum C) → C ⧸ i.asIdeal := Pi.single m 1
    let e : C := (IsArtinianRing.equivPi C).symm v
    have hv : IsIdempotentElem v := by
      change v * v = v
      ext i
      by_cases hi : i = m
      · subst i
        simp [v]
      · simp [v, Pi.single_apply, hi]
    have he : IsIdempotentElem e := by
      apply (IsArtinianRing.equivPi C).injective
      simpa [IsIdempotentElem, e] using hv
    let z : integralClosure B C := ⟨e, isIntegral_of_isIdempotentElem e he⟩
    have hz : IsIdempotentElem z := by
      apply Subtype.ext
      exact he
    have hz01 : z = 0 ∨ z = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self z with hunit | hunit
      · right
        apply hunit.mul_left_cancel
        simpa [IsIdempotentElem] using hz
      · left
        apply hunit.mul_left_cancel
        rw [sub_mul, one_mul, show z * z = z from hz, sub_self, mul_zero]
    have he01 : e = 0 ∨ e = 1 := hz01.imp
      (fun h ↦ congrArg Subtype.val h) (fun h ↦ congrArg Subtype.val h)
    rcases he01 with he0 | he1
    · have hmap := congrArg (IsArtinianRing.equivPi C) he0
      dsimp only [e] at hmap
      rw [AlgEquiv.apply_symm_apply, map_zero] at hmap
      have := congrFun hmap m
      simp [v] at this
    · have hmap := congrArg (IsArtinianRing.equivPi C) he1
      dsimp only [e] at hmap
      rw [AlgEquiv.apply_symm_apply, map_one] at hmap
      have := congrFun hmap n
      have hnm : n ≠ m := fun h ↦ hmn h.symm
      simp [v, hnm] at this⟩
  letI : Subsingleton (MaximalSpectrum C) := hsub
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- A polynomial ring in finitely many variables over an integrally closed
domain is integrally closed. -/
private theorem isIntegrallyClosed_mvPolynomial_fin
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (n : ℕ) :
    IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero =>
      exact IsIntegrallyClosed.of_equiv
        (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv
  | succ n ih =>
      letI : IsIntegrallyClosed (MvPolynomial (Fin n) A) := ih
      letI : IsIntegrallyClosed (Polynomial (MvPolynomial (Fin n) A)) := inferInstance
      exact IsIntegrallyClosed.of_equiv
        (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

/-- If smooth base change for integral closure is bijective, the integral
closure of a local target in its generic fiber is local. -/
private theorem integralClosure_genericFiber_isLocal_of_bijective
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Flat A B]
    (hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure A B (FractionRing A))) :
    IsLocalRing (integralClosure B (B ⊗[A] FractionRing A)) := by
  let eIC : integralClosure A (FractionRing A) ≃ₐ[A] A :=
    (Subalgebra.equivOfEq _ _
      (IsIntegrallyClosed.integralClosure_eq_bot A (FractionRing A))).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective A (FractionRing A)))
  let eSource : B ⊗[A] integralClosure A (FractionRing A) ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) eIC).trans
      ((Algebra.TensorProduct.rid A B B).restrictScalars A)
  letI : IsLocalRing (B ⊗[A] integralClosure A (FractionRing A)) :=
    eSource.symm.toRingEquiv.isLocalRing
  exact (AlgEquiv.ofBijective
    (TensorProduct.toIntegralClosure A B (FractionRing A)) hcomp).toRingEquiv.isLocalRing

/-- Under the local essentially-étale hypotheses, the generic fiber is a
field. -/
private theorem isField_genericFiber_of_formallyUnramified_of_local
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Flat A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure A B (FractionRing A))) :
    IsField (B ⊗[A] FractionRing A) := by
  let C := B ⊗[A] FractionRing A
  letI : Nontrivial C :=
    (Algebra.TensorProduct.includeLeft_injective
      (R := A) (S := B) (A := B) (B := FractionRing A)
      (IsFractionRing.injective A (FractionRing A))).nontrivial
  letI : Algebra (FractionRing A) C := Algebra.TensorProduct.rightAlgebra
  let e : FractionRing A ⊗[A] B ≃ₐ[FractionRing A] C :=
    { toRingEquiv := (Algebra.TensorProduct.comm A (FractionRing A) B).toRingEquiv
      commutes' := by
        intro x
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        simp }
  letI : Algebra.FormallyUnramified (FractionRing A) C :=
    Algebra.FormallyUnramified.of_equiv e
  letI : Algebra.EssFiniteType (FractionRing A) C :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  letI : IsReduced C :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) C
  letI : Module.Finite (FractionRing A) C :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing A) C
  letI : IsArtinianRing C := IsArtinianRing.of_finite (FractionRing A) C
  letI : IsLocalRing (integralClosure B C) :=
    integralClosure_genericFiber_isLocal_of_bijective A B hcomp
  letI : IsLocalRing C :=
    isLocalRing_of_integralClosure_isLocal_of_isArtinian_of_isReduced B C
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing C

/-- Bijectivity of smooth base change for integral closure identifies a local
target with its integral closure in the generic fiber. -/
private theorem isIntegrallyClosedIn_genericFiber_of_bijective
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Flat A B]
    (hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure A B (FractionRing A))) :
    IsIntegrallyClosedIn B (B ⊗[A] FractionRing A) := by
  let C := B ⊗[A] FractionRing A
  have hIC : integralClosure A (FractionRing A) = ⊥ :=
    IsIntegrallyClosed.integralClosure_eq_bot A (FractionRing A)
  have hAIC : Function.Bijective
      (algebraMap A (integralClosure A (FractionRing A))) := by
    refine ⟨FaithfulSMul.algebraMap_injective _ _, ?_⟩
    intro z
    have hz : (z : FractionRing A) ∈ (⊥ : Subalgebra A (FractionRing A)) := by
      rw [← hIC]
      exact z.property
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hz
    exact ⟨a, Subtype.ext ha⟩
  have hleft : Function.Bijective
      (Algebra.TensorProduct.includeLeft :
        B →ₐ[B] B ⊗[A] integralClosure A (FractionRing A)) :=
    Algebra.TensorProduct.includeLeft_bijective
      (R := A) (S := B) (A := B)
      (B := integralClosure A (FractionRing A)) hAIC
  let φ : B →ₐ[B] integralClosure B C :=
    (TensorProduct.toIntegralClosure A B (FractionRing A)).comp
      (Algebra.TensorProduct.includeLeft :
        B →ₐ[B] B ⊗[A] integralClosure A (FractionRing A))
  have hφ : Function.Bijective φ := hcomp.comp hleft
  have hφeq : φ = Algebra.ofId B (integralClosure B C) := by
    ext
  have hsurj : Function.Surjective
      (Algebra.ofId B (integralClosure B C)) := by
    rw [← hφeq]
    exact hφ.2
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective
      (R := A) (S := B) (A := B) (B := FractionRing A)
      (IsFractionRing.injective A (FractionRing A))
  · intro x hx
    obtain ⟨b, hb⟩ := hsurj ⟨x, hx⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- Under the local essentially-étale hypotheses, the generic fiber is a
fraction field of the target. -/
private theorem isFractionRing_genericFiber_of_formallyUnramified_of_local
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Flat A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure A B (FractionRing A))) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  let C := B ⊗[A] FractionRing A
  letI : Algebra (FractionRing A) C := Algebra.TensorProduct.rightAlgebra
  letI : Field C :=
    IsField.toField
      (isField_genericFiber_of_formallyUnramified_of_local A B hcomp)
  have hinjK : Function.Injective (algebraMap (FractionRing A) C) :=
    (algebraMap (FractionRing A) C).injective
  letI : FaithfulSMul (FractionRing A) C :=
    (faithfulSMul_iff_algebraMap_injective (FractionRing A) C).mpr hinjK
  have hinj : Function.Injective (algebraMap B C) :=
    Algebra.TensorProduct.includeLeft_injective
      (R := A) (S := B) (A := B) (B := FractionRing A)
      (IsFractionRing.injective A (FractionRing A))
  letI : FaithfulSMul B C :=
    (faithfulSMul_iff_algebraMap_injective B C).mpr hinj
  apply IsFractionRing.of_field B C
  intro z
  have hrat : ∃ x y : B,
      algebraMap B C y ≠ 0 ∧ z = algebraMap B C x / algebraMap B C y := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, by simp, by simp⟩
    | tmul b k =>
      obtain ⟨a, d, hd, hk⟩ := IsFractionRing.div_surjective A k
      have hdK : algebraMap A (FractionRing A) d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have hdC : algebraMap B C (algebraMap A B d) ≠ 0 := by
        rw [show algebraMap B C (algebraMap A B d) =
          algebraMap (FractionRing A) C (algebraMap A (FractionRing A) d) by
            change (algebraMap A B d) ⊗ₜ[A] 1 =
              1 ⊗ₜ[A] (algebraMap A (FractionRing A) d)
            simpa only [Algebra.smul_def, one_mul, mul_one] using
              (TensorProduct.smul_tmul (R := A) (R' := A) (M := B)
                (N := FractionRing A) d (1 : B) (1 : FractionRing A))]
        simpa only [map_zero] using hinjK.ne hdK
      refine ⟨b * algebraMap A B a, algebraMap A B d, hdC, ?_⟩
      rw [← hk]
      apply (eq_div_iff hdC).2
      change (b ⊗ₜ[A] _) * ((algebraMap A B d) ⊗ₜ[A] 1) =
        (b * algebraMap A B a) ⊗ₜ[A] 1
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [mul_comm b (algebraMap A B d), mul_comm b (algebraMap A B a)]
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul]
      congr 1
      simpa only [Algebra.smul_def, mul_one] using
        mul_div_cancel₀ (algebraMap A (FractionRing A) a) hdK
    | add z w hz hw =>
      obtain ⟨xz, yz, hyz, hz⟩ := hz
      obtain ⟨xw, yw, hyw, hw⟩ := hw
      refine ⟨xz * yw + xw * yz, yz * yw,
        by simpa using mul_ne_zero hyz hyw, ?_⟩
      rw [hz, hw]
      push_cast
      simpa [mul_comm] using
        div_add_div (algebraMap B C xz) (algebraMap B C xw) hyz hyw
  obtain ⟨x, y, _, hxy⟩ := hrat
  exact ⟨x, y, hxy⟩

/-- A local essentially-étale algebra over an integrally closed domain is
normal when smooth base change for integral closure is bijective. -/
private theorem isNormalRing_of_formallyUnramified_of_isLocalRing
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Flat A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure A B (FractionRing A))) :
    IsNormalRing B := by
  let C := B ⊗[A] FractionRing A
  letI : IsFractionRing B C :=
    isFractionRing_genericFiber_of_formallyUnramified_of_local A B hcomp
  letI : Field C :=
    IsField.toField
      (isField_genericFiber_of_formallyUnramified_of_local A B hcomp)
  letI : IsDomain B := (IsFractionRing.injective B C).isDomain
  letI : IsIntegrallyClosed B :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).mpr
      (isIntegrallyClosedIn_genericFiber_of_bijective A B hcomp)
  exact IsNormalRing.of_isDomain_of_isIntegrallyClosed

/-- Smooth base change for integral closure remains bijective after localizing
at a prime of the target and its contraction in the source. -/
theorem toIntegralClosure_bijective_of_smooth_atPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (Q : Ideal S) [Q.IsPrime] :
    let p := Q.under R
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver p Q
    Function.Bijective
      (TensorProduct.toIntegralClosure (Localization.AtPrime p)
        (Localization.AtPrime Q) (FractionRing (Localization.AtPrime p))) := by
  let p := Q.under R
  let A := Localization.AtPrime p
  let B := Localization.AtPrime Q
  let D := A ⊗[R] S
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver p Q
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.Smooth A D := Algebra.Smooth.baseChange R S A
  let M : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  letI : IsLocalization M D := IsLocalization.tensorRight A p.primeCompl
  have hMQ : M ≤ Q.primeCompl := by
    rintro y ⟨x, hx, rfl⟩
    change algebraMap R S x ∉ Q
    intro hQ
    exact hx hQ
  letI : Algebra D B :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D B M Q.primeCompl hMQ
  letI : IsScalarTower S D B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      D B M Q.primeCompl hMQ
  have hADB : algebraMap A B = (algebraMap D B).comp (algebraMap A D) := by
    apply IsLocalization.ringHom_ext
      (R := R) (S := A) (P := B) p.primeCompl
    ext x
    simp only [RingHom.comp_apply]
    calc
      algebraMap A B (algebraMap R A x) = algebraMap R B x :=
        (IsScalarTower.algebraMap_apply R A B x).symm
      _ = algebraMap S B (algebraMap R S x) :=
        IsScalarTower.algebraMap_apply R S B x
      _ = algebraMap D B (algebraMap S D (algebraMap R S x)) :=
        IsScalarTower.algebraMap_apply S D B (algebraMap R S x)
      _ = algebraMap D B (algebraMap A D (algebraMap R A x)) := by
        congr 1
        exact (IsScalarTower.algebraMap_apply R S D x).symm.trans
          (IsScalarTower.algebraMap_apply R A D x)
  letI : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq' hADB
  let N : Submonoid D := Q.primeCompl.map (algebraMap S D)
  letI : IsLocalization N B :=
    IsLocalization.isLocalization_of_submonoid_le D B M Q.primeCompl hMQ
  exact TensorProduct.toIntegralClosure_bijective_of_tower
    (R := A) (S := D) (T := B) (B := FractionRing A)
    TensorProduct.toIntegralClosure_bijective_of_smooth
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization N)

/-- A localization at a prime of a smooth algebra over an integrally closed
domain is a normal local ring. -/
theorem isNormalRing_localizationAtPrime_of_smooth_of_domain
    (A S : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing S] [Algebra A S] [Algebra.Smooth A S]
    (Q : Ideal S) [Q.IsPrime] : IsNormalRing (Localization.AtPrime Q) := by
  obtain ⟨f, hfQ, n, hP, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := Q)
  let Sf := Localization.Away f
  let Qf := Q.map (algebraMap S Sf)
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid S) : Set S) (Q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfQ
  haveI : Qf.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (.powers f) Sf Q inferInstance hdisj
  let P := MvPolynomial (Fin n) A
  letI : Algebra P Sf := hP
  letI : IsScalarTower A P Sf := hTower
  letI : Algebra.IsStandardEtale P Sf := hEtale
  let p := Qf.under P
  let B := Localization.AtPrime Qf
  let R := Localization.AtPrime p
  letI : IsDomain P := inferInstance
  letI : IsIntegrallyClosed P := isIntegrallyClosed_mvPolynomial_fin A n
  letI : IsDomain R := inferInstance
  letI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization (R := P) R p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  letI : Algebra R B := Localization.AtPrime.algebraOfLiesOver p Qf
  letI : Module.Flat R B := Module.Flat.atPrime p Qf rfl
  letI : Algebra.FormallyUnramified R B := by
    exact Algebra.FormallyUnramified.localization_base p.primeCompl
  letI : Algebra.EssFiniteType P B := Algebra.EssFiniteType.comp P Sf B
  letI : Algebra.EssFiniteType R B := Algebra.EssFiniteType.of_comp P R B
  have hcomp : Function.Bijective
      (TensorProduct.toIntegralClosure R B (FractionRing R)) :=
    toIntegralClosure_bijective_of_smooth_atPrime P Sf Qf
  letI : IsNormalRing B :=
    isNormalRing_of_formallyUnramified_of_isLocalRing R B hcomp
  have hunder : Qf.under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint
      (.powers f) Sf inferInstance hdisj
  letI : IsLocalization.AtPrime B Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (.powers f) B Qf
    exact hunder.symm
  let e : B ≃ₐ[S] Localization.AtPrime Q :=
    IsLocalization.algEquiv Q.primeCompl B (Localization.AtPrime Q)
  letI : IsDomain B := IsNormalRing.isDomain_of_isLocalRing
  letI : IsIntegrallyClosed B := IsNormalRing.isIntegrallyClosed_of_isLocalRing
  letI : IsDomain (Localization.AtPrime Q) := e.symm.injective.isDomain
  letI : IsIntegrallyClosed (Localization.AtPrime Q) :=
    IsIntegrallyClosed.of_equiv
      (R := B) (S := Localization.AtPrime Q) e.toRingEquiv
  exact IsNormalRing.of_isDomain_of_isIntegrallyClosed

/-- A localization at a prime of a smooth algebra over a normal ring is a
normal local ring. -/
theorem isNormalRing_localizationAtPrime_of_smooth
    (R S : Type u) [CommRing R] [IsNormalRing R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (Q : Ideal S) [Q.IsPrime] : IsNormalRing (Localization.AtPrime Q) := by
  let p := Q.under R
  let A := Localization.AtPrime p
  let D := A ⊗[R] S
  letI : IsDomain A := IsNormalRing.isDomain_localization p
  letI : IsIntegrallyClosed A := IsNormalRing.isIntegrallyClosed_localization p
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.Smooth A D := Algebra.Smooth.baseChange R S A
  let M : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  letI : IsLocalization M D := IsLocalization.tensorRight A p.primeCompl
  have hdisj : Disjoint (M : Set S) (Q : Set S) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hyQ
    exact hx hyQ
  let QD := Q.map (algebraMap S D)
  haveI : QD.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M D Q inferInstance hdisj
  letI : IsNormalRing (Localization.AtPrime QD) :=
    isNormalRing_localizationAtPrime_of_smooth_of_domain A D QD
  have hunder : QD.under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M D inferInstance hdisj
  letI : IsLocalization.AtPrime (Localization.AtPrime QD) Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime QD) QD
    exact hunder.symm
  let e : Localization.AtPrime QD ≃ₐ[S] Localization.AtPrime Q :=
    IsLocalization.algEquiv Q.primeCompl
      (Localization.AtPrime QD) (Localization.AtPrime Q)
  letI : IsDomain (Localization.AtPrime QD) :=
    IsNormalRing.isDomain_of_isLocalRing (R := Localization.AtPrime QD)
  letI : IsIntegrallyClosed (Localization.AtPrime QD) :=
    IsNormalRing.isIntegrallyClosed_of_isLocalRing
      (R := Localization.AtPrime QD)
  letI : IsDomain (Localization.AtPrime Q) := e.symm.injective.isDomain
  letI : IsIntegrallyClosed (Localization.AtPrime Q) :=
    IsIntegrallyClosed.of_equiv
      (R := Localization.AtPrime QD) (S := Localization.AtPrime Q) e.toRingEquiv
  exact IsNormalRing.of_isDomain_of_isIntegrallyClosed

/-- **Stacks 033C** (`algebra-lemma-smooth-normal`): normality ascends along
smooth maps of rings. -/
@[stacks 033C]
theorem isNormalRing_of_smooth
    (R S : Type u) [CommRing R] [IsNormalRing R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S] : IsNormalRing S where
  isDomain_localization Q _ := by
    letI : IsNormalRing (Localization.AtPrime Q) :=
      isNormalRing_localizationAtPrime_of_smooth R S Q
    exact IsNormalRing.isDomain_of_isLocalRing
  isIntegrallyClosed_localization Q _ := by
    letI : IsNormalRing (Localization.AtPrime Q) :=
      isNormalRing_localizationAtPrime_of_smooth R S Q
    letI : IsDomain (Localization.AtPrime Q) :=
      IsNormalRing.isDomain_of_isLocalRing
    exact IsNormalRing.isIntegrallyClosed_of_isLocalRing
