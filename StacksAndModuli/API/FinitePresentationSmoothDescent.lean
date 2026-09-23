module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.Etale
public import StacksAndModuli.API.FiniteTypeSmoothDescent

/-!
# Descent of finite presentation through a smooth faithfully flat factor

If `R → A → B`, the composite `R → B` is finitely presented, and `A → B` is
smooth and faithfully flat, then `R → A` is finitely presented.  The proof spreads the
smooth algebra out over a finitely presented coefficient algebra and then applies faithfully
flat base-change descent.

## Main results

* `Algebra.FinitePresentation.of_faithfullyFlat_baseChange`
* `Algebra.FinitePresentation.of_smooth_of_faithfullyFlat`
* `RingHom.FinitePresentation.of_comp_of_smooth_of_faithfullyFlat`
-/

@[expose] public section

open TensorProduct

universe u

namespace Algebra.FinitePresentation

variable {R C A D : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing D]
  [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
  [Algebra C D]

theorem of_faithfullyFlat_baseChange
    [Algebra.FinitePresentation R C] [Algebra.FinitePresentation C D]
    [Module.Flat C D] [Module.FaithfullyFlat A (A ⊗[C] D)]
    [Algebra.FinitePresentation R (A ⊗[C] D)] :
    Algebra.FinitePresentation R A := by
  classical
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap C D))) := by
    simpa using PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := C) (S := D) _ isOpen_univ
  obtain ⟨sI, hsI⟩ := (PrimeSpectrum.isOpen_iff _).mp hopen
  have hzero : (Set.range (PrimeSpectrum.comap (algebraMap C D)))ᶜ =
      PrimeSpectrum.zeroLocus ((Ideal.span sI : Ideal C) : Set C) := by
    rw [hsI, PrimeSpectrum.zeroLocus_span]
  have hIA : Ideal.span (algebraMap C A '' sI) = ⊤ := by
    rw [← Ideal.map_span]
    by_contra hne
    obtain ⟨mIdeal, hmIdeal, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI : mIdeal.IsPrime := hmIdeal.isPrime
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := A) (B := A ⊗[C] D) ⟨mIdeal, inferInstance⟩
    have hcomp : (algebraMap A (A ⊗[C] D)).comp (algebraMap C A) =
        (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := D)).toRingHom.comp
          (algebraMap C D) := by
      ext c
      simp
    have hmem : PrimeSpectrum.comap (algebraMap C A)
        (⟨mIdeal, inferInstance⟩ : PrimeSpectrum A) ∈
        Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      refine ⟨PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := D)).toRingHom Q, ?_⟩
      rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hcomp]
    have hnotin : PrimeSpectrum.comap (algebraMap C A)
        (⟨mIdeal, inferInstance⟩ : PrimeSpectrum A) ∉
        PrimeSpectrum.zeroLocus ((Ideal.span sI : Ideal C) : Set C) := by
      rw [← hzero]
      simpa using hmem
    rw [PrimeSpectrum.mem_zeroLocus] at hnotin
    exact hnotin (Ideal.map_le_iff_le_comap.mp hle)
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp
    (show (1 : A) ∈ Ideal.span (algebraMap C A '' sI) from
      hIA ▸ Submodule.mem_top)
  choose b hb hb' using fun i : Fin N ↦ (g i).2
  let q : MvPolynomial (Fin N) C :=
    ∑ i, MvPolynomial.X i * MvPolynomial.C (b i) - 1
  let I : Ideal (MvPolynomial (Fin N) C) := Ideal.span {q}
  let C₁ := MvPolynomial (Fin N) C ⧸ I
  letI : CommRing C₁ := inferInstance
  letI : Algebra C C₁ := inferInstance
  have hqmem : q ∈ I := Ideal.subset_span (Set.mem_singleton q)
  have hrel :
      (∑ i, Ideal.Quotient.mk I (MvPolynomial.X i) * algebraMap C C₁ (b i)) = 1 := by
    change (∑ i, Ideal.Quotient.mk I (MvPolynomial.X i) *
      Ideal.Quotient.mk I (MvPolynomial.C (b i))) = 1
    have hqzero : Ideal.Quotient.mk I q = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hqmem
    apply sub_eq_zero.mp
    simpa [q] using hqzero
  let ev : MvPolynomial (Fin N) C →ₐ[C] A := MvPolynomial.aeval f
  have hevq : ev q = 0 := by
    dsimp only [ev, q]
    simp only [map_sub, map_sum, map_mul, map_one, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C]
    apply sub_eq_zero.mpr
    simpa [← hb', Algebra.smul_def, mul_comm] using hfg
  have hIle : I ≤ RingHom.ker ev.toRingHom := by
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact RingHom.mem_ker.mpr hevq
  have hIker : ∀ x, x ∈ I → ev x = 0 := by
    intro x hx
    exact RingHom.mem_ker.mp (hIle hx)
  let α : C₁ →ₐ[C] A := Ideal.Quotient.liftₐ I ev hIker
  letI : Algebra C₁ A := α.toRingHom.toAlgebra
  haveI : IsScalarTower C C₁ A := IsScalarTower.of_algebraMap_eq fun c ↦ by
    exact (α.commutes c).symm
  haveI : IsScalarTower R C₁ A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R C A,
      IsScalarTower.algebraMap_apply R C C₁,
      IsScalarTower.algebraMap_apply C C₁ A]
  let D₁ := C₁ ⊗[C] D
  letI : CommRing D₁ := inferInstance
  letI : Algebra C₁ D₁ := inferInstance
  haveI : Module.Flat C₁ D₁ := Module.Flat.baseChange C C₁ D
  haveI : Module.FaithfullyFlat C₁ D₁ := by
    refine Module.FaithfullyFlat.of_comap_surjective fun q₁ ↦
      mem_range_comap_tensorProduct q₁ ?_
    by_contra hcon
    have hsub : ((Ideal.span sI : Ideal C) : Set C) ⊆
        (PrimeSpectrum.comap (algebraMap C C₁) q₁).asIdeal := by
      rw [← PrimeSpectrum.mem_zeroLocus, ← hzero]
      exact hcon
    refine q₁.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
    rw [← hrel]
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ ?_
    exact hsub (Ideal.subset_span (hb i))
  haveI : Algebra.FinitePresentation R C₁ := by
    haveI : Algebra.FinitePresentation C (MvPolynomial (Fin N) C) := inferInstance
    have hIfg : I.FG := by
      exact ⟨{q}, by simp [I]⟩
    haveI : Algebra.FinitePresentation C C₁ :=
      Algebra.FinitePresentation.quotient hIfg
    exact Algebra.FinitePresentation.trans R C C₁
  haveI : Algebra.FinitePresentation R D₁ := by
    haveI : Algebra.FinitePresentation C₁ D₁ := inferInstance
    exact Algebra.FinitePresentation.trans R C₁ D₁
  letI : Algebra D₁ (A ⊗[C₁] D₁) := Algebra.TensorProduct.rightAlgebra
  let eComm : D₁ ⊗[C₁] A ≃ₐ[D₁] A ⊗[C₁] D₁ :=
    Algebra.TensorProduct.commRight C₁ D₁ A
  let eCancel : A ⊗[C₁] D₁ ≃ₐ[A] A ⊗[C] D :=
    Algebra.TensorProduct.cancelBaseChange C C₁ A A D
  let e : D₁ ⊗[C₁] A ≃ₐ[R] A ⊗[C] D :=
    ((eComm.restrictScalars C₁).restrictScalars R).trans
      ((eCancel.restrictScalars C₁).restrictScalars R)
  haveI : Algebra.FinitePresentation R (D₁ ⊗[C₁] A) :=
    Algebra.FinitePresentation.equiv e.symm
  haveI : Algebra.FinitePresentation D₁ (D₁ ⊗[C₁] A) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R D₁ _
  haveI : Algebra.FinitePresentation C₁ A :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat D₁
  exact Algebra.FinitePresentation.trans R C₁ A

/-- Finite presentation descends through a smooth faithfully flat factor. -/
theorem of_smooth_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.Smooth A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation R B] : Algebra.FinitePresentation R A := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨eB⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ A B
  letI : Algebra.Smooth A₀ B₀ := hB₀
  haveI : Algebra.FinitePresentation ℤ A₀ :=
    Algebra.FinitePresentation.of_finiteType.mp
      ((Subalgebra.fg_iff_finiteType A₀).mp hA₀)
  let C := R ⊗[ℤ] A₀
  letI : CommRing C := inferInstance
  letI : Algebra R C := inferInstance
  letI : Algebra A₀ C := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower ℤ A₀ C := Algebra.TensorProduct.right_isScalarTower
  haveI : Algebra.FinitePresentation R C := inferInstance
  let θ : C →ₐ[R] A := Algebra.TensorProduct.lift
    (Algebra.ofId R A) (IsScalarTower.toAlgHom ℤ A₀ A) (fun _ _ ↦ Commute.all _ _)
  letI : Algebra C A := θ.toRingHom.toAlgebra
  haveI : IsScalarTower R C A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact (θ.commutes r).symm
  haveI : IsScalarTower A₀ C A := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A₀ A a = θ (algebraMap A₀ C a)
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    dsimp only [θ]
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  let D := C ⊗[A₀] B₀
  letI : CommRing D := inferInstance
  letI : Algebra C D := inferInstance
  haveI : Algebra.Smooth C D := inferInstance
  haveI : Module.Flat C D := inferInstance
  haveI : Algebra.FinitePresentation C D := inferInstance
  let eCancel : A ⊗[C] D ≃ₐ[A] A ⊗[A₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange A₀ C A A B₀
  let e : A ⊗[C] D ≃ₐ[A] B := eCancel.trans eB.symm
  haveI : Module.FaithfullyFlat A (A ⊗[C] D) :=
    Module.FaithfullyFlat.of_linearEquiv A B e.toLinearEquiv
  haveI : Algebra.FinitePresentation R (A ⊗[C] D) :=
    Algebra.FinitePresentation.equiv ((e.symm).restrictScalars R)
  exact of_faithfullyFlat_baseChange (R := R) (C := C) (A := A) (D := D)

end Algebra.FinitePresentation

namespace RingHom.FinitePresentation

/-- If `R → A → B`, the composite is finitely presented, and `A → B` is smooth and
faithfully flat, then `R → A` is finitely presented. -/
theorem of_comp_of_smooth_of_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] (f : R →+* A) (g : A →+* B)
    (hcomp : (g.comp f).FinitePresentation) (hsmooth : g.Smooth)
    (hff : g.FaithfullyFlat) : f.FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.of_smooth_of_faithfullyFlat (B := B)

/-- The étale special case of
`RingHom.FinitePresentation.of_comp_of_smooth_of_faithfullyFlat`. -/
theorem of_comp_of_etale_of_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] (f : R →+* A) (g : A →+* B)
    (hcomp : (g.comp f).FinitePresentation) (hetale : g.Etale)
    (hff : g.FaithfullyFlat) : f.FinitePresentation :=
  of_comp_of_smooth_of_faithfullyFlat f g hcomp
    ((g.etale_iff_formallyUnramified_and_smooth).mp hetale).2 hff

end RingHom.FinitePresentation
