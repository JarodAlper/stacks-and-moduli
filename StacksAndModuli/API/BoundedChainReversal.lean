module

public import StacksAndModuli.API.LocalAlgebraFibreExactComplex
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Reversing a bounded chain complex

A chain complex concentrated in degrees `0, …, N` can be read backwards as a cochain
complex: cochain degree `j` is chain degree `N - j`, and all cochain terms above `N` are
zero.  This file packages that elementary construction for complexes of modules, together
with its differential, boundedness, flatness, and finiteness interfaces.

The construction is intended for local forms of Stacks Project tag 00MI, whose natural
input is a bounded chain resolution while the reusable descending exactness machinery in
`ProjectiveGradedFlatComplex` is cochain-oriented.

Main declaration:

* `ChainComplex.reverseUpToCochain`;
* `ChainComplex.reverseUpToCochain_exact_baseChange_of_exact`;
* `ChainComplex.reverseUpToCochain_exact_of_localAlgebra`;
* `ChainComplex.reverseUpToCochain_flat_syzygy_of_localAlgebra`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open scoped TensorProduct

namespace ChainComplex

open Algebra TensorProduct
open AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R]

/-- The object in cochain degree `j` of the reversal of a chain complex through degree
`N`.  Terms strictly above `N` are zero. -/
def reverseUpToCochainX
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) :
    ModuleCat.{u} R :=
  if j ≤ N then C.X (N - j) else ModuleCat.of R PUnit.{u + 1}

/-- The differential of the bounded reversal, including the transports into and out of
the conditionally chosen terms. -/
noncomputable def reverseUpToCochainD
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) :
    reverseUpToCochainX C N j ⟶ reverseUpToCochainX C N (j + 1) :=
  if h : j < N then
    eqToHom (show reverseUpToCochainX C N j = C.X (N - j) by
      simp [reverseUpToCochainX, Nat.le_of_lt h]) ≫
      C.d (N - j) (N - (j + 1)) ≫
      eqToHom (show reverseUpToCochainX C N (j + 1) = C.X (N - (j + 1)) by
        have hj₁ : j + 1 ≤ N := h
        simp [reverseUpToCochainX, hj₁]).symm
  else 0

/-- Reverse a chain complex through degree `N` and extend the result by zero in cochain
degrees above `N`. -/
noncomputable def reverseUpToCochain
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (reverseUpToCochainX C N)
    (reverseUpToCochainD C N)
    (fun j ↦ by
      by_cases h₀ : j < N
      · by_cases h₁ : j + 1 < N
        · simp [reverseUpToCochainD, h₀, h₁, Category.assoc]
        · simp [reverseUpToCochainD, h₀, h₁]
      · simp [reverseUpToCochainD, h₀])

@[simp]
theorem reverseUpToCochain_X_of_le
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : j ≤ N) :
    (reverseUpToCochain C N).X j = C.X (N - j) := by
  simp [reverseUpToCochain, reverseUpToCochainX, hj]

@[simp]
theorem reverseUpToCochain_X_of_lt
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : N < j) :
    (reverseUpToCochain C N).X j = ModuleCat.of R PUnit.{u + 1} := by
  simp [reverseUpToCochain, reverseUpToCochainX, Nat.not_le.mpr hj]

@[simp]
theorem reverseUpToCochain_d_of_lt
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : j < N) :
    (reverseUpToCochain C N).d j (j + 1) =
      eqToHom (reverseUpToCochain_X_of_le C N j (Nat.le_of_lt hj)) ≫
        C.d (N - j) (N - (j + 1)) ≫
        eqToHom (reverseUpToCochain_X_of_le C N (j + 1)
          (Nat.succ_le_iff.mpr hj)).symm := by
  simp [reverseUpToCochain, reverseUpToCochainD, hj]

@[simp]
theorem reverseUpToCochain_d_of_ge
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : N ≤ j) :
    (reverseUpToCochain C N).d j (j + 1) = 0 := by
  simp [reverseUpToCochain, reverseUpToCochainD, Nat.not_lt.mpr hj]

/-- The reversed cochain complex is zero above the chosen reversal bound. -/
theorem reverseUpToCochain_bounded
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : N < j) :
    Subsingleton ((reverseUpToCochain C N).X j) := by
  rw [reverseUpToCochain_X_of_lt C N j hj]
  infer_instance

/-- Degreewise flatness is preserved by bounded reversal. -/
theorem reverseUpToCochain_flat
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i : ℕ, Module.Flat R (C.X i))
    (N j : ℕ) :
    Module.Flat R ((reverseUpToCochain C N).X j) := by
  by_cases hj : j ≤ N
  · rw [reverseUpToCochain_X_of_le C N j hj]
    exact hflat (N - j)
  · rw [reverseUpToCochain_X_of_lt C N j (Nat.lt_of_not_ge hj)]
    infer_instance

/-- Degreewise finiteness is preserved by bounded reversal. -/
theorem reverseUpToCochain_finite
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ i : ℕ, Module.Finite R (C.X i))
    (N j : ℕ) :
    Module.Finite R ((reverseUpToCochain C N).X j) := by
  by_cases hj : j ≤ N
  · rw [reverseUpToCochain_X_of_le C N j hj]
    exact hfinite (N - j)
  · rw [reverseUpToCochain_X_of_lt C N j (Nat.lt_of_not_ge hj)]
    infer_instance

/-- Exactness of the corresponding two base-changed chain differentials gives exactness
at an interior degree of the base-changed bounded reversal. -/
theorem exactAtSucc_baseChange_reverseUpToCochain_of_exact
    {A : Type u} [CommRing A] [Algebra R A]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N j : ℕ) (hj : j + 1 < N)
    (h : Function.Exact
      (LinearMap.baseChange A (C.d (N - j) (N - (j + 1))).hom)
      (LinearMap.baseChange A (C.d (N - (j + 1)) (N - (j + 2))).hom)) :
    CochainComplex.ExactAtSucc
      (GradedModule.cochainBaseChange A (C.reverseUpToCochain N)) j := by
  let D := C.reverseUpToCochain N
  have hx₀ := C.reverseUpToCochain_X_of_le N j (by omega)
  have hx₁ := C.reverseUpToCochain_X_of_le N (j + 1) (by omega)
  have hx₂ := C.reverseUpToCochain_X_of_le N (j + 2) (by omega)
  let e₀ := ((eqToIso hx₀).toLinearEquiv.baseChange R A)
  let e₁ := ((eqToIso hx₁).toLinearEquiv.baseChange R A)
  let e₂ := ((eqToIso hx₂).toLinearEquiv.baseChange R A)
  have hcat₀₁ : eqToHom hx₀ ≫ C.d (N - j) (N - (j + 1)) =
      D.d j (j + 1) ≫ eqToHom hx₁ := by
    dsimp only [D]
    rw [C.reverseUpToCochain_d_of_lt N j (by omega)]
    simp
  have hcat₁₂ : eqToHom hx₁ ≫ C.d (N - (j + 1)) (N - (j + 2)) =
      D.d (j + 1) (j + 2) ≫ eqToHom hx₂ := by
    dsimp only [D]
    rw [C.reverseUpToCochain_d_of_lt N (j + 1) (by omega)]
    simp
  have h₀₁ :
      (LinearMap.baseChange A (C.d (N - j) (N - (j + 1))).hom) ∘ₗ
          (e₀ : (A ⊗[R] D.X j) →ₗ[A] A ⊗[R] C.X (N - j)) =
        (e₁ : (A ⊗[R] D.X (j + 1)) →ₗ[A] A ⊗[R] C.X (N - (j + 1))) ∘ₗ
          LinearMap.baseChange A (D.d j (j + 1)).hom := by
    change LinearMap.baseChange A (C.d (N - j) (N - (j + 1))).hom ∘ₗ
        LinearMap.baseChange A (eqToHom hx₀).hom =
      LinearMap.baseChange A (eqToHom hx₁).hom ∘ₗ
        LinearMap.baseChange A (D.d j (j + 1)).hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    exact congrArg (LinearMap.baseChange A)
      (congrArg ModuleCat.Hom.hom hcat₀₁)
  have h₁₂ :
      (LinearMap.baseChange A (C.d (N - (j + 1)) (N - (j + 2))).hom) ∘ₗ
          (e₁ : (A ⊗[R] D.X (j + 1)) →ₗ[A] A ⊗[R] C.X (N - (j + 1))) =
        (e₂ : (A ⊗[R] D.X (j + 2)) →ₗ[A] A ⊗[R] C.X (N - (j + 2))) ∘ₗ
          LinearMap.baseChange A (D.d (j + 1) (j + 2)).hom := by
    change LinearMap.baseChange A (C.d (N - (j + 1)) (N - (j + 2))).hom ∘ₗ
        LinearMap.baseChange A (eqToHom hx₁).hom =
      LinearMap.baseChange A (eqToHom hx₂).hom ∘ₗ
        LinearMap.baseChange A (D.d (j + 1) (j + 2)).hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    exact congrArg (LinearMap.baseChange A)
      (congrArg ModuleCat.Hom.hom hcat₁₂)
  have hiff := Function.Exact.iff_of_ladder_linearEquiv h₀₁ h₁₂
  have hex : Function.Exact
      (LinearMap.baseChange A (D.d j (j + 1)).hom)
      (LinearMap.baseChange A (D.d (j + 1) (j + 2)).hom) := hiff.mp h
  rw [CochainComplex.ExactAtSucc, CochainComplex.cocyclesSub]
  rw [CochainComplex.cochainBaseChange_d_hom,
    CochainComplex.cochainBaseChange_d_hom]
  exact (LinearMap.exact_iff.mp hex).symm

/-- Exactness of the base-changed chain complex at degree zero gives exactness at the top
nonzero degree of the base-changed bounded reversal. -/
theorem exactAtSucc_baseChange_reverseUpToCochain_top_of_exact_zero
    {A : Type u} [CommRing A] [Algebra R A]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N : ℕ) (hN : 0 < N)
    (h : Function.Exact
      (LinearMap.baseChange A (C.d 1 0).hom)
      (LinearMap.baseChange A (C.d 0 0).hom)) :
    CochainComplex.ExactAtSucc
      (GradedModule.cochainBaseChange A (C.reverseUpToCochain N)) (N - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [Nat.succ_sub_one]
  let D := C.reverseUpToCochain (n + 1)
  have hx₀ := C.reverseUpToCochain_X_of_le (n + 1) n (by omega)
  have hx₁ := C.reverseUpToCochain_X_of_le (n + 1) (n + 1) (by omega)
  let e₀ := ((eqToIso hx₀).toLinearEquiv.baseChange R A)
  let e₁ := ((eqToIso hx₁).toLinearEquiv.baseChange R A)
  have hcat₀₁ : eqToHom hx₀ ≫ C.d ((n + 1) - n) ((n + 1) - (n + 1)) =
      D.d n (n + 1) ≫ eqToHom hx₁ := by
    dsimp only [D]
    rw [C.reverseUpToCochain_d_of_lt (n + 1) n (by omega)]
    simp
  have h₀₁ :
      LinearMap.baseChange A (C.d ((n + 1) - n) ((n + 1) - (n + 1))).hom ∘ₗ
          (e₀ : (A ⊗[R] D.X n) →ₗ[A] A ⊗[R] C.X ((n + 1) - n)) =
        (e₁ : (A ⊗[R] D.X (n + 1)) →ₗ[A]
          A ⊗[R] C.X ((n + 1) - (n + 1))) ∘ₗ
          LinearMap.baseChange A (D.d n (n + 1)).hom := by
    change LinearMap.baseChange A
          (C.d ((n + 1) - n) ((n + 1) - (n + 1))).hom ∘ₗ
        LinearMap.baseChange A (eqToHom hx₀).hom =
      LinearMap.baseChange A (eqToHom hx₁).hom ∘ₗ
        LinearMap.baseChange A (D.d n (n + 1)).hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    exact congrArg (LinearMap.baseChange A)
      (congrArg ModuleCat.Hom.hom hcat₀₁)
  have hzeroC : LinearMap.baseChange A (C.d 0 0).hom = 0 := by
    rw [C.shape 0 0 (by simp)]
    simp
  have hsurjC : Function.Surjective (LinearMap.baseChange A (C.d 1 0).hom) := by
    simpa [hzeroC] using h
  have hsurjC' : Function.Surjective
      (LinearMap.baseChange A
        (C.d ((n + 1) - n) ((n + 1) - (n + 1))).hom) := by
    rw [show (n + 1) - n = 1 by omega,
      show (n + 1) - (n + 1) = 0 by omega]
    exact hsurjC
  have hsurjD : Function.Surjective
      (LinearMap.baseChange A (D.d n (n + 1)).hom) := by
    intro y
    obtain ⟨x, hx⟩ := hsurjC' (e₁ y)
    refine ⟨e₀.symm x, ?_⟩
    apply e₁.injective
    calc
      e₁ (LinearMap.baseChange A (D.d n (n + 1)).hom (e₀.symm x)) =
          LinearMap.baseChange A
            (C.d ((n + 1) - n) ((n + 1) - (n + 1))).hom
              (e₀ (e₀.symm x)) :=
        (LinearMap.congr_fun h₀₁ (e₀.symm x)).symm
      _ = LinearMap.baseChange A
            (C.d ((n + 1) - n) ((n + 1) - (n + 1))).hom x := by
        rw [e₀.apply_symm_apply]
      _ = e₁ y := hx
  have hzeroD : LinearMap.baseChange A (D.d (n + 1) (n + 2)).hom = 0 := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      C.reverseUpToCochain_d_of_ge (n + 1) (n + 1) le_rfl]
    simp
  have hexD : Function.Exact
      (LinearMap.baseChange A (D.d n (n + 1)).hom)
      (LinearMap.baseChange A (D.d (n + 1) (n + 2)).hom) := by
    rw [hzeroD, LinearMap.exact_zero_iff_surjective]
    exact hsurjD
  change CochainComplex.ExactAtSucc
    (GradedModule.cochainBaseChange A D) n
  rw [CochainComplex.ExactAtSucc, CochainComplex.cocyclesSub,
    CochainComplex.cochainBaseChange_d_hom,
    CochainComplex.cochainBaseChange_d_hom]
  exact (LinearMap.exact_iff.mp hexD).symm

/-- If a chain complex is exact after scalar extension in every chain degree below `N`,
then its bounded reversal through `N` is exact in every cochain degree after scalar
extension. -/
theorem reverseUpToCochain_exact_baseChange_of_exact
    {A : Type u} [CommRing A] [Algebra R A]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (h : ∀ i : ℕ, i < N → Function.Exact
      (LinearMap.baseChange A (C.d (i + 1) i).hom)
      (LinearMap.baseChange A (C.d i (i - 1)).hom)) :
    ∀ j : ℕ, CochainComplex.ExactAtSucc
      (GradedModule.cochainBaseChange A (C.reverseUpToCochain N)) j := by
  intro j
  by_cases hj : j < N
  · by_cases hj₁ : j + 1 < N
    · apply C.exactAtSucc_baseChange_reverseUpToCochain_of_exact N j hj₁
      have hi := h (N - (j + 1)) (by omega)
      have hleft : (N - (j + 1)) + 1 = N - j := by omega
      have hright : N - (j + 1) - 1 = N - (j + 2) := by omega
      rw [hleft, hright] at hi
      exact hi
    · have hjtop : j = N - 1 := by omega
      rw [hjtop]
      apply C.exactAtSucc_baseChange_reverseUpToCochain_top_of_exact_zero N (by omega)
      exact h 0 (by omega)
  · let D := C.reverseUpToCochain N
    letI : Subsingleton (D.X (j + 1)) :=
      C.reverseUpToCochain_bounded N (j + 1) (by omega)
    exact CochainComplex.exactAtSucc_of_subsingleton_X
      (CochainComplex.subsingleton_baseChange_of_subsingleton (R := R) (A := A))

/-- If a bounded finite flat chain complex becomes exact after reversing and extending
scalars to a local algebra, then its reversal was already exact over the source local ring.

This packages the chain-to-cochain input for the local form of Stacks Project tag 00MI.
The hypothesis is phrased on the reversed fibre so that it can be supplied either by a
residue-field computation or by a localized relative fibre. -/
theorem reverseUpToCochain_exact_of_localAlgebra
    [IsLocalRing R] [IsNoetherianRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ i : ℕ, Module.Finite R (C.X i))
    (hflat : ∀ i : ℕ, Module.Flat R (C.X i))
    (N : ℕ)
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      AlgebraicGeometry.ProjectiveSpace.CochainComplex.ExactAtSucc
        (AlgebraicGeometry.ProjectiveSpace.GradedModule.cochainBaseChange A
          (reverseUpToCochain C N)) j) :
    ∀ j : ℕ,
      AlgebraicGeometry.ProjectiveSpace.CochainComplex.ExactAtSucc
        (reverseUpToCochain C N) j := by
  let D := reverseUpToCochain C N
  exact
    AlgebraicGeometry.ProjectiveSpace.CochainComplex.exactAtSucc_of_localAlgebra
      D (reverseUpToCochain_flat C hflat N)
      (reverseUpToCochain_bounded C N)
      (AlgebraicGeometry.ProjectiveSpace.CochainComplex.finite_cohomologySucc_of_finite_terms
        D (reverseUpToCochain_finite C hfinite N)) A hfib

/-- Under the hypotheses of `reverseUpToCochain_exact_of_localAlgebra`, every cocycle of
the reversed complex is flat over the source local ring.  These cocycles are the successive
syzygies of the original chain complex, read from degree `N` downwards. -/
theorem reverseUpToCochain_flat_syzygy_of_localAlgebra
    [IsLocalRing R] [IsNoetherianRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ i : ℕ, Module.Finite R (C.X i))
    (hflat : ∀ i : ℕ, Module.Flat R (C.X i))
    (N : ℕ)
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      AlgebraicGeometry.ProjectiveSpace.CochainComplex.ExactAtSucc
        (AlgebraicGeometry.ProjectiveSpace.GradedModule.cochainBaseChange A
          (reverseUpToCochain C N)) j)
    (i : ℕ) :
    Module.Flat R
      (AlgebraicGeometry.ProjectiveSpace.CochainComplex.cocyclesSub
        (reverseUpToCochain C N) i) := by
  let D := reverseUpToCochain C N
  exact
    AlgebraicGeometry.ProjectiveSpace.CochainComplex.flat_cocyclesSub_of_localAlgebra
      D (reverseUpToCochain_flat C hflat N)
      (reverseUpToCochain_bounded C N)
      (AlgebraicGeometry.ProjectiveSpace.CochainComplex.finite_cohomologySucc_of_finite_terms
        D (reverseUpToCochain_finite C hfinite N)) A hfib i

end ChainComplex

end

end
