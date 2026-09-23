module

public import StacksAndModuli.API.BoundedChainReversal
public import StacksAndModuli.API.RelativeFibreExactnessInterface

/-!
# Exact bounded complexes from a localized relative fibre

Let `q` be a prime of an `R`-algebra `S`, and let `A` be the localization at the induced
prime of the fibre over `q ∩ R`.  The natural map `S_q → A` is a local homomorphism.
Consequently, exactness of a bounded finite flat complex after extension from `S` to `A`
detects exactness after extension to `S_q`; its localized syzygies are flat over `S_q`.

This file packages that local implication for a bounded chain complex by reversing it into
a cochain complex.  It is the pointwise algebraic step toward Stacks Project tag 00RB; it
makes no assertion that the relative-fibre exactness condition is open.

Main declaration:

* `ChainComplex.relativeFibreExact_reverseUpToCochain`;
* `ChainComplex.localizedReverseExactAndFlatSyzygies_of_relativeFibre`;
* `ChainComplex.localizedReverseExactAndFlatSyzygies_of_relativeFibreExactAtDegree`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

variable {T : Type u} [CommRing T]

/-- Exactness at a concrete cochain degree is invariant under an isomorphism of complexes. -/
theorem exactAtSucc_iff_of_iso
    {C D : CochainComplex (ModuleCat.{u} T) ℕ} (e : C ≅ D) (j : ℕ) :
    ExactAtSucc C j ↔ ExactAtSucc D j := by
  let e₀ := (HomologicalComplex.Hom.isoApp e j).toLinearEquiv
  let e₁ := (HomologicalComplex.Hom.isoApp e (j + 1)).toLinearEquiv
  let e₂ := (HomologicalComplex.Hom.isoApp e (j + 2)).toLinearEquiv
  have h₀₁ :
      (D.d j (j + 1)).hom ∘ₗ (e₀ : C.X j →ₗ[T] D.X j) =
        (e₁ : C.X (j + 1) →ₗ[T] D.X (j + 1)) ∘ₗ
          (C.d j (j + 1)).hom := by
    apply LinearMap.ext
    intro x
    have h := congrArg ModuleCat.Hom.hom (e.hom.comm j (j + 1))
    exact LinearMap.congr_fun h x
  have h₁₂ :
      (D.d (j + 1) (j + 2)).hom ∘ₗ
          (e₁ : C.X (j + 1) →ₗ[T] D.X (j + 1)) =
        (e₂ : C.X (j + 2) →ₗ[T] D.X (j + 2)) ∘ₗ
          (C.d (j + 1) (j + 2)).hom := by
    apply LinearMap.ext
    intro x
    have h := congrArg ModuleCat.Hom.hom (e.hom.comm (j + 1) (j + 2))
    exact LinearMap.congr_fun h x
  have hiff := Function.Exact.iff_of_ladder_linearEquiv h₀₁ h₁₂
  rw [ExactAtSucc, ExactAtSucc, cocyclesSub, cocyclesSub]
  constructor
  · intro hC
    have hexC : Function.Exact (C.d j (j + 1)).hom
        (C.d (j + 1) (j + 2)).hom :=
      LinearMap.exact_iff.mpr hC.symm
    exact (LinearMap.exact_iff.mp (hiff.mpr hexC)).symm
  · intro hD
    have hexD : Function.Exact (D.d j (j + 1)).hom
        (D.d (j + 1) (j + 2)).hom :=
      LinearMap.exact_iff.mpr hD.symm
    exact (LinearMap.exact_iff.mp (hiff.mp hexD)).symm

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

namespace ChainComplex

open Algebra TensorProduct
open AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Relative-fibre exactness in each chain degree below `N` gives exactness, in every
degree, of the base-changed bounded reversal on that localized fibre. -/
theorem relativeFibreExact_reverseUpToCochain
    (C : ChainComplex (ModuleCat.{u} S) ℕ) (N : ℕ) (q : PrimeSpectrum S)
    (h : ∀ i : ℕ, i < N → IsRelativeFibreExactAtDegree (R := R) C q i) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
    ∀ j : ℕ, CochainComplex.ExactAtSucc
      (GradedModule.cochainBaseChange (Localization.AtPrime qf.asIdeal)
        (reverseUpToCochain C N)) j := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  apply C.reverseUpToCochain_exact_baseChange_of_exact N
  intro i hi
  exact h i hi

/-- A bounded finite flat chain complex that is exact on the localized relative fibre at
`q` becomes exact after localization at `q`, and all syzygies of its reversed localized
complex are `S_q`-flat.

The fibre hypothesis is expressed on the bounded reversal.  This form remains useful for
augmented resolutions where the degree-zero endpoint is supplied explicitly; the wrapper
`localizedReverseExactAndFlatSyzygies_of_relativeFibreExactAtDegree` below supplies it
directly from the degreewise relative-fibre predicate. -/
theorem localizedReverseExactAndFlatSyzygies_of_relativeFibre
    [IsNoetherianRing S]
    (C : ChainComplex (ModuleCat.{u} S) ℕ)
    (hfinite : ∀ i : ℕ, Module.Finite S (C.X i))
    (hflat : ∀ i : ℕ, Module.Flat S (C.X i))
    (N : ℕ) (q : PrimeSpectrum S)
    (hfib :
      let p := q.comap (algebraMap R S)
      let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
      letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
      ∀ j : ℕ, CochainComplex.ExactAtSucc
        (GradedModule.cochainBaseChange (Localization.AtPrime qf.asIdeal)
          (reverseUpToCochain C N)) j) :
    let Sq := Localization.AtPrime q.asIdeal
    let Dq := GradedModule.cochainBaseChange Sq (reverseUpToCochain C N)
    (∀ j : ℕ, CochainComplex.ExactAtSucc Dq j) ∧
      ∀ i : ℕ, Module.Flat Sq (CochainComplex.cocyclesSub Dq i) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let Sq := Localization.AtPrime q.asIdeal
  let A := Localization.AtPrime qf.asIdeal
  let D := reverseUpToCochain C N
  let Dq := GradedModule.cochainBaseChange Sq D
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  have hqf : qf.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, Algebra.TensorProduct.algebraMap_eq_includeRight]
    exact (PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q).symm⟩
  letI : qf.asIdeal.LiesOver q.asIdeal := hqf
  letI : Algebra Sq A :=
    Localization.AtPrime.algebraOfLiesOver q.asIdeal qf.asIdeal
  have hflatD : ∀ i : ℕ, Module.Flat S (D.X i) :=
    reverseUpToCochain_flat C hflat N
  have hfiniteD : ∀ i : ℕ, Module.Finite S (D.X i) :=
    reverseUpToCochain_finite C hfinite N
  have hflatDq : ∀ i : ℕ, Module.Flat Sq (Dq.X i) := by
    intro i
    letI : Module.Flat S (D.X i) := hflatD i
    change Module.Flat Sq (Sq ⊗[S] D.X i)
    exact Module.Flat.baseChange S Sq (D.X i)
  have hfiniteDq : ∀ i : ℕ, Module.Finite Sq (Dq.X i) := by
    intro i
    letI : Module.Finite S (D.X i) := hfiniteD i
    change Module.Finite Sq (Sq ⊗[S] D.X i)
    infer_instance
  have hvanDq : ∀ i : ℕ, N < i → Subsingleton (Dq.X i) := by
    intro i hi
    letI : Subsingleton (D.X i) := reverseUpToCochain_bounded C N i hi
    exact CochainComplex.subsingleton_baseChange_of_subsingleton
  have hfinDq : ∀ j : ℕ,
      Module.Finite Sq (CochainComplex.cohomologySucc Dq j) :=
    CochainComplex.finite_cohomologySucc_of_finite_terms Dq hfiniteDq
  have hfibDq : ∀ j : ℕ,
      CochainComplex.ExactAtSucc (GradedModule.cochainBaseChange A Dq) j := by
    intro j
    let e := CochainComplex.cochainBaseChangeCompIso D Sq A
    exact (CochainComplex.exactAtSucc_iff_of_iso e j).mpr (hfib j)
  have hex : ∀ j : ℕ, CochainComplex.ExactAtSucc Dq j :=
    CochainComplex.exactAtSucc_of_localAlgebra
      Dq hflatDq hvanDq hfinDq A hfibDq
  refine ⟨hex, ?_⟩
  intro i
  exact CochainComplex.flat_cocyclesSub_of_localAlgebra
    Dq hflatDq hvanDq hfinDq A hfibDq i

/-- A bounded finite flat chain complex that is relatively fibre-exact in every degree
below `N` has an exact localized bounded reversal at `q`, whose localized syzygies are
flat over `S_q`. -/
theorem localizedReverseExactAndFlatSyzygies_of_relativeFibreExactAtDegree
    [IsNoetherianRing S]
    (C : ChainComplex (ModuleCat.{u} S) ℕ)
    (hfinite : ∀ i : ℕ, Module.Finite S (C.X i))
    (hflat : ∀ i : ℕ, Module.Flat S (C.X i))
    (N : ℕ) (q : PrimeSpectrum S)
    (hfib : ∀ i : ℕ, i < N → IsRelativeFibreExactAtDegree (R := R) C q i) :
    let Sq := Localization.AtPrime q.asIdeal
    let Dq := GradedModule.cochainBaseChange Sq (reverseUpToCochain C N)
    (∀ j : ℕ, CochainComplex.ExactAtSucc Dq j) ∧
      ∀ i : ℕ, Module.Flat Sq (CochainComplex.cocyclesSub Dq i) := by
  apply localizedReverseExactAndFlatSyzygies_of_relativeFibre
    (R := R) (S := S) C hfinite hflat N q
  exact relativeFibreExact_reverseUpToCochain (R := R) C N q hfib

end ChainComplex

end

end
