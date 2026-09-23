module

public import StacksAndModuli.API.IdealTensorKernelFlatBaseChange
public import StacksAndModuli.API.LocalNoetherianPolynomialFlatApproximation

/-!
# Flatness of a local polynomial stage at a prime

The local Noetherian approximation of a polynomial presentation kills the finite
maximal-ideal tensor obstruction at a sufficiently late coefficient stage.  The resulting
injectivity can be localized at any polynomial prime lying over the closed point of that
coefficient stage.  The localized polynomial ring is then a local Noetherian algebra, so the
Noetherian local criterion makes the localized module coefficient-flat.

This is the per-prime local step toward the flat coefficient model in Stacks Project tag
02JO.  It deliberately assumes that the polynomial prime contracts to the coefficient
maximal ideal; an arbitrary polynomial prime need not have that property.

Main declarations:
- `Module.Flat.localizationAtPrime_of_maximalIdeal_tensorMul_injective`.
- `PolynomialModel.flat_localSystemStage_atPrime_of_transition_comp_eq_zero`.
- `PolynomialModel.exists_later_flat_localSystemStage_atPrime`.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w

namespace Module.Flat

/-- If maximal-ideal multiplication is injective on a finite module over a Noetherian
algebra, then the module localized at any source prime over the coefficient closed point is
flat over the coefficient ring. -/
theorem localizationAtPrime_of_maximalIdeal_tensorMul_injective
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hmul : Function.Injective
      (Ideal.tensorMul (R := R) (S := S) (M := M) (maximalIdeal R))) :
    Module.Flat R (Localization.AtPrime q ⊗[S] M) := by
  let T := Localization.AtPrime q
  have hlocal :
      (maximalIdeal T).comap (algebraMap R T) = maximalIdeal R := by
    rw [IsScalarTower.algebraMap_eq R S T, ← Ideal.comap_comap]
    change (maximalIdeal T).under R = maximalIdeal R
    rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]
    change q.comap (algebraMap R S) = maximalIdeal R
    exact hq
  letI : IsLocalHom (algebraMap R T) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R T)).out 4 0).mp hlocal
  have tensorMul_baseChange :
      Ideal.tensorMul (R := R) (S := T) (M := T ⊗[S] M) (maximalIdeal R) =
        (Ideal.tensorMul (R := R) (S := S) (M := M) (maximalIdeal R)).baseChange T ∘ₗ
          (AlgebraTensorModule.assoc R S T T M (maximalIdeal R)).toLinearMap := by
    apply AlgebraTensorModule.ext
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul t m =>
        change (i : R) • (t ⊗ₜ[S] m) =
          (Ideal.tensorMul (R := R) (S := S) (M := M) (maximalIdeal R)).baseChange T
            (AlgebraTensorModule.assoc R S T T M (maximalIdeal R)
              ((t ⊗ₜ[S] m) ⊗ₜ[R] i))
        rw [AlgebraTensorModule.assoc_tmul, LinearMap.baseChange_tmul,
          Ideal.tensorMul_tmul]
        calc
          ((i : R) • t) ⊗ₜ[S] m =
              (algebraMap R S (i : R) • t) ⊗ₜ[S] m := by
            rw [IsScalarTower.algebraMap_smul S]
          _ = t ⊗ₜ[S] (algebraMap R S (i : R) • m) :=
            TensorProduct.smul_tmul _ _ _
          _ = t ⊗ₜ[S] ((i : R) • m) := by
            rw [IsScalarTower.algebraMap_smul S]
  have hmul' : Function.Injective
      (Ideal.tensorMul (R := R) (S := T) (M := T ⊗[S] M) (maximalIdeal R)) := by
    rw [tensorMul_baseChange]
    exact (Module.Flat.lTensor_preserves_injective_linearMap
        (Ideal.tensorMul (R := R) (S := S) (M := M) (maximalIdeal R)) hmul).comp
      (AlgebraTensorModule.assoc R S T T M (maximalIdeal R)).injective
  apply Module.Flat.of_maximalIdeal_rTensor_injective_of_finite T
  exact (Ideal.tensorMul_injective_iff_rTensor_injective
    (R := R) (S := T) (M := T ⊗[S] M) (maximalIdeal R)).mp hmul'

end Module.Flat

namespace LocalNoetherianApproximation

/-- The contraction of a prime of the limit polynomial ring to a Noetherian polynomial
coefficient stage. -/
noncomputable def polynomialPrimeAtStage
    {R : Type u} [CommRing R] [IsLocalRing R] {sigma : Type v}
    (q : Ideal (MvPolynomial sigma R)) (i : Index R) :
    Ideal (MvPolynomial sigma (coefficient R i)) :=
  q.comap (MvPolynomial.map (toLimit R i))

instance polynomialPrimeAtStage_isPrime
    {R : Type u} [CommRing R] [IsLocalRing R] {sigma : Type v}
    (q : Ideal (MvPolynomial sigma R)) [q.IsPrime] (i : Index R) :
    (polynomialPrimeAtStage q i).IsPrime :=
  Ideal.IsPrime.comap _

/-- If a polynomial prime lies over the closed point of a local coefficient ring, then its
contraction to every local Noetherian coefficient stage also lies over that stage's closed
point. -/
theorem polynomialPrimeAtStage_comap_algebraMap
    {R : Type u} [CommRing R] [IsLocalRing R] {sigma : Type v}
    (q : Ideal (MvPolynomial sigma R)) (i : Index R)
    (hq : q.comap (algebraMap R (MvPolynomial sigma R)) = maximalIdeal R) :
    (polynomialPrimeAtStage q i).comap
      (algebraMap (coefficient R i) (MvPolynomial sigma (coefficient R i))) =
        maximalIdeal (coefficient R i) := by
  rw [← IsLocalRing.maximalIdeal_comap (toLimit R i)]
  ext x
  change MvPolynomial.map (toLimit R i)
      (algebraMap (coefficient R i) (MvPolynomial sigma (coefficient R i)) x) ∈ q ↔
    toLimit R i x ∈ maximalIdeal R
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  exact SetLike.ext_iff.mp hq (toLimit R i x)

end LocalNoetherianApproximation

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {sigma : Type v} [Finite sigma]
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial sigma R) M]

/-- Once the transitioned tensor obstruction vanishes, a local polynomial-model stage is
coefficient-flat after localization at any prime lying over the coefficient closed point. -/
theorem flat_localSystemStage_atPrime_of_transition_comp_eq_zero
    (D : PolynomialModel R sigma M) (j : Later R D.localIndex)
    (q : Ideal (polynomial R sigma j)) [q.IsPrime]
    (hq : q.comap
      (algebraMap (coefficient R j.1) (polynomial R sigma j)) =
        maximalIdeal (coefficient R j.1))
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Module.Flat (coefficient R j.1)
      (Localization.AtPrime q ⊗[polynomial R sigma j] D.localSystemStage j) := by
  let _ : Module.Finite (polynomial R sigma j) (D.localSystemStage j) :=
    D.localSystemStage_finite j
  let _ : Module.Flat
      (D.localCoefficient ⧸ maximalIdeal D.localCoefficient)
      ((D.localCoefficient ⧸ maximalIdeal D.localCoefficient) ⊗[
        D.localCoefficient] D.localModelModule) := D.localModelClosedFibre_flat
  apply Module.Flat.localizationAtPrime_of_maximalIdeal_tensorMul_injective
    (R := coefficient R j.1) (S := polynomial R sigma j)
    (M := D.localSystemStage j) q hq
  exact D.tensorMul_injective_of_transition_comp_eq_zero j hzero

/-- For a polynomial prime over the closed point of a local coefficient ring, a
coefficient-flat finitely presented polynomial module has a later local Noetherian stage
whose localization at the contracted prime is coefficient-flat. -/
theorem exists_later_flat_localSystemStage_atPrime
    (D : PolynomialModel R sigma M) (q : Ideal (MvPolynomial sigma R)) [q.IsPrime]
    (hq : q.comap (algebraMap R (MvPolynomial sigma R)) = maximalIdeal R)
    (hflat :
      letI : Module R M := Module.compHom M
        (algebraMap R (MvPolynomial sigma R))
      Module.Flat R M) :
    ∃ j : Later R D.localIndex,
      ∃ _hij : initialLater R D.localIndex ≤ j,
        Module.Flat (coefficient R j.1)
          (Localization.AtPrime
              (LocalNoetherianApproximation.polynomialPrimeAtStage q j.1) ⊗[
            polynomial R sigma j] D.localSystemStage j) := by
  obtain ⟨j, hij, hzero⟩ :=
    D.exists_later_localInitialTensorKernelMap_eq_zero hflat
  refine ⟨j, hij, ?_⟩
  apply D.flat_localSystemStage_atPrime_of_transition_comp_eq_zero
    j (LocalNoetherianApproximation.polynomialPrimeAtStage q j.1)
    (LocalNoetherianApproximation.polynomialPrimeAtStage_comap_algebraMap q j.1 hq)
  exact hzero

end Module.FinitePresentation.PolynomialModel
