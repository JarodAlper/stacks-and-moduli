module

public import StacksAndModuli.API.PartialProjectiveResolutionClosedFibre
public import StacksAndModuli.API.PolynomialLocalizedResidueFibre
public import StacksAndModuli.API.NoetherianLocalFlatCokernelFiberCriterion

/-!
# Free final syzygies on polynomial closed fibres

For a prime `q` of a polynomial ring `A[x_i]`, suppose a finite partial projective
resolution over `A[x_i]_q` resolves a module flat over `A`.  If the resolution is
at least one less than the number of variables, its final syzygy becomes finite
free after quotienting by the contracted coefficient prime.

When `A` is Noetherian local and `q` lies over its closed point, the local lifting
criterion upgrades this closed-fibre freeness to freeness of the final syzygy over
`A[x_i]_q` itself.

This assembles the exact closed-fibre resolution with the regularity and global
dimension of a localized polynomial ring over the residue field.

Main declaration:

* `Module.IsPartialProjectiveResolution.free_polynomialLocalization_closedFibre_of_flat`.
* `Module.IsPartialProjectiveResolution.free_polynomialLocalization_of_flat`.
-/

@[expose] public section

universe u

noncomputable section

namespace Module.IsPartialProjectiveResolution

set_option linter.style.haveILetI false

/-- A sufficiently long finite partial projective resolution over a localized
polynomial ring has finite-free final syzygy on the coefficient closed fibre. -/
theorem free_polynomialLocalization_closedFibre_of_flat
    {A sigma : Type u} [CommRing A] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (Localization.AtPrime q.asIdeal) M]
    [AddCommGroup K] [Module (Localization.AtPrime q.asIdeal) K]
    [Module.Finite (Localization.AtPrime q.asIdeal) M]
    [Module.Finite (Localization.AtPrime q.asIdeal) K]
    (hres : Module.IsPartialProjectiveResolution
      (Localization.AtPrime q.asIdeal) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M
        (algebraMap A (Localization.AtPrime q.asIdeal))))
    (he : Nat.card sigma - 1 ≤ e) :
    let p := (q.comap
      (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal
    let J := p.map
      (algebraMap A (Localization.AtPrime q.asIdeal))
    letI : SMul (MvPolynomial.localizedResidueFibre q)
        (K ⧸ J • (⊤ : Submodule (Localization.AtPrime q.asIdeal) K)) :=
      Ideal.Quotient.smulModuleQuotient J
    letI : Module (MvPolynomial.localizedResidueFibre q)
        (K ⧸ J • (⊤ : Submodule (Localization.AtPrime q.asIdeal) K)) :=
      Ideal.Quotient.moduleQuotient J
    Module.Free (MvPolynomial.localizedResidueFibre q)
      (K ⧸ J • (⊤ : Submodule (Localization.AtPrime q.asIdeal) K)) := by
  let S := Localization.AtPrime q.asIdeal
  let p := (q.comap
    (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal
  let J := p.map (algebraMap A S)
  letI : SMul (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
    Ideal.Quotient.smulModuleQuotient J
  letI : Module (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
    Ideal.Quotient.moduleQuotient J
  letI : SMul (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
    Ideal.Quotient.smulModuleQuotient J
  letI : Module (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
    Ideal.Quotient.moduleQuotient J
  letI : Module.Finite (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
    Ideal.Quotient.finite_moduleQuotient J
  letI : Module.Finite (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
    Ideal.Quotient.finite_moduleQuotient J
  have hresq := hres.quotientByMappedIdeal_of_flat hM p
  exact hresq.free_localizedResidueFibre q he

/-- Over a Noetherian local coefficient ring, a sufficiently long finite partial
projective resolution of a coefficient-flat module has free final syzygy at every
polynomial prime lying over the closed point. -/
theorem free_polynomialLocalization_of_flat
    {A sigma : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (hq : (q.comap
      (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal =
        IsLocalRing.maximalIdeal A)
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (Localization.AtPrime q.asIdeal) M]
    [AddCommGroup K] [Module (Localization.AtPrime q.asIdeal) K]
    [Module.Finite (Localization.AtPrime q.asIdeal) M]
    [Module.Finite (Localization.AtPrime q.asIdeal) K]
    (hres : Module.IsPartialProjectiveResolution
      (Localization.AtPrime q.asIdeal) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M
        (algebraMap A (Localization.AtPrime q.asIdeal))))
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Free (Localization.AtPrime q.asIdeal) K := by
  cases subsingleton_or_nontrivial K
  · exact Module.Free.of_subsingleton _ _
  let S := Localization.AtPrime q.asIdeal
  letI : Module A K := Module.compHom K (algebraMap A S)
  letI : IsScalarTower A S K := IsScalarTower.of_compHom A S K
  letI : Module.Flat A K := hres.flat_final_of_flat hM
  have hlocal :
      (IsLocalRing.maximalIdeal S).comap (algebraMap A S) =
        IsLocalRing.maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A (MvPolynomial sigma A) S,
      ← Ideal.comap_comap]
    change (IsLocalRing.maximalIdeal S).under A = IsLocalRing.maximalIdeal A
    rw [← Ideal.under_under (B := MvPolynomial sigma A),
      Localization.AtPrime.under_maximalIdeal]
    change q.asIdeal.comap (algebraMap A (MvPolynomial sigma A)) =
      IsLocalRing.maximalIdeal A
    rw [MvPolynomial.algebraMap_eq, ← PrimeSpectrum.comap_asIdeal]
    exact hq
  letI : IsLocalHom (algebraMap A S) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A S)).out 4 0).mp hlocal
  have hclosed := hres.free_polynomialLocalization_closedFibre_of_flat q hM he
  let FreeClosed (I : Ideal A) : Prop :=
    let J := I.map (algebraMap A S)
    letI : SMul (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
      Ideal.Quotient.smulModuleQuotient J
    letI : Module (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
      Ideal.Quotient.moduleQuotient J
    Module.Free (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K))
  have hp : FreeClosed
      (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal := by
    exact hclosed
  have hm : FreeClosed (IsLocalRing.maximalIdeal A) := hq ▸ hp
  letI : SMul (S ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A S))
      (K ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) •
        (⊤ : Submodule S K)) :=
    Ideal.Quotient.smulModuleQuotient _
  letI : Module (S ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A S))
      (K ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) •
        (⊤ : Submodule S K)) :=
    Ideal.Quotient.moduleQuotient _
  have hfreeClosed : Module.Free
      (S ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A S))
      (K ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) •
        (⊤ : Submodule S K)) := by
    exact hm
  have hmoduleEq :
      Ideal.Quotient.moduleQuotient (M := K)
        ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) =
      @Module.instQuotientIdealSubmoduleHSMulTop S K _ _ _
        ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) _ :=
    Ideal.Quotient.moduleQuotient_eq_canonical _
  have hfreeNative : @Module.Free
      (S ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A S))
      (K ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) •
        (⊤ : Submodule S K)) _ _
      (@Module.instQuotientIdealSubmoduleHSMulTop S K _ _ _
        ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) _) := by
    rw [← hmoduleEq]
    exact hfreeClosed
  exact (@Module.Flat.free_and_source_flat_of_free_closedFiber
    A S K _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfreeNative _).1

end Module.IsPartialProjectiveResolution

end

end
