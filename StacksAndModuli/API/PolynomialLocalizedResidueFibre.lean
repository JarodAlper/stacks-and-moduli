module

public import StacksAndModuli.API.PolynomialRegularProjectiveDimension
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Localized polynomial residue fibres

Let `q` be a prime of `A[x_i]` and let `p = q ∩ A`.  The fibre of the local
ring `A[x_i]_q` over `p` is

`A[x_i]_q / p A[x_i]_q`.

This file identifies that quotient with a prime localization of
`ResidueField p[x_i]`.  It then transports the regular polynomial-ring
projective-dimension bound across the equivalence.  In particular, the last
syzygy of a sufficiently long finite partial projective resolution over the
localized fibre is projective, and is free when it is finite.

Main declarations:

* `MvPolynomial.residueFibrePrime`;
* `MvPolynomial.residueFibreLocalizationAlgEquiv`;
* `Module.hasProjectiveDimensionLE_localizedResidueFibre`;
* `Module.IsPartialProjectiveResolution.projective_localizedResidueFibre`;
* `Module.IsPartialProjectiveResolution.free_localizedResidueFibre`.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

namespace MvPolynomial

variable {A sigma : Type u} [CommRing A]

/-- The residue fibre of `A[x_i]_q` over the contraction of `q` to `A`. -/
abbrev localizedResidueFibre
    (q : PrimeSpectrum (MvPolynomial sigma A)) :=
  Localization.AtPrime q.asIdeal ⧸
    (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal.map
      (algebraMap A (Localization.AtPrime q.asIdeal))

/-- The prime of `ResidueField (q ∩ A)[x_i]` induced by the polynomial
prime `q`. -/
noncomputable def residueFibrePrime
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    PrimeSpectrum (MvPolynomial sigma
      (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal.ResidueField) := by
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let qf : PrimeSpectrum (p.asIdeal.Fiber (MvPolynomial sigma A)) :=
    PrimeSpectrum.preimageEquivFiber A (MvPolynomial sigma A) p ⟨q, rfl⟩
  let e : p.asIdeal.Fiber (MvPolynomial sigma A) ≃ₐ[p.asIdeal.ResidueField]
      MvPolynomial sigma p.asIdeal.ResidueField :=
    MvPolynomial.algebraTensorAlgEquiv A p.asIdeal.ResidueField
  exact PrimeSpectrum.comapEquiv e.toRingEquiv qf

/-- The prime of the tensor-product model
`ResidueField (q ∩ A) ⊗[A] A[x_i]` induced by `q`. -/
noncomputable def residueFibreTensorPrime
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    PrimeSpectrum
      ((q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal.Fiber
        (MvPolynomial sigma A)) :=
  PrimeSpectrum.preimageEquivFiber A (MvPolynomial sigma A)
    (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)) ⟨q, rfl⟩

/-- The tensor-product fibre prime induced by `q` contracts to `q` along the
right tensor-factor map. -/
lemma residueFibreTensorPrime_comap
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    (residueFibreTensorPrime q).asIdeal.comap
      Algebra.TensorProduct.includeRight = q.asIdeal := by
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let E := PrimeSpectrum.preimageEquivFiber A (MvPolynomial sigma A) p
  have h := E.left_inv ⟨q, rfl⟩
  exact congrArg (fun x => x.1.asIdeal) h

/-- The polynomial residue-fibre prime pulls back to the tensor-product fibre
prime along `MvPolynomial.algebraTensorAlgEquiv`. -/
lemma residueFibrePrime_comap_equiv
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    (residueFibrePrime q).asIdeal.comap
      (MvPolynomial.algebraTensorAlgEquiv A
        (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal.ResidueField) =
      (residueFibreTensorPrime q).asIdeal := by
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let qf := residueFibreTensorPrime q
  let e : p.asIdeal.Fiber (MvPolynomial sigma A) ≃ₐ[p.asIdeal.ResidueField]
      MvPolynomial sigma p.asIdeal.ResidueField :=
    MvPolynomial.algebraTensorAlgEquiv A p.asIdeal.ResidueField
  change ((PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    ((PrimeSpectrum.comapEquiv e.toRingEquiv) qf)).asIdeal = qf.asIdeal
  exact congrArg PrimeSpectrum.asIdeal
    ((PrimeSpectrum.comapEquiv e.toRingEquiv).symm_apply_apply qf)

/-- The residue fibre of the localized polynomial ring at `q` is the
localization of `ResidueField (q ∩ A)[x_i]` at the prime induced by `q`. -/
noncomputable def residueFibreLocalizationAlgEquiv
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    Localization.AtPrime (residueFibrePrime q).asIdeal ≃ₐ[A]
      localizedResidueFibre q := by
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let qf := residueFibreTensorPrime q
  let qp := residueFibrePrime q
  let e : p.asIdeal.Fiber (MvPolynomial sigma A) ≃ₐ[p.asIdeal.ResidueField]
      MvPolynomial sigma p.asIdeal.ResidueField :=
    MvPolynomial.algebraTensorAlgEquiv A p.asIdeal.ResidueField
  have hqp : qf.asIdeal = qp.asIdeal.comap e := by
    exact (residueFibrePrime_comap_equiv q).symm
  let eLoc : Localization.AtPrime qf.asIdeal ≃ₐ[p.asIdeal.ResidueField]
      Localization.AtPrime qp.asIdeal :=
    Localization.localAlgEquiv qf.asIdeal qp.asIdeal e hqp
  let r : Ideal (MvPolynomial sigma A) :=
    qf.asIdeal.comap Algebra.TensorProduct.includeRight
  have hr : r = q.asIdeal := residueFibreTensorPrime_comap q
  have hq_over : q.asIdeal.LiesOver p.asIdeal := ⟨by
    rw [Ideal.under_def, MvPolynomial.algebraMap_eq]
    rfl⟩
  haveI : r.LiesOver p.asIdeal := hr ▸ hq_over
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  let eQuot := Ideal.Fiber.localizationAlgEquivQuotient p.asIdeal qf.asIdeal
  change Localization.AtPrime qf.asIdeal ≃ₐ[Localization.AtPrime p.asIdeal]
    Localization.AtPrime r ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime r)) at eQuot
  have hr_refl : r = q.asIdeal.comap
      (AlgEquiv.refl : MvPolynomial sigma A ≃ₐ[A] MvPolynomial sigma A) := by
    rw [hr]
    change q.asIdeal = q.asIdeal.comap (RingHom.id _)
    rw [Ideal.comap_id]
  let eRq : Localization.AtPrime r ≃ₐ[A] Localization.AtPrime q.asIdeal :=
    Localization.localAlgEquiv r q.asIdeal AlgEquiv.refl hr_refl
  have hmap :
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)) =
        (p.asIdeal.map (algebraMap A (Localization.AtPrime r))).map eRq := by
    change p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)) =
      (p.asIdeal.map (algebraMap A (Localization.AtPrime r))).map
        eRq.toRingEquiv.toRingHom
    rw [Ideal.map_map]
    congr 1
    ext x
    exact (eRq.commutes x).symm
  let eQuotRq :
      (Localization.AtPrime r ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime r))) ≃ₐ[A]
        (Localization.AtPrime q.asIdeal ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) :=
    Ideal.quotientEquivAlg _ _ eRq hmap
  exact ((eLoc.symm.restrictScalars A).trans (eQuot.restrictScalars A)).trans eQuotRq

end MvPolynomial

namespace Module

variable {A sigma : Type u} [CommRing A] [Finite sigma]

/-- A finite module over the localized polynomial residue fibre has projective
dimension at most the number of variables. -/
theorem hasProjectiveDimensionLE_localizedResidueFibre
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial.localizedResidueFibre q) M]
    [Module.Finite (MvPolynomial.localizedResidueFibre q) M] :
    Module.HasProjectiveDimensionLE
      (MvPolynomial.localizedResidueFibre q) (Nat.card sigma) M := by
  let P := Localization.AtPrime (MvPolynomial.residueFibrePrime q).asIdeal
  let Q := MvPolynomial.localizedResidueFibre q
  let e : P ≃ₐ[A] Q := MvPolynomial.residueFibreLocalizationAlgEquiv q
  letI : Module P M := Module.compHom M e.toRingEquiv.toRingHom
  letI hpair : RingHomInvPair e.toRingEquiv.toRingHom
      e.toRingEquiv.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI hpair' : RingHomInvPair e.toRingEquiv.symm.toRingHom
      e.toRingEquiv.toRingHom :=
    RingHomInvPair.symm e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom
  let eM : M ≃ₛₗ[e.toRingEquiv.toRingHom] M :=
    { Equiv.refl M with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : Module.Finite P M :=
    (eM.toLinearMap.finite_iff_of_bijective eM.bijective).mpr inferInstance
  letI : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of P M) (Nat.card sigma) :=
    Module.hasProjectiveDimensionLE_localizationAtPrime_mvPolynomial_of_field
      _ _ (MvPolynomial.residueFibrePrime q) M
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (M := ModuleCat.of P M) (N := ModuleCat.of Q M)
      e.toRingEquiv eM (Nat.card sigma)

namespace IsPartialProjectiveResolution

/-- The final syzygy in a sufficiently long finite partial projective
resolution over a localized polynomial residue fibre is projective. -/
theorem projective_localizedResidueFibre
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial.localizedResidueFibre q) M]
    [AddCommGroup K] [Module (MvPolynomial.localizedResidueFibre q) K]
    [Module.Finite (MvPolynomial.localizedResidueFibre q) M]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial.localizedResidueFibre q) e M K)
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Projective (MvPolynomial.localizedResidueFibre q) K :=
  hres.projective_of_projectiveDimension_le he
    (Module.hasProjectiveDimensionLE_localizedResidueFibre q M)

/-- A finite final syzygy as in `projective_localizedResidueFibre` is free over
the localized polynomial residue fibre. -/
theorem free_localizedResidueFibre
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial.localizedResidueFibre q) M]
    [AddCommGroup K] [Module (MvPolynomial.localizedResidueFibre q) K]
    [Module.Finite (MvPolynomial.localizedResidueFibre q) M]
    [Module.Finite (MvPolynomial.localizedResidueFibre q) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial.localizedResidueFibre q) e M K)
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Free (MvPolynomial.localizedResidueFibre q) K := by
  letI : IsLocalRing (MvPolynomial.localizedResidueFibre q) :=
    (MvPolynomial.residueFibreLocalizationAlgEquiv q).toRingEquiv.isLocalRing
  letI : Module.Projective (MvPolynomial.localizedResidueFibre q) K :=
    hres.projective_localizedResidueFibre q he
  exact Module.free_of_flat_of_isLocalRing
    (R := MvPolynomial.localizedResidueFibre q) (P := K)

end IsPartialProjectiveResolution

end Module

end
