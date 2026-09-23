module

public import StacksAndModuli.API.PolynomialPartialResolutionFreeNeighborhood
public import StacksAndModuli.API.PolynomialPrimeCoefficientLocalization
public import StacksAndModuli.API.SemilinearTransport

/-!
# Projective neighbourhoods of polynomial syzygies at arbitrary primes

Let `A` be Noetherian, let `q` be any prime of `A[x_i]`, and let a sufficiently long
finite partial projective resolution become coefficient-flat after localization at `q`.
Localizing `A` at `q ∩ A` turns `q` into a prime over the closed point, so the local
polynomial syzygy-neighbourhood theorem applies.  The free-locus criterion then transports
the result back through the coefficient localization and produces a principal neighbourhood
of the original prime.  Global coefficient-flatness gives the same conclusion at every
prime.

Main declaration:

* `Module.IsPartialProjectiveResolution.exists_away_free_final_of_flat_localizationAtPrime`;
* `Module.IsPartialProjectiveResolution.exists_away_free_final_of_flat_at_arbitraryPrime`;
* `Module.IsPartialProjectiveResolution.exists_away_projective_final_of_flat_at_arbitraryPrime`.
-/

@[expose] public section

universe u v w

noncomputable section

open TensorProduct

namespace Module.IsPartialProjectiveResolution

set_option linter.style.haveILetI false

/-- A partial projective resolution may be transported by restricting all module
structures along a ring equivalence. -/
theorem compHom_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (eR : R ≃+* S) {d : ℕ} {M K : Type w}
    [AddCommGroup M] [Module S M] [AddCommGroup K] [Module S K]
    (h : Module.IsPartialProjectiveResolution S d M K) :
    letI : Module R M := Module.compHom M eR.toRingHom
    letI : Module R K := Module.compHom K eR.toRingHom
    Module.IsPartialProjectiveResolution R d M K := by
  letI : Module R M := Module.compHom M eR.toRingHom
  letI : Module R K := Module.compHom K eR.toRingHom
  letI : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eR
  induction h with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      letI : Module R F := Module.compHom F eR.toRingHom
      let eF : F ≃ₛₗ[eR.symm.toRingHom] F :=
        { Equiv.refl F with
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun s x ↦ by
            change s • x = eR (eR.symm s) • x
            rw [eR.apply_symm_apply] }
      letI : Module.Projective R F := Module.Projective.of_equiv eF
      let fR : F →ₗ[R] M :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun r x ↦ f.map_smul (eR r) x }
      let iR : K →ₗ[R] F :=
        { toFun := i
          map_add' := i.map_add
          map_smul' := fun r x ↦ i.map_smul (eR r) x }
      have hexactR : Function.Exact iR fR := by
        change Function.Exact i f
        exact LinearMap.exact_iff.mpr hexact.symm
      exact Module.IsPartialProjectiveResolution.zero fR hf iR hi
        (LinearMap.exact_iff.mp hexactR).symm
  | @succ d M _ _ K' _ _ K _ _ h F _ _ _ f hf i hi hexact ih =>
      letI : Module R K' := Module.compHom K' eR.toRingHom
      letI : Module R F := Module.compHom F eR.toRingHom
      let eF : F ≃ₛₗ[eR.symm.toRingHom] F :=
        { Equiv.refl F with
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun s x ↦ by
            change s • x = eR (eR.symm s) • x
            rw [eR.apply_symm_apply] }
      letI : Module.Projective R F := Module.Projective.of_equiv eF
      let fR : F →ₗ[R] K' :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun r x ↦ f.map_smul (eR r) x }
      let iR : K →ₗ[R] F :=
        { toFun := i
          map_add' := i.map_add
          map_smul' := fun r x ↦ i.map_smul (eR r) x }
      have hexactR : Function.Exact iR fR := by
        change Function.Exact i f
        exact LinearMap.exact_iff.mpr hexact.symm
      exact Module.IsPartialProjectiveResolution.succ ih fR hf iR hi
        (LinearMap.exact_iff.mp hexactR).symm

-- The module carriers live in the ambient universe of the polynomial ring; introducing an
-- independent third universe makes the iterated localization tensors prohibitively costly
-- to normalize without strengthening this theorem's polynomial-matrix use case.
/-- If the resolved module is coefficient-flat after localization at one polynomial prime,
then the terminal syzygy of a sufficiently long finite polynomial resolution is free on a
principal neighbourhood of that prime. -/
theorem exists_away_free_final_of_flat_localizationAtPrime
    {A : Type u} {sigma : Type v}
    [CommRing A] [IsNoetherianRing A] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type (max u v)}
    [AddCommGroup M] [Module (MvPolynomial sigma A) M]
    [AddCommGroup K] [Module (MvPolynomial sigma A) K]
    [Module.Finite (MvPolynomial sigma A) M]
    [Module.Finite (MvPolynomial sigma A) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma A) e M K)
    (hM : Module.Flat A
      (Localization.AtPrime q.asIdeal ⊗[MvPolynomial sigma A] M))
    (he : Nat.card sigma - 1 ≤ e) :
    ∃ f : MvPolynomial sigma A, f ∉ q.asIdeal ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away f K) := by
  let S := MvPolynomial sigma A
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* S)
  let Ap := Localization.AtPrime p.asIdeal
  let Sq := MvPolynomial sigma Ap
  let pc := Submonoid.map
    (MvPolynomial.C : A →+* S).toMonoidHom p.asIdeal.primeCompl
  letI : Algebra S Sq := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization pc Sq :=
    MvPolynomial.isLocalization p.asIdeal.primeCompl Ap
  let q' := MvPolynomial.coefficientLocalizedPrime q
  let T := Localization.AtPrime q'.asIdeal
  let commRingT : CommRing T := inferInstance
  letI : CommRing T := commRingT
  letI : CommSemiring T := commRingT.toCommSemiring
  letI : Semiring T := commRingT.toCommSemiring.toSemiring
  have hcomap : q'.asIdeal.comap (algebraMap S Sq) = q.asIdeal := by
    have hdisj : Disjoint (pc : Set S) (q.asIdeal : Set S) := by
      rw [Set.disjoint_left]
      intro x hxpc hxq
      obtain ⟨a, ha, rfl⟩ := hxpc
      exact ha hxq
    change Ideal.comap (algebraMap S Sq)
        (q.asIdeal.map (algebraMap S Sq)) = q.asIdeal
    exact IsLocalization.under_map_of_isPrime_disjoint
      pc Sq q.isPrime hdisj
  letI : IsLocalization.AtPrime T q.asIdeal := by
    have hloc : IsLocalization.AtPrime T
        (q'.asIdeal.comap (algebraMap S Sq)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (T := T) pc q'.asIdeal
    change IsLocalization
      (q'.asIdeal.comap (algebraMap S Sq)).primeCompl T at hloc
    change IsLocalization q.asIdeal.primeCompl T
    have hcompl :
        (q'.asIdeal.comap (algebraMap S Sq)).primeCompl =
          q.asIdeal.primeCompl := by
      ext x
      change (x ∉ q'.asIdeal.comap (algebraMap S Sq)) ↔
        (x ∉ q.asIdeal)
      rw [hcomap]
    exact hcompl ▸ hloc
  letI : Module.Flat S T :=
    IsLocalization.flat T q.asIdeal.primeCompl
  let MT := T ⊗[S] M
  let KT := T ⊗[S] K
  letI : AddCommGroup MT := TensorProduct.addCommGroup
  letI : AddCommGroup KT := TensorProduct.addCommGroup
  have hresT : Module.IsPartialProjectiveResolution T e
      (T ⊗[S] M) (T ⊗[S] K) :=
    hres.baseChange T
  have hMTA : Module.Flat A MT := by
    let U := Localization.AtPrime q.asIdeal
    let eRing : U ≃ₐ[S] T :=
      IsLocalization.algEquiv q.asIdeal.primeCompl U T
    let eTensor : (U ⊗[S] M) ≃ₗ[S] MT :=
      TensorProduct.congr eRing.toLinearEquiv (LinearEquiv.refl S M)
    let _ : Module.Flat A (U ⊗[S] M) := hM
    exact Module.Flat.of_linearEquiv
      (eTensor.symm.restrictScalars A)
  have hMTAp : @Module.Flat Ap MT _ _
      (Module.compHom MT (algebraMap Ap T)) := by
    have hflat : Module.Flat Ap MT :=
      (Module.flat_iff_of_isLocalization Ap p.asIdeal.primeCompl MT).mpr hMTA
    have hmodule :
        Module.compHom MT (algebraMap Ap T) =
          (TensorProduct.leftModule : Module Ap MT) := by
      apply Module.ext'
      intro a x
      change (algebraMap Ap T a : T) • x = _
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, smul_zero]
      | add x y hx hy => rw [smul_add, smul_add, hx, hy]
      | tmul s m =>
          rw [TensorProduct.smul_tmul']
          exact congrArg (fun t : T => t ⊗ₜ[S] m)
            (IsScalarTower.algebraMap_smul T a s)
    rw [hmodule]
    exact hflat
  have hq' :
      (q'.comap (MvPolynomial.C : Ap →+* Sq)).asIdeal =
        IsLocalRing.maximalIdeal Ap := by
    change Ideal.comap (MvPolynomial.C : Ap →+* Sq) q'.asIdeal =
      IsLocalRing.maximalIdeal Ap
    dsimp only [q', Ap, Sq]
    exact MvPolynomial.coefficientLocalizedPrime_comap_C q
  have hfreeT : Module.Free T KT := by
    let Ap' := ULift.{v} Ap
    let sigma' := ULift.{u} sigma
    let eA : Ap' ≃+* Ap := ULift.ringEquiv
    let S' := MvPolynomial sigma' Ap'
    let eS : S' ≃+* Sq :=
      (MvPolynomial.mapEquiv sigma' eA).trans
        (MvPolynomial.renameEquiv Ap Equiv.ulift).toRingEquiv
    have heS_coeff (a : Ap') :
        eS (MvPolynomial.C a) = MvPolynomial.C (eA a) := by
      change MvPolynomial.rename Equiv.ulift
          (MvPolynomial.map eA.toRingHom (MvPolynomial.C a)) =
        MvPolynomial.C (eA a)
      rw [MvPolynomial.map_C, MvPolynomial.rename_C]
      rfl
    let q0 : PrimeSpectrum S' :=
      (PrimeSpectrum.comapEquiv eS).symm q'
    let T' := Localization.AtPrime q0.asIdeal
    let eT : T' ≃+* T :=
      Localization.localRingEquiv q0.asIdeal q'.asIdeal eS (by rfl)
    letI : IsNoetherianRing Ap' :=
      isNoetherianRing_of_ringEquiv Ap eA.symm
    letI : IsLocalRing Ap' := eA.symm.isLocalRing
    letI : IsLocalHom eA.toRingHom :=
      IsLocalHom.of_surjective eA.toRingHom eA.surjective
    letI : RingHomInvPair eA.toRingHom eA.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eA
    letI : RingHomInvPair eA.symm.toRingHom eA.symm.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eA.symm
    letI : RingHomInvPair eA.symm.symm.toRingHom eA.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm eA.symm
    letI : Module T' MT := Module.compHom MT eT.toRingHom
    letI : Module T' KT := Module.compHom KT eT.toRingHom
    letI : RingHomInvPair eT.toRingHom eT.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eT
    letI : RingHomInvPair eT.symm.toRingHom eT.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm eT
    let eMT : MT ≃ₛₗ[eT.toRingHom] MT :=
      { Equiv.refl MT with
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let eKT : KT ≃ₛₗ[eT.toRingHom] KT :=
      { Equiv.refl KT with
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    letI : Module.Finite T' MT :=
      (eMT.toLinearMap.finite_iff_of_bijective eMT.bijective).mpr inferInstance
    letI : Module.Finite T' KT :=
      (eKT.toLinearMap.finite_iff_of_bijective eKT.bijective).mpr inferInstance
    have hresT' :=
      compHom_ringEquiv (R := T') (S := T) (M := MT) (K := KT) eT hresT
    have hq0 :
        (q0.comap (MvPolynomial.C : Ap' →+* S')).asIdeal =
          IsLocalRing.maximalIdeal Ap' := by
      calc
        (q0.comap (MvPolynomial.C : Ap' →+* S')).asIdeal =
            (IsLocalRing.maximalIdeal Ap).comap eA := by
          rw [← hq']
          ext a
          change eS (MvPolynomial.C a) ∈ q'.asIdeal ↔
            MvPolynomial.C (eA a) ∈ q'.asIdeal
          rw [heS_coeff]
        _ = IsLocalRing.maximalIdeal Ap' :=
          IsLocalRing.maximalIdeal_comap eA.toRingHom
    have heT_coeff (a : Ap') :
        eT (algebraMap Ap' T' a) = algebraMap Ap T (eA a) := by
      change eT (algebraMap S' T' (MvPolynomial.C a)) =
        algebraMap Sq T (MvPolynomial.C (eA a))
      rw [show eT (algebraMap S' T' (MvPolynomial.C a)) =
          algebraMap Sq T (eS (MvPolynomial.C a)) by
        exact Localization.localRingHom_to_map q0.asIdeal q'.asIdeal
          eS (by rfl) (MvPolynomial.C a)]
      rw [heS_coeff]
    have hMTA' : @Module.Flat Ap' MT _ _
        (Module.compHom MT (algebraMap Ap' T')) := by
      letI : Module Ap MT :=
        Module.compHom MT (algebraMap Ap T)
      letI : Module Ap' MT :=
        Module.compHom MT (algebraMap Ap' T')
      letI : Module.Flat Ap MT := hMTAp
      let eMA : MT ≃ₛₗ[eA.symm.toRingHom] MT :=
        { Equiv.refl MT with
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            change (algebraMap Ap T a) • x =
              eT (algebraMap Ap' T' (eA.symm a)) • x
            rw [heT_coeff, eA.apply_symm_apply] }
      exact @Module.Flat.of_ringEquiv Ap Ap' MT MT _ _ _ _ _ _
        eA.symm (RingHomInvPair.of_ringEquiv eA.symm)
          (RingHomInvPair.of_ringEquiv_symm eA.symm) eMA hMTAp
    have he' : Nat.card sigma' - 1 ≤ e := by
      simpa [sigma', Nat.card_ulift] using he
    have hfreeT' : Module.Free T' KT :=
      hresT'.free_polynomialLocalization_of_flat q0 hq0 hMTA' he'
    let _ : Module.Free T' KT := hfreeT'
    exact Module.Free.of_equiv eKT
  have hqfree : q ∈ Module.freeLocus S K :=
    (Module.mem_freeLocus_iff_tensor q T).mpr hfreeT
  let _ : Module.FinitePresentation S K :=
    Module.finitePresentation_of_finite S K
  apply Module.FinitePresentation.exists_away_free_of_free_atPrime q
  exact (Module.mem_freeLocus_iff_tensor q
    (Localization.AtPrime q.asIdeal)).mp hqfree

/-- The terminal syzygy of a sufficiently long polynomial resolution of a
coefficient-flat module is free on a principal neighbourhood of any polynomial
prime. -/
theorem exists_away_free_final_of_flat_at_arbitraryPrime
    {A sigma : Type u} [CommRing A] [IsNoetherianRing A] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial sigma A) M]
    [AddCommGroup K] [Module (MvPolynomial sigma A) K]
    [Module.Finite (MvPolynomial sigma A) M]
    [Module.Finite (MvPolynomial sigma A) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma A) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M (algebraMap A (MvPolynomial sigma A))))
    (he : Nat.card sigma - 1 ≤ e) :
    ∃ f : MvPolynomial sigma A, f ∉ q.asIdeal ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away f K) := by
  let S := MvPolynomial sigma A
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* S)
  let Ap := Localization.AtPrime p.asIdeal
  let Sq := MvPolynomial sigma Ap
  let pc := Submonoid.map
    (MvPolynomial.C : A →+* S).toMonoidHom p.asIdeal.primeCompl
  letI : Algebra S Sq := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization pc Sq :=
    MvPolynomial.isLocalization p.asIdeal.primeCompl Ap
  letI : Module.Flat S Sq := IsLocalization.flat Sq pc
  let q' := MvPolynomial.coefficientLocalizedPrime q
  let Mq := Sq ⊗[S] M
  let Kq := Sq ⊗[S] K
  have hresq : Module.IsPartialProjectiveResolution Sq e Mq Kq :=
    hres.baseChange Sq
  have hMq : @Module.Flat Ap Mq _ _
      (Module.compHom Mq (algebraMap Ap Sq)) := by
    letI : Module A M := Module.compHom M (algebraMap A S)
    letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
    let _ : Module.Flat A M := hM
    have hflat : Module.Flat Ap Mq :=
      Module.Flat.baseChange_of_isPushout A Ap S Sq M
    have hmodule :
        Module.compHom Mq (algebraMap Ap Sq) =
          (TensorProduct.leftModule : Module Ap Mq) := by
      apply Module.ext'
      intro a x
      change (algebraMap Ap Sq a : Sq) • x = _
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, smul_zero]
      | add x y hx hy => rw [smul_add, smul_add, hx, hy]
      | tmul s m =>
          rw [TensorProduct.smul_tmul']
          exact congrArg (fun t : Sq => t ⊗ₜ[S] m)
            (IsScalarTower.algebraMap_smul Sq a s)
    rw [hmodule]
    exact hflat
  obtain ⟨g, hg, hgproj⟩ :=
    hresq.exists_away_projective_final_of_flat q'
      (by
        change Ideal.comap (MvPolynomial.C : Ap →+* Sq) q'.asIdeal =
          IsLocalRing.maximalIdeal Ap
        dsimp only [q', Ap, Sq]
        exact MvPolynomial.coefficientLocalizedPrime_comap_C q)
      hMq he
  let _ : Module.FinitePresentation Sq Kq :=
    Module.finitePresentation_of_finite Sq Kq
  have hq'free : q' ∈ Module.freeLocus Sq Kq :=
    (Module.basicOpen_subset_freeLocus_iff.mpr hgproj) hg
  let T := Localization.AtPrime q'.asIdeal
  have hfreeT : Module.Free T (T ⊗[Sq] Kq) :=
    (Module.mem_freeLocus_iff_tensor q' T).mp hq'free
  have hcomap : q'.asIdeal.comap (algebraMap S Sq) = q.asIdeal := by
    have hdisj : Disjoint (pc : Set S) (q.asIdeal : Set S) := by
      rw [Set.disjoint_left]
      intro x hxpc hxq
      obtain ⟨a, ha, rfl⟩ := hxpc
      exact ha hxq
    change Ideal.comap (algebraMap S Sq)
        (q.asIdeal.map (algebraMap S Sq)) = q.asIdeal
    exact IsLocalization.under_map_of_isPrime_disjoint
      pc Sq q.isPrime hdisj
  letI : IsLocalization.AtPrime T q.asIdeal := by
    have hloc : IsLocalization.AtPrime T
        (q'.asIdeal.comap (algebraMap S Sq)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (T := T) pc q'.asIdeal
    change IsLocalization
      (q'.asIdeal.comap (algebraMap S Sq)).primeCompl T at hloc
    change IsLocalization q.asIdeal.primeCompl T
    have hcompl :
        (q'.asIdeal.comap (algebraMap S Sq)).primeCompl =
          q.asIdeal.primeCompl := by
      ext x
      change (x ∉ q'.asIdeal.comap (algebraMap S Sq)) ↔
        (x ∉ q.asIdeal)
      rw [hcomap]
    exact hcompl ▸ hloc
  have hfreeOriginal : Module.Free T (T ⊗[S] K) := by
    let _ : Module.Free T (T ⊗[Sq] Kq) := hfreeT
    exact Module.Free.of_equiv
      (AlgebraTensorModule.cancelBaseChange S Sq T T K)
  have hqfree : q ∈ Module.freeLocus S K :=
    (Module.mem_freeLocus_iff_tensor q T).mpr hfreeOriginal
  let _ : Module.FinitePresentation S K :=
    Module.finitePresentation_of_finite S K
  apply Module.FinitePresentation.exists_away_free_of_free_atPrime q
  exact (Module.mem_freeLocus_iff_tensor q
    (Localization.AtPrime q.asIdeal)).mp hqfree

/-- Projective form of
`exists_away_free_final_of_flat_at_arbitraryPrime`. -/
theorem exists_away_projective_final_of_flat_at_arbitraryPrime
    {A sigma : Type u} [CommRing A] [IsNoetherianRing A] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial sigma A) M]
    [AddCommGroup K] [Module (MvPolynomial sigma A) K]
    [Module.Finite (MvPolynomial sigma A) M]
    [Module.Finite (MvPolynomial sigma A) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma A) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M (algebraMap A (MvPolynomial sigma A))))
    (he : Nat.card sigma - 1 ≤ e) :
    ∃ f : MvPolynomial sigma A, f ∉ q.asIdeal ∧
      Module.Projective (Localization.Away f)
        (LocalizedModule.Away f K) := by
  obtain ⟨f, hf, hfree⟩ :=
    hres.exists_away_free_final_of_flat_at_arbitraryPrime q hM he
  let _ : Module.Free (Localization.Away f) (LocalizedModule.Away f K) :=
    hfree
  exact ⟨f, hf, Module.Projective.of_free⟩

end Module.IsPartialProjectiveResolution

end

end
