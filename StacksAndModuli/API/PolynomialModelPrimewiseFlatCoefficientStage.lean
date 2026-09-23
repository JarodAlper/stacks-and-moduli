module

public import StacksAndModuli.API.FinitePresentationLocalizationFactorization
public import StacksAndModuli.API.LocalNoetherianPolynomialFlatStageContainingCoefficients
public import StacksAndModuli.API.FlatCoefficientModelPrimewiseNeighborhood
public import StacksAndModuli.API.PolynomialMatrixLocalizedFlatBaseChange

/-!
# Primewise coefficient-flat stages for flat polynomial models

This file combines local Noetherian approximation with finite-presentation denominator
clearing.  Starting from a polynomial model whose presented module is flat over the
coefficient ring, it constructs, at each prime of the ambient polynomial ring, a canonical
finitely generated integer coefficient stage whose localized matrix cokernel is flat over
that stage.

The proof first finds a finite local coefficient model after coefficient localization.  A
relative denominator-clearing theorem descends that model to the localization of a finite
subalgebra of the original coefficient ring.  Polynomial-matrix base change and localization
then transport the local flatness statement back to the canonical coefficient system.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {R : Type u} {M : Type w} {sigma : Type v} [CommRing R]
variable [AddCommGroup M] [Module (MvPolynomial sigma R) M]

/-- The coefficient-localized polynomial prime contracts to the original prime. -/
theorem coefficientLocalizedPrime_comap_polynomialMap
    {A : Type u} [CommRing A]
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    (MvPolynomial.coefficientLocalizedPrime q).asIdeal.comap
        (MvPolynomial.map (algebraMap A
          (MvPolynomial.coefficientLocalization q))) = q.asIdeal := by
  let p : PrimeSpectrum A :=
    q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let Ap := Localization.AtPrime p.asIdeal
  let S := MvPolynomial sigma A
  let Sp := MvPolynomial sigma Ap
  let pc := Submonoid.map
    (MvPolynomial.C : A →+* S).toMonoidHom p.asIdeal.primeCompl
  letI : Algebra S Sp := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization pc Sp :=
    MvPolynomial.isLocalization p.asIdeal.primeCompl Ap
  have hdisj : Disjoint (pc : Set S) (q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    intro x hxpc hxq
    obtain ⟨a, ha, rfl⟩ := hxpc
    exact ha hxq
  change Ideal.comap (algebraMap S Sp)
      (q.asIdeal.map (algebraMap S Sp)) = q.asIdeal
  exact IsLocalization.under_map_of_isPrime_disjoint
    pc Sp q.isPrime hdisj

theorem flat_localizationAtPrime_polynomialMatrixCokernel_map_of_eq
    {S : Type u} [CommRing S] [Algebra R S]
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial sigma R))
    (q : Ideal (MvPolynomial sigma S)) [q.IsPrime]
    (p₀ : Ideal (MvPolynomial sigma R)) [p₀.IsPrime]
    (hp₀ : q.comap (MvPolynomial.map (algebraMap R S)) = p₀)
    (hflat : Module.Flat R
      (TensorProduct (MvPolynomial sigma R) (Localization.AtPrime p₀)
        (polynomialMatrixCokernel G))) :
    Module.Flat S
      (TensorProduct (MvPolynomial sigma S) (Localization.AtPrime q)
        (polynomialMatrixCokernel
          (G.map (MvPolynomial.map (algebraMap R S))))) := by
  subst p₀
  exact flat_localizationAtPrime_polynomialMatrixCokernel_map G q hflat

/-- Polynomial matrix cokernels commute with extension of coefficients. -/
noncomputable def polynomialMatrixCokernelBaseChangeEquiv
    {R₁ S₁ : Type u} {σ₁ : Type v}
    [CommRing R₁] [CommRing S₁] [Algebra R₁ S₁]
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ₁ R₁)) :
    let P := MvPolynomial σ₁ R₁
    let Q := MvPolynomial σ₁ S₁
    letI : Algebra P Q := MvPolynomial.algebraMvPolynomial
    TensorProduct P Q (polynomialMatrixCokernel G) ≃ₗ[Q]
      polynomialMatrixCokernel
        (G.map (MvPolynomial.map (algebraMap R₁ S₁))) := by
  let P := MvPolynomial σ₁ R₁
  let Q := MvPolynomial σ₁ S₁
  letI : Algebra P Q := MvPolynomial.algebraMvPolynomial
  let GQ := G.map (MvPolynomial.map (algebraMap R₁ S₁))
  let NQ := polynomialMatrixCokernel GQ
  let gQ : (Fin m → Q) →ₗ[Q] (Fin n → Q) := Matrix.toLin' GQ
  let fQ : (Fin n → Q) →ₗ[Q] NQ := (LinearMap.range gQ).mkQ
  apply polynomialPresentationBaseChangeEquivOfMap fQ gQ G
  · change GQ = LinearMap.toMatrix' (Matrix.toLin' GQ)
    exact (LinearMap.toMatrix'_toLin' GQ).symm
  · exact Submodule.mkQ_surjective _
  · rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _

/-- Equal polynomial matrices have canonically linearly equivalent cokernels. -/
noncomputable def polynomialMatrixCokernelCongr
    {R₁ : Type u} {σ₁ : Type v} [CommRing R₁] {m n : ℕ}
    {G H : Matrix (Fin n) (Fin m) (MvPolynomial σ₁ R₁)}
    (h : G = H) :
    polynomialMatrixCokernel G ≃ₗ[MvPolynomial σ₁ R₁]
      polynomialMatrixCokernel H := by
  subst H
  exact LinearEquiv.refl _ _

noncomputable def localSystemStageCokernelEquiv
    [IsLocalRing R]
    (D : PolynomialModel R sigma M) (j : Later R D.localIndex) :
    D.localSystemStage j ≃ₗ[polynomial R sigma j]
      polynomialMatrixCokernel
        (D.localRelation.map (MvPolynomial.map
          (transition R D.localIndex j.1 j.2))) := by
  let K := coefficient R j.1
  let S := MvPolynomial sigma K
  let G := D.localRelation.map (MvPolynomial.map
    (transition R D.localIndex j.1 j.2))
  let g : (Fin D.relations → S) →ₗ[S] (Fin D.generators → S) := Matrix.toLin' G
  let f : (Fin D.generators → S) →ₗ[S] polynomialMatrixCokernel G :=
    (LinearMap.range g).mkQ
  apply polynomialPresentationBaseChangeEquivOfMap f g D.localRelation
  · change D.localRelation.map (MvPolynomial.map
        (algebraMap D.localCoefficient K)) = LinearMap.toMatrix' g
    change G = LinearMap.toMatrix' (Matrix.toLin' G)
    exact (LinearMap.toMatrix'_toLin' G).symm
  · exact Submodule.mkQ_surjective _
  · rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _

variable {A₀ N₀ : Type u} {sigma₀ : Type v} [CommRing A₀]
variable [AddCommGroup N₀] [Module (MvPolynomial sigma₀ A₀) N₀] [Finite sigma₀]

set_option maxHeartbeats 1600000 in
-- The explicit coherence transport crosses several nested localization and tensor-product
-- instances; elaborating those instance-pinned equivalences exceeds the default budget.
theorem exists_coefficientStage_flat_localizationAtPrime_of_flat
    (D : PolynomialModel A₀ sigma₀ N₀)
    (q : PrimeSpectrum (MvPolynomial sigma₀ A₀))
    (hflat :
      letI : Module A₀ N₀ := Module.compHom N₀
        (algebraMap A₀ (MvPolynomial sigma₀ A₀))
      Module.Flat A₀ N₀) :
    ∃ i : CoefficientStage (R := ℤ) D,
      Module.Flat i.1
        (TensorProduct (MvPolynomial sigma₀ i.1)
          (Localization.AtPrime (coefficientStagePrime D q i).asIdeal)
          (polynomialMatrixCokernel (coefficientStageRelation D i))) := by
  let Aq := MvPolynomial.coefficientLocalization q
  let p : Ideal A₀ :=
    (q.comap (MvPolynomial.C : A₀ →+* MvPolynomial sigma₀ A₀)).asIdeal
  let Sq := MvPolynomial sigma₀ Aq
  letI : Algebra (MvPolynomial sigma₀ A₀) Sq :=
    MvPolynomial.algebraMvPolynomial
  let Mq := TensorProduct (MvPolynomial sigma₀ A₀) Sq N₀
  let Dq : PolynomialModel Aq sigma₀ Mq := D.baseChange
  obtain ⟨k, hcontains, hkflat⟩ :=
    D.exists_later_flat_baseChangeLocalSystemStage_containing_originalCoefficients
      q hflat
  let B₀ : Subalgebra ℤ A₀ := D.coefficientRing (R := ℤ)
  let intAlgAq : Algebra ℤ Aq := Ring.toIntAlgebra Aq
  letI : Algebra ℤ Aq := intAlgAq
  let C : Subalgebra ℤ Aq := k.1.1
  let baseToC : B₀ →+* C :=
    { toFun := fun b ↦ ⟨algebraMap A₀ Aq b.1, by
          apply hcontains
          apply Subalgebra.mem_map.mpr
          exact ⟨b, b.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; exact map_one (algebraMap A₀ Aq)
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        exact map_mul (algebraMap A₀ Aq) x.1 y.1
      map_zero' := by apply Subtype.ext; exact map_zero (algebraMap A₀ Aq)
      map_add' := fun x y ↦ by
        apply Subtype.ext
        exact map_add (algebraMap A₀ Aq) x.1 y.1 }
  letI : Algebra B₀ C := baseToC.toAlgebra
  letI : IsScalarTower ℤ B₀ C := IsScalarTower.of_algebraMap_eq fun z : ℤ ↦ by
    apply Subtype.ext
    change algebraMap ℤ Aq z = algebraMap A₀ Aq (algebraMap ℤ A₀ z)
    exact IsScalarTower.algebraMap_apply ℤ A₀ Aq z
  letI : Algebra.FiniteType ℤ B₀ :=
    (Subalgebra.fg_iff_finiteType B₀).mp D.coefficientRing_fg
  letI : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing ℤ B₀
  letI : Algebra.FiniteType ℤ C :=
    (Subalgebra.fg_iff_finiteType C).mp k.1.2
  letI : Algebra.FiniteType B₀ C :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ B₀ C
  letI : Algebra.FinitePresentation B₀ C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra B₀ Aq := Algebra.compHom Aq (algebraMap B₀ A₀)
  let g : C →ₐ[B₀] Aq :=
    { __ := C.val.toRingHom
      commutes' := fun b ↦ by
        change ((algebraMap A₀ Aq) b.1) = (baseToC b : Aq)
        rfl }
  obtain ⟨E, hE, hEfg, hB₀E, f, hf⟩ :=
    Algebra.FinitePresentation.exists_fg_subalgebra_over_factorization_atPrime
      p B₀ D.coefficientRing_fg g
  let gr : C →+* Aq := g.toRingHom
  have gr_commutes (b : B₀) :
      gr (algebraMap B₀ C b) =
        @algebraMap B₀ Aq _ _ this b := g.commutes b
  letI : Algebra B₀ Aq := OreLocalization.instAlgebra
  let g' : C →ₐ[B₀] Aq :=
    { __ := gr
      commutes' := gr_commutes }
  have hgf :
      (Localization.localAlgHom (p.comap E.val) p E.val rfl).comp f = g' := by
    apply AlgHom.ext
    intro c
    exact hf c
  obtain ⟨fₗ, hfₗ⟩ :=
    Algebra.FinitePresentation.exists_localized_source_lift_of_factorization_atPrime
      p E g' f hgf
  let B : Subalgebra ℤ A₀ := E.restrictScalars ℤ
  let i : CoefficientStage (R := ℤ) D := ⟨B, hEfg, hB₀E⟩
  let eBE : B ≃+* E :=
    { toFun := fun b ↦ ⟨b.1, b.2⟩
      invFun := fun e ↦ ⟨e.1, e.2⟩
      left_inv := fun b ↦ Subtype.ext rfl
      right_inv := fun e ↦ Subtype.ext rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have hpBE : p.comap B.val = (p.comap E.val).comap eBE.toRingHom := by
    ext b
    rfl
  let Bp := Localization.AtPrime (p.comap B.val)
  let eBp : Localization.AtPrime (p.comap E.val) ≃+* Bp :=
    Localization.localRingEquiv (p.comap E.val) (p.comap B.val)
      eBE.symm hpBE.symm
  have heBp_algebraMap (e : E) :
      eBp (algebraMap E (Localization.AtPrime (p.comap E.val)) e) =
        algebraMap B Bp (eBE.symm e) := by
    change Localization.localRingHom (p.comap E.val) (p.comap B.val)
      eBE.symm.toRingHom hpBE.symm
        (algebraMap E (Localization.AtPrime (p.comap E.val)) e) = _
    exact Localization.localRingHom_to_map
      (p.comap E.val) (p.comap B.val) eBE.symm.toRingHom hpBE.symm e
  let Rk := coefficient Aq k.1
  let fLoc : Rk →+* Bp := eBp.toRingHom.comp fₗ.toRingHom
  let Pk := MvPolynomial sigma₀ Rk
  let qk : Ideal Pk :=
    polynomialPrimeAtStage (MvPolynomial.coefficientLocalizedPrime q).asIdeal k.1
  let Tk := Localization.AtPrime qk
  let Gk : Matrix (Fin Dq.generators) (Fin Dq.relations)
      (MvPolynomial sigma₀ Rk) :=
    Dq.localRelation.map (MvPolynomial.map
      (transition Aq Dq.localIndex k.1 k.2))
  let eStage := Dq.localSystemStageCokernelEquiv k
  let eLocalized :
      TensorProduct Pk Tk (Dq.localSystemStage k) ≃ₗ[Pk]
        TensorProduct Pk Tk (polynomialMatrixCokernel Gk) :=
    eStage.lTensor Tk
  have hkflat' : Module.Flat Rk
      (TensorProduct Pk Tk (polynomialMatrixCokernel Gk)) := by
    letI : Module.Flat Rk
        (TensorProduct Pk Tk (Dq.localSystemStage k)) := hkflat
    exact Module.Flat.of_linearEquiv (eLocalized.restrictScalars Rk).symm
  let phi : Bp →+* Aq :=
    Localization.localRingHom (p.comap B.val) p B.val.toRingHom rfl
  let phiE : Localization.AtPrime (p.comap E.val) →+* Aq :=
    Localization.localRingHom (p.comap E.val) p E.val.toRingHom rfl
  have hphi_eBp : phi.comp eBp.toRingHom = phiE := by
    apply IsLocalization.ringHom_ext (p.comap E.val).primeCompl
    ext e
    change phi (eBp (algebraMap E
      (Localization.AtPrime (p.comap E.val)) e)) =
        phiE (algebraMap E (Localization.AtPrime (p.comap E.val)) e)
    rw [heBp_algebraMap]
    change Localization.localRingHom (p.comap B.val) p B.val.toRingHom rfl
        (algebraMap B Bp (eBE.symm e)) =
      Localization.localRingHom (p.comap E.val) p E.val.toRingHom rfl
        (algebraMap E (Localization.AtPrime (p.comap E.val)) e)
    rw [Localization.localRingHom_to_map,
      Localization.localRingHom_to_map]
    rfl
  have hfLoc_base (c : C) :
      fLoc (algebraMap C Rk c) = eBp (f c) := by
    exact congrArg eBp (hfₗ c)
  have hphi_f (c : C) : phi (eBp (f c)) = g c := by
    change (phi.comp eBp.toRingHom) (f c) = g c
    rw [hphi_eBp]
    exact hf c
  have hphi_fLoc : phi.comp fLoc = toLimit Aq k.1 := by
    apply IsLocalization.ringHom_ext
      ((IsLocalRing.maximalIdeal Aq).comap C.val).primeCompl
    ext c
    change phi (fLoc (algebraMap C Rk c)) =
      toLimit Aq k.1 (algebraMap C Rk c)
    rw [hfLoc_base c, hphi_f c]
    exact toLimit_algebraMap Aq k.1 c |>.symm
  let QBp := MvPolynomial sigma₀ Bp
  let qBp : Ideal QBp :=
    (MvPolynomial.coefficientLocalizedPrime q).asIdeal.comap
      (MvPolynomial.map phi)
  have hqBp : qBp.IsPrime := Ideal.IsPrime.comap _
  letI : qBp.IsPrime := hqBp
  letI : Algebra Rk Bp := fLoc.toAlgebra
  let polyLoc : Pk →+* QBp := MvPolynomial.map (algebraMap Rk Bp)
  let GkBp : Matrix (Fin Dq.generators) (Fin Dq.relations) QBp :=
    Gk.map polyLoc
  have hcontract :
      qBp.comap polyLoc = qk := by
    ext z
    change MvPolynomial.map phi
        (MvPolynomial.map fLoc z) ∈
          (MvPolynomial.coefficientLocalizedPrime q).asIdeal ↔
      MvPolynomial.map (toLimit Aq k.1) z ∈
        (MvPolynomial.coefficientLocalizedPrime q).asIdeal
    rw [MvPolynomial.map_map]
    change MvPolynomial.map (phi.comp fLoc) z ∈ _ ↔ _
    rw [hphi_fLoc]
  have hBpflat :=
    flat_localizationAtPrime_polynomialMatrixCokernel_map_of_eq
      (R := Rk) (S := Bp) (sigma := sigma₀) Gk qBp qk hcontract hkflat'
  let inc₀C : Dq.coefficientRing (R := ℤ) →ₐ[ℤ] C :=
    Subalgebra.inclusion k.2
  let GC₀ : Matrix (Fin Dq.generators) (Fin Dq.relations)
      (MvPolynomial sigma₀ C) :=
    Dq.modelRelation.map (MvPolynomial.map inc₀C.toRingHom)
  let baseToCAlg : B₀ →ₐ[ℤ] C :=
    { __ := baseToC
      commutes' := fun z ↦ by
        apply Subtype.ext
        change algebraMap A₀ Aq (algebraMap ℤ A₀ z) = algebraMap ℤ Aq z
        exact (IsScalarTower.algebraMap_apply ℤ A₀ Aq z).symm }
  let GCC : Matrix (Fin D.generators) (Fin D.relations)
      (MvPolynomial sigma₀ C) :=
    D.modelRelation.map (MvPolynomial.map baseToCAlg.toRingHom)
  have hGC : GC₀ = GCC := by
    apply Matrix.ext
    intro a b
    apply (MvPolynomial.map_injective C.val.toRingHom fun _ _ h ↦ Subtype.ext h)
    change MvPolynomial.map C.val.toRingHom
        (MvPolynomial.map inc₀C.toRingHom (Dq.modelRelation a b)) =
      MvPolynomial.map C.val.toRingHom
        (MvPolynomial.map baseToCAlg.toRingHom (D.modelRelation a b))
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    have hinc : C.val.toRingHom.comp inc₀C.toRingHom =
        algebraMap (Dq.coefficientRing (R := ℤ)) Aq := by
      ext x
      rfl
    have hbase : C.val.toRingHom.comp baseToCAlg.toRingHom =
        (algebraMap A₀ Aq).comp
          (algebraMap (D.coefficientRing (R := ℤ)) A₀) := by
      ext x
      rfl
    have hq := congrFun (congrFun (Dq.modelRelation_map (R := ℤ)) a) b
    have hD := congrFun (congrFun (D.modelRelation_map (R := ℤ)) a) b
    have hbc := congrFun (congrFun
      (D.toMatrix_baseChangeRelation (B := Aq)) a) b
    change LinearMap.toMatrix' Dq.relation a b = _ at hbc
    rw [Matrix.map_apply] at hq hD hbc
    rw [hinc, hbase, hq, hbc, ← hD, MvPolynomial.map_map]
  let cToRk : C →+* Rk := algebraMap C Rk
  have htransitionBase :
      (transition Aq Dq.localIndex k.1 k.2).comp Dq.localBaseMap =
        cToRk.comp inc₀C.toRingHom := by
    ext x
    exact transition_algebraMap Aq Dq.localIndex k.1 k.2 x
  have hGkC : Gk = GC₀.map (MvPolynomial.map cToRk) := by
    apply Matrix.ext
    intro a b
    change MvPolynomial.map (transition Aq Dq.localIndex k.1 k.2)
        (MvPolynomial.map Dq.localBaseMap (Dq.modelRelation a b)) =
      MvPolynomial.map cToRk
        (MvPolynomial.map inc₀C.toRingHom (Dq.modelRelation a b))
    rw [MvPolynomial.map_map, MvPolynomial.map_map, htransitionBase]
  let fB : C →+* Bp := eBp.toRingHom.comp f.toRingHom
  have hfLocC : fLoc.comp cToRk = fB := by
    ext c
    exact hfLoc_base c
  have hGkBpC : GkBp = GCC.map (MvPolynomial.map fB) := by
    have hGC₀ : GkBp = GC₀.map (MvPolynomial.map fB) := by
      dsimp only [GkBp, QBp]
      rw [hGkC, Matrix.map_map]
      apply Matrix.ext
      intro a b
      change MvPolynomial.map fLoc
          (MvPolynomial.map cToRk (GC₀ a b)) =
        MvPolynomial.map fB (GC₀ a b)
      rw [MvPolynomial.map_map, hfLocC]
    exact hGC₀.trans (congrArg
      (fun G ↦ G.map (MvPolynomial.map fB)) hGC)
  let GB : Matrix (Fin D.generators) (Fin D.relations)
      (MvPolynomial sigma₀ B) := coefficientStageRelation D i
  let inc₀B : B₀ →ₐ[ℤ] B := Subalgebra.inclusion hB₀E
  have hbaseBp :
      (algebraMap B Bp).comp inc₀B.toRingHom =
        fB.comp baseToCAlg.toRingHom := by
    ext b
    change algebraMap B Bp (inc₀B b) = eBp (f (baseToCAlg b))
    have hbC : baseToCAlg b = algebraMap B₀ C b := rfl
    rw [hbC, f.commutes]
    calc
      algebraMap B Bp (inc₀B b) =
          algebraMap B Bp (eBE.symm (algebraMap B₀ E b)) := by rfl
      _ = eBp (algebraMap E (Localization.AtPrime (p.comap E.val))
          (algebraMap B₀ E b)) := (heBp_algebraMap _).symm
      _ = eBp (algebraMap B₀ (Localization.AtPrime (p.comap E.val)) b) := by
        congr 1
  have hGkBp :
      GkBp = GB.map (MvPolynomial.map (algebraMap B Bp)) := by
    dsimp only [Dq, PolynomialModel.baseChange] at hGkBpC ⊢
    refine hGkBpC.trans ?_
    dsimp only [GB, GCC]
    rw [coefficientStageRelation, Matrix.map_map, Matrix.map_map]
    apply Matrix.ext
    intro a b
    change MvPolynomial.map fB
        (MvPolynomial.map baseToCAlg.toRingHom (D.modelRelation a b)) =
      MvPolynomial.map (algebraMap B Bp)
        (MvPolynomial.map inc₀B.toRingHom (D.modelRelation a b))
    rw [MvPolynomial.map_map, MvPolynomial.map_map, hbaseBp]
  let PB := MvPolynomial sigma₀ B
  let qB : Ideal PB := (coefficientStagePrime D q i).asIdeal
  have hphi_B : phi.comp (algebraMap B Bp) =
      (algebraMap A₀ Aq).comp B.val.toRingHom := by
    ext b
    change Localization.localRingHom (p.comap B.val) p B.val.toRingHom rfl
        (algebraMap B Bp b) = algebraMap A₀ Aq b.1
    rw [Localization.localRingHom_to_map]
    rfl
  have hqBpB :
      qBp.comap (MvPolynomial.map (algebraMap B Bp)) = qB := by
    ext z
    change MvPolynomial.map phi
        (MvPolynomial.map (algebraMap B Bp) z) ∈
          (MvPolynomial.coefficientLocalizedPrime q).asIdeal ↔
      coefficientStageToLimit D i z ∈ q.asIdeal
    rw [MvPolynomial.map_map]
    change MvPolynomial.map (phi.comp (algebraMap B Bp)) z ∈ _ ↔ _
    rw [hphi_B, ← MvPolynomial.map_map]
    have hlocal :
        MvPolynomial.map (algebraMap A₀ Aq)
            (MvPolynomial.map B.val.toRingHom z) ∈
              (MvPolynomial.coefficientLocalizedPrime q).asIdeal ↔
          MvPolynomial.map B.val.toRingHom z ∈ q.asIdeal := by
      exact SetLike.ext_iff.mp
        (coefficientLocalizedPrime_comap_polynomialMap q)
          (MvPolynomial.map B.val.toRingHom z)
    rw [hlocal]
    rfl
  let pB : Ideal B := p.comap B.val
  let pc : Submonoid PB := Submonoid.map
    (MvPolynomial.C : B →+* PB).toMonoidHom pB.primeCompl
  let algPBQBp : Algebra PB QBp := MvPolynomial.algebraMvPolynomial
  letI : Algebra PB QBp := algPBQBp
  letI : SMul PB QBp := algPBQBp.toSMul
  let modPBQBp : Module PB QBp := Module.compHom QBp (algebraMap PB QBp)
  letI : Module PB QBp := modPBQBp
  letI : IsLocalization pc QBp :=
    MvPolynomial.isLocalization pB.primeCompl Bp
  let TqBp := Localization.AtPrime qBp
  letI : IsLocalization.AtPrime TqBp qB := by
    have hloc : IsLocalization
        (qBp.comap (algebraMap PB QBp)).primeCompl TqBp :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (T := TqBp) pc qBp
    change IsLocalization
      (qBp.comap (MvPolynomial.map (algebraMap B Bp))).primeCompl TqBp at hloc
    have hcompl :
        (qBp.comap (MvPolynomial.map (algebraMap B Bp))).primeCompl =
          qB.primeCompl := by
      ext x
      change (x ∉ qBp.comap (MvPolynomial.map (algebraMap B Bp))) ↔
        (x ∉ qB)
      rw [hqBpB]
    change IsLocalization qB.primeCompl TqBp
    rw [← hcompl]
    exact hloc
  let TqB := Localization.AtPrime qB
  let NB := polynomialMatrixCokernel GB
  let NBP := polynomialMatrixCokernel GkBp
  let eN : TensorProduct PB QBp NB ≃ₗ[QBp] NBP :=
    (polynomialMatrixCokernelBaseChangeEquiv GB).trans
      (polynomialMatrixCokernelCongr hGkBp.symm)
  let L := TensorProduct PB TqB NB
  let K := TensorProduct QBp TqBp NBP
  have hKflatBp : Module.Flat Bp K := by
    dsimp only [K, NBP, GkBp, polyLoc, QBp]
    exact hBpflat
  let eT : TqB ≃ₐ[PB] TqBp :=
    IsLocalization.algEquiv qB.primeCompl TqB TqBp
  let L' := TensorProduct PB TqBp NB
  let L'' := TensorProduct QBp TqBp (TensorProduct PB QBp NB)
  let eCancel : L'' ≃ₗ[TqBp] L' :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      PB QBp TqBp TqBp NB
  let eReplace : L'' ≃ₗ[TqBp] K :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl TqBp TqBp) eN
  let modBpK : Module Bp K := inferInstance
  letI : Module Bp K := modBpK
  letI : SMul Bp K := modBpK.toSMul
  let modBK : Module B K := Module.compHom K (algebraMap B Bp)
  letI : Module B K := modBK
  letI : SMul B K := modBK.toSMul
  letI : IsScalarTower B Bp K := IsScalarTower.of_compHom B Bp K
  have hKflatB : Module.Flat B K := by
    letI : Module.Flat Bp K := hKflatBp
    exact Module.Flat.trans B Bp K
  let modTqL' : Module TqBp L' := inferInstance
  letI : Module TqBp L' := modTqL'
  letI : SMul TqBp L' := modTqL'.toSMul
  let modPBL' : Module PB L' := inferInstance
  letI : Module PB L' := modPBL'
  letI : SMul PB L' := modPBL'.toSMul
  letI : IsScalarTower PB TqBp L' := by
    apply IsScalarTower.of_algebraMap_smul
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t n => simp
    | add y z hy hz => simp [hy, hz]
  let modTqK : Module TqBp K := inferInstance
  letI : Module TqBp K := modTqK
  letI : SMul TqBp K := modTqK.toSMul
  let modPBK : Module PB K := Module.compHom K (algebraMap PB TqBp)
  letI : Module PB K := modPBK
  letI : SMul PB K := modPBK.toSMul
  letI : IsScalarTower PB TqBp K := IsScalarTower.of_compHom PB TqBp K
  letI : IsScalarTower Bp TqBp TqBp := ⟨by
    intro a t x
    simp [Algebra.smul_def, mul_assoc]
  ⟩
  letI : IsScalarTower Bp TqBp K := TensorProduct.isScalarTower_left
  let eTensor : L ≃ₗ[PB] L' :=
    TensorProduct.congr eT.toLinearEquiv (LinearEquiv.refl PB NB)
  let eMid : L' ≃ₗ[TqBp] K := eCancel.symm.trans eReplace
  let ePB : L ≃ₗ[PB] K :=
    eTensor.trans (eMid.restrictScalars PB)
  have hBT (b : B) :
      algebraMap PB TqBp (algebraMap B PB b) =
        algebraMap Bp TqBp (algebraMap B Bp b) := by
    rw [← IsScalarTower.algebraMap_apply B PB TqBp,
      ← IsScalarTower.algebraMap_apply B Bp TqBp]
  have hPB_smul (x : PB) (y : K) :
      x • y = algebraMap PB TqBp x • y := by
    rfl
  have hB_smul (b : B) (y : K) :
      b • y = algebraMap Bp TqBp (algebraMap B Bp b) • y := by
    change algebraMap B Bp b • y =
      algebraMap Bp TqBp (algebraMap B Bp b) • y
    exact (IsScalarTower.algebraMap_smul TqBp
      (algebraMap B Bp b) y).symm
  letI : IsScalarTower B PB K := ⟨by
    intro b x y
    show (b • x) • y = b • x • y
    rw [Algebra.smul_def, hPB_smul, hB_smul, hPB_smul,
      map_mul, hBT, mul_smul]
  ⟩
  letI : SMul B L := TensorProduct.leftHasSMul
    (R := PB) (R' := B) (M := TqB) (N := NB)
  letI : Module B L := TensorProduct.leftModule
    (R := PB) (R'' := B) (M := TqB) (N := NB)
  letI : IsScalarTower B PB TqB := by infer_instance
  letI : IsScalarTower B PB L := TensorProduct.isScalarTower_left
    (R := PB) (R' := PB) (R'₂ := B) (M := TqB) (N := NB)
  let eTotal : L ≃ₗ[B] K := ePB.restrictScalars B
  have hLflatB : Module.Flat B L := by
    letI : Module.Flat B K := hKflatB
    exact Module.Flat.of_linearEquiv eTotal
  refine ⟨i, ?_⟩
  change Module.Flat B L
  exact hLflatB

/-- A module which is flat over its coefficient ring admits a coefficient-flat canonical
stage at every prime of the ambient polynomial ring. -/
theorem hasCoefficientStageFlatPointAtEveryPrime_of_flat
    (D : PolynomialModel A₀ sigma₀ N₀)
    (hflat :
      letI : Module A₀ N₀ := Module.compHom N₀
        (algebraMap A₀ (MvPolynomial sigma₀ A₀))
      Module.Flat A₀ N₀) :
    HasCoefficientStageFlatPointAtEveryPrime (R := ℤ) D := by
  intro q
  exact D.exists_coefficientStage_flat_localizationAtPrime_of_flat q hflat

end Module.FinitePresentation.PolynomialModel

end

end
