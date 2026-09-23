module

public import StacksAndModuli.API.FlatLocal
public import StacksAndModuli.API.SemilinearTransport
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Localized flatness under coefficient base change for polynomial matrices

Let `R → S` be a map of coefficient rings, let `G` be a finite matrix over
`R[x]`, and let `q` be a prime of `S[x]`. If the cokernel presented by `G`,
localized at the contraction of `q`, is flat over `R`, then the cokernel
presented by the coefficientwise image of `G`, localized at `q`, is flat over
`S`.

The proof identifies the two polynomial cokernels by scalar extension. It then
cancels the localization already present over `R[x]`, uses that
`S[x] = S ⊗[R] R[x]`, and finally localizes the resulting `S`-flat module at
`q`.

Main declaration:

* `Module.FinitePresentation.flat_localizationAtPrime_polynomialMatrixCokernel_map`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open TensorProduct

universe u v

namespace Module.FinitePresentation

variable {R S : Type u} {sigma : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Flatness over the coefficient ring of a localized polynomial-matrix cokernel
ascends along coefficient base change and localization at a prime above the
contracted prime. -/
theorem flat_localizationAtPrime_polynomialMatrixCokernel_map
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial sigma R))
    (q : Ideal (MvPolynomial sigma S)) [q.IsPrime]
    (hflat : Module.Flat R
      (Localization.AtPrime
          (q.comap (MvPolynomial.map (algebraMap R S))) ⊗[MvPolynomial sigma R]
        polynomialMatrixCokernel G)) :
    Module.Flat S
      (Localization.AtPrime q ⊗[MvPolynomial sigma S]
        polynomialMatrixCokernel
          (G.map (MvPolynomial.map (algebraMap R S)))) := by
  let P := MvPolynomial sigma R
  let Q := MvPolynomial sigma S
  let p : Ideal P := q.comap (MvPolynomial.map (algebraMap R S))
  let TP := Localization.AtPrime p
  let TQ := Localization.AtPrime q
  let N := polynomialMatrixCokernel G
  let GQ := G.map (MvPolynomial.map (algebraMap R S))
  let NQ := polynomialMatrixCokernel GQ
  let L := TP ⊗[P] N
  let K := TQ ⊗[Q] NQ
  change Module.Flat S K
  let algPQ : Algebra P Q := MvPolynomial.algebraMvPolynomial
  letI : Algebra P Q := algPQ
  letI : SMul P Q := algPQ.toSMul
  let algPTP : Algebra P TP := inferInstance
  letI : Algebra P TP := algPTP
  letI : SMul P TP := algPTP.toSMul
  let algQTQ : Algebra Q TQ := inferInstance
  letI : Algebra Q TQ := algQTQ
  letI : SMul Q TQ := algQTQ.toSMul
  let t : TP →+* TQ := Localization.localRingHom p q (algebraMap P Q) rfl
  let algPTQ : Algebra P TQ := Algebra.compHom TQ (algebraMap P Q)
  letI : Algebra P TQ := algPTQ
  letI : SMul P TQ := algPTQ.toSMul
  let algTPTQ : Algebra TP TQ := t.toAlgebra
  letI : Algebra TP TQ := algTPTQ
  letI : SMul TP TQ := algTPTQ.toSMul
  letI : IsScalarTower P Q TQ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower P TP TQ := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap Q TQ (algebraMap P Q x) = t (algebraMap P TP x)
    exact (Localization.localRingHom_to_map p q (algebraMap P Q) rfl x).symm)
  -- The two polynomial cokernels are related by scalar extension.
  let gQ : (Fin m → Q) →ₗ[Q] (Fin n → Q) := Matrix.toLin' GQ
  let fQ : (Fin n → Q) →ₗ[Q] NQ := (LinearMap.range gQ).mkQ
  let eN : Q ⊗[P] N ≃ₗ[Q] NQ := by
    apply polynomialPresentationBaseChangeEquivOfMap fQ gQ G
    · change G.map (MvPolynomial.map (algebraMap R S)) = LinearMap.toMatrix' gQ
      change GQ = LinearMap.toMatrix' (Matrix.toLin' GQ)
      exact (LinearMap.toMatrix'_toLin' GQ).symm
    · exact Submodule.mkQ_surjective _
    · rw [LinearMap.exact_iff]
      exact Submodule.ker_mkQ _
  letI : Module P NQ := Module.compHom NQ (algebraMap P Q)
  letI : IsScalarTower P Q NQ := IsScalarTower.of_compHom P Q NQ
  let v : N →ₗ[P] NQ :=
    (eN.toLinearMap.restrictScalars P).comp (TensorProduct.mk P Q N 1)
  have hv : IsBaseChange Q v := by
    apply IsBaseChange.of_equiv eN
    intro x
    simp [v]
  let u : N →ₗ[P] L := TensorProduct.mk P TP N 1
  have hu : IsBaseChange TP u := TensorProduct.isBaseChange P N TP
  let w : NQ →ₗ[Q] K := TensorProduct.mk Q TQ NQ 1
  have hw : IsBaseChange TQ w := TensorProduct.isBaseChange Q NQ TQ
  let modTQK : Module TQ K := inferInstance
  let modQK₀ : Module Q K := inferInstance
  let towerQTQK : IsScalarTower Q TQ K := inferInstance
  letI : Module TQ K := modTQK
  letI : SMul TQ K := modTQK.toSMul
  letI : Module Q K := modQK₀
  letI : SMul Q K := modQK₀.toSMul
  letI : IsScalarTower Q TQ K := towerQTQK
  let modPK : Module P K := Module.compHom K (algebraMap P TQ)
  letI : Module P K := modPK
  letI : SMul P K := modPK.toSMul
  letI : IsScalarTower P TQ K :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower P Q K := IsScalarTower.to₁₂₄ P Q TQ K
  let modTPK : Module TP K := Module.compHom K (algebraMap TP TQ)
  letI : Module TP K := modTPK
  letI : SMul TP K := modTPK.toSMul
  letI : IsScalarTower TP TQ K :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower P TP K := IsScalarTower.to₁₂₄ P TP TQ K
  let g : N →ₗ[P] K := (w.restrictScalars P).comp v
  have hg : IsBaseChange TQ g := hv.comp hw
  let h : L →ₗ[TP] K := hu.lift g
  have hh : IsBaseChange TQ h := by
    apply IsBaseChange.of_comp hu
    simpa only [h, hu.lift_comp] using hg
  -- First base-change the already-flat localized module across the polynomial pushout.
  let LQ := Q ⊗[P] L
  let z : L →ₗ[P] LQ := TensorProduct.mk P Q L 1
  have hz : IsBaseChange Q z := TensorProduct.isBaseChange P L Q
  let k : LQ →ₗ[Q] K := hz.lift (h.restrictScalars P)
  have hk : IsBaseChange TQ k := by
    apply IsBaseChange.of_comp hz
    have hrestr : IsBaseChange TQ (h.restrictScalars P) := by
      let i : L →ₗ[P] L := LinearMap.id
      have hi : IsBaseChange TP i := by
        letI : CompatibleSMul P TP TP L :=
          IsLocalization.tensorProduct_compatibleSMul p.primeCompl TP TP L
        apply IsBaseChange.of_equiv
          (IsLocalization.moduleLid p.primeCompl TP L)
        intro x
        change TensorProduct.lidOfCompatibleSMul P TP L
          (1 ⊗ₜ[P] x) = x
        rw [TensorProduct.lidOfCompatibleSMul_tmul, one_smul]
      have hc := hi.comp hh
      simpa only [i, LinearMap.restrictScalars_id, LinearMap.comp_id] using hc
    simpa only [k, hz.lift_comp] using hrestr
  haveI : IsLocalizedModule q.primeCompl k :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl TQ k).mpr hk
  haveI : Algebra.IsPushout R S P Q := inferInstance
  haveI : Module.Flat R L := hflat
  have hflatLQ : Module.Flat S LQ :=
    Module.Flat.baseChange_of_isPushout R S P Q L
  letI : Module.Flat S LQ := hflatLQ
  exact Module.Flat.of_isLocalizedModule_of_flat_base
    (N := LQ) (Nₗ := K) S q.primeCompl k

end Module.FinitePresentation

end

end
