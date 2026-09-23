module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Localized relative fibres as pushouts

Let `p` be a prime of a ring `R`, let `S` be an `R`-algebra, and let `q` be a
prime of the fibre `κ(p) ⊗[R] S`.  If `r` is the contraction of `q` to `S`,
then the local ring of the fibre at `q` is the quotient of `S_r` by the
extension of `p`.  The equivalence is linear over `S_r`, not merely over
`R_p`.

Combining this equivalence with the usual tensor/quotient equivalence proves
that the square formed by `R_p`, `S_r`, `κ(p)`, and the localized fibre is a
pushout.  This is the concrete ring-theoretic bridge from exactness on a
relative fibre to the local closed-fibre flatness criterion.

Main declarations:

* `Ideal.Fiber.localizationAlgEquivQuotientOverLocalizedSource`;
* `PrimeSpectrum.localizedRelativeFibre_isPushout`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Ideal

/-- The local ring of a relative fibre is the quotient of the corresponding
localization of the source, as an algebra over that localized source. -/
noncomputable def Fiber.localizationAlgEquivQuotientOverLocalizedSource
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    let r := q.comap Algebra.TensorProduct.includeRight
    let Sr := Localization.AtPrime r
    let pS := p.map (algebraMap R S)
    letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
    letI : q.LiesOver r := ⟨rfl⟩
    letI : Algebra Sr (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver r q
    Localization.AtPrime q ≃ₐ[Sr]
      Sr ⧸ pS.map (algebraMap S Sr) := by
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pS := p.map (algebraMap R S)
  let SpS := S ⧸ pS
  let r := q.comap Algebra.TensorProduct.includeRight
  let Sr := Localization.AtPrime r
  let e₁ : p.Fiber S ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp) :=
    Fiber.algEquivAux₁ p
  let q' : Ideal (Sp ⧸ pS.map (algebraMap S Sp)) := q.comap e₁.symm
  haveI : (q'.under SpS).LiesOver r :=
    under_liesOver_of_liesOver SpS q' (q.under S)
  haveI : Algebra.algebraMapSubmonoid SpS r.primeCompl =
      (q'.under SpS).primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (q'.under SpS) r Ideal.Quotient.mk_surjective
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid SpS r.primeCompl)
      (Localization.AtPrime q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid SpS
        (Algebra.algebraMapSubmonoid S p.primeCompl))
      (Localization.AtPrime q') q'
  haveI := IsScalarTower.to₁₃₄ S SpS (Localization.AtPrime q')
  haveI := IsScalarTower.to₁₃₄ S SpS
    (Sr ⧸ pS.map (algebraMap S Sr))
  let eS : Localization.AtPrime q ≃ₐ[S]
      Sr ⧸ pS.map (algebraMap S Sr) :=
    (Localization.localAlgEquiv q' q e₁.symm rfl).symm |>.trans
      ((IsLocalization.algEquiv
        (Algebra.algebraMapSubmonoid SpS r.primeCompl)
        (Localization.AtPrime q')
        (Sr ⧸ pS.map (algebraMap S Sr))).restrictScalars S)
  haveI : q.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver r q
  exact eS.extendScalarsOfIsLocalization Sr r.primeCompl

end Ideal

namespace PrimeSpectrum

set_option maxRecDepth 2000

/-- The local ring of a relative fibre is the pushout of the localized source
along the residue-field map of the localized base. -/
theorem localizedRelativeFibre_isPushout
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (qf : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let r := qf.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    let k := p.asIdeal.ResidueField
    let A := Localization.AtPrime qf.asIdeal
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : qf.asIdeal.LiesOver r := ⟨rfl⟩
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    letI : Algebra Sr A :=
      Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
    Algebra.IsPushout Rp Sr k A := by
  let r := qf.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  let k := p.asIdeal.ResidueField
  let A := Localization.AtPrime qf.asIdeal
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hq_over : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  haveI : r.LiesOver p.asIdeal := hq_over
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  let I := p.asIdeal.map (algebraMap R Sr)
  let J := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sr)
  have hIJ : I = J := by
    dsimp only [I, J, Rp]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  let Ip :=
    (p.asIdeal.map (algebraMap R S)).map (algebraMap S Sr)
  have hIpI : Ip = I := by
    dsimp only [Ip, I]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eSrc :=
    Ideal.Fiber.localizationAlgEquivQuotientOverLocalizedSource
      p.asIdeal qf.asIdeal
  change A ≃ₐ[Sr] Sr ⧸ Ip at eSrc
  let e0S : A ≃ₐ[Sr] Sr ⧸ I :=
    eSrc.trans (Ideal.quotientEquivAlgOfEq Sr hIpI)
  let eIJ : (Sr ⧸ I) ≃ₐ[Sr] (Sr ⧸ J) :=
    Ideal.quotientEquivAlgOfEq Sr hIJ
  let eTQ : (Sr ⊗[Rp] k) ≃ₐ[Sr] (Sr ⧸ J) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sr
      (IsLocalRing.maximalIdeal Rp)).symm
  letI : Algebra k (Sr ⊗[Rp] k) :=
    Algebra.TensorProduct.rightAlgebra
  let e : (Sr ⊗[Rp] k) ≃ₐ[Sr] A :=
    (eTQ.trans eIJ.symm).trans e0S.symm
  apply Algebra.IsPushout.of_equiv e
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  change e (algebraMap k (Sr ⊗[Rp] k) (IsLocalRing.residue Rp x)) =
    algebraMap k A (IsLocalRing.residue Rp x)
  rw [show algebraMap k (Sr ⊗[Rp] k) (IsLocalRing.residue Rp x) =
      1 ⊗ₜ[Rp] IsLocalRing.residue Rp x by rfl]
  dsimp only [e, AlgEquiv.trans_apply]
  rw [show eTQ (1 ⊗ₜ[Rp] IsLocalRing.residue Rp x) =
      Submodule.Quotient.mk (x • (1 : Sr)) by rfl]
  rw [show eIJ.symm (Submodule.Quotient.mk (x • (1 : Sr))) =
      Submodule.Quotient.mk (x • (1 : Sr)) by rfl]
  rw [show Submodule.Quotient.mk (x • (1 : Sr)) =
      algebraMap Sr (Sr ⧸ I) (algebraMap Rp Sr x) by
    simp only [Algebra.smul_def, mul_one]
    rfl]
  rw [e0S.symm.commutes]
  rw [← IsScalarTower.algebraMap_apply Rp Sr A]
  change algebraMap Rp A x = algebraMap k A (algebraMap Rp k x)
  exact (IsScalarTower.algebraMap_apply Rp k A x).symm

end PrimeSpectrum

end

end
