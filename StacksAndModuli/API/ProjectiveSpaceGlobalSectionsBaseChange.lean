module

public import StacksAndModuli.API.PolynomialProjectiveGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveSpaceOverMapIso

/-!
# Global sections on relative projective space after field extension

This file transports the finite-cover base-change theorem from intrinsic
polynomial `Proj` to the relative projective-space model used in Chapter 2.
As a consequence, a Hilbert polynomial over a field automatically gives the
corresponding fieldwise Hilbert polynomial.

Main declarations:

* `Scheme.projectiveSpaceGlobalSectionsBaseChangeLinearEquiv`;
* `Scheme.HasHilbertPolynomialOver.hasFiberwise_over_field`.
-/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Global sections of a quasicoherent module on relative projective space
commute with arbitrary extension of the coefficient field. -/
noncomputable def Scheme.projectiveSpaceGlobalSectionsBaseChangeLinearEquiv
    (n : ℕ) {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of K))).Modules)
    [Q.IsQuasicoherent] :
    let g := Scheme.projectiveSpaceOverMap n
      (Spec.map (CommRingCat.ofHom f))
    let N := (Scheme.Modules.pullback g).obj Q
    let pK := Scheme.projectiveSpaceOverπ n (Spec (.of K))
    let pL := Scheme.projectiveSpaceOverπ n (Spec (.of L))
    letI : Algebra K L := f.toAlgebra
    letI : Module K Γ(Q, ⊤) := Scheme.Modules.globalSectionsModule pK Q
    letI : Module L Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pL N
    L ⊗[K] Γ(Q, ⊤) ≃ₗ[L] Γ(N, ⊤) := by
  let eK := Proj.polynomialProjOverSpecIso (Fin (n + 1)) K
  let eL := Proj.polynomialProjOverSpecIso (Fin (n + 1)) L
  let g := Scheme.projectiveSpaceOverMap n
    (Spec.map (CommRingCat.ofHom f))
  let gp := Proj.polynomialMap (Fin (n + 1)) f
  let pK := Scheme.projectiveSpaceOverπ n (Spec (.of K))
  let pL := Scheme.projectiveSpaceOverπ n (Spec (.of L))
  let ppK := Proj.polynomialToSpec (Fin (n + 1)) K
  let ppL := Proj.polynomialToSpec (Fin (n + 1)) L
  let M := (Scheme.Modules.pullback eK.inv).obj Q
  let N := (Scheme.Modules.pullback g).obj Q
  let NP := (Scheme.Modules.pullback gp).obj M
  let NL := (Scheme.Modules.pullback eL.inv).obj N
  letI : Algebra K L := f.toAlgebra
  letI : Module K Γ(Q, ⊤) := Scheme.Modules.globalSectionsModule pK Q
  letI : Module L Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pL N
  letI : Module K Γ(M, ⊤) := Scheme.Modules.globalSectionsModule ppK M
  letI : Module L Γ(NP, ⊤) := Scheme.Modules.globalSectionsModule ppL NP
  letI : Module L Γ(NL, ⊤) := Scheme.Modules.globalSectionsModule ppL NL
  let aKaux := Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv
    eK.inv pK Q (Iso.refl M)
  have hK : eK.inv ≫ pK = ppK := by
    apply (cancel_epi eK.hom).1
    rw [eK.hom_inv_id_assoc]
    exact (Proj.polynomialProjOverSpecIso_hom_toSpec (Fin (n + 1)) K).symm
  rw [hK] at aKaux
  let aK : Γ(Q, ⊤) ≃ₗ[K] Γ(M, ⊤) := aKaux
  let aLaux := Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv
    eL.inv pL N (Iso.refl NL)
  have hL : eL.inv ≫ pL = ppL := by
    apply (cancel_epi eL.hom).1
    rw [eL.hom_inv_id_assoc]
    exact (Proj.polynomialProjOverSpecIso_hom_toSpec (Fin (n + 1)) L).symm
  rw [hL] at aLaux
  let aL : Γ(N, ⊤) ≃ₗ[L] Γ(NL, ⊤) := aLaux
  let eSource := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl L L) aK
  let ePoly := Proj.polynomialProjectiveGlobalSectionsBaseChangeLinearEquiv n f M
  let eBC := ProjectiveSpace.pullbackPolynomialTransportIso n f Q
  let eBCΓ := Scheme.Modules.globalSectionsLinearEquivOfIso ppL eBC
  exact eSource.trans (ePoly.trans (eBCΓ.trans aL.symm))

/-- Over a field, a Hilbert polynomial of a quasicoherent module on projective
space is automatically valid after every extension of the coefficient field. -/
theorem Scheme.HasHilbertPolynomialOver.hasFiberwise_over_field
    (n : ℕ) {K : Type u} [Field K]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of K))).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ)
    (hQ : Scheme.HasHilbertPolynomialOver Q P) :
    Scheme.HasFiberwiseHilbertPolynomial Q P := by
  apply hQ.hasFiberwise_of_naturalDegreeGlobalSectionsBaseChange_canonical n
  intro L _ f d
  exact Scheme.projectiveSpaceGlobalSectionsBaseChangeLinearEquiv n f
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))

end AlgebraicGeometry
