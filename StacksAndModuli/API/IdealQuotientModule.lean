module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Modules over an ideal quotient

If `M` is an `R`-module and `I` is an ideal, the quotient `M / IM` carries its expected
module structure over `R / I`.  Mathlib provides this structure for a few specialized
quotients but not for an arbitrary ideal and module, so this file packages the construction
without installing a global instance.

It also upgrades the canonical `R`-linear tensor/quotient equivalence to an
`R / I`-linear equivalence.

Main declarations:

* `Ideal.Quotient.moduleQuotient`;
* `Ideal.Quotient.moduleQuotient_eq_canonical`;
* `Ideal.Quotient.quotTensorEquivQuotSMul`;
* `Ideal.Quotient.finite_moduleQuotient`;
* `Ideal.Quotient.projective_moduleQuotient`.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

open TensorProduct

namespace Ideal.Quotient

variable {R M : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- The scalar action of `R / I` on `M / IM`. -/
@[instance_reducible]
def smulModuleQuotient (I : Ideal R) :
    SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) where
  smul r x :=
    Quotient.liftOn r (· • x) fun b₁ b₂ h ↦ by
      induction x using Quotient.inductionOn'
      have h' : b₁ - b₂ ∈ (I : Submodule R R) := by
        rwa [← Submodule.quotientRel_def]
      rw [← sub_eq_zero, ← sub_smul,
        Submodule.Quotient.mk''_eq_mk,
        ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h' Submodule.mem_top

/-- The module structure of `R / I` on `M / IM`. -/
@[instance_reducible]
def moduleQuotient (I : Ideal R) :
    Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    smulModuleQuotient I
  exact Function.Surjective.moduleLeft (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (fun _ _ ↦ rfl)

/-- The explicit quotient-module structure agrees with Mathlib's canonical module
structure on `M / IM`.  This permits results proved using `moduleQuotient` to be passed to
APIs whose quotient-module structure is synthesized automatically. -/
theorem moduleQuotient_eq_canonical (I : Ideal R) :
    moduleQuotient (M := M) I =
      @Module.instQuotientIdealSubmoduleHSMulTop R M _ _ _ I _ := by
  apply Module.ext
  funext r x
  induction r, x using Quotient.inductionOn₂' with
  | _ r x => rfl

@[simp]
lemma mk_smul_mk_moduleQuotient (I : Ideal R) (r : R) (x : M) :
    letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      smulModuleQuotient I
    Ideal.Quotient.mk I r •
        Submodule.Quotient.mk
          (p := I • (⊤ : Submodule R M)) x =
      Submodule.Quotient.mk (r • x) :=
  rfl

/-- The native `R`-action and the quotient-ring action on `M / IM` form the expected
scalar tower. -/
theorem isScalarTower_moduleQuotient (I : Ideal R) :
    letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      smulModuleQuotient I
    letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      moduleQuotient I
    IsScalarTower R (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    smulModuleQuotient I
  letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    moduleQuotient I
  constructor
  intro r s x
  induction s, x using Quotient.inductionOn₂' with
  | _ s x =>
      simp only [Submodule.Quotient.mk''_eq_mk]
      rw [← Submodule.Quotient.mk_smul,
        Ideal.Quotient.mk_eq_mk, mk_smul_mk_moduleQuotient,
        smul_assoc]
      rfl

/-- The canonical identification `(R / I) ⊗[R] M ≃ M / IM`, as an
`R / I`-linear equivalence. -/
noncomputable def quotTensorEquivQuotSMul (I : Ideal R) :
    letI : Module (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
      TensorProduct.leftModule
    letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      smulModuleQuotient I
    letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      moduleQuotient I
    letI : IsScalarTower R (R ⧸ I)
        (M ⧸ I • (⊤ : Submodule R M)) :=
      isScalarTower_moduleQuotient I
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I]
      (M ⧸ I • (⊤ : Submodule R M)) := by
  letI : Module (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    TensorProduct.leftModule
  letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    smulModuleQuotient I
  letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    moduleQuotient I
  letI : IsScalarTower R (R ⧸ I)
      (M ⧸ I • (⊤ : Submodule R M)) :=
    isScalarTower_moduleQuotient I
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  exact (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    hsurj

/-- Quotienting a finite module by the action of an ideal gives a finite module
over the quotient ring. -/
theorem finite_moduleQuotient (I : Ideal R) [Module.Finite R M] :
    letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      smulModuleQuotient I
    letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      moduleQuotient I
    Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    smulModuleQuotient I
  letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    moduleQuotient I
  letI : Module (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    TensorProduct.leftModule
  letI : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Finite.base_change R (R ⧸ I) M
  exact Module.Finite.equiv (quotTensorEquivQuotSMul I)

/-- Quotienting a projective module by the action of an ideal gives a projective
module over the quotient ring. -/
theorem projective_moduleQuotient (I : Ideal R)
    [Module.Projective R M] :
    letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      smulModuleQuotient I
    letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
      moduleQuotient I
    Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  letI : SMul (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    smulModuleQuotient I
  letI : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
    moduleQuotient I
  letI : Module (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    TensorProduct.leftModule
  have hP : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Projective.tensorProduct
  exact Module.Projective.of_equiv (quotTensorEquivQuotSMul I)

end Ideal.Quotient

end
