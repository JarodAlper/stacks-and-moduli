module

public import StacksAndModuli.API.NoetherianLocalFlatCokernelComplexCriterion
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Flat cokernels from exactness on a pushout fibre

Suppose that the square of rings with vertices `R`, `k`, `S`, and `B` is a pushout, so
that `B` is a model of `k ⊗[R] S`.  Cancelling the scalar extension from `S` to `B`
identifies the base change of an `S`-module to `B` with its scalar extension from `R` to
`k`.  This identification is natural in module maps, and hence transports exactness of a
two-differential complex between the two models of the fibre.

When `R → S` is a local homomorphism of noetherian local rings and `k` is the residue
field of `R`, exactness over any pushout model `B` therefore implies ordinary exactness and
`R`-flatness of the cokernel, provided the last term is `R`-flat and the two relevant
`S`-modules are finite.

Main declarations:

* `LinearMap.baseChange_exact_iff_lTensor_exact_of_isPushout`;
* `Module.Flat.exact_and_flat_coker_of_isPushout_baseChange_exact`;
* `Module.Flat.coker_of_isPushout_baseChange_exact`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w x

open TensorProduct

namespace LinearMap

/-- Exactness after base change around a pushout square agrees with exactness after
tensoring over the base ring with the other side of the square. -/
theorem baseChange_exact_iff_lTensor_exact_of_isPushout
    {R k : Type u} {S : Type v} {B : Type w} {L K F : Type x}
    [CommRing R] [CommRing k] [CommRing S] [CommRing B]
    [Algebra R k] [Algebra R S] [Algebra R B]
    [Algebra S B] [Algebra k B]
    [IsScalarTower R S B] [IsScalarTower R k B]
    [Algebra.IsPushout R k S B]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F) :
    Function.Exact (f.baseChange B) (g.baseChange B) ↔
      Function.Exact ((f.restrictScalars R).lTensor k)
        ((g.restrictScalars R).lTensor k) := by
  have cancel_apply
      {M : Type x} [AddCommGroup M] [Module R M] [Module S M]
      [IsScalarTower R S M] (a : k) (m : M) :
      Algebra.IsPushout.cancelBaseChange R k S B M
          (algebraMap k B a ⊗ₜ[S] m) = a ⊗ₜ[R] m := by
    rw [show algebraMap k B a ⊗ₜ[S] m =
      a • (1 ⊗ₜ[S] m) by
        rw [TensorProduct.smul_tmul']
        simp [Algebra.smul_def]]
    rw [map_smul, Algebra.IsPushout.cancelBaseChange_tmul,
      TensorProduct.smul_tmul']
    simp
  have naturality
      {M N : Type x} [AddCommGroup M] [Module R M] [Module S M]
      [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N]
      [IsScalarTower R S N] (h : M →ₗ[S] N) :
      (((h.restrictScalars R).lTensor k) :
          (k ⊗[R] M) →ₗ[R] (k ⊗[R] N)).comp
        ((Algebra.IsPushout.cancelBaseChange R k S B M).toLinearMap.restrictScalars R) =
        ((Algebra.IsPushout.cancelBaseChange R k S B N).toLinearMap.restrictScalars R).comp
          ((h.baseChange B).restrictScalars R) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ :=
      (Algebra.IsPushout.cancelBaseChange R k S B M).symm.surjective x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
        change ((h.restrictScalars R).lTensor k)
            (Algebra.IsPushout.cancelBaseChange R k S B M
              (algebraMap k B a ⊗ₜ[S] m)) =
          Algebra.IsPushout.cancelBaseChange R k S B N
            ((h.baseChange B) (algebraMap k B a ⊗ₜ[S] m))
        rw [cancel_apply, LinearMap.lTensor_tmul,
          LinearMap.baseChange_tmul, cancel_apply]
        rfl
    | add x y hx hy =>
        simp only [map_add, hx, hy]
  let fB := (f.baseChange B).restrictScalars R
  let gB := (g.baseChange B).restrictScalars R
  have hiff : Function.Exact
      ((f.restrictScalars R).lTensor k)
      ((g.restrictScalars R).lTensor k) ↔ Function.Exact fB gB :=
    Function.Exact.iff_of_ladder_linearEquiv
      (f₁₂ := fB) (f₂₃ := gB)
      (g₁₂ := (f.restrictScalars R).lTensor k)
      (g₂₃ := (g.restrictScalars R).lTensor k)
      (e₁ := (Algebra.IsPushout.cancelBaseChange R k S B L).restrictScalars R)
      (e₂ := (Algebra.IsPushout.cancelBaseChange R k S B K).restrictScalars R)
      (e₃ := (Algebra.IsPushout.cancelBaseChange R k S B F).restrictScalars R)
      (naturality f) (naturality g)
  exact hiff.symm

end LinearMap

namespace Module.Flat

/-- Over a noetherian local algebra, exactness of two consecutive maps on a pushout model
of the closed coefficient fibre makes the original pair exact and the cokernel of the
second map coefficient-flat. -/
theorem exact_and_flat_coker_of_isPushout_baseChange_exact
    {R : Type u} {S : Type v} {B : Type w} {L K F : Type x}
    [CommRing R] [CommRing S] [CommRing B]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [Algebra R B] [Algebra S B]
    [Algebra (IsLocalRing.ResidueField R) B]
    [IsScalarTower R S B]
    [IsScalarTower R (IsLocalRing.ResidueField R) B]
    [Algebra.IsPushout R (IsLocalRing.ResidueField R) S B]
    [IsLocalHom (algebraMap R S)]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S K] [Module.Finite S F] [Module.Flat R F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : Function.Exact (f.baseChange B) (g.baseChange B)) :
    Function.Exact f g ∧ Module.Flat R (F ⧸ LinearMap.range g) := by
  apply exact_and_flat_coker_of_lTensor_residueField_exact f g hcomp
  exact (LinearMap.baseChange_exact_iff_lTensor_exact_of_isPushout f g).mp hfibre

/-- Over a noetherian local algebra, exactness of two consecutive maps on a pushout model
of the closed coefficient fibre makes the cokernel of the second map coefficient-flat. -/
theorem coker_of_isPushout_baseChange_exact
    {R S B L K F : Type u} [CommRing R] [CommRing S] [CommRing B]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [Algebra R B] [Algebra S B]
    [Algebra (IsLocalRing.ResidueField R) B]
    [IsScalarTower R S B]
    [IsScalarTower R (IsLocalRing.ResidueField R) B]
    [Algebra.IsPushout R (IsLocalRing.ResidueField R) S B]
    [IsLocalHom (algebraMap R S)]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S K] [Module.Finite S F] [Module.Flat R F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : Function.Exact (f.baseChange B) (g.baseChange B)) :
    Module.Flat R (F ⧸ LinearMap.range g) :=
  (exact_and_flat_coker_of_isPushout_baseChange_exact
    f g hcomp hfibre).2

end Module.Flat

end

end
