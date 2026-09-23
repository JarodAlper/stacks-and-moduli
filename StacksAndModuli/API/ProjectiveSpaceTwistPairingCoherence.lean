module

public import StacksAndModuli.API.ProjectiveTwistPairingCoherence
public import StacksAndModuli.API.ProjectiveSpaceTwistCancellation
public import StacksAndModuli.API.SchemeModulesPullbackTensorCoherence

/-!
# Pairing coherence for opposite twists on relative projective space

The multiplication pairing between `O(-d)` and `O(d)` is transported from polynomial
projective space to relative projective space.  The pullback tensor comparison preserves
its left triangle identity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The multiplication pairing between `O(-d)` and `O(d)` on relative projective space. -/
noncomputable def projectiveSpaceOverTwist_pairingIso_nat (n : ℕ) (T : Scheme.{u}) (d : ℕ) :
    Modules.tensor
      (projectiveSpaceOverTwist n T (-(d : ℤ)))
      (projectiveSpaceOverTwist n T (d : ℤ)) ≅
      SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf :=
  projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d ≪≫
    eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega)) ≪≫
    projectiveSpaceOverTwistZeroIso n T

/-- The canonical pairing of opposite relative projective twists satisfies the left
triangle identity. -/
lemma projectiveSpaceOverTwist_pairing_left_triangle_nat
    (n : ℕ) (T : Scheme.{u}) (d : ℕ) :
    let N := projectiveSpaceOverTwist n T (-(d : ℤ))
    let D := projectiveSpaceOverTwist n T (d : ℤ)
    let e := projectiveSpaceOverTwist_pairingIso_nat n T d
    (Modules.tensorLeftUnitIso N).inv ≫
        Modules.tensorMapLeft e.inv N ≫
        (Modules.tensorAssocIso N D N).hom ≫
        Modules.tensorMapRight N ((Modules.tensorCommIso D N).hom ≫ e.hom) ≫
        (Modules.tensorUnitIso N).hom = 𝟙 N := by
  dsimp only
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let N0 := ProjectiveSpectrum.Twist.twist 𝒜 (-(d : ℤ))
  let D0 := ProjectiveSpectrum.Twist.twist 𝒜 (d : ℤ)
  let e0 : Modules.tensor N0 D0 ≅
      SheafOfModules.unit (projectiveSpace n).ringCatSheaf :=
    ProjectiveSpectrum.Twist.polynomialMultiplyIso
        (R := ULift.{u} ℤ) (Fin (n + 1)) (-(d : ℤ)) (d : ℤ) ≪≫
      eqToIso (congrArg (ProjectiveSpectrum.Twist.twist 𝒜) (by omega)) ≪≫
      ProjectiveSpectrum.Twist.zeroIso 𝒜
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let e := projectiveSpaceOverTwist_pairingIso_nat n T d
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit h
  letI : IsIso (Modules.pullbackTensorComparison h N0 D0) := by
    dsimp only [N0, D0]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ d
  letI : IsIso (Modules.pullbackTensorComparison h D0 N0) :=
    Modules.pullbackTensorComparison_isIso_swap h N0 D0
  have hb := ProjectiveSpectrum.Twist.polynomialTwist_pairing_left_triangle_nat
    n d
  change (Modules.tensorLeftUnitIso N0).inv ≫
        Modules.tensorMapLeft e0.inv N0 ≫
        (Modules.tensorAssocIso N0 D0 N0).hom ≫
        Modules.tensorMapRight N0 ((Modules.tensorCommIso D0 N0).hom ≫ e0.hom) ≫
        (Modules.tensorUnitIso N0).hom = 𝟙 N0 at hb
  have ht := Modules.pullback_pairing_left_triangle h N0 D0 e0.inv
    ((Modules.tensorCommIso D0 N0).hom ≫ e0.hom) hb
  dsimp only at ht
  let u := SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom
  let cND := Modules.pullbackTensorComparison h N0 D0
  let cDN := Modules.pullbackTensorComparison h D0 N0
  have hcoev : e.inv = inv u ≫ (Modules.pullback h).map e0.inv ≫ cND := by
    dsimp only [e, projectiveSpaceOverTwist_pairingIso_nat, projectiveSpaceOverTwist_addIso_nat,
      projectiveSpaceOverTwistZeroIso, e0, u, cND,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    simp only [asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
    rw [← eqToIso_map]
    rfl
  have hehom : e.hom = inv cND ≫ (Modules.pullback h).map e0.hom ≫ u := by
    dsimp only [e, projectiveSpaceOverTwist_pairingIso_nat, projectiveSpaceOverTwist_addIso_nat,
      projectiveSpaceOverTwistZeroIso, e0, u, cND,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
    rw [← eqToIso_map]
    rfl
  have hcomm0 := Modules.pullbackTensorComparison_comm h D0 N0
  change cDN ≫
      (Modules.tensorCommIso ((Modules.pullback h).obj D0)
        ((Modules.pullback h).obj N0)).hom =
    (Modules.pullback h).map (Modules.tensorCommIso D0 N0).hom ≫ cND at hcomm0
  have hcommInv :
      (Modules.tensorCommIso ((Modules.pullback h).obj D0)
          ((Modules.pullback h).obj N0)).hom ≫ inv cND =
        inv cDN ≫ (Modules.pullback h).map
          (Modules.tensorCommIso D0 N0).hom := by
    rw [← cancel_epi cDN]
    calc
      cDN ≫ (Modules.tensorCommIso ((Modules.pullback h).obj D0)
            ((Modules.pullback h).obj N0)).hom ≫ inv cND =
          ((Modules.pullback h).map (Modules.tensorCommIso D0 N0).hom ≫
            cND) ≫ inv cND :=
        congrArg (fun k ↦ k ≫ inv cND) hcomm0
      _ = (Modules.pullback h).map (Modules.tensorCommIso D0 N0).hom := by
        simp
      _ = cDN ≫ inv cDN ≫
          (Modules.pullback h).map (Modules.tensorCommIso D0 N0).hom := by
        simp
  have heval :
      (Modules.tensorCommIso D N).hom ≫ e.hom =
        inv cDN ≫ (Modules.pullback h).map
          ((Modules.tensorCommIso D0 N0).hom ≫ e0.hom) ≫ u := by
    rw [hehom]
    calc
      (Modules.tensorCommIso D N).hom ≫ inv cND ≫
            (Modules.pullback h).map e0.hom ≫ u =
          (inv cDN ≫ (Modules.pullback h).map
            (Modules.tensorCommIso D0 N0).hom) ≫
            (Modules.pullback h).map e0.hom ≫ u :=
        congrArg (fun k ↦ k ≫ (Modules.pullback h).map e0.hom ≫ u)
          hcommInv
      _ = inv cDN ≫ (Modules.pullback h).map
            ((Modules.tensorCommIso D0 N0).hom ≫ e0.hom) ≫ u := by
        rw [Functor.map_comp]
        simp only [Category.assoc]
  change (Modules.tensorLeftUnitIso ((Modules.pullback h).obj N0)).inv ≫
      Modules.tensorMapLeft e.inv ((Modules.pullback h).obj N0) ≫
      (Modules.tensorAssocIso ((Modules.pullback h).obj N0)
        ((Modules.pullback h).obj D0) ((Modules.pullback h).obj N0)).hom ≫
      Modules.tensorMapRight ((Modules.pullback h).obj N0)
        ((Modules.tensorCommIso ((Modules.pullback h).obj D0)
          ((Modules.pullback h).obj N0)).hom ≫ e.hom) ≫
      (Modules.tensorUnitIso ((Modules.pullback h).obj N0)).hom =
        𝟙 ((Modules.pullback h).obj N0)
  change (Modules.tensorCommIso ((Modules.pullback h).obj D0)
      ((Modules.pullback h).obj N0)).hom ≫ e.hom =
    inv cDN ≫ (Modules.pullback h).map
      ((Modules.tensorCommIso D0 N0).hom ≫ e0.hom) ≫ u at heval
  simpa only [hcoev, heval, u, cND, cDN] using ht

end AlgebraicGeometry.Scheme

end

end

