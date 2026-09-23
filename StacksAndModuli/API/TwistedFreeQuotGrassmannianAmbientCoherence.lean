module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection
public import StacksAndModuli.API.ProjectiveTwistMultiplicationCoherence
public import StacksAndModuli.API.SchemeModulesPullbackTensorCoherence
public import StacksAndModuli.API.ProjectiveSpaceTwistPairingCoherence
public import StacksAndModuli.API.SchemeModulesPairingCoherence

/-!
# Ambient coherence for twisted-free Quot reconstruction

This file isolates the one-monomial comparison between direct multiplication and
tensoring a homogeneous section followed by cancellation of opposite twists.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Applying the morphism induced by an equality to a section is transport along
that equality. -/
lemma Modules.hom_app_eqToHom
    {X : Scheme.{u}} (G : ℤ → X.Modules) {a b : ℤ} (h : a = b)
    (s : Γ(G a, ⊤)) :
    Modules.Hom.app (eqToHom (congrArg G h)) ⊤ s =
      (show Γ(G b, ⊤) from h ▸ s) := by
  subst h
  rfl

/-- The morphism represented by the transported monomial section before undoing the
positive twist. -/
noncomputable def twistMonomialSectionHom
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (i : Fin ((n + e).choose n)) :
    SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf ⟶
      projectiveSpaceOverTwist n T (e : ℤ) :=
  (projectiveSpaceOverTwist n T (e : ℤ)).unitHomEquiv.symm
    ((Modules.sectionsTopEquiv
      (projectiveSpaceOverTwist n T (e : ℤ))).symm
        (twistMonomialSection n T e i))

/-- The relative monomial-section morphism is the normalized pullback of the
homogeneous-section morphism on polynomial projective space. -/
lemma twistMonomialSectionHom_eq_pullback_homogeneousSectionHom
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (i : Fin ((n + e).choose n)) :
    let 𝒜 := MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ)
    let h := Limits.pullback.snd
      (specULiftZIsTerminal.from T)
      (specULiftZIsTerminal.from (projectiveSpace n))
    let p := MvPolynomial.homogeneousSubmoduleFinBasis
      n (ULift.{u} ℤ) e i
    twistMonomialSectionHom n T e i =
      Modules.Hom.pullbackUnitMap h
        (ProjectiveSpectrum.Twist.homogeneousSectionHom 𝒜 p) := by
  dsimp only
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule
    n (ULift.{u} ℤ) e
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let p := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) e i
  let M := projectiveSpaceOverTwist n T (e : ℤ)
  apply (SheafOfModules.unitHomEquiv M).injective
  apply_fun (Modules.sectionsTopEquiv M)
  dsimp only [M, twistMonomialSectionHom]
  rw [show (SheafOfModules.unitHomEquiv
      (projectiveSpaceOverTwist n T (e : ℤ)))
        ((SheafOfModules.unitHomEquiv
          (projectiveSpaceOverTwist n T (e : ℤ))).symm
            ((Modules.sectionsTopEquiv
              (projectiveSpaceOverTwist n T (e : ℤ))).symm
                (twistMonomialSection n T e i))) =
      (Modules.sectionsTopEquiv
        (projectiveSpaceOverTwist n T (e : ℤ))).symm
          (twistMonomialSection n T e i) from
    (SheafOfModules.unitHomEquiv
      (projectiveSpaceOverTwist n T (e : ℤ))).apply_symm_apply _]
  rw [show (Modules.sectionsTopEquiv
      (projectiveSpaceOverTwist n T (e : ℤ)))
        ((Modules.sectionsTopEquiv
          (projectiveSpaceOverTwist n T (e : ℤ))).symm
            (twistMonomialSection n T e i)) =
      twistMonomialSection n T e i from
    (Modules.sectionsTopEquiv
      (projectiveSpaceOverTwist n T (e : ℤ))).apply_symm_apply _]
  change twistMonomialSection n T e i =
    Modules.Hom.app
      (Modules.Hom.pullbackUnitMap h
        (ProjectiveSpectrum.Twist.homogeneousSectionHom 𝒜 p)) ⊤
          (1 : Γ(projectiveSpaceOver n T, ⊤))
  rw [pullbackUnitMap_app_top_one]
  change _root_.Scheme.Modules.pullbackGlobalSections h
      (ProjectiveSpectrum.Twist.twist 𝒜 (e : ℤ))
        (MvPolynomial.projectiveTwistGlobalSectionsBasis
          n (ULift.{u} ℤ) e i) =
    _root_.Scheme.Modules.pullbackGlobalSections h
      (ProjectiveSpectrum.Twist.twist 𝒜 (e : ℤ))
        (Modules.Hom.app
          (ProjectiveSpectrum.Twist.homogeneousSectionHom 𝒜 p) ⊤
            (1 : Γ(Proj 𝒜, ⊤)))
  congr 1
  calc
    MvPolynomial.projectiveTwistGlobalSectionsBasis
          n (ULift.{u} ℤ) e i =
        MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv
          n (ULift.{u} ℤ) e p := Module.Basis.map_apply _ _ _
    _ = ProjectiveSpectrum.Twist.homogeneousSection 𝒜 p ⊤ := rfl
    _ = Modules.Hom.app
      (ProjectiveSpectrum.Twist.homogeneousSectionHom 𝒜 p) ⊤
            (1 : Γ(Proj 𝒜, ⊤)) :=
      (ProjectiveSpectrum.Twist.homogeneousSectionHom_app_one 𝒜 p ⊤).symm

/-- The relative monomial-section morphism is multiplication from the zero twist,
after the canonical identification of the zero twist with the structure sheaf. -/
lemma twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (i : Fin ((n + e).choose n)) :
    twistMonomialSectionHom n T e i =
      (projectiveSpaceOverTwistZeroIso n T).inv ≫
        twistMonomialMulHom n T 0 (e : ℤ) e (by omega) i := by
  rw [twistMonomialSectionHom_eq_pullback_homogeneousSectionHom]
  rw [ProjectiveSpectrum.Twist.homogeneousSectionHom_eq_zeroIso_inv_comp_mulHom]
  dsimp only [Modules.Hom.pullbackUnitMap,
    projectiveSpaceOverTwistZeroIso, twistMonomialMulHom, Iso.trans_inv,
    Functor.mapIso_inv]
  rw [Functor.map_comp]
  rfl

/-- Relative multiplication of twists commutes with multiplication by one monomial
in the right factor. -/
lemma tensorMapRight_twistMonomialMulHom_comp_addIso_nat
    (n : ℕ) (T : Scheme.{u}) (a : ℤ) (b c e : ℕ)
    (hbc : (c : ℤ) = (b : ℤ) + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    Modules.tensorMapRight (projectiveSpaceOverTwist n T a)
          (twistMonomialMulHom n T (b : ℤ) (c : ℤ) e hbc i) ≫
        (projectiveSpaceOverTwist_addIso_nat n T a c).hom =
      (projectiveSpaceOverTwist_addIso_nat n T a b).hom ≫
        twistMonomialMulHom n T (a + (b : ℤ)) (a + (c : ℤ)) e
          (by omega) i := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let p := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) e i
  let Oa := ProjectiveSpectrum.Twist.twist 𝒜 a
  let Ob := ProjectiveSpectrum.Twist.twist 𝒜 (b : ℤ)
  let Oc := ProjectiveSpectrum.Twist.twist 𝒜 (c : ℤ)
  let m : Ob ⟶ Oc := ProjectiveSpectrum.Twist.mulHom
    𝒜 p (b : ℤ) (c : ℤ) hbc
  let tb := Modules.pullbackTensorComparison h Oa Ob
  let tc := Modules.pullbackTensorComparison h Oa Oc
  haveI : IsIso tb := by
    dsimp only [tb, Oa, Ob]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ b
  haveI : IsIso tc := by
    dsimp only [tc, Oa, Oc]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ c
  have hnat := Modules.pullbackTensorComparison_naturality_right h Oa m
  have hinv :
      Modules.tensorMapRight ((Modules.pullback h).obj Oa)
            ((Modules.pullback h).map m) ≫ inv tc =
        inv tb ≫
          (Modules.pullback h).map (Modules.tensorMapRight Oa m) := by
    rw [← cancel_epi tb]
    calc
      tb ≫ Modules.tensorMapRight ((Modules.pullback h).obj Oa)
              ((Modules.pullback h).map m) ≫ inv tc =
          ((Modules.pullback h).map (Modules.tensorMapRight Oa m) ≫ tc) ≫
            inv tc := congrArg (fun k ↦ k ≫ inv tc) hnat.symm
      _ = (Modules.pullback h).map (Modules.tensorMapRight Oa m) := by
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = (tb ≫ inv tb) ≫
          (Modules.pullback h).map (Modules.tensorMapRight Oa m) := by
        simp only [IsIso.hom_inv_id, Category.id_comp]
      _ = tb ≫ inv tb ≫
          (Modules.pullback h).map (Modules.tensorMapRight Oa m) := rfl
  have hsq := ProjectiveSpectrum.Twist.multiplyHom_mulHom 𝒜 p
    a (b : ℤ) (c : ℤ) hbc (by omega)
  dsimp only [projectiveSpaceOverTwist_addIso_nat,
    twistMonomialMulHom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [asIso_hom, asIso_inv, Category.assoc]
  change Modules.tensorMapRight ((Modules.pullback h).obj Oa)
        ((Modules.pullback h).map m) ≫ inv tc ≫
          (Modules.pullback h).map
            (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (c : ℤ)) =
      inv tb ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (b : ℤ)) ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.mulHom 𝒜 p
            (a + (b : ℤ)) (a + (c : ℤ)) (by omega))
  calc
    Modules.tensorMapRight ((Modules.pullback h).obj Oa)
          ((Modules.pullback h).map m) ≫ inv tc ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (c : ℤ)) =
      (inv tb ≫
          (Modules.pullback h).map (Modules.tensorMapRight Oa m)) ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (c : ℤ)) :=
      congrArg (fun k ↦ k ≫ (Modules.pullback h).map
        (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (c : ℤ))) hinv
    _ = inv tb ≫ (Modules.pullback h).map
          (Modules.tensorMapRight Oa m ≫
            ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (c : ℤ)) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = inv tb ≫ (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (b : ℤ) ≫
            ProjectiveSpectrum.Twist.mulHom 𝒜 p
              (a + (b : ℤ)) (a + (c : ℤ)) (by omega)) :=
      congrArg (fun k ↦ inv tb ≫ (Modules.pullback h).map k) hsq
    _ = _ := by
      rw [Functor.map_comp]

/-- Relative multiplication of twists commutes with multiplication by one monomial
in the left factor. -/
lemma tensorMapLeft_twistMonomialMulHom_comp_addIso_nat
    (n : ℕ) (T : Scheme.{u}) (a ac : ℤ) (b e : ℕ)
    (hac : ac = a + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    Modules.tensorMapLeft
          (twistMonomialMulHom n T a ac e hac i)
          (projectiveSpaceOverTwist n T (b : ℤ)) ≫
        (projectiveSpaceOverTwist_addIso_nat n T ac b).hom =
      (projectiveSpaceOverTwist_addIso_nat n T a b).hom ≫
        twistMonomialMulHom n T (a + (b : ℤ))
          (ac + (b : ℤ)) e (by omega) i := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let p := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) e i
  let Oa := ProjectiveSpectrum.Twist.twist 𝒜 a
  let Oac := ProjectiveSpectrum.Twist.twist 𝒜 ac
  let Ob := ProjectiveSpectrum.Twist.twist 𝒜 (b : ℤ)
  let m : Oa ⟶ Oac := ProjectiveSpectrum.Twist.mulHom
    𝒜 p a ac hac
  let ta := Modules.pullbackTensorComparison h Oa Ob
  let tac := Modules.pullbackTensorComparison h Oac Ob
  haveI : IsIso ta := by
    dsimp only [ta, Oa, Ob]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ b
  haveI : IsIso tac := by
    dsimp only [tac, Oac, Ob]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ b
  have hnat := Modules.pullbackTensorComparison_naturality_left h m Ob
  have hinv :
      Modules.tensorMapLeft ((Modules.pullback h).map m)
            ((Modules.pullback h).obj Ob) ≫ inv tac =
        inv ta ≫
          (Modules.pullback h).map (Modules.tensorMapLeft m Ob) := by
    rw [← cancel_epi ta]
    calc
      ta ≫ Modules.tensorMapLeft ((Modules.pullback h).map m)
              ((Modules.pullback h).obj Ob) ≫ inv tac =
          ((Modules.pullback h).map (Modules.tensorMapLeft m Ob) ≫ tac) ≫
            inv tac := congrArg (fun k ↦ k ≫ inv tac) hnat.symm
      _ = (Modules.pullback h).map (Modules.tensorMapLeft m Ob) := by
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = (ta ≫ inv ta) ≫
          (Modules.pullback h).map (Modules.tensorMapLeft m Ob) := by
        simp only [IsIso.hom_inv_id, Category.id_comp]
      _ = ta ≫ inv ta ≫
          (Modules.pullback h).map (Modules.tensorMapLeft m Ob) := rfl
  have hsq := ProjectiveSpectrum.Twist.mulHom_multiplyHom 𝒜 p
    a ac (b : ℤ) hac (by omega)
  dsimp only [projectiveSpaceOverTwist_addIso_nat,
    twistMonomialMulHom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [asIso_hom, asIso_inv, Category.assoc]
  change Modules.tensorMapLeft ((Modules.pullback h).map m)
        ((Modules.pullback h).obj Ob) ≫ inv tac ≫
          (Modules.pullback h).map
            (ProjectiveSpectrum.Twist.multiplyHom 𝒜 ac (b : ℤ)) =
      inv ta ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (b : ℤ)) ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.mulHom 𝒜 p
            (a + (b : ℤ)) (ac + (b : ℤ)) (by omega))
  calc
    Modules.tensorMapLeft ((Modules.pullback h).map m)
          ((Modules.pullback h).obj Ob) ≫ inv tac ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 ac (b : ℤ)) =
      (inv ta ≫
          (Modules.pullback h).map (Modules.tensorMapLeft m Ob)) ≫
        (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 ac (b : ℤ)) :=
      congrArg (fun k ↦ k ≫ (Modules.pullback h).map
        (ProjectiveSpectrum.Twist.multiplyHom 𝒜 ac (b : ℤ))) hinv
    _ = inv ta ≫ (Modules.pullback h).map
          (Modules.tensorMapLeft m Ob ≫
            ProjectiveSpectrum.Twist.multiplyHom 𝒜 ac (b : ℤ)) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = inv ta ≫ (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.multiplyHom 𝒜 a (b : ℤ) ≫
            ProjectiveSpectrum.Twist.mulHom 𝒜 p
              (a + (b : ℤ)) (ac + (b : ℤ)) (by omega)) :=
      congrArg (fun k ↦ inv ta ≫ (Modules.pullback h).map k) hsq
    _ = _ := by
      rw [Functor.map_comp]

/-- Changing the recorded output degree of relative monomial multiplication is
postcomposition by the corresponding equality morphism. -/
lemma twistMonomialMulHom_comp_eqToHom
    (n : ℕ) (T : Scheme.{u}) (d dc dc' : ℤ) (e : ℕ)
    (hdc : dc = d + (e : ℤ)) (hdc' : dc' = d + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    twistMonomialMulHom n T d dc e hdc i ≫
        eqToHom (congrArg (fun z : ℤ ↦
          projectiveSpaceOverTwist n T z) (hdc.trans hdc'.symm)) =
      twistMonomialMulHom n T d dc' e hdc' i := by
  subst dc
  subst dc'
  rfl

/-- Changing the recorded input degree of relative monomial multiplication is
precomposition by the corresponding equality morphism. -/
lemma eqToHom_comp_twistMonomialMulHom
    (n : ℕ) (T : Scheme.{u}) (d d' dc : ℤ) (e : ℕ)
    (hdd : d = d') (hdc : dc = d + (e : ℤ))
    (hdc' : dc = d' + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    eqToHom (congrArg (fun z : ℤ ↦
          projectiveSpaceOverTwist n T z) hdd) ≫
        twistMonomialMulHom n T d' dc e hdc' i =
      twistMonomialMulHom n T d dc e hdc i := by
  subst d'
  simp only [eqToHom_refl, Category.id_comp]

/-- The twisted monomial section is obtained by transporting the basic monomial
section and then undoing multiplication of the two twists. -/
lemma twistMonomialTwistedSectionHom_eq
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    twistMonomialTwistedSectionHom n T l d e he i =
      twistMonomialSectionHom n T e i ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c) he.symm) ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (neg_add_eq_sub l (d : ℤ)).symm) ≫
        (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv := by
  symm
  rw [twistMonomialTwistedSectionHom]
  dsimp only [twistMonomialSectionHom]
  rw [Modules.unitHomOfSection_comp]
  change
    (SheafOfModules.unitHomEquiv
      (Modules.tensor (projectiveSpaceOverTwist n T (-l))
        (projectiveSpaceOverTwist n T (d : ℤ)))).symm _ =
      (SheafOfModules.unitHomEquiv
        (Modules.tensor (projectiveSpaceOverTwist n T (-l))
          (projectiveSpaceOverTwist n T (d : ℤ)))).symm _
  apply (SheafOfModules.unitHomEquiv
    (Modules.tensor (projectiveSpaceOverTwist n T (-l))
      (projectiveSpaceOverTwist n T (d : ℤ)))).injective
  simp only [Equiv.apply_symm_apply]
  change
    (Modules.sectionsTopEquiv
      (Modules.tensor (projectiveSpaceOverTwist n T (-l))
        (projectiveSpaceOverTwist n T (d : ℤ)))).symm _ =
      (Modules.sectionsTopEquiv
        (Modules.tensor (projectiveSpaceOverTwist n T (-l))
          (projectiveSpaceOverTwist n T (d : ℤ)))).symm _
  apply_fun (Modules.sectionsTopEquiv
    (Modules.tensor (projectiveSpaceOverTwist n T (-l))
      (projectiveSpaceOverTwist n T (d : ℤ))))
  simp only [Equiv.apply_symm_apply]
  rw [Modules.Hom.comp_app, Modules.Hom.comp_app]
  simp only [CategoryTheory.comp_apply]
  exact congrArg
    (fun z : Γ(projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) ↦
      Modules.Hom.app
        (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
          (Modules.Hom.app
            (eqToHom (congrArg
              (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
                (neg_add_eq_sub l (d : ℤ)).symm)) ⊤ z))
    (Modules.hom_app_eqToHom
      (fun c : ℤ ↦ projectiveSpaceOverTwist n T c) he.symm
        (twistMonomialSection n T e i))

/-- The twisted monomial section is obtained from the canonical coevaluation of
`O(-d)` by applying monomial multiplication in its left factor. -/
lemma twistMonomialTwistedSectionHom_eq_coevaluation_comp_tensorMapLeft
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    twistMonomialTwistedSectionHom n T l d e he i =
      (projectiveSpaceOverTwistZeroIso n T).inv ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (show (0 : ℤ) = -(d : ℤ) + (d : ℤ) by omega)) ≫
        (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d).inv ≫
        Modules.tensorMapLeft
          (twistMonomialMulHom n T (-(d : ℤ)) (-l) e
            (by omega) i)
          (projectiveSpaceOverTwist n T (d : ℤ)) := by
  rw [twistMonomialTwistedSectionHom_eq,
    twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom]
  let A := projectiveSpaceOverTwist n T (-(d : ℤ))
  let L := projectiveSpaceOverTwist n T (-l)
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let z := projectiveSpaceOverTwistZeroIso n T
  let ad := projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d
  let ld := projectiveSpaceOverTwist_addIso_nat n T (-l) d
  let f : A ⟶ L := twistMonomialMulHom n T (-(d : ℤ)) (-l) e
    (by omega) i
  let g := twistMonomialMulHom n T (-(d : ℤ) + (d : ℤ))
    (-l + (d : ℤ)) e (by omega) i
  let c : projectiveSpaceOverTwist n T 0 ⟶
      projectiveSpaceOverTwist n T (-(d : ℤ) + (d : ℤ)) :=
    eqToHom (congrArg
      (fun x : ℤ ↦ projectiveSpaceOverTwist n T x) (by omega))
  let m0 := twistMonomialMulHom n T 0 (e : ℤ) e (by omega) i
  let ce : projectiveSpaceOverTwist n T (e : ℤ) ⟶
      projectiveSpaceOverTwist n T ((d : ℤ) - l) :=
    eqToHom (congrArg
      (fun x : ℤ ↦ projectiveSpaceOverTwist n T x) he.symm)
  let cl : projectiveSpaceOverTwist n T ((d : ℤ) - l) ⟶
      projectiveSpaceOverTwist n T (-l + (d : ℤ)) :=
    eqToHom (congrArg
      (fun x : ℤ ↦ projectiveSpaceOverTwist n T x)
        (neg_add_eq_sub l (d : ℤ)).symm)
  have hleft := tensorMapLeft_twistMonomialMulHom_comp_addIso_nat
    n T (-(d : ℤ)) (-l) d e (by omega) i
  change Modules.tensorMapLeft f D ≫ ld.hom = ad.hom ≫ g at hleft
  have hin := eqToHom_comp_twistMonomialMulHom n T
    0 (-(d : ℤ) + (d : ℤ)) (-l + (d : ℤ)) e
      (by omega) (by omega) (by omega) i
  change c ≫ g =
    twistMonomialMulHom n T 0 (-l + (d : ℤ)) e (by omega) i at hin
  have hout := twistMonomialMulHom_comp_eqToHom n T
    0 (e : ℤ) (-l + (d : ℤ)) e (by omega) (by omega) i
  have hout' : m0 ≫ ce ≫ cl =
      twistMonomialMulHom n T 0 (-l + (d : ℤ)) e (by omega) i := by
    simpa only [m0, ce, cl, Category.assoc, eqToHom_trans] using hout
  rw [← cancel_mono ld.hom]
  change z.inv ≫ m0 ≫ ce ≫ cl ≫ ld.inv ≫ ld.hom =
    z.inv ≫ c ≫ ad.inv ≫ Modules.tensorMapLeft f D ≫ ld.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hleft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hin, ← hout']

/-- The zero-twist multiplication isomorphism agrees with the chosen right unitor
after identifying `O(0)` with the structure sheaf. -/
def ProjectiveSpaceOverTwistZeroRightUnitCoherence
    (n : ℕ) (T : Scheme.{u}) (a : ℤ) : Prop :=
  (Modules.tensorUnitIso (projectiveSpaceOverTwist n T a)).inv ≫
      Modules.tensorMapRight (projectiveSpaceOverTwist n T a)
        (projectiveSpaceOverTwistZeroIso n T).inv =
    eqToHom (congrArg (fun z : ℤ ↦ projectiveSpaceOverTwist n T z)
        (add_zero a).symm) ≫
      (projectiveSpaceOverTwist_addIso_nat n T a 0).inv

/-- The relative zero-twist multiplication satisfies the chosen right-unitor
coherence. -/
lemma projectiveSpaceOverTwistZeroRightUnitCoherence
    (n : ℕ) (T : Scheme.{u}) (a : ℤ) :
    ProjectiveSpaceOverTwistZeroRightUnitCoherence n T a := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let Oa := ProjectiveSpectrum.Twist.twist 𝒜 a
  let O0 := ProjectiveSpectrum.Twist.twist 𝒜 0
  let u := SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom
  let cu := Modules.pullbackTensorComparison h Oa
    (SheafOfModules.unit (projectiveSpace n).ringCatSheaf)
  let c0 := Modules.pullbackTensorComparison h Oa O0
  let μ := ProjectiveSpectrum.Twist.multiplyHom 𝒜 a 0
  letI : IsIso u := isIso_pullbackObjUnitToUnit h
  letI : IsIso μ := by
    dsimp only [μ, 𝒜]
    exact ProjectiveSpectrum.Twist.polynomial_multiplyHom_isIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) a 0
  letI : IsIso c0 := by
    dsimp only [c0, Oa, O0]
    exact MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h _ 0
  have hunit := Modules.tensorUnitIso_inv_comp_pullbackUnit_inv h Oa
  change (Modules.tensorUnitIso ((Modules.pullback h).obj Oa)).inv ≫
      Modules.tensorMapRight ((Modules.pullback h).obj Oa) (inv u) =
    (Modules.pullback h).map (Modules.tensorUnitIso Oa).inv ≫ cu at hunit
  have hnat := Modules.pullbackTensorComparison_naturality_right h Oa
    (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv
  change (Modules.pullback h).map
      (Modules.tensorMapRight Oa (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) ≫
        c0 =
    cu ≫ Modules.tensorMapRight ((Modules.pullback h).obj Oa)
      ((Modules.pullback h).map
        (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) at hnat
  have hpoly :=
    ProjectiveSpectrum.Twist.tensorUnitIso_inv_tensorMapRight_zeroIso_inv
      𝒜 a
  change (Modules.tensorUnitIso Oa).inv ≫
      Modules.tensorMapRight Oa (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv =
    eqToHom (congrArg (ProjectiveSpectrum.Twist.twist 𝒜)
      (add_zero a).symm) ≫ inv μ at hpoly
  dsimp only [ProjectiveSpaceOverTwistZeroRightUnitCoherence,
    projectiveSpaceOverTwistZeroIso, projectiveSpaceOverTwist_addIso_nat,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [asIso_hom, asIso_inv, Category.assoc]
  change (Modules.tensorUnitIso ((Modules.pullback h).obj Oa)).inv ≫
      Modules.tensorMapRight ((Modules.pullback h).obj Oa)
        (inv u ≫ (Modules.pullback h).map
          (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) =
    eqToHom (congrArg
        (fun z : ℤ ↦ (Modules.pullback h).obj
          (ProjectiveSpectrum.Twist.twist 𝒜 z)) (add_zero a).symm) ≫
      (Modules.pullback h).map (inv μ) ≫ c0
  rw [Modules.tensorMapRight_comp]
  calc
    (Modules.tensorUnitIso ((Modules.pullback h).obj Oa)).inv ≫
          Modules.tensorMapRight ((Modules.pullback h).obj Oa) (inv u) ≫
          Modules.tensorMapRight ((Modules.pullback h).obj Oa)
            ((Modules.pullback h).map
              (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) =
        ((Modules.pullback h).map (Modules.tensorUnitIso Oa).inv ≫ cu) ≫
          Modules.tensorMapRight ((Modules.pullback h).obj Oa)
            ((Modules.pullback h).map
              (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) :=
      congrArg (fun k ↦ k ≫
        Modules.tensorMapRight ((Modules.pullback h).obj Oa)
          ((Modules.pullback h).map
            (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv)) hunit
    _ = (Modules.pullback h).map (Modules.tensorUnitIso Oa).inv ≫
          ((Modules.pullback h).map
            (Modules.tensorMapRight Oa
              (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) ≫ c0) := by
      rw [hnat]
      simp only [Category.assoc]
    _ = (Modules.pullback h).map
          ((Modules.tensorUnitIso Oa).inv ≫
            Modules.tensorMapRight Oa
              (ProjectiveSpectrum.Twist.zeroIso 𝒜).inv) ≫ c0 := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (Modules.pullback h).map
          (eqToHom (congrArg (ProjectiveSpectrum.Twist.twist 𝒜)
            (add_zero a).symm) ≫ inv μ) ≫ c0 := by rw [hpoly]
    _ = eqToHom (congrArg
          (fun z : ℤ ↦ (Modules.pullback h).obj
            (ProjectiveSpectrum.Twist.twist 𝒜 z)) (add_zero a).symm) ≫
          (Modules.pullback h).map (inv μ) ≫ c0 := by
      rw [Functor.map_comp, eqToHom_map]
      simp only [Category.assoc]

/-- Associativity, symmetry, and cancellation coherence for tensoring an arbitrary
degree-`e` section into the two presentations of the same relative twist. -/
def ProjectiveSpaceOverTwistSectionCancellationCoherence
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) : Prop :=
  ∀ s : SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf ⟶
      projectiveSpaceOverTwist n T (e : ℤ),
    (Modules.tensorUnitIso
          (projectiveSpaceOverTwist n T (-(d : ℤ)))).inv ≫
        Modules.tensorMapRight
          (projectiveSpaceOverTwist n T (-(d : ℤ))) s ≫
        (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) e).hom ≫
        eqToHom (congrArg (fun z : ℤ ↦ projectiveSpaceOverTwist n T z)
          (by omega)) =
      (Modules.tensorLeftUnitIso
          (projectiveSpaceOverTwist n T (-(d : ℤ)))).inv ≫
        Modules.tensorMapLeft
          (s ≫
            eqToHom (congrArg
              (fun z : ℤ ↦ projectiveSpaceOverTwist n T z) he.symm) ≫
            eqToHom (congrArg
              (fun z : ℤ ↦ projectiveSpaceOverTwist n T z)
                (neg_add_eq_sub l (d : ℤ)).symm) ≫
            (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv)
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T
          (projectiveSpaceOverTwist n T (-l)) d).hom

/-- Multiplication by one monomial agrees unconditionally with tensoring its
twisted section and cancelling the auxiliary positive and negative twists. -/
lemma twistMonomialMulHom_eq_tensor_twistedSection_cancel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    twistMonomialMulHom n T (-(d : ℤ)) (-l) e (by omega) i =
      (Modules.tensorLeftUnitIso
        (projectiveSpaceOverTwist n T (-(d : ℤ)))).inv ≫
        Modules.tensorMapLeft
          (twistMonomialTwistedSectionHom n T l d e he i)
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T
          (projectiveSpaceOverTwist n T (-l)) d).hom := by
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let L := projectiveSpaceOverTwist n T (-l)
  let pair := projectiveSpaceOverTwist_pairingIso_nat n T d
  let f := twistMonomialMulHom n T (-(d : ℤ)) (-l) e (by omega) i
  have hsec :=
    twistMonomialTwistedSectionHom_eq_coevaluation_comp_tensorMapLeft
      n T l d e he i
  change twistMonomialTwistedSectionHom n T l d e he i =
    pair.inv ≫ Modules.tensorMapLeft f D at hsec
  have htri := projectiveSpaceOverTwist_pairing_left_triangle_nat n T d
  change (Modules.tensorLeftUnitIso N).inv ≫
      Modules.tensorMapLeft pair.inv N ≫
      (Modules.tensorAssocIso N D N).hom ≫
      Modules.tensorMapRight N
        ((Modules.tensorCommIso D N).hom ≫ pair.hom) ≫
      (Modules.tensorUnitIso N).hom = 𝟙 N at htri
  have hm := Modules.pairing_left_triangle_mate N D L pair.inv
    ((Modules.tensorCommIso D N).hom ≫ pair.hom) htri f
  rw [hsec]
  change f = (Modules.tensorLeftUnitIso N).inv ≫
      Modules.tensorMapLeft (pair.inv ≫ Modules.tensorMapLeft f D) N ≫
      (projectiveSpaceOverTwistModule_cancelIso_nat n T L d).hom
  symm
  exact hm

/-- Once the two canonical relative tensor coherences are supplied, multiplication
by one monomial agrees with tensoring its twisted section and cancelling the
auxiliary positive and negative twists. -/
lemma twistMonomialMulHom_eq_tensor_twistedSection_cancel_of_relative_coherence
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (hzero : ProjectiveSpaceOverTwistZeroRightUnitCoherence
      n T (-(d : ℤ)))
    (hsection : ProjectiveSpaceOverTwistSectionCancellationCoherence
      n T l d e he)
    (i : Fin ((n + e).choose n)) :
    twistMonomialMulHom n T (-(d : ℤ)) (-l) e (by omega) i =
      (Modules.tensorLeftUnitIso
        (projectiveSpaceOverTwist n T (-(d : ℤ)))).inv ≫
        Modules.tensorMapLeft
          (twistMonomialTwistedSectionHom n T l d e he i)
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T
          (projectiveSpaceOverTwist n T (-l)) d).hom := by
  rw [twistMonomialTwistedSectionHom_eq]
  let a : ℤ := -(d : ℤ)
  let A := projectiveSpaceOverTwist n T a
  let s := twistMonomialSectionHom n T e i
  let z := projectiveSpaceOverTwistZeroIso n T
  let m₀ := twistMonomialMulHom n T 0 (e : ℤ) e (by omega) i
  let ae := projectiveSpaceOverTwist_addIso_nat n T a e
  let a₀ := projectiveSpaceOverTwist_addIso_nat n T a 0
  let c₀ : A ⟶ projectiveSpaceOverTwist n T (a + (0 : ℤ)) :=
    eqToHom (congrArg (fun x : ℤ ↦ projectiveSpaceOverTwist n T x)
      (add_zero a).symm)
  let ct : projectiveSpaceOverTwist n T (a + (e : ℤ)) ⟶
      projectiveSpaceOverTwist n T (-l) :=
    eqToHom (congrArg (fun x : ℤ ↦ projectiveSpaceOverTwist n T x)
      (by dsimp only [a]; omega))
  change (Modules.tensorUnitIso A).inv ≫
      Modules.tensorMapRight A z.inv = c₀ ≫ a₀.inv at hzero
  have hm := tensorMapRight_twistMonomialMulHom_comp_addIso_nat
    n T a 0 e e (by omega) i
  change Modules.tensorMapRight A m₀ ≫ ae.hom =
    a₀.hom ≫ twistMonomialMulHom n T (a + (0 : ℤ))
      (a + (e : ℤ)) e (by omega) i at hm
  have hin := eqToHom_comp_twistMonomialMulHom n T
    a (a + (0 : ℤ)) (a + (e : ℤ)) e
      (add_zero a).symm (by omega) (by omega) i
  change c₀ ≫ twistMonomialMulHom n T (a + (0 : ℤ))
      (a + (e : ℤ)) e (by omega) i =
    twistMonomialMulHom n T a (a + (e : ℤ)) e (by omega) i at hin
  have hout := twistMonomialMulHom_comp_eqToHom n T
    a (a + (e : ℤ)) (-l) e (by omega) (by dsimp only [a]; omega) i
  change twistMonomialMulHom n T a (a + (e : ℤ)) e (by omega) i ≫ ct =
    twistMonomialMulHom n T a (-l) e (by omega) i at hout
  have hs : s = z.inv ≫ m₀ := by
    exact twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom n T e i
  have hdirect :
      (Modules.tensorUnitIso A).inv ≫ Modules.tensorMapRight A s ≫
          ae.hom ≫ ct =
        twistMonomialMulHom n T a (-l) e (by omega) i := by
    rw [hs, Modules.tensorMapRight_comp]
    calc
      (Modules.tensorUnitIso A).inv ≫
            (Modules.tensorMapRight A z.inv ≫
              Modules.tensorMapRight A m₀) ≫ ae.hom ≫ ct =
          ((Modules.tensorUnitIso A).inv ≫
            Modules.tensorMapRight A z.inv) ≫
              Modules.tensorMapRight A m₀ ≫ ae.hom ≫ ct := by
        simp only [Category.assoc]
      _ = (c₀ ≫ a₀.inv) ≫
              Modules.tensorMapRight A m₀ ≫ ae.hom ≫ ct :=
        congrArg (fun k ↦ k ≫ Modules.tensorMapRight A m₀ ≫ ae.hom ≫ ct)
          hzero
      _ = c₀ ≫ a₀.inv ≫
            (a₀.hom ≫ twistMonomialMulHom n T (a + (0 : ℤ))
              (a + (e : ℤ)) e (by omega) i) ≫ ct := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (c₀ ≫ a₀.inv) ≫ k ≫ ct) hm
      _ = c₀ ≫ twistMonomialMulHom n T (a + (0 : ℤ))
              (a + (e : ℤ)) e (by omega) i ≫ ct := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = twistMonomialMulHom n T a (a + (e : ℤ)) e (by omega) i ≫
            ct := congrArg (fun k ↦ k ≫ ct) hin
      _ = _ := hout
  change ∀ s : SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf ⟶
      projectiveSpaceOverTwist n T (e : ℤ), _ at hsection
  exact hdirect.symm.trans (hsection s)

end AlgebraicGeometry.Scheme

end

end
