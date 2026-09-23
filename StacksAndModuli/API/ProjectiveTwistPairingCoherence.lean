module

public import StacksAndModuli.API.ProjectiveTwistMultiplicationCoherence

/-!
# Pairing coherence for opposite projective twists

The multiplication isomorphism between opposite polynomial twists defines a canonical
coevaluation/evaluation pair.  This file proves its left triangle identity from the
associativity, commutativity, and unit coherence of twist multiplication.
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

section DegreeTransport

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (G : ℕ → σ) [GradedRing G]

/-- Multiplication is compatible with transport of the degree in its left factor. -/
lemma multiplyHom_transport_left
    (a a' b t : ℤ) (h : a = a')
    (hout : a' + b = t) (hout' : a + b = t) :
    Scheme.Modules.tensorMapLeft
          (eqToHom (congrArg (twist G) h)) (twist G b) ≫
        multiplyHom G a' b ≫
        eqToHom (congrArg (twist G) hout) =
      multiplyHom G a b ≫
        eqToHom (congrArg (twist G) hout') := by
  subst a'
  simp only [eqToHom_refl, Scheme.Modules.tensorMapLeft_id,
    Category.id_comp]

/-- Multiplication is compatible with transport of the degree in its right factor. -/
lemma multiplyHom_transport_right
    (a b b' t : ℤ) (h : b = b')
    (hout : a + b' = t) (hout' : a + b = t) :
    Scheme.Modules.tensorMapRight (twist G a)
          (eqToHom (congrArg (twist G) h)) ≫
        multiplyHom G a b' ≫
        eqToHom (congrArg (twist G) hout) =
      multiplyHom G a b ≫
        eqToHom (congrArg (twist G) hout') := by
  subst b'
  simp only [eqToHom_refl, Scheme.Modules.tensorMapRight_id,
    Category.id_comp]

end DegreeTransport

/-- Opposite polynomial twists, paired by multiplication and the zero-twist
identification, satisfy the left triangle identity. -/
lemma polynomialTwist_pairing_left_triangle_nat (n d : ℕ) :
    let R := ULift.{u} ℤ
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
    let a : ℤ := -(d : ℤ)
    let N := twist 𝒜 a
    let D := twist 𝒜 (d : ℤ)
    let ev : Scheme.Modules.tensor N D ≅
        SheafOfModules.unit (Proj 𝒜).ringCatSheaf :=
      polynomialMultiplyIso (R := R) (Fin (n + 1)) a (d : ℤ) ≪≫
        eqToIso (congrArg (twist 𝒜) (by omega)) ≪≫ zeroIso 𝒜
    (Scheme.Modules.tensorLeftUnitIso N).inv ≫
        Scheme.Modules.tensorMapLeft ev.inv N ≫
        (Scheme.Modules.tensorAssocIso N D N).hom ≫
        Scheme.Modules.tensorMapRight N
          ((Scheme.Modules.tensorCommIso D N).hom ≫ ev.hom) ≫
      (Scheme.Modules.tensorUnitIso N).hom = 𝟙 N := by
  dsimp only
  let R := ULift.{u} ℤ
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let a : ℤ := -(d : ℤ)
  let N := twist 𝒜 a
  let D := twist 𝒜 (d : ℤ)
  let μ := multiplyHom 𝒜 a (d : ℤ)
  letI : IsIso μ := by
    dsimp only [μ, 𝒜, R]
    exact polynomial_multiplyHom_isIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) a (d : ℤ)
  let z := zeroIso 𝒜
  let had : a + (d : ℤ) = 0 := by dsimp only [a]; omega
  let c : twist 𝒜 (a + (d : ℤ)) ≅ twist 𝒜 0 :=
    eqToIso (congrArg (twist 𝒜) had)
  let hda : (d : ℤ) + a = 0 := by dsimp only [a]; omega
  let c' : twist 𝒜 ((d : ℤ) + a) ≅ twist 𝒜 0 :=
    eqToIso (congrArg (twist 𝒜) hda)
  let μ' := multiplyHom 𝒜 (d : ℤ) a
  letI : IsIso μ' := by
    dsimp only [μ', 𝒜, R]
    exact polynomial_multiplyHom_isIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) (d : ℤ) a
  let q : Scheme.Modules.tensor N D ≅ twist 𝒜 0 := asIso μ ≪≫ c
  let r : Scheme.Modules.tensor D N ≅ twist 𝒜 0 := asIso μ' ≪≫ c'
  let μ0 := multiplyHom 𝒜 0 a
  letI : IsIso μ0 := by
    dsimp only [μ0, 𝒜, R]
    exact polynomial_multiplyHom_isIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) 0 a
  let c0 : twist 𝒜 (0 + a) ≅ N :=
    eqToIso (congrArg (twist 𝒜) (zero_add a))
  let m0 : Scheme.Modules.tensor (twist 𝒜 0) N ≅ N :=
    asIso μ0 ≪≫ c0
  let μA0 := multiplyHom 𝒜 a 0
  letI : IsIso μA0 := by
    dsimp only [μA0, 𝒜, R]
    exact polynomial_multiplyHom_isIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) a 0
  let cA0 : twist 𝒜 (a + 0) ≅ N :=
    eqToIso (congrArg (twist 𝒜) (add_zero a))
  let mA0 : Scheme.Modules.tensor N (twist 𝒜 0) ≅ N :=
    asIso μA0 ≪≫ cA0
  have hleftUnit :
      Scheme.Modules.tensorMapLeft z.inv N ≫ m0.hom =
        (Scheme.Modules.tensorLeftUnitIso N).hom := by
    dsimp only [m0, c0, μ0, z, N, Iso.trans_hom, asIso_hom]
    exact tensorMapLeft_zeroIso_inv_multiplyHom 𝒜 a
  have hprefix :
      (Scheme.Modules.tensorLeftUnitIso N).inv ≫
          Scheme.Modules.tensorMapLeft z.inv N = m0.inv := by
    rw [← cancel_mono m0.hom]
    calc
      ((Scheme.Modules.tensorLeftUnitIso N).inv ≫
            Scheme.Modules.tensorMapLeft z.inv N) ≫ m0.hom =
          (Scheme.Modules.tensorLeftUnitIso N).inv ≫
            (Scheme.Modules.tensorLeftUnitIso N).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (Scheme.Modules.tensorLeftUnitIso N).inv ≫ k) hleftUnit
      _ = 𝟙 N := (Scheme.Modules.tensorLeftUnitIso N).inv_hom_id
      _ = m0.inv ≫ m0.hom := m0.inv_hom_id.symm
  have hrightUnit :
      (Scheme.Modules.tensorUnitIso N).inv ≫
          Scheme.Modules.tensorMapRight N z.inv ≫ mA0.hom = 𝟙 N := by
    dsimp only [mA0, cA0, μA0, z, N, Iso.trans_hom, asIso_hom]
    exact tensorUnitIso_inv_tensorMapRight_zeroIso_inv_multiplyHom 𝒜 a
  have hsuffix :
      Scheme.Modules.tensorMapRight N z.hom ≫
          (Scheme.Modules.tensorUnitIso N).hom = mA0.hom := by
    letI : IsIso (Scheme.Modules.tensorMapRight N z.inv) := by
      change IsIso (Scheme.Modules.tensorRightIso N z).inv
      infer_instance
    letI : IsIso ((Scheme.Modules.tensorUnitIso N).inv ≫
        Scheme.Modules.tensorMapRight N z.inv) := by infer_instance
    have hz : Scheme.Modules.tensorMapRight N z.inv ≫
        Scheme.Modules.tensorMapRight N z.hom = 𝟙 _ := by
      change (Scheme.Modules.tensorRightIso N z).inv ≫
        (Scheme.Modules.tensorRightIso N z).hom = 𝟙 _
      exact (Scheme.Modules.tensorRightIso N z).inv_hom_id
    rw [← cancel_epi ((Scheme.Modules.tensorUnitIso N).inv ≫
      Scheme.Modules.tensorMapRight N z.inv)]
    calc
      ((Scheme.Modules.tensorUnitIso N).inv ≫
            Scheme.Modules.tensorMapRight N z.inv) ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom) = 𝟙 N := by
        slice_lhs 2 3 => rw [hz]
        simp
      _ = ((Scheme.Modules.tensorUnitIso N).inv ≫
            Scheme.Modules.tensorMapRight N z.inv) ≫ mA0.hom :=
        hrightUnit.symm
  have hcomm :
      (Scheme.Modules.tensorCommIso D N).hom ≫ q.hom = r.hom := by
    let hswap : a + (d : ℤ) = (d : ℤ) + a := by omega
    have h := multiplyHom_comm' 𝒜 (d : ℤ) a hswap
    dsimp only [q, r, c, c', μ, μ', Iso.trans_hom, asIso_hom]
    change (Scheme.Modules.tensorCommIso D N).hom ≫ μ ≫
        eqToHom (congrArg (twist 𝒜) had) =
      μ' ≫ eqToHom (congrArg (twist 𝒜) hda)
    simpa only [Category.assoc, eqToHom_trans] using congrArg
      (fun k ↦ k ≫ eqToHom (congrArg (twist 𝒜) hda)) h
  let hL : (a + (d : ℤ)) + a = a := by omega
  let hR : a + ((d : ℤ) + a) = a := by omega
  have htransportL :
      Scheme.Modules.tensorMapLeft c.hom N ≫ μ0 ≫ c0.hom =
        multiplyHom 𝒜 (a + (d : ℤ)) a ≫
          eqToHom (congrArg (twist 𝒜) hL) := by
    exact multiplyHom_transport_left 𝒜
      (a + (d : ℤ)) 0 a a had (zero_add a) hL
  have htransportR :
      Scheme.Modules.tensorMapRight N c'.hom ≫ μA0 ≫ cA0.hom =
        multiplyHom 𝒜 a ((d : ℤ) + a) ≫
          eqToHom (congrArg (twist 𝒜) hR) := by
    exact multiplyHom_transport_right 𝒜
      a ((d : ℤ) + a) 0 a hda (add_zero a) hR
  have hassoc0 := multiplyHom_assoc' 𝒜 a (d : ℤ) a
    (add_assoc a (d : ℤ) a)
  have hassoc :
      Scheme.Modules.tensorMapLeft μ N ≫
          multiplyHom 𝒜 (a + (d : ℤ)) a ≫
          eqToHom (congrArg (twist 𝒜) hL) =
        (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N μ' ≫
          multiplyHom 𝒜 a ((d : ℤ) + a) ≫
          eqToHom (congrArg (twist 𝒜) hR) := by
    simpa only [N, D, μ, μ', Category.assoc, eqToHom_trans] using congrArg
      (fun k ↦ k ≫ eqToHom (congrArg (twist 𝒜) hR)) hassoc0
  have hnormalized :
      Scheme.Modules.tensorMapLeft q.hom N ≫ m0.hom =
        (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N r.hom ≫ mA0.hom := by
    calc
      Scheme.Modules.tensorMapLeft q.hom N ≫ m0.hom =
          Scheme.Modules.tensorMapLeft μ N ≫
            Scheme.Modules.tensorMapLeft c.hom N ≫ μ0 ≫ c0.hom := by
        dsimp only [q, m0, Iso.trans_hom, asIso_hom]
        rw [Scheme.Modules.tensorMapLeft_comp]
        simp only [Category.assoc]
      _ = Scheme.Modules.tensorMapLeft μ N ≫
            multiplyHom 𝒜 (a + (d : ℤ)) a ≫
            eqToHom (congrArg (twist 𝒜) hL) := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ Scheme.Modules.tensorMapLeft μ N ≫ k) htransportL
      _ = (Scheme.Modules.tensorAssocIso N D N).hom ≫
            Scheme.Modules.tensorMapRight N μ' ≫
            multiplyHom 𝒜 a ((d : ℤ) + a) ≫
            eqToHom (congrArg (twist 𝒜) hR) := hassoc
      _ = (Scheme.Modules.tensorAssocIso N D N).hom ≫
            Scheme.Modules.tensorMapRight N μ' ≫
            Scheme.Modules.tensorMapRight N c'.hom ≫ μA0 ≫ cA0.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (Scheme.Modules.tensorAssocIso N D N).hom ≫
            Scheme.Modules.tensorMapRight N μ' ≫ k) htransportR.symm
      _ = (Scheme.Modules.tensorAssocIso N D N).hom ≫
            Scheme.Modules.tensorMapRight N r.hom ≫ mA0.hom := by
        dsimp only [r, mA0, Iso.trans_hom, asIso_hom]
        rw [Scheme.Modules.tensorMapRight_comp]
        simp only [Category.assoc]
  change (Scheme.Modules.tensorLeftUnitIso N).inv ≫
      Scheme.Modules.tensorMapLeft (z.inv ≫ c.inv ≫ inv μ) N ≫
      (Scheme.Modules.tensorAssocIso N D N).hom ≫
      Scheme.Modules.tensorMapRight N
        ((Scheme.Modules.tensorCommIso D N).hom ≫ μ ≫ c.hom ≫ z.hom) ≫
      (Scheme.Modules.tensorUnitIso N).hom = 𝟙 N
  change (Scheme.Modules.tensorLeftUnitIso N).inv ≫
      Scheme.Modules.tensorMapLeft (z.inv ≫ q.inv) N ≫
      (Scheme.Modules.tensorAssocIso N D N).hom ≫
      Scheme.Modules.tensorMapRight N
        ((Scheme.Modules.tensorCommIso D N).hom ≫ q.hom ≫ z.hom) ≫
      (Scheme.Modules.tensorUnitIso N).hom = 𝟙 N
  rw [Scheme.Modules.tensorMapLeft_comp,
    Scheme.Modules.tensorMapRight_comp, Scheme.Modules.tensorMapRight_comp]
  simp only [Category.assoc]
  have hcommT :
      Scheme.Modules.tensorMapRight N (Scheme.Modules.tensorCommIso D N).hom ≫
          Scheme.Modules.tensorMapRight N q.hom =
        Scheme.Modules.tensorMapRight N r.hom := by
    calc
      _ = Scheme.Modules.tensorMapRight N
          ((Scheme.Modules.tensorCommIso D N).hom ≫ q.hom) :=
        (Scheme.Modules.tensorMapRight_comp N _ _).symm
      _ = _ := congrArg (Scheme.Modules.tensorMapRight N) hcomm
  have hq :
      Scheme.Modules.tensorMapLeft q.inv N ≫
          Scheme.Modules.tensorMapLeft q.hom N = 𝟙 _ := by
    change (Scheme.Modules.tensorLeftIso q N).inv ≫
      (Scheme.Modules.tensorLeftIso q N).hom = 𝟙 _
    exact (Scheme.Modules.tensorLeftIso q N).inv_hom_id
  calc
    (Scheme.Modules.tensorLeftUnitIso N).inv ≫
          Scheme.Modules.tensorMapLeft z.inv N ≫
          Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N
            (Scheme.Modules.tensorCommIso D N).hom ≫
          Scheme.Modules.tensorMapRight N q.hom ≫
          Scheme.Modules.tensorMapRight N z.hom ≫
          (Scheme.Modules.tensorUnitIso N).hom =
        ((Scheme.Modules.tensorLeftUnitIso N).inv ≫
          Scheme.Modules.tensorMapLeft z.inv N) ≫
          Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          (Scheme.Modules.tensorMapRight N
            (Scheme.Modules.tensorCommIso D N).hom ≫
            Scheme.Modules.tensorMapRight N q.hom) ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom) := by
      simp only [Category.assoc]
    _ = m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          (Scheme.Modules.tensorMapRight N
            (Scheme.Modules.tensorCommIso D N).hom ≫
            Scheme.Modules.tensorMapRight N q.hom) ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom) :=
      congrArg
        (fun k ↦ k ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          (Scheme.Modules.tensorMapRight N
            (Scheme.Modules.tensorCommIso D N).hom ≫
            Scheme.Modules.tensorMapRight N q.hom) ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom)) hprefix
    _ = m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N r.hom ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫ k ≫
          (Scheme.Modules.tensorMapRight N z.hom ≫
            (Scheme.Modules.tensorUnitIso N).hom)) hcommT
    _ = m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N r.hom ≫ mA0.hom :=
      congrArg
        (fun k ↦ m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          (Scheme.Modules.tensorAssocIso N D N).hom ≫
          Scheme.Modules.tensorMapRight N r.hom ≫ k) hsuffix
    _ = m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫
          Scheme.Modules.tensorMapLeft q.hom N ≫ m0.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ m0.inv ≫ Scheme.Modules.tensorMapLeft q.inv N ≫ k)
        hnormalized.symm
    _ = m0.inv ≫ 𝟙 _ ≫ m0.hom := by
      slice_lhs 2 3 => rw [hq]
    _ = 𝟙 N := by simp

end ProjectiveSpectrum.Twist

end

end
