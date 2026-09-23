module

public import StacksAndModuli.API.GlobalPrincipalBundle

/-!
# Trivializing a principal bundle at a point

A map into the total space of a principal bundle canonically trivializes the
pullback bundle.  The construction is explicit: the forward map sends `(g,z)`
to `g • z`, while the inverse uses torsor coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme.GlobalPrincipalBundle

variable {S : Scheme.{u}} {G T Z : Over S} [GrpObj G]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- The map `(g,z) ↦ (g • z,z)` from the trivial bundle to the pullback of
a principal bundle along a chosen point. -/
noncomputable def pointPullbackTotal (B : GlobalPrincipalBundle G T)
    (z : Z ⟶ B.P) :
    (trivial G Z).P ⟶ Limits.pullback B.p (z ≫ B.p) :=
  pullback.lift
    (trivialActionMapTo (G := G) z)
    (trivialSnd G Z)
    (by
      letI : ModObj G T := ModObj.trivialAction G T
      letI : IsModHom G B.p := by
        constructor
        change γ[G, B.P] ≫ B.p = (G ◁ B.p) ≫ snd G T
        rw [B.invariant]
        simp
      rw [trivialActionMapTo_comp]
      simp only [trivialActionMapTo, CategoryTheory.Hom.smul_def]
      change lift _ _ ≫ snd G T = _
      simp)

@[reassoc (attr := simp)]
lemma pointPullbackTotal_fst (B : GlobalPrincipalBundle G T) (z : Z ⟶ B.P) :
    pointPullbackTotal B z ≫ pullback.fst B.p (z ≫ B.p) =
      trivialActionMapTo (G := G) z :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pointPullbackTotal_snd (B : GlobalPrincipalBundle G T) (z : Z ⟶ B.P) :
    pointPullbackTotal B z ≫ pullback.snd B.p (z ≫ B.p) =
      trivialSnd G Z :=
  pullback.lift_snd _ _ _

/-- The inverse candidate to `pointPullbackTotal`, expressed in torsor
coordinates. -/
noncomputable def pointPullbackInv (B : GlobalPrincipalBundle G T)
    (z : Z ⟶ B.P) :
    Limits.pullback B.p (z ≫ B.p) ⟶ (trivial G Z).P :=
  pullback.lift
    (torsorDifference B
      (pullback.fst B.p (z ≫ B.p))
      (pullback.snd B.p (z ≫ B.p) ≫ z)
      (by simpa only [Category.assoc] using
        (pullback.condition : pullback.fst B.p (z ≫ B.p) ≫ B.p =
          pullback.snd B.p (z ≫ B.p) ≫ (z ≫ B.p))))
    (pullback.snd B.p (z ≫ B.p))
    (by apply toUnit_unique)

@[reassoc (attr := simp)]
lemma pointPullbackInv_fst (B : GlobalPrincipalBundle G T) (z : Z ⟶ B.P) :
    pointPullbackInv B z ≫ trivialFst G Z =
      torsorDifference B
        (pullback.fst B.p (z ≫ B.p))
        (pullback.snd B.p (z ≫ B.p) ≫ z)
        (by simpa only [Category.assoc] using
          (pullback.condition : pullback.fst B.p (z ≫ B.p) ≫ B.p =
            pullback.snd B.p (z ≫ B.p) ≫ (z ≫ B.p))) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pointPullbackInv_snd (B : GlobalPrincipalBundle G T) (z : Z ⟶ B.P) :
    pointPullbackInv B z ≫ trivialSnd G Z =
      pullback.snd B.p (z ≫ B.p) :=
  pullback.lift_snd _ _ _

/-- The point-induced map followed by its torsor-coordinate inverse is the
identity. -/
lemma pointPullbackTotal_hom_inv (B : GlobalPrincipalBundle G T)
    (z : Z ⟶ B.P) :
    pointPullbackTotal B z ≫ pointPullbackInv B z = 𝟙 _ := by
  apply trivial_hom_ext
  · rw [Category.assoc, pointPullbackInv_fst, Category.id_comp]
    apply smul_left_cancel B (trivialSnd G Z ≫ z)
    calc
      (pointPullbackTotal B z ≫
            torsorDifference B (pullback.fst B.p (z ≫ B.p))
              (pullback.snd B.p (z ≫ B.p) ≫ z) _) •
          (trivialSnd G Z ≫ z) =
          (pointPullbackTotal B z ≫
            torsorDifference B (pullback.fst B.p (z ≫ B.p))
              (pullback.snd B.p (z ≫ B.p) ≫ z) _) •
          (pointPullbackTotal B z ≫
            (pullback.snd B.p (z ≫ B.p) ≫ z)) := by
              rw [pointPullbackTotal_snd_assoc]
      _ = pointPullbackTotal B z ≫
          (torsorDifference B (pullback.fst B.p (z ≫ B.p))
              (pullback.snd B.p (z ≫ B.p) ≫ z) _ •
            (pullback.snd B.p (z ≫ B.p) ≫ z)) := by
              rw [ModObj.comp_smul]
      _ = pointPullbackTotal B z ≫ pullback.fst B.p (z ≫ B.p) := by
            rw [torsorDifference_smul]
      _ = trivialActionMapTo (G := G) z := pointPullbackTotal_fst B z
      _ = trivialFst G Z • (trivialSnd G Z ≫ z) := rfl
  · simp

/-- The torsor-coordinate inverse followed by the point-induced map is the
identity. -/
lemma pointPullbackTotal_inv_hom (B : GlobalPrincipalBundle G T)
    (z : Z ⟶ B.P) :
    pointPullbackInv B z ≫ pointPullbackTotal B z = 𝟙 _ := by
  apply pullback.hom_ext
  · calc
      (pointPullbackInv B z ≫ pointPullbackTotal B z) ≫
          pullback.fst B.p (z ≫ B.p) =
          pointPullbackInv B z ≫ trivialActionMapTo (G := G) z := by
            rw [Category.assoc, pointPullbackTotal_fst]
      _ = (pointPullbackInv B z ≫ trivialFst G Z) •
          (pointPullbackInv B z ≫ trivialSnd G Z ≫ z) := by
            rw [trivialActionMapTo, ModObj.comp_smul]
      _ = torsorDifference B (pullback.fst B.p (z ≫ B.p))
            (pullback.snd B.p (z ≫ B.p) ≫ z) _ •
          (pullback.snd B.p (z ≫ B.p) ≫ z) := by
            rw [pointPullbackInv_fst, pointPullbackInv_snd_assoc]
      _ = pullback.fst B.p (z ≫ B.p) := torsorDifference_smul B _ _ _
      _ = 𝟙 _ ≫ pullback.fst B.p (z ≫ B.p) := by simp
  · simp

/-- The point-induced trivialization is an isomorphism. -/
noncomputable instance pointPullbackTotal_isIso
    (B : GlobalPrincipalBundle G T) (z : Z ⟶ B.P) :
    IsIso (pointPullbackTotal B z) :=
  ⟨⟨pointPullbackInv B z, pointPullbackTotal_hom_inv B z,
    pointPullbackTotal_inv_hom B z⟩⟩

/-- The point-induced trivialization is equivariant. -/
lemma pointPullbackTotal_equivariant (B : GlobalPrincipalBundle G T)
    (z : Z ⟶ B.P) :
    letI := ModObj.pullbackTorsorAction B.p (z ≫ B.p) B.invariant
    IsModHom G (pointPullbackTotal B z) := by
  letI : ModObj G T := ModObj.trivialAction G T
  letI : ModObj G Z := ModObj.trivialAction G Z
  letI : IsModHom G B.p := by
    constructor
    change γ[G, B.P] ≫ B.p = (G ◁ B.p) ≫ snd G T
    rw [B.invariant]
    simp
  letI : IsModHom G (z ≫ B.p) := ModObj.isModHom_trivialAction G _
  letI : IsModHom G (trivialActionMapTo (G := G) z) :=
    trivialActionMapTo_equivariant (G := G) z
  letI : IsModHom G (trivialSnd G Z) := by
    constructor
    change γ[G, (trivial G Z).P] ≫ trivialSnd G Z =
      (G ◁ trivialSnd G Z) ≫ snd G Z
    rw [trivialSnd_invariant]
    simp
  exact ModObj.isModHom_pullback_lift G B.p (z ≫ B.p)
    (trivialActionMapTo (G := G) z) (trivialSnd G Z) _

end AlgebraicGeometry.Scheme.GlobalPrincipalBundle
