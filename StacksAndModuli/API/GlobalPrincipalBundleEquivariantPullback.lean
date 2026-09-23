module

public import StacksAndModuli.API.PrincipalBundlePointTrivialization
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Equivariant maps of principal bundles

An equivariant map between principal bundles over a commuting map of bases is
cartesian.  The proof trivializes after the source torsor projection and then
descends the resulting isomorphism along that fppf cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme.GlobalPrincipalBundle

variable {S : Scheme.{u}} {G T T' : Over S} [GrpObj G]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- Acting on a point of a principal bundle does not change its image in the
base. -/
lemma smul_comp_projection (B : GlobalPrincipalBundle G T) {Z : Over S}
    (m : Z ⟶ G) (x : Z ⟶ B.P) : (m • x) ≫ B.p = x ≫ B.p := by
  change lift m x ≫ γ[G, B.P] ≫ B.p = x ≫ B.p
  rw [B.invariant]
  simp

lemma isPullback_of_equivariant (A : GlobalPrincipalBundle G T)
    (B : GlobalPrincipalBundle G T') (base : T ⟶ T')
    (total : A.P ⟶ B.P) (w : total ≫ B.p = A.p ≫ base)
    (hequivariant : IsModHom G total) :
    IsPullback total A.p B.p base := by
  letI : IsModHom G total := hequivariant
  let PB := Limits.pullback B.p base
  let j : A.P ⟶ PB := Limits.pullback.lift total A.p w
  have j_fst : j ≫ Limits.pullback.fst B.p base = total :=
    Limits.pullback.lift_fst _ _ _
  have j_snd : j ≫ Limits.pullback.snd B.p base = A.p :=
    Limits.pullback.lift_snd _ _ _
  let D := Limits.pullback A.p ((𝟙 A.P) ≫ A.p)
  let E := Limits.pullback B.p (total ≫ B.p)
  let l : D ⟶ E :=
    pointPullbackInv A (𝟙 A.P) ≫ pointPullbackTotal B total
  have l_fst : l ≫ Limits.pullback.fst B.p (total ≫ B.p) =
      Limits.pullback.fst A.p ((𝟙 A.P) ≫ A.p) ≫ total := by
    dsimp only [l]
    rw [Category.assoc, pointPullbackTotal_fst]
    change pointPullbackInv A (𝟙 A.P) ≫
        trivialActionMapTo (G := G) total = _
    rw [trivialActionMapTo, ModObj.comp_smul]
    rw [pointPullbackInv_fst, pointPullbackInv_snd_assoc]
    rw [← IsModHom.map_smul]
    simp only [Category.comp_id]
    rw [torsorDifference_smul]
  have l_snd : l ≫ Limits.pullback.snd B.p (total ≫ B.p) =
      Limits.pullback.snd A.p ((𝟙 A.P) ≫ A.p) := by
    dsimp only [l]
    rw [Category.assoc, pointPullbackTotal_snd, pointPullbackInv_snd]
  let hTotal : E ⟶ PB := Limits.pullback.lift
    (Limits.pullback.fst B.p (total ≫ B.p))
    (Limits.pullback.snd B.p (total ≫ B.p) ≫ A.p) (by
      calc
        Limits.pullback.fst B.p (total ≫ B.p) ≫ B.p =
            Limits.pullback.snd B.p (total ≫ B.p) ≫
              (total ≫ B.p) := Limits.pullback.condition
        _ = Limits.pullback.snd B.p (total ≫ B.p) ≫
              (A.p ≫ base) :=
            congrArg (fun q ↦
              Limits.pullback.snd B.p (total ≫ B.p) ≫ q) w
        _ = (Limits.pullback.snd B.p (total ≫ B.p) ≫ A.p) ≫
              base := (Category.assoc _ _ _).symm)
  have hTotal_fst : hTotal ≫ Limits.pullback.fst B.p base =
      Limits.pullback.fst B.p (total ≫ B.p) :=
    Limits.pullback.lift_fst _ _ _
  have hTotal_snd : hTotal ≫ Limits.pullback.snd B.p base =
      Limits.pullback.snd B.p (total ≫ B.p) ≫ A.p :=
    Limits.pullback.lift_snd _ _ _
  have hcover : IsPullback hTotal
      (Limits.pullback.snd B.p (total ≫ B.p))
      (Limits.pullback.snd B.p base) A.p := by
    apply IsPullback.mk'
    · exact hTotal_snd
    · intro Q a b hab hbase
      apply Limits.pullback.hom_ext
      · have h := congrArg (fun q ↦ q ≫ Limits.pullback.fst B.p base) hab
        simpa only [Category.assoc, hTotal_fst] using h
      · exact hbase
    · intro Q a b hab
      let z : Q ⟶ E := Limits.pullback.lift
        (a ≫ Limits.pullback.fst B.p base) b (by
          calc
            (a ≫ Limits.pullback.fst B.p base) ≫ B.p =
                (a ≫ Limits.pullback.snd B.p base) ≫ base := by
              simpa only [Category.assoc] using
                congrArg (fun q ↦ a ≫ q) Limits.pullback.condition
            _ = (b ≫ A.p) ≫ base := by rw [hab]
            _ = b ≫ (total ≫ B.p) := by
              rw [Category.assoc, w])
      refine ⟨z, ?_, Limits.pullback.lift_snd _ _ _⟩
      apply Limits.pullback.hom_ext
      · change (z ≫ hTotal) ≫ Limits.pullback.fst B.p base = _
        rw [Category.assoc, hTotal_fst]
        exact Limits.pullback.lift_fst _ _ _
      · change (z ≫ hTotal) ≫ Limits.pullback.snd B.p base = _
        rw [Category.assoc, hTotal_snd, ← Category.assoc]
        rw [show z ≫ Limits.pullback.snd B.p (total ≫ B.p) = b from
          Limits.pullback.lift_snd _ _ _]
        exact hab.symm
  have hlocal_comm : l ≫ hTotal =
      Limits.pullback.fst A.p ((𝟙 A.P) ≫ A.p) ≫ j := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hTotal_fst, l_fst,
        Category.assoc, j_fst]
    · rw [Category.assoc, hTotal_snd, ← Category.assoc, l_snd,
        Category.assoc, j_snd]
      simpa only [Category.id_comp] using
        (Limits.pullback.condition :
          Limits.pullback.fst A.p ((𝟙 A.P) ≫ A.p) ≫ A.p =
            Limits.pullback.snd A.p ((𝟙 A.P) ≫ A.p) ≫
              ((𝟙 A.P) ≫ A.p)).symm
  have hlocal : IsPullback l
      (Limits.pullback.fst A.p ((𝟙 A.P) ≫ A.p)) hTotal j := by
    apply IsPullback.mk'
    · exact hlocal_comm
    · intro Q a b hab hbase
      apply Limits.pullback.hom_ext
      · exact hbase
      · have h := congrArg
          (fun q ↦ q ≫ Limits.pullback.snd B.p (total ≫ B.p)) hab
        rw [Category.assoc, l_snd, Category.assoc, l_snd] at h
        exact h
    · intro Q a b hab
      have hbase : b ≫ A.p =
          (a ≫ Limits.pullback.snd B.p (total ≫ B.p)) ≫
            ((𝟙 A.P) ≫ A.p) := by
        have h := congrArg (fun q ↦ q ≫ Limits.pullback.snd B.p base) hab
        rw [Category.assoc, hTotal_snd, Category.assoc, j_snd] at h
        simpa only [Category.assoc, Category.id_comp] using h.symm
      let z : Q ⟶ D := Limits.pullback.lift b
        (a ≫ Limits.pullback.snd B.p (total ≫ B.p)) hbase
      refine ⟨z, ?_, Limits.pullback.lift_fst _ _ _⟩
      apply Limits.pullback.hom_ext
      · have h := congrArg (fun q ↦ q ≫ Limits.pullback.fst B.p base) hab
        rw [Category.assoc, hTotal_fst, Category.assoc, j_fst] at h
        change (z ≫ l) ≫ Limits.pullback.fst B.p (total ≫ B.p) = _
        rw [Category.assoc, l_fst, ← Category.assoc]
        rw [show z ≫ Limits.pullback.fst A.p ((𝟙 A.P) ≫ A.p) = b from
          Limits.pullback.lift_fst _ _ _]
        exact h.symm
      · change (z ≫ l) ≫ Limits.pullback.snd B.p (total ≫ B.p) = _
        rw [Category.assoc, l_snd]
        exact Limits.pullback.lift_snd _ _ _
  letI : IsIso (pointPullbackInv A (𝟙 A.P)) :=
    ⟨⟨pointPullbackTotal A (𝟙 A.P),
      pointPullbackTotal_inv_hom A (𝟙 A.P),
      pointPullbackTotal_hom_inv A (𝟙 A.P)⟩⟩
  letI : IsIso l := by
    dsimp only [l]
    infer_instance
  let Q : MorphismProperty Scheme.{u} :=
    @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation
  have hQ : Q hTotal.left := by
    have hc := hcover.map (Over.forget S)
    exact ⟨⟨
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hc.flip
        (inferInstance : Surjective A.p.left),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hc.flip
        (inferInstance : Flat A.p.left)⟩,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hc.flip
        (inferInstance : LocallyOfFinitePresentation A.p.left)⟩
  have hj : MorphismProperty.isomorphisms Scheme.{u}
      ((Over.forget S).map j) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := Q)
      (hlocal.map (Over.forget S)) hQ (by
        change IsIso ((Over.forget S).map l)
        infer_instance)
  letI : IsIso ((Over.forget S).map j) := hj
  letI : IsIso j := isIso_of_reflects_iso j (Over.forget S)
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso j) j_fst j_snd

end AlgebraicGeometry.Scheme.GlobalPrincipalBundle
