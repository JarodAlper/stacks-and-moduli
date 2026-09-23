module

public import StacksAndModuli.API.RelativeVeryAmplePullback
public import StacksAndModuli.API.RepresentedRelativeClassifyingImmersion

/-!
# Very ampleness induced by a represented Grassmannian immersion

Combining the represented-classifying immersion with the Plücker line bundle gives the
generic endgame used by the determinant statement for Quot schemes.

Main declaration:

* `AlgebraicGeometry.Scheme.isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A relatively representable immersion into a relative Grassmannian makes the
determinant of the pulled-back universal quotient relatively very ample on any chosen
representative of the source functor. -/
theorem isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} {q n : ℕ}
    (V : S.Modules) [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V)
    (α : F ⟶ Modules.grassmannianOverFunctor q V)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α)
    {Q P : Over S} (eF : F.RepresentableBy Q)
    (eG : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (x : Modules.PullbackQuotient q V P)
    (hx : Quotient.mk (Modules.PullbackQuotient.setoid q V P) x =
      eG.homEquiv (𝟙 P)) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower
        (x.pullback (representedRelativeClassifyingHom hα eF eG)).Q q) :=
  isRelativelyVeryAmple_exteriorPower_pullback_universalQuotient
    V hV eG x hx (representedRelativeClassifyingHom hα eF eG)
      (representedRelativeClassifyingHom_isImmersion α hα eF eG)

/-- Isomorphic identification of the pulled-back universal quotient may be supplied after
the represented Grassmannian-immersion argument.  This is the form used when the target
is a canonically defined pushforward sheaf. -/
theorem isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion_of_iso
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} {q n : ℕ}
    (V : S.Modules) [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V)
    (α : F ⟶ Modules.grassmannianOverFunctor q V)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α)
    {Q P : Over S} (eF : F.RepresentableBy Q)
    (eG : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (x : Modules.PullbackQuotient q V P)
    (hx : Quotient.mk (Modules.PullbackQuotient.setoid q V P) x =
      eG.homEquiv (𝟙 P)) (M : Q.left.Modules) [M.IsQuasicoherent]
    (e : (x.pullback (representedRelativeClassifyingHom hα eF eG)).Q ≅ M) :
    IsRelativelyVeryAmple Q.hom (Modules.exteriorPower M q) := by
  have h := isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion
    V hV α hα eF eG x hx
  exact h.of_iso (Modules.exteriorPowerIso e q)

/-- Point-representative form of the Grassmannian very-ampleness endgame.  It is enough
to exhibit a concrete quotient presentation for the image of the universal source point;
the quotient presentation selected on the representing Grassmannian is automatically
isomorphic to it.  This avoids making any result depend on the representative chosen by
`Quotient.out`. -/
theorem isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion_of_point
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} {q n : ℕ}
    (V : S.Modules) [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V)
    (α : F ⟶ Modules.grassmannianOverFunctor q V)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α)
    {Q P : Over S} (eF : F.RepresentableBy Q)
    (eG : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (y : Modules.PullbackQuotient q V Q)
    (hy : Quotient.mk (Modules.PullbackQuotient.setoid q V Q) y =
      α.app (op Q) (eF.homEquiv (𝟙 Q))) (M : Q.left.Modules) [M.IsQuasicoherent]
    (e : y.Q ≅ M) :
    IsRelativelyVeryAmple Q.hom (Modules.exteriorPower M q) := by
  let x : Modules.PullbackQuotient q V P := (eG.homEquiv (𝟙 P)).out
  have hx : Quotient.mk (Modules.PullbackQuotient.setoid q V P) x =
      eG.homEquiv (𝟙 P) := Quotient.out_eq _
  let t : Q ⟶ P := representedRelativeClassifyingHom hα eF eG
  have hxy : (Modules.PullbackQuotient.setoid q V Q).r (x.pullback t) y := by
    apply Quotient.exact
    calc
      Quotient.mk (Modules.PullbackQuotient.setoid q V Q) (x.pullback t) =
          (Modules.grassmannianOverFunctor q V).map t.op
            (Quotient.mk (Modules.PullbackQuotient.setoid q V P) x) := rfl
      _ = (Modules.grassmannianOverFunctor q V).map t.op
            (eG.homEquiv (𝟙 P)) := congrArg _ hx
      _ = eG.homEquiv t := by
        simpa only [Category.comp_id] using
          (eG.homEquiv_comp t (𝟙 P)).symm
      _ = α.app (op Q) (eF.homEquiv (𝟙 Q)) :=
        representedRelativeClassifyingHom_homEquiv α hα eF eG
      _ = Quotient.mk (Modules.PullbackQuotient.setoid q V Q) y := hy.symm
  obtain ⟨i, -⟩ := hxy
  exact isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion_of_iso
    V hV α hα eF eG x hx M (i ≪≫ e)

end AlgebraicGeometry.Scheme

end

end
