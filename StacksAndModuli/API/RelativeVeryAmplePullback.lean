module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# Pulling back relative very ampleness along immersions

The Grassmannian formulation of relative very ampleness used in Corollary 2.2.15 is
stable under further immersion into the source.  The proof simply composes the chosen
immersion into the projective bundle and pulls back its universal line quotient.

Main declaration:

* `AlgebraicGeometry.Scheme.IsRelativelyVeryAmple.pullback_of_isImmersion`.
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

/-- Relative very ampleness is invariant under isomorphism of the designated line
bundle. -/
theorem IsRelativelyVeryAmple.of_iso
    {X S : Scheme.{u}} {f : X ⟶ S} {L L' : X.Modules}
    (hL : IsRelativelyVeryAmple f L) (e : L ≅ L') :
    IsRelativelyVeryAmple f L' := by
  obtain ⟨E, hEqc, hEfin, P, repr, t, ht, x, hx, ⟨i⟩⟩ := hL
  exact ⟨E, hEqc, hEfin, P, repr, t, ht, x, hx, ⟨i ≪≫ e⟩⟩

/-- Relative very ampleness is preserved by pullback along an immersion.  In the
Grassmannian presentation, the new projective-bundle map is the composite immersion and
the new universal quotient is the pullback of the old one. -/
theorem IsRelativelyVeryAmple.pullback_of_isImmersion
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ X} {L : X.Modules}
    (hL : IsRelativelyVeryAmple f L) (hg : IsImmersion g) :
    IsRelativelyVeryAmple (g ≫ f) ((Modules.pullback g).obj L) := by
  obtain ⟨E, hEqc, hEfin, P, repr, t, ht, x, hx, ⟨e⟩⟩ := hL
  letI : E.IsQuasicoherent := hEqc
  let a : Over.mk (g ≫ f) ⟶ Over.mk f := Over.homMk g rfl
  let t' : Over.mk (g ≫ f) ⟶ P := a ≫ t
  have ht' : IsImmersion t'.left := by
    change IsImmersion (g ≫ t.left)
    exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hg ht
  let x' : Modules.PullbackQuotient 1 E (Over.mk (g ≫ f)) := x.pullback a
  have hx' : Quotient.mk
      (Modules.PullbackQuotient.setoid 1 E (Over.mk (g ≫ f))) x' =
      repr.homEquiv t' := by
    rw [show t' = a ≫ t from rfl, repr.homEquiv_comp]
    rw [← hx]
    rfl
  refine ⟨E, inferInstance, hEfin, P, repr, t', ht', x', hx', ⟨?_⟩⟩
  exact (Modules.pullback g).mapIso e

/-- Pulling the universal quotient on a relative Grassmannian back along an immersed
test object gives a relatively very ample determinant on that object. -/
theorem isRelativelyVeryAmple_exteriorPower_pullback_universalQuotient
    {S : Scheme.{u}} {q n : ℕ} (V : S.Modules) [V.IsQuasicoherent]
    (hV : Modules.IsProjectiveOfRank n V) {P : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (x : Modules.PullbackQuotient q V P)
    (hx : Quotient.mk (Modules.PullbackQuotient.setoid q V P) x =
      repr.homEquiv (𝟙 P)) {Q : Over S} (t : Q ⟶ P) (ht : IsImmersion t.left) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower (x.pullback t).Q q) := by
  have hP : IsRelativelyVeryAmple P.hom (Modules.exteriorPower x.Q q) :=
    isRelativelyVeryAmple_exteriorPower_universalQuotient V hV repr x hx
  have hQ : IsRelativelyVeryAmple (t.left ≫ P.hom)
      ((Modules.pullback t.left).obj (Modules.exteriorPower x.Q q)) :=
    hP.pullback_of_isImmersion ht
  rw [Over.w t] at hQ
  haveI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact hQ.of_iso
    (Modules.pullbackExteriorPowerIso t.left x.Q x.isProjectiveOfRank q)

end AlgebraicGeometry.Scheme

end

end
