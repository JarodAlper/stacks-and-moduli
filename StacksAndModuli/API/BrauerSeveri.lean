module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import StacksAndModuli.API.ArrowCartesianProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Brauer--Severi morphisms

This file defines a Brauer--Severi morphism of relative dimension `r` exactly as
an étale form of relative projective `r`-space: after a surjective étale base
change, its pullback is isomorphic over the new base to `ℙ^r`.

This is the geometric definition used in Appendix B.1.5 and in Exercise 3.5.15(a).
The further equivalence with principal `PGL_(r+1)`-bundles requires representability
of the automorphism functor of projective space and is deliberately not built into
the definition.

Main declarations:

* `AlgebraicGeometry.Scheme.IsBrauerSeveri`: the predicate on a scheme morphism;
* `AlgebraicGeometry.Scheme.brauerSeveriProperty`: its bundled morphism property;
* `AlgebraicGeometry.Scheme.brauerSeveriPrestack`: the cartesian-family
  prestack of Brauer--Severi schemes.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism `P ⟶ S` is Brauer--Severi of relative dimension `r` if it becomes
isomorphic over some surjective étale cover `T ⟶ S` to relative projective
`r`-space over `T`. -/
def IsBrauerSeveri (r : ℕ) {P S : Scheme.{u}} (f : P ⟶ S) : Prop :=
  ∃ (T : Scheme.{u}) (p : T ⟶ S),
    Etale p ∧ Surjective p ∧
      Nonempty
        (Over.mk (pullback.snd f p) ≅
          Over.mk (projectiveSpaceOverπ r T))

/-- The morphism property of being a Brauer--Severi scheme of relative
dimension `r`. -/
def brauerSeveriProperty (r : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ IsBrauerSeveri r f

lemma mem_brauerSeveriProperty_iff (r : ℕ) {P S : Scheme.{u}} (f : P ⟶ S) :
    brauerSeveriProperty r f ↔ IsBrauerSeveri r f :=
  Iff.rfl

/-- Relative projective space commutes with an arbitrary base change, expressed
as an isomorphism in the slice over the new base. -/
noncomputable def projectiveSpaceOverPullbackIso (r : ℕ) {T' T : Scheme.{u}}
    (q : T' ⟶ T) :
    Over.mk (pullback.snd (projectiveSpaceOverπ r T) q) ≅
      Over.mk (projectiveSpaceOverπ r T') := by
  let zT : T ⟶ Spec (.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from T
  let zT' : T' ⟶ Spec (.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from T'
  let zP : projectiveSpace r ⟶ Spec (.of (ULift.{u} ℤ)) :=
    specULiftZIsTerminal.from (projectiveSpace r)
  have hterm : q ≫ zT = zT' := specULiftZIsTerminal.hom_ext _ _
  have houter : IsPullback
      (pullback.fst (projectiveSpaceOverπ r T) q ≫
        pullback.snd zT zP)
      (pullback.snd (projectiveSpaceOverπ r T) q)
      zP zT' := by
    have htop := IsPullback.of_hasPullback (projectiveSpaceOverπ r T) q
    have hright := (IsPullback.of_hasPullback zT zP).flip
    have hpaste := htop.paste_horiz hright
    rw [hterm] at hpaste
    exact hpaste
  exact houter.flip.isoOverPullback

/-- Relative projective space is the trivial Brauer--Severi morphism. -/
lemma projectiveSpaceOver_isBrauerSeveri (r : ℕ) (S : Scheme.{u}) :
    IsBrauerSeveri r (projectiveSpaceOverπ r S) :=
  ⟨S, 𝟙 S, inferInstance, inferInstance,
    ⟨projectiveSpaceOverPullbackIso r (𝟙 S)⟩⟩

section PullbackComparison

variable {X Y Y' S T : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
  (p : T ⟶ S)

/-- The map from the iterated pullback
`(Y ×_S T) ×_T (T ×_S X)` to the base change `Y'`, obtained from the
pullback square defining `Y'`. -/
noncomputable def brauerSeveriToBaseChange :
    pullback (pullback.snd g p) (pullback.fst p f) ⟶ Y' := by
  let toY : pullback (pullback.snd g p) (pullback.fst p f) ⟶ Y :=
    pullback.fst (pullback.snd g p) (pullback.fst p f) ≫ pullback.fst g p
  let toX : pullback (pullback.snd g p) (pullback.fst p f) ⟶ X :=
    pullback.snd (pullback.snd g p) (pullback.fst p f) ≫ pullback.snd p f
  have hYX : toY ≫ g = toX ≫ f := by
    dsimp [toY, toX]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, pullback.condition]
    simp only [Category.assoc]
  exact sq.lift toY toX hYX

@[reassoc (attr := simp)]
lemma brauerSeveriToBaseChange_fst :
    brauerSeveriToBaseChange sq p ≫ f' =
      pullback.fst (pullback.snd g p) (pullback.fst p f) ≫
        pullback.fst g p := by
  simp [brauerSeveriToBaseChange]

@[reassoc (attr := simp)]
lemma brauerSeveriToBaseChange_snd :
    brauerSeveriToBaseChange sq p ≫ g' =
      pullback.snd (pullback.snd g p) (pullback.fst p f) ≫
        pullback.snd p f := by
  simp [brauerSeveriToBaseChange]

lemma brauerSeveriToBaseChange_isPullback :
    IsPullback (brauerSeveriToBaseChange sq p)
      (pullback.snd (pullback.snd g p) (pullback.fst p f))
      g' (pullback.snd p f) := by
  have houter :=
    (IsPullback.of_hasPullback (pullback.snd g p) (pullback.fst p f)).paste_horiz
      (IsPullback.of_hasPullback g p)
  have houter' : IsPullback
      (brauerSeveriToBaseChange sq p ≫ f')
      (pullback.snd (pullback.snd g p) (pullback.fst p f))
      g (pullback.snd p f ≫ f) := by
    convert houter using 1
    · exact brauerSeveriToBaseChange_fst sq p
    · exact (pullback.condition : pullback.fst p f ≫ p = pullback.snd p f ≫ f).symm
  exact houter'.of_right (brauerSeveriToBaseChange_snd sq p) sq

/-- Base-changing the pullback of `g` along `p` through a pullback square for
`g` gives the same object over `T ×_S X` as pulling back the base-changed
morphism. -/
noncomputable def brauerSeveriPullbackIso :
    Over.mk (pullback.snd (pullback.snd g p) (pullback.fst p f)) ≅
      Over.mk (pullback.snd g' (pullback.snd p f)) := by
  let h := brauerSeveriToBaseChange_isPullback sq p
  let h' := IsPullback.of_hasPullback g' (pullback.snd p f)
  exact Over.isoMk (h.isoIsPullback _ _ h')
    (h.isoIsPullback_hom_snd _ _ h')

end PullbackComparison

/-- Being a Brauer--Severi morphism of fixed relative dimension is preserved by
arbitrary base change. -/
instance brauerSeveriProperty_isStableUnderBaseChange (r : ℕ) :
    (brauerSeveriProperty r).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' sq hg
  obtain ⟨T, p, hpEtale, hpSurjective, e⟩ := hg
  refine ⟨pullback p f, pullback.snd p f,
    MorphismProperty.pullback_snd p f hpEtale,
    MorphismProperty.pullback_snd p f hpSurjective, ?_⟩
  let q := pullback.fst p f
  let ebase := (Over.pullback q).mapIso e.some
  exact ⟨(brauerSeveriPullbackIso sq p).symm ≪≫ ebase ≪≫
    projectiveSpaceOverPullbackIso r q⟩

/-- The prestack of Brauer--Severi schemes of relative dimension `r`, with
cartesian squares as morphisms. -/
abbrev brauerSeveriPrestack (r : ℕ) : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty (brauerSeveriProperty r)

instance brauerSeveriPrestack_isFiberedInGroupoids (r : ℕ) :
    (brauerSeveriPrestack r).p.IsFiberedInGroupoids :=
  inferInstance

end AlgebraicGeometry.Scheme
