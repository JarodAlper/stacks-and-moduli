module

public import StacksAndModuli.API.ArrowCartesianProperty

/-!
# Pointed cartesian families

This file packages families equipped with a section.  If `P` is a pullback-stable
property of arrows in a category with pullbacks, then `pointedCartesianProperty P`
is the prestack whose objects are `P`-arrows `X ⟶ S` together with a section
`S ⟶ X`, and whose morphisms are cartesian squares preserving the sections.

The elementary equivalence `pullbackSectionEquiv` is the objectwise core of the
universal-family square: sections of `X ×_S T ⟶ T` are the same as lifts
`T ⟶ X` of a fixed map `T ⟶ S`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A `P`-family equipped with a section. -/
structure PointedCartesianObj (P : MorphismProperty C) where
  /-- The total space of the family. -/
  left : C
  /-- The base of the family. -/
  right : C
  /-- The family map. -/
  hom : left ⟶ right
  /-- The property imposed on the family map. -/
  property : P hom
  /-- The chosen section of the family. -/
  mark : right ⟶ left
  /-- The chosen map is a section. -/
  mark_fac : mark ≫ hom = 𝟙 right

/-- A cartesian square of families which preserves their chosen sections. -/
@[ext]
structure PointedCartesianHom {P : MorphismProperty C}
    (a b : PointedCartesianObj P) where
  /-- The map on total spaces. -/
  left : a.left ⟶ b.left
  /-- The map on bases. -/
  right : a.right ⟶ b.right
  /-- The underlying square is cartesian. -/
  isPullback : IsPullback left a.hom b.hom right
  /-- Compatibility with the chosen sections. -/
  mark_naturality : a.mark ≫ left = right ≫ b.mark

namespace PointedCartesianHom

/-- The identity morphism of a pointed family. -/
@[simps]
def id {P : MorphismProperty C} (a : PointedCartesianObj P) :
    PointedCartesianHom a a where
  left := 𝟙 a.left
  right := 𝟙 a.right
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
  mark_naturality := by simp

/-- Composition of morphisms of pointed families. -/
@[simps]
def comp {P : MorphismProperty C} {a b c : PointedCartesianObj P}
    (f : PointedCartesianHom a b) (g : PointedCartesianHom b c) :
    PointedCartesianHom a c where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  isPullback := f.isPullback.paste_horiz g.isPullback
  mark_naturality :=
    calc
      a.mark ≫ (f.left ≫ g.left) = (a.mark ≫ f.left) ≫ g.left :=
        (Category.assoc _ _ _).symm
      _ =
          (f.right ≫ b.mark) ≫ g.left :=
        congrArg (fun q ↦ q ≫ g.left) f.mark_naturality
      _ = f.right ≫ (b.mark ≫ g.left) := Category.assoc _ _ _
      _ = f.right ≫ (g.right ≫ c.mark) :=
        congrArg (fun q ↦ f.right ≫ q) g.mark_naturality
      _ = (f.right ≫ g.right) ≫ c.mark := (Category.assoc _ _ _).symm

end PointedCartesianHom

instance {P : MorphismProperty C} : Category (PointedCartesianObj P) where
  Hom := PointedCartesianHom
  id := PointedCartesianHom.id
  comp := PointedCartesianHom.comp
  id_comp f := by ext <;> simp [PointedCartesianHom.id, PointedCartesianHom.comp]
  comp_id f := by ext <;> simp [PointedCartesianHom.id, PointedCartesianHom.comp]
  assoc f g h := by ext <;> simp [PointedCartesianHom.comp, Category.assoc]

/-- Pointed `P`-families, based over the target of the family map. -/
abbrev pointedCartesianProperty (P : MorphismProperty C) : BasedCategory C where
  obj := PointedCartesianObj P
  p :=
    { obj := fun a ↦ a.right
      map := fun {a b} f ↦ (show PointedCartesianHom a b from f).right
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

namespace pointedCartesianProperty

variable (P : MorphismProperty C)

/-- Forget the section of a pointed family. -/
def forget : BasedFunctor (pointedCartesianProperty P) (arrowCartesianProperty P) where
  obj a := ⟨ArrowCartesian.mk a.hom, a.property⟩
  map {a b} f := ObjectProperty.homMk
    { left := (show PointedCartesianHom a b from f).left
      right := (show PointedCartesianHom a b from f).right
      isPullback := (show PointedCartesianHom a b from f).isPullback }
  w := rfl

/-- Pullback-stable pointed families form a prestack. -/
instance [HasPullbacks C] [P.IsStableUnderBaseChange] :
    (pointedCartesianProperty P).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    change PointedCartesianObj P at a
    let pb : IsPullback (pullback.fst a.hom f) (pullback.snd a.hom f) a.hom f :=
      IsPullback.of_hasPullback a.hom f
    let bSection : R ⟶ pullback a.hom f :=
      pullback.lift (f ≫ a.mark) (𝟙 R) (by
        rw [Category.assoc, a.mark_fac, Category.comp_id, Category.id_comp])
    have hbSection : bSection ≫ pullback.snd a.hom f = 𝟙 R := by
      exact pullback.lift_snd _ _ _
    have hbProperty : P (pullback.snd a.hom f) :=
      P.of_isPullback pb a.property
    let b : PointedCartesianObj P :=
      { left := pullback a.hom f
        right := R
        hom := pullback.snd a.hom f
        property := hbProperty
        mark := bSection
        mark_fac := hbSection }
    let phi : b ⟶ a :=
      { left := pullback.fst a.hom f
        right := f
        isPullback := pb
        mark_naturality := pullback.lift_fst _ _ _ }
    refine ⟨b, phi, ?_⟩
    exact Functor.IsHomLift.map (p := (pointedCartesianProperty P).p) phi
  · intro a b phi
    change PointedCartesianObj P at a b
    change PointedCartesianHom a b at phi
    letI : IsHomLift (pointedCartesianProperty P).p phi.right phi :=
      Functor.IsHomLift.map (p := (pointedCartesianProperty P).p) phi
    constructor
    intro c g psi hpsi
    change PointedCartesianObj P at c
    change PointedCartesianHom c b at psi
    have hg : g ≫ phi.right = psi.right := by
      have hbase := IsHomLift.eq_of_isHomLift (pointedCartesianProperty P).p
        (g ≫ (pointedCartesianProperty P).p.map phi) psi
      exact hbase
    have hw : psi.left ≫ b.hom = (c.hom ≫ g) ≫ phi.right := by
      calc
        psi.left ≫ b.hom = c.hom ≫ psi.right := psi.isPullback.w
        _ = c.hom ≫ (g ≫ phi.right) := by rw [hg]
        _ = (c.hom ≫ g) ≫ phi.right :=
          (Category.assoc _ _ _).symm
    let chiLeft : c.left ⟶ a.left :=
      phi.isPullback.lift psi.left (c.hom ≫ g) hw
    have hchiLeft : chiLeft ≫ phi.left = psi.left :=
      phi.isPullback.lift_fst _ _ _
    have hchiRight : chiLeft ≫ a.hom = c.hom ≫ g :=
      phi.isPullback.lift_snd _ _ _
    have hchiPb : IsPullback chiLeft c.hom a.hom g := by
      have hout : IsPullback (chiLeft ≫ phi.left) c.hom b.hom
          (g ≫ phi.right) := by
        simpa only [hchiLeft, hg] using psi.isPullback
      exact hout.of_right hchiRight phi.isPullback
    have hchiSection : c.mark ≫ chiLeft = g ≫ a.mark := by
      apply phi.isPullback.hom_ext
      · calc
          (c.mark ≫ chiLeft) ≫ phi.left = c.mark ≫ psi.left := by
            rw [Category.assoc, hchiLeft]
          _ = psi.right ≫ b.mark := psi.mark_naturality
          _ = (g ≫ phi.right) ≫ b.mark := by rw [hg]
          _ = g ≫ (phi.right ≫ b.mark) := Category.assoc _ _ _
          _ = g ≫ (a.mark ≫ phi.left) := by rw [phi.mark_naturality]
          _ = (g ≫ a.mark) ≫ phi.left := (Category.assoc _ _ _).symm
      · calc
          (c.mark ≫ chiLeft) ≫ a.hom = c.mark ≫ (c.hom ≫ g) := by
            rw [Category.assoc, hchiRight]
          _ = (c.mark ≫ c.hom) ≫ g := (Category.assoc _ _ _).symm
          _ = g := by rw [c.mark_fac, Category.id_comp]
          _ = g ≫ 𝟙 a.right := (Category.comp_id _).symm
          _ = g ≫ (a.mark ≫ a.hom) := by rw [a.mark_fac]
          _ = (g ≫ a.mark) ≫ a.hom := (Category.assoc _ _ _).symm
    let chi : c ⟶ a :=
      { left := chiLeft
        right := g
        isPullback := hchiPb
        mark_naturality := hchiSection }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · exact Functor.IsHomLift.map (p := (pointedCartesianProperty P).p) chi
    · apply PointedCartesianHom.ext
      · exact hchiLeft
      · exact hg
    · intro chi' hchi'
      change PointedCartesianHom c a at chi'
      letI : IsHomLift (pointedCartesianProperty P).p g chi' := hchi'.1
      apply PointedCartesianHom.ext
      · apply phi.isPullback.hom_ext
        · have h := congrArg (fun q ↦ (show PointedCartesianHom c b from q).left) hchi'.2
          exact h.trans hchiLeft.symm
        · rw [chi'.isPullback.w]
          have hright : chi'.right = g :=
            (IsHomLift.eq_of_isHomLift (pointedCartesianProperty P).p g chi').symm
          rw [hright, hchiRight]
      · exact (IsHomLift.eq_of_isHomLift (pointedCartesianProperty P).p g chi').symm

end pointedCartesianProperty

section PullbackSections

variable [HasPullbacks C] {X S T : C} (f : X ⟶ S) (g : T ⟶ S)

/-- Sections of the pullback of `f` along `g`. -/
abbrev PullbackSection :=
  { s : T ⟶ pullback f g // s ≫ pullback.snd f g = 𝟙 T }

/-- Lifts of `g` through `f`. -/
abbrev LiftOver := { h : T ⟶ X // h ≫ f = g }

/-- A section of `X ×_S T ⟶ T` is equivalently a lift `T ⟶ X` of
`g : T ⟶ S`. -/
noncomputable def pullbackSectionEquiv : PullbackSection f g ≃ LiftOver f g where
  toFun s :=
    ⟨s.1 ≫ pullback.fst f g, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, s.2,
        Category.id_comp]⟩
  invFun h :=
    ⟨pullback.lift h.1 (𝟙 T) (by simpa using h.2), pullback.lift_snd _ _ _⟩
  left_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd, s.2]
  right_inv h := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

end PullbackSections

end CategoryTheory
