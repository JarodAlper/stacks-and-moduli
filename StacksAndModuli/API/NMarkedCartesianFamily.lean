module

public import StacksAndModuli.API.PointedCartesianFamily

/-!
# Cartesian families with an indexed collection of markings

This file generalizes `PointedCartesianFamily.lean` from one section to a family of
sections indexed by a type `I`.  If `P` is a pullback-stable property of arrows in a
category with pullbacks, then `markedCartesianProperty I P` is the prestack whose objects
are `P`-arrows `X ⟶ S` with sections `sᵢ : S ⟶ X`, and whose morphisms are cartesian
squares preserving every `sᵢ`.

The specialization `nMarkedCartesianProperty n P` uses `I = Fin n`.  Reindexing the
markings, forgetting all markings, and retaining one selected marking are provided as
based functors.

## Main declarations

* `CategoryTheory.MarkedCartesianObj` and `CategoryTheory.MarkedCartesianHom`;
* `CategoryTheory.markedCartesianProperty` and
  `CategoryTheory.nMarkedCartesianProperty`;
* `CategoryTheory.markedCartesianProperty.forget`, `.forgetAt`, and `.reindex`;
* the `IsFiberedInGroupoids` instance for pullback-stable `P`;
* `CategoryTheory.pullbackMarkingEquiv`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A `P`-family equipped with sections indexed by `I`. -/
structure MarkedCartesianObj (I : Type w) (P : MorphismProperty C) where
  /-- The total space of the family. -/
  left : C
  /-- The base of the family. -/
  right : C
  /-- The family map. -/
  hom : left ⟶ right
  /-- The property imposed on the family map. -/
  property : P hom
  /-- The indexed collection of sections. -/
  mark : I → (right ⟶ left)
  /-- Every marking is a section of the family map. -/
  mark_fac : ∀ i, mark i ≫ hom = 𝟙 right

/-- A cartesian square of marked families which preserves every marking. -/
@[ext]
structure MarkedCartesianHom {I : Type w} {P : MorphismProperty C}
    (a b : MarkedCartesianObj I P) where
  /-- The map on total spaces. -/
  left : a.left ⟶ b.left
  /-- The map on bases. -/
  right : a.right ⟶ b.right
  /-- The underlying square is cartesian. -/
  isPullback : IsPullback left a.hom b.hom right
  /-- Compatibility with every marking. -/
  mark_naturality : ∀ i, a.mark i ≫ left = right ≫ b.mark i

namespace MarkedCartesianHom

/-- The identity morphism of a marked family. -/
@[simps]
def id {I : Type w} {P : MorphismProperty C} (a : MarkedCartesianObj I P) :
    MarkedCartesianHom a a where
  left := 𝟙 a.left
  right := 𝟙 a.right
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
  mark_naturality := fun _ ↦ by simp

/-- Composition of morphisms of marked families. -/
@[simps]
def comp {I : Type w} {P : MorphismProperty C} {a b c : MarkedCartesianObj I P}
    (f : MarkedCartesianHom a b) (g : MarkedCartesianHom b c) :
    MarkedCartesianHom a c where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  isPullback := f.isPullback.paste_horiz g.isPullback
  mark_naturality i :=
    calc
      a.mark i ≫ (f.left ≫ g.left) = (a.mark i ≫ f.left) ≫ g.left :=
        (Category.assoc _ _ _).symm
      _ = (f.right ≫ b.mark i) ≫ g.left :=
        congrArg (fun q ↦ q ≫ g.left) (f.mark_naturality i)
      _ = f.right ≫ (b.mark i ≫ g.left) := Category.assoc _ _ _
      _ = f.right ≫ (g.right ≫ c.mark i) :=
        congrArg (fun q ↦ f.right ≫ q) (g.mark_naturality i)
      _ = (f.right ≫ g.right) ≫ c.mark i := (Category.assoc _ _ _).symm

end MarkedCartesianHom

instance {I : Type w} {P : MorphismProperty C} : Category (MarkedCartesianObj I P) where
  Hom := MarkedCartesianHom
  id := MarkedCartesianHom.id
  comp := MarkedCartesianHom.comp
  id_comp f := by ext <;> simp [MarkedCartesianHom.id, MarkedCartesianHom.comp]
  comp_id f := by ext <;> simp [MarkedCartesianHom.id, MarkedCartesianHom.comp]
  assoc f g h := by ext <;> simp [MarkedCartesianHom.comp, Category.assoc]

/-- Marked `P`-families, based over the target of the family map. -/
abbrev markedCartesianProperty (I : Type w) (P : MorphismProperty C) : BasedCategory C where
  obj := MarkedCartesianObj I P
  p :=
    { obj := fun a ↦ a.right
      map := fun {a b} f ↦ (show MarkedCartesianHom a b from f).right
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

/-- A `P`-family with `n` ordered markings. -/
abbrev NMarkedCartesianObj (n : ℕ) (P : MorphismProperty C) :=
  MarkedCartesianObj (Fin n) P

/-- A morphism of `P`-families with `n` ordered markings. -/
abbrev NMarkedCartesianHom {n : ℕ} {P : MorphismProperty C}
    (a b : NMarkedCartesianObj n P) := MarkedCartesianHom a b

/-- `P`-families with `n` ordered markings, based over the target of the family map. -/
abbrev nMarkedCartesianProperty (n : ℕ) (P : MorphismProperty C) : BasedCategory C :=
  markedCartesianProperty (Fin n) P

namespace markedCartesianProperty

variable (I : Type w) (P : MorphismProperty C)

/-- Forget all markings of a marked family. -/
def forget : BasedFunctor (markedCartesianProperty I P) (arrowCartesianProperty P) where
  obj a := ⟨ArrowCartesian.mk a.hom, a.property⟩
  map {a b} f := ObjectProperty.homMk
    { left := (show MarkedCartesianHom a b from f).left
      right := (show MarkedCartesianHom a b from f).right
      isPullback := (show MarkedCartesianHom a b from f).isPullback }
  w := rfl

/-- Retain the marking indexed by `i` and forget all the others. -/
def forgetAt (i : I) :
    BasedFunctor (markedCartesianProperty I P) (pointedCartesianProperty P) where
  obj a :=
    { left := a.left
      right := a.right
      hom := a.hom
      property := a.property
      mark := a.mark i
      mark_fac := a.mark_fac i }
  map {a b} f :=
    { left := (show MarkedCartesianHom a b from f).left
      right := (show MarkedCartesianHom a b from f).right
      isPullback := (show MarkedCartesianHom a b from f).isPullback
      mark_naturality := (show MarkedCartesianHom a b from f).mark_naturality i }
  w := rfl

/-- Reindex markings by precomposition with a map of index types. -/
def reindex {J : Type*} (φ : J → I) :
    BasedFunctor (markedCartesianProperty I P) (markedCartesianProperty J P) where
  obj a :=
    { left := a.left
      right := a.right
      hom := a.hom
      property := a.property
      mark := fun j ↦ a.mark (φ j)
      mark_fac := fun j ↦ a.mark_fac (φ j) }
  map {a b} f :=
    { left := (show MarkedCartesianHom a b from f).left
      right := (show MarkedCartesianHom a b from f).right
      isPullback := (show MarkedCartesianHom a b from f).isPullback
      mark_naturality := fun j ↦
        (show MarkedCartesianHom a b from f).mark_naturality (φ j) }
  w := rfl

/-- Pullback-stable marked families form a prestack. -/
instance [HasPullbacks C] [P.IsStableUnderBaseChange] :
    (markedCartesianProperty I P).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    change MarkedCartesianObj I P at a
    let pb : IsPullback (pullback.fst a.hom f) (pullback.snd a.hom f) a.hom f :=
      IsPullback.of_hasPullback a.hom f
    let bMark (i : I) : R ⟶ pullback a.hom f :=
      pullback.lift (f ≫ a.mark i) (𝟙 R) (by
        rw [Category.assoc, a.mark_fac i, Category.comp_id, Category.id_comp])
    have hbMark (i : I) : bMark i ≫ pullback.snd a.hom f = 𝟙 R :=
      pullback.lift_snd _ _ _
    have hbProperty : P (pullback.snd a.hom f) :=
      P.of_isPullback pb a.property
    let b : MarkedCartesianObj I P :=
      { left := pullback a.hom f
        right := R
        hom := pullback.snd a.hom f
        property := hbProperty
        mark := bMark
        mark_fac := hbMark }
    let phi : b ⟶ a :=
      { left := pullback.fst a.hom f
        right := f
        isPullback := pb
        mark_naturality := fun _ ↦ pullback.lift_fst _ _ _ }
    refine ⟨b, phi, ?_⟩
    exact Functor.IsHomLift.map (p := (markedCartesianProperty I P).p) phi
  · intro a b phi
    change MarkedCartesianObj I P at a b
    change MarkedCartesianHom a b at phi
    let _ : IsHomLift (markedCartesianProperty I P).p phi.right phi :=
      Functor.IsHomLift.map (p := (markedCartesianProperty I P).p) phi
    constructor
    intro c g psi hpsi
    change MarkedCartesianObj I P at c
    change MarkedCartesianHom c b at psi
    have hg : g ≫ phi.right = psi.right := by
      have hbase := IsHomLift.eq_of_isHomLift (markedCartesianProperty I P).p
        (g ≫ (markedCartesianProperty I P).p.map phi) psi
      exact hbase
    have hw : psi.left ≫ b.hom = (c.hom ≫ g) ≫ phi.right := by
      calc
        psi.left ≫ b.hom = c.hom ≫ psi.right := psi.isPullback.w
        _ = c.hom ≫ (g ≫ phi.right) := by rw [hg]
        _ = (c.hom ≫ g) ≫ phi.right := (Category.assoc _ _ _).symm
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
    have hchiMark (i : I) : c.mark i ≫ chiLeft = g ≫ a.mark i := by
      apply phi.isPullback.hom_ext
      · calc
          (c.mark i ≫ chiLeft) ≫ phi.left = c.mark i ≫ psi.left := by
            rw [Category.assoc, hchiLeft]
          _ = psi.right ≫ b.mark i := psi.mark_naturality i
          _ = (g ≫ phi.right) ≫ b.mark i := by rw [hg]
          _ = g ≫ (phi.right ≫ b.mark i) := Category.assoc _ _ _
          _ = g ≫ (a.mark i ≫ phi.left) := by rw [phi.mark_naturality i]
          _ = (g ≫ a.mark i) ≫ phi.left := (Category.assoc _ _ _).symm
      · calc
          (c.mark i ≫ chiLeft) ≫ a.hom = c.mark i ≫ (c.hom ≫ g) := by
            rw [Category.assoc, hchiRight]
          _ = (c.mark i ≫ c.hom) ≫ g := (Category.assoc _ _ _).symm
          _ = g := by rw [c.mark_fac i, Category.id_comp]
          _ = g ≫ 𝟙 a.right := (Category.comp_id _).symm
          _ = g ≫ (a.mark i ≫ a.hom) := by rw [a.mark_fac i]
          _ = (g ≫ a.mark i) ≫ a.hom := (Category.assoc _ _ _).symm
    let chi : c ⟶ a :=
      { left := chiLeft
        right := g
        isPullback := hchiPb
        mark_naturality := hchiMark }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · exact Functor.IsHomLift.map (p := (markedCartesianProperty I P).p) chi
    · apply MarkedCartesianHom.ext
      · exact hchiLeft
      · exact hg
    · intro chi' hchi'
      change MarkedCartesianHom c a at chi'
      let _ : IsHomLift (markedCartesianProperty I P).p g chi' := hchi'.1
      apply MarkedCartesianHom.ext
      · apply phi.isPullback.hom_ext
        · have h := congrArg (fun q ↦ (show MarkedCartesianHom c b from q).left) hchi'.2
          exact h.trans hchiLeft.symm
        · rw [chi'.isPullback.w]
          have hright : chi'.right = g :=
            (IsHomLift.eq_of_isHomLift (markedCartesianProperty I P).p g chi').symm
          rw [hright, hchiRight]
      · exact (IsHomLift.eq_of_isHomLift (markedCartesianProperty I P).p g chi').symm

end markedCartesianProperty

section PullbackMarkings

variable [HasPullbacks C] {X S T : C} (I : Type w) (f : X ⟶ S) (g : T ⟶ S)

/-- Indexed sections of a pullback family are equivalently indexed lifts of the base map
through the original family. -/
noncomputable def pullbackMarkingEquiv :
    (I → PullbackSection f g) ≃ (I → LiftOver f g) :=
  Equiv.piCongrRight fun _ ↦ pullbackSectionEquiv f g

end PullbackMarkings

end CategoryTheory
