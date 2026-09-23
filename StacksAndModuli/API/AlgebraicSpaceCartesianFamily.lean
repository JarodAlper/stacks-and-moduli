module

public import StacksAndModuli.API.AlgebraicSpaceMarkedFamilies

/-!
# Cartesian families with algebraic-space total space

This file packages unpointed algebraic-space families whose base scheme is part of the
object.  An arbitrary dependent predicate can be imposed on the family, while morphisms
remain cartesian squares of presheaves over morphisms of base schemes.  This separates
the reusable categorical construction from book-facing predicates such as “stable of
genus `g`”.

The construction is a based category for an arbitrary predicate.  It is fibered in
groupoids as soon as the chosen family predicate is preserved by arbitrary base change,
which is the one geometric input; that input belongs with the predicate.  The base change
of a family is formed as a pullback of functors of points, which exists because presheaves
have all limits and algebraic spaces are stable under base change.

## Main declarations

* `AlgebraicGeometry.UnpointedAlgebraicSpaceFamilyProperty`;
* `AlgebraicGeometry.UnpointedAlgebraicSpaceCartesianObj`;
* `AlgebraicGeometry.UnpointedAlgebraicSpaceCartesianHom`;
* `AlgebraicGeometry.moduliOfAllCurves`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.unpointedBaseChange`;
* `AlgebraicGeometry.UnpointedAlgebraicSpaceFamilyProperty.StableUnderBaseChange`;
* `AlgebraicGeometry.isFiberedInGroupoids_moduliOfAllCurves`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A property of an unpointed algebraic-space family over a varying base scheme. -/
abbrev UnpointedAlgebraicSpaceFamilyProperty : Type (u + 1) :=
  (S : Scheme.{u}) → MarkedAlgebraicSpaceOver (Fin 0) S → Prop

/-- An unpointed algebraic-space family satisfying `Q`, with its base included as data. -/
structure UnpointedAlgebraicSpaceCartesianObj
    (Q : UnpointedAlgebraicSpaceFamilyProperty.{u}) where
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The algebraic-space family over `base`. -/
  family : MarkedAlgebraicSpaceOver (Fin 0) base
  /-- The property imposed on the family. -/
  property : Q base family

/-- A morphism of unpointed algebraic-space families is a cartesian square of their
functors of points over a morphism of base schemes.

There is no marking-compatibility field: a family indexed by `Fin 0` has no markings. -/
@[ext]
structure UnpointedAlgebraicSpaceCartesianHom
    {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}}
    (A B : UnpointedAlgebraicSpaceCartesianObj Q) where
  /-- The natural transformation on total algebraic spaces. -/
  total : A.family.total ⟶ B.family.total
  /-- The morphism on base schemes. -/
  base : A.base ⟶ B.base
  /-- The resulting square of presheaves is cartesian. -/
  isPullback :
    IsPullback total A.family.hom B.family.hom (yoneda.map base)

namespace UnpointedAlgebraicSpaceCartesianHom

/-- The identity cartesian morphism of an unpointed algebraic-space family. -/
@[simps]
def id {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}}
    (A : UnpointedAlgebraicSpaceCartesianObj Q) :
    UnpointedAlgebraicSpaceCartesianHom A A where
  total := 𝟙 A.family.total
  base := 𝟙 A.base
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Composition of cartesian morphisms of unpointed algebraic-space families. -/
@[simps]
def comp {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}}
    {A B C : UnpointedAlgebraicSpaceCartesianObj Q}
    (f : UnpointedAlgebraicSpaceCartesianHom A B)
    (g : UnpointedAlgebraicSpaceCartesianHom B C) :
    UnpointedAlgebraicSpaceCartesianHom A C where
  total := f.total ≫ g.total
  base := f.base ≫ g.base
  isPullback := by
    simpa using f.isPullback.paste_horiz g.isPullback

end UnpointedAlgebraicSpaceCartesianHom

instance (Q : UnpointedAlgebraicSpaceFamilyProperty.{u}) :
    Category (UnpointedAlgebraicSpaceCartesianObj Q) where
  Hom := UnpointedAlgebraicSpaceCartesianHom
  id := UnpointedAlgebraicSpaceCartesianHom.id
  comp := UnpointedAlgebraicSpaceCartesianHom.comp
  id_comp f := by
    apply UnpointedAlgebraicSpaceCartesianHom.ext <;>
      simp [UnpointedAlgebraicSpaceCartesianHom.id,
        UnpointedAlgebraicSpaceCartesianHom.comp]
  comp_id f := by
    apply UnpointedAlgebraicSpaceCartesianHom.ext <;>
      simp [UnpointedAlgebraicSpaceCartesianHom.id,
        UnpointedAlgebraicSpaceCartesianHom.comp]
  assoc f g h := by
    apply UnpointedAlgebraicSpaceCartesianHom.ext <;>
      simp [UnpointedAlgebraicSpaceCartesianHom.comp, Category.assoc]

/-- Unpointed algebraic-space families satisfying `Q`, based over their base schemes.

This is the categorical input to a prestack.  An `IsFiberedInGroupoids` instance can be
added once `Q` is known to be preserved by arbitrary base change. -/
def moduliOfAllCurves
    (Q : UnpointedAlgebraicSpaceFamilyProperty.{u}) : BasedCategory Scheme.{u} where
  obj := UnpointedAlgebraicSpaceCartesianObj Q
  p :=
    { obj := UnpointedAlgebraicSpaceCartesianObj.base
      map := fun {A B} f ↦
        (show UnpointedAlgebraicSpaceCartesianHom A B from f).base
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

/-- The base change of an unpointed algebraic-space family along a morphism of base
schemes, formed as the pullback of functors of points. -/
def MarkedAlgebraicSpaceOver.unpointedBaseChange {S T : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) :
    MarkedAlgebraicSpaceOver (Fin 0) T where
  total := Limits.pullback F.hom (yoneda.map f)
  isAlgebraicSpace := IsAlgebraicSpace.pullback F.hom (yoneda.map f)
  hom := Limits.pullback.snd F.hom (yoneda.map f)
  mark i := i.elim0
  mark_fac i := i.elim0

/-- The defining square of a base change is cartesian. -/
theorem MarkedAlgebraicSpaceOver.isPullback_unpointedBaseChange {S T : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) :
    IsPullback (Limits.pullback.fst F.hom (yoneda.map f))
      (F.unpointedBaseChange f).hom F.hom (yoneda.map f) :=
  (IsPullback.of_hasPullback F.hom (yoneda.map f)).flip.flip

/-- A family property is *stable under base change* if it is inherited by the pullback of
a family along every morphism of base schemes.  This is the geometric input that makes the
cartesian-family construction fibered in groupoids. -/
def UnpointedAlgebraicSpaceFamilyProperty.StableUnderBaseChange
    (Q : UnpointedAlgebraicSpaceFamilyProperty.{u}) : Prop :=
  ∀ {S T : Scheme.{u}} (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S),
    Q S F → Q T (F.unpointedBaseChange f)

/-- API lemma: base change of a cartesian-family object along a morphism of base schemes. -/
def UnpointedAlgebraicSpaceCartesianObj.baseChange
    {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}} (hQ : Q.StableUnderBaseChange)
    (A : UnpointedAlgebraicSpaceCartesianObj Q) {T : Scheme.{u}} (f : T ⟶ A.base) :
    UnpointedAlgebraicSpaceCartesianObj Q where
  base := T
  family := A.family.unpointedBaseChange f
  property := hQ A.family f A.property

/-- API lemma: the cartesian morphism from a base change to the original family. -/
def UnpointedAlgebraicSpaceCartesianObj.baseChangeHom
    {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}} (hQ : Q.StableUnderBaseChange)
    (A : UnpointedAlgebraicSpaceCartesianObj Q) {T : Scheme.{u}} (f : T ⟶ A.base) :
    UnpointedAlgebraicSpaceCartesianHom (A.baseChange hQ f) A where
  total := Limits.pullback.fst A.family.hom (yoneda.map f)
  base := f
  isPullback := A.family.isPullback_unpointedBaseChange f

/-- If the family property is stable under base change, then the category of cartesian
families is fibered in groupoids over schemes: base change supplies the cartesian lifts,
and every morphism is cartesian because its defining square is. -/
theorem isFiberedInGroupoids_moduliOfAllCurves
    {Q : UnpointedAlgebraicSpaceFamilyProperty.{u}} (hQ : Q.StableUnderBaseChange) :
    (moduliOfAllCurves Q).p.IsFiberedInGroupoids := by
  constructor
  · intro A R f
    refine ⟨A.baseChange hQ f, A.baseChangeHom hQ f, ?_⟩
    exact IsHomLift.map (moduliOfAllCurves Q).p
      (A.baseChangeHom hQ f)
  · intro A B φ
    constructor
    intro Z g ψ hψ
    have hg : g ≫ φ.base = ψ.base :=
      IsHomLift.eq_of_isHomLift (moduliOfAllCurves Q).p
        (g ≫ (moduliOfAllCurves Q).p.map φ) ψ
    have hw : ψ.total ≫ B.family.hom =
        (Z.family.hom ≫ yoneda.map g) ≫ yoneda.map φ.base := by
      rw [Category.assoc, ← Functor.map_comp, hg]
      exact ψ.isPullback.w
    let χtotal : Z.family.total ⟶ A.family.total :=
      φ.isPullback.lift ψ.total (Z.family.hom ≫ yoneda.map g) hw
    have hχfst : χtotal ≫ φ.total = ψ.total := φ.isPullback.lift_fst _ _ hw
    have hχsnd : χtotal ≫ A.family.hom = Z.family.hom ≫ yoneda.map g :=
      φ.isPullback.lift_snd _ _ hw
    have hout : IsPullback (χtotal ≫ φ.total) Z.family.hom B.family.hom
        (yoneda.map g ≫ yoneda.map φ.base) := by
      rw [hχfst, ← Functor.map_comp, hg]
      exact ψ.isPullback
    have hχpb : IsPullback χtotal Z.family.hom A.family.hom (yoneda.map g) :=
      hout.of_right hχsnd φ.isPullback
    let χ : Z ⟶ A :=
      { total := χtotal
        base := g
        isPullback := hχpb }
    have hχbase : (moduliOfAllCurves Q).p.map χ = g := rfl
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · rw [← hχbase]
      infer_instance
    · apply UnpointedAlgebraicSpaceCartesianHom.ext
      · exact hχfst
      · exact hg
    · intro χ' hχ'
      obtain ⟨hχ'lift, hχ'fac⟩ := hχ'
      have hright : χ'.base = g :=
        (IsHomLift.eq_of_isHomLift (moduliOfAllCurves Q).p g χ').symm
      apply UnpointedAlgebraicSpaceCartesianHom.ext
      · apply φ.isPullback.hom_ext
        · have h := congrArg UnpointedAlgebraicSpaceCartesianHom.total hχ'fac
          change χ'.total ≫ φ.total = ψ.total at h
          exact h.trans hχfst.symm
        · have h : χ'.total ≫ A.family.hom = Z.family.hom ≫ yoneda.map g := by
            rw [χ'.isPullback.w, hright]
          exact h.trans hχsnd.symm
      · exact hright

@[simp]
lemma moduliOfAllCurves_p_obj
    (Q : UnpointedAlgebraicSpaceFamilyProperty.{u})
    (A : (moduliOfAllCurves Q).obj) :
    (moduliOfAllCurves Q).p.obj A = A.base :=
  rfl

@[simp]
lemma moduliOfAllCurves_p_map
    (Q : UnpointedAlgebraicSpaceFamilyProperty.{u})
    {A B : (moduliOfAllCurves Q).obj} (f : A ⟶ B) :
    (moduliOfAllCurves Q).p.map f =
      (show UnpointedAlgebraicSpaceCartesianHom A B from f).base :=
  rfl

end AlgebraicGeometry
