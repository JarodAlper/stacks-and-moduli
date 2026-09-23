module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import StacksAndModuli.API.PointedCartesianFamily
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Elliptic curves as one-dimensional abelian schemes

An elliptic curve over a scheme can equivalently be described as a smooth,
proper, geometrically connected commutative group scheme of relative dimension
one.  This file packages that description and its stability under arbitrary
base change.  The unit of the group object is the marked section.

The book instead starts with a pointed smooth proper family whose geometric
fibers have genus one.  Showing that the marked point induces the unique group
law is a genuine geometric theorem and is not asserted here without proof; the
explicit name `EllipticGroupFamily` keeps the two descriptions distinct until
that comparison is formalized.

Main declarations:

* `AlgebraicGeometry.Scheme.EllipticGroupFamily`;
* `EllipticGroupFamily.zeroSection`;
* `EllipticGroupFamily.toPointedSmoothCurve`;
* `EllipticGroupFamily.pullback`;
* `AlgebraicGeometry.Scheme.ellipticGroupPrestack`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

universe u

namespace AlgebraicGeometry.Scheme

/-- A smooth, proper, geometrically connected commutative group scheme of
relative dimension one over `S`.  This is the group-scheme description of a
family of elliptic curves. -/
structure EllipticGroupFamily (S : Scheme.{u}) where
  curve : CommGrp (Over S)
  smooth : SmoothOfRelativeDimension 1 curve.X.hom
  proper : IsProper curve.X.hom
  geometricallyConnected : GeometricallyConnected curve.X.hom

namespace EllipticGroupFamily

variable {S T : Scheme.{u}} (E : EllipticGroupFamily S)

/-- The total space of an elliptic group family. -/
abbrev total : Scheme.{u} := E.curve.X.left

/-- The structure morphism of an elliptic group family. -/
abbrev π : E.total ⟶ S := E.curve.X.hom

/-- The unit of the group scheme, viewed as the marked section. -/
noncomputable def zeroSection : S ⟶ E.total :=
  (η[E.curve.X]).left

@[reassoc (attr := simp)]
lemma zeroSection_comp_π : E.zeroSection ≫ E.π = 𝟙 S :=
  (η[E.curve.X]).w

/-- An elliptic group family, regarded as a pointed smooth-curve family by
forgetting its group operations and retaining the unit section. -/
noncomputable def toPointedSmoothCurve :
    PointedCartesianObj smoothCurveProperty.{u} where
  left := E.total
  right := S
  hom := E.π
  property := ⟨E.smooth, E.proper, E.geometricallyConnected⟩
  mark := E.zeroSection
  mark_fac := E.zeroSection_comp_π

/-- Pullback of an elliptic group family along an arbitrary morphism of bases. -/
noncomputable def pullback (f : T ⟶ S) : EllipticGroupFamily T where
  curve := (Over.pullback f).mapCommGrp.obj E.curve
  smooth := by
    change SmoothOfRelativeDimension 1 (pullback.snd E.π f)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback E.π f) E.smooth
  proper := by
    change IsProper (pullback.snd E.π f)
    exact MorphismProperty.pullback_snd E.π f E.proper
  geometricallyConnected := by
    change GeometricallyConnected (pullback.snd E.π f)
    exact MorphismProperty.pullback_snd E.π f E.geometricallyConnected

/-- The unit section of a pulled-back elliptic group family is the pullback of
the original unit section. -/
lemma pullback_zeroSection_fst (f : T ⟶ S) :
    (E.pullback f).zeroSection ≫ pullback.fst E.π f =
      f ≫ E.zeroSection := by
  change (η[((Over.pullback f).mapCommGrp.obj E.curve).X]).left ≫
    pullback.fst E.π f = f ≫ (η[E.curve.X]).left
  dsimp only [Functor.mapCommGrp, Functor.mapGrp, Functor.mapMon]
  have hη : η[((Over.pullback f).mapCommGrp.obj E.curve).X] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫
        (Over.pullback f).map η[E.curve.X] := rfl
  rw [hη]
  have hmap := Over.pullback_map_left f (𝟙_ (Over S))
    (k := η[E.curve.X])
  have hinner :
      Over.Hom.left ((Over.pullback f).map η[E.curve.X]) ≫
          pullback.fst E.π f =
        pullback.fst (𝟙 S) f ≫ (η[E.curve.X]).left := by
    calc
      _ = pullback.lift
          (pullback.fst (𝟙 S) f ≫ (η[E.curve.X]).left)
          (pullback.snd (𝟙 S) f) (by
            rw [Category.assoc, (η[E.curve.X]).w]
            change pullback.fst (𝟙 S) f ≫ 𝟙 S =
              pullback.snd (𝟙 S) f ≫ f
            exact pullback.condition) ≫ pullback.fst E.π f :=
        congrArg (fun q ↦ q ≫ pullback.fst E.π f) hmap
      _ = _ := pullback.lift_fst _ _ _
  calc
    Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback f) ≫
        (Over.pullback f).map η[E.curve.X]) ≫ pullback.fst E.π f =
      Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback f)) ≫
        Over.Hom.left ((Over.pullback f).map η[E.curve.X]) ≫
          pullback.fst E.π f := by rw [Over.comp_left_assoc]
    _ = Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback f)) ≫
        (pullback.fst (𝟙 S) f ≫ (η[E.curve.X]).left) := by
      rw [hinner]
    _ = f ≫ (η[E.curve.X]).left := by
      have hfst : pullback.fst (𝟙 S) f =
          pullback.snd (𝟙 S) f ≫ f := by
        simpa using (pullback.condition :
          pullback.fst (𝟙 S) f ≫ 𝟙 S = pullback.snd (𝟙 S) f ≫ f)
      rw [Over.ε_pullback_left, hfst, ← Category.assoc,
        IsIso.inv_hom_id_assoc]

/-- Pullback of elliptic group families gives the canonical cartesian arrow of
their underlying pointed smooth-curve families. -/
noncomputable def pullbackToPointedSmoothCurve (f : T ⟶ S) :
    (E.pullback f).toPointedSmoothCurve ⟶ E.toPointedSmoothCurve where
  left := pullback.fst E.π f
  right := f
  isPullback := IsPullback.of_hasPullback E.π f
  mark_naturality := E.pullback_zeroSection_fst f

end EllipticGroupFamily

/-- A group-structured elliptic family with its base included as data. -/
structure EllipticGroupObj where
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The elliptic group family over the base. -/
  family : EllipticGroupFamily base

namespace EllipticGroupObj

/-- Morphisms of group-structured elliptic families are cartesian morphisms of
the underlying pointed smooth curves.  This is the book's notion of morphism;
the group operations are auxiliary structure on the objects. -/
abbrev Hom (A B : EllipticGroupObj.{u}) :=
  PointedCartesianHom A.family.toPointedSmoothCurve
    B.family.toPointedSmoothCurve

noncomputable instance : Category EllipticGroupObj.{u} where
  Hom := Hom
  id A := PointedCartesianHom.id A.family.toPointedSmoothCurve
  comp f g := PointedCartesianHom.comp f g
  id_comp f := by
    apply PointedCartesianHom.ext <;>
      simp [PointedCartesianHom.id, PointedCartesianHom.comp]
  comp_id f := by
    apply PointedCartesianHom.ext <;>
      simp [PointedCartesianHom.id, PointedCartesianHom.comp]
  assoc f g h := by
    apply PointedCartesianHom.ext <;>
      simp [PointedCartesianHom.comp, Category.assoc]

end EllipticGroupObj

/-- The prestack candidate whose objects are elliptic curves in the
commutative-group-scheme model and whose arrows are cartesian pointed arrows. -/
noncomputable def ellipticGroupPrestack : BasedCategory Scheme.{u} where
  obj := EllipticGroupObj.{u}
  p :=
    { obj := EllipticGroupObj.base
      map := fun {A B} f ↦
        (show EllipticGroupObj.Hom A B from f).right
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

/-- Forget the commutative group operations while retaining the pointed smooth
curve family. -/
noncomputable def ellipticGroupPrestackForget :
    BasedFunctor ellipticGroupPrestack
      (CategoryTheory.pointedCartesianProperty smoothCurveProperty.{u}) where
  obj A := A.family.toPointedSmoothCurve
  map f := f
  w := rfl

instance ellipticGroupPrestackForget_faithful :
    ellipticGroupPrestackForget.{u}.Faithful where
  map_injective h := h

instance ellipticGroupPrestackForget_full :
    ellipticGroupPrestackForget.{u}.Full where
  map_surjective f := ⟨f, rfl⟩

/-- Group-structured elliptic families and cartesian pointed arrows form a
category fibered in groupoids over schemes. -/
instance ellipticGroupPrestack_isFiberedInGroupoids :
    ellipticGroupPrestack.{u}.p.IsFiberedInGroupoids := by
  constructor
  · intro A R f
    change EllipticGroupObj at A
    let B : EllipticGroupObj.{u} :=
      ⟨R, A.family.pullback f⟩
    let phi : B ⟶ A := A.family.pullbackToPointedSmoothCurve f
    refine ⟨B, phi, ?_⟩
    exact Functor.IsHomLift.map (p := ellipticGroupPrestack.p) phi
  · intro A B phi
    change EllipticGroupObj at A B
    change EllipticGroupObj.Hom A B at phi
    constructor
    intro C g psi hpsi
    change EllipticGroupObj at C
    change C.base ⟶ A.base at g
    change EllipticGroupObj.Hom C B at psi
    have hg : g ≫ phi.right = psi.right := by
      have hbase := IsHomLift.eq_of_isHomLift ellipticGroupPrestack.p
        (g ≫ ellipticGroupPrestack.p.map phi) psi
      exact hbase
    have hw : psi.left ≫ B.family.π =
        (C.family.π ≫ g) ≫ phi.right := by
      calc
        psi.left ≫ B.family.π = C.family.π ≫ psi.right :=
          psi.isPullback.w
        _ = C.family.π ≫ (g ≫ phi.right) := by rw [hg]
        _ = (C.family.π ≫ g) ≫ phi.right :=
          (Category.assoc _ _ _).symm
    let chiLeft : C.family.total ⟶ A.family.total :=
      phi.isPullback.lift psi.left (C.family.π ≫ g) hw
    have hchiLeft : chiLeft ≫ phi.left = psi.left :=
      phi.isPullback.lift_fst _ _ _
    have hchiRight : chiLeft ≫ A.family.π = C.family.π ≫ g :=
      phi.isPullback.lift_snd _ _ _
    have hchiPb : IsPullback chiLeft C.family.π A.family.π g := by
      have hpsiPb : IsPullback psi.left C.family.π B.family.π
          psi.right := psi.isPullback
      have hout : IsPullback (chiLeft ≫ phi.left) C.family.π
          B.family.π (g ≫ phi.right) := by
        simpa only [hchiLeft, hg] using hpsiPb
      exact hout.of_right hchiRight phi.isPullback
    have hchiSection : C.family.zeroSection ≫ chiLeft =
        g ≫ A.family.zeroSection := by
      have hphiMark : A.family.zeroSection ≫ phi.left =
          phi.right ≫ B.family.zeroSection := phi.mark_naturality
      apply phi.isPullback.hom_ext
      · calc
          (C.family.zeroSection ≫ chiLeft) ≫ phi.left =
              C.family.zeroSection ≫ psi.left := by
            rw [Category.assoc, hchiLeft]
          _ = psi.right ≫ B.family.zeroSection :=
            psi.mark_naturality
          _ = (g ≫ phi.right) ≫ B.family.zeroSection := by rw [hg]
          _ = g ≫ (phi.right ≫ B.family.zeroSection) :=
            Category.assoc _ _ _
          _ = g ≫ (A.family.zeroSection ≫ phi.left) :=
            congrArg (fun q ↦ g ≫ q) hphiMark.symm
          _ = (g ≫ A.family.zeroSection) ≫ phi.left :=
            (Category.assoc _ _ _).symm
      · calc
          (C.family.zeroSection ≫ chiLeft) ≫ A.family.π =
              C.family.zeroSection ≫ (C.family.π ≫ g) := by
            rw [Category.assoc, hchiRight]
          _ = (C.family.zeroSection ≫ C.family.π) ≫ g :=
            (Category.assoc _ _ _).symm
          _ = g := by rw [C.family.zeroSection_comp_π, Category.id_comp]
          _ = g ≫ 𝟙 A.base := (Category.comp_id _).symm
          _ = g ≫ (A.family.zeroSection ≫ A.family.π) := by
            rw [A.family.zeroSection_comp_π]
          _ = (g ≫ A.family.zeroSection) ≫ A.family.π :=
            (Category.assoc _ _ _).symm
    let chi : C ⟶ A :=
      { left := chiLeft
        right := g
        isPullback := hchiPb
        mark_naturality := hchiSection }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · exact Functor.IsHomLift.map (p := ellipticGroupPrestack.p) chi
    · apply PointedCartesianHom.ext
      · exact hchiLeft
      · exact hg
    · intro chi' hchi'
      change EllipticGroupObj.Hom C A at chi'
      have hbase : g = ellipticGroupPrestack.p.map chi' :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift
          Scheme EllipticGroupObj inferInstance inferInstance
          ellipticGroupPrestack.p C A g chi' hchi'.1
      apply PointedCartesianHom.ext
      · apply phi.isPullback.hom_ext
        · have h := congrArg
            (fun q ↦ (show EllipticGroupObj.Hom C B from q).left) hchi'.2
          exact h.trans hchiLeft.symm
        · rw [chi'.isPullback.w]
          have hright : chi'.right = g := hbase.symm
          rw [hright]
          change C.family.π ≫ g = chiLeft ≫ A.family.π
          exact hchiRight.symm
      · exact hbase.symm

end AlgebraicGeometry.Scheme
