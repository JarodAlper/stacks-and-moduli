module

public import StacksAndModuli.API.GlobalPrincipalBundleFpqcDescent

/-!
# From scheme-arrow gluing to principal-bundle gluing

This file forgets a descent diagram of principal bundles to the cartesian
diagram of its underlying scheme arrows.  Any effective gluing of that diagram
then supplies the underlying gluing required by the structured fpqc descent
API.  It deliberately has no dependency on Chapter 3's later stack vocabulary.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]
variable {T : Over S} {R : Sieve T}
  (D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G))
  (hDobj : ∀ q : R.arrows.category,
    (classifyingPrestack G).p.obj (D.obj q) = q.obj.left)
  (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    IsHomLift (classifyingPrestack G).p k.hom.left (D.map k))

namespace ClassifyingObj

/-- Forget a principal-bundle descent diagram to the cartesian diagram of its
underlying scheme arrows. -/
def underlyingArrowFunctor :
    CategoryTheory.Functor R.arrows.category
      (CategoryTheory.ArrowCartesian Scheme.{u}) where
  obj q := CategoryTheory.ArrowCartesian.mk (D.obj q).bundle.p.left
  map k :=
    { left := (D.map k).total.left
      right := (D.map k).base.left
      isPullback := (D.map k).isPullback.map (Over.forget S) }
  map_id q := by
    apply CategoryTheory.CartesianArrowHom.ext <;> rw [D.map_id] <;> rfl
  map_comp k l := by
    apply CategoryTheory.CartesianArrowHom.ext <;> rw [D.map_comp] <;> rfl

@[simp]
lemma underlyingArrowFunctor_obj_hom (q : R.arrows.category) :
    ((underlyingArrowFunctor D).obj q : Arrow Scheme.{u}).hom =
      (D.obj q).bundle.p.left := rfl

@[simp]
lemma underlyingArrowFunctor_map_left {q r : R.arrows.category} (k : q ⟶ r) :
    ((underlyingArrowFunctor D).map k).left = (D.map k).total.left := rfl

@[simp]
lemma underlyingArrowFunctor_map_right {q r : R.arrows.category} (k : q ⟶ r) :
    ((underlyingArrowFunctor D).map k).right = (D.map k).base.left := rfl

include hDobj in
lemma underlyingArrowFunctor_obj_base (q : R.arrows.category) :
    (CategoryTheory.arrowCartesian Scheme.{u}).p.obj
      ((underlyingArrowFunctor D).obj q) = q.obj.left.left := by
  exact congrArg Over.left (hDobj q)

include hDobj hDmap in
lemma underlyingArrowFunctor_map_isHomLift {q r : R.arrows.category} (k : q ⟶ r) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left.left
      ((underlyingArrowFunctor D).map k) := by
  letI := hDmap k
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left.left
      ((underlyingArrowFunctor D).map k)
      (underlyingArrowFunctor_obj_base D hDobj q)
      (underlyingArrowFunctor_obj_base D hDobj r)
  change (D.map k).base.left ≫
      eqToHom (congrArg Over.left (hDobj r)) =
    eqToHom (congrArg Over.left (hDobj q)) ≫ k.hom.left.left
  have H := IsHomLift.fac' (classifyingPrestack G).p k.hom.left (D.map k)
  change (D.map k).base =
    eqToHom (hDobj q) ≫ k.hom.left ≫ eqToHom (hDobj r).symm at H
  rw [H]
  simp

section FromArrowGluing

variable (A : Arrow Scheme.{u})
  (hA : (CategoryTheory.arrowCartesian Scheme.{u}).p.obj A = T.left)
  (ε : ∀ q : R.arrows.category, (underlyingArrowFunctor D).obj q ⟶ A)
  (hε : ∀ q : R.arrows.category,
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p q.obj.hom.left (ε q))
  (hnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    (underlyingArrowFunctor D).map k ≫ ε r = ε q)

/-- The total space over the fixed base scheme underlying a glued scheme arrow. -/
noncomputable def arrowGluingTotalOver : Over S :=
  Over.mk ((A : Arrow Scheme.{u}).hom ≫ eqToHom hA ≫ T.hom)

/-- The projection of the total space underlying a glued scheme arrow. -/
noncomputable def arrowGluingProjection :
    arrowGluingTotalOver A hA ⟶ T :=
  Over.homMk ((A : Arrow Scheme.{u}).hom ≫ eqToHom hA)

/-- The local comparison, regarded as a morphism over the fixed base scheme. -/
noncomputable def arrowGluingTotal (q : R.arrows.category) :
    (D.obj q).bundle.P ⟶ arrowGluingTotalOver A hA := by
  refine Over.homMk (ε q).left ?_
  dsimp [arrowGluingTotalOver]
  have hw := (ε q).isPullback.w
  change (ε q).left ≫ (A : Arrow Scheme.{u}).hom =
    (D.obj q).bundle.p.left ≫ (ε q).right at hw
  simp only [← Category.assoc]
  rw [hw]
  simp only [Category.assoc]
  letI := hε q
  have H := IsHomLift.fac'
    (CategoryTheory.arrowCartesian Scheme.{u}).p q.obj.hom.left (ε q)
  change (ε q).right =
    eqToHom (congrArg Over.left (hDobj q)) ≫ q.obj.hom.left ≫
      eqToHom hA.symm at H
  rw [H]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [q.obj.hom.w]
  have heq : eqToHom (congrArg Over.left (hDobj q)) ≫ q.obj.left.hom =
      (D.obj q).base.hom := by
    simpa using (eqToHom (hDobj q) : (D.obj q).base ⟶ q.obj.left).w
  rw [heq, (D.obj q).bundle.p.w]

include hDobj in
lemma arrowGluingIsPullback (q : R.arrows.category) :
    IsPullback (arrowGluingTotal D hDobj A hA ε hε q)
      (D.obj q).bundle.p (arrowGluingProjection A hA)
      (eqToHom (hDobj q) ≫ q.obj.hom) := by
  let eA : (A : Arrow Scheme.{u}).right ≅ T.left := eqToIso hA
  have hpb₂ : IsPullback (𝟙 (A : Arrow Scheme.{u}).left)
      (A : Arrow Scheme.{u}).hom
      ((A : Arrow Scheme.{u}).hom ≫ eA.hom) eA.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hpbscheme := (ε q).isPullback.paste_horiz hpb₂
  letI := hε q
  have H := IsHomLift.fac'
    (CategoryTheory.arrowCartesian Scheme.{u}).p q.obj.hom.left (ε q)
  change (ε q).right =
    eqToHom (congrArg Over.left (hDobj q)) ≫ q.obj.hom.left ≫
      eqToHom hA.symm at H
  have hbottom : (ε q).right ≫ eqToHom hA =
      (eqToHom (hDobj q) ≫ q.obj.hom).left := by
    rw [H]
    simp
  apply IsPullback.of_map_of_faithful (F := Over.forget S)
  simpa [arrowGluingTotal, arrowGluingProjection, eA, hbottom] using hpbscheme

include hnat in
lemma arrowGluingTotal_naturality {q r : R.arrows.category} (k : q ⟶ r) :
    (D.map k).total ≫ arrowGluingTotal D hDobj A hA ε hε r =
      arrowGluingTotal D hDobj A hA ε hε q := by
  apply CategoryTheory.Over.OverMorphism.ext
  exact congrArg CategoryTheory.CartesianArrowHom.left (hnat k)

/-- A gluing of the underlying scheme arrows induces the underlying cartesian
gluing needed to descend the principal-bundle structure. -/
noncomputable def underlyingGluingOfArrowGluing :
    UnderlyingGluing D hDobj hDmap where
  P := arrowGluingTotalOver A hA
  p := arrowGluingProjection A hA
  total := arrowGluingTotal D hDobj A hA ε hε
  isPullback := arrowGluingIsPullback D hDobj A hA ε hε
  naturality := arrowGluingTotal_naturality D hDobj A hA ε hε hnat

end FromArrowGluing

end ClassifyingObj

end AlgebraicGeometry.Scheme
