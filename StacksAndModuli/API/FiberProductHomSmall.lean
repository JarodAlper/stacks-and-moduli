module

public import StacksAndModuli.API.PresheafPrestackSmall
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import Mathlib.CategoryTheory.HomCongr

/-!
# Smallness of morphisms detected by a fiber product

This file relates morphisms between two points in the image of a based functor to
isomorphism classes in the fiber of its self-fiber-product.  It is supporting API for
universe-safe representability arguments for diagonals of algebraic stacks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {𝒳 : BasedCategory.{v₂, u₂} C}
  {𝒴 : BasedCategory.{v₃, u₃} C} {S : C}

/-- Isomorphisms between the images of two objects that lie over the identity of the
base of the first object. -/
abbrev LiftedIso (F : BasedFunctor 𝒳 𝒴) (x y : 𝒳.obj) :=
  {e : F.obj x ≅ F.obj y // IsHomLift 𝒴.p (𝟙 (𝒳.p.obj x)) e.hom}

/-- An isomorphism in a target fiber, between the images of two objects in a source
fiber, regarded as a lifted isomorphism over the source base. -/
noncomputable def liftedIsoOfFiberIso (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.p.Fiber S)
    (e : (F.onFiber S).obj x ≅ (F.onFiber S).obj y) : LiftedIso F x.1 y.1 := by
  refine ⟨Fiber.fiberInclusion.mapIso e, ?_⟩
  apply IsHomLift.of_fac' 𝒴.p
    (𝟙 (𝒳.p.obj x.1)) (Fiber.fiberInclusion.map e.hom)
    (F.w_obj x.1) ((F.w_obj y.1).trans (y.2.trans x.2.symm))
  have h := IsHomLift.fac' 𝒴.p (𝟙 S) (Fiber.fiberInclusion.map e.hom)
  rw [show IsHomLift.domain_eq 𝒴.p (𝟙 S)
      (Fiber.fiberInclusion.map e.hom) = (F.w_obj x.1).trans x.2 from
        Subsingleton.elim _ _,
    show IsHomLift.codomain_eq 𝒴.p (𝟙 S)
      (Fiber.fiberInclusion.map e.hom) = (F.w_obj y.1).trans y.2 from
        Subsingleton.elim _ _] at h
  simpa only [eqToHom_trans, Category.assoc, Category.id_comp, Category.comp_id,
    eqToHom_refl] using h

@[simp]
lemma liftedIsoOfFiberIso_iso (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.p.Fiber S)
    (e : (F.onFiber S).obj x ≅ (F.onFiber S).obj y) :
    (liftedIsoOfFiberIso F x y e).1 = Fiber.fiberInclusion.mapIso e :=
  rfl

/-- An isomorphism between the images of two objects determines an object of the
corresponding fiber of the self-fiber-product. -/
def fiberProductPointOfIso (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.obj) (hxy : 𝒳.p.obj y = 𝒳.p.obj x)
    (e : LiftedIso F x y) : (fiberProduct F F).p.Fiber (𝒳.p.obj x) :=
  ⟨{ fst := x
     snd := y
     over_eq := hxy
     iso := e.1
     isHomLift := e.2 }, rfl⟩

@[simp]
lemma fiberProductPointOfIso_fst (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.obj) (hxy : 𝒳.p.obj y = 𝒳.p.obj x)
    (e : LiftedIso F x y) :
    (fiberProductPointOfIso F x y hxy e).1.fst = x :=
  rfl

@[simp]
lemma fiberProductPointOfIso_snd (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.obj) (hxy : 𝒳.p.obj y = 𝒳.p.obj x)
    (e : LiftedIso F x y) :
    (fiberProductPointOfIso F x y hxy e).1.snd = y :=
  rfl

@[simp]
lemma fiberProductPointOfIso_iso (F : BasedFunctor 𝒳 𝒴)
    (x y : 𝒳.obj) (hxy : 𝒳.p.obj y = 𝒳.p.obj x)
    (e : LiftedIso F x y) :
    (fiberProductPointOfIso F x y hxy e).1.iso = e.1 :=
  rfl

/-- If the source projection is faithful, distinct lifted isomorphisms determine
distinct isomorphism classes in the fiber of the self-fiber-product. -/
theorem fiberProductPointOfIso_toSkeleton_injective (F : BasedFunctor 𝒳 𝒴)
    [𝒳.p.Faithful] (x y : 𝒳.obj)
    (hxy : 𝒳.p.obj y = 𝒳.p.obj x) :
    Function.Injective (fun e : LiftedIso F x y ↦
      toSkeleton (fiberProductPointOfIso F x y hxy e)) := by
  intro e e' h
  let α : fiberProductPointOfIso F x y hxy e ≅
      fiberProductPointOfIso F x y hxy e' := Skeleton.isoOfEq h
  let q := Fiber.fiberInclusion.map α.hom
  have hq : IsHomLift (fiberProduct F F).p (𝟙 (𝒳.p.obj x)) q := α.hom.2
  have hfstLift : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj x)) q.fst :=
    FiberProductHom.isHomLift_fst q (𝟙 (𝒳.p.obj x)) hq
  have hsndLift : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj x)) q.snd :=
    FiberProductHom.isHomLift_snd q (𝟙 (𝒳.p.obj x)) hq
  have hfst : q.fst = 𝟙 x := by
    apply 𝒳.p.map_injective
    exact (IsHomLift.eq_of_isHomLift 𝒳.p (𝟙 (𝒳.p.obj x)) q.fst).symm.trans
      (𝒳.p.map_id x).symm
  have hsnd : q.snd = 𝟙 y := by
    apply 𝒳.p.map_injective
    have hs := IsHomLift.fac' 𝒳.p (𝟙 (𝒳.p.obj x)) q.snd
    simp at hs
    change 𝒳.p.map q.snd = 𝟙 (𝒳.p.obj y) at hs
    exact hs.trans (𝒳.p.map_id y).symm
  apply Subtype.ext
  apply Iso.ext
  have hw : F.map q.fst ≫ e'.1.hom = e.1.hom ≫ F.map q.snd := q.w
  rw [hfst, hsnd] at hw
  calc
    e.1.hom = e.1.hom ≫ 𝟙 (F.obj y) := (Category.comp_id _).symm
    _ = e.1.hom ≫ F.map (𝟙 y) :=
      congrArg (fun t ↦ e.1.hom ≫ t) (F.toFunctor.map_id y).symm
    _ = F.map (𝟙 x) ≫ e'.1.hom := hw.symm
    _ = 𝟙 (F.obj x) ≫ e'.1.hom :=
      congrArg (fun t ↦ t ≫ e'.1.hom) (F.toFunctor.map_id x)
    _ = e'.1.hom := Category.id_comp _

/-- If the self-fiber-product is represented by a pointwise-small presheaf, then
the lifted isomorphisms between any two fixed source objects form a small type. -/
theorem small_liftedIso_of_isRepresentedByPresheaf (F : BasedFunctor 𝒳 𝒴)
    [𝒳.p.Faithful] [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {A : Cᵒᵖ ⥤ Type v₁} [FunctorToTypes.Small.{w} A]
    (hA : (fiberProduct F F).IsRepresentedByPresheaf A)
    (x y : 𝒳.obj) (hxy : 𝒳.p.obj y = 𝒳.p.obj x) :
    Small.{w} (LiftedIso F x y) := by
  obtain ⟨E, hE⟩ := hA
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : EssentiallySmall.{w} ((ofPresheaf A).p.Fiber (𝒳.p.obj x)) :=
    essentiallySmall_fiber_ofPresheaf A (𝒳.p.obj x)
  let _ : Small.{w} (Skeleton ((fiberProduct F F).p.Fiber (𝒳.p.obj x))) :=
    small_skeleton_fiber_of_isEquivalence E (𝒳.p.obj x)
  exact small_of_injective (fiberProductPointOfIso_toSkeleton_injective F x y hxy)

/-- If the self-fiber-product of a based functor is represented by a pointwise-small
presheaf, then the hom type between the images of any two objects in one source fiber
is small. -/
theorem small_hom_onFiber_of_isRepresentedByPresheaf (F : BasedFunctor 𝒳 𝒴)
    [𝒳.p.Faithful] [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {A : Cᵒᵖ ⥤ Type v₁} [FunctorToTypes.Small.{w} A]
    (hA : (fiberProduct F F).IsRepresentedByPresheaf A)
    (x y : 𝒳.p.Fiber S) :
    Small.{w} ((F.onFiber S).obj x ⟶ (F.onFiber S).obj y) := by
  let _ : Small.{w} (LiftedIso F x.1 y.1) :=
    small_liftedIso_of_isRepresentedByPresheaf F hA x.1 y.1 (y.2.trans x.2.symm)
  apply small_of_injective (f := fun φ ↦ liftedIsoOfFiberIso F x y (asIso φ))
  intro φ ψ h
  apply Fiber.hom_ext
  exact congrArg (fun e : LiftedIso F x.1 y.1 ↦ e.1.hom) h

end CategoryTheory.BasedCategory
