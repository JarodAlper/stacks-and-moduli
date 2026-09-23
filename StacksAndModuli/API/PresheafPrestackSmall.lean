module

public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.PresheafPrestack
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Small fibers of presheaf prestacks

The fiber over `S` of the prestack associated to a presheaf `F` is controlled by
the type `F(S)`.  This file packages the resulting smallness statement and its
transport along universe-heterogeneous equivalences of based categories.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe w w' v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C]

/-- Restriction along a singleton family for which a presheaf is separated
detects equality; hence a small target of restriction makes its source small. -/
theorem small_obj_of_isSeparatedFor_singleton
    {F : Cᵒᵖ ⥤ Type w'} {X Y : C} (f : Y ⟶ X)
    (hF : IsSeparatedFor F (.singleton f)) [Small.{w} (F.obj (op Y))] :
    Small.{w} (F.obj (op X)) := by
  apply small_of_injective (f := F.map f.op)
  exact isSeparatedFor_singleton.mp hF

/-- A sheaf whose sections become small after restriction along a singleton
cover already has small sections before restriction. -/
theorem small_obj_of_isSheaf_of_generate_singleton_mem
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w'}
    (hF : IsSheaf J F) {X Y : C} (f : Y ⟶ X)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J X)
    [Small.{w} (F.obj (op Y))] : Small.{w} (F.obj (op X)) := by
  apply small_obj_of_isSeparatedFor_singleton f
  exact (hF.isSheafFor (Presieve.singleton f) hf).isSeparatedFor

end CategoryTheory.Presieve

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]

/-- A section of a presheaf determines the canonical object of its associated
prestack fiber. -/
noncomputable def ofPresheafFiberObj (F : Cᵒᵖ ⥤ Type v) (S : C)
    (x : F.obj (op S)) : (ofPresheaf F).p.Fiber S :=
  ⟨CostructuredArrow.mk (yonedaEquiv.symm x), rfl⟩

/-- Every object in a presheaf-prestack fiber is the canonical object associated
to a section. -/
lemma ofPresheafFiberObj_surjective (F : Cᵒᵖ ⥤ Type v) (S : C) :
    Function.Surjective (ofPresheafFiberObj F S) := by
  rintro ⟨X, hX⟩
  obtain ⟨T, x, rfl⟩ := X.mk_surjective
  change T = S at hX
  subst T
  refine ⟨yonedaEquiv x, ?_⟩
  apply Subtype.ext
  change CostructuredArrow.mk (yonedaEquiv.symm (yonedaEquiv x)) =
    CostructuredArrow.mk x
  rw [yonedaEquiv.symm_apply_apply]

/-- If the values of a presheaf are `w`-small, then the object type of every
fiber of its associated prestack is `w`-small. -/
theorem small_fiber_ofPresheaf (F : Cᵒᵖ ⥤ Type v)
    [FunctorToTypes.Small.{w} F] (S : C) :
    Small.{w} ((ofPresheaf F).p.Fiber S) :=
  small_of_surjective (ofPresheafFiberObj_surjective F S)

/-- Every fiber category of a presheaf prestack is thin. -/
theorem isThin_fiber_ofPresheaf (F : Cᵒᵖ ⥤ Type v) (S : C) :
    Quiver.IsThin ((ofPresheaf F).p.Fiber S) := by
  intro X Y
  constructor
  intro f g
  apply Fiber.hom_ext
  apply CostructuredArrow.hom_ext
  have hf := IsHomLift.fac' (ofPresheaf F).p (𝟙 S)
    (Fiber.fiberInclusion.map f)
  have hg := IsHomLift.fac' (ofPresheaf F).p (𝟙 S)
    (Fiber.fiberInclusion.map g)
  exact hf.trans hg.symm

/-- Pointwise smallness of a presheaf makes every fiber of its associated
prestack essentially small. -/
theorem essentiallySmall_fiber_ofPresheaf (F : Cᵒᵖ ⥤ Type v)
    [FunctorToTypes.Small.{w} F] (S : C) :
    EssentiallySmall.{w} ((ofPresheaf F).p.Fiber S) := by
  let _ : Small.{w} ((ofPresheaf F).p.Fiber S) := small_fiber_ofPresheaf F S
  let _ : Quiver.IsThin ((ofPresheaf F).p.Fiber S) := isThin_fiber_ofPresheaf F S
  exact essentiallySmall_of_small_of_locallySmall _

/-- The skeleton of a fiber of a pointwise-small presheaf prestack is small. -/
theorem small_skeleton_fiber_ofPresheaf (F : Cᵒᵖ ⥤ Type v)
    [FunctorToTypes.Small.{w} F] (S : C) :
    Small.{w} (Skeleton ((ofPresheaf F).p.Fiber S)) := by
  let _ : EssentiallySmall.{w} ((ofPresheaf F).p.Fiber S) :=
    essentiallySmall_fiber_ofPresheaf F S
  infer_instance

variable {C₁ : Type u₀} [Category.{v₀} C₁]
  {X : BasedCategory.{v₁, u₁} C₁} {Y : BasedCategory.{v₂, u₂} C₁}

/-- An equivalence of universe-heterogeneous fibered categories induces an
equivalence on every fiber. -/
noncomputable def fiberEquivalenceOfBasedFunctor (E : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] (S : C₁) : X.p.Fiber S ≌ Y.p.Fiber S := by
  let _ : (E.onFiber S).Full := E.onFiber_full S
  let _ : (E.onFiber S).Faithful := E.onFiber_faithful S
  let _ : (E.onFiber S).EssSurj := onFiber_essSurj_of_essSurj E S
  let _ : (E.onFiber S).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact (E.onFiber S).asEquivalence

/-- Essential smallness of fibers is invariant under a universe-heterogeneous
equivalence of based fibered categories. -/
theorem essentiallySmall_fiber_iff_of_isEquivalence (E : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] (S : C₁) :
    EssentiallySmall.{w} (X.p.Fiber S) ↔ EssentiallySmall.{w} (Y.p.Fiber S) :=
  essentiallySmall_congr (fiberEquivalenceOfBasedFunctor E S)

/-- A based equivalence transports essential smallness from its source fiber to
its target fiber. -/
theorem essentiallySmall_fiber_of_isEquivalence (E : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] (S : C₁)
    [EssentiallySmall.{w} (X.p.Fiber S)] :
    EssentiallySmall.{w} (Y.p.Fiber S) :=
  (essentiallySmall_fiber_iff_of_isEquivalence E S).mp inferInstance

/-- A based equivalence transports smallness of the source fiber skeleton to the
target fiber skeleton. -/
theorem small_skeleton_fiber_of_isEquivalence (E : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] (S : C₁)
    [EssentiallySmall.{w} (X.p.Fiber S)] :
    Small.{w} (Skeleton (Y.p.Fiber S)) := by
  let _ : EssentiallySmall.{w} (Y.p.Fiber S) :=
    essentiallySmall_fiber_of_isEquivalence E S
  infer_instance

end CategoryTheory.BasedCategory
