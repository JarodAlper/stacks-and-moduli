module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»

/-!
# Fully faithful morphisms and point spaces

A fully faithful morphism of prestacks induces an injective map on field-valued point
classes.  After passing to a common field extension, fullness and faithfulness lift the
resulting isomorphism in the target fiber to the source fiber; the 2-Yoneda lemma then
reconstructs an isomorphism of the corresponding scheme-valued points.

## Main result

* `AlgebraicGeometry.BasedFunctor.injective_mapPoints_of_full_faithful`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite AlgebraicGeometry
  CategoryTheory.BasedCategory AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {A : BasedCategory.{v₂, u₂} Scheme.{u}}
  {B : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A fully faithful morphism of prestacks is injective on field-valued point classes. -/
theorem injective_mapPoints_of_full_faithful
    [A.p.IsFiberedInGroupoids] [B.p.IsFiberedInGroupoids]
    (F : A ⥤ᵇ B) [F.toFunctor.Full] [F.toFunctor.Faithful] :
    Function.Injective (mapPoints F) := by
  intro p q hpq
  induction p using BasedCategory.pointSpace.ind with
  | _ x =>
  induction q using BasedCategory.pointSpace.ind with
  | _ y =>
  obtain ⟨L, hL, φ, ψ, ⟨e⟩⟩ := BasedCategory.pointSpace.mk_eq_mk_iff.mp hpq
  let S := Spec (CommRingCat.of L)
  let Z : Over S := Over.mk (𝟙 S)
  let a := (x.restrict φ).obj Z
  let b := (y.restrict ψ).obj Z
  have ha : A.p.obj a = S := (x.restrict φ).w_obj Z
  have hb : A.p.obj b = S := (y.restrict ψ).w_obj Z
  let aa : A.p.Fiber S := ⟨a, ha⟩
  let bb : A.p.Fiber S := ⟨b, hb⟩
  let ee : (F.onFiber S).obj aa ≅ (F.onFiber S).obj bb :=
    asIso ⟨e.hom.toNatTrans.app Z, e.hom.app_isHomLift Z⟩
  let _ : (F.onFiber S).Full := F.onFiber_full S
  let _ : (F.onFiber S).Faithful := F.onFiber_faithful S
  let dd : aa ≅ bb := (F.onFiber S).preimageIso ee
  obtain ⟨d⟩ :=
    AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nonempty_iso_of_fiber_iso
      (x.restrict φ) (y.restrict ψ) (Fiber.fiberInclusion.mapIso dd) dd.hom.2
  exact BasedCategory.pointSpace.sound ⟨L, hL, φ, ψ, ⟨d⟩⟩

end AlgebraicGeometry.BasedFunctor
