module

public import StacksAndModuli.API.FiberProductHomSmall
public import StacksAndModuli.API.PresheafPrestackSmall
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Small hom-sets detected by a representable morphism

A representable morphism from a representable prestack makes the morphisms between
objects in its image universe-small. This is the local smallness input needed to
shrink Isom presheaves of algebraic stacks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  [Xcat.p.IsFiberedInGroupoids]

/-- For a representable morphism from a scheme, the type of lifted isomorphisms
between the images of two fixed source objects is universe-small. -/
theorem Representable.small_liftedIso {U : Scheme.{u}}
    {P : overBased U ⥤ᵇ Xcat} (hP : Representable P)
    (x y : (overBased U).obj) (hxy : (overBased U).p.obj y = (overBased U).p.obj x) :
    Small.{u} (LiftedIso P x y) := by
  classical
  obtain ⟨Z, hZ, E, hE⟩ := hP U P
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : FunctorToTypes.Small.{u} Z := fun _ ↦ inferInstance
  let _ : EssentiallySmall.{u} ((ofPresheaf Z).p.Fiber ((overBased U).p.obj x)) :=
    essentiallySmall_fiber_ofPresheaf Z _
  let _ : Small.{u}
      (Skeleton ((fiberProduct P P).p.Fiber ((overBased U).p.obj x))) :=
    small_skeleton_fiber_of_isEquivalence E _
  exact small_of_injective (fiberProductPointOfIso_toSkeleton_injective P x y hxy)

/-- For a representable morphism from a scheme, morphisms in the target fiber
between the images of two source-fiber objects form a universe-small type. -/
theorem Representable.small_hom_between_images {U T : Scheme.{u}}
    {P : overBased U ⥤ᵇ Xcat} (hP : Representable P)
    (x y : (overBased U).p.Fiber T) :
    Small.{u} ((P.onFiber T).obj x ⟶ (P.onFiber T).obj y) := by
  classical
  let hxy : (overBased U).p.obj (Fiber.fiberInclusion.obj y) =
      (overBased U).p.obj (Fiber.fiberInclusion.obj x) := y.2.trans x.2.symm
  let encode : ((P.onFiber T).obj x ⟶ (P.onFiber T).obj y) →
      LiftedIso P (Fiber.fiberInclusion.obj x) (Fiber.fiberInclusion.obj y) := fun φ ↦
    ⟨asIso (Fiber.fiberInclusion.map φ), by
      have hφ : IsHomLift Xcat.p (𝟙 T) (Fiber.fiberInclusion.map φ) := φ.2
      change IsHomLift Xcat.p (𝟙 ((overBased U).p.obj x.1))
        (Fiber.fiberInclusion.map φ)
      rw [x.2]
      exact hφ⟩
  let _ : Small.{u}
      (LiftedIso P (Fiber.fiberInclusion.obj x) (Fiber.fiberInclusion.obj y)) :=
    hP.small_liftedIso _ _ hxy
  apply small_of_injective (f := encode)
  intro φ ψ h
  apply Fiber.hom_ext
  have hiso := congrArg Subtype.val h
  exact congrArg Iso.hom hiso

end AlgebraicGeometry.BasedFunctor
