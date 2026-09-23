module

public import StacksAndModuli.API.IsomPresheafStack
public import StacksAndModuli.API.FiberHomIsoTransport
public import StacksAndModuli.API.PresheafPrestackSmall
public import StacksAndModuli.API.RepresentableHomSmall
public import StacksAndModuli.API.SchemeRepresentableSheafDescent
public import StacksAndModuli.API.StackPresentationLocalLift

/-!
# Universe-small Isom presheaves of algebraic stacks

An algebraic-stack presentation makes Isom sets small after a surjective étale
base change. Separatedness of the Isom sheaf then descends this smallness.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- If the Isom set of two fiber objects is small after pullback by a surjective
étale morphism, then the original Isom set is small. -/
theorem small_fiber_hom_of_small_pullback
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    [BasedCategory.IsStack Scheme.etaleTopology Xcat]
    {T T' : Scheme.{u}} (a b : Xcat.p.Fiber T) (p : T' ⟶ T)
    [Etale p] [Surjective p]
    [Small.{u} ((BasedCategory.isomPresheaf a b).obj (op (Over.mk p)))] :
    Small.{u} (a ⟶ b) := by
  classical
  let terminal : Over T := Over.mk (𝟙 T)
  let k : Over.mk p ⟶ terminal := Over.homMk p
  have hkcover : Sieve.generate (Presieve.singleton k) ∈
      (Scheme.etaleTopology.over T) terminal := by
    simpa [k, terminal] using
      Scheme.generate_singleton_mem_etaleTopology_over_of_smooth p (𝟙 T)
  let _ : Small.{u} ((BasedCategory.isomPresheaf a b).obj (op terminal)) :=
    Presieve.small_obj_of_isSheaf_of_generate_singleton_mem
      ((isSheaf_iff_isSheaf_of_type _ _).mp
        (BasedCategory.isomPresheaf_isSheaf a b)) k hkcover
  let πa : BasedCategory.pullbackFiberObj a terminal ⟶ a :=
    ⟨IsPreFibered.pullbackMap a.2 terminal.hom, by
      change Xcat.p.IsHomLift terminal.hom _
      infer_instance⟩
  let πb : BasedCategory.pullbackFiberObj b terminal ⟶ b :=
    ⟨IsPreFibered.pullbackMap b.2 terminal.hom, by
      change Xcat.p.IsHomLift terminal.hom _
      infer_instance⟩
  let encode : (a ⟶ b) →
      (BasedCategory.isomPresheaf a b).obj (op terminal) := fun φ ↦
    πa ≫ φ ≫ inv πb
  apply small_of_injective (f := encode)
  intro φ ψ h
  dsimp [encode] at h
  rw [← cancel_epi πa, ← cancel_mono (inv πb)]
  simpa only [Category.assoc] using h

/-- The hom-set between any two objects in the same fiber of an algebraic stack
is universe-small. -/
theorem IsAlgebraicStack.small_fiber_hom
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) : Small.{u} (a ⟶ b) := by
  classical
  obtain ⟨U, P, hP⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Xcat)
  obtain ⟨T', p, hpEtale, hpSurjective, liftA, liftB, ⟨eA⟩, ⟨eB⟩⟩ :=
    hP.exists_etale_surjective_pair_lift
      (BasedCategory.twoYonedaPullback T a)
      (BasedCategory.twoYonedaPullback T b)
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  let x : (overBased U).p.Fiber T' :=
    (BasedCategory.twoYonedaEval (𝒳 := overBased U) T').obj liftA
  let y : (overBased U).p.Fiber T' :=
    (BasedCategory.twoYonedaEval (𝒳 := overBased U) T').obj liftB
  let ex : (P.onFiber T').obj x ≅
      BasedCategory.pullbackFiberObj a (Over.mk p) := by
    let hsource : (P.onFiber T').obj x =
        (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').obj (liftA.comp P) := by
      apply Fiber.fiberInclusion_obj_inj
      rfl
    let htarget :
        (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').obj
            ((overBased.map p).comp (BasedCategory.twoYonedaPullback T a)) =
          BasedCategory.pullbackFiberObj a (Over.mk p) := by
      apply Fiber.fiberInclusion_obj_inj
      rfl
    exact eqToIso hsource ≪≫
      (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').mapIso eA ≪≫
        eqToIso htarget
  let ey : (P.onFiber T').obj y ≅
      BasedCategory.pullbackFiberObj b (Over.mk p) := by
    let hsource : (P.onFiber T').obj y =
        (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').obj (liftB.comp P) := by
      apply Fiber.fiberInclusion_obj_inj
      rfl
    let htarget :
        (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').obj
            ((overBased.map p).comp (BasedCategory.twoYonedaPullback T b)) =
          BasedCategory.pullbackFiberObj b (Over.mk p) := by
      apply Fiber.fiberInclusion_obj_inj
      rfl
    exact eqToIso hsource ≪≫
      (BasedCategory.twoYonedaEval (𝒳 := Xcat) T').mapIso eB ≪≫
        eqToIso htarget
  let _ : Small.{u} ((P.onFiber T').obj x ⟶ (P.onFiber T').obj y) :=
    hP.representable.small_hom_between_images x y
  let _ : Small.{u}
      ((BasedCategory.isomPresheaf a b).obj (op (Over.mk p))) := by
    change Small.{u}
      (BasedCategory.pullbackFiberObj a (Over.mk p) ⟶
        BasedCategory.pullbackFiberObj b (Over.mk p))
    exact BasedFunctor.small_hom_of_iso_onFiber (S := T') P ex ey
  exact small_fiber_hom_of_small_pullback a b p

/-- The Isom presheaf between two objects in a fiber of an algebraic stack is
pointwise small in the universe of schemes. -/
theorem IsAlgebraicStack.small_isomPresheaf
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) :
    FunctorToTypes.Small.{u} (BasedCategory.isomPresheaf a b) := by
  intro f
  exact IsAlgebraicStack.small_fiber_hom
    (BasedCategory.pullbackFiberObj a f.unop)
    (BasedCategory.pullbackFiberObj b f.unop)

end AlgebraicGeometry
