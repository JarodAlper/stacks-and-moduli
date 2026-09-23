module

public import StacksAndModuli.API.FiberProductHomSmall
public import StacksAndModuli.API.PrestackComponents

/-!
# Small connected components of fibers of a presentation

If a map from a small presheaf has pointwise-small self-intersection, then its
base change along a scheme-valued point has universe-small connected components.
The key observation is that an object of the base change is encoded by a point of
the source presheaf, a map to the test scheme, and an isomorphism in the target.
The last datum is a torsor under an automorphism type controlled by the represented
self-intersection.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace CategoryTheory

/-- In a groupoid, if the endomorphisms of `a` are small, then so are the
morphisms from `a` to any object `b`.  When the latter type is inhabited, a
chosen arrow identifies it with a subset of the endomorphisms of `a`. -/
theorem small_hom_from_of_small_end {C : Type u₂} [Category.{v₂} C]
    [IsGroupoid C] (a b : C) [Small.{u} (a ⟶ a)] : Small.{u} (a ⟶ b) := by
  cases isEmpty_or_nonempty (a ⟶ b) with
  | inl h =>
      let _ : IsEmpty (a ⟶ b) := h
      infer_instance
  | inr h =>
      let q : a ⟶ b := Classical.choice h
      apply small_of_injective (f := fun φ : a ⟶ b ↦ φ ≫ inv q)
      intro φ ψ hφψ
      have h' := congrArg (fun k : a ⟶ a ↦ k ≫ q) hφψ
      simpa [Category.assoc] using h'

end CategoryTheory

namespace AlgebraicGeometry

/-- The canonical object of the fiber of `Over T → Scheme` associated to a
morphism `f : S → T`. -/
def overBasedFiberObj (T S : Scheme.{u}) (f : S ⟶ T) :
    (overBased T).p.Fiber S :=
  ⟨Over.mk f, rfl⟩

/-- Every object of a fiber of `Over T → Scheme` is the canonical object
associated to its structural morphism. -/
lemma overBasedFiberObj_surjective (T S : Scheme.{u}) :
    Function.Surjective (overBasedFiberObj T S) := by
  rintro ⟨a, hV⟩
  obtain ⟨V, f, rfl⟩ := a.mk_surjective
  change V = S at hV
  subst V
  exact ⟨f, rfl⟩

/-- Fibers of a representable prestack have universe-small object types. -/
theorem small_fiber_overBased (T S : Scheme.{u}) :
    Small.{u} ((overBased T).p.Fiber S) :=
  small_of_surjective (overBasedFiberObj_surjective T S)

namespace BasedFunctor

variable {Ycat : BasedCategory.{v₂, u₂} Scheme.{u}}
  [Ycat.p.IsFiberedInGroupoids]
  {U R : Scheme.{u}ᵒᵖ ⥤ Type u}
  (F : ofPresheaf U ⥤ᵇ Ycat)
  {T : Scheme.{u}} (g : overBased T ⥤ᵇ Ycat)

/-- Codes for the objects, and hence for the connected components, of a fiber
of `U ×_Y T`. -/
abbrev FiberProductComponentCode (S : Scheme.{u}) :=
  Σ x : (ofPresheaf U).p.Fiber S,
    Σ t : (overBased T).p.Fiber S,
      (F.onFiber S).obj x ⟶ (g.onFiber S).obj t

/-- The isomorphism coordinate in a fiber-product component code is small when
the self-intersection of the source map is represented by a small presheaf. -/
theorem small_fiberProductCode_hom
    (hR : (fiberProduct F F).IsRepresentedByPresheaf R)
    (S : Scheme.{u}) (x : (ofPresheaf U).p.Fiber S)
    (t : (overBased T).p.Fiber S) :
    Small.{u} ((F.onFiber S).obj x ⟶ (g.onFiber S).obj t) := by
  let _ : FunctorToTypes.Small.{u} R := fun _ ↦ inferInstance
  let _ : Small.{u} ((F.onFiber S).obj x ⟶ (F.onFiber S).obj x) :=
    small_hom_onFiber_of_isRepresentedByPresheaf F hR x x
  exact small_hom_from_of_small_end _ _

/-- The type of fiber-product component codes is universe-small. -/
theorem small_fiberProductComponentCode
    (hR : (fiberProduct F F).IsRepresentedByPresheaf R)
    (S : Scheme.{u}) :
    Small.{u} (FiberProductComponentCode F g S) := by
  let _ : Small.{u} ((ofPresheaf U).p.Fiber S) :=
    small_fiber_ofPresheaf U S
  let _ : Small.{u} ((overBased T).p.Fiber S) :=
    small_fiber_overBased T S
  let _ : ∀ (x : (ofPresheaf U).p.Fiber S)
      (t : (overBased T).p.Fiber S),
      Small.{u} ((F.onFiber S).obj x ⟶ (g.onFiber S).obj t) :=
    fun x t ↦ small_fiberProductCode_hom F g hR S x t
  infer_instance

/-- Decode a component code as an object of the corresponding fiber product. -/
noncomputable def fiberProductFiberObjOfCode (S : Scheme.{u})
    (c : FiberProductComponentCode F g S) :
    (fiberProduct F g).p.Fiber S := by
  rcases c with ⟨⟨x, hx⟩, ⟨⟨t, ht⟩, φ⟩⟩
  subst S
  refine ⟨
    { fst := x
      snd := t
      over_eq := ht
      iso := Fiber.fiberInclusion.mapIso (asIso φ)
      isHomLift := φ.2 }, rfl⟩

/-- Decode a component code as a connected component of the corresponding
fiber-product fiber. -/
noncomputable def fiberProductCodeToComponent (S : Scheme.{u}) :
    FiberProductComponentCode F g S →
      CategoryTheory.ConnectedComponents ((fiberProduct F g).p.Fiber S) :=
  fun c ↦ CategoryTheory.ConnectedComponents.mk
    (fiberProductFiberObjOfCode F g S c)

/-- Every connected component of a scheme-valued base change has a component
code. -/
theorem fiberProductCodeToComponent_surjective (S : Scheme.{u}) :
    Function.Surjective (fiberProductCodeToComponent F g S) := by
  intro j
  let a₀ : (fiberProduct F g).p.Fiber S :=
    componentRepresentative (𝒳 := fiberProduct F g) j
  have ha₀ : CategoryTheory.ConnectedComponents.mk a₀ = j :=
    componentRepresentative_component j
  rcases a₀ with ⟨a, ha⟩
  subst S
  let x : (ofPresheaf U).p.Fiber ((ofPresheaf U).p.obj a.fst) :=
    ⟨a.fst, rfl⟩
  let t : (overBased T).p.Fiber ((ofPresheaf U).p.obj a.fst) :=
    ⟨a.snd, a.over_eq⟩
  let _ : IsHomLift Ycat.p
      (𝟙 ((ofPresheaf U).p.obj a.fst)) a.iso.hom := a.isHomLift
  let φ : (F.onFiber ((ofPresheaf U).p.obj a.fst)).obj x ⟶
      (g.onFiber ((ofPresheaf U).p.obj a.fst)).obj t :=
    Fiber.homMk Ycat.p ((ofPresheaf U).p.obj a.fst) a.iso.hom
  let c : FiberProductComponentCode F g ((ofPresheaf U).p.obj a.fst) :=
    ⟨x, t, φ⟩
  refine ⟨c, ?_⟩
  let b := fiberProductFiberObjOfCode F g _ c
  have hbFst : b.1.fst = a.fst := by
    change a.fst = a.fst
    rfl
  have hbSnd : b.1.snd = a.snd := by
    change a.snd = a.snd
    rfl
  have hiso : b.1.iso.hom = a.iso.hom := by
    change Fiber.fiberInclusion.map φ = a.iso.hom
    rfl
  have hbObj : b.1 = a := by
    rw [FiberProductObj.mk.injEq]
    refine ⟨hbFst, hbSnd, ?_⟩
    exact heq_of_eq (Iso.ext hiso)
  let a' : (fiberProduct F g).p.Fiber ((ofPresheaf U).p.obj a.fst) :=
    ⟨a, rfl⟩
  have hb : b = a' := Subtype.ext hbObj
  change CategoryTheory.ConnectedComponents.mk b = j
  rw [hb]
  simpa only [a'] using ha₀

/-- A small represented self-intersection makes every connected-component type
of a scheme-valued base change universe-small. -/
theorem small_connectedComponents_fiberProduct
    (hR : (fiberProduct F F).IsRepresentedByPresheaf R)
    (S : Scheme.{u}) :
    Small.{u} (CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber S)) := by
  let _ : Small.{u} (FiberProductComponentCode F g S) :=
    small_fiberProductComponentCode F g hR S
  exact small_of_surjective (fiberProductCodeToComponent_surjective F g S)

end BasedFunctor

end AlgebraicGeometry
