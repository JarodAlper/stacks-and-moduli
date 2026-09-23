module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Fiber products of presheaves and sheaves

This module formalizes the "Fiber products" subsection of §3.3 (Presheaves and sheaves) of
*Stacks and Moduli*, section
label `sec:sheaves` (the subsection itself is unlabeled): the explicit fiber product of
presheaves (Definition 3.3.12, `def:fiber-product`, and Equation 3.3.13,
`eqn:fiber-product`) and the fact that it is a fiber product in the categories of
presheaves and of sheaves (Exercise 3.3.14, `exer:presheaves-sheaves-fiber-product`).

Main results:
- `CategoryTheory.Presheaf.fiberProduct`: the fiber product `F ×_G G'` of presheaves of
  types along `α : F ⟶ G` and `β : G' ⟶ G`, with sections
  `{(a, b) ∈ F(S) × G'(S) | α(a) = β(b)}`;
- `CategoryTheory.Presheaf.fiberProduct.isLimit`: the explicit fiber product is a fiber
  product in the category of presheaves;
- `CategoryTheory.Presieve.IsSheaf.fiberProduct`: if `F`, `G`, `G'` are sheaves for a
  Grothendieck topology, so is `F ×_G G'`;
- `CategoryTheory.Sheaf.explicitFiberProductIsLimit`: the pointwise construction, packaged
  as a sheaf, is a fiber product in the category of sheaves.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefFiberProduct

open CategoryTheory Limits ConcreteCategory

universe w v u

/- Background Yoneda observation preceding Definition 3.3.12: a morphism from the presheaf represented by `X` to a
presheaf `F` is canonically the same as an element of `F(X)`. -/
example {𝒮 : Type u} [Category.{v} 𝒮] (X : 𝒮) (F : 𝒮ᵒᵖ ⥤ Type v) :
    (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X) :=
  yonedaEquiv

namespace CategoryTheory.Presheaf

variable {𝒮 : Type u} [Category.{v} 𝒮] {F G G' : 𝒮ᵒᵖ ⥤ Type w} (α : F ⟶ G) (β : G' ⟶ G)

/-- **Definition 3.3.12** (`def:fiber-product`), also **Equation 3.3.13**
(`eqn:fiber-product`):
let $\alpha \colon F \to G$ and $\beta \colon G' \to G$ be
morphisms of presheaves of sets on a category $\cS$. The *fiber product* $F \times_G G'$ is
the presheaf whose set of sections over $S$ is
$\{(a, b) \in F(S) \times G'(S) \mid \alpha_S(a) = \beta_S(b)\}$. -/
@[simps]
def fiberProduct : 𝒮ᵒᵖ ⥤ Type w where
  obj S := Types.PullbackObj (α.app S) (β.app S)
  map {S T} f := ↾fun p ↦
    ⟨⟨F.map f p.1.1, G'.map f p.1.2⟩, by
      have h₁ := congr_hom (α.naturality f) p.1.1
      have h₂ := congr_hom (β.naturality f) p.1.2
      dsimp at h₁ h₂
      rw [h₁, h₂, p.2]⟩
  map_id S := by
    ext p
    · exact congr_hom (F.map_id S) p.1.1
    · exact congr_hom (G'.map_id S) p.1.2
  map_comp f g := by
    ext p
    · exact congr_hom (F.map_comp f g) p.1.1
    · exact congr_hom (G'.map_comp f g) p.1.2

namespace fiberProduct

/-- The first projection $F \times_G G' \to F$. -/
@[simps]
def fst : fiberProduct α β ⟶ F where
  app S := ↾fun p ↦ p.1.1

/-- The second projection $F \times_G G' \to G'$. -/
@[simps]
def snd : fiberProduct α β ⟶ G' where
  app S := ↾fun p ↦ p.1.2

/-- The fiber product square commutes. -/
lemma condition : fst α β ≫ α = snd α β ≫ β := by
  ext S p
  exact p.2

end fiberProduct

end CategoryTheory.Presheaf

end DefFiberProduct

section ExerPresheavesSheavesFiberProduct

open CategoryTheory Limits ConcreteCategory

universe w v u

namespace CategoryTheory.Presheaf

variable {𝒮 : Type u} [Category.{v} 𝒮] {F G G' : 𝒮ᵒᵖ ⥤ Type w} (α : F ⟶ G) (β : G' ⟶ G)

namespace fiberProduct

/-- **Exercise 3.3.14** (`exer:presheaves-sheaves-fiber-product`) (part (a)): the explicit
fiber product of presheaves (Equation 3.3.13), together with its two
projections, is a fiber product in the category of presheaves. -/
def isLimit : IsLimit (PullbackCone.mk (fst α β) (snd α β) (condition α β)) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦
      { app := fun S ↦ ↾fun x ↦
          ⟨⟨s.fst.app S x, s.snd.app S x⟩, congr_hom (congr_app s.condition S) x⟩
        naturality := fun S T f ↦ by
          ext x
          refine Subtype.ext (Prod.ext ?_ ?_)
          · exact congr_hom (s.fst.naturality f) x
          · exact congr_hom (s.snd.naturality f) x })
    (fun s ↦ by ext S x; rfl)
    (fun s ↦ by ext S x; rfl)
    (fun s m h₁ h₂ ↦ by
      ext S x
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact congr_hom (congr_app h₁ S) x
      · exact congr_hom (congr_app h₂ S) x)

end fiberProduct

end CategoryTheory.Presheaf

namespace CategoryTheory.Presieve.IsSheaf

open Presheaf Opposite

variable {𝒮 : Type u} [Category.{v} 𝒮] {J : GrothendieckTopology 𝒮}
variable {F G G' : 𝒮ᵒᵖ ⥤ Type w} {α : F ⟶ G} {β : G' ⟶ G}

/-- **Exercise 3.3.14** (`exer:presheaves-sheaves-fiber-product`) (part (b)): let
$\alpha \colon F \to G$ and $\beta \colon G' \to G$ be morphisms of sheaves on a site. Then
the fiber product presheaf $F \times_G G'$ is a sheaf. In particular the explicit fiber
product of presheaves is also a fiber product in the category of sheaves. -/
theorem fiberProduct (hF : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G)
    (hG' : Presieve.IsSheaf J G') :
    Presieve.IsSheaf J (Presheaf.fiberProduct α β) := by
  intro X R hR x hx
  -- amalgamate the two component families
  obtain ⟨t₁, ht₁, ht₁u⟩ := hF R hR (fun Y f hf ↦ (x f hf).1.1)
    (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦ congrArg (fun p ↦ p.1.1) (hx g₁ g₂ h₁ h₂ w))
  obtain ⟨t₂, ht₂, ht₂u⟩ := hG' R hR (fun Y f hf ↦ (x f hf).1.2)
    (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦ congrArg (fun p ↦ p.1.2) (hx g₁ g₂ h₁ h₂ w))
  -- `α t₁ = β t₂`: both amalgamate the same family, and `G` is separated
  have hglue : α.app (op X) t₁ = β.app (op X) t₂ := by
    refine (hG R hR).isSeparatedFor (fun Y f hf ↦ α.app (op Y) ((x f hf).1.1)) _ _
      (fun Y f hf ↦ ?_) (fun Y f hf ↦ ?_)
    · have h₁ := congr_hom (α.naturality f.op) t₁
      dsimp at h₁
      rw [← h₁, ht₁ f hf]
    · have h₂ := congr_hom (β.naturality f.op) t₂
      dsimp at h₂
      rw [← h₂, ht₂ f hf, ← (x f hf).2]
  refine ⟨⟨⟨t₁, t₂⟩, hglue⟩, fun Y f hf ↦ ?_, fun y hy ↦ ?_⟩
  · exact Subtype.ext (Prod.ext (ht₁ f hf) (ht₂ f hf))
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact ht₁u y.1.1 fun Y f hf ↦ congrArg (fun p ↦ p.1.1) (hy f hf)
    · exact ht₂u y.1.2 fun Y f hf ↦ congrArg (fun p ↦ p.1.2) (hy f hf)

end CategoryTheory.Presieve.IsSheaf

namespace CategoryTheory.Sheaf

variable {𝒮 : Type u} [Category.{v} 𝒮] {J : GrothendieckTopology 𝒮}
variable {F G G' : Sheaf J (Type w)} (α : F ⟶ G) (β : G' ⟶ G)

/-- Background construction for Exercise 3.3.14 (part (b), the implicit
construction): the pointwise fiber product of the underlying presheaves of three sheaves is
again a sheaf. -/
def explicitFiberProduct : Sheaf J (Type w) :=
  ⟨Presheaf.fiberProduct α.hom β.hom, by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact Presieve.IsSheaf.fiberProduct
      ((CategoryTheory.isSheaf_iff_isSheaf_of_type J F.obj).mp F.2)
      ((CategoryTheory.isSheaf_iff_isSheaf_of_type J G.obj).mp G.2)
      ((CategoryTheory.isSheaf_iff_isSheaf_of_type J G'.obj).mp G'.2)⟩

/-- The first projection from the explicit fiber product sheaf. -/
def explicitFiberProductFst : explicitFiberProduct α β ⟶ F :=
  ⟨Presheaf.fiberProduct.fst α.hom β.hom⟩

/-- The second projection from the explicit fiber product sheaf. -/
def explicitFiberProductSnd : explicitFiberProduct α β ⟶ G' :=
  ⟨Presheaf.fiberProduct.snd α.hom β.hom⟩

/-- The explicit fiber product square of sheaves commutes. -/
lemma explicitFiberProduct_condition :
    explicitFiberProductFst α β ≫ α = explicitFiberProductSnd α β ≫ β := by
  apply Sheaf.hom_ext
  exact Presheaf.fiberProduct.condition α.hom β.hom

/-- **Exercise 3.3.14** (`exer:presheaves-sheaves-fiber-product`) (part (b), categorical
pullback clause): the pointwise fiber product, with the sheaf structure supplied above, is a
fiber product in the category of sheaves. -/
def explicitFiberProductIsLimit : IsLimit
    (PullbackCone.mk (explicitFiberProductFst α β) (explicitFiberProductSnd α β)
      (explicitFiberProduct_condition α β)) :=
  PullbackCone.IsLimit.mk _
    (fun s =>
      let s' : PullbackCone α.hom β.hom :=
        PullbackCone.mk s.fst.hom s.snd.hom
          (congrArg (fun k => k.hom) s.condition)
      ⟨(Presheaf.fiberProduct.isLimit α.hom β.hom).lift s'⟩)
    (fun s => by
      apply Sheaf.hom_ext
      exact (Presheaf.fiberProduct.isLimit α.hom β.hom).fac
        (PullbackCone.mk s.fst.hom s.snd.hom
          (congrArg (fun k => k.hom) s.condition)) WalkingCospan.left)
    (fun s => by
      apply Sheaf.hom_ext
      exact (Presheaf.fiberProduct.isLimit α.hom β.hom).fac
        (PullbackCone.mk s.fst.hom s.snd.hom
          (congrArg (fun k => k.hom) s.condition)) WalkingCospan.right)
    (fun s m h₁ h₂ => by
      apply Sheaf.hom_ext
      apply PullbackCone.IsLimit.hom_ext
        (Presheaf.fiberProduct.isLimit α.hom β.hom)
      · exact congrArg (fun k => k.hom) h₁
      · exact congrArg (fun k => k.hom) h₂)

end CategoryTheory.Sheaf

end ExerPresheavesSheavesFiberProduct
