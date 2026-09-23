module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Algebraic spaces and stacks — a minimal working example

A self-contained experimental excerpt of the library, mirroring Definitions 4.1.2, 4.1.4,
and 4.1.6 of §4.1 (Definitions of algebraic spaces and stacks) of *Stacks and Moduli*.
It is stated from Mathlib alone, with no `sorry`, and none of its declarations are the
canonical book formalizations.

The three definitions are word-for-word those of `StacksAndModuli/Section4.1-Definitions/`; what
is stripped away is everything they do not *need*. Of the supporting notions only the
minimum required to write the statements is redeveloped here, in the order the book
introduces it:

- `CategoryTheory.Functor.IsFiberedInGroupoids`: Definition 3.4.1,
  prestacks (categories fibered in groupoids);
- `CategoryTheory.BasedCategory.ofPresheaf`: Example 3.4.7, the prestack of a presheaf;
- `CategoryTheory.BasedCategory.overBased`: Example 3.4.8,
  the representable prestack `𝒮/S`;
- `CategoryTheory.BasedCategory.fiberProduct` with `fiberProductSnd`: Construction 3.4.33,
  fiber products of prestacks;
- `CategoryTheory.Functor.IsStack` and `CategoryTheory.BasedCategory.IsStack`:
  Definition 3.5.1, the stack axioms;
- `CategoryTheory.BasedCategory.IsRepresentedByPresheaf`,
  `AlgebraicGeometry.BasedFunctor.Representable` and `.RepresentableWith`:
  Definition 4.1.3, representable morphisms of prestacks and their properties.

Omitted, since no statement below mentions them: the universal property of the fiber
product and its first projection, every lemma and `simp` normal form, all instances
(`overBased S` and `ofPresheaf X` being fibered in groupoids, schemes being algebraic
spaces, algebraic spaces being Deligne–Mumford stacks, …), and the prestack-level
representability by schemes of Definition 4.1.1 — at the presheaf level, which is all
the algebraic-space definition uses, that notion is Mathlib's `MorphismProperty.presheaf`.

Experimental main declarations:

- `AlgebraicGeometry.IsAlgebraicSpace`: mirrors Definition 4.1.2;
- `AlgebraicGeometry.IsDeligneMumfordStack`: mirrors Definition 4.1.4;
- `AlgebraicGeometry.IsAlgebraicStack`: mirrors Definition 4.1.6.

The declarations carry the names they have in the library, so this module and
`StacksAndModuli/Section4.1-Definitions/` are not meant to be imported together. The single
respelling is the composite appearing in `RepresentableWith`: the library goes through
`overBasedToOfPresheafYoneda` and `ofPresheaf.map`, which are contracted here into the
one step `overBasedToOfPresheaf`.

Build it with `lake build StacksAndModuli.mwe.AlgebraicSpacesAndStacks`; nothing imports it.
-/

@[expose] public section

-- The library-wide transparency options.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefPrestack

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Experimental supporting definition for Definition 3.4.1: a functor `p : 𝒳 ⥤ 𝒮` makes `𝒳` a *prestack*
over the category `𝒮` (in standard terminology, a *category fibered in groupoids*) if
(1) pullbacks exist: for every object `a` of `𝒳` and morphism `f : R ⟶ p(a)` in `𝒮` there
exists a morphism `φ : b ⟶ a` of `𝒳` lying over `f`; and (2) the universal property for
pullbacks holds: for every diagram of morphisms lying over a composition `R ⟶ S ⟶ T` in
`𝒮` there is a unique filling morphism over `R ⟶ S` — that is, every morphism of `𝒳` is
strongly cartesian. -/
class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) : Prop where
  /-- Pullbacks exist: every morphism into the image of `a` lifts to a morphism into `a`
  (Definition 3.4.1(1)). -/
  exists_isHomLift {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsHomLift p f φ
  /-- The universal property of pullbacks holds for every morphism: every morphism of `𝒳`
  is strongly cartesian (Definition 3.4.1(2)). -/
  isStronglyCartesian {a b : 𝒳} (φ : a ⟶ b) : IsStronglyCartesian p (p.map φ) φ

end CategoryTheory.Functor

end DefPrestack

section ExPresheavesArePrestacks

open CategoryTheory Functor

universe v u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u} [Category.{v} 𝒮]

/-- Experimental supporting example for Example 3.4.7: the prestack associated to a
presheaf `F` on `𝒮` — its objects are the pairs `(S, a)` with `S : 𝒮` and `a ∈ F(S)`,
written as costructured arrows `Mor(-, S) ⟶ F`, and its projection remembers `S`. -/
abbrev ofPresheaf (F : 𝒮ᵒᵖ ⥤ Type v) : BasedCategory 𝒮 where
  obj := CostructuredArrow yoneda F
  p := CostructuredArrow.proj yoneda F

end CategoryTheory.BasedCategory

end ExPresheavesArePrestacks

section ExRepresentablePrestacks

open CategoryTheory Functor

universe v₁ u₁

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Experimental supporting example for Example 3.4.8 (repackaged as a based category):
the prestack represented by an object `S : 𝒮` — the slice category `𝒮/S` with its
projection, as a based category over `𝒮`. -/
abbrev overBased (S : 𝒮) : BasedCategory 𝒮 where
  obj := Over S
  p := Over.forget S

end CategoryTheory.BasedCategory

end ExRepresentablePrestacks

section ConstrFiberProductPrestacks

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}

/-- Experimental supporting definition for Construction 3.4.33 (objects): an object of
the fiber product `𝒳 ×_𝒴 𝒴'` of two morphisms `F : 𝒳 ⥤ᵇ 𝒴` and `G : 𝒴' ⥤ᵇ 𝒴` of based
categories — a pair of objects `fst : 𝒳`, `snd : 𝒴'` lying over the same object of the
base, together with an isomorphism `iso : F(fst) ≅ G(snd)` lying over the identity. -/
structure FiberProductObj (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) where
  /-- The first component, an object of `𝒳`. -/
  fst : 𝒳.obj
  /-- The second component, an object of `𝒴'`. -/
  snd : 𝒴'.obj
  /-- The two components lie over the same object of the base. -/
  over_eq : 𝒴'.p.obj snd = 𝒳.p.obj fst
  /-- The comparison isomorphism `F(fst) ≅ G(snd)`. -/
  iso : F.obj fst ≅ G.obj snd
  /-- The comparison isomorphism lies over the identity. -/
  isHomLift : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj fst)) iso.hom

variable {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}

/-- Experimental supporting definition for Construction 3.4.33 (morphisms): a morphism of
the fiber product `𝒳 ×_𝒴 𝒴'` — a pair of morphisms in `𝒳` and `𝒴'` lying over a common
morphism of the base and compatible with the comparison isomorphisms. -/
@[ext]
structure FiberProductHom (a b : FiberProductObj F G) where
  /-- The first component. -/
  fst : a.fst ⟶ b.fst
  /-- The second component. -/
  snd : a.snd ⟶ b.snd
  /-- The second component lies over the image in the base of the first. -/
  isHomLift : IsHomLift 𝒴'.p (𝒳.p.map fst) snd
  /-- Compatibility with the comparison isomorphisms. -/
  w : F.map fst ≫ b.iso.hom = a.iso.hom ≫ G.map snd := by cat_disch

attribute [instance] FiberProductHom.isHomLift
attribute [reassoc] FiberProductHom.w

/-- The identity morphism of the fiber product. -/
@[simps]
def FiberProductHom.id (a : FiberProductObj F G) : FiberProductHom a a where
  fst := 𝟙 a.fst
  snd := 𝟙 a.snd
  isHomLift := by
    rw [𝒳.p.map_id]
    exact IsHomLift.id a.over_eq
  w := by simp

/-- Composition of morphisms of the fiber product. -/
@[simps]
def FiberProductHom.comp {a b c : FiberProductObj F G} (φ : FiberProductHom a b)
    (ψ : FiberProductHom b c) : FiberProductHom a c where
  fst := φ.fst ≫ ψ.fst
  snd := φ.snd ≫ ψ.snd
  isHomLift := by
    rw [𝒳.p.map_comp]
    infer_instance
  w := by
    rw [F.toFunctor.map_comp, G.toFunctor.map_comp, Category.assoc, ψ.w, φ.w_assoc]

instance FiberProductObj.instCategory : Category (FiberProductObj F G) where
  Hom a b := FiberProductHom a b
  id a := FiberProductHom.id a
  comp φ ψ := φ.comp ψ
  id_comp φ := by ext <;> simp
  comp_id φ := by ext <;> simp
  assoc φ ψ χ := by ext <;> simp

variable (F G) in
/-- Experimental supporting definition for Construction 3.4.33: the fiber product of two
morphisms `F : 𝒳 ⥤ᵇ 𝒴`, `G : 𝒴' ⥤ᵇ 𝒴` of based categories over `𝒮`, as a based category
over `𝒮` — an object over `S` is a triple `(x, y', γ)` of objects `x` of `𝒳` and `y'` of
`𝒴'` over `S` and an isomorphism `γ : F(x) ≅ G(y')` over the identity of `S`. -/
abbrev fiberProduct : BasedCategory.{max v₂ v₄, max u₂ u₄ v₃} 𝒮 where
  obj := FiberProductObj F G
  p :=
    { obj := fun a ↦ 𝒳.p.obj a.fst
      map := fun φ ↦ 𝒳.p.map (FiberProductHom.fst φ)
      map_id := fun a ↦ 𝒳.p.map_id a.fst
      map_comp := fun φ ψ ↦ 𝒳.p.map_comp (FiberProductHom.fst φ) (FiberProductHom.fst ψ) }

variable (F G) in
/-- Experimental supporting definition for Construction 3.4.33 (the second projection
`p₂`): the projection `𝒳 ×_𝒴 𝒴' ⥤ᵇ 𝒴'`, `(x, y', γ) ↦ y'`. -/
def fiberProductSnd : fiberProduct F G ⥤ᵇ 𝒴' where
  obj a := a.snd
  map φ := FiberProductHom.snd φ
  w := by
    refine Functor.ext_of_iso (NatIso.ofComponents (fun a ↦ eqToIso a.over_eq) ?_)
      (fun a ↦ a.over_eq)
    intro a b φ
    have h := IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst φ)) (FiberProductHom.snd φ)
    simp only [Functor.comp_map, h]
    simp

end CategoryTheory.BasedCategory

end ConstrFiberProductPrestacks

section DefStack

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Experimental supporting definition for Definition 3.5.1: let `𝒮` be a site and let `p : 𝒳 ⥤ 𝒮` be a
prestack (category fibered in groupoids). Then `𝒳` is a *stack* if for every covering
sieve `R` of an object `S`:

1. *(morphisms glue)* for objects `a, b` of `𝒳` over `S`, every family assigning to each
   `(g : T ⟶ S) ∈ R` and each lift `ξ : x ⟶ a` of `g` a morphism `φ ξ : x ⟶ b` over `g`,
   compatibly with restriction, arises from a unique morphism `Φ : a ⟶ b` over `𝟙 S` via
   `φ ξ = ξ ≫ Φ`;
2. *(objects glue)* every descent datum over `R` — a functor `D` from the full subcategory
   of `𝒮/S` of arrows of `R` to `𝒳` lying over the forgetful functor — is effective:
   there is an object `a` over `S` together with morphisms `ε f : D(f) ⟶ a` over `f`,
   natural in `f ∈ R`.

(The formulation by covering families `{Sᵢ ⟶ S}` with isomorphisms `αᵢⱼ` satisfying the
cocycle condition is the special case of the descent datum associated to the generated
sieve; in a category fibered in groupoids all morphisms are strongly cartesian, so no
cartesianness conditions appear.) -/
class IsStack (p : 𝒳 ⥤ 𝒮) [p.IsFiberedInGroupoids] (J : GrothendieckTopology 𝒮) :
    Prop where
  /-- Experimental supporting definition for Definition 3.5.1 (part (1), morphisms glue): morphisms glue
  uniquely along covering sieves. -/
  existsUnique_gluing_hom : ∀ {S : 𝒮} {R : Sieve S}, R ∈ J S →
    ∀ {a b : 𝒳}, p.obj a = S → p.obj b = S →
    ∀ (φ : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄, R g → ∀ ⦃x : 𝒳⦄ (ξ : x ⟶ a), IsHomLift p g ξ → (x ⟶ b)),
      (∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : 𝒳⦄ (ξ : x ⟶ a) (hξ : IsHomLift p g ξ),
        IsHomLift p g (φ hg ξ hξ)) →
      (∀ ⦃T' T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃h : T' ⟶ T⦄ ⦃x' x : 𝒳⦄ (χ : x' ⟶ x)
        (ξ : x ⟶ a) (hξ : IsHomLift p g ξ) (_hχ : IsHomLift p h χ),
        φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) →
      ∃! Φ : a ⟶ b, IsHomLift p (𝟙 S) Φ ∧
        ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : 𝒳⦄ (ξ : x ⟶ a) (hξ : IsHomLift p g ξ),
          φ hg ξ hξ = ξ ≫ Φ
  /-- Experimental supporting definition for Definition 3.5.1 (part (2), objects glue): every descent datum
  over a covering sieve is effective. -/
  exists_gluing_obj : ∀ {S : 𝒮} {R : Sieve S}, R ∈ J S →
    ∀ (D : R.arrows.category ⥤ 𝒳),
      (∀ f : R.arrows.category, p.obj (D.obj f) = f.obj.left) →
      (∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), IsHomLift p h.hom.left (D.map h)) →
      ∃ (a : 𝒳) (_ : p.obj a = S) (ε : ∀ f : R.arrows.category, D.obj f ⟶ a),
        (∀ f : R.arrows.category, IsHomLift p f.obj.hom (ε f)) ∧
        ∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), D.map h ≫ ε g = ε f

end CategoryTheory.Functor

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (J : GrothendieckTopology 𝒮)

/-- Experimental supporting definition for Definition 3.5.1 (based-category form): a based category `𝒳` over a
site `(𝒮, J)` is a stack if it is fibered in groupoids and satisfies the stack axioms. -/
class IsStack (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : Prop where
  isFiberedInGroupoids : 𝒳.p.IsFiberedInGroupoids
  isStack : 𝒳.p.IsStack J

attribute [instance] IsStack.isFiberedInGroupoids IsStack.isStack

end CategoryTheory.BasedCategory

end DefStack

section DefAlgebraicSpace

open CategoryTheory Functor AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Experimental supporting definition for Definition 4.1.2: let `X` be a presheaf on `Sch`. Then
`X` is an *algebraic space* if it is a sheaf for the étale topology and there exist a
scheme `U` and a morphism `U ⟶ X` which is representable by schemes, surjective, and
étale (an *étale presentation* of `X`).

"Representable by schemes with a property `P`" is Definition 4.1.1 at the level of
presheaves, which is Mathlib's
`MorphismProperty.presheaf`: every base change along a morphism from a scheme is a
morphism of schemes with `P`. -/
class IsAlgebraicSpace (X : Scheme.{u}ᵒᵖ ⥤ Type u) : Prop where
  isSheaf : Presieve.IsSheaf Scheme.etaleTopology X
  exists_presentation : ∃ (U : Scheme.{u}) (p : yoneda.obj U ⟶ X),
    MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p

end AlgebraicGeometry

end DefAlgebraicSpace

section DefRepresentableMorphisms

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The prestack morphism `𝒮/U ⥤ᵇ 𝒳_X` classified by a morphism `q : Mor(-, U) ⟶ X` of
presheaves: an object `f : T ⟶ U` of `𝒮/U` is sent to `Mor(-, f) ≫ q`. It is the
composition of the 2-Yoneda equivalence `𝒮/U ≃ 𝒳_{Mor(-, U)}` with the functoriality of
`X ↦ 𝒳_X`, spelled out in one step. -/
def overBasedToOfPresheaf {U : 𝒮} {X : 𝒮ᵒᵖ ⥤ Type v₁} (q : yoneda.obj U ⟶ X) :
    overBased U ⥤ᵇ ofPresheaf X where
  toFunctor :=
    { obj := fun f ↦ CostructuredArrow.mk (yoneda.map f.hom ≫ q)
      map := fun {f g} φ ↦ CostructuredArrow.homMk φ.left (by
        simp only [CostructuredArrow.mk_hom_eq_self]
        rw [← Category.assoc, ← yoneda.map_comp, Over.w φ]) }
  w := rfl

/-- Experimental supporting definition for Definition 4.1.1 (the implicit notion
of a prestack represented by a presheaf): a prestack `𝒳` over `𝒮` *is represented by* a
presheaf `F` on `𝒮` if there is an equivalence `𝒳_F → 𝒳` of prestacks, where `𝒳_F` is the
prestack associated to `F`. -/
def IsRepresentedByPresheaf (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (F : 𝒮ᵒᵖ ⥤ Type v₁) : Prop :=
  ∃ E : ofPresheaf F ⥤ᵇ 𝒳, E.toFunctor.IsEquivalence

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Let `S, T` be objects of a category `𝒮`. A morphism of representable prestacks
`F : 𝒮/S ⥤ᵇ 𝒮/T` determines a morphism `S ⟶ T` in `𝒮`, namely the structure morphism of
the object `F(𝟙 S)` of `𝒮/T`. By the 2-Yoneda lemma (Lemma 3.4.21)
this induces a bijection between 2-isomorphism classes of morphisms of prestacks
`𝒮/S ⥤ᵇ 𝒮/T` and morphisms `S ⟶ T`. -/
def overHom {S T : 𝒮} (F : overBased S ⥤ᵇ overBased T) : S ⟶ T :=
  eqToHom (F.w_obj (Over.mk (𝟙 S))).symm ≫ (F.obj (Over.mk (𝟙 S))).hom

end CategoryTheory.BasedFunctor

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Experimental supporting definition for Definition 4.1.3: let `F : 𝒳 ⥤ᵇ 𝒴` be a morphism
of prestacks over `Sch`. Then `F` is *representable* if for every scheme `T` and every
morphism `Sch/T ⥤ᵇ 𝒴` of prestacks, the fiber product `𝒳 ×_𝒴 Sch/T` is an algebraic
space. -/
def Representable (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴), ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u,
    IsAlgebraicSpace X ∧ (fiberProduct F g).IsRepresentedByPresheaf X

/-- Experimental supporting definition for Definition 4.1.3 (the "has property `P`"
refinement): let `P` be a property of morphisms of schemes stable under base change and
étale-local on the source, and let `F : 𝒳 ⥤ᵇ 𝒴` be a morphism of prestacks over `Sch`.
Then `F` is representable *with property `P`* if it is representable and for every
morphism `T ⟶ 𝒴` from a scheme, every realization of the fiber product `𝒳 ×_𝒴 Sch/T` as
an algebraic space `X`, and every étale presentation `U ⟶ X` by a scheme, the composition
`U ⟶ X ⟶ T` has property `P`. -/
def RepresentableWith (P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  Representable F ∧
    ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴) (X : Scheme.{u}ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace X → ∀ (E : ofPresheaf X ⥤ᵇ fiberProduct F g),
        E.toFunctor.IsEquivalence → ∀ (U : Scheme.{u}) (q : yoneda.obj U ⟶ X),
          MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
            q →
          P ((overBasedToOfPresheaf q).comp (E.comp (fiberProductSnd F g))).overHom

end AlgebraicGeometry.BasedFunctor

end DefRepresentableMorphisms

section DefDeligneMumfordStack

open CategoryTheory Functor CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- Experimental supporting definition for Definition 4.1.4: let `𝒳` be a stack over
`Sch_ét`. Then `𝒳` is a *Deligne–Mumford stack* if there exist a scheme `U` and a
surjective, étale, and representable morphism `U ⟶ 𝒳` (an *étale presentation*). -/
class IsDeligneMumfordStack (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop where
  isStack : BasedCategory.IsStack Scheme.etaleTopology 𝒳
  exists_presentation : ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) F

end AlgebraicGeometry

end DefDeligneMumfordStack

section DefAlgebraicStack

open CategoryTheory Functor CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- Experimental supporting definition for Definition 4.1.6: let `𝒳` be a stack over `Sch_ét`. Then
`𝒳` is an *algebraic stack* if there exist a scheme `U` and a surjective, smooth, and
representable morphism `U ⟶ 𝒳` (a *smooth presentation*).

In the literature most authors add a representability condition on the diagonal; as shown
in Theorem 4.2.1, the existence of a smooth
presentation already implies the representability of the diagonal, so no condition is
imposed here. -/
class IsAlgebraicStack (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop where
  isStack : BasedCategory.IsStack Scheme.etaleTopology 𝒳
  exists_presentation : ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F

end AlgebraicGeometry

end DefAlgebraicStack
