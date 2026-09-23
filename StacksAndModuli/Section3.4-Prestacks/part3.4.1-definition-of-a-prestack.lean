module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid

/-!
# Prestacks (categories fibered in groupoids)

This module formalizes the definition of a prestack of §3.4 (Prestacks) of *Stacks and
Moduli*, label `sec:prestacks`.

A *prestack* over a category `𝒮` — in standard terminology, a *category fibered in
groupoids* — is a functor `p : 𝒳 ⥤ 𝒮` such that (1) pullbacks exist: for every object `a`
of `𝒳` and morphism `f : R ⟶ p.obj a` there is a morphism to `a` lying over `f`; and
(2) every commutative triangle fills uniquely: every morphism of `𝒳` is strongly cartesian.
This builds directly on Mathlib's fibered-category library
(`CategoryTheory.Functor.IsHomLift`, `IsStronglyCartesian`, `IsFibered`, `Fiber`).

Main declarations:
- `CategoryTheory.Functor.IsFiberedInGroupoids`: the prestack axioms for a functor
  `p : 𝒳 ⥤ 𝒮`;
- `CategoryTheory.Functor.IsFiberedInGroupoids.isFibered`: a prestack is a fibered
  category (instance);
- `CategoryTheory.Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id` and the
  `Groupoid (p.Fiber S)` instance: the fiber categories of a prestack are groupoids;
- `CategoryTheory.Functor.IsFiberedInGroupoids.of_isFibered_of_isIso`: conversely, a
  fibered category all of whose fiber morphisms are isomorphisms is fibered in groupoids.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefPrestack

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- **Definition 3.4.1** (`def:prestack`): a functor `p : 𝒳 ⥤ 𝒮` makes `𝒳` a *prestack*
over the category `𝒮` (in standard terminology, a *category fibered in groupoids*) if
(1) pullbacks exist: for every object `a` of `𝒳` and morphism `f : R ⟶ p(a)` in `𝒮` there
exists a morphism `φ : b ⟶ a` of `𝒳` lying over `f`; and (2) the universal property for
pullbacks holds: for every diagram of morphisms lying over a composition `R ⟶ S ⟶ T` in
`𝒮` there is a unique filling morphism over `R ⟶ S` — that is, every morphism of `𝒳` is
strongly cartesian. -/
class IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) : Prop where
  /-- Pullbacks exist: every morphism into the image of `a` lifts to a morphism into `a`
  (part (1) of Definition 3.4.1). -/
  exists_isHomLift {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsHomLift p f φ
  /-- The universal property of pullbacks holds for every morphism: every morphism of `𝒳`
  is strongly cartesian (part (2) of Definition 3.4.1). -/
  isStronglyCartesian {a b : 𝒳} (φ : a ⟶ b) : IsStronglyCartesian p (p.map φ) φ

namespace IsFiberedInGroupoids

variable (p : 𝒳 ⥤ 𝒮) [p.IsFiberedInGroupoids]

instance isStronglyCartesian_of_isHomLift {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsHomLift p f φ] : IsStronglyCartesian p f φ := by
  subst_hom_lift p f φ
  exact IsFiberedInGroupoids.isStronglyCartesian φ

/-- Supporting equivalence following Definition 3.4.1 (forward direction): a prestack is a fibered category —
every morphism of the base admits a strongly cartesian lift. In the book's words, a
prestack is a fibered category in which every arrow is cartesian. -/
instance isFibered : p.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b, φ, hφ⟩ := IsFiberedInGroupoids.exists_isHomLift (p := p) f
  exact ⟨b, φ, inferInstance⟩

variable {p}

/-- API construction following Definition 3.4.1: two pullback arrows of the same object along the same base
morphism have canonically isomorphic domains.  The isomorphism lies over the
identity of the source in the base. -/
noncomputable def pullbackDomainUniqueUpToIso {R : 𝒮} {a a' b : 𝒳}
    (f : R ⟶ p.obj b) (φ : a ⟶ b) [IsHomLift p f φ]
    (ψ : a' ⟶ b) [IsHomLift p f ψ] : a' ≅ a :=
  IsCartesian.domainUniqueUpToIso p f φ ψ

instance pullbackDomainUniqueUpToIso_hom_isHomLift {R : 𝒮} {a a' b : 𝒳}
    (f : R ⟶ p.obj b) (φ : a ⟶ b) [IsHomLift p f φ]
    (ψ : a' ⟶ b) [IsHomLift p f ψ] :
    IsHomLift p (𝟙 R) (pullbackDomainUniqueUpToIso (p := p) f φ ψ).hom :=
  IsCartesian.domainUniqueUpToIso_inv_isHomLift p f φ ψ

@[reassoc]
lemma pullbackDomainUniqueUpToIso_hom_comp {R : 𝒮} {a a' b : 𝒳}
    (f : R ⟶ p.obj b) (φ : a ⟶ b) [IsHomLift p f φ]
    (ψ : a' ⟶ b) [IsHomLift p f ψ] :
    (pullbackDomainUniqueUpToIso (p := p) f φ ψ).hom ≫ φ = ψ :=
  IsCartesian.fac p f φ ψ

/-- API lemma following Definition 3.4.1 (uniqueness): the comparison between two choices of a pullback
is the unique isomorphism over the identity whose composite with one pullback arrow
is the other. -/
lemma pullbackDomainUniqueUpToIso_unique {R : 𝒮} {a a' b : 𝒳}
    (f : R ⟶ p.obj b) (φ : a ⟶ b) [IsHomLift p f φ]
    (ψ : a' ⟶ b) [IsHomLift p f ψ] (e : a' ≅ a)
    [IsHomLift p (𝟙 R) e.hom] (he : e.hom ≫ φ = ψ) :
    e = pullbackDomainUniqueUpToIso (p := p) f φ ψ := by
  apply Iso.ext
  exact IsCartesian.map_uniq p f φ ψ e.hom he


/-- Background definition from Section 3.4 (fiber categories):
the fiber category `𝒳(S)` of a prestack `p : 𝒳 ⟶ 𝒮` is Mathlib's category
`p.Fiber S`, whose objects lie over `S` and whose arrows lie over `𝟙 S`. -/
abbrev PrestackFiber (S : 𝒮) := p.Fiber S

/-- In a prestack, a morphism lying over an isomorphism of the base is an isomorphism. -/
lemma isIso_of_isHomLift_isIso {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) [IsIso f] (φ : a ⟶ b)
    [IsHomLift p f φ] : IsIso φ :=
  IsStronglyCartesian.isIso_of_base_isIso p f φ

/-- Helper lemma for the unlabeled exercise in Section 3.4 following the definition of
fiber categories): in a prestack, a morphism lying over an identity is an isomorphism —
the key step in showing that the fiber categories of a prestack are groupoids. -/
lemma isIso_of_isHomLift_id {S : 𝒮} {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    IsIso φ :=
  isIso_of_isHomLift_isIso (p := p) (𝟙 S) φ

/-- Morphisms of the fiber categories of a prestack are isomorphisms. -/
instance {S : 𝒮} {a b : p.Fiber S} (φ : a ⟶ b) : IsIso φ := by
  have h2 := φ.2
  have : IsIso φ.val := isIso_of_isHomLift_id (p := p) (S := S) φ.val
  refine ⟨⟨⟨CategoryTheory.inv φ.val, inferInstance⟩, ?_, ?_⟩⟩
  · exact Subtype.ext (IsIso.hom_inv_id φ.val)
  · exact Subtype.ext (IsIso.inv_hom_id φ.val)

/-- Result of the unlabeled exercise in Section 3.4 following the definition of
fiber categories): the fiber categories `𝒳(S)` of a prestack are groupoids. -/
noncomputable instance (S : 𝒮) : Groupoid (p.Fiber S) :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

end IsFiberedInGroupoids

/-- Supporting equivalence following Definition 3.4.1 (reverse direction): a fibered category all of whose fiber
morphisms are isomorphisms is fibered in groupoids — a fibered category whose fiber
categories are groupoids is a prestack. -/
lemma IsFiberedInGroupoids.of_isFibered_of_isIso (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
    (h : ∀ (S : 𝒮) (a b : p.Fiber S) (φ : a ⟶ b), IsIso φ) :
    p.IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) f
    exact ⟨b, φ, inferInstance⟩
  isStronglyCartesian {a b} φ := by
    -- factor `φ` as a fiber morphism `χ` followed by a strongly cartesian lift `ψ`
    obtain ⟨c, ψ, hψ⟩ := IsPreFibered.exists_isCartesian' (p := p) (p.map φ)
    have hsψ : IsStronglyCartesian p (p.map φ) ψ := inferInstance
    have hfac : IsCartesian.map p (p.map φ) ψ φ ≫ ψ = φ := IsCartesian.fac p (p.map φ) ψ φ
    have hχiso : IsIso (IsCartesian.map p (p.map φ) ψ φ) := by
      have := h (p.obj a) _ _ (Fiber.homMk p (p.obj a) (IsCartesian.map p (p.map φ) ψ φ))
      exact inferInstanceAs
        (IsIso (Fiber.fiberInclusion.map (Fiber.homMk p (p.obj a)
          (IsCartesian.map p (p.map φ) ψ φ))))
    have hχ : IsStronglyCartesian p (𝟙 (p.obj a)) (IsCartesian.map p (p.map φ) ψ φ) :=
      IsStronglyCartesian.of_isIso p (𝟙 (p.obj a)) _
    have hcomp : IsStronglyCartesian p (𝟙 (p.obj a) ≫ p.map φ)
        (IsCartesian.map p (p.map φ) ψ φ ≫ ψ) := inferInstance
    rw [Category.id_comp] at hcomp
    simpa only [hfac] using hcomp

end CategoryTheory.Functor

end DefPrestack
