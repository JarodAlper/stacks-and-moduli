module

public import StacksAndModuli.«Section3.2-Sites».«part3.2.3-restricted-and-affine-sites»
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Groupoids and equivalence relations

This module formalizes **Definition 4.4.1** (`def:etale-groupoid`) and the unlabelled
remark "relations" following it, from §4.4 (Equivalence relations and groupoids) of
*Stacks and Moduli*, section
label `subsec:equivalence-relations`.

A groupoid `s, t : R ⇉ U` of schemes (or of algebraic spaces) is encoded once and for all at
the presheaf level: a `AlgebraicGeometry.PresheafGroupoid` bundles presheaves `U` and `R` on
`Sch`, source and target morphisms `s, t : R ⟶ U`, a composition defined pointwise on
composable pairs, an identity `e : U ⟶ R` and an inverse `inv : R ⟶ R`, together with the
groupoid axioms. Étale/smooth/fppf groupoids and equivalence relations are property mixins.

Main results:
- `AlgebraicGeometry.PresheafGroupoid`: groupoid objects in presheaves on `Sch`
  (**Definition 4.4.1**);
- `AlgebraicGeometry.PresheafGroupoid.IsEtale`, `.IsSmooth`: the source and target are
  representable by schemes and étale (resp. smooth);
- `AlgebraicGeometry.PresheafGroupoid.IsEquivalenceRelation`: `(s, t)` is pointwise
  injective;
- `AlgebraicGeometry.PresheafGroupoid.ofSchemes`: the groupoid of presheaves associated to
  a groupoid of schemes.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefEtaleGroupoid

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Definition 4.4.1** (`def:etale-groupoid`): a *groupoid object in presheaves* on the
category of schemes: presheaves `U` (of objects) and `R` (of relations) together with
source and target morphisms `s, t : R ⟶ U`, a composition defined pointwise on composable
pairs, an identity `e : U ⟶ R` and an inverse `inv : R ⟶ R`, satisfying the groupoid
axioms pointwise. An element `r ∈ R(T)` is viewed as a relation `r : s(r) → t(r)` between
elements of `U(T)`; a composable pair is a pair `(x, y)` with `s(x) = t(y)`, composing —
like functions — to `x ∘ y` with source `s(y)` and target `t(x)`.

This single notion covers the book's étale/smooth groupoids of schemes (via
`AlgebraicGeometry.PresheafGroupoid.ofSchemes` and the mixins
`AlgebraicGeometry.PresheafGroupoid.IsEtale` and `.IsSmooth`) and of algebraic spaces (by
requiring `AlgebraicGeometry.IsAlgebraicSpace` for `U` and `R`). The book quantifies the
identity and the inverse existentially; they are uniquely determined by `(s, t, comp)`
(the unlabelled exercise following Definition 4.4.7), so we record them as data — see
this folder's COMMENTARY.md. -/
@[pp_with_univ]
structure PresheafGroupoid where
  /-- The presheaf of objects. -/
  U : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- The presheaf of relations. -/
  R : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- The source morphism. -/
  s : R ⟶ U
  /-- The target morphism. -/
  t : R ⟶ U
  /-- Composition of a pointwise composable pair: for `x, y ∈ R(T)` with `s(x) = t(y)`, a
  relation `x ∘ y ∈ R(T)`. -/
  comp : ∀ {T : Scheme.{u}ᵒᵖ} (x y : R.obj T), s.app T x = t.app T y → R.obj T
  /-- The source of a composition is the source of the second factor. -/
  s_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x y : R.obj T) (h : s.app T x = t.app T y),
    s.app T (comp x y h) = s.app T y
  /-- The target of a composition is the target of the first factor. -/
  t_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x y : R.obj T) (h : s.app T x = t.app T y),
    t.app T (comp x y h) = t.app T x
  /-- Composition is compatible with restriction along morphisms of schemes. -/
  comp_naturality : ∀ {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T') (x y : R.obj T)
    (h : s.app T x = t.app T y) (h' : s.app T' (R.map f x) = t.app T' (R.map f y)),
    R.map f (comp x y h) = comp (R.map f x) (R.map f y) h'
  /-- Composition is associative (Definition 4.4.1, part (1)). -/
  comp_assoc : ∀ {T : Scheme.{u}ᵒᵖ} (x y z : R.obj T) (hxy : s.app T x = t.app T y)
    (hyz : s.app T y = t.app T z) (h₁ : s.app T (comp x y hxy) = t.app T z)
    (h₂ : s.app T x = t.app T (comp y z hyz)),
    comp (comp x y hxy) z h₁ = comp x (comp y z hyz) h₂
  /-- The identity morphism (Definition 4.4.1, part (2)). -/
  e : U ⟶ R
  /-- The source of an identity relation `e(u)` is `u`. -/
  e_s : e ≫ s = 𝟙 U
  /-- The target of an identity relation `e(u)` is `u`. -/
  e_t : e ≫ t = 𝟙 U
  /-- Right unit law: `x ∘ e(s(x)) = x` (Definition 4.4.1, part (2)). -/
  comp_e : ∀ {T : Scheme.{u}ᵒᵖ} (x : R.obj T)
    (h : s.app T x = t.app T (e.app T (s.app T x))), comp x (e.app T (s.app T x)) h = x
  /-- Left unit law: `e(t(x)) ∘ x = x` (Definition 4.4.1, part (2)). -/
  e_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x : R.obj T)
    (h : s.app T (e.app T (t.app T x)) = t.app T x), comp (e.app T (t.app T x)) x h = x
  /-- The inverse morphism (Definition 4.4.1, part (3)). -/
  inv : R ⟶ R
  /-- The source of the inverse of a relation is its target. -/
  inv_s : inv ≫ s = t
  /-- The target of the inverse of a relation is its source. -/
  inv_t : inv ≫ t = s
  /-- Left inverse law: `x⁻¹ ∘ x = e(s(x))` (Definition 4.4.1, part (3)). -/
  inv_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x : R.obj T)
    (h : s.app T (inv.app T x) = t.app T x), comp (inv.app T x) x h = e.app T (s.app T x)
  /-- Right inverse law: `x ∘ x⁻¹ = e(t(x))` (Definition 4.4.1, part (3)). -/
  comp_inv : ∀ {T : Scheme.{u}ᵒᵖ} (x : R.obj T)
    (h : s.app T x = t.app T (inv.app T x)), comp x (inv.app T x) h = e.app T (t.app T x)

attribute [simp] PresheafGroupoid.s_comp PresheafGroupoid.t_comp

namespace PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u}) {T T' : Scheme.{u}ᵒᵖ}

/-- The source of an identity relation `e(a)` is `a` (pointwise form of
`PresheafGroupoid.e_s`). -/
@[simp]
lemma s_app_e_app (a : 𝒢.U.obj T) : 𝒢.s.app T (𝒢.e.app T a) = a := by
  rw [← NatTrans.comp_app_apply, 𝒢.e_s, NatTrans.id_app, types_id_apply]

/-- The target of an identity relation `e(a)` is `a` (pointwise form of
`PresheafGroupoid.e_t`). -/
@[simp]
lemma t_app_e_app (a : 𝒢.U.obj T) : 𝒢.t.app T (𝒢.e.app T a) = a := by
  rw [← NatTrans.comp_app_apply, 𝒢.e_t, NatTrans.id_app, types_id_apply]

/-- The source of the inverse of a relation is its target (pointwise form of
`PresheafGroupoid.inv_s`). -/
@[simp]
lemma s_app_inv_app (x : 𝒢.R.obj T) : 𝒢.s.app T (𝒢.inv.app T x) = 𝒢.t.app T x := by
  rw [← NatTrans.comp_app_apply, 𝒢.inv_s]

/-- The target of the inverse of a relation is its source (pointwise form of
`PresheafGroupoid.inv_t`). -/
@[simp]
lemma t_app_inv_app (x : 𝒢.R.obj T) : 𝒢.t.app T (𝒢.inv.app T x) = 𝒢.s.app T x := by
  rw [← NatTrans.comp_app_apply, 𝒢.inv_t]

/-- Restriction commutes with the source: `s(f*x) = f*(s(x))` (pointwise naturality of
`PresheafGroupoid.s`). -/
@[simp]
lemma s_app_map (f : T ⟶ T') (x : 𝒢.R.obj T) :
    𝒢.s.app T' (𝒢.R.map f x) = 𝒢.U.map f (𝒢.s.app T x) :=
  NatTrans.naturality_apply 𝒢.s f x

/-- Restriction commutes with the target: `t(f*x) = f*(t(x))` (pointwise naturality of
`PresheafGroupoid.t`). -/
@[simp]
lemma t_app_map (f : T ⟶ T') (x : 𝒢.R.obj T) :
    𝒢.t.app T' (𝒢.R.map f x) = 𝒢.U.map f (𝒢.t.app T x) :=
  NatTrans.naturality_apply 𝒢.t f x

/-- Restriction commutes with the identity: `f*(e(a)) = e(f*a)` (pointwise naturality of
`PresheafGroupoid.e`). -/
@[simp]
lemma map_e_app (f : T ⟶ T') (a : 𝒢.U.obj T) :
    𝒢.R.map f (𝒢.e.app T a) = 𝒢.e.app T' (𝒢.U.map f a) :=
  (NatTrans.naturality_apply 𝒢.e f a).symm

/-- Restriction commutes with the inverse: `f*(x⁻¹) = (f*x)⁻¹` (pointwise naturality of
`PresheafGroupoid.inv`). -/
@[simp]
lemma map_inv_app (f : T ⟶ T') (x : 𝒢.R.obj T) :
    𝒢.R.map f (𝒢.inv.app T x) = 𝒢.inv.app T' (𝒢.R.map f x) :=
  (NatTrans.naturality_apply 𝒢.inv f x).symm

/-- Right unit law in flexible form: `x ∘ e(a) = x` for any `a` (necessarily `a = s(x)`). -/
@[simp]
lemma comp_e_app (x : 𝒢.R.obj T) (a : 𝒢.U.obj T)
    (h : 𝒢.s.app T x = 𝒢.t.app T (𝒢.e.app T a)) : 𝒢.comp x (𝒢.e.app T a) h = x := by
  obtain rfl : a = 𝒢.s.app T x := by simpa using h.symm
  exact 𝒢.comp_e x h

/-- Left unit law in flexible form: `e(a) ∘ x = x` for any `a` (necessarily `a = t(x)`). -/
@[simp]
lemma e_app_comp (x : 𝒢.R.obj T) (a : 𝒢.U.obj T)
    (h : 𝒢.s.app T (𝒢.e.app T a) = 𝒢.t.app T x) : 𝒢.comp (𝒢.e.app T a) x h = x := by
  obtain rfl : a = 𝒢.t.app T x := by simpa using h
  exact 𝒢.e_comp x h

/-- Composing with the inverse cancels: `x⁻¹ ∘ (x ∘ y) = y`. -/
@[simp]
lemma inv_comp_comp (x y : 𝒢.R.obj T) (hxy : 𝒢.s.app T x = 𝒢.t.app T y)
    (h : 𝒢.s.app T (𝒢.inv.app T x) = 𝒢.t.app T (𝒢.comp x y hxy)) :
    𝒢.comp (𝒢.inv.app T x) (𝒢.comp x y hxy) h = y := by
  rw [← 𝒢.comp_assoc (𝒢.inv.app T x) x y (by simp) hxy (by simp [hxy]) h]
  simp only [𝒢.inv_comp]
  exact 𝒢.e_app_comp y _ _

/-- Composing with the inverse cancels: `x ∘ (x⁻¹ ∘ y) = y`. -/
@[simp]
lemma comp_inv_comp (x y : 𝒢.R.obj T) (hxy : 𝒢.s.app T (𝒢.inv.app T x) = 𝒢.t.app T y)
    (h : 𝒢.s.app T x = 𝒢.t.app T (𝒢.comp (𝒢.inv.app T x) y hxy)) :
    𝒢.comp x (𝒢.comp (𝒢.inv.app T x) y hxy) h = y := by
  rw [← 𝒢.comp_assoc x (𝒢.inv.app T x) y (by simp) hxy (by simp [hxy]) h]
  simp only [𝒢.comp_inv]
  exact 𝒢.e_app_comp y _ _

/-- Left cancellation: if `x ∘ y = x ∘ y'` then `y = y'`. -/
lemma comp_left_cancel {x y y' : 𝒢.R.obj T} (hxy : 𝒢.s.app T x = 𝒢.t.app T y)
    (hxy' : 𝒢.s.app T x = 𝒢.t.app T y')
    (h : 𝒢.comp x y hxy = 𝒢.comp x y' hxy') : y = y' := by
  have h₁ := 𝒢.inv_comp_comp x y hxy (by simp)
  have h₂ := 𝒢.inv_comp_comp x y' hxy' (by simp)
  rw [← h₁, ← h₂]
  congr 1

/-- API lemma for Definition 4.4.1 (the inverse is an involution): in a
groupoid of presheaves, `(r⁻¹)⁻¹ = r`. -/
@[simp]
lemma inv_inv_app {T : Scheme.{u}ᵒᵖ} (x : 𝒢.R.obj T) :
    𝒢.inv.app T (𝒢.inv.app T x) = x := by
  refine 𝒢.comp_left_cancel (x := 𝒢.inv.app T x) (by simp) (by simp) ?_
  rw [𝒢.comp_inv (𝒢.inv.app T x) (by simp), 𝒢.inv_comp x (by simp)]
  simp

/-- **Definition 4.4.1** (`def:etale-groupoid`) (equivalence relations): let `𝒢` be a
groupoid of presheaves on `Sch`. Then `𝒢` is an *equivalence relation* if the morphism
`(s, t) : R → U × U` is a monomorphism, i.e. a relation is determined by its source and
target: there is at most one relation between any two elements of `U(T)`. -/
def IsEquivalenceRelation : Prop :=
  ∀ ⦃T : Scheme.{u}ᵒᵖ⦄ ⦃x y : 𝒢.R.obj T⦄,
    𝒢.s.app T x = 𝒢.s.app T y → 𝒢.t.app T x = 𝒢.t.app T y → x = y

/-- **Definition 4.4.1** (`def:etale-groupoid`) (étale groupoids): let `𝒢` be a groupoid
of presheaves on `Sch`. Then `𝒢` is an *étale groupoid* if its source and target are
representable by schemes and étale. (For a groupoid of algebraic spaces the
representability by schemes is automatic, by Corollary 4.2.3; we include it in the
mixin.) -/
class IsEtale (𝒢 : PresheafGroupoid.{u}) : Prop where
  /-- The source is representable by schemes and étale. -/
  presheaf_s : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u}) 𝒢.s
  /-- The target is representable by schemes and étale. -/
  presheaf_t : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u}) 𝒢.t

/-- **Definition 4.4.1** (`def:etale-groupoid`) (smooth groupoids): let `𝒢` be a groupoid
of presheaves on `Sch`. Then `𝒢` is a *smooth groupoid* if its source and target are
representable by schemes and smooth. -/
class IsSmooth (𝒢 : PresheafGroupoid.{u}) : Prop where
  /-- The source is representable by schemes and smooth. -/
  presheaf_s : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u}) 𝒢.s
  /-- The target is representable by schemes and smooth. -/
  presheaf_t : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u}) 𝒢.t

/-- Background definition used in Remark 4.4.14 (an fppf groupoid, stated as a variant
of Definition 4.4.1): let `𝒢` be a groupoid of
presheaves on `Sch`. Then `𝒢` is an *fppf groupoid* if its source and target are
representable by schemes, flat, and locally of finite presentation. -/
class IsFppf (𝒢 : PresheafGroupoid.{u}) : Prop where
  /-- The source is representable by schemes, flat and locally of finite presentation. -/
  presheaf_s : MorphismProperty.presheaf
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) 𝒢.s
  /-- The target is representable by schemes, flat and locally of finite presentation. -/
  presheaf_t : MorphismProperty.presheaf
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) 𝒢.t

/-- Supporting instance for Definition 4.4.1 (étale groupoids are smooth): an étale
groupoid of presheaves is smooth. -/
instance (priority := 900) IsSmooth.of_isEtale [𝒢.IsEtale] : 𝒢.IsSmooth where
  presheaf_s := MorphismProperty.relative_monotone etale_le_smooth _ IsEtale.presheaf_s
  presheaf_t := MorphismProperty.relative_monotone etale_le_smooth _ IsEtale.presheaf_t

section OfSchemes

variable {U₀ R₀ : Scheme.{u}} (s t : R₀ ⟶ U₀) (c : pullback s t ⟶ R₀) (e : U₀ ⟶ R₀)
  (i : R₀ ⟶ R₀)

variable (hcs : c ≫ s = pullback.snd s t ≫ s) (hct : c ≫ t = pullback.fst s t ≫ t)
  (hes : e ≫ s = 𝟙 U₀) (het : e ≫ t = 𝟙 U₀) (his : i ≫ s = t) (hit : i ≫ t = s)

variable (hassoc : ∀ {T : Scheme.{u}} (x y z : T ⟶ R₀) (hxy : x ≫ s = y ≫ t)
    (hyz : y ≫ s = z ≫ t) (h₁ : (pullback.lift x y hxy ≫ c) ≫ s = z ≫ t)
    (h₂ : x ≫ s = (pullback.lift y z hyz ≫ c) ≫ t),
    pullback.lift (pullback.lift x y hxy ≫ c) z h₁ ≫ c =
      pullback.lift x (pullback.lift y z hyz ≫ c) h₂ ≫ c)

variable (hce : ∀ {T : Scheme.{u}} (x : T ⟶ R₀) (h : x ≫ s = (x ≫ s ≫ e) ≫ t),
    pullback.lift x (x ≫ s ≫ e) h ≫ c = x)

variable (hec : ∀ {T : Scheme.{u}} (x : T ⟶ R₀) (h : (x ≫ t ≫ e) ≫ s = x ≫ t),
    pullback.lift (x ≫ t ≫ e) x h ≫ c = x)

variable (hic : ∀ {T : Scheme.{u}} (x : T ⟶ R₀) (h : (x ≫ i) ≫ s = x ≫ t),
    pullback.lift (x ≫ i) x h ≫ c = x ≫ s ≫ e)

variable (hci : ∀ {T : Scheme.{u}} (x : T ⟶ R₀) (h : x ≫ s = (x ≫ i) ≫ t),
    pullback.lift x (x ≫ i) h ≫ c = x ≫ t ≫ e)

/-- **Definition 4.4.1** (`def:etale-groupoid`) (groupoids of schemes): the groupoid of
presheaves associated to a groupoid of schemes: given schemes `U₀`, `R₀`, source and
target `s, t : R₀ ⟶ U₀`, a composition `c : R₀ ×_{s, U₀, t} R₀ ⟶ R₀`, an identity
`e : U₀ ⟶ R₀` and an inverse `i : R₀ ⟶ R₀` satisfying the groupoid axioms of schemes
(stated on `T`-points, which is equivalent to the commutativity of the diagrams of schemes
by the Yoneda lemma), the groupoid of presheaves `Mor(-, R₀) ⇉ Mor(-, U₀)` acting on
`T`-points by composition of relations. -/
noncomputable def ofSchemes : PresheafGroupoid.{u} where
  U := yoneda.obj U₀
  R := yoneda.obj R₀
  s := yoneda.map s
  t := yoneda.map t
  comp {T} x y h := pullback.lift x y h ≫ c
  s_comp {T} x y h := by
    change (pullback.lift x y h ≫ c) ≫ s = y ≫ s
    rw [Category.assoc, hcs, pullback.lift_snd_assoc]
  t_comp {T} x y h := by
    change (pullback.lift x y h ≫ c) ≫ t = x ≫ t
    rw [Category.assoc, hct, pullback.lift_fst_assoc]
  comp_naturality {T T'} f x y h h' := by
    change f.unop ≫ pullback.lift x y h ≫ c = pullback.lift (f.unop ≫ x) (f.unop ≫ y) h' ≫ c
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  comp_assoc {T} x y z hxy hyz h₁ h₂ := hassoc x y z hxy hyz h₁ h₂
  e := yoneda.map e
  e_s := by rw [← yoneda.map_comp, hes, yoneda.map_id]
  e_t := by rw [← yoneda.map_comp, het, yoneda.map_id]
  comp_e {T} x h := by
    change pullback.lift x ((x ≫ s) ≫ e) _ ≫ c = x
    simp only [Category.assoc]
    exact hce x _
  e_comp {T} x h := by
    change pullback.lift ((x ≫ t) ≫ e) x _ ≫ c = x
    simp only [Category.assoc]
    exact hec x _
  inv := yoneda.map i
  inv_s := by rw [← yoneda.map_comp, his]
  inv_t := by rw [← yoneda.map_comp, hit]
  inv_comp {T} x h := by
    change pullback.lift (x ≫ i) x _ ≫ c = (x ≫ s) ≫ e
    rw [Category.assoc]
    exact hic x _
  comp_inv {T} x h := by
    change pullback.lift x (x ≫ i) _ ≫ c = (x ≫ t) ≫ e
    rw [Category.assoc]
    exact hci x _

/-- Let `C` be a category with pullbacks and `P` a property of morphisms of `C` stable
under base change. Then `P` transfers from a morphism of `C` to the associated morphism
of presheaves (which is relatively representable, since the Yoneda embedding preserves
fiber products). For `C = Sch` this transfers étaleness or smoothness of a morphism of
schemes to the corresponding morphism of functors of points. -/
lemma _root_.CategoryTheory.MorphismProperty.presheaf_yoneda_map {C : Type*} [Category C]
    [Limits.HasPullbacks C] {P : MorphismProperty C} [P.IsStableUnderBaseChange]
    {X Y : C} {f : X ⟶ Y} (hf : P f) : P.presheaf (yoneda.map f) :=
  MorphismProperty.relative_map hf

/-- Supporting transfer lemma for Definition 4.4.1 (étale groupoids of schemes): the groupoid
of presheaves associated to an étale groupoid of schemes is an étale groupoid. -/
lemma ofSchemes_isEtale [Etale s] [Etale t] :
    (ofSchemes s t c e i hcs hct hes het his hit hassoc hce hec hic hci).IsEtale where
  presheaf_s := MorphismProperty.presheaf_yoneda_map ‹Etale s›
  presheaf_t := MorphismProperty.presheaf_yoneda_map ‹Etale t›

/-- Supporting transfer lemma for Definition 4.4.1 (smooth groupoids of schemes): the
groupoid of presheaves associated to a smooth groupoid of schemes is a smooth groupoid. -/
lemma ofSchemes_isSmooth [Smooth s] [Smooth t] :
    (ofSchemes s t c e i hcs hct hes het his hit hassoc hce hec hic hci).IsSmooth where
  presheaf_s := MorphismProperty.presheaf_yoneda_map ‹Smooth s›
  presheaf_t := MorphismProperty.presheaf_yoneda_map ‹Smooth t›

/-- Supporting transfer lemma for Definition 4.4.1 (equivalence relations of schemes): if
`(s, t) : R₀ → U₀ × U₀` is a monomorphism (stated on `T`-points), the associated groupoid
of presheaves is an equivalence relation. -/
lemma ofSchemes_isEquivalenceRelation
    (hmono : ∀ {T : Scheme.{u}} (x y : T ⟶ R₀), x ≫ s = y ≫ s → x ≫ t = y ≫ t → x = y) :
    IsEquivalenceRelation
      (ofSchemes s t c e i hcs hct hes het his hit hassoc hce hec hic hci) := by
  intro T x y hs ht
  exact hmono x y hs ht

end OfSchemes

end PresheafGroupoid

end AlgebraicGeometry

end DefEtaleGroupoid

section RmkRelations

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u}) (T : Scheme.{u}ᵒᵖ)

/-- Background definition from the unnumbered "relations" remark in §4.4
following Definition 4.4.1): the set of `T`-points of the presheaf of objects of a
groupoid of presheaves, regarded as the objects of the groupoid of sets `R(T) ⇉ U(T)`: a
point `r ∈ R(T)` is a relation `r : s(r) → t(r)` between elements of `U(T)`. -/
def Fiber : Type u := 𝒢.U.obj T

variable {𝒢} {T}

/-- Background definition from the unnumbered "relations" remark in §4.4
following Definition 4.4.1): a morphism `a → b` in the groupoid of `T`-points of a
groupoid of presheaves: a relation `r ∈ R(T)` with source `a` and target `b`. -/
structure FiberHom (a b : 𝒢.Fiber T) where
  /-- The underlying relation. -/
  rel : 𝒢.R.obj T
  /-- The source of the relation is the domain. -/
  s_rel : 𝒢.s.app T rel = a
  /-- The target of the relation is the codomain. -/
  t_rel : 𝒢.t.app T rel = b

/-- Morphisms in the groupoid of `T`-points are determined by their underlying relation. -/
@[ext]
lemma FiberHom.ext {a b : 𝒢.Fiber T} {φ ψ : FiberHom a b} (h : φ.rel = ψ.rel) : φ = ψ := by
  cases φ
  cases ψ
  subst h
  rfl

/-- Supporting instance for the unnumbered "relations" remark in §4.4
following Definition 4.4.1): the `T`-points of a groupoid of presheaves form a groupoid of
sets, with objects `U(T)`, morphisms the relations in `R(T)`, composition induced by the
groupoid composition, and inverses induced by the groupoid inverse. -/
instance instGroupoidFiber : Groupoid (𝒢.Fiber T) where
  Hom a b := FiberHom a b
  id a := ⟨𝒢.e.app T a, by simp, by simp⟩
  comp {a b c} φ ψ :=
    ⟨𝒢.comp ψ.rel φ.rel (ψ.s_rel.trans φ.t_rel.symm), by simp [φ.s_rel], by simp [ψ.t_rel]⟩
  id_comp {a b} φ := by
    apply FiberHom.ext
    exact 𝒢.comp_e_app φ.rel a _
  comp_id {a b} φ := by
    apply FiberHom.ext
    exact 𝒢.e_app_comp φ.rel b _
  assoc {a b c d} φ ψ χ := by
    apply FiberHom.ext
    exact (𝒢.comp_assoc χ.rel ψ.rel φ.rel (χ.s_rel.trans ψ.t_rel.symm)
      (ψ.s_rel.trans φ.t_rel.symm) (by simp [ψ.s_rel, φ.t_rel])
      (by simp [χ.s_rel, ψ.t_rel])).symm
  inv {a b} φ := ⟨𝒢.inv.app T φ.rel, by simp [φ.t_rel], by simp [φ.s_rel]⟩
  inv_comp {a b} φ := by
    apply FiberHom.ext
    have h := 𝒢.comp_inv φ.rel (by simp)
    simpa [φ.t_rel] using h
  comp_inv {a b} φ := by
    apply FiberHom.ext
    have h := 𝒢.inv_comp φ.rel (by simp)
    simpa [φ.s_rel] using h

/-- The relation underlying the identity morphism of the groupoid of `T`-points is the
identity relation. -/
@[simp]
lemma id_rel (a : 𝒢.Fiber T) : FiberHom.rel (𝟙 a) = 𝒢.e.app T a :=
  rfl

/-- The relation underlying a composition in the groupoid of `T`-points is the composition
of the underlying relations. -/
@[simp]
lemma comp_rel {a b c : 𝒢.Fiber T} (φ : a ⟶ b) (ψ : b ⟶ c) :
    FiberHom.rel (φ ≫ ψ) = 𝒢.comp ψ.rel φ.rel (ψ.s_rel.trans φ.t_rel.symm) :=
  rfl

/-- The relation underlying the inverse of a morphism in the groupoid of `T`-points is the
inverse of the underlying relation. -/
@[simp]
lemma inv_rel {a b : 𝒢.Fiber T} (φ : a ⟶ b) :
    FiberHom.rel (Groupoid.inv φ) = 𝒢.inv.app T φ.rel :=
  rfl

/-- API lemma for the unnumbered "relations" remark in §4.4
following Definition 4.4.1, the equivalence-relation case): in the groupoid of `T`-points
of an equivalence relation there is at most one morphism between any two objects. -/
lemma IsEquivalenceRelation.subsingleton_fiberHom (h𝒢 : 𝒢.IsEquivalenceRelation)
    (a b : 𝒢.Fiber T) : Subsingleton (a ⟶ b) := by
  constructor
  intro φ ψ
  exact FiberHom.ext (h𝒢 (φ.s_rel.trans ψ.s_rel.symm) (φ.t_rel.trans ψ.t_rel.symm))

end AlgebraicGeometry.PresheafGroupoid

end RmkRelations
