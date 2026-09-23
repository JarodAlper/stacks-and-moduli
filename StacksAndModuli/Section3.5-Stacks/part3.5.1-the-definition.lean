module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»
public import StacksAndModuli.API.PseudofunctorAffineStackCriterion
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Stacks: the definition

This module formalizes `def:stack` and `exer:fiber-product-stacks` of §3.5 (Stacks) of
*Stacks and Moduli*, label `sec:stacks`.

A stack over a site is a prestack (category fibered in groupoids,
`CategoryTheory.Functor.IsFiberedInGroupoids`) in which both morphisms and objects glue for
the Grothendieck topology. The definition `CategoryTheory.Functor.IsStack` is stated in
sieve form and pullback-free: no choices of pullbacks appear (the same design as Mathlib's
`CategoryTheory.Pseudofunctor.IsStack` for pseudofunctors). A descent datum of objects
over a covering sieve `R` of `S` is a functor to `𝒳` from the full subcategory
`R.arrows.category` of `𝒮/S` of arrows of the sieve, lying over the forgetful functor; in
a category fibered in groupoids every morphism is strongly cartesian, so this datum
subsumes the cocycle condition of the book's covering-family formulation.

Main results:
- `CategoryTheory.Functor.IsStack`: **Definition 3.5.1** (`def:stack`), the stack axioms
  for a prestack over a site;
- `CategoryTheory.BasedCategory.IsStack`: the same condition for a based category;
- `AlgebraicGeometry.isStack_etaleTopology_iff_affine_singletons` (and the fppf/fpqc
  variants): **Exercise 3.5.5** (`exer:stack-axiom-reduced-to-single-map`);
- `CategoryTheory.BasedCategory.isStack_fiberProduct`: **Exercise 3.5.6**
  (`exer:fiber-product-stacks`), fiber products of stacks are stacks.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefStack

open CategoryTheory Functor Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- **Definition 3.5.1** (`def:stack`): let $\cS$ be a site and let $p \colon \cX \to \cS$
be a prestack (category fibered in groupoids). Then $\cX$ is a *stack* if for every
covering sieve $R$ of an object $S$:

1. *(morphisms glue)* for objects $a, b$ of $\cX$ over $S$, every family assigning to each
   $(g \colon T \to S) \in R$ and each lift $\xi \colon x \to a$ of $g$ a morphism
   $\varphi_\xi \colon x \to b$ over $g$, compatibly with restriction, arises from a unique
   morphism $\Phi \colon a \to b$ over $\operatorname{id}_S$ via
   $\varphi_\xi = \xi \circ \Phi$;
2. *(objects glue)* every descent datum over $R$ — a functor $D$ from the full subcategory
   of $\cS/S$ of arrows of $R$ to $\cX$ lying over the forgetful functor — is effective:
   there is an object $a$ over $S$ together with morphisms $\varepsilon_f \colon D(f) \to a$
   over $f$, natural in $f \in R$.

(The formulation by covering families $\{S_i \to S\}$ with isomorphisms
$\alpha_{ij}$ satisfying the cocycle condition is the special case of the descent datum
associated to the generated sieve; in a category fibered in groupoids all morphisms are
strongly cartesian, so no cartesianness conditions appear. See the Definition 3.5.1 entry of
this folder's COMMENTARY.md.) -/
class IsStack (p : 𝒳 ⥤ 𝒮) [p.IsFiberedInGroupoids] (J : GrothendieckTopology 𝒮) :
    Prop where
  /-- API projection from Definition 3.5.1 (part (1), morphisms glue): morphisms glue
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
  /-- API projection from Definition 3.5.1 (part (2), objects glue): every descent datum
  over a covering sieve is effective. -/
  exists_gluing_obj : ∀ {S : 𝒮} {R : Sieve S}, R ∈ J S →
    ∀ (D : R.arrows.category ⥤ 𝒳),
      (∀ f : R.arrows.category, p.obj (D.obj f) = f.obj.left) →
      (∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), IsHomLift p h.hom.left (D.map h)) →
      ∃ (a : 𝒳) (_ : p.obj a = S) (ε : ∀ f : R.arrows.category, D.obj f ⟶ a),
        (∀ f : R.arrows.category, IsHomLift p f.obj.hom (ε f)) ∧
        ∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), D.map h ≫ ε g = ε f

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {Base : Type u₁} {Total : Type u₂} [Category.{v₁} Base]
  [Category.{v₂} Total]

/-- Axiom (1) in Definition 3.5.1, separated from object descent: morphisms in a
prestack glue uniquely along every covering sieve. This predicate is useful for
statements, such as Exercise 3.5.21(a), which assert only the first stack axiom. -/
def MorphismsGlue (p : Total ⥤ Base) [p.IsFiberedInGroupoids]
    (J : GrothendieckTopology Base) : Prop :=
  ∀ {S : Base} {R : Sieve S}, R ∈ J S →
    ∀ {a b : Total}, p.obj a = S → p.obj b = S →
    ∀ (φ : ∀ {T : Base} {g : T ⟶ S}, R g → ∀ {x : Total} (ξ : x ⟶ a),
        IsHomLift p g ξ → (x ⟶ b)),
      (∀ {T : Base} {g : T ⟶ S} (hg : R g) {x : Total} (ξ : x ⟶ a)
        (hξ : IsHomLift p g ξ), IsHomLift p g (φ hg ξ hξ)) →
      (∀ {T' T : Base} {g : T ⟶ S} (hg : R g) {h : T' ⟶ T}
        {x' x : Total} (χ : x' ⟶ x) (ξ : x ⟶ a) (hξ : IsHomLift p g ξ)
        (_hχ : IsHomLift p h χ),
        φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) →
      ∃! Φ : a ⟶ b, IsHomLift p (𝟙 S) Φ ∧
        ∀ {T : Base} {g : T ⟶ S} (hg : R g) {x : Total} (ξ : x ⟶ a)
          (hξ : IsHomLift p g ξ), φ hg ξ hξ = ξ ≫ Φ

/-- Every stack satisfies its morphism-gluing axiom. -/
lemma IsStack.morphismsGlue (p : Total ⥤ Base) [p.IsFiberedInGroupoids]
    (J : GrothendieckTopology Base) [p.IsStack J] : p.MorphismsGlue J :=
  IsStack.existsUnique_gluing_hom

end CategoryTheory.Functor

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (J : GrothendieckTopology 𝒮)

/-- **Definition 3.5.1** (`def:stack`) (based-category form): a based category `𝒳` over a
site `(𝒮, J)` is a stack if it is fibered in groupoids and satisfies the stack axioms. -/
class IsStack (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : Prop where
  isFiberedInGroupoids : 𝒳.p.IsFiberedInGroupoids
  isStack : 𝒳.p.IsStack J

attribute [instance] IsStack.isFiberedInGroupoids IsStack.isStack

end CategoryTheory.BasedCategory

end DefStack

section StackHomExt

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.IsStack

variable {SBase : Type u₁} {XTotal : Type u₂} [Category.{v₁} SBase]
  [Category.{v₂} XTotal] {p : XTotal ⥤ SBase} [p.IsFiberedInGroupoids]
  {J : GrothendieckTopology SBase} [p.IsStack J]

/-- Morphisms in a stack can be compared after restriction to a covering sieve. -/
lemma hom_ext_of_cover {S : SBase} {R : Sieve S} (hR : R ∈ J S)
    {a b : XTotal} (ha : p.obj a = S) (hb : p.obj b = S) {f g : a ⟶ b}
    (hf : IsHomLift p (𝟙 S) f) (hg : IsHomLift p (𝟙 S) g)
    (h : ∀ {T : SBase} {q : T ⟶ S} (_hq : R q) {x : XTotal}
      (ξ : x ⟶ a) (_hξ : IsHomLift p q ξ), ξ ≫ f = ξ ≫ g) : f = g := by
  obtain ⟨Φ, -, huniq⟩ := IsStack.existsUnique_gluing_hom hR ha hb
    (fun {_} {_} _ {_} ξ _ ↦ ξ ≫ f)
    (fun {_} {_} _ {_} ξ hξ ↦ by
      letI := hξ
      letI := hf
      infer_instance)
    (fun {_} {_} {_} _ {_} {_} {_} χ ξ _ _ ↦ by simp)
  exact (huniq f ⟨hf, fun {_} {_} _ {_} ξ _ ↦ rfl⟩).trans
    (huniq g ⟨hg, fun {_} {_} hq {_} ξ hξ ↦ h hq ξ hξ⟩).symm

/-- To glue a morphism in a stack it suffices to give it on one functorial choice of lift
over every arrow of the covering sieve. -/
lemma existsUnique_gluing_hom_of_cocone {S : SBase} {R : Sieve S} (hR : R ∈ J S)
    (D : R.arrows.category ⥤ XTotal)
    {a b : XTotal} (ha : p.obj a = S) (hb : p.obj b = S)
    (η : ∀ q : R.arrows.category, D.obj q ⟶ a)
    (hηlift : ∀ q, IsHomLift p q.obj.hom (η q))
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift p k.hom.left (D.map k))
    (hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ η r = η q)
    (θ : ∀ q : R.arrows.category, D.obj q ⟶ b)
    (hθlift : ∀ q, IsHomLift p q.obj.hom (θ q))
    (hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ θ r = θ q) :
    ∃! Φ : a ⟶ b, IsHomLift p (𝟙 S) Φ ∧
      ∀ {T : SBase} {q : T ⟶ S} (hq : R q), θ (R.arrows.categoryMk q hq) =
        η (R.arrows.categoryMk q hq) ≫ Φ := by
  let Q : ∀ {T : SBase} {q : T ⟶ S}, R q → R.arrows.category :=
    fun {_} {q} hq ↦ R.arrows.categoryMk q hq
  let κ : ∀ {T : SBase} {q : T ⟶ S} (hq : R q) {x : XTotal}
      (ξ : x ⟶ a) [IsHomLift p q ξ], x ⟶ D.obj (Q hq) :=
    fun {_} {q} hq {_} ξ hξ ↦ by
      letI := hξ
      letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
      letI : IsStronglyCartesian p q (η (Q hq)) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
      exact IsStronglyCartesian.map p q (η (Q hq)) (Category.id_comp q).symm ξ
  have hκ_fac : ∀ {T : SBase} {q : T ⟶ S} (hq : R q) {x : XTotal}
      (ξ : x ⟶ a) [IsHomLift p q ξ], κ hq ξ ≫ η (Q hq) = ξ := by
    intro T q hq x ξ hξ
    letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
    letI : IsStronglyCartesian p q (η (Q hq)) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
    simp [κ]
  obtain ⟨Φ, hΦ, huniq⟩ := IsStack.existsUnique_gluing_hom hR ha hb
    (fun {_} {_} hq {_} ξ hξ ↦ by
      letI := hξ
      exact κ hq ξ ≫ θ (Q hq))
    (fun {_} {q} hq {_} ξ hξ ↦ by
      letI := hξ
      letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
      letI : IsStronglyCartesian p q (η (Q hq)) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
      letI := IsStronglyCartesian.map_isHomLift p q (η (Q hq))
        (Category.id_comp q).symm ξ
      letI : IsHomLift p q (θ (Q hq)) := by simpa [Q] using hθlift (Q hq)
      infer_instance)
    (fun {T'} {T} {q} hq {r} {x'} {x} χ ξ hξ hχ ↦ by
      letI := hξ
      letI := hχ
      let hq' := R.downward_closed hq r
      let k : Q hq' ⟶ Q hq := ObjectProperty.homMk (Over.homMk r rfl)
      have hkη : D.map k ≫ η (Q hq) = η (Q hq') := hηnat k
      have hkθ : D.map k ≫ θ (Q hq) = θ (Q hq') := hθnat k
      have hκ : κ hq' (χ ≫ ξ) ≫ D.map k = χ ≫ κ hq ξ := by
        letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
        letI : IsHomLift p (r ≫ q) (η (Q hq')) := by
          simpa [Q] using hηlift (Q hq')
        letI : IsHomLift p r (D.map k) := by simpa [k, Q] using hDmap k
        letI : IsStronglyCartesian p q (η (Q hq)) :=
          Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
        letI : IsStronglyCartesian p (r ≫ q) (η (Q hq')) :=
          Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p (r ≫ q) _
        letI : IsHomLift p (𝟙 _) (κ hq ξ) := by
          simpa [κ] using IsStronglyCartesian.map_isHomLift p q (η (Q hq))
            (Category.id_comp q).symm ξ
        letI : IsHomLift p (𝟙 _) (κ hq' (χ ≫ ξ)) := by
          simpa [κ] using IsStronglyCartesian.map_isHomLift p (r ≫ q) (η (Q hq'))
            (Category.id_comp (r ≫ q)).symm (χ ≫ ξ)
        letI : IsHomLift p r (χ ≫ κ hq ξ) := inferInstance
        letI : IsHomLift p r (κ hq' (χ ≫ ξ) ≫ D.map k) :=
          IsHomLift.comp_lift_id_left' p T' _ r _
        apply IsStronglyCartesian.ext p q (η (Q hq)) r
        rw [Category.assoc, hkη, hκ_fac, Category.assoc, hκ_fac]
      calc
        κ hq' (χ ≫ ξ) ≫ θ (Q hq') =
            (κ hq' (χ ≫ ξ) ≫ D.map k) ≫ θ (Q hq) := by
          rw [Category.assoc, hkθ]
        _ = (χ ≫ κ hq ξ) ≫ θ (Q hq) := by rw [hκ]
        _ = χ ≫ κ hq ξ ≫ θ (Q hq) := Category.assoc _ _ _)
  refine ⟨Φ, ⟨hΦ.1, fun {T q} hq ↦ ?_⟩, ?_⟩
  · let q' := R.arrows.categoryMk q hq
    letI := hηlift q'
    have h := hΦ.2 hq (η q') (hηlift q')
    dsimp [q'] at h ⊢
    simpa [Q, κ] using h
  · intro Ψ hΨ
    apply huniq Ψ
    refine ⟨hΨ.1, ?_⟩
    intro T q hq x ξ hξ
    letI := hξ
    calc
      κ hq ξ ≫ θ (Q hq) = κ hq ξ ≫ (η (Q hq) ≫ Ψ) := by rw [← hΨ.2 hq]
      _ = (κ hq ξ ≫ η (Q hq)) ≫ Ψ := (Category.assoc _ _ _).symm
      _ = ξ ≫ Ψ := by rw [hκ_fac]

/-- Over a sieve, a prestack admits a functorial choice of lifts into a fixed object.
The resulting functor comes with its tautological cartesian cocone. -/
lemma exists_lift_cocone {a : XTotal} (R : Sieve (p.obj a)) :
    ∃ (D : R.arrows.category ⥤ XTotal) (η : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q, IsHomLift p q.obj.hom (η q)) ∧
      (∀ {q r : R.arrows.category} (k : q ⟶ r),
        IsHomLift p k.hom.left (D.map k)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ η r = η q := by
  classical
  let D₀ : R.arrows.category → XTotal := fun q ↦
    (Functor.IsFiberedInGroupoids.exists_isHomLift (p := p) q.obj.hom).choose
  let η : ∀ q : R.arrows.category, D₀ q ⟶ a := fun q ↦
    (Functor.IsFiberedInGroupoids.exists_isHomLift (p := p) q.obj.hom).choose_spec.choose
  have hη : ∀ q, IsHomLift p q.obj.hom (η q) := fun q ↦
    (Functor.IsFiberedInGroupoids.exists_isHomLift (p := p) q.obj.hom).choose_spec.choose_spec
  let map : ∀ {q r : R.arrows.category} (k : q ⟶ r), D₀ q ⟶ D₀ r :=
    fun {q r} k ↦ by
      letI := hη r
      letI := hη q
      exact IsStronglyCartesian.map p r.obj.hom (η r) k.hom.w.symm (η q)
  have map_fac : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      map k ≫ η r = η q := by
    intro q r k
    letI := hη r
    letI := hη q
    exact IsStronglyCartesian.fac p r.obj.hom (η r) k.hom.w.symm (η q)
  have map_lift : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift p k.hom.left (map k) := by
    intro q r k
    letI := hη r
    letI := hη q
    exact IsStronglyCartesian.map_isHomLift p r.obj.hom (η r) k.hom.w.symm (η q)
  let D : R.arrows.category ⥤ XTotal :=
    { obj := D₀
      map := fun k ↦ map k
      map_id := fun q ↦ by
        letI := hη q
        letI := map_lift (𝟙 q)
        letI : IsHomLift p (𝟙 q.obj.left) (𝟙 (D₀ q)) :=
          IsHomLift.id (IsHomLift.domain_eq p q.obj.hom (η q))
        apply IsStronglyCartesian.ext p q.obj.hom (η q) (𝟙 q.obj.left)
        simp [map_fac]
      map_comp := fun {q r s} k l ↦ by
        letI := hη s
        letI := map_lift k
        letI := map_lift l
        letI := map_lift (k ≫ l)
        letI : IsHomLift p (k.hom.left ≫ l.hom.left) (map k ≫ map l) := inferInstance
        letI : IsHomLift p (k ≫ l).hom.left (map k ≫ map l) := by
          simpa using (inferInstance :
            IsHomLift p (k.hom.left ≫ l.hom.left) (map k ≫ map l))
        apply IsStronglyCartesian.ext p s.obj.hom (η s) (k ≫ l).hom.left
        calc
          map (k ≫ l) ≫ η s = η q := map_fac (k ≫ l)
          _ = (map k ≫ map l) ≫ η s := by
            rw [Category.assoc, map_fac, map_fac] }
  exact ⟨D, η, hη, map_lift, map_fac⟩

end CategoryTheory.Functor.IsStack

namespace CategoryTheory.BasedFunctor

open _root_.CategoryTheory.Functor

variable {SBase : Type u₁} [Category.{v₁} SBase]
  {A : BasedCategory.{v₂, u₂} SBase} {B : BasedCategory.{v₃, u₃} SBase}
  {J : GrothendieckTopology SBase} [B.p.IsFiberedInGroupoids] [B.p.IsStack J]

/-- A based functor into a stack sends a descent datum to a datum admitting a global
amalgamation. -/
lemma exists_gluing_obj_of_isStack (H : A ⥤ᵇ B) {S : SBase} {R : Sieve S}
    (hR : R ∈ J S) (D : R.arrows.category ⥤ A.obj)
    (hDobj : ∀ q : R.arrows.category, A.p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift A.p k.hom.left (D.map k)) :
    ∃ (b : B.obj) (_ : B.p.obj b = S) (ε : ∀ q : R.arrows.category, H.obj (D.obj q) ⟶ b),
      (∀ q, IsHomLift B.p q.obj.hom (ε q)) ∧
        ∀ {q r : R.arrows.category} (k : q ⟶ r), H.map (D.map k) ≫ ε r = ε q := by
  apply Functor.IsStack.exists_gluing_obj hR (D ⋙ H.toFunctor)
  · exact fun q ↦ (H.w_obj _).trans (hDobj q)
  · intro q r k
    letI := hDmap k
    exact H.preserves_isHomLift k.hom.left (D.map k)

end CategoryTheory.BasedFunctor

end StackHomExt

section ExerStackAxiomReducedToSingleMap

section

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {Base : Type u₁} {Total : Type u₂} [Category.{v₁} Base] [Category.{v₂} Total]

/-- Background definition for Exercise 3.5.5: both stack axioms of Definition 3.5.1,
relative to one
fixed sieve rather than to every covering sieve of a topology.

`IsStack p J` is exactly `∀ S, ∀ R ∈ J S, IsStackForSieve p R`; isolating the
single-sieve form is what lets the exercise say "the axioms hold for a surjective étale
map of affines" without naming a topology in which that map covers. -/
def IsStackForSieve (p : Total ⥤ Base) [p.IsFiberedInGroupoids] {S : Base}
    (R : Sieve S) : Prop :=
  (∀ {a b : Total}, p.obj a = S → p.obj b = S →
    ∀ (φ : ∀ ⦃T : Base⦄ ⦃g : T ⟶ S⦄, R g → ∀ ⦃x : Total⦄ (ξ : x ⟶ a),
        IsHomLift p g ξ → (x ⟶ b)),
      (∀ ⦃T : Base⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Total⦄ (ξ : x ⟶ a)
        (hξ : IsHomLift p g ξ), IsHomLift p g (φ hg ξ hξ)) →
      (∀ ⦃T' T : Base⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃h : T' ⟶ T⦄ ⦃x' x : Total⦄ (χ : x' ⟶ x)
        (ξ : x ⟶ a) (hξ : IsHomLift p g ξ) (_hχ : IsHomLift p h χ),
        φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) →
      ∃! Φ : a ⟶ b, IsHomLift p (𝟙 S) Φ ∧
        ∀ ⦃T : Base⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Total⦄ (ξ : x ⟶ a)
          (hξ : IsHomLift p g ξ), φ hg ξ hξ = ξ ≫ Φ) ∧
  (∀ (D : R.arrows.category ⥤ Total),
      (∀ f : R.arrows.category, p.obj (D.obj f) = f.obj.left) →
      (∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), IsHomLift p h.hom.left (D.map h)) →
      ∃ (a : Total) (_ : p.obj a = S) (ε : ∀ f : R.arrows.category, D.obj f ⟶ a),
        (∀ f : R.arrows.category, IsHomLift p f.obj.hom (ε f)) ∧
        ∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), D.map h ≫ ε g = ε f)

/-- A stack satisfies both axioms for every covering sieve of its topology. -/
theorem IsStack.isStackForSieve (p : Total ⥤ Base) [p.IsFiberedInGroupoids]
    (J : GrothendieckTopology Base) [p.IsStack J] {S : Base} {R : Sieve S} (hR : R ∈ J S) :
    p.IsStackForSieve R :=
  ⟨fun ha hb ↦ IsStack.existsUnique_gluing_hom hR ha hb,
    fun D hD hD' ↦ IsStack.exists_gluing_obj hR D hD hD'⟩

/-- Conversely, a functor satisfying both axioms for every covering sieve is a stack. -/
theorem isStack_of_isStackForSieve (p : Total ⥤ Base) [p.IsFiberedInGroupoids]
    (J : GrothendieckTopology Base)
    (h : ∀ {S : Base} {R : Sieve S}, R ∈ J S → p.IsStackForSieve R) :
    p.IsStack J := by
  constructor
  · intro S R hR a b ha hb
    exact (h hR).1 ha hb
  · intro S R hR D hD hD'
    exact (h hR).2 D hD hD'

/-- The stack condition passes to coarser topologies: a covering sieve for `J ≤ K` is a
covering sieve for `K`, and both axioms are quantified over covering sieves.

An immediate payoff of the single-sieve form: without it this needs the two axiom bodies
transported by hand. -/
theorem IsStack.of_le {J K : GrothendieckTopology Base} (h : J ≤ K)
    (p : Total ⥤ Base) [p.IsFiberedInGroupoids] [p.IsStack K] : p.IsStack J :=
  isStack_of_isStackForSieve p J fun hR ↦ IsStack.isStackForSieve p K (h _ hR)

end CategoryTheory.Functor

namespace CategoryTheory.BasedCategory

variable {SBase : Type u₁} [Category.{v₁} SBase]

/-- The stack condition for a based category passes to coarser topologies. -/
theorem IsStack.of_le {J K : GrothendieckTopology SBase} (h : J ≤ K)
    (𝒳 : BasedCategory.{v₂, u₂} SBase) [BasedCategory.IsStack K 𝒳] :
    BasedCategory.IsStack J 𝒳 where
  isFiberedInGroupoids := BasedCategory.IsStack.isFiberedInGroupoids (J := K)
  isStack :=
    haveI := BasedCategory.IsStack.isFiberedInGroupoids (J := K) (𝒳 := 𝒳)
    haveI := BasedCategory.IsStack.isStack (J := K) (𝒳 := 𝒳)
    Functor.IsStack.of_le h 𝒳.p

end CategoryTheory.BasedCategory

end

section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry

/-- **Exercise 3.5.5** (`exer:stack-axiom-reduced-to-single-map`) (etale case): in the
pseudofunctor (equivalently, cleavage) presentation of a prestack on schemes, the
prestack is an etale stack if and only if it is a Zariski stack and both descent axioms
hold for every surjective etale morphism between affine schemes. -/
theorem isStack_etaleTopology_iff_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v, u}) :
    F.IsStack Scheme.etaleTopology ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
          Etale (Spec.map q) → Surjective (Spec.map q) →
            F.IsStackFor (.singleton (Spec.map q)) := by
  letI : (Scheme.propQCTopology (@Etale : MorphismProperty Scheme.{u})).Subcanonical := by
    rw [← Scheme.etaleTopology_eq_propQCTopology]
    infer_instance
  rw [Scheme.etaleTopology_eq_propQCTopology]
  exact isStack_propQCTopology_iff_affine_singletons (P := @Etale) F

/-- **Exercise 3.5.5** (`exer:stack-axiom-reduced-to-single-map`) (fppf case): in the
pseudofunctor (equivalently, cleavage) presentation of a prestack on schemes, the
prestack is an fppf stack if and only if it is a Zariski stack and both descent axioms
hold for every surjective flat, locally finitely presented morphism between affine
schemes. -/
theorem isStack_fppfTopology_iff_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v, u}) :
    F.IsStack Scheme.fppfTopology ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
          Flat (Spec.map q) → LocallyOfFinitePresentation (Spec.map q) →
            Surjective (Spec.map q) →
              F.IsStackFor (.singleton (Spec.map q)) := by
  let P : MorphismProperty Scheme.{u} :=
    @Flat ⊓ @LocallyOfFinitePresentation
  letI : P.IsMultiplicative := by
    dsimp [P]
    exact
      { id_mem := fun X ↦ ⟨MorphismProperty.id_mem _ X, inferInstance⟩
        comp_mem := fun f g hf hg ↦
          ⟨MorphismProperty.comp_mem _ f g hf.1 hg.1,
            MorphismProperty.comp_mem _ f g hf.2 hg.2⟩ }
  letI : P.IsStableUnderBaseChange := by dsimp [P]; infer_instance
  letI : IsZariskiLocalAtSource P := by dsimp [P]; infer_instance
  letI : (Scheme.propQCTopology P).Subcanonical := by
    change (Scheme.propQCTopology
      (@Flat ⊓ @LocallyOfFinitePresentation)).Subcanonical
    rw [← Scheme.fppfTopology_eq_propQCTopology]
    infer_instance
  rw [Scheme.fppfTopology_eq_propQCTopology]
  change F.IsStack (Scheme.propQCTopology P) ↔ _
  rw [isStack_propQCTopology_iff_affine_singletons (P := P)]
  exact and_congr_right fun _ ↦
    ⟨fun H R S q hf hlf hs ↦ H q ⟨hf, hlf⟩ hs,
      fun H R S q hq hs ↦ H q hq.1 hq.2 hs⟩

/-- **Exercise 3.5.5** (`exer:stack-axiom-reduced-to-single-map`) (fpqc case): in the
pseudofunctor (equivalently, cleavage) presentation of a prestack on schemes, the
prestack is an fpqc stack if and only if it is a Zariski stack and both descent axioms
hold for every faithfully flat morphism between affine schemes. -/
theorem isStack_fpqcTopology_iff_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v, u}) :
    F.IsStack Scheme.fpqcTopology ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
          Flat (Spec.map q) → Surjective (Spec.map q) →
            F.IsStackFor (.singleton (Spec.map q)) := by
  letI : (Scheme.propQCTopology
      (@Flat : MorphismProperty Scheme.{u})).Subcanonical := by
    rw [← Scheme.fpqcTopology_eq_propQCTopology]
    infer_instance
  rw [Scheme.fpqcTopology_eq_propQCTopology]
  exact isStack_propQCTopology_iff_affine_singletons (P := @Flat) F

end AlgebraicGeometry

end

end ExerStackAxiomReducedToSingleMap

section ExerFiberProductStacks

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (J : GrothendieckTopology 𝒮)

namespace FiberProductStack

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒴' : BasedCategory.{v₄, u₄} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
  [IsStack J 𝒳] [IsStack J 𝒴] [IsStack J 𝒴']

/-- Helper lemma used in Exercise 3.5.6 (object-effectivity half): descent
data with values in a fiber product of stacks admit an amalgamation. -/
lemma exists_gluing_obj {S : 𝒮} {R : Sieve S} (hR : R ∈ J S)
    (D : R.arrows.category ⥤ (fiberProduct F G).obj)
    (hDobj : ∀ q : R.arrows.category, (fiberProduct F G).p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift (fiberProduct F G).p k.hom.left (D.map k)) :
    ∃ (b : (fiberProduct F G).obj) (_ : (fiberProduct F G).p.obj b = S)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ b),
      (∀ q, IsHomLift (fiberProduct F G).p q.obj.hom (ε q)) ∧
        ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ ε r = ε q := by
  obtain ⟨x, hx, εx, hεx, hεxnat⟩ :=
    BasedFunctor.exists_gluing_obj_of_isStack (fiberProductFst F G) hR D hDobj hDmap
  obtain ⟨y, hy, εy, hεy, hεynat⟩ :=
    BasedFunctor.exists_gluing_obj_of_isStack (fiberProductSnd F G) hR D hDobj hDmap
  let η : ∀ q : R.arrows.category, F.obj (D.obj q).fst ⟶ F.obj x :=
    fun q ↦ F.map (εx q)
  let θ : ∀ q : R.arrows.category, F.obj (D.obj q).fst ⟶ G.obj y :=
    fun q ↦ (D.obj q).iso.hom ≫ G.map (εy q)
  have hηlift : ∀ q, IsHomLift 𝒴.p q.obj.hom (η q) := by
    intro q
    letI := hεx q
    simpa [η] using F.preserves_isHomLift q.obj.hom (εx q)
  have hθlift : ∀ q, IsHomLift 𝒴.p q.obj.hom (θ q) := by
    intro q
    letI := hεy q
    letI : IsHomLift 𝒴.p (𝟙 q.obj.left) (D.obj q).iso.hom := by
      have h := (D.obj q).isHomLift
      rw [hDobj q] at h
      exact h
    letI : IsHomLift 𝒴.p q.obj.hom (G.map (εy q)) := by
      simpa using G.preserves_isHomLift q.obj.hom (εy q)
    exact IsHomLift.comp_lift_id_left' 𝒴.p q.obj.left _ q.obj.hom _
  have hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ (fiberProductFst F G).toFunctor ⋙ F.toFunctor).map k ≫ η r = η q := by
    intro q r k
    simp only [Functor.comp_map, η, ← F.toFunctor.map_comp, hεxnat]
  have hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ (fiberProductFst F G).toFunctor ⋙ F.toFunctor).map k ≫ θ r = θ q := by
    intro q r k
    dsimp [θ]
    change F.map (D.map k).fst ≫ ((D.obj r).iso.hom ≫ G.map (εy r)) =
      (D.obj q).iso.hom ≫ G.map (εy q)
    have hk := hεynat k
    change (D.map k).snd ≫ εy r = εy q at hk
    rw [← Category.assoc, (D.map k).w, Category.assoc,
      ← G.toFunctor.map_comp, hk]
  obtain ⟨γ, hγ, -⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone hR
    (D ⋙ (fiberProductFst F G).toFunctor ⋙ F.toFunctor)
    (F.w_obj x ▸ hx) (G.w_obj y ▸ hy) η hηlift
    (fun k ↦ by
      have hk := FiberProductHom.isHomLift_fst (D.map k) k.hom.left (hDmap k)
      letI := hk
      exact F.preserves_isHomLift k.hom.left (D.map k).fst)
    hηnat θ hθlift hθnat
  letI : IsHomLift 𝒴.p (𝟙 S) γ := hγ.1
  letI : IsIso γ := Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id
    (p := 𝒴.p) (S := S) γ
  let b : FiberProductObj F G :=
    { fst := x
      snd := y
      over_eq := hy.trans hx.symm
      iso := asIso γ
      isHomLift := by
        have h := hγ.1
        rw [← hx] at h
        exact h }
  let ε : ∀ q : R.arrows.category, D.obj q ⟶ b := fun q ↦
    { fst := εx q
      snd := εy q
      isHomLift := by
        apply IsHomLift.of_fac 𝒴'.p (𝒳.p.map (εx q)) (εy q)
          (D.obj q).over_eq (hy.trans hx.symm)
        rw [IsHomLift.fac' 𝒳.p q.obj.hom (εx q),
          IsHomLift.fac' 𝒴'.p q.obj.hom (εy q)]
        simp
      w := by
        change η q ≫ γ = θ q
        exact (hγ.2 q.property).symm }
  refine ⟨b, hx, ε, ?_, ?_⟩
  · intro q
    exact FiberProductHom.isHomLift_of_fst (ε q) q.obj.hom (hεx q)
  · intro q r k
    apply FiberProductHom.ext
    · exact hεxnat k
    · exact hεynat k

/-- Helper lemma used in Exercise 3.5.6 (morphism-gluing half): compatible
local morphisms in a fiber product of stacks glue uniquely. -/
lemma existsUnique_gluing_hom {S : 𝒮} {R : Sieve S} (hR : R ∈ J S)
    {a b : FiberProductObj F G} (ha : (fiberProduct F G).p.obj a = S)
    (hb : (fiberProduct F G).p.obj b = S)
    (φ : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄, R g → ∀ ⦃z : FiberProductObj F G⦄
      (ξ : z ⟶ a), IsHomLift (fiberProduct F G).p g ξ → (z ⟶ b))
    (hφlift : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃z : FiberProductObj F G⦄
      (ξ : z ⟶ a) (hξ : IsHomLift (fiberProduct F G).p g ξ),
        IsHomLift (fiberProduct F G).p g (φ hg ξ hξ))
    (hφnat : ∀ ⦃T' T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃h : T' ⟶ T⦄
      ⦃z' z : FiberProductObj F G⦄ (χ : z' ⟶ z) (ξ : z ⟶ a)
      (hξ : IsHomLift (fiberProduct F G).p g ξ)
      (_hχ : IsHomLift (fiberProduct F G).p h χ),
        φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) :
    ∃! Φ : a ⟶ b, IsHomLift (fiberProduct F G).p (𝟙 S) Φ ∧
      ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃z : FiberProductObj F G⦄
        (ξ : z ⟶ a) (hξ : IsHomLift (fiberProduct F G).p g ξ),
          φ hg ξ hξ = ξ ≫ Φ := by
  subst S
  obtain ⟨D, η, hηlift, hDmap, hηnat⟩ :=
    Functor.IsStack.exists_lift_cocone (p := (fiberProduct F G).p) R
  let θ : ∀ q : R.arrows.category, D.obj q ⟶ b :=
    fun q ↦ φ q.property (η q) (hηlift q)
  have hθlift : ∀ q, IsHomLift (fiberProduct F G).p q.obj.hom (θ q) :=
    fun q ↦ hφlift q.property (η q) (hηlift q)
  have hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ θ r = θ q := by
    intro q r k
    have h := (hφnat r.property (D.map k) (η r) (hηlift r) (hDmap k)).symm
    convert h using 1
    simp only [θ, hηnat k]
    congr 1
    exact k.hom.w.symm
  obtain ⟨Φx, hΦx, huniqx⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone hR
    (D ⋙ (fiberProductFst F G).toFunctor) rfl hb
    (fun q ↦ (η q).fst)
    (fun q ↦ FiberProductHom.isHomLift_fst (η q) q.obj.hom (hηlift q))
    (fun k ↦ FiberProductHom.isHomLift_fst (D.map k) k.hom.left (hDmap k))
    (fun k ↦ congrArg FiberProductHom.fst (hηnat k))
    (fun q ↦ (θ q).fst)
    (fun q ↦ FiberProductHom.isHomLift_fst (θ q) q.obj.hom (hθlift q))
    (fun k ↦ congrArg FiberProductHom.fst (hθnat k))
  obtain ⟨Φy, hΦy, huniqy⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone hR
    (D ⋙ (fiberProductSnd F G).toFunctor) a.over_eq (b.over_eq.trans hb)
    (fun q ↦ (η q).snd)
    (fun q ↦ by
      letI := hηlift q
      exact (fiberProductSnd F G).preserves_isHomLift q.obj.hom (η q))
    (fun k ↦ by
      letI := hDmap k
      exact (fiberProductSnd F G).preserves_isHomLift k.hom.left (D.map k))
    (fun k ↦ congrArg FiberProductHom.snd (hηnat k))
    (fun q ↦ (θ q).snd)
    (fun q ↦ by
      letI := hθlift q
      exact (fiberProductSnd F G).preserves_isHomLift q.obj.hom (θ q))
    (fun k ↦ congrArg FiberProductHom.snd (hθnat k))
  have hw : F.map Φx ≫ b.iso.hom = a.iso.hom ≫ G.map Φy := by
    apply Functor.IsStack.hom_ext_of_cover hR
      (F.w_obj a.fst) ((G.w_obj b.snd).trans (b.over_eq.trans hb))
    · letI := hΦx.1
      letI : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a.fst)) (F.map Φx) :=
        F.preserves_isHomLift (𝟙 (𝒳.p.obj a.fst)) Φx
      letI : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj b.fst)) b.iso.hom := b.isHomLift
      exact IsHomLift.comp_lift_id_right' 𝒴.p (𝟙 (𝒳.p.obj a.fst)) _
        (𝒳.p.obj b.fst) _
    · letI : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a.fst)) a.iso.hom := a.isHomLift
      letI := hΦy.1
      letI : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a.fst)) (G.map Φy) :=
        G.preserves_isHomLift (𝟙 (𝒳.p.obj a.fst)) Φy
      exact IsHomLift.comp_lift_id_left' 𝒴.p (𝒳.p.obj a.fst) _
        (𝟙 (𝒳.p.obj a.fst)) _
    · intro T q hq z ξ hξ
      let q' := R.arrows.categoryMk q hq
      have hηx : IsHomLift 𝒳.p q ((η q').fst) :=
        FiberProductHom.isHomLift_fst (η q') q (by simpa [q'] using hηlift q')
      letI := hηx
      letI : IsHomLift 𝒴.p q (F.map (η q').fst) :=
        F.preserves_isHomLift q (η q').fst
      letI : IsStronglyCartesian 𝒴.p q (F.map (η q').fst) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift 𝒴.p q _
      letI := hξ
      let κ : z ⟶ F.obj (D.obj q').fst :=
        IsStronglyCartesian.map 𝒴.p q (F.map (η q').fst)
          (Category.id_comp q).symm ξ
      have hκfac : κ ≫ F.map (η q').fst = ξ :=
        IsStronglyCartesian.fac 𝒴.p q (F.map (η q').fst)
          (Category.id_comp q).symm ξ
      have hchosen : F.map (η q').fst ≫ (F.map Φx ≫ b.iso.hom) =
          F.map (η q').fst ≫ (a.iso.hom ≫ G.map Φy) := by
        calc
          F.map (η q').fst ≫ (F.map Φx ≫ b.iso.hom) =
              F.map ((η q').fst ≫ Φx) ≫ b.iso.hom := by
                rw [F.toFunctor.map_comp, Category.assoc]
          _ = F.map (θ q').fst ≫ b.iso.hom := by rw [← hΦx.2 hq]
          _ = (D.obj q').iso.hom ≫ G.map (θ q').snd := (θ q').w
          _ = (D.obj q').iso.hom ≫ G.map ((η q').snd ≫ Φy) := by
                rw [← hΦy.2 hq]
          _ = ((D.obj q').iso.hom ≫ G.map (η q').snd) ≫ G.map Φy := by
                rw [G.toFunctor.map_comp, Category.assoc]
          _ = (F.map (η q').fst ≫ a.iso.hom) ≫ G.map Φy := by rw [(η q').w]
          _ = F.map (η q').fst ≫ (a.iso.hom ≫ G.map Φy) := Category.assoc _ _ _
      calc
        ξ ≫ (F.map Φx ≫ b.iso.hom) =
            (κ ≫ F.map (η q').fst) ≫ (F.map Φx ≫ b.iso.hom) := by rw [hκfac]
        _ = κ ≫ (F.map (η q').fst ≫ (F.map Φx ≫ b.iso.hom)) :=
          Category.assoc _ _ _
        _ = κ ≫ (F.map (η q').fst ≫ (a.iso.hom ≫ G.map Φy)) := by rw [hchosen]
        _ = (κ ≫ F.map (η q').fst) ≫ (a.iso.hom ≫ G.map Φy) :=
          (Category.assoc _ _ _).symm
        _ = ξ ≫ (a.iso.hom ≫ G.map Φy) := by rw [hκfac]
  let Φ : a ⟶ b :=
    { fst := Φx
      snd := Φy
      isHomLift := by
        letI : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a.fst)) Φx := hΦx.1
        letI : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj a.fst)) Φy := hΦy.1
        apply IsHomLift.of_fac 𝒴'.p (𝒳.p.map Φx) Φy a.over_eq b.over_eq
        have hxmap := IsHomLift.fac' 𝒳.p (𝟙 (𝒳.p.obj a.fst)) Φx
        have hymap := IsHomLift.fac' 𝒴'.p (𝟙 (𝒳.p.obj a.fst)) Φy
        rw [hxmap, hymap]
        simp
      w := hw }
  refine ⟨Φ, ⟨FiberProductHom.isHomLift_of_fst Φ _ hΦx.1, ?_⟩, ?_⟩
  · intro T g hg z ξ hξ
    let q := R.arrows.categoryMk g hg
    letI : IsHomLift (fiberProduct F G).p g (η q) := by
      simpa [q] using hηlift q
    letI : IsStronglyCartesian (fiberProduct F G).p g (η q) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        (fiberProduct F G).p g _
    letI := hξ
    let κ : z ⟶ D.obj q :=
      IsStronglyCartesian.map (fiberProduct F G).p g (η q)
        (Category.id_comp g).symm ξ
    have hκlift : IsHomLift (fiberProduct F G).p (𝟙 T) κ :=
      IsStronglyCartesian.map_isHomLift (fiberProduct F G).p g (η q)
        (Category.id_comp g).symm ξ
    have hκfac : κ ≫ η q = ξ :=
      IsStronglyCartesian.fac (fiberProduct F G).p g (η q)
        (Category.id_comp g).symm ξ
    have hlocal : φ hg ξ hξ = κ ≫ θ q := by
      have h := hφnat q.property κ (η q) (hηlift q) hκlift
      simpa [q, θ, hκfac] using h
    rw [hlocal]
    apply FiberProductHom.ext
    · change κ.fst ≫ (θ q).fst = ξ.fst ≫ Φx
      rw [hΦx.2 hg, ← Category.assoc]
      have hk := congrArg FiberProductHom.fst hκfac
      change κ.fst ≫ (η q).fst = ξ.fst at hk
      rw [hk]
    · change κ.snd ≫ (θ q).snd = ξ.snd ≫ Φy
      rw [hΦy.2 hg, ← Category.assoc]
      have hk := congrArg FiberProductHom.snd hκfac
      change κ.snd ≫ (η q).snd = ξ.snd at hk
      rw [hk]
  · intro Ψ hΨ
    apply FiberProductHom.ext
    · apply huniqx Ψ.fst
      refine ⟨FiberProductHom.isHomLift_fst Ψ (𝟙 _) hΨ.1, ?_⟩
      intro T g hg
      let q := R.arrows.categoryMk g hg
      simpa [q, θ] using congrArg FiberProductHom.fst
        (hΨ.2 hg (η q) (hηlift q))
    · apply huniqy Ψ.snd
      refine ⟨?_, ?_⟩
      · letI := hΨ.1
        exact (fiberProductSnd F G).preserves_isHomLift (𝟙 _) Ψ
      · intro T g hg
        let q := R.arrows.categoryMk g hg
        simpa [q, θ] using congrArg FiberProductHom.snd
          (hΨ.2 hg (η q) (hηlift q))

end FiberProductStack

/-- **Exercise 3.5.6** (`exer:fiber-product-stacks`): fiber products of stacks are stacks —
if `𝒳 → 𝒴 ← 𝒴'` are morphisms of stacks over a site `(𝒮, J)`, then the fiber product
`𝒳 ×_𝒴 𝒴'` is a stack. -/
theorem isStack_fiberProduct {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) [IsStack J 𝒳] [IsStack J 𝒴] [IsStack J 𝒴'] :
    IsStack J (fiberProduct F G) := by
  refine { isFiberedInGroupoids := inferInstance, isStack := ?_ }
  exact
    { existsUnique_gluing_hom := FiberProductStack.existsUnique_gluing_hom J
      exists_gluing_obj := FiberProductStack.exists_gluing_obj J }

end CategoryTheory.BasedCategory

end ExerFiberProductStacks
