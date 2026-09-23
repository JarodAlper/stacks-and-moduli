module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.1-groupoids-and-equivalence-relations»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.6-stackification»
public import StacksAndModuli.API.FreeStackCompletionLocal
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.FiberProductSmallSheafRepresentation
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Quotient stacks of groupoids

This module formalizes **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`), the
first cartesian diagram of the unlabelled exercise following it (the second is deferred —
see the comment in the section `ExerGroupoidCartesianDiagrams`), and **Exercise 4.4.12**
(`exer:quotient-stack-is-sheaf`), of §4.4 (Equivalence relations and groupoids) of
*Stacks and Moduli*, section
label `subsec:equivalence-relations`.

For a groupoid `s, t : R ⇉ U` of presheaves on `Sch` we construct the quotient prestack
`[U/R]^pre` (objects: pairs of a scheme `T` and a point of `U(T)`; morphisms: pairs of a
morphism of schemes and a relation) and prove that it is fibered in groupoids. The
quotient stack `[U/R]` is handled through two complementary characteristic predicates:
`CategoryTheory.BasedFunctor.IsStackification` records its universal property, while
`CategoryTheory.BasedFunctor.IsLocalStackification` records the standard local-equivalence
criterion used for cartesian and geometric properties. Their existence for the free stack
completion is supplied by the stackification API. Similarly, the sheaf quotient `U/R` of an
equivalence relation is handled through
`AlgebraicGeometry.PresheafGroupoid.IsQuotientSheaf`.

Main results:
- `AlgebraicGeometry.PresheafGroupoid.QuotientObj`, `.QuotientHom`,
  `.quotientPrestack`: the quotient prestack `[U/R]^pre`, fibered in groupoids;
- `AlgebraicGeometry.PresheafGroupoid.quotientPresheaf`, `.IsQuotientSheaf`: the quotient
  presheaf `T ↦ U(T)/R(T)` and the predicate
  characterizing its étale sheafification `U/R`;
- `AlgebraicGeometry.PresheafGroupoid.isRepresentedByPresheaf_fiberProduct_quotientPresentation`:
  `R` represents `U ×_[U/R]^pre U`, before stackification;
- `AlgebraicGeometry.PresheafGroupoid.quotientProj_morphismsGlue_of_sheaves`:
  `[U/R]^pre` has morphism descent when `U` and `R` are étale sheaves;
- the statements that `R` represents `U ×_{[U/R]} U`
  (`AlgebraicGeometry.PresheafGroupoid.isRepresentedByPresheaf_fiberProduct_of_isStackification`)
  and that `[U/R]` is a sheaf exactly for equivalence relations
  (`AlgebraicGeometry.PresheafGroupoid.exists_isRepresentedByPresheaf_iff_isEquivalenceRelation`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefQuotientOfSmoothGroupoid

open CategoryTheory Functor Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₁ u₁ u

namespace AlgebraicGeometry.PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u})

/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`) (objects of `[U/R]^pre`): an
object of the quotient prestack `[U/R]^pre` of a groupoid of presheaves on `Sch`: a scheme
`T` together with a point of `U(T)` (equivalently, by the Yoneda lemma, a morphism `T → U`
of presheaves). -/
structure QuotientObj where
  /-- The underlying scheme. -/
  base : Scheme.{u}
  /-- The marked point of `U` over the underlying scheme. -/
  pt : 𝒢.U.obj (op base)

variable {𝒢}

/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`) (morphisms of `[U/R]^pre`):
a morphism `(S, a) → (T, b)` in the quotient prestack `[U/R]^pre`: a morphism of schemes
`f : S → T` together with a relation `r ∈ R(S)` from `a` to the restriction `f*(b)`. (The
book writes the target condition as `t(r) = f ∘ b`; the intended composite is `b ∘ f`, the
restriction of `b` along `f` — see this folder's COMMENTARY.md.) -/
structure QuotientHom (a b : 𝒢.QuotientObj) where
  /-- The underlying morphism of schemes. -/
  hom : a.base ⟶ b.base
  /-- The relating element of `R`. -/
  rel : 𝒢.R.obj (op a.base)
  /-- The source of the relation is the marked point of the domain. -/
  s_rel : 𝒢.s.app (op a.base) rel = a.pt
  /-- The target of the relation is the restriction of the marked point of the codomain. -/
  t_rel : 𝒢.t.app (op a.base) rel = 𝒢.U.map hom.op b.pt

/-- Morphisms of the quotient prestack are determined by the underlying morphism of
schemes and the relating element. -/
lemma QuotientHom.ext {a b : 𝒢.QuotientObj} {φ ψ : QuotientHom a b} (h₁ : φ.hom = ψ.hom)
    (h₂ : φ.rel = ψ.rel) : φ = ψ := by
  cases φ
  cases ψ
  subst h₁ h₂
  rfl

/-- The quotient prestack `[U/R]^pre` is a category: identities are given by the identity
relations, and composition composes the relations after restriction. -/
instance instCategoryQuotientObj : Category 𝒢.QuotientObj where
  Hom a b := QuotientHom a b
  id a := ⟨𝟙 a.base, 𝒢.e.app (op a.base) a.pt, by simp, by simp⟩
  comp {a b c} φ ψ :=
    ⟨φ.hom ≫ ψ.hom, 𝒢.comp (𝒢.R.map φ.hom.op ψ.rel) φ.rel (by simp [ψ.s_rel, φ.t_rel]),
      by simp [φ.s_rel], by simp [ψ.t_rel]⟩
  id_comp {a b} φ := by
    refine QuotientHom.ext (Category.id_comp _) ?_
    dsimp only
    simp only [op_id, Functor.map_id_apply]
    exact 𝒢.comp_e_app φ.rel a.pt _
  comp_id {a b} φ := by
    refine QuotientHom.ext (Category.comp_id _) ?_
    dsimp only
    simp only [PresheafGroupoid.map_e_app]
    exact 𝒢.e_app_comp φ.rel _ _
  assoc {a b c d} φ ψ χ := by
    refine QuotientHom.ext (Category.assoc _ _ _) ?_
    have hnat := 𝒢.comp_naturality φ.hom.op (𝒢.R.map ψ.hom.op χ.rel) ψ.rel
      (by simp [χ.s_rel, ψ.t_rel]) (by simp [χ.s_rel, ψ.t_rel])
    simp only [op_comp, Functor.map_comp_apply, hnat]
    exact (𝒢.comp_assoc _ _ _ _ _ _ _).symm

/-- The underlying morphism of schemes of an identity of the quotient prestack. -/
@[simp]
lemma quotientHom_id_hom (a : 𝒢.QuotientObj) : QuotientHom.hom (𝟙 a) = 𝟙 a.base :=
  rfl

/-- The relating element of an identity of the quotient prestack. -/
@[simp]
lemma quotientHom_id_rel (a : 𝒢.QuotientObj) :
    QuotientHom.rel (𝟙 a) = 𝒢.e.app (op a.base) a.pt :=
  rfl

/-- The underlying morphism of schemes of a composition in the quotient prestack. -/
@[simp]
lemma quotientHom_comp_hom {a b c : 𝒢.QuotientObj} (φ : a ⟶ b) (ψ : b ⟶ c) :
    QuotientHom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom :=
  rfl

/-- The relating element of a composition in the quotient prestack. -/
@[simp]
lemma quotientHom_comp_rel {a b c : 𝒢.QuotientObj} (φ : a ⟶ b) (ψ : b ⟶ c) :
    QuotientHom.rel (φ ≫ ψ) =
      𝒢.comp (𝒢.R.map φ.hom.op ψ.rel) φ.rel (by simp [ψ.s_rel, φ.t_rel]) :=
  rfl

variable (𝒢) in
/-- Background construction for Definition 4.4.10 (the projection to `Sch`): the
projection functor from the quotient prestack `[U/R]^pre` of a groupoid of presheaves
to the category of schemes, remembering the underlying scheme of an object and the
underlying morphism of schemes of a morphism. (An `abbrev`, so that the projection is
reducibly the structure projections of `AlgebraicGeometry.PresheafGroupoid.QuotientObj`
and `.QuotientHom`.) -/
abbrev quotientProj : 𝒢.QuotientObj ⥤ Scheme.{u} :=
  { obj := fun a ↦ a.base
    map := fun φ ↦ QuotientHom.hom φ
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

variable (𝒢) in
/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`): the quotient prestack
`[U/R]^pre` of a groupoid `s, t : R ⇉ U` of presheaves on `Sch`: objects over a scheme `T`
are the points of `U(T)`, and morphisms over `f : S → T` from `a ∈ U(S)` to `b ∈ U(T)` are
the relations `r : a → f*(b)` in `R(S)`. (This is an `abbrev` packaging
`AlgebraicGeometry.PresheafGroupoid.quotientProj` as a based category, so that the objects
and the projection are reducibly the quotient objects and the projection functor.) -/
abbrev quotientPrestack : BasedCategory Scheme.{u} where
  obj := 𝒢.QuotientObj
  p := 𝒢.quotientProj

/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`) (`[U/R]^pre` is a prestack):
the quotient prestack `[U/R]^pre` of a groupoid of presheaves is a prestack (a category
fibered in groupoids): pullbacks are given by identity relations, and the fibered
structure by composing with inverses of restricted relations. -/
instance : 𝒢.quotientProj.IsFiberedInGroupoids where
  exists_isHomLift {a S} f := by
    refine ⟨⟨S, 𝒢.U.map f.op a.pt⟩, ⟨f, 𝒢.e.app (op S) (𝒢.U.map f.op a.pt),
      𝒢.s_app_e_app _, 𝒢.t_app_e_app _⟩, ?_⟩
    exact IsHomLift.of_fac 𝒢.quotientProj f _ rfl rfl
      (by rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])
  isStronglyCartesian {x z} φ := by
    have : 𝒢.quotientProj.IsHomLift (𝒢.quotientProj.map φ) φ := IsHomLift.map φ
    refine { universal_property' := ?_ }
    intro y g ψ hψ
    have hgf : g ≫ φ.hom = ψ.hom :=
      IsHomLift.eq_of_isHomLift 𝒢.quotientProj (g ≫ 𝒢.quotientProj.map φ) ψ
    have hsA : 𝒢.s.app _ (𝒢.inv.app _ (𝒢.R.map g.op φ.rel)) = 𝒢.t.app _ ψ.rel := by
      simp only [PresheafGroupoid.s_app_inv_app, PresheafGroupoid.t_app_map, φ.t_rel,
        ψ.t_rel, ← hgf, op_comp, Functor.map_comp_apply]
    refine ⟨⟨g, 𝒢.comp (𝒢.inv.app _ (𝒢.R.map g.op φ.rel)) ψ.rel hsA,
      by simp only [PresheafGroupoid.s_comp, ψ.s_rel],
      by simp only [PresheafGroupoid.t_comp, PresheafGroupoid.t_app_inv_app,
        PresheafGroupoid.s_app_map, φ.s_rel]⟩, ⟨?_, ?_⟩, ?_⟩
    · exact IsHomLift.of_fac 𝒢.quotientProj g _ rfl rfl
        (by rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])
    · refine QuotientHom.ext hgf ?_
      simp only [quotientHom_comp_rel]
      exact 𝒢.comp_inv_comp _ ψ.rel hsA _
    · rintro χ ⟨hχlift, hχcomp⟩
      obtain ⟨g', ρ, hsρ, htρ⟩ := χ
      obtain rfl : g' = g :=
        (IsHomLift.eq_of_isHomLift 𝒢.quotientProj g (QuotientHom.mk g' ρ hsρ htρ)).symm
      have hrel := congrArg QuotientHom.rel hχcomp
      simp only [quotientHom_comp_rel] at hrel
      refine QuotientHom.ext rfl ?_
      simp only [← hrel]
      exact (𝒢.inv_comp_comp _ ρ (by simp only [PresheafGroupoid.s_app_map, φ.s_rel, htρ])
        _).symm

variable (𝒢) in
/-- Background construction from the unlabelled prose following Definition 4.4.10: the
canonical morphism of prestacks
`U → [U/R]^pre` induced by the identity of `U`: it sends a point `a ∈ U(T)` to the object
`(T, a)` of the quotient prestack, and a morphism to the identity relation. Composed with
a stackification `[U/R]^pre → [U/R]` it yields the presentation `p : U → [U/R]`. -/
def quotientPresentation : BasedCategory.ofPresheaf 𝒢.U ⥤ᵇ 𝒢.quotientPrestack where
  toFunctor :=
    { obj := fun x ↦ ⟨x.left, yonedaEquiv x.hom⟩
      map := fun {x y} f ↦
        ⟨f.left, 𝒢.e.app (op x.left) (yonedaEquiv x.hom), by simp,
          by simp [yonedaEquiv_naturality, CostructuredArrow.w f]⟩
      map_id := fun x ↦ QuotientHom.ext rfl rfl
      map_comp := fun {x y z} f g ↦ QuotientHom.ext rfl (by
        change 𝒢.e.app (op x.left) (yonedaEquiv x.hom) =
          𝒢.comp (𝒢.R.map f.left.op (𝒢.e.app (op y.left) (yonedaEquiv y.hom)))
            (𝒢.e.app (op x.left) (yonedaEquiv x.hom)) _
        simp only [PresheafGroupoid.map_e_app]
        exact (𝒢.e_app_comp _ _ _).symm) }
  w := rfl

/-- The image of an object under the canonical morphism `U → [U/R]^pre`. -/
@[simp]
lemma quotientPresentation_obj (x : (BasedCategory.ofPresheaf 𝒢.U).obj) :
    (𝒢.quotientPresentation.obj x : 𝒢.QuotientObj) = ⟨x.left, yonedaEquiv x.hom⟩ :=
  rfl

/-- The canonical presentation of a quotient prestack is faithful. -/
instance quotientPresentation_faithful :
    𝒢.quotientPresentation.toFunctor.Faithful where
  map_injective {x y} f g h := by
    apply CostructuredArrow.hom_ext
    exact congrArg QuotientHom.hom h

variable (𝒢) in
/-- The functor from the groupoid of `T`-points of `R ⇉ U` to the objects of the quotient
prestack, sending a point of `U(T)` to the object `(T, a)` and a relation to itself over
the identity of `T`. -/
def fiberToQuotientObj (T : Scheme.{u}) : 𝒢.Fiber (op T) ⥤ 𝒢.QuotientObj where
  obj a := ⟨T, a⟩
  map {a b} φ := ⟨𝟙 T, φ.rel, φ.s_rel, by simpa using φ.t_rel⟩
  map_id a := QuotientHom.ext rfl rfl
  map_comp {a b c} φ ψ := QuotientHom.ext (by simp) (by
    simp only [quotientHom_comp_rel, comp_rel]
    congr 1
    simp)

variable (𝒢) in
/-- The comparison functor lands in the fiber over `T`. -/
lemma fiberToQuotientObj_comp (T : Scheme.{u}) :
    fiberToQuotientObj 𝒢 T ⋙ 𝒢.quotientProj = (Functor.const _).obj T := rfl

variable (𝒢) in
/-- The comparison functor from the groupoid of `T`-points of `R ⇉ U` to the fiber
category of the quotient prestack over `T`. -/
def fiberFunctor (T : Scheme.{u}) : 𝒢.Fiber (op T) ⥤ 𝒢.quotientProj.Fiber T :=
  Functor.Fiber.inducedFunctor (fiberToQuotientObj_comp 𝒢 T)

instance (T : Scheme.{u}) : (fiberFunctor 𝒢 T).Faithful where
  map_injective {a b} φ ψ h := by
    apply FiberHom.ext
    exact congrArg (fun χ => QuotientHom.rel (Functor.Fiber.fiberInclusion.map χ)) h

instance (T : Scheme.{u}) : (fiberFunctor 𝒢 T).Full where
  map_surjective {a b} φ := by
    obtain ⟨χ, hlift⟩ := φ
    have h := IsHomLift.eq_of_isHomLift 𝒢.quotientProj (𝟙 T) χ
    obtain ⟨f, r, hs, ht⟩ := χ
    obtain rfl : f = 𝟙 T := h.symm
    refine ⟨⟨r, hs, ?_⟩, ?_⟩
    · have hb : 𝒢.U.map (𝟙 T).op b = b := by simp
      exact hb ▸ ht
    · exact Subtype.ext (QuotientHom.ext rfl rfl)

instance (T : Scheme.{u}) : (fiberFunctor 𝒢 T).EssSurj where
  mem_essImage x := by
    obtain ⟨⟨B, pt⟩, hx⟩ := x
    obtain rfl : B = T := hx
    exact ⟨pt, ⟨Iso.refl _⟩⟩

instance (T : Scheme.{u}) : (fiberFunctor 𝒢 T).IsEquivalence where

/-- API theorem from the unlabelled prose following Definition 4.4.10: the fiber category of
the quotient prestack `[U/R]^pre` over a scheme `T` is the groupoid of `T`-points of the
groupoid `R ⇉ U`: its objects are `U(T)` and its morphisms `a → b` are the relations in
`R(T)` with source `a` and target `b`. -/
theorem nonempty_equivalence_fiber_quotientPrestack (T : Scheme.{u}) :
    Nonempty (𝒢.quotientPrestack.p.Fiber T ≌ 𝒢.Fiber (op T)) :=
  ⟨(fiberFunctor 𝒢 T).asEquivalence.symm⟩

end AlgebraicGeometry.PresheafGroupoid

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory AlgebraicGeometry

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Background definition used to formulate Definition 4.4.10 (stackification): let
`i : 𝒳 → 𝒳ˢᵗ` be a morphism of based categories over a
site `(𝒮, J)`. Then `i` *is a stackification* (it exhibits `𝒳ˢᵗ` as the stackification of
`𝒳`) if `𝒳ˢᵗ` is a stack, for every stack `𝒴` precomposition with `i` is an equivalence
`MOR(𝒳ˢᵗ, 𝒴) ≌ MOR(𝒳, 𝒴)`, and every object of `𝒳ˢᵗ` is locally in the essential image
of `i`. Here locality is expressed by a covering sieve, the natural generality of a
Grothendieck topology. The universes of the test stacks `𝒴` are those of the
stackification produced by `CategoryTheory.BasedCategory.exists_stackification`
(Theorem 3.5.18); they cannot be independent universe parameters,
since a `Prop` cannot quantify over universes. For `𝒳 = [U/R]^pre` over `Sch_ét` this
predicate characterizes the quotient stack `[U/R]` of a groupoid `R ⇉ U`. -/
structure IsStackification (J : GrothendieckTopology 𝒮) {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒳st : BasedCategory.{v₃, u₃} 𝒮} (i : 𝒳 ⥤ᵇ 𝒳st) : Prop where
  /-- The target is a stack. -/
  isStack : IsStack J 𝒳st
  /-- Precomposition with `i` is an equivalence onto morphisms from `𝒳`, for every test
  stack. -/
  precompFunctor_isEquivalence :
    ∀ (𝒴 : BasedCategory.{max u₁ v₁ u₂ v₂, max u₁ u₂ v₁ v₂} 𝒮), IsStack J 𝒴 →
      (i.precompFunctor 𝒴).IsEquivalence
  /-- Every target object is locally in the essential image of the stackification map. -/
  locallyEssentiallySurjective : i.IsLocallyEssentiallySurjective (J := J)

/-- API repackaging of Theorem 3.5.18 through the predicate
`CategoryTheory.BasedFunctor.IsStackification`: every prestack over a site admits a
stackification. -/
theorem _root_.CategoryTheory.BasedCategory.exists_isStackification
    (J : GrothendieckTopology 𝒮) (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
    [𝒳.p.IsFiberedInGroupoids] :
    ∃ (𝒳st : BasedCategory.{max u₁ v₁ u₂ v₂, max u₁ u₂ v₁ v₂} 𝒮) (i : 𝒳 ⥤ᵇ 𝒳st),
      i.IsStackification J := by
  let 𝒳st := FreeStackCompletion.completion J 𝒳
  let i := FreeStackCompletion.inclusion J 𝒳
  refine ⟨𝒳st, i, ⟨inferInstance, ?_,
    FreeStackCompletion.inclusion_isLocallyEssentiallySurjective J 𝒳⟩⟩
  intro 𝒴 h𝒴
  let _ := h𝒴
  let P := i.precompFunctor 𝒴
  let _ : P.Full := by
    constructor
    intro H K alpha
    refine ⟨FreeStackCompletion.UniversalGraph.extendNatTrans H K alpha, ?_⟩
    apply BasedNatTrans.homCategory.ext
    ext a
    exact FreeStackCompletion.UniversalGraph.extendNatTrans_inclusion_app H K alpha a
  let _ : P.Faithful := by
    constructor
    intro H K alpha beta hab
    apply BasedNatTrans.homCategory.ext
    ext a
    apply FreeStackCompletion.UniversalGraph.component_ext H K alpha beta
      (fun b ↦ congrArg (fun gamma ↦ gamma.app b) hab)
      (Classical.choice a.valid)
  let _ : P.EssSurj := by
    constructor
    intro F
    exact ⟨FreeStackCompletion.Interpretation.extension (J := J) F,
      ⟨FreeStackCompletion.Interpretation.extensionInclusionIso (J := J) F⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Supporting local-lifting theorem used in the proof of Theorem 4.4.13: let
`i : 𝒳 → 𝒳ˢᵗ` be a stackification of a prestack over
the big étale site of schemes. Every object `y` of `𝒳ˢᵗ` lifts étale-locally to `𝒳`:
there is an étale covering sieve of the base of `y`, and over every arrow in that sieve
a cartesian arrow from an object in the image of `i` to `y`. This covering-sieve form is
the local-density datum supplied by the free stack completion; it does not assert that
the sieve can be replaced by one surjective étale morphism. -/
theorem IsStackification.exists_locally_lift {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒳st : BasedCategory.{v₃, u₃} Scheme.{u}} {i : 𝒳 ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) (y : 𝒳st.obj) :
    ∃ R : Sieve (𝒳st.p.obj y), R ∈ Scheme.etaleTopology (𝒳st.p.obj y) ∧
      ∀ {T : Scheme.{u}} (f : T ⟶ 𝒳st.p.obj y), R f →
        ∃ (x : 𝒳.obj) (q : i.obj x ⟶ y), 𝒳st.p.IsHomLift f q :=
  hi.locallyEssentiallySurjective y

end CategoryTheory.BasedFunctor

namespace AlgebraicGeometry.PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u})

/-- Background definition implicit in Definition 4.4.10: the relation on `U(T)` induced by a
groupoid of presheaves `R ⇉ U`: two points are related if there is a relation in `R(T)`
between them. -/
def quotientRel (T : Scheme.{u}ᵒᵖ) (a b : 𝒢.U.obj T) : Prop :=
  ∃ r : 𝒢.R.obj T, 𝒢.s.app T r = a ∧ 𝒢.t.app T r = b

/-- The relation induced on points by any groupoid of presheaves is an equivalence
relation on the set `U(T)`: reflexivity by the identity, symmetry by the inverse, and
transitivity by the composition. -/
lemma equivalence_quotientRel (T : Scheme.{u}ᵒᵖ) : Equivalence (𝒢.quotientRel T) where
  refl a := ⟨𝒢.e.app T a, by simp, by simp⟩
  symm := fun ⟨r, hs, ht⟩ ↦ ⟨𝒢.inv.app T r, by simp [ht], by simp [hs]⟩
  trans := fun ⟨r, hs, ht⟩ ⟨r', hs', ht'⟩ ↦
    ⟨𝒢.comp r' r (hs'.trans ht.symm), by simp [hs], by simp [ht']⟩

/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`) (the sheaf quotient `U/R`):
the quotient presheaf of a groupoid `R ⇉ U` of presheaves on `Sch`: the presheaf
`T ↦ U(T)/R(T)` of pointwise quotients by the induced equivalence relation. Its étale
sheafification is the sheaf quotient `U/R` (see
`AlgebraicGeometry.PresheafGroupoid.IsQuotientSheaf`). -/
def quotientPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Quot (𝒢.quotientRel T)
  map {T T'} f := ↾(Quot.lift (fun a ↦ Quot.mk _ (𝒢.U.map f a))
    (fun a b ⟨r, hs, ht⟩ ↦ Quot.sound ⟨𝒢.R.map f r, by simp [hs], by simp [ht]⟩))
  map_id T := by
    ext x
    induction x using Quot.ind with
    | mk a => simp
  map_comp {T T' T''} f g := by
    ext x
    induction x using Quot.ind with
    | mk a => simp

/-- Background construction for Definition 4.4.10: the canonical projection from the
presheaf of objects of a groupoid of
presheaves to its quotient presheaf. -/
def toQuotientPresheaf : 𝒢.U ⟶ 𝒢.quotientPresheaf where
  app _ := ↾(Quot.mk _)
  naturality _ _ _ := rfl

/-- Two points of `U(T)` related by a relation in `R(T)` have the same image in the
quotient presheaf. -/
lemma toQuotientPresheaf_app_eq {T : Scheme.{u}ᵒᵖ} {a b : 𝒢.U.obj T}
    (h : 𝒢.quotientRel T a b) :
    𝒢.toQuotientPresheaf.app T a = 𝒢.toQuotientPresheaf.app T b :=
  Quot.sound h

/-- **Definition 4.4.10** (`def:quotient-of-smooth-groupoid`) (the characterization of the
sheaf quotient `U/R`): let `R ⇉ U` be a groupoid of presheaves on `Sch` (in practice, an
étale equivalence relation), let `X` be a presheaf and `q` a morphism from the quotient
presheaf to `X`. Then `(X, q)` *is the quotient sheaf* `U/R` if `X` is a sheaf for the big
étale topology and `q` is locally injective and locally surjective — that is, `q` exhibits
`X` as the étale sheafification of the quotient presheaf. (Sheafification of
`Type u`-valued presheaves on the large site `Sch` is not available as a construction
here, whence the characteristic-predicate formulation; see this folder's
COMMENTARY.md.) -/
structure IsQuotientSheaf (X : Scheme.{u}ᵒᵖ ⥤ Type u) (q : 𝒢.quotientPresheaf ⟶ X) :
    Prop where
  /-- The quotient is an étale sheaf. -/
  isSheaf : Presieve.IsSheaf Scheme.etaleTopology X
  /-- The comparison map is locally injective for the étale topology. -/
  isLocallyInjective : Presheaf.IsLocallyInjective Scheme.etaleTopology q
  /-- The comparison map is locally surjective for the étale topology. -/
  isLocallySurjective : Presheaf.IsLocallySurjective Scheme.etaleTopology q

end AlgebraicGeometry.PresheafGroupoid

end DefQuotientOfSmoothGroupoid

section ExerGroupoidCartesianDiagrams

open CategoryTheory Functor Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₃ u₃ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}} {𝒳st : BasedCategory.{v₃, u₃} Scheme.{u}}
  {i : 𝒢.quotientPrestack ⥤ᵇ 𝒳st}

/-- If the object and relation presheaves of a groupoid are étale sheaves, morphisms in
its quotient prestack glue uniquely.  A local family of quotient-prestack morphisms is
glued by gluing its relation components in `R`; separatedness of `U` verifies the source
and target equations. -/
theorem quotientProj_morphismsGlue_of_sheaves (𝒢 : PresheafGroupoid.{u})
    (hR : Presieve.IsSheaf Scheme.etaleTopology 𝒢.R)
    (hU : Presieve.IsSheaf Scheme.etaleTopology 𝒢.U) :
    𝒢.quotientProj.MorphismsGlue Scheme.etaleTopology := by
  intro S V hV a b ha hb φ hφlift hφcompat
  rcases a with ⟨abase, apoint⟩
  rcases b with ⟨bbase, bpoint⟩
  dsimp [quotientProj] at ha hb
  subst S
  subst bbase
  let sourceObj : 𝒢.QuotientObj := { base := abase, pt := apoint }
  let targetObj : 𝒢.QuotientObj := { base := abase, pt := bpoint }
  let pullObj : ∀ {T : Scheme.{u}}, (T ⟶ abase) → 𝒢.QuotientObj := fun {T} g ↦
    { base := T
      pt := 𝒢.U.map g.op apoint }
  let pullHom : ∀ {T : Scheme.{u}} (g : T ⟶ abase),
      QuotientHom (pullObj g) sourceObj := fun {T} g ↦
    { hom := g
      rel := 𝒢.e.app (op T) (𝒢.U.map g.op apoint)
      s_rel := 𝒢.s_app_e_app _
      t_rel := 𝒢.t_app_e_app _ }
  have pullHom_lift : ∀ {T : Scheme.{u}} (g : T ⟶ abase),
      𝒢.quotientProj.IsHomLift g (pullHom g) := by
    intro T g
    exact Functor.IsHomLift.map (p := 𝒢.quotientProj) (pullHom g)
  let restrictHom : ∀ {T Z : Scheme.{u}} (f : T ⟶ abase) (g : Z ⟶ T),
      QuotientHom (pullObj (g ≫ f)) (pullObj f) := fun {T Z} f g ↦
    { hom := g
      rel := 𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint)
      s_rel := 𝒢.s_app_e_app _
      t_rel := by
        rw [𝒢.t_app_e_app]
        simp only [op_comp, Functor.map_comp_apply, pullObj] }
  have restrictHom_lift : ∀ {T Z : Scheme.{u}} (f : T ⟶ abase) (g : Z ⟶ T),
      𝒢.quotientProj.IsHomLift g (restrictHom f g) := by
    intro T Z f g
    exact Functor.IsHomLift.map (p := 𝒢.quotientProj) (restrictHom f g)
  have restrictHom_comp_pullHom : ∀ {T Z : Scheme.{u}} (f : T ⟶ abase)
      (g : Z ⟶ T),
      @CategoryStruct.comp 𝒢.QuotientObj _ (pullObj (g ≫ f)) (pullObj f) sourceObj
        (restrictHom f g) (pullHom f) =
          (pullHom (g ≫ f) : QuotientHom (pullObj (g ≫ f)) sourceObj) := by
    intro T Z f g
    apply QuotientHom.ext
    · rfl
    · change 𝒢.comp
          (𝒢.R.map g.op (𝒢.e.app (op T) (𝒢.U.map f.op apoint)))
          (𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint)) _ =
        𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint)
      calc
        𝒢.comp
            (𝒢.R.map g.op (𝒢.e.app (op T) (𝒢.U.map f.op apoint)))
            (𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint)) _ =
          𝒢.R.map g.op (𝒢.e.app (op T) (𝒢.U.map f.op apoint)) :=
            𝒢.comp_e_app _ _ _
        _ = 𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint) := by
          rw [𝒢.map_e_app]
          congr 1
          simp
  let fam : Presieve.FamilyOfElements 𝒢.R V.arrows :=
    fun T g hg ↦ (φ hg (pullHom g) (pullHom_lift g)).rel
  have fam_compatible : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T Z f g hf
    have hsame := restrictHom_comp_pullHom f g
    let composed : QuotientHom (pullObj (g ≫ f)) sourceObj :=
      @CategoryStruct.comp 𝒢.QuotientObj _ (pullObj (g ≫ f)) (pullObj f) sourceObj
        (restrictHom f g) (pullHom f)
    have hcompLift : 𝒢.quotientProj.IsHomLift (g ≫ f) composed := by
      let _ := restrictHom_lift f g
      let _ := pullHom_lift f
      exact IsHomLift.comp (p := 𝒢.quotientProj) g f (restrictHom f g) (pullHom f)
    let Lifted := { q : QuotientHom (pullObj (g ≫ f)) sourceObj //
      𝒢.quotientProj.IsHomLift (g ≫ f) q }
    have hpairs :
        (⟨composed, hcompLift⟩ : Lifted) =
          ⟨pullHom (g ≫ f), pullHom_lift (g ≫ f)⟩ := by
      apply Subtype.ext
      exact hsame
    have hφsame := congrArg
      (fun q : Lifted ↦ φ (V.downward_closed hf g) q.1 q.2) hpairs
    have hcomp := hφcompat hf (restrictHom f g) (pullHom f)
      (pullHom_lift f) (restrictHom_lift f g)
    have htotal : φ (V.downward_closed hf g) (pullHom (g ≫ f))
        (pullHom_lift (g ≫ f)) =
          restrictHom f g ≫ φ hf (pullHom f) (pullHom_lift f) :=
      hφsame.symm.trans (by simpa only using hcomp)
    have hrel := congrArg QuotientHom.rel htotal
    change fam (g ≫ f) (V.downward_closed hf g) =
      𝒢.comp (𝒢.R.map g.op (fam f hf))
        (𝒢.e.app (op Z) (𝒢.U.map (g ≫ f).op apoint)) _ at hrel
    change fam (g ≫ f) (V.downward_closed hf g) =
      𝒢.R.map g.op (fam f hf)
    exact hrel.trans (𝒢.comp_e_app _ _ _)
  obtain ⟨rel, hrel, hrel_unique⟩ := (hR V hV) fam fam_compatible
  have global_source : 𝒢.s.app (op abase) rel = apoint := by
    apply (hU V hV).isSeparatedFor.ext
    intro T g hg
    rw [← 𝒢.s_app_map, hrel g hg]
    exact (φ hg (pullHom g) (pullHom_lift g)).s_rel
  have global_target : 𝒢.t.app (op abase) rel = 𝒢.U.map (𝟙 abase).op bpoint := by
    apply (hU V hV).isSeparatedFor.ext
    intro T g hg
    rw [← 𝒢.t_app_map, hrel g hg]
    let theta := φ hg (pullHom g) (pullHom_lift g)
    have htheta_lift := hφlift hg (pullHom g) (pullHom_lift g)
    let _ := htheta_lift
    have hbase : g = theta.hom := by
      exact IsHomLift.eq_of_isHomLift 𝒢.quotientProj g theta
    change 𝒢.t.app (op T) theta.rel =
      𝒢.U.map g.op (𝒢.U.map (𝟙 abase).op bpoint)
    rw [theta.t_rel, ← hbase]
    rw [op_id, Functor.map_id_apply]
  let Phi : QuotientHom sourceObj targetObj :=
    { hom := 𝟙 abase
      rel := rel
      s_rel := global_source
      t_rel := global_target }
  have Phi_lift : 𝒢.quotientProj.IsHomLift (𝟙 abase) Phi :=
    Functor.IsHomLift.map (p := 𝒢.quotientProj) Phi
  refine ⟨Phi, ⟨Phi_lift, ?_⟩, ?_⟩
  · intro T g hg x xi hxi
    let _ := hxi
    let _ := pullHom_lift g
    let _ : IsStronglyCartesian 𝒢.quotientProj g (pullHom g) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        𝒢.quotientProj g (pullHom g)
    let chi : QuotientHom x (pullObj g) :=
      IsStronglyCartesian.map 𝒢.quotientProj g (pullHom g)
        (Category.id_comp g).symm xi
    have hchi_fac : chi ≫ pullHom g = xi :=
      IsStronglyCartesian.fac 𝒢.quotientProj g (pullHom g)
        (Category.id_comp g).symm xi
    have hchi_lift : 𝒢.quotientProj.IsHomLift (𝟙 T) chi := by
      simpa [chi] using IsStronglyCartesian.map_isHomLift 𝒢.quotientProj g
        (pullHom g) (Category.id_comp g).symm xi
    let theta := φ hg (pullHom g) (pullHom_lift g)
    have htheta_lift := hφlift hg (pullHom g) (pullHom_lift g)
    let _ := htheta_lift
    have htheta_base : g = theta.hom :=
      IsHomLift.eq_of_isHomLift 𝒢.quotientProj g theta
    have htheta_rel : theta.rel = 𝒢.R.map g.op rel := by
      simpa [fam, theta] using (hrel g hg).symm
    have theta_eq : theta = pullHom g ≫ Phi := by
      apply QuotientHom.ext
      · change theta.hom = g ≫ 𝟙 abase
        exact htheta_base.symm.trans (Category.comp_id g).symm
      · change theta.rel =
          𝒢.comp (𝒢.R.map g.op rel)
            (𝒢.e.app (op T) (𝒢.U.map g.op apoint)) _
        rw [htheta_rel]
        exact (𝒢.comp_e_app _ _ _).symm
    let composed : QuotientHom x sourceObj :=
      @CategoryStruct.comp 𝒢.QuotientObj _ x (pullObj g) sourceObj chi (pullHom g)
    have hcompLift : 𝒢.quotientProj.IsHomLift g composed := by
      let _ := hchi_lift
      let _ := pullHom_lift g
      simpa only [Category.id_comp] using
        IsHomLift.comp (p := 𝒢.quotientProj) (𝟙 T) g chi (pullHom g)
    let Lifted := { q : QuotientHom x sourceObj //
      𝒢.quotientProj.IsHomLift g q }
    have hpairs : (⟨composed, hcompLift⟩ : Lifted) = ⟨xi, hxi⟩ := by
      apply Subtype.ext
      exact hchi_fac
    have hφsame := congrArg (fun q : Lifted ↦ φ hg q.1 q.2) hpairs
    have hcompat := hφcompat hg chi (pullHom g) (pullHom_lift g) hchi_lift
    simp only [Category.id_comp] at hcompat
    have hfirst : φ hg xi hxi = chi ≫ theta :=
      hφsame.symm.trans (by simpa only using hcompat)
    calc
      φ hg xi hxi = chi ≫ theta := hfirst
      _ = chi ≫ (pullHom g ≫ Phi) := by rw [theta_eq]
      _ = (chi ≫ pullHom g) ≫ Phi := (Category.assoc _ _ _).symm
      _ = xi ≫ Phi := by rw [hchi_fac]
  · intro Psi hPsi
    apply QuotientHom.ext
    · let _ := hPsi.1
      have hbase : (𝟙 abase) = Psi.hom := by
        exact IsHomLift.eq_of_isHomLift 𝒢.quotientProj (𝟙 abase) Psi
      simpa [Phi] using hbase.symm
    · change Psi.rel = rel
      apply hrel_unique
      intro T g hg
      have hfactor := hPsi.2 hg (pullHom g) (pullHom_lift g)
      have hfactor_rel := congrArg QuotientHom.rel hfactor
      change fam g hg =
        𝒢.comp (𝒢.R.map g.op Psi.rel)
          (𝒢.e.app (op T) (𝒢.U.map g.op apoint)) _ at hfactor_rel
      rw [𝒢.comp_e_app] at hfactor_rel
      exact hfactor_rel.symm

/-- The quotient prestack of a groupoid of algebraic spaces has effective descent for
morphisms in the big étale topology. -/
theorem quotientProj_morphismsGlue (𝒢 : PresheafGroupoid.{u})
    [IsAlgebraicSpace 𝒢.U] [IsAlgebraicSpace 𝒢.R] :
    𝒢.quotientProj.MorphismsGlue Scheme.etaleTopology :=
  quotientProj_morphismsGlue_of_sheaves 𝒢
    (IsAlgebraicSpace.isSheaf (X := 𝒢.R))
    (IsAlgebraicSpace.isSheaf (X := 𝒢.U))

/-- The relation represented by an object of the prestack associated to `R`. -/
abbrev relationPoint (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    𝒢.R.obj (op x.left) :=
  yonedaEquiv x.hom

/-- The source point of a represented relation. -/
noncomputable def relationSourceObj
    (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    (BasedCategory.ofPresheaf 𝒢.U).obj :=
  CostructuredArrow.mk (x.hom ≫ 𝒢.s)

/-- The target point of a represented relation. -/
noncomputable def relationTargetObj
    (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    (BasedCategory.ofPresheaf 𝒢.U).obj :=
  CostructuredArrow.mk (x.hom ≫ 𝒢.t)

/-- A represented relation gives an arrow between its source and target in the
quotient prestack. -/
noncomputable def relationHom (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    𝒢.quotientPresentation.obj (relationSourceObj x) ⟶
      𝒢.quotientPresentation.obj (relationTargetObj x) where
  hom := 𝟙 x.left
  rel := relationPoint x
  s_rel := by
    change 𝒢.s.app _ (yonedaEquiv x.hom) = yonedaEquiv (x.hom ≫ 𝒢.s)
    rw [yonedaEquiv_comp]
  t_rel := by
    change 𝒢.t.app _ (yonedaEquiv x.hom) =
      𝒢.U.map (𝟙 x.left).op (yonedaEquiv (x.hom ≫ 𝒢.t))
    rw [yonedaEquiv_comp]
    simp

/-- The arrow associated to a represented relation lies over the identity. -/
lemma relationHom_isHomLift (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    𝒢.quotientProj.IsHomLift (𝟙 x.left) (relationHom x) :=
  IsHomLift.of_fac 𝒢.quotientProj (𝟙 x.left) (relationHom x) rfl rfl (by
    simp [relationHom])

/-- The arrow associated to a represented relation is an isomorphism. -/
noncomputable def relationIso (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    𝒢.quotientPresentation.obj (relationSourceObj x) ≅
      𝒢.quotientPresentation.obj (relationTargetObj x) := by
  let f := relationHom x
  let _ : 𝒢.quotientProj.IsHomLift (𝟙 x.left) f := relationHom_isHomLift x
  let _ : IsIso f :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id
      (p := 𝒢.quotientProj) (S := x.left) f
  exact asIso f

/-- The relation component of the isomorphism attached to a represented relation. -/
@[simp]
lemma relationIso_hom_rel (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    QuotientHom.rel (relationIso x).hom = relationPoint x := by
  rfl

/-- The base component of the isomorphism attached to a represented relation. -/
@[simp]
lemma relationIso_hom_hom (x : (BasedCategory.ofPresheaf 𝒢.R).obj) :
    QuotientHom.hom (relationIso x).hom = 𝟙 x.left := by
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The canonical comparison from `R` to the self-intersection of the quotient-prestack
presentation. -/
noncomputable def relationComparison :
    BasedFunctor (BasedCategory.ofPresheaf 𝒢.R)
      (BasedCategory.fiberProduct 𝒢.quotientPresentation 𝒢.quotientPresentation) where
  obj x :=
    { fst := (BasedCategory.ofPresheaf.map 𝒢.s).obj x
      snd := (BasedCategory.ofPresheaf.map 𝒢.t).obj x
      over_eq := rfl
      iso := relationIso x
      isHomLift := by
        change 𝒢.quotientProj.IsHomLift (𝟙 x.left) (relationIso x).hom
        dsimp [relationIso]
        exact relationHom_isHomLift x }
  map {x y} q :=
    { fst := (BasedCategory.ofPresheaf.map 𝒢.s).map q
      snd := (BasedCategory.ofPresheaf.map 𝒢.t).map q
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl (by
        change q.left = q.left
        rfl)
      w := by
        apply QuotientHom.ext
        · rfl
        · have hq : 𝒢.R.map q.left.op (relationPoint y) = relationPoint x := by
            rw [relationPoint, relationPoint, yonedaEquiv_naturality,
              CostructuredArrow.w q]
          change
            𝒢.comp (𝒢.R.map q.left.op (relationPoint y))
                (𝒢.e.app _ _) _ =
              𝒢.comp (𝒢.R.map (𝟙 x.left).op (𝒢.e.app _ _))
                (relationPoint x) _
          simpa only [PresheafGroupoid.map_e_app, Functor.map_id_apply,
            PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp] using hq }
  map_id x := by
    apply FiberProductHom.ext
    · apply CostructuredArrow.hom_ext
      rfl
    · apply CostructuredArrow.hom_ext
      rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> apply CostructuredArrow.hom_ext <;> simp
  w := rfl

/-- The first projection of the canonical relation comparison is the source map. -/
@[simp]
lemma relationComparison_comp_fiberProductFst :
    (relationComparison (𝒢 := 𝒢)).comp
      (BasedCategory.fiberProductFst 𝒢.quotientPresentation
        𝒢.quotientPresentation) =
      BasedCategory.ofPresheaf.map 𝒢.s := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- The second projection of the canonical relation comparison is the target map. -/
@[simp]
lemma relationComparison_comp_fiberProductSnd :
    (relationComparison (𝒢 := 𝒢)).comp
      (BasedCategory.fiberProductSnd 𝒢.quotientPresentation
        𝒢.quotientPresentation) =
      BasedCategory.ofPresheaf.map 𝒢.t := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- The relation comparison is faithful. -/
private instance relationComparison_faithful :
    (relationComparison (𝒢 := 𝒢)).toFunctor.Faithful where
  map_injective {x y} q r h := by
    apply CostructuredArrow.hom_ext
    exact congrArg (fun k ↦ k.fst.left) h

/-- The relation comparison is full. -/
private instance relationComparison_full :
    (relationComparison (𝒢 := 𝒢)).toFunctor.Full where
  map_surjective {x y} q := by
    let f : x.left ⟶ y.left := q.fst.left
    have hrel : 𝒢.R.map f.op (relationPoint y) = relationPoint x := by
      have hw := congrArg QuotientHom.rel q.w
      change
        𝒢.comp (𝒢.R.map f.op (relationPoint y))
            (𝒢.e.app _ _) _ =
          𝒢.comp (𝒢.R.map (𝟙 x.left).op (𝒢.e.app _ _))
            (relationPoint x) _ at hw
      simpa only [PresheafGroupoid.map_e_app, Functor.map_id_apply,
        PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp] using hw
    have hnat : yoneda.map f ≫ y.hom = x.hom := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_naturality] using hrel
    let r : x ⟶ y := CostructuredArrow.homMk f hnat
    refine ⟨r, ?_⟩
    apply FiberProductHom.ext
    · apply CostructuredArrow.hom_ext
      exact rfl
    · apply CostructuredArrow.hom_ext
      let _ : (BasedCategory.ofPresheaf 𝒢.U).p.IsHomLift
          ((BasedCategory.ofPresheaf 𝒢.U).p.map q.fst) q.snd := q.isHomLift
      have hs := IsHomLift.fac' (BasedCategory.ofPresheaf 𝒢.U).p
        ((BasedCategory.ofPresheaf 𝒢.U).p.map q.fst) q.snd
      change q.fst.left = q.snd.left
      simpa using hs.symm

/-- The base arrow of an isomorphism in the presentation self-intersection is the
equality transport dictated by its two displayed bases. -/
private lemma fiberIso_hom
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    a.iso.hom.hom = eqToHom a.over_eq.symm := by
  let _ : 𝒢.quotientProj.IsHomLift (𝟙 a.fst.left) a.iso.hom := a.isHomLift
  have h := IsHomLift.fac' 𝒢.quotientProj (𝟙 a.fst.left) a.iso.hom
  simpa using h

/-- The relation component of an object in the presentation self-intersection, regarded
as a represented point of `R`. -/
private noncomputable def relationPreimage
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    (BasedCategory.ofPresheaf 𝒢.R).obj :=
  CostructuredArrow.mk (yonedaEquiv.symm a.iso.hom.rel)

/-- Passing a self-intersection object to its relation point and back recovers its
relation component. -/
@[simp]
private lemma relationPoint_relationPreimage
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    relationPoint (relationPreimage a) = a.iso.hom.rel := by
  exact Equiv.apply_symm_apply yonedaEquiv _

/-- The source of the relation extracted from a self-intersection object recovers its
first component. -/
private noncomputable def relationPreimageFstIso
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    relationSourceObj (relationPreimage a) ≅ a.fst :=
  CostructuredArrow.isoMk (Iso.refl _) (by
    have hs : 𝒢.s.app _ a.iso.hom.rel = yonedaEquiv a.fst.hom := by
      simpa only [quotientPresentation_obj] using a.iso.hom.s_rel
    change yoneda.map (𝟙 a.fst.left) ≫ a.fst.hom =
      yonedaEquiv.symm a.iso.hom.rel ≫ 𝒢.s
    rw [yoneda.map_id, Category.id_comp]
    calc
      a.fst.hom = yonedaEquiv.symm (yonedaEquiv a.fst.hom) :=
        (Equiv.symm_apply_apply yonedaEquiv a.fst.hom).symm
      _ = yonedaEquiv.symm (𝒢.s.app _ a.iso.hom.rel) :=
        congrArg yonedaEquiv.symm hs.symm
      _ = yonedaEquiv.symm a.iso.hom.rel ≫ 𝒢.s :=
        (yonedaEquiv_symm_naturality_right _ _ _).symm)

/-- The target of the relation extracted from a self-intersection object recovers its
second component. -/
private noncomputable def relationPreimageSndIso
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    relationTargetObj (relationPreimage a) ≅ a.snd :=
  CostructuredArrow.isoMk (eqToIso a.over_eq.symm) (by
    have ht : 𝒢.t.app _ a.iso.hom.rel =
        𝒢.U.map (eqToHom a.over_eq.symm).op (yonedaEquiv a.snd.hom) := by
      have ht' := a.iso.hom.t_rel
      change 𝒢.t.app _ a.iso.hom.rel =
        𝒢.U.map a.iso.hom.hom.op (yonedaEquiv a.snd.hom) at ht'
      rw [fiberIso_hom] at ht'
      exact ht'
    change yoneda.map (eqToHom a.over_eq.symm) ≫ a.snd.hom =
      yonedaEquiv.symm a.iso.hom.rel ≫ 𝒢.t
    calc
      yoneda.map (eqToHom a.over_eq.symm) ≫ a.snd.hom =
          yoneda.map (eqToHom a.over_eq.symm) ≫
            yonedaEquiv.symm (yonedaEquiv a.snd.hom) := by
              rw [Equiv.symm_apply_apply]
      _ = yonedaEquiv.symm
          (𝒢.U.map (eqToHom a.over_eq.symm).op (yonedaEquiv a.snd.hom)) :=
            yonedaEquiv_symm_naturality_left _ _ _
      _ = yonedaEquiv.symm (𝒢.t.app _ a.iso.hom.rel) :=
        congrArg yonedaEquiv.symm ht.symm
      _ = yonedaEquiv.symm a.iso.hom.rel ≫ 𝒢.t :=
        (yonedaEquiv_symm_naturality_right _ _ _).symm)

/-- The target isomorphism extracted from a self-intersection object lies over the
source isomorphism. -/
private lemma relationPreimageSndIso_isHomLift
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    (BasedCategory.ofPresheaf 𝒢.U).p.IsHomLift
      ((BasedCategory.ofPresheaf 𝒢.U).p.map (relationPreimageFstIso a).hom)
      (relationPreimageSndIso a).hom := by
  apply IsHomLift.of_fac' _ _ _ rfl a.over_eq
  exact (Category.id_comp _).symm

/-- Every object of the presentation self-intersection is isomorphic to the image of
its extracted relation. -/
private noncomputable def relationPreimageIso
    (a : FiberProductObj 𝒢.quotientPresentation 𝒢.quotientPresentation) :
    relationComparison.obj (relationPreimage a) ≅ a := by
  apply FiberProductObj.isoMk (relationPreimageFstIso a) (relationPreimageSndIso a)
    (relationPreimageSndIso_isHomLift a)
  apply QuotientHom.ext
  · change (relationPreimageFstIso a).hom.left ≫ a.iso.hom.hom =
      (relationIso (relationPreimage a)).hom.hom ≫
        (relationPreimageSndIso a).hom.left
    rw [fiberIso_hom]
    rfl
  · simp only [quotientHom_comp_rel, quotientPresentation,
      CostructuredArrow.isoMk_hom_left, relationPreimageFstIso,
      relationPreimageSndIso, PresheafGroupoid.map_e_app,
      PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp]
    change 𝒢.R.map (𝟙 _).op a.iso.hom.rel =
      QuotientHom.rel (relationIso (relationPreimage a)).hom
    rw [relationIso_hom_rel, relationPoint_relationPreimage]
    simp

/-- The relation comparison is essentially surjective. -/
private instance relationComparison_essSurj :
    (relationComparison (𝒢 := 𝒢)).toFunctor.EssSurj where
  mem_essImage a := ⟨relationPreimage a, ⟨relationPreimageIso a⟩⟩

/-- The relation comparison is an equivalence. -/
theorem relationComparison_isEquivalence :
    (relationComparison (𝒢 := 𝒢)).toFunctor.IsEquivalence :=
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- For any groupoid of presheaves, `R` represents the self-intersection of the
canonical presentation of its quotient prestack. -/
theorem isRepresentedByPresheaf_fiberProduct_quotientPresentation :
    (BasedCategory.fiberProduct 𝒢.quotientPresentation
      𝒢.quotientPresentation).IsRepresentedByPresheaf 𝒢.R :=
  ⟨relationComparison, relationComparison_isEquivalence⟩

/-- Postcomposing the quotient-prestack presentation by a fully faithful morphism
preserves its self-intersection, so it remains represented by `R`. -/
theorem isRepresentedByPresheaf_fiberProduct_quotientPresentation_comp
    (i : BasedFunctor 𝒢.quotientPrestack 𝒳st)
    [i.toFunctor.Full] [i.toFunctor.Faithful] :
    (BasedCategory.fiberProduct (𝒢.quotientPresentation.comp i)
      (𝒢.quotientPresentation.comp i)).IsRepresentedByPresheaf 𝒢.R := by
  refine ⟨relationComparison.comp
    (BasedCategory.fiberProductPostcomp 𝒢.quotientPresentation
      𝒢.quotientPresentation i), ?_⟩
  let _ : (relationComparison (𝒢 := 𝒢)).toFunctor.IsEquivalence :=
    relationComparison_isEquivalence
  let _ : (BasedCategory.fiberProductPostcomp 𝒢.quotientPresentation
      𝒢.quotientPresentation i).toFunctor.IsEquivalence :=
    BasedCategory.isEquivalence_fiberProductPostcomp _ _ _
  exact Functor.isEquivalence_trans _ _

/-- A local stackification preserves the relation self-intersection of the quotient
presentation. -/
theorem isRepresentedByPresheaf_fiberProduct_of_isLocalStackification
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i) :
    (BasedCategory.fiberProduct (𝒢.quotientPresentation.comp i)
      (𝒢.quotientPresentation.comp i)).IsRepresentedByPresheaf 𝒢.R := by
  let _ : i.toFunctor.Full := hi.full
  let _ : i.toFunctor.Faithful := hi.faithful
  exact isRepresentedByPresheaf_fiberProduct_quotientPresentation_comp i

/-- Statement of the unnumbered exercise following Definition 4.4.10 (first cartesian
diagram, extending Exercise 3.4.37): let `R ⇉ U` be a smooth groupoid of algebraic
spaces and let `i : [U/R]^pre → 𝒳` be a stackification, so that
`p = i ∘ pres : U → 𝒳` is the projection to the quotient stack `𝒳 = [U/R]`. Then the
square with vertical maps `t, p` and horizontal maps `s, p` is cartesian: the presheaf
`R` represents the fiber product `U ×_{[U/R]} U` of prestacks. -/
theorem isRepresentedByPresheaf_fiberProduct_of_isStackification
    [𝒢.IsSmooth] [IsAlgebraicSpace 𝒢.U] [IsAlgebraicSpace 𝒢.R]
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i) :
    (BasedCategory.fiberProduct (𝒢.quotientPresentation.comp i)
      (𝒢.quotientPresentation.comp i)).IsRepresentedByPresheaf 𝒢.R := by
  exact isRepresentedByPresheaf_fiberProduct_of_isLocalStackification hi

/- **Subsection 4.4** (`subsec:equivalence-relations`) (the unlabelled exercise following
Definition 4.4.10, second cartesian diagram): not formalized. The square expressing
`R → U × U` as the base change of the diagonal `Δ : [U/R] → [U/R] × [U/R]` along `p × p`
is not stated: StacksAndModuli has no binary products of prestacks (`𝒳 × 𝒴`) yet, which the
statement requires. The first cartesian diagram above carries the same mathematical
content in the form used later (the diagonal square is its formal consequence once
products of prestacks are available). -/

end AlgebraicGeometry.PresheafGroupoid

end ExerGroupoidCartesianDiagrams

section ExerQuotientStackIsSheaf

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₃ u₃ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}} {𝒳st : BasedCategory.{v₃, u₃} Scheme.{u}}
  {i : 𝒢.quotientPrestack ⥤ᵇ 𝒳st}

/-- Supporting comparison for Exercise 4.4.12 before stackification: the quotient
prestack `[U/R]^pre` maps to the prestack associated to the
pointwise quotient presheaf `T ↦ U(T)/R(T)`. It sends a point of `U(T)` to its relation
class and forgets the chosen relation carried by a morphism. -/
noncomputable def quotientPrestackToQuotientPresheaf :
    𝒢.quotientPrestack ⥤ᵇ BasedCategory.ofPresheaf 𝒢.quotientPresheaf where
  obj a := CostructuredArrow.mk
    ((yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
      (Quot.mk (𝒢.quotientRel (op a.base)) a.pt))
  map {a b} φ := CostructuredArrow.homMk φ.hom (by
    change yoneda.map φ.hom ≫
        (yonedaEquiv (X := b.base) (F := 𝒢.quotientPresheaf)).symm
          (Quot.mk (𝒢.quotientRel (op b.base)) b.pt) =
      (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
        (Quot.mk (𝒢.quotientRel (op a.base)) a.pt)
    calc
      yoneda.map φ.hom ≫
          (yonedaEquiv (X := b.base) (F := 𝒢.quotientPresheaf)).symm
            (Quot.mk (𝒢.quotientRel (op b.base)) b.pt) =
        (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
          (𝒢.quotientPresheaf.map φ.hom.op
            (Quot.mk (𝒢.quotientRel (op b.base)) b.pt)) :=
          yonedaEquiv_symm_naturality_left _ _ _
      _ = (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
          (Quot.mk (𝒢.quotientRel (op a.base)) a.pt) := by
        apply congrArg
          (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
        change Quot.mk (𝒢.quotientRel (op a.base))
            (𝒢.U.map φ.hom.op b.pt) =
          Quot.mk (𝒢.quotientRel (op a.base)) a.pt
        exact (Quot.sound ⟨φ.rel, φ.s_rel, φ.t_rel⟩).symm)
  map_id a := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp φ ψ := by
    apply CostructuredArrow.hom_ext
    rfl
  w := rfl

/-- Equality of two pointwise quotient classes is witnessed by a relation. The raw
quotient uses the equivalence closure of `quotientRel`, while the groupoid operations
show that `quotientRel` itself is already an equivalence relation. -/
private lemma quotientRel_of_quotientClass_eq {T : Scheme.{u}ᵒᵖ}
    {a b : 𝒢.U.obj T}
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b) :
    𝒢.quotientRel T a b :=
  (𝒢.equivalence_quotientRel T).eqvGen_iff.mp (Quot.eqvGen_exact h)

/-- Supporting full-surjectivity statement for Exercise 4.4.12: every morphism between
pointwise quotient classes is induced by a relation
in the quotient prestack. -/
instance quotientPrestackToQuotientPresheaf_full :
    (quotientPrestackToQuotientPresheaf (𝒢 := 𝒢)).toFunctor.Full := by
  constructor
  intro a b q
  let f : a.base ⟶ b.base := q.left
  have hq : Quot.mk (𝒢.quotientRel (op a.base)) a.pt =
      Quot.mk (𝒢.quotientRel (op a.base)) (𝒢.U.map f.op b.pt) := by
    have hw := CostructuredArrow.w q
    change yoneda.map f ≫
        (yonedaEquiv (X := b.base) (F := 𝒢.quotientPresheaf)).symm
          (Quot.mk (𝒢.quotientRel (op b.base)) b.pt) =
      (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm
        (Quot.mk (𝒢.quotientRel (op a.base)) a.pt) at hw
    apply (yonedaEquiv (X := a.base) (F := 𝒢.quotientPresheaf)).symm.injective
    exact hw.symm.trans (yonedaEquiv_symm_naturality_left _ _ _)
  obtain ⟨r, hs, ht⟩ := quotientRel_of_quotientClass_eq hq
  let φ : QuotientHom a b := ⟨f, r, hs, ht⟩
  refine ⟨φ, ?_⟩
  apply CostructuredArrow.hom_ext
  rfl

/-- Supporting essential-surjectivity statement for Exercise 4.4.12: every pointwise
quotient class has a representative in `U`, so
the canonical comparison from `[U/R]^pre` is essentially surjective. -/
instance quotientPrestackToQuotientPresheaf_essSurj :
    (quotientPrestackToQuotientPresheaf (𝒢 := 𝒢)).toFunctor.EssSurj := by
  constructor
  intro x
  obtain ⟨T, c, rfl⟩ := x.mk_surjective
  obtain ⟨a, ha⟩ := Quot.exists_rep (yonedaEquiv c)
  let y : 𝒢.QuotientObj := ⟨T, a⟩
  refine ⟨y, ⟨?_⟩⟩
  exact CostructuredArrow.isoMk (Iso.refl T) (by
    change yoneda.map (𝟙 T) ≫ c =
      (yonedaEquiv (X := T) (F := 𝒢.quotientPresheaf)).symm
        (Quot.mk (𝒢.quotientRel (op T)) a)
    rw [yoneda.map_id, Category.id_comp]
    exact (Equiv.symm_apply_apply
      (yonedaEquiv (X := T) (F := 𝒢.quotientPresheaf)) c).symm.trans
        (congrArg
          (yonedaEquiv (X := T) (F := 𝒢.quotientPresheaf)).symm ha.symm))

/-- Supporting faithfulness criterion for Exercise 4.4.12: the projection
`[U/R]^pre → Sch` is faithful exactly when a relation
is determined by its source and target, i.e. exactly when `R ⇉ U` is an equivalence
relation. -/
theorem quotientProj_faithful_iff_isEquivalenceRelation :
    𝒢.quotientProj.Faithful ↔ 𝒢.IsEquivalenceRelation := by
  constructor
  · intro hfaithful T x y hs ht
    let _ : 𝒢.quotientProj.Faithful := hfaithful
    let a : 𝒢.QuotientObj := ⟨T.unop, 𝒢.s.app T x⟩
    let b : 𝒢.QuotientObj := ⟨T.unop, 𝒢.t.app T x⟩
    let φ : QuotientHom a b :=
      ⟨𝟙 T.unop, x, rfl, by simp [a, b]⟩
    let ψ : QuotientHom a b :=
      ⟨𝟙 T.unop, y, hs.symm, by simpa [a, b] using ht.symm⟩
    have hmap : 𝒢.quotientProj.map φ = 𝒢.quotientProj.map ψ := rfl
    exact congrArg QuotientHom.rel (𝒢.quotientProj.map_injective hmap)
  · intro hER
    constructor
    intro a b φ ψ hbase
    apply QuotientHom.ext hbase
    apply hER
    · exact φ.s_rel.trans ψ.s_rel.symm
    · rw [φ.t_rel, ψ.t_rel]
      exact congrArg (fun f => 𝒢.U.map f.op b.pt) hbase

/-- Supporting prestack-level reduction for Exercise 4.4.12: the canonical comparison
from `[U/R]^pre` to the prestack of the pointwise quotient is an
equivalence if and only if `R ⇉ U` is an equivalence relation. Thus the exercise's
categorical assertion is already true before sheafification; what remains for the
stack-level statement is compatibility with stackification and a universe-small sheaf
model. -/
theorem isEquivalence_quotientPrestackToQuotientPresheaf_iff :
    (quotientPrestackToQuotientPresheaf (𝒢 := 𝒢)).toFunctor.IsEquivalence ↔
      𝒢.IsEquivalenceRelation := by
  rw [← quotientProj_faithful_iff_isEquivalenceRelation]
  constructor
  · intro h
    let _ := h
    constructor
    intro a b φ ψ hbase
    apply (quotientPrestackToQuotientPresheaf (𝒢 := 𝒢)).toFunctor.map_injective
    apply CostructuredArrow.hom_ext
    exact hbase
  · intro h
    let _ : 𝒢.quotientProj.Faithful := h
    let _ : (quotientPrestackToQuotientPresheaf
        (𝒢 := 𝒢)).toFunctor.Faithful := by
      constructor
      intro a b φ ψ hmap
      apply 𝒢.quotientProj.map_injective
      exact congrArg CostructuredArrow.Hom.left hmap
    exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Supporting conditional stack-level form of Exercise 4.4.12: a local stackification
is represented by a universe-small étale sheaf exactly
when the groupoid is an equivalence relation, provided the fiberwise connected
components of the target are universe-small in the equivalence-relation case. -/
theorem exists_isRepresentedByPresheaf_iff_isEquivalenceRelation_of_isLocalStackification
    (hiLocal : i.IsLocalStackification (J := Scheme.etaleTopology))
    (hsmall : 𝒢.IsEquivalenceRelation → ∀ R : Scheme.{u}, Small.{u}
      (CategoryTheory.ConnectedComponents (𝒳st.p.Fiber R))) :
    (∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, Presieve.IsSheaf Scheme.etaleTopology X ∧
      𝒳st.IsRepresentedByPresheaf X) ↔ 𝒢.IsEquivalenceRelation := by
  let _ : BasedCategory.IsStack Scheme.etaleTopology 𝒳st := hiLocal.isStack
  have hfaithful : 𝒳st.p.Faithful ↔ 𝒢.IsEquivalenceRelation :=
    hiLocal.projection_faithful_iff.symm.trans
      quotientProj_faithful_iff_isEquivalenceRelation
  constructor
  · rintro ⟨X, -, E, hE⟩
    let _ : E.toFunctor.IsEquivalence := hE
    exact hfaithful.mp
      (projection_faithful_of_equivalence_from_ofPresheaf E)
  · intro hER
    let _ : 𝒳st.p.Faithful := hfaithful.mpr hER
    let D := BasedFunctor.smallEtaleSheafRepresentation_of_smallFiberComponents
      𝒳st (hsmall hER)
    exact ⟨D.X, D.isSheaf, D.representation,
      D.representation_isEquivalence⟩

/-- **Exercise 4.4.12** (`exer:quotient-stack-is-sheaf`): let `R ⇉ U` be a smooth groupoid
of algebraic spaces and let `i : [U/R]^pre → 𝒳` be a stackification, so `𝒳 = [U/R]`. Then
`[U/R]` is equivalent to (the prestack associated to) an étale sheaf if and only if
`R ⇉ U` is an equivalence relation.

The prestack-level equivalence is
`isEquivalence_quotientPrestackToQuotientPresheaf_iff`, while
`exists_isRepresentedByPresheaf_iff_isEquivalenceRelation_of_isLocalStackification`
proves the stack-level assertion from a local stackification and universe-small
fiberwise components. Thus the remaining obligation is isolated to upgrading the
given universal-property stackification to that local criterion and proving the
component smallness supplied geometrically by the smooth algebraic-space presentation. -/
theorem exists_isRepresentedByPresheaf_iff_isEquivalenceRelation [𝒢.IsSmooth]
    [IsAlgebraicSpace 𝒢.U] [IsAlgebraicSpace 𝒢.R]
    (hi : i.IsStackification Scheme.etaleTopology) :
    (∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, Presieve.IsSheaf Scheme.etaleTopology X ∧
      𝒳st.IsRepresentedByPresheaf X) ↔ 𝒢.IsEquivalenceRelation := by
  obtain ⟨hfull, hfaithful, hsmall⟩ :
      i.toFunctor.Full ∧ i.toFunctor.Faithful ∧
        (𝒢.IsEquivalenceRelation → ∀ R : Scheme.{u}, Small.{u}
          (CategoryTheory.ConnectedComponents (𝒳st.p.Fiber R))) := by
    sorry
  exact
    exists_isRepresentedByPresheaf_iff_isEquivalenceRelation_of_isLocalStackification
      { isStack := hi.isStack
        full := hfull
        faithful := hfaithful
        locallyEssentiallySurjective := hi.locallyEssentiallySurjective }
      hsmall

end AlgebraicGeometry.PresheafGroupoid

end ExerQuotientStackIsSheaf
