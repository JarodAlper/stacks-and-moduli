module

public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»
public import StacksAndModuli.API.PrestackFiberProductAssoc
public import StacksAndModuli.API.BasedFunctorWhiskering
public import StacksAndModuli.API.OverMapIsIso
public import StacksAndModuli.API.PresheafPrestack
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Morphisms representable by schemes, and algebraic spaces

This module formalizes **Definition 4.1.1** (`def:morphisms-representable-by-schemes`) and
**Definition 4.1.2** (`def:algebraic-space`) of §4.1 (Definitions of algebraic spaces and
stacks) of *Stacks and Moduli*, label
`sec:algebraic-spaces-and-stacks`.

At the presheaf level, a morphism of presheaves on `Sch` is representable by schemes when
every base change by a map from a scheme is a scheme; this is Mathlib's
`yoneda.relativelyRepresentable`, and the refinement by a property `P` of morphisms of
schemes is Mathlib's `MorphismProperty.presheaf`. Both are recalled by `example`s. At the
prestack level the corresponding notions are new, provided here on based categories over
an arbitrary base category `𝒮` together with the supporting infrastructure
(`CategoryTheory.BasedCategory.ofPresheaf`, the prestack associated to a presheaf;
`CategoryTheory.BasedCategory.overBased.map` and `CategoryTheory.BasedFunctor.overHom`,
the correspondence between morphisms `S ⟶ T` of `𝒮` and morphisms of prestacks
`𝒮/S → 𝒮/T`, with `overHom_map`, `overHom_id` and `overHom_comp`; and the based
equivalences `CategoryTheory.BasedCategory.ofPresheafYonedaToOverBased` and
`CategoryTheory.BasedCategory.overBasedToOfPresheafYoneda` comparing `𝒮/S` with the
prestack of the presheaf `Mor(-, S)`).

Main book results:
- `CategoryTheory.BasedFunctor.RelativelyRepresentable` and
  `CategoryTheory.BasedFunctor.RelativelyRepresentableWith`: **Definition 4.1.1**
  (`def:morphisms-representable-by-schemes`), a morphism of prestacks being
  representable by objects of `𝒮` (for `𝒮 = Sch`: by schemes), and having a property `P`
  of morphisms of `𝒮` stable under base change;
- `AlgebraicGeometry.IsAlgebraicSpace`: **Definition 4.1.2** (`def:algebraic-space`),
  the class of algebraic spaces — étale sheaves on `Sch` admitting a surjective étale
  presentation by a scheme, representable by schemes.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefMorphismsRepresentableBySchemes

open CategoryTheory Functor Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Let $f \colon S \to T$ be a morphism in a category $\cS$. Composition with $f$ defines
a morphism of representable prestacks $\cS/S \to \cS/T$ over $\cS$. -/
@[simps! toFunctor]
def overBased.map {S T : 𝒮} (f : S ⟶ T) : overBased S ⥤ᵇ overBased T where
  toFunctor := Over.map f
  w := Over.mapForget_eq f

/-- Composition of morphisms of a category induces composition of the morphisms of
representable prestacks: the morphism of prestacks `𝒮/S → 𝒮/V` induced by a composition
`f ≫ g` is the composition of the morphisms induced by `f` and by `g`.

Mathlib's `CategoryTheory.Over.mapComp` is only an isomorphism of functors, but
`Over.mapComp_eq` shows the two functors are equal, and a morphism of based categories is
determined by its underlying functor. -/
lemma overBased.map_comp {S T V : 𝒮} (f : S ⟶ T) (g : T ⟶ V) :
    overBased.map (f ≫ g) = (overBased.map f).comp (overBased.map g) :=
  BasedFunctor.ext_of_toFunctor_eq (Over.mapComp_eq f g)

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Let $S, T$ be objects of a category $\cS$. A morphism of representable prestacks
$F \colon \cS/S \to \cS/T$ determines a morphism $S \to T$ in $\cS$, namely the structure
morphism of the object $F(\operatorname{id}_S)$ of $\cS/T$. By the 2-Yoneda lemma this
induces a bijection between 2-isomorphism classes of morphisms of prestacks
$\cS/S \to \cS/T$ and morphisms $S \to T$. -/
def overHom {S T : 𝒮} (F : overBased S ⥤ᵇ overBased T) : S ⟶ T :=
  eqToHom (F.w_obj (Over.mk (𝟙 S))).symm ≫ (F.obj (Over.mk (𝟙 S))).hom

/-- The morphism classified by the identity morphism of prestacks `𝒮/S → 𝒮/S` is the
identity of `S`. -/
@[simp]
lemma overHom_id (S : 𝒮) : (BasedFunctor.id (overBased S)).overHom = 𝟙 S := by
  simp [overHom]
  rfl

/-- The morphism of `𝒮` classified by the morphism of prestacks `𝒮/S → 𝒮/T` induced by
`f : S ⟶ T` is `f` itself. -/
@[simp]
lemma overHom_map {S T : 𝒮} (f : S ⟶ T) : (overBased.map f).overHom = f := by
  simp [overHom, overBased.map]

/-- The structure morphism of the value of a morphism of prestacks `F : 𝒮/S → 𝒮/T` on an
object `X` of `𝒮/S` is the composition of the structure morphism of `X` with the morphism
`S ⟶ T` classified by `F`. -/
lemma obj_hom_eq_overHom {S T : 𝒮} (F : overBased S ⥤ᵇ overBased T) (X : Over S) :
    (F.obj X).hom = eqToHom (F.w_obj X) ≫ X.hom ≫ F.overHom := by
  have h₁ := Over.w (F.map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S)))
  have h₂ : (F.map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left =
      eqToHom (F.w_obj X) ≫ X.hom ≫ eqToHom (F.w_obj (Over.mk (𝟙 S))).symm := by
    have h₀ := Functor.congr_hom F.w (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))
    simp only [Functor.comp_map] at h₀
    exact h₀
  rw [← h₁, h₂]
  simp [overHom]

/-- The classified morphism is invariant under 2-isomorphism: two 2-isomorphic morphisms
of representable prestacks `𝒮/S → 𝒮/T` classify the same morphism `S ⟶ T` of `𝒮`. -/
lemma overHom_eq_of_iso {S T : 𝒮} {F G : overBased S ⥤ᵇ overBased T} (α : F ≅ G) :
    F.overHom = G.overHom := by
  have hlift := BasedNatTrans.app_isHomLift (α := α.hom) (Over.mk (𝟙 S))
  have h₁ : (α.hom.toNatTrans.app (Over.mk (𝟙 S))).left =
      eqToHom (F.w_obj (Over.mk (𝟙 S))) ≫ 𝟙 S ≫
        eqToHom (G.w_obj (Over.mk (𝟙 S))).symm := by
    exact IsHomLift.fac' ((overBased T).p)
      (𝟙 ((overBased S).p.obj (Over.mk (𝟙 S)))) (α.hom.toNatTrans.app (Over.mk (𝟙 S)))
  have h₂ := Over.w (α.hom.toNatTrans.app (Over.mk (𝟙 S)))
  simp only [overHom]
  rw [← h₂, h₁]
  simp

/-- Classified morphisms are functorial: the morphism classified by a composition
`𝒮/S → 𝒮/T → 𝒮/V` of morphisms of representable prestacks is the composition of the
classified morphisms. -/
@[simp]
lemma overHom_comp {S T V : 𝒮} (F : overBased S ⥤ᵇ overBased T)
    (G : overBased T ⥤ᵇ overBased V) : (F.comp G).overHom = F.overHom ≫ G.overHom := by
  have h := G.obj_hom_eq_overHom (F.obj (Over.mk (𝟙 S)))
  change eqToHom _ ≫ (G.obj (F.obj (Over.mk (𝟙 S)))).hom = _
  rw [h]
  simp [overHom]

/-- API lemma for Lemma 3.4.21 (the converse of `overHom_eq_of_iso`, for
representable targets): every morphism of representable prestacks `𝒮/S → 𝒮/T` is
2-isomorphic to the one induced by the morphism `S ⟶ T` it classifies. Together with
`overHom_eq_of_iso` this says that `overHom` is a bijection from 2-isomorphism classes of
morphisms `𝒮/S → 𝒮/T` onto `Mor(S, T)`, which is the 2-Yoneda lemma read for a
representable target.

The proof evaluates at `𝟙 S`: the 2-Yoneda equivalence `MOR(𝒮/S, 𝒮/T) ≌ (𝒮/T)(S)` turns
the required 2-isomorphism into an isomorphism in the fiber, and there both objects are
`S ⟶ T` read as objects of `𝒮/T` over `S`, compared by `obj_hom_eq_overHom`. -/
lemma nonempty_iso_overBased_map {S T : 𝒮} (F : overBased S ⥤ᵇ overBased T) :
    Nonempty (F ≅ overBased.map F.overHom) := by
  haveI := isEquivalence_twoYonedaEval (𝒳 := overBased T) S
  have hw : ((overBased T).p).obj (F.obj (Over.mk (𝟙 S))) = S := F.w_obj (Over.mk (𝟙 S))
  have hhom : (F.obj (Over.mk (𝟙 S))).hom = eqToHom hw ≫ (𝟙 S ≫ F.overHom) := by
    simpa using F.obj_hom_eq_overHom (Over.mk (𝟙 S))
  let φ : F.obj (Over.mk (𝟙 S)) ≅ (Over.map F.overHom).obj (Over.mk (𝟙 S)) :=
    Over.isoMk (eqToIso hw) hhom.symm
  have h1 : ((overBased T).p).IsHomLift (𝟙 S) φ.hom :=
    IsHomLift.of_fac' _ _ _ hw (by simp) (by simp [φ])
  have h2 : ((overBased T).p).IsHomLift (𝟙 S) φ.inv :=
    IsHomLift.of_fac' _ _ _ (by simp) hw (by simp [φ])
  have := h1
  have := h2
  let ψ : (twoYonedaEval (𝒳 := overBased T) S).obj F ≅
      (twoYonedaEval (𝒳 := overBased T) S).obj (overBased.map F.overHom) :=
    { hom := Fiber.homMk _ S φ.hom
      inv := Fiber.homMk _ S φ.inv
      hom_inv_id := by
        apply Fiber.hom_ext
        exact φ.hom_inv_id
      inv_hom_id := by
        apply Fiber.hom_ext
        exact φ.inv_hom_id }
  exact ⟨(twoYonedaEval (𝒳 := overBased T) S).preimageIso ψ⟩

/-- An equivalence of representable prestacks `𝒮/S → 𝒮/T` classifies an *isomorphism*
`S ⟶ T`. (Combine `nonempty_iso_overBased_map`, which replaces the equivalence by
`overBased.map` of the classified morphism, with
`CategoryTheory.Over.isIso_of_isEquivalence_map`.) -/
lemma isIso_overHom_of_isEquivalence {S T : 𝒮} (F : overBased S ⥤ᵇ overBased T)
    (hF : F.toFunctor.IsEquivalence) : IsIso F.overHom := by
  obtain ⟨e⟩ := nonempty_iso_overBased_map F
  have h1 : ((BasedNatTrans.forgetful (overBased S) (overBased T)).obj F).IsEquivalence := hF
  exact Over.isIso_of_isEquivalence_map _
    (Functor.isEquivalence_of_iso ((BasedNatTrans.forgetful _ _).mapIso e))

/-- The morphism classified by the composition of the morphisms of representable prestacks
induced by `f` and `g` is `f ≫ g`. (Stated separately from `overHom_comp` because the two
factors of such a composite often arrive with their sources written in different but
definitionally equal ways, which blocks `simp` from applying `overHom_map` afterwards.) -/
@[simp]
lemma overHom_map_comp_map {S T V : 𝒮} (f : S ⟶ T) (g : T ⟶ V) :
    ((overBased.map f).comp (overBased.map g)).overHom = f ≫ g := by
  rw [overHom_comp, overHom_map, overHom_map]

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Background definition for Definition 4.1.1 (the implicit notion
of a prestack represented by an object): let $\cX$ be a prestack over a category $\cS$
and let $S$ be an object of $\cS$. Then
$\cX$ *is represented by* $S$ if there is an equivalence $\cS/S \to \cX$ of prestacks. (We
record the condition on the underlying functor of a morphism of based categories; for
categories fibered in groupoids this is equivalent to being an equivalence in the
2-category of prestacks, cf.
`CategoryTheory.BasedCategory.isEquivalence_iff_full_and_faithful_and_essSurj`.) -/
def IsRepresentedBy (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (S : 𝒮) : Prop :=
  ∃ E : overBased S ⥤ᵇ 𝒳, E.toFunctor.IsEquivalence

/-- Background definition for Definition 4.1.1 (the implicit notion
of a prestack represented by a presheaf): let $\cX$ be a prestack over a category $\cS$
and let $F$ be a presheaf on $\cS$. Then
$\cX$ *is represented by* $F$ if there is an equivalence $\cX_F \to \cX$ of prestacks,
where $\cX_F$ is the prestack associated to $F$. For $\cS = \Sch$ and $F$ a sheaf this
expresses that the prestack $\cX$ "is" the sheaf $F$; combined with
`AlgebraicGeometry.IsAlgebraicSpace` it expresses that $\cX$ is an algebraic space. -/
def IsRepresentedByPresheaf (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (F : 𝒮ᵒᵖ ⥤ Type v₁) : Prop :=
  ∃ E : ofPresheaf F ⥤ᵇ 𝒳, E.toFunctor.IsEquivalence

/-- Let $S, T$ be objects of a category $\cS$. Applying the Yoneda embedding to an element
of $\Mor(T, S)$ obtained by the Yoneda lemma from a morphism of presheaves
$a \colon \Mor(-, T) \to \Mor(-, S)$ recovers $a$. -/
lemma _root_.CategoryTheory.yoneda_map_yonedaEquiv {S T : 𝒮}
    (a : yoneda.obj T ⟶ yoneda.obj S) : yoneda.map (yonedaEquiv a) = a :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- Let $S$ be an object of a category $\cS$. The canonical functor from the category of
pairs $(T, a \colon \Mor(-, T) \to \Mor(-, S))$ to the slice category $\cS/S$, sending a
pair to the morphism $T \to S$ given by the Yoneda lemma. It is an equivalence. -/
@[simps!]
def costructuredArrowYonedaToOver (S : 𝒮) :
    CostructuredArrow yoneda (yoneda.obj S) ⥤ Over S where
  obj c := Over.mk (yonedaEquiv c.hom : c.left ⟶ S)
  map {c d} f := Over.homMk f.left (by
    simp only [Over.mk_hom]
    rw [← CostructuredArrow.w f, ← yonedaEquiv_naturality]
    rfl)
  map_id c := by ext; simp
  map_comp f g := by ext; simp

/-- Let $S$ be an object of a category $\cS$. The canonical functor from the slice
category $\cS/S$ to the category of pairs $(T, a \colon \Mor(-, T) \to \Mor(-, S))$,
sending $f \colon T \to S$ to composition with $f$. It is an equivalence, quasi-inverse
to `CategoryTheory.BasedCategory.costructuredArrowYonedaToOver`. -/
@[simps!]
def overToCostructuredArrowYoneda (S : 𝒮) :
    Over S ⥤ CostructuredArrow yoneda (yoneda.obj S) where
  obj X := CostructuredArrow.mk (yoneda.map X.hom)
  map {X Y} φ := CostructuredArrow.homMk φ.left (by
    simp only [CostructuredArrow.mk_hom_eq_self]
    rw [← yoneda.map_comp, Over.w φ])
  map_id X := by ext; simp
  map_comp φ ψ := by ext; simp

/-- Let $S$ be an object of a category $\cS$. The category of pairs
$(T, a \colon \Mor(-, T) \to \Mor(-, S))$ is equivalent to the slice category $\cS/S$, by
the Yoneda lemma. -/
@[simps]
def costructuredArrowYonedaOverEquivalence (S : 𝒮) :
    CostructuredArrow yoneda (yoneda.obj S) ≌ Over S where
  functor := costructuredArrowYonedaToOver S
  inverse := overToCostructuredArrowYoneda S
  unitIso := NatIso.ofComponents
    (fun c => by
      dsimp
      exact CostructuredArrow.isoMk (Iso.refl _) (by
        simp only [overToCostructuredArrowYoneda_obj_left,
          costructuredArrowYonedaToOver_obj_left, Iso.refl_hom, Functor.map_id,
          Category.id_comp]
        exact yoneda_map_yonedaEquiv c.hom))
    (fun f => by ext; simp)
  counitIso := NatIso.ofComponents
    (fun X => by
      dsimp
      exact Over.isoMk (Iso.refl _) (by
        simp only [costructuredArrowYonedaToOver_obj_left,
          overToCostructuredArrowYoneda_obj_left, Iso.refl_hom, Category.id_comp,
          costructuredArrowYonedaToOver_obj_hom]
        exact (yonedaEquiv_yoneda_map X.hom).symm))
    (fun φ => by ext; simp)
  functor_unitIso_comp c := by ext; simp; rfl

instance (S : 𝒮) : (costructuredArrowYonedaToOver S).IsEquivalence :=
  (costructuredArrowYonedaOverEquivalence S).isEquivalence_functor

instance (S : 𝒮) : (overToCostructuredArrowYoneda S).IsEquivalence :=
  (costructuredArrowYonedaOverEquivalence S).isEquivalence_inverse

/-- The canonical equivalence from the prestack associated to the presheaf represented by
an object `S` to the representable prestack `𝒮/S`, as a morphism of based categories. -/
def ofPresheafYonedaToOverBased (S : 𝒮) : ofPresheaf (yoneda.obj S) ⥤ᵇ overBased S where
  toFunctor := costructuredArrowYonedaToOver S
  w := rfl

/-- The canonical equivalence from the representable prestack `𝒮/S` to the prestack
associated to the presheaf represented by `S`, as a morphism of based categories. -/
def overBasedToOfPresheafYoneda (S : 𝒮) : overBased S ⥤ᵇ ofPresheaf (yoneda.obj S) where
  toFunctor := overToCostructuredArrowYoneda S
  w := rfl

instance (S : 𝒮) : (ofPresheafYonedaToOverBased S).toFunctor.IsEquivalence :=
  inferInstanceAs (costructuredArrowYonedaToOver S).IsEquivalence

instance (S : 𝒮) : (overBasedToOfPresheafYoneda S).toFunctor.IsEquivalence :=
  inferInstanceAs (overToCostructuredArrowYoneda S).IsEquivalence

/-- A prestack represented by an object `S` is represented by the presheaf `Mor(-, S)`. -/
lemma IsRepresentedBy.isRepresentedByPresheaf {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮}
    (h : 𝒳.IsRepresentedBy S) : 𝒳.IsRepresentedByPresheaf (yoneda.obj S) := by
  obtain ⟨E, hE⟩ := h
  exact ⟨(ofPresheafYonedaToOverBased S).comp E,
    inferInstanceAs ((ofPresheafYonedaToOverBased S).toFunctor ⋙ E.toFunctor).IsEquivalence⟩

/-- A prestack represented by the presheaf `Mor(-, S)` is represented by `S`. -/
lemma IsRepresentedByPresheaf.isRepresentedBy {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮}
    (h : 𝒳.IsRepresentedByPresheaf (yoneda.obj S)) : 𝒳.IsRepresentedBy S := by
  obtain ⟨E, hE⟩ := h
  exact ⟨(overBasedToOfPresheafYoneda S).comp E,
    inferInstanceAs ((overBasedToOfPresheafYoneda S).toFunctor ⋙ E.toFunctor).IsEquivalence⟩

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- **Definition 4.1.1** (`def:morphisms-representable-by-schemes`): let
$F \colon \cX \to \cY$ be a morphism of prestacks over a category $\cS$. Then $F$
is *relatively representable* (for $\cS = \Sch$: *representable by schemes*, or
*schematic*) if for every object $S$ of $\cS$ and every morphism $\cS/S \to \cY$ of
prestacks, the fiber product $\cX \times_{\cY} \cS/S$ is represented by an object of
$\cS$. -/
def RelativelyRepresentable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (S : 𝒮) (g : overBased S ⥤ᵇ 𝒴), ∃ S' : 𝒮, (fiberProduct F g).IsRepresentedBy S'

/-- **Definition 4.1.1** (`def:morphisms-representable-by-schemes`) (the "has property
$\cP$" refinement): let $\cP$ be a property of morphisms of a category $\cS$ stable under
base change, and let $F \colon \cX \to \cY$ be a morphism of prestacks over $\cS$. Then
$F$ is relatively representable *with property $\cP$* if it is relatively representable
and for every morphism $\cS/S \to \cY$ from a representable prestack and every
representation $\cS/S' \to \cX \times_{\cY} \cS/S$ of the fiber product, the induced
morphism $S' \to S$ of $\cS$ has property $\cP$. For $\cS = \Sch$ this is the book's
"representable by schemes with property $\cP$" (e.g. surjective, étale, or smooth). -/
def RelativelyRepresentableWith (P : MorphismProperty 𝒮) {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentable ∧
    ∀ (S : 𝒮) (g : overBased S ⥤ᵇ 𝒴) (S' : 𝒮)
      (E : overBased S' ⥤ᵇ fiberProduct F g), E.toFunctor.IsEquivalence →
      P (E.comp (fiberProductSnd F g)).overHom

/-- A morphism of prestacks that is relatively representable with a property is relatively
representable. -/
lemma RelativelyRepresentableWith.relativelyRepresentable {P : MorphismProperty 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴}
    (h : F.RelativelyRepresentableWith P) : F.RelativelyRepresentable :=
  h.1

/-- Relative representability with a property is monotone in the property. -/
lemma RelativelyRepresentableWith.mono {P Q : MorphismProperty 𝒮} (hPQ : P ≤ Q)
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴}
    (h : F.RelativelyRepresentableWith P) : F.RelativelyRepresentableWith Q :=
  ⟨h.1, fun S g S' E hE => hPQ _ (h.2 S g S' E hE)⟩

end CategoryTheory.BasedFunctor

end DefMorphismsRepresentableBySchemes


section DefAlgebraicSpace

open CategoryTheory Functor Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Background presheaf-level definition for Definition 4.1.1, recalled from Mathlib: a morphism
`φ : F ⟶ G` of presheaves on `Sch` is *representable by schemes* if for every scheme `T`
and morphism `Mor(-, T) ⟶ G`, the fiber product `F ×_G Mor(-, T)` is a scheme. This is
Mathlib's relative representability with respect to the Yoneda embedding. -/
example {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (φ : F ⟶ G) : Prop :=
  yoneda.relativelyRepresentable φ

/- Background presheaf-level definition for Definition 4.1.1 (the "has property `P`"
refinement, recalled from Mathlib): for a property
`P` of morphisms of schemes stable under base change, a morphism of presheaves on `Sch`
representable by schemes *has property `P`* if all its base changes by morphisms from
schemes have `P`. This is Mathlib's `MorphismProperty.presheaf` (which includes the
representability). -/
example (P : MorphismProperty Scheme.{u}) {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (φ : F ⟶ G) :
    Prop :=
  P.presheaf φ

/-- **Definition 4.1.2** (`def:algebraic-space`): let $X$ be a presheaf on $\Sch$. Then
$X$ is an *algebraic space* if it is a sheaf for
the étale topology and there exist a scheme $U$ and a morphism $U \to X$ which is
representable by schemes, surjective, and étale (an *étale presentation* of $X$). -/
class IsAlgebraicSpace (X : Scheme.{u}ᵒᵖ ⥤ Type u) : Prop where
  isSheaf : Presieve.IsSheaf Scheme.etaleTopology X
  exists_presentation : ∃ (U : Scheme.{u}) (p : yoneda.obj U ⟶ X),
    MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p

/-- The identity of a presheaf is representable by schemes with any property `P` of
morphisms of schemes that respects isomorphisms and contains identities. (More generally
this holds for the relative representability of `MorphismProperty.relative` along any
fully faithful functor.) -/
lemma _root_.CategoryTheory.MorphismProperty.presheaf_id {C : Type*} [Category C]
    (P : MorphismProperty C) [P.RespectsIso] [P.ContainsIdentities]
    (F : Cᵒᵖ ⥤ Type _) : P.presheaf (𝟙 F) :=
  MorphismProperty.relative.of_exists fun a g =>
    ⟨a, g, 𝟙 a, by simpa using IsPullback.id_vert g, P.id_mem a⟩

/-- Supporting instance for Definition 4.1.2 (the following prose: schemes are
algebraic spaces): the functor of points $\Mor(-, X)$ of a scheme $X$
is an étale sheaf, and the identity is an étale presentation. -/
instance (X : Scheme.{u}) : IsAlgebraicSpace (yoneda.obj X) where
  isSheaf :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.etaleTopology) _
  exists_presentation := ⟨X, 𝟙 _, MorphismProperty.presheaf_id _ _⟩

/-- API lemma for Definition 4.1.2 (transport along an isomorphism): being an
algebraic space is invariant under isomorphism of presheaves. Both clauses transport — the
sheaf condition by `CategoryTheory.Presieve.isSheaf_iso`, and an étale presentation by
postcomposing with the isomorphism, since `MorphismProperty.presheaf` respects
isomorphisms. -/
theorem IsAlgebraicSpace.of_iso {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X]
    (e : X ≅ Y) : IsAlgebraicSpace Y where
  isSheaf := Presieve.isSheaf_iso Scheme.etaleTopology e (IsAlgebraicSpace.isSheaf (X := X))
  exists_presentation := by
    obtain ⟨U, p, hp⟩ := IsAlgebraicSpace.exists_presentation (X := X)
    exact ⟨U, p ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom p hp⟩

namespace IsAlgebraicSpace

variable (X : Scheme.{u}ᵒᵖ ⥤ Type u) [IsAlgebraicSpace X]

/-- An étale presentation scheme of an algebraic space `X`: a scheme `U` admitting a
surjective étale morphism `Mor(-, U) ⟶ X` representable by schemes, chosen using the
axiom of choice. -/
noncomputable def presentationScheme : Scheme.{u} :=
  (exists_presentation (X := X)).choose

/-- The étale presentation morphism `Mor(-, U) ⟶ X` from the chosen presentation scheme
of an algebraic space `X`. -/
noncomputable def presentation : yoneda.obj (presentationScheme X) ⟶ X :=
  (exists_presentation (X := X)).choose_spec.choose

/-- The chosen presentation of an algebraic space is representable by schemes, surjective
and étale. -/
lemma presheaf_surjective_etale_presentation :
    MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      (presentation X) :=
  (exists_presentation (X := X)).choose_spec.choose_spec

end IsAlgebraicSpace

end AlgebraicGeometry

end DefAlgebraicSpace


section DefMorphismsRepresentableBySchemes

open CategoryTheory Functor CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
  {𝒵 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (H : 𝒵 ⥤ᵇ 𝒴')

/-- API lemma for Definition 4.1.1 (transport along the
pasting law): if `𝒳 ×_𝒴 𝒵` is represented by an object `S`, then so is
`(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵`. -/
lemma IsRepresentedBy.of_fiberProductAssoc {S : 𝒮}
    (h : (fiberProduct F (H.comp G)).IsRepresentedBy S) :
    (fiberProduct (fiberProductSnd F G) H).IsRepresentedBy S := by
  obtain ⟨E, hE⟩ := h
  have h1 := hE
  have h2 := isEquivalence_fiberProductAssocInv F G H
  exact ⟨E.comp (fiberProductAssocInv F G H),
    Functor.isEquivalence_trans E.toFunctor (fiberProductAssocInv F G H).toFunctor⟩

/-- API lemma for Definition 4.1.1 (transport along the
pasting law, presheaf version): if `𝒳 ×_𝒴 𝒵` is represented by a presheaf `X`, then so
is `(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵`. -/
lemma IsRepresentedByPresheaf.of_fiberProductAssoc {X : 𝒮ᵒᵖ ⥤ Type v₁}
    (h : (fiberProduct F (H.comp G)).IsRepresentedByPresheaf X) :
    (fiberProduct (fiberProductSnd F G) H).IsRepresentedByPresheaf X := by
  obtain ⟨E, hE⟩ := h
  have h1 := hE
  have h2 := isEquivalence_fiberProductAssocInv F G H
  exact ⟨E.comp (fiberProductAssocInv F G H),
    Functor.isEquivalence_trans E.toFunctor (fiberProductAssocInv F G H).toFunctor⟩

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}

/-- API lemma for Definition 4.1.1 (stability under base
change): if `F : 𝒳 → 𝒴` is relatively representable and `G : 𝒴' → 𝒴` is any morphism of
prestacks, then the projection `𝒳 ×_𝒴 𝒴' → 𝒴'` is relatively representable. -/
lemma RelativelyRepresentable.fiberProductSnd {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentable) (G : 𝒴' ⥤ᵇ 𝒴) :
    (BasedCategory.fiberProductSnd F G).RelativelyRepresentable := by
  intro S g
  obtain ⟨S', hS'⟩ := hF S (g.comp G)
  exact ⟨S', IsRepresentedBy.of_fiberProductAssoc F G g hS'⟩

/-- API lemma for Definition 4.1.1 (stability under base
change, with a property): if `F : 𝒳 → 𝒴` is relatively representable with property `P`,
so is the projection `𝒳 ×_𝒴 𝒴' → 𝒴'`. -/
lemma RelativelyRepresentableWith.fiberProductSnd {P : MorphismProperty 𝒮} {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentableWith P) (G : 𝒴' ⥤ᵇ 𝒴) :
    (BasedCategory.fiberProductSnd F G).RelativelyRepresentableWith P := by
  refine ⟨hF.1.fiberProductSnd G, ?_⟩
  intro S g S' E hE
  have h1 := hE
  have h2 := isEquivalence_fiberProductAssoc F G g
  exact hF.2 S (g.comp G) S' (E.comp (fiberProductAssoc F G g))
    (Functor.isEquivalence_trans E.toFunctor (fiberProductAssoc F G g).toFunctor)

end CategoryTheory.BasedFunctor

end DefMorphismsRepresentableBySchemes
