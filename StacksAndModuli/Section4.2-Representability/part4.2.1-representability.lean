module

public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.FiberProductPresentationRepresentable
public import StacksAndModuli.API.AlgebraicSpaceDiagonal
public import StacksAndModuli.API.AlgebraicStackDiagonal
public import StacksAndModuli.API.MagicSquareInverse
public import StacksAndModuli.API.OfPresheafPairFiberProduct
public import StacksAndModuli.API.OverBasedProducts
public import StacksAndModuli.API.RelativeDiagonalBaseChange
public import StacksAndModuli.API.RelativeDiagonalFiber
public import StacksAndModuli.API.RelativePresheafOver
public import StacksAndModuli.API.SchemeRelationMapGeometry
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.6-criterion-for-sheaf-to-be-scheme»
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Representability of the diagonal

This module formalizes `thm:representability-of-the-diagonal` (Theorem 4.2.1),
`cor:morphisms-from-schemes-are-representable` (Corollary 4.2.3) and
`exer:diagonal-of-morphisms` (Exercise 4.2.4) of §4.2 (Representability of the diagonal) of
*Stacks and Moduli*, section
label `subsec:representability-of-the-diagonal`.

At the presheaf level the diagonal of a presheaf `X` on `Sch` is `Limits.diag X : X ⟶ X ⨯ X`.
At the prestack level we introduce the product of based categories as the fiber product over
the base (`CategoryTheory.BasedCategory.prod`, via `CategoryTheory.BasedCategory.base` and
`CategoryTheory.BasedCategory.toBase`), the diagonal `CategoryTheory.BasedCategory.diag` of a
prestack, and the relative diagonal `CategoryTheory.BasedFunctor.diag` of a morphism of
prestacks.

Main book results:
- `AlgebraicGeometry.IsAlgebraicSpace.relativelyRepresentable_diag` and
  `AlgebraicGeometry.IsAlgebraicStack.representable_diag`: the Representability of the
  Diagonal theorem;
- `CategoryTheory.BasedFunctor.representable_of_representable_diag`,
  `CategoryTheory.BasedFunctor.relativelyRepresentable_of_relativelyRepresentable_diag`,
  `CategoryTheory.BasedFunctor.representable_of_isAlgebraicStack`, and
  `AlgebraicGeometry.relativelyRepresentable_of_isAlgebraicSpace`: the four forms of the
  corollary on morphisms from schemes;
- `AlgebraicGeometry.BasedFunctor.Representable.relativelyRepresentable_diag` and
  `AlgebraicGeometry.BasedFunctor.representable_diag`: the two parts of
  `exer:diagonal-of-morphisms` on relative diagonals.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmRepresentabilityOfTheDiagonal

open CategoryTheory Functor Limits Opposite

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u

namespace CategoryTheory.MorphismProperty

/-- Let `ι : C ⥤ D` be a fully faithful functor and let `P` be a property of morphisms of
`C` stable under composition. If `f : W ⟶ X` and `g : Y ⟶ Z` are morphisms of `D` that are
relatively representable along `ι` with property `P`, then so is the product
`f × g : W ⨯ Y ⟶ X ⨯ Z`. -/
lemma relative_prodMap {C : Type u₂} {D : Type u₃} [Category.{v₂} C] [Category.{v₃} D]
    {ι : C ⥤ D} [ι.Faithful] [ι.Full] {P : MorphismProperty C} [P.IsStableUnderComposition]
    {W X Y Z : D} [Limits.HasBinaryProduct W Y] [Limits.HasBinaryProduct X Y]
    [Limits.HasBinaryProduct X Z] [Limits.HasBinaryProduct Y X]
    [Limits.HasBinaryProduct Z X] {f : W ⟶ X} {g : Y ⟶ Z} (hf : P.relative ι f)
    (hg : P.relative ι g) : P.relative ι (Limits.prod.map f g) := by
  open Limits in
  have h₁ : P.relative ι (prod.map f (𝟙 Y)) :=
    (relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_prod_fst_with_id f Y) hf
  have h₂ : P.relative ι (prod.map (𝟙 X) g) := by
    have h₂' : P.relative ι (prod.map g (𝟙 X)) :=
      (relative_isStableUnderBaseChange P).of_isPullback
        (IsPullback.of_prod_fst_with_id g X) hg
    exact (arrow_mk_iso_iff (P.relative ι)
      ((CategoryTheory.Arrow.isoMk (prod.braiding Y X) (prod.braiding Z X)
          (by dsimp; ext <;> simp)) :
        CategoryTheory.Arrow.mk (prod.map g (𝟙 X)) ≅
          CategoryTheory.Arrow.mk (prod.map (𝟙 X) g))).1 h₂'
  rw [show Limits.prod.map f g = Limits.prod.map f (𝟙 Y) ≫ Limits.prod.map (𝟙 X) g by
    ext <;> simp]
  exact comp_mem _ _ _ h₁ h₂

/-- Let `P` be a property of morphisms of a category `C` stable under composition. If two
morphisms of presheaves on `C` are representable with property `P`, then so is their
product. -/
lemma presheaf_prodMap {C : Type u₂} [Category.{v₂} C] {P : MorphismProperty C}
    [P.IsStableUnderComposition] {W X Y Z : Cᵒᵖ ⥤ Type v₂} {f : W ⟶ X} {g : Y ⟶ Z}
    (hf : P.presheaf f) (hg : P.presheaf g) : P.presheaf (Limits.prod.map f g) :=
  relative_prodMap hf hg

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

/- Proof-stage fact for Theorem 4.2.1: the diagonal
of a presheaf of sets is a (split) monomorphism — the Mathlib instance
`IsSplitMono (Limits.diag X)`, recalled here because the proof of the Representability of
the Diagonal uses it to see that the base change `R = U ×_X U → U × U` of the diagonal is
a monomorphism of schemes, hence separated. -/
example (X : Scheme.{u}ᵒᵖ ⥤ Type u) : IsSplitMono (Limits.diag X) :=
  inferInstance

/- **Equation 4.2.2** (`eqn:cube-of-representability`): the cartesian cube relating
`Q_T = X ×_{X × X} T`, its base change `Q_{T'} = R ×_{U × U} T'`, the étale presentation
`U → X`, and `R = U ×_X U`. It is a proof-internal diagram of the Representability of the
Diagonal and carries no separate formal statement; the two cartesian faces used in the
proof are the base-change squares realized by `Limits.pullback` in the presheaf
category. -/

/-- **Theorem 4.2.1** (`thm:representability-of-the-diagonal`) (part (1), Representability
of the Diagonal): the diagonal `Δ : X → X × X` of an algebraic space `X` is representable
by schemes. -/
theorem IsAlgebraicSpace.relativelyRepresentable_diag (X : Scheme.{u}ᵒᵖ ⥤ Type u)
    [IsAlgebraicSpace X] :
    CategoryTheory.yoneda.relativelyRepresentable (Limits.diag X) := by
  obtain ⟨U, p, hp⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  let R := hp.rep.pullback p
  let s : R ⟶ U := hp.rep.fst' p
  let t : R ⟶ U := hp.rep.snd p
  let r : R ⟶ U ⨯ U := prod.lift t s
  have hR : IsPullback (yoneda.map s) (yoneda.map t) p p :=
    hp.rep.isPullback' p
  have ht : Etale t := (hp.property_snd p).2
  let _ : Etale t := ht
  have hrMono : Mono r := by
    constructor
    intro Z a b hab
    apply hp.rep.hom_ext'
    · have hsnd := congrArg (fun q ↦ q ≫ prod.snd) hab
      simpa only [r, Category.assoc, prod.lift_snd] using hsnd
    · have hfst := congrArg (fun q ↦ q ≫ prod.fst) hab
      simpa only [r, Category.assoc, prod.lift_fst] using hfst
  let _ : Mono r := hrMono
  have hr :
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u}) r :=
    relationMap_locallyOfFiniteType_locallyQuasiFinite_isSeparated t s
  let e : yoneda.obj (U ⨯ U) ≅ yoneda.obj U ⨯ yoneda.obj U :=
    preservesLimitIso yoneda (pair U U) ≪≫
      HasLimit.isoOfNatIso (pairComp U U yoneda)
  let st : yoneda.obj R ⟶ yoneda.obj U ⨯ yoneda.obj U :=
    prod.lift (yoneda.map t) (yoneda.map s)
  have her : yoneda.map r ≫ e.hom = st := by
    apply prod.hom_ext <;>
      simp [r, e, st, pairComp, diagramIsoPair]
  have hst : MorphismProperty.presheaf
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u}) st := by
    rw [← her]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom _
      (MorphismProperty.relative_map hr)
  have hRel : IsPullback (yoneda.map t ≫ p) st
      (Limits.diag X) (prod.map p p) := by
    exact hR.flip.relation_diagonal
  have hprod : MorphismProperty.presheaf
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      (prod.map p p) :=
    MorphismProperty.presheaf_prodMap hp hp
  intro T g
  let T' := hprod.rep.pullback g
  let k := hprod.rep.fst g
  let pT := hprod.rep.snd g
  have hk : IsPullback k (yoneda.map pT) (prod.map p p) g :=
    hprod.rep.isPullback g
  have hpTEtale : Etale pT := (hprod.property_snd g).2
  have hpTSurjective : Surjective pT := (hprod.property_snd g).1
  let W := hst.rep.pullback k
  let fstW := hst.rep.fst k
  let sndW := hst.rep.snd k
  have hW : IsPullback fstW (yoneda.map sndW) st k :=
    hst.rep.isPullback k
  have hWΔ : IsPullback (fstW ≫ (yoneda.map t ≫ p))
      (yoneda.map sndW) (Limits.diag X) (yoneda.map pT ≫ g) := by
    rw [← hk.w]
    exact hW.paste_horiz hRel
  let Pabs := Limits.pullback (Limits.diag X) g
  let fstP := Limits.pullback.fst (Limits.diag X) g
  let η := Limits.pullback.snd (Limits.diag X) g
  have hP : IsPullback fstP η (Limits.diag X) g :=
    IsPullback.of_hasPullback _ _
  let liftW : yoneda.obj W ⟶ Pabs :=
    hP.lift (fstW ≫ (yoneda.map t ≫ p))
      (yoneda.map sndW ≫ yoneda.map pT) (by
        simpa only [Category.assoc] using hWΔ.w)
  have hWP : IsPullback liftW (yoneda.map sndW) η (yoneda.map pT) :=
    hWΔ.of_right' hP
  let eWP : Over.mk (yoneda.map sndW) ≅
      Over.mk (Limits.pullback.snd η (yoneda.map pT)) :=
    Over.isoMk hWP.isoPullback (by exact hWP.isoPullback_hom_snd)
  let eLocal : yoneda.obj (Over.mk sndW) ≅
      (Over.map pT).op ⋙ Presheaf.relativeOver η :=
    Presheaf.relativeOverYonedaIso (Over.mk sndW) ≪≫
      Presheaf.relativeOverMapIso eWP ≪≫
        Presheaf.relativeOverPullbackIso pT η
  let _ : IsAlgebraicSpace (X ⨯ X) := IsAlgebraicSpace.prod X X
  have hXX : Presieve.IsSheaf Scheme.etaleTopology (X ⨯ X) := by
    rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
    refine ObjectProperty.prop_of_isLimit
      (P := Presheaf.IsSheaf Scheme.etaleTopology)
      (limit.isLimit (pair X X)) ?_
    rintro ⟨j⟩
    cases j with
    | left =>
        rw [pair_obj_left, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact IsAlgebraicSpace.isSheaf (X := X)
    | right =>
        rw [pair_obj_right, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact IsAlgebraicSpace.isSheaf (X := X)
  have hPabsSheaf : Presieve.IsSheaf Scheme.etaleTopology Pabs := by
    dsimp only [Pabs]
    exact AlgebraicGeometry.isSheaf_pullback Scheme.etaleTopology _ _
      (IsAlgebraicSpace.isSheaf (X := X))
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (yoneda.obj T)) hXX
  let Frel : Sheaf (Scheme.etaleTopology.over T) (Type u) :=
    ⟨Presheaf.relativeOver η,
      (isSheaf_iff_isSheaf_of_type _ _).2
        (Presheaf.relativeOver_isSheaf Scheme.etaleTopology η hPabsSheaf)⟩
  let _ : Etale pT := hpTEtale
  let _ : Surjective pT := hpTSurjective
  have hLocal :
      (Scheme.etaleTopology.representableByProperty
        (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
          MorphismProperty Scheme.{u})).prop (.mk (op T'))
        ((Scheme.etaleTopology.overMapPullback (Type u) pT).obj Frel) := by
    refine ⟨Over.mk sndW, hst.property_snd k, ⟨?_⟩⟩
    exact eLocal
  obtain ⟨Z, _, ⟨eZ⟩⟩ :=
    MorphismProperty.presheaf_locallyQuasiFinite_isSeparated_of_pullback
      pT Frel hLocal
  let eArrow := Presheaf.relativeOverRepresentationArrowIso η Z eZ
  have heArrow_right : eArrow.hom.right = 𝟙 (yoneda.obj T) := by
    rfl
  have hIso : IsPullback eArrow.hom.left (yoneda.map Z.hom) η
      (𝟙 (yoneda.obj T)) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [← heArrow_right]
    exact eArrow.hom.w
  refine ⟨Z.left, Z.hom, eArrow.hom.left ≫ fstP, ?_⟩
  simpa using hIso.paste_horiz hP

/-- **Theorem 4.2.1** (`thm:representability-of-the-diagonal`) (part (2), Representability
of the Diagonal): the diagonal `Δ : 𝒳 → 𝒳 × 𝒳` of an algebraic stack `𝒳` is representable
(its base changes by morphisms from schemes are algebraic spaces). -/
theorem IsAlgebraicStack.representable_diag (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})
    [IsAlgebraicStack 𝒳] : BasedFunctor.Representable (BasedCategory.diag 𝒳) := by
  exact IsAlgebraicStack.representable_diag_of_presentation 𝒳

end AlgebraicGeometry

end ThmRepresentabilityOfTheDiagonal

section CorMorphismsFromSchemesAreRepresentable

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

/-- **Corollary 4.2.3** (`cor:morphisms-from-schemes-are-representable`) (part (1),
representable case): if the diagonal of a prestack `𝒳` over `Sch` is representable, then
every morphism `T → 𝒳` from a scheme is representable. Stated for an arbitrary prestack
where the book says "stack" — the argument only uses the magic square (see the section's
COMMENTARY.md). -/
theorem BasedFunctor.representable_of_representable_diag
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    (h : BasedFunctor.Representable (BasedCategory.diag 𝒳)) {T : Scheme.{u}}
    (F : overBased T ⥤ᵇ 𝒳) : BasedFunctor.Representable F := by
  intro S g
  let E₀ := overBasedProdComparison T S
  let H := prodMap F g
  obtain ⟨X, hX, E, hE⟩ := h (T ⨯ S) (E₀.comp H)
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : E₀.toFunctor.IsEquivalence := isEquivalence_overBasedProdComparison T S
  let E₁ := fiberProductRightMap (diag 𝒳) H E₀
  let _ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (diag 𝒳) H E₀
  let E₂ := fiberProductSymm (diag 𝒳) H
  let _ : E₂.toFunctor.IsEquivalence := inferInstance
  let E₃ := prodMapDiagToFiberProduct F g
  let _ : E₃.toFunctor.IsEquivalence :=
    isEquivalence_prodMapDiagToFiberProduct F g
  let E₂₃ := E₂.comp E₃
  let _ : E₂₃.toFunctor.IsEquivalence := by
    change (E₂.toFunctor ⋙ E₃.toFunctor).IsEquivalence
    infer_instance
  let E₁₂₃ := E₁.comp E₂₃
  let _ : E₁₂₃.toFunctor.IsEquivalence := by
    change (E₁.toFunctor ⋙ E₂₃.toFunctor).IsEquivalence
    infer_instance
  let Eall := E.comp E₁₂₃
  have hEall : Eall.toFunctor.IsEquivalence := by
    change (E.toFunctor ⋙ E₁₂₃.toFunctor).IsEquivalence
    infer_instance
  exact ⟨X, hX, Eall, hEall⟩

/-- **Corollary 4.2.3** (`cor:morphisms-from-schemes-are-representable`) (part (1),
representable-by-schemes case): if the diagonal of a prestack `𝒳` over `Sch` is
representable by schemes, then every morphism `T → 𝒳` from a scheme is representable by
schemes. Stated for an arbitrary prestack where the book says "stack" (see the section's
COMMENTARY.md). -/
theorem BasedFunctor.relativelyRepresentable_of_relativelyRepresentable_diag
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    (h : (BasedCategory.diag 𝒳).RelativelyRepresentable) {T : Scheme.{u}}
    (F : overBased T ⥤ᵇ 𝒳) : F.RelativelyRepresentable := by
  intro S g
  let E₀ := overBasedProdComparison T S
  let H := prodMap F g
  obtain ⟨S', E, hE⟩ := h (T ⨯ S) (E₀.comp H)
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : E₀.toFunctor.IsEquivalence := isEquivalence_overBasedProdComparison T S
  let E₁ := fiberProductRightMap (diag 𝒳) H E₀
  let _ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (diag 𝒳) H E₀
  let E₂ := fiberProductSymm (diag 𝒳) H
  let _ : E₂.toFunctor.IsEquivalence := inferInstance
  let E₃ := prodMapDiagToFiberProduct F g
  let _ : E₃.toFunctor.IsEquivalence :=
    isEquivalence_prodMapDiagToFiberProduct F g
  let E₂₃ := E₂.comp E₃
  let _ : E₂₃.toFunctor.IsEquivalence := by
    change (E₂.toFunctor ⋙ E₃.toFunctor).IsEquivalence
    infer_instance
  let E₁₂₃ := E₁.comp E₂₃
  let _ : E₁₂₃.toFunctor.IsEquivalence := by
    change (E₁.toFunctor ⋙ E₂₃.toFunctor).IsEquivalence
    infer_instance
  let Eall := E.comp E₁₂₃
  have hEall : Eall.toFunctor.IsEquivalence := by
    change (E.toFunctor ⋙ E₁₂₃.toFunctor).IsEquivalence
    infer_instance
  exact ⟨S', Eall, hEall⟩

/-- **Corollary 4.2.3** (`cor:morphisms-from-schemes-are-representable`) (part (2),
algebraic stacks): every morphism from a scheme to an algebraic stack is
representable. -/
theorem BasedFunctor.representable_of_isAlgebraicStack
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳] {T : Scheme.{u}}
    (F : overBased T ⥤ᵇ 𝒳) : BasedFunctor.Representable F :=
  BasedFunctor.representable_of_representable_diag
    (IsAlgebraicStack.representable_diag 𝒳) F

/-- **Corollary 4.2.3** (`cor:morphisms-from-schemes-are-representable`) (part (2),
algebraic spaces): every morphism of presheaves from a scheme to an algebraic space is
representable by schemes. -/
theorem relativelyRepresentable_of_isAlgebraicSpace {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    [IsAlgebraicSpace X] {T : Scheme.{u}} (φ : CategoryTheory.yoneda.obj T ⟶ X) :
    CategoryTheory.yoneda.relativelyRepresentable φ :=
  CategoryTheory.Functor.relativelyRepresentable.of_diag
    (IsAlgebraicSpace.relativelyRepresentable_diag X) φ

end AlgebraicGeometry

end CorMorphismsFromSchemesAreRepresentable

section ExerDiagonalOfMorphisms

open CategoryTheory Functor Limits

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Exercise 4.2.4** (`exer:diagonal-of-morphisms`) (part (a)): if `F : 𝒳 → 𝒴` is a
representable morphism of algebraic stacks (for example a morphism of algebraic spaces),
then the relative diagonal `𝒳 → 𝒳 ×_𝒴 𝒳` is representable by schemes.

For a test point `g` of `𝒳 ×_𝒴 𝒳`, the base change of `F` along the first underlying
point is an algebraic-space prestack by representability of `F`, so the relative
diagonal of its structural morphism is representable by schemes through the presheaf
diagonal of the algebraic space (Theorem 4.2.1). The comparison of that diagonal with
the fiber of `Δ_F` over `g` is the canonical base-change factorization of relative
diagonals. -/
theorem BasedFunctor.Representable.relativelyRepresentable_diag [IsAlgebraicStack 𝒳]
    [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴} (hF : BasedFunctor.Representable F) :
    F.diag.RelativelyRepresentable := by
  intro T g
  let G := (relativeDiagonalPointFst F g).comp F
  let K := baseChangeDiagonalTarget F G
  let C := baseChangeDiagonalComparison F G
  let _ : C.toFunctor.IsEquivalence :=
    isEquivalence_baseChangeDiagonalComparison F G
  obtain ⟨X, hX, E, hE⟩ := hF T G
  let _ : IsAlgebraicSpace X := hX
  let _ : E.toFunctor.IsEquivalence := hE
  let H := BasedCategory.fiberProductSnd F G
  have hM : (E.comp H).diag.RelativelyRepresentableWith
      (⊤ : CategoryTheory.MorphismProperty Scheme.{u}) :=
    CategoryTheory.BasedFunctor.relativelyRepresentableWith_top_diag_of_target_overBased
      (E.comp H) (IsAlgebraicSpace.relativelyRepresentable_diag X)
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  have hJ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((CategoryTheory.BasedNatTrans.forgetful _ _).mapIso β).symm
      ((CategoryTheory.BasedNatTrans.forgetful _ _).mapIso α)
  let _ : J.toFunctor.IsEquivalence := hJ
  have hJdiag := hM.diag_comp_of_isEquivalence J
  let eH : J.comp (E.comp H) ≅ H :=
    (eqToIso (CategoryTheory.BasedFunctor.comp_assoc J E H).symm).trans
      ((BasedCategory.isoWhiskerRight β H).trans
        (eqToIso (CategoryTheory.BasedFunctor.id_comp H)))
  have hHdiag : H.diag.RelativelyRepresentableWith
      (⊤ : CategoryTheory.MorphismProperty Scheme.{u}) :=
    hJdiag.diag_of_iso eH
  let D := BasedCategory.fiberProductSnd F.diag K
  have hCD : (C.comp D).RelativelyRepresentableWith
      (⊤ : CategoryTheory.MorphismProperty Scheme.{u}) := by
    dsimp only [C, D, K]
    rw [BasedCategory.baseChangeDiagonalComparison_comp_snd]
    exact hHdiag
  have hD : D.RelativelyRepresentableWith
      (⊤ : CategoryTheory.MorphismProperty Scheme.{u}) :=
    hCD.of_comp_isEquivalence C
  let l := BasedCategory.relativeDiagonalTargetLift F g
  let e := BasedCategory.relativeDiagonalTargetLiftIso F g
  let L₁ := BasedCategory.fiberProductAssoc F.diag K l
  let L₂ := BasedCategory.fiberProductMapRightIso F.diag e
  let _ : L₁.toFunctor.IsEquivalence :=
    BasedCategory.isEquivalence_fiberProductAssoc F.diag K l
  let _ : L₂.toFunctor.IsEquivalence :=
    BasedCategory.isEquivalence_fiberProductMapRightIso F.diag e
  obtain ⟨A, R, hR⟩ := hD.1 T l
  let _ : R.toFunctor.IsEquivalence := hR
  refine ⟨A, (R.comp L₁).comp L₂, ?_⟩
  change (R.toFunctor ⋙ L₁.toFunctor ⋙ L₂.toFunctor).IsEquivalence
  infer_instance

/-- **Exercise 4.2.4** (`exer:diagonal-of-morphisms`) (part (b)): if `F : 𝒳 → 𝒴` is a
morphism of algebraic stacks, then the relative diagonal `𝒳 → 𝒳 ×_𝒴 𝒳` is
representable. -/
theorem BasedFunctor.representable_diag [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
    (F : 𝒳 ⥤ᵇ 𝒴) : Representable F.diag := by
  intro T g
  let a := relativeDiagonalPointFst F g
  let b := relativeDiagonalPointSnd F g
  obtain ⟨A, hA, EA, hEA⟩ :=
    exists_isAlgebraicSpace_fiberProduct_of_representableDiagonal a b
      (IsAlgebraicStack.representable_diag 𝒳)
  obtain ⟨B, hB, EB, hEB⟩ :=
    exists_isAlgebraicSpace_fiberProduct_of_representableDiagonal
      (a.comp F) (b.comp F) (IsAlgebraicStack.representable_diag 𝒴)
  let _ : IsAlgebraicSpace A := hA
  let _ : IsAlgebraicSpace B := hB
  let _ : EA.toFunctor.IsEquivalence := hEA
  let _ : EB.toFunctor.IsEquivalence := hEB
  obtain ⟨LB, ⟨alphaB⟩, ⟨betaB⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor EB
  have hLB : LB.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' EB.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso betaB).symm
      ((BasedNatTrans.forgetful _ _).mapIso alphaB)
  let _ : LB.toFunctor.IsEquivalence := hLB
  let N := relativeDiagonalIsomMap F g
  let H := (EA.comp N).comp LB
  let ψ := ofPresheafMapOfBasedFunctor H
  have hH : Representable H :=
    (Representable.ofPresheafMap ψ).of_iso
      (ofPresheafMapOfBasedFunctorIso H)
  have hHEB : Representable (H.comp EB) :=
    hH.comp_target_isEquivalence EB
  let η : H.comp EB ≅ EA.comp N :=
    (eqToIso (BasedFunctor.comp_assoc (EA.comp N) LB EB)).trans
      ((isoWhiskerLeft (EA.comp N) betaB).trans
        (eqToIso (BasedFunctor.comp_id (EA.comp N))))
  have hEAN : Representable (EA.comp N) := hHEB.of_iso η
  have hN : Representable N := Representable.of_comp_isEquivalence EA hEAN
  obtain ⟨P, hP, R, hR⟩ := hN T (relativeDiagonalIsomSection F g)
  let K := isomMapFiberToRelativeDiagonalFiber F g
  have hK : K.toFunctor.IsEquivalence :=
    isEquivalence_isomMapFiberToRelativeDiagonalFiber F g
  exact ⟨P, hP, R.comp K,
    Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩

end AlgebraicGeometry

end ExerDiagonalOfMorphisms
