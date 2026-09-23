module

public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.OverBasedYonedaEquivalence
public import StacksAndModuli.API.PrestackFiberProductAssoc
public import StacksAndModuli.API.PresheafPrestackHom
public import StacksAndModuli.API.PresheafPrestackMapPullback
public import StacksAndModuli.API.PresheafPrestackPullback
public import StacksAndModuli.API.ProductReassembly
public import StacksAndModuli.API.ProdMapPullback
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Composition lemmas for representable morphisms of prestacks

This file provides composition results that follow from the current representability
API without invoking descent for algebraic spaces. In particular, a representable
morphism remains representable after composing with a morphism representable by
schemes. The fully general composition theorem requires the separate theorem that
representability is étale-local on algebraic-space targets.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
  {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒵 : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- A representable morphism followed by a morphism representable by schemes is
representable. -/
theorem Representable.comp_relativelyRepresentable
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    [𝒵.p.IsFiberedInGroupoids] {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴 ⥤ᵇ 𝒵}
    (hF : Representable F) (hG : G.RelativelyRepresentable) :
    Representable (F.comp G) := by
  intro T g
  obtain ⟨S, E, hE⟩ := hG T g
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨X, hX, H, hH⟩ := hF S (E.comp (fiberProductFst G g))
  let _ : H.toFunctor.IsEquivalence := hH
  let _ := isEquivalence_fiberProductRightMap F (fiberProductFst G g) E
  let K := (H.comp (fiberProductRightMap F (fiberProductFst G g) E)).comp
    (pasteFwd F G g)
  refine ⟨X, hX, K, ?_⟩
  dsimp [K]
  let _ := Functor.isEquivalence_trans H.toFunctor
    (fiberProductRightMap F (fiberProductFst G g) E).toFunctor
  exact Functor.isEquivalence_trans
    (H.toFunctor ⋙
      (fiberProductRightMap F (fiberProductFst G g) E).toFunctor)
    (pasteFwd F G g).toFunctor

/-- Every morphism between algebraic spaces induces a representable morphism between
their associated prestacks. -/
theorem Representable.ofPresheafMap
    {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] [IsAlgebraicSpace Y]
    (f : X ⟶ Y) : Representable (ofPresheaf.map f) := by
  intro T g
  exact ⟨Limits.pullback f (CategoryTheory.BasedFunctor.ofPresheafHom g),
    IsAlgebraicSpace.pullback f (CategoryTheory.BasedFunctor.ofPresheafHom g),
    isRepresentedByPresheaf_ofPresheafPullback g⟩

/-- Precomposing a representable morphism by a morphism of algebraic spaces preserves
representability. -/
theorem Representable.comp_ofPresheafMap
    {Target : BasedCategory.{v₄, u₄} Scheme.{u}}
    [Target.p.IsFiberedInGroupoids]
    {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] [IsAlgebraicSpace Y]
    (f : X ⟶ Y) {G : ofPresheaf Y ⥤ᵇ Target} (hG : Representable G) :
    Representable ((ofPresheaf.map f).comp G) := by
  intro T g
  obtain ⟨A, hA, E, hE⟩ := hG T g
  let _ : E.toFunctor.IsEquivalence := hE
  let H := E.comp (fiberProductFst G g)
  let ψ := ofPresheafMapOfBasedFunctor H
  let P := ofPresheafMapPullback (φ := f) (ψ := ψ)
  have hP : IsAlgebraicSpace P := IsAlgebraicSpace.pullback f ψ
  let L := ofPresheafMapPullbackLift (φ := f) (ψ := ψ)
  let _ : L.toFunctor.IsEquivalence :=
    isEquivalence_ofPresheafMapPullbackLift
  let η := ofPresheafMapOfBasedFunctorIso H
  let R₁ := fiberProductMapRightIso (ofPresheaf.map f) η
  let _ : R₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso (ofPresheaf.map f) η
  let R₂ := fiberProductRightMap (ofPresheaf.map f) (fiberProductFst G g) E
  let _ : R₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (ofPresheaf.map f) (fiberProductFst G g) E
  let R₃ := pasteFwd (ofPresheaf.map f) G g
  let _ : R₃.toFunctor.IsEquivalence := isEquivalence_pasteFwd _ _ _
  let K := ((L.comp R₁).comp R₂).comp R₃
  refine ⟨P, hP, K, ?_⟩
  dsimp only [K]
  let _ : (L.comp R₁).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L.toFunctor R₁.toFunctor
  let _ : ((L.comp R₁).comp R₂).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (L.comp R₁).toFunctor R₂.toFunctor
  exact Functor.isEquivalence_trans ((L.comp R₁).comp R₂).toFunctor
    R₃.toFunctor

/-- The product of two representable morphisms of prestacks is representable. -/
theorem Representable.prodMap
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {𝒳' : BasedCategory.{v₄, u₄} Scheme.{u}}
    {𝒴' : BasedCategory.{v₅, u₅} Scheme.{u}}
    [𝒳'.p.IsFiberedInGroupoids] [𝒴'.p.IsFiberedInGroupoids]
    {F : BasedFunctor 𝒳 𝒴} {G : BasedFunctor 𝒳' 𝒴'}
    (hF : Representable F) (hG : Representable G) :
    Representable (prodMap F G) := by
  intro T g
  let p₁ := fiberProductFst 𝒴.toBase 𝒴'.toBase
  let p₂ := CategoryTheory.BasedCategory.fiberProductSnd
    𝒴.toBase 𝒴'.toBase
  let a := g.comp p₁
  let b := g.comp p₂
  obtain ⟨A, hA, E₁, hE₁⟩ := hF T a
  obtain ⟨B, hB, E₂, hE₂⟩ := hG T b
  let _ : E₁.toFunctor.IsEquivalence := hE₁
  let _ : E₂.toFunctor.IsEquivalence := hE₂
  let q₁ := CategoryTheory.BasedCategory.fiberProductSnd F a
  let q₂ := CategoryTheory.BasedCategory.fiberProductSnd G b
  let H₁ := E₁.comp q₁
  let H₂ := E₂.comp q₂
  let O := overBasedToOfPresheafYoneda T
  let I := ofPresheafYonedaToOverBased T
  let K₁ := H₁.comp O
  let K₂ := H₂.comp O
  let ψ₁ := ofPresheafMapOfBasedFunctor K₁
  let ψ₂ := ofPresheafMapOfBasedFunctor K₂
  let P := Limits.pullback ψ₁ ψ₂
  have hP : IsAlgebraicSpace P := IsAlgebraicSpace.pullback ψ₁ ψ₂
  let L := ofPresheafMapPullbackLift (φ := ψ₁) (ψ := ψ₂)
  let _ : L.toFunctor.IsEquivalence :=
    isEquivalence_ofPresheafMapPullbackLift
  let η₁ := ofPresheafMapOfBasedFunctorIso K₁
  let η₂ := ofPresheafMapOfBasedFunctorIso K₂
  let θ₁ : (ofPresheaf.map ψ₁).comp I ≅ H₁ :=
    (whiskerRightIso η₁ I).trans
      (whiskerLeftIso H₁ (overBasedYonedaCounitIso T))
  let θ₂ : (ofPresheaf.map ψ₂).comp I ≅ H₂ :=
    (whiskerRightIso η₂ I).trans
      (whiskerLeftIso H₂ (overBasedYonedaCounitIso T))
  let R₀ := fiberProductPostcomp (ofPresheaf.map ψ₁) (ofPresheaf.map ψ₂) I
  let _ : R₀.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp _ _ _
  let R₁ := fiberProductMapLeftIso θ₁ ((ofPresheaf.map ψ₂).comp I)
  let _ : R₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso _ _
  let R₂ := fiberProductMapRightIso H₁ θ₂
  let _ : R₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso _ _
  let R₃ := fiberProductRightMap H₁ q₂ E₂
  let _ : R₃.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap H₁ q₂ E₂
  let R₄ := fiberProductSymm H₁ q₂
  let _ : R₄.toFunctor.IsEquivalence := inferInstance
  let R₅ := fiberProductRightMap q₂ q₁ E₁
  let _ : R₅.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap q₂ q₁ E₁
  let R₆ := fiberProductSymm q₂ q₁
  let _ : R₆.toFunctor.IsEquivalence := inferInstance
  let R₇ := fiberProductAssoc F a q₂
  let _ : R₇.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F a q₂
  let R₈ := iteratedToProdMapPullback F G a b
  let _ : R₈.toFunctor.IsEquivalence :=
    isEquivalence_iteratedToProdMapPullback F G a b
  let ρ := prodLiftProjectionsIso g
  let R₉ := fiberProductMapRightIso
    (CategoryTheory.BasedCategory.prodMap F G) ρ
  let _ : R₉.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso _ _
  let C₀ := L.comp R₀
  let _ : C₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L.toFunctor R₀.toFunctor
  let C₁ := C₀.comp R₁
  let _ : C₁.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₀.toFunctor R₁.toFunctor
  let C₂ := C₁.comp R₂
  let _ : C₂.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₁.toFunctor R₂.toFunctor
  let C₃ := C₂.comp R₃
  let _ : C₃.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₂.toFunctor R₃.toFunctor
  let C₄ := C₃.comp R₄
  let _ : C₄.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₃.toFunctor R₄.toFunctor
  let C₅ := C₄.comp R₅
  let _ : C₅.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₄.toFunctor R₅.toFunctor
  let C₆ := C₅.comp R₆
  let _ : C₆.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₅.toFunctor R₆.toFunctor
  let C₇ := C₆.comp R₇
  let _ : C₇.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₆.toFunctor R₇.toFunctor
  let C₈ := C₇.comp R₈
  let _ : C₈.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₇.toFunctor R₈.toFunctor
  let E := C₈.comp R₉
  exact ⟨P, hP, E,
    Functor.isEquivalence_trans C₈.toFunctor R₉.toFunctor⟩

end AlgebraicGeometry.BasedFunctor
