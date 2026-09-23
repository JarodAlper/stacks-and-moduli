module

public import StacksAndModuli.«Section4.8-Properness».«part4.8.1-definitions»

/-!
# Absolute properties of prestacks over `Sch`: proper, separated, finite type

`Spec ℤ` is the final scheme, so `Sch = Sch/Spec ℤ`, and a prestack over `Sch` is the same
thing as a prestack over `Spec ℤ`. Following the book, an *absolute* property of a prestack
`𝒳` — “`𝒳` is proper”, “`𝒳` is separated”, “`𝒳` is of finite type” — means the
corresponding property of its structure morphism `𝒳 → Spec ℤ` (“proper over `Spec ℤ`”).
In the library that structure morphism is `𝒳.toBase : 𝒳 ⥤ᵇ base Scheme`, the projection of
`𝒳` regarded as a based functor to `Sch` itself (`StacksAndModuli/API/PrestackProducts.lean`); the
absolute quasi-separatedness `AlgebraicGeometry.BasedCategory.IsQuasiSeparated` of §4.8.3
is already phrased this way. This file names the remaining absolute properties so that
theorems can be stated about the prestack itself rather than about its projection.

## Main declarations

* `AlgebraicGeometry.BasedCategory.UniversallyClosed`,
  `AlgebraicGeometry.BasedCategory.IsSeparated`, `AlgebraicGeometry.BasedCategory.FiniteType`:
  the absolute forms of `AlgebraicGeometry.BasedFunctor.UniversallyClosed`, `…IsSeparated`
  and `…FiniteType`, applied to `𝒳.toBase`;
* `AlgebraicGeometry.BasedCategory.IsProper`: universally closed, separated and of finite
  type, definitionally `AlgebraicGeometry.BasedFunctor.IsProper 𝒳.toBase`
  (`AlgebraicGeometry.BasedCategory.isProper_toBase_iff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedCategory

variable (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) [𝒳.p.IsFiberedInGroupoids]

/-- A prestack `𝒳` over `Sch` is *universally closed* (over `Spec ℤ`) if its structure
morphism `𝒳.toBase : 𝒳 → Sch = Sch/Spec ℤ` is universally closed in the sense of
Definition 4.8.1. -/
abbrev UniversallyClosed : Prop :=
  BasedFunctor.UniversallyClosed 𝒳.toBase

/-- A prestack `𝒳` over `Sch` is *separated* (over `Spec ℤ`) if its structure morphism
`𝒳.toBase : 𝒳 → Sch = Sch/Spec ℤ` is separated in the sense of Definition 4.8.1, i.e. the
diagonal `𝒳 → 𝒳 × 𝒳` is proper. -/
abbrev IsSeparated : Prop :=
  BasedFunctor.IsSeparated 𝒳.toBase

/-- A prestack `𝒳` over `Sch` is *of finite type* (over `Spec ℤ`) if its structure
morphism `𝒳.toBase : 𝒳 → Sch = Sch/Spec ℤ` is of finite type: locally of finite type and
quasi-compact. -/
abbrev FiniteType : Prop :=
  BasedFunctor.FiniteType 𝒳.toBase

/-- A prestack `𝒳` over `Sch` is *proper* (over `Spec ℤ`) if it is universally closed,
separated and of finite type over `Spec ℤ` — that is, if its structure morphism
`𝒳.toBase : 𝒳 → Sch = Sch/Spec ℤ` is proper in the sense of Definition 4.8.1
(`AlgebraicGeometry.BasedCategory.isProper_toBase_iff`). The conjunction is spelled out so
that a goal `IsProper 𝒳` splits into the three absolute properties. -/
abbrev IsProper : Prop :=
  UniversallyClosed 𝒳 ∧ IsSeparated 𝒳 ∧ FiniteType 𝒳

/-- Properness over `Spec ℤ` is properness of the structure morphism to the base. -/
theorem isProper_toBase_iff : BasedFunctor.IsProper 𝒳.toBase ↔ IsProper 𝒳 :=
  Iff.rfl

/-- Properness over `Spec ℤ` unpacked into its three constituents. -/
theorem isProper_iff :
    IsProper 𝒳 ↔ UniversallyClosed 𝒳 ∧ IsSeparated 𝒳 ∧ FiniteType 𝒳 :=
  Iff.rfl

variable {𝒳}

/-- A proper prestack is universally closed over `Spec ℤ`. -/
theorem IsProper.universallyClosed (h : IsProper 𝒳) : UniversallyClosed 𝒳 :=
  h.1

/-- A proper prestack is separated over `Spec ℤ`. -/
theorem IsProper.isSeparated (h : IsProper 𝒳) : IsSeparated 𝒳 :=
  h.2.1

/-- A proper prestack is of finite type over `Spec ℤ`. -/
theorem IsProper.finiteType (h : IsProper 𝒳) : FiniteType 𝒳 :=
  h.2.2

end AlgebraicGeometry.BasedCategory

end
