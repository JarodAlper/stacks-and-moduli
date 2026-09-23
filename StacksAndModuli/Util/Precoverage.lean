module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Singleton presieves and base change

Supporting API with no Stacks Project counterpart: the singleton specialization of
`CategoryTheory.Precoverage.mem_coverings_of_isPullback`.

A precoverage that is stable under base change carries that stability to singleton presieves,
which is the form used by the fpqc descent statements of §3.1: "`{f}` is an fpqc covering" is
rendered throughout as `Presieve.singleton f ∈ Scheme.fpqcPrecoverage S`, and base-changing a
covering morphism must again be a covering.

Main declarations:
- `CategoryTheory.Precoverage.mem_singleton_of_isPullback`: the singleton presieve of a
  base change of a covering morphism is a covering presieve.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Precoverage

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- If the singleton presieve on `f : T ⟶ S` is a covering for a precoverage stable under
base change, and `p₁ : P ⟶ Y` is a base change of `f` along `g : Y ⟶ S`, then the singleton
presieve on `p₁` is a covering of `Y`.

This is the singleton form of `CategoryTheory.Precoverage.mem_coverings_of_isPullback`. -/
theorem mem_singleton_of_isPullback {J : Precoverage C} [J.IsStableUnderBaseChange]
    {S T : C} {f : T ⟶ S} (hf : Presieve.singleton f ∈ J S)
    {Y P : C} {g : Y ⟶ S} {p₁ : P ⟶ Y} {p₂ : P ⟶ T} (h : IsPullback p₁ p₂ g f) :
    Presieve.singleton p₁ ∈ J Y := by
  rw [← Presieve.ofArrows_pUnit.{v}] at hf ⊢
  exact mem_coverings_of_isPullback (fun _ ↦ f) hf g (fun _ ↦ p₁) (fun _ ↦ p₂) fun _ ↦ h

end CategoryTheory.Precoverage
