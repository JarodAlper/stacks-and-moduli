module

public import StacksAndModuli.API.PrestackProducts
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»

/-!
# The magic square

This module formalizes `exer:magic-square` (Exercise 3.4.38) of §3.4 (Prestacks)
of *Stacks and Moduli*, section label
`sec:prestacks`.

The canonical comparison from a fiber product `𝒳 ×_𝒴 𝒴'` to the fiber product of
`𝒳 ×_𝒮 𝒴' → 𝒴 ×_𝒮 𝒴` with the diagonal is an equivalence. Specializing `𝒳` and `𝒴'`
to representable prestacks is precisely the cartesian diagram in the exercise.

Main declaration:
- `CategoryTheory.BasedCategory.magicSquare_isCartesian`: the exercise for the
  representable prestacks associated to `S,T ∈ 𝒮`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ExerMagicSquare

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- API generalization used in the proof of Exercise 3.4.38: the canonical
comparison
`𝒳 ×_𝒴 𝒴' ⟶ (𝒳 ×_𝒮 𝒴') ×_(𝒴 ×_𝒮 𝒴) 𝒴`
induced by `(F,G)` and the diagonal is an equivalence. This is the categorical
magic-square statement; the next declaration specializes it to the representable
prestacks appearing in the book. -/
theorem isEquivalence_fiberProductToProdMapDiag
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductToProdMapDiag F G).toFunctor.IsEquivalence := by
  letI : (fiberProductToProdMapDiag F G).toFunctor.Faithful :=
    fiberProductToProdMapDiag_faithful F G
  letI : (fiberProductToProdMapDiag F G).toFunctor.Full :=
    fiberProductToProdMapDiag_full F G
  letI : (fiberProductToProdMapDiag F G).toFunctor.EssSurj :=
    fiberProductToProdMapDiag_essSurj F G
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- **Exercise 3.4.38** (`exer:magic-square`): for objects `S,T ∈ 𝒮`, a prestack
`𝒳 → 𝒮`, and morphisms of prestacks `a : 𝒮/S → 𝒳` and `b : 𝒮/T → 𝒳`, the square
whose top map is `a × b` and whose bottom map is the diagonal of `𝒳` is cartesian.
Here cartesianness means that its canonical comparison to the 2-fiber product is an
equivalence of categories. -/
theorem magicSquare_isCartesian (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (S T : 𝒮)
    (a : overBased S ⥤ᵇ 𝒳) (b : overBased T ⥤ᵇ 𝒳) :
    (fiberProductToProdMapDiag a b).toFunctor.IsEquivalence :=
  isEquivalence_fiberProductToProdMapDiag a b

end CategoryTheory.BasedCategory

end ExerMagicSquare
