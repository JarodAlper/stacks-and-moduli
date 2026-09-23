module

public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent

/-!
# Naturality of the unit isomorphisms for the tensor product of scheme modules

`Scheme.Modules.tensorLeftUnitIso F : 𝒪_X ⊗ F ≅ F` is built from the left unitor of the
monoidal structure on presheaves of modules followed by the counit of the sheafification
adjunction.  Both are natural, so the isomorphism is natural in `F`; this file records that,
in the two forms a rewrite needs.

The inverse form is what identifies a graded module of sections of `𝒪(d)` with `Γ_*` of the
*structure sheaf*: `twistModule 𝒜 (unit) d` is `𝒪 ⊗ 𝒪(d)`, not `𝒪(d)` on the nose, and the
degree-raising map of `Γ_*` is `tensorMapRight (unit) (mulHom …)` while the one on
`Γ(𝒪(d), ⊤)` is `mulHom …` itself.  See `StacksAndModuli/API/ProjGammaStarStructure.lean`.

Also here, because it is what one needs immediately afterwards: taking sections of an
isomorphism of sheaves of modules gives a bijection
(`AlgebraicGeometry.Scheme.Modules.bijective_app_of_iso`).

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso_hom_naturality`;
* `AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso_inv_naturality`;
* `AlgebraicGeometry.Scheme.Modules.bijective_app_of_iso`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The left unit isomorphism is natural.**  Tensoring a morphism on the right with the
structure sheaf on the left is the morphism itself, after the unit identifications. -/
theorem tensorLeftUnitIso_hom_naturality {G G' : X.Modules} (ψ : G ⟶ G') :
    tensorMapRight (SheafOfModules.unit X.ringCatSheaf) ψ ≫ (tensorLeftUnitIso G').hom
      = (tensorLeftUnitIso G).hom ≫ ψ := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := Adjunction.counit_isIso_of_R_fully_faithful adj
  change (sheafification X).map (MonoidalCategoryStruct.whiskerLeft
      (C := X.PresheafOfModules) (𝟙_ (X.PresheafOfModules)) ψ.val) ≫
      ((sheafification X).map (λ_ G'.val).hom ≫ adj.counit.app G')
    = ((sheafification X).map (λ_ G.val).hom ≫ adj.counit.app G) ≫ ψ
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    MonoidalCategory.leftUnitor_naturality, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact adj.counit.naturality ψ

/-- **The left unit isomorphism is natural**, in the form used to transport a degree-raising
map along `𝒪 ⊗ F ≅ F`. -/
theorem tensorLeftUnitIso_inv_naturality {G G' : X.Modules} (ψ : G ⟶ G') :
    (tensorLeftUnitIso G).inv ≫ tensorMapRight (SheafOfModules.unit X.ringCatSheaf) ψ
      = ψ ≫ (tensorLeftUnitIso G').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact tensorLeftUnitIso_hom_naturality ψ

/-- **Sections of an isomorphism of sheaves of modules are bijective**, on every open. -/
theorem bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opensᵒᵖ) :
    Function.Bijective ((PresheafOfModules.Hom.app e.hom.val U).hom) := by
  have h1 : ∀ z, (PresheafOfModules.Hom.app e.inv.val U).hom
      ((PresheafOfModules.Hom.app e.hom.val U).hom z) = z :=
    fun z ↦ congrArg (fun ψ : M ⟶ M ↦ (PresheafOfModules.Hom.app ψ.val U).hom z) e.hom_inv_id
  have h2 : ∀ z, (PresheafOfModules.Hom.app e.hom.val U).hom
      ((PresheafOfModules.Hom.app e.inv.val U).hom z) = z :=
    fun z ↦ congrArg (fun ψ : N ⟶ N ↦ (PresheafOfModules.Hom.app ψ.val U).hom z) e.inv_hom_id
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end AlgebraicGeometry.Scheme.Modules

end

end
