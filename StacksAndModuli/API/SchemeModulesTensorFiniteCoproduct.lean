module

public import StacksAndModuli.API.SchemeModulesTensor
public import StacksAndModuli.API.SheafOfModulesColimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Tensor products and finite coproducts of sheaves of modules

The tensor product of sheaves of modules is obtained by sheafifying the presheaf tensor
product. This file packages tensoring in the left variable as an additive functor and
deduces that it distributes over finite biproducts and finite coproducts.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable local instance sheafification_isLeftAdjoint :
    (sheafification X).IsLeftAdjoint :=
  (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).isLeftAdjoint

/-- Sheafification of presheaves of modules is additive. -/
noncomputable instance sheafification_additive : (sheafification X).Additive := by
  letI : HasFiniteBiproducts X.PresheafOfModules :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (sheafification X)
  exact Functor.additive_of_preservesBinaryBiproducts _

noncomputable local instance tensorRight_preservesColimits (G : X.PresheafOfModules) :
    PreservesColimitsOfSize.{u, u} (tensorRight G) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (tensorRight (show _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) from G)))

noncomputable local instance : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

noncomputable local instance : HasFiniteBiproducts X.PresheafOfModules :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

noncomputable local instance tensorRight_presheaf_additive (G : X.PresheafOfModules) :
    (tensorRight G).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight G)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Tensoring a sheaf of modules with `G` in the right tensor factor, as a functor in
the left tensor factor. -/
noncomputable def tensorRightFunctor (G : X.Modules) : X.Modules ⥤ X.Modules :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    tensorRight G.val ⋙ sheafification X

noncomputable instance (G : X.Modules) : (tensorRightFunctor G).Additive := by
  letI : (tensorRight G.val).Additive := tensorRight_presheaf_additive G.val
  letI : (sheafification X).Additive := sheafification_additive
  letI : (SheafOfModules.forget X.ringCatSheaf ⋙ tensorRight G.val).Additive :=
    inferInstance
  letI : (tensorRight G.val ⋙ sheafification X).Additive := inferInstance
  constructor
  intro F F' φ ψ
  change (sheafification X).map
      ((tensorRight G.val).map
        ((SheafOfModules.forget X.ringCatSheaf).map (φ + ψ))) = _
  calc
    _ = (sheafification X).map
        ((tensorRight G.val).map
          ((SheafOfModules.forget X.ringCatSheaf).map φ +
            (SheafOfModules.forget X.ringCatSheaf).map ψ)) := by
      rw [(SheafOfModules.forget X.ringCatSheaf).map_add]
    _ = (sheafification X).map
        ((tensorRight G.val).map
            ((SheafOfModules.forget X.ringCatSheaf).map φ) +
          (tensorRight G.val).map
            ((SheafOfModules.forget X.ringCatSheaf).map ψ)) := by
      rw [(tensorRight G.val).map_add]
    _ = (sheafification X).map
          ((tensorRight G.val).map
            ((SheafOfModules.forget X.ringCatSheaf).map φ)) +
        (sheafification X).map
          ((tensorRight G.val).map
            ((SheafOfModules.forget X.ringCatSheaf).map ψ)) := by
      rw [(sheafification X).map_add]
    _ = _ := rfl

/-- Tensoring in the right factor distributes over finite biproducts. -/
noncomputable def tensorFiniteBiproductIso {J : Type} [Finite J]
    (F : J → X.Modules) (G : X.Modules) :
    ((⨁ F) ⊗ₘ G) ≅ ⨁ (fun j ↦ F j ⊗ₘ G) :=
  (tensorRightFunctor G).mapBiproduct F

/-- Tensoring in the right factor distributes over finite coproducts. -/
noncomputable def tensorFiniteCoproductIso {J : Type} [Finite J]
    (F : J → X.Modules) (G : X.Modules) :
    ((∐ F) ⊗ₘ G) ≅ ∐ (fun j ↦ F j ⊗ₘ G) :=
  tensorLeftIso (biproduct.isoCoproduct F).symm G
    ≪≫ tensorFiniteBiproductIso F G
    ≪≫ biproduct.isoCoproduct (fun j ↦ F j ⊗ₘ G)

end AlgebraicGeometry.Scheme.Modules
