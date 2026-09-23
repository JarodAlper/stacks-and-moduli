module

public import StacksAndModuli.API.SchemeModulesTensorSymmetry
public import StacksAndModuli.API.SchemeModulesTensorLocallyFree

/-!
# Triangle identities for pairings of module sheaves

This file records the mate identity obtained by applying a morphism to the left factor
of a coevaluation and then evaluating the paired factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A left triangle identity evaluates a morphism inserted into the left factor of
the coevaluation. -/
lemma pairing_left_triangle_mate
    (N D L : X.Modules)
    (coev : SheafOfModules.unit X.ringCatSheaf ⟶ tensor N D)
    (ev : tensor D N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (htriangle :
      (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫
          (tensorUnitIso N).hom = 𝟙 N)
    (f : N ⟶ L) :
    (tensorLeftUnitIso N).inv ≫
        tensorMapLeft (coev ≫ tensorMapLeft f D) N ≫
        (tensorAssocIso L D N).hom ≫ tensorMapRight L ev ≫
        (tensorUnitIso L).hom = f := by
  rw [tensorMapLeft_comp]
  have hassoc := tensorAssocIso_hom_naturality_left f D N
  have hex := tensorMap_exchange f ev
  have hunit := tensorUnitIso_naturality f
  calc
    (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          tensorMapLeft (tensorMapLeft f D) N ≫
          (tensorAssocIso L D N).hom ≫ tensorMapRight L ev ≫
          (tensorUnitIso L).hom =
        (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫
          tensorMapLeft f (tensor D N) ≫ tensorMapRight L ev ≫
          (tensorUnitIso L).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫ k ≫
          tensorMapRight L ev ≫ (tensorUnitIso L).hom) hassoc
    _ = (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫
          tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf) ≫
          (tensorUnitIso L).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ k ≫
          (tensorUnitIso L).hom) hex.symm
    _ = (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫
          (tensorUnitIso N).hom ≫ f := by
      exact congrArg
        (fun k ↦ (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫ k)
        hunit
    _ = 𝟙 N ≫ f := congrArg (fun k ↦ k ≫ f) htriangle
    _ = f := Category.id_comp f

end AlgebraicGeometry.Scheme.Modules

end

end
