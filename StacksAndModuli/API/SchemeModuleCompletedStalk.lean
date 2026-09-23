module

public import StacksAndModuli.API.CompletedLocalRing
public import StacksAndModuli.API.PresheafModuleStalkTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Completed stalks of scheme modules

The stalk of a sheaf of modules retains its natural module structure over the local
ring.  For a locally Noetherian scheme, scalar extension from that local ring to its
completion is faithfully flat.  Consequently, a morphism of scheme modules is an
isomorphism on a stalk whenever its scalar extension to the completed local ring is
bijective.

This file deliberately works with tensor-product completion rather than adic completion
of the module.  For finite stalk modules the two agree by
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, but faithful-flat reflection
does not require finite generation.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.stalkModule`: the module-valued stalk.
* `AlgebraicGeometry.Scheme.Modules.stalkLinearMap`: the linear map on stalks.
* `AlgebraicGeometry.Scheme.Modules.completedStalkModule`: scalar extension of a stalk
  module to the completed local ring.
* `AlgebraicGeometry.Scheme.Modules.completedStalkLinearMap`: scalar extension of a
  stalk map to the completed local ring.
* `AlgebraicGeometry.Scheme.Modules.isIso_stalkFunctor_map_of_completed_bijective`:
  completed-local bijectivity reflects to an isomorphism on the ordinary additive stalk.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The stalk of a scheme module, retaining its module structure over the local ring. -/
noncomputable abbrev stalkModule (M : X.Modules) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) :=
  PresheafOfModules.StalkTensor.colimitModule X.presheaf x M.val

/-- The linear map on module-valued stalks induced by a morphism of scheme modules. -/
noncomputable abbrev stalkLinearMap {M N : X.Modules} (f : M ⟶ N) (x : X) :
    stalkModule M x ⟶ stalkModule N x :=
  PresheafOfModules.StalkTensor.colimitMap X.presheaf x f.val

/-- After forgetting scalar multiplication, `stalkLinearMap` is the ordinary additive
map on stalks. -/
lemma forget_stalkLinearMap {M N : X.Modules} (f : M ⟶ N) (x : X) :
    (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map
        (stalkLinearMap f x) =
      (toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f := by
  exact PresheafOfModules.StalkTensor.forget_colimitMap X.presheaf x f.val

/-- The completion of the local ring of a locally Noetherian scheme is faithfully flat
over that local ring. -/
noncomputable instance completedLocalRing_faithfullyFlat
    [IsLocallyNoetherian X] (x : X) :
    Module.FaithfullyFlat (X.presheaf.stalk x) (X.completedLocalRing x) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The tensor-product completion of a module-valued stalk. -/
noncomputable abbrev completedStalkModule (M : X.Modules) (x : X) :=
  TensorProduct (X.presheaf.stalk x) (X.completedLocalRing x) (stalkModule M x)

/-- Scalar extension of a stalk map to the completed local ring. -/
noncomputable def completedStalkLinearMap
    {M N : X.Modules} (f : M ⟶ N) (x : X) :
    completedStalkModule M x →ₗ[X.presheaf.stalk x] completedStalkModule N x :=
  (stalkLinearMap f x).hom.lTensor (X.completedLocalRing x)

/-- Bijectivity after tensoring with the completed local ring reflects bijectivity of the
ordinary module-valued stalk map. -/
theorem stalkLinearMap_bijective_of_completed_bijective [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : Function.Bijective (completedStalkLinearMap f x)) :
    Function.Bijective (stalkLinearMap f x) := by
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    (X.presheaf.stalk x) (X.completedLocalRing x) (stalkLinearMap f x).hom).mp h

/-- A morphism of scheme modules is an isomorphism on an additive stalk if its scalar
extension to the completed local ring is bijective. -/
theorem isIso_stalkFunctor_map_of_completed_bijective [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : Function.Bijective (completedStalkLinearMap f x)) :
    IsIso ((toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
  have hlinear : Function.Bijective (stalkLinearMap f x) :=
    stalkLinearMap_bijective_of_completed_bijective f x h
  let _ : IsIso (stalkLinearMap f x) :=
    (ConcreteCategory.isIso_iff_bijective (stalkLinearMap f x)).mpr hlinear
  rw [← forget_stalkLinearMap f x]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

end
