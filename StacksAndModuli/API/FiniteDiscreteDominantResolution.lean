module

public import StacksAndModuli.API.FiniteDiscreteTopology
public import StacksAndModuli.API.AffinePushforwardExactQuasicoherent
public import StacksAndModuli.API.QuasicoherentCokernel
public import StacksAndModuli.API.SheafCohomologyPushforwardAcyclicResolution
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The finite-discrete dominant resolution

Let `j : D ⟶ X` be a dominant morphism from a finite discrete scheme to a
reduced scheme.  The unit map embeds the structure sheaf of `X` into the
pushforward of the structure sheaf of `D`.  Its cokernel gives a short exact
sequence

`0 ⟶ 𝒪_X ⟶ j_* 𝒪_D ⟶ 𝒱_j ⟶ 0`.

The middle term is flasque, while all three terms are quasicoherent.  Therefore
an affine morphism out of `X` preserves this resolution and induces the
canonical isomorphism on first cohomology.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.finiteDiscreteFunctionModule`: the module
  `j_* 𝒪_D`.
* `AlgebraicGeometry.Scheme.Hom.finiteDiscretePrincipalPartsModule`: the
  quotient of `j_* 𝒪_D` by `𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.finiteDiscreteFunctionComplex`: the resulting
  short complex.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finiteDiscreteFunctionComplex_shortExact`:
  the finite-discrete function complex is short exact.
* `Modules.pushforwardCohomologyMap_one_bijective_structureModule_of_finiteDiscreteDominant`:
  the canonical `H¹` pushforward comparison is bijective for an affine
  morphism whose source admits such a finite-discrete dominant cover.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {D X : Scheme.{u}} (j : D ⟶ X)

/-- The pushforward `j_* 𝒪_D` associated to a morphism `j : D ⟶ X`. -/
abbrev finiteDiscreteFunctionModule : X.Modules :=
  (Modules.pushforward j).obj (structureModule D)

/-- The underlying additive sheaf of `finiteDiscreteFunctionModule`. -/
abbrev finiteDiscreteFunctionAddSheaf :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj
    j.finiteDiscreteFunctionModule

/-- If the source is discrete, `j_* 𝒪_D` is flasque. -/
instance finiteDiscreteFunctionModule_isFlasque [DiscreteTopology D] :
    TopCat.Presheaf.IsFlasque j.finiteDiscreteFunctionAddSheaf.obj := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} D :=
    (SheafOfModules.toSheaf D.ringCatSheaf).obj (structureModule D)
  let _ : F.IsFlasque := TopCat.Sheaf.isFlasque_of_discreteTopology F
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F j.base

/-- The unit map from the structure sheaf to `j_* 𝒪_D`. -/
def structureToFiniteDiscreteFunction :
    structureModule X ⟶ j.finiteDiscreteFunctionModule :=
  SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom

/-- For a dominant morphism from a finite discrete scheme to a reduced scheme,
the unit map into `j_* 𝒪_D` is a monomorphism. -/
instance structureToFiniteDiscreteFunction_mono
    [Finite D] [DiscreteTopology D] [IsReduced X] [IsDominant j] :
    Mono j.structureToFiniteDiscreteFunction := by
  let _ : IsAffineHom j :=
    isAffineHom_of_finite_of_discreteTopology j
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  apply Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf)
  change Mono j.structureToFiniteDiscreteFunction.val
  apply PresheafOfModules.mono_of_injective
  intro U a b hab
  exact j.app_injective U.unop hab

/-- The quotient of `j_* 𝒪_D` by the image of `𝒪_X`. -/
abbrev finiteDiscretePrincipalPartsModule : X.Modules :=
  cokernel j.structureToFiniteDiscreteFunction

/-- The quotient map to the finite-discrete principal-parts module. -/
def finiteDiscretePrincipalPartsProjection :
    j.finiteDiscreteFunctionModule ⟶
      j.finiteDiscretePrincipalPartsModule :=
  cokernel.π j.structureToFiniteDiscreteFunction

/-- The structure-sheaf resolution associated to a finite discrete dominant
morphism. -/
abbrev finiteDiscreteFunctionComplex
    [Finite D] [DiscreteTopology D] [IsReduced X] [IsDominant j] :
    ShortComplex X.Modules :=
  ShortComplex.mk j.structureToFiniteDiscreteFunction
    j.finiteDiscretePrincipalPartsProjection (by
      simp [finiteDiscretePrincipalPartsProjection])

/-- The finite-discrete function complex is short exact. -/
theorem finiteDiscreteFunctionComplex_shortExact
    [Finite D] [DiscreteTopology D] [IsReduced X] [IsDominant j] :
    j.finiteDiscreteFunctionComplex.ShortExact := by
  exact
    { exact := by
        simpa [finiteDiscreteFunctionComplex,
          finiteDiscretePrincipalPartsProjection] using
          ShortComplex.exact_cokernel j.structureToFiniteDiscreteFunction
      mono_f := inferInstance
      epi_g := by
        dsimp [finiteDiscreteFunctionComplex,
          finiteDiscretePrincipalPartsProjection]
        infer_instance }

/-- For a finite discrete source, `j_* 𝒪_D` is quasicoherent. -/
instance finiteDiscreteFunctionModule_isQuasicoherent
    [Finite D] [DiscreteTopology D] :
    j.finiteDiscreteFunctionModule.IsQuasicoherent := by
  let _ : IsAffineHom j :=
    isAffineHom_of_finite_of_discreteTopology j
  let _ : (structureModule D).IsQuasicoherent :=
    Modules.unit_isQuasicoherent D
  exact Modules.isQuasicoherent_pushforward_of_isAffineHom j
    (structureModule D)

/-- The finite-discrete principal-parts module is quasicoherent. -/
instance finiteDiscretePrincipalPartsModule_isQuasicoherent
    [Finite D] [DiscreteTopology D] :
    j.finiteDiscretePrincipalPartsModule.IsQuasicoherent := by
  let _ : (structureModule X).IsQuasicoherent :=
    Modules.unit_isQuasicoherent X
  exact Modules.isQuasicoherent_cokernel
    j.structureToFiniteDiscreteFunction

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {D X Y : Scheme.{u}} (j : D ⟶ X)

/-- If a reduced scheme admits a dominant map from a finite discrete scheme,
then the canonical first-cohomology comparison along any affine morphism out of
it is bijective. -/
theorem pushforwardCohomologyMap_one_bijective_structureModule_of_finiteDiscreteDominant
    [Finite D] [DiscreteTopology D] [IsReduced X] [IsDominant j]
    (f : X ⟶ Y) [IsAffineHom f] :
    Function.Bijective
      (pushforwardCohomologyMap f (structureModule X) 1) := by
  let _ : (structureModule X).IsQuasicoherent :=
    unit_isQuasicoherent X
  let Q : ShortComplex X.Modules :=
    j.finiteDiscreteFunctionComplex
  have hQ : Q.ShortExact :=
    j.finiteDiscreteFunctionComplex_shortExact
  have hRQ : (Q.map (pushforward f)).ShortExact :=
    shortExact_map_pushforward_of_isAffineHom f hQ
  let _ : TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q.X₂) := by
    change TopCat.Sheaf.IsFlasque j.finiteDiscreteFunctionAddSheaf
    exact Hom.finiteDiscreteFunctionModule_isFlasque j
  have hcmp : Function.Bijective
      (pushforwardCohomologyMap f Q.X₁ 1) :=
    pushforwardCohomologyMap_one_bijective_of_shortExact f hQ hRQ
  change Function.Bijective
    (pushforwardCohomologyMap f (structureModule X) 1) at hcmp
  exact hcmp

end AlgebraicGeometry.Scheme.Modules

end
