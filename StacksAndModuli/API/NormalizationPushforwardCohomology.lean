module

public import StacksAndModuli.API.ReducedSchemeNormalization
public import StacksAndModuli.API.FiniteDiscreteDominantResolution

/-!
# First cohomology and normalization pushforward

For a reduced scheme with finitely many irreducible components, the
component-generic scheme is finite and discrete.  Its canonical dominant map
to the normalization therefore supplies a flasque quasicoherent resolution of
the normalization's structure sheaf.  Since the normalization morphism is
integral, hence affine, pushforward preserves this resolution.

This proves bijectivity of the canonical comparison

`H¹(X, ν_* 𝒪_{X̃}) ⟶ H¹(X̃, 𝒪_{X̃})`

without assuming exactness of pushforward on arbitrary abelian sheaves.

## Main results

* `AlgebraicGeometry.Scheme.componentGenericScheme_discreteTopology`: the
  component-generic scheme of a reduced scheme is discrete.
* `AlgebraicGeometry.Scheme.normalizationMap_pushforwardCohomologyMap_one_bijective`:
  the canonical first-cohomology comparison for normalization is bijective.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)]

/-- The component-generic scheme of a reduced scheme with finitely many
irreducible components has the discrete topology. -/
noncomputable instance componentGenericScheme_discreteTopology :
    DiscreteTopology X.componentGenericScheme := by
  let _ : ∀ Z : irreducibleComponents X,
      DiscreteTopology
        (Spec (X.presheaf.stalk Z.property.1.genericPoint)) :=
    fun Z ↦ by
      let _ : Subsingleton
          (Spec (X.presheaf.stalk Z.property.1.genericPoint)) :=
        PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr
          (X.componentGenericStalk_isField Z)
      infer_instance
  exact (sigmaMk (fun Z : irreducibleComponents X ↦
    Spec (X.presheaf.stalk Z.property.1.genericPoint))).discreteTopology

/-- The canonical first-cohomology comparison along the normalization map of a
reduced scheme with finitely many irreducible components is bijective. -/
theorem normalizationMap_pushforwardCohomologyMap_one_bijective :
    Function.Bijective
      (Modules.pushforwardCohomologyMap X.normalizationMap
        (structureModule X.normalization) 1) := by
  let j := X.componentGenericToNormalization
  let _ : Finite X.componentGenericScheme := inferInstance
  let _ : DiscreteTopology X.componentGenericScheme := inferInstance
  let _ : IsReduced X.normalization := inferInstance
  let _ : IsDominant j := by
    dsimp [j, componentGenericToNormalization]
    infer_instance
  let _ : IsAffineHom X.normalizationMap := by
    infer_instance
  exact
    Modules.pushforwardCohomologyMap_one_bijective_structureModule_of_finiteDiscreteDominant
      j X.normalizationMap

end AlgebraicGeometry.Scheme

end
