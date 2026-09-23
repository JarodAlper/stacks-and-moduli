module

public import StacksAndModuli.API.ProjectiveGradedStrictlyPerfectExact

/-!
# Base change of noetherian Cech models

A noetherian model for a fixed-degree graded Cech complex remains a noetherian model after
an arbitrary further coefficient change.  The only comparison needed is the canonical
cancellation isomorphism between two successive tensor products and tensoring along the
composite ring map.

This separates the formal base-change step from the geometric approximation input: once a
family and its fixed-degree Cech model have descended to a noetherian coefficient ring, the
same model works over every later coefficient ring.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct

/-- Two successive coefficient changes of a graded module agree with coefficient change
along the composite algebra map. -/
noncomputable def baseChangeTransIso
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {n : ℕ} (M : GradedModule R n) :
    (M.baseChange A).baseChange B ≅ M.baseChange B := by
  let f : (M.baseChange A).baseChange B ⟶ M.baseChange B :=
    { app := fun d ↦ ModuleCat.ofHom
        (AlgebraTensorModule.cancelBaseChange R A B B (M.obj d)).toLinearMap
      comm := fun i d ↦ by
        apply ModuleCat.hom_ext
        exact (AlgebraTensorModule.lTensor_comp_cancelBaseChange R A B
          (M.mulX i d).hom) }
  exact isoOfBijective f fun d ↦
    (AlgebraTensorModule.cancelBaseChange R A B B (M.obj d)).bijective

namespace NoetherianCechModel

/-- Transport a noetherian fixed-degree Cech model across an isomorphism of its target
graded module. -/
noncomputable def ofIso
    {A : Type u} [CommRing A] {n : ℕ}
    {M N : GradedModule A n} {d : ℤ}
    (E : NoetherianCechModel M d) (e : M ≅ N) :
    NoetherianCechModel N d where
  coefficientRing := E.coefficientRing
  coefficientRingCommRing := E.coefficientRingCommRing
  coefficientRingNoetherian := E.coefficientRingNoetherian
  coefficientAlgebra := E.coefficientAlgebra
  model := E.model
  model_isFG := E.model_isFG
  flatCochain := E.flatCochain
  fibreVanishing := E.fibreVanishing
  baseChangeIso := E.baseChangeIso ≪≫ e

/-- A noetherian fixed-degree Cech model remains such a model after arbitrary coefficient
change.  Its noetherian coefficient ring, model, flatness, and fibre-vanishing data are
unchanged; only the comparison with the target graded module is extended. -/
noncomputable def baseChange
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} {M : GradedModule A n} {d : ℤ}
    (E : NoetherianCechModel M d) :
    NoetherianCechModel (M.baseChange B) d := by
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  letI : Algebra E.coefficientRing B :=
    ((algebraMap A B).comp (algebraMap E.coefficientRing A)).toAlgebra
  letI : IsScalarTower E.coefficientRing A B :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact
    { coefficientRing := E.coefficientRing
      coefficientRingCommRing := inferInstance
      coefficientRingNoetherian := inferInstance
      coefficientAlgebra := inferInstance
      model := E.model
      model_isFG := E.model_isFG
      flatCochain := E.flatCochain
      fibreVanishing := E.fibreVanishing
      baseChangeIso :=
        (baseChangeTransIso E.model).symm ≪≫ baseChangeMapIso B E.baseChangeIso }

/-- A noetherian Cech model remains a model after arbitrary coefficient change and a chosen
normalization isomorphism of the resulting graded module. -/
noncomputable def baseChangeOfIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} {M : GradedModule A n} {N : GradedModule B n} {d : ℤ}
    (E : NoetherianCechModel M d) (e : M.baseChange B ≅ N) :
    NoetherianCechModel N d :=
  (baseChange E).ofIso e

end NoetherianCechModel

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
