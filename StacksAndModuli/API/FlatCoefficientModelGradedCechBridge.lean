module

public import StacksAndModuli.API.FlatCoefficientModelNoetherian
public import StacksAndModuli.API.ProjectiveGradedRelativeCBC
public import StacksAndModuli.API.ProjectiveGradedStrictlyPerfectExact
public import StacksAndModuli.API.ProjectiveGradedTotalFinite

/-!
# From flat coefficient models to graded Čech models

A flat coefficient model descends an ordinary module over a polynomial ring.  The projective
Čech construction additionally needs that ordinary model to carry the intended grading and
that the chosen grading have the required field-fibre vanishing in the fixed twist.  This file
isolates exactly those two extra pieces of data in `HasGradedCechRealization`.

Once such a realization is supplied, finite generation and flatness of every Čech cochain are
automatic: finite presentation of the ordinary model gives finite generation of the graded
model, while coefficient-flatness of the ordinary model descends first to each graded piece
and then to the Čech cochains.  The resulting theorem constructs the existing
`GradedModule.NoetherianCechModel` interface used by the Quot projectivity argument.

Thus this file is also a precise boundary statement.  The remaining passage from the
ring-theoretic `FlatCoefficientModel` API to the projective input is compatible descent of
the grading/base-change isomorphism and field-fibre vanishing; no further flatness or
noetherianity theorem is needed after that data exists.

For one fixed graded realization, relative Serre vanishing supplies the field-fibre condition
in all sufficiently large twists.  The resulting bound depends on the model; obtaining one
degree uniform over all affine charts and Quot families remains a separate geometric step.

Main declaration:

* `NoetherianFlatPolynomialModel.HasGradedCechRealization.toNoetherianCechModel`.
* `NoetherianFlatPolynomialModel.HasGradedRealization.exists_eventual_noetherianCechModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u w

open CategoryTheory

namespace Module.FinitePresentation.PolynomialModel

open AlgebraicGeometry.ProjectiveSpace

namespace NoetherianFlatPolynomialModel

/-- A grading on an ordinary noetherian flat polynomial model which recovers the specified
graded module after coefficient change. -/
def HasGradedRealization
    {A : Type u} [CommRing A] {n : ℕ}
    (M : GradedModule A n)
    (E : NoetherianFlatPolynomialModel A M.Total (Fin (n + 1))) : Prop :=
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  letI : AddCommGroup E.model := E.modelAddCommGroup
  letI : Module (MvPolynomial (Fin (n + 1)) E.coefficientRing) E.model :=
    E.modelModule
  ∃ N : GradedModule E.coefficientRing n,
    Nonempty (N.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing] E.model) ∧
    Nonempty (N.baseChange A ≅ M)

/-- A grading on a noetherian flat polynomial model which recovers the specified graded
module after coefficient change and has the required positive field-fibre Čech vanishing in
one degree.

The ordinary total-module comparison is kept separately from the graded base-change
comparison.  An ungraded polynomial-module equivalence does not determine either the grading
or compatibility of the variable maps. -/
def HasGradedCechRealization
    {A : Type u} [CommRing A] {n : ℕ}
    (M : GradedModule A n) (d : ℤ)
    (E : NoetherianFlatPolynomialModel A M.Total (Fin (n + 1))) : Prop :=
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  letI : AddCommGroup E.model := E.modelAddCommGroup
  letI : Module (MvPolynomial (Fin (n + 1)) E.coefficientRing) E.model :=
    E.modelModule
  ∃ N : GradedModule E.coefficientRing n,
    Nonempty (N.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing] E.model) ∧
    Nonempty (N.baseChange A ≅ M) ∧
    ∀ (K : Type u) [Field K] [Algebra E.coefficientRing K]
      (i : ℕ), 1 ≤ i → Subsingleton (((N.baseChange K).cechHgr i).obj d)

/-- A graded realization of a noetherian flat polynomial model gives a noetherian Čech model.

Finite generation and flatness of all Čech cochains are consequences, not additional
hypotheses: they are respectively inherited from finite presentation and coefficient-flatness
of the ordinary polynomial model. -/
theorem HasGradedCechRealization.toNoetherianCechModel
    {A : Type u} [CommRing A] {n : ℕ}
    {M : GradedModule A n} {d : ℤ}
    (E : NoetherianFlatPolynomialModel A M.Total (Fin (n + 1)))
    (h : E.HasGradedCechRealization M d) :
    Nonempty (GradedModule.NoetherianCechModel M d) := by
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  letI : AddCommGroup E.model := E.modelAddCommGroup
  letI : Module (MvPolynomial (Fin (n + 1)) E.coefficientRing) E.model :=
    E.modelModule
  obtain ⟨N, ⟨eTotal⟩, ⟨eBase⟩, hfib⟩ := h
  let S := MvPolynomial (Fin (n + 1)) E.coefficientRing
  letI : Module.FinitePresentation S E.model := E.modelFinitePresentation
  letI : Module.Finite S E.model := inferInstance
  have htotalFinite : Module.Finite S N.Total :=
    Module.Finite.equiv eTotal.symm
  have hNfg : GradedModule.IsFG N :=
    GradedModule.Total.isFG_of_finite_total N htotalFinite
  letI : Module E.coefficientRing E.model :=
    Module.compHom E.model
      (algebraMap E.coefficientRing
        (MvPolynomial (Fin (n + 1)) E.coefficientRing))
  letI : IsScalarTower E.coefficientRing S E.model :=
    IsScalarTower.of_compHom E.coefficientRing S E.model
  letI : IsScalarTower E.coefficientRing S N.Total := by
    infer_instance
  have htotalFlat : Module.Flat E.coefficientRing N.Total := by
    letI : Module.Flat E.coefficientRing E.model := E.modelFlat
    exact Module.Flat.of_linearEquiv
      (eTotal.restrictScalars E.coefficientRing)
  have hNflat : GradedModule.IsFlat N := by
    intro e
    letI : Module.Flat E.coefficientRing N.Total := htotalFlat
    apply Module.Flat.of_retract
      (GradedModule.Total.tof N e) (GradedModule.Total.tcomp N e)
    apply LinearMap.ext
    intro x
    exact GradedModule.Total.tcomp_tof N e x
  exact
    ⟨{ coefficientRing := E.coefficientRing
       coefficientRingCommRing := inferInstance
       coefficientRingNoetherian := inferInstance
       coefficientAlgebra := inferInstance
       model := N
       model_isFG := hNfg
       flatCochain := fun p ↦ hNflat.flat_cechCochain p d
       fibreVanishing := hfib
       baseChangeIso := eBase }⟩

/-- A compatible grading on a noetherian flat polynomial model gives noetherian Čech
models in every sufficiently large twist.

The field-fibre vanishing is derived from uniform relative Serre vanishing for this one
graded model.  The resulting threshold is model-dependent. -/
theorem HasGradedRealization.exists_eventual_noetherianCechModel
    {A : Type u} [CommRing A] {n : ℕ}
    {M : GradedModule A n}
    (E : NoetherianFlatPolynomialModel A M.Total (Fin (n + 1)))
    (h : E.HasGradedRealization M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel M d) := by
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  letI : AddCommGroup E.model := E.modelAddCommGroup
  letI : Module (MvPolynomial (Fin (n + 1)) E.coefficientRing) E.model :=
    E.modelModule
  obtain ⟨N, ⟨eTotal⟩, ⟨eBase⟩⟩ := h
  let S := MvPolynomial (Fin (n + 1)) E.coefficientRing
  letI : Module.FinitePresentation S E.model := E.modelFinitePresentation
  letI : Module.Finite S E.model := inferInstance
  have htotalFinite : Module.Finite S N.Total :=
    Module.Finite.equiv eTotal.symm
  have hNfg : GradedModule.IsFG N :=
    GradedModule.Total.isFG_of_finite_total N htotalFinite
  letI : Module E.coefficientRing E.model :=
    Module.compHom E.model
      (algebraMap E.coefficientRing
        (MvPolynomial (Fin (n + 1)) E.coefficientRing))
  letI : IsScalarTower E.coefficientRing S E.model :=
    IsScalarTower.of_compHom E.coefficientRing S E.model
  letI : IsScalarTower E.coefficientRing S N.Total := by
    infer_instance
  have htotalFlat : Module.Flat E.coefficientRing N.Total := by
    letI : Module.Flat E.coefficientRing E.model := E.modelFlat
    exact Module.Flat.of_linearEquiv
      (eTotal.restrictScalars E.coefficientRing)
  have hNflat : GradedModule.IsFlat N := by
    intro e
    letI : Module.Flat E.coefficientRing N.Total := htotalFlat
    apply Module.Flat.of_retract
      (GradedModule.Total.tof N e) (GradedModule.Total.tcomp N e)
    apply LinearMap.ext
    intro x
    exact GradedModule.Total.tcomp_tof N e x
  obtain ⟨d₀, hvan⟩ :=
    GradedModule.exists_uniform_subsingleton_cechHgr_baseChange
      (M := N) hNfg hNflat
  refine ⟨d₀, fun d hd ↦ ⟨?_⟩⟩
  exact
    { coefficientRing := E.coefficientRing
      coefficientRingCommRing := inferInstance
      coefficientRingNoetherian := inferInstance
      coefficientAlgebra := inferInstance
      model := N
      model_isFG := hNfg
      flatCochain := fun p ↦ hNflat.flat_cechCochain p d
      fibreVanishing := fun K _ _ i hi ↦ hvan K i hi d hd
      baseChangeIso := eBase }

end NoetherianFlatPolynomialModel

namespace FlatCoefficientModel

/-- A flat coefficient model gives the projective Čech input as soon as its ordinary
polynomial module has a compatible graded realization with field-fibre vanishing. -/
theorem toNoetherianCechModel_of_hasGradedCechRealization
    {R : Type w} {A : Type u}
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] {n : ℕ}
    {M : GradedModule A n} {d : ℤ}
    {D : PolynomialModel A (Fin (n + 1)) M.Total}
    (E : FlatCoefficientModel (R := R) D)
    (h : (FlatCoefficientModel.toNoetherianFlatPolynomialModel (R := R) E).HasGradedCechRealization
      M d) :
    Nonempty (GradedModule.NoetherianCechModel M d) :=
  h.toNoetherianCechModel
    (FlatCoefficientModel.toNoetherianFlatPolynomialModel (R := R) E)

/-- A flat coefficient model over a noetherian base gives noetherian Čech models in all
sufficiently large twists once its ordinary module has a compatible graded realization. -/
theorem exists_eventual_noetherianCechModel_of_hasGradedRealization
    {R : Type w} {A : Type u}
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] {n : ℕ}
    {M : GradedModule A n}
    {D : PolynomialModel A (Fin (n + 1)) M.Total}
    (E : FlatCoefficientModel (R := R) D)
    (h : (FlatCoefficientModel.toNoetherianFlatPolynomialModel (R := R) E).HasGradedRealization
      M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel M d) :=
  h.exists_eventual_noetherianCechModel
    (FlatCoefficientModel.toNoetherianFlatPolynomialModel (R := R) E)

end FlatCoefficientModel

end Module.FinitePresentation.PolynomialModel

end

end
