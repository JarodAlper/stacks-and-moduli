module

public import StacksAndModuli.API.ProjectiveGradedStrictlyPerfectExact

/-!
# Noetherian models of fixed Cech complexes

For cohomology and base change in one fixed twist, a noetherian approximation need not
recover the entire graded module after extending coefficients.  It is enough to recover
the fixed Cech complex.  This weaker interface is important for projective families: the
standard-chart localizations are coefficient-flat even when the total graded module is not.

`NoetherianCechComplexModel` records the same noetherian finiteness, cochain-flatness, and
field-fibre vanishing data as `NoetherianCechModel`, but replaces its graded base-change
isomorphism by an isomorphism of the fixed Cech complexes.  The existing strictly-perfect
replacement construction only uses this weaker comparison.

Main declarations:

* `GradedModule.NoetherianCechComplexModel`;
* `GradedModule.NoetherianCechModel.toCechComplexModel`;
* `GradedModule.exists_eventual_noetherianCechComplexModel_of_flat_loc`;
* `GradedModule.NoetherianCechComplexModel.strictlyPerfectReplacement`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

/-- A noetherian model for one fixed-degree Cech complex.

Unlike `NoetherianCechModel`, the comparison after coefficient change is required only for
the Cech complex in the selected twist.  This is precisely the comparison used by the
strictly-perfect replacement construction. -/
structure NoetherianCechComplexModel {A : Type u} [CommRing A]
    (M : GradedModule A n) (d : ℤ) where
  coefficientRing : Type u
  [coefficientRingCommRing : CommRing coefficientRing]
  [coefficientRingNoetherian : IsNoetherianRing coefficientRing]
  [coefficientAlgebra : Algebra coefficientRing A]
  model : GradedModule coefficientRing n
  model_isFG : IsFG model
  flatCochain : ∀ p : ℕ,
    Module.Flat coefficientRing ((model.cechComplex d).X p)
  fibreVanishing : ∀ (K : Type u) [Field K] [Algebra coefficientRing K]
    (i : ℕ), 1 ≤ i → Subsingleton (((model.baseChange K).cechHgr i).obj d)
  baseChangeCechIso :
    (model.baseChange A).cechComplex d ≅ M.cechComplex d

namespace NoetherianCechModel

variable {A : Type u} [CommRing A] {M : GradedModule A n} {d : ℤ}

/-- A noetherian model of the whole graded module is, in particular, a model of every
fixed Cech complex. -/
noncomputable def toCechComplexModel (E : NoetherianCechModel M d) :
    NoetherianCechComplexModel M d where
  coefficientRing := E.coefficientRing
  coefficientRingCommRing := E.coefficientRingCommRing
  coefficientRingNoetherian := E.coefficientRingNoetherian
  coefficientAlgebra := E.coefficientAlgebra
  model := E.model
  model_isFG := E.model_isFG
  flatCochain := E.flatCochain
  fibreVanishing := E.fibreVanishing
  baseChangeCechIso := cechComplexMapIso E.baseChangeIso d

end NoetherianCechModel

/-- A finitely generated graded model over a noetherian coefficient ring whose standard-chart
localizations are coefficient-flat gives fixed-Cech-complex models in every sufficiently
large twist, provided those Cech complexes recover the desired complexes after extending
coefficients.

The comparison is deliberately allowed to depend on the twist.  This is the form needed for
tail presentations and chartwise constructions, where a global isomorphism of graded modules
would be unnecessarily strong. -/
theorem exists_eventual_noetherianCechComplexModel_of_flat_loc
    {R A : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A]
    (N : GradedModule R n) (hN : IsFG N)
    (hflat : ∀ a : Fin (n + 1), IsFlat (N.loc [a]))
    (M : GradedModule A n)
    (e : ∀ d : ℤ, (N.baseChange A).cechComplex d ≅ M.cechComplex d) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (NoetherianCechComplexModel M d) := by
  have hflatC : ∀ (d : ℤ) (p : ℕ), Module.Flat R ((N.cechComplex d).X p) :=
    fun d p ↦ flat_cechCochain_of_flat_loc N hflat p d
  obtain ⟨d₀, hd₀⟩ := exists_uniform_subsingleton_cechHgr_baseChange' hN hflatC
  refine ⟨d₀, fun d hd ↦ ⟨?_⟩⟩
  exact
    { coefficientRing := R
      coefficientRingCommRing := inferInstance
      coefficientRingNoetherian := inferInstance
      coefficientAlgebra := inferInstance
      model := N
      model_isFG := hN
      flatCochain := fun p ↦ hflatC d p
      fibreVanishing := fun K _ _ i hi ↦ hd₀ K i hi d hd
      baseChangeCechIso := e d }

namespace NoetherianCechComplexModel

variable {A : Type u} [CommRing A] {M : GradedModule A n} {d : ℤ}

/-- A noetherian fixed-Cech-complex model supplies the universal strictly-perfect
replacement over the original coefficient ring. -/
noncomputable def strictlyPerfectReplacement (E : NoetherianCechComplexModel M d) :
    CochainComplex.StrictlyPerfectReplacement (M.cechComplex d) := by
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  let D := strictlyPerfectReplacement_cechComplex_baseChange_of_noetherian
    E.model E.model_isFG d E.flatCochain E.fibreVanishing A
  exact CochainComplex.StrictlyPerfectReplacement.ofIso
    ((E.model.baseChange A).cechComplex d) D E.baseChangeCechIso

end NoetherianCechComplexModel

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
