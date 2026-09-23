module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksAndModuli.API.QuasicoherentObjectProperties

/-!
# Relative differentials on affine schemes

For a ring map `φ : R ⟶ A`, the expected affine model of the relative
differential sheaf on `Spec A` is the quasicoherent sheaf associated to the
Kähler differential module `Ω[A/R]`.  This file records that model and the
finite-locally-free conclusions supplied by standard smoothness.

The comparison between this model and
`Scheme.Hom.relativeDifferentials (Spec.map φ)` is deliberately not asserted
here: it requires identifying the inverse-image structure presheaf on affine
charts.  The declarations below isolate the commutative-algebra input needed
for that future comparison.

Main declarations:

* `AlgebraicGeometry.Scheme.affineRelativeDifferentials`: the tilde sheaf of
  `Ω[A/R]`;
* `affineRelativeDifferentials_isFiniteLocallyFree`: standard smoothness makes
  this model finite locally free;
* `affineRelativeDifferentials_isProjectiveOfRank`: the relative-dimension
  refinement gives the expected constant rank.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {R A : CommRingCat.{u}}

/-- The affine model of `Ω_{Spec A / Spec R}` associated to a ring map
`φ : R ⟶ A`: the quasicoherent sheaf attached to `Ω[A/R]`. -/
noncomputable def affineRelativeDifferentials (φ : R ⟶ A) :
    (Spec A).Modules :=
  AlgebraicGeometry.tilde (CommRingCat.KaehlerDifferential φ)

instance affineRelativeDifferentials_isQuasicoherent (φ : R ⟶ A) :
    (affineRelativeDifferentials φ).IsQuasicoherent := by
  change (AlgebraicGeometry.tilde
    (CommRingCat.KaehlerDifferential φ)).IsQuasicoherent
  infer_instance

/-- For a standard-smooth ring map, the affine differential model is finite
locally free. -/
theorem affineRelativeDifferentials_isFiniteLocallyFree (φ : R ⟶ A)
    (hφ : φ.hom.IsStandardSmooth) :
    Modules.IsFiniteLocallyFree (affineRelativeDifferentials φ) := by
  algebraize [φ.hom]
  let _ : Algebra.IsStandardSmooth R A := hφ.toAlgebra
  let M := CommRingCat.KaehlerDifferential φ
  let e := AlgebraicGeometry.tilde.isoTop M
  let _ : Module.Free A M := by
    change Module.Free A (_root_.KaehlerDifferential R A)
    infer_instance
  have hfin : Module.Finite A M := by
    change Module.Finite A (_root_.KaehlerDifferential R A)
    infer_instance
  have hproj : Module.Projective A M := by
    exact Module.Projective.of_free
  have hfin' : Module.Finite A
      (moduleSpecΓFunctor.obj (affineRelativeDifferentials φ)) :=
    Module.Finite.equiv e.toLinearEquiv
  have hproj' : Module.Projective A
      (moduleSpecΓFunctor.obj (affineRelativeDifferentials φ)) :=
    Module.Projective.of_equiv e.toLinearEquiv
  obtain ⟨hfinTop, hprojTop⟩ :=
    moduleSpecΓFunctor_finite_projective_top
      (affineRelativeDifferentials φ) hfin' hproj'
  exact Modules.isFiniteLocallyFree_of_top hfinTop hprojTop

/-- For a standard-smooth ring map of relative dimension `n`, the affine
differential model is finite locally free of constant rank `n`. -/
theorem affineRelativeDifferentials_isProjectiveOfRank (n : ℕ) (φ : R ⟶ A)
    [Nontrivial A]
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension n) :
    Modules.IsProjectiveOfRank n (affineRelativeDifferentials φ) := by
  algebraize [φ.hom]
  let _ : Algebra.IsStandardSmoothOfRelativeDimension n R A := hφ.toAlgebra
  let _ : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let M := CommRingCat.KaehlerDifferential φ
  let e := AlgebraicGeometry.tilde.isoTop M
  let _ : Module.Free A M := by
    change Module.Free A (_root_.KaehlerDifferential R A)
    infer_instance
  have hfin : Module.Finite A M := by
    change Module.Finite A (_root_.KaehlerDifferential R A)
    infer_instance
  have hproj : Module.Projective A M := by
    exact Module.Projective.of_free
  have hfin' : Module.Finite A
      (moduleSpecΓFunctor.obj (affineRelativeDifferentials φ)) :=
    Module.Finite.equiv e.toLinearEquiv
  have hproj' : Module.Projective A
      (moduleSpecΓFunctor.obj (affineRelativeDifferentials φ)) :=
    Module.Projective.of_equiv e.toLinearEquiv
  have hrankM : ∀ p : PrimeSpectrum A,
      Module.rankAtStalk M p = n := by
    intro p
    have hfinrank : Module.finrank A M = n := by
      apply Nat.cast_injective (R := Cardinal)
      rw [Module.finrank_eq_rank]
      exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
    have hfun := congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := A) (M := M)) p
    rw [hfinrank] at hfun
    exact hfun
  have hrank' : ∀ p : PrimeSpectrum A,
      Module.rankAtStalk
        (moduleSpecΓFunctor.obj (affineRelativeDifferentials φ)) p = n := by
    intro p
    exact (congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) p).symm.trans
      (hrankM p)
  obtain ⟨hfinTop, hprojTop, hrankTop⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_top
      (affineRelativeDifferentials φ) hfin' hproj' hrank'
  exact Modules.isProjectiveOfRank_of_top hfinTop hprojTop hrankTop

end AlgebraicGeometry.Scheme
