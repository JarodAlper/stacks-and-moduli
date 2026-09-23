module

public import StacksAndModuli.API.AffineSheafMorphismZeroLocus
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Finite-projective coefficient models for sheaf-morphism zero loci

The affine zero-locus API asks for equations valued in a finite free module.  Relative
Cohomology and Base Change naturally produces a finite projective module instead.  This
file bridges the two interfaces: a finite projective module is a retract of a finite free
module, and the retraction remains a retraction after every scalar extension.

The geometric input is deliberately isolated in
`Scheme.Modules.HasFiniteProjectiveVanishingModel.pullback_zero_iff`.  In the projective
application it is supplied by a finite twisted-free presentation of the source, eventual
vanishing for the target, and the arbitrary-base comparison for its global sections.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace LinearMap

/-- For a map into finite free coordinates, the coordinatewise scalar extension is zero
exactly when the ordinary tensor-product scalar extension is zero. -/
lemma baseChangeToPi_eq_zero_iff_baseChange_eq_zero
    {R A M : Type u} [CommRing R] [CommRing A] [AddCommGroup M] [Module R M]
    {r : ℕ} (φ : M →ₗ[R] (Fin r → R)) (f : R →+* A) :
    (letI : Algebra R A := f.toAlgebra;
      φ.baseChangeToPi f = 0 ↔ φ.baseChange A = 0) := by
  letI : Algebra R A := f.toAlgebra
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply (TensorProduct.piScalarRight R A A (Fin r)).injective
    have hx := LinearMap.congr_fun h x
    simpa [LinearMap.baseChangeToPi] using hx
  · intro h
    simp [LinearMap.baseChangeToPi, h]

end LinearMap

section FiniteProjectiveVanishingModel

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (pX : X ⟶ Spec (.of R))
variable {E F : X.Modules} (p : E ⟶ F)

/-- A finite base-ring model which detects universal vanishing of a sheaf morphism and
whose target is finite projective.

This is the intermediate form naturally produced by global sections of a sufficiently
positive twist.  The source is finite so that, after embedding the target in a finite free
module, the resulting coefficient ideal is finitely generated without a noetherian
hypothesis. -/
structure HasFiniteProjectiveVanishingModel where
  /-- The finite module carrying the inputs of the equation map. -/
  M : Type u
  [addCommGroupM : AddCommGroup M]
  [moduleM : Module R M]
  [finiteM : Module.Finite R M]
  /-- The finite projective module carrying the values of the equation map. -/
  N : Type u
  [addCommGroupN : AddCommGroup N]
  [moduleN : Module R N]
  [finiteN : Module.Finite R N]
  [projectiveN : Module.Projective R N]
  /-- The finite-projective-valued equation map over the base ring. -/
  coordinates : M →ₗ[R] N
  /-- Pullback vanishing is detected by scalar extension of `coordinates` after every
  affine base change. -/
  pullback_zero_iff : ∀ (A : Type u) [CommRing A] (f : R →+* A),
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      (letI : Algebra R A := f.toAlgebra;
        coordinates.baseChange A = 0)

namespace HasFiniteProjectiveVanishingModel

attribute [instance] addCommGroupM moduleM finiteM
  addCommGroupN moduleN finiteN projectiveN

/-- Transport a finite-projective vanishing model across a universally equivalent
pullback-zero condition.  This is useful when an autoequivalence such as twisting is used
to construct the finite presentation. -/
noncomputable def of_pullback_zero_iff
    {E' F' : X.Modules} {p' : E' ⟶ F'}
    (H : HasFiniteProjectiveVanishingModel pX p')
    (h : ∀ (A : Type u) [CommRing A] (f : R →+* A),
      (pullback
          (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
        (pullback
          (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p' = 0) :
    HasFiniteProjectiveVanishingModel pX p where
  M := H.M
  N := H.N
  coordinates := H.coordinates
  pullback_zero_iff A _ f := (h A f).trans (H.pullback_zero_iff A f)

/-- A chosen split embedding of a finite projective module into a finite free module. -/
structure FiniteFreeRetract (R N : Type u) [CommRing R] [AddCommGroup N]
    [Module R N] where
  rank : ℕ
  projection : (Fin rank → R) →ₗ[R] N
  inclusion : N →ₗ[R] (Fin rank → R)
  projection_comp_inclusion : projection.comp inclusion = LinearMap.id

/-- Finite projective modules admit a finite-free retract presentation. -/
noncomputable def finiteFreeRetract (R N : Type u) [CommRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    FiniteFreeRetract R N :=
  Classical.choice <| by
    obtain ⟨r, q, i, _hq, _hi, hqi⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R N
    exact ⟨⟨r, q, i, hqi⟩⟩

/-- Replace the finite projective target of a universal vanishing model by a finite free
target.  No choice of basis is required: finite projectivity supplies a split embedding
into `R^r`, and its split retraction proves that this embedding still detects zero after
arbitrary scalar extension. -/
noncomputable def toFiniteFreeVanishingModel
    (H : HasFiniteProjectiveVanishingModel pX p) :
    HasFiniteFreeVanishingModel pX p := by
  classical
  let D := finiteFreeRetract R H.N
  refine
    { M := H.M
      r := D.rank
      coordinates := D.inclusion.comp H.coordinates
      pullback_zero_iff := fun A _ f ↦ ?_ }
  rw [H.pullback_zero_iff A f]
  letI : Algebra R A := f.toAlgebra
  rw [LinearMap.baseChangeToPi_eq_zero_iff_baseChange_eq_zero]
  constructor
  · intro h
    rw [LinearMap.baseChange_comp, h]
    simp
  · intro h
    have hretract :
        D.projection.baseChange A ∘ₗ D.inclusion.baseChange A = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, D.projection_comp_inclusion,
        LinearMap.baseChange_id]
    calc
      H.coordinates.baseChange A =
          LinearMap.id.comp (H.coordinates.baseChange A) := by simp
      _ = (D.projection.baseChange A ∘ₗ D.inclusion.baseChange A) ∘ₗ
          H.coordinates.baseChange A := by rw [hretract]
      _ = D.projection.baseChange A ∘ₗ
          (D.inclusion.baseChange A ∘ₗ H.coordinates.baseChange A) := by
            rw [LinearMap.comp_assoc]
      _ = D.projection.baseChange A ∘ₗ
          (D.inclusion.comp H.coordinates).baseChange A := by
            rw [LinearMap.baseChange_comp]
      _ = 0 := by rw [h]; simp

/-- The free model obtained from a finite-projective one detects precisely the same
pullback-zero condition. -/
lemma toFiniteFreeVanishingModel_pullback_zero_iff
    (H : HasFiniteProjectiveVanishingModel pX p)
    (A : Type u) [CommRing A] (f : R →+* A) :
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      (letI : Algebra R A := f.toAlgebra;
        H.toFiniteFreeVanishingModel.coordinates.baseChangeToPi f = 0) :=
  H.toFiniteFreeVanishingModel.pullback_zero_iff A f

end HasFiniteProjectiveVanishingModel

end FiniteProjectiveVanishingModel

end AlgebraicGeometry.Scheme.Modules
