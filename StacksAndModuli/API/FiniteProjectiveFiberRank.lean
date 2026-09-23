module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Ranks of fibres of finite projective modules over local rings

Supporting API for the constancy of Hilbert polynomials in a flat family over a discrete
valuation ring.  Once cohomology and base change identifies the global sections of a fibre
with a scalar extension of a finite projective module on the base, their dimensions are
independent of the chosen field-valued point.
-/

@[expose] public section

universe u

open TensorProduct

/-- A finite projective module over a local ring has the same finite rank after arbitrary
base change to a field. -/
theorem Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing
    {R K M : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.finrank K (K ⊗[R] M) = Module.finrank R M := by
  letI : Module.Flat R M := inferInstance
  letI : Module.Free R M := Module.free_of_flat_of_isLocalRing
  exact Module.finrank_baseChange

/-- Transporting the scalar field through a ring equivalence does not change
the finite rank of a vector space.  On the left, the target vector space is
viewed as a source-field vector space through the equivalence. -/
theorem Module.finrank_compHom_eq_of_ringEquiv
    {K L V : Type u} [Field K] [Field L]
    (e : K ≃+* L) [AddCommGroup V] [Module L V] :
    letI : Algebra K L := e.toRingHom.toAlgebra
    letI : Module K V := Module.compHom V e.toRingHom
    Module.finrank K V = Module.finrank L V := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Module K V := Module.compHom V e.toRingHom
  letI : IsScalarTower K L V := IsScalarTower.of_compHom K L V
  have hKL : Module.finrank K L = 1 := by
    apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    exact e.bijective
  have htower := Module.finrank_mul_finrank K L V
  rw [hKL, one_mul] at htower
  exact htower.symm
