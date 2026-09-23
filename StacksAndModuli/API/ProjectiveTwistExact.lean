module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.SchemeModulesTensorExact

/-!
# Exactness of polynomial projective twists

This file begins the exactness package for Serre twists on polynomial projective
space.  The degree-one coordinate opens trivialize every twisting sheaf.  The generic
local-triviality theorem for tensor products therefore shows that tensoring by a
twisting sheaf preserves monomorphisms.

Tensoring by a twist also preserves all colimits.  Hence it preserves homology and
finite limits, sends short exact sequences to short exact sequences, and canonically
identifies the twist of a kernel with the kernel of the twisted morphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory TopologicalSpace
open ProjectiveSpectrum

universe u

namespace ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (i : Type) {R : Type u} [CommRing R]

/-- Tensoring a monomorphism of module sheaves on polynomial projective spectrum by
any integral twist preserves the monomorphism. -/
theorem polynomial_tensorMapLeft_mono
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule i R)).Modules}
    (f : F ⟶ F') [Mono f] (d : ℤ) :
    Mono (Scheme.Modules.tensorMapLeft f
      (twist (MvPolynomial.homogeneousSubmodule i R) d)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let U (j : ULift.{u} i) := Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  have hU : IsOpenCover U := by
    change ⨆ j : ULift.{u} i, U j = ⊤
    dsimp only [U]
    rw [iSup_ulift]
    exact polynomialCoordinateCover_iSup_eq_top (R := R) i
  let e (j : ULift.{u} i) :
      (Scheme.Modules.restrictFunctor (U j).ι).obj (twist 𝒜 d) ≅
        SheafOfModules.unit (U j).toScheme.ringCatSheaf :=
    restrictTwistIsoUnit
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X R j.down)) d
  exact Scheme.Modules.tensorMapLeft_mono_of_iSup_iso_unit f U hU e

/-- Tensoring on the right by an integral twist on polynomial projective spectrum
preserves monomorphisms. -/
noncomputable instance polynomial_tensorRightFunctor_preservesMonomorphisms
    (d : ℤ) :
    (Scheme.Modules.tensorRightFunctor
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).PreservesMonomorphisms where
  preserves f _ := polynomial_tensorMapLeft_mono i f d

/-- Tensoring on the right by an integral twist on polynomial projective spectrum
preserves homology. -/
noncomputable instance polynomial_tensorRightFunctor_preservesHomology
    (d : ℤ) :
    (Scheme.Modules.tensorRightFunctor
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Tensoring on the right by an integral twist on polynomial projective spectrum
preserves finite limits. -/
noncomputable instance polynomial_tensorRightFunctor_preservesFiniteLimits
    (d : ℤ) :
    PreservesFiniteLimits
      (Scheme.Modules.tensorRightFunctor
        (twist (MvPolynomial.homogeneousSubmodule i R) d)) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Tensoring a short exact sequence on polynomial projective spectrum by an integral
twist gives another short exact sequence. -/
theorem polynomial_shortExact_tensorRightFunctor
    {S : ShortComplex (Proj
      (MvPolynomial.homogeneousSubmodule i R)).Modules}
    (hS : S.ShortExact) (d : ℤ) :
    (S.map (Scheme.Modules.tensorRightFunctor
      (twist (MvPolynomial.homogeneousSubmodule i R) d))).ShortExact :=
  hS.map_of_exact _

/-- The twist of the kernel of a morphism on polynomial projective spectrum is
canonically the kernel of the twisted morphism. -/
noncomputable def polynomialTensorKernelIso
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule i R)).Modules}
    (f : F ⟶ F') (d : ℤ) :
    Scheme.Modules.tensor (kernel f)
        (twist (MvPolynomial.homogeneousSubmodule i R) d) ≅
      kernel (Scheme.Modules.tensorMapLeft f
        (twist (MvPolynomial.homogeneousSubmodule i R) d)) :=
  PreservesKernel.iso
    (Scheme.Modules.tensorRightFunctor
      (twist (MvPolynomial.homogeneousSubmodule i R) d)) f

end ProjectiveSpectrum.Twist

end
