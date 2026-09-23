module

public import StacksAndModuli.API.ProjectiveTwistFlatOver
public import StacksAndModuli.API.SchemeModulesTensorExact

/-!
# Exactness of twists on relative projective space

Every integral twisting sheaf on relative projective space is trivial on the pullback
of the standard coordinate cover.  Consequently, tensoring by a relative twisting
sheaf preserves monomorphisms, homology, and finite limits.  In particular it sends
short exact sequences to short exact sequences and commutes canonically with kernels.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory TopologicalSpace
open ProjectiveSpectrum

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring a monomorphism of module sheaves on relative projective space by an
integral twist preserves the monomorphism. -/
theorem projectiveSpaceOverTwist_tensorMapLeft_mono
    (n : ℕ) (S : Scheme.{u})
    {F F' : (projectiveSpaceOver n S).Modules}
    (f : F ⟶ F') [Mono f] (d : ℤ) :
    Mono (Modules.tensorMapLeft f (projectiveSpaceOverTwist n S d)) := by
  let X := projectiveSpaceOver n S
  let A := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let g : X ⟶ Proj A := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let U (j : ULift.{u} (Fin (n + 1))) : X.Opens :=
    g ⁻¹ᵁ Proj.basicOpen A (MvPolynomial.X j.down)
  have hU : IsOpenCover U := by
    change ⨆ j, U j = ⊤
    dsimp only [U]
    rw [← Scheme.Hom.preimage_iSup, iSup_ulift]
    rw [ProjectiveSpectrum.Twist.polynomialCoordinateCover_iSup_eq_top,
      Scheme.Hom.preimage_top]
  let e (j : ULift.{u} (Fin (n + 1))) :
      (Modules.restrictFunctor (U j).ι).obj
          (projectiveSpaceOverTwist n S d) ≅
        SheafOfModules.unit (U j).toScheme.ringCatSheaf := by
    let hX : MvPolynomial.X j.down ∈ A 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j.down)
    dsimp [projectiveSpaceOverTwist, U, g, X, A]
    exact ProjectiveSpectrum.Twist.restrictPullbackTwistIsoUnitOfHom
      (Limits.pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (projectiveSpace n))) d hX
  exact Modules.tensorMapLeft_mono_of_iSup_iso_unit f U hU e

/-- Tensoring on the right by an integral twist on relative projective space preserves
monomorphisms. -/
noncomputable instance
    projectiveSpaceOverTwist_tensorRightFunctor_preservesMonomorphisms
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (Modules.tensorRightFunctor
      (projectiveSpaceOverTwist n S d)).PreservesMonomorphisms where
  preserves f _ := projectiveSpaceOverTwist_tensorMapLeft_mono n S f d

/-- Tensoring on the right by an integral twist on relative projective space preserves
homology. -/
noncomputable instance projectiveSpaceOverTwist_tensorRightFunctor_preservesHomology
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (Modules.tensorRightFunctor
      (projectiveSpaceOverTwist n S d)).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Tensoring on the right by an integral twist on relative projective space preserves
finite limits. -/
noncomputable instance projectiveSpaceOverTwist_tensorRightFunctor_preservesFiniteLimits
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    PreservesFiniteLimits
      (Modules.tensorRightFunctor (projectiveSpaceOverTwist n S d)) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Tensoring a short exact sequence on relative projective space by an integral twist
gives another short exact sequence. -/
theorem projectiveSpaceOverTwist_shortExact_tensorRightFunctor
    (n : ℕ) (S : Scheme.{u})
    {C : ShortComplex (projectiveSpaceOver n S).Modules}
    (hC : C.ShortExact) (d : ℤ) :
    (C.map (Modules.tensorRightFunctor
      (projectiveSpaceOverTwist n S d))).ShortExact :=
  hC.map_of_exact _

/-- The twist of the kernel of a morphism on relative projective space is canonically
the kernel of the twisted morphism. -/
noncomputable def projectiveSpaceOverTwistTensorKernelIso
    (n : ℕ) (S : Scheme.{u})
    {F F' : (projectiveSpaceOver n S).Modules}
    (f : F ⟶ F') (d : ℤ) :
    Modules.tensor (kernel f) (projectiveSpaceOverTwist n S d) ≅
      kernel (Modules.tensorMapLeft f (projectiveSpaceOverTwist n S d)) :=
  PreservesKernel.iso
    (Modules.tensorRightFunctor (projectiveSpaceOverTwist n S d)) f

end AlgebraicGeometry.Scheme

end
