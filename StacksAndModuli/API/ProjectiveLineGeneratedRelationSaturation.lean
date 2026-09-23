module

public import StacksAndModuli.API.ProjectiveLineGeneratedRelationPersistence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianLineSaturation
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianRelationKernelCohomology

/-!
# Saturation of generated relations on the projective line

For a quotient of a twisted-free degree piece over an affine base, the successor
piece of the algebraically generated graded quotient is the finite next-degree
cokernel.  Under reconstructed next-degree saturation, that cokernel is the
affine module of the corresponding twisted pushforward of the reconstructed
geometric quotient.

On a projective line over a noetherian affine base, when the degree-`d` relation
coefficient is finite locally free, reconstructed next-degree saturation is
equivalent to vanishing of the first cohomology of the reconstructed relation
kernel.  Thus this file isolates the precise cohomological obstruction to using
generated-relation persistence for the geometric quotient.

Main declarations:

* `Scheme.ReconstructedNextDegreeRelationKernelHOneVanishing`;
* `Scheme.twistedFreeNextDegreeReconstructionSaturation_iff_relationKernelHOneVanishing_line`;
* `affineReconstructedGeneratedGradedQuotientSuccPushforwardIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Vanishing of the first cohomology of the kernel of the reconstructed
relation-to-image map after twisting to the next degree.  This is the genuine
relation-generation obstruction in reconstructed next-degree saturation. -/
abbrev ReconstructedNextDegreeRelationKernelHOneVanishing
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  Subsingleton
    (((SheafOfModules.toSheaf _).obj
      (kernel (Modules.tensorMapLeft
        (Abelian.factorThruImage
          (reconstructedRelation' n T l r d e he u))
        (projectiveSpaceOverTwist n T
          ((d + 1 : ℕ) : ℤ))))).H 1)

/-- On a projective line over a noetherian affine base, finite local freeness of
the degree-`d` relation coefficient identifies full reconstructed next-degree
saturation with vanishing of the reconstructed relation-kernel `H¹`.

The forward implication uses the relation-generation field of saturation.  The
other saturation field, next-degree global generation, is automatic here from
finite local freeness and the two-chart cohomology calculation. -/
theorem
    twistedFreeNextDegreeReconstructionSaturation_iff_relationKernelHOneVanishing_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u)) :
    TwistedFreeNextDegreeReconstructionSaturation
        1 (Spec (.of R)) l r d e he u ↔
      ReconstructedNextDegreeRelationKernelHOneVanishing
        1 (Spec (.of R)) l r d e he u := by
  constructor
  · intro hsaturation
    haveI hKqc : (kernel u).IsQuasicoherent :=
      Modules.kernel_isQuasicoherent u
    have hpullback1 :=
      @subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
        R _ _ (kernel u) hKqc hK
    have hsource1 := Modules.subsingleton_H_of_iso
      (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
        1 (Spec (.of R)) d (kernel u)).symm 1 hpullback1
    exact
      (subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_kernelLift_epi
        1 (Spec (.of R)) l r d e he u hK hsource1).2
          hsaturation.relationKernelLift_epi
  · intro hrelationKernel1
    exact
      twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_vanishing
        R l r d e he u hK hrelationKernel1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Under reconstructed next-degree saturation, the successor piece of the
affine generated graded quotient is the affine module of the next twisted
pushforward of the reconstructed geometric quotient. -/
noncomputable def affineReconstructedGeneratedGradedQuotientSuccPushforwardIso
    (n : ℕ) (R : CommRingCat.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : (Spec R).Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (h : Scheme.TwistedFreeNextDegreeReconstructionSaturation
      n (Spec R) l r d e he u) :
    (affineReconstructedGeneratedGradedQuotient
        n R l r d e he u).obj ((d : ℤ) + 1) ≅
      moduleSpecΓFunctor.obj
        (Scheme.Modules.projectiveTwistedPushforward n
          (Scheme.reconstructedQuotient' n (Spec R) l r d e he u) (d + 1)) :=
  affineReconstructedGeneratedGradedQuotientSuccIso
      n R l r d e he u ≪≫
    moduleSpecΓFunctor.mapIso
      (Scheme.twistedFreeNextDegreeSaturationIso
        n (Spec R) l r d e he u h)

/-- Projective-line form of the successor comparison, with its saturation
hypothesis replaced by the equivalent reconstructed relation-kernel `H¹`
vanishing condition. -/
noncomputable def
    affineReconstructedGeneratedGradedQuotientSuccPushforwardIso_of_relationKernelHOneVanishing_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hK : Scheme.Modules.IsFiniteLocallyFree (kernel u))
    (hrelationKernel1 :
      Scheme.ReconstructedNextDegreeRelationKernelHOneVanishing
        1 (Spec (.of R)) l r d e he u) :
    (affineReconstructedGeneratedGradedQuotient
        1 (.of R) l r d e he u).obj ((d : ℤ) + 1) ≅
      moduleSpecΓFunctor.obj
        (Scheme.Modules.projectiveTwistedPushforward 1
          (Scheme.reconstructedQuotient'
            1 (Spec (.of R)) l r d e he u) (d + 1)) := by
  let hsaturation :=
    Scheme.twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_vanishing
      R l r d e he u hK hrelationKernel1
  exact affineReconstructedGeneratedGradedQuotientSuccPushforwardIso
    1 (.of R) l r d e he u hsaturation

end AlgebraicGeometry

end

end
