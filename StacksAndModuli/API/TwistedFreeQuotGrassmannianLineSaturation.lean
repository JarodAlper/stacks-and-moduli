module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianLineSaturationVanishing
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSourceComparison

/-!
# Reconstructed next-degree saturation on the projective line

For a reconstructed quotient on the projective line over a noetherian affine base,
finite local freeness of the relation coefficient makes its pullback-coefficient
`H¹` vanish.  The relation-kernel `H²` vanishes by the two-chart computation, and
the canonical source comparison is automatic.  Thus full next-degree saturation
reduces to the single genuine cohomological input that the reconstructed relation
kernel has vanishing `H¹`.
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

/-- On the projective line over a noetherian affine base, finite local freeness of
the relation coefficient and vanishing of `H¹` of the reconstructed relation kernel
imply full next-degree saturation. -/
theorem
    twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1)) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  exact twistedFreeNextDegreeReconstructionSaturation
    1 (Spec (.of R)) l r d e he u hK
      (subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
        R hK)
      hrelationKernel1
      (subsingleton_H_two_reconstructedNextDegreeRelationKernel_line
        R l r d e he u)

/-- For an epimorphic finite-free quotient on the projective line, projective rank
of the coefficient quotient and vanishing of `H¹` of the reconstructed relation
kernel imply full next-degree saturation. -/
theorem
    twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsProjectiveOfRank q E)
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1)) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  let m := r * (1 + e).choose 1
  let σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((1 + e).choose 1) :=
    twistedFreeMonomialIndexEquiv r ((1 + e).choose 1)
  let f := SheafOfModules.freeMap
    (R := (Spec (.of R)).ringCatSheaf) σ.symm
  letI : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  have hSource : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))) :=
    (Modules.free_isFiniteLocallyFree (Spec (.of R)) m).of_iso
      (asIso f).symm
  have hK : Modules.IsFiniteLocallyFree (kernel u) :=
    Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
      hSource hE.isFiniteLocallyFree u
  exact
    twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_vanishing
      R l r d e he u hK hrelationKernel1

end AlgebraicGeometry.Scheme

end

end
