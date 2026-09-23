module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianGotzmannReduction
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianKernelMultiplication

/-!
# Relation generation for actual twisted-free Quot families

The pointwise Gotzmann reduction isolates next-degree relation generation as a forward
regularity input for an arbitrary Grassmannian quotient.  For a point which is the degree-
`d` image of an actual flat Quot family, this input follows uniformly from kernel regularity.

This file states that result directly in the vocabulary of
`TwistedFreeQuotNextDegreeRelationGeneration`: above one bound, an actual noetherian-affine
Quot family both reconstructs from its Grassmannian point and satisfies the exact relation-
generation field used by the Gotzmann reduction.  The remaining Gotzmann problem is therefore
the converse for arbitrary Grassmannian points, not forward regularity on the image of Quot.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Uniform reflection and the exact Gotzmann forward relation-generation field for
Grassmannian points arising from actual noetherian-affine Quot families. -/
theorem exists_bound_reconstructedRelationPresentsKernel_and_relationGeneration_of_actualQuot
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ e : ℕ,
      (he : (d : ℤ) - l = (e : ℤ)) →
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P),
      Nonempty (Scheme.ReconstructedRelationPresentsKernel n (Spec (.of R))
        l r d e he (Scheme.quotGrassmannianFreeMap n (Spec (.of R))
          l r q d e he) q) ∧
      Scheme.Modules.TwistedFreeQuotNextDegreeRelationGeneration
        n (Spec (.of R)) l r P d e he
          (Scheme.quotGrassmannianFreeMap n (Spec (.of R)) l r q d e he) := by
  obtain ⟨D, hD⟩ :=
    exists_bound_reconstruction_reflection_and_nextDegreeRelation_epi n r hn l P
  refine ⟨D, ?_⟩
  intro d hd e he R _ _ Q hQfp q hq hflat hP
  obtain ⟨Drel, hrelation⟩ :=
    hD d hd e he R Q hQfp q hq hflat hP
  refine ⟨⟨Drel⟩, ?_⟩
  intro _
  exact hrelation

end AlgebraicGeometry.ProjectiveSpace
