module

public import StacksAndModuli.API.ProjectiveOneStepIteratedBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianResidueSurjectivity

/-!
# Residue-field detection for projective multiplication

For a projective twisted pushforward whose target is a vector bundle of fixed rank,
epimorphy of degree-one multiplication can be checked after pullback to all field-valued
points.  A one-step multiplication base-change package then reduces those field pullbacks
after one prior base change to multiplication for the actual twice-base-changed family.

Main declarations:

* `projectiveTwistedPushforwardMul_epi_of_field_pullbacks_of_rank`;
* `ProjectiveOneStepMultiplicationBaseChangeComparison.multiplication_epi_familyAt_of_field`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- If the target twisted pushforward is a vector bundle of fixed rank, then degree-one
multiplication is epic as soon as all of its field-valued pullbacks are epic. -/
theorem projectiveTwistedPushforwardMul_epi_of_field_pullbacks_of_rank
    {T : Scheme.{u}} {n d q : ℕ}
    {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
    (hTarget : IsProjectiveOfRank q
      (projectiveTwistedPushforward n Q (d + 1)))
    (hfield : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ T),
      Epi ((pullback s).map (projectiveTwistedPushforwardMul n Q d))) :
    Epi (projectiveTwistedPushforwardMul n Q d) := by
  letI : (∐ fun _ : Fin ((n + 1).choose n) ↦
      projectiveTwistedPushforward n Q d).IsQuasicoherent :=
    isQuasicoherent_coproduct_small _
  apply epi_of_geometric_residue_pullbacks_epi_of_rank _ hTarget
  intro U I hI
  let κ := Γ(T, U.1) ⧸ I
  letI : Field κ := @Ideal.Quotient.field _ _ I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let s := k ≫ (j ≫ i)
  have hκ : IsField (CommRingCat.of κ) := Field.toIsField κ
  have hs : Epi
      ((pullback s).map (projectiveTwistedPushforwardMul n Q d)) :=
    hfield (CommRingCat.of κ) hκ s
  exact hs

namespace ProjectiveOneStepMultiplicationBaseChangeComparison

/-- For the family obtained after one base change, a fixed-rank target and epimorphy of
multiplication on every actual twice-base-changed field family imply epimorphy over the
whole intermediate base. -/
theorem multiplication_epi_familyAt_of_field
    {T : Scheme.{u}} {n d q : ℕ}
    {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T)
    (hTarget : IsProjectiveOfRank q
      (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)))
    (hfield : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ A.left),
      Epi (projectiveTwistedPushforwardMul n
        (projectiveFamilyAt n Q ((Over.map A.hom).obj (Over.mk s))) d)) :
    Epi (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d) := by
  apply projectiveTwistedPushforwardMul_epi_of_field_pullbacks_of_rank hTarget
  intro K hK s
  let B : Over A.left := Over.mk s
  haveI hmul : Epi (projectiveTwistedPushforwardMul n
      (projectiveFamilyAt n Q ((Over.map A.hom).obj B)) d) := by
    dsimp only [B]
    exact hfield K hK s
  exact C.pullback_multiplication_epi_of_iterated_family A B

end ProjectiveOneStepMultiplicationBaseChangeComparison

end AlgebraicGeometry.Scheme.Modules

end

end
