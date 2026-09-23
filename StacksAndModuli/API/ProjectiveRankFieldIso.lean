module

public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianQuot

/-!
# Isomorphisms between equal-rank vector bundles over a field

On the spectrum of a field, two quasicoherent finite locally free sheaves of the same
constant rank are isomorphic.  This file packages the elementary argument through the
affine tilde--global-sections equivalence.  The isomorphism is deliberately noncanonical.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Two quasicoherent vector bundles of the same rank on the spectrum of a field are
noncanonically isomorphic. -/
noncomputable def IsProjectiveOfRank.iso_of_isField
    {K : CommRingCat.{u}} (hK : IsField K) {q : ℕ}
    {M N : (Spec K).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : IsProjectiveOfRank q M) (hN : IsProjectiveOfRank q N) : M ≅ N := by
  letI : Field K := hK.toField
  have hMf := moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree
    M hM.isFiniteLocallyFree
  have hNf := moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree
    N hN.isFiniteLocallyFree
  letI : Module.Finite K (moduleSpecΓFunctor.obj M) := hMf.1
  letI : Module.Finite K (moduleSpecΓFunctor.obj N) := hNf.1
  let e : moduleSpecΓFunctor.obj M ≃ₗ[K] moduleSpecΓFunctor.obj N :=
    LinearEquiv.ofFinrankEq _ _
      ((hM.finrank_moduleSpecΓFunctor_of_isField hK).trans
        (hN.finrank_moduleSpecΓFunctor_of_isField hK).symm)
  letI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  letI : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  exact (asIso M.fromTildeΓ).symm ≪≫
    (AlgebraicGeometry.tilde.functor K).mapIso e.toModuleIso ≪≫
    asIso N.fromTildeΓ

end AlgebraicGeometry.Scheme.Modules

end

end
