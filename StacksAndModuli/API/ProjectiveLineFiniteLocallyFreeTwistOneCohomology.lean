module

public import StacksAndModuli.API.ProjectiveLineTwistOneCohomology
public import StacksAndModuli.API.QuotGrassmannianReconstruction
public import StacksAndModuli.API.SchemeModulesAffineFiniteLocallyFreeProjectionFormula
public import StacksAndModuli.API.SheafCohomologyLES

/-!
# First cohomology of pullback coefficients twisted by `O(1)` on a projective line

A finite locally free quasicoherent sheaf on an affine scheme is a retract of a finite
free sheaf. Pulling that retract to the projective line and tensoring it with `O(1)`
exhibits the twisted pullback coefficient as a retract of a finite coproduct of `O(1)`.
The vanishing of `H¹(O(1))` therefore gives the same vanishing for every such coefficient.

## Main result

* `AlgebraicGeometry.ProjectiveSpace.
  subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree`:
  `H¹(P¹_R, π⁺K ⊗ O(1)) = 0` for finite locally free `K` and noetherian `R`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the projective line over a noetherian ring, the pullback of a finite locally
free coefficient sheaf, tensored with `O(1)`, has zero first cohomology. -/
theorem
    subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {K : (Spec (.of R)).Modules} [K.IsQuasicoherent]
    (hK : Scheme.Modules.IsFiniteLocallyFree K) :
    Subsingleton (Scheme.Modules.H
      (Scheme.projectiveSpaceOverTwistModule
        ((Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverπ 1 (Spec (.of R)))).obj K) 1) 1) := by
  obtain ⟨J, hJ, i, p, hip⟩ :=
    Scheme.Modules.exists_retract_free_of_isFiniteLocallyFree_of_isAffine hK
  letI : Finite J := hJ
  let π := Scheme.projectiveSpaceOverπ 1 (Spec (.of R))
  let O1 := Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 1
  let F := Scheme.projectiveSpaceOverTwistModule
    ((Scheme.Modules.pullback π).obj K) 1
  let G := ∐ fun _ : J ↦ O1
  let eFree := Scheme.Modules.pullbackFreeIso π J
  let eTensor := Scheme.freeTensorTwistIso 1 (Spec (.of R)) J 1
  let iF : F ⟶ G :=
    Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map i) O1 ≫
      (Scheme.Modules.tensorLeftIso eFree O1).hom ≫ eTensor.hom
  let pF : G ⟶ F :=
    eTensor.inv ≫ (Scheme.Modules.tensorLeftIso eFree O1).inv ≫
      Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map p) O1
  have hiFpF : iF ≫ pF = 𝟙 F := by
    dsimp only [iF, pF]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Scheme.Modules.tensorMapLeft_comp, ← Functor.map_comp, hip]
    simp
    rfl
  have hO1 : Subsingleton (Scheme.Modules.H O1 1) := by
    dsimp only [O1]
    exact subsingleton_H_one_projectiveSpaceOverTwist_one R
  have hG : Subsingleton (Scheme.Modules.H G 1) := by
    dsimp only [G]
    exact Scheme.Modules.subsingleton_H_coproduct_of_finite
      (fun _ : J ↦ O1) 1 (fun _ ↦ hO1)
  exact Scheme.Modules.subsingleton_H_of_retract iF pF hiFpF 1 hG

end AlgebraicGeometry.ProjectiveSpace

end

end
