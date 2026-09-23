module

public import StacksAndModuli.API.ProjectiveLineGradedKoszulSurjectivity
public import StacksAndModuli.API.SchemeModulesAffineFiniteLocallyFreeProjectionFormula
public import StacksAndModuli.API.QuotGrassmannianReconstruction

/-!
# Cech vanishing for pullback coefficients on the projective line

A finite locally free sheaf on an affine scheme is a retract of a finite free sheaf.
After arbitrary pullback, tensoring with a projective-line twist preserves this retract.
The first Cech cohomology therefore vanishes in the same range as for the twisting sheaf,
namely in graded degree `t` when `-1-a ≤ t` for a coefficient twist `a`.

Combining this with the projective-line Koszul long exact sequence gives surjectivity of
`lineKoszulG` on zeroth Cech cohomology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- After arbitrary pullback from an affine base, the first graded Cech cohomology of a
finite-locally-free pullback coefficient tensored with `O(a)` on the projective line
vanishes in degrees `t` satisfying `-1-a ≤ t`. -/
theorem subsingleton_cechHgr_one_gammaStar_pullbackTwist_of_isFiniteLocallyFree_of_isAffine
    {T : Scheme.{u}} [IsAffine T] (g : Spec (.of R) ⟶ T)
    {K : T.Modules} [K.IsQuasicoherent]
    (hK : Scheme.Modules.IsFiniteLocallyFree K) (a t : ℤ)
    (ht : -(1 : ℤ) - a ≤ t) :
    let KR := (Scheme.Modules.pullback g).obj K
    let F := Scheme.projectiveSpaceOverTwistModule
      ((Scheme.Modules.pullback
        (Scheme.projectiveSpaceOverπ 1 (Spec (.of R)))).obj KR) a
    Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj F)
      (stdVars 1 R)).cechHgr 1).obj t) := by
  dsimp only
  obtain ⟨J, hJ, i, p, hip⟩ :=
    Scheme.Modules.exists_retract_free_of_isFiniteLocallyFree_of_isAffine hK
  letI : Finite J := hJ
  let eJ := Scheme.Modules.pullbackFreeIso g J
  let iR : (Scheme.Modules.pullback g).obj K ⟶
      SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) J :=
    (Scheme.Modules.pullback g).map i ≫ eJ.hom
  let pR : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) J ⟶
      (Scheme.Modules.pullback g).obj K :=
    eJ.inv ≫ (Scheme.Modules.pullback g).map p
  have hiRpR : iR ≫ pR = 𝟙 ((Scheme.Modules.pullback g).obj K) := by
    dsimp only [iR, pR]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hip]
    exact (Scheme.Modules.pullback g).map_id K
  let π := Scheme.projectiveSpaceOverπ 1 (Spec (.of R))
  let Oa := Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) a
  let F := Scheme.projectiveSpaceOverTwistModule
    ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback g).obj K)) a
  let G := ∐ fun _ : J ↦ Oa
  let eFree := Scheme.Modules.pullbackFreeIso π J
  let eTensor := Scheme.freeTensorTwistIso 1 (Spec (.of R)) J a
  let iF : F ⟶ G :=
    Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map iR) Oa ≫
      (Scheme.Modules.tensorLeftIso eFree Oa).hom ≫ eTensor.hom
  let pF : G ⟶ F :=
    eTensor.inv ≫ (Scheme.Modules.tensorLeftIso eFree Oa).inv ≫
      Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map pR) Oa
  have hiFpF : iF ≫ pF = 𝟙 F := by
    dsimp only [iF, pF]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Scheme.Modules.tensorMapLeft_comp, ← Functor.map_comp, hiRpR]
    simp
    rfl
  let c := (Finite.equivFin J).trans Equiv.ulift.symm
  let eG : G ≅ ∐ fun _ : ULift.{u} (Fin (Nat.card J)) ↦ Oa :=
    (Limits.Sigma.reindex c.symm (fun _ : J ↦ Oa)).symm
  let h := (projectiveSpaceOverSpecIso 1 R).inv
  let FP := (Scheme.Modules.pullback h).obj F
  let GP := (Scheme.Modules.pullback h).obj G
  let iP : FP ⟶ GP := (Scheme.Modules.pullback h).map iF
  let pP : GP ⟶ FP := (Scheme.Modules.pullback h).map pF
  have hiPpP : iP ≫ pP = 𝟙 FP := by
    dsimp only [iP, pP]
    rw [← Functor.map_comp, hiFpF]
    exact (Scheme.Modules.pullback h).map_id F
  let E : Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) GP
        (stdVars 1 R) ≅
      ((GradedModule.structureModule R 1).twist a).pow (Nat.card J) :=
    Proj.gammaStarMapIso _ (projSpecπ 1 R) (stdVars 1 R)
        ((Scheme.Modules.pullback h).mapIso eG) ≪≫
      gammaStarPullTwistedFreeIso 1 R (by omega) a (Nat.card J)
  haveI hfree : Subsingleton
      (((((GradedModule.structureModule R 1).twist a).pow
        (Nat.card J)).cechHgr 1).obj t) :=
    GradedModule.subsingleton_cechHgr_free a (Nat.card J) 1 (by omega) t ht
  haveI hG : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) GP
      (stdVars 1 R)).cechHgr 1).obj t) :=
    GradedModule.subsingleton_cechHgr_of_retract E.hom E.inv E.hom_inv_id t
  have hFP : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) FP
      (stdVars 1 R)).cechHgr 1).obj t) :=
    Proj.subsingleton_cechHgr_gammaStar_of_retract _ (projSpecπ 1 R)
      (stdVars 1 R) iP pP hiPpP 1 t
  simpa only [FP, F] using hFP

/-- The preceding vanishing gives a right-exact projective-line Koszul recurrence on
zeroth Cech cohomology. -/
theorem
    lineKoszulG_cechHgr_zero_surjective_gammaStar_pullbackTwist_of_isFiniteLocallyFree_of_isAffine
    {T : Scheme.{u}} [IsAffine T] (g : Spec (.of R) ⟶ T)
    {K : T.Modules} [K.IsQuasicoherent]
    (hK : Scheme.Modules.IsFiniteLocallyFree K) (a t : ℤ)
    (ht : -(1 : ℤ) - a ≤ t) :
    let KR := (Scheme.Modules.pullback g).obj K
    let F := Scheme.projectiveSpaceOverTwistModule
      ((Scheme.Modules.pullback
        (Scheme.projectiveSpaceOverπ 1 (Spec (.of R)))).obj KR) a
    Function.Surjective (GradedModule.lineKoszulG
      ((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj F)
        (stdVars 1 R)).cechHgr 0) t) := by
  dsimp only
  letI :=
    subsingleton_cechHgr_one_gammaStar_pullbackTwist_of_isFiniteLocallyFree_of_isAffine
      g hK a t ht
  exact GradedModule.lineKoszulG_cechHgr_zero_surjective_of_subsingleton_one _ t

end AlgebraicGeometry.ProjectiveSpace

end

end
