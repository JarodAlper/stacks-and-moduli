module

public import StacksAndModuli.API.OpenCoverModuleMorphismZero
public import StacksAndModuli.API.ProjGammaStarChartNaturality
public import StacksAndModuli.API.ProjGammaStarQuotientModel
public import StacksAndModuli.API.ProjectiveSpaceBaseChange
public import StacksAndModuli.API.SchemeModulesTensorLocallyFree

/-!
# Faithfulness of twisting on polynomial projective space

Tensoring a sheaf of modules with `𝒪(d)` is faithful on polynomial projective
space.  For the finite-presentation application it is enough to treat nonnegative
`d`: multiplication by `xᵢ^d` identifies the zero twist with the `d`-th twist on
each standard chart, and the degree-zero twist is canonically the original sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "X" => Proj 𝒜
local notation "π" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "x" => _root_.AlgebraicGeometry.ProjectiveSpace.stdVars n R

/-- The degree-zero twist of a module sheaf is canonically the original module. -/
noncomputable def twistModuleZeroIso (F : (Proj 𝒜).Modules) :
    twistModule 𝒜 F 0 ≅ F :=
  Scheme.Modules.tensorRightIso F (ProjectiveSpectrum.Twist.zeroIso 𝒜) ≪≫
    Scheme.Modules.tensorUnitIso F

/-- The degree-zero twist identification is natural in the module sheaf. -/
@[reassoc]
lemma twistModuleMap_zero_comp_twistModuleZeroIso_hom
    {F F' : (Proj 𝒜).Modules} (p : F ⟶ F') :
    twistModuleMap 𝒜 p 0 ≫ (twistModuleZeroIso F').hom =
      (twistModuleZeroIso F).hom ≫ p := by
  change
    (Scheme.Modules.tensorMapLeft p (twist 𝒜 0) ≫
        Scheme.Modules.tensorMapRight F' (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom) ≫
          (Scheme.Modules.tensorUnitIso F').hom =
      (Scheme.Modules.tensorMapRight F (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom ≫
        (Scheme.Modules.tensorUnitIso F).hom) ≫ p
  calc
    _ = (Scheme.Modules.tensorMapRight F
          (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom ≫
        Scheme.Modules.tensorMapLeft p
          (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)) ≫
          (Scheme.Modules.tensorUnitIso F').hom :=
      congrArg (fun q ↦ q ≫ (Scheme.Modules.tensorUnitIso F').hom)
        (Scheme.Modules.tensorMap_exchange p
          (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom).symm
    _ = Scheme.Modules.tensorMapRight F
          (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom ≫
        (Scheme.Modules.tensorMapLeft p
            (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) ≫
          (Scheme.Modules.tensorUnitIso F').hom) :=
      Category.assoc _ _ _
    _ = Scheme.Modules.tensorMapRight F
          (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom ≫
        ((Scheme.Modules.tensorUnitIso F).hom ≫ p) :=
      congrArg (fun q ↦ Scheme.Modules.tensorMapRight F
        (ProjectiveSpectrum.Twist.zeroIso 𝒜).hom ≫ q)
          (Scheme.Modules.tensorUnitIso_naturality p)
    _ = _ := (Category.assoc _ _ _).symm

/-- On polynomial projective space, twisting a module morphism by a nonnegative
degree detects whether the morphism is zero. -/
theorem twistModuleMap_nat_eq_zero_iff
    {F F' : (Proj 𝒜).Modules} (p : F ⟶ F') (d : ℕ) :
    twistModuleMap 𝒜 p (d : ℤ) = 0 ↔ p = 0 := by
  constructor
  · intro hd
    have hzero : twistModuleMap 𝒜 p 0 = 0 := by
      let U := (polynomialAffineOpenCover (Fin (n + 1)) R).openCover
      apply Scheme.Modules.eq_zero_of_openCover_restrict U
      intro i
      apply Scheme.Modules.hom_ext
      intro W
      let V : (Proj 𝒜).Opens := (U.f i) ''ᵁ W
      change Scheme.Modules.Hom.app (twistModuleMap 𝒜 p 0) V = 0
      have hV : V ≤ basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) := by
        apply (Scheme.Hom.image_le_opensRange (U.f i) W).trans_eq
        change (Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
          (MvPolynomial.isHomogeneous_X R i) Nat.one_pos).opensRange = _
        exact Proj.opensRange_awayι 𝒜
          (x i : MvPolynomial (Fin (n + 1)) R)
          (MvPolynomial.isHomogeneous_X R i) Nat.one_pos
      let c : 𝒜 d := ⟨(x i : MvPolynomial (Fin (n + 1)) R) ^ d,
        pow_var_mem 𝒜 x i d⟩
      have hnat := twistModuleMulHom_comp_twistModuleMap 𝒜 p c
        0 (d : ℤ) (by simp)
      have hcomp :
          twistModuleMap 𝒜 p 0 ≫
              twistModuleMulHom 𝒜 F' c 0 (d : ℤ) (by simp) = 0 := by
        rw [← hnat, hd, comp_zero]
      haveI : IsIso (Scheme.Modules.Hom.app
          (twistModuleMulHom 𝒜 F' c 0 (d : ℤ) (by simp)) V) :=
        (ConcreteCategory.isIso_iff_bijective _).2
          (bijective_app_twistModuleMulHom_natPow 𝒜 (x i).2 F' 0 d
            (pow_var_mem 𝒜 x i d) (d : ℤ) (by simp) V hV)
      apply (cancel_mono (Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜 F' c 0 (d : ℤ) (by simp)) V)).mp
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app, zero_comp]
        using congrArg (fun q ↦ Scheme.Modules.Hom.app q V) hcomp
    have hnat := twistModuleMap_zero_comp_twistModuleZeroIso_hom p
    rw [hzero, zero_comp] at hnat
    apply (cancel_epi (twistModuleZeroIso F).hom).mp
    exact hnat.symm
  · rintro rfl
    exact twistModuleMap_zero 𝒜 F F' (d : ℤ)

end AlgebraicGeometry.Proj

end

end
