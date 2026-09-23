module

public import StacksAndModuli.API.ProjectiveGradedGlobalGeneration
public import StacksAndModuli.API.ProjectiveLineQuasicoherentHigherCohomology
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison
public import StacksAndModuli.API.QuasicoherentFiniteCoproduct

/-!
# First cohomology of `O(1)` on the projective line

The degree-one coordinates give an epimorphism from two copies of `O` to
`O(1)` on the polynomial projective line.  The two-chart Laurent calculation
shows that the structure sheaf has zero first cohomology, while arbitrary
quasicoherent modules have zero second cohomology.  The associated long exact
sequence therefore proves that `O(1)` has zero first cohomology.

The final theorem transports this calculation to relative projective space
over an affine spectrum.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry ProjectiveSpectrum

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- The two degree-one coordinates define the standard epimorphism
`O(0) ⊕ O(0) ⟶ O(1)` on the polynomial projective line. -/
noncomputable def projectiveLineDegreeOneCoordinateMap :
    (∐ fun _ : ULift.{u} (Fin 2) =>
      ProjectiveSpectrum.Twist.twist (lineGrading R) 0) ⟶
      ProjectiveSpectrum.Twist.twist (lineGrading R) 1 :=
  Limits.Sigma.desc (fun i =>
    ProjectiveSpectrum.Twist.mulHom (lineGrading R)
      (⟨MvPolynomial.X i.down,
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_X R i.down)⟩ : lineGrading R 1)
      0 1 (by omega))

/-- The two standard coordinate opens as an open cover of the polynomial
projective line. -/
noncomputable def projectiveLineCoordinateCover :
    (projectiveLine R).OpenCover :=
  Scheme.Cover.mkOfCovers (ULift.{u} (Fin 2))
    (fun i => (Proj.basicOpen (lineGrading R)
      (MvPolynomial.X i.down)).toScheme)
    (fun i => (Proj.basicOpen (lineGrading R)
      (MvPolynomial.X i.down)).ι)
    (fun x => by
      have hx : x ∈ (⨆ i : Fin 2,
          Proj.basicOpen (lineGrading R) (MvPolynomial.X i) :
          (projectiveLine R).Opens) := by
        rw [ProjectiveSpectrum.Twist.polynomialCoordinateCover_iSup_eq_top]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨ULift.up i, ⟨⟨x, hi⟩, rfl⟩⟩)

set_option maxHeartbeats 2000000 in
-- Restriction unfolds the sheafification and finite-colimit machinery.
set_option synthInstance.maxHeartbeats 1000000 in
-- The same calculation synthesizes quasicoherence through a finite coproduct.
/-- The standard degree-one coordinate map on the polynomial projective line
is an epimorphism. -/
theorem projectiveLineDegreeOneCoordinateMap_epi :
    Epi (projectiveLineDegreeOneCoordinateMap R) := by
  let φ := projectiveLineDegreeOneCoordinateMap R
  letI : (∐ fun _ : ULift.{u} (Fin 2) =>
      ProjectiveSpectrum.Twist.twist (lineGrading R) 0).IsQuasicoherent :=
    @Scheme.Modules.isQuasicoherent_coproduct _ _
      (fun _ : ULift.{u} (Fin 2) =>
        ProjectiveSpectrum.Twist.twist (lineGrading R) 0)
      (fun _ =>
        ProjectiveSpectrum.Twist.polynomialTwist_isQuasicoherent (Fin 2) 0)
  letI : (ProjectiveSpectrum.Twist.twist
      (lineGrading R) 1).IsQuasicoherent :=
    ProjectiveSpectrum.Twist.polynomialTwist_isQuasicoherent (Fin 2) 1
  apply Scheme.Modules.epi_of_openCover_restrict φ
    (projectiveLineCoordinateCover R)
  intro z
  let i : Fin 2 := z.down
  let j := (Proj.basicOpen (lineGrading R) (MvPolynomial.X i)).ι
  let m := ProjectiveSpectrum.Twist.mulHom (lineGrading R)
      (⟨MvPolynomial.X i,
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_X R i)⟩ : lineGrading R 1)
      0 1 (by omega)
  haveI hm : IsIso ((Scheme.Modules.restrictFunctor j).map m) :=
    ProjectiveSpectrum.Twist.isIso_restrict_mulHom (lineGrading R)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X R i)) 0 (by omega)
  have hcomp :
      (Scheme.Modules.restrictFunctor j).map
          (Limits.Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
            ProjectiveSpectrum.Twist.twist (lineGrading R) 0) (ULift.up i)) ≫
        (Scheme.Modules.restrictFunctor j).map φ =
      (Scheme.Modules.restrictFunctor j).map m := by
    rw [← (Scheme.Modules.restrictFunctor j).map_comp]
    dsimp only [φ, projectiveLineDegreeOneCoordinateMap, m]
    rw [Limits.Sigma.ι_desc]
  haveI : Epi
      ((Scheme.Modules.restrictFunctor j).map
          (Limits.Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
            ProjectiveSpectrum.Twist.twist (lineGrading R) 0) (ULift.up i)) ≫
        (Scheme.Modules.restrictFunctor j).map φ) := by
    rw [hcomp]
    infer_instance
  change Epi ((Scheme.Modules.restrictFunctor j).map φ)
  exact epi_of_epi
    ((Scheme.Modules.restrictFunctor j).map
      (Limits.Sigma.ι (fun _ : ULift.{u} (Fin 2) =>
        ProjectiveSpectrum.Twist.twist (lineGrading R) 0) (ULift.up i)))
    ((Scheme.Modules.restrictFunctor j).map φ)

/-- The structure sheaf of a projective line over a noetherian ring has zero
first cohomology. -/
theorem subsingleton_H_one_projectiveLine_structure [IsNoetherianRing R] :
    Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLine R)) 1) := by
  let U := projectiveLineChartZero R
  let V := projectiveLineChartOne R
  let F := Scheme.structureModule (projectiveLine R)
  let A := (SheafOfModules.toSheaf (projectiveLine R).ringCatSheaf).obj F
  letI : F.IsQuasicoherent := by
    dsimp only [F]
    exact Scheme.Modules.unit_isQuasicoherent _
  have hU : IsAffineOpen U := polynomialStandardOpen_isAffineOpen 1 R 0
  have hV : IsAffineOpen V := polynomialStandardOpen_isAffineOpen 1 R 1
  letI : IsLocallyNoetherian (projectiveLine R) :=
    ProjectiveSpace.polynomialProj_isLocallyNoetherian 1 R
  letI : IsNoetherianRing Γ(projectiveLine R, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsNoetherianRing Γ(projectiveLine R, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI hHU : Subsingleton (A.H' 1 U) := by
    simpa only [Nat.zero_add] using
      (Scheme.Modules.subsingleton_HPrime_of_isAffineOpen hU F 0)
  letI hHV : Subsingleton (A.H' 1 V) := by
    simpa only [Nat.zero_add] using
      (Scheme.Modules.subsingleton_HPrime_of_isAffineOpen hV F 0)
  let S := _root_.Opens.mayerVietorisSquare U V
  letI : Subsingleton (A.H' 1 S.X₂) := by
    change Subsingleton (A.H' 1 U)
    exact hHU
  letI : Subsingleton (A.H' 1 S.X₃) := by
    change Subsingleton (A.H' 1 V)
    exact hHV
  have hT : IsTerminal (U ⊔ V) :=
    IsTerminal.ofIso isTerminalTop
      (eqToIso (projectiveLineChart_sup R)).symm
  change Subsingleton (A.H 1)
  exact S.subsingleton_H_one_of_terminal_of_surjective_sectionsDifference
    A hT (projectiveLineSectionsDifference_surjective R)

/-- The positive generator `O(1)` on a projective line over a noetherian ring
has zero first cohomology. -/
theorem subsingleton_H_one_projectiveLine_twist_one [IsNoetherianRing R] :
    Subsingleton (Scheme.Modules.H
      (ProjectiveSpectrum.Twist.twist (lineGrading R) 1) 1) := by
  let φ := projectiveLineDegreeOneCoordinateMap R
  letI : Epi φ := projectiveLineDegreeOneCoordinateMap_epi R
  letI hsourceqc : (∐ fun _ : ULift.{u} (Fin 2) =>
      ProjectiveSpectrum.Twist.twist (lineGrading R) 0).IsQuasicoherent :=
    @Scheme.Modules.isQuasicoherent_coproduct _ _
      (fun _ : ULift.{u} (Fin 2) =>
        ProjectiveSpectrum.Twist.twist (lineGrading R) 0)
      (fun _ =>
        ProjectiveSpectrum.Twist.polynomialTwist_isQuasicoherent (Fin 2) 0)
  letI htargetqc : (ProjectiveSpectrum.Twist.twist
      (lineGrading R) 1).IsQuasicoherent :=
    ProjectiveSpectrum.Twist.polynomialTwist_isQuasicoherent (Fin 2) 1
  have hO : Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLine R)) 1) :=
    subsingleton_H_one_projectiveLine_structure R
  have hzero : Subsingleton (Scheme.Modules.H
      (ProjectiveSpectrum.Twist.twist (lineGrading R) 0) 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      (ProjectiveSpectrum.Twist.zeroIso (lineGrading R)).symm 1 hO
  have hsource : Subsingleton (Scheme.Modules.H
      (∐ fun _ : ULift.{u} (Fin 2) =>
        ProjectiveSpectrum.Twist.twist (lineGrading R) 0) 1) :=
    Scheme.Modules.subsingleton_H_coproduct_of_finite
      (fun _ : ULift.{u} (Fin 2) =>
        ProjectiveSpectrum.Twist.twist (lineGrading R) 0) 1
      (fun _ => hzero)
  letI : IsLocallyNoetherian (projectiveLine R) :=
    ProjectiveSpace.polynomialProj_isLocallyNoetherian 1 R
  letI : (kernel φ).IsQuasicoherent :=
    Scheme.Modules.kernel_isQuasicoherent φ
  have hkernel : Subsingleton (Scheme.Modules.H (kernel φ) 2) :=
    subsingleton_H_projectiveLine_of_two_le R (kernel φ) 2 (by omega)
  let C := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hC : C.ShortExact :=
    { exact := ShortComplex.exact_kernel φ }
  exact Scheme.Modules.subsingleton_H_of_shortExact_right
    hC rfl hsource hkernel

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative twisting sheaf `O(1)` on the projective line over the spectrum
of a noetherian ring has zero first cohomology. -/
theorem subsingleton_H_one_projectiveSpaceOverTwist_one
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Subsingleton (Scheme.Modules.H
      (Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 1) 1) := by
  let e := projectiveSpaceOverSpecIso 1 R
  let F := Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 1
  let G := Scheme.Modules.restrict F e.inv
  have hpoly : Subsingleton (Scheme.Modules.H
      (ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) 1) 1) :=
    Proj.subsingleton_H_one_projectiveLine_twist_one R
  have hpull : Subsingleton (Scheme.Modules.H
      ((Scheme.Modules.pullback e.inv).obj F) 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      (projectiveSpaceOverTwistPullbackIso 1 R 1).symm 1 hpoly
  have hG : Subsingleton (Scheme.Modules.H G 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app F).symm 1 hpull
  have hback : Subsingleton
      (Scheme.Modules.H (Scheme.Modules.restrict G e.hom) 1) :=
    Scheme.subsingleton_H_restrict_of_iso e G 0 (by simpa using hG)
  let eBack : Scheme.Modules.restrict G e.hom ≅ F :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app F ≪≫
      (Scheme.Modules.restrictFunctorId).app F
  exact Scheme.Modules.subsingleton_H_of_iso eBack 1 hback

end AlgebraicGeometry.ProjectiveSpace

end
