module

public import StacksAndModuli.API.AffineOpenAcyclic
public import StacksAndModuli.API.PolynomialProjChartNoetherian
public import StacksAndModuli.API.ProjectiveLineStandardCoverCohomology
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import StacksAndModuli.API.SchemeIsoCohomology
public import StacksAndModuli.API.SheafCohomologyLES

/-!
# Higher quasicoherent cohomology on the projective line

Over a noetherian coefficient ring, every quasicoherent sheaf on the polynomial
projective line has vanishing cohomology in degrees at least two.  The two standard
charts and their intersection are affine.  Their positive cohomology therefore
vanishes, and the degree-shifted Mayer--Vietoris sequence gives the result.

The second theorem transports this calculation across the canonical isomorphism
between polynomial `Proj` and relative projective space over an affine spectrum.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every quasicoherent module on the polynomial projective line over a
noetherian ring has zero cohomology in degrees at least two. -/
theorem subsingleton_H_projectiveLine_of_two_le
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : (projectiveLine R).Modules) [F.IsQuasicoherent]
    (i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (Scheme.Modules.H F i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  let U := projectiveLineChartZero R
  let V := projectiveLineChartOne R
  let A := (SheafOfModules.toSheaf (projectiveLine R).ringCatSheaf).obj F
  have hU : IsAffineOpen U := polynomialStandardOpen_isAffineOpen 1 R 0
  have hV : IsAffineOpen V := polynomialStandardOpen_isAffineOpen 1 R 1
  have hUV : IsAffineOpen (U ⊓ V) :=
    polynomialStandardOpen_inf_isAffineOpen 1 R 0 1
  letI : IsLocallyNoetherian (projectiveLine R) :=
    ProjectiveSpace.polynomialProj_isLocallyNoetherian 1 R
  letI : IsNoetherianRing Γ(projectiveLine R, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : IsNoetherianRing Γ(projectiveLine R, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : IsNoetherianRing Γ(projectiveLine R, U ⊓ V) :=
    IsLocallyNoetherian.component_noetherian ⟨U ⊓ V, hUV⟩
  have hintersection : Subsingleton (A.H' (k + 1) (U ⊓ V)) := by
    exact Scheme.Modules.subsingleton_HPrime_of_isAffineOpen hUV F k
  have hU' : Subsingleton (A.H' (2 + k) U) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Scheme.Modules.subsingleton_HPrime_of_isAffineOpen hU F (k + 1))
  have hV' : Subsingleton (A.H' (2 + k) V) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Scheme.Modules.subsingleton_HPrime_of_isAffineOpen hV F (k + 1))
  have hsup : Subsingleton (A.H' (2 + k) (U ⊔ V)) :=
    CategoryTheory.Sheaf.subsingleton_HPrime_sup A U V (k + 1) (2 + k)
      (by omega) hintersection hU' hV'
  rw [show U ⊔ V = ⊤ from projectiveLineChart_sup R] at hsup
  rw [← CategoryTheory.Sheaf.subsingleton_HPrime_terminal_iff
    (Opens.grothendieckTopology (projectiveLine R)) A (2 + k) isTerminalTop]
  exact hsup

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every quasicoherent module on the relative projective line over the spectrum
of a noetherian ring has zero cohomology in degrees at least two. -/
theorem subsingleton_H_projectiveSpaceOver_one_of_two_le
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [F.IsQuasicoherent] (i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (Scheme.Modules.H F i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  let e := projectiveSpaceOverSpecIso 1 R
  let G := Scheme.Modules.restrict F e.inv
  have hG : Subsingleton (Scheme.Modules.H G (2 + k)) :=
    Proj.subsingleton_H_projectiveLine_of_two_le R G (2 + k) (by omega)
  have hback : Subsingleton
      (Scheme.Modules.H (Scheme.Modules.restrict G e.hom) (2 + k)) := by
    have hback' := Scheme.subsingleton_H_restrict_of_iso e G (k + 1) (by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hG)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hback'
  let eBack : Scheme.Modules.restrict G e.hom ≅ F :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app F ≪≫
      (Scheme.Modules.restrictFunctorId).app F
  exact Scheme.Modules.subsingleton_H_of_iso eBack (2 + k) hback

end AlgebraicGeometry.ProjectiveSpace

end

end
