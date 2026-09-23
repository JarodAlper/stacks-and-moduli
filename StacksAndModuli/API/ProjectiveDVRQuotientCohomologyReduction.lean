module

public import StacksAndModuli.API.ProjectiveDVRFiberGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSpaceTwistCohomology

/-!
# Closed-fibre Hilbert polynomials from a quotient presentation over a DVR

Let `q : M ⟶ Q` be an epimorphism of module sheaves on projective space over a
discrete valuation ring.  Exactness of projective twisting and the cohomology long exact
sequence reduce eventual finiteness of `H⁰(Q(d))` and vanishing of `H¹(Q(d))` to the
corresponding ambient and kernel inputs.  The DVR global-section rank comparison then
transports a Hilbert polynomial from the generic fibre to the canonical residue-field
fibre.

Main declaration:
- `AlgebraicGeometry.Scheme.Modules.FlatOver.
    hasHilbertPolynomialOver_residueField_of_fractionRing_of_epi_twist`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A generic-fibre Hilbert polynomial of a flat quasicoherent quotient on projective
space over a DVR is also the Hilbert polynomial of its canonical residue-field fibre,
provided a presentation supplies eventual finite ambient `H⁰` and eventual vanishing of
ambient `H¹` and kernel `H¹`, `H²` after twisting. -/
theorem FlatOver.hasHilbertPolynomialOver_residueField_of_fractionRing_of_epi_twist
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    {M Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules}
    (q : M ⟶ Q) [Epi q] [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      letI := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R))
        (Scheme.projectiveSpaceOverTwistModule M (d : ℤ))
      Module.Finite R
        Γ(Scheme.projectiveSpaceOverTwistModule M (d : ℤ), ⊤))
    (hM₁ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule M (d : ℤ))).H 1))
    (hker₁ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) (d : ℤ))).H 1))
    (hker₂ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) (d : ℤ))).H 2))
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
      Scheme.HasHilbertPolynomialOver QK P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.HasHilbertPolynomialOver Qκ P := by
  have hQ := eventually_finite_globalSections_and_H_one_of_epi_twist
    n (Spec R) (Scheme.projectiveSpaceOverπ n (Spec R)) q
      hfinite hM₁ hker₁ hker₂
  have hQfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤) := by
    filter_upwards [hQ] with d hd
    exact hd.1
  have hQ₁ : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
    filter_upwards [hQ] with d hd
    exact hd.2
  exact hflat.hasHilbertPolynomialOver_residueField_of_fractionRing
    n R Q ϖ hϖ hQ₁ hQfinite P hgeneric

end AlgebraicGeometry.Scheme.Modules

end
