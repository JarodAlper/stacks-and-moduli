module

public import StacksAndModuli.API.ProjectiveDVRQuotientCohomologyReduction
public import StacksAndModuli.API.ProjectiveTwistedFreeCohomology
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.ProjectiveSpaceSerreVanishing
public import StacksAndModuli.API.ProjectiveTwistedFreePresentation
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation

/-!
# DVR closed fibres from finite twisted-free presentations

Consider an epimorphism onto a flat quasicoherent module sheaf on projective space over
a discrete valuation ring whose source is a finite coproduct of copies of `O(-l)`.
Twisting identifies the source with the corresponding coproduct of `O(d-l)`.  Hence
eventual vanishing of `H¹(O(d-l))` supplies the ambient `H¹` input in the quotient
cohomology reduction.

Finite generation of the ambient twisted global sections is automatic from the polynomial
basis computation.  The first endpoint retains eventual `H¹` and `H²` vanishing for the
kernel as explicit hypotheses.  The stronger Serre endpoint derives all three vanishings,
as well as quasicoherence and finite presentation of the kernel, and concludes that a
generic-fibre Hilbert polynomial transfers to the canonical residue-field fibre.

Main declaration:
- `AlgebraicGeometry.Scheme.Modules.FlatOver.
    hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi`.
- `AlgebraicGeometry.Scheme.Modules.FlatOver.
    hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi_of_serre`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A Hilbert polynomial on the generic fibre of a flat quasicoherent quotient of a
finite coproduct of copies of `O(-l)` is also the Hilbert polynomial of its canonical
residue-field fibre.  The ambient `H¹` hypothesis is reduced to eventual vanishing for
the single twist `O(d-l)`. -/
theorem FlatOver.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi
    (n r : ℕ) (l : ℤ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    {Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)) ⟶ Q)
    [Epi q] [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hO₁ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwist n (Spec R) ((d : ℤ) - l))).H 1))
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
  have hfinite :=
    Scheme.eventually_projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite
      (J := ULift.{u} (Fin r)) n R l
  have hM₁ :=
    eventually_subsingleton_H_projectiveSpaceOverNegativeTwist_coproduct_twist
      (J := ULift.{u} (Fin r)) n (Spec R) l 1 hO₁
  exact hflat.hasHilbertPolynomialOver_residueField_of_fractionRing_of_epi_twist
      n R q ϖ hϖ hfinite hM₁ hker₁ hker₂ P hgeneric

/-- Under scheme-level Serre vanishing, the preceding DVR specialization needs no
separate cohomology or presentation-kernel hypotheses.  Over a DVR, the kernel of
the twisted-free presentation is automatically quasicoherent and finitely
presented. -/
theorem FlatOver.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi_of_serre
    (n r : ℕ) (l : ℤ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    {Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)) ⟶ Q)
    [Epi q] [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (hserre : Scheme.ProjectiveSpaceHasSerreVanishing n (Spec R))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
      Scheme.HasHilbertPolynomialOver QK P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.HasHilbertPolynomialOver Qκ P := by
  letI : IsLocallyNoetherian (Scheme.projectiveSpaceOver n (Spec R)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Scheme.projectiveSpaceOverπ n (Spec R))
  have hsourceqc : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsQuasicoherent :=
    projectiveSpaceOverTwistCoproduct_isQuasicoherent
      (ULift.{u} (Fin r)) n (Spec R) (-l)
  letI : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsQuasicoherent :=
    hsourceqc
  have hsourcefp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsFinitePresentation :=
    projectiveSpaceOverTwistCoproduct_isFinitePresentation
      (ULift.{u} (Fin r)) n (Spec R) (-l)
  letI : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsFinitePresentation :=
    hsourcefp
  have hkerqc : (kernel q).IsQuasicoherent := kernel_isQuasicoherent q
  letI : (kernel q).IsQuasicoherent := hkerqc
  have hkerfp : (kernel q).IsFinitePresentation :=
    kernel_isFinitePresentation q
  have hO₁ :=
    hserre.eventually_subsingleton_H_projectiveSpaceOverTwist_sub l 1 (by omega)
  have hker₁ := hserre.eventually_subsingleton_H
    (kernel q) hkerqc hkerfp 1 (by omega)
  have hker₂ := hserre.eventually_subsingleton_H
    (kernel q) hkerqc hkerfp 2 (by omega)
  exact hflat.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi
    n r l R q ϖ hϖ hO₁ hker₁ hker₂ P hgeneric

end AlgebraicGeometry.Scheme.Modules

end
