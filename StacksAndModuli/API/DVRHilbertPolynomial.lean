module

public import StacksAndModuli.API.DVRFieldPoints
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Fibrewise Hilbert polynomials over a DVR

This file reduces a fibrewise Hilbert-polynomial assertion over the spectrum of a
discrete valuation ring to its restrictions to the generic and closed points.  The
reduction uses `IsDiscreteValuationRing.fieldPoint_factorization`: every field-valued
point factors through one of those two points.

The remaining input in the valuative criterion for fixed-polynomial Quot is therefore
precisely constancy between the generic and closed fibres of a flat projective family.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Fibrewise Hilbert polynomial is preserved by base change. -/
theorem HasFiberwiseHilbertPolynomial.pullback
    {n : ℕ} {S T : Scheme.{u}} (g : T ⟶ S)
    {Q : (Scheme.projectiveSpaceOver n S).Modules} {P : Polynomial ℚ}
    (hQ : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    Scheme.HasFiberwiseHilbertPolynomial
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj Q) P := by
  intro K hK s
  let e₀ := (Scheme.Modules.pullbackComp
    (Scheme.projectiveSpaceOverMap n s)
    (Scheme.projectiveSpaceOverMap n g)).app Q
  let e₁ := (Scheme.Modules.pullbackCongr
    (Scheme.projectiveSpaceOverMap_comp n s g)).app Q
  apply Scheme.HasHilbertPolynomialOver.iso (e₀ ≪≫ e₁).symm
  exact hQ K hK (s ≫ g)

/-- A sheaf on projective space over a DVR has fibrewise Hilbert polynomial `P` if its
restrictions to both the generic point and the closed residue-field point do. -/
theorem HasFiberwiseHilbertPolynomial.of_dvr_generic_and_closed
    {n : ℕ} {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    (P : Polynomial ℚ)
    (hgeneric : Scheme.HasFiberwiseHilbertPolynomial
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj Q) P)
    (hclosed : Scheme.HasFiberwiseHilbertPolynomial
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n
        ((Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R)))).obj Q) P) :
    Scheme.HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  letI : Field K := hK.toField
  rcases IsDiscreteValuationRing.fieldPoint_factorization K s with
    ⟨t, ht⟩ | ⟨t, ht⟩
  · let e₀ := (Scheme.Modules.pullbackComp
      (Scheme.projectiveSpaceOverMap n t)
      (Scheme.projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).app Q
    let e₁ := (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverMap_comp n t
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).app Q
    let e₂ := (Scheme.Modules.pullbackCongr
      (congrArg (Scheme.projectiveSpaceOverMap n) ht)).app Q
    apply Scheme.HasHilbertPolynomialOver.iso (e₀ ≪≫ e₁ ≪≫ e₂)
    exact hgeneric (CommRingCat.of K) (Field.toIsField K) t
  · let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let e₀ := (Scheme.Modules.pullbackComp
      (Scheme.projectiveSpaceOverMap n t)
      (Scheme.projectiveSpaceOverMap n c)).app Q
    let e₁ := (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverMap_comp n t c)).app Q
    let e₂ := (Scheme.Modules.pullbackCongr
      (congrArg (Scheme.projectiveSpaceOverMap n) ht)).app Q
    apply Scheme.HasHilbertPolynomialOver.iso (e₀ ≪≫ e₁ ≪≫ e₂)
    exact hclosed (CommRingCat.of K) (Field.toIsField K) t

end AlgebraicGeometry.Scheme
