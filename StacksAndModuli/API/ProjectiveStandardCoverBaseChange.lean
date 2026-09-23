module

public import StacksAndModuli.API.ProjectiveSpaceBaseChange

/-!
# Base change of the standard affine cover of polynomial projective space

This file packages the standard opens `D₊(Xᵢ)` of polynomial `Proj` as scheme opens and
records their behavior under coefficient change.  The opens and their pairwise intersections
are affine, they cover projective space, and restricting the cartesian coefficient-change
square to either a chart or an overlap remains cartesian.

These are the geometric inputs for a finite-Čech proof that global sections of a
quasicoherent sheaf on projective space commute with flat coefficient change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry ProjectiveSpectrum

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The standard affine open `D₊(Xᵢ)` in polynomial projective space. -/
noncomputable def polynomialStandardOpen (n : ℕ) (R : Type u) [CommRing R]
    (i : Fin (n + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i)

/-- The inverse image of a standard polynomial projective chart under coefficient
change is the corresponding standard chart. -/
theorem polynomialMap_preimage_polynomialStandardOpen
    (n : ℕ) (f : R →+* S) (i : Fin (n + 1)) :
    polynomialMap (Fin (n + 1)) f ⁻¹ᵁ polynomialStandardOpen n R i =
      polynomialStandardOpen n S i := by
  unfold polynomialStandardOpen
  rw [polynomialMap_preimage_basicOpen, MvPolynomial.map_X]

/-- Coefficient change also preserves pairwise intersections of the standard
projective cover. -/
theorem polynomialMap_preimage_polynomialStandardOpen_inf
    (n : ℕ) (f : R →+* S) (i j : Fin (n + 1)) :
    polynomialMap (Fin (n + 1)) f ⁻¹ᵁ
        (polynomialStandardOpen n R i ⊓ polynomialStandardOpen n R j) =
      polynomialStandardOpen n S i ⊓ polynomialStandardOpen n S j := by
  rw [Scheme.Hom.preimage_inf,
    polynomialMap_preimage_polynomialStandardOpen,
    polynomialMap_preimage_polynomialStandardOpen]

/-- A standard polynomial projective chart is affine. -/
theorem polynomialStandardOpen_isAffineOpen
    (n : ℕ) (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    IsAffineOpen (polynomialStandardOpen n R i) := by
  unfold polynomialStandardOpen
  exact isAffineOpen_basicOpen
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (f := MvPolynomial.X i) (m := 1)
    (MvPolynomial.isHomogeneous_X R i) Nat.one_pos

/-- Pairwise intersections of standard polynomial projective charts are affine. -/
theorem polynomialStandardOpen_inf_isAffineOpen
    (n : ℕ) (R : Type u) [CommRing R] (i j : Fin (n + 1)) :
    IsAffineOpen (polynomialStandardOpen n R i ⊓
      polynomialStandardOpen n R j) := by
  unfold polynomialStandardOpen
  rw [← basicOpen_mul]
  exact isAffineOpen_basicOpen
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (f := MvPolynomial.X i * MvPolynomial.X j) (m := 2)
    (by
      have hi : MvPolynomial.X i ∈
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_X R i)
      have hj : MvPolynomial.X j ∈
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_X R j)
      simpa using SetLike.mul_mem_graded hi hj) (by omega)

/-- The standard polynomial projective charts cover the projective spectrum. -/
theorem iSup_polynomialStandardOpen_eq_top (n : ℕ) (R : Type u) [CommRing R] :
    ⨆ i : Fin (n + 1), polynomialStandardOpen n R i = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (MvPolynomial.irrelevant_toIdeal_le_idealOfVars (Fin (n + 1)) R)

namespace ProjectiveCoverPullback

variable (n : ℕ) (f : R →+* S)

noncomputable abbrev XR : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

noncomputable abbrev YS : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)

noncomputable abbrev g : YS (S := S) n ⟶ XR (R := R) n :=
  polynomialMap (Fin (n + 1)) f

noncomputable abbrev pR : XR (R := R) n ⟶ Spec (.of R) :=
  polynomialToSpec (Fin (n + 1)) R

noncomputable abbrev pS : YS (S := S) n ⟶ Spec (.of S) :=
  polynomialToSpec (Fin (n + 1)) S

noncomputable abbrev b : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom f)

noncomputable abbrev UR (i : Fin (n + 1)) : (XR (R := R) n).Opens :=
  polynomialStandardOpen n R i

noncomputable abbrev US (i : Fin (n + 1)) : (YS (S := S) n).Opens :=
  g n f ⁻¹ᵁ UR (R := R) n i

/-- The source chart, defined literally as an inverse image for pullback arguments,
is the correspondingly named standard chart. -/
theorem US_eq_polynomialStandardOpen (i : Fin (n + 1)) :
    US n f i = polynomialStandardOpen n S i :=
  polynomialMap_preimage_polynomialStandardOpen n f i

/-- The literal inverse-image charts cover the source polynomial projective space. -/
theorem iSup_US_eq_top : ⨆ i : Fin (n + 1), US n f i = ⊤ := by
  simp_rw [US_eq_polynomialStandardOpen]
  exact iSup_polynomialStandardOpen_eq_top n S

/-- Each target chart in the restricted coefficient-change square is affine. -/
theorem UR_isAffineOpen (i : Fin (n + 1)) :
    IsAffineOpen (UR (R := R) n i) :=
  polynomialStandardOpen_isAffineOpen n R i

/-- Each source chart in the restricted coefficient-change square is affine. -/
theorem US_isAffineOpen (i : Fin (n + 1)) :
    IsAffineOpen (US n f i) := by
  rw [US_eq_polynomialStandardOpen]
  exact polynomialStandardOpen_isAffineOpen n S i

noncomputable def chartMap (i : Fin (n + 1)) :
    (US n f i).toScheme ⟶ (UR (R := R) n i).toScheme :=
  g n f ∣_ UR (R := R) n i

/-- Restricting the cartesian coefficient-change square to one standard chart
remains cartesian. -/
theorem isPullback_chart (i : Fin (n + 1)) :
    IsPullback (chartMap n f i)
      ((US n f i).ι ≫ pS (S := S) n)
      ((UR (R := R) n i).ι ≫ pR (R := R) n)
      (b f) := by
  let H := polynomialMap_isPullback (Fin (n + 1)) R f
  let Hres := isPullback_morphismRestrict (g n f) (UR (R := R) n i)
  exact Hres.paste_vert H

noncomputable abbrev UR2 (ij : Fin (n + 1) × Fin (n + 1)) :
    (XR (R := R) n).Opens :=
  polynomialStandardOpen n R ij.1 ⊓ polynomialStandardOpen n R ij.2

noncomputable abbrev US2 (ij : Fin (n + 1) × Fin (n + 1)) :
    (YS (S := S) n).Opens :=
  g n f ⁻¹ᵁ UR2 (R := R) n ij

/-- A literal inverse-image overlap is the corresponding pairwise intersection of
standard source charts. -/
theorem US2_eq_polynomialStandardOpen_inf
    (ij : Fin (n + 1) × Fin (n + 1)) :
    US2 n f ij =
      polynomialStandardOpen n S ij.1 ⊓ polynomialStandardOpen n S ij.2 :=
  polynomialMap_preimage_polynomialStandardOpen_inf n f ij.1 ij.2

/-- Each target pairwise overlap is affine. -/
theorem UR2_isAffineOpen (ij : Fin (n + 1) × Fin (n + 1)) :
    IsAffineOpen (UR2 (R := R) n ij) :=
  polynomialStandardOpen_inf_isAffineOpen n R ij.1 ij.2

/-- Each source pairwise overlap is affine. -/
theorem US2_isAffineOpen (ij : Fin (n + 1) × Fin (n + 1)) :
    IsAffineOpen (US2 n f ij) := by
  rw [US2_eq_polynomialStandardOpen_inf]
  exact polynomialStandardOpen_inf_isAffineOpen n S ij.1 ij.2

noncomputable def overlapMap (ij : Fin (n + 1) × Fin (n + 1)) :
    (US2 n f ij).toScheme ⟶ (UR2 (R := R) n ij).toScheme :=
  g n f ∣_ UR2 (R := R) n ij

/-- Restricting the cartesian coefficient-change square to a pairwise overlap
remains cartesian. -/
theorem isPullback_overlap (ij : Fin (n + 1) × Fin (n + 1)) :
    IsPullback (overlapMap n f ij)
      ((US2 n f ij).ι ≫ pS (S := S) n)
      ((UR2 (R := R) n ij).ι ≫ pR (R := R) n)
      (b f) := by
  let H := polynomialMap_isPullback (Fin (n + 1)) R f
  let Hres := isPullback_morphismRestrict (g n f) (UR2 (R := R) n ij)
  exact Hres.paste_vert H

end ProjectiveCoverPullback

end AlgebraicGeometry.Proj
