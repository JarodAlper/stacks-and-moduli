module

public import StacksAndModuli.API.ProjectiveLineLaurentCech
public import StacksAndModuli.API.ProjectiveStandardCoverBaseChange
public import StacksAndModuli.API.SheafCohomologyMayerVietorisVanishing
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Structure-sheaf sections on the standard cover of the projective line

This file identifies the rings of sections on the two standard charts of polynomial
`Proj` in dimension one with `R[X]`, and the ring of sections on their intersection
with `R[T;T⁻¹]`. Under these identifications, the two restriction maps are the
embeddings `p(X) ↦ p(T)` and `q(X) ↦ q(T⁻¹)`.

Consequently, the actual Mayer--Vietoris difference map on structure-sheaf sections
is surjective. Combined with the generic Mayer--Vietoris criterion, this proves
`H¹(ℙ¹_R, 𝒪) = 0` from precisely the two remaining local `H¹`-vanishing
assumptions on the standard affine charts. Discharging those assumptions requires
the affine quasicoherent acyclicity theorem, which is not yet available in the
repository.

## Main results

* `AlgebraicGeometry.Proj.overlapLaurentEquivAway`;
* `AlgebraicGeometry.Proj.standardAwayDifference_surjective`;
* `AlgebraicGeometry.Proj.projectiveLineSectionsDifference_surjective`;
* `AlgebraicGeometry.Proj.projectiveLine_H_one_subsingleton_of_chart_H_one`.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial Polynomial
open CategoryTheory TopologicalSpace
open AlgebraicGeometry ProjectiveSpectrum HomogeneousLocalization

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- The standard total-degree grading on the homogeneous coordinate ring of `ℙ¹_R`. -/
noncomputable abbrev lineGrading :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

/-- The first homogeneous coordinate has degree one. -/
theorem X_zero_mem_lineGrading :
    MvPolynomial.X (0 : Fin 2) ∈ lineGrading R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2))

/-- The second homogeneous coordinate has degree one. -/
theorem X_one_mem_lineGrading :
    MvPolynomial.X (1 : Fin 2) ∈ lineGrading R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))

/-- The product of the two homogeneous coordinates has degree two. -/
theorem X_zero_mul_X_one_mem_lineGrading :
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
      lineGrading R 2 :=
  SetLike.mul_mem_graded (X_zero_mem_lineGrading R)
    (X_one_mem_lineGrading R)

/-- There is a unique index in `Fin 2` distinct from zero. -/
@[instance_reducible]
def finTwoNeZeroUnique : Unique {j : Fin 2 // j ≠ (0 : Fin 2)} :=
  { default := ⟨1, by decide⟩
    uniq := by
      rintro ⟨j, hj⟩
      apply Subtype.ext
      fin_cases j
      · exact (hj rfl).elim
      · rfl }

/-- There is a unique index in `Fin 2` distinct from one. -/
@[instance_reducible]
def finTwoNeOneUnique : Unique {j : Fin 2 // j ≠ (1 : Fin 2)} :=
  { default := ⟨0, by decide⟩
    uniq := by
      rintro ⟨j, hj⟩
      apply Subtype.ext
      fin_cases j
      · rfl
      · exact (hj rfl).elim }

attribute [local instance] finTwoNeZeroUnique finTwoNeOneUnique

/-- The coordinate ring of the first standard chart of `ℙ¹_R` is `R[X]`. -/
noncomputable def chartZeroPolynomialEquivAway :
    R[X] ≃+* Away (lineGrading R) (MvPolynomial.X (0 : Fin 2)) := by
  exact (MvPolynomial.uniqueAlgEquiv R _).symm.toRingEquiv.trans
    (projectiveChartPolynomialEquivAway (Fin 2) 0 R)

/-- The coordinate ring of the second standard chart of `ℙ¹_R` is `R[X]`. -/
noncomputable def chartOnePolynomialEquivAway :
    R[X] ≃+* Away (lineGrading R) (MvPolynomial.X (1 : Fin 2)) := by
  exact (MvPolynomial.uniqueAlgEquiv R _).symm.toRingEquiv.trans
    (projectiveChartPolynomialEquivAway (Fin 2) 1 R)

/-- The polynomial generator on the first chart is the ratio `X₁ / X₀`. -/
theorem chartZeroPolynomialEquivAway_X :
    chartZeroPolynomialEquivAway R Polynomial.X =
      Away.isLocalizationElem
        (X_zero_mem_lineGrading R) (X_one_mem_lineGrading R) := by
  rw [chartZeroPolynomialEquivAway, RingEquiv.trans_apply]
  change polynomialChartToAway (Fin 2) 0 R
      ((MvPolynomial.uniqueAlgEquiv R _).symm Polynomial.X) = _
  rw [show (MvPolynomial.uniqueAlgEquiv R _).symm Polynomial.X =
      MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 2 // j ≠ (0 : Fin 2)}) by
    rw [MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.eval₂_X]
    exact congrArg (MvPolynomial.X (R := R)) (Subsingleton.elim _ _)]
  rw [polynomialChartToAway_X]
  simp [polynomialChartCoordinate, Away.isLocalizationElem]

/-- The polynomial generator on the second chart is the ratio `X₀ / X₁`. -/
theorem chartOnePolynomialEquivAway_X :
    chartOnePolynomialEquivAway R Polynomial.X =
      Away.isLocalizationElem
        (X_one_mem_lineGrading R) (X_zero_mem_lineGrading R) := by
  rw [chartOnePolynomialEquivAway, RingEquiv.trans_apply]
  change polynomialChartToAway (Fin 2) 1 R
      ((MvPolynomial.uniqueAlgEquiv R _).symm Polynomial.X) = _
  rw [show (MvPolynomial.uniqueAlgEquiv R _).symm Polynomial.X =
      MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 2 // j ≠ (1 : Fin 2)}) by
    rw [MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.eval₂_X]
    exact congrArg (MvPolynomial.X (R := R)) (Subsingleton.elim _ _)]
  rw [polynomialChartToAway_X]
  simp [polynomialChartCoordinate, Away.isLocalizationElem]

/-- The overlap ring as an `R[X]`-algebra via restriction from the first chart. -/
@[instance_reducible]
noncomputable instance overlapPolynomialAlgebra :
    Algebra R[X]
      (Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))) :=
  ((HomogeneousLocalization.awayMap (lineGrading R)
    (X_one_mem_lineGrading R) rfl).comp
      (chartZeroPolynomialEquivAway R).toRingHom).toAlgebra

/-- The overlap ring is obtained from the first chart ring by inverting `X`. -/
noncomputable instance overlapPolynomialIsLocalization :
    IsLocalization.Away (Polynomial.X : R[X])
      (Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))) := by
  let A₀ := Away (lineGrading R) (MvPolynomial.X (0 : Fin 2))
  let Q := Away (lineGrading R)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
  let t : A₀ := Away.isLocalizationElem
    (X_zero_mem_lineGrading R) (X_one_mem_lineGrading R)
  let h₀ : R[X] ≃+* A₀ := chartZeroPolynomialEquivAway R
  letI : Algebra A₀ Q :=
    (HomogeneousLocalization.awayMap (lineGrading R)
      (X_one_mem_lineGrading R) rfl).toAlgebra
  letI : IsLocalization.Away t Q := by
    dsimp only [t, A₀, Q]
    exact HomogeneousLocalization.Away.isLocalization_mul
      (f := MvPolynomial.X (0 : Fin 2))
      (g := MvPolynomial.X (1 : Fin 2))
      (X_zero_mem_lineGrading R) (X_one_mem_lineGrading R) rfl (by decide)
  have hloc := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers t) Q h₀.symm
  have ht : h₀.symm t = Polynomial.X := by
    apply h₀.injective
    rw [h₀.apply_symm_apply]
    simpa only [h₀, t, A₀] using
      (chartZeroPolynomialEquivAway_X R).symm
  have hM : (Submonoid.powers t).map h₀.symm =
      Submonoid.powers (Polynomial.X : R[X]) := by
    rw [Submonoid.map_powers, ht]
  rw [hM] at hloc
  exact hloc

/-- The coordinate ring of the intersection of the standard charts is `R[T;T⁻¹]`. -/
noncomputable def overlapLaurentEquivAway :
    R[T;T⁻¹] ≃+*
      Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) :=
  (IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : R[X]))
    R[T;T⁻¹]
      (Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))).toRingEquiv

/-- Restriction from the first chart sends `p(X)` to `p(T)` on the overlap. -/
theorem overlapLaurentEquivAway_toLaurent (p : R[X]) :
    overlapLaurentEquivAway R (Polynomial.toLaurent p) =
      HomogeneousLocalization.awayMap (lineGrading R)
        (X_one_mem_lineGrading R) rfl
        (chartZeroPolynomialEquivAway R p) := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact (IsLocalization.algEquiv
    (Submonoid.powers (Polynomial.X : R[X])) R[T;T⁻¹]
      (Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))).commutes p

/-- Restriction from the second chart sends `p(X)` to `p(T⁻¹)` on the overlap. -/
theorem overlapLaurentEquivAway_invert_toLaurent (p : R[X]) :
    overlapLaurentEquivAway R
        (LaurentPolynomial.invert (Polynomial.toLaurent p)) =
      HomogeneousLocalization.awayMap (lineGrading R)
        (X_zero_mem_lineGrading R)
        (mul_comm _ _) (chartOnePolynomialEquivAway R p) := by
  let Q := Away (lineGrading R)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
  have hC (r : R) : overlapLaurentEquivAway R
        (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r))) =
      HomogeneousLocalization.awayMap (lineGrading R)
        (X_zero_mem_lineGrading R) (mul_comm _ _)
        (chartOnePolynomialEquivAway R (Polynomial.C r)) := by
    calc
      _ = overlapLaurentEquivAway R
          (Polynomial.toLaurent (Polynomial.C r)) := by
        rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
      _ = HomogeneousLocalization.awayMap (lineGrading R)
          (X_one_mem_lineGrading R) rfl
          (chartZeroPolynomialEquivAway R (Polynomial.C r)) :=
        overlapLaurentEquivAway_toLaurent R (Polynomial.C r)
      _ = _ := by
        apply HomogeneousLocalization.val_injective
        simp only [Fin.isValue, chartZeroPolynomialEquivAway, ne_eq,
          AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
          AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
          RingEquiv.coe_trans, RingEquiv.coe_mk, EquivLike.coe_coe,
          Function.comp_apply, MvPolynomial.uniqueAlgEquiv_symm_apply,
          Polynomial.eval₂_C, projectiveChartPolynomialEquivAway_apply,
          HomogeneousLocalization.val_awayMap, polynomialChartToAway_C_val,
          chartOnePolynomialEquivAway]
        rw [show (⟨1, Submonoid.one_mem _⟩ :
              Submonoid.powers (MvPolynomial.X (0 : Fin 2))) = 1 by rfl,
          show (⟨1, Submonoid.one_mem _⟩ :
              Submonoid.powers (MvPolynomial.X (1 : Fin 2))) = 1 by rfl,
          Localization.mk_one_eq_algebraMap,
          Localization.mk_one_eq_algebraMap,
          IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  have hX : overlapLaurentEquivAway R
        (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X)) =
      HomogeneousLocalization.awayMap (lineGrading R)
        (X_zero_mem_lineGrading R) (mul_comm _ _)
        (chartOnePolynomialEquivAway R Polynomial.X) := by
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    have hT := overlapLaurentEquivAway_toLaurent R Polynomial.X
    rw [Polynomial.toLaurent_X] at hT
    apply IsUnit.mul_right_cancel
      ((LaurentPolynomial.isUnit_T (R := R) (1 : ℤ)).map
        (overlapLaurentEquivAway R).toRingHom)
    change overlapLaurentEquivAway R (LaurentPolynomial.T (-1)) *
        overlapLaurentEquivAway R (LaurentPolynomial.T 1) =
      _ * overlapLaurentEquivAway R (LaurentPolynomial.T 1)
    rw [← map_mul]
    rw [← LaurentPolynomial.T_add]
    simp only [neg_add_cancel, LaurentPolynomial.T_zero, map_one]
    rw [hT]
    apply HomogeneousLocalization.val_injective
    simp only [Fin.isValue, HomogeneousLocalization.val_one,
      chartOnePolynomialEquivAway_X, Away.isLocalizationElem, pow_one,
      HomogeneousLocalization.awayMap_mk, Nat.reduceAdd,
      chartZeroPolynomialEquivAway_X, HomogeneousLocalization.val_mul,
      Away.val_mk]
    rw [Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp
    ring
  let f : R[X] →+* Q := (overlapLaurentEquivAway R).toRingHom.comp
    (LaurentPolynomial.invert (R := R)).toRingEquiv.toRingHom |>.comp
      Polynomial.toLaurent
  let g : R[X] →+* Q :=
    (HomogeneousLocalization.awayMap (lineGrading R)
      (X_zero_mem_lineGrading R)
      (mul_comm _ _)).comp (chartOnePolynomialEquivAway R).toRingHom
  have hfg : f = g := by
    apply Polynomial.ringHom_ext hC hX
  exact DFunLike.congr_fun hfg p

/-- The difference of the two restriction maps to the standard-chart overlap. -/
noncomputable def standardAwayDifference :
    Away (lineGrading R) (MvPolynomial.X (0 : Fin 2)) ×
        Away (lineGrading R) (MvPolynomial.X (1 : Fin 2)) →+
      Away (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) where
  toFun pq := HomogeneousLocalization.awayMap (lineGrading R)
      (X_one_mem_lineGrading R) rfl pq.1 -
    HomogeneousLocalization.awayMap (lineGrading R)
      (X_zero_mem_lineGrading R) (mul_comm _ _) pq.2
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/-- The Laurent-coordinate equivalences intertwine the two chart-difference maps. -/
theorem overlapLaurentEquivAway_twoChartDifference
    (pq : R[X] × R[X]) :
    overlapLaurentEquivAway R
        (LaurentPolynomial.twoChartDifference R pq) =
      standardAwayDifference R
        (chartZeroPolynomialEquivAway R pq.1,
          chartOnePolynomialEquivAway R pq.2) := by
  rw [LaurentPolynomial.twoChartDifference_apply, map_sub,
    overlapLaurentEquivAway_toLaurent,
    overlapLaurentEquivAway_invert_toLaurent]
  rfl

/-- The difference map from the two standard chart rings to their overlap is surjective. -/
theorem standardAwayDifference_surjective :
    Function.Surjective (standardAwayDifference R) := by
  intro z
  obtain ⟨⟨p, q⟩, hpq⟩ := LaurentPolynomial.twoChartDifference_surjective R
    ((overlapLaurentEquivAway R).symm z)
  refine ⟨⟨chartZeroPolynomialEquivAway R p,
    chartOnePolynomialEquivAway R q⟩, ?_⟩
  calc
    standardAwayDifference R _ = overlapLaurentEquivAway R
        (LaurentPolynomial.twoChartDifference R (p, q)) :=
      (overlapLaurentEquivAway_twoChartDifference R (p, q)).symm
    _ = overlapLaurentEquivAway R ((overlapLaurentEquivAway R).symm z) :=
      congrArg (overlapLaurentEquivAway R) hpq
    _ = z := (overlapLaurentEquivAway R).apply_symm_apply z

/-- Polynomial `Proj` in two variables, regarded as the projective line over `R`. -/
noncomputable abbrev projectiveLine := Proj (lineGrading R)

/-- The first standard affine chart of the projective line. -/
noncomputable abbrev projectiveLineChartZero : (projectiveLine R).Opens :=
  polynomialStandardOpen 1 R 0

/-- The second standard affine chart of the projective line. -/
noncomputable abbrev projectiveLineChartOne : (projectiveLine R).Opens :=
  polynomialStandardOpen 1 R 1

/-- The underlying additive sheaf of the structure sheaf of the projective line. -/
noncomputable abbrev projectiveLineStructureAddSheaf :
    TopCat.Sheaf AddCommGrpCat (projectiveLine R) :=
  (SheafOfModules.toSheaf (projectiveLine R).ringCatSheaf).obj
    (Scheme.structureModule (projectiveLine R))

/-- The intersection of the two standard charts is the basic open of `X₀X₁`. -/
theorem projectiveLineChart_inf :
    projectiveLineChartZero R ⊓ projectiveLineChartOne R =
      Proj.basicOpen (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) := by
  exact (Proj.basicOpen_mul (lineGrading R)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))).symm

/-- The two standard charts cover the projective line. -/
theorem projectiveLineChart_sup :
    projectiveLineChartZero R ⊔ projectiveLineChartOne R = ⊤ := by
  calc
    projectiveLineChartZero R ⊔ projectiveLineChartOne R =
        ⨆ i : Fin 2, polynomialStandardOpen 1 R i := by
      apply le_antisymm
      · exact sup_le (le_iSup _ 0) (le_iSup _ 1)
      · refine iSup_le fun i ↦ ?_
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
    _ = ⊤ := iSup_polynomialStandardOpen_eq_top 1 R

/-- Sections on the chart intersection transported to sections on the basic open of `X₀X₁`. -/
noncomputable def projectiveLineOverlapSectionsIso :
    Γ(projectiveLine R,
        projectiveLineChartZero R ⊓ projectiveLineChartOne R) ≅
      Γ(projectiveLine R, Proj.basicOpen (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))) :=
  (projectiveLine R).presheaf.mapIso
    ((eqToIso (projectiveLineChart_inf R).symm).op)

/-- Restriction from the first standard chart agrees with homogeneous localization. -/
theorem chartZeroRestriction_eq_awayMap (a :
    Away (lineGrading R) (MvPolynomial.X (0 : Fin 2))) :
    (projectiveLine R).presheaf.map
        (homOfLE (Proj.basicOpen_mono (lineGrading R)
          (MvPolynomial.X (0 : Fin 2))
          (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
          ⟨MvPolynomial.X (1 : Fin 2), rfl⟩)).op
        ((Proj.basicOpenIsoAway (lineGrading R) (MvPolynomial.X (0 : Fin 2))
          (X_zero_mem_lineGrading R) (by decide)).hom a) =
      (Proj.basicOpenIsoAway (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
        (X_zero_mul_X_one_mem_lineGrading R) (by decide)).hom
        (HomogeneousLocalization.awayMap (lineGrading R)
          (X_one_mem_lineGrading R) rfl a) := by
  change (projectiveLine R).presheaf.map _
      (Proj.awayToSection (lineGrading R) (MvPolynomial.X (0 : Fin 2)) a) =
    Proj.awayToSection (lineGrading R)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
      (HomogeneousLocalization.awayMap (lineGrading R)
        (X_one_mem_lineGrading R) rfl a)
  have h := Proj.awayMap_awayToSection (lineGrading R)
    (f := MvPolynomial.X (0 : Fin 2))
    (g := MvPolynomial.X (1 : Fin 2))
    (x := MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    (X_one_mem_lineGrading R) rfl
  exact congrArg (fun k ↦ k a) h.symm

/-- Restriction from the second standard chart agrees with homogeneous localization. -/
theorem chartOneRestriction_eq_awayMap (a :
    Away (lineGrading R) (MvPolynomial.X (1 : Fin 2))) :
    (projectiveLine R).presheaf.map
        (homOfLE (Proj.basicOpen_mono (lineGrading R)
          (MvPolynomial.X (1 : Fin 2))
          (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
          ⟨MvPolynomial.X (0 : Fin 2), mul_comm _ _⟩)).op
        ((Proj.basicOpenIsoAway (lineGrading R) (MvPolynomial.X (1 : Fin 2))
          (X_one_mem_lineGrading R) (by decide)).hom a) =
      (Proj.basicOpenIsoAway (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
        (X_zero_mul_X_one_mem_lineGrading R) (by decide)).hom
        (HomogeneousLocalization.awayMap (lineGrading R)
          (X_zero_mem_lineGrading R) (mul_comm _ _) a) := by
  change (projectiveLine R).presheaf.map _
      (Proj.awayToSection (lineGrading R) (MvPolynomial.X (1 : Fin 2)) a) =
    Proj.awayToSection (lineGrading R)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
      (HomogeneousLocalization.awayMap (lineGrading R)
        (X_zero_mem_lineGrading R) (mul_comm _ _) a)
  have h := Proj.awayMap_awayToSection (lineGrading R)
    (f := MvPolynomial.X (1 : Fin 2))
    (g := MvPolynomial.X (0 : Fin 2))
    (x := MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    (X_zero_mem_lineGrading R) (mul_comm _ _)
  exact congrArg (fun k ↦ k a) h.symm

/-- The first restriction map after transporting the intersection to the basic open. -/
theorem projectiveLineOverlapSectionsIso_restrict_zero (a :
    Away (lineGrading R) (MvPolynomial.X (0 : Fin 2))) :
    (projectiveLineOverlapSectionsIso R).hom
        ((projectiveLine R).presheaf.map
          (homOfLE (show projectiveLineChartZero R ⊓
            projectiveLineChartOne R ≤ projectiveLineChartZero R from inf_le_left)).op
          ((Proj.basicOpenIsoAway (lineGrading R) (MvPolynomial.X (0 : Fin 2))
            (X_zero_mem_lineGrading R) (by decide)).hom a)) =
      (Proj.basicOpenIsoAway (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
        (X_zero_mul_X_one_mem_lineGrading R) (by decide)).hom
        (HomogeneousLocalization.awayMap (lineGrading R)
          (X_one_mem_lineGrading R) rfl a) := by
  rw [← chartZeroRestriction_eq_awayMap]
  change (projectiveLine R).presheaf.map _
      ((projectiveLine R).presheaf.map _ _) = _
  rw [← (projectiveLine R).presheaf.map_comp_apply]
  congr 1

/-- The second restriction map after transporting the intersection to the basic open. -/
theorem projectiveLineOverlapSectionsIso_restrict_one (a :
    Away (lineGrading R) (MvPolynomial.X (1 : Fin 2))) :
    (projectiveLineOverlapSectionsIso R).hom
        ((projectiveLine R).presheaf.map
          (homOfLE (show projectiveLineChartZero R ⊓
            projectiveLineChartOne R ≤ projectiveLineChartOne R from inf_le_right)).op
          ((Proj.basicOpenIsoAway (lineGrading R) (MvPolynomial.X (1 : Fin 2))
            (X_one_mem_lineGrading R) (by decide)).hom a)) =
      (Proj.basicOpenIsoAway (lineGrading R)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
        (X_zero_mul_X_one_mem_lineGrading R) (by decide)).hom
        (HomogeneousLocalization.awayMap (lineGrading R)
          (X_zero_mem_lineGrading R) (mul_comm _ _) a) := by
  rw [← chartOneRestriction_eq_awayMap]
  change (projectiveLine R).presheaf.map _
      ((projectiveLine R).presheaf.map _ _) = _
  rw [← (projectiveLine R).presheaf.map_comp_apply]
  congr 1

/-- The actual two-chart Mayer--Vietoris difference on structure-sheaf sections is
surjective. -/
theorem projectiveLineSectionsDifference_surjective : Function.Surjective
    ((_root_.Opens.mayerVietorisSquare
      (projectiveLineChartZero R) (projectiveLineChartOne R)).sectionsDifference
        (projectiveLineStructureAddSheaf R)) := by
  intro s
  let e₀ := Proj.basicOpenIsoAway (lineGrading R)
    (MvPolynomial.X (0 : Fin 2)) (X_zero_mem_lineGrading R) (by decide)
  let e₁ := Proj.basicOpenIsoAway (lineGrading R)
    (MvPolynomial.X (1 : Fin 2)) (X_one_mem_lineGrading R) (by decide)
  let e₀₁ := Proj.basicOpenIsoAway (lineGrading R)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    (X_zero_mul_X_one_mem_lineGrading R) (by decide)
  let eₒ := projectiveLineOverlapSectionsIso R
  obtain ⟨⟨a₀, a₁⟩, ha⟩ := standardAwayDifference_surjective R
    (e₀₁.inv (eₒ.hom s))
  refine ⟨⟨e₀.hom a₀, e₁.hom a₁⟩, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso eₒ.hom).injective
  change eₒ.hom
      ((projectiveLine R).presheaf.map
          (homOfLE (show projectiveLineChartZero R ⊓
            projectiveLineChartOne R ≤ projectiveLineChartZero R from inf_le_left)).op
          (e₀.hom a₀) -
        (projectiveLine R).presheaf.map
          (homOfLE (show projectiveLineChartZero R ⊓
            projectiveLineChartOne R ≤ projectiveLineChartOne R from inf_le_right)).op
          (e₁.hom a₁)) = eₒ.hom s
  rw [map_sub, projectiveLineOverlapSectionsIso_restrict_zero,
    projectiveLineOverlapSectionsIso_restrict_one]
  rw [← map_sub]
  change e₀₁.hom (standardAwayDifference R (a₀, a₁)) = eₒ.hom s
  rw [ha]
  exact e₀₁.inv_hom_id_apply (eₒ.hom s)

/-- If structure-sheaf `H¹` vanishes on both standard charts, then it vanishes on
the projective line. The two assumptions are exactly the remaining instances of
affine quasicoherent acyclicity needed by this argument. -/
theorem projectiveLine_H_one_subsingleton_of_chart_H_one
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLineChartZero R).toScheme) 1)]
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLineChartOne R).toScheme) 1)] :
    Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLine R)) 1) :=
  Scheme.Modules.subsingleton_H_one_structureModule_of_openCover_of_sections
    (projectiveLine R) (projectiveLineChartZero R) (projectiveLineChartOne R)
    (projectiveLineChart_sup R) (projectiveLineSectionsDifference_surjective R)

end AlgebraicGeometry.Proj

end
