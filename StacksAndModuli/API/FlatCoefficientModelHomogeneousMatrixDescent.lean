module

public import StacksAndModuli.API.FlatCoefficientModelHomogeneousPresentation

/-!
# Descending homogeneous matrix presentations

A uniformly homogeneous polynomial matrix has a canonical finite polynomial presentation:
its quotient is the total module of the degreewise graded cokernel.  This choice remembers
the grading which an arbitrary `PolynomialModel` forgets.  Consequently every coefficient
matrix mapping to this canonical relation matrix is homogeneous as well, because coefficient
subalgebras embed in the original coefficient ring.

This file supplies the presentation-level input for upgrading a flat coefficient model to a
`FlatCoefficientModel.ShiftedFreeHomogeneousPresentation`.  The remaining comparison is now
only the canonical cokernel base-change isomorphism from
`GradedModule.Total.homogeneousMatrixCokerBaseChangeIso`.

Main declarations:

* `GradedModule.Total.homogeneousMatrixPolynomialModel`;
* `FlatCoefficientModel.homogeneousRelation_of_homogeneousMatrixPolynomialModel`;
* `FlatCoefficientModel.shiftedFreeHomogeneousPresentation_of_homogeneousMatrixPolynomialModel`;
* `FlatCoefficientModel.hasGradedRealization_of_homogeneousMatrixPolynomialModel`;
* `FlatCoefficientModel.exists_eventual_noetherianCechModel_of_homogeneousMatrixPolynomialModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open MvPolynomial

variable {A : Type u} [CommRing A] {n m r degree : ℕ}

/-- The canonical ordinary finite presentation attached to a uniformly homogeneous matrix.

Its presented module is the total module of the degreewise graded cokernel.  The quotient
map is the total cokernel map written in the standard basis of the unshifted free target. -/
noncomputable def homogeneousMatrixPolynomialModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree) :
    Module.FinitePresentation.PolynomialModel A (Fin (n + 1))
      (GradedModule.coker (homogeneousMatrixHom G hG)).Total := by
  let f := homogeneousMatrixHom G hG
  let eM := shiftedFreeLinearEquiv (R := A) (n := n) (r := m) (-(degree : ℤ))
  let eN := shiftedFreeLinearEquiv (R := A) (n := n) (r := r) 0
  let q := (GradedModule.Total.map (GradedModule.toCoker f)).comp eN.toLinearMap
  refine
    { generators := r
      relations := m
      quotient := q
      relation := Matrix.toLin' G
      quotient_surjective := ?_
      exact := ?_ }
  · exact (GradedModule.Total.surjective_map_of_surjective
      (GradedModule.toCoker f) (GradedModule.surjective_toCoker_app f)).comp eN.surjective
  · have hExact : Function.Exact (GradedModule.Total.map f)
        (GradedModule.Total.map (GradedModule.toCoker f)) := by
      rw [LinearMap.exact_iff]
      exact (GradedModule.Total.range_map_eq_kernel_map_toCoker f).symm
    have hConj : Function.Exact
        (eN.symm.toLinearMap.comp (GradedModule.Total.map f)) q := by
      exact (LinearEquiv.conj_exact_iff_exact
        (GradedModule.Total.map f)
        (GradedModule.Total.map (GradedModule.toCoker f)) eN.symm).mpr hExact
    have hPre : Function.Exact
        ((eN.symm.toLinearMap.comp (GradedModule.Total.map f)).comp eM.toLinearMap) q :=
      (LinearEquiv.precomp_exact_iff_exact (e := eM)).mpr hConj
    have hRelation :
        (eN.symm.toLinearMap.comp (GradedModule.Total.map f)).comp eM.toLinearMap =
          Matrix.toLin' G := by
      have htotal := homogeneousMatrixHom_totalRelation G hG
      change eN.symm.toLinearMap.comp (GradedModule.Total.map f) =
        (Matrix.toLin' G).comp eM.symm.toLinearMap at htotal
      rw [htotal]
      have hinv : eM.symm.toLinearMap.comp eM.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact eM.symm_apply_apply x
      rw [LinearMap.comp_assoc, hinv, LinearMap.comp_id]
    rw [← hRelation]
    exact hPre

@[simp] lemma homogeneousMatrixPolynomialModel_generators
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree) :
    (homogeneousMatrixPolynomialModel G hG).generators = r := rfl

@[simp] lemma homogeneousMatrixPolynomialModel_relations
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree) :
    (homogeneousMatrixPolynomialModel G hG).relations = m := rfl

@[simp] lemma homogeneousMatrixPolynomialModel_relation
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree) :
    (homogeneousMatrixPolynomialModel G hG).relation = Matrix.toLin' G := rfl

@[simp] lemma toMatrix_homogeneousMatrixPolynomialModel_relation
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree) :
    LinearMap.toMatrix' (homogeneousMatrixPolynomialModel G hG).relation = G := by
  change LinearMap.toMatrix' (Matrix.toLin' G) = G
  convert LinearMap.toMatrix'_toLin' G using 1

/-- Homogeneity of a polynomial is reflected by an injective coefficient map. -/
lemma mem_polySubmodule_of_map_mem
    {B : Type u} [CommRing B] (f : B →+* A) (hf : Function.Injective f)
    {p : MvPolynomial (Fin (n + 1)) B}
    (hp : MvPolynomial.map f p ∈ polySubmodule A n degree) :
    p ∈ polySubmodule B n degree := by
  rw [polySubmodule_of_nonneg (k := B) (n := n) (by omega),
    MvPolynomial.mem_homogeneousSubmodule]
  rw [polySubmodule_of_nonneg (k := A) (n := n) (by omega),
    MvPolynomial.mem_homogeneousSubmodule] at hp
  exact MvPolynomial.IsHomogeneous.of_map hf hp

/-- The graded morphism constructed from a homogeneous matrix depends only on the matrix,
not on the proof of homogeneity. -/
lemma homogeneousMatrixHom_congr
    {G H : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A)}
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree)
    (hH : ∀ i j, H i j ∈ polySubmodule A n degree) (h : G = H) :
    homogeneousMatrixHom G hG = homogeneousMatrixHom H hH := by
  subst H
  rfl

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

namespace Module.FinitePresentation.PolynomialModel.FlatCoefficientModel

open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

variable {R : Type w} {A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] {n m r degree : ℕ}

omit [IsNoetherianRing R] in
/-- The relation matrix in a flat coefficient model of the canonical homogeneous
presentation remains homogeneous of the same degree. -/
theorem homogeneousRelation_of_homogeneousMatrixPolynomialModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ GradedModule.polySubmodule A n degree)
    (E : FlatCoefficientModel (R := R) (homogeneousMatrixPolynomialModel G hG)) :
    ∀ i j, E.relation i j ∈
      GradedModule.polySubmodule E.coefficientRing n degree := by
  intro i j
  apply mem_polySubmodule_of_map_mem
    (f := algebraMap E.coefficientRing A) Subtype.val_injective
  have hij := congrFun (congrFun E.relation_map i) j
  simp only [Matrix.map_apply,
    toMatrix_homogeneousMatrixPolynomialModel_relation] at hij
  rw [hij]
  exact hG i j

omit [IsNoetherianRing R] in
/-- A flat coefficient model of the canonical homogeneous matrix presentation automatically
has the shifted-free homogeneous presentation needed for a compatible graded realization. -/
noncomputable def shiftedFreeHomogeneousPresentation_of_homogeneousMatrixPolynomialModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ GradedModule.polySubmodule A n degree)
    (E : FlatCoefficientModel (R := R) (homogeneousMatrixPolynomialModel G hG)) :
    ShiftedFreeHomogeneousPresentation
      (GradedModule.coker (homogeneousMatrixHom G hG)) E := by
  let hE := homogeneousRelation_of_homogeneousMatrixPolynomialModel G hG E
  let mappedRelation := E.relation.map
    (MvPolynomial.map (algebraMap E.coefficientRing A))
  let hMapped := homogeneousMatrix_map_mem_polySubmodule (A := A) E.relation hE
  have hmap : mappedRelation = G := by
    simpa only [mappedRelation,
      toMatrix_homogeneousMatrixPolynomialModel_relation] using E.relation_map
  have hhom : homogeneousMatrixHom mappedRelation hMapped =
      homogeneousMatrixHom G hG :=
    homogeneousMatrixHom_congr hMapped hG hmap
  let eTarget : GradedModule.coker (homogeneousMatrixHom mappedRelation hMapped) ≅
      GradedModule.coker (homogeneousMatrixHom G hG) :=
    eqToIso (congrArg (fun f ↦ GradedModule.coker f) hhom)
  exact ShiftedFreeHomogeneousPresentation.ofHomogeneousMatrix
    (GradedModule.coker (homogeneousMatrixHom G hG)) E degree hE
    ⟨homogeneousMatrixCokerBaseChangeIso E.relation hE ≪≫ eTarget⟩

/-- A flat coefficient model of the canonical homogeneous-matrix presentation carries the
compatible grading required by the noetherian flat polynomial model API.  No additional
choice of a descended grading is needed: it is the cokernel grading of the descended
homogeneous matrix. -/
theorem hasGradedRealization_of_homogeneousMatrixPolynomialModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ GradedModule.polySubmodule A n degree)
    (E : FlatCoefficientModel (R := R) (homogeneousMatrixPolynomialModel G hG)) :
    (E.toNoetherianFlatPolynomialModel (R := R)).HasGradedRealization
      (GradedModule.coker (homogeneousMatrixHom G hG)) :=
  (E.shiftedFreeHomogeneousPresentation_of_homogeneousMatrixPolynomialModel G
    hG).toHasGradedRealization

/-- A flat coefficient model of a canonical homogeneous-matrix cokernel therefore gives
noetherian Čech models in every sufficiently large twist.  This is the composed endpoint
used by projective Quot once its affine graded module has been put in homogeneous-matrix
form. -/
theorem exists_eventual_noetherianCechModel_of_homogeneousMatrixPolynomialModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ GradedModule.polySubmodule A n degree)
    (E : FlatCoefficientModel (R := R) (homogeneousMatrixPolynomialModel G hG)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel
        (GradedModule.coker (homogeneousMatrixHom G hG)) d) :=
  (E.shiftedFreeHomogeneousPresentation_of_homogeneousMatrixPolynomialModel G
    hG).exists_eventual_noetherianCechModel

end Module.FinitePresentation.PolynomialModel.FlatCoefficientModel

end

end
