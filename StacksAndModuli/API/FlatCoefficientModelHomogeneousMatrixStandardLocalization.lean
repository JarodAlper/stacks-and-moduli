module

public import StacksAndModuli.API.FlatCoefficientModelHomogeneousMatrixDescent
public import StacksAndModuli.API.FlatCoefficientModelNoetherianPolynomial
public import StacksAndModuli.API.PolynomialModelPrimewiseFlatCoefficientStage
public import StacksAndModuli.API.ProjectiveGradedH0
public import StacksAndModuli.API.ProjectiveGradedNoetherianCechComplexModel
public import StacksAndModuli.API.ProjectiveSpaceBaseChange

/-!
# Coefficient models flat on the standard projective charts

A homogeneous polynomial matrix need not have a coefficient-flat total cokernel even when
its associated projective family is flat.  The appropriate input for projective Cech
arguments is weaker: the degreewise cokernel becomes coefficient-flat after localizing at
each standard variable.

This file first identifies the degree-zero part of such a localization with the ordinary
cokernel of the matrix obtained by dehomogenizing at the corresponding variable.  It then
uses polynomial coefficient spreading simultaneously on the finitely many standard charts.
The resulting homogeneous matrix over one finitely generated noetherian coefficient ring
has flat standard-variable localizations, without asserting flatness of its total cokernel.

Main declarations:

* `GradedModule.Total.homogeneousMatrixDehomogenize`;
* `GradedModule.Total.homogeneousMatrixCokerLocZeroEquiv`;
* `GradedModule.Total.HomogeneousMatrixStandardFlatModel`;
* `GradedModule.Total.exists_homogeneousMatrixStandardFlatModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open CategoryTheory
open TensorProduct
open Module.FinitePresentation

namespace LinearMap

/-- A commuting square whose vertical maps are linear equivalences identifies the concrete
cokernels of its horizontal maps. -/
noncomputable def cokerEquivOfComm
    {R M₁ M₂ N₁ N₂ : Type u} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f : M₁ →ₗ[R] M₂) (g : N₁ →ₗ[R] N₂)
    (e₁ : M₁ ≃ₗ[R] N₁) (e₂ : M₂ ≃ₗ[R] N₂)
    (h : e₂.toLinearMap.comp f = g.comp e₁.toLinearMap) :
    (M₂ ⧸ LinearMap.range f) ≃ₗ[R] (N₂ ⧸ LinearMap.range g) := by
  have hrange : (LinearMap.range f).map e₂.toLinearMap = LinearMap.range g := by
    rw [← LinearMap.range_comp, h]
    apply LinearMap.range_comp_of_range_eq_top
    exact LinearEquiv.range e₁
  exact Submodule.Quotient.equiv _ _ e₂ hrange

end LinearMap

namespace Module.FinitePresentation.PolynomialModel

variable {A B : Type u} {sigma : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable {m r : ℕ}

/-- The tautological polynomial presentation of the concrete cokernel of a polynomial
matrix. -/
noncomputable def ofPolynomialMatrixCokernel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    PolynomialModel A sigma (polynomialMatrixCokernel G) where
  generators := r
  relations := m
  quotient := (LinearMap.range (Matrix.toLin' G)).mkQ
  relation := Matrix.toLin' G
  quotient_surjective := Submodule.mkQ_surjective _
  exact := LinearMap.exact_map_mkQ_range (Matrix.toLin' G)

@[simp]
lemma ofPolynomialMatrixCokernel_generators
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    (ofPolynomialMatrixCokernel G).generators = r := rfl

@[simp]
lemma ofPolynomialMatrixCokernel_relations
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    (ofPolynomialMatrixCokernel G).relations = m := rfl

@[simp]
lemma ofPolynomialMatrixCokernel_relation
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    (ofPolynomialMatrixCokernel G).relation = Matrix.toLin' G := rfl

@[simp]
lemma toMatrix_ofPolynomialMatrixCokernel_relation
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    LinearMap.toMatrix' (ofPolynomialMatrixCokernel G).relation = G := by
  exact LinearMap.toMatrix'_toLin' G

/-- Flatness for the canonical coefficient action is equivalent to flatness for the
explicit restriction of the polynomial-ring action. -/
theorem flat_polynomialMatrixCokernel_iff_compHom
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    Module.Flat A (polynomialMatrixCokernel G) ↔
      letI : Module A (polynomialMatrixCokernel G) :=
        Module.compHom (polynomialMatrixCokernel G)
          (algebraMap A (MvPolynomial sigma A))
      Module.Flat A (polynomialMatrixCokernel G) := by
  rw [compHom_polynomialMatrixCokernel_eq G]

/-- Coefficient-ring scalar extension commutes with the concrete cokernel of a polynomial
matrix.  This is the coefficient-level form of
`polynomialMatrixCokernelBaseChangeEquiv`; the polynomial-algebra tensor factor is cancelled
using the standard pushout square. -/
noncomputable def polynomialMatrixCokernelCoefficientBaseChangeEquiv
    (G : Matrix (Fin r) (Fin m) (MvPolynomial sigma A)) :
    let N := polynomialMatrixCokernel G
    let G' := G.map (MvPolynomial.map (algebraMap A B))
    let N' := polynomialMatrixCokernel G'
    B ⊗[A] N ≃ₗ[B] N' := by
  let P := MvPolynomial sigma A
  let Q := MvPolynomial sigma B
  let N := polynomialMatrixCokernel G
  let G' := G.map (MvPolynomial.map (algebraMap A B))
  let N' := polynomialMatrixCokernel G'
  letI : IsScalarTower A P N := inferInstance
  letI : IsScalarTower B Q N' := inferInstance
  letI : Algebra P Q := MvPolynomial.algebraMvPolynomial
  letI : Module B (Q ⊗[P] N) := TensorProduct.leftModule
  letI : IsScalarTower B Q (Q ⊗[P] N) :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      induction x with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add x y hx hy =>
        rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy]
      | tmul q x => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  let eCancel : B ⊗[A] N ≃ₗ[B] Q ⊗[P] N :=
    (Algebra.IsPushout.cancelBaseChange A B P Q N).symm
  let eCokerQ : Q ⊗[P] N ≃ₗ[Q] N' :=
    polynomialMatrixCokernelBaseChangeEquiv (R₁ := A) (S₁ := B) G
  let eCoker : Q ⊗[P] N ≃ₗ[B] N' := eCokerQ.restrictScalars B
  exact eCancel.trans eCoker

end Module.FinitePresentation.PolynomialModel

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

/-! ## Localization commutes with the concrete degreewise cokernel -/

/-- The concrete cokernel of a localized graded morphism is the corresponding component of
the localization of its degreewise cokernel. -/
noncomputable def locCokerAppEquiv {M N : GradedModule A n} (f : M ⟶ N)
    (l : List (Fin (n + 1))) (d : ℤ) :
    ((N.loc l).obj d ⧸ LinearMap.range ((locMap l f).app d).hom) ≃ₗ[A]
      ((coker f).loc l).obj d := by
  let q := ((locMap l (toCoker f)).app d).hom
  have hq : Function.Surjective q :=
    surjective_locMap_app_of_surjective (M := N) (l := l) (toCoker f) d
      (fun t ↦ surjective_toCoker_app f (locDeg l d t))
  have hex : Function.Exact ((locMap l f).app d).hom q :=
    exact_locMap_app l f (toCoker f) d (fun t ↦ by
      change Function.Exact ((f.app (locDeg l d t)).hom)
        (LinearMap.range ((f.app (locDeg l d t)).hom)).mkQ
      exact LinearMap.exact_map_mkQ_range ((f.app (locDeg l d t)).hom))
  let eKer :
      ((N.loc l).obj d ⧸ LinearMap.range ((locMap l f).app d).hom) ≃ₗ[A]
        ((N.loc l).obj d ⧸ LinearMap.ker q) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl A _)
      (by simpa using hex.linearMap_ker_eq.symm)
  exact eKer.trans (q.quotKerEquivOfSurjective hq)

/-- On a localization at one variable, coefficient-flatness of the degree-zero piece
implies coefficient-flatness in every degree.  Multiplication by the inverted variable
identifies all adjacent pieces. -/
theorem isFlat_loc_singleton_of_flat_zero (M : GradedModule A n)
    (a : Fin (n + 1))
    (hzero : Module.Flat A ((M.loc [a]).obj 0)) : IsFlat (M.loc [a]) := by
  letI : Module.Flat A ((M.loc [a]).obj 0) := hzero
  intro d
  induction d using Int.induction_on with
  | zero => infer_instance
  | succ i hi =>
      letI : Module.Flat A ((M.loc [a]).obj (i : ℤ)) := hi
      letI := M.loc_mulX_isIso [a] a (by simp) (i : ℤ)
      exact Module.Flat.of_linearEquiv
        (asIso ((M.loc [a]).mulX a (i : ℤ))).symm.toLinearEquiv
  | pred i hi =>
      letI : Module.Flat A ((M.loc [a]).obj (-(i : ℤ))) := hi
      letI := M.loc_mulX_isIso [a] a (by simp) (-(i : ℤ) - 1)
      have hpred : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by omega
      exact Module.Flat.of_linearEquiv
        ((asIso ((M.loc [a]).mulX a (-(i : ℤ) - 1))).toLinearEquiv.trans
          (eqToIso (congrArg (M.loc [a]).obj hpred)).toLinearEquiv)

/-! ## Degree-zero localization of a shifted polynomial module -/

namespace Total

open _root_.Module.FinitePresentation.PolynomialModel

variable {m r D : ℕ}

/-- Dehomogenization as a coefficient-linear map. -/
noncomputable def dehomogenizeLinearMap (a : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) A →ₗ[A]
      MvPolynomial {j : Fin (n + 1) // j ≠ a} A where
  toFun := AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A
  map_add' p q := map_add _ p q
  map_smul' c p := by simp [Algebra.smul_def]

@[simp]
lemma dehomogenizeLinearMap_apply (a : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) A) :
    dehomogenizeLinearMap (A := A) a p =
      AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A p := rfl

/-- The stage map from forms of degree `-D+j` to the polynomial ring of the standard
`a`-chart.  Algebraically it simply sets `X_a` equal to one. -/
noncomputable def structureLocNegChartStage (a : Fin (n + 1)) (D j : ℕ) :
    (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j) →ₗ[A]
      MvPolynomial {b : Fin (n + 1) // b ≠ a} A :=
  (dehomogenizeLinearMap (A := A) a).comp
    (polySubmodule A n (locDeg [a] (0 + -(D : ℤ)) j)).subtype

@[simp]
lemma structureLocNegChartStage_apply (a : Fin (n + 1)) (D j : ℕ)
    (p : (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j)) :
    structureLocNegChartStage (A := A) a D j p =
      AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A p.1 := rfl

/-- The dehomogenization stage maps respect the transition maps in the localization tower. -/
lemma structureLocNegChartStage_locTr (a : Fin (n + 1)) (D : ℕ)
    (j j' : ℕ) (hjj' : j ≤ j')
    (p : (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j)) :
    structureLocNegChartStage (A := A) a D j'
        (((structureModule A n).locTr [a] (0 + -(D : ℤ)) j j' hjj').hom p) =
      structureLocNegChartStage (A := A) a D j p := by
  rw [structureLocNegChartStage_apply, structureLocNegChartStage_apply, locTr,
    structureModule_mulList_singleton_val]
  simp only [map_mul, map_pow,
    AlgebraicGeometry.Proj.polynomialDehomogenize_X_pivot, one_pow, one_mul]

/-- Dehomogenization on the sequential localization tower. -/
noncomputable def structureLocNegToChart (a : Fin (n + 1)) (D : ℕ) :
    ((structureModule A n).loc [a]).obj (0 + -(D : ℤ)) →ₗ[A]
      MvPolynomial {b : Fin (n + 1) // b ≠ a} A :=
  Module.DirectLimit.lift A ℕ
    (fun j : ℕ ↦ (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j))
    (fun j j' h ↦ ((structureModule A n).locTr [a] (0 + -(D : ℤ)) j j' h).hom)
    (fun j ↦ structureLocNegChartStage (A := A) a D j)
    (fun j j' hjj' p ↦ structureLocNegChartStage_locTr a D j j' hjj' p)

/-- Evaluation of the localization-to-chart map on a tower representative. -/
lemma structureLocNegToChart_locIncl (a : Fin (n + 1)) (D j : ℕ)
    (p : (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j)) :
    structureLocNegToChart (A := A) a D
        (((structureModule A n).locIncl [a] (0 + -(D : ℤ)) j).hom p) =
      AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A p.1 := by
  exact Module.DirectLimit.lift_of _ _ _

/-- On one homogeneous stage, setting the pivot variable to one is injective. -/
lemma structureLocNegChartStage_injective (a : Fin (n + 1)) (D j : ℕ) :
    Function.Injective (structureLocNegChartStage (A := A) a D j) := by
  intro p q hpq
  let e : ℤ := locDeg [a] (0 + -(D : ℤ)) j
  by_cases he : e < 0
  · have hp0 : p = 0 := by
      apply Subtype.ext
      have hle : polySubmodule A n e ≤ ⊥ :=
        le_of_eq (polySubmodule_of_neg A n he)
      exact (Submodule.mem_bot A).mp (hle p.2)
    have hq0 : q = 0 := by
      apply Subtype.ext
      have hle : polySubmodule A n e ≤ ⊥ :=
        le_of_eq (polySubmodule_of_neg A n he)
      exact (Submodule.mem_bot A).mp (hle q.2)
    rw [hp0, hq0]
  · have he0 : 0 ≤ e := le_of_not_gt he
    have hpHom : p.1.IsHomogeneous e.toNat := by
      have hle : polySubmodule A n e ≤
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e.toNat :=
        le_of_eq (polySubmodule_of_nonneg A n he0)
      exact (MvPolynomial.mem_homogeneousSubmodule e.toNat p.1).mp (hle p.2)
    have hqHom : q.1.IsHomogeneous e.toNat := by
      have hle : polySubmodule A n e ≤
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e.toNat :=
        le_of_eq (polySubmodule_of_nonneg A n he0)
      exact (MvPolynomial.mem_homogeneousSubmodule e.toNat q.1).mp (hle q.2)
    let P := MvPolynomial (Fin (n + 1)) A
    let L := Localization (Submonoid.powers (MvPolynomial.X a : P))
    let s : Submonoid.powers (MvPolynomial.X a : P) :=
      ⟨MvPolynomial.X a ^ e.toNat, by use e.toNat⟩
    have hpFrac :
        (AlgebraicGeometry.Proj.polynomialChartToAway (Fin (n + 1)) a A
          (AlgebraicGeometry.Proj.polynomialDehomogenize
            (Fin (n + 1)) a A p.1)).val =
          (Localization.mk p.1 s : L) := by
      simpa only [P, L, s] using
        AlgebraicGeometry.Proj.polynomialChartToAway_dehomogenize
          (Fin (n + 1)) a A p.1 e.toNat hpHom
    have hqFrac :
        (AlgebraicGeometry.Proj.polynomialChartToAway (Fin (n + 1)) a A
          (AlgebraicGeometry.Proj.polynomialDehomogenize
            (Fin (n + 1)) a A q.1)).val =
          (Localization.mk q.1 s : L) := by
      simpa only [P, L, s] using
        AlgebraicGeometry.Proj.polynomialChartToAway_dehomogenize
          (Fin (n + 1)) a A q.1 e.toNat hqHom
    have hfrac : (Localization.mk p.1 s : L) = Localization.mk q.1 s := by
      rw [← hpFrac, ← hqFrac]
      exact congrArg (fun z ↦
        (AlgebraicGeometry.Proj.polynomialChartToAway
          (Fin (n + 1)) a A z).val) hpq
    have hmul := congrArg (fun z : L ↦ z * algebraMap P L (s : P)) hfrac
    rw [Localization.mk_eq_mk',
      IsLocalization.mk'_spec L p.1 s, IsLocalization.mk'_spec L q.1 s] at hmul
    apply Subtype.ext
    apply IsLocalization.injectiveₛ L
      (fun z hz ↦ by
        obtain ⟨t, ht⟩ :=
          (Submonoid.mem_powers_iff z (MvPolynomial.X a : P)).mp hz
        rw [← ht]
        exact MvPolynomial.isRegular_X_pow t)
    exact hmul

/-- Dehomogenization from the degree `-D` localization is injective. -/
lemma structureLocNegToChart_injective (a : Fin (n + 1)) (D : ℕ) :
    Function.Injective (structureLocNegToChart (A := A) a D) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨j, p, rfl⟩ :=
    (structureModule A n).locIncl_exists [a] (0 + -(D : ℤ)) z
  rw [structureLocNegToChart_locIncl] at hz
  have hp0 : p = 0 := structureLocNegChartStage_injective a D j (by
    simpa only [structureLocNegChartStage_apply, map_zero] using hz)
  rw [hp0, map_zero]

/-- Every chart polynomial is the dehomogenization of a homogeneous representative in a
sufficiently late tower stage. -/
lemma structureLocNegToChart_surjective (a : Fin (n + 1)) (D : ℕ) :
    Function.Surjective (structureLocNegToChart (A := A) a D) := by
  intro q
  let j : ℕ := q.totalDegree + D
  have hdeg : locDeg [a] (0 + -(D : ℤ)) j = (q.totalDegree : ℤ) := by
    simp only [locDeg, List.length_singleton, Nat.cast_one, mul_one, j]
    push_cast
    ring
  let p : (structureModule A n).obj (locDeg [a] (0 + -(D : ℤ)) j) :=
    ⟨AlgebraicGeometry.Proj.polynomialChartHomogenize (Fin (n + 1)) a A q, by
      rw [hdeg, polySubmodule_of_nonneg A n (Int.natCast_nonneg _),
        MvPolynomial.mem_homogeneousSubmodule]
      simpa using
        AlgebraicGeometry.Proj.polynomialChartHomogenize_isHomogeneous
          (Fin (n + 1)) a A q⟩
  refine ⟨((structureModule A n).locIncl [a] (0 + -(D : ℤ)) j).hom p, ?_⟩
  rw [structureLocNegToChart_locIncl]
  exact AlgebraicGeometry.Proj.polynomialDehomogenize_chartHomogenize
    (Fin (n + 1)) a A q

/-- The degree `-D` part of the localization of the polynomial structure module at `X_a`
is the polynomial ring on the non-pivot variables. -/
noncomputable def structureLocNegChartEquiv (a : Fin (n + 1)) (D : ℕ) :
    ((structureModule A n).loc [a]).obj (0 + -(D : ℤ)) ≃ₗ[A]
      MvPolynomial {b : Fin (n + 1) // b ≠ a} A :=
  LinearEquiv.ofBijective (structureLocNegToChart (A := A) a D)
    ⟨structureLocNegToChart_injective a D,
      structureLocNegToChart_surjective a D⟩

/-- After localizing at `X_a`, a rank-`r` free module shifted by `-D` is a rank-`r`
free module over the dehomogenized chart ring in degree zero. -/
noncomputable def shiftedFreeLocZeroChartEquiv (a : Fin (n + 1)) (r D : ℕ) :
    ((shiftedFree A n r (-(D : ℤ))).loc [a]).obj 0 ≃ₗ[A]
      (Fin r → MvPolynomial {b : Fin (n + 1) // b ≠ a} A) :=
  (locPowIso ((structureModule A n).twist (-(D : ℤ))) [a] r 0).toLinearEquiv |>.trans
    (LinearEquiv.piCongrRight fun _ : Fin r ↦
      (twistLocIso (structureModule A n) [a] (-(D : ℤ)) 0).toLinearEquiv |>.trans
        (structureLocNegChartEquiv (A := A) a D))

/-- The free chart comparison sends a tower representative to its coordinatewise
dehomogenization. -/
lemma shiftedFreeLocZeroChartEquiv_locIncl_apply (a : Fin (n + 1)) (r D j : ℕ)
    (x : (shiftedFree A n r (-(D : ℤ))).obj (locDeg [a] 0 j))
    (i : Fin r) :
    shiftedFreeLocZeroChartEquiv (A := A) a r D
        (((shiftedFree A n r (-(D : ℤ))).locIncl [a] 0 j).hom x) i =
      AlgebraicGeometry.Proj.polynomialDehomogenize
        (Fin (n + 1)) a A (x i).1 := by
  simp only [shiftedFreeLocZeroChartEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  change structureLocNegToChart (A := A) a D
    ((twistLocToLoc (structureModule A n) [a] (-(D : ℤ)) 0).hom
      ((locPowToPi ((structureModule A n).twist (-(D : ℤ))) [a] r 0).hom
        (((shiftedFree A n r (-(D : ℤ))).locIncl [a] 0 j).hom x) i)) = _
  rw [show
    ((locPowToPi ((structureModule A n).twist (-(D : ℤ))) [a] r 0).hom
      (((shiftedFree A n r (-(D : ℤ))).locIncl [a] 0 j).hom x)) i =
        ((((structureModule A n).twist (-(D : ℤ))).locIncl [a] 0 j).hom (x i)) by
      simpa only [locPowToPi, ModuleCat.hom_ofHom, LinearMap.pi_apply] using
        locIncl_locPowProj ((structureModule A n).twist (-(D : ℤ))) [a] r i 0 j x]
  have htw := congrArg ModuleCat.Hom.hom
    (locIncl_twistLocToLoc (structureModule A n) [a] (-(D : ℤ)) 0 j)
  simp only [ModuleCat.hom_comp] at htw
  have hdeg : locDeg [a] 0 j + -(D : ℤ) =
      locDeg [a] (0 + -(D : ℤ)) j := by
    rw [locDeg_def, locDeg_def]
    ring
  have hstage :
      twistLoc_stage_eq (structureModule A n) [a] (-(D : ℤ)) 0 j =
        congrArg (structureModule A n).obj hdeg :=
    Subsingleton.elim _ _
  rw [hstage] at htw
  have htwx := LinearMap.congr_fun htw (x i)
  simp only [LinearMap.comp_apply] at htwx
  calc
    _ =
      structureLocNegToChart (A := A) a D
        (((structureModule A n).locIncl [a] (0 + -(D : ℤ)) j).hom
          ((eqToHom (twistLoc_stage_eq
            (structureModule A n) [a] (-(D : ℤ)) 0 j)).hom (x i))) :=
        congrArg (structureLocNegToChart (A := A) a D) htwx
    _ = _ := by
      rw [structureLocNegToChart_locIncl]
      apply congrArg
      exact structureModule_eqToHom_val hdeg (x i)

/-! ## Homogeneous matrices on a standard chart -/

/-- The matrix on the standard `a`-chart obtained by setting `X_a` equal to one. -/
noncomputable def homogeneousMatrixDehomogenize
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (a : Fin (n + 1)) :
    Matrix (Fin r) (Fin m)
      (MvPolynomial {b : Fin (n + 1) // b ≠ a} A) :=
  G.map (AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A)

@[simp]
lemma homogeneousMatrixDehomogenize_apply
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (a : Fin (n + 1)) (i : Fin r) (j : Fin m) :
    homogeneousMatrixDehomogenize G a i j =
      AlgebraicGeometry.Proj.polynomialDehomogenize
        (Fin (n + 1)) a A (G i j) := rfl

/-- Dehomogenization commutes with a change of coefficients. -/
theorem polynomialDehomogenize_map
    {B : Type u} [CommRing B] (f : B →+* A) (a : Fin (n + 1)) :
    (AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A).comp
        (MvPolynomial.map f) =
      (MvPolynomial.map f).comp
        (AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a B) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, MvPolynomial.map_C,
      AlgebraicGeometry.Proj.polynomialDehomogenize_C]
  · intro i
    by_cases hia : i = a
    · subst i
      simp only [RingHom.comp_apply, MvPolynomial.map_X,
        AlgebraicGeometry.Proj.polynomialDehomogenize_X_pivot, map_one]
    · simp only [RingHom.comp_apply, MvPolynomial.map_X,
        AlgebraicGeometry.Proj.polynomialDehomogenize_X_nonpivot _ _ _ i hia]

/-- Under the free chart comparisons, localization of a homogeneous matrix map is the
ordinary linear map associated to its dehomogenized matrix. -/
theorem homogeneousMatrixLocZero_chart
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n D) (a : Fin (n + 1)) :
    (shiftedFreeLocZeroChartEquiv (A := A) a r 0).toLinearMap.comp
        (((locMap [a] (homogeneousMatrixHom G hG)).app 0).hom) =
      ((Matrix.toLin' (homogeneousMatrixDehomogenize G a)).restrictScalars A).comp
        (shiftedFreeLocZeroChartEquiv (A := A) a m D).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨j, x, rfl⟩ :=
    (shiftedFree A n m (-(D : ℤ))).locIncl_exists [a] 0 z
  funext i
  simp only [LinearMap.comp_apply]
  have hloc := locMap_locIncl_apply
    (M := shiftedFree A n m (-(D : ℤ))) (l := [a])
    (homogeneousMatrixHom G hG) 0 j x
  calc
    _ = shiftedFreeLocZeroChartEquiv (A := A) a r 0
        (((shiftedFree A n r 0).locIncl [a] 0 j).hom
          (((homogeneousMatrixHom G hG).app (locDeg [a] 0 j)).hom x)) i :=
      congrArg (fun y ↦ shiftedFreeLocZeroChartEquiv (A := A) a r 0 y i) hloc
    _ = AlgebraicGeometry.Proj.polynomialDehomogenize
          (Fin (n + 1)) a A
          ((((homogeneousMatrixHom G hG).app (locDeg [a] 0 j)).hom x) i).1 := by
      simpa using
        shiftedFreeLocZeroChartEquiv_locIncl_apply
          (A := A) a r 0 j
            (((homogeneousMatrixHom G hG).app (locDeg [a] 0 j)).hom x) i
    _ = _ := by
      simp only [homogeneousMatrixHom_app_apply, map_sum, LinearMap.restrictScalars_apply,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_mul,
        homogeneousMatrixDehomogenize_apply]
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg
        (fun z ↦ AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A (G i k) * z)
        (shiftedFreeLocZeroChartEquiv_locIncl_apply (A := A) a m D j x k).symm

/-- The degree-zero localization of a homogeneous-matrix cokernel is the ordinary cokernel
of the dehomogenized chart matrix. -/
noncomputable def homogeneousMatrixCokerLocZeroEquiv
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n D) (a : Fin (n + 1)) :
    polynomialMatrixCokernel (homogeneousMatrixDehomogenize G a) ≃ₗ[A]
      ((coker (homogeneousMatrixHom G hG)).loc [a]).obj 0 := by
  let f := homogeneousMatrixHom G hG
  let eSource := shiftedFreeLocZeroChartEquiv (A := A) a m D
  let eTarget := shiftedFreeLocZeroChartEquiv (A := A) a r 0
  let eCoker := LinearMap.cokerEquivOfComm
    (((locMap [a] f).app 0).hom)
    ((Matrix.toLin' (homogeneousMatrixDehomogenize G a)).restrictScalars A)
    eSource eTarget (homogeneousMatrixLocZero_chart G hG a)
  exact eCoker.symm.trans (locCokerAppEquiv f [a] 0)

/-! ## Standard-localization-flat coefficient models -/

/-- A coefficient model of a homogeneous matrix whose cokernel is flat after localization
at every standard variable.  Flatness of the unlocalized total cokernel is deliberately not
part of this structure. -/
structure HomogeneousMatrixStandardFlatModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A)) where
  coefficientRing : Subalgebra ℤ A
  coefficientRing_fg : coefficientRing.FG
  relation : Matrix (Fin r) (Fin m)
    (MvPolynomial (Fin (n + 1)) coefficientRing)
  relation_homogeneous : ∀ i j,
    relation i j ∈ polySubmodule coefficientRing n D
  relation_map : relation.map
    (MvPolynomial.map (algebraMap coefficientRing A)) = G
  flat_loc : ∀ a : Fin (n + 1),
    IsFlat ((coker
      (homogeneousMatrixHom relation relation_homogeneous)).loc [a])

namespace HomogeneousMatrixStandardFlatModel

variable
    {G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A)}

instance coefficientRing_isNoetherian
    (E : HomogeneousMatrixStandardFlatModel (D := D) G) :
    IsNoetherianRing E.coefficientRing :=
  isNoetherianRing_of_fg E.coefficientRing_fg

/-- The descended graded cokernel. -/
noncomputable abbrev model
    (E : HomogeneousMatrixStandardFlatModel (D := D) G) :
    GradedModule E.coefficientRing n :=
  coker (homogeneousMatrixHom E.relation E.relation_homogeneous)

/-- The descended graded cokernel is finitely generated. -/
theorem model_isFG (E : HomogeneousMatrixStandardFlatModel (D := D) G) :
    IsFG E.model :=
  (((isFG_structureModule (k := E.coefficientRing) (n := n)).twist 0).pow r).coker
    (homogeneousMatrixHom E.relation E.relation_homogeneous)

/-- Extending coefficients in the descended graded cokernel recovers the original
homogeneous-matrix cokernel. -/
noncomputable def baseChangeIso
    (E : HomogeneousMatrixStandardFlatModel (D := D) G)
    (hG : ∀ i j, G i j ∈ polySubmodule A n D) :
    E.model.baseChange A ≅ coker (homogeneousMatrixHom G hG) := by
  let mappedRelation := E.relation.map
    (MvPolynomial.map (algebraMap E.coefficientRing A))
  let hMapped := homogeneousMatrix_map_mem_polySubmodule
    (A := A) E.relation E.relation_homogeneous
  have hhom : homogeneousMatrixHom mappedRelation hMapped =
      homogeneousMatrixHom G hG :=
    homogeneousMatrixHom_congr hMapped hG E.relation_map
  exact homogeneousMatrixCokerBaseChangeIso
      E.relation E.relation_homogeneous ≪≫
    eqToIso (congrArg (fun f ↦ coker f) hhom)

/-- A standard-localization-flat homogeneous coefficient model supplies the weak
noetherian Cech-complex models used by the projectivity argument. -/
theorem exists_eventual_noetherianCechComplexModel
    (E : HomogeneousMatrixStandardFlatModel (D := D) G)
    (hG : ∀ i j, G i j ∈ polySubmodule A n D) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (NoetherianCechComplexModel
        (coker (homogeneousMatrixHom G hG)) d) := by
  apply exists_eventual_noetherianCechComplexModel_of_flat_loc
    E.model E.model_isFG E.flat_loc (coker (homogeneousMatrixHom G hG))
  intro d
  exact cechComplexMapIso (E.baseChangeIso hG) d

end HomogeneousMatrixStandardFlatModel

set_option maxSynthPendingDepth 1 in
-- Lean's default depth avoids unnecessary nested instance searches in the chosen chart models.
/-- A homogeneous matrix whose cokernel is flat on every standard projective chart admits
one finitely generated noetherian coefficient model with the same property.

The coefficient ring is the finite supremum of the original homogeneous coefficient stage
and one flat coefficient model for each dehomogenized chart matrix. -/
theorem exists_homogeneousMatrixStandardFlatModel
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n D)
    (hflat : ∀ a : Fin (n + 1),
      IsFlat ((coker (homogeneousMatrixHom G hG)).loc [a])) :
    Nonempty (HomogeneousMatrixStandardFlatModel (D := D) G) := by
  let chartMatrix (a : Fin (n + 1)) := homogeneousMatrixDehomogenize G a
  let chartModel (a : Fin (n + 1)) :=
    _root_.Module.FinitePresentation.PolynomialModel.ofPolynomialMatrixCokernel
      (chartMatrix a)
  have hchartFlat (a : Fin (n + 1)) :
      let N := polynomialMatrixCokernel (chartMatrix a)
      letI : Module A N := Module.compHom N
        (algebraMap A
          (MvPolynomial {b : Fin (n + 1) // b ≠ a} A))
      Module.Flat A N := by
    dsimp only
    rw [_root_.Module.FinitePresentation.PolynomialModel.compHom_polynomialMatrixCokernel_eq]
    letI : Module.Flat A
        (((coker (homogeneousMatrixHom G hG)).loc [a]).obj 0) :=
      hflat a 0
    exact Module.Flat.of_linearEquiv
      (homogeneousMatrixCokerLocZeroEquiv G hG a)
  have hchartModel (a : Fin (n + 1)) : Nonempty
      (_root_.Module.FinitePresentation.PolynomialModel.FlatCoefficientModel
        (R := ℤ) (chartModel a)) :=
    _root_.Module.FinitePresentation.PolynomialModel.exists_flatCoefficientModel_of_flat
      (chartModel a) (hchartFlat a)
  let E (a : Fin (n + 1)) :
      _root_.Module.FinitePresentation.PolynomialModel.FlatCoefficientModel
        (R := ℤ) (chartModel a) :=
    Classical.choice (hchartModel a)
  let D₀ := homogeneousMatrixPolynomialModel G hG
  let chartRing (a : Fin (n + 1)) : Subalgebra ℤ A :=
    (E a).coefficientRing
  let chartSup : Subalgebra ℤ A := Finset.univ.sup chartRing
  let C : Subalgebra ℤ A := D₀.coefficientRing (R := ℤ) ⊔ chartSup
  have hchartSup : chartSup.FG := by
    exact Finset.sup_induction Subalgebra.fg_bot
      (fun _ hB _ hC ↦ hB.sup hC)
      (fun a _ ↦ (E a).coefficientRing_fg)
  have hCfg : C.FG := by
    exact D₀.coefficientRing_fg.sup hchartSup
  let i : _root_.Module.FinitePresentation.PolynomialModel.CoefficientStage
      (R := ℤ) D₀ := ⟨C, hCfg, le_sup_left⟩
  let H := _root_.Module.FinitePresentation.PolynomialModel.coefficientStageRelation D₀ i
  have hHMap : H.map (MvPolynomial.map (algebraMap C A)) = G := by
    simpa only [H, D₀,
      toMatrix_homogeneousMatrixPolynomialModel_relation] using
      _root_.Module.FinitePresentation.PolynomialModel.coefficientStageRelation_map D₀ i
  have hH : ∀ p q, H p q ∈ polySubmodule C n D := by
    intro p q
    apply mem_polySubmodule_of_map_mem
      (f := algebraMap C A) Subtype.val_injective
    have hpq : MvPolynomial.map (algebraMap C A) (H p q) = G p q := by
      simpa only [Matrix.map_apply] using congrFun (congrFun hHMap p) q
    rw [hpq]
    exact hG p q
  refine ⟨{
    coefficientRing := C
    coefficientRing_fg := hCfg
    relation := H
    relation_homogeneous := hH
    relation_map := hHMap
    flat_loc := ?_ }⟩
  intro a
  have hBaC : (E a).coefficientRing ≤ C := by
    exact (Finset.le_sup (f := chartRing) (Finset.mem_univ a)).trans le_sup_right
  let Ba := (E a).coefficientRing
  let algBaC : Algebra Ba C := (Subalgebra.inclusion hBaC).toRingHom.toAlgebra
  letI : Algebra Ba C := algBaC
  let HaC := (E a).relation.map
    (MvPolynomial.map (algebraMap Ba C))
  let NBa := polynomialMatrixCokernel (E a).relation
  letI : Module.Flat Ba NBa :=
    (flat_polynomialMatrixCokernel_iff_compHom ((E a).relation)).mpr (E a).flat
  have hbase : Module.Flat C (C ⊗[Ba] NBa) :=
    Module.Flat.baseChange Ba C NBa
  let NHaC := polynomialMatrixCokernel HaC
  have hHaC : Module.Flat C NHaC := by
    letI : Module.Flat C (C ⊗[Ba] NBa) := hbase
    let e : C ⊗[Ba] NBa ≃ₗ[C] NHaC :=
      polynomialMatrixCokernelCoefficientBaseChangeEquiv (B := C) (E a).relation
    exact Module.Flat.of_linearEquiv e.symm
  have hEMap : (E a).relation.map
      (MvPolynomial.map (algebraMap Ba A)) = chartMatrix a := by
    simpa only [chartModel,
      toMatrix_ofPolynomialMatrixCokernel_relation] using
      (E a).relation_map
  have hrel : homogeneousMatrixDehomogenize H a = HaC := by
    apply Matrix.ext
    intro p q
    apply MvPolynomial.map_injective (algebraMap C A) Subtype.val_injective
    simp only [homogeneousMatrixDehomogenize_apply, HaC, Matrix.map_apply]
    calc
      MvPolynomial.map (algebraMap C A)
          (AlgebraicGeometry.Proj.polynomialDehomogenize
            (Fin (n + 1)) a C (H p q)) =
          AlgebraicGeometry.Proj.polynomialDehomogenize
            (Fin (n + 1)) a A
              (MvPolynomial.map (algebraMap C A) (H p q)) := by
            exact (DFunLike.congr_fun
              (polynomialDehomogenize_map (algebraMap C A) a) (H p q)).symm
      _ = AlgebraicGeometry.Proj.polynomialDehomogenize
            (Fin (n + 1)) a A (G p q) := by
          exact congrArg
            (AlgebraicGeometry.Proj.polynomialDehomogenize (Fin (n + 1)) a A)
            (congrFun (congrFun hHMap p) q)
      _ = MvPolynomial.map (algebraMap C A)
            (MvPolynomial.map (algebraMap Ba C) ((E a).relation p q)) := by
          rw [MvPolynomial.map_map]
          have hcomp : (algebraMap C A).comp (algebraMap Ba C) =
              algebraMap Ba A := by
            apply RingHom.ext
            intro x
            rfl
          rw [hcomp]
          exact (congrFun (congrFun hEMap p) q).symm
  let Ndehom := polynomialMatrixCokernel
    (homogeneousMatrixDehomogenize H a)
  have hdehom : Module.Flat C Ndehom := by
    letI : Module.Flat C NHaC := hHaC
    let e : Ndehom ≃ₗ[MvPolynomial {b : Fin (n + 1) // b ≠ a} C] NHaC :=
      polynomialMatrixCokernelCongr hrel
    exact Module.Flat.of_linearEquiv (e.restrictScalars C)
  have hzero : Module.Flat C
      (((coker (homogeneousMatrixHom H hH)).loc [a]).obj 0) := by
    letI : Module.Flat C Ndehom := hdehom
    exact Module.Flat.of_linearEquiv
      (homogeneousMatrixCokerLocZeroEquiv H hH a).symm
  exact isFlat_loc_singleton_of_flat_zero
    (coker (homogeneousMatrixHom H hH)) a hzero

end Total

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
