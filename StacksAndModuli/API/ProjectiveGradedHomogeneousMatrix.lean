module

public import StacksAndModuli.API.ProjectiveGradedCokerBaseChange
public import StacksAndModuli.API.ProjectiveGradedTwistedFreeTotal
public import StacksAndModuli.API.ProjectiveGradedTotalMap

/-!
# Homogeneous polynomial matrices as maps of shifted graded-free modules

A matrix whose entries are homogeneous of one degree defines a degree-zero morphism from
the corresponding negatively shifted graded-free module to an unshifted graded-free module.
This file constructs that morphism directly and proves that, after forgetting the grading
through the standard total-module bases, its total map is the ordinary matrix linear map.

This is the concrete matrix-to-grading boundary needed when a descended polynomial
presentation is upgraded to a homogeneous presentation.  Coefficient base change carries
the resulting morphism to the morphism of the coefficientwise mapped matrix, under the
standard shifted-free comparisons; consequently their degreewise cokernels agree.

Main declarations:

* `GradedModule.Total.homogeneousMatrixHom`;
* `GradedModule.Total.homogeneousMatrixHom_totalRelation`;
* `GradedModule.Total.homogeneousMatrixCokerBaseChangeIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open MvPolynomial

variable {R : Type u} [CommRing R] {n m r D : ℕ}

/-- Multiplication by a variable on a shifted graded-free module is ordinary polynomial
multiplication in every coordinate. -/
lemma shiftedFree_mulX_val (s : ℤ) (a : Fin (n + 1)) (d : ℤ)
    (x : (shiftedFree R n r s).obj d) (i : Fin r) :
    (((shiftedFree R n r s).mulX a d).hom x i).1 =
      MvPolynomial.X a * (x i).1 := by
  exact structureModule_mulX'_val a (d + s) (d + 1 + s) (by ring) (x i)

/-- The degreewise function defined by multiplying a vector by a homogeneous polynomial
matrix. -/
def homogeneousMatrixFun
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) (d : ℤ)
    (x : (shiftedFree R n m (-(D : ℤ))).obj d) :
    (shiftedFree R n r 0).obj d :=
  fun i ↦ ⟨∑ j, G i j * (x j).1, by
    apply Submodule.sum_mem
    intro j _
    simpa only [add_zero] using mul_mem_polySubmodule (hG i j) (x j).2⟩

/-- The underlying polynomial of one coordinate of `homogeneousMatrixFun`. -/
lemma homogeneousMatrixFun_val
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) (d : ℤ)
    (x : (shiftedFree R n m (-(D : ℤ))).obj d) (i : Fin r) :
    (homogeneousMatrixFun G hG d x i).1 = ∑ j, G i j * (x j).1 := rfl

/-- The coefficient-linear degree-`d` map defined by a homogeneous polynomial matrix. -/
def homogeneousMatrixApp
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) (d : ℤ) :
    (shiftedFree R n m (-(D : ℤ))).obj d →ₗ[R]
      (shiftedFree R n r 0).obj d where
  toFun := homogeneousMatrixFun G hG d
  map_add' x y := by
    funext i
    apply Subtype.ext
    rw [homogeneousMatrixFun_val]
    have hout :
        ((homogeneousMatrixFun G hG d x + homogeneousMatrixFun G hG d y) i).1 =
          (homogeneousMatrixFun G hG d x i).1 +
            (homogeneousMatrixFun G hG d y i).1 := rfl
    rw [hout, homogeneousMatrixFun_val, homogeneousMatrixFun_val]
    have hxy (j : Fin m) : ((x + y) j).1 = (x j).1 + (y j).1 := rfl
    simp_rw [hxy, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    funext i
    apply Subtype.ext
    rw [homogeneousMatrixFun_val]
    have hout : (((RingHom.id R) c • homogeneousMatrixFun G hG d x) i).1 =
        (RingHom.id R) c • (homogeneousMatrixFun G hG d x i).1 := rfl
    rw [hout, homogeneousMatrixFun_val]
    have hcx (j : Fin m) : ((c • x) j).1 = c • (x j).1 := rfl
    simp_rw [hcx]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingHom.id_apply, Algebra.smul_def]
    change G i j * (algebraMap R (MvPolynomial (Fin (n + 1)) R) c * (x j).1) =
      algebraMap R (MvPolynomial (Fin (n + 1)) R) c * (G i j * (x j).1)
    ring

/-- Evaluation of the degreewise homogeneous matrix map. -/
lemma homogeneousMatrixApp_apply
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) (d : ℤ)
    (x : (shiftedFree R n m (-(D : ℤ))).obj d) (i : Fin r) :
    ((homogeneousMatrixApp G hG d) x i).1 = ∑ j, G i j * (x j).1 := by
  exact homogeneousMatrixFun_val G hG d x i

/-- A matrix with entries homogeneous of degree `D` defines a graded morphism from the
free module shifted by `-D` to the unshifted free module. -/
def homogeneousMatrixHom
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) :
    shiftedFree R n m (-(D : ℤ)) ⟶ shiftedFree R n r 0 where
  app d := ModuleCat.ofHom (homogeneousMatrixApp G hG d)
  comm a d := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    apply Subtype.ext
    have ht := shiftedFree_mulX_val (R := R) (n := n) (r := r)
      0 a d ((homogeneousMatrixApp G hG d) x) i
    have hs (j : Fin m) := shiftedFree_mulX_val (R := R) (n := n) (r := m)
      (-(D : ℤ)) a d x j
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at ht hs ⊢
    rw [ht, homogeneousMatrixApp_apply, homogeneousMatrixApp_apply]
    change MvPolynomial.X a * (∑ j, G i j * (x j).1) =
      ∑ j, G i j * ((((shiftedFree R n m (-(D : ℤ))).mulX a d).hom x j).1)
    simp_rw [hs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Evaluation of the graded morphism associated to a homogeneous matrix. -/
lemma homogeneousMatrixHom_app_apply
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) (d : ℤ)
    (x : (shiftedFree R n m (-(D : ℤ))).obj d) (i : Fin r) :
    (((homogeneousMatrixHom G hG).app d).hom x i).1 =
      ∑ j, G i j * (x j).1 :=
  homogeneousMatrixApp_apply G hG d x i

/-- In the standard total-module bases, the totalized homogeneous matrix morphism is the
ordinary linear map associated to the same matrix. -/
theorem homogeneousMatrixHom_totalRelation
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) :
    (shiftedFreeLinearEquiv (R := R) (n := n) (r := r) 0).symm.toLinearMap.comp
        (GradedModule.Total.map (homogeneousMatrixHom G hG)) =
      (Matrix.toLin' G).comp
        (shiftedFreeLinearEquiv (R := R) (n := n) (r := m)
          (-(D : ℤ))).symm.toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of d x =>
      rw [show DirectSum.of
        (fun e ↦ ((shiftedFree R n m (-(D : ℤ))).obj e : Type u)) d x =
          tof (shiftedFree R n m (-(D : ℤ))) d x from rfl]
      simp only [LinearMap.comp_apply, map_tof]
      funext i
      have hl := shiftedFreeLinearEquiv_symm_tof
        (R := R) (n := n) (r := r) 0 d
        (((homogeneousMatrixHom G hG).app d).hom x)
      have hr := shiftedFreeLinearEquiv_symm_tof
        (R := R) (n := n) (r := m) (-(D : ℤ)) d x
      change ((shiftedFreeLinearEquiv (R := R) (n := n) (r := r) 0).symm
          (tof (shiftedFree R n r 0) d
            (((homogeneousMatrixHom G hG).app d).hom x))) i =
        Matrix.toLin' G
          ((shiftedFreeLinearEquiv (R := R) (n := n) (r := m)
            (-(D : ℤ))).symm
              (tof (shiftedFree R n m (-(D : ℤ))) d x)) i
      rw [congrFun hl i, hr, Matrix.toLin'_apply, Matrix.mulVec]
      exact homogeneousMatrixApp_apply G hG d x i

/-! ## Coefficient base change -/

/-- Applying a coefficient map preserves membership in a homogeneous polynomial piece. -/
lemma map_mem_polySubmodule_of_mem
    {A : Type u} [CommRing A] [Algebra R A]
    {p : MvPolynomial (Fin (n + 1)) R}
    (hp : p ∈ polySubmodule R n D) :
    MvPolynomial.map (algebraMap R A) p ∈ polySubmodule A n D := by
  rw [polySubmodule_of_nonneg (k := R) (n := n) (by omega),
    MvPolynomial.mem_homogeneousSubmodule] at hp
  rw [polySubmodule_of_nonneg (k := A) (n := n) (by omega),
    MvPolynomial.mem_homogeneousSubmodule]
  exact hp.map (algebraMap R A)

/-- The coefficientwise image of a homogeneous matrix is homogeneous of the same degree. -/
theorem homogeneousMatrix_map_mem_polySubmodule
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) :
    ∀ i j, (G.map (MvPolynomial.map (algebraMap R A))) i j ∈
      polySubmodule A n D :=
  fun i j ↦ map_mem_polySubmodule_of_mem (A := A) (hG i j)

/-- On a pure tensor, the standard shifted-free base-change isomorphism applies the
coefficient map to every polynomial coordinate and scales by the tensor coefficient. -/
lemma freeBaseChangeIso_hom_app_tmul_apply_val
    {A : Type u} [CommRing A] [Algebra R A]
    (a d : ℤ) (c : A) (x : (shiftedFree R n r a).obj d) (i : Fin r) :
    ((((freeBaseChangeIso (R := R) (A := A) (n := n) r a).hom.app d).hom
      (c ⊗ₜ[R] x)) i).1 =
      c • MvPolynomial.map (algebraMap R A) (x i).1 := by
  rw [freeBaseChangeIso]
  simp only [Iso.trans_hom, comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    powBaseChangeIso, isoOfAppEquiv, powMapIso, twistBaseChangeIso, twistMapIso,
    structureModuleBaseChangeIso, structureModuleBaseChangeHom, powMap_app,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
  exact polySubmoduleBaseChangeEquiv_tmul_val R A n c (x i)

/-- Under the standard shifted-free base-change isomorphisms, base change of a homogeneous
matrix morphism is the morphism associated to the coefficientwise mapped matrix. -/
theorem baseChangeMap_homogeneousMatrixHom
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) :
    baseChangeMap (homogeneousMatrixHom G hG) A ≫
        (freeBaseChangeIso (R := R) (A := A) (n := n) r 0).hom =
      (freeBaseChangeIso (R := R) (A := A) (n := n) m (-(D : ℤ))).hom ≫
        homogeneousMatrixHom (G.map (MvPolynomial.map (algebraMap R A)))
          (homogeneousMatrix_map_mem_polySubmodule (A := A) G hG) := by
  apply hom_ext
  intro d
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
      simp only [comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
        baseChangeMap_app_tmul]
      funext i
      apply Subtype.ext
      rw [freeBaseChangeIso_hom_app_tmul_apply_val,
        homogeneousMatrixHom_app_apply, homogeneousMatrixHom_app_apply]
      simp_rw [freeBaseChangeIso_hom_app_tmul_apply_val]
      simp only [Matrix.map_apply, map_sum, map_mul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Algebra.smul_def]
      ring

/-- Coefficient base change of the degreewise cokernel of a homogeneous matrix morphism is
the cokernel of the coefficientwise mapped homogeneous matrix morphism. -/
noncomputable def homogeneousMatrixCokerBaseChangeIso
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) R))
    (hG : ∀ i j, G i j ∈ polySubmodule R n D) :
    (GradedModule.coker (homogeneousMatrixHom G hG)).baseChange A ≅
      GradedModule.coker (homogeneousMatrixHom
        (G.map (MvPolynomial.map (algebraMap R A)))
        (homogeneousMatrix_map_mem_polySubmodule (A := A) G hG)) :=
  GradedModule.cokerBaseChangeIso (A := A) (homogeneousMatrixHom G hG) ≪≫
    GradedModule.cokerMapIso
      (baseChangeMap (homogeneousMatrixHom G hG) A)
      (homogeneousMatrixHom
        (G.map (MvPolynomial.map (algebraMap R A)))
        (homogeneousMatrix_map_mem_polySubmodule (A := A) G hG))
      (freeBaseChangeIso (R := R) (A := A) (n := n) m (-(D : ℤ)))
      (freeBaseChangeIso (R := R) (A := A) (n := n) r 0)
      (baseChangeMap_homogeneousMatrixHom (A := A) G hG)

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end

end
