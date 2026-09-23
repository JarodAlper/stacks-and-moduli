module

public import StacksAndModuli.API.ProjectiveGradedTotalMap
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite products of graded modules and their total modules

A finite product of diagrammatic graded modules is defined degreewise.  Totalization commutes
with this finite product: a finitely supported family of degreewise tuples is equivalent to a
tuple of finitely supported homogeneous families.  The equivalence is polynomial-linear and
therefore transports finite presentation componentwise.

This supplies finite families of differently shifted free summands for the graded
finite-presentation theorem corresponding to Stacks Project tag 053C.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The degreewise product of a family of graded modules. -/
def pi {ι : Type u} (M : ι → GradedModule R n) : GradedModule R n where
  obj d := ModuleCat.of R (∀ i, (M i).obj d)
  mulX j d := ModuleCat.ofHom
    (LinearMap.pi fun i => ((M i).mulX j d).hom.comp (LinearMap.proj i))
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun a => ?_)
    simpa using congrArg (fun f : (M a).obj d ⟶ (M a).obj (d + 1 + 1) => f.hom (x a))
      ((M a).mulX_comm i j d)

@[simp]
lemma pi_obj {ι : Type u} (M : ι → GradedModule R n) (d : ℤ) :
    (pi M).obj d = ModuleCat.of R (∀ i, (M i).obj d) := rfl

/-- Projection from a degreewise product. -/
def piProj {ι : Type u} (M : ι → GradedModule R n) (i : ι) : pi M ⟶ M i where
  app _d := ModuleCat.ofHom (LinearMap.proj i)
  comm _ _ := rfl

@[simp]
lemma piProj_app_apply {ι : Type u} (M : ι → GradedModule R n) (i : ι)
    (_d : ℤ) (x : (pi M).obj _d) : ((piProj M i).app _d).hom x = x i := rfl

/-- Inclusion of one factor into a degreewise product. -/
noncomputable def piIncl {ι : Type u} (M : ι → GradedModule R n) (i : ι) : M i ⟶ pi M := by
  classical
  exact
    { app := fun d => ModuleCat.ofHom (LinearMap.single R (fun i => (M i).obj d) i)
      comm := fun j d => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun a => ?_)
        by_cases h : i = a
        · subst a
          simp [pi]
        · simp [pi, h] }

@[simp]
lemma piIncl_app_apply_same {ι : Type u} (M : ι → GradedModule R n) (i : ι)
    (d : ℤ) (x : (M i).obj d) : ((piIncl M i).app d).hom x i = x := by
  classical
  simp [piIncl]

@[simp]
lemma piIncl_app_apply_ne {ι : Type u} (M : ι → GradedModule R n) (i j : ι)
    (h : i ≠ j) (d : ℤ) (x : (M i).obj d) : ((piIncl M i).app d).hom x j = 0 := by
  classical
  simp [piIncl, h]

/-- The finite sum of maps out of the factors of a degreewise product. -/
noncomputable def piDesc {ι : Type u} [Fintype ι]
    (M : ι → GradedModule R n) {N : GradedModule R n}
    (f : ∀ i, M i ⟶ N) : pi M ⟶ N := by
  classical
  exact
    { app := fun d => ∑ i, (piProj M i).app d ≫ (f i).app d
      comm := fun j d => by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Category.assoc, (f i).comm, ← Category.assoc,
          (piProj M i).comm, Category.assoc] }

set_option linter.flexible false in
lemma piDesc_app_apply {ι : Type u} [Fintype ι]
    (M : ι → GradedModule R n) {N : GradedModule R n}
    (f : ∀ i, M i ⟶ N) (d : ℤ) (x : (pi M).obj d) :
    ((piDesc M f).app d).hom x = ∑ i, ((f i).app d).hom (x i) := by
  classical
  simp [piDesc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

@[simp]
lemma piDesc_piIncl_app {ι : Type u} [Fintype ι]
    (M : ι → GradedModule R n) {N : GradedModule R n}
    (f : ∀ i, M i ⟶ N) (i : ι) (d : ℤ) (x : (M i).obj d) :
    ((piDesc M f).app d).hom (((piIncl M i).app d).hom x) = ((f i).app d).hom x := by
  classical
  rw [piDesc_app_apply, Finset.sum_eq_single i]
  · rw [piIncl_app_apply_same]
  · intro j _ hji
    rw [piIncl_app_apply_ne M i j (Ne.symm hji), map_zero]
  · simp

/-- A finite degreewise product of finitely generated graded modules is finitely generated. -/
lemma IsFG.pi {ι : Type u} [Finite ι] (M : ι → GradedModule R n)
    (hM : ∀ i, IsFG (M i)) : IsFG (pi M) := by
  classical
  letI := Fintype.ofFinite ι
  choose lo hlo using fun i => (hM i).2.1
  choose hi hhi using fun i => (hM i).2.2
  let B₀ : ℤ := ∑ i, |lo i|
  let B₁ : ℤ := ∑ i, |hi i|
  have hlo_bound (i : ι) : -B₀ ≤ lo i := by
    have habs : |lo i| ≤ B₀ := by
      exact Finset.single_le_sum (fun j _ => abs_nonneg (lo j)) (Finset.mem_univ i)
    exact (neg_le_neg habs).trans (neg_abs_le (lo i))
  have hhi_bound (i : ι) : hi i ≤ B₁ := by
    have habs : |hi i| ≤ B₁ := by
      exact Finset.single_le_sum (fun j _ => abs_nonneg (hi j)) (Finset.mem_univ i)
    exact (le_abs_self (hi i)).trans habs
  refine ⟨fun d => ?_, ⟨-B₀, fun d hd => ?_⟩, ⟨B₁, fun d hd => ?_⟩⟩
  · letI : ∀ i, Module.Finite R ((M i).obj d) := fun i => (hM i).1 d
    exact inferInstanceAs (Module.Finite R (∀ i, (M i).obj d))
  · letI : ∀ i, Subsingleton ((M i).obj d) :=
      fun i => hlo i d (lt_of_lt_of_le hd (hlo_bound i))
    exact inferInstanceAs (Subsingleton (∀ i, (M i).obj d))
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : ∑ i, ((piIncl M i).app (d + 1)).hom (x i) = x := by
      funext j
      change (∑ i, Pi.single i (x i)) j = x j
      exact congrFun (Finset.univ_sum_single x) j
    rw [← hx]
    apply Submodule.sum_mem
    intro i _
    apply mulSpan_map_le (piIncl M i) d (d + 1)
    refine ⟨x i, ?_, rfl⟩
    rw [hhi i d ((hhi_bound i).trans hd)]
    trivial

namespace Total

/-- Totalization maps a degreewise product into the product of the total modules. -/
noncomputable def piTo {ι : Type u} (M : ι → GradedModule R n) :
    Total (pi M) →ₗ[MvPolynomial (Fin (n + 1)) R] (∀ i, Total (M i)) :=
  LinearMap.pi fun i => map (piProj M i)

@[simp]
lemma piTo_apply {ι : Type u} (M : ι → GradedModule R n)
    (x : Total (pi M)) (i : ι) : piTo M x i = map (piProj M i) x := rfl

/-- A finite tuple of total elements maps back by summing the factor inclusions. -/
noncomputable def piFrom {ι : Type u} [Fintype ι] (M : ι → GradedModule R n) :
    (∀ i, Total (M i)) →ₗ[MvPolynomial (Fin (n + 1)) R] Total (pi M) := by
  classical
  exact ∑ i, (map (piIncl M i)).comp (LinearMap.proj i)

lemma piFrom_apply {ι : Type u} [Fintype ι] (M : ι → GradedModule R n)
    (x : ∀ i, Total (M i)) : piFrom M x = ∑ i, map (piIncl M i) (x i) := by
  classical
  simp [piFrom]

@[simp]
lemma map_piProj_piIncl_same {ι : Type u}
    (M : ι → GradedModule R n) (i : ι) (x : Total (M i)) :
    map (piProj M i) (map (piIncl M i) x) = x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of d x =>
      rw [show DirectSum.of (fun e => ((M i).obj e : Type u)) d x = tof (M i) d x from rfl]
      rw [map_tof, map_tof, piProj_app_apply, piIncl_app_apply_same]

lemma map_piProj_piIncl_ne {ι : Type u} (M : ι → GradedModule R n) (i j : ι)
    (h : i ≠ j) (x : Total (M i)) :
    map (piProj M j) (map (piIncl M i) x) = 0 := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | of d x =>
      rw [show DirectSum.of (fun e => ((M i).obj e : Type u)) d x = tof (M i) d x from rfl]
      rw [map_tof, map_tof, piProj_app_apply, piIncl_app_apply_ne M i j h, map_zero]

lemma piTo_piFrom {ι : Type u} [Fintype ι] (M : ι → GradedModule R n)
    (x : ∀ i, Total (M i)) : piTo M (piFrom M x) = x := by
  classical
  funext j
  rw [piTo_apply, piFrom_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · exact map_piProj_piIncl_same M j (x j)
  · intro i _ hij
    exact map_piProj_piIncl_ne M i j hij (x i)
  · simp

lemma piFrom_piTo_tof {ι : Type u} [Fintype ι] (M : ι → GradedModule R n)
    (d : ℤ) (x : (pi M).obj d) :
    piFrom M (piTo M (tof (pi M) d x)) = tof (pi M) d x := by
  classical
  rw [piFrom_apply]
  simp only [piTo_apply, map_tof, piProj_app_apply]
  rw [← map_sum]
  congr 1
  funext j
  change (∑ i, Pi.single i (x i)) j = x j
  exact congrFun (Finset.univ_sum_single x) j

lemma piFrom_piTo {ι : Type u} [Fintype ι] (M : ι → GradedModule R n)
    (x : Total (pi M)) : piFrom M (piTo M x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of d x =>
      rw [show DirectSum.of (fun e => ((pi M).obj e : Type u)) d x = tof (pi M) d x from rfl]
      exact piFrom_piTo_tof M d x

/-- Totalization commutes with finite products of graded modules. -/
noncomputable def piLinearEquiv {ι : Type u} [Fintype ι] (M : ι → GradedModule R n) :
    Total (pi M) ≃ₗ[MvPolynomial (Fin (n + 1)) R] (∀ i, Total (M i)) where
  toFun := piTo M
  invFun := piFrom M
  left_inv := piFrom_piTo M
  right_inv := piTo_piFrom M
  map_add' := (piTo M).map_add
  map_smul' := (piTo M).map_smul

/-- A finite product of graded modules with finitely presented total modules again has a
finitely presented total module. -/
theorem finitePresentation_pi {ι : Type u} [Finite ι]
    (M : ι → GradedModule R n)
    (hM : ∀ i, Module.FinitePresentation
      (MvPolynomial (Fin (n + 1)) R) (Total (M i))) :
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total (pi M)) := by
  letI := Fintype.ofFinite ι
  letI : ∀ i, Module.FinitePresentation
      (MvPolynomial (Fin (n + 1)) R) (Total (M i)) := hM
  letI : Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (∀ i, Total (M i)) := Module.FinitePresentation.pi _
  exact Module.FinitePresentation.of_equiv (piLinearEquiv M).symm

end Total

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
