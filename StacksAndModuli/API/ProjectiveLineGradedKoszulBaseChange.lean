module

public import StacksAndModuli.API.ProjectiveLineGradedKoszul
public import StacksAndModuli.API.FiniteProjectiveCokernelFiberComparison
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Naturality and base change of the projective-line Koszul recurrence

The two-step Koszul recurrence of a graded module on projective one-space is natural in
graded morphisms and commutes with arbitrary coefficient change.  Scalar extension also
commutes canonically with a finite power: a comparison on one component induces a comparison
on the whole finite power, and is bijective whenever the component comparison is.

The final theorem specializes
`LinearMap.finite_projective_and_fibreComparison_of_twoStep_baseChange` to this recurrence.
It propagates finite projectivity of the graded pieces and bijectivity of a graded fibre
comparison from two adjacent degrees.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace LinearMap

open TensorProduct

variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module A N]

/-- The canonical comparison from scalar extension of a finite power to the corresponding
finite power of a chosen scalar-extension target. -/
noncomputable def finitePiBaseChangeComparison
    (ι : Type v) [Fintype ι]
    (β : (A ⊗[R] M) →ₗ[A] N) :
    (A ⊗[R] (ι → M)) →ₗ[A] (ι → N) := by
  classical
  exact (LinearMap.compLeft β ι).comp
    (TensorProduct.piRight R A A (fun _ : ι ↦ M)).toLinearMap

@[simp]
lemma finitePiBaseChangeComparison_tmul_apply
    (ι : Type v) [Fintype ι]
    (β : (A ⊗[R] M) →ₗ[A] N) (a : A) (x : ι → M) (i : ι) :
    finitePiBaseChangeComparison ι β (a ⊗ₜ[R] x) i = β (a ⊗ₜ[R] x i) := by
  classical
  rfl

theorem finitePiBaseChangeComparison_bijective
    (ι : Type v) [Fintype ι]
    (β : (A ⊗[R] M) →ₗ[A] N) (hβ : Function.Bijective β) :
    Function.Bijective (finitePiBaseChangeComparison ι β) := by
  classical
  have hpow : Function.Bijective (LinearMap.compLeft β ι) := by
    constructor
    · intro x y hxy
      funext i
      exact hβ.1 (congrFun hxy i)
    · intro y
      choose x hx using fun i ↦ hβ.2 (y i)
      refine ⟨x, ?_⟩
      funext i
      exact hx i
  exact hpow.comp (TensorProduct.piRight R A A (fun _ : ι ↦ M)).bijective

theorem finitePiBaseChangeComparison_factor
    (ι : Type v) [Fintype ι]
    (β : (A ⊗[R] M) →ₗ[A] N) :
    finitePiBaseChangeComparison ι β =
      (LinearMap.compLeft β ι).comp
        (finitePiBaseChangeComparison ι
          (LinearMap.id : (A ⊗[R] M) →ₗ[A] (A ⊗[R] M))) := by
  classical
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end LinearMap

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R]

theorem lineKoszulF_naturality
    {M N : GradedModule R 1} (φ : M ⟶ N) (d : ℤ) :
    (LinearMap.compLeft (φ.app (d + 1)).hom (Fin 2)).comp
        (lineKoszulF M d) =
      (lineKoszulF N d).comp (φ.app d).hom := by
  ext x i
  fin_cases i
  · change (φ.app (d + 1)).hom (-((M.mulX 1 d).hom x)) =
      -((N.mulX 1 d).hom ((φ.app d).hom x))
    rw [map_neg]
    congr 1
    have h := congrArg ModuleCat.Hom.hom (φ.comm 1 d)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (LinearMap.congr_fun h x).symm
  · change (φ.app (d + 1)).hom ((M.mulX 0 d).hom x) =
      (N.mulX 0 d).hom ((φ.app d).hom x)
    have h := congrArg ModuleCat.Hom.hom (φ.comm 0 d)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (LinearMap.congr_fun h x).symm

theorem lineKoszulG_naturality
    {M N : GradedModule R 1} (φ : M ⟶ N) (d : ℤ) :
    (φ.app ((d + 1) + 1)).hom.comp (lineKoszulG M d) =
      (lineKoszulG N d).comp
        (LinearMap.compLeft (φ.app (d + 1)).hom (Fin 2)) := by
  apply LinearMap.ext
  intro y
  change (φ.app ((d + 1) + 1)).hom
      ((M.mulX 0 (d + 1)).hom (y 0) +
        (M.mulX 1 (d + 1)).hom (y 1)) =
    (N.mulX 0 (d + 1)).hom ((φ.app (d + 1)).hom (y 0)) +
      (N.mulX 1 (d + 1)).hom ((φ.app (d + 1)).hom (y 1))
  rw [map_add]
  congr 1
  · have h := congrArg ModuleCat.Hom.hom (φ.comm 0 (d + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (LinearMap.congr_fun h (y 0)).symm
  · have h := congrArg ModuleCat.Hom.hom (φ.comm 1 (d + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (LinearMap.congr_fun h (y 1)).symm

theorem lineKoszulF_baseChange
    (M : GradedModule R 1) (A : Type u) [CommRing A] [Algebra R A]
    (d : ℤ) :
    (LinearMap.finitePiBaseChangeComparison
        (R := R) (A := A) (M := (M.obj (d + 1) : Type u))
        (N := (M.baseChange A).obj (d + 1)) (Fin 2)
        (LinearMap.id :
          A ⊗[R] (M.obj (d + 1) : Type u) →ₗ[A]
            A ⊗[R] (M.obj (d + 1) : Type u))).comp
        ((lineKoszulF M d).baseChange A) =
      lineKoszulF (M.baseChange A) d := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change 0 = -(((M.baseChange A).mulX 1 d).hom 0)
        rw [map_zero, neg_zero]
      · change 0 = ((M.baseChange A).mulX 0 d).hom 0
        rw [map_zero]
  | tmul a x =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change a ⊗ₜ[R] (-((M.mulX 1 d).hom x)) =
          -(a ⊗ₜ[R] ((M.mulX 1 d).hom x))
        rw [tmul_neg]
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lineKoszulG_baseChange
    (M : GradedModule R 1) (A : Type u) [CommRing A] [Algebra R A]
    (d : ℤ) :
    (lineKoszulG M d).baseChange A =
      (lineKoszulG (M.baseChange A) d).comp
        (LinearMap.finitePiBaseChangeComparison
          (R := R) (A := A) (M := (M.obj (d + 1) : Type u))
          (N := (M.baseChange A).obj (d + 1)) (Fin 2)
          (LinearMap.id :
            A ⊗[R] (M.obj (d + 1) : Type u) →ₗ[A]
              A ⊗[R] (M.obj (d + 1) : Type u))) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      simp [lineKoszulG, LinearMap.finitePiBaseChangeComparison,
        GradedModule.baseChange, LinearMap.baseChange_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lineKoszulF_baseChange_naturality
    (M : GradedModule R 1) (A : Type u) [CommRing A] [Algebra R A]
    {N : GradedModule A 1} (φ : M.baseChange A ⟶ N) (d : ℤ) :
    (LinearMap.finitePiBaseChangeComparison
        (R := R) (A := A) (M := (M.obj (d + 1) : Type u))
        (N := N.obj (d + 1)) (Fin 2) (φ.app (d + 1)).hom).comp
        ((lineKoszulF M d).baseChange A) =
      (lineKoszulF N d).comp (φ.app d).hom := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change (φ.app (d + 1)).hom
            (a ⊗ₜ[R] (-((M.mulX 1 d).hom x))) =
          -((N.mulX 1 d).hom ((φ.app d).hom (a ⊗ₜ[R] x)))
        rw [tmul_neg, map_neg]
        congr 1
        have h := congrArg ModuleCat.Hom.hom (φ.comm 1 d)
        have hx := LinearMap.congr_fun h (a ⊗ₜ[R] x)
        change (N.mulX 1 d).hom ((φ.app d).hom (a ⊗ₜ[R] x)) =
          (φ.app (d + 1)).hom
            (a ⊗ₜ[R] ((M.mulX 1 d).hom x)) at hx
        exact hx.symm
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change (φ.app (d + 1)).hom
            (a ⊗ₜ[R] ((M.mulX 0 d).hom x)) =
          (N.mulX 0 d).hom ((φ.app d).hom (a ⊗ₜ[R] x))
        have h := congrArg ModuleCat.Hom.hom (φ.comm 0 d)
        have hx := LinearMap.congr_fun h (a ⊗ₜ[R] x)
        change (N.mulX 0 d).hom ((φ.app d).hom (a ⊗ₜ[R] x)) =
          (φ.app (d + 1)).hom
            (a ⊗ₜ[R] ((M.mulX 0 d).hom x)) at hx
        exact hx.symm
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lineKoszulG_baseChange_naturality
    (M : GradedModule R 1) (A : Type u) [CommRing A] [Algebra R A]
    {N : GradedModule A 1} (φ : M.baseChange A ⟶ N) (d : ℤ) :
    (φ.app ((d + 1) + 1)).hom.comp
        ((lineKoszulG M d).baseChange A) =
      (lineKoszulG N d).comp
        (LinearMap.finitePiBaseChangeComparison
          (R := R) (A := A) (M := (M.obj (d + 1) : Type u))
          (N := N.obj (d + 1)) (Fin 2) (φ.app (d + 1)).hom) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y =>
      have h0 := congrArg ModuleCat.Hom.hom (φ.comm 0 (d + 1))
      have h0' := LinearMap.congr_fun h0 (a ⊗ₜ[R] y 0)
      have h1 := congrArg ModuleCat.Hom.hom (φ.comm 1 (d + 1))
      have h1' := LinearMap.congr_fun h1 (a ⊗ₜ[R] y 1)
      change (φ.app ((d + 1) + 1)).hom
          (a ⊗ₜ[R] ((M.mulX 0 (d + 1)).hom (y 0) +
            (M.mulX 1 (d + 1)).hom (y 1))) =
        (N.mulX 0 (d + 1)).hom ((φ.app (d + 1)).hom (a ⊗ₜ[R] y 0)) +
          (N.mulX 1 (d + 1)).hom ((φ.app (d + 1)).hom (a ⊗ₜ[R] y 1))
      rw [tmul_add, map_add]
      exact congrArg₂ (fun x y ↦ x + y)
        (by
          change (N.mulX 0 (d + 1)).hom
              ((φ.app (d + 1)).hom (a ⊗ₜ[R] y 0)) =
            (φ.app ((d + 1) + 1)).hom
              (a ⊗ₜ[R] ((M.mulX 0 (d + 1)).hom (y 0))) at h0'
          exact h0'.symm)
        (by
          change (N.mulX 1 (d + 1)).hom
              ((φ.app (d + 1)).hom (a ⊗ₜ[R] y 1)) =
            (φ.app ((d + 1) + 1)).hom
              (a ⊗ₜ[R] ((M.mulX 1 (d + 1)).hom (y 1))) at h1'
          exact h1'.symm)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The degree obtained by starting at `d` and taking `t` successive degree-one steps. -/
def lineKoszulDegree (d : ℤ) : ℕ → ℤ
  | 0 => d
  | t + 1 => lineKoszulDegree d t + 1

@[simp]
theorem lineKoszulDegree_eq_add (d : ℤ) (t : ℕ) :
    lineKoszulDegree d t = d + (t : ℤ) := by
  induction t with
  | zero => simp [lineKoszulDegree]
  | succ t ht =>
      simp only [lineKoszulDegree, ht, Nat.cast_add, Nat.cast_one]
      ring

/-- The finite-projective two-step induction specialized to the projective-line Koszul
recurrence and a family of graded base-change comparison maps. -/
theorem finite_projective_and_fibreComparison_of_lineKoszul_baseChange
    (M : GradedModule R 1) (d : ℤ)
    (hex : ∀ t, Function.Exact
      (lineKoszulF M (lineKoszulDegree d t))
      (lineKoszulG M (lineKoszulDegree d t)))
    (hg : ∀ t, Function.Surjective
      (lineKoszulG M (lineKoszulDegree d t)))
    (N : ∀ (I : Ideal R) [I.IsMaximal],
      GradedModule I.ResidueField 1)
    (φ : ∀ (I : Ideal R) [I.IsMaximal],
      M.baseChange I.ResidueField ⟶ N I)
    (hexN : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Function.Exact
        (lineKoszulF (N I) (lineKoszulDegree d t))
        (lineKoszulG (N I) (lineKoszulDegree d t)))
    (hgN : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Function.Surjective
        (lineKoszulG (N I) (lineKoszulDegree d t)))
    (hinjN : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Function.Injective
        (lineKoszulF (N I) (lineKoszulDegree d t)))
    (hfin0 : Module.Finite R (M.obj d))
    (hproj0 : Module.Projective R (M.obj d))
    (hfin1 : Module.Finite R (M.obj (d + 1)))
    (hproj1 : Module.Projective R (M.obj (d + 1)))
    (hφ0 : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Bijective ((φ I).app d).hom)
    (hφ1 : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Bijective ((φ I).app (d + 1)).hom) :
    ∀ t,
      (Module.Finite R (M.obj (lineKoszulDegree d t)) ∧
        Module.Projective R (M.obj (lineKoszulDegree d t))) ∧
      ∀ (I : Ideal R) [I.IsMaximal],
        Function.Bijective ((φ I).app (lineKoszulDegree d t)).hom := by
  apply LinearMap.finite_projective_and_fibreComparison_of_twoStep_baseChange
    (fun t ↦ M.obj (lineKoszulDegree d t))
    (fun t ↦ lineKoszulF M (lineKoszulDegree d t))
    (fun t ↦ lineKoszulG M (lineKoszulDegree d t))
    hex hg
    (fun I _ t ↦ (N I).obj (lineKoszulDegree d t))
    (fun I _ t ↦ lineKoszulF (N I) (lineKoszulDegree d t))
    (fun I _ t ↦ lineKoszulG (N I) (lineKoszulDegree d t))
    hexN hgN hinjN
    (fun I _ t ↦ ((φ I).app (lineKoszulDegree d t)).hom)
    (fun I _ t ↦ LinearMap.finitePiBaseChangeComparison
      (R := R) (A := I.ResidueField)
      (M := (M.obj (lineKoszulDegree d t) : Type u))
      (N := (N I).obj (lineKoszulDegree d t))
      (Fin 2) ((φ I).app (lineKoszulDegree d t)).hom)
    (fun I _ t h ↦
      LinearMap.finitePiBaseChangeComparison_bijective (Fin 2)
        ((φ I).app (lineKoszulDegree d t)).hom h)
    (fun I _ t ↦ lineKoszulF_baseChange_naturality
      M I.ResidueField (φ I) (lineKoszulDegree d t))
    (fun I _ t ↦ lineKoszulG_baseChange_naturality
      M I.ResidueField (φ I) (lineKoszulDegree d t))
    hfin0 hproj0 hfin1 hproj1 hφ0 hφ1

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
