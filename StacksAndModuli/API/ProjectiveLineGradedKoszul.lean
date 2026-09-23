module

public import StacksAndModuli.API.ProjectiveLineGradedFlatnessPersistence

/-!
# The localized Koszul recurrence on projective one-space

For a graded module over `R[x₀,x₁]`, the usual signed diagonal and addition maps form
the recurrence `M_d → M_(d+1)² → M_(d+2)`.  After localizing at any nonempty list of
variables, one of `x₀,x₁` is invertible, so this recurrence is short exact.

This is the local algebraic input for propagating flatness of projective-line families from
two adjacent pushforwards.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R]

def lineKoszulF (M : GradedModule R 1) (d : ℤ) :
    M.obj d →ₗ[R] (Fin 2 → M.obj (d + 1)) where
  toFun x i := Fin.cases (-((M.mulX 1 d).hom x))
    (fun _ ↦ (M.mulX 0 d).hom x) i
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [add_comm]
    · simp
  map_smul' a x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp

def lineKoszulG (M : GradedModule R 1) (d : ℤ) :
    (Fin 2 → M.obj (d + 1)) →ₗ[R] M.obj ((d + 1) + 1) :=
  (M.mulX 0 (d + 1)).hom.comp
      (LinearMap.proj 0 : (Fin 2 → M.obj (d + 1)) →ₗ[R] M.obj (d + 1)) +
    (M.mulX 1 (d + 1)).hom.comp
      (LinearMap.proj 1 : (Fin 2 → M.obj (d + 1)) →ₗ[R] M.obj (d + 1))

theorem lineKoszulG_comp_lineKoszulF (M : GradedModule R 1) (d : ℤ) :
    (lineKoszulG M d).comp (lineKoszulF M d) = 0 := by
  ext x
  change (M.mulX 0 (d + 1)).hom (-((M.mulX 1 d).hom x)) +
    (M.mulX 1 (d + 1)).hom ((M.mulX 0 d).hom x) = 0
  rw [map_neg]
  have h := congrArg ModuleCat.Hom.hom (M.mulX_comm 1 0 d)
  simp only [ModuleCat.hom_comp] at h
  have hx := LinearMap.congr_fun h x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
  rw [hx]
  exact neg_add_cancel _

theorem lineKoszul_exact_of_mulX_zero_isIso
    (M : GradedModule R 1) (d : ℤ)
    [IsIso (M.mulX 0 d)] [IsIso (M.mulX 0 (d + 1))] :
    Function.Exact (lineKoszulF M d) (lineKoszulG M d) := by
  intro y
  constructor
  · intro hy
    change (M.mulX 0 (d + 1)).hom (y 0) +
      (M.mulX 1 (d + 1)).hom (y 1) = 0 at hy
    let x : M.obj d := (asIso (M.mulX 0 d)).inv.hom (y 1)
    have hx0 : (M.mulX 0 d).hom x = y 1 := by
      exact (asIso (M.mulX 0 d)).inv_hom_id_apply (y 1)
    have hcomm : (M.mulX 0 (d + 1)).hom ((M.mulX 1 d).hom x) =
        (M.mulX 1 (d + 1)).hom ((M.mulX 0 d).hom x) := by
      have h := congrArg ModuleCat.Hom.hom (M.mulX_comm 1 0 d)
      simp only [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h x
    have hyrel : (M.mulX 0 (d + 1)).hom (y 0) =
        -((M.mulX 1 (d + 1)).hom (y 1)) :=
      eq_neg_of_add_eq_zero_left hy
    refine ⟨x, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change -((M.mulX 1 d).hom x) = y 0
      apply (ModuleCat.mono_iff_injective (M.mulX 0 (d + 1))).mp inferInstance
      calc
        (M.mulX 0 (d + 1)).hom (-((M.mulX 1 d).hom x)) =
            -((M.mulX 0 (d + 1)).hom ((M.mulX 1 d).hom x)) := by rw [map_neg]
        _ = -((M.mulX 1 (d + 1)).hom ((M.mulX 0 d).hom x)) :=
          congrArg Neg.neg hcomm
        _ = -((M.mulX 1 (d + 1)).hom (y 1)) := by rw [hx0]
        _ = (M.mulX 0 (d + 1)).hom (y 0) := hyrel.symm
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact hx0
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (lineKoszulG_comp_lineKoszulF M d) x

theorem lineKoszul_exact_of_mulX_one_isIso
    (M : GradedModule R 1) (d : ℤ)
    [IsIso (M.mulX 1 d)] [IsIso (M.mulX 1 (d + 1))] :
    Function.Exact (lineKoszulF M d) (lineKoszulG M d) := by
  intro y
  constructor
  · intro hy
    change (M.mulX 0 (d + 1)).hom (y 0) +
      (M.mulX 1 (d + 1)).hom (y 1) = 0 at hy
    let x : M.obj d := (asIso (M.mulX 1 d)).inv.hom (-y 0)
    have hx1 : (M.mulX 1 d).hom x = -y 0 := by
      exact (asIso (M.mulX 1 d)).inv_hom_id_apply (-y 0)
    have hcomm : (M.mulX 1 (d + 1)).hom ((M.mulX 0 d).hom x) =
        (M.mulX 0 (d + 1)).hom ((M.mulX 1 d).hom x) := by
      have h := congrArg ModuleCat.Hom.hom (M.mulX_comm 0 1 d)
      simp only [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h x
    have hyrel : (M.mulX 0 (d + 1)).hom (y 0) =
        -((M.mulX 1 (d + 1)).hom (y 1)) :=
      eq_neg_of_add_eq_zero_left hy
    refine ⟨x, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change -((M.mulX 1 d).hom x) = y 0
      rw [hx1, neg_neg]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (M.mulX 0 d).hom x = y 1
      apply (ModuleCat.mono_iff_injective (M.mulX 1 (d + 1))).mp inferInstance
      calc
        (M.mulX 1 (d + 1)).hom ((M.mulX 0 d).hom x) =
            (M.mulX 0 (d + 1)).hom ((M.mulX 1 d).hom x) := hcomm
        _ = (M.mulX 0 (d + 1)).hom (-y 0) := by rw [hx1]
        _ = -((M.mulX 0 (d + 1)).hom (y 0)) := by rw [map_neg]
        _ = (M.mulX 1 (d + 1)).hom (y 1) := by rw [hyrel, neg_neg]
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (lineKoszulG_comp_lineKoszulF M d) x

theorem lineKoszulF_injective_of_mulX_zero_isIso
    (M : GradedModule R 1) (d : ℤ) [IsIso (M.mulX 0 d)] :
    Function.Injective (lineKoszulF M d) := by
  intro x y hxy
  have h := congrFun hxy 1
  change (M.mulX 0 d).hom x = (M.mulX 0 d).hom y at h
  exact (ModuleCat.mono_iff_injective (M.mulX 0 d)).mp inferInstance h

theorem lineKoszulF_injective_of_mulX_one_isIso
    (M : GradedModule R 1) (d : ℤ) [IsIso (M.mulX 1 d)] :
    Function.Injective (lineKoszulF M d) := by
  intro x y hxy
  have h := congrFun hxy 0
  change -((M.mulX 1 d).hom x) = -((M.mulX 1 d).hom y) at h
  have h' : (M.mulX 1 d).hom x = (M.mulX 1 d).hom y := neg_injective h
  exact (ModuleCat.mono_iff_injective (M.mulX 1 d)).mp inferInstance h'

theorem lineKoszulG_surjective_of_mulX_zero_isIso
    (M : GradedModule R 1) (d : ℤ) [IsIso (M.mulX 0 (d + 1))] :
    Function.Surjective (lineKoszulG M d) := by
  intro z
  let y : Fin 2 → M.obj (d + 1) := fun i ↦
    Fin.cases ((asIso (M.mulX 0 (d + 1))).inv.hom z) (fun _ ↦ 0) i
  refine ⟨y, ?_⟩
  change (M.mulX 0 (d + 1)).hom ((asIso (M.mulX 0 (d + 1))).inv.hom z) +
      (M.mulX 1 (d + 1)).hom 0 = z
  rw [map_zero, add_zero]
  exact (asIso (M.mulX 0 (d + 1))).inv_hom_id_apply z

theorem lineKoszulG_surjective_of_mulX_one_isIso
    (M : GradedModule R 1) (d : ℤ) [IsIso (M.mulX 1 (d + 1))] :
    Function.Surjective (lineKoszulG M d) := by
  intro z
  let y : Fin 2 → M.obj (d + 1) := fun i ↦
    Fin.cases 0 (fun _ ↦ (asIso (M.mulX 1 (d + 1))).inv.hom z) i
  refine ⟨y, ?_⟩
  change (M.mulX 0 (d + 1)).hom 0 +
      (M.mulX 1 (d + 1)).hom ((asIso (M.mulX 1 (d + 1))).inv.hom z) = z
  rw [map_zero, zero_add]
  exact (asIso (M.mulX 1 (d + 1))).inv_hom_id_apply z

theorem lineKoszul_shortExact_loc (M : GradedModule R 1)
    (l : List (Fin 2)) (hl : l ≠ []) (d : ℤ) :
    Function.Injective (lineKoszulF (M.loc l) d) ∧
      Function.Exact (lineKoszulF (M.loc l) d) (lineKoszulG (M.loc l) d) ∧
      Function.Surjective (lineKoszulG (M.loc l) d) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons i t =>
  have hi : i ∈ i :: t := by simp
  fin_cases i
  · letI := M.loc_mulX_isIso (0 :: t) 0 hi d
    letI := M.loc_mulX_isIso (0 :: t) 0 hi (d + 1)
    exact ⟨lineKoszulF_injective_of_mulX_zero_isIso (M.loc (0 :: t)) d,
      lineKoszul_exact_of_mulX_zero_isIso (M.loc (0 :: t)) d,
      lineKoszulG_surjective_of_mulX_zero_isIso (M.loc (0 :: t)) d⟩
  · letI := M.loc_mulX_isIso (1 :: t) 1 hi d
    letI := M.loc_mulX_isIso (1 :: t) 1 hi (d + 1)
    exact ⟨lineKoszulF_injective_of_mulX_one_isIso (M.loc (1 :: t)) d,
      lineKoszul_exact_of_mulX_one_isIso (M.loc (1 :: t)) d,
      lineKoszulG_surjective_of_mulX_one_isIso (M.loc (1 :: t)) d⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
