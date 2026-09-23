module

public import StacksAndModuli.API.ProjectiveGradedModule

/-!
# A hyperplane in `ℙⁿ⁺¹` is a `ℙⁿ`: the graded-module form

Supporting API with no Stacks Project counterpart, developed for §2.3 (Castelnuovo–Mumford
regularity) of *Stacks and Moduli*.

`StacksAndModuli/API/PolynomialHyperplane.lean` provides the graded `k`-algebra map
`k[x₀, …, x_{n+1}] → k[y₀, …, y_n]` cutting out the hyperplane `V(L)` of a linear form
`L = ∑ᵢ cᵢxᵢ` with `c_j` a unit, and identifies its kernel with `(L)`. This file assembles that
into the isomorphism of graded modules

`(𝒪_{ℙⁿ⁺¹}^{⊕r})|_{V(L)} ≅ 𝒪_{ℙⁿ}^{⊕r}`,

which is what lets the inductive step of Mumford's Boundedness of Regularity
(**Theorem 2.3.8**, `thm:boundedness-of-regularity`) apply the inductive hypothesis on `ℙⁿ`.
It discharges the obligation recorded in `StacksAndModuli/API/ProjectiveGradedModule.lean`.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.restrictLPowStructureHom`: the morphism.
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.nonempty_restrictL_pow_structureIso`: it is
  an isomorphism.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k] {n : ℕ}

lemma hyperplaneAlgHom_mem_polySubmodule (c : Fin (n + 2) → k) (j : Fin (n + 2)) {d : ℤ}
    {p : MvPolynomial (Fin (n + 2)) k} (hp : p ∈ polySubmodule k (n + 1) d) :
    hyperplaneAlgHom c j p ∈ polySubmodule k n d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [polySubmodule_of_neg k (n + 1) hd, Submodule.mem_bot] at hp
    subst hp
    rw [map_zero]
    exact Submodule.zero_mem _
  · rw [polySubmodule_of_nonneg k (n + 1) hd] at hp
    rw [polySubmodule_of_nonneg k n hd]
    exact isHomogeneous_hyperplaneAlgHom c j hp

lemma liftAlgHom_mem_polySubmodule (j : Fin (n + 2)) {d : ℤ}
    {p : MvPolynomial (Fin (n + 1)) k} (hp : p ∈ polySubmodule k n d) :
    liftAlgHom j p ∈ polySubmodule k (n + 1) d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [polySubmodule_of_neg k n hd, Submodule.mem_bot] at hp
    subst hp
    rw [map_zero]
    exact Submodule.zero_mem _
  · rw [polySubmodule_of_nonneg k n hd] at hp
    rw [polySubmodule_of_nonneg k (n + 1) hd]
    exact isHomogeneous_liftAlgHom j hp

/-- The substitution, on the degree-`d` graded pieces. -/
noncomputable def hyperplaneLinearMap (c : Fin (n + 2) → k) (j : Fin (n + 2)) (d : ℤ) :
    ↥(polySubmodule k (n + 1) d) →ₗ[k] ↥(polySubmodule k n d) where
  toFun p := ⟨hyperplaneAlgHom c j p.1, hyperplaneAlgHom_mem_polySubmodule c j p.2⟩
  map_add' p q := Subtype.ext (by simp)
  map_smul' a p := Subtype.ext (by simp)

@[simp] lemma hyperplaneLinearMap_val (c : Fin (n + 2) → k) (j : Fin (n + 2)) (d : ℤ)
    (p : ↥(polySubmodule k (n + 1) d)) :
    (hyperplaneLinearMap c j d p).1 = hyperplaneAlgHom c j p.1 := rfl

/-- The substitution on `r` copies of the degree-`d` graded pieces. -/
noncomputable def hyperplanePowLinearMap (c : Fin (n + 2) → k) (j : Fin (n + 2)) (r : ℕ)
    (d : ℤ) : (Fin r → ↥(polySubmodule k (n + 1) d)) →ₗ[k] (Fin r → ↥(polySubmodule k n d)) :=
  LinearMap.pi fun t => (hyperplaneLinearMap c j d).comp (LinearMap.proj t)

@[simp] lemma hyperplanePowLinearMap_apply (c : Fin (n + 2) → k) (j : Fin (n + 2)) (r : ℕ)
    (d : ℤ) (x : Fin r → ↥(polySubmodule k (n + 1) d)) (t : Fin r) :
    hyperplanePowLinearMap c j r d x t = hyperplaneLinearMap c j d (x t) := rfl

lemma range_mulLHom_le_ker (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : c j ≠ 0) (r : ℕ)
    (d : ℤ) :
    LinearMap.range ((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom
      ≤ LinearMap.ker (hyperplanePowLinearMap c j r d) := by
  rintro y ⟨z, rfl⟩
  rw [LinearMap.mem_ker]
  funext t
  refine Subtype.ext ?_
  have hcomp : ((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom z t
      = (((structureModule k (n + 1)).mulL c (d + -1) d (by ring)).hom (z t)) :=
    pow_mulL_apply (structureModule k (n + 1)) r c (d + -1) d (by ring) z t
  have hval : ((hyperplanePowLinearMap c j r d
      (((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom z)) t).1
      = hyperplaneAlgHom c j
        ((((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom z) t).1 := rfl
  have h2 : (((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom z t).1
      = linearForm c * (z t).1 :=
    (congrArg Subtype.val hcomp).trans
      (structureModule_mulL_val c (d + -1) d (by ring) (z t))
  have h3 : hyperplaneAlgHom c j
      ((((((structureModule k (n + 1)).pow r).mulLHom c).app d).hom z) t).1 = 0 := by
    rw [h2, map_mul, hyperplaneAlgHom_linearForm c j hj, zero_mul]
  exact hval.trans h3

/-- The morphism `(𝒪_{ℙⁿ⁺¹}^{⊕r})|_{V(L)} ⟶ 𝒪_{ℙⁿ}^{⊕r}` induced by the substitution. -/
noncomputable def restrictLPowStructureHom (c : Fin (n + 2) → k) (j : Fin (n + 2))
    (hj : c j ≠ 0) (r : ℕ) :
    ((structureModule k (n + 1)).pow r).restrictL c j ⟶ (structureModule k n).pow r where
  app d := ModuleCat.ofHom (Submodule.liftQ _ (hyperplanePowLinearMap c j r d)
    (range_mulLHom_le_ker c j hj r d))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext ?_)
    rintro ⟨x⟩
    funext t
    refine Subtype.ext ?_
    have hLHS : (((((structureModule k n).pow r).mulX i d).hom
        (Submodule.liftQ _ (hyperplanePowLinearMap c j r d)
          (range_mulLHom_le_ker c j hj r d) (Submodule.Quotient.mk x))) t).1
        = MvPolynomial.X i * hyperplaneAlgHom c j (x t).1 := rfl
    have hRHS : ((Submodule.liftQ _ (hyperplanePowLinearMap c j r (d + 1))
          (range_mulLHom_le_ker c j hj r (d + 1))
          (Submodule.Quotient.mk
            ((((structureModule k (n + 1)).pow r).mulX (j.succAbove i) d).hom x))) t).1
        = hyperplaneAlgHom c j (MvPolynomial.X (j.succAbove i) * (x t).1) := rfl
    refine Eq.trans hLHS (Eq.trans ?_ hRHS.symm)
    rw [map_mul, hyperplaneAlgHom_X_succAbove]

lemma bijective_restrictLPowStructureHom_app (c : Fin (n + 2) → k) (j : Fin (n + 2))
    (hj : c j ≠ 0) (r : ℕ) (d : ℤ) :
    Function.Bijective ((restrictLPowStructureHom c j hj r).app d).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x⟩ hx
    have hzero : ∀ t, hyperplaneAlgHom c j (x t).1 = 0 := fun t =>
      congrArg Subtype.val (congrFun hx t)
    rcases lt_or_ge d 0 with hd | hd
    · have hx0 : x = 0 := by
        funext t
        refine Subtype.ext ?_
        have hbot : polySubmodule k (n + 1) d ≤ ⊥ :=
          le_of_eq (polySubmodule_of_neg k (n + 1) hd)
        exact (Submodule.mem_bot k).mp (hbot (x t).2)
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      rw [hx0]
      exact Submodule.zero_mem _
    · have hxh : ∀ t, (x t).1.IsHomogeneous d.toNat := by
        intro t
        have hle : polySubmodule k (n + 1) d
            ≤ MvPolynomial.homogeneousSubmodule (Fin (n + 2)) k d.toNat :=
          le_of_eq (polySubmodule_of_nonneg k (n + 1) hd)
        exact hle (x t).2
      choose h hh1 hh2 hh3 using fun t =>
        exists_isHomogeneous_of_mem_span_of_isHomogeneous (isHomogeneous_linearForm c) (hxh t)
          (mem_span_linearForm_of_hyperplaneAlgHom_eq_zero c j hj (hzero t))
      rcases eq_or_lt_of_le hd with hd0 | hd1
      · have hx0 : x = 0 := by
          funext t
          exact Subtype.ext (hh3 t (by omega))
        refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
        rw [hx0]
        exact Submodule.zero_mem _
      · refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨fun t => ⟨h t, ?_⟩, ?_⟩
        · rw [polySubmodule_of_nonneg k (n + 1) (by omega),
            show (d + -1).toNat = d.toNat - 1 from by omega]
          exact hh1 t
        · funext t
          refine Subtype.ext ?_
          have hcomp := pow_mulL_apply (structureModule k (n + 1)) r c (d + -1) d (by ring)
            (fun t => (⟨h t, by
              rw [polySubmodule_of_nonneg k (n + 1) (by omega),
                show (d + -1).toNat = d.toNat - 1 from by omega]
              exact hh1 t⟩ : (structureModule k (n + 1)).obj (d + -1))) t
          refine Eq.trans (congrArg Subtype.val hcomp) ?_
          rw [structureModule_mulL_val]
          exact (hh2 t).symm
  · intro y
    refine ⟨Submodule.Quotient.mk (fun t =>
      (⟨liftAlgHom j (y t).1, liftAlgHom_mem_polySubmodule j (y t).2⟩ :
        (structureModule k (n + 1)).obj d)), ?_⟩
    funext t
    exact Subtype.ext (hyperplaneAlgHom_liftAlgHom c j (y t).1)

/-- **A hyperplane in `ℙⁿ⁺¹` is a `ℙⁿ`**: for a linear form `L = ∑ᵢ cᵢxᵢ` with `c_j` a unit,
the restriction of `𝒪^{⊕r}` to `V(L)` is `𝒪^{⊕r}` on `ℙⁿ`.

This discharges the obligation recorded in `StacksAndModuli/API/ProjectiveGradedModule.lean`. -/
theorem nonempty_restrictL_pow_structureIso (c : Fin (n + 2) → k) (j : Fin (n + 2))
    (hj : IsUnit (c j)) (r : ℕ) :
    Nonempty (((structureModule k (n + 1)).pow r).restrictL c j ≅
      (structureModule k n).pow r) :=
  ⟨isoOfBijective (restrictLPowStructureHom c j hj.ne_zero r)
    (bijective_restrictLPowStructureHom_app c j hj.ne_zero r)⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule

