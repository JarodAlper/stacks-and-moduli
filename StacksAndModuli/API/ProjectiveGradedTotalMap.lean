module

public import StacksAndModuli.API.ProjectiveGradedTotalDecomposition

/-!
# Functoriality of the total module

A morphism in StacksAndModuli's diagrammatic category of graded modules induces a linear map of total
modules over the polynomial ring.  This file proves polynomial linearity directly from the
commutation with the variable actions and records its behaviour on pure degree elements and
degree projections.

The resulting map is the presentation map needed when Stacks Project tag 053C is applied to the
total module of a flat graded family.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open CategoryTheory DirectSum MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}
variable {M N P : GradedModule R n}

/-- The coefficient-linear map on total modules induced degree by degree. -/
def mapLinear (f : M ⟶ N) : Total M →ₗ[R] Total N :=
  DirectSum.lmap fun d => (f.app d).hom

@[simp]
lemma mapLinear_tof (f : M ⟶ N) (d : ℤ) (x : M.obj d) :
    mapLinear f (tof M d x) = tof N d ((f.app d).hom x) := by
  exact DirectSum.lmap_lof (fun d => (f.app d).hom) d x

@[simp]
lemma tcomp_mapLinear (f : M ⟶ N) (d : ℤ) (x : Total M) :
    tcomp N d (mapLinear f x) = (f.app d).hom (tcomp M d x) := by
  rfl

/-- A graded morphism commutes with multiplication by a monomial. -/
lemma map_mulMono_apply (f : M ⟶ N) (b : Fin (n + 1) →₀ ℕ)
    (d e : ℤ) (h : d + (b.degree : ℤ) = e) (x : M.obj d) :
    (f.app e).hom ((M.mulMono b d e h).hom x) =
      (N.mulMono b d e h).hom ((f.app d).hom x) := by
  have hcomm := congrArg
    (fun g : M.obj d ⟶ N.obj e => g.hom x)
    (comm_mulList f (monoList b) d e (by rw [monoList_length]; exact h))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, mulMono] using hcomm.symm

/-- The total map commutes with multiplication by a monomial. -/
lemma mapLinear_monomial_smul (f : M ⟶ N) (b : Fin (n + 1) →₀ ℕ) (c : R)
    (x : Total M) :
    mapLinear f ((monomial b c : MvPolynomial (Fin (n + 1)) R) • x) =
      (monomial b c : MvPolynomial (Fin (n + 1)) R) • mapLinear f x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      rw [show DirectSum.of (fun d => (M.obj d : Type u)) d x = tof M d x from rfl]
      have h : d + (b.degree : ℤ) = d + (b.degree : ℤ) := rfl
      rw [monomial_smul_tof M b c h x, mapLinear_tof, map_smul,
        mapLinear_tof, monomial_smul_tof N b c h]
      congr 2
      exact map_mulMono_apply f b d (d + (b.degree : ℤ)) h x
  | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]

/-- The total map commutes with the full polynomial action. -/
lemma mapLinear_smul (f : M ⟶ N) (p : MvPolynomial (Fin (n + 1)) R)
    (x : Total M) : mapLinear f (p • x) = p • mapLinear f x := by
  induction p using MvPolynomial.induction_on' with
  | monomial b c => exact mapLinear_monomial_smul f b c x
  | add p q hp hq =>
      simp only [add_smul, map_add, hp, hq]

/-- A graded morphism induces a polynomial-linear map on total modules. -/
def map (f : M ⟶ N) :
    Total M →ₗ[MvPolynomial (Fin (n + 1)) R] Total N where
  toFun := mapLinear f
  map_add' := (mapLinear f).map_add
  map_smul' := mapLinear_smul f

@[simp]
lemma map_tof (f : M ⟶ N) (d : ℤ) (x : M.obj d) :
    map f (tof M d x) = tof N d ((f.app d).hom x) := mapLinear_tof f d x

@[simp]
lemma tcomp_map (f : M ⟶ N) (d : ℤ) (x : Total M) :
    tcomp N d (map f x) = (f.app d).hom (tcomp M d x) := tcomp_mapLinear f d x

lemma map_comp (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = (map g).comp (map f) := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      rw [show DirectSum.of (fun d => (M.obj d : Type u)) d x = tof M d x from rfl]
      simp [map_tof]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
lemma map_id : map (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      rw [show DirectSum.of (fun d => (M.obj d : Type u)) d x = tof M d x from rfl]
      simp [map_tof]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.id_apply]

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end
