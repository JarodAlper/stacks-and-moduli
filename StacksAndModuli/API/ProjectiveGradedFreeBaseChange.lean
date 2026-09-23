module

public import StacksAndModuli.API.ProjectiveGradedFreeH0Homogeneous
public import StacksAndModuli.API.ProjectiveTwistGlobalSections
public import StacksAndModuli.API.ProjectiveGradedFamilies
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change of the free graded modules

For the `H⁰` comparison of `PLAN-hilbert-quot.md` the fibre statement needs to recognise the
base change of the free graded module `⨁_r S_R(-l)` as the corresponding free graded module
over the target ring.  Two isomorphisms do that:

* `structureModuleBaseChangeIso` — `(S_R)~ ⊗_R A ≅ S_A` degreewise, from
  `MvPolynomial.homogeneousSubmoduleBaseChangeEquiv` in nonnegative degrees and triviality in
  negative ones;
* `powBaseChangeIso` — base change commutes with a finite power, by `TensorProduct.piRight`.

Base change commutes with `twist` definitionally, so together these identify
`(((structureModule R n).twist a).pow r).baseChange A` with
`(((structureModule A n).twist a).pow r)`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial TensorProduct

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

/-- A degreewise linear equivalence commuting with multiplication by the variables is an
isomorphism of graded modules. -/
noncomputable def isoOfAppEquiv {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (e : ∀ d : ℤ, (M.obj d : Type u) ≃ₗ[k] (N.obj d : Type u))
    (he : ∀ (i : Fin (m + 1)) (d : ℤ) (x : (M.obj d : Type u)),
      (N.mulX i d).hom (e d x) = e (d + 1) ((M.mulX i d).hom x)) :
    M ≅ N where
  hom :=
    { app := fun d => ModuleCat.ofHom (e d).toLinearMap
      comm := fun i d => ModuleCat.hom_ext (LinearMap.ext fun x => he i d x) }
  inv :=
    { app := fun d => ModuleCat.ofHom (e d).symm.toLinearMap
      comm := fun i d => ModuleCat.hom_ext (LinearMap.ext fun y => by
        refine (e (d + 1)).injective ?_
        show e (d + 1) ((M.mulX i d).hom ((e d).symm y))
          = e (d + 1) ((e (d + 1)).symm ((N.mulX i d).hom y))
        rw [LinearEquiv.apply_symm_apply, ← he i d ((e d).symm y),
          LinearEquiv.apply_symm_apply]) }
  hom_inv_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (e d).symm_apply_apply x
  inv_hom_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact (e d).apply_symm_apply y

omit [Algebra R A] in
lemma subsingleton_polySubmodule_of_neg {e : ℤ} (he : e < 0) :
    Subsingleton (polySubmodule R n e) := by
  rw [polySubmodule_of_neg (k := R) (n := n) he]
  infer_instance

lemma subsingleton_tensor_polySubmodule_of_neg {e : ℤ} (he : e < 0) :
    Subsingleton (A ⊗[R] (polySubmodule R n e)) := by
  have := subsingleton_polySubmodule_of_neg R n he
  refine ⟨fun x y => ?_⟩
  have hz : ∀ z : A ⊗[R] (polySubmodule R n e), z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m => rw [Subsingleton.elim m 0, tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hz x, hz y]

/-- In negative degrees both sides of the base-change comparison vanish. -/
noncomputable def polySubmoduleBaseChangeEquivOfNeg {e : ℤ} (he : e < 0) :
    (A ⊗[R] (polySubmodule R n e)) ≃ₗ[A] polySubmodule A n e :=
  letI := subsingleton_tensor_polySubmodule_of_neg R A n he
  letI := subsingleton_polySubmodule_of_neg A n he
  { toFun := 0, invFun := 0, map_add' := by intros; simp, map_smul' := by intros; simp,
    left_inv := fun _ => Subsingleton.elim _ _,
    right_inv := fun _ => Subsingleton.elim _ _ }

/-- In nonnegative degrees the base-change comparison is the standard one for homogeneous
forms. -/
noncomputable def polySubmoduleBaseChangeEquivOfNonneg {e : ℤ} (he : 0 ≤ e) :
    (A ⊗[R] (polySubmodule R n e)) ≃ₗ[A] polySubmodule A n e :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (LinearEquiv.ofEq _ _ (polySubmodule_of_nonneg (k := R) (n := n) he))).trans
    ((MvPolynomial.homogeneousSubmoduleBaseChangeEquiv R A n e.toNat).trans
      (LinearEquiv.ofEq _ _ (polySubmodule_of_nonneg (k := A) (n := n) he).symm))

/-- **Base change of the degree-`e` piece of the polynomial ring.** -/
noncomputable def polySubmoduleBaseChangeEquiv (e : ℤ) :
    (A ⊗[R] (polySubmodule R n e)) ≃ₗ[A] polySubmodule A n e :=
  if he : 0 ≤ e then polySubmoduleBaseChangeEquivOfNonneg R A n he
  else polySubmoduleBaseChangeEquivOfNeg R A n (not_le.mp he)

/-- The base-change comparison sends `a ⊗ p` to `a • (p with coefficients pushed to `A`)`. -/
lemma polySubmoduleBaseChangeEquiv_tmul_val {e : ℤ} (a : A) (p : polySubmodule R n e) :
    ((polySubmoduleBaseChangeEquiv R A n e (a ⊗ₜ[R] p) : polySubmodule A n e) :
      MvPolynomial (Fin (n + 1)) A)
      = a • MvPolynomial.map (algebraMap R A) (p : MvPolynomial (Fin (n + 1)) R) := by
  rw [polySubmoduleBaseChangeEquiv]
  split
  · rename_i he
    show ((polySubmoduleBaseChangeEquivOfNonneg R A n he (a ⊗ₜ[R] p) :
      polySubmodule A n e) : MvPolynomial (Fin (n + 1)) A) = _
    rw [polySubmoduleBaseChangeEquivOfNonneg]
    simp only [LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.coe_ofEq_apply]
    rw [MvPolynomial.homogeneousSubmoduleBaseChangeEquiv_tmul]
    rfl
  · rename_i he
    have hsub := subsingleton_polySubmodule_of_neg R n (not_le.mp he)
    have hp : (p : MvPolynomial (Fin (n + 1)) R) = 0 := congrArg _ (Subsingleton.elim p 0)
    have hsub' := subsingleton_polySubmodule_of_neg A n (not_le.mp he)
    rw [hp, map_zero, smul_zero]
    exact congrArg _ (Subsingleton.elim _ 0)

/-- The base-change comparison intertwines multiplication by a variable. -/
lemma polySubmoduleBaseChangeEquiv_mulX (i : Fin (n + 1)) (d : ℤ)
    (u : A ⊗[R] (polySubmodule R n d)) :
    polyMulX A n i d (polySubmoduleBaseChangeEquiv R A n d u)
      = polySubmoduleBaseChangeEquiv R A n (d + 1)
        (LinearMap.baseChange A (polyMulX R n i d) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a p =>
      refine Subtype.ext ?_
      show MvPolynomial.X i *
          ((polySubmoduleBaseChangeEquiv R A n d (a ⊗ₜ[R] p) : polySubmodule A n d) :
            MvPolynomial (Fin (n + 1)) A) = _
      rw [polySubmoduleBaseChangeEquiv_tmul_val, LinearMap.baseChange_tmul,
        polySubmoduleBaseChangeEquiv_tmul_val]
      show _ = a • MvPolynomial.map (algebraMap R A)
        (MvPolynomial.X i * (p : MvPolynomial (Fin (n + 1)) R))
      rw [map_mul, MvPolynomial.map_X, Algebra.mul_smul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- The base-change comparison morphism of graded modules. -/
noncomputable def structureModuleBaseChangeHom :
    (structureModule R n).baseChange A ⟶ structureModule A n where
  app d := ModuleCat.ofHom (polySubmoduleBaseChangeEquiv R A n d).toLinearMap
  comm i d := ModuleCat.hom_ext (LinearMap.ext fun u =>
    polySubmoduleBaseChangeEquiv_mulX R A n i d u)

/-- **Base change of the polynomial structure module.** -/
noncomputable def structureModuleBaseChangeIso :
    (structureModule R n).baseChange A ≅ structureModule A n where
  hom := structureModuleBaseChangeHom R A n
  inv :=
    { app := fun d => ModuleCat.ofHom (polySubmoduleBaseChangeEquiv R A n d).symm.toLinearMap
      comm := fun i d => by
        refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
        refine (polySubmoduleBaseChangeEquiv R A n (d + 1)).injective ?_
        show polySubmoduleBaseChangeEquiv R A n (d + 1)
            (LinearMap.baseChange A (polyMulX R n i d)
              ((polySubmoduleBaseChangeEquiv R A n d).symm v))
          = polySubmoduleBaseChangeEquiv R A n (d + 1)
            ((polySubmoduleBaseChangeEquiv R A n (d + 1)).symm (polyMulX A n i d v))
        rw [LinearEquiv.apply_symm_apply,
          ← polySubmoduleBaseChangeEquiv_mulX R A n i d
            ((polySubmoduleBaseChangeEquiv R A n d).symm v),
          LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun u => ?_)
    exact (polySubmoduleBaseChangeEquiv R A n d).symm_apply_apply u
  inv_hom_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    exact (polySubmoduleBaseChangeEquiv R A n d).apply_symm_apply v

variable {R A n}

/-- Base change commutes with the degree shift. -/
lemma ofHom_baseChange_mulX' (M : GradedModule R n) (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e) :
    (ModuleCat.ofHom (LinearMap.baseChange A (M.mulX' i d e h).hom) :
        ModuleCat.of A (A ⊗[R] (M.obj d)) ⟶ ModuleCat.of A (A ⊗[R] (M.obj e)))
      = (M.baseChange A).mulX' i d e h := by
  subst h
  rw [mulX'_rfl, mulX'_rfl]
  rfl

noncomputable def twistBaseChangeIso (M : GradedModule R n) (a : ℤ) :
    (M.twist a).baseChange A ≅ (M.baseChange A).twist a where
  hom :=
    { app := fun _ => 𝟙 _
      comm := fun i d => by
        rw [Category.id_comp, Category.comp_id]
        exact (ofHom_baseChange_mulX' M i (d + a) (d + 1 + a) (by ring)).symm }
  inv :=
    { app := fun _ => 𝟙 _
      comm := fun i d => by
        rw [Category.id_comp, Category.comp_id]
        exact ofHom_baseChange_mulX' M i (d + a) (d + 1 + a) (by ring) }
  hom_inv_id := by refine hom_ext fun d => ?_; simp
  inv_hom_id := by refine hom_ext fun d => ?_; simp

variable (r : ℕ)

/-- Base change commutes with a finite power, by `TensorProduct.piRight`. -/
noncomputable def powBaseChangeIso (M : GradedModule R n) :
    (M.pow r).baseChange A ≅ (M.baseChange A).pow r :=
  isoOfAppEquiv
    (fun d => TensorProduct.piRight R A A (fun _ : Fin r => (M.obj d : Type u)))
    (fun i d u => by
      induction u using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x =>
          funext ρ
          show (LinearMap.baseChange A ((M.mulX i d).hom))
              ((TensorProduct.piRight R A A (fun _ : Fin r => (M.obj d : Type u))
                (a ⊗ₜ[R] x)) ρ)
            = (TensorProduct.piRight R A A (fun _ : Fin r => (M.obj (d + 1) : Type u))
                ((LinearMap.baseChange A ((M.pow r).mulX i d).hom) (a ⊗ₜ[R] x))) ρ
          rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
            LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
            TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
          rfl
      | add x y hx hy => simp only [map_add, hx, hy])

/-! ## Functoriality of `twist` and `pow`

`twistMap` is already in `StacksAndModuli/API/ProjectiveGradedModule.lean`; the finite power and the
two isomorphism versions are added here, since they are what assembles the base-change
comparison for a twisted-free module. -/

/-- Functoriality of the finite power of a graded module. -/
def powMap {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m} (f : M ⟶ N) (r : ℕ) :
    M.pow r ⟶ N.pow r where
  app d := ModuleCat.ofHom
    (LinearMap.pi fun ρ : Fin r => (f.app d).hom.comp (LinearMap.proj ρ))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun ρ => ?_)
    have h := congrArg ModuleCat.Hom.hom (f.comm i d)
    simp only [ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h (x ρ)

@[simp] lemma powMap_app {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (f : M ⟶ N) (r : ℕ) (d : ℤ) :
    (powMap f r).app d
      = ModuleCat.ofHom (LinearMap.pi fun ρ : Fin r => (f.app d).hom.comp (LinearMap.proj ρ)) :=
  rfl

/-- The degree shift of an isomorphism of graded modules. -/
noncomputable def twistMapIso {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (e : M ≅ N) (a : ℤ) : M.twist a ≅ N.twist a where
  hom := twistMap e.hom a
  inv := twistMap e.inv a
  hom_inv_id := by
    refine hom_ext fun d => ?_
    show e.hom.app (d + a) ≫ e.inv.app (d + a) = 𝟙 _
    rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by
    refine hom_ext fun d => ?_
    show e.inv.app (d + a) ≫ e.hom.app (d + a) = 𝟙 _
    rw [← comp_app, e.inv_hom_id, id_app]

/-- The finite power of an isomorphism of graded modules. -/
noncomputable def powMapIso {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (e : M ≅ N) (r : ℕ) : M.pow r ≅ N.pow r where
  hom := powMap e.hom r
  inv := powMap e.inv r
  hom_inv_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun ρ => ?_)
    have h := congrArg ModuleCat.Hom.hom (congrArg (fun t : M ⟶ M => t.app d) e.hom_inv_id)
    simp only [comp_app, ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h (x ρ)
  inv_hom_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun ρ => ?_)
    have h := congrArg ModuleCat.Hom.hom (congrArg (fun t : N ⟶ N => t.app d) e.inv_hom_id)
    simp only [comp_app, ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h (x ρ)

/-- **Base change of the twisted-free graded module.** -/
noncomputable def freeBaseChangeIso (a : ℤ) :
    ((((structureModule R n).twist a)).pow r).baseChange A ≅
      (((structureModule A n).twist a)).pow r :=
  powBaseChangeIso r ((structureModule R n).twist a) ≪≫
    powMapIso (twistBaseChangeIso (structureModule R n) a ≪≫
      twistMapIso (structureModuleBaseChangeIso R A n) a) r

/-- Base change of the identity is the identity. -/
@[simp] theorem baseChangeMap_id {k : Type u} [CommRing k] {m : ℕ} (M : GradedModule k m)
    (B : Type u) [CommRing B] [Algebra k B] :
    baseChangeMap (𝟙 M) B = 𝟙 (M.baseChange B) :=
  hom_ext fun _ ↦ ModuleCat.hom_ext LinearMap.baseChange_id

/-- Base change of graded modules is functorial. -/
@[simp] theorem baseChangeMap_comp {k : Type u} [CommRing k] {m : ℕ}
    {M N P : GradedModule k m} (f : M ⟶ N) (g : N ⟶ P)
    (B : Type u) [CommRing B] [Algebra k B] :
    baseChangeMap (f ≫ g) B = baseChangeMap f B ≫ baseChangeMap g B :=
  hom_ext fun _ ↦ ModuleCat.hom_ext (LinearMap.baseChange_comp _ _)

/-- Base change of an isomorphism of graded modules. -/
noncomputable def baseChangeMapIso {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (B : Type u) [CommRing B] [Algebra k B] (e : M ≅ N) :
    M.baseChange B ≅ N.baseChange B where
  hom := baseChangeMap e.hom B
  inv := baseChangeMap e.inv B
  hom_inv_id := by rw [← baseChangeMap_comp, e.hom_inv_id, baseChangeMap_id]
  inv_hom_id := by rw [← baseChangeMap_comp, e.inv_hom_id, baseChangeMap_id]

/-- The degree-`d` component of an isomorphism of graded modules. -/
noncomputable def appIso {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (e : M ≅ N) (d : ℤ) : M.obj d ≅ N.obj d where
  hom := e.hom.app d
  inv := e.inv.app d
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

/-- Čech cohomology of graded modules transports along an isomorphism. -/
noncomputable def cechHgrMapIso {k : Type u} [CommRing k] {m : ℕ} {M N : GradedModule k m}
    (e : M ≅ N) (q : ℕ) : M.cechHgr q ≅ N.cechHgr q where
  hom := cechHgrMap e.hom q
  inv := cechHgrMap e.inv q
  hom_inv_id := by rw [← cechHgrMap_comp, e.hom_inv_id, cechHgrMap_id]
  inv_hom_id := by rw [← cechHgrMap_comp, e.inv_hom_id, cechHgrMap_id]

/-- **The graded half of the fibre comparison.**  The base change to `A` of the twisted-free
graded module has the same `H⁰` description as the twisted-free module over `A`. -/
noncomputable def cechHgrFreeBaseChangeHomogeneousEquiv (l : ℤ) (d : ℤ) (e : ℕ)
    (he : (e : ℤ) = d - l) :
    ((((((structureModule R n).twist (-l)).pow r).baseChange A).cechHgr 0).obj d) ≃ₗ[A]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e) :=
  (appIso (cechHgrMapIso
      (freeBaseChangeIso (R := R) (A := A) (n := n) r (-l)) 0) d).toLinearEquiv.trans
    (cechHgrFreeHomogeneousEquiv A n l r d e he)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
