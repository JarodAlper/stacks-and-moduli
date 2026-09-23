module

public import StacksAndModuli.API.ProjectiveGradedCechBaseChange
public import StacksAndModuli.API.ProjectiveGradedCohomologyExists
public import StacksAndModuli.API.ProjectiveGradedFamilies
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Base change of graded modules along a field extension

Supporting API with no Stacks Project counterpart.

`GradedModule.baseChange` (`API/ProjectiveGradedFamilies.lean`) is `M ↦ k' ⊗_k M`
degreewise, the graded-module model of `F ↦ F ⊗_k k'` on `ℙⁿ`.  This file records what it
preserves along a *field* extension.
Because `k → k'` is faithfully flat, everything in sight is preserved and reflected; this is
the input to the reduction to an infinite base field at the start of Proposition 2.3.5 and
Theorem 2.3.8.

Main declarations:
- `GradedModule.IsFG.baseChange`;
- `GradedModule.locBaseChangeToTensor`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial TensorProduct

variable {k : Type u} [Field k] {n : ℕ}
variable (k' : Type u) [Field k'] [Algebra k k']
variable (M : GradedModule k n)

/-! ## Flatness and faithful flatness of a field extension

The cochain-level comparison — which needs no flatness at all and holds along an arbitrary
ring map — is `API/ProjectiveGradedCechBaseChange.lean`.  This file is what a *faithfully
flat* extension buys on top of it: base change commutes with cohomology, preserves
dimensions, and reflects vanishing and global generation. -/

section Flat

variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

lemma injective_baseChange {f : V →ₗ[k] W} (hf : Function.Injective f) :
    Function.Injective (LinearMap.baseChange k' f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Base change of a kernel is the kernel of the base change. -/
lemma ker_baseChange (f : V →ₗ[k] W) :
    LinearMap.ker (LinearMap.baseChange k' f)
      = LinearMap.range (LinearMap.baseChange k' (LinearMap.ker f).subtype) := by
  refine le_antisymm (fun u hu => ?_) ?_
  · exact (Module.Flat.lTensor_exact (M := k') f.exact_subtype_ker_map u).mp hu
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      show f ∘ₗ (LinearMap.ker f).subtype = 0 from LinearMap.ext fun x => x.2]
    simp

/-- Base change of an image is the image of the base change. -/
lemma range_baseChange (f : V →ₗ[k] W) :
    LinearMap.range (LinearMap.baseChange k' f)
      = LinearMap.range (LinearMap.baseChange k' (LinearMap.range f).subtype) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    have hfac : f = (LinearMap.range f).subtype ∘ₗ f.rangeRestrict := rfl
    rw [hfac, LinearMap.baseChange_comp]
    exact ⟨(LinearMap.baseChange k' f.rangeRestrict) u, rfl⟩
  · rintro _ ⟨v, rfl⟩
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a w =>
        obtain ⟨x, hx⟩ := w.2
        refine ⟨a ⊗ₜ[k] x, ?_⟩
        change a ⊗ₜ[k] (f x) = a ⊗ₜ[k] (w : W)
        rw [hx]
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq

lemma subsingleton_baseChange_iff :
    Subsingleton (k' ⊗[k] V) ↔ Subsingleton V :=
  Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k k'

end Flat

/-! ## Faithful flatness reflects submodules -/

section Reflect

variable {V W U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

lemma mem_of_tmul_one_mem_baseChange (S : Submodule k V) (v : V)
    (h : (1 : k') ⊗ₜ[k] v ∈ LinearMap.range (LinearMap.baseChange k' S.subtype)) :
    v ∈ S := by
  obtain ⟨w, hw⟩ := h
  have h2 : (LinearMap.baseChange k' S.mkQ) ((1 : k') ⊗ₜ[k] v) = 0 := by
    rw [← hw, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      show S.mkQ ∘ₗ S.subtype = 0 from LinearMap.ext fun x => by simp]
    simp
  rw [LinearMap.baseChange_tmul] at h2
  exact (Submodule.Quotient.mk_eq_zero _).mp
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := k) (A := k') (M := V ⧸ S)
      (S.mkQ v)).mp h2)

lemma tmul_one_mem_baseChange (S : Submodule k V) {v : V} (hv : v ∈ S) :
    (1 : k') ⊗ₜ[k] v ∈ LinearMap.range (LinearMap.baseChange k' S.subtype) :=
  ⟨(1 : k') ⊗ₜ[k] (⟨v, hv⟩ : S), rfl⟩

/-- A submodule is determined by its base change. -/
lemma submodule_eq_of_baseChange_range_eq {S T : Submodule k V}
    (h : LinearMap.range (LinearMap.baseChange k' S.subtype)
      = LinearMap.range (LinearMap.baseChange k' T.subtype)) : S = T := by
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · exact mem_of_tmul_one_mem_baseChange k' T v
      (h ▸ tmul_one_mem_baseChange k' S hv)
  · exact mem_of_tmul_one_mem_baseChange k' S v
      (h ▸ tmul_one_mem_baseChange k' T hv)

/-- Exactness at the middle spot is detected by base change. -/
lemma range_eq_ker_baseChange_iff (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    LinearMap.range (LinearMap.baseChange k' f)
        = LinearMap.ker (LinearMap.baseChange k' g)
      ↔ LinearMap.range f = LinearMap.ker g := by
  rw [range_baseChange, ker_baseChange]
  exact ⟨fun h => submodule_eq_of_baseChange_range_eq k' h, fun h => by rw [h]⟩

end Reflect

/-! ## Base change preserves the dimensions of kernels and images -/

section FlatRank

variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

lemma finrank_ker_baseChange (f : V →ₗ[k] W) :
    Module.finrank k' (LinearMap.ker (LinearMap.baseChange k' f))
      = Module.finrank k (LinearMap.ker f) := by
  have e := LinearEquiv.ofInjective (LinearMap.baseChange k' (LinearMap.ker f).subtype)
    (injective_baseChange k' (Submodule.injective_subtype _))
  rw [ker_baseChange, ← e.finrank_eq]
  exact Module.finrank_baseChange

lemma finrank_range_baseChange (f : V →ₗ[k] W) :
    Module.finrank k' (LinearMap.range (LinearMap.baseChange k' f))
      = Module.finrank k (LinearMap.range f) := by
  have e := LinearEquiv.ofInjective (LinearMap.baseChange k' (LinearMap.range f).subtype)
    (injective_baseChange k' (Submodule.injective_subtype _))
  rw [range_baseChange, ← e.finrank_eq]
  exact Module.finrank_baseChange

end FlatRank

/-! ## Faithful flatness reflects the multiplication spans -/

lemma mulSpan_of_baseChange_eq_top (d e : ℤ)
    (h : (M.baseChange k').mulSpan d e = ⊤) : M.mulSpan d e = ⊤ := by
  have hle : (M.baseChange k').mulSpan d e
      ≤ LinearMap.range (LinearMap.baseChange k' (M.mulSpan d e).subtype) := by
    refine iSup_le fun l => ?_
    rintro _ ⟨x, rfl⟩
    have hg : (M.mulSpan d e).subtype ∘ₗ
        ((M.mulList l.1 d e l.2).hom.codRestrict (M.mulSpan d e)
          (fun y => le_mulSpan M d e l.1 l.2 ⟨y, rfl⟩))
        = (M.mulList l.1 d e l.2).hom := rfl
    rw [baseChange_mulList]
    refine ⟨(LinearMap.baseChange k'
      ((M.mulList l.1 d e l.2).hom.codRestrict (M.mulSpan d e)
        (fun y => le_mulSpan M d e l.1 l.2 ⟨y, rfl⟩))) x, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hg]
    rfl
  refine eq_top_iff.mpr fun v _ => ?_
  have h1 : (1 : k') ⊗ₜ[k] v
      ∈ LinearMap.range (LinearMap.baseChange k' (M.mulSpan d e).subtype) :=
    hle (h ▸ Submodule.mem_top)
  obtain ⟨w, hw⟩ := h1
  have h2 : (LinearMap.baseChange k' (M.mulSpan d e).mkQ) ((1 : k') ⊗ₜ[k] v) = 0 := by
    rw [← hw, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      show (M.mulSpan d e).mkQ ∘ₗ (M.mulSpan d e).subtype = 0 from
        LinearMap.ext fun x => by simp]
    simp
  rw [LinearMap.baseChange_tmul] at h2
  have h3 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := k) (A := k')
    (M := (M.obj e) ⧸ (M.mulSpan d e)) ((M.mulSpan d e).mkQ v)).mp h2
  exact (Submodule.Quotient.mk_eq_zero _).mp h3

lemma mulSpan_baseChange_iff (d e : ℤ) :
    (M.baseChange k').mulSpan d e = ⊤ ↔ M.mulSpan d e = ⊤ :=
  ⟨mulSpan_of_baseChange_eq_top k' M d e, baseChange_mulSpan_eq_top k' M d e⟩

/-! ## Base change of the twisting sheaves -/

lemma smul_map_mem_polySubmodule (d : ℤ) (a : k') {p : MvPolynomial (Fin (n + 1)) k}
    (hp : p ∈ polySubmodule k n d) :
    a • (MvPolynomial.map (algebraMap k k') p) ∈ polySubmodule k' n d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [polySubmodule_of_neg k n hd, Submodule.mem_bot] at hp
    subst hp
    rw [polySubmodule_of_neg k' n hd]
    simp
  · rw [polySubmodule_of_nonneg k n hd, MvPolynomial.mem_homogeneousSubmodule] at hp
    rw [polySubmodule_of_nonneg k' n hd]
    exact Submodule.smul_mem _ a
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hp.map (algebraMap k k')))

/-- Base change of the degree-`d` forms. -/
noncomputable def polyBaseChange (d : ℤ) :
    (k' ⊗[k] (polySubmodule k n d)) →ₗ[k'] (polySubmodule k' n d) :=
  LinearMap.codRestrict (polySubmodule k' n d)
    (((MvPolynomial.algebraTensorAlgEquiv k k').toLinearMap).comp
      (LinearMap.baseChange k' (polySubmodule k n d).subtype))
    (fun u => by
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
          change MvPolynomial.algebraTensorAlgEquiv k k'
            (a ⊗ₜ[k] (p : MvPolynomial (Fin (n + 1)) k)) ∈ polySubmodule k' n d
          rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
          exact smul_map_mem_polySubmodule k' d a p.2
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy)

@[simp] lemma polyBaseChange_tmul (d : ℤ) (a : k') (p : polySubmodule k n d) :
    (polyBaseChange k' d (a ⊗ₜ[k] p) : MvPolynomial (Fin (n + 1)) k')
      = a • (MvPolynomial.map (algebraMap k k') (p : MvPolynomial (Fin (n + 1)) k)) := by
  change MvPolynomial.algebraTensorAlgEquiv k k'
    (a ⊗ₜ[k] (p : MvPolynomial (Fin (n + 1)) k)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]

lemma injective_polyBaseChange (d : ℤ) :
    Function.Injective (polyBaseChange k' (k := k) (n := n) d) := by
  intro x y hxy
  have h1 : ((MvPolynomial.algebraTensorAlgEquiv k k').toLinearMap.comp
      (LinearMap.baseChange k' (polySubmodule k n d).subtype)) x
    = ((MvPolynomial.algebraTensorAlgEquiv k k').toLinearMap.comp
      (LinearMap.baseChange k' (polySubmodule k n d).subtype)) y :=
    congrArg Subtype.val hxy
  refine injective_baseChange k' (Submodule.injective_subtype _) ?_
  exact (MvPolynomial.algebraTensorAlgEquiv k k').injective h1

lemma polyBaseChange_mulX (i : Fin (n + 1)) (d : ℤ)
    (u : k' ⊗[k] (polySubmodule k n d)) :
    polyBaseChange k' (d + 1) ((LinearMap.baseChange k' (polyMulX k n i d)) u)
      = polyMulX k' n i d (polyBaseChange k' d u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
      refine Subtype.ext ?_
      change (polyBaseChange k' (d + 1) (a ⊗ₜ[k] (polyMulX k n i d p))
          : MvPolynomial (Fin (n + 1)) k')
        = MvPolynomial.X i * (polyBaseChange k' d (a ⊗ₜ[k] p) : MvPolynomial _ k')
      rw [polyBaseChange_tmul, polyBaseChange_tmul]
      change a • (MvPolynomial.map (algebraMap k k')
          (MvPolynomial.X i * (p : MvPolynomial (Fin (n + 1)) k))) = _
      rw [map_mul, MvPolynomial.map_X, Algebra.mul_smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma injective_piBaseChangeProj {r : ℕ} (V : Fin r → Type u)
    [∀ ρ, AddCommGroup (V ρ)] [∀ ρ, Module k (V ρ)] :
    Function.Injective (LinearMap.pi (fun ρ : Fin r =>
      LinearMap.baseChange k' (LinearMap.proj ρ : (∀ ρ, V ρ) →ₗ[k] V ρ))) := by
  have hagree : ∀ u : k' ⊗[k] (∀ ρ, V ρ),
      (LinearMap.pi (fun ρ : Fin r =>
        LinearMap.baseChange k' (LinearMap.proj ρ : (∀ ρ, V ρ) →ₗ[k] V ρ))) u
      = (TensorProduct.piRight k k' k' V) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a f =>
        rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
        funext ρ
        rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  exact (TensorProduct.piRight k k' k' V).injective
    ((hagree x).symm.trans (hxy.trans (hagree y)))

/-- Base change of a finite direct sum of copies of the structure sheaf. -/
noncomputable def structurePowBaseChangeHom (r : ℕ) :
    ((structureModule k n).pow r).baseChange k' ⟶ (structureModule k' n).pow r where
  app d := ModuleCat.ofHom (LinearMap.pi (fun ρ : Fin r =>
    (polyBaseChange k' d).comp (LinearMap.baseChange k'
      (LinearMap.proj ρ : (∀ _ : Fin r, (polySubmodule k n d)) →ₗ[k] (polySubmodule k n d)))))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun u => funext fun ρ => ?_)
    refine Eq.symm ?_
    have hmap : ((LinearMap.proj ρ :
          (∀ _ : Fin r, (polySubmodule k n (d + 1))) →ₗ[k] (polySubmodule k n (d + 1)))
        ∘ₗ (LinearMap.pi (fun σ : Fin r => (polyMulX k n i d).comp (LinearMap.proj σ))))
      = (polyMulX k n i d).comp (LinearMap.proj ρ) := rfl
    have hbc : (LinearMap.baseChange k' (LinearMap.proj ρ :
          (∀ _ : Fin r, (polySubmodule k n (d + 1))) →ₗ[k] (polySubmodule k n (d + 1))))
        ∘ₗ (LinearMap.baseChange k' (LinearMap.pi (fun σ : Fin r =>
          (polyMulX k n i d).comp (LinearMap.proj σ))))
      = (LinearMap.baseChange k' (polyMulX k n i d))
        ∘ₗ (LinearMap.baseChange k' (LinearMap.proj ρ :
          (∀ _ : Fin r, (polySubmodule k n d)) →ₗ[k] (polySubmodule k n d))) := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      exact congrArg (LinearMap.baseChange k') hmap
    have h2 := LinearMap.congr_fun hbc u
    simp only [LinearMap.comp_apply] at h2
    change polyBaseChange k' (d + 1) ((LinearMap.baseChange k' (LinearMap.proj ρ))
        ((LinearMap.baseChange k' (LinearMap.pi (fun σ : Fin r =>
          (polyMulX k n i d).comp (LinearMap.proj σ)))) u))
      = polyMulX k' n i d (polyBaseChange k' d
          ((LinearMap.baseChange k' (LinearMap.proj ρ)) u))
    rw [h2, polyBaseChange_mulX]
    rfl

lemma injective_structurePowBaseChangeHom (r : ℕ) (d : ℤ) :
    Function.Injective (((structurePowBaseChangeHom (k := k) (n := n) k' r).app d).hom) := by
  intro x y hxy
  refine injective_piBaseChangeProj (k := k) k' (fun _ : Fin r => (polySubmodule k n d)) ?_
  funext ρ
  exact injective_polyBaseChange k' d (congrFun hxy ρ)

/-- **Base change of a subsheaf of `𝒪^{⊕r}` is a subsheaf of `𝒪^{⊕r}`**: the `mono` field of
`Cohomology.BaseChange`. -/
lemma exists_mono_baseChange {r : ℕ} {M : GradedModule k n}
    (f : M ⟶ (structureModule k n).pow r)
    (hf : ∀ d, Function.Injective (f.app d).hom) :
    ∃ f' : M.baseChange k' ⟶ (structureModule k' n).pow r,
      ∀ d, Function.Injective (f'.app d).hom := by
  refine ⟨GradedModule.baseChangeMap f k' ≫ structurePowBaseChangeHom (k := k) k' r,
    fun d => ?_⟩
  intro x y hxy
  refine injective_baseChange k' (hf d) ?_
  exact injective_structurePowBaseChangeHom (k := k) k' r d hxy

/-! ## Base change of homology -/

/-- The base change of a short complex of `k`-vector spaces. -/
noncomputable def shortComplexBaseChange (S : ShortComplex (ModuleCat.{u} k)) :
    ShortComplex (ModuleCat.{u} k') where
  X₁ := ModuleCat.of k' (k' ⊗[k] S.X₁)
  X₂ := ModuleCat.of k' (k' ⊗[k] S.X₂)
  X₃ := ModuleCat.of k' (k' ⊗[k] S.X₃)
  f := ModuleCat.ofHom (LinearMap.baseChange k' S.f.hom)
  g := ModuleCat.ofHom (LinearMap.baseChange k' S.g.hom)
  zero := by
    refine ModuleCat.hom_ext ?_
    change LinearMap.baseChange k' S.g.hom ∘ₗ LinearMap.baseChange k' S.f.hom = 0
    rw [← LinearMap.baseChange_comp]
    have h := congrArg ModuleCat.Hom.hom S.zero
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    rw [h]
    simp

/-- The cycles of a base change are the base change of the cycles. -/
noncomputable def kerBaseChangeEquiv (S : ShortComplex (ModuleCat.{u} k)) :
    (k' ⊗[k] (LinearMap.ker S.g.hom))
      ≃ₗ[k'] (LinearMap.ker (LinearMap.baseChange k' S.g.hom)) :=
  (LinearEquiv.ofInjective (LinearMap.baseChange k' (LinearMap.ker S.g.hom).subtype)
      (injective_baseChange k' (Submodule.injective_subtype _))).trans
    (LinearEquiv.ofEq _ _ (ker_baseChange k' S.g.hom).symm)

lemma kerBaseChangeEquiv_val (S : ShortComplex (ModuleCat.{u} k))
    (w : k' ⊗[k] (LinearMap.ker S.g.hom)) :
    ((kerBaseChangeEquiv k' S w : LinearMap.ker (LinearMap.baseChange k' S.g.hom))
        : k' ⊗[k] S.X₂)
      = (LinearMap.baseChange k' (LinearMap.ker S.g.hom).subtype) w := rfl

lemma map_kerBaseChangeEquiv (S : ShortComplex (ModuleCat.{u} k)) :
    Submodule.map (kerBaseChangeEquiv k' S).toLinearMap
        (LinearMap.range (LinearMap.baseChange k' S.moduleCatToCycles))
      = LinearMap.range (shortComplexBaseChange k' S).moduleCatToCycles := by
  have hcomp : ∀ u : k' ⊗[k] S.X₁,
      kerBaseChangeEquiv k' S ((LinearMap.baseChange k' S.moduleCatToCycles) u)
        = (shortComplexBaseChange k' S).moduleCatToCycles u := by
    intro u
    refine Subtype.ext ?_
    rw [kerBaseChangeEquiv_val, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  ext y
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (hcomp u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(LinearMap.baseChange k' S.moduleCatToCycles) u, ⟨u, rfl⟩, hcomp u⟩

/-- **Base change commutes with the homology of a short complex of vector spaces.** -/
noncomputable def homologyBaseChangeEquiv (S : ShortComplex (ModuleCat.{u} k)) :
    ((shortComplexBaseChange k' S).homology) ≃ₗ[k'] (k' ⊗[k] S.homology) :=
  ((ShortComplex.moduleCatHomologyIso (shortComplexBaseChange k' S)).toLinearEquiv.trans
    ((Submodule.Quotient.equiv _ _ (kerBaseChangeEquiv k' S)
        (map_kerBaseChangeEquiv k' S)).symm.trans
      ((Submodule.quotEquivOfEq _ _ (range_baseChange k' S.moduleCatToCycles)).trans
        ((quotBaseChangeEquiv k' (LinearMap.range S.moduleCatToCycles)).trans
          (LinearEquiv.baseChange k k' _ _
            (ShortComplex.moduleCatHomologyIso S).toLinearEquiv.symm)))))

/-- Functoriality of the base change of short complexes. -/
noncomputable def shortComplexBaseChangeMap {S T : ShortComplex (ModuleCat.{u} k)}
    (ψ : S ⟶ T) : shortComplexBaseChange k' S ⟶ shortComplexBaseChange k' T where
  τ₁ := ModuleCat.ofHom (LinearMap.baseChange k' ψ.τ₁.hom)
  τ₂ := ModuleCat.ofHom (LinearMap.baseChange k' ψ.τ₂.hom)
  τ₃ := ModuleCat.ofHom (LinearMap.baseChange k' ψ.τ₃.hom)
  comm₁₂ := by
    refine ModuleCat.hom_ext ?_
    change LinearMap.baseChange k' T.f.hom ∘ₗ LinearMap.baseChange k' ψ.τ₁.hom
      = LinearMap.baseChange k' ψ.τ₂.hom ∘ₗ LinearMap.baseChange k' S.f.hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    have h := congrArg ModuleCat.Hom.hom ψ.comm₁₂
    simp only [ModuleCat.hom_comp] at h
    exact h
  comm₂₃ := by
    refine ModuleCat.hom_ext ?_
    change LinearMap.baseChange k' T.g.hom ∘ₗ LinearMap.baseChange k' ψ.τ₂.hom
      = LinearMap.baseChange k' ψ.τ₃.hom ∘ₗ LinearMap.baseChange k' S.g.hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    have h := congrArg ModuleCat.Hom.hom ψ.comm₂₃
    simp only [ModuleCat.hom_comp] at h
    exact h

/-- The homology comparison, computed on a class. -/
lemma homologyBaseChangeEquiv_mk (S : ShortComplex (ModuleCat.{u} k)) (a : k')
    (z : LinearMap.ker S.g.hom) :
    homologyBaseChangeEquiv k' S
        ((ShortComplex.moduleCatHomologyIso (shortComplexBaseChange k' S)).toLinearEquiv.symm
          (Submodule.Quotient.mk (kerBaseChangeEquiv k' S (a ⊗ₜ[k] z))))
      = a ⊗ₜ[k] ((ShortComplex.moduleCatHomologyIso S).toLinearEquiv.symm
          (Submodule.Quotient.mk z)) := by
  rw [homologyBaseChangeEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have h1 : (Submodule.Quotient.equiv
        (LinearMap.range (LinearMap.baseChange k' S.moduleCatToCycles))
        (LinearMap.range (shortComplexBaseChange k' S).moduleCatToCycles)
        (kerBaseChangeEquiv k' S) (map_kerBaseChangeEquiv k' S)).symm
      (Submodule.Quotient.mk ((kerBaseChangeEquiv k' S) (a ⊗ₜ[k] z)))
    = Submodule.Quotient.mk (a ⊗ₜ[k] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  erw [h1]
  have h3 : (quotBaseChangeEquiv k' (LinearMap.range S.moduleCatToCycles))
      ((Submodule.quotEquivOfEq _ _ (range_baseChange k' S.moduleCatToCycles))
        (Submodule.Quotient.mk (a ⊗ₜ[k] z)))
    = a ⊗ₜ[k] (Submodule.Quotient.mk z) := by
    rw [quotBaseChangeEquiv]
    simp only [LinearEquiv.trans_apply]
    rfl
  erw [h3]
  rfl

lemma mem_ker_tau2 {S T : ShortComplex (ModuleCat.{u} k)} (ψ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) : ψ.τ₂.hom (z : S.X₂) ∈ LinearMap.ker T.g.hom := by
  have h := congrArg ModuleCat.Hom.hom ψ.comm₂₃
  simp only [ModuleCat.hom_comp] at h
  have hz := LinearMap.congr_fun h (z : S.X₂)
  simp only [LinearMap.comp_apply] at hz
  rw [LinearMap.mem_ker, hz, show S.g.hom (z : S.X₂) = 0 from z.2, map_zero]

lemma sbcMap_kerBaseChangeEquiv_val {S T : ShortComplex (ModuleCat.{u} k)} (ψ : S ⟶ T)
    (a : k') (z : LinearMap.ker S.g.hom) :
    ((shortComplexBaseChangeMap k' ψ).τ₂).hom
        ((kerBaseChangeEquiv k' S (a ⊗ₜ[k] z) : k' ⊗[k] S.X₂))
      = ((kerBaseChangeEquiv k' T (a ⊗ₜ[k]
          (⟨ψ.τ₂.hom (z : S.X₂), mem_ker_tau2 ψ z⟩ : LinearMap.ker T.g.hom)))
            : k' ⊗[k] T.X₂) := by
  rw [kerBaseChangeEquiv_val, kerBaseChangeEquiv_val]
  change (LinearMap.baseChange k' ψ.τ₂.hom)
    ((LinearMap.baseChange k' (LinearMap.ker S.g.hom).subtype) (a ⊗ₜ[k] z))
    = (LinearMap.baseChange k' (LinearMap.ker T.g.hom).subtype)
      (a ⊗ₜ[k] (⟨ψ.τ₂.hom (z : S.X₂), mem_ker_tau2 ψ z⟩ : LinearMap.ker T.g.hom))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

/-- **The homology comparison is natural.** -/
lemma homologyBaseChangeEquiv_naturality {S T : ShortComplex (ModuleCat.{u} k)} (ψ : S ⟶ T)
    (x : (shortComplexBaseChange k' S).homology) :
    homologyBaseChangeEquiv k' T
        ((ShortComplex.homologyMap (shortComplexBaseChangeMap k' ψ)).hom x)
      = (LinearMap.baseChange k' (ShortComplex.homologyMap ψ).hom)
          (homologyBaseChangeEquiv k' S x) := by
  obtain ⟨w, rfl⟩ := (ShortComplex.moduleCatHomologyIso
    (shortComplexBaseChange k' S)).toLinearEquiv.symm.surjective x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨u, rfl⟩ := (kerBaseChangeEquiv k' S).surjective v
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      rw [moduleCatHomologyIso_symm_mk_naturality (shortComplexBaseChangeMap k' ψ) _
          (mem_ker_tau2 (shortComplexBaseChangeMap k' ψ) _),
        show (⟨_, mem_ker_tau2 (shortComplexBaseChangeMap k' ψ)
            (kerBaseChangeEquiv k' S (a ⊗ₜ[k] z))⟩
              : LinearMap.ker ((shortComplexBaseChange k' T).g).hom)
          = kerBaseChangeEquiv k' T (a ⊗ₜ[k]
              (⟨ψ.τ₂.hom (z : S.X₂), mem_ker_tau2 ψ z⟩ : LinearMap.ker T.g.hom)) from
          Subtype.ext (sbcMap_kerBaseChangeEquiv_val k' ψ a z),
        homologyBaseChangeEquiv_mk,
        homologyBaseChangeEquiv_mk, LinearMap.baseChange_tmul,
        moduleCatHomologyIso_symm_mk_naturality ψ z (mem_ker_tau2 ψ z)]
  | add p q hp hq => simp only [map_add, Submodule.Quotient.mk_add, hp, hq]

/-- The short complex of a base-changed complex is the base change of the short complex. -/
noncomputable def scCochainBaseChangeIso (C : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (cochainBaseChange k' C).sc i ≅ shortComplexBaseChange k' (C.sc i) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (cochainBaseChange_d' k' C ((ComplexShape.up ℕ).prev i) i).symm)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (cochainBaseChange_d' k' C i ((ComplexShape.up ℕ).next i)).symm)

noncomputable def homologyCochainBaseChangeEquiv (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (i : ℕ) :
    ((cochainBaseChange k' C).homology i) ≃ₗ[k'] (k' ⊗[k] (C.homology i)) :=
  ((ShortComplex.homologyMapIso (scCochainBaseChangeIso k' C i)).toLinearEquiv).trans
    (homologyBaseChangeEquiv k' (C.sc i))

lemma scCochainBaseChangeIso_naturality {C D : CochainComplex (ModuleCat.{u} k) ℕ}
    (φ : C ⟶ D) (i : ℕ) :
    ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor
        (ModuleCat.{u} k') (ComplexShape.up ℕ) i).map (cochainBaseChangeMap k' φ))
      ≫ ShortComplex.homologyMap (scCochainBaseChangeIso k' D i).hom
      = ShortComplex.homologyMap (scCochainBaseChangeIso k' C i).hom
        ≫ ShortComplex.homologyMap (shortComplexBaseChangeMap k'
            ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k)
              (ComplexShape.up ℕ) i).map φ)) := by
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1


/-- **Base change commutes with graded Čech cohomology.** -/
noncomputable def cechHgrBaseChangeEquiv (i : ℕ) (d : ℤ) :
    (((M.baseChange k').cechHgr i).obj d) ≃ₗ[k'] (k' ⊗[k] ((M.cechHgr i).obj d)) :=
  ((HomologicalComplex.homologyMapIso (cechComplexBaseChangeIso k' M d) i).toLinearEquiv).trans
    (homologyCochainBaseChangeEquiv k' (M.cechComplex d) i)

/-- The Čech comparison is compatible with multiplication by a variable. -/
lemma cechHgrBaseChangeEquiv_mulX (i : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (x : ((M.baseChange k').cechHgr i).obj d) :
    cechHgrBaseChangeEquiv k' M i (d + 1)
        ((((M.baseChange k').cechHgr i).mulX j d).hom x)
      = (LinearMap.baseChange k' (((M.cechHgr i).mulX j d).hom))
          (cechHgrBaseChangeEquiv k' M i d x) := by
  have hA := congrArg (fun t : ((M.baseChange k').cechComplex d)
      ⟶ (cochainBaseChange k' (M.cechComplex (d + 1))) =>
      (HomologicalComplex.homologyMap t i).hom)
    (cechMulX_cechComplexBaseChangeIso k' M j d)
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp] at hA
  have hAx := LinearMap.congr_fun hA x
  simp only [LinearMap.comp_apply] at hAx
  have hB := congrArg ModuleCat.Hom.hom
    (scCochainBaseChangeIso_naturality k' (M.cechMulX j d) i)
  simp only [ModuleCat.hom_comp] at hB
  have hC := homologyBaseChangeEquiv_naturality k'
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i).map
      (M.cechMulX j d))
  change homologyBaseChangeEquiv k' ((M.cechComplex (d + 1)).sc i)
      ((ShortComplex.homologyMap
        (scCochainBaseChangeIso k' (M.cechComplex (d + 1)) i).hom).hom
        ((HomologicalComplex.homologyMap
          (cechComplexBaseChangeIso k' M (d + 1)).hom i).hom
          ((HomologicalComplex.homologyMap ((M.baseChange k').cechMulX j d) i).hom x)))
    = _
  rw [hAx]
  have hBx := LinearMap.congr_fun hB
    ((HomologicalComplex.homologyMap (cechComplexBaseChangeIso k' M d).hom i).hom x)
  simp only [LinearMap.comp_apply] at hBx
  erw [hBx, hC]
  rfl

/-- **Base change preserves every cohomological dimension.** -/
lemma finrank_cechHgr_baseChange (i : ℕ) (d : ℤ) :
    Module.finrank k' (((M.baseChange k').cechHgr i).obj d)
      = Module.finrank k ((M.cechHgr i).obj d) := by
  rw [(cechHgrBaseChangeEquiv k' M i d).finrank_eq]
  exact Module.finrank_baseChange

/-- **Base change is faithfully flat, so vanishing may be checked after base change.** -/
lemma subsingleton_cechHgr_baseChange_iff (i : ℕ) (d : ℤ) :
    Subsingleton (((M.baseChange k').cechHgr i).obj d)
      ↔ Subsingleton ((M.cechHgr i).obj d) := by
  rw [(cechHgrBaseChangeEquiv k' M i d).toEquiv.subsingleton_congr]
  exact subsingleton_baseChange_iff k'

/-- **Base change commutes with graded Čech cohomology, as graded modules.** -/
noncomputable def cechHgrBaseChangeHom (i : ℕ) :
    (M.baseChange k').cechHgr i ⟶ (M.cechHgr i).baseChange k' where
  app d := ModuleCat.ofHom (cechHgrBaseChangeEquiv k' M i d).toLinearMap
  comm j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (cechHgrBaseChangeEquiv_mulX k' M i j d x).symm

noncomputable def cechHgrBaseChangeIso (i : ℕ) :
    (M.baseChange k').cechHgr i ≅ (M.cechHgr i).baseChange k' :=
  isoOfBijective (cechHgrBaseChangeHom k' M i)
    (fun d => (cechHgrBaseChangeEquiv k' M i d).bijective)

/-- **Base change preserves and reflects the multiplication spans of graded Čech
cohomology.** -/
lemma mulSpan_cechHgr_baseChange_iff (i : ℕ) (d e : ℤ) :
    ((M.baseChange k').cechHgr i).mulSpan d e = ⊤
      ↔ (M.cechHgr i).mulSpan d e = ⊤ := by
  constructor
  · intro h
    exact (mulSpan_baseChange_iff k' (M.cechHgr i) d e).mp
      (mulSpan_eq_top_of_iso (cechHgrBaseChangeIso k' M i) d e h)
  · intro h
    exact mulSpan_eq_top_of_iso (cechHgrBaseChangeIso k' M i).symm d e
      ((mulSpan_baseChange_iff k' (M.cechHgr i) d e).mpr h)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open GradedModule

/-- **Flat base change for the Čech cohomology theory along a field extension.**

Every field extension `k ⊆ k'` induces a packaged base change
`Cohomology.BaseChange (Cohomology.cech k) (Cohomology.cech k')`, given on sheaves by
`M ↦ k' ⊗_k M`. The five fields are the faithful flatness of `k → k'` applied to the
Čech complex: `k' ⊗_k -` is exact, so it commutes with the homology of the Čech complex
(`GradedModule.cechHgrBaseChangeIso`), and a `k'`-vector space `k' ⊗_k V` has the same
dimension as `V` and vanishes exactly when `V` does. -/
noncomputable def cechBaseChange (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Cohomology.BaseChange (Cohomology.cech k) (Cohomology.cech k') where
  obj M := M.baseChange k'
  isCoherent _ hM := IsFG.baseChange k' hM
  finrank_eq M i d := finrank_cechHgr_baseChange k' M i d
  subsingleton_iff M i d := subsingleton_cechHgr_baseChange_iff k' M i d
  mulSpan_iff M i d e := mulSpan_cechHgr_baseChange_iff k' M i d e
  isGloballyGenerated_iff M d := by
    constructor
    · rintro ⟨e₀, he⟩
      exact ⟨e₀, fun e hee => (mulSpan_cechHgr_baseChange_iff k' M 0 d e).mp (he e hee)⟩
    · rintro ⟨e₀, he⟩
      exact ⟨e₀, fun e hee => (mulSpan_cechHgr_baseChange_iff k' M 0 d e).mpr (he e hee)⟩
  mono f hf := exists_mono_baseChange k' f hf

/-- **The canonical Čech cohomology theory satisfies the infinite-base-field reduction.**
Take `k' = k(t)`, which is infinite and is a field extension of `k` in the same universe. -/
theorem hasInfiniteBaseChange_cech (k : Type u) [Field k] :
    (Cohomology.cech k).HasInfiniteBaseChange := by
  let _ : Infinite (RatFunc k) := Cohomology.infinite_ratFunc k
  exact ⟨RatFunc k, inferInstance, Cohomology.cech (RatFunc k), inferInstance,
    ⟨cechBaseChange k (RatFunc k)⟩⟩

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
