module

public import StacksAndModuli.API.ProjTwistII514Global
public import StacksAndModuli.API.ProjGammaStar
public import StacksAndModuli.API.ProjectiveGradedLocalization
public import StacksAndModuli.API.ProjectiveGradedCech

/-!
# `Γ_*(F)` localized at a variable is the sections on the chart

Hartshorne II.5.14 says that `Γ(D₊(xᵢ), F(d))` is the degree-`d` piece of `Γ_*(F)` localized away
from `xᵢ`.  In the graded model of `API/ProjectiveGradedLocalization.lean` that localization is the
sequential direct limit

`(Γ_*(F).loc [i]).obj d = colimⱼ Γ(Proj 𝒜, F(locDeg [i] d j))`

along multiplication by `xᵢ`.  This file provides the `R`-linear plumbing needed to compare that
direct limit with `Γ(D₊(xᵢ), F(d))`:

* `Scheme.Modules.openSectionsLinearMap`, `Scheme.Modules.resFromTopLinearMap` — the `R`-linear
  structure on sections over an open, and on restriction from `⊤`;
* `AlgebraicGeometry.Proj.gammaStar_mulX'`, `gammaStar_mulList_listPow`, `gammaStar_locTr` — the
  transition maps of the localization tower, identified with multiplication by a power of `xᵢ`
  at the sheaf level.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false
set_option linter.style.show false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring map from the base ring of a scheme over `Spec R` to the functions on an open. -/
noncomputable def openRingHom (f : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  baseRingHom f ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op

/-- Sections over an open of a scheme over `Spec R`, as an `R`-module.

Not an instance: it depends on the chosen morphism `f`.  For `U = ⊤` it is propositionally but
not definitionally `globalSectionsModule f M`, so the two are never mixed. -/
@[instance_reducible]
noncomputable def openSectionsModuleOver (f : X ⟶ Spec R) (M : X.Modules) (U : X.Opens) :
    Module R Γ(M, U) :=
  Module.compHom _ (openRingHom f U).hom

/-- A morphism of module sheaves induces an `R`-linear map on sections over any open. -/
noncomputable def openSectionsLinearMap (f : X ⟶ Spec R) {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) :
    letI := openSectionsModuleOver f M U
    letI := openSectionsModuleOver f N U
    Γ(M, U) →ₗ[R] Γ(N, U) := by
  letI := openSectionsModuleOver f M U
  letI := openSectionsModuleOver f N U
  exact
    { toFun := Scheme.Modules.Hom.app φ U
      map_add' := map_add _
      map_smul' := fun r s ↦ Scheme.Modules.Hom.app_smul φ ((openRingHom f U).hom r) s }

@[simp]
theorem openSectionsLinearMap_apply (f : X ⟶ Spec R) {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    letI := openSectionsModuleOver f M U
    letI := openSectionsModuleOver f N U
    openSectionsLinearMap f φ U s = Scheme.Modules.Hom.app φ U s := rfl

/-- Restriction from global sections to an open is `R`-linear. -/
noncomputable def resFromTopLinearMap (f : X ⟶ Spec R) (M : X.Modules) (U : X.Opens) :
    letI := globalSectionsModule f M
    letI := openSectionsModuleOver f M U
    Γ(M, ⊤) →ₗ[R] Γ(M, U) := by
  letI := globalSectionsModule f M
  letI := openSectionsModuleOver f M U
  exact
    { toFun := M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        change M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ((baseRingHom f).hom r • s)
          = ((openRingHom f U).hom r) • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s
        rw [M.map_smul]
        rfl }

@[simp]
theorem resFromTopLinearMap_apply (f : X ⟶ Spec R) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, ⊤)) :
    letI := globalSectionsModule f M
    letI := openSectionsModuleOver f M U
    resFromTopLinearMap f M U s = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

open AlgebraicGeometry.ProjectiveSpace

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-raising map of `Γ_*(F)` is multiplication by `xᵢ` at the sheaf level.

Stated pointwise: an equality of `ModuleCat R` morphisms would have to name the `Module R`
instance coming from `Scheme.Modules.globalSectionsModule`, whereas
`Scheme.Modules.Hom.app` mentions no instance at all. -/
theorem gammaStar_mulX'_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) (d e : ℤ)
    (h : d + 1 = e) (h' : e = d + ((1 : ℕ) : ℤ))
    (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤)) :
    ((gammaStar 𝒜 f F x).mulX' i d e h).hom s
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (x i) d e h') ⊤ s := by
  subst h
  rw [GradedModule.mulX'_rfl]
  rfl

/-- Iterated multiplication by `xᵢ` in `Γ_*(F)` is multiplication by `xᵢ^m` at the sheaf level. -/
theorem gammaStar_mulList_listPow_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) (d : ℤ) :
    ∀ (m : ℕ) (e : ℤ) (h : d + ((GradedModule.listPow [i] m).length : ℤ) = e)
      (hxm : ((x i : A)) ^ m ∈ 𝒜 m) (h' : e = d + (m : ℤ))
      (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤)),
      ((gammaStar 𝒜 f F x).mulList (GradedModule.listPow [i] m) d e h).hom s
        = Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
              (⟨((x i : A)) ^ m, hxm⟩ : 𝒜 m) d e h') ⊤ s := by
  intro m
  induction m with
  | zero =>
    intro e h hxm h' s
    have hde : d = e := by simpa using h
    subst hde
    rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨((x i : A)) ^ 0, hxm⟩ : 𝒜 0) (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0)
        (pow_zero _) d d h' h',
      ProjectiveSpectrum.Twist.twistModuleMulHom_one]
    simp [GradedModule.mulList]
  | succ m ih =>
    intro e h hxm h' s
    have hxm1 : ((x i : A)) ^ m ∈ 𝒜 m := by simpa using SetLike.pow_mem_graded _ (x i).2
    have hx1 : ((x i : A)) ^ 1 ∈ 𝒜 1 := by rw [pow_one]; exact (x i).2
    have hone : GradedModule.listPow ([i] : List (Fin (n + 1))) 1 = [i] := by
      simp [GradedModule.listPow]
    have hlen : GradedModule.listPow ([i] : List (Fin (n + 1))) (m + 1)
        = GradedModule.listPow ([i] : List (Fin (n + 1))) m ++ [i] := by
      rw [GradedModule.listPow_add, hone]
    have h1 : d + ((GradedModule.listPow ([i] : List (Fin (n + 1))) m).length : ℤ)
        = d + (m : ℤ) := by simp
    have h2 : (d + (m : ℤ)) + (([i] : List (Fin (n + 1))).length : ℤ) = e := by
      rw [h']; simp only [List.length_singleton]; push_cast; ring
    have happ : d + (((GradedModule.listPow ([i] : List (Fin (n + 1))) m ++ [i]) :
        List (Fin (n + 1))).length : ℤ) = e := by rw [← hlen]; exact h
    rw [GradedModule.mulList_congr_list _ hlen d e h happ,
      GradedModule.mulList_append _ _ _ d (d + (m : ℤ)) e h1 h2 happ,
      ModuleCat.hom_comp, LinearMap.comp_apply,
      ih (d + (m : ℤ)) h1 hxm1 rfl s,
      GradedModule.mulList_singleton,
      gammaStar_mulX'_apply 𝒜 f F x i (d + (m : ℤ)) e (by simpa using h2)
        (by rw [h']; push_cast; ring),
      ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F (x i)
        (⟨((x i : A)) ^ 1, hx1⟩ : 𝒜 1) (pow_one _).symm (d + (m : ℤ)) e
        (by rw [h']; push_cast; ring) (by rw [h']; push_cast; ring)]
    exact app_twistModuleMulHom_pow_add 𝒜 F d ⊤ m 1 hxm1 hx1 hxm (d + (m : ℤ)) e
      rfl h' (by rw [h']; push_cast; ring) s

/-- The transition map of the localization tower of `Γ_*(F)` at `xᵢ` is multiplication by a
power of `xᵢ` at the sheaf level. -/
theorem gammaStar_locTr_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) (d : ℤ)
    (j j' : ℕ) (hjj : j ≤ j') (hxk : ((x i : A)) ^ (j' - j) ∈ 𝒜 (j' - j))
    (h' : GradedModule.locDeg [i] d j'
      = GradedModule.locDeg [i] d j + ((j' - j : ℕ) : ℤ))
    (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j), ⊤)) :
    (((gammaStar 𝒜 f F x).locTr [i] d j j' hjj).hom) s
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨((x i : A)) ^ (j' - j), hxk⟩ : 𝒜 (j' - j))
            (GradedModule.locDeg [i] d j) (GradedModule.locDeg [i] d j') h') ⊤ s := by
  rw [GradedModule.locTr]
  exact gammaStar_mulList_listPow_apply 𝒜 f F x i _ (j' - j) _ _ hxk h' s

/-- The monomial attached to a list of variables. -/
def varProd {n : ℕ} (x : Fin (n + 1) → 𝒜 1) (l : List (Fin (n + 1))) : A :=
  (l.map (fun k ↦ ((x k : A)))).prod

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp] theorem varProd_nil {n : ℕ} (x : Fin (n + 1) → 𝒜 1) :
    varProd 𝒜 x ([] : List (Fin (n + 1))) = 1 := rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp] theorem varProd_cons {n : ℕ} (x : Fin (n + 1) → 𝒜 1) (k : Fin (n + 1))
    (l : List (Fin (n + 1))) :
    varProd 𝒜 x (k :: l) = ((x k : A)) * varProd 𝒜 x l := rfl

theorem varProd_mem {n : ℕ} (x : Fin (n + 1) → 𝒜 1) :
    ∀ l : List (Fin (n + 1)), varProd 𝒜 x l ∈ 𝒜 l.length
  | [] => by simpa using SetLike.one_mem_graded 𝒜
  | k :: l => by
    rw [varProd_cons, List.length_cons, Nat.add_comm]
    exact SetLike.mul_mem_graded (x k).2 (varProd_mem x l)

/-- **Iterated multiplication in `Γ_*(F)` is multiplication by the monomial.**  The general form
of `gammaStar_mulList_listPow_apply`, needed for the multi-variable charts of the Čech complex. -/
theorem gammaStar_mulList_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ) (h : d + (l.length : ℤ) = e)
      (hp : varProd 𝒜 x l ∈ 𝒜 l.length) (h' : e = d + ((l.length : ℕ) : ℤ))
      (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤)),
      ((gammaStar 𝒜 f F x).mulList l d e h).hom s
        = Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
              (⟨varProd 𝒜 x l, hp⟩ : 𝒜 l.length) d e h') ⊤ s := by
  intro l
  induction l with
  | nil =>
    intro d e h hp h' s
    have hde : d = e := by simpa using h
    subst hde
    rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨varProd 𝒜 x ([] : List (Fin (n + 1))), hp⟩ : 𝒜 ([] : List (Fin (n + 1))).length)
        (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) rfl d d h' h',
      ProjectiveSpectrum.Twist.twistModuleMulHom_one]
    simp [GradedModule.mulList]
  | cons k l ih =>
    intro d e h hp h' s
    have hl : d + 1 + (l.length : ℤ) = e := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
      omega
    have hl' : e = (d + 1) + ((l.length : ℕ) : ℤ) := by omega
    have hd1 : d + 1 = d + ((1 : ℕ) : ℤ) := by push_cast; ring
    rw [GradedModule.mulList, ModuleCat.hom_comp, LinearMap.comp_apply,
      show ((gammaStar 𝒜 f F x).mulX k d).hom s
        = Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (x k) d (d + 1) hd1) ⊤ s from rfl,
      ih (d + 1) e hl (varProd_mem 𝒜 x l) hl',
      ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨varProd 𝒜 x (k :: l), hp⟩ : 𝒜 (k :: l).length)
        (⟨((x k : A)) * varProd 𝒜 x l,
          SetLike.mul_mem_graded (x k).2 (varProd_mem 𝒜 x l)⟩ : 𝒜 (1 + l.length))
        rfl d e h' (by rw [h']; simp only [List.length_cons]; push_cast; ring),
      ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (x k)
        (⟨varProd 𝒜 x l, varProd_mem 𝒜 x l⟩ : 𝒜 l.length) d (d + 1) e hd1 hl'
        (by rw [h']; simp only [List.length_cons]; push_cast; ring),
      Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp] theorem varProd_append {n : ℕ} (x : Fin (n + 1) → 𝒜 1) (l₁ l₂ : List (Fin (n + 1))) :
    varProd 𝒜 x (l₁ ++ l₂) = varProd 𝒜 x l₁ * varProd 𝒜 x l₂ := by
  simp [varProd]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem varProd_listPow {n : ℕ} (x : Fin (n + 1) → 𝒜 1) (l : List (Fin (n + 1))) (m : ℕ) :
    varProd 𝒜 x (GradedModule.listPow l m) = (varProd 𝒜 x l) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hone : GradedModule.listPow l 1 = l := by simp [GradedModule.listPow]
    rw [GradedModule.listPow_add, hone, varProd_append, ih, pow_succ]

/-- The transition maps of the localization tower at an arbitrary list of variables are
multiplication by the corresponding monomial. -/
theorem gammaStar_locTr_apply' {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (l : List (Fin (n + 1))) (d : ℤ)
    (t t' : ℕ) (htt : t ≤ t')
    (hp : varProd 𝒜 x (GradedModule.listPow l (t' - t))
      ∈ 𝒜 (GradedModule.listPow l (t' - t)).length)
    (h' : GradedModule.locDeg l d t' = GradedModule.locDeg l d t
      + (((GradedModule.listPow l (t' - t)).length : ℕ) : ℤ))
    (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg l d t), ⊤)) :
    (((gammaStar 𝒜 f F x).locTr l d t t' htt).hom) s
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨varProd 𝒜 x (GradedModule.listPow l (t' - t)), hp⟩ :
              𝒜 (GradedModule.listPow l (t' - t)).length)
            (GradedModule.locDeg l d t) (GradedModule.locDeg l d t') h') ⊤ s := by
  rw [GradedModule.locTr]
  exact gammaStar_mulList_apply 𝒜 f F x _ _ _ _ hp h' s

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem varProd_listPow_mul {n : ℕ} (x : Fin (n + 1) → 𝒜 1) (l : List (Fin (n + 1)))
    (t t' : ℕ) (h : t ≤ t') :
    varProd 𝒜 x (GradedModule.listPow l t) * varProd 𝒜 x (GradedModule.listPow l (t' - t))
      = varProd 𝒜 x (GradedModule.listPow l t') := by
  rw [← varProd_append, ← GradedModule.listPow_add, Nat.add_sub_cancel' h]

theorem locDeg_eq_length {n : ℕ} (l : List (Fin (n + 1))) (d : ℤ) (t : ℕ) :
    GradedModule.locDeg l d t = d + (((GradedModule.listPow l t).length : ℕ) : ℤ) := by
  simp only [GradedModule.locDeg_def, GradedModule.listPow_length]
  push_cast
  ring

theorem locDeg_add_length {n : ℕ} (l : List (Fin (n + 1))) (d : ℤ) (t t' : ℕ) (h : t ≤ t') :
    GradedModule.locDeg l d t'
      = GradedModule.locDeg l d t + (((GradedModule.listPow l (t' - t)).length : ℕ) : ℤ) := by
  simp only [GradedModule.locDeg_def, GradedModule.listPow_length]
  push_cast [Nat.cast_sub h]
  ring

/-! ## The comparison with sections on the chart -/

variable {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R) (F : (Proj 𝒜).Modules)
  (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1))

/-- Powers of a variable are homogeneous of the matching degree. -/
theorem pow_var_mem (k : ℕ) : ((x i : A)) ^ k ∈ 𝒜 k := by
  simpa using SetLike.pow_mem_graded _ (x i).2

/-- The stages of the localization tower at `xᵢ` sit in degrees `d + j`. -/
theorem locDeg_singleton (d : ℤ) (j : ℕ) :
    GradedModule.locDeg [i] d j = d + (j : ℤ) := by
  simp [GradedModule.locDeg]

/-- **The chart trivialization as an `R`-linear equivalence.**  On `D₊(xᵢ)`, multiplication by
`xᵢ^k` identifies the sections of `F(d)` with those of `F(d + k)`. -/
noncomputable def chartTwistLinearEquiv (d : ℤ) (k : ℕ) (ec : ℤ) (hec : ec = d + (k : ℤ)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec) (basicOpen 𝒜 ((x i : A)))
    Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, basicOpen 𝒜 ((x i : A)))
      ≃ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F ec, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec) (basicOpen 𝒜 ((x i : A)))
  exact LinearEquiv.ofBijective
    (Scheme.Modules.openSectionsLinearMap π
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
        (⟨((x i : A)) ^ k, pow_var_mem 𝒜 x i k⟩ : 𝒜 k) d ec hec) (basicOpen 𝒜 ((x i : A))))
    (bijective_app_twistModuleMulHom_natPow 𝒜 (x i).2 F d k (pow_var_mem 𝒜 x i k) ec hec _ le_rfl)

@[simp]
theorem chartTwistLinearEquiv_apply (d : ℤ) (k : ℕ) (ec : ℤ) (hec : ec = d + (k : ℤ))
    (v : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, basicOpen 𝒜 ((x i : A)))) :
    chartTwistLinearEquiv 𝒜 π F x i d k ec hec v
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨((x i : A)) ^ k, pow_var_mem 𝒜 x i k⟩ : 𝒜 k) d ec hec)
          (basicOpen 𝒜 ((x i : A))) v := rfl

/-- The stage-`j` comparison map: restrict to the chart and divide by `xᵢ^j`. -/
noncomputable def chartStageMap (d : ℤ) (j : ℕ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j)
      →ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j))
    (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.globalSectionsModule π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j))
  exact
    (chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
        (locDeg_singleton i d j)).symm.toLinearMap ∘ₗ
      Scheme.Modules.resFromTopLinearMap π
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j))
        (basicOpen 𝒜 ((x i : A)))

@[simp]
theorem chartStageMap_apply (d : ℤ) (j : ℕ)
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j)) :
    chartStageMap 𝒜 π F x i d j z
      = (chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
          (locDeg_singleton i d j)).symm
        ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z) := rfl

/-- Passing from stage `j` to stage `j'` of the chart trivialization is multiplication by
`xᵢ^{j'-j}`. -/
theorem chartTwist_symm_trans (d : ℤ) (j j' : ℕ) (hjj : j ≤ j')
    (hd1 : GradedModule.locDeg [i] d j'
      = GradedModule.locDeg [i] d j + ((j' - j : ℕ) : ℤ))
    (w : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d j),
      basicOpen 𝒜 ((x i : A)))) :
    chartTwistLinearEquiv 𝒜 π F x i d j' (GradedModule.locDeg [i] d j')
        (locDeg_singleton i d j')
        ((chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
          (locDeg_singleton i d j)).symm w)
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨((x i : A)) ^ (j' - j), pow_var_mem 𝒜 x i (j' - j)⟩ : 𝒜 (j' - j))
            (GradedModule.locDeg [i] d j) (GradedModule.locDeg [i] d j') hd1)
          (basicOpen 𝒜 ((x i : A))) w := by
  have hec : GradedModule.locDeg [i] d j' = d + ((j + (j' - j) : ℕ) : ℤ) := by
    rw [Nat.add_sub_cancel' hjj]
    exact locDeg_singleton i d j'
  conv_rhs => rw [← LinearEquiv.apply_symm_apply
    (chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
      (locDeg_singleton i d j)) w]
  generalize (chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
    (locDeg_singleton i d j)).symm w = u
  rw [chartTwistLinearEquiv_apply, chartTwistLinearEquiv_apply,
    app_twistModuleMulHom_pow_add 𝒜 F d (basicOpen 𝒜 ((x i : A))) j (j' - j)
      (pow_var_mem 𝒜 x i j) (pow_var_mem 𝒜 x i (j' - j)) (pow_var_mem 𝒜 x i (j + (j' - j)))
      (GradedModule.locDeg [i] d j) (GradedModule.locDeg [i] d j')
      (locDeg_singleton i d j) hec hd1 u,
    ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨((x i : A)) ^ j', pow_var_mem 𝒜 x i j'⟩ : 𝒜 j')
      (⟨((x i : A)) ^ (j + (j' - j)), pow_var_mem 𝒜 x i (j + (j' - j))⟩ : 𝒜 (j + (j' - j)))
      (by rw [Nat.add_sub_cancel' hjj]) d (GradedModule.locDeg [i] d j')
      (locDeg_singleton i d j') hec]

/-- The degree bookkeeping of the localization tower at a single variable. -/
theorem locDeg_sub (d : ℤ) (j j' : ℕ) (hjj : j ≤ j') :
    GradedModule.locDeg [i] d j' = GradedModule.locDeg [i] d j + ((j' - j : ℕ) : ℤ) := by
  rw [locDeg_singleton i d j, locDeg_singleton i d j', Nat.cast_sub hjj]
  ring

/-- **The stage maps are compatible with the tower.**  This is the hypothesis of
`Module.DirectLimit.lift`. -/
theorem chartStageMap_locTr (d : ℤ) (j j' : ℕ) (hjj : j ≤ j')
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j)) :
    chartStageMap 𝒜 π F x i d j' (((gammaStar 𝒜 π F x).locTr [i] d j j' hjj).hom z)
      = chartStageMap 𝒜 π F x i d j z := by
  refine (chartTwistLinearEquiv 𝒜 π F x i d j' (GradedModule.locDeg [i] d j')
    (locDeg_singleton i d j')).injective ?_
  rw [chartStageMap_apply, chartStageMap_apply, LinearEquiv.apply_symm_apply,
    chartTwist_symm_trans 𝒜 π F x i d j j' hjj (locDeg_sub i d j j' hjj),
    gammaStar_locTr_apply 𝒜 π F x i d j j' hjj (pow_var_mem 𝒜 x i (j' - j))
      (locDeg_sub i d j j' hjj) z,
    ← Scheme.Modules.app_restrict]

/-- **The comparison map.**  From `Γ_*(F)` localized at `xᵢ`, in degree `d`, to the sections of
`F(d)` on the chart `D₊(xᵢ)`: restrict to the chart and divide by the appropriate power of
`xᵢ`. -/
noncomputable def chartColimitMap (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    ((gammaStar 𝒜 π F x).loc [i]).obj d
      →ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  exact Module.DirectLimit.lift R ℕ
    (fun j : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j))
    (fun j j' h ↦ ((gammaStar 𝒜 π F x).locTr [i] d j j' h).hom)
    (chartStageMap 𝒜 π F x i d)
    (fun j j' h z ↦ chartStageMap_locTr 𝒜 π F x i d j j' h z)

theorem chartColimitMap_of (d : ℤ) (j : ℕ)
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    chartColimitMap 𝒜 π F x i d
        (Module.DirectLimit.of R ℕ
          (fun j : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j))
          (fun j j' h ↦ ((gammaStar 𝒜 π F x).locTr [i] d j j' h).hom) j z)
      = chartStageMap 𝒜 π F x i d j z := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  exact Module.DirectLimit.lift_of _ _ _

/-- **Hartshorne II.5.14, in the graded model.**  The localization of `Γ_*(F)` at the variable
`xᵢ` is, in each degree, the sections of the corresponding twist on the chart `D₊(xᵢ)`. -/
theorem bijective_chartColimitMap
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    Function.Bijective (chartColimitMap 𝒜 π F x i d) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  constructor
  · refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun w hw ↦ ?_)
    obtain ⟨j, z, rfl⟩ := Module.DirectLimit.exists_of w
    rw [chartColimitMap_of, chartStageMap_apply] at hw
    have hres : (ProjectiveSpectrum.Twist.twistModule 𝒜 F
        (GradedModule.locDeg [i] d j)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z = 0 := by
      have := congrArg (chartTwistLinearEquiv 𝒜 π F x i d j (GradedModule.locDeg [i] d j)
        (locDeg_singleton i d j)) hw
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    obtain ⟨N, hN⟩ := exists_pow_app_top_eq_zero 𝒜 (fun k ↦ ((x k : A))) (fun k ↦ (x k).2)
      hcover F (GradedModule.locDeg [i] d j) i z hres
    have hsub : j + N - j = N := by omega
    have hzero : ((gammaStar 𝒜 π F x).locTr [i] d j (j + N) (Nat.le_add_right j N)).hom z = 0 := by
      rw [gammaStar_locTr_apply 𝒜 π F x i d j (j + N) (Nat.le_add_right j N)
        (pow_var_mem 𝒜 x i (j + N - j)) (locDeg_sub i d j (j + N) (Nat.le_add_right j N))]
      have hg := hN (pow_var_mem 𝒜 x i N) (GradedModule.locDeg [i] d (j + N))
        (by rw [locDeg_sub i d j (j + N) (Nat.le_add_right j N), hsub])
      refine Eq.trans (congrArg (fun ψ ↦ Scheme.Modules.Hom.app ψ ⊤ z) ?_) hg
      exact ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨((x i : A)) ^ (j + N - j), pow_var_mem 𝒜 x i (j + N - j)⟩ : 𝒜 (j + N - j))
        (⟨((x i : A)) ^ N, pow_var_mem 𝒜 x i N⟩ : 𝒜 N) (by rw [hsub]) _ _ _ _
    rw [← Module.DirectLimit.of_f (hij := Nat.le_add_right j N), hzero, map_zero]
  · intro u
    obtain ⟨L, hgL, hs⟩ := exists_global_lift' 𝒜 (fun k ↦ ((x k : A))) (fun k ↦ (x k).2)
      hcover F d i u
    obtain ⟨s, hsspec⟩ := hs (GradedModule.locDeg [i] d L) (locDeg_singleton i d L)
    refine ⟨Module.DirectLimit.of R ℕ
      (fun j : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j))
      (fun j j' h ↦ ((gammaStar 𝒜 π F x).locTr [i] d j j' h).hom) L s, ?_⟩
    rw [chartColimitMap_of, chartStageMap_apply, hsspec]
    rw [LinearEquiv.symm_apply_eq, chartTwistLinearEquiv_apply]

/-- The comparison of `bijective_chartColimitMap`, as an `R`-linear equivalence. -/
noncomputable def chartColimitEquiv
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    ((gammaStar 𝒜 π F x).loc [i]).obj d
      ≃ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  exact LinearEquiv.ofBijective _ (bijective_chartColimitMap 𝒜 π F x i hcover d)

/-! ## The two-variable charts of the Čech complex -/

variable (j : Fin (n + 1))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem varProd_pair_listPow (t : ℕ) :
    varProd 𝒜 x (GradedModule.listPow [i, j] t) = ((x i : A)) ^ t * ((x j : A)) ^ t := by
  rw [varProd_listPow, show varProd 𝒜 x [i, j] = ((x i : A)) * ((x j : A)) by simp [varProd],
    mul_pow]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem length_pair_listPow (t : ℕ) :
    (GradedModule.listPow [i, j] t).length = t * 2 := by
  simp

/-- On the overlap `D₊(xᵢ) ⊓ D₊(xⱼ)`, multiplication by `(xᵢxⱼ)^t` is bijective. -/
theorem bijective_app_twistModuleMulHom_pair (d : ℤ) (t : ℕ)
    (hp : varProd 𝒜 x (GradedModule.listPow [i, j] t)
      ∈ 𝒜 (GradedModule.listPow [i, j] t).length)
    (ec : ℤ) (hec : ec = d + (((GradedModule.listPow [i, j] t).length : ℕ) : ℤ)) :
    Function.Bijective (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
        (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t), hp⟩ :
          𝒜 (GradedModule.listPow [i, j] t).length) d ec hec)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))) := by
  have hmul : ((x i : A)) ^ t * ((x j : A)) ^ t ∈ 𝒜 (t + t) :=
    SetLike.mul_mem_graded (pow_var_mem 𝒜 x i t) (pow_var_mem 𝒜 x j t)
  have hec' : ec = d + ((t + t : ℕ) : ℤ) := by
    rw [hec, length_pair_listPow]; push_cast; ring
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t), hp⟩ :
      𝒜 (GradedModule.listPow [i, j] t).length)
    (⟨((x i : A)) ^ t * ((x j : A)) ^ t, hmul⟩ : 𝒜 (t + t))
    (varProd_pair_listPow 𝒜 x i j t) d ec hec hec']
  exact bijective_app_twistModuleMulHom_mul 𝒜 (x i).2 (x j).2 F d t hmul ec hec'
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) inf_le_left inf_le_right

/-- The two-variable chart trivialization as an `R`-linear equivalence. -/
noncomputable def pairTwistLinearEquiv (d : ℤ) (t : ℕ) (ec : ℤ)
    (hec : ec = d + (((GradedModule.listPow [i, j] t).length : ℕ) : ℤ)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d,
        basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
      ≃ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F ec,
        basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  exact LinearEquiv.ofBijective
    (Scheme.Modules.openSectionsLinearMap π
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
        (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t),
          varProd_mem 𝒜 x _⟩ : 𝒜 (GradedModule.listPow [i, j] t).length) d ec hec)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))))
    (bijective_app_twistModuleMulHom_pair 𝒜 F x i j d t (varProd_mem 𝒜 x _) ec hec)

@[simp]
theorem pairTwistLinearEquiv_apply (d : ℤ) (t : ℕ) (ec : ℤ)
    (hec : ec = d + (((GradedModule.listPow [i, j] t).length : ℕ) : ℤ))
    (v : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d,
      basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))) :
    pairTwistLinearEquiv 𝒜 π F x i j d t ec hec v
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t),
              varProd_mem 𝒜 x _⟩ : 𝒜 (GradedModule.listPow [i, j] t).length) d ec hec)
          (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) v := rfl

/-- The stage-`t` comparison map for the two-variable chart. -/
noncomputable def pairStageMap (d : ℤ) (t : ℕ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t)
      →ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d,
        basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i, j] d t))
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  letI := Scheme.Modules.globalSectionsModule π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i, j] d t))
  exact
    (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
        (locDeg_eq_length [i, j] d t)).symm.toLinearMap ∘ₗ
      Scheme.Modules.resFromTopLinearMap π
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i, j] d t))
        (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))

theorem pairStageMap_apply (d : ℤ) (t : ℕ)
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t)) :
    pairStageMap 𝒜 π F x i j d t z
      = (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
          (locDeg_eq_length [i, j] d t)).symm
        ((ProjectiveSpectrum.Twist.twistModule 𝒜 F
          (GradedModule.locDeg [i, j] d t)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z) := rfl

/-- Passing from stage `t` to stage `t'` on the two-variable chart is multiplication by
`(xᵢxⱼ)^{t'-t}`. -/
theorem pairTwist_symm_trans (d : ℤ) (t t' : ℕ) (htt : t ≤ t')
    (w : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i, j] d t),
      basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))) :
    pairTwistLinearEquiv 𝒜 π F x i j d t' (GradedModule.locDeg [i, j] d t')
        (locDeg_eq_length [i, j] d t')
        ((pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
          (locDeg_eq_length [i, j] d t)).symm w)
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨varProd 𝒜 x (GradedModule.listPow [i, j] (t' - t)), varProd_mem 𝒜 x _⟩ :
              𝒜 (GradedModule.listPow [i, j] (t' - t)).length)
            (GradedModule.locDeg [i, j] d t) (GradedModule.locDeg [i, j] d t')
            (locDeg_add_length [i, j] d t t' htt))
          (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) w := by
  conv_rhs => rw [← LinearEquiv.apply_symm_apply
    (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
      (locDeg_eq_length [i, j] d t)) w]
  generalize (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
    (locDeg_eq_length [i, j] d t)).symm w = u
  rw [pairTwistLinearEquiv_apply, pairTwistLinearEquiv_apply]
  exact (app_twistModuleMulHom_mul_eq 𝒜 F d
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t), varProd_mem 𝒜 x _⟩ :
      𝒜 (GradedModule.listPow [i, j] t).length)
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] (t' - t)), varProd_mem 𝒜 x _⟩ :
      𝒜 (GradedModule.listPow [i, j] (t' - t)).length)
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t'), varProd_mem 𝒜 x _⟩ :
      𝒜 (GradedModule.listPow [i, j] t').length)
    (varProd_listPow_mul 𝒜 x [i, j] t t' htt)
    (GradedModule.locDeg [i, j] d t) (GradedModule.locDeg [i, j] d t')
    (locDeg_eq_length [i, j] d t) (locDeg_add_length [i, j] d t t' htt)
    (locDeg_eq_length [i, j] d t') u).symm

/-- The two-variable stage maps are compatible with the tower. -/
theorem pairStageMap_locTr (d : ℤ) (t t' : ℕ) (htt : t ≤ t')
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t)) :
    pairStageMap 𝒜 π F x i j d t' (((gammaStar 𝒜 π F x).locTr [i, j] d t t' htt).hom z)
      = pairStageMap 𝒜 π F x i j d t z := by
  refine (pairTwistLinearEquiv 𝒜 π F x i j d t' (GradedModule.locDeg [i, j] d t')
    (locDeg_eq_length [i, j] d t')).injective ?_
  rw [pairStageMap_apply, pairStageMap_apply, LinearEquiv.apply_symm_apply,
    pairTwist_symm_trans 𝒜 π F x i j d t t' htt,
    gammaStar_locTr_apply' 𝒜 π F x [i, j] d t t' htt (varProd_mem 𝒜 x _)
      (locDeg_add_length [i, j] d t t' htt) z,
    ← Scheme.Modules.app_restrict]

/-- **The two-variable comparison map.** -/
noncomputable def pairColimitMap (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    ((gammaStar 𝒜 π F x).loc [i, j]).obj d
      →ₗ[R] Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d,
        basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  exact Module.DirectLimit.lift R ℕ
    (fun t : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t))
    (fun t t' h ↦ ((gammaStar 𝒜 π F x).locTr [i, j] d t t' h).hom)
    (pairStageMap 𝒜 π F x i j d)
    (fun t t' h z ↦ pairStageMap_locTr 𝒜 π F x i j d t t' h z)

theorem pairColimitMap_of (d : ℤ) (t : ℕ)
    (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    pairColimitMap 𝒜 π F x i j d
        (Module.DirectLimit.of R ℕ
          (fun t : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d t))
          (fun t t' h ↦ ((gammaStar 𝒜 π F x).locTr [i, j] d t t' h).hom) t z)
      = pairStageMap 𝒜 π F x i j d t z := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  exact Module.DirectLimit.lift_of _ _ _

/-- **The two-variable comparison map is injective.**  This is all that the Čech `H⁰`
computation needs from the overlaps: the kernel of the Čech differential is detected inside
`∏ᵢⱼ Γ(D₊(xᵢ) ⊓ D₊(xⱼ), F(d))`. -/
theorem injective_pairColimitMap
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    Function.Injective (pairColimitMap 𝒜 π F x i j d) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun w hw ↦ ?_)
  obtain ⟨t, z, rfl⟩ := Module.DirectLimit.exists_of w
  rw [pairColimitMap_of, pairStageMap_apply] at hw
  have hres : (ProjectiveSpectrum.Twist.twistModule 𝒜 F
      (GradedModule.locDeg [i, j] d t)).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z = 0 := by
    have hap := congrArg (pairTwistLinearEquiv 𝒜 π F x i j d t
      (GradedModule.locDeg [i, j] d t) (locDeg_eq_length [i, j] d t)) hw
    rwa [LinearEquiv.apply_symm_apply, map_zero] at hap
  obtain ⟨N, hN⟩ := exists_pow_app_top_eq_zero_pair 𝒜 (fun k ↦ ((x k : A)))
    (fun k ↦ (x k).2) hcover F (GradedModule.locDeg [i, j] d t) i j z hres
  have hsub : t + N - t = N := by omega
  have hmul : ((x i : A)) ^ N * ((x j : A)) ^ N ∈ 𝒜 (N + N) :=
    SetLike.mul_mem_graded (pow_var_mem 𝒜 x i N) (pow_var_mem 𝒜 x j N)
  have hdeg : GradedModule.locDeg [i, j] d (t + N)
      = GradedModule.locDeg [i, j] d t + ((N + N : ℕ) : ℤ) := by
    simp only [GradedModule.locDeg_def, List.length_cons, List.length_nil]
    push_cast
    ring
  have hzero : ((gammaStar 𝒜 π F x).locTr [i, j] d t (t + N)
      (Nat.le_add_right t N)).hom z = 0 := by
    rw [gammaStar_locTr_apply' 𝒜 π F x [i, j] d t (t + N) (Nat.le_add_right t N)
        (varProd_mem 𝒜 x _)
        (locDeg_add_length [i, j] d t (t + N) (Nat.le_add_right t N)) z,
      ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨varProd 𝒜 x (GradedModule.listPow [i, j] (t + N - t)), varProd_mem 𝒜 x _⟩ :
          𝒜 (GradedModule.listPow [i, j] (t + N - t)).length)
        (⟨((x i : A)) ^ N * ((x j : A)) ^ N, hmul⟩ : 𝒜 (N + N))
        (by rw [hsub]; exact varProd_pair_listPow 𝒜 x i j N)
        (GradedModule.locDeg [i, j] d t) (GradedModule.locDeg [i, j] d (t + N))
        (locDeg_add_length [i, j] d t (t + N) (Nat.le_add_right t N)) hdeg]
    exact hN hmul (GradedModule.locDeg [i, j] d (t + N)) hdeg
  rw [← Module.DirectLimit.of_f (hij := Nat.le_add_right t N), hzero, map_zero]

/-- **The comparison squares commute.**  The restriction map `M.loc [i] ⟶ M.loc [i,j]` of the
Čech complex corresponds, under the two comparison maps, to restriction of sections from
`D₊(xᵢ)` to `D₊(xᵢ) ⊓ D₊(xⱼ)`. -/
theorem pairColimitMap_locResApp
    (hp : ([i, j] : List (Fin (n + 1))).Perm ([i] ++ [j])) (d : ℤ)
    (w : ((gammaStar 𝒜 π F x).loc [i]).obj d) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    pairColimitMap 𝒜 π F x i j d (((gammaStar 𝒜 π F x).locResApp [i] hp d).hom w)
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (inf_le_left : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))
            ≤ basicOpen 𝒜 ((x i : A)))).op
          (chartColimitMap 𝒜 π F x i d w) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  obtain ⟨t, z, rfl⟩ := Module.DirectLimit.exists_of w
  have hlr : ((gammaStar 𝒜 π F x).locResApp [i] hp d).hom
      (Module.DirectLimit.of R ℕ
        (fun s : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d s))
        (fun s s' h ↦ ((gammaStar 𝒜 π F x).locTr [i] d s s' h).hom) t z)
      = Module.DirectLimit.of R ℕ
        (fun s : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d s))
        (fun s s' h ↦ ((gammaStar 𝒜 π F x).locTr [i, j] d s s' h).hom) t
        (((gammaStar 𝒜 π F x).mulList (GradedModule.listPow [j] t)
          (GradedModule.locDeg [i] d t) (GradedModule.locDeg [i, j] d t)
          (GradedModule.locRes_stage_degree [i] [i, j] [j] hp d t)).hom z) := by
    have h1 := congrArg
      (fun g : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d t) ⟶
        ((gammaStar 𝒜 π F x).loc [i, j]).obj d ↦ g.hom z)
      (GradedModule.locIncl_locResApp (gammaStar 𝒜 π F x) [i] hp d t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, GradedModule.locIncl,
      ModuleCat.hom_ofHom] at h1
    exact h1
  rw [hlr, pairColimitMap_of, chartColimitMap_of, pairStageMap_apply, chartStageMap_apply]
  refine (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
    (locDeg_eq_length [i, j] d t)).injective ?_
  rw [LinearEquiv.apply_symm_apply, pairTwistLinearEquiv_apply]
  -- name the chart lift `u`
  have hu := LinearEquiv.apply_symm_apply
    (chartTwistLinearEquiv 𝒜 π F x i d t (GradedModule.locDeg [i] d t)
      (locDeg_singleton i d t))
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d t)).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z)
  rw [chartTwistLinearEquiv_apply] at hu
  generalize hudef : (chartTwistLinearEquiv 𝒜 π F x i d t (GradedModule.locDeg [i] d t)
    (locDeg_singleton i d t)).symm
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d t)).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z) = u at hu ⊢
  -- rewrite the left-hand side into a two-step multiplication
  rw [gammaStar_mulList_apply 𝒜 π F x (GradedModule.listPow [j] t)
      (GradedModule.locDeg [i] d t) (GradedModule.locDeg [i, j] d t) _
      (varProd_mem 𝒜 x _)
      (by rw [locDeg_eq_length [i, j] d t, locDeg_eq_length [i] d t]
          simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
          push_cast
          ring) z,
    ← Scheme.Modules.app_restrict,
    show (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [i] d t)).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F
          (GradedModule.locDeg [i] d t)).presheaf.map
          (homOfLE (inf_le_left : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))
            ≤ basicOpen 𝒜 ((x i : A)))).op
        ((ProjectiveSpectrum.Twist.twistModule 𝒜 F
          (GradedModule.locDeg [i] d t)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z) from by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl,
    ← hu, Scheme.Modules.app_restrict,
    ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨varProd 𝒜 x (GradedModule.listPow [j] t), varProd_mem 𝒜 x _⟩ :
        𝒜 (GradedModule.listPow [j] t).length)
      (⟨((x j : A)) ^ t, pow_var_mem 𝒜 x j t⟩ : 𝒜 t)
      (by show varProd 𝒜 x (GradedModule.listPow [j] t) = ((x j : A)) ^ t
          rw [varProd_listPow]
          simp [varProd])
      (GradedModule.locDeg [i] d t) (GradedModule.locDeg [i, j] d t) _
      (by rw [locDeg_eq_length [i, j] d t, locDeg_singleton i d t]
          simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
          push_cast
          ring)]
  rw [← Scheme.Modules.app_restrict, ← Scheme.Modules.app_restrict]
  exact app_twistModuleMulHom_mul_eq 𝒜 F d
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    (⟨((x i : A)) ^ t, pow_var_mem 𝒜 x i t⟩ : 𝒜 t)
    (⟨((x j : A)) ^ t, pow_var_mem 𝒜 x j t⟩ : 𝒜 t)
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t), varProd_mem 𝒜 x _⟩ :
      𝒜 (GradedModule.listPow [i, j] t).length)
    (varProd_pair_listPow 𝒜 x i j t).symm
    (GradedModule.locDeg [i] d t) (GradedModule.locDeg [i, j] d t)
    (locDeg_singleton i d t)
    (by rw [locDeg_eq_length [i, j] d t, locDeg_singleton i d t]
        simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
        push_cast
        ring)
    (locDeg_eq_length [i, j] d t) _

/-- The other comparison square: the restriction `M.loc [j] ⟶ M.loc [i,j]` corresponds to
restriction of sections from `D₊(xⱼ)` to `D₊(xᵢ) ⊓ D₊(xⱼ)`. -/
theorem pairColimitMap_locResApp_right
    (hp : ([i, j] : List (Fin (n + 1))).Perm ([j] ++ [i])) (d : ℤ)
    (w : ((gammaStar 𝒜 π F x).loc [j]).obj d) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x j : A)))
    pairColimitMap 𝒜 π F x i j d (((gammaStar 𝒜 π F x).locResApp [j] hp d).hom w)
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (inf_le_right : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))
            ≤ basicOpen 𝒜 ((x j : A)))).op
          (chartColimitMap 𝒜 π F x j d w) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x j : A)))
  obtain ⟨t, z, rfl⟩ := Module.DirectLimit.exists_of w
  have hlr : ((gammaStar 𝒜 π F x).locResApp [j] hp d).hom
      (Module.DirectLimit.of R ℕ
        (fun s : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [j] d s))
        (fun s s' h ↦ ((gammaStar 𝒜 π F x).locTr [j] d s s' h).hom) t z)
      = Module.DirectLimit.of R ℕ
        (fun s : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i, j] d s))
        (fun s s' h ↦ ((gammaStar 𝒜 π F x).locTr [i, j] d s s' h).hom) t
        (((gammaStar 𝒜 π F x).mulList (GradedModule.listPow [i] t)
          (GradedModule.locDeg [j] d t) (GradedModule.locDeg [i, j] d t)
          (GradedModule.locRes_stage_degree [j] [i, j] [i] hp d t)).hom z) := by
    have h1 := congrArg
      (fun g : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [j] d t) ⟶
        ((gammaStar 𝒜 π F x).loc [i, j]).obj d ↦ g.hom z)
      (GradedModule.locIncl_locResApp (gammaStar 𝒜 π F x) [j] hp d t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, GradedModule.locIncl,
      ModuleCat.hom_ofHom] at h1
    exact h1
  rw [hlr, pairColimitMap_of, chartColimitMap_of, pairStageMap_apply, chartStageMap_apply]
  refine (pairTwistLinearEquiv 𝒜 π F x i j d t (GradedModule.locDeg [i, j] d t)
    (locDeg_eq_length [i, j] d t)).injective ?_
  rw [LinearEquiv.apply_symm_apply, pairTwistLinearEquiv_apply]
  have hu := LinearEquiv.apply_symm_apply
    (chartTwistLinearEquiv 𝒜 π F x j d t (GradedModule.locDeg [j] d t)
      (locDeg_singleton j d t))
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [j] d t)).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z)
  rw [chartTwistLinearEquiv_apply] at hu
  generalize hudef : (chartTwistLinearEquiv 𝒜 π F x j d t (GradedModule.locDeg [j] d t)
    (locDeg_singleton j d t)).symm
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [j] d t)).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z) = u at hu ⊢
  rw [gammaStar_mulList_apply 𝒜 π F x (GradedModule.listPow [i] t)
      (GradedModule.locDeg [j] d t) (GradedModule.locDeg [i, j] d t) _
      (varProd_mem 𝒜 x _)
      (by rw [locDeg_eq_length [i, j] d t, locDeg_eq_length [j] d t]
          simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
          push_cast
          ring) z,
    ← Scheme.Modules.app_restrict,
    show (ProjectiveSpectrum.Twist.twistModule 𝒜 F (GradedModule.locDeg [j] d t)).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F
          (GradedModule.locDeg [j] d t)).presheaf.map
          (homOfLE (inf_le_right : basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A))
            ≤ basicOpen 𝒜 ((x j : A)))).op
        ((ProjectiveSpectrum.Twist.twistModule 𝒜 F
          (GradedModule.locDeg [j] d t)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x j : A)) ≤ ⊤)).op z) from by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl,
    ← hu, Scheme.Modules.app_restrict,
    ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨varProd 𝒜 x (GradedModule.listPow [i] t), varProd_mem 𝒜 x _⟩ :
        𝒜 (GradedModule.listPow [i] t).length)
      (⟨((x i : A)) ^ t, pow_var_mem 𝒜 x i t⟩ : 𝒜 t)
      (by show varProd 𝒜 x (GradedModule.listPow [i] t) = ((x i : A)) ^ t
          rw [varProd_listPow]
          simp [varProd])
      (GradedModule.locDeg [j] d t) (GradedModule.locDeg [i, j] d t) _
      (by rw [locDeg_eq_length [i, j] d t, locDeg_singleton j d t]
          simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
          push_cast
          ring)]
  rw [← Scheme.Modules.app_restrict, ← Scheme.Modules.app_restrict]
  exact app_twistModuleMulHom_mul_eq 𝒜 F d
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    (⟨((x j : A)) ^ t, pow_var_mem 𝒜 x j t⟩ : 𝒜 t)
    (⟨((x i : A)) ^ t, pow_var_mem 𝒜 x i t⟩ : 𝒜 t)
    (⟨varProd 𝒜 x (GradedModule.listPow [i, j] t), varProd_mem 𝒜 x _⟩ :
      𝒜 (GradedModule.listPow [i, j] t).length)
    (by show ((x j : A)) ^ t * ((x i : A)) ^ t
          = varProd 𝒜 x (GradedModule.listPow [i, j] t)
        rw [varProd_pair_listPow]
        ring)
    (GradedModule.locDeg [j] d t) (GradedModule.locDeg [i, j] d t)
    (locDeg_singleton j d t)
    (by rw [locDeg_eq_length [i, j] d t, locDeg_singleton j d t]
        simp only [GradedModule.listPow_length, List.length_cons, List.length_nil]
        push_cast
        ring)
    (locDeg_eq_length [i, j] d t) _

/-! ## The augmentation -/

/-- Multiplication by `a^0` is the degree transport. -/
theorem app_twistModuleMulHom_zero_eq_eqToHom {a : A} (G : (Proj 𝒜).Modules) {d dc : ℤ}
    (h2 : d = dc) (h : dc = d + ((0 : ℕ) : ℤ)) (h0 : a ^ 0 ∈ 𝒜 0) (V : (Proj 𝒜).Opens)
    (v : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 G d, V)) :
    Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 G (⟨a ^ 0, h0⟩ : 𝒜 0) d dc h) V v
      = Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun e : ℤ ↦ ProjectiveSpectrum.Twist.twistModule 𝒜 G e) h2)) V v := by
  subst h2
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 G (⟨a ^ 0, h0⟩ : 𝒜 0)
      (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) (pow_zero a) d d h h,
    ProjectiveSpectrum.Twist.twistModuleMulHom_one]
  simp

/-- The degree transport commutes with restriction. -/
theorem res_app_eqToHom (G : (Proj 𝒜).Modules) {d dc : ℤ} (h2 : d = dc) (V : (Proj 𝒜).Opens)
    (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 G d, ⊤)) :
    (ProjectiveSpectrum.Twist.twistModule 𝒜 G dc).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op
        (Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun e : ℤ ↦ ProjectiveSpectrum.Twist.twistModule 𝒜 G e) h2)) ⊤ t)
      = Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun e : ℤ ↦ ProjectiveSpectrum.Twist.twistModule 𝒜 G e) h2)) V
          ((ProjectiveSpectrum.Twist.twistModule 𝒜 G d).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op t) := by
  subst h2
  rfl

/-- The `ModuleCat`-level degree transport of `Γ_*(F)` is the sheaf-level one. -/
theorem gammaStar_eqToHom_apply {d dc : ℤ} (h2 : d = dc)
    (t : (gammaStar 𝒜 π F x).obj d) :
    (eqToHom (congrArg (gammaStar 𝒜 π F x).obj h2)).hom t
      = Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun e : ℤ ↦ ProjectiveSpectrum.Twist.twistModule 𝒜 F e) h2)) ⊤ t := by
  subst h2
  rfl

/-- **The augmentation is restriction.**  Localizing a global section of `F(d)` at `xᵢ` and
comparing with the chart gives exactly its restriction to `D₊(xᵢ)`. -/
theorem chartColimitMap_locOf (d : ℤ) (t : (gammaStar 𝒜 π F x).obj d) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    chartColimitMap 𝒜 π F x i d ((((gammaStar 𝒜 π F x).locOf [i]).app d).hom t)
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op t := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  have hd0 : d = GradedModule.locDeg [i] d 0 := by
    rw [locDeg_singleton i d 0]; push_cast; ring
  have hof : (((gammaStar 𝒜 π F x).locOf [i]).app d).hom t
      = Module.DirectLimit.of R ℕ
        (fun s : ℕ ↦ (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d s))
        (fun s s' h ↦ ((gammaStar 𝒜 π F x).locTr [i] d s s' h).hom) 0
        ((eqToHom (congrArg (gammaStar 𝒜 π F x).obj hd0)).hom t) := rfl
  rw [hof, chartColimitMap_of, chartStageMap_apply]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  have h1 := gammaStar_eqToHom_apply (h2 := hd0) (t := t)
  have h2 := res_app_eqToHom (G := F) (h2 := hd0)
    (V := basicOpen 𝒜 ((x i : A))) (t := t)
  have h3 := app_twistModuleMulHom_zero_eq_eqToHom (G := F) (h2 := hd0)
    (h := locDeg_singleton i d 0) (h0 := pow_var_mem 𝒜 x i 0)
    (V := basicOpen 𝒜 ((x i : A)))
    (v := (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op t)
  rw [chartTwistLinearEquiv_apply, h3, ← h2, h1]

/-- **The Čech augmentation of `Γ_*(F)` is injective.**  A global section of `F(d)` that dies in
every localization `Γ_*(F)[1/xᵢ]` restricts to zero on every chart, hence is zero.

Note this does *not* go through `GradedModule.injective_cechAug₀`, whose hypothesis — that every
`mulX i` is injective — fails for a general quasicoherent `F` (a sheaf supported on the
hyperplane `xᵢ = 0` has `xᵢ`-torsion global sections). -/
theorem injective_gammaStar_cechAug₀
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    Function.Injective (((gammaStar 𝒜 π F x).cechAug₀ d).hom) := by
  intro t t' h
  refine (Scheme.Modules.abSheaf (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)).eq_of_locally_eq'
    (fun k : Fin (n + 1) ↦ basicOpen 𝒜 ((x k : A))) ⊤
    (fun _ ↦ homOfLE le_top) hcover t t' fun k ↦ ?_
  have hk := congrFun h (GradedModule.CechIdx.zeroIdx (n := n) k)
  have hgoal : (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 ((x k : A)) ≤ ⊤)).op t
      = (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 ((x k : A)) ≤ ⊤)).op t' := by
    rw [← chartColimitMap_locOf 𝒜 π F x k d t, ← chartColimitMap_locOf 𝒜 π F x k d t']
    exact congrArg _ hk
  exact hgoal

/-- **Every Čech `0`-cocycle of `Γ_*(F)` comes from a global section.**  This is the hypothesis of
`GradedModule.surjective_cechAug_of_cocycles`. -/
theorem exists_gammaStar_cechAug₀_eq
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ)
    (c : (gammaStar 𝒜 π F x).cechCochain 0 d)
    (hc : ((gammaStar 𝒜 π F x).cechD 0 d).hom c = 0) :
    ∃ t : (gammaStar 𝒜 π F x).obj d, ((gammaStar 𝒜 π F x).cechAug₀ d).hom t = c := by
  classical
  have hlt : ∀ k l : Fin (n + 1), k < l →
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (inf_le_left : basicOpen 𝒜 ((x k : A)) ⊓ basicOpen 𝒜 ((x l : A))
            ≤ basicOpen 𝒜 ((x k : A)))).op
          (chartColimitMap 𝒜 π F x k d (c (GradedModule.CechIdx.zeroIdx k)))
        = (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (inf_le_right : basicOpen 𝒜 ((x k : A)) ⊓ basicOpen 𝒜 ((x l : A))
            ≤ basicOpen 𝒜 ((x l : A)))).op
          (chartColimitMap 𝒜 π F x l d (c (GradedModule.CechIdx.zeroIdx l))) := by
    intro k l hkl
    let τ : GradedModule.CechIdx n 1 := ⟨[k, l], by simp [hkl], rfl⟩
    have hτ : (((gammaStar 𝒜 π F x).cechFaceMap τ 0).app d).hom (c (τ.face 0))
        = (((gammaStar 𝒜 π F x).cechFaceMap τ 1).app d).hom (c (τ.face 1)) := by
      have h1 : (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) •
          (((gammaStar 𝒜 π F x).cechFaceMap τ i).app d).hom (c (τ.face i))) = 0 :=
        congrFun hc τ
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_one_smul, add_neg_eq_zero] at h1
      exact h1
    have hA := pairColimitMap_locResApp_right 𝒜 π F x k l (τ.perm_face_append 0) d
      (c (τ.face 0))
    have hB := pairColimitMap_locResApp 𝒜 π F x k l (τ.perm_face_append 1) d (c (τ.face 1))
    exact (hA.symm.trans ((congrArg (pairColimitMap 𝒜 π F x k l d) hτ).trans hB)).symm
  have hcompat : TopCat.Presheaf.IsCompatible
      (Scheme.Modules.abSheaf (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)).1
      (fun k : Fin (n + 1) ↦ basicOpen 𝒜 ((x k : A)))
      (fun k : Fin (n + 1) ↦
        chartColimitMap 𝒜 π F x k d (c (GradedModule.CechIdx.zeroIdx k))) := by
    intro k l
    have hL : (Opens.infLELeft (basicOpen 𝒜 ((x k : A))) (basicOpen 𝒜 ((x l : A))))
        = homOfLE inf_le_left := Subsingleton.elim _ _
    have hR : (Opens.infLERight (basicOpen 𝒜 ((x k : A))) (basicOpen 𝒜 ((x l : A))))
        = homOfLE inf_le_right := Subsingleton.elim _ _
    rw [hL, hR]
    rcases lt_trichotomy k l with h | h | h
    · exact hlt k l h
    · subst h; rfl
    · have hres := hlt l k h
      have hle : basicOpen 𝒜 ((x k : A)) ⊓ basicOpen 𝒜 ((x l : A))
          ≤ basicOpen 𝒜 ((x l : A)) ⊓ basicOpen 𝒜 ((x k : A)) := le_inf inf_le_right inf_le_left
      have h2 := congrArg ((ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
        (homOfLE hle).op) hres
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at h2
      exact h2.symm
  obtain ⟨t, ht, -⟩ := (Scheme.Modules.abSheaf
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)).existsUnique_gluing'
      (fun k : Fin (n + 1) ↦ basicOpen 𝒜 ((x k : A))) ⊤ (fun _ ↦ homOfLE le_top) hcover _ hcompat
  refine ⟨t, ?_⟩
  funext τ
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 τ.length_eq
  have hτa : τ = GradedModule.CechIdx.zeroIdx a := GradedModule.CechIdx.ext ha
  subst hτa
  refine (bijective_chartColimitMap 𝒜 π F x a hcover d).1 ?_
  exact (chartColimitMap_locOf 𝒜 π F x a d t).trans (ht a)

/-- **Hartshorne II.5.14 in the form the graded Čech machinery consumes.**  For a quasicoherent
sheaf `F` on `Proj 𝒜` covered by the degree-one charts `D₊(xᵢ)`, the augmentation

`Γ(Proj 𝒜, F(d)) ⟶ H⁰(Čech complex of Γ_*(F) in degree d)`

is bijective.  This is the content of
`RelativeCohomology.SchemeGlobalSectionsComparison.globalSectionsIso`. -/
theorem bijective_gammaStar_cechAug
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    Function.Bijective (((gammaStar 𝒜 π F x).cechAug d).hom) :=
  ⟨GradedModule.injective_cechAug_of_aug₀ _ d
      (injective_gammaStar_cechAug₀ 𝒜 π F x hcover d),
    GradedModule.surjective_cechAug_of_cocycles _ d
      fun c hc ↦ exists_gammaStar_cechAug₀_eq 𝒜 π F x hcover d c hc⟩

/-- The `R`-linear equivalence `H⁰(Čech) ≃ Γ(Proj 𝒜, F(d))`. -/
noncomputable def cechHgrZeroEquiv
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent] (d : ℤ) :
    ((gammaStar 𝒜 π F x).cechHgr 0).obj d ≃ₗ[R] (gammaStar 𝒜 π F x).obj d :=
  (LinearEquiv.ofBijective ((gammaStar 𝒜 π F x).cechAug d).hom
    (bijective_gammaStar_cechAug 𝒜 π F x hcover d)).symm

end AlgebraicGeometry.Proj
