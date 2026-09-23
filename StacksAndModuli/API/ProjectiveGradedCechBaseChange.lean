module

public import StacksAndModuli.API.ProjectiveGradedCohomologyExists
public import StacksAndModuli.API.ProjectiveGradedFamilies
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Base change of the graded Čech complex along an arbitrary ring map

Supporting API with no Stacks Project counterpart.

`GradedModule.baseChange` (`API/ProjectiveGradedFamilies.lean`) is `M ↦ A ⊗_R M` degreewise,
the graded-module model of `F ↦ F ⊗_R A` on `ℙⁿ`.  This file records what it preserves along
an **arbitrary** map of commutative rings `R → A`: finite generation, and — the point of the
file — the Čech *cochain* complex, which base-changes on the nose:

`(M ⊗_R A)^~ ⁱ`-cochains `= (M^~ ⁱ-cochains) ⊗_R A`, complex by complex
(`GradedModule.cechComplexBaseChangeIso`).

No flatness is used.  The localization `M[1/x_I]` is a *filtered* colimit, and the tensor
product commutes with filtered colimits (`TensorProduct.directLimitLeft`); in a filtered
colimit of modules an element of a stage vanishes exactly when it vanishes at some later
stage, which is what replaces the usual flatness argument.  This is what makes the
comparison available along `R → κ` for a residue field `κ` of the base of a family, where
`κ` is very far from flat.

What base change does to *cohomology* — as opposed to cochains — needs flatness and lives in
`API/ProjectiveGradedBaseChange.lean`.

Main declarations:
- `GradedModule.IsFG.baseChange`;
- `GradedModule.locBaseChangeIso`: `(M ⊗ A)[1/x_l] ≅ M[1/x_l] ⊗ A`;
- `GradedModule.cechCochainBaseChangeEquiv`, `GradedModule.cechComplexBaseChangeIso`.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial TensorProduct

variable {k : Type u} [CommRing k] {n : ℕ}
variable (k' : Type u) [CommRing k'] [Algebra k k']

lemma baseChange_mulList (M : GradedModule k n) :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ) (h : d + (l.length : ℤ) = e),
      (M.baseChange k').mulList l d e h
        = ModuleCat.ofHom (LinearMap.baseChange k' (M.mulList l d e h).hom)
  | [], d, e, h => by
      have he : d = e := by simpa using h
      subst he
      refine ModuleCat.hom_ext ?_
      change LinearMap.id = LinearMap.baseChange k' (LinearMap.id)
      rw [LinearMap.baseChange_id]
  | i :: t, d, e, h => by
      have h' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
      change (M.baseChange k').mulX i d ≫ (M.baseChange k').mulList t (d + 1) e h' = _
      rw [baseChange_mulList M t (d + 1) e h']
      refine ModuleCat.hom_ext ?_
      change LinearMap.baseChange k' (M.mulList t (d + 1) e h').hom ∘ₗ
          LinearMap.baseChange k' (M.mulX i d).hom
        = LinearMap.baseChange k' (M.mulList (i :: t) d e h).hom
      rw [← LinearMap.baseChange_comp]
      congr 1

/-! ## Base change preserves finite generation -/

lemma baseChange_mulSpan_eq_top (M : GradedModule k n) (d e : ℤ) (h : M.mulSpan d e = ⊤) :
    (M.baseChange k').mulSpan d e = ⊤ := by
  have key : ∀ v : M.obj e, (1 : k') ⊗ₜ[k] v ∈ (M.baseChange k').mulSpan d e := by
    intro v
    have hv : v ∈ M.mulSpan d e := by rw [h]; trivial
    refine Submodule.iSup_induction (motive := fun w => (1 : k') ⊗ₜ[k] w
      ∈ (M.baseChange k').mulSpan d e) _ hv ?_ ?_ ?_
    · rintro l _ ⟨x, rfl⟩
      refine le_mulSpan (M.baseChange k') d e l.1 l.2 ⟨(1 : k') ⊗ₜ[k] x, ?_⟩
      rw [baseChange_mulList]
      rfl
    · rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ ha hb
  refine eq_top_iff.mpr fun z _ => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
      rw [show a ⊗ₜ[k] v = a • ((1 : k') ⊗ₜ[k] v) from by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ a (key v)
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

lemma subsingleton_baseChange {V : Type u} [AddCommGroup V] [Module k V] [Subsingleton V] :
    Subsingleton (k' ⊗[k] V) := by
  refine ⟨fun x y => ?_⟩
  have hz : ∀ w : k' ⊗[k] V, w = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rfl
    | tmul a v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add p q hp hq => rw [hp, hq, add_zero]
  rw [hz x, hz y]

lemma IsFG.baseChange {M : GradedModule k n} (hM : IsFG M) : IsFG (M.baseChange k') := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := hM
  refine ⟨fun d => ?_, ⟨lo, fun d hd => ?_⟩,
    ⟨hi, fun d hd => baseChange_mulSpan_eq_top k' M d (d + 1) (hgen d hd)⟩⟩
  · haveI := hfd d
    exact Module.Finite.base_change k k' (M.obj d)
  · haveI := hlow d hd
    exact subsingleton_baseChange k'

/-! ## Base change of the localization tower -/

variable (M : GradedModule k n) (l : List (Fin (n + 1)))

lemma baseChange_locTr (d : ℤ) (t t' : ℕ) (h : t ≤ t') :
    (M.baseChange k').locTr l d t t' h
      = ModuleCat.ofHom (LinearMap.baseChange k' (M.locTr l d t t' h).hom) := by
  rw [locTr, locTr, baseChange_mulList]

/-- Forward comparison: the localization of a base change maps to the base change of the
localization. -/
def locBaseChangeToTensor (d : ℤ) :
    ((M.baseChange k').loc l).obj d ⟶ ModuleCat.of k' (k' ⊗[k] ((M.loc l).obj d)) :=
  ModuleCat.ofHom (Module.DirectLimit.lift k' ℕ
    (fun t : ℕ => (((M.baseChange k').obj (locDeg l d t) : ModuleCat.{u} k') : Type u))
    (fun t t' h => ((M.baseChange k').locTr l d t t' h).hom)
    (fun t => LinearMap.baseChange k' (M.locIncl l d t).hom)
    (fun t t' h x => by
      have hcmp := congrArg ModuleCat.Hom.hom (M.locTr_locIncl l d t t' h)
      simp only [ModuleCat.hom_comp] at hcmp
      have hbc : LinearMap.baseChange k'
            ((M.locIncl l d t').hom ∘ₗ (M.locTr l d t t' h).hom)
          = LinearMap.baseChange k' (M.locIncl l d t).hom := by rw [hcmp]
      rw [LinearMap.baseChange_comp] at hbc
      have hlt := congrArg ModuleCat.Hom.hom (baseChange_locTr k' M l d t t' h)
      change (LinearMap.baseChange k' (M.locIncl l d t').hom)
          (((M.baseChange k').locTr l d t t' h).hom x)
        = (LinearMap.baseChange k' (M.locIncl l d t).hom) x
      rw [hlt]
      exact LinearMap.congr_fun hbc x))

lemma locIncl_locBaseChangeToTensor (d : ℤ) (t : ℕ) :
    (M.baseChange k').locIncl l d t ≫ locBaseChangeToTensor k' M l d
      = ModuleCat.ofHom (LinearMap.baseChange k' (M.locIncl l d t).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl, ModuleCat.hom_ofHom,
    locBaseChangeToTensor]
  exact Module.DirectLimit.lift_of _ _ _

/-! ## The localization comparison is an isomorphism -/

lemma baseChange_locTr_eq_zero_of_le (d : ℤ) {t t₁ T : ℕ} (h₁ : t ≤ t₁) (h₂ : t₁ ≤ T)
    (w : k' ⊗[k] (M.obj (locDeg l d t)))
    (hw : (LinearMap.baseChange k' (M.locTr l d t t₁ h₁).hom) w = 0) :
    (LinearMap.baseChange k' (M.locTr l d t T (le_trans h₁ h₂)).hom) w = 0 := by
  have htr := congrArg ModuleCat.Hom.hom (M.locTr_trans l d t t₁ T h₁ h₂)
  simp only [ModuleCat.hom_comp] at htr
  have hbc : LinearMap.baseChange k'
        ((M.locTr l d t₁ T h₂).hom ∘ₗ (M.locTr l d t t₁ h₁).hom)
      = LinearMap.baseChange k' (M.locTr l d t T (le_trans h₁ h₂)).hom := by rw [htr]
  rw [LinearMap.baseChange_comp] at hbc
  rw [← hbc]
  change (LinearMap.baseChange k' (M.locTr l d t₁ T h₂).hom)
    ((LinearMap.baseChange k' (M.locTr l d t t₁ h₁).hom) w) = 0
  rw [hw, map_zero]

/-- Base change intertwines `k' ⊗ -` and `- ⊗ k'`, up to the commutativity isomorphism. -/
lemma comm_baseChange {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (g : V →ₗ[k] W) (x : k' ⊗[k] V) :
    TensorProduct.comm k k' W (LinearMap.baseChange k' g x)
      = LinearMap.rTensor k' g (TensorProduct.comm k k' V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add p q hp hq => simp [hp, hq]

/-- An element of a stage of the localization that dies after base change already dies at a
later stage.

No flatness is needed: the tensor product commutes with the *filtered* colimit defining the
localization (`TensorProduct.directLimitLeft`), and in a filtered colimit of modules an
element of a stage vanishes exactly when it vanishes at some later stage. This is what makes
the whole comparison work along an arbitrary ring map, in particular along `R → κ` for a
residue field of the base of a family. -/
lemma exists_baseChange_locTr_eq_zero (d : ℤ) (t : ℕ)
    (u : k' ⊗[k] (M.obj (locDeg l d t)))
    (hu : (LinearMap.baseChange k' (M.locIncl l d t).hom) u = 0) :
    ∃ (t' : ℕ) (h : t ≤ t'),
      (LinearMap.baseChange k' (M.locTr l d t t' h).hom) u = 0 := by
  set f : ∀ j j' : ℕ, j ≤ j' → ((M.obj (locDeg l d j) : Type u) →ₗ[k]
      (M.obj (locDeg l d j') : Type u)) := fun j j' h => (M.locTr l d j j' h).hom with hf
  have hli : (M.locIncl l d t).hom
      = Module.DirectLimit.of k ℕ (fun j => (M.obj (locDeg l d j) : Type u)) f t := rfl
  have hzero : Module.DirectLimit.of k ℕ (fun j => (M.obj (locDeg l d j) : Type u) ⊗[k] k')
      (fun j j' h => LinearMap.rTensor k' (f j j' h)) t
      (TensorProduct.comm k k' (M.obj (locDeg l d t)) u) = 0 := by
    have h1 := congrArg (TensorProduct.comm k k' ((M.loc l).obj d)) hu
    rw [comm_baseChange k' (M.locIncl l d t).hom u, map_zero, hli] at h1
    have h2 := congrArg
      (TensorProduct.directLimitLeft
        (R := k) (ι := ℕ) (G := fun j => (M.obj (locDeg l d j) : Type u)) f k') h1
    rw [map_zero] at h2
    erw [TensorProduct.directLimitLeft_rTensor_of] at h2
    exact h2
  obtain ⟨t', h, ht'⟩ := Module.DirectLimit.of.zero_exact hzero
  refine ⟨t', h, ?_⟩
  have hinj := (TensorProduct.comm k k' (M.obj (locDeg l d t'))).injective
  refine hinj ?_
  rw [comm_baseChange k' (M.locTr l d t t' h).hom u, map_zero]
  exact ht'

lemma bijective_locBaseChangeToTensor (d : ℤ) :
    Function.Bijective ((locBaseChangeToTensor k' M l d).hom) := by
  constructor
  · intro w z hwz
    have h0 : (locBaseChangeToTensor k' M l d).hom (w - z) = 0 := by
      rw [map_sub, hwz, sub_self]
    obtain ⟨t, u, hu⟩ := (M.baseChange k').locIncl_exists l d (w - z)
    have hΦ := congrArg ModuleCat.Hom.hom (locIncl_locBaseChangeToTensor k' M l d t)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hΦ
    have h1 := LinearMap.congr_fun hΦ u
    simp only [LinearMap.comp_apply] at h1
    rw [hu] at h1
    obtain ⟨t', h, ht'⟩ := exists_baseChange_locTr_eq_zero k' M l d t u (h1.symm.trans h0)
    have hlt := congrArg ModuleCat.Hom.hom (baseChange_locTr k' M l d t t' h)
    simp only [ModuleCat.hom_ofHom] at hlt
    have hstep := congrArg ModuleCat.Hom.hom
      ((M.baseChange k').locTr_locIncl l d t t' h)
    simp only [ModuleCat.hom_comp] at hstep
    have h2 := LinearMap.congr_fun hstep u
    simp only [LinearMap.comp_apply] at h2
    have h3 : ((M.baseChange k').locTr l d t t' h).hom u = 0 := by
      rw [hlt]
      exact ht'
    rw [← sub_eq_zero, ← hu, ← h2, h3, map_zero]
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a z =>
        obtain ⟨t, x, hx⟩ := M.locIncl_exists l d z
        refine ⟨((M.baseChange k').locIncl l d t).hom (a ⊗ₜ[k] x), ?_⟩
        have hΦ := congrArg ModuleCat.Hom.hom (locIncl_locBaseChangeToTensor k' M l d t)
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hΦ
        have h1 := LinearMap.congr_fun hΦ (a ⊗ₜ[k] x)
        simp only [LinearMap.comp_apply] at h1
        rw [h1, ← hx]
        rfl
    | add p q hp hq =>
        obtain ⟨wp, hwp⟩ := hp
        obtain ⟨wq, hwq⟩ := hq
        exact ⟨wp + wq, by rw [map_add, hwp, hwq]⟩

/-- **Base change commutes with localization.** -/
noncomputable def locBaseChangeIso (d : ℤ) :
    ((M.baseChange k').loc l).obj d ≅ ModuleCat.of k' (k' ⊗[k] ((M.loc l).obj d)) := by
  haveI : Mono (locBaseChangeToTensor k' M l d) :=
    (ModuleCat.mono_iff_injective _).mpr (bijective_locBaseChangeToTensor k' M l d).1
  haveI : Epi (locBaseChangeToTensor k' M l d) :=
    (ModuleCat.epi_iff_surjective _).mpr (bijective_locBaseChangeToTensor k' M l d).2
  haveI : IsIso (locBaseChangeToTensor k' M l d) := isIso_of_mono_of_epi _
  exact asIso (locBaseChangeToTensor k' M l d)

/-- **The localization/base-change comparison is natural in the morphism.** -/
lemma locBaseChangeToTensor_locMap {M N : GradedModule k n} (φ : M ⟶ N)
    (l : List (Fin (n + 1))) (d : ℤ) :
    (locMap l (baseChangeMap φ k')).app d ≫ locBaseChangeToTensor k' N l d
      = locBaseChangeToTensor k' M l d
        ≫ ModuleCat.ofHom (LinearMap.baseChange k' ((locMap l φ).app d).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  obtain ⟨t, u, rfl⟩ := (M.baseChange k').locIncl_exists l d z
  have hM := congrArg ModuleCat.Hom.hom (locIncl_locBaseChangeToTensor k' M l d t)
  have hN := congrArg ModuleCat.Hom.hom (locIncl_locBaseChangeToTensor k' N l d t)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hM hN
  have hnat := congrArg ModuleCat.Hom.hom (locIncl_locMap M l φ d t)
  simp only [ModuleCat.hom_comp] at hnat
  have hbc : LinearMap.baseChange k' (((locMap l φ).app d).hom ∘ₗ (M.locIncl l d t).hom)
      = LinearMap.baseChange k' ((N.locIncl l d t).hom ∘ₗ (φ.app (locDeg l d t)).hom) := by
    rw [hnat]
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hbc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hN' : ∀ y, (locBaseChangeToTensor k' N l d).hom
      (((N.baseChange k').locIncl l d t).hom y)
      = LinearMap.baseChange k' (N.locIncl l d t).hom y := fun y => by
    have h := LinearMap.congr_fun hN y
    simp only [LinearMap.comp_apply] at h
    exact h
  have hM' : ∀ y, (locBaseChangeToTensor k' M l d).hom
      (((M.baseChange k').locIncl l d t).hom y)
      = LinearMap.baseChange k' (M.locIncl l d t).hom y := fun y => by
    have h := LinearMap.congr_fun hM y
    simp only [LinearMap.comp_apply] at h
    exact h
  rw [locMap_locIncl_apply, hN', hM']
  exact (LinearMap.congr_fun hbc u).symm

/-- **Base change preserves a localized isomorphism.**  If `φ` becomes bijective in degree `d`
after localizing at `l`, so does its base change: the comparison `locBaseChangeToTensor` is an
isomorphism, and tensoring a bijection is a bijection. -/
theorem bijective_locMap_baseChangeMap_app {M N : GradedModule k n} (φ : M ⟶ N)
    (l : List (Fin (n + 1))) (d : ℤ)
    (h : Function.Bijective (((locMap l φ).app d).hom)) :
    Function.Bijective (((locMap l (baseChangeMap φ k')).app d).hom) := by
  have hsq := congrArg ModuleCat.Hom.hom (locBaseChangeToTensor_locMap k' φ l d)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hsq
  have hbc : Function.Bijective (LinearMap.baseChange k' ((locMap l φ).app d).hom) :=
    ((LinearEquiv.ofBijective _ h).baseChange _ k' _ _).bijective
  have hM := bijective_locBaseChangeToTensor k' M l d
  have hN := bijective_locBaseChangeToTensor k' N l d
  have hΨ : Function.Bijective
      (fun a => (locBaseChangeToTensor k' N l d).hom
        (((locMap l (baseChangeMap φ k')).app d).hom a)) := by
    have hfun : (fun a => (locBaseChangeToTensor k' N l d).hom
          (((locMap l (baseChangeMap φ k')).app d).hom a))
        = fun a => LinearMap.baseChange k' ((locMap l φ).app d).hom
          ((locBaseChangeToTensor k' M l d).hom a) := by
      funext a
      have ha := LinearMap.congr_fun hsq a
      simp only [LinearMap.comp_apply] at ha
      exact ha
    rw [hfun]
    exact hbc.comp hM
  refine ⟨fun a b hab => hΨ.1 (by simp only [hab]), fun y => ?_⟩
  obtain ⟨a, ha⟩ := hΨ.2 ((locBaseChangeToTensor k' N l d).hom y)
  exact ⟨a, hN.1 ha⟩

lemma baseChange_mulX' (i : Fin (n + 1)) (a b : ℤ) (h : a + 1 = b) :
    (M.baseChange k').mulX' i a b h
      = ModuleCat.ofHom (LinearMap.baseChange k' (M.mulX' i a b h).hom) := by
  subst h
  rw [mulX'_rfl, mulX'_rfl]
  rfl

lemma locBaseChangeToTensor_mulX (i : Fin (n + 1)) (d : ℤ) :
    ((M.baseChange k').loc l).mulX i d ≫ locBaseChangeToTensor k' M l (d + 1)
      = locBaseChangeToTensor k' M l d
        ≫ ModuleCat.ofHom (LinearMap.baseChange k' ((M.loc l).mulX i d).hom) := by
  refine loc_hom_ext (M.baseChange k') l fun t => ?_
  have e1 := locIncl_mulX (M.baseChange k') l d t i
  have e2 := locIncl_locBaseChangeToTensor k' M l (d + 1) t
  have e3 := locIncl_locBaseChangeToTensor k' M l d t
  have e4 := locIncl_mulX M l d t i
  conv_lhs => rw [← Category.assoc, e1, Category.assoc, e2]
  conv_rhs => rw [← Category.assoc, e3]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h4 := congrArg ModuleCat.Hom.hom e4
  simp only [ModuleCat.hom_comp] at h4
  have hbc : LinearMap.baseChange k'
        ((M.locIncl l (d + 1) t).hom ∘ₗ (M.mulX' i (locDeg l d t) (locDeg l (d + 1) t)
          (by rw [locDeg_def, locDeg_def]; ring)).hom)
      = LinearMap.baseChange k' (((M.loc l).mulX i d).hom ∘ₗ (M.locIncl l d t).hom) := by
    rw [h4]
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hbc
  have hmx := congrArg ModuleCat.Hom.hom (baseChange_mulX' k' M i (locDeg l d t)
    (locDeg l (d + 1) t) (by rw [locDeg_def, locDeg_def]; ring))
  simp only [ModuleCat.hom_ofHom] at hmx
  change (LinearMap.baseChange k' (M.locIncl l (d + 1) t).hom)
      (((M.baseChange k').mulX' i (locDeg l d t) (locDeg l (d + 1) t)
        (by rw [locDeg_def, locDeg_def]; ring)).hom x)
    = (LinearMap.baseChange k' ((M.loc l).mulX i d).hom)
      ((LinearMap.baseChange k' (M.locIncl l d t).hom) x)
  rw [hmx]
  exact LinearMap.congr_fun hbc x

/-! ## The comparison intertwines the restriction maps -/

lemma locResApp_locBaseChangeToTensor {l l' m : List (Fin (n + 1))}
    (hp : l'.Perm (l ++ m)) (d : ℤ) :
    (M.baseChange k').locResApp l hp d ≫ locBaseChangeToTensor k' M l' d
      = locBaseChangeToTensor k' M l d
        ≫ ModuleCat.ofHom (LinearMap.baseChange k' (M.locResApp l hp d).hom) := by
  refine loc_hom_ext (M.baseChange k') l fun t => ?_
  have e1 := locIncl_locResApp (M.baseChange k') l hp d t
  have e2 := locIncl_locBaseChangeToTensor k' M l' d t
  have e3 := locIncl_locBaseChangeToTensor k' M l d t
  have e4 := locIncl_locResApp M l hp d t
  conv_lhs => rw [← Category.assoc, e1, Category.assoc, e2]
  conv_rhs => rw [← Category.assoc, e3]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hml := congrArg ModuleCat.Hom.hom
    (baseChange_mulList k' M (listPow m t) (locDeg l d t) (locDeg l' d t)
      (locRes_stage_degree l l' m hp d t))
  simp only [ModuleCat.hom_ofHom] at hml
  have h4 := congrArg ModuleCat.Hom.hom e4
  simp only [ModuleCat.hom_comp] at h4
  have hbc : LinearMap.baseChange k'
        ((M.locIncl l' d t).hom ∘ₗ (M.mulList (listPow m t) (locDeg l d t) (locDeg l' d t)
          (locRes_stage_degree l l' m hp d t)).hom)
      = LinearMap.baseChange k' ((M.locResApp l hp d).hom ∘ₗ (M.locIncl l d t).hom) := by
    rw [h4]
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hbc
  change (LinearMap.baseChange k' (M.locIncl l' d t).hom)
      (((M.baseChange k').mulList (listPow m t) (locDeg l d t) (locDeg l' d t)
        (locRes_stage_degree l l' m hp d t)).hom x)
    = (LinearMap.baseChange k' (M.locResApp l hp d).hom)
      ((LinearMap.baseChange k' (M.locIncl l d t).hom) x)
  rw [hml]
  exact LinearMap.congr_fun hbc x

/-! ## Base change of the Čech cochain groups -/

instance decidableEqCechIdx {p : ℕ} : DecidableEq (CechIdx n p) := fun σ τ =>
  decidable_of_iff (σ.toList = τ.toList) ⟨CechIdx.ext, fun h => h ▸ rfl⟩

/-- Base change commutes with localization, as a linear equivalence. -/
noncomputable def locBaseChangeEquiv (d : ℤ) :
    (((M.baseChange k').loc l).obj d) ≃ₗ[k'] (k' ⊗[k] ((M.loc l).obj d)) :=
  LinearEquiv.ofBijective (locBaseChangeToTensor k' M l d).hom
    (bijective_locBaseChangeToTensor k' M l d)

@[simp] lemma locBaseChangeEquiv_apply (d : ℤ) (x : ((M.baseChange k').loc l).obj d) :
    locBaseChangeEquiv k' M l d x = (locBaseChangeToTensor k' M l d).hom x := rfl

lemma locBaseChangeEquiv_symm_mulX (i : Fin (n + 1)) (d : ℤ) (a : k')
    (y : (M.loc l).obj d) :
    (((M.baseChange k').loc l).mulX i d).hom
        ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))
      = (locBaseChangeEquiv k' M l (d + 1)).symm
          (a ⊗ₜ[k] (((M.loc l).mulX i d).hom y)) := by
  refine (locBaseChangeEquiv k' M l (d + 1)).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  have h := congrArg ModuleCat.Hom.hom (locBaseChangeToTensor_mulX k' M l i d)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  have h2 := LinearMap.congr_fun h ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))
  simp only [LinearMap.comp_apply] at h2
  change (locBaseChangeToTensor k' M l (d + 1)).hom
    ((((M.baseChange k').loc l).mulX i d).hom
      ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))) = _
  rw [h2]
  change (LinearMap.baseChange k' ((M.loc l).mulX i d).hom)
    ((locBaseChangeEquiv k' M l d) ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl


/-- Base change commutes with the Čech cochain groups. -/
noncomputable def cechCochainBaseChangeEquiv (p : ℕ) (d : ℤ) :
    ((M.baseChange k').cechCochain p d) ≃ₗ[k'] (k' ⊗[k] (M.cechCochain p d)) :=
  (LinearEquiv.piCongrRight (fun τ : CechIdx n p =>
      locBaseChangeEquiv k' M τ.toList d)).trans
    (TensorProduct.piRight k k' k' (fun τ : CechIdx n p => ((M.loc τ.toList).obj d))).symm

lemma locResApp_locBaseChangeEquiv_symm {l l' m : List (Fin (n + 1))}
    (hp : l'.Perm (l ++ m)) (d : ℤ) (a : k') (y : (M.loc l).obj d) :
    ((M.baseChange k').locResApp l hp d).hom
        ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))
      = (locBaseChangeEquiv k' M l' d).symm
          (a ⊗ₜ[k] ((M.locResApp l hp d).hom y)) := by
  refine (locBaseChangeEquiv k' M l' d).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  have h := congrArg ModuleCat.Hom.hom (locResApp_locBaseChangeToTensor k' M hp d)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  have h2 := LinearMap.congr_fun h ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))
  simp only [LinearMap.comp_apply] at h2
  change (locBaseChangeToTensor k' M l' d).hom
    (((M.baseChange k').locResApp l hp d).hom
      ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))) = _
  rw [h2]
  change (LinearMap.baseChange k' (M.locResApp l hp d).hom)
    ((locBaseChangeEquiv k' M l d) ((locBaseChangeEquiv k' M l d).symm (a ⊗ₜ[k] y))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma cechFaceMap_locBaseChangeEquiv_symm {p : ℕ} (τ : CechIdx n (p + 1))
    (i : Fin (p + 2)) (d : ℤ) (a : k') (y : (M.loc (τ.face i).toList).obj d) :
    (((M.baseChange k').cechFaceMap τ i).app d).hom
        ((locBaseChangeEquiv k' M (τ.face i).toList d).symm (a ⊗ₜ[k] y))
      = (locBaseChangeEquiv k' M τ.toList d).symm
          (a ⊗ₜ[k] (((M.cechFaceMap τ i).app d).hom y)) :=
  locResApp_locBaseChangeEquiv_symm k' M (τ.perm_face_append i) d a y

lemma cechCochainBaseChangeEquiv_symm_tmul (p : ℕ) (d : ℤ) (a : k')
    (c : M.cechCochain p d) (τ : CechIdx n p) :
    ((cechCochainBaseChangeEquiv k' M p d).symm (a ⊗ₜ[k] c)) τ
      = (locBaseChangeEquiv k' M τ.toList d).symm (a ⊗ₜ[k] (c τ)) := by
  change ((LinearEquiv.piCongrRight (fun σ : CechIdx n p =>
      locBaseChangeEquiv k' M σ.toList d)).symm
    ((TensorProduct.piRight k k' k'
      (fun σ : CechIdx n p => (((M.loc σ.toList).obj d : ModuleCat.{u} k) : Type u)))
        (a ⊗ₜ[k] c))) τ = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  rfl

/-- The Čech differential commutes with base change. -/
lemma cechD_cechCochainBaseChangeEquiv_symm (p : ℕ) (d : ℤ)
    (w : k' ⊗[k] (M.cechCochain p d)) :
    ((M.baseChange k').cechD p d).hom
        ((cechCochainBaseChangeEquiv k' M p d).symm w)
      = (cechCochainBaseChangeEquiv k' M (p + 1) d).symm
          ((LinearMap.baseChange k' (M.cechD p d).hom) w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a c =>
      funext τ
      change ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          (((M.baseChange k').cechFaceMap τ i).app d).hom
            (((cechCochainBaseChangeEquiv k' M p d).symm (a ⊗ₜ[k] c)) (τ.face i))
        = ((cechCochainBaseChangeEquiv k' M (p + 1) d).symm
            (a ⊗ₜ[k] ((M.cechD p d).hom c))) τ
      rw [cechCochainBaseChangeEquiv_symm_tmul]
      change _ = (locBaseChangeEquiv k' M τ.toList d).symm
        (a ⊗ₜ[k] (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          (((M.cechFaceMap τ i).app d).hom (c (τ.face i)))))
      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cechCochainBaseChangeEquiv_symm_tmul,
        show (a ⊗ₜ[k] (((-1 : ℤ) ^ (i : ℕ)) •
            (((M.cechFaceMap τ i).app d).hom (c (τ.face i))))
              : k' ⊗[k] ((M.loc τ.toList).obj d))
          = ((-1 : ℤ) ^ (i : ℕ)) •
            (a ⊗ₜ[k] (((M.cechFaceMap τ i).app d).hom (c (τ.face i))))
          from map_zsmul (TensorProduct.mk k k' ((M.loc τ.toList).obj d) a) _ _,
        map_zsmul, cechFaceMap_locBaseChangeEquiv_symm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-! ## Base change of a cochain complex -/

/-- The base change of a cochain complex of `k`-vector spaces. -/
noncomputable def cochainBaseChange (C : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k') ℕ :=
  CochainComplex.of (fun p => ModuleCat.of k' (k' ⊗[k] (C.X p)))
    (fun p => ModuleCat.ofHom (LinearMap.baseChange k' (C.d p (p + 1)).hom))
    (fun p => by
      refine ModuleCat.hom_ext ?_
      change LinearMap.baseChange k' (C.d (p + 1) (p + 1 + 1)).hom ∘ₗ
          LinearMap.baseChange k' (C.d p (p + 1)).hom = 0
      rw [← LinearMap.baseChange_comp]
      have hdd : (C.d (p + 1) (p + 1 + 1)).hom ∘ₗ (C.d p (p + 1)).hom = 0 := by
        have h := congrArg ModuleCat.Hom.hom (C.d_comp_d p (p + 1) (p + 1 + 1))
        rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact h
      rw [hdd]
      simp)

lemma cochainBaseChange_d (C : CochainComplex (ModuleCat.{u} k) ℕ) (p : ℕ) :
    (cochainBaseChange k' C).d p (p + 1)
      = ModuleCat.ofHom (LinearMap.baseChange k' (C.d p (p + 1)).hom) := by
  simp only [cochainBaseChange, CochainComplex.of_d]

/-- Multiplication by a variable commutes with base change on Čech cochains. -/
lemma cechMulX_cechCochainBaseChangeEquiv_symm (i : Fin (n + 1)) (p : ℕ) (d : ℤ)
    (w : k' ⊗[k] (M.cechCochain p d)) :
    (((M.baseChange k').cechMulX i d).f p).hom
        ((cechCochainBaseChangeEquiv k' M p d).symm w)
      = (cechCochainBaseChangeEquiv k' M p (d + 1)).symm
          ((LinearMap.baseChange k' ((M.cechMulX i d).f p).hom) w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a c =>
      funext τ
      change (((M.baseChange k').loc τ.toList).mulX i d).hom
          (((cechCochainBaseChangeEquiv k' M p d).symm (a ⊗ₜ[k] c)) τ)
        = ((cechCochainBaseChangeEquiv k' M p (d + 1)).symm
            (a ⊗ₜ[k] (((M.cechMulX i d).f p).hom c))) τ
      rw [cechCochainBaseChangeEquiv_symm_tmul, cechCochainBaseChangeEquiv_symm_tmul]
      exact locBaseChangeEquiv_symm_mulX k' M τ.toList i d a (c τ)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Functoriality of the base change of cochain complexes. -/
noncomputable def cochainBaseChangeMap {C D : CochainComplex (ModuleCat.{u} k) ℕ}
    (φ : C ⟶ D) : cochainBaseChange k' C ⟶ cochainBaseChange k' D :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (LinearMap.baseChange k' (φ.f p).hom))
    (fun p => by
      simp only [cochainBaseChange, CochainComplex.of_d]
      refine ModuleCat.hom_ext ?_
      change LinearMap.baseChange k' (D.d p (p + 1)).hom
          ∘ₗ LinearMap.baseChange k' (φ.f p).hom
        = LinearMap.baseChange k' (φ.f (p + 1)).hom
          ∘ₗ LinearMap.baseChange k' (C.d p (p + 1)).hom
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      have h := congrArg ModuleCat.Hom.hom (φ.comm p (p + 1))
      simp only [ModuleCat.hom_comp] at h
      exact h)

/-- The Čech complex of a base change is the base change of the Čech complex. -/
noncomputable def cechComplexBaseChangeIso (d : ℤ) :
    (M.baseChange k').cechComplex d ≅ cochainBaseChange k' (M.cechComplex d) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (cechCochainBaseChangeEquiv k' M p d).toModuleIso)
    (fun p q hpq => by
      obtain rfl : q = p + 1 := hpq.symm
      simp only [cechComplex, cochainBaseChange, CochainComplex.of_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      change (LinearMap.baseChange k' (M.cechD p d).hom)
          ((cechCochainBaseChangeEquiv k' M p d) c)
        = (cechCochainBaseChangeEquiv k' M (p + 1) d)
            (((M.baseChange k').cechD p d).hom c)
      have h := cechD_cechCochainBaseChangeEquiv_symm k' M p d
        ((cechCochainBaseChangeEquiv k' M p d) c)
      rw [LinearEquiv.symm_apply_apply] at h
      rw [h, LinearEquiv.apply_symm_apply])

lemma cochainBaseChange_d' (C : CochainComplex (ModuleCat.{u} k) ℕ) (p q : ℕ) :
    (cochainBaseChange k' C).d p q
      = ModuleCat.ofHom (LinearMap.baseChange k' (C.d p q).hom) := by
  by_cases h : (ComplexShape.up ℕ).Rel p q
  · obtain rfl : q = p + 1 := h.symm
    exact cochainBaseChange_d k' C p
  · rw [(cochainBaseChange k' C).shape p q h, C.shape p q h]
    refine ModuleCat.hom_ext ?_
    change (0 : _ →ₗ[k'] _) = LinearMap.baseChange k' (0 : _ →ₗ[k] _)
    simp


/-- The Čech complex comparison is compatible with multiplication by a variable. -/
lemma cechMulX_cechComplexBaseChangeIso (j : Fin (n + 1)) (d : ℤ) :
    (M.baseChange k').cechMulX j d ≫ (cechComplexBaseChangeIso k' M (d + 1)).hom
      = (cechComplexBaseChangeIso k' M d).hom
        ≫ cochainBaseChangeMap k' (M.cechMulX j d) := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  change (cechCochainBaseChangeEquiv k' M p (d + 1))
      ((((M.baseChange k').cechMulX j d).f p).hom c)
    = (LinearMap.baseChange k' ((M.cechMulX j d).f p).hom)
        ((cechCochainBaseChangeEquiv k' M p d) c)
  have h := cechMulX_cechCochainBaseChangeEquiv_symm k' M j p d
    ((cechCochainBaseChangeEquiv k' M p d) c)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, LinearEquiv.apply_symm_apply]

/-! ## Right exactness: base change of a quotient -/

/-- **Right exactness**: base change of a quotient, along an arbitrary ring map.

Only the right exactness of `k' ⊗_k -` is used (`lTensor_exact` applied to
`P → V → V ⧸ P → 0`), so this holds for every `k`-algebra `k'`. -/
noncomputable def quotBaseChangeEquiv {V : Type u} [AddCommGroup V] [Module k V]
    (P : Submodule k V) :
    ((k' ⊗[k] V) ⧸ (LinearMap.range (LinearMap.baseChange k' P.subtype)))
      ≃ₗ[k'] (k' ⊗[k] (V ⧸ P)) := by
  have hsurj : Function.Surjective (LinearMap.baseChange k' P.mkQ) :=
    LinearMap.baseChange_surjective k' (Submodule.mkQ_surjective P)
  have hker : LinearMap.ker (LinearMap.baseChange k' P.mkQ)
      = LinearMap.range (LinearMap.baseChange k' P.subtype) := by
    have hex : Function.Exact (LinearMap.baseChange k' P.subtype)
        (LinearMap.baseChange k' P.mkQ) := by
      have h := lTensor_exact k' (f := P.subtype) (g := P.mkQ)
        (LinearMap.exact_subtype_mkQ P) (Submodule.mkQ_surjective P)
      intro x
      simpa only [LinearMap.baseChange_eq_ltensor] using h x
    exact LinearMap.exact_iff.mp hex
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)

/-! ## Homology naturality, at the level of explicit classes -/

/-- `moduleCatCyclesIso` is natural: it identifies the abstract cycles map with the
restriction of `τ₂` to kernels. -/
lemma moduleCatCyclesIso_naturality {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (ψ : S ⟶ T) (z : LinearMap.ker S.g.hom) :
    (T.moduleCatLeftHomologyData.i).hom
        ((ShortComplex.moduleCatCyclesIso T).hom.hom
          ((ShortComplex.cyclesMap ψ).hom
            ((ShortComplex.moduleCatCyclesIso S).inv.hom z)))
      = ψ.τ₂.hom ((S.moduleCatLeftHomologyData.i).hom z) := by
  have h1 := congrArg ModuleCat.Hom.hom (ShortComplex.moduleCatCyclesIso_hom_i T)
  have h2 := congrArg ModuleCat.Hom.hom (ShortComplex.cyclesMap_i ψ)
  have h3 := congrArg ModuleCat.Hom.hom (ShortComplex.moduleCatCyclesIso_inv_iCycles S)
  simp only [ModuleCat.hom_comp] at h1 h2 h3
  rw [← LinearMap.comp_apply, h1, ← LinearMap.comp_apply, h2]
  simp only [LinearMap.comp_apply]
  congr 1
  have h4 := LinearMap.congr_fun h3 z
  simpa only [LinearMap.comp_apply] using h4

/-- `homologyMap` computed on an explicit class. -/
lemma moduleCatHomologyIso_symm_mk_naturality {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (ψ : S ⟶ T) (z : LinearMap.ker S.g.hom)
    (hz : ψ.τ₂.hom (z : S.X₂) ∈ LinearMap.ker T.g.hom) :
    (ShortComplex.homologyMap ψ).hom
        ((ShortComplex.moduleCatHomologyIso S).toLinearEquiv.symm (Submodule.Quotient.mk z))
      = (ShortComplex.moduleCatHomologyIso T).toLinearEquiv.symm
          (Submodule.Quotient.mk ⟨ψ.τ₂.hom (z : S.X₂), hz⟩) := by
  have h1 := congrArg ModuleCat.Hom.hom (ShortComplex.moduleCatCyclesIso_inv_π S)
  have h2 := congrArg ModuleCat.Hom.hom (ShortComplex.homologyπ_naturality ψ)
  have h3 := congrArg ModuleCat.Hom.hom (ShortComplex.π_moduleCatCyclesIso_hom T)
  simp only [ModuleCat.hom_comp] at h1 h2 h3
  have e1 : (ShortComplex.moduleCatHomologyIso S).toLinearEquiv.symm
        (Submodule.Quotient.mk z)
      = S.homologyπ.hom ((ShortComplex.moduleCatCyclesIso S).inv.hom z) :=
    (LinearMap.congr_fun h1 z).symm
  rw [e1, ← LinearMap.comp_apply, h2, LinearMap.comp_apply]
  refine (ShortComplex.moduleCatHomologyIso T).toLinearEquiv.injective ?_
  rw [LinearEquiv.apply_symm_apply]
  change (ShortComplex.moduleCatHomologyIso T).hom.hom
    (T.homologyπ.hom ((ShortComplex.cyclesMap ψ).hom
      ((ShortComplex.moduleCatCyclesIso S).inv.hom z))) = _
  rw [← LinearMap.comp_apply, h3, LinearMap.comp_apply]
  change Submodule.Quotient.mk ((ShortComplex.moduleCatCyclesIso T).hom.hom
    ((ShortComplex.cyclesMap ψ).hom
      ((ShortComplex.moduleCatCyclesIso S).inv.hom z))) = _
  congr 1
  exact Subtype.ext (moduleCatCyclesIso_naturality ψ z)

/-- The base change of a supremum of ranges is the supremum of the base-changed ranges. -/
lemma range_baseChange_subtype_iSup {ι : Type u} {U V : Type u} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] (f : ι → (U →ₗ[k] V)) :
    LinearMap.range (LinearMap.baseChange k' (⨆ i, LinearMap.range (f i)).subtype)
      = ⨆ i, LinearMap.range (LinearMap.baseChange k' (f i)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
        rw [LinearMap.baseChange_tmul]
        refine Submodule.iSup_induction (fun i => LinearMap.range (f i))
          (motive := fun q => (a ⊗ₜ[k] q) ∈
            ⨆ i, LinearMap.range (LinearMap.baseChange k' (f i))) p.2 ?_ ?_ ?_
        · rintro i _ ⟨u, rfl⟩
          exact Submodule.mem_iSup_of_mem i ⟨a ⊗ₜ[k] u, by rw [LinearMap.baseChange_tmul]⟩
        · simp
        · intro p q hp hq
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hp hq
    | add p q hp hq =>
        rw [map_add]
        exact Submodule.add_mem _ hp hq
  · refine iSup_le fun i => ?_
    rintro _ ⟨z, rfl⟩
    have hle : LinearMap.range (f i) ≤ ⨆ i', LinearMap.range (f i') :=
      le_iSup (fun i' => LinearMap.range (f i')) i
    refine ⟨LinearMap.baseChange k' (LinearMap.codRestrict (⨆ i, LinearMap.range (f i)) (f i)
      (fun u => hle ⟨u, rfl⟩)) z, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl

/-- If the multiplication span of a base change is everything, then so is the image of the
base-changed inclusion of the multiplication span. -/
lemma range_baseChange_mulSpan_subtype_eq_top (V : GradedModule k n) (d e : ℤ)
    (h : (V.baseChange k').mulSpan d e = ⊤) :
    LinearMap.range (LinearMap.baseChange k' (V.mulSpan d e).subtype) = ⊤ := by
  refine top_le_iff.mp ?_
  refine le_trans (le_of_eq h.symm) (iSup_le fun l => ?_)
  rw [baseChange_mulList k' V l.1 d e l.2]
  rintro _ ⟨z, rfl⟩
  refine ⟨LinearMap.baseChange k' (LinearMap.codRestrict (V.mulSpan d e)
    ((V.mulList l.1 d e l.2).hom)
    (fun u => le_mulSpan V d e l.1 l.2 ⟨u, rfl⟩)) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
