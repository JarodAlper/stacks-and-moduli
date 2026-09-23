module

public import StacksAndModuli.API.ProjectiveGradedLocalization
public import StacksAndModuli.API.ProjectiveGradedFlat

/-!
# Localizing at a pair of variables

The degree-`d` piece of `M[1/(x_a x_b)]` is the colimit of `M` along multiplication by
`(x_a x_b)`, whereas `(M[1/x_a])[1/x_b]` is the corresponding *double* colimit.  The diagonal
is cofinal in the square, so the comparison `pairLocMap` from the first to the second is an
isomorphism. Both injectivity and surjectivity are proved explicitly, and `pairLocEquiv`
packages the resulting linear equivalence.

That last statement is the point of the file.  Localization at a single variable is computed
by the charts `D₊(x_a)` of `Proj`, so it is often possible to prove that a morphism of graded
modules becomes degreewise *bijective* after inverting one variable.  The Čech criterion
`GradedModule.isIso_cechHgrMap_app_zero_of_injective`, however, also asks for *injectivity* on
the overlaps `D₊(x_a x_b)`; `injective_locMap_pair_app` supplies exactly that, with no further
hypotheses, by localizing the single-variable statement once more. More generally,
`bijective_locMap_app_of_singleton_bijective` propagates single-variable bijectivity to every
nonempty list and feeds the all-degree Čech comparison.

Main declarations:
- `GradedModule.pairLocStage` and `GradedModule.locTr_pairLocStage`, the cofinal diagonal;
- `GradedModule.pairLocMap`, the comparison, and `GradedModule.pairLocMap_naturality`;
- `GradedModule.injective_pairLocMap`, `GradedModule.surjective_pairLocMap`, and
  `GradedModule.pairLocEquiv`;
- `GradedModule.injective_locMap_pair_app`;
- `GradedModule.bijective_locMap_app_of_singleton_bijective`;
- `GradedModule.bijective_locMap_app_of_eq`, `GradedModule.bijective_locMap_app_of_list_eq` and
  `GradedModule.injective_locMap_app_of_list_eq`, transport along equal degrees and equal
  lists (the Čech index of a `p`-simplex is a list, and `rw`-ing it changes a type);
- `GradedModule.flat_loc_cons` and `GradedModule.flat_cechCochain_of_flat_loc`, which propagate
  flatness from the chart localizations to the Čech cochains.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Degree bookkeeping: stage `t` of the `l₁ ++ l₂`-tower over `d` is stage `t` of the
`l₁`-tower over stage `t` of the `l₂`-tower. -/
lemma locDeg_pair (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) (t : ℕ) :
    locDeg (l₁ ++ l₂) d t = locDeg l₁ (locDeg l₂ d t) t := by
  simp only [locDeg_def, List.length_append]
  push_cast
  ring

/-- The stage map of the comparison `M.loc (l₁ ++ l₂) ⟶ (M.loc l₁).loc l₂`. -/
noncomputable def pairLocStage (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ)
    (t : ℕ) :
    M.obj (locDeg (l₁ ++ l₂) d t) ⟶ ((M.loc l₁).loc l₂).obj d :=
  eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t)) ≫
    M.locIncl l₁ (locDeg l₂ d t) t ≫ (M.loc l₁).locIncl l₂ d t

lemma locTr_pairLocStage (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ)
    (t t' : ℕ) (h : t ≤ t') :
    M.locTr (l₁ ++ l₂) d t t' h ≫ pairLocStage M l₁ l₂ d t' = pairLocStage M l₁ l₂ d t := by
  have hlen : ∀ (l : List (Fin (n + 1))) (e : ℤ) (s s' : ℕ), s ≤ s' →
      locDeg l e s + ((listPow l (s' - s)).length : ℤ) = locDeg l e s' := by
    intro l e s s' hs
    rw [listPow_length, locDeg_def, locDeg_def]
    push_cast [Nat.cast_sub hs]
    ring
  have step1 : pairLocStage M l₁ l₂ d t
      = eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t)) ≫
        (M.locIncl l₁ (locDeg l₂ d t) t ≫ (M.loc l₁).locTr l₂ d t t' h) ≫
        (M.loc l₁).locIncl l₂ d t' := by
    rw [pairLocStage, Category.assoc, locTr_locIncl]
  have step2 : M.locIncl l₁ (locDeg l₂ d t) t ≫ (M.loc l₁).locTr l₂ d t t' h
      = M.mulList (listPow l₂ (t' - t)) (locDeg l₁ (locDeg l₂ d t) t)
          (locDeg l₁ (locDeg l₂ d t') t)
          (by
            simp only [locDeg_def, listPow_length]
            push_cast [Nat.cast_sub h]; ring) ≫
        M.locIncl l₁ (locDeg l₂ d t') t := by
    rw [locTr]
    exact locIncl_mulList M l₁ (listPow l₂ (t' - t)) (locDeg l₂ d t) (locDeg l₂ d t')
      (hlen l₂ d t t' h) t
  have step3 : M.locIncl l₁ (locDeg l₂ d t') t
      = M.locTr l₁ (locDeg l₂ d t') t t' h ≫ M.locIncl l₁ (locDeg l₂ d t') t' :=
    (locTr_locIncl M l₁ (locDeg l₂ d t') t t' h).symm
  have hlenB : locDeg l₁ (locDeg l₂ d t) t + ((listPow l₂ (t' - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t') t := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub h]
    ring
  have hlenA : locDeg l₁ (locDeg l₂ d t') t + ((listPow l₁ (t' - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t') t' := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub h]
    ring
  have hlenApp : locDeg l₁ (locDeg l₂ d t) t
      + ((listPow l₂ (t' - t) ++ listPow l₁ (t' - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t') t' := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub h]
    ring
  have hlenPair : locDeg l₁ (locDeg l₂ d t) t + ((listPow (l₁ ++ l₂) (t' - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t') t' := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub h]
    ring
  have hlenC : locDeg (l₁ ++ l₂) d t + ((listPow (l₁ ++ l₂) (t' - t)).length : ℤ)
      = locDeg (l₁ ++ l₂) d t' := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub h]
    ring
  have key : M.locTr (l₁ ++ l₂) d t t' h ≫ eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t'))
      = eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t)) ≫
        M.mulList (listPow l₂ (t' - t)) (locDeg l₁ (locDeg l₂ d t) t)
            (locDeg l₁ (locDeg l₂ d t') t) hlenB ≫
          M.locTr l₁ (locDeg l₂ d t') t t' h := by
    rw [locTr, locTr,
      ← M.mulList_append (listPow l₂ (t' - t)) (listPow l₁ (t' - t))
        (locDeg l₁ (locDeg l₂ d t) t) (locDeg l₁ (locDeg l₂ d t') t)
        (locDeg l₁ (locDeg l₂ d t') t') hlenB hlenA hlenApp,
      M.mulList_perm (listPow_append_perm' l₁ l₂ (t' - t)) _ _ hlenApp hlenPair,
      M.mulList_congr_degree (listPow (l₁ ++ l₂) (t' - t)) (locDeg_pair l₁ l₂ d t)
        (locDeg_pair l₁ l₂ d t') hlenC hlenPair]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  calc M.locTr (l₁ ++ l₂) d t t' h ≫ pairLocStage M l₁ l₂ d t'
      = (M.locTr (l₁ ++ l₂) d t t' h ≫ eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t'))) ≫
          (M.locIncl l₁ (locDeg l₂ d t') t' ≫ (M.loc l₁).locIncl l₂ d t') := by
        rw [pairLocStage]; simp only [Category.assoc]
    _ = (eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t)) ≫
          M.mulList (listPow l₂ (t' - t)) (locDeg l₁ (locDeg l₂ d t) t)
              (locDeg l₁ (locDeg l₂ d t') t) hlenB ≫
            M.locTr l₁ (locDeg l₂ d t') t t' h) ≫
          (M.locIncl l₁ (locDeg l₂ d t') t' ≫ (M.loc l₁).locIncl l₂ d t') := by
        rw [key]
    _ = pairLocStage M l₁ l₂ d t := by
        rw [step1, step2, step3]; simp only [Category.assoc]

/-- Degreewise transport commutes with a morphism of graded modules. -/
lemma app_comp_eqToHom {M N : GradedModule k n} (φ : M ⟶ N) {c a : ℤ} (hca : c = a) :
    φ.app c ≫ eqToHom (congrArg N.obj hca) =
      eqToHom (congrArg M.obj hca) ≫ φ.app a := by
  subst hca; simp

/-- **The comparison from the pair localization to the iterated localization.** -/
noncomputable def pairLocMap (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) :
    (M.loc (l₁ ++ l₂)).obj d ⟶ ((M.loc l₁).loc l₂).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun t : ℕ => M.obj (locDeg (l₁ ++ l₂) d t))
    (fun t t' h => (M.locTr (l₁ ++ l₂) d t t' h).hom)
    (fun t => (pairLocStage M l₁ l₂ d t).hom)
    (fun t t' htt' x => by
      have h1 := congrArg ModuleCat.Hom.hom (locTr_pairLocStage M l₁ l₂ d t t' htt')
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

/-- The comparison restricted to a stage is the stage map. -/
lemma locIncl_pairLocMap (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) (t : ℕ) :
    M.locIncl (l₁ ++ l₂) d t ≫ pairLocMap M l₁ l₂ d = pairLocStage M l₁ l₂ d t := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, pairLocMap, locIncl,
    ModuleCat.hom_ofHom]
  exact Module.DirectLimit.lift_of _ _ _

/-- The stage maps are natural in the graded module. -/
lemma pairLocStage_naturality {M N : GradedModule k n} (φ : M ⟶ N) (l₁ l₂ : List (Fin (n + 1)))
    (d : ℤ) (t : ℕ) :
    φ.app (locDeg (l₁ ++ l₂) d t) ≫ pairLocStage N l₁ l₂ d t
      = pairLocStage M l₁ l₂ d t ≫ (locMap l₂ (locMap l₁ φ)).app d := by
  rw [pairLocStage, pairLocStage, ← Category.assoc, app_comp_eqToHom φ (locDeg_pair l₁ l₂ d t)]
  simp only [Category.assoc]
  rw [locIncl_locMap (M.loc l₁) l₂ (locMap l₁ φ) d t]
  slice_rhs 2 3 => rw [locIncl_locMap M l₁ φ (locDeg l₂ d t) t]
  simp only [Category.assoc]

/-- **The comparison is natural in the graded module.** -/
theorem pairLocMap_naturality {M N : GradedModule k n} (φ : M ⟶ N) (l₁ l₂ : List (Fin (n + 1)))
    (d : ℤ) :
    (locMap (l₁ ++ l₂) φ).app d ≫ pairLocMap N l₁ l₂ d
      = pairLocMap M l₁ l₂ d ≫ (locMap l₂ (locMap l₁ φ)).app d := by
  refine ModuleCat.hom_ext ?_
  refine Module.DirectLimit.hom_ext fun t => ?_
  have e1 : M.locIncl (l₁ ++ l₂) d t ≫ (locMap (l₁ ++ l₂) φ).app d ≫ pairLocMap N l₁ l₂ d
      = pairLocStage M l₁ l₂ d t ≫ (locMap l₂ (locMap l₁ φ)).app d := by
    rw [← Category.assoc, locIncl_locMap M (l₁ ++ l₂) φ d t, Category.assoc,
      locIncl_pairLocMap N l₁ l₂ d t, pairLocStage_naturality φ l₁ l₂ d t]
  have e2 : M.locIncl (l₁ ++ l₂) d t ≫ pairLocMap M l₁ l₂ d ≫ (locMap l₂ (locMap l₁ φ)).app d
      = pairLocStage M l₁ l₂ d t ≫ (locMap l₂ (locMap l₁ φ)).app d := by
    rw [← Category.assoc, locIncl_pairLocMap M l₁ l₂ d t]
  exact congrArg ModuleCat.Hom.hom (e1.trans e2.symm)

/-- **The comparison is injective.**  Cofinality of the diagonal in the double tower. -/
theorem injective_pairLocMap (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) :
    Function.Injective ((pairLocMap M l₁ l₂ d).hom) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨t, x, rfl⟩ := locIncl_exists M (l₁ ++ l₂) d z
  have hstage : (pairLocStage M l₁ l₂ d t).hom x = 0 := by
    have h1 := congrArg ModuleCat.Hom.hom (locIncl_pairLocMap M l₁ l₂ d t)
    simp only [ModuleCat.hom_comp] at h1
    exact (LinearMap.congr_fun h1 x).symm.trans hz
  set x' := (eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d t))).hom x with hx'
  have hexp : (pairLocStage M l₁ l₂ d t).hom x
      = (((M.loc l₁).locIncl l₂ d t).hom
          ((M.locIncl l₁ (locDeg l₂ d t) t).hom x')) := by
    simp only [pairLocStage, ModuleCat.hom_comp, LinearMap.comp_apply, hx']
  rw [hexp] at hstage
  obtain ⟨t₁, ht₁, h₁⟩ := locIncl_eq_zero (M.loc l₁) l₂ d t _ hstage
  have hlen1 : locDeg l₂ d t + ((listPow l₂ (t₁ - t)).length : ℤ) = locDeg l₂ d t₁ := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub ht₁]
    ring
  have hAB : locDeg l₁ (locDeg l₂ d t) t + ((listPow l₂ (t₁ - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t₁) t := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub ht₁]
    ring
  rw [locTr] at h₁
  have hmul := congrArg ModuleCat.Hom.hom
    (locIncl_mulList M l₁ (listPow l₂ (t₁ - t)) (locDeg l₂ d t) (locDeg l₂ d t₁) hlen1 t)
  simp only [ModuleCat.hom_comp] at hmul
  have hmul' := LinearMap.congr_fun hmul x'
  simp only [LinearMap.comp_apply] at hmul'
  rw [hmul'] at h₁
  obtain ⟨s, hs, h₃⟩ := locIncl_eq_zero M l₁ (locDeg l₂ d t₁) t _ h₁
  rw [locTr] at h₃
  -- the four exponents and the common upper stage
  set u := max t₁ s with hu
  have htu : t ≤ u := le_trans ht₁ (le_max_left _ _)
  have ht₁u : t₁ ≤ u := le_max_left _ _
  have hsu : s ≤ u := le_max_right _ _
  have hpp' : (t₁ - t) + (u - t₁) = u - t := by omega
  have hqq' : (s - t) + (u - s) = u - t := by omega
  have hBC : locDeg l₁ (locDeg l₂ d t₁) t + ((listPow l₁ (s - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t₁) s := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub hs]
    ring
  have hf3 : locDeg l₁ (locDeg l₂ d t₁) s
      + ((listPow l₁ (u - s) ++ listPow l₂ (u - t₁)).length : ℤ) = locDeg (l₁ ++ l₂) d u := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub hsu, Nat.cast_sub ht₁u]
    ring
  have hX : locDeg l₁ (locDeg l₂ d t) t
      + ((listPow l₂ (t₁ - t) ++ listPow l₁ (s - t)).length : ℤ)
      = locDeg l₁ (locDeg l₂ d t₁) s := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub ht₁, Nat.cast_sub hs]
    ring
  have hBig : locDeg l₁ (locDeg l₂ d t) t
      + (((listPow l₂ (t₁ - t) ++ listPow l₁ (s - t))
          ++ (listPow l₁ (u - s) ++ listPow l₂ (u - t₁))).length : ℤ)
      = locDeg (l₁ ++ l₂) d u := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub ht₁, Nat.cast_sub hs, Nat.cast_sub hsu, Nat.cast_sub ht₁u]
    ring
  have hPair : locDeg l₁ (locDeg l₂ d t) t + ((listPow (l₁ ++ l₂) (u - t)).length : ℤ)
      = locDeg (l₁ ++ l₂) d u := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub htu]
    ring
  have hC : locDeg (l₁ ++ l₂) d t + ((listPow (l₁ ++ l₂) (u - t)).length : ℤ)
      = locDeg (l₁ ++ l₂) d u := by
    simp only [locDeg_def, listPow_length, List.length_append]
    push_cast [Nat.cast_sub htu]
    ring
  have hbig : (M.mulList ((listPow l₂ (t₁ - t) ++ listPow l₁ (s - t))
      ++ (listPow l₁ (u - s) ++ listPow l₂ (u - t₁)))
      (locDeg l₁ (locDeg l₂ d t) t) (locDeg (l₁ ++ l₂) d u) hBig).hom x' = 0 := by
    rw [M.mulList_append _ _ _ (locDeg l₁ (locDeg l₂ d t₁) s) _ hX hf3 hBig,
      M.mulList_append _ _ _ (locDeg l₁ (locDeg l₂ d t₁) t) _ hAB hBC hX]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h₃, map_zero]
  have hperm : ((listPow l₂ (t₁ - t) ++ listPow l₁ (s - t))
      ++ (listPow l₁ (u - s) ++ listPow l₂ (u - t₁))).Perm (listPow (l₁ ++ l₂) (u - t)) := by
    have e1 : listPow l₁ (u - t) = listPow l₁ (s - t) ++ listPow l₁ (u - s) := by
      rw [← hqq', listPow_add]
    have e2 : listPow l₂ (u - t) = listPow l₂ (t₁ - t) ++ listPow l₂ (u - t₁) := by
      rw [← hpp', listPow_add]
    refine List.Perm.trans ?_ (listPow_append_perm l₁ l₂ (u - t)).symm
    rw [e1, e2]
    refine List.perm_iff_count.mpr fun c => ?_
    simp only [List.count_append]
    omega
  rw [M.mulList_perm hperm _ _ hBig hPair] at hbig
  have hfin : (M.locTr (l₁ ++ l₂) d t u htu).hom x = 0 := by
    rw [locTr, mulList_congr_degree M (listPow (l₁ ++ l₂) (u - t)) (locDeg_pair l₁ l₂ d t) rfl
      hC hPair]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, eqToHom_refl, ModuleCat.id_apply]
    exact hbig
  have hli := congrArg ModuleCat.Hom.hom (locTr_locIncl M (l₁ ++ l₂) d t u htu)
  simp only [ModuleCat.hom_comp] at hli
  rw [← LinearMap.congr_fun hli x]
  simp only [LinearMap.comp_apply, hfin, map_zero]

/-- Transport of degreewise bijectivity along an equality of degrees. -/
lemma bijective_locMap_app_of_eq {M N : GradedModule k n} (φ : M ⟶ N)
    (l : List (Fin (n + 1))) {d d' : ℤ} (hdd : d = d')
    (h : Function.Bijective (((locMap l φ).app d').hom)) :
    Function.Bijective (((locMap l φ).app d).hom) := by
  subst hdd; exact h

/-- Transport of degreewise bijectivity along an equality of lists. -/
lemma bijective_locMap_app_of_list_eq {M N : GradedModule k n} (φ : M ⟶ N)
    {l l' : List (Fin (n + 1))} (hll : l = l') (d : ℤ)
    (h : Function.Bijective (((locMap l' φ).app d).hom)) :
    Function.Bijective (((locMap l φ).app d).hom) := by
  subst hll; exact h

/-- Transport of degreewise injectivity along an equality of lists. -/
lemma injective_locMap_app_of_list_eq {M N : GradedModule k n} (φ : M ⟶ N)
    {l l' : List (Fin (n + 1))} (hll : l = l') (d : ℤ)
    (h : Function.Injective (((locMap l' φ).app d).hom)) :
    Function.Injective (((locMap l φ).app d).hom) := by
  subst hll; exact h

/-- **Localizing at a pair of variables preserves injectivity.**  If `φ` becomes
bijective after localizing at `x_a`, in every degree `d + t` with `t : ℕ`, then localizing at
`x_a x_b` makes it injective in degree `d`.  Proved by comparing `M[1/x_a x_b]` with
`(M[1/x_a])[1/x_b]`.

The degrees `d + t`, rather than all of `ℤ`, are what the `[b]`-tower over `d` visits; this
matters because the chart comparison over a base change is available only in non-negative
degrees. -/
theorem injective_locMap_pair_app {M N : GradedModule k n} (φ : M ⟶ N)
    (a b : Fin (n + 1)) (d : ℤ)
    (h : ∀ t : ℕ, Function.Bijective (((locMap [a] φ).app (d + (t : ℤ))).hom)) :
    Function.Injective (((locMap [a, b] φ).app d).hom) := by
  have hb : Function.Bijective (((locMap [b] (locMap [a] φ)).app d).hom) :=
    bijective_locMap_app_of_bijective (M.loc [a]) (locMap [a] φ) [b] d fun t =>
      bijective_locMap_app_of_eq φ [a]
        (by simp only [locDeg_def, List.length_cons, List.length_nil]; push_cast; ring)
        (h t)
  have hnat := congrArg ModuleCat.Hom.hom (pairLocMap_naturality φ [a] [b] d)
  simp only [ModuleCat.hom_comp] at hnat
  have hcomp : Function.Injective
      ⇑((pairLocMap N [a] [b] d).hom ∘ₗ ((locMap ([a] ++ [b]) φ).app d).hom) := by
    rw [hnat]
    simp only [LinearMap.coe_comp]
    exact hb.injective.comp (injective_pairLocMap M [a] [b] d)
  simp only [LinearMap.coe_comp] at hcomp
  exact hcomp.of_comp

/-- **The comparison is surjective.**  The other half of cofinality: an element of the double
tower is reached at some pair of stages, and both are pushed up to their maximum. -/
theorem surjective_pairLocMap (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) :
    Function.Surjective ((pairLocMap M l₁ l₂ d).hom) := by
  intro z
  obtain ⟨t, y, rfl⟩ := locIncl_exists (M.loc l₁) l₂ d z
  obtain ⟨s, x, rfl⟩ := locIncl_exists M l₁ (locDeg l₂ d t) y
  set u := max t s with hu
  have htu : t ≤ u := le_max_left _ _
  have hsu : s ≤ u := le_max_right _ _
  have hlen : locDeg l₂ d t + ((listPow l₂ (u - t)).length : ℤ) = locDeg l₂ d u := by
    simp only [locDeg_def, listPow_length]
    push_cast [Nat.cast_sub htu]
    ring
  set x₁ := (M.locTr l₁ (locDeg l₂ d t) s u hsu).hom x with hx₁
  set x₂ := (M.mulList (listPow l₂ (u - t)) (locDeg l₁ (locDeg l₂ d t) u)
      (locDeg l₁ (locDeg l₂ d u) u) (by
        simp only [locDeg_def, listPow_length]
        push_cast [Nat.cast_sub htu]
        ring)).hom x₁ with hx₂
  refine ⟨(M.locIncl (l₁ ++ l₂) d u).hom
    ((eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d u).symm)).hom x₂), ?_⟩
  have hstage : ∀ w : M.obj (locDeg (l₁ ++ l₂) d u),
      (pairLocMap M l₁ l₂ d).hom ((M.locIncl (l₁ ++ l₂) d u).hom w)
        = (pairLocStage M l₁ l₂ d u).hom w := by
    intro w
    have h := congrArg ModuleCat.Hom.hom (locIncl_pairLocMap M l₁ l₂ d u)
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h w
    simp only [LinearMap.comp_apply] at h2
    exact h2
  rw [hstage]
  have hcancel : ∀ w : M.obj (locDeg l₁ (locDeg l₂ d u) u),
      (pairLocStage M l₁ l₂ d u).hom
        ((eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d u).symm)).hom w)
      = ((M.loc l₁).locIncl l₂ d u).hom ((M.locIncl l₁ (locDeg l₂ d u) u).hom w) := by
    intro w
    have he : ((eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d u)) :
          M.obj (locDeg (l₁ ++ l₂) d u) ⟶ M.obj (locDeg l₁ (locDeg l₂ d u) u))).hom
        ((eqToHom (congrArg M.obj (locDeg_pair l₁ l₂ d u).symm)).hom w) = w := by
      rw [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl]
      rfl
    simp only [pairLocStage, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [he]
  rw [hcancel]
  -- now compare with the original element
  have hinner : (M.locIncl l₁ (locDeg l₂ d t) u).hom x₁
      = (M.locIncl l₁ (locDeg l₂ d t) s).hom x := by
    have h := congrArg ModuleCat.Hom.hom (locTr_locIncl M l₁ (locDeg l₂ d t) s u hsu)
    simp only [ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h x
  have houter := congrArg ModuleCat.Hom.hom
    (locIncl_mulList M l₁ (listPow l₂ (u - t)) (locDeg l₂ d t) (locDeg l₂ d u) hlen u)
  simp only [ModuleCat.hom_comp] at houter
  have hstep : ((M.loc l₁).locTr l₂ d t u htu).hom
      ((M.locIncl l₁ (locDeg l₂ d t) u).hom x₁)
      = (M.locIncl l₁ (locDeg l₂ d u) u).hom x₂ := by
    rw [locTr]
    have h := LinearMap.congr_fun houter x₁
    simp only [LinearMap.comp_apply] at h
    rw [hx₂]
    exact h
  have hfin := congrArg ModuleCat.Hom.hom (locTr_locIncl (M.loc l₁) l₂ d t u htu)
  simp only [ModuleCat.hom_comp] at hfin
  have h2 := LinearMap.congr_fun hfin ((M.locIncl l₁ (locDeg l₂ d t) u).hom x₁)
  simp only [LinearMap.comp_apply] at h2
  rw [← hstep, h2, hinner]

/-- **The comparison is an isomorphism.**  Localizing at `l₁ ++ l₂` is localizing at `l₁` and
then at `l₂`. -/
theorem bijective_pairLocMap (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) :
    Function.Bijective ((pairLocMap M l₁ l₂ d).hom) :=
  ⟨injective_pairLocMap M l₁ l₂ d, surjective_pairLocMap M l₁ l₂ d⟩

/-- The comparison as a linear equivalence. -/
noncomputable def pairLocEquiv (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d : ℤ) :
    ((M.loc (l₁ ++ l₂)).obj d) ≃ₗ[k] (((M.loc l₁).loc l₂).obj d) :=
  LinearEquiv.ofBijective _ (bijective_pairLocMap M l₁ l₂ d)

/-- **Localizing at any nonempty list of variables preserves bijectivity.**  If `φ` becomes
bijective after localizing at each single variable, in every degree `d + t` with `t : ℕ`, then
localizing at any nonempty list makes it bijective in degree `d`.  Via the comparison
between localization at the product indexed by `a :: l` and iterated localization first at
`a` and then along `l`, supplied by `pairLocEquiv`.

The degrees `d + t`, rather than all of `ℤ`, are what the tail tower over `d` visits; this
matters because the chart comparison over a base change is available only in non-negative
degrees. -/
theorem bijective_locMap_app_of_singleton_bijective {M N : GradedModule k n} (φ : M ⟶ N)
    (l : List (Fin (n + 1))) (hl : l ≠ []) (d : ℤ)
    (h : ∀ (a : Fin (n + 1)) (t : ℕ),
      Function.Bijective (((locMap [a] φ).app (d + (t : ℤ))).hom)) :
    Function.Bijective (((locMap l φ).app d).hom) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  have hb : Function.Bijective (((locMap t (locMap [a] φ)).app d).hom) := by
    refine bijective_locMap_app_of_bijective (M.loc [a]) (locMap [a] φ) t d (fun j => ?_)
    refine bijective_locMap_app_of_eq φ [a]
      (show locDeg t d j = d + ((j * t.length : ℕ) : ℤ) by
        simp only [locDeg_def]; push_cast; ring) ?_
    exact h a (j * t.length)
  have hnat := congrArg ModuleCat.Hom.hom (pairLocMap_naturality φ [a] t d)
  simp only [ModuleCat.hom_comp] at hnat
  have hMab := bijective_pairLocMap M [a] t d
  have hNab := bijective_pairLocMap N [a] t d
  have hcomp : Function.Bijective
      ⇑((pairLocMap N [a] t d).hom ∘ₗ ((locMap ([a] ++ t) φ).app d).hom) := by
    rw [hnat]
    simp only [LinearMap.coe_comp]
    exact hb.comp hMab
  simp only [LinearMap.coe_comp] at hcomp
  constructor
  · exact fun x y hxy => hcomp.1 (by simp [hxy])
  · intro y
    obtain ⟨x, hx⟩ := hcomp.2 ((pairLocMap N [a] t d).hom y)
    exact ⟨x, hNab.1 hx⟩

/-- **Flatness of a localization at a list, from flatness of the single-variable
localizations.**  If `M[1/x_a]` is degreewise flat, so is `M[1/x_{a::t}]` in every degree:
`M.loc (a :: t)` is `(M.loc [a]).loc t`, and a localization of a degreewise flat graded module
is flat (`GradedModule.IsFlat.flat_loc`). -/
theorem flat_loc_cons {R : Type u} [CommRing R] (M : GradedModule R n)
    (a : Fin (n + 1)) (t : List (Fin (n + 1))) (hflat : IsFlat (M.loc [a])) (d : ℤ) :
    Module.Flat R ((M.loc (a :: t)).obj d) := by
  haveI : Module.Flat R (((M.loc [a]).loc t).obj d) := hflat.flat_loc t d
  exact Module.Flat.of_linearEquiv (pairLocEquiv M [a] t d)

/-- Flatness of the localization at any **nonempty** list, from flatness of the
single-variable localizations. -/
theorem flat_loc_of_ne_nil {R : Type u} [CommRing R] (M : GradedModule R n)
    (hflat : ∀ a : Fin (n + 1), IsFlat (M.loc [a]))
    (l : List (Fin (n + 1))) (hl : l ≠ []) (d : ℤ) :
    Module.Flat R ((M.loc l).obj d) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact flat_loc_cons M a t (hflat a) d

/-- **Flatness of the Čech cochain groups from flatness of the chart localizations.**  This is
the hypothesis that Cohomology and Base Change really needs; it is strictly weaker than
`GradedModule.IsFlat`, and on `Proj` it holds for the graded model of a flat quotient sheaf
even though that model is not degreewise flat. -/
theorem flat_cechCochain_of_flat_loc {R : Type u} [CommRing R] (M : GradedModule R n)
    (hflat : ∀ a : Fin (n + 1), IsFlat (M.loc [a])) (p : ℕ) (d : ℤ) :
    Module.Flat R (M.cechCochain p d) := by
  classical
  haveI : ∀ τ : CechIdx n p, Module.Flat R ((M.loc τ.toList).obj d) := by
    intro τ
    refine flat_loc_of_ne_nil M hflat τ.toList ?_ d
    intro h
    have := τ.length_eq
    rw [h] at this
    simp at this
  exact Module.Flat.pi (fun τ : CechIdx n p => (((M.loc τ.toList).obj d : Type u)))

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
