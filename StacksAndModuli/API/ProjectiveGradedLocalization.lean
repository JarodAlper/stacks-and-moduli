module

public import StacksAndModuli.API.ProjectiveGradedModule
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Localization of graded modules at products of variables

Supporting API with no Stacks Project counterpart, developed towards the graded Čech
complex of the standard affine cover of `ℙⁿ` (the construction obligation
`Cohomology.nonempty` of `StacksAndModuli/API/ProjectiveGradedCohomology.lean`).

For a graded module `M` over `S = k[x₀, …, xₙ]` in the graded-piece encoding of
`API/ProjectiveGradedModule.lean` and a list `l` of variables, the localization
`M[1/x_l]` at the product `x_l` of the entries of `l` is again a graded module: its
degree-`d` piece is the sequential direct limit of
`M_d → M_{d + |l|} → M_{d + 2|l|} → ⋯` along multiplication by `x_l`.  This file
constructs the localization (`GradedModule.loc`), the localization map
(`GradedModule.locOf`), its functoriality (`GradedModule.locMap`), and proves that
localization preserves degreewise short exact sequences (`GradedModule.loc_shortExact`)
— sequential direct limits of modules are exact.

Main declarations:
- `GradedModule.listPow`, `GradedModule.mulX'_mulList_comm`;
- `GradedModule.loc`, `GradedModule.locOf`, `GradedModule.locMap`;
- `GradedModule.loc_shortExact`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ## Iterated lists and commutation of iterated multiplication -/

/-- The list `l` repeated `m` times; multiplication by its entries is multiplication by
`x_l^m`. -/
def listPow (l : List (Fin (n + 1))) (m : ℕ) : List (Fin (n + 1)) :=
  (List.replicate m l).flatten

@[simp] lemma listPow_zero (l : List (Fin (n + 1))) : listPow l 0 = [] := rfl

lemma listPow_add (l : List (Fin (n + 1))) (a b : ℕ) :
    listPow l (a + b) = listPow l a ++ listPow l b := by
  unfold listPow
  rw [List.replicate_add, List.flatten_append]

@[simp] lemma listPow_one (l : List (Fin (n + 1))) : listPow l 1 = l := by
  simp [listPow]

/-- The monomial list of a concatenation is a permutation of the concatenated monomial
lists. -/
lemma listPow_append_perm (l₁ l₂ : List (Fin (n + 1))) (m : ℕ) :
    (listPow (l₁ ++ l₂) m).Perm (listPow l₁ m ++ listPow l₂ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : listPow (l₁ ++ l₂) (m + 1) = (l₁ ++ l₂) ++ listPow (l₁ ++ l₂) m := by
        rw [show m + 1 = 1 + m from Nat.add_comm m 1, listPow_add, listPow_one]
      have h2 : listPow l₁ (m + 1) = l₁ ++ listPow l₁ m := by
        rw [show m + 1 = 1 + m from Nat.add_comm m 1, listPow_add, listPow_one]
      have h3 : listPow l₂ (m + 1) = l₂ ++ listPow l₂ m := by
        rw [show m + 1 = 1 + m from Nat.add_comm m 1, listPow_add, listPow_one]
      rw [h1, h2, h3]
      refine (ih.append_left (l₁ ++ l₂)).trans ?_
      simp only [List.append_assoc]
      refine List.Perm.append_left l₁ ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- The multiplicity of a variable in `listPow l m`. -/
lemma listPow_count (l : List (Fin (n + 1))) (m : ℕ) (c : Fin (n + 1)) :
    (listPow l m).count c = m * l.count c := by
  induction m with
  | zero => simp
  | succ a ih =>
      rw [show a + 1 = 1 + a from Nat.add_comm a 1, listPow_add, listPow_one,
        List.count_append, ih]
      ring

/-- The two orders in which the monomials of two lists of coordinates can be collected. -/
lemma listPow_append_perm' (l₁ l₂ : List (Fin (n + 1))) (m : ℕ) :
    (listPow l₂ m ++ listPow l₁ m).Perm (listPow (l₁ ++ l₂) m) :=
  List.perm_append_comm.trans (listPow_append_perm l₁ l₂ m).symm

/-- The two orders in which the monomials of a pair of coordinates can be collected. -/
lemma listPow_pair_perm (i k : Fin (n + 1)) (m : ℕ) :
    (listPow [k] m ++ listPow [i] m).Perm (listPow [i, k] m) := by
  refine List.Perm.trans List.perm_append_comm ?_
  exact (listPow_append_perm [i] [k] m).symm

@[simp] lemma listPow_length (l : List (Fin (n + 1))) (m : ℕ) :
    (listPow l m).length = m * l.length := by
  induction m with
  | zero => simp
  | succ a ih =>
      rw [show a + 1 = 1 + a from by omega, listPow_add]
      simp only [List.length_append, ih]
      have : listPow l 1 = l := by simp [listPow]
      rw [this]
      ring

/-- Multiplication by a single variable commutes with iterated multiplication by a list
of variables, in degree-transported form. -/
lemma mulX'_mulList_comm (M : GradedModule k n) (i : Fin (n + 1))
    (l : List (Fin (n + 1))) (d e e' f : ℤ)
    (h₁ : d + 1 = e) (h₂ : e + (l.length : ℤ) = f)
    (h₁' : d + (l.length : ℤ) = e') (h₂' : e' + 1 = f) :
    M.mulX' i d e h₁ ≫ M.mulList l e f h₂ =
      M.mulList l d e' h₁' ≫ M.mulX' i e' f h₂' := by
  induction l generalizing d e e' f with
  | nil =>
      have he' : e' = d := by simpa using h₁'.symm
      subst he'
      have hf : f = e := by simpa using h₂.symm
      subst hf
      subst h₁
      simp [mulList]
  | cons a t ih =>
      have h₁t : (d + 1) + 1 = e + 1 := by omega
      have h₂t : (e + 1) + (t.length : ℤ) = f := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h₂
        omega
      have h₁t' : (d + 1) + (t.length : ℤ) = e' := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h₁'
        omega
      simp only [mulList]
      rw [show M.mulX a e = M.mulX' a e (e + 1) rfl from (M.mulX'_rfl a e).symm,
        ← Category.assoc, mulX'_comm M i a d e (d + 1) (e + 1) h₁ rfl rfl h₁t,
        Category.assoc,
        ih (d + 1) (e + 1) e' f h₁t h₂t h₁t' h₂',
        show M.mulX a d = M.mulX' a d (d + 1) rfl from (M.mulX'_rfl a d).symm,
        ← Category.assoc]

/-- Iterated multiplications by two lists of variables commute, in degree-transported
form. -/
lemma mulList_mulList_comm (M : GradedModule k n)
    (l₁ l₂ : List (Fin (n + 1))) (d e e' f : ℤ)
    (h₁ : d + (l₁.length : ℤ) = e) (h₂ : e + (l₂.length : ℤ) = f)
    (h₁' : d + (l₂.length : ℤ) = e') (h₂' : e' + (l₁.length : ℤ) = f) :
    M.mulList l₁ d e h₁ ≫ M.mulList l₂ e f h₂ =
      M.mulList l₂ d e' h₁' ≫ M.mulList l₁ e' f h₂' := by
  induction l₁ generalizing d e e' f with
  | nil =>
      have hde : d = e := by simpa using h₁
      subst hde
      have hfe : f = e' := by
        simp only [List.length_nil, Nat.cast_zero] at h₂'
        omega
      subst hfe
      simp only [mulList, eqToHom_refl, Category.id_comp, Category.comp_id]
  | cons a t ih =>
      have h₁t : (d + 1) + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h₁
        omega
      have h₂t' : (e' + 1) + (t.length : ℤ) = f := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h₂'
        omega
      have hmid : (d + 1) + (l₂.length : ℤ) = e' + 1 := by omega
      simp only [mulList, Category.assoc]
      rw [ih (d + 1) e (e' + 1) f h₁t h₂ hmid h₂t']
      rw [show M.mulX a d = M.mulX' a d (d + 1) rfl from (M.mulX'_rfl a d).symm,
        show M.mulX a e' = M.mulX' a e' (e' + 1) rfl from (M.mulX'_rfl a e').symm,
        ← Category.assoc, ← Category.assoc,
        mulX'_mulList_comm M a l₂ d (d + 1) e' (e' + 1) rfl hmid h₁' rfl]

/-- `mulList` depends on the list only up to equality (the degree proofs are
irrelevant). -/
lemma mulList_congr_list (M : GradedModule k n) {L L' : List (Fin (n + 1))}
    (hL : L = L') (d e : ℤ) (h : d + (L.length : ℤ) = e)
    (h' : d + (L'.length : ℤ) = e) :
    M.mulList L d e h = M.mulList L' d e h' := by
  subst hL
  rfl

/-- `mulList` of a trivial list is the identity transport. -/
lemma mulList_of_eq_nil (M : GradedModule k n) {L : List (Fin (n + 1))}
    (hL : L = []) (d e : ℤ) (h : d + (L.length : ℤ) = e) :
    M.mulList L d e h =
      eqToHom (congrArg M.obj (by subst hL; simpa using h)) := by
  subst hL
  rfl

/-- Transport on both sides of a single multiplication. -/
lemma eqToHom_mulX' (M : GradedModule k n) (i : Fin (n + 1)) {a b d : ℤ}
    (ha : d = a) (hb : d + 1 = b) (h : a + 1 = b) :
    eqToHom (congrArg M.obj ha) ≫ M.mulX' i a b h =
      M.mulX i d ≫ eqToHom (congrArg M.obj hb) := by
  subst ha
  subst hb
  simp [mulX']

/-- `mulList` is invariant under permutation of the list, in degree-transported
form: the variables commute. -/
lemma mulList_perm (M : GradedModule k n) {L L' : List (Fin (n + 1))}
    (hp : L.Perm L') (d e : ℤ) (h : d + (L.length : ℤ) = e)
    (h' : d + (L'.length : ℤ) = e) :
    M.mulList L d e h = M.mulList L' d e h' := by
  induction hp generalizing d e with
  | nil =>
      rfl
  | cons a hp ih =>
      rename_i t t'
      have ht : (d + 1) + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      have ht' : (d + 1) + (t'.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h'
        omega
      simp only [mulList]
      rw [show M.mulList t (d + 1) e ht = M.mulList t' (d + 1) e ht' from
        ih (d + 1) e ht ht']
  | swap a b t =>
      have h2 : (d + 1) + 1 = d + 2 := by ring
      have ht : (d + 2) + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      simp only [mulList]
      rw [show M.mulX b d = M.mulX' b d (d + 1) rfl from (M.mulX'_rfl b d).symm,
        show M.mulX a d = M.mulX' a d (d + 1) rfl from (M.mulX'_rfl a d).symm,
        show M.mulX a (d + 1) = M.mulX' a (d + 1) (d + 1 + 1) rfl from
          (M.mulX'_rfl a (d + 1)).symm,
        show M.mulX b (d + 1) = M.mulX' b (d + 1) (d + 1 + 1) rfl from
          (M.mulX'_rfl b (d + 1)).symm,
        ← Category.assoc, ← Category.assoc,
        mulX'_comm M b a d (d + 1) (d + 1) (d + 1 + 1) rfl rfl rfl rfl]
  | trans hp₁ hp₂ ih₁ ih₂ =>
      rename_i t₁ t₂ t₃
      have hmid : d + (t₂.length : ℤ) = e := by
        rw [hp₂.length_eq]
        exact h'
      rw [ih₁ d e h hmid, ih₂ d e hmid h']

/-- `mulList` transported along equal degrees. -/
lemma mulList_congr_degree (M : GradedModule k n) (L : List (Fin (n + 1)))
    {d d' e e' : ℤ} (hd : d = d') (he : e = e')
    (h : d + (L.length : ℤ) = e) (h' : d' + (L.length : ℤ) = e') :
    M.mulList L d e h =
      eqToHom (congrArg M.obj hd) ≫ M.mulList L d' e' h' ≫
        eqToHom (congrArg M.obj he.symm) := by
  subst hd
  subst he
  simp

/-! ## The localization tower -/

/-- Degree of the `j`-th stage of the localization tower at `x_l` over degree `d`. -/
def locDeg (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) : ℤ :=
  d + (j : ℤ) * (l.length : ℤ)

@[simp] lemma locDeg_def (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    locDeg l d j = d + (j : ℤ) * (l.length : ℤ) := rfl

variable (M : GradedModule k n) (l : List (Fin (n + 1)))

/-- Transition map of the localization tower: multiplication by `x_l^{j'-j}`. -/
def locTr (d : ℤ) (j j' : ℕ) (h : j ≤ j') :
    M.obj (locDeg l d j) ⟶ M.obj (locDeg l d j') :=
  M.mulList (listPow l (j' - j)) (locDeg l d j) (locDeg l d j') (by
    rw [listPow_length, locDeg_def, locDeg_def]
    push_cast [Nat.cast_sub h]
    ring)

/-- The transition map at equal stages is the identity. -/
lemma locTr_self (d : ℤ) (j : ℕ) : M.locTr l d j j le_rfl = 𝟙 _ := by
  rw [locTr, mulList_of_eq_nil M (by rw [Nat.sub_self, listPow_zero])]
  simp

/-- Transition maps of the localization tower compose. -/
lemma locTr_trans (d : ℤ) (j₁ j₂ j₃ : ℕ) (h₁₂ : j₁ ≤ j₂) (h₂₃ : j₂ ≤ j₃) :
    M.locTr l d j₁ j₂ h₁₂ ≫ M.locTr l d j₂ j₃ h₂₃ =
      M.locTr l d j₁ j₃ (h₁₂.trans h₂₃) := by
  rw [locTr, locTr, locTr,
    ← M.mulList_append (listPow l (j₂ - j₁)) (listPow l (j₃ - j₂))
      (locDeg l d j₁) (locDeg l d j₂) (locDeg l d j₃) _ _
      (by
        rw [List.length_append, listPow_length, listPow_length,
          locDeg_def, locDeg_def]
        push_cast [Nat.cast_sub h₁₂, Nat.cast_sub h₂₃]
        ring)]
  exact mulList_congr_list M (by
    rw [← listPow_add]
    congr 1
    omega) _ _ _ _

/-- Transition maps commute with a single multiplication, in transported form. -/
lemma locTr_mulX' (d : ℤ) (i : Fin (n + 1)) (j j' : ℕ) (h : j ≤ j') :
    M.locTr l d j j' h ≫
      M.mulX' i (locDeg l d j') (locDeg l (d + 1) j') (by
        rw [locDeg_def, locDeg_def]; ring) =
    M.mulX' i (locDeg l d j) (locDeg l (d + 1) j) (by
        rw [locDeg_def, locDeg_def]; ring) ≫
      M.locTr l (d + 1) j j' h := by
  rw [locTr, locTr]
  exact (mulX'_mulList_comm M i (listPow l (j' - j)) _ _ _ _ _ _ _ _).symm

/-- The directed system underlying the localization tower. -/
instance locDirectedSystem (d : ℤ) :
    DirectedSystem (fun j : ℕ => M.obj (locDeg l d j))
      (fun j j' h => (M.locTr l d j j' h).hom) where
  map_self j x := by
    have h1 := congrArg ModuleCat.Hom.hom (M.locTr_self l d j)
    exact LinearMap.congr_fun h1 x
  map_map {j₃ j₂ j₁} h₁₂ h₂₃ x := by
    have h1 := congrArg ModuleCat.Hom.hom (M.locTr_trans l d j₁ j₂ j₃ h₁₂ h₂₃)
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 x

/-- The localization `M[1/x_l]` of a graded module at the product of a list of
variables: the degree-`d` piece is the sequential direct limit of `M` along
multiplication by `x_l`. -/
noncomputable def loc : GradedModule k n where
  obj d := ModuleCat.of k (Module.DirectLimit
    (fun j : ℕ => M.obj (locDeg l d j))
    (fun j j' h => (M.locTr l d j j' h).hom))
  mulX i d := ModuleCat.ofHom (Module.DirectLimit.map
    (fun j => (M.mulX' i (locDeg l d j) (locDeg l (d + 1) j) (by
      rw [locDeg_def, locDeg_def]; ring)).hom)
    (fun j j' h => by
      have h1 := congrArg ModuleCat.Hom.hom (M.locTr_mulX' l d i j j' h)
      simpa using h1))
  mulX_comm i i' d := by
    refine ModuleCat.hom_ext ?_
    refine Module.DirectLimit.hom_ext fun j => ?_
    refine LinearMap.ext fun x => ?_
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Module.DirectLimit.map_apply_of]
    congr 1
    have hcomm := M.mulX'_comm i i' (locDeg l d j) (locDeg l (d + 1) j)
      (locDeg l (d + 1) j) (locDeg l (d + 1 + 1) j)
      (by rw [locDeg_def, locDeg_def]; ring)
      (by rw [locDeg_def, locDeg_def]; ring)
      (by rw [locDeg_def, locDeg_def]; ring)
      (by rw [locDeg_def, locDeg_def]; ring)
    have h1 := congrArg ModuleCat.Hom.hom hcomm
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 x

/-- The localization map `M ⟶ M[1/x_l]`: inclusion at stage zero of the tower. -/
noncomputable def locOf : M ⟶ M.loc l where
  app d := ModuleCat.ofHom
    ((Module.DirectLimit.of k ℕ (fun j : ℕ => M.obj (locDeg l d j))
      (fun j j' h => (M.locTr l d j j' h).hom) 0) ∘ₗ
      (eqToHom (congrArg M.obj (show d = locDeg l d 0 by
        rw [locDeg_def]; push_cast; ring))).hom)
  comm i d := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x => ?_
    simp only [loc, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Module.DirectLimit.map_apply_of]
    congr 1
    have h0 := eqToHom_mulX' M i
      (show d = locDeg l d 0 by rw [locDeg_def]; push_cast; ring)
      (show d + 1 = locDeg l (d + 1) 0 by rw [locDeg_def]; push_cast; ring)
      (by rw [locDeg_def, locDeg_def]; ring)
    have h1 := congrArg ModuleCat.Hom.hom h0
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 x

/-! ## Functoriality and exactness of localization -/

/-- A morphism of graded modules commutes with the localization towers. -/
lemma locTr_comm {M N : GradedModule k n} (φ : M ⟶ N) (l : List (Fin (n + 1)))
    (d : ℤ) (j j' : ℕ) (h : j ≤ j') :
    φ.app (locDeg l d j) ≫ N.locTr l d j j' h =
      M.locTr l d j j' h ≫ φ.app (locDeg l d j') := by
  rw [locTr, locTr]
  exact comm_mulList φ (listPow l (j' - j)) _ _ _

/-- The stage inclusion into the localized degree piece. -/
noncomputable def locIncl (d : ℤ) (j : ℕ) :
    M.obj (locDeg l d j) ⟶ (M.loc l).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.of k ℕ
    (fun j : ℕ => M.obj (locDeg l d j))
    (fun j j' h => (M.locTr l d j j' h).hom) j)

/-- Stage inclusions are compatible with the transition maps. -/
lemma locTr_locIncl (d : ℤ) (j j' : ℕ) (h : j ≤ j') :
    M.locTr l d j j' h ≫ M.locIncl l d j' = M.locIncl l d j := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  exact Module.DirectLimit.of_f (hij := h)

/-- Every element of the localization comes from some stage. -/
lemma locIncl_exists (d : ℤ) (z : (M.loc l).obj d) :
    ∃ (j : ℕ) (x : M.obj (locDeg l d j)), (M.locIncl l d j).hom x = z := by
  obtain ⟨j, x, hx⟩ := Module.DirectLimit.exists_of z
  exact ⟨j, x, hx⟩

/-- An element of a stage dying in the localization dies at a later stage. -/
lemma locIncl_eq_zero (d : ℤ) (j : ℕ) (x : M.obj (locDeg l d j))
    (hx : (M.locIncl l d j).hom x = 0) :
    ∃ (j' : ℕ) (h : j ≤ j'), (M.locTr l d j j' h).hom x = 0 := by
  obtain ⟨j', h, hz⟩ := Module.DirectLimit.of.zero_exact hx
  exact ⟨j', h, hz⟩

/-- The stage inclusion intertwines multiplication with the stage-level
multiplication. -/
lemma locIncl_mulX (d : ℤ) (j : ℕ) (i : Fin (n + 1)) :
    M.locIncl l d j ≫ (M.loc l).mulX i d =
      M.mulX' i (locDeg l d j) (locDeg l (d + 1) j)
          (by rw [locDeg_def, locDeg_def]; ring) ≫
        M.locIncl l (d + 1) j := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, loc, locIncl,
    ModuleCat.hom_ofHom]
  exact Module.DirectLimit.map_apply_of _ _ _

section Restriction

variable (l' m : List (Fin (n + 1)))

/-- Degree bookkeeping for the restriction stage maps. -/
lemma locRes_stage_degree (hp : l'.Perm (l ++ m)) (d : ℤ) (j : ℕ) :
    locDeg l d j + ((listPow m j).length : ℤ) = locDeg l' d j := by
  rw [listPow_length, locDeg_def, locDeg_def, hp.length_eq, List.length_append]
  push_cast
  ring

/-- The coercion of an iterated list to a multiset is the repeated multiset. -/
lemma listPow_coe (L : List (Fin (n + 1))) (a : ℕ) :
    ((listPow L a : List (Fin (n + 1))) : Multiset (Fin (n + 1))) =
      a • (L : Multiset (Fin (n + 1))) := by
  induction a with
  | zero => simp [listPow]
  | succ b ih =>
      rw [show b + 1 = 1 + b from by omega, listPow_add, ← Multiset.coe_add, ih,
        show (listPow L 1 : List (Fin (n + 1))) = L from by simp [listPow],
        add_nsmul, one_nsmul]

/-- The stage maps of the restriction are compatible with the towers. -/
lemma locRes_stage_compat (hp : l'.Perm (l ++ m)) (d : ℤ) (j j' : ℕ)
    (h : j ≤ j') :
    M.locTr l d j j' h ≫
      M.mulList (listPow m j') (locDeg l d j') (locDeg l' d j')
        (locRes_stage_degree l l' m hp d j') ≫
      M.locIncl l' d j' =
    M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
        (locRes_stage_degree l l' m hp d j) ≫
      M.locIncl l' d j := by
  conv_rhs => rw [← M.locTr_locIncl l' d j j' h]
  rw [locTr, locTr, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← M.mulList_append (listPow l (j' - j)) (listPow m j')
      (locDeg l d j) (locDeg l d j') (locDeg l' d j') _ _
      (by
        rw [List.length_append, listPow_length, listPow_length,
          locDeg_def, locDeg_def]
        rw [hp.length_eq, List.length_append]
        push_cast [Nat.cast_sub h]
        ring),
    ← M.mulList_append (listPow m j) (listPow l' (j' - j))
      (locDeg l d j) (locDeg l' d j) (locDeg l' d j') _ _
      (by
        rw [List.length_append, listPow_length, listPow_length,
          locDeg_def, locDeg_def]
        rw [hp.length_eq, List.length_append]
        push_cast [Nat.cast_sub h]
        ring)]
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add,
    listPow_coe, listPow_coe, listPow_coe, listPow_coe]
  have hl' : (l' : Multiset (Fin (n + 1))) =
      (l : Multiset (Fin (n + 1))) + (m : Multiset (Fin (n + 1))) := by
    have h2 := hp
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add] at h2
    exact h2
  rw [hl', nsmul_add]
  have hj' : j' = j + (j' - j) := by omega
  calc (j' - j) • (l : Multiset (Fin (n + 1))) + j' • (m : Multiset (Fin (n + 1)))
      = (j' - j) • (l : Multiset (Fin (n + 1))) +
        (j + (j' - j)) • (m : Multiset (Fin (n + 1))) := by rw [← hj']
    _ = j • (m : Multiset (Fin (n + 1))) +
        ((j' - j) • (l : Multiset (Fin (n + 1))) +
          (j' - j) • (m : Multiset (Fin (n + 1)))) := by
        rw [add_nsmul]
        abel

variable {m l'} in
/-- Degree component of the restriction map between localizations. -/
noncomputable def locResApp (hp : l'.Perm (l ++ m)) (d : ℤ) :
    (M.loc l).obj d ⟶ (M.loc l').obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => M.obj (locDeg l d j))
    (fun j j' h => (M.locTr l d j j' h).hom)
    (fun j => (M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
        (locRes_stage_degree l l' m hp d j) ≫ M.locIncl l' d j).hom)
    (fun j j' hjj' x => by
      have h1 := congrArg ModuleCat.Hom.hom
        (locRes_stage_compat M l l' m hp d j j' hjj')
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

variable {m l'} in
/-- The restriction restricted to a stage is multiplication by the missing factor. -/
lemma locIncl_locResApp (hp : l'.Perm (l ++ m)) (d : ℤ) (j : ℕ) :
    M.locIncl l d j ≫ M.locResApp l hp d =
      M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
          (locRes_stage_degree l l' m hp d j) ≫
        M.locIncl l' d j := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locResApp, locIncl,
    ModuleCat.hom_ofHom]
  exact Module.DirectLimit.lift_of _ _ _

variable {m l'} in
/-- The restriction intertwines the multiplications. -/
lemma locResApp_mulX (hp : l'.Perm (l ++ m)) (d : ℤ) (i : Fin (n + 1)) :
    M.locResApp l hp d ≫ (M.loc l').mulX i d =
      (M.loc l).mulX i d ≫ M.locResApp l hp (d + 1) := by
  refine ModuleCat.hom_ext ?_
  refine Module.DirectLimit.hom_ext fun j => ?_
  have e1 : M.locIncl l d j ≫ M.locResApp l hp d ≫ (M.loc l').mulX i d =
      M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
          (locRes_stage_degree l l' m hp d j) ≫
        M.mulX' i (locDeg l' d j) (locDeg l' (d + 1) j)
          (by rw [locDeg_def, locDeg_def]; ring) ≫
        M.locIncl l' (d + 1) j := by
    rw [← Category.assoc, locIncl_locResApp M l hp d j, Category.assoc,
      M.locIncl_mulX l' d j i, ← Category.assoc]
  have e2 : M.locIncl l d j ≫ (M.loc l).mulX i d ≫ M.locResApp l hp (d + 1) =
      M.mulX' i (locDeg l d j) (locDeg l (d + 1) j)
          (by rw [locDeg_def, locDeg_def]; ring) ≫
        M.mulList (listPow m j) (locDeg l (d + 1) j) (locDeg l' (d + 1) j)
          (locRes_stage_degree l l' m hp (d + 1) j) ≫
        M.locIncl l' (d + 1) j := by
    rw [← Category.assoc, M.locIncl_mulX l d j i, Category.assoc,
      locIncl_locResApp M l hp (d + 1) j, ← Category.assoc]
  have e3 : M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
          (locRes_stage_degree l l' m hp d j) ≫
        M.mulX' i (locDeg l' d j) (locDeg l' (d + 1) j)
          (by rw [locDeg_def, locDeg_def]; ring) =
      M.mulX' i (locDeg l d j) (locDeg l (d + 1) j)
          (by rw [locDeg_def, locDeg_def]; ring) ≫
        M.mulList (listPow m j) (locDeg l (d + 1) j) (locDeg l' (d + 1) j)
          (locRes_stage_degree l l' m hp (d + 1) j) :=
    (mulX'_mulList_comm M i (listPow m j) _ _ _ _ _ _ _ _).symm
  have e4 : M.locIncl l d j ≫ M.locResApp l hp d ≫ (M.loc l').mulX i d =
      M.locIncl l d j ≫ (M.loc l).mulX i d ≫ M.locResApp l hp (d + 1) := by
    rw [e1, e2, ← Category.assoc, e3, Category.assoc]
  have h1 := congrArg ModuleCat.Hom.hom e4
  simp only [ModuleCat.hom_comp, locIncl, ModuleCat.hom_ofHom] at h1
  exact h1

variable {m l'} in
/-- The restriction map between localizations: for `x_{l'} = x_l · x_m` (up to
permutation), every `x_l`-localized element is `x_{l'}`-localized after multiplying by
the missing factor. -/
noncomputable def locRes (hp : l'.Perm (l ++ m)) : M.loc l ⟶ M.loc l' where
  app d := M.locResApp l hp d
  comm i d := locResApp_mulX M l hp d i

variable {m l'} in
/-- The restriction after the localization map is multiplication before it. -/
lemma locIncl_locRes_app (hp : l'.Perm (l ++ m)) (d : ℤ) (j : ℕ) :
    M.locIncl l d j ≫ (M.locRes l hp).app d =
      M.mulList (listPow m j) (locDeg l d j) (locDeg l' d j)
          (locRes_stage_degree l l' m hp d j) ≫
        M.locIncl l' d j :=
  locIncl_locResApp M l hp d j

variable {m l'} in
/-- Maps out of a localized degree piece agree once they agree on every stage. -/
lemma loc_hom_ext {V : ModuleCat.{u} k} {d : ℤ} {f g : (M.loc l).obj d ⟶ V}
    (h : ∀ j : ℕ, M.locIncl l d j ≫ f = M.locIncl l d j ≫ g) : f = g := by
  refine ModuleCat.hom_ext ?_
  refine Module.DirectLimit.hom_ext fun j => ?_
  have h1 := congrArg ModuleCat.Hom.hom (h j)
  simp only [ModuleCat.hom_comp, locIncl, ModuleCat.hom_ofHom] at h1
  exact h1

/-- Restrictions of localizations compose: the missing factors multiply. -/
lemma locRes_locRes {l' l'' m₁ m₂ : List (Fin (n + 1))}
    (hp₁ : l'.Perm (l ++ m₁)) (hp₂ : l''.Perm (l' ++ m₂)) :
    M.locRes l hp₁ ≫ M.locRes l' hp₂ =
      M.locRes l (m := m₁ ++ m₂)
        (hp₂.trans ((hp₁.append_right m₂).trans
          (by rw [List.append_assoc]))) := by
  refine hom_ext fun d => ?_
  rw [comp_app]
  show M.locResApp l hp₁ d ≫ M.locResApp l' hp₂ d =
    M.locResApp l (hp₂.trans ((hp₁.append_right m₂).trans
      (by rw [List.append_assoc]))) d
  refine loc_hom_ext M l fun j => ?_
  rw [← Category.assoc, locIncl_locResApp M l hp₁ d j, Category.assoc,
    locIncl_locResApp M l' hp₂ d j, locIncl_locResApp M l _ d j,
    ← Category.assoc, ← M.mulList_append (listPow m₁ j) (listPow m₂ j)
      (locDeg l d j) (locDeg l' d j) (locDeg l'' d j) _ _
      (by
        rw [List.length_append, listPow_length, listPow_length, locDeg_def,
          locDeg_def, hp₂.length_eq, List.length_append, hp₁.length_eq,
          List.length_append]
        push_cast
        ring)]
  congr 1
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, listPow_coe, listPow_coe,
    listPow_coe, ← Multiset.coe_add, smul_add]

end Restriction

variable {M} in
/-- Localization of a morphism of graded modules. -/
noncomputable def locMap {N : GradedModule k n} (φ : M ⟶ N) :
    M.loc l ⟶ N.loc l where
  app d := ModuleCat.ofHom (Module.DirectLimit.map
    (fun j => (φ.app (locDeg l d j)).hom)
    (fun j j' h => by
      have h1 := congrArg ModuleCat.Hom.hom (locTr_comm φ l d j j' h)
      simp only [ModuleCat.hom_comp] at h1
      exact h1.symm))
  comm i d := by
    refine ModuleCat.hom_ext ?_
    refine Module.DirectLimit.hom_ext fun j => ?_
    refine LinearMap.ext fun x => ?_
    simp only [loc, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Module.DirectLimit.map_apply_of]
    congr 1
    have h1 := congrArg ModuleCat.Hom.hom
      (φ.comm' i (locDeg l d j) (locDeg l (d + 1) j)
        (by rw [locDeg_def, locDeg_def]; ring))
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 x

/-- The localized morphism restricted to a stage is the morphism at that stage. -/
lemma locIncl_locMap {N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) (j : ℕ) :
    M.locIncl l d j ≫ (locMap l φ).app d =
      φ.app (locDeg l d j) ≫ N.locIncl l d j := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locMap, locIncl,
    ModuleCat.hom_ofHom]
  exact Module.DirectLimit.map_apply_of _ _ _

/-- **The stage inclusion intertwines iterated multiplication.**  The `mulList` form of
`locIncl_mulX`. -/
lemma locIncl_mulList (L : List (Fin (n + 1))) (d e : ℤ) (h : d + (L.length : ℤ) = e) (j : ℕ) :
    M.locIncl l d j ≫ (M.loc l).mulList L d e h
      = M.mulList L (locDeg l d j) (locDeg l e j)
          (by simp only [locDeg_def]; omega) ≫ M.locIncl l e j := by
  induction L generalizing d e with
  | nil =>
      obtain rfl : e = d := by simpa using h.symm
      simp [mulList]
  | cons a L ih =>
      have hd1 : d + 1 + (L.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      have hb : locDeg l d j + 1 = locDeg l (d + 1) j := by
        simp only [locDeg_def]; ring
      have h1 : locDeg l (d + 1) j + (L.length : ℤ) = locDeg l e j := by
        simp only [locDeg_def]; omega
      have h2 : locDeg l d j + 1 + (L.length : ℤ) = locDeg l e j := by
        simp only [locDeg_def]; omega
      show M.locIncl l d j ≫ ((M.loc l).mulX a d ≫ (M.loc l).mulList L (d + 1) e hd1) = _
      rw [← Category.assoc, locIncl_mulX, Category.assoc, ih (d + 1) e hd1]
      show (M.mulX a (locDeg l d j) ≫ eqToHom (congrArg M.obj hb)) ≫ _ = _
      show _ = (M.mulX a (locDeg l d j) ≫ M.mulList L (locDeg l d j + 1) (locDeg l e j) h2)
        ≫ M.locIncl l e j
      rw [mulList_congr_degree M L hb rfl h2 h1]
      simp

/-- **A localization of a degreewise bijective morphism is bijective.**  If `φ` is bijective in
every degree of the localization tower at `l`, then `locMap l φ` is bijective in degree `d`:
a direct limit of isomorphisms is an isomorphism (`Module.DirectLimit.congr`). -/
theorem bijective_locMap_app_of_bijective {N : GradedModule k n} (φ : M ⟶ N)
    (l : List (Fin (n + 1))) (d : ℤ)
    (h : ∀ t : ℕ, Function.Bijective ((φ.app (locDeg l d t)).hom)) :
    Function.Bijective (((locMap l φ).app d).hom) := by
  have hcompat : ∀ (t t' : ℕ) (htt : t ≤ t'),
      (LinearEquiv.ofBijective _ (h t')).toLinearMap ∘ₗ (M.locTr l d t t' htt).hom
        = (N.locTr l d t t' htt).hom ∘ₗ
          (LinearEquiv.ofBijective _ (h t)).toLinearMap := by
    intro t t' htt
    have h1 := congrArg ModuleCat.Hom.hom (locTr_comm φ l d t t' htt)
    simp only [ModuleCat.hom_comp] at h1
    exact h1.symm
  exact (Module.DirectLimit.congr
    (fun t : ℕ ↦ LinearEquiv.ofBijective _ (h t)) hcompat).bijective

/-- Elementwise form of `locIncl_locMap`. -/
lemma locMap_locIncl_apply {N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) (j : ℕ)
    (x : M.obj (locDeg l d j)) :
    ((locMap l φ).app d).hom ((M.locIncl l d j).hom x) =
      (N.locIncl l d j).hom ((φ.app (locDeg l d j)).hom x) := by
  have h1 := congrArg ModuleCat.Hom.hom (locIncl_locMap M l φ d j)
  simp only [ModuleCat.hom_comp] at h1
  exact LinearMap.congr_fun h1 x

/-- **A localization of a degreewise injective morphism is injective.** -/
theorem injective_locMap_app_of_injective {N : GradedModule k n} (φ : M ⟶ N)
    (d : ℤ) (h : ∀ t : ℕ, Function.Injective ((φ.app (locDeg l d t)).hom)) :
    Function.Injective (((locMap l φ).app d).hom) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨t, y, rfl⟩ := locIncl_exists M l d z
  rw [locMap_locIncl_apply] at hz
  obtain ⟨t', htt', hkill⟩ := locIncl_eq_zero N l d t _ hz
  have hcomm := congrArg ModuleCat.Hom.hom (locTr_comm φ l d t t' htt')
  simp only [ModuleCat.hom_comp] at hcomm
  have hzero : ((φ.app (locDeg l d t')).hom) ((M.locTr l d t t' htt').hom y) = 0 := by
    have hy := LinearMap.congr_fun hcomm y
    simp only [LinearMap.comp_apply] at hy
    rw [← hy]; exact hkill
  have hy0 : (M.locTr l d t t' htt').hom y = 0 := h t' (by rw [hzero, map_zero])
  have htr := congrArg ModuleCat.Hom.hom (locTr_locIncl M l d t t' htt')
  simp only [ModuleCat.hom_comp] at htr
  rw [← LinearMap.congr_fun htr y]
  simp only [LinearMap.comp_apply, hy0, map_zero]

/-- **A localization of a degreewise surjective morphism is surjective.** -/
theorem surjective_locMap_app_of_surjective {N : GradedModule k n} (φ : M ⟶ N)
    (d : ℤ) (h : ∀ t : ℕ, Function.Surjective ((φ.app (locDeg l d t)).hom)) :
    Function.Surjective (((locMap l φ).app d).hom) := by
  intro z
  obtain ⟨t, y, rfl⟩ := locIncl_exists N l d z
  obtain ⟨x, rfl⟩ := h t y
  exact ⟨(M.locIncl l d t).hom x, locMap_locIncl_apply M l φ d t x⟩

/-- **Localization is exact.**  If `A → B → C` is exact in every degree of the tower at `l`
over `d`, the localized sequence is exact in degree `d`.  Both directions are the
"lift to a stage" argument: an element of `(B.loc l).obj d` killed by `g` is killed at some
later stage, where exactness applies. -/
theorem exact_locMap_app {A B C : GradedModule k n} (f : A ⟶ B) (g : B ⟶ C) (d : ℤ)
    (h : ∀ t : ℕ, Function.Exact ((f.app (locDeg l d t)).hom) ((g.app (locDeg l d t)).hom)) :
    Function.Exact (((locMap l f).app d).hom) (((locMap l g).app d).hom) := by
  intro z
  constructor
  · intro hz
    obtain ⟨t, y, rfl⟩ := locIncl_exists B l d z
    rw [locMap_locIncl_apply] at hz
    obtain ⟨t', htt', hkill⟩ := locIncl_eq_zero C l d t _ hz
    have hcomm := congrArg ModuleCat.Hom.hom (locTr_comm g l d t t' htt')
    simp only [ModuleCat.hom_comp] at hcomm
    have hzero : ((g.app (locDeg l d t')).hom) ((B.locTr l d t t' htt').hom y) = 0 := by
      have hy := LinearMap.congr_fun hcomm y
      simp only [LinearMap.comp_apply] at hy
      rw [← hy]; exact hkill
    obtain ⟨x, hx⟩ := (h t' _).mp hzero
    refine ⟨(A.locIncl l d t').hom x, ?_⟩
    rw [locMap_locIncl_apply, hx]
    have htr := congrArg ModuleCat.Hom.hom (locTr_locIncl B l d t t' htt')
    simp only [ModuleCat.hom_comp] at htr
    exact LinearMap.congr_fun htr y
  · rintro ⟨w, rfl⟩
    obtain ⟨t, x, rfl⟩ := locIncl_exists A l d w
    rw [locMap_locIncl_apply, locMap_locIncl_apply]
    rw [(h t).apply_apply_eq_zero x, map_zero]

/-- Localization is functorial: identities. -/
lemma locMap_id : locMap l (𝟙 M) = 𝟙 (M.loc l) := by
  refine hom_ext fun d => ?_
  refine ModuleCat.hom_ext (Module.DirectLimit.hom_ext fun j => ?_)
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  show ((locMap l (𝟙 M)).app d).hom ((M.locIncl l d j).hom x) =
    ((𝟙 (M.loc l) : M.loc l ⟶ M.loc l).app d).hom ((M.locIncl l d j).hom x)
  rw [locMap_locIncl_apply]
  rfl

/-- Localization is functorial: composition. -/
lemma locMap_comp {N P : GradedModule k n} (φ : M ⟶ N) (ψ : N ⟶ P) :
    locMap l (φ ≫ ψ) = locMap l φ ≫ locMap l ψ := by
  refine hom_ext fun d => ?_
  refine ModuleCat.hom_ext (Module.DirectLimit.hom_ext fun j => ?_)
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  show ((locMap l (φ ≫ ψ)).app d).hom ((M.locIncl l d j).hom x) =
    (((locMap l φ ≫ locMap l ψ)).app d).hom ((M.locIncl l d j).hom x)
  rw [locMap_locIncl_apply, comp_app]
  show _ = ((locMap l ψ).app d).hom (((locMap l φ).app d).hom
    ((M.locIncl l d j).hom x))
  rw [locMap_locIncl_apply, locMap_locIncl_apply]
  rfl

variable {M l} in
/-- An element of the localization killed by the localization of a degreewise
injective morphism is zero. -/
lemma locMap_eq_zero_of_injective {N : GradedModule k n} {φ : M ⟶ N} {d : ℤ}
    (hinj : ∀ e, Function.Injective (φ.app e).hom)
    (z : (M.loc l).obj d) (hz : ((locMap l φ).app d).hom z = 0) : z = 0 := by
  obtain ⟨j, x, rfl⟩ := M.locIncl_exists l d z
  rw [locMap_locIncl_apply] at hz
  obtain ⟨j', hjj', hk⟩ := N.locIncl_eq_zero l d j _ hz
  have hcomm := congrArg ModuleCat.Hom.hom (locTr_comm φ l d j j' hjj')
  simp only [ModuleCat.hom_comp] at hcomm
  have h2 := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply] at h2
  have hk' : (φ.app (locDeg l d j')).hom ((M.locTr l d j j' hjj').hom x) = 0 := by
    rw [← h2]
    exact hk
  have hx0 : (M.locTr l d j j' hjj').hom x = 0 :=
    hinj (locDeg l d j') (by rw [hk', map_zero])
  have h3 := congrArg ModuleCat.Hom.hom (M.locTr_locIncl l d j j' hjj')
  simp only [ModuleCat.hom_comp] at h3
  rw [← LinearMap.congr_fun h3 x]
  simp only [LinearMap.comp_apply, hx0, map_zero]

variable {l} in
/-- Localization preserves degreewise short exact sequences: sequential direct limits
of modules are exact. -/
theorem loc_shortExact {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) : ShortExact (locMap l φ) (locMap l ψ) where
  injective d := by
    intro z w hzw
    have hsub : ((locMap l φ).app d).hom (z - w) = 0 := by
      rw [map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (locMap_eq_zero_of_injective h.injective (z - w) hsub)
  exact d := by
    ext z
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨j, x, rfl⟩ := M.locIncl_exists l d w
      rw [locMap_locIncl_apply, locMap_locIncl_apply]
      have hx : (ψ.app (locDeg l d j)).hom ((φ.app (locDeg l d j)).hom x) = 0 := by
        have hmem : (φ.app (locDeg l d j)).hom x ∈
            LinearMap.range (φ.app (locDeg l d j)).hom := ⟨x, rfl⟩
        rw [h.exact (locDeg l d j)] at hmem
        exact hmem
      rw [hx, map_zero]
    · intro hz
      obtain ⟨j, x, rfl⟩ := N.locIncl_exists l d z
      rw [locMap_locIncl_apply] at hz
      obtain ⟨j', hjj', hk⟩ := P.locIncl_eq_zero l d j _ hz
      have hcomm := congrArg ModuleCat.Hom.hom (locTr_comm ψ l d j j' hjj')
      simp only [ModuleCat.hom_comp] at hcomm
      have h2 := LinearMap.congr_fun hcomm x
      simp only [LinearMap.comp_apply] at h2
      have hker' : (N.locTr l d j j' hjj').hom x ∈
          LinearMap.ker (ψ.app (locDeg l d j')).hom := by
        rw [LinearMap.mem_ker, ← h2]
        exact hk
      rw [← h.exact (locDeg l d j')] at hker'
      obtain ⟨m, hm⟩ := hker'
      refine ⟨(M.locIncl l d j').hom m, ?_⟩
      rw [locMap_locIncl_apply, hm]
      have h3 := congrArg ModuleCat.Hom.hom (N.locTr_locIncl l d j j' hjj')
      simp only [ModuleCat.hom_comp] at h3
      exact LinearMap.congr_fun h3 x
  surjective d := by
    intro z
    obtain ⟨j, x, rfl⟩ := P.locIncl_exists l d z
    obtain ⟨m, hm⟩ := h.surjective (locDeg l d j) x
    refine ⟨(N.locIncl l d j).hom m, ?_⟩
    rw [locMap_locIncl_apply, hm]

/-- Multiplication by a linear form transported along an equal source degree. -/
lemma mulL_congr_degree (M : GradedModule k n) (c : Fin (n + 1) → k)
    {d d' e : ℤ} (hd : d = d') (h : d + 1 = e) (h' : d' + 1 = e) :
    eqToHom (congrArg M.obj hd) ≫ M.mulL c d' e h' = M.mulL c d e h := by
  subst hd
  simp

/-! ## The localization map through the stage inclusions -/

section LocOf

variable (M : GradedModule k n) (l : List (Fin (n + 1)))

/-- The localization map is the stage-zero inclusion. -/
lemma locOf_app (d : ℤ) :
    (M.locOf l).app d =
      eqToHom (congrArg M.obj (show d = locDeg l d 0 by
        rw [locDeg_def]; push_cast; ring)) ≫ M.locIncl l d 0 := by
  rfl

/-- Localizing further is localizing: the localization map is compatible with the
restriction maps. -/
lemma locOf_locRes {l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) :
    M.locOf l ≫ M.locRes l hp = M.locOf l' := by
  refine hom_ext fun d => ?_
  rw [comp_app, locOf_app, locOf_app, Category.assoc,
    show (M.locRes l hp).app d = M.locResApp l hp d from rfl,
    locIncl_locResApp M l hp d 0]
  rw [mulList_of_eq_nil M (by rw [listPow_zero]) (locDeg l d 0) (locDeg l' d 0)]
  rw [← Category.assoc, eqToHom_trans]

end LocOf

/-! ## Injectivity of the localization map for torsion-free modules -/

section Injective

variable (M : GradedModule k n)

/-- If every variable acts injectively, so does every iterated multiplication. -/
lemma injective_mulList (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom)) :
    ∀ (L : List (Fin (n + 1))) (d e : ℤ) (h : d + (L.length : ℤ) = e),
      Function.Injective ((M.mulList L d e h).hom)
  | [], d, e, h => by
      have hde : d = e := by simpa using h
      subst hde
      intro x y hxy
      simpa [mulList] using hxy
  | i :: t, d, e, h => by
      have h' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      intro x y hxy
      refine hinj i d ?_
      refine injective_mulList hinj t (d + 1) e h' ?_
      simpa only [mulList, ModuleCat.hom_comp, LinearMap.comp_apply] using hxy

/-- If every variable acts injectively, the tower transitions are injective. -/
lemma injective_locTr (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom))
    (l : List (Fin (n + 1))) (d : ℤ) (j j' : ℕ) (h : j ≤ j') :
    Function.Injective ((M.locTr l d j j' h).hom) :=
  injective_mulList M hinj _ _ _ _

/-- If every variable acts injectively, the stage inclusions into the localization are
injective. -/
lemma injective_locIncl (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom))
    (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    Function.Injective ((M.locIncl l d j).hom) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨j', hjj', hkill⟩ := M.locIncl_eq_zero l d j x hx
  exact injective_locTr M hinj l d j j' hjj' (by rw [hkill, map_zero])

/-- For a module on which every variable acts injectively — a torsion-free sheaf — the
localization map is injective. -/
lemma injective_locOf (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom))
    (l : List (Fin (n + 1))) (d : ℤ) :
    Function.Injective (((M.locOf l).app d).hom) := by
  rw [locOf_app]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp]
  refine Function.Injective.comp (injective_locIncl M hinj l d 0) ?_
  intro x y hxy
  have h1 : ∀ (z : M.obj d),
      (eqToHom (congrArg M.obj (show d = locDeg l d 0 by
        rw [locDeg_def]; push_cast; ring))).hom z =
      (eqToHom (congrArg M.obj (show d = locDeg l d 0 by
        rw [locDeg_def]; push_cast; ring))).hom z := fun _ => rfl
  have hmono : Function.Injective
      ((eqToHom (congrArg M.obj (show d = locDeg l d 0 by
        rw [locDeg_def]; push_cast; ring)) :
        M.obj d ⟶ M.obj (locDeg l d 0))).hom := by
    have hiso : IsIso (eqToHom (congrArg M.obj (show d = locDeg l d 0 by
      rw [locDeg_def]; push_cast; ring)) :
        M.obj d ⟶ M.obj (locDeg l d 0)) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hmono hxy

/-- Every variable acts injectively on the structure module of `ℙⁿ` over a domain. -/
lemma injective_structureModule_mulX {K : Type u} [CommRing K]
    (m : ℕ) (i : Fin (m + 1)) (d : ℤ) :
    Function.Injective (((structureModule K m).mulX i d).hom) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  refine Subtype.ext ?_
  have h : MvPolynomial.X i * p.1 = 0 := congrArg Subtype.val hp
  refine MvPolynomial.ext _ _ fun b => ?_
  have hb := congrArg (MvPolynomial.coeff (Finsupp.single i 1 + b)) h
  rw [MvPolynomial.coeff_X_mul] at hb
  simpa using hb

end Injective


/-! ## Multiplication by a linear form on the localization -/

section MulL

variable (M : GradedModule k n) (l : List (Fin (n + 1)))

/-- Degree bookkeeping for a degree-raising map on the tower. -/
lemma locDeg_succ {d e : ℤ} (h : d + 1 = e) (j : ℕ) :
    locDeg l d j + 1 = locDeg l e j := by
  rw [locDeg_def, locDeg_def]
  omega

/-- Stage inclusions intertwine the transported multiplications. -/
lemma locIncl_mulX' (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e) (j : ℕ) :
    M.locIncl l d j ≫ (M.loc l).mulX' i d e h =
      M.mulX' i (locDeg l d j) (locDeg l e j) (locDeg_succ l h j) ≫
        M.locIncl l e j := by
  subst h
  simpa using M.locIncl_mulX l d j i

/-- Stage inclusions intertwine multiplication by a linear form. -/
lemma locIncl_mulL (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e) (j : ℕ) :
    M.locIncl l d j ≫ (M.loc l).mulL c d e h =
      M.mulL c (locDeg l d j) (locDeg l e j) (locDeg_succ l h j) ≫
        M.locIncl l e j := by
  simp only [mulL, Preadditive.comp_sum, Preadditive.sum_comp,
    Linear.comp_smul, Linear.smul_comp]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (c i • ·) (M.locIncl_mulX' l i d e h j)

end MulL

/-! ## Inverting the multiplication on the localization -/

section MulXInv

variable (M : GradedModule k n) (l : List (Fin (n + 1)))

/-- Division stage map: multiply by the complementary variables and shift one stage up
the tower. -/
lemma locDeg_div_degree (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) (j : ℕ) :
    locDeg l (d + 1) j + ((l.erase i).length : ℤ) = locDeg l d (j + 1) := by
  have hlen : (l.erase i).length + 1 = l.length := by
    rw [List.length_erase_of_mem hi]
    have : 0 < l.length := List.length_pos_of_mem hi
    omega
  rw [locDeg_def, locDeg_def]
  push_cast [← hlen]
  ring

/-- The stage maps of division by `xᵢ`. -/
noncomputable def locDivStage (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) (j : ℕ) :
    M.obj (locDeg l (d + 1) j) ⟶ (M.loc l).obj d :=
  M.mulList (l.erase i) (locDeg l (d + 1) j) (locDeg l d (j + 1))
      (locDeg_div_degree l i hi d j) ≫
    M.locIncl l d (j + 1)

/-- Division stages are compatible with the tower transitions. -/
lemma locDivStage_compat (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) (j j' : ℕ)
    (h : j ≤ j') :
    M.locTr l (d + 1) j j' h ≫ M.locDivStage l i hi d j' =
      M.locDivStage l i hi d j := by
  unfold locDivStage
  conv_rhs => rw [← M.locTr_locIncl l d (j + 1) (j' + 1) (by omega)]
  rw [locTr, locTr, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← M.mulList_append (listPow l (j' - j)) (l.erase i)
      (locDeg l (d + 1) j) (locDeg l (d + 1) j') (locDeg l d (j' + 1)) _ _
      (by
        rw [List.length_append, listPow_length, locDeg_def, locDeg_def]
        have hlen : (l.erase i).length + 1 = l.length := by
          rw [List.length_erase_of_mem hi]
          have : 0 < l.length := List.length_pos_of_mem hi
          omega
        push_cast [Nat.cast_sub h, ← hlen]
        ring),
    ← M.mulList_append (l.erase i) (listPow l ((j' + 1) - (j + 1)))
      (locDeg l (d + 1) j) (locDeg l d (j + 1)) (locDeg l d (j' + 1)) _ _
      (by
        rw [List.length_append, listPow_length, locDeg_def, locDeg_def,
          show (j' + 1) - (j + 1) = j' - j from by omega]
        have hlen : (l.erase i).length + 1 = l.length := by
          rw [List.length_erase_of_mem hi]
          have : 0 < l.length := List.length_pos_of_mem hi
          omega
        push_cast [Nat.cast_sub h, ← hlen]
        ring)]
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add,
    listPow_coe, listPow_coe]
  rw [show (j' + 1) - (j + 1) = j' - j from by omega]
  exact add_comm _ _

/-- Division by `xᵢ` on the localization at a list containing `i`. -/
noncomputable def locDiv (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) :
    (M.loc l).obj (d + 1) ⟶ (M.loc l).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => M.obj (locDeg l (d + 1) j))
    (fun j j' h => (M.locTr l (d + 1) j j' h).hom)
    (fun j => (M.locDivStage l i hi d j).hom)
    (fun j j' hjj' x => by
      have h1 := congrArg ModuleCat.Hom.hom
        (M.locDivStage_compat l i hi d j j' hjj')
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

/-- The stage inclusions intertwine division. -/
lemma locIncl_locDiv (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) (j : ℕ) :
    M.locIncl l (d + 1) j ≫ M.locDiv l i hi d = M.locDivStage l i hi d j := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl,
    ModuleCat.hom_ofHom, locDiv]
  exact Module.DirectLimit.lift_of _ _ _

/-- Division is a right inverse to multiplication on the localization. -/
lemma locDiv_mulX (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) :
    M.locDiv l i hi d ≫ (M.loc l).mulX i d =
      𝟙 ((M.loc l).obj (d + 1)) := by
  refine loc_hom_ext M l fun j => ?_
  rw [← Category.assoc, locIncl_locDiv, Category.comp_id]
  unfold locDivStage
  rw [Category.assoc, M.locIncl_mulX l d (j + 1) i, ← Category.assoc]
  conv_rhs => rw [← M.locTr_locIncl l (d + 1) j (j + 1) (by omega)]
  congr 1
  rw [locTr]
  rw [show M.mulX' i (locDeg l d (j + 1)) (locDeg l (d + 1) (j + 1))
      (by rw [locDeg_def, locDeg_def]; ring) =
    M.mulList [i] (locDeg l d (j + 1)) (locDeg l (d + 1) (j + 1))
      (by
        rw [locDeg_def, locDeg_def, List.length_singleton]
        push_cast
        ring) from by
    simp only [mulList]
    rw [mulX']]
  rw [← M.mulList_append (l.erase i) [i]
      (locDeg l (d + 1) j) (locDeg l d (j + 1)) (locDeg l (d + 1) (j + 1)) _ _
      (by
        rw [List.length_append, List.length_singleton, locDeg_def, locDeg_def]
        have hlen : (l.erase i).length + 1 = l.length := by
          rw [List.length_erase_of_mem hi]
          have : 0 < l.length := List.length_pos_of_mem hi
          omega
        push_cast [← hlen]
        ring)]
  refine mulList_perm M ?_ _ _ _ _
  rw [show (j + 1) - j = 1 from by omega]
  have h1 : listPow l 1 = l := by simp [listPow]
  rw [h1]
  exact (List.perm_append_singleton i (l.erase i)).trans
    (List.perm_cons_erase hi).symm

/-- Division is a left inverse to multiplication on the localization. -/
lemma mulX_locDiv (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) :
    (M.loc l).mulX i d ≫ M.locDiv l i hi d = 𝟙 ((M.loc l).obj d) := by
  refine loc_hom_ext M l fun j => ?_
  rw [← Category.assoc, M.locIncl_mulX l d j i, Category.comp_id,
    Category.assoc, locIncl_locDiv]
  unfold locDivStage
  conv_rhs => rw [← M.locTr_locIncl l d j (j + 1) (by omega)]
  rw [← Category.assoc]
  congr 1
  rw [locTr]
  rw [show M.mulX' i (locDeg l d j) (locDeg l (d + 1) j)
      (by rw [locDeg_def, locDeg_def]; ring) =
    M.mulList [i] (locDeg l d j) (locDeg l (d + 1) j)
      (by
        rw [locDeg_def, locDeg_def, List.length_singleton]
        push_cast
        ring) from by
    simp only [mulList]
    rw [mulX']]
  rw [← M.mulList_append [i] (l.erase i)
      (locDeg l d j) (locDeg l (d + 1) j) (locDeg l d (j + 1)) _ _
      (by
        rw [List.length_append, List.length_singleton, locDeg_def, locDeg_def]
        have hlen : (l.erase i).length + 1 = l.length := by
          rw [List.length_erase_of_mem hi]
          have : 0 < l.length := List.length_pos_of_mem hi
          omega
        push_cast [← hlen]
        ring)]
  refine mulList_perm M ?_ _ _ _ _
  rw [show (j + 1) - j = 1 from by omega]
  have h1 : listPow l 1 = l := by simp [listPow]
  rw [h1]
  exact (List.perm_cons_erase hi).symm

/-- Multiplication by a variable of the list is an isomorphism on the
localization. -/
lemma loc_mulX_isIso (i : Fin (n + 1)) (hi : i ∈ l) (d : ℤ) :
    IsIso ((M.loc l).mulX i d) :=
  ⟨M.locDiv l i hi d, mulX_locDiv M l i hi d, locDiv_mulX M l i hi d⟩

end MulXInv

/-! ## Localization and finite direct sums -/

section PowLoc

variable (M : GradedModule k n) (l : List (Fin (n + 1))) (r : ℕ)

/-- Iterated multiplication on a finite direct sum acts componentwise. -/
lemma pow_mulList (L : List (Fin (n + 1))) (d e : ℤ)
    (h : d + (L.length : ℤ) = e) (x : Fin r → M.obj d) (ρ : Fin r) :
    (((M.pow r).mulList L d e h).hom x) ρ = (M.mulList L d e h).hom (x ρ) := by
  induction L generalizing d x with
  | nil =>
      have hde : d = e := by simpa using h
      subst hde
      rfl
  | cons a t ih =>
      simp only [mulList, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [ih]
      rfl

/-- Tower transitions on a finite direct sum act componentwise. -/
lemma pow_locTr (d : ℤ) (j j' : ℕ) (h : j ≤ j')
    (x : Fin r → M.obj (locDeg l d j)) (ρ : Fin r) :
    (((M.pow r).locTr l d j j' h).hom x) ρ =
      (M.locTr l d j j' h).hom (x ρ) := by
  unfold locTr
  exact pow_mulList M r _ _ _ _ x ρ

/-- The projection out of the localized direct sum. -/
noncomputable def locPowProj (ρ : Fin r) (d : ℤ) :
    ((M.pow r).loc l).obj d ⟶ (M.loc l).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => ((M.pow r).obj (locDeg l d j)))
    (fun j j' h => ((M.pow r).locTr l d j j' h).hom)
    (fun j => (M.locIncl l d j).hom ∘ₗ
      (LinearMap.proj (R := k)
        (φ := fun _ : Fin r => M.obj (locDeg l d j)) ρ))
    (fun j j' hjj' x => by
      have h1 := congrArg ModuleCat.Hom.hom (M.locTr_locIncl l d j j' hjj')
      simp only [ModuleCat.hom_comp] at h1
      have h2 := LinearMap.congr_fun h1 (x ρ)
      simp only [LinearMap.comp_apply] at h2
      show (M.locIncl l d j').hom
          ((((M.pow r).locTr l d j j' hjj').hom x) ρ) =
        (M.locIncl l d j).hom (x ρ)
      rw [pow_locTr M l r d j j' hjj' x ρ]
      exact h2))

/-- Projection intertwines the stage inclusions. -/
lemma locIncl_locPowProj (ρ : Fin r) (d : ℤ) (j : ℕ)
    (x : (M.pow r).obj (locDeg l d j)) :
    (M.locPowProj l r ρ d).hom (((M.pow r).locIncl l d j).hom x) =
      (M.locIncl l d j).hom (x ρ) := by
  simp only [locPowProj, locIncl, ModuleCat.hom_ofHom]
  exact Module.DirectLimit.lift_of _ _ _

/-- The comparison from the localized direct sum to the direct sum of
localizations. -/
noncomputable def locPowToPi (d : ℤ) :
    ((M.pow r).loc l).obj d ⟶
      ModuleCat.of k (Fin r → ((M.loc l).obj d)) :=
  ModuleCat.ofHom (LinearMap.pi fun ρ => (M.locPowProj l r ρ d).hom)

/-- The comparison is bijective. -/
lemma locPowToPi_bijective (d : ℤ) :
    Function.Bijective (M.locPowToPi l r d).hom := by
  constructor
  · have hker : ∀ z, (M.locPowToPi l r d).hom z = 0 → z = 0 := by
      intro z hz
      obtain ⟨j, x, rfl⟩ := (M.pow r).locIncl_exists l d z
      have hcoord : ∀ ρ : Fin r, (M.locIncl l d j).hom (x ρ) = 0 := by
        intro ρ
        have h1 := congrFun hz ρ
        rw [Pi.zero_apply] at h1
        simpa only [locPowToPi, ModuleCat.hom_ofHom, LinearMap.pi_apply,
          locIncl_locPowProj] using h1
      choose js hjs hkill using fun ρ =>
        M.locIncl_eq_zero l d j _ (hcoord ρ)
      set K := max j (Finset.univ.sup js) with hKdef
      have hjK : j ≤ K := le_max_left _ _
      have hkillK : ∀ ρ : Fin r, (M.locTr l d j K hjK).hom (x ρ) = 0 := by
        intro ρ
        have hρK : js ρ ≤ K :=
          le_trans (Finset.le_sup (Finset.mem_univ ρ)) (le_max_right _ _)
        have h3 := congrArg ModuleCat.Hom.hom
          (M.locTr_trans l d j (js ρ) K (hjs ρ) hρK)
        simp only [ModuleCat.hom_comp] at h3
        calc (M.locTr l d j K hjK).hom (x ρ)
            = (M.locTr l d (js ρ) K hρK).hom
                ((M.locTr l d j (js ρ) (hjs ρ)).hom (x ρ)) :=
              (LinearMap.congr_fun h3 (x ρ)).symm
          _ = 0 := by rw [hkill ρ, map_zero]
      have hxK : (((M.pow r).locTr l d j K hjK).hom x) = 0 := by
        funext ρ
        rw [pow_locTr M l r d j K hjK x ρ, hkillK ρ]
        rfl
      have h4 := congrArg ModuleCat.Hom.hom
        ((M.pow r).locTr_locIncl l d j K hjK)
      simp only [ModuleCat.hom_comp] at h4
      calc ((M.pow r).locIncl l d j).hom x
          = ((M.pow r).locIncl l d K).hom
              (((M.pow r).locTr l d j K hjK).hom x) :=
            (LinearMap.congr_fun h4 x).symm
        _ = 0 := by rw [hxK, map_zero]
    intro z w hzw
    have hsub : (M.locPowToPi l r d).hom (z - w) = 0 := by
      rw [map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (hker (z - w) hsub)
  · intro g
    choose js ys hys using fun ρ => M.locIncl_exists l d (g ρ)
    set K := Finset.univ.sup js with hKdef
    refine ⟨((M.pow r).locIncl l d K).hom (fun ρ =>
      (M.locTr l d (js ρ) K (Finset.le_sup (Finset.mem_univ ρ))).hom (ys ρ)),
      ?_⟩
    funext ρ
    simp only [locPowToPi, ModuleCat.hom_ofHom, LinearMap.pi_apply,
      locIncl_locPowProj]
    have h4 := congrArg ModuleCat.Hom.hom
      (M.locTr_locIncl l d (js ρ) K (Finset.le_sup (Finset.mem_univ ρ)))
    simp only [ModuleCat.hom_comp] at h4
    have h5 := LinearMap.congr_fun h4 (ys ρ)
    simp only [LinearMap.comp_apply] at h5
    rw [h5]
    exact hys ρ

/-- The localized direct sum is the direct sum of the localizations. -/
noncomputable def locPowIso (d : ℤ) :
    ((M.pow r).loc l).obj d ≅
      ModuleCat.of k (Fin r → ((M.loc l).obj d)) := by
  haveI hm : Mono (M.locPowToPi l r d) :=
    (ModuleCat.mono_iff_injective _).mpr (locPowToPi_bijective M l r d).1
  haveI he : Epi (M.locPowToPi l r d) :=
    (ModuleCat.epi_iff_surjective _).mpr (locPowToPi_bijective M l r d).2
  haveI : IsIso (M.locPowToPi l r d) := isIso_of_mono_of_epi _
  exact asIso (M.locPowToPi l r d)

end PowLoc

/-! ## Localization and the Serre twist -/

/-- Iterated multiplication on a twist is iterated multiplication at shifted
degrees. -/
lemma twist_mulList (M : GradedModule k n) (a : ℤ) (L : List (Fin (n + 1)))
    (d e : ℤ) (h : d + (L.length : ℤ) = e) :
    (M.twist a).mulList L d e h =
      M.mulList L (d + a) (e + a) (by omega) := by
  induction L generalizing d e with
  | nil =>
      have hde : d = e := by simpa using h
      subst hde
      simp [mulList]
  | cons i t ih =>
      simp only [mulList]
      rw [ih (d + 1) e (by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega)]
      simp only [twist_mulX]
      rw [mulX']
      rw [mulList_congr_degree M t (show d + 1 + a = d + a + 1 by ring) rfl _
        (by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
          omega)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.comp_id, Category.id_comp]

section TwistLoc

variable (M : GradedModule k n) (l : List (Fin (n + 1))) (a : ℤ)

/-- Stage comparison for the localization of a twist. -/
lemma twistLoc_stage_eq (d : ℤ) (j : ℕ) :
    ((M.twist a).obj (locDeg l d j) : ModuleCat k) =
      M.obj (locDeg l (d + a) j) := by
  rw [twist_obj]
  exact congrArg M.obj (by rw [locDeg_def, locDeg_def]; ring)

/-- The transition maps of the twist tower agree with those of the shifted tower,
through the stage comparison. -/
lemma twistLoc_locTr (d : ℤ) (j j' : ℕ) (h : j ≤ j') :
    (M.twist a).locTr l d j j' h =
      eqToHom (twistLoc_stage_eq M l a d j) ≫
        M.locTr l (d + a) j j' h ≫
        eqToHom (twistLoc_stage_eq M l a d j').symm := by
  rw [locTr, locTr, twist_mulList]
  rw [mulList_congr_degree M (listPow l (j' - j))
    (show locDeg l d j + a = locDeg l (d + a) j by
      rw [locDeg_def, locDeg_def]; ring)
    (show locDeg l d j' + a = locDeg l (d + a) j' by
      rw [locDeg_def, locDeg_def]; ring)
    _ (by rw [listPow_length, locDeg_def, locDeg_def]
          push_cast [Nat.cast_sub h]
          ring)]

/-- Forward comparison: the localization of a twist maps to the shifted
localization. -/
noncomputable def twistLocToLoc (d : ℤ) :
    ((M.twist a).loc l).obj d ⟶ (M.loc l).obj (d + a) :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => ((M.twist a).obj (locDeg l d j)))
    (fun j j' h => ((M.twist a).locTr l d j j' h).hom)
    (fun j => (eqToHom (twistLoc_stage_eq M l a d j) ≫
      M.locIncl l (d + a) j).hom)
    (fun j j' hjj' x => by
      have hcmp : (M.twist a).locTr l d j j' hjj' ≫
          (eqToHom (twistLoc_stage_eq M l a d j') ≫
            M.locIncl l (d + a) j') =
          eqToHom (twistLoc_stage_eq M l a d j) ≫
            M.locIncl l (d + a) j := by
        rw [twistLoc_locTr]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [M.locTr_locIncl l (d + a) j j' hjj']
      have h1 := congrArg ModuleCat.Hom.hom hcmp
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

/-- Backward comparison: the shifted localization maps to the localization of the
twist. -/
noncomputable def locToTwistLoc (d : ℤ) :
    (M.loc l).obj (d + a) ⟶ ((M.twist a).loc l).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => (M.obj (locDeg l (d + a) j)))
    (fun j j' h => (M.locTr l (d + a) j j' h).hom)
    (fun j => (eqToHom (twistLoc_stage_eq M l a d j).symm ≫
      (M.twist a).locIncl l d j).hom)
    (fun j j' hjj' x => by
      have hcmp : M.locTr l (d + a) j j' hjj' ≫
          (eqToHom (twistLoc_stage_eq M l a d j').symm ≫
            (M.twist a).locIncl l d j') =
          eqToHom (twistLoc_stage_eq M l a d j).symm ≫
            (M.twist a).locIncl l d j := by
        conv_rhs => rw [← (M.twist a).locTr_locIncl l d j j' hjj']
        rw [twistLoc_locTr]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
      have h1 := congrArg ModuleCat.Hom.hom hcmp
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

/-- The stage inclusions intertwine the forward twist comparison. -/
lemma locIncl_twistLocToLoc (d : ℤ) (j : ℕ) :
    (M.twist a).locIncl l d j ≫ twistLocToLoc M l a d =
      eqToHom (twistLoc_stage_eq M l a d j) ≫ M.locIncl l (d + a) j := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl,
    ModuleCat.hom_ofHom, twistLocToLoc]
  exact Module.DirectLimit.lift_of _ _ _

/-- The stage inclusions intertwine the backward twist comparison. -/
lemma locIncl_locToTwistLoc (d : ℤ) (j : ℕ) :
    M.locIncl l (d + a) j ≫ locToTwistLoc M l a d =
      eqToHom (twistLoc_stage_eq M l a d j).symm ≫
        (M.twist a).locIncl l d j := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl,
    ModuleCat.hom_ofHom, locToTwistLoc]
  exact Module.DirectLimit.lift_of _ _ _

/-- Degreewise comparison between the localization of a twist and the shift of the
localization. -/
noncomputable def twistLocIso (d : ℤ) :
    ((M.twist a).loc l).obj d ≅ (M.loc l).obj (d + a) where
  hom := twistLocToLoc M l a d
  inv := locToTwistLoc M l a d
  hom_inv_id := by
    refine loc_hom_ext (M.twist a) l fun j => ?_
    rw [← Category.assoc, locIncl_twistLocToLoc, Category.assoc,
      locIncl_locToTwistLoc, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine loc_hom_ext M l fun j => ?_
    rw [← Category.assoc, locIncl_locToTwistLoc, Category.assoc,
      locIncl_twistLocToLoc, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]

/-- The twist comparison intertwines the restriction maps. -/
lemma twistLocToLoc_locResApp {l' m : List (Fin (n + 1))}
    (hp : l'.Perm (l ++ m)) (d : ℤ) :
    (M.twist a).locResApp l hp d ≫ twistLocToLoc M l' a d =
      twistLocToLoc M l a d ≫ M.locResApp l hp (d + a) := by
  refine loc_hom_ext (M.twist a) l fun j => ?_
  rw [← Category.assoc, locIncl_locResApp (M.twist a) l hp d j,
    Category.assoc, locIncl_twistLocToLoc M l' a d j]
  conv_rhs => rw [← Category.assoc, locIncl_twistLocToLoc M l a d j,
    Category.assoc, locIncl_locResApp M l hp (d + a) j]
  rw [twist_mulList]
  rw [mulList_congr_degree M (listPow m j)
    (show locDeg l d j + a = locDeg l (d + a) j by
      rw [locDeg_def, locDeg_def]; ring)
    (show locDeg l' d j + a = locDeg l' (d + a) j by
      rw [locDeg_def, locDeg_def]; ring)
    _ (by
      rw [listPow_length, locDeg_def, locDeg_def, hp.length_eq,
        List.length_append]
      push_cast
      ring)]
  rw [show (eqToHom (twistLoc_stage_eq M l' a d j) :
      ((M.twist a).obj (locDeg l' d j) : ModuleCat k) ⟶
        M.obj (locDeg l' (d + a) j)) =
    eqToHom (show (M.obj (locDeg l' d j + a) : ModuleCat k) =
        M.obj (locDeg l' (d + a) j) from
      congrArg M.obj (by rw [locDeg_def, locDeg_def]; ring)) from rfl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- The twist comparison turns the localized multiplication-by-a-linear-form map
into multiplication by that linear form on the localization.  This is the
`map_mulLHom` field of the cohomology interface, at the level of localizations. -/
lemma twistLocIso_inv_locMap_mulLHom (c : Fin (n + 1) → k) (d : ℤ) :
    (twistLocIso M l (-1) d).inv ≫ (locMap l (M.mulLHom c)).app d =
      (M.loc l).mulL c (d + -1) d (by ring) := by
  refine loc_hom_ext M l fun j => ?_
  rw [← Category.assoc,
    show (twistLocIso M l (-1) d).inv = locToTwistLoc M l (-1) d from rfl,
    locIncl_locToTwistLoc M l (-1) d j, Category.assoc,
    locIncl_locMap (M.twist (-1)) l (M.mulLHom c) d j,
    locIncl_mulL M l c (d + -1) d (by ring) j, ← Category.assoc]
  congr 1
  exact mulL_congr_degree M c
    (show locDeg l (d + -1) j = locDeg l d j + -1 by
      rw [locDeg_def, locDeg_def]; ring)
    (locDeg_succ l (show d + -1 + 1 = d by ring) j) (by ring)

end TwistLoc

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
