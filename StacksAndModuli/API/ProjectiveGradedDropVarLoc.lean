module

public import StacksAndModuli.API.ProjectiveGradedH0Large

/-!
# Localization and dropping a variable

Supporting API with no Stacks Project counterpart.

`N.dropVar j` is `N` with only the variables `≠ j` remembered, so localizing it at a list
`l` of the remaining variables is localizing `N` at `l.map j.succAbove`.  The two towers
carry the same maps but sit over propositionally — not definitionally — equal degrees
(`(l.map f).length = l.length` is an induction), so the comparison has to be built by hand,
exactly as `twistLocIso` is.

Main declarations:
- `GradedModule.dropVarLocIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k] {n : ℕ}

lemma listPow_map (l : List (Fin (n + 1))) {m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (t : ℕ) :
    (listPow l t).map f = listPow (l.map f) t := by
  induction t with
  | zero => simp [listPow]
  | succ a ih =>
      rw [show a + 1 = 1 + a from by omega, listPow_add, listPow_add, List.map_append, ih,
        show (listPow l 1 : List (Fin (n + 1))) = l from by simp [listPow],
        show (listPow (l.map f) 1 : List (Fin (m + 1))) = l.map f from by simp [listPow]]

variable (N : GradedModule k (n + 1)) (j : Fin (n + 2)) (l : List (Fin (n + 1)))

lemma dropVarLoc_stage_eq (d : ℤ) (t : ℕ) :
    (((N.dropVar j).obj (locDeg l d t)) : ModuleCat.{u} k)
      = N.obj (locDeg (l.map j.succAbove) d t) :=
  congrArg N.obj (by rw [locDeg_def, locDeg_def, List.length_map])

lemma dropVarLoc_locTr (d : ℤ) (t t' : ℕ) (h : t ≤ t') :
    (N.dropVar j).locTr l d t t' h
      = eqToHom (dropVarLoc_stage_eq N j l d t) ≫
        N.locTr (l.map j.succAbove) d t t' h ≫
        eqToHom (dropVarLoc_stage_eq N j l d t').symm := by
  rw [locTr, locTr, dropVar_mulList]
  rw [N.mulList_congr_list (listPow_map l j.succAbove (t' - t)) (locDeg l d t)
    (locDeg l d t') _ (by
      rw [listPow_length, locDeg_def, locDeg_def, List.length_map]
      push_cast [Nat.cast_sub h]
      ring)]
  exact N.mulList_congr_degree (listPow (l.map j.succAbove) (t' - t))
    (by rw [locDeg_def, locDeg_def, List.length_map])
    (by rw [locDeg_def, locDeg_def, List.length_map]) _
    (by rw [listPow_length, locDeg_def, locDeg_def]
        push_cast [Nat.cast_sub h]
        ring)

/-- Forward comparison: the localization of a drop-variable module maps to the
localization of `N` at the image list. -/
noncomputable def dropVarLocToLoc (d : ℤ) :
    ((N.dropVar j).loc l).obj d ⟶ (N.loc (l.map j.succAbove)).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun t : ℕ => ((N.dropVar j).obj (locDeg l d t)))
    (fun t t' h => ((N.dropVar j).locTr l d t t' h).hom)
    (fun t => (eqToHom (dropVarLoc_stage_eq N j l d t) ≫
      N.locIncl (l.map j.succAbove) d t).hom)
    (fun t t' htt' x => by
      have hcmp : (N.dropVar j).locTr l d t t' htt' ≫
          (eqToHom (dropVarLoc_stage_eq N j l d t') ≫
            N.locIncl (l.map j.succAbove) d t') =
          eqToHom (dropVarLoc_stage_eq N j l d t) ≫
            N.locIncl (l.map j.succAbove) d t := by
        rw [dropVarLoc_locTr]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [N.locTr_locIncl (l.map j.succAbove) d t t' htt']
      have h1 := congrArg ModuleCat.Hom.hom hcmp
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

/-- Backward comparison. -/
noncomputable def locToDropVarLoc (d : ℤ) :
    (N.loc (l.map j.succAbove)).obj d ⟶ ((N.dropVar j).loc l).obj d :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun t : ℕ => (N.obj (locDeg (l.map j.succAbove) d t)))
    (fun t t' h => (N.locTr (l.map j.succAbove) d t t' h).hom)
    (fun t => (eqToHom (dropVarLoc_stage_eq N j l d t).symm ≫
      (N.dropVar j).locIncl l d t).hom)
    (fun t t' htt' x => by
      have hcmp : N.locTr (l.map j.succAbove) d t t' htt' ≫
          (eqToHom (dropVarLoc_stage_eq N j l d t').symm ≫
            (N.dropVar j).locIncl l d t') =
          eqToHom (dropVarLoc_stage_eq N j l d t).symm ≫
            (N.dropVar j).locIncl l d t := by
        conv_rhs => rw [← (N.dropVar j).locTr_locIncl l d t t' htt']
        rw [dropVarLoc_locTr]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have h1 := congrArg ModuleCat.Hom.hom hcmp
      simp only [ModuleCat.hom_comp] at h1
      exact LinearMap.congr_fun h1 x))

lemma locIncl_dropVarLocToLoc (d : ℤ) (t : ℕ) :
    (N.dropVar j).locIncl l d t ≫ dropVarLocToLoc N j l d =
      eqToHom (dropVarLoc_stage_eq N j l d t) ≫ N.locIncl (l.map j.succAbove) d t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl,
    ModuleCat.hom_ofHom, dropVarLocToLoc]
  exact Module.DirectLimit.lift_of _ _ _

lemma locIncl_locToDropVarLoc (d : ℤ) (t : ℕ) :
    N.locIncl (l.map j.succAbove) d t ≫ locToDropVarLoc N j l d =
      eqToHom (dropVarLoc_stage_eq N j l d t).symm ≫ (N.dropVar j).locIncl l d t := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, locIncl,
    ModuleCat.hom_ofHom, locToDropVarLoc]
  exact Module.DirectLimit.lift_of _ _ _

/-- Localizing `N.dropVar j` is localizing `N` at the image list. -/
noncomputable def dropVarLocIso (d : ℤ) :
    ((N.dropVar j).loc l).obj d ≅ (N.loc (l.map j.succAbove)).obj d where
  hom := dropVarLocToLoc N j l d
  inv := locToDropVarLoc N j l d
  hom_inv_id := by
    refine loc_hom_ext (N.dropVar j) l fun t => ?_
    rw [← Category.assoc, locIncl_dropVarLocToLoc, Category.assoc,
      locIncl_locToDropVarLoc, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine loc_hom_ext N (l.map j.succAbove) fun t => ?_
    rw [← Category.assoc, locIncl_locToDropVarLoc, Category.assoc,
      locIncl_dropVarLocToLoc, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id]

/-! ## Reindexing Čech indices along `succAbove` -/

section Idx

variable {p : ℕ}

/-- A Čech index for the `n+1` remaining variables, seen as one for all `n+2`. -/
def CechIdx.mapSuccAbove (j : Fin (n + 2)) (σ : CechIdx n p) : CechIdx (n + 1) p where
  toList := σ.toList.map j.succAbove
  sorted := σ.sorted.map _ fun _ _ hab => Fin.succAbove_lt_succAbove_iff.mpr hab
  length_eq := by rw [List.length_map]; exact σ.length_eq

@[simp] lemma CechIdx.mapSuccAbove_toList (j : Fin (n + 2)) (σ : CechIdx n p) :
    (σ.mapSuccAbove j).toList = σ.toList.map j.succAbove := rfl

lemma CechIdx.notMem_mapSuccAbove (j : Fin (n + 2)) (σ : CechIdx n p) :
    j ∉ (σ.mapSuccAbove j).toList := by
  rw [CechIdx.mapSuccAbove_toList, List.mem_map]
  rintro ⟨i, -, hi⟩
  exact Fin.succAbove_ne j i hi

lemma CechIdx.mapSuccAbove_injective (j : Fin (n + 2)) :
    Function.Injective (CechIdx.mapSuccAbove (n := n) (p := p) j) := by
  intro σ σ' h
  refine CechIdx.ext ?_
  have hl : σ.toList.map j.succAbove = σ'.toList.map j.succAbove :=
    congrArg CechIdx.toList h
  exact List.map_injective_iff.mpr (Fin.succAbove_right_injective (p := j)) hl

/-- A one-sided inverse to `succAbove j`, total by convention. -/
def succAboveInv (j : Fin (n + 2)) (x : Fin (n + 2)) : Fin (n + 1) :=
  if h : x = j then 0 else (Fin.exists_succAbove_eq h).choose

lemma succAbove_succAboveInv {j x : Fin (n + 2)} (h : x ≠ j) :
    j.succAbove (succAboveInv j x) = x := by
  rw [succAboveInv, dif_neg h]
  exact (Fin.exists_succAbove_eq h).choose_spec

/-- The preimage of a Čech index missing `j` under `succAbove j`. -/
def CechIdx.preSuccAbove (j : Fin (n + 2)) (τ : CechIdx (n + 1) p)
    (hj : j ∉ τ.toList) : CechIdx n p where
  toList := τ.toList.map (succAboveInv j)
  sorted := by
    rw [List.pairwise_map]
    refine τ.sorted.imp_of_mem ?_
    intro a b ha hb hab
    have ha' : a ≠ j := fun hc => hj (hc ▸ ha)
    have hb' : b ≠ j := fun hc => hj (hc ▸ hb)
    rw [← Fin.succAbove_lt_succAbove_iff (p := j),
      succAbove_succAboveInv ha', succAbove_succAboveInv hb']
    exact hab
  length_eq := by rw [List.length_map]; exact τ.length_eq

@[simp] lemma CechIdx.mapSuccAbove_preSuccAbove (j : Fin (n + 2)) (τ : CechIdx (n + 1) p)
    (hj : j ∉ τ.toList) : (τ.preSuccAbove j hj).mapSuccAbove j = τ := by
  refine CechIdx.ext ?_
  show (τ.toList.map (succAboveInv j)).map j.succAbove = τ.toList
  rw [List.map_map]
  conv_rhs => rw [← List.map_id τ.toList]
  refine List.map_congr_left fun x hx => ?_
  have hx' : x ≠ j := fun hc => hj (hc ▸ hx)
  exact succAbove_succAboveInv hx' 

/-- Every Čech index missing `j` comes from one for the remaining variables. -/
lemma CechIdx.exists_mapSuccAbove (j : Fin (n + 2)) (τ : CechIdx (n + 1) p)
    (hj : j ∉ τ.toList) : ∃ σ : CechIdx n p, σ.mapSuccAbove j = τ :=
  ⟨τ.preSuccAbove j hj, CechIdx.mapSuccAbove_preSuccAbove j τ hj⟩

lemma CechIdx.preSuccAbove_mapSuccAbove (j : Fin (n + 2)) (σ : CechIdx n p)
    (hj : j ∉ (σ.mapSuccAbove j).toList) :
    (σ.mapSuccAbove j).preSuccAbove j hj = σ :=
  CechIdx.mapSuccAbove_injective j (CechIdx.mapSuccAbove_preSuccAbove j _ hj)

end Idx

/-! ## The comparison intertwines the restriction maps -/

lemma dropVar_mulList_congr (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    (L : List (Fin (n + 1))) {a b a' b' : ℤ} (ha : a = a') (hb : b = b')
    (h : a + (L.length : ℤ) = b) (h' : a' + ((L.map j.succAbove).length : ℤ) = b') :
    (N.dropVar j).mulList L a b h
      = eqToHom (congrArg N.obj ha) ≫ N.mulList (L.map j.succAbove) a' b' h' ≫
        eqToHom (congrArg N.obj hb.symm) := by
  rw [dropVar_mulList]
  exact N.mulList_congr_degree (L.map j.succAbove) ha hb _ h'

lemma locResApp_dropVarLocToLoc (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    {l l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) (d : ℤ)
    (hpm : (l'.map j.succAbove).Perm ((l.map j.succAbove) ++ (m.map j.succAbove))) :
    (N.dropVar j).locResApp l hp d ≫ dropVarLocToLoc N j l' d
      = dropVarLocToLoc N j l d ≫ N.locResApp (l.map j.succAbove) hpm d := by
  refine loc_hom_ext (N.dropVar j) l fun t => ?_
  have e1 := locIncl_locResApp (N.dropVar j) l hp d t
  have e2 := locIncl_dropVarLocToLoc N j l' d t
  have e3 := locIncl_dropVarLocToLoc N j l d t
  have e4 := locIncl_locResApp N (l.map j.succAbove) hpm d t
  conv_lhs => rw [← Category.assoc, e1, Category.assoc, e2]
  conv_rhs => rw [← Category.assoc, e3, Category.assoc, e4]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  have hstep := dropVar_mulList_congr N j (listPow m t)
    (show locDeg l d t = locDeg (l.map j.succAbove) d t by
      rw [locDeg_def, locDeg_def, List.length_map])
    (show locDeg l' d t = locDeg (l'.map j.succAbove) d t by
      rw [locDeg_def, locDeg_def, List.length_map])
    (locRes_stage_degree l l' m hp d t)
    (by
      rw [List.length_map, listPow_length, locDeg_def, locDeg_def, List.length_map,
        List.length_map]
      have h0 := locRes_stage_degree l l' m hp d t
      rw [listPow_length, locDeg_def, locDeg_def] at h0
      exact h0)
  rw [hstep, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  congr 1
  rw [N.mulList_congr_list (listPow_map m j.succAbove t)
    (locDeg (l.map j.succAbove) d t) (locDeg (l'.map j.succAbove) d t) _
    (locRes_stage_degree _ _ _ hpm d t)]

/-! ## The restriction of Čech cochains -/

lemma CechIdx.mapSuccAbove_face {p : ℕ} (j : Fin (n + 2)) (σ : CechIdx n (p + 1))
    (i : Fin (p + 2)) :
    (σ.mapSuccAbove j).face i = (σ.face i).mapSuccAbove j := by
  refine CechIdx.ext ?_
  show (σ.toList.map j.succAbove).eraseIdx i = (σ.toList.eraseIdx i).map j.succAbove
  rw [List.eraseIdx_map]

lemma CechIdx.mapSuccAbove_elem {p : ℕ} (j : Fin (n + 2)) (σ : CechIdx n p)
    (i : Fin (p + 1)) :
    (σ.mapSuccAbove j).elem i = j.succAbove (σ.elem i) := by
  show (σ.toList.map j.succAbove)[(i : ℕ)]'_ = j.succAbove (σ.toList[(i : ℕ)]'_)
  rw [List.getElem_map]

lemma locToDropVarLoc_locResApp (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    {l l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) (d : ℤ)
    (hpm : (l'.map j.succAbove).Perm ((l.map j.succAbove) ++ (m.map j.succAbove))) :
    locToDropVarLoc N j l d ≫ (N.dropVar j).locResApp l hp d
      = N.locResApp (l.map j.succAbove) hpm d ≫ locToDropVarLoc N j l' d := by
  have h := locResApp_dropVarLocToLoc N j hp d hpm
  have hiso : locToDropVarLoc N j l d ≫ dropVarLocToLoc N j l d = 𝟙 _ :=
    (dropVarLocIso N j l d).inv_hom_id
  have hiso' : dropVarLocToLoc N j l' d ≫ locToDropVarLoc N j l' d = 𝟙 _ :=
    (dropVarLocIso N j l' d).hom_inv_id
  calc locToDropVarLoc N j l d ≫ (N.dropVar j).locResApp l hp d
      = locToDropVarLoc N j l d ≫ ((N.dropVar j).locResApp l hp d
          ≫ dropVarLocToLoc N j l' d) ≫ locToDropVarLoc N j l' d := by
        rw [Category.assoc, hiso', Category.comp_id]
    _ = locToDropVarLoc N j l d ≫ (dropVarLocToLoc N j l d
          ≫ N.locResApp (l.map j.succAbove) hpm d) ≫ locToDropVarLoc N j l' d := by
        rw [h]
    _ = N.locResApp (l.map j.succAbove) hpm d ≫ locToDropVarLoc N j l' d := by
        rw [← Category.assoc, ← Category.assoc, hiso, Category.id_comp]

/-- Restriction of Čech cochains to the indices missing `j`. -/
noncomputable def cechCochainDropVarRes (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    (p : ℕ) (d : ℤ) : N.cechCochain p d ⟶ (N.dropVar j).cechCochain p d :=
  ModuleCat.ofHom
    { toFun := fun c σ => (locToDropVarLoc N j σ.toList d).hom (c (σ.mapSuccAbove j))
      map_add' := fun c₁ c₂ => by
        funext σ
        simp only [Pi.add_apply, map_add]
      map_smul' := fun a c => by
        funext σ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }

lemma eqToHom_app {A B : GradedModule k n} (h : A = B) (d : ℤ) :
    (eqToHom h).app d = eqToHom (congrArg (fun X : GradedModule k n => X.obj d) h) := by
  subst h
  simp

lemma cechCochain_congr_idx (N : GradedModule k (n + 1)) (d : ℤ) {p : ℕ}
    (c : N.cechCochain p d) {X Y : CechIdx (n + 1) p} (h : X = Y) :
    (eqToHom (congrArg (fun τ : CechIdx (n + 1) p => (N.loc τ.toList).obj d) h)).hom (c X)
      = c Y := by
  subst h
  simp

/-- The face restriction of `N` on an index coming from the remaining variables is the
face restriction of `N.dropVar j`, through the localization comparison. -/
lemma cechFaceMap_mapSuccAbove (N : GradedModule k (n + 1)) (j : Fin (n + 2)) {p : ℕ}
    (σ : CechIdx n (p + 1)) (i : Fin (p + 2)) (d : ℤ)
    (hpm : (σ.toList.map j.succAbove).Perm
      (((σ.face i).toList.map j.succAbove) ++ ([σ.elem i].map j.succAbove))) :
    (N.cechFaceMap (σ.mapSuccAbove j) i).app d
      = eqToHom (congrArg (fun τ : CechIdx (n + 1) p => (N.loc τ.toList).obj d)
          (CechIdx.mapSuccAbove_face j σ i)) ≫
        N.locResApp ((σ.face i).toList.map j.succAbove) hpm d := by
  have hlist : ((σ.mapSuccAbove j).face i).toList
      = (σ.face i).toList.map j.succAbove :=
    congrArg CechIdx.toList (CechIdx.mapSuccAbove_face j σ i)
  have hm : [(σ.mapSuccAbove j).elem i].Perm ([σ.elem i].map j.succAbove) := by
    rw [CechIdx.mapSuccAbove_elem]
    exact List.Perm.refl _
  have h := locRes_congr_list N hlist hm
    ((σ.mapSuccAbove j).perm_face_append i) hpm
  have h2 := congrArg (fun t : N.loc ((σ.mapSuccAbove j).face i).toList
      ⟶ N.loc (σ.mapSuccAbove j).toList => t.app d) h
  simp only [comp_app] at h2
  rw [cechFaceMap, h2, eqToHom_app]
  rfl

/-- The restriction of Čech cochains is a chain map. -/
lemma cechD_cechCochainDropVarRes (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    (p : ℕ) (d : ℤ) :
    N.cechD p d ≫ cechCochainDropVarRes N j (p + 1) d
      = cechCochainDropVarRes N j p d ≫ (N.dropVar j).cechD p d := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun σ => ?_)
  show (locToDropVarLoc N j σ.toList d).hom
      (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((N.cechFaceMap (σ.mapSuccAbove j) i).app d).hom (c ((σ.mapSuccAbove j).face i)))
    = ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (((N.dropVar j).cechFaceMap σ i).app d).hom
          ((locToDropVarLoc N j (σ.face i).toList d).hom
            (c ((σ.face i).mapSuccAbove j)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  have hpm : (σ.toList.map j.succAbove).Perm
      (((σ.face i).toList.map j.succAbove) ++ ([σ.elem i].map j.succAbove)) := by
    rw [← List.map_append]
    exact List.Perm.map _ (σ.perm_face_append i)
  rw [cechFaceMap_mapSuccAbove N j σ i d hpm,
    ← cechCochain_congr_idx N d c (CechIdx.mapSuccAbove_face j σ i)]
  have hcomp := locToDropVarLoc_locResApp N j (σ.perm_face_append i) d hpm
  have h1 := congrArg ModuleCat.Hom.hom hcomp
  simp only [ModuleCat.hom_comp] at h1
  exact (LinearMap.congr_fun h1 _).symm

/-- The restriction of Čech complexes to the cover missing `x_j`. -/
noncomputable def cechComplexDropVarRes (N : GradedModule k (n + 1)) (j : Fin (n + 2))
    (d : ℤ) : N.cechComplex d ⟶ (N.dropVar j).cechComplex d :=
  CochainComplex.ofHom (fun p => cechCochainDropVarRes N j p d) (fun p => by
    simpa only [cechComplex, CochainComplex.of_d] using
      (cechD_cechCochainDropVarRes N j p d).symm)

/-! ## The kernel of the restriction -/

variable (N : GradedModule k (n + 1)) (j : Fin (n + 2))

lemma notMem_face_toList {p : ℕ} {τ : CechIdx (n + 1) (p + 1)} (hτ : j ∉ τ.toList)
    (i : Fin (p + 2)) : j ∉ (τ.face i).toList := by
  intro hc
  exact hτ ((List.eraseIdx_sublist τ.toList (i : ℕ)).mem hc)

/-- Cochains supported on the indices that contain `j`. -/
def dropVarKerSub (p : ℕ) (d : ℤ) : Submodule k (N.cechCochain p d) where
  carrier := {c | ∀ τ : CechIdx (n + 1) p, j ∉ τ.toList → c τ = 0}
  add_mem' := fun {a b} hx hz τ hτ => by
    have he : (a + b) τ = a τ + b τ := rfl
    rw [he, hx τ hτ, hz τ hτ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun a x hx τ hτ => by
    have he : (a • x) τ = a • x τ := rfl
    rw [he, hx τ hτ, smul_zero]

lemma cechD_mem_dropVarKerSub {p : ℕ} {d : ℤ} {c : N.cechCochain p d}
    (hc : c ∈ dropVarKerSub N j p d) :
    (N.cechD p d).hom c ∈ dropVarKerSub N j (p + 1) d := by
  intro τ hτ
  show (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
    ((N.cechFaceMap τ i).app d).hom (c (τ.face i))) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hc (τ.face i) (notMem_face_toList j hτ i), map_zero, smul_zero]

lemma cechMulX_mem_dropVarKerSub {p : ℕ} {d : ℤ} {c : N.cechCochain p d}
    (hc : c ∈ dropVarKerSub N j p d) (i : Fin (n + 2)) :
    ((N.cechMulX i d).f p).hom c ∈ dropVarKerSub N j p (d + 1) := by
  intro τ hτ
  show ((N.loc τ.toList).mulX i d).hom (c τ) = 0
  rw [hc τ hτ, map_zero]

/-- The kernel of the restriction, as a cochain complex. -/
noncomputable def dropVarKerComplex (d : ℤ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of k (dropVarKerSub N j p d))
    (fun p => ModuleCat.ofHom ((N.cechD p d).hom.restrict
      (fun _ hc => cechD_mem_dropVarKerSub N j hc)))
    (fun p => by
      refine ModuleCat.hom_ext (LinearMap.ext fun c => Subtype.ext ?_)
      have h := congrArg ModuleCat.Hom.hom (N.cechD_comp_cechD p d)
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h c.1)

/-- The inclusion of the kernel complex. -/
noncomputable def dropVarKerι (d : ℤ) : dropVarKerComplex N j d ⟶ N.cechComplex d :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (dropVarKerSub N j p d).subtype)
    (fun p => by
      simp only [cechComplex, dropVarKerComplex, CochainComplex.of_d]
      rfl)

/-! ## The restriction is degreewise short exact onto its kernel -/

lemma dropVarSection_aux {p : ℕ} (d : ℤ) (b : (N.dropVar j).cechCochain p d)
    {σ' σ : CechIdx n p} (h : σ'.mapSuccAbove j = σ.mapSuccAbove j) :
    (eqToHom (congrArg (fun X : CechIdx (n + 1) p => (N.loc X.toList).obj d) h)).hom
        ((dropVarLocToLoc N j σ'.toList d).hom (b σ'))
      = (dropVarLocToLoc N j σ.toList d).hom (b σ) := by
  obtain rfl : σ' = σ := CechIdx.mapSuccAbove_injective j h
  simp

lemma surjective_cechCochainDropVarRes (p : ℕ) (d : ℤ) :
    Function.Surjective ((cechCochainDropVarRes N j p d).hom) := by
  classical
  intro b
  refine ⟨fun τ => if h : j ∈ τ.toList then 0 else
    (eqToHom (congrArg (fun X : CechIdx (n + 1) p => (N.loc X.toList).obj d)
      (CechIdx.mapSuccAbove_preSuccAbove j τ h))).hom
      ((dropVarLocToLoc N j (τ.preSuccAbove j h).toList d).hom
        (b (τ.preSuccAbove j h))), ?_⟩
  funext σ
  show (locToDropVarLoc N j σ.toList d).hom
    (dite (j ∈ (σ.mapSuccAbove j).toList) _ _) = b σ
  rw [dif_neg (CechIdx.notMem_mapSuccAbove j σ),
    dropVarSection_aux N j d b (CechIdx.mapSuccAbove_preSuccAbove j _
      (CechIdx.notMem_mapSuccAbove j σ))]
  have h := congrArg ModuleCat.Hom.hom (dropVarLocIso N j σ.toList d).hom_inv_id
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h (b σ)

lemma ker_cechCochainDropVarRes (p : ℕ) (d : ℤ) :
    LinearMap.ker ((cechCochainDropVarRes N j p d).hom)
      = dropVarKerSub N j p d := by
  ext c
  simp only [LinearMap.mem_ker]
  constructor
  · intro hc τ hτ
    obtain ⟨σ, rfl⟩ := CechIdx.exists_mapSuccAbove j τ hτ
    have hσ : (locToDropVarLoc N j σ.toList d).hom (c (σ.mapSuccAbove j)) = 0 :=
      congrFun hc σ
    have hinj : Function.Injective ((locToDropVarLoc N j σ.toList d).hom) :=
      (ModuleCat.mono_iff_injective _).mp
        (by rw [show locToDropVarLoc N j σ.toList d
          = (dropVarLocIso N j σ.toList d).inv from rfl]; infer_instance)
    exact hinj (by rw [hσ, map_zero])
  · intro hc
    funext σ
    show (locToDropVarLoc N j σ.toList d).hom (c (σ.mapSuccAbove j)) = 0
    rw [hc _ (CechIdx.notMem_mapSuccAbove j σ), map_zero]

/-- The short complex `K → Č(N) → Č(N.dropVar j)`. -/
noncomputable def dropVarShortComplex (d : ℤ) :
    CategoryTheory.ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  CategoryTheory.ShortComplex.mk (dropVarKerι N j d) (cechComplexDropVarRes N j d) (by
    ext p : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun σ => ?_)
    show (locToDropVarLoc N j σ.toList d).hom (c.1 (σ.mapSuccAbove j)) = 0
    rw [c.2 _ (CechIdx.notMem_mapSuccAbove j σ), map_zero])

theorem dropVarShortComplex_shortExact (d : ℤ) :
    (dropVarShortComplex N j d).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro p
  exact
    { exact := by
        rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
        show LinearMap.range ((dropVarKerSub N j p d).subtype)
          = LinearMap.ker ((cechCochainDropVarRes N j p d).hom)
        rw [ker_cechCochainDropVarRes]
        exact Submodule.range_subtype _
      mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr
        (surjective_cechCochainDropVarRes N j p d) }

/-! ## The kernel complex is `x_j`-periodic -/

/-- Multiplication by `x_j` on the kernel complex. -/
noncomputable def dropVarKerMulX (d : ℤ) :
    dropVarKerComplex N j d ⟶ dropVarKerComplex N j (d + 1) :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (((N.cechMulX j d).f p).hom.restrict
      (fun _ hc => cechMulX_mem_dropVarKerSub N j hc j)))
    (fun p => by
      simp only [dropVarKerComplex, CochainComplex.of_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun c => Subtype.ext ?_)
      have h := congrArg ModuleCat.Hom.hom ((N.cechMulX j d).comm p (p + 1))
      simp only [ModuleCat.hom_comp, cechComplex, CochainComplex.of_d] at h
      exact LinearMap.congr_fun h c.1)

lemma bijective_dropVarKerMulX (d : ℤ) (p : ℕ) :
    Function.Bijective (((dropVarKerMulX N j d).f p).hom) := by
  have hiso : ∀ τ : CechIdx (n + 1) p, j ∈ τ.toList →
      Function.Bijective (((N.loc τ.toList).mulX j d).hom) := by
    intro τ hτ
    haveI := N.loc_mulX_isIso τ.toList j hτ d
    exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  constructor
  · intro x z hxz
    refine Subtype.ext (funext fun τ => ?_)
    by_cases hτ : j ∈ τ.toList
    · refine (hiso τ hτ).1 ?_
      exact congrFun (congrArg Subtype.val hxz) τ
    · rw [x.2 τ hτ, z.2 τ hτ]
  · classical
    intro b
    choose w hw using fun τ (hτ : j ∈ τ.toList) => (hiso τ hτ).2 (b.1 τ)
    refine ⟨⟨fun τ => if hτ : j ∈ τ.toList then w τ hτ else 0, ?_⟩, ?_⟩
    · intro τ hτ
      exact dif_neg hτ
    · refine Subtype.ext (funext fun τ => ?_)
      show ((N.loc τ.toList).mulX j d).hom (dite (j ∈ τ.toList) _ _) = b.1 τ
      by_cases hτ : j ∈ τ.toList
      · rw [dif_pos hτ, hw τ hτ]
      · rw [dif_neg hτ, map_zero, b.2 τ hτ]

instance isIso_dropVarKerMulX (d : ℤ) : IsIso (dropVarKerMulX N j d) := by
  haveI : ∀ p : ℕ, IsIso ((dropVarKerMulX N j d).f p) := by
    intro p
    haveI : Mono ((dropVarKerMulX N j d).f p) :=
      (ModuleCat.mono_iff_injective _).mpr (bijective_dropVarKerMulX N j d p).1
    haveI : Epi ((dropVarKerMulX N j d).f p) :=
      (ModuleCat.epi_iff_surjective _).mpr (bijective_dropVarKerMulX N j d p).2
    exact isIso_of_mono_of_epi _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The homology of the kernel complex does not depend on the twist. -/
lemma subsingleton_homology_dropVarKer_step (d : ℤ) (q : ℕ)
    (h : Subsingleton ((dropVarKerComplex N j (d + 1)).homology q)) :
    Subsingleton ((dropVarKerComplex N j d).homology q) := by
  haveI : IsIso (HomologicalComplex.homologyMap (dropVarKerMulX N j d) q) := by
    rw [show HomologicalComplex.homologyMap (dropVarKerMulX N j d) q
      = (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q).map
        (dropVarKerMulX N j d) from rfl]
    infer_instance
  haveI := h
  constructor
  intro x z
  have hinj : Function.Injective
      ((HomologicalComplex.homologyMap (dropVarKerMulX N j d) q).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hinj (Subsingleton.elim _ _)

lemma subsingleton_homology_dropVarKer_of_le {d : ℤ} (e : ℕ) (q : ℕ)
    (h : Subsingleton ((dropVarKerComplex N j (d + (e : ℤ))).homology q)) :
    Subsingleton ((dropVarKerComplex N j d).homology q) := by
  induction e generalizing d with
  | zero => simpa using h
  | succ t ih =>
      refine subsingleton_homology_dropVarKer_step N j d q (ih ?_)
      have hd : d + 1 + (t : ℤ) = d + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hd]
      exact h

/-! ## The augmentation is compatible with the restriction -/

lemma locOf_dropVarLocToLoc (M₀ : GradedModule k (n + 1)) (j₀ : Fin (n + 2))
    (l₀ : List (Fin (n + 1))) (d : ℤ) :
    ((M₀.dropVar j₀).locOf l₀).app d ≫ dropVarLocToLoc M₀ j₀ l₀ d
      = (M₀.locOf (l₀.map j₀.succAbove)).app d := by
  rw [locOf_app, Category.assoc, locIncl_dropVarLocToLoc, ← Category.assoc, locOf_app]
  congr 1
  simp

lemma cechAug₀_dropVarRes (d : ℤ) :
    N.cechAug₀ d ≫ cechCochainDropVarRes N j 0 d = (N.dropVar j).cechAug₀ d := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun σ => ?_)
  have h := congrArg ModuleCat.Hom.hom (locOf_dropVarLocToLoc N j σ.toList d)
  simp only [ModuleCat.hom_comp] at h
  have hiso := congrArg ModuleCat.Hom.hom (dropVarLocIso N j σ.toList d).hom_inv_id
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hiso
  show (locToDropVarLoc N j σ.toList d).hom
      (((N.locOf (σ.toList.map j.succAbove)).app d).hom x)
    = ((N.dropVar j).cechAug₀ d).hom x σ
  have hiso2 : ∀ w, (locToDropVarLoc N j σ.toList d).hom
      ((dropVarLocToLoc N j σ.toList d).hom w) = w := fun w => by
    have hw := LinearMap.congr_fun hiso w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hw
    exact hw
  rw [← h]
  simp only [LinearMap.comp_apply]
  exact hiso2 _

lemma cechAug_dropVarRes (d : ℤ) :
    N.cechAug d ≫ HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0
      = (N.dropVar j).cechAug d := by
  show ((N.cechComplex d).liftCycles (N.cechAug₀ d) 1 (by simp)
        (by rw [N.cechComplex_d_zero_one d]; exact N.cechAug₀_comp_cechD d) ≫
      (N.cechComplex d).homologyπ 0) ≫
      HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0
    = ((N.dropVar j).cechComplex d).liftCycles ((N.dropVar j).cechAug₀ d) 1 (by simp)
        (by rw [(N.dropVar j).cechComplex_d_zero_one d]
            exact (N.dropVar j).cechAug₀_comp_cechD d) ≫
      ((N.dropVar j).cechComplex d).homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  refine (cancel_mono (((N.dropVar j).cechComplex d).iCycles 0)).mp ?_
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact cechAug₀_dropVarRes N j d

/-! ## The kernel complex is exact in large degrees -/

lemma isIso_homologyMap_zero_dropVarRes (d : ℤ)
    (hA : Function.Bijective ((N.cechAug d).hom))
    (hB : Function.Bijective (((N.dropVar j).cechAug d).hom)) :
    IsIso (HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0) := by
  haveI : IsIso (N.cechAug d) := by
    haveI : Mono (N.cechAug d) := (ModuleCat.mono_iff_injective _).mpr hA.1
    haveI : Epi (N.cechAug d) := (ModuleCat.epi_iff_surjective _).mpr hA.2
    exact isIso_of_mono_of_epi _
  haveI : IsIso ((N.dropVar j).cechAug d) := by
    haveI : Mono ((N.dropVar j).cechAug d) := (ModuleCat.mono_iff_injective _).mpr hB.1
    haveI : Epi ((N.dropVar j).cechAug d) := (ModuleCat.epi_iff_surjective _).mpr hB.2
    exact isIso_of_mono_of_epi _
  have hfac : HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0
      = inv (N.cechAug d) ≫ (N.dropVar j).cechAug d := by
    rw [← cechAug_dropVarRes N j d, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac]
  infer_instance

lemma bijective_homologyMap_zero_dropVarRes (d : ℤ)
    (hA : Function.Bijective ((N.cechAug d).hom))
    (hB : Function.Bijective (((N.dropVar j).cechAug d).hom)) :
    Function.Bijective
      ((HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0).hom) := by
  haveI := isIso_homologyMap_zero_dropVarRes N j d hA hB
  exact ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
    (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

lemma injective_homologyMap_zero_dropVarKerι (d : ℤ) :
    Function.Injective ((HomologicalComplex.homologyMap (dropVarKerι N j d) 0).hom) := by
  haveI : Mono ((dropVarKerι N j d).f 0) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hm := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (dropVarKerι N j d) 0 (fun i => by simp)
  exact (ModuleCat.mono_iff_injective _).mp hm

theorem exists_subsingleton_homology_dropVarKer (hN : IsFG N)
    (hdrop : IsFG (N.dropVar j)) :
    ∃ D : ℤ, ∀ d : ℤ, D ≤ d → ∀ q : ℕ,
      Subsingleton ((dropVarKerComplex N j d).homology q) := by
  classical
  choose fA hfA using fun t : ℕ =>
    exists_subsingleton_cechHgr_of_isFG N hN (t + 1) (by omega)
  choose fB hfB using fun t : ℕ =>
    exists_subsingleton_cechHgr_of_isFG (N.dropVar j) hdrop (t + 1) (by omega)
  obtain ⟨dA, hdA⟩ := exists_bijective_cechAug N hN
  obtain ⟨dB, hdB⟩ := exists_bijective_cechAug (N.dropVar j) hdrop
  have hSne : (Finset.range (n + 2)).Nonempty := ⟨0, by simp⟩
  set D : ℤ := max (max dA dB)
    ((Finset.range (n + 2)).sup' hSne (fun t => max (fA t) (fB t))) with hD
  have hDA : dA ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hDB : dB ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDf : ∀ t, t < n + 2 → max (fA t) (fB t) ≤ D := fun t ht =>
    le_trans (Finset.le_sup' (fun t => max (fA t) (fB t)) (Finset.mem_range.mpr ht))
      (le_max_right _ _)
  refine ⟨D, fun d hd q => ?_⟩
  have hvA : ∀ t : ℕ, Subsingleton ((N.cechComplex d).homology (t + 1)) := by
    intro t
    by_cases ht : t < n + 2
    · exact hfA t d (le_trans (le_trans (le_max_left _ _) (hDf t ht)) hd)
    · exact subsingleton_cechHgr N (t + 1) (by omega) d
  have hvB : ∀ t : ℕ, Subsingleton (((N.dropVar j).cechComplex d).homology (t + 1)) := by
    intro t
    by_cases ht : t < n + 2
    · exact hfB t d (le_trans (le_trans (le_max_right _ _) (hDf t ht)) hd)
    · exact subsingleton_cechHgr (N.dropVar j) (t + 1) (by omega) d
  have hbij0 := bijective_homologyMap_zero_dropVarRes N j d
    (hdA d (le_trans hDA hd)) (hdB d (le_trans hDB hd))
  have SE := dropVarShortComplex_shortExact N j d
  have hz : HomologicalComplex.homologyMap (dropVarKerι N j d) 0 ≫
      HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) 0 = 0 := by
    rw [← HomologicalComplex.homologyMap_comp,
      show dropVarKerι N j d ≫ cechComplexDropVarRes N j d = 0 from
        (dropVarShortComplex N j d).zero]
    exact HomologicalComplex.homologyMap_zero _ _ _
  cases q with
  | zero =>
      refine ⟨fun x z => ?_⟩
      refine injective_homologyMap_zero_dropVarKerι N j d (hbij0.1 ?_)
      have hx := congrArg (fun t : (dropVarKerComplex N j d).homology 0
          ⟶ ((N.dropVar j).cechComplex d).homology 0 => t.hom x) hz
      have hzz := congrArg (fun t : (dropVarKerComplex N j d).homology 0
          ⟶ ((N.dropVar j).cechComplex d).homology 0 => t.hom z) hz
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at hx hzz
      rw [hx, hzz]
  | succ t =>
      have hex1 := SE.homology_exact₁ t (t + 1) rfl
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        at hex1
      have hex3 := SE.homology_exact₃ t (t + 1) rfl
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        at hex3
      haveI hsA : Subsingleton (((dropVarShortComplex N j d).X₂).homology (t + 1)) :=
        hvA t
      have hxz : ∀ w : (dropVarKerComplex N j d).homology (t + 1), w = 0 := by
        intro w
        obtain ⟨y, hy⟩ := (hex1 w).mp (Subsingleton.elim _ _)
        rw [← hy]
        cases t with
        | zero =>
            obtain ⟨v, hv⟩ := hbij0.2 y
            exact (hex3 y).mpr ⟨v, hv⟩
        | succ t' =>
            haveI hsB : Subsingleton (((dropVarShortComplex N j d).X₃).homology (t' + 1)) :=
              hvB t'
            rw [Subsingleton.elim y 0, map_zero]
      exact ⟨fun x z => by rw [hxz x, hxz z]⟩

/-! ## The hyperplane comparison -/

theorem subsingleton_homology_dropVarKer (hN : IsFG N) (hdrop : IsFG (N.dropVar j))
    (d : ℤ) (q : ℕ) : Subsingleton ((dropVarKerComplex N j d).homology q) := by
  obtain ⟨D, hD⟩ := exists_subsingleton_homology_dropVarKer N j hN hdrop
  refine subsingleton_homology_dropVarKer_of_le N j ((max d D - d).toNat) q ?_
  have hmax : d + (((max d D - d).toNat : ℕ) : ℤ) = max d D := by
    have h1 : d ≤ max d D := le_max_left _ _
    omega
  rw [hmax]
  exact hD (max d D) (le_max_right _ _) q

theorem bijective_homologyMap_dropVarRes (hN : IsFG N) (hdrop : IsFG (N.dropVar j))
    (q : ℕ) (d : ℤ) :
    Function.Bijective
      ((HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) q).hom) := by
  have SE := dropVarShortComplex_shortExact N j d
  have hex2 := SE.homology_exact₂ q
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex2
  have hex3 := SE.homology_exact₃ q (q + 1) rfl
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex3
  haveI hK : Subsingleton (((dropVarShortComplex N j d).X₁).homology q) :=
    subsingleton_homology_dropVarKer N j hN hdrop d q
  haveI hK' : Subsingleton (((dropVarShortComplex N j d).X₁).homology (q + 1)) :=
    subsingleton_homology_dropVarKer N j hN hdrop d (q + 1)
  constructor
  · intro a b hab
    have h0 : (HomologicalComplex.homologyMap
        (cechComplexDropVarRes N j d) q).hom (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨w, hw⟩ := (hex2 _).mp h0
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact sub_eq_zero.mp hw.symm
  · intro z
    exact (hex3 z).mp (Subsingleton.elim _ _)

lemma mulX'_congr_degree (M₀ : GradedModule k (n + 1)) (i : Fin (n + 2))
    {a b a' b' : ℤ} (ha : a = a') (hb : b = b') (h : a + 1 = b) (h' : a' + 1 = b') :
    M₀.mulX' i a b h ≫ eqToHom (congrArg M₀.obj hb)
      = eqToHom (congrArg M₀.obj ha) ≫ M₀.mulX' i a' b' h' := by
  subst ha
  subst hb
  simp

lemma dropVarLocToLoc_mulX (M₀ : GradedModule k (n + 1)) (j₀ : Fin (n + 2))
    (l₀ : List (Fin (n + 1))) (i' : Fin (n + 1)) (d : ℤ) :
    ((M₀.dropVar j₀).loc l₀).mulX i' d ≫ dropVarLocToLoc M₀ j₀ l₀ (d + 1)
      = dropVarLocToLoc M₀ j₀ l₀ d
        ≫ (M₀.loc (l₀.map j₀.succAbove)).mulX (j₀.succAbove i') d := by
  refine loc_hom_ext (M₀.dropVar j₀) l₀ fun t => ?_
  have e1 := locIncl_mulX (M₀.dropVar j₀) l₀ d t i'
  have e2 := locIncl_dropVarLocToLoc M₀ j₀ l₀ (d + 1) t
  have e3 := locIncl_dropVarLocToLoc M₀ j₀ l₀ d t
  have e4 := locIncl_mulX M₀ (l₀.map j₀.succAbove) d t (j₀.succAbove i')
  conv_lhs => rw [← Category.assoc, e1, Category.assoc, e2]
  conv_rhs => rw [← Category.assoc, e3, Category.assoc, e4]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact mulX'_congr_degree M₀ (j₀.succAbove i')
    (show locDeg l₀ d t = locDeg (l₀.map j₀.succAbove) d t by
      rw [locDeg_def, locDeg_def, List.length_map])
    (show locDeg l₀ (d + 1) t = locDeg (l₀.map j₀.succAbove) (d + 1) t by
      rw [locDeg_def, locDeg_def, List.length_map])
    (by rw [locDeg_def, locDeg_def]; ring) (by rw [locDeg_def, locDeg_def]; ring)

lemma locToDropVarLoc_mulX (M₀ : GradedModule k (n + 1)) (j₀ : Fin (n + 2))
    (l₀ : List (Fin (n + 1))) (i' : Fin (n + 1)) (d : ℤ) :
    locToDropVarLoc M₀ j₀ l₀ d ≫ ((M₀.dropVar j₀).loc l₀).mulX i' d
      = (M₀.loc (l₀.map j₀.succAbove)).mulX (j₀.succAbove i') d
        ≫ locToDropVarLoc M₀ j₀ l₀ (d + 1) := by
  have h := dropVarLocToLoc_mulX M₀ j₀ l₀ i' d
  have hiso : locToDropVarLoc M₀ j₀ l₀ d ≫ dropVarLocToLoc M₀ j₀ l₀ d = 𝟙 _ :=
    (dropVarLocIso M₀ j₀ l₀ d).inv_hom_id
  have hiso' : dropVarLocToLoc M₀ j₀ l₀ (d + 1) ≫ locToDropVarLoc M₀ j₀ l₀ (d + 1) = 𝟙 _ :=
    (dropVarLocIso M₀ j₀ l₀ (d + 1)).hom_inv_id
  calc locToDropVarLoc M₀ j₀ l₀ d ≫ ((M₀.dropVar j₀).loc l₀).mulX i' d
      = locToDropVarLoc M₀ j₀ l₀ d ≫ (((M₀.dropVar j₀).loc l₀).mulX i' d
          ≫ dropVarLocToLoc M₀ j₀ l₀ (d + 1)) ≫ locToDropVarLoc M₀ j₀ l₀ (d + 1) := by
        rw [Category.assoc, hiso', Category.comp_id]
    _ = locToDropVarLoc M₀ j₀ l₀ d ≫ (dropVarLocToLoc M₀ j₀ l₀ d
          ≫ (M₀.loc (l₀.map j₀.succAbove)).mulX (j₀.succAbove i') d)
          ≫ locToDropVarLoc M₀ j₀ l₀ (d + 1) := by rw [h]
    _ = (M₀.loc (l₀.map j₀.succAbove)).mulX (j₀.succAbove i') d
          ≫ locToDropVarLoc M₀ j₀ l₀ (d + 1) := by
        rw [← Category.assoc, ← Category.assoc, hiso, Category.id_comp]

lemma cechMulX_cechCochainDropVarRes (i' : Fin (n + 1)) (p : ℕ) (d : ℤ) :
    (N.cechMulX (j.succAbove i') d).f p ≫ cechCochainDropVarRes N j p (d + 1)
      = cechCochainDropVarRes N j p d ≫ ((N.dropVar j).cechMulX i' d).f p := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun σ => ?_)
  show (locToDropVarLoc N j σ.toList (d + 1)).hom
      (((N.loc (σ.toList.map j.succAbove)).mulX (j.succAbove i') d).hom
        (c (σ.mapSuccAbove j)))
    = (((N.dropVar j).loc σ.toList).mulX i' d).hom
        ((locToDropVarLoc N j σ.toList d).hom (c (σ.mapSuccAbove j)))
  have h := congrArg ModuleCat.Hom.hom (locToDropVarLoc_mulX N j σ.toList i' d)
  simp only [ModuleCat.hom_comp] at h
  exact (LinearMap.congr_fun h (c (σ.mapSuccAbove j))).symm

/-- The comparison morphism of graded modules. -/
noncomputable def dropVarHgrHom (i : ℕ) :
    (N.cechHgr i).dropVar j ⟶ (N.dropVar j).cechHgr i where
  app d := HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) i
  comm i' d := by
    show HomologicalComplex.homologyMap (cechComplexDropVarRes N j d) i ≫
        HomologicalComplex.homologyMap ((N.dropVar j).cechMulX i' d) i
      = HomologicalComplex.homologyMap (N.cechMulX (j.succAbove i') d) i ≫
        HomologicalComplex.homologyMap (cechComplexDropVarRes N j (d + 1)) i
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    ext p : 1
    exact (cechMulX_cechCochainDropVarRes N j i' p d).symm

/-- **The hyperplane comparison**: for a finitely generated graded module killed by a
linear form with a unit coefficient, forgetting the variable `x_j` does not change the
Čech cohomology. -/
noncomputable def dropVarHgrIso (hN : IsFG N) (hdrop : IsFG (N.dropVar j)) (i : ℕ) :
    (N.dropVar j).cechHgr i ≅ (N.cechHgr i).dropVar j :=
  (isoOfBijective (dropVarHgrHom N j i)
    (fun d => bijective_homologyMap_dropVarRes N j hN hdrop i d)).symm

end AlgebraicGeometry.ProjectiveSpace.GradedModule



end
