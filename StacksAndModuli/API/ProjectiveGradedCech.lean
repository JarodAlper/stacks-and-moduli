module

public import StacksAndModuli.API.ProjectiveGradedLocalization
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# The graded Čech complex of the standard affine cover

Supporting API with no Stacks Project counterpart, towards the construction obligation
`Cohomology.nonempty` of `StacksAndModuli/API/ProjectiveGradedCohomology.lean`.

For a graded module `M` over `S = k[x₀, …, xₙ]` and a degree `d`, the Čech complex of
the standard affine cover `ℙⁿ = ⋃ D₊(xᵢ)` has `p`-cochains the product of the degree-`d`
pieces of the localizations `M[1/x_σ]` over the strictly increasing `(p+1)`-tuples `σ`
of variables, with the alternating differential given by the restriction maps of
`API/ProjectiveGradedLocalization.lean`.

This file constructs the index combinatorics (`CechIdx`, `CechIdx.face`), the cochain
modules (`cechCochain`) and the differential (`cechD`), and proves the simplicial
relations needed for `δ ≫ δ = 0`.

Main declarations:
- `CechIdx`, `CechIdx.face`, `CechIdx.face_face`;
- `GradedModule.cechCochain`, `GradedModule.cechD`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory

/-! ## Index combinatorics -/

/-- Erasing a smaller index after a larger one agrees with erasing them in the other
order: the simplicial face relation at the level of lists. -/
lemma List.eraseIdx_eraseIdx_of_le {α : Type*} :
    ∀ (L : List α) (i j : ℕ), j ≤ i →
      (L.eraseIdx (i + 1)).eraseIdx j = (L.eraseIdx j).eraseIdx i
  | [], _, _, _ => by simp
  | a :: t, i, 0, _ => by simp
  | a :: t, i + 1, j + 1, h => by
      simp only [List.eraseIdx_cons_succ, List.cons.injEq, true_and]
      exact List.eraseIdx_eraseIdx_of_le t i j (by omega)
  | a :: t, 0, j + 1, h => by omega

/-- A strictly increasing `(p+1)`-tuple of variables: the index of a Čech cochain. -/
structure CechIdx (n p : ℕ) : Type where
  /-- The underlying sorted list of variables. -/
  toList : List (Fin (n + 1))
  /-- The list is strictly increasing. -/
  sorted : toList.Pairwise (· < ·)
  /-- The list has `p + 1` entries. -/
  length_eq : toList.length = p + 1

namespace CechIdx

variable {n p : ℕ}

@[ext] lemma ext {σ τ : CechIdx n p} (h : σ.toList = τ.toList) : σ = τ := by
  cases σ; cases τ; simpa using h

/-- The element at position `i` of the tuple. -/
def elem (τ : CechIdx n p) (i : Fin (p + 1)) : Fin (n + 1) :=
  τ.toList[(i : ℕ)]'(by rw [τ.length_eq]; exact i.isLt)

/-- The `i`-th face of a tuple: remove the `i`-th entry. -/
def face (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) : CechIdx n p where
  toList := τ.toList.eraseIdx i
  sorted := List.Pairwise.eraseIdx _ τ.sorted
  length_eq := by
    rw [List.length_eraseIdx_of_lt (by rw [τ.length_eq]; exact i.isLt),
      τ.length_eq]
    omega

@[simp] lemma face_toList (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) :
    (τ.face i).toList = τ.toList.eraseIdx i := rfl

/-- The simplicial face relation: for `j ≤ i`, the `j`-th face of the `(i+1)`-th face
is the `i`-th face of the `j`-th face. -/
lemma face_face (τ : CechIdx n (p + 2)) (i j : ℕ) (hij : j ≤ i)
    (hi : i + 1 ≤ p + 2) :
    (τ.face ⟨i + 1, by omega⟩).face ⟨j, by omega⟩ =
      (τ.face ⟨j, by omega⟩).face ⟨i, by omega⟩ := by
  refine CechIdx.ext ?_
  simp only [face_toList]
  exact List.eraseIdx_eraseIdx_of_le τ.toList i j hij

/-- The permutation witness for the face restriction: the tuple is a permutation of its
face with the removed element appended. -/
lemma perm_face_append (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) :
    τ.toList.Perm ((τ.face i).toList ++ [τ.elem i]) := by
  refine ((List.perm_append_singleton _ _).trans ?_).symm
  exact List.getElem_cons_eraseIdx_perm (by rw [τ.length_eq]; exact i.isLt)

end CechIdx

/-! ## Cochains and the differential -/

variable {k : Type u} [CommRing k] {n : ℕ}

variable (M : GradedModule k n)

/-- The face restriction on localizations: invert the removed variable as well. -/
noncomputable def cechFaceMap {p : ℕ} (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) :
    M.loc (τ.face i).toList ⟶ M.loc τ.toList :=
  M.locRes (τ.face i).toList (m := [τ.elem i]) (τ.perm_face_append i)

/-- Čech `p`-cochains in degree `d`: a section of the degree-`d` pieces of the
localizations over all strictly increasing `(p+1)`-tuples. -/
noncomputable def cechCochain (p : ℕ) (d : ℤ) : ModuleCat.{u} k :=
  ModuleCat.of k (Π τ : CechIdx n p, ((M.loc τ.toList).obj d))

/-- The alternating Čech differential. -/
noncomputable def cechD (p : ℕ) (d : ℤ) :
    M.cechCochain p d ⟶ M.cechCochain (p + 1) d :=
  ModuleCat.ofHom
    { toFun := fun c τ => ∑ i : Fin (p + 2),
        ((-1 : ℤ) ^ (i : ℕ)) • ((M.cechFaceMap τ i).app d).hom (c (τ.face i))
      map_add' := fun c₁ c₂ => by
        funext τ
        simp only [Pi.add_apply, map_add, smul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext τ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_comm] }

/-! ## The simplicial relation for the face restrictions -/

/-- Restriction maps with permuted missing factors agree. -/
lemma locRes_congr {l l' m₁ m₂ : List (Fin (n + 1))} (hm : m₁.Perm m₂)
    (hp₁ : l'.Perm (l ++ m₁)) (hp₂ : l'.Perm (l ++ m₂)) :
    M.locRes l hp₁ = M.locRes l hp₂ := by
  refine hom_ext fun d => ?_
  show M.locResApp l hp₁ d = M.locResApp l hp₂ d
  refine loc_hom_ext M l fun j => ?_
  rw [locIncl_locResApp, locIncl_locResApp]
  congr 1
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, listPow_coe, listPow_coe]
  exact congrArg _ (Multiset.coe_eq_coe.mpr hm)

/-- Restriction maps with equal sources and permuted missing factors agree, up to the
transport of the source. -/
lemma locRes_congr_list {l₁ l₂ l' m₁ m₂ : List (Fin (n + 1))} (h : l₁ = l₂)
    (hm : m₁.Perm m₂) (hp₁ : l'.Perm (l₁ ++ m₁)) (hp₂ : l'.Perm (l₂ ++ m₂)) :
    M.locRes l₁ hp₁ = eqToHom (by rw [h]) ≫ M.locRes l₂ hp₂ := by
  subst h
  rw [locRes_congr M hm hp₁ hp₂, eqToHom_refl, Category.id_comp]

/-- The composite of two face restrictions is the two-variable restriction. -/
lemma cechFaceMap_cechFaceMap {p : ℕ} (τ : CechIdx n (p + 2)) (i : Fin (p + 3))
    (j : Fin (p + 2)) :
    M.cechFaceMap (τ.face i) j ≫ M.cechFaceMap τ i =
      M.locRes ((τ.face i).face j).toList
        (m := [(τ.face i).elem j] ++ [τ.elem i])
        ((τ.perm_face_append i).trans
          ((((τ.face i).perm_face_append j).append_right _).trans
            (by rw [List.append_assoc]))) := by
  exact M.locRes_locRes ((τ.face i).face j).toList
    ((τ.face i).perm_face_append j) (τ.perm_face_append i)

namespace CechIdx

variable {p : ℕ}

/-- Below the erased position, the elements of a face agree with the original. -/
lemma elem_face_of_lt (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) (j : Fin (p + 1))
    (h : (j : ℕ) < (i : ℕ)) :
    (τ.face i).elem j = τ.elem ⟨(j : ℕ), by omega⟩ := by
  unfold elem
  simp only [face_toList]
  exact List.getElem_eraseIdx_of_lt
    (by rw [← face_toList, (τ.face i).length_eq]; exact j.isLt) h

/-- At and above the erased position, the elements of a face are shifted. -/
lemma elem_face_of_ge (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) (j : Fin (p + 1))
    (h : (i : ℕ) ≤ (j : ℕ)) :
    (τ.face i).elem j = τ.elem ⟨(j : ℕ) + 1, by omega⟩ := by
  unfold elem
  simp only [face_toList]
  exact List.getElem_eraseIdx_of_ge
    (by rw [← face_toList, (τ.face i).length_eq]; exact j.isLt) h

end CechIdx

/-! ## The double differential vanishes -/

variable {p : ℕ}

/-- Transport a restriction term along an equality of source tuples. -/
lemma cech_term_congr {d : ℤ} {p : ℕ} {L : List (Fin (n + 1))}
    {σ σ' : CechIdx n p} (h : σ' = σ) {m m' : List (Fin (n + 1))}
    (hm : m'.Perm m) (w' : L.Perm (σ'.toList ++ m')) (w : L.Perm (σ.toList ++ m))
    (c : ∀ ρ : CechIdx n p, ((M.loc ρ.toList).obj d)) :
    ((M.locRes σ'.toList w').app d).hom (c σ') =
      ((M.locRes σ.toList w).app d).hom (c σ) := by
  subst h
  rw [locRes_congr M hm w' w]

/-- One term of the Čech double differential. -/
noncomputable def cechTerm (d : ℤ) (τ : CechIdx n (p + 2)) (i : Fin (p + 3))
    (j : Fin (p + 2)) (c : ∀ ρ : CechIdx n p, ((M.loc ρ.toList).obj d)) :
    ((M.loc τ.toList).obj d) :=
  ((M.cechFaceMap τ i).app d).hom
    (((M.cechFaceMap (τ.face i) j).app d).hom (c ((τ.face i).face j)))

/-- The double-face term through the collapsed two-variable restriction. -/
lemma cechTerm_eq_locRes (d : ℤ) (τ : CechIdx n (p + 2)) (i : Fin (p + 3))
    (j : Fin (p + 2)) (c : ∀ ρ : CechIdx n p, ((M.loc ρ.toList).obj d)) :
    M.cechTerm d τ i j c =
      ((M.locRes ((τ.face i).face j).toList
        (m := [(τ.face i).elem j] ++ [τ.elem i])
        ((τ.perm_face_append i).trans
          ((((τ.face i).perm_face_append j).append_right _).trans
            (by rw [List.append_assoc])))).app d).hom (c ((τ.face i).face j)) := by
  have h1 := congrArg (fun (t : M.loc ((τ.face i).face j).toList ⟶ M.loc τ.toList) =>
    (t.app d).hom) (M.cechFaceMap_cechFaceMap τ i j)
  have h2 := LinearMap.congr_fun h1 (c ((τ.face i).face j))
  simpa [cechTerm, comp_app, ModuleCat.hom_comp] using h2

/-- The fundamental pairing: the `(i, j)`-term with `i ≤ j` agrees with the
`(j+1, i)`-term. -/
lemma cechTerm_pair (d : ℤ) (τ : CechIdx n (p + 2)) (i : Fin (p + 3))
    (j : Fin (p + 2)) (hij : (i : ℕ) ≤ (j : ℕ))
    (c : ∀ ρ : CechIdx n p, ((M.loc ρ.toList).obj d)) :
    M.cechTerm d τ ⟨(j : ℕ) + 1, by omega⟩ ⟨(i : ℕ), by omega⟩ c =
      M.cechTerm d τ i j c := by
  rw [cechTerm_eq_locRes, cechTerm_eq_locRes]
  refine cech_term_congr M ?_ ?_ _ _ c
  · exact CechIdx.face_face τ (j : ℕ) (i : ℕ) hij
      (by have := j.isLt; omega)
  · -- the two removed-element lists are swaps of one another
    have e₁ : (τ.face ⟨(j : ℕ) + 1, by omega⟩).elem ⟨(i : ℕ), by omega⟩ =
        τ.elem ⟨(i : ℕ), by omega⟩ := by
      refine CechIdx.elem_face_of_lt τ _ _ ?_
      exact Nat.lt_succ_of_le hij
    have e₂ : (τ.face i).elem j = τ.elem ⟨(j : ℕ) + 1, by omega⟩ := by
      refine CechIdx.elem_face_of_ge τ _ _ ?_
      exact hij
    rw [e₁, e₂]
    exact List.Perm.swap _ _ _

/-- The Čech differential squares to zero. -/
lemma cechD_comp_cechD (p : ℕ) (d : ℤ) :
    M.cechD p d ≫ M.cechD (p + 1) d = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show (∑ i : Fin (p + 3), ((-1 : ℤ) ^ (i : ℕ)) • ((M.cechFaceMap τ i).app d).hom
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        ((M.cechFaceMap (τ.face i) j).app d).hom (c ((τ.face i).face j)))) = 0
  have hstep : ∀ i : Fin (p + 3),
      ((-1 : ℤ) ^ (i : ℕ)) • ((M.cechFaceMap τ i).app d).hom
        (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          ((M.cechFaceMap (τ.face i) j).app d).hom (c ((τ.face i).face j))) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        M.cechTerm d τ i j c := by
    intro i
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, ← pow_add]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.sum_product']
  refine Finset.sum_involution
    (fun x _ =>
      if h : (x.1 : ℕ) ≤ (x.2 : ℕ) then
        (⟨(x.2 : ℕ) + 1, by omega⟩, ⟨(x.1 : ℕ), by omega⟩)
      else
        (⟨(x.2 : ℕ), by omega⟩, ⟨(x.1 : ℕ) - 1, by omega⟩))
    ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ -
    by_cases h : (i : ℕ) ≤ (j : ℕ)
    · rw [dite_eq_left h]
      rw [M.cechTerm_pair d τ i j h c]
      have hsign : ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) +
          ((-1 : ℤ) ^ (((j : ℕ) + 1) + (i : ℕ))) = 0 := by
        rw [show ((j : ℕ) + 1) + (i : ℕ) = ((i : ℕ) + (j : ℕ)) + 1 from by omega,
          pow_succ]
        ring
      rw [← add_smul]
      rw [show ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) +
          ((-1 : ℤ) ^ (((j : ℕ) + 1) + (i : ℕ))) = 0 from hsign, zero_smul]
    · rw [dite_eq_right h]
      rw [Nat.not_le] at h
      have hj : (j : ℕ) ≤ (i : ℕ) - 1 := by omega
      have hpair := M.cechTerm_pair d τ ⟨(j : ℕ), by omega⟩
        ⟨(i : ℕ) - 1, by omega⟩ hj c
      have hi1 : ((i : ℕ) - 1) + 1 = (i : ℕ) := by omega
      rw [show (⟨((i : ℕ) - 1) + 1, by omega⟩ : Fin (p + 3)) =
          ⟨(i : ℕ), by omega⟩ from by ext; omega] at hpair
      rw [show (⟨(i : ℕ), by omega⟩ : Fin (p + 3)) = i from by ext; rfl,
        show (⟨(j : ℕ), by omega⟩ : Fin (p + 2)) = j from by ext; rfl] at hpair
      rw [← hpair]
      have hsign : ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) +
          ((-1 : ℤ) ^ ((j : ℕ) + ((i : ℕ) - 1))) = 0 := by
        rw [show (i : ℕ) + (j : ℕ) = ((j : ℕ) + ((i : ℕ) - 1)) + 1 from by omega,
          pow_succ]
        ring
      rw [← add_smul, hsign, zero_smul]
  · rintro ⟨i, j⟩ - hne
    by_cases h : (i : ℕ) ≤ (j : ℕ)
    · rw [dite_eq_left h]
      intro hcontra
      have h1 := congrArg (fun x => (x.1 : ℕ)) hcontra
      have h2 := congrArg (fun x => (x.2 : ℕ)) hcontra
      simp at h1 h2
      omega
    · rw [dite_eq_right h]
      rw [Nat.not_le] at h
      intro hcontra
      have h1 := congrArg (fun x => (x.1 : ℕ)) hcontra
      have h2 := congrArg (fun x => (x.2 : ℕ)) hcontra
      simp at h1 h2
      omega
  · rintro ⟨i, j⟩ -
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩ -
    by_cases h : (i : ℕ) ≤ (j : ℕ)
    · rw [dite_eq_left h]
      have h2 : ¬ ((j : ℕ) + 1 ≤ (i : ℕ)) := by omega
      rw [dite_eq_right h2]
      refine Prod.ext ?_ ?_
      · ext; simp
      · ext; simp
    · rw [dite_eq_right h]
      rw [Nat.not_le] at h
      have h2 : (j : ℕ) ≤ (i : ℕ) - 1 := by omega
      rw [dite_eq_left h2]
      refine Prod.ext ?_ ?_
      · ext; simp; omega
      · ext; simp

/-! ## The Čech complex and its functoriality -/

/-- Localization of a morphism commutes with restriction. -/
lemma locMap_locRes {N : GradedModule k n} (φ : M ⟶ N)
    {l l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) :
    locMap l φ ≫ N.locRes l hp = M.locRes l hp ≫ locMap l' φ := by
  refine hom_ext fun d => ?_
  rw [comp_app, comp_app]
  refine loc_hom_ext M l fun j => ?_
  rw [← Category.assoc, locIncl_locMap M l φ d j, Category.assoc,
    show (N.locRes l hp).app d = N.locResApp l hp d from rfl,
    locIncl_locResApp N l hp d j,
    ← Category.assoc (M.locIncl l d j),
    show (M.locRes l hp).app d = M.locResApp l hp d from rfl,
    locIncl_locResApp M l hp d j, Category.assoc,
    locIncl_locMap M l' φ d j]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact comm_mulList φ (listPow m j) _ _ _

/-- The Čech complex of a graded module in a fixed twist degree. -/
noncomputable def cechComplex (d : ℤ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun p => M.cechCochain p d) (fun p => M.cechD p d)
    (fun p => M.cechD_comp_cechD p d)

variable {M} in
/-- Functoriality of Čech cochains. -/
noncomputable def cechCochainMap {N : GradedModule k n} (φ : M ⟶ N) (p : ℕ)
    (d : ℤ) : M.cechCochain p d ⟶ N.cechCochain p d :=
  ModuleCat.ofHom
    { toFun := fun c τ => ((locMap τ.toList φ).app d).hom (c τ)
      map_add' := fun c₁ c₂ => by
        funext τ
        simp only [Pi.add_apply, map_add]
      map_smul' := fun a c => by
        funext τ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }

variable {M} in
/-- The Čech differential is natural. -/
lemma cechD_naturality {N : GradedModule k n} (φ : M ⟶ N) (p : ℕ) (d : ℤ) :
    M.cechD p d ≫ cechCochainMap φ (p + 1) d =
      cechCochainMap φ p d ≫ N.cechD p d := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show ((locMap τ.toList φ).app d).hom
      (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((M.cechFaceMap τ i).app d).hom (c (τ.face i))) =
    ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      ((N.cechFaceMap τ i).app d).hom
        (((locMap (τ.face i).toList φ).app d).hom (c (τ.face i)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  have h1 := congrArg (fun (t : M.loc (τ.face i).toList ⟶ N.loc τ.toList) =>
    (t.app d).hom) (locMap_locRes M φ (τ.perm_face_append i)).symm
  have h2 := LinearMap.congr_fun h1 (c (τ.face i))
  simpa [comp_app, ModuleCat.hom_comp, cechFaceMap] using h2

variable {M} in
/-- The Čech complex is functorial. -/
noncomputable def cechComplexMap {N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) :
    M.cechComplex d ⟶ N.cechComplex d :=
  CochainComplex.ofHom (fun p => cechCochainMap φ p d) (fun p => by
    simpa only [cechComplex, CochainComplex.of_d] using
      (cechD_naturality φ p d).symm)

variable {M} in
/-- The Čech chain map of an identity is the identity. -/
lemma cechComplexMap_id (d : ℤ) :
    cechComplexMap (𝟙 M) d = 𝟙 (M.cechComplex d) := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show ((locMap τ.toList (𝟙 M)).app d).hom (c τ) = c τ
  have h1 := congrArg (fun (t : M.loc τ.toList ⟶ M.loc τ.toList) =>
    (t.app d).hom) (locMap_id M τ.toList)
  exact LinearMap.congr_fun h1 (c τ)

variable {M} in
/-- The Čech chain map of a composite is the composite. -/
lemma cechComplexMap_comp {N P : GradedModule k n} (φ : M ⟶ N) (ψ : N ⟶ P)
    (d : ℤ) :
    cechComplexMap (φ ≫ ψ) d = cechComplexMap φ d ≫ cechComplexMap ψ d := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show ((locMap τ.toList (φ ≫ ψ)).app d).hom (c τ) = _
  have h1 := congrArg (fun (t : M.loc τ.toList ⟶ P.loc τ.toList) =>
    (t.app d).hom) (locMap_comp M τ.toList φ ψ)
  exact LinearMap.congr_fun h1 (c τ)

variable {M} in
/-- The Čech cochains of a short exact sequence of graded modules form a degreewise
short exact sequence. -/
theorem cech_shortExact {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (p : ℕ) (d : ℤ) :
    Function.Injective (cechCochainMap φ p d).hom ∧
      LinearMap.range (cechCochainMap φ p d).hom =
        LinearMap.ker (cechCochainMap ψ p d).hom ∧
      Function.Surjective (cechCochainMap ψ p d).hom := by
  refine ⟨?_, ?_, ?_⟩
  · intro c₁ c₂ hc
    funext τ
    have hτ := congrFun hc τ
    exact (loc_shortExact M (l := τ.toList) h).injective d hτ
  · ext c
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨c₀, rfl⟩
      funext τ
      show ((locMap τ.toList ψ).app d).hom
        (((locMap τ.toList φ).app d).hom (c₀ τ)) = 0
      have hmem : ((locMap τ.toList φ).app d).hom (c₀ τ) ∈
          LinearMap.range ((locMap τ.toList φ).app d).hom := ⟨c₀ τ, rfl⟩
      rw [(loc_shortExact M (l := τ.toList) h).exact d] at hmem
      exact hmem
    · intro hc
      have hτ : ∀ τ : CechIdx n p, ∃ x,
          ((locMap τ.toList φ).app d).hom x = c τ := by
        intro τ
        have hker : c τ ∈ LinearMap.ker ((locMap τ.toList ψ).app d).hom := by
          rw [LinearMap.mem_ker]
          exact congrFun hc τ
        rw [← (loc_shortExact M (l := τ.toList) h).exact d] at hker
        exact hker
      choose c₀ hc₀ using hτ
      refine ⟨c₀, ?_⟩
      funext τ
      exact hc₀ τ
  · intro c
    have hτ : ∀ τ : CechIdx n p, ∃ x,
        ((locMap τ.toList ψ).app d).hom x = c τ := fun τ =>
      (loc_shortExact M (l := τ.toList) h).surjective d (c τ)
    choose c₀ hc₀ using hτ
    refine ⟨c₀, ?_⟩
    funext τ
    exact hc₀ τ

/-! ## Multiplication and graded Čech cohomology -/

/-- Multiplication by a variable, as a chain map raising the twist degree. -/
noncomputable def cechMulX (i : Fin (n + 1)) (d : ℤ) :
    M.cechComplex d ⟶ M.cechComplex (d + 1) :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom
      { toFun := fun c τ => (((M.loc τ.toList).mulX i d).hom (c τ))
        map_add' := fun c₁ c₂ => by
          funext τ
          simp only [Pi.add_apply, map_add]
        map_smul' := fun a c => by
          funext τ
          simp only [Pi.smul_apply, map_smul, RingHom.id_apply] })
    (fun p => by
      simp only [cechComplex, CochainComplex.of_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
      show (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          ((M.cechFaceMap τ j).app (d + 1)).hom
            (((M.loc (τ.face j).toList).mulX i d).hom (c (τ.face j)))) =
        ((M.loc τ.toList).mulX i d).hom
          (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            ((M.cechFaceMap τ j).app d).hom (c (τ.face j)))
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul]
      congr 1
      have h1 := congrArg ModuleCat.Hom.hom
        (M.locResApp_mulX (τ.face j).toList (τ.perm_face_append j) d i)
      simp only [ModuleCat.hom_comp] at h1
      exact (LinearMap.congr_fun h1 (c (τ.face j))).symm)

/-- Multiplication chain maps commute. -/
lemma cechMulX_comm (i j : Fin (n + 1)) (d : ℤ) :
    M.cechMulX i d ≫ M.cechMulX j (d + 1) =
      M.cechMulX j d ≫ M.cechMulX i (d + 1) := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show ((M.loc τ.toList).mulX j (d + 1)).hom
      (((M.loc τ.toList).mulX i d).hom (c τ)) =
    ((M.loc τ.toList).mulX i (d + 1)).hom
      (((M.loc τ.toList).mulX j d).hom (c τ))
  have h1 := congrArg ModuleCat.Hom.hom ((M.loc τ.toList).mulX_comm i j d)
  simp only [ModuleCat.hom_comp] at h1
  exact LinearMap.congr_fun h1 (c τ)

/-- Graded Čech cohomology: the homology of the Čech complexes, with the variable
action induced on homology.  This is the candidate for the `Hgr` field of the
cohomology interface `Cohomology`. -/
noncomputable def cechHgr (q : ℕ) : GradedModule k n where
  obj d := (M.cechComplex d).homology q
  mulX i d := HomologicalComplex.homologyMap (M.cechMulX i d) q
  mulX_comm i j d := by
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, cechMulX_comm]

variable {M} in
/-- Functoriality of graded Čech cohomology. -/
noncomputable def cechHgrMap {N : GradedModule k n} (φ : M ⟶ N) (q : ℕ) :
    M.cechHgr q ⟶ N.cechHgr q where
  app d := HomologicalComplex.homologyMap (cechComplexMap φ d) q
  comm i d := by
    show HomologicalComplex.homologyMap (cechComplexMap φ d) q ≫
        HomologicalComplex.homologyMap (N.cechMulX i d) q =
      HomologicalComplex.homologyMap (M.cechMulX i d) q ≫
        HomologicalComplex.homologyMap (cechComplexMap φ (d + 1)) q
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    congr 1
    ext p : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    show ((N.loc τ.toList).mulX i d).hom
        (((locMap τ.toList φ).app d).hom (c τ)) =
      ((locMap τ.toList φ).app (d + 1)).hom
        (((M.loc τ.toList).mulX i d).hom (c τ))
    have h1 := congrArg ModuleCat.Hom.hom ((locMap τ.toList φ).comm i d)
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 (c τ)

/-- Graded Čech cohomology is functorial: identities. -/
lemma cechHgrMap_id (q : ℕ) : cechHgrMap (𝟙 M) q = 𝟙 (M.cechHgr q) := by
  refine hom_ext fun d => ?_
  show HomologicalComplex.homologyMap (cechComplexMap (𝟙 M) d) q = 𝟙 _
  rw [cechComplexMap_id, HomologicalComplex.homologyMap_id]

variable {M} in
/-- Graded Čech cohomology is functorial: composition. -/
lemma cechHgrMap_comp {N P : GradedModule k n} (φ : M ⟶ N) (ψ : N ⟶ P) (q : ℕ) :
    cechHgrMap (φ ≫ ψ) q = cechHgrMap φ q ≫ cechHgrMap ψ q := by
  refine hom_ext fun d => ?_
  show HomologicalComplex.homologyMap (cechComplexMap (φ ≫ ψ) d) q = _
  rw [cechComplexMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-! ## The long exact sequence of Čech cohomology -/

variable {M} in
/-- The short complex of Čech complexes attached to a short exact sequence of graded
modules. -/
noncomputable def cechShortComplex {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (d : ℤ) :
    CategoryTheory.ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  CategoryTheory.ShortComplex.mk (cechComplexMap φ d) (cechComplexMap ψ d) (by
    ext p : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    show ((locMap τ.toList ψ).app d).hom
      (((locMap τ.toList φ).app d).hom (c τ)) = 0
    have hmem : ((locMap τ.toList φ).app d).hom (c τ) ∈
        LinearMap.range ((locMap τ.toList φ).app d).hom := ⟨c τ, rfl⟩
    rw [(loc_shortExact M (l := τ.toList) h).exact d] at hmem
    exact hmem)

variable {M} in
/-- The short complex of Čech complexes of a short exact sequence is short exact. -/
theorem cechShortComplex_shortExact {N P : GradedModule k n} {φ : M ⟶ N}
    {ψ : N ⟶ P} (h : ShortExact φ ψ) (d : ℤ) :
    (cechShortComplex h d).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro p
  obtain ⟨hinj, hexact, hsurj⟩ := cech_shortExact h p d
  exact
    { exact := by
        rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
        exact hexact
      mono_f := (ModuleCat.mono_iff_injective _).mpr hinj
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hsurj }

variable {M} in
/-- The connecting homomorphism of the Čech long exact sequence. -/
noncomputable def cechδ {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (q : ℕ) (d : ℤ) :
    (P.cechHgr q).obj d ⟶ (M.cechHgr (q + 1)).obj d :=
  (cechShortComplex_shortExact h d).δ q (q + 1) rfl

variable {M} in
/-- Exactness of Čech cohomology at the middle spot. -/
theorem cech_exact_map_map {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (q : ℕ) (d : ℤ) :
    Function.Exact ((cechHgrMap φ q).app d).hom ((cechHgrMap ψ q).app d).hom := by
  have h2 := (cechShortComplex_shortExact h d).homology_exact₂ q
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    at h2
  exact h2

variable {M} in
/-- Exactness of Čech cohomology at the third spot: map then connecting. -/
theorem cech_exact_map_δ {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (q : ℕ) (d : ℤ) :
    Function.Exact ((cechHgrMap ψ q).app d).hom (cechδ h q d).hom := by
  have h3 := (cechShortComplex_shortExact h d).homology_exact₃ q (q + 1) rfl
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    at h3
  exact h3

variable {M} in
/-- Exactness of Čech cohomology at the first spot: connecting then map. -/
theorem cech_exact_δ_map {N P : GradedModule k n} {φ : M ⟶ N} {ψ : N ⟶ P}
    (h : ShortExact φ ψ) (q : ℕ) (d : ℤ) :
    Function.Exact (cechδ h q d).hom ((cechHgrMap φ (q + 1)).app d).hom := by
  have h1 := (cechShortComplex_shortExact h d).homology_exact₁ q (q + 1) rfl
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    at h1
  exact h1

/-! ## Grothendieck vanishing -/

/-- There are no strictly increasing `(p+1)`-tuples in `Fin (n+1)` once `p > n`. -/
lemma cechIdx_isEmpty {p : ℕ} (hnp : n < p) : IsEmpty (CechIdx n p) := by
  constructor
  intro τ
  have hnodup : τ.toList.Nodup := τ.sorted.nodup
  have hle := hnodup.length_le_card
  rw [τ.length_eq, Fintype.card_fin] at hle
  omega

/-- The Čech cochains vanish above the dimension. -/
lemma isZero_cechCochain {p : ℕ} (hnp : n < p) (d : ℤ) :
    Limits.IsZero (M.cechCochain p d) := by
  haveI := cechIdx_isEmpty (n := n) hnp
  haveI : Unique (∀ τ : CechIdx n p, ((M.loc τ.toList).obj d)) :=
    Pi.uniqueOfIsEmpty _
  haveI : Subsingleton ↑(M.cechCochain p d) :=
    inferInstanceAs (Subsingleton (∀ τ : CechIdx n p, ((M.loc τ.toList).obj d)))
  exact ModuleCat.isZero_of_subsingleton _

/-- Grothendieck vanishing: the Čech cohomology vanishes above the dimension. -/
lemma isZero_cechHgr (q : ℕ) (hq : n < q) (d : ℤ) :
    Limits.IsZero ((M.cechHgr q).obj d) :=
  CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂
    ((M.cechComplex d).sc q) (isZero_cechCochain M hq d)

/-- Grothendieck vanishing, in the subsingleton form used by the cohomology
interface. -/
lemma subsingleton_cechHgr (q : ℕ) (hq : n < q) (d : ℤ) :
    Subsingleton ((M.cechHgr q).obj d) := by
  have h1 := isZero_cechHgr M q hq d
  rw [ModuleCat.isZero_iff_subsingleton] at h1
  exact h1

/-- A graded module vanishing in all large degrees has vanishing localizations at any
nonempty set of variables: every element is killed after enough multiplications. -/
lemma subsingleton_loc_of_eventually_zero (l : List (Fin (n + 1))) (hl : l ≠ [])
    (h : ∃ d₀ : ℤ, ∀ e : ℤ, d₀ ≤ e → Subsingleton (M.obj e)) (d : ℤ) :
    Subsingleton ((M.loc l).obj d) := by
  obtain ⟨d₀, hd₀⟩ := h
  have hlen : 1 ≤ (l.length : ℤ) := by
    have : l.length ≠ 0 := fun hc => hl (List.eq_nil_of_length_eq_zero hc)
    omega
  have hall : ∀ y : (M.loc l).obj d, y = 0 := by
    intro y
    obtain ⟨j, x, rfl⟩ := M.locIncl_exists l d y
    obtain ⟨j', hjj', hbig⟩ : ∃ j' : ℕ, j ≤ j' ∧ d₀ ≤ locDeg l d j' := by
      refine ⟨max j (d₀ - d).toNat, le_max_left _ _, ?_⟩
      have h1 : (d₀ - d).toNat ≤ max j (d₀ - d).toNat := le_max_right _ _
      have h2 : (d₀ - d) ≤ ((max j (d₀ - d).toNat : ℕ) : ℤ) := by
        have h3 : (d₀ - d) ≤ ((d₀ - d).toNat : ℤ) := Int.self_le_toNat _
        have h4 : (((d₀ - d).toNat : ℕ) : ℤ) ≤ ((max j (d₀ - d).toNat : ℕ) : ℤ) := by
          exact_mod_cast h1
        omega
      have h5 : ((max j (d₀ - d).toNat : ℕ) : ℤ) * 1
          ≤ ((max j (d₀ - d).toNat : ℕ) : ℤ) * (l.length : ℤ) :=
        mul_le_mul_of_nonneg_left hlen (Int.natCast_nonneg _)
      rw [locDeg_def]
      omega
    have hsub := hd₀ _ hbig
    have hzero : (M.locTr l d j j' hjj').hom x = 0 := Subsingleton.elim _ _
    have hfac := congrArg ModuleCat.Hom.hom (M.locTr_locIncl l d j j' hjj')
    rw [ModuleCat.hom_comp] at hfac
    have := LinearMap.congr_fun hfac x
    simp only [LinearMap.comp_apply] at this
    rw [← this, hzero, map_zero]
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- The Čech cochains of a graded module vanishing in all large degrees are zero. -/
lemma subsingleton_cechCochain_of_eventually_zero
    (h : ∃ d₀ : ℤ, ∀ e : ℤ, d₀ ≤ e → Subsingleton (M.obj e)) (p : ℕ) (d : ℤ) :
    Subsingleton (M.cechCochain p d) := by
  have hτ : ∀ τ : CechIdx n p, Subsingleton ((M.loc τ.toList).obj d) := fun τ =>
    subsingleton_loc_of_eventually_zero M τ.toList
      (fun hc => by simpa [hc] using τ.length_eq) h d
  exact inferInstanceAs (Subsingleton (∀ τ : CechIdx n p, ((M.loc τ.toList).obj d)))

/-- **A graded module vanishing in all large degrees has no cohomology.**  Such a module has
finite length, so its associated sheaf is zero; this is what makes a comparison map with
finite-length kernel and cokernel an isomorphism on cohomology. -/
theorem subsingleton_cechHgr_of_eventually_zero
    (h : ∃ d₀ : ℤ, ∀ e : ℤ, d₀ ≤ e → Subsingleton (M.obj e)) (i : ℕ) (d : ℤ) :
    Subsingleton ((M.cechHgr i).obj d) := by
  haveI := subsingleton_cechCochain_of_eventually_zero M h i d
  have hz0 : Limits.IsZero (M.cechCochain i d) := ModuleCat.isZero_of_subsingleton _
  have hz : Limits.IsZero ((M.cechHgr i).obj d) :=
    CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂ ((M.cechComplex d).sc i) hz0
  rw [ModuleCat.isZero_iff_subsingleton] at hz
  exact hz

variable {M} in
/-- Localization of a degreewise injective morphism is injective. -/
lemma locMap_injective {N : GradedModule k n} {φ : M ⟶ N}
    (hinj : ∀ e, Function.Injective (φ.app e).hom)
    (l : List (Fin (n + 1))) (d : ℤ) :
    Function.Injective ((locMap l φ).app d).hom := by
  intro a b hab
  have h0 := locMap_eq_zero_of_injective (l := l) hinj (a - b)
    (by rw [map_sub, hab, sub_self])
  exact sub_eq_zero.mp h0

variable {M} in
/-- `H⁰` is left exact: the zeroth Čech cohomology of a degreewise injection
injects. -/
theorem cech_injective_map_zero {N : GradedModule k n} {φ : M ⟶ N}
    (hinj : ∀ e, Function.Injective (φ.app e).hom) (d : ℤ) :
    Function.Injective ((cechHgrMap φ 0).app d).hom := by
  haveI : Mono ((cechComplexMap φ d).f 0) := by
    rw [ModuleCat.mono_iff_injective]
    intro c₁ c₂ hc
    funext τ
    exact locMap_injective hinj τ.toList d (congrFun hc τ)
  have hm := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (cechComplexMap φ d) 0 (fun i => by simp)
  exact (ModuleCat.mono_iff_injective
    (HomologicalComplex.homologyMap (cechComplexMap φ d) 0)).mp hm

/-! ## Multiplication by a linear form -/

section MulL

/-- Sum of homology maps of a finite family of chain maps. -/
lemma homologyMap_sum {K L : CochainComplex (ModuleCat.{u} k) ℕ}
    {ι : Type} (s : Finset ι) (f : ι → (K ⟶ L)) (q : ℕ) :
    HomologicalComplex.homologyMap (∑ ρ ∈ s, f ρ) q =
      ∑ ρ ∈ s, HomologicalComplex.homologyMap (f ρ) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HomologicalComplex.homologyMap_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        HomologicalComplex.homologyMap_add, ih]

/-- Homology maps are `k`-linear.  Mathlib records this only for `ShortComplex`
(`Algebra/Homology/Linear.lean` lists the complex-level version as future work). -/
lemma homologyMap_smul {K L : CochainComplex (ModuleCat.{u} k) ℕ} (a : k)
    (f : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap (a • f) q =
      a • HomologicalComplex.homologyMap f q := by
  have hmap : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k)
      (ComplexShape.up ℕ) q).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k)
        (ComplexShape.up ℕ) q).map f := by
    ext <;> rfl
  show CategoryTheory.ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k)
        (ComplexShape.up ℕ) q).map (a • f)) = _
  rw [hmap, CategoryTheory.ShortComplex.homologyMap_smul]
  rfl

/-- Multiplication by a variable on the Čech complex, in transported degrees. -/
noncomputable def cechMulX' (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e) :
    M.cechComplex d ⟶ M.cechComplex e :=
  M.cechMulX i d ≫ eqToHom (congrArg M.cechComplex h)

/-- Multiplication by a variable induces multiplication on Čech cohomology. -/
lemma homologyMap_cechMulX' (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e)
    (q : ℕ) :
    HomologicalComplex.homologyMap (M.cechMulX' i d e h) q =
      (M.cechHgr q).mulX' i d e h := by
  subst h
  rw [cechMulX', mulX']
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- Multiplication by a linear form on the Čech complex. -/
noncomputable def cechMulL (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e) :
    M.cechComplex d ⟶ M.cechComplex e :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom
      { toFun := fun z τ => ((M.loc τ.toList).mulL c d e h).hom (z τ)
        map_add' := fun z₁ z₂ => by
          funext τ
          simp only [Pi.add_apply, map_add]
        map_smul' := fun a z => by
          funext τ
          simp only [Pi.smul_apply, map_smul, RingHom.id_apply] })
    (fun p => by
      simp only [cechComplex, CochainComplex.of_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun z => funext fun τ => ?_)
      show (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((M.cechFaceMap τ i).app e).hom
            (((M.loc (τ.face i).toList).mulL c d e h).hom (z (τ.face i)))) =
        ((M.loc τ.toList).mulL c d e h).hom
          (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
            ((M.cechFaceMap τ i).app d).hom (z (τ.face i)))
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul]
      congr 1
      have h1 := congrArg ModuleCat.Hom.hom
        (comm_mulL (M.cechFaceMap τ i) c d e h)
      simp only [ModuleCat.hom_comp] at h1
      exact (LinearMap.congr_fun h1 (z (τ.face i))).symm)

/-- Multiplication by a linear form decomposes into the coordinate
multiplications. -/
lemma cechMulL_eq_sum (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e) :
    M.cechMulL c d e h = ∑ i : Fin (n + 1), c i • M.cechMulX' i d e h := by
  ext p : 1
  rw [show (∑ i : Fin (n + 1), c i • M.cechMulX' i d e h).f p =
      ∑ i : Fin (n + 1), (c i • M.cechMulX' i d e h).f p from
    (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℕ) p).map_sum
      _ _]
  refine ModuleCat.hom_ext (LinearMap.ext fun z => funext fun τ => ?_)
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  show ((M.loc τ.toList).mulL c d e h).hom (z τ) =
    (∑ i : Fin (n + 1), ((c i • M.cechMulX' i d e h).f p).hom z) τ
  rw [Finset.sum_apply]
  show ((M.loc τ.toList).mulL c d e h).hom (z τ) =
    ∑ i : Fin (n + 1), c i • (((M.cechMulX' i d e h).f p).hom z) τ
  subst h
  simp only [cechMulX', eqToHom_refl, Category.comp_id, mulL,
    ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  congr 1

/-- Multiplication by a linear form induces multiplication on Čech
cohomology. -/
lemma homologyMap_cechMulL (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e)
    (q : ℕ) :
    HomologicalComplex.homologyMap (M.cechMulL c d e h) q =
      (M.cechHgr q).mulL c d e h := by
  rw [cechMulL_eq_sum, homologyMap_sum, mulL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [homologyMap_smul, homologyMap_cechMulX']

end MulL

/-! ## The twist comparison -/

section Twist

variable (a : ℤ)

/-- Degreewise cochain comparison between the Čech cochains of a twist and the
shifted Čech cochains. -/
noncomputable def cechCochainTwistIso (p : ℕ) (d : ℤ) :
    (M.twist a).cechCochain p d ≅ M.cechCochain p (d + a) where
  hom := ModuleCat.ofHom
    { toFun := fun c τ => (twistLocToLoc M τ.toList a d).hom (c τ)
      map_add' := fun c₁ c₂ => by
        funext τ
        simp only [Pi.add_apply, map_add]
      map_smul' := fun r c => by
        funext τ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }
  inv := ModuleCat.ofHom
    { toFun := fun c τ => (locToTwistLoc M τ.toList a d).hom (c τ)
      map_add' := fun c₁ c₂ => by
        funext τ
        simp only [Pi.add_apply, map_add]
      map_smul' := fun r c => by
        funext τ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }
  hom_inv_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    show (locToTwistLoc M τ.toList a d).hom
      ((twistLocToLoc M τ.toList a d).hom (c τ)) = c τ
    have h1 := congrArg ModuleCat.Hom.hom (twistLocIso M τ.toList a d).hom_inv_id
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 (c τ)
  inv_hom_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    show (twistLocToLoc M τ.toList a d).hom
      ((locToTwistLoc M τ.toList a d).hom (c τ)) = c τ
    have h1 := congrArg ModuleCat.Hom.hom (twistLocIso M τ.toList a d).inv_hom_id
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 (c τ)

/-- The cochain twist comparison commutes with the Čech differential. -/
lemma cechCochainTwistIso_cechD (p : ℕ) (d : ℤ) :
    (cechCochainTwistIso M a p d).hom ≫ M.cechD p (d + a) =
      (M.twist a).cechD p d ≫ (cechCochainTwistIso M a (p + 1) d).hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      ((M.cechFaceMap τ i).app (d + a)).hom
        ((twistLocToLoc M (τ.face i).toList a d).hom (c (τ.face i)))) =
    (twistLocToLoc M τ.toList a d).hom
      (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (((M.twist a).cechFaceMap τ i).app d).hom (c (τ.face i)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  have h1 := congrArg ModuleCat.Hom.hom
    (twistLocToLoc_locResApp M (τ.face i).toList a (τ.perm_face_append i) d)
  simp only [ModuleCat.hom_comp] at h1
  exact (LinearMap.congr_fun h1 (c (τ.face i))).symm

/-- The Čech complex of a twist is the shifted Čech complex. -/
noncomputable def cechComplexTwistIso (d : ℤ) :
    (M.twist a).cechComplex d ≅ M.cechComplex (d + a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => cechCochainTwistIso M a p d)
    (fun p q hpq => by
      obtain rfl : q = p + 1 := hpq.symm
      simpa only [cechComplex, CochainComplex.of_d] using
        cechCochainTwistIso_cechD M a p d)

/-- Graded Čech cohomology takes twists to shifts: the `twistIso` field of the
cohomology interface. -/
noncomputable def cechHgrTwistIso (q : ℕ) (d : ℤ) :
    ((M.twist a).cechHgr q).obj d ≅ (M.cechHgr q).obj (d + a) :=
  HomologicalComplex.homologyMapIso (cechComplexTwistIso M a d) q

end Twist

/-! ## The twist–linear-form compatibility -/

section MulLHom

variable (c : Fin (n + 1) → k)

/-- The twist comparison turns the Čech map of the linear-form multiplication into
multiplication by that linear form: the complex-level `map_mulLHom`. -/
lemma cechComplexTwistIso_inv_cechComplexMap_mulLHom (d : ℤ) :
    (cechComplexTwistIso M (-1) d).inv ≫
        cechComplexMap (M.mulLHom c) d =
      M.cechMulL c (d + -1) d (by ring) := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun z => funext fun τ => ?_)
  show ((locMap τ.toList (M.mulLHom c)).app d).hom
      ((locToTwistLoc M τ.toList (-1) d).hom (z τ)) =
    ((M.loc τ.toList).mulL c (d + -1) d (by ring)).hom (z τ)
  have h1 := congrArg ModuleCat.Hom.hom
    (twistLocIso_inv_locMap_mulLHom M τ.toList c d)
  simp only [ModuleCat.hom_comp] at h1
  exact LinearMap.congr_fun h1 (z τ)

/-- **The `map_mulLHom` field**: on Čech cohomology, the twist comparison composed
with the induced map of multiplication by a linear form is multiplication by that
linear form. -/
theorem cechHgr_map_mulLHom (q : ℕ) (d : ℤ) :
    (cechHgrTwistIso M (-1) q d).inv ≫
        (cechHgrMap (M.mulLHom c) q).app d =
      (M.cechHgr q).mulL c (d + -1) d (by ring) := by
  show HomologicalComplex.homologyMap (cechComplexTwistIso M (-1) d).inv q ≫
      HomologicalComplex.homologyMap
        (cechComplexMap (M.mulLHom c) d) q = _
  rw [← HomologicalComplex.homologyMap_comp,
    cechComplexTwistIso_inv_cechComplexMap_mulLHom,
    homologyMap_cechMulL]

end MulLHom

/-! ## The base case of projective zero-space: multiplication is invertible -/

section ZeroSpace

/-- Every Čech index over `ℙ⁰` contains the unique variable. -/
lemma CechIdx.zero_mem {p : ℕ} (τ : CechIdx 0 p) (i : Fin 1) :
    i ∈ τ.toList := by
  have hne : τ.toList ≠ [] := by
    intro h0
    have := τ.length_eq
    rw [h0] at this
    simp at this
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  have : i = a := Subsingleton.elim i a
  rw [this]
  exact ha

variable (M : GradedModule k 0)

/-- Over `ℙ⁰`, multiplication is invertible on every Čech cochain module. -/
lemma zero_cechMulX_component_isIso (i : Fin 1) (p : ℕ) (d : ℤ) :
    IsIso ((M.cechMulX i d).f p) := by
  refine ⟨ModuleCat.ofHom
    { toFun := fun c τ =>
        (haveI := M.loc_mulX_isIso τ.toList i (τ.zero_mem i) d
         inv ((M.loc τ.toList).mulX i d)).hom (c τ)
      map_add' := fun c₁ c₂ => by
        funext τ
        simp only [Pi.add_apply, map_add]
      map_smul' := fun r c => by
        funext τ
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }, ?_, ?_⟩
  · refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    haveI := M.loc_mulX_isIso τ.toList i (τ.zero_mem i) d
    show (inv ((M.loc τ.toList).mulX i d)).hom
      (((M.loc τ.toList).mulX i d).hom (c τ)) = c τ
    have h1 := congrArg ModuleCat.Hom.hom
      (IsIso.hom_inv_id ((M.loc τ.toList).mulX i d))
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 (c τ)
  · refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
    haveI := M.loc_mulX_isIso τ.toList i (τ.zero_mem i) d
    show ((M.loc τ.toList).mulX i d).hom
      ((inv ((M.loc τ.toList).mulX i d)).hom (c τ)) = c τ
    have h1 := congrArg ModuleCat.Hom.hom
      (IsIso.inv_hom_id ((M.loc τ.toList).mulX i d))
    simp only [ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 (c τ)

/-- Over `ℙ⁰`, the multiplication chain map is an isomorphism. -/
lemma zero_cechMulX_isIso (i : Fin 1) (d : ℤ) :
    IsIso (M.cechMulX i d) := by
  haveI : ∀ p, IsIso ((M.cechMulX i d).f p) :=
    fun p => zero_cechMulX_component_isIso M i p d
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Over `ℙ⁰`, multiplication is invertible on Čech cohomology. -/
lemma zero_cechHgr_mulX_isIso (i : Fin 1) (q : ℕ) (d : ℤ) :
    IsIso ((M.cechHgr q).mulX i d) := by
  haveI := zero_cechMulX_isIso M i d
  show IsIso (HomologicalComplex.homologyMap (M.cechMulX i d) q)
  rw [show HomologicalComplex.homologyMap (M.cechMulX i d) q =
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k)
      (ComplexShape.up ℕ) q).map (M.cechMulX i d) from rfl]
  infer_instance

/-- Over `ℙ⁰`, every iterated multiplication is invertible on Čech cohomology. -/
lemma zero_cechHgr_mulList_isIso (q : ℕ) (L : List (Fin 1)) (d e : ℤ)
    (h : d + (L.length : ℤ) = e) :
    IsIso ((M.cechHgr q).mulList L d e h) := by
  induction L generalizing d e with
  | nil =>
      have hde : d = e := by simpa using h
      subst hde
      simp only [mulList]
      infer_instance
  | cons a t ih =>
      simp only [mulList]
      haveI := zero_cechHgr_mulX_isIso M a q d
      haveI := ih (d + 1) e (by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega)
      exact IsIso.comp_isIso

/-- Over `ℙ⁰`, the multiplication maps span everything: the `mulSpan_zero` field of
the cohomology interface. -/
theorem zero_cechHgr_mulSpan (d e : ℤ) (hde : d ≤ e) :
    (M.cechHgr 0).mulSpan d e = ⊤ := by
  set L : List (Fin 1) := List.replicate (e - d).toNat 0 with hL
  have hlen : d + (L.length : ℤ) = e := by
    rw [hL, List.length_replicate]
    omega
  refine top_unique ?_
  refine le_trans ?_ (le_mulSpan (M.cechHgr 0) d e L hlen)
  haveI := zero_cechHgr_mulList_isIso M 0 L d e hlen
  intro x _
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((M.cechHgr 0).mulList L d e hlen)).mp inferInstance x
  exact ⟨y, hy⟩

end ZeroSpace

/-! ## The augmentation into `H⁰` -/

section Augmentation

/-- The augmentation of the Čech complex: a section of `M` in degree `d` gives the
constant `0`-cochain, one localization map for each variable. -/
noncomputable def cechAug₀ (d : ℤ) : M.obj d ⟶ M.cechCochain 0 d :=
  ModuleCat.ofHom
    { toFun := fun x τ => ((M.locOf τ.toList).app d).hom x
      map_add' := fun x y => by
        funext τ
        simp only [map_add]
        rfl
      map_smul' := fun a x => by
        funext τ
        simp only [map_smul, RingHom.id_apply]
        rfl }

/-- The augmentation is a cocycle: localizing a global section gives compatible
localizations. -/
lemma cechAug₀_comp_cechD (d : ℤ) :
    M.cechAug₀ d ≫ M.cechD 0 d = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun τ => ?_)
  show (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) •
      ((M.cechFaceMap τ i).app d).hom
        (((M.locOf (τ.face i).toList).app d).hom x)) = 0
  have hterm : ∀ i : Fin 2,
      ((M.cechFaceMap τ i).app d).hom
        (((M.locOf (τ.face i).toList).app d).hom x) =
      ((M.locOf τ.toList).app d).hom x := by
    intro i
    have h1 := congrArg (fun (t : M ⟶ M.loc τ.toList) => (t.app d).hom)
      (locOf_locRes M (τ.face i).toList (τ.perm_face_append i))
    simp only [comp_app, ModuleCat.hom_comp] at h1
    exact LinearMap.congr_fun h1 x
  rw [Finset.sum_congr rfl
    (fun (i : Fin 2) _ => congrArg (fun t => ((-1 : ℤ) ^ (i : ℕ)) • t) (hterm i)),
    ← Finset.sum_smul]
  have hsigns : (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ))) = 0 := by decide
  rw [hsigns, zero_smul]

/-- The differential of the Čech complex, read off the `CochainComplex.of`
construction. -/
lemma cechComplex_d_zero_one (d : ℤ) :
    (M.cechComplex d).d 0 1 = M.cechD 0 d := by
  exact CochainComplex.of_d (fun p => M.cechCochain p d) (fun p => M.cechD p d) 0

/-- The augmentation `M_d ⟶ H⁰(ℙⁿ, M~(d))`. -/
noncomputable def cechAug (d : ℤ) : M.obj d ⟶ (M.cechHgr 0).obj d :=
  (M.cechComplex d).liftCycles (M.cechAug₀ d) 1 (by simp)
      (by
        rw [M.cechComplex_d_zero_one d]
        exact M.cechAug₀_comp_cechD d) ≫
    (M.cechComplex d).homologyπ 0

/-- Every Čech index is nonempty, so a `0`-cochain has at least one component. -/
noncomputable def CechIdx.zeroIdx (i : Fin (n + 1)) : CechIdx n 0 where
  toList := [i]
  sorted := by simp
  length_eq := rfl

/-- On a torsion-free module the augmentation into the `0`-cochains is injective. -/
lemma injective_cechAug₀ (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom)) (d : ℤ) :
    Function.Injective ((M.cechAug₀ d).hom) := by
  intro x y hxy
  have hcomp := congrFun hxy (CechIdx.zeroIdx (n := n) 0)
  exact injective_locOf M hinj _ d hcomp

/-- **The augmentation into `H⁰` is injective on a torsion-free module.**  A global
section that dies in every `D₊(xᵢ)` is zero. -/
theorem injective_cechAug (hinj : ∀ (i : Fin (n + 1)) (d : ℤ),
      Function.Injective ((M.mulX i d).hom)) (d : ℤ) :
    Function.Injective ((M.cechAug d).hom) := by
  haveI : IsIso ((M.cechComplex d).homologyπ 0) :=
    CochainComplex.isIso_homologyπ₀ (M.cechComplex d)
  have hfac : M.cechAug d ≫ (inv ((M.cechComplex d).homologyπ 0) ≫
      (M.cechComplex d).iCycles 0) = M.cechAug₀ d := by
    rw [cechAug, Category.assoc,
      ← Category.assoc ((M.cechComplex d).homologyπ 0),
      IsIso.hom_inv_id, Category.id_comp]
    exact HomologicalComplex.liftCycles_i _ _ _ _ _
  have h1 := congrArg ModuleCat.Hom.hom hfac
  simp only [ModuleCat.hom_comp] at h1
  intro x y hxy
  refine injective_cechAug₀ M hinj d ?_
  have hx := LinearMap.congr_fun h1 x
  have hy := LinearMap.congr_fun h1 y
  simp only [LinearMap.comp_apply] at hx hy
  exact hx.symm.trans ((congrArg
    (fun w => ((M.cechComplex d).iCycles 0).hom
      ((inv ((M.cechComplex d).homologyπ 0)).hom w)) hxy).trans hy)

/-- **Surjectivity of the augmentation is a statement about cochains.**  If every
`0`-cocycle of the Čech complex is the augmentation of a section, then the augmentation
onto `H⁰` is surjective.  This removes homology entirely from the remaining half of the
`H⁰`-identification. -/
theorem surjective_cechAug_of_cocycles (d : ℤ)
    (h : ∀ c : M.cechCochain 0 d, (M.cechD 0 d).hom c = 0 →
      ∃ x : M.obj d, (M.cechAug₀ d).hom x = c) :
    Function.Surjective ((M.cechAug d).hom) := by
  haveI : IsIso ((M.cechComplex d).homologyπ 0) :=
    CochainComplex.isIso_homologyπ₀ (M.cechComplex d)
  intro z
  set w := (inv ((M.cechComplex d).homologyπ 0)).hom z with hw
  -- the underlying cochain of `w` is a cocycle
  have hid := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.iCycles_d (M.cechComplex d) 0 1)
  rw [ModuleCat.hom_comp, M.cechComplex_d_zero_one d, ModuleCat.hom_zero] at hid
  have hcoc : (M.cechD 0 d).hom (((M.cechComplex d).iCycles 0).hom w) = 0 :=
    LinearMap.congr_fun hid w
  obtain ⟨x, hx⟩ := h _ hcoc
  refine ⟨x, ?_⟩
  -- the lift of `x` agrees with `w`, because `iCycles` is monic
  have hfac := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.liftCycles_i (M.cechComplex d) (M.cechAug₀ d) 1 (by simp)
      (by rw [M.cechComplex_d_zero_one d]; exact M.cechAug₀_comp_cechD d))
  rw [ModuleCat.hom_comp] at hfac
  have hmono : Function.Injective (((M.cechComplex d).iCycles 0).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hlift : ((M.cechComplex d).liftCycles (M.cechAug₀ d) 1 (by simp)
      (by rw [M.cechComplex_d_zero_one d]; exact M.cechAug₀_comp_cechD d)).hom x = w := by
    refine hmono ?_
    have hthis := LinearMap.congr_fun hfac x
    simp only [LinearMap.comp_apply] at hthis
    rw [hthis]
    exact hx
  show ((M.cechComplex d).homologyπ 0).hom
    (((M.cechComplex d).liftCycles (M.cechAug₀ d) 1 _ _).hom x) = z
  rw [hlift, hw]
  have hinv := congrArg ModuleCat.Hom.hom
    (IsIso.inv_hom_id ((M.cechComplex d).homologyπ 0))
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hinv
  exact LinearMap.congr_fun hinv z

/-- **Injectivity of the augmentation into `H⁰` follows from injectivity into the
`0`-cochains**, with no hypothesis on `M` and no torsion-freeness.

This is the variant needed for `Γ_*` of an arbitrary quasicoherent sheaf, whose
`mulX` maps need not be injective: a sheaf supported on a hyperplane `xᵢ = 0` has
`xᵢ`-torsion global sections, so `injective_cechAug` does not apply, while the
components of `cechAug₀` are the restrictions to the standard charts and the sheaf
axiom makes them jointly injective. -/
theorem injective_cechAug_of_aug₀ (d : ℤ)
    (h0 : Function.Injective ((M.cechAug₀ d).hom)) :
    Function.Injective ((M.cechAug d).hom) := by
  haveI : IsIso ((M.cechComplex d).homologyπ 0) :=
    CochainComplex.isIso_homologyπ₀ (M.cechComplex d)
  have hfac : M.cechAug d ≫ (inv ((M.cechComplex d).homologyπ 0) ≫
      (M.cechComplex d).iCycles 0) = M.cechAug₀ d := by
    rw [cechAug, Category.assoc,
      ← Category.assoc ((M.cechComplex d).homologyπ 0),
      IsIso.hom_inv_id, Category.id_comp]
    exact HomologicalComplex.liftCycles_i _ _ _ _ _
  have h1 := congrArg ModuleCat.Hom.hom hfac
  simp only [ModuleCat.hom_comp] at h1
  intro x y hxy
  refine h0 ?_
  have hx := LinearMap.congr_fun h1 x
  have hy := LinearMap.congr_fun h1 y
  simp only [LinearMap.comp_apply] at hx hy
  exact hx.symm.trans ((congrArg
    (fun w => ((M.cechComplex d).iCycles 0).hom
      ((inv ((M.cechComplex d).homologyπ 0)).hom w)) hxy).trans hy)

end Augmentation

/-! ## Finite direct sums -/

section Pow

variable (r : ℕ)

/-- Coordinate inclusion into the finite direct sum of a graded module. -/
def powCoord (ρ : Fin r) : M ⟶ M.pow r where
  app d := ModuleCat.ofHom
    (LinearMap.single k (fun _ : Fin r => M.obj d) ρ)
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun σ => ?_)
    show (((M.pow r).mulX i d).hom
        (Pi.single (M := fun _ : Fin r => M.obj d) ρ x)) σ =
      Pi.single (M := fun _ : Fin r => M.obj (d + 1)) ρ
        ((M.mulX i d).hom x) σ
    have hcomp : (((M.pow r).mulX i d).hom
        (Pi.single (M := fun _ : Fin r => M.obj d) ρ x)) σ =
        (M.mulX i d).hom
          (Pi.single (M := fun _ : Fin r => M.obj d) ρ x σ) := rfl
    rw [hcomp]
    by_cases hσ : σ = ρ
    · subst hσ
      simp
    · rw [Pi.single_eq_of_ne hσ, Pi.single_eq_of_ne hσ, map_zero]

/-- Coordinate projection out of the finite direct sum. -/
def powProj (ρ : Fin r) : M.pow r ⟶ M where
  app d := ModuleCat.ofHom
    (LinearMap.proj (R := k) (φ := fun _ : Fin r => M.obj d) ρ)
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

/-- The composite of a coordinate inclusion with the same projection is the
identity. -/
lemma powCoord_powProj (ρ : Fin r) :
    powCoord M r ρ ≫ powProj M r ρ = 𝟙 M := by
  refine hom_ext fun d => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show Pi.single (M := fun _ : Fin r => M.obj d) ρ x ρ = x
  simp

/-- The Čech chain map of a mismatched inclusion–projection composite vanishes. -/
lemma cechComplexMap_powCoord_powProj_ne {ρ σ : Fin r} (h : σ ≠ ρ) (d : ℤ) :
    cechComplexMap (powCoord M r σ ≫ powProj M r ρ) d = 0 := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  show ((locMap τ.toList (powCoord M r σ ≫ powProj M r ρ)).app d).hom (c τ) =
    ((0 : M.cechCochain p d ⟶ M.cechCochain p d)).hom c τ
  obtain ⟨j, x, hx⟩ := M.locIncl_exists τ.toList d (c τ)
  rw [← hx, locMap_locIncl_apply]
  have hzero : ((powCoord M r σ ≫ powProj M r ρ).app
      (locDeg τ.toList d j)).hom x = 0 := by
    show Pi.single (M := fun _ : Fin r => M.obj (locDeg τ.toList d j)) σ x ρ = 0
    exact Pi.single_eq_of_ne (M := fun _ : Fin r => M.obj (locDeg τ.toList d j))
      (Ne.symm h) x
  rw [hzero, map_zero]
  rfl

/-- The coordinate composites of the Čech complexes sum to the identity. -/
lemma sum_cechComplexMap_powProj_powCoord (d : ℤ) :
    (∑ ρ : Fin r, cechComplexMap (powProj M r ρ) d ≫
        cechComplexMap (powCoord M r ρ) d) =
      𝟙 ((M.pow r).cechComplex d) := by
  ext p : 1
  rw [show (∑ ρ : Fin r, cechComplexMap (powProj M r ρ) d ≫
        cechComplexMap (powCoord M r ρ) d).f p =
      ∑ ρ : Fin r, (cechComplexMap (powProj M r ρ) d ≫
        cechComplexMap (powCoord M r ρ) d).f p from
    (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℕ) p).map_sum
      _ _]
  refine ModuleCat.hom_ext (LinearMap.ext fun c => funext fun τ => ?_)
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  obtain ⟨j, x, hx⟩ := (M.pow r).locIncl_exists τ.toList d (c τ)
  have hterm : ∀ ρ : Fin r,
      (((cechComplexMap (powProj M r ρ) d ≫
        cechComplexMap (powCoord M r ρ) d).f p).hom c) τ =
      ((M.pow r).locIncl τ.toList d j).hom
        (Pi.single (M := fun _ : Fin r => M.obj (locDeg τ.toList d j))
          ρ (x ρ)) := by
    intro ρ
    show ((locMap τ.toList (powCoord M r ρ)).app d).hom
      (((locMap τ.toList (powProj M r ρ)).app d).hom (c τ)) = _
    rw [← hx, locMap_locIncl_apply, locMap_locIncl_apply]
    rfl
  show (∑ ρ : Fin r, (((cechComplexMap (powProj M r ρ) d ≫
      cechComplexMap (powCoord M r ρ) d).f p).hom c)) τ = c τ
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun ρ _ => hterm ρ), ← map_sum,
    ← hx]
  congr 1
  exact Finset.univ_sum_single x

/-- The diagonal coordinate composite is the identity on Čech cohomology. -/
lemma homologyMap_powCoord_powProj_self (σ : Fin r) (q : ℕ) (d : ℤ) :
    HomologicalComplex.homologyMap (cechComplexMap (powCoord M r σ) d) q ≫
        HomologicalComplex.homologyMap
          (cechComplexMap (powProj M r σ) d) q =
      𝟙 ((M.cechComplex d).homology q) := by
  rw [← HomologicalComplex.homologyMap_comp, ← cechComplexMap_comp,
    powCoord_powProj, cechComplexMap_id, HomologicalComplex.homologyMap_id]

/-- An off-diagonal coordinate composite vanishes on Čech cohomology. -/
lemma homologyMap_powCoord_powProj_ne {ρ σ : Fin r} (h : ρ ≠ σ) (q : ℕ)
    (d : ℤ) :
    HomologicalComplex.homologyMap (cechComplexMap (powCoord M r ρ) d) q ≫
        HomologicalComplex.homologyMap
          (cechComplexMap (powProj M r σ) d) q = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M r h d,
    HomologicalComplex.homologyMap_zero]

/-- Čech cohomology of a finite direct sum is the finite direct sum of the Čech
cohomologies: the `HgrPowIso` field of the cohomology interface. -/
noncomputable def cechHgrPowIso (q : ℕ) (d : ℤ) :
    ((M.pow r).cechHgr q).obj d ≅ (((M.cechHgr q).pow r).obj d) where
  hom := ModuleCat.ofHom (LinearMap.pi fun ρ =>
    (HomologicalComplex.homologyMap
      (cechComplexMap (powProj M r ρ) d) q).hom)
  inv := ModuleCat.ofHom (∑ ρ : Fin r,
    (HomologicalComplex.homologyMap
      (cechComplexMap (powCoord M r ρ) d) q).hom ∘ₗ
    LinearMap.proj (R := k)
      (φ := fun _ : Fin r => ((M.cechHgr q).obj d)) ρ)
  hom_inv_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    have hsum : (∑ ρ : Fin r,
        HomologicalComplex.homologyMap (cechComplexMap (powProj M r ρ) d) q ≫
          HomologicalComplex.homologyMap
            (cechComplexMap (powCoord M r ρ) d) q) =
        𝟙 (((M.pow r).cechComplex d).homology q) := by
      rw [Finset.sum_congr rfl (fun ρ _ =>
        (HomologicalComplex.homologyMap_comp
          (cechComplexMap (powProj M r ρ) d)
          (cechComplexMap (powCoord M r ρ) d) q).symm),
        ← homologyMap_sum, sum_cechComplexMap_powProj_powCoord,
        HomologicalComplex.homologyMap_id]
    have h1 := congrArg ModuleCat.Hom.hom hsum
    rw [ModuleCat.hom_sum] at h1
    have h2 := LinearMap.congr_fun h1 z
    rw [LinearMap.sum_apply, ModuleCat.hom_id, LinearMap.id_apply] at h2
    show (∑ ρ : Fin r,
        (HomologicalComplex.homologyMap
          (cechComplexMap (powCoord M r ρ) d) q).hom ∘ₗ
        LinearMap.proj (R := k)
          (φ := fun _ : Fin r => ((M.cechHgr q).obj d)) ρ)
        ((LinearMap.pi fun ρ =>
          (HomologicalComplex.homologyMap
            (cechComplexMap (powProj M r ρ) d) q).hom) z) = z
    rw [LinearMap.sum_apply]
    refine Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) h2
    rfl
  inv_hom_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun g => funext fun σ => ?_)
    show (HomologicalComplex.homologyMap
        (cechComplexMap (powProj M r σ) d) q).hom
        ((∑ ρ : Fin r,
          (HomologicalComplex.homologyMap
            (cechComplexMap (powCoord M r ρ) d) q).hom ∘ₗ
          LinearMap.proj (R := k)
            (φ := fun _ : Fin r => ((M.cechHgr q).obj d)) ρ) g) = g σ
    rw [LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single σ]
    · have hd := congrArg ModuleCat.Hom.hom
        (homologyMap_powCoord_powProj_self M r σ q d)
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hd
      exact LinearMap.congr_fun hd (g σ)
    · intro ρ _ hne
      have ho := congrArg ModuleCat.Hom.hom
        (homologyMap_powCoord_powProj_ne M r hne q d)
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at ho
      exact LinearMap.congr_fun ho (g ρ)
    · intro hσ
      exact absurd (Finset.mem_univ σ) hσ

end Pow

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
