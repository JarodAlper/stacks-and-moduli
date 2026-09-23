module

public import StacksAndModuli.API.ProjectiveGradedCech
public import StacksAndModuli.API.PolynomialCoprimeVariables

/-!
# `H⁰(ℙⁿ, 𝒪(d)) = S_d`

Supporting API with no Stacks Project counterpart.

The `0`-cocycles of the graded Čech complex of the structure module are exactly the
augmentations of global forms: a family `fᵢ/xᵢ^m` of degree `d` agreeing on the overlaps
comes from a unique `h ∈ S_d`.  This is Hartshorne III.5.1(a) in degrees `d ≥ 0`, and it
is the last field of `CechSerreData` concerning `H⁰`.

The argument: pick a common tower stage `m`; the cocycle condition on the pair `{a, b}`
says `x_a^m g_b = x_b^m g_a` in `S` (equality in the colimit upgrades to equality in `S`
because the stage inclusions are injective on a domain); the variables are pairwise
coprime primes, so `xᵢ^m ∣ gᵢ` (`MvPolynomial.X_pow_dvd_of_mul_eq_mul`, with the one
variable case handled by degree, `MvPolynomial.X_pow_dvd_of_isHomogeneous_subsingleton`);
the quotients are homogeneous (`MvPolynomial.IsHomogeneous.of_X_pow_mul`) and agree.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.CechIdx.pairIdx`;
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.structureModule_mulList_val`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ## Index bookkeeping -/

/-- A `0`-index is the singleton on its unique entry. -/
lemma CechIdx.eq_zeroIdx (τ : CechIdx n 0) : τ = CechIdx.zeroIdx (τ.elem 0) := by
  refine CechIdx.ext ?_
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp τ.length_eq
  have helem : τ.elem 0 = a := by
    show τ.toList[(0 : ℕ)]'_ = a
    simp only [ha]
    rfl
  rw [ha, helem]
  rfl

/-- The `1`-index attached to a strictly increasing pair. -/
def CechIdx.pairIdx (a b : Fin (n + 1)) (hab : a < b) : CechIdx n 1 where
  toList := [a, b]
  sorted := by simp [hab]
  length_eq := rfl

@[simp] lemma CechIdx.pairIdx_toList (a b : Fin (n + 1)) (hab : a < b) :
    (CechIdx.pairIdx a b hab).toList = [a, b] := rfl

@[simp] lemma CechIdx.pairIdx_face_zero (a b : Fin (n + 1)) (hab : a < b) :
    (CechIdx.pairIdx a b hab).face 0 = CechIdx.zeroIdx b := by
  refine CechIdx.ext ?_
  rfl

@[simp] lemma CechIdx.pairIdx_face_one (a b : Fin (n + 1)) (hab : a < b) :
    (CechIdx.pairIdx a b hab).face 1 = CechIdx.zeroIdx a := by
  refine CechIdx.ext ?_
  rfl

@[simp] lemma CechIdx.pairIdx_elem_zero (a b : Fin (n + 1)) (hab : a < b) :
    (CechIdx.pairIdx a b hab).elem 0 = a := rfl

@[simp] lemma CechIdx.pairIdx_elem_one (a b : Fin (n + 1)) (hab : a < b) :
    (CechIdx.pairIdx a b hab).elem 1 = b := rfl

@[simp] lemma CechIdx.zeroIdx_toList (i : Fin (n + 1)) :
    (CechIdx.zeroIdx i).toList = [i] := rfl

/-! ## Iterated multiplication on the structure module -/

/-- Iterated multiplication on the structure module is multiplication by the product of
the corresponding variables. -/
lemma structureModule_mulList_val (K : Type u) [CommRing K] (m : ℕ) :
    ∀ (L : List (Fin (m + 1))) (d e : ℤ) (h : d + (L.length : ℤ) = e)
      (p : (structureModule K m).obj d),
      (((structureModule K m).mulList L d e h).hom p).1 =
        (L.map MvPolynomial.X).prod * p.1
  | [], d, e, h, p => by
      have hde : d = e := by simpa using h
      subst hde
      simp [mulList]
  | i :: t, d, e, h, p => by
      have h' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      simp only [mulList, ModuleCat.hom_comp, LinearMap.comp_apply, List.map_cons,
        List.prod_cons]
      rw [structureModule_mulList_val K m t (d + 1) e h']
      have hx : (((structureModule K m).mulX i d).hom p).1 =
          MvPolynomial.X i * p.1 := rfl
      rw [hx, ← mul_assoc, mul_comm (List.map MvPolynomial.X t).prod]

/-- The iterated list of a single variable is the constant list. -/
lemma listPow_singleton (i : Fin (n + 1)) (m : ℕ) :
    listPow [i] m = List.replicate m i := by
  induction m with
  | zero => rfl
  | succ a ih =>
      rw [show a + 1 = 1 + a from by omega, listPow_add, ih,
        show listPow [i] 1 = [i] from by simp [listPow]]
      rw [show List.replicate (1 + a) i = List.replicate 1 i ++ List.replicate a i from
        by rw [List.replicate_add]]
      rfl

/-- Multiplication along the iterated singleton list is multiplication by a power. -/
lemma structureModule_mulList_singleton_val (i : Fin (n + 1)) (m : ℕ) (d e : ℤ)
    (h : d + ((listPow [i] m).length : ℤ) = e)
    (p : (structureModule k n).obj d) :
    (((structureModule k n).mulList (listPow [i] m) d e h).hom p).1 =
      (MvPolynomial.X i) ^ m * p.1 := by
  rw [structureModule_mulList_val k n (listPow [i] m) d e h p, listPow_singleton]
  congr 1
  rw [List.map_replicate, List.prod_replicate]

/-! ## The cocycle condition on a pair -/


/-- The degree of the `m`-th stage over a singleton index. -/
lemma locDeg_singleton (i : Fin (n + 1)) (d : ℤ) (m : ℕ) :
    locDeg [i] d m = d + (m : ℤ) := by
  rw [locDeg_def]
  simp

/-- Stage inclusions for the structure module are injective. -/
lemma injective_locIncl_structureModule (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    Function.Injective (((structureModule k n).locIncl l d j).hom) :=
  injective_locIncl _ (injective_structureModule_mulX n) l d j

/-- The face restriction, evaluated on a stage element. -/
lemma cechFaceMap_locIncl (M : GradedModule k n) {p : ℕ} (τ : CechIdx n (p + 1))
    (i : Fin (p + 2)) (d : ℤ) (j : ℕ)
    (x : M.obj (locDeg (τ.face i).toList d j)) :
    ((M.cechFaceMap τ i).app d).hom
        ((M.locIncl (τ.face i).toList d j).hom x) =
      (M.locIncl τ.toList d j).hom
        ((M.mulList (listPow [τ.elem i] j)
          (locDeg (τ.face i).toList d j) (locDeg τ.toList d j)
          (locRes_stage_degree (τ.face i).toList τ.toList [τ.elem i]
            (τ.perm_face_append i) d j)).hom x) := by
  have h := congrArg ModuleCat.Hom.hom
    (locIncl_locRes_app M (τ.face i).toList (τ.perm_face_append i) d j)
  simp only [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h x

/-- **The cocycle relation on a pair, read in the polynomial ring.**  If a `0`-cochain of
the structure module is a cocycle and its components at `a < b` are represented at a
common stage `m` by `g_a` and `g_b`, then `x_a^m g_b = x_b^m g_a` in `S`. -/
lemma cocycle_pair_eq (d : ℤ) (c : (structureModule k n).cechCochain 0 d)
    (hc : ((structureModule k n).cechD 0 d).hom c = 0)
    (m : ℕ) (a b : Fin (n + 1)) (hab : a < b)
    (ga : (structureModule k n).obj (locDeg [a] d m))
    (gb : (structureModule k n).obj (locDeg [b] d m))
    (hga : ((structureModule k n).locIncl [a] d m).hom ga =
      c (CechIdx.zeroIdx a))
    (hgb : ((structureModule k n).locIncl [b] d m).hom gb =
      c (CechIdx.zeroIdx b)) :
    (MvPolynomial.X a) ^ m * gb.1 = (MvPolynomial.X b) ^ m * ga.1 := by
  set τ : CechIdx n 1 := CechIdx.pairIdx a b hab with hτ
  -- restate the representatives at the faces of `τ` (definitionally the same indices)
  have hgb' : ((structureModule k n).locIncl (τ.face 0).toList d m).hom gb =
      c (τ.face 0) := hgb
  have hga' : ((structureModule k n).locIncl (τ.face 1).toList d m).hom ga =
      c (τ.face 1) := hga
  -- the cocycle condition at the pair
  have hcτ : (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) •
      (((structureModule k n).cechFaceMap τ i).app d).hom (c (τ.face i))) = 0 :=
    congrFun hc τ
  rw [Fin.sum_univ_two] at hcτ
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul] at hcτ
  have hAB := add_neg_eq_zero.mp hcτ
  rw [← hgb', ← hga', cechFaceMap_locIncl, cechFaceMap_locIncl] at hAB
  -- the stage inclusion at the pair is injective
  have hinj := injective_locIncl_structureModule (k := k) τ.toList d m hAB
  have hval := congrArg Subtype.val hinj
  have hL := structureModule_mulList_singleton_val (k := k) (τ.elem 0) m
    (locDeg (τ.face 0).toList d m) (locDeg τ.toList d m)
    (locRes_stage_degree (τ.face 0).toList τ.toList [τ.elem 0]
      (τ.perm_face_append 0) d m) gb
  have hR := structureModule_mulList_singleton_val (k := k) (τ.elem 1) m
    (locDeg (τ.face 1).toList d m) (locDeg τ.toList d m)
    (locRes_stage_degree (τ.face 1).toList τ.toList [τ.elem 1]
      (τ.perm_face_append 1) d m) ga
  exact hL.symm.trans (hval.trans hR)

/-- The cocycle relation for an unordered pair of distinct indices: `xᵢ^m` divides the
representative `gᵢ`. -/
lemma X_pow_dvd_of_cocycle (d : ℤ) (c : (structureModule k n).cechCochain 0 d)
    (hc : ((structureModule k n).cechD 0 d).hom c = 0)
    (m : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (gi : (structureModule k n).obj (locDeg [i] d m))
    (gj : (structureModule k n).obj (locDeg [j] d m))
    (hgi : ((structureModule k n).locIncl [i] d m).hom gi =
      c (CechIdx.zeroIdx i))
    (hgj : ((structureModule k n).locIncl [j] d m).hom gj =
      c (CechIdx.zeroIdx j)) :
    ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) ^ m ∣ gi.1 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- `i < j` : the pair lemma gives `xᵢ^m g_j = x_j^m g_i`
    have h := cocycle_pair_eq d c hc m i j hlt gi gj hgi hgj
    exact MvPolynomial.X_pow_dvd_of_mul_eq_mul hij m h.symm
  · -- `j < i`
    have h := cocycle_pair_eq d c hc m j i hgt gj gi hgj hgi
    exact MvPolynomial.X_pow_dvd_of_mul_eq_mul hij m h

/-- Transport along an equality of degrees does not change the underlying polynomial. -/
lemma structureModule_eqToHom_val {e₁ e₂ : ℤ} (he : e₁ = e₂)
    (x : (structureModule k n).obj e₁) :
    (((eqToHom (congrArg (structureModule k n).obj he)).hom x)).1 = x.1 := by
  subst he
  simp

/-! ## The `H⁰` computation -/

/-- The symmetric form of the pair relation. -/
lemma cocycle_ne_eq (d : ℤ) (c : (structureModule k n).cechCochain 0 d)
    (hc : ((structureModule k n).cechD 0 d).hom c = 0)
    (m : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j)
    (gi : (structureModule k n).obj (locDeg [i] d m))
    (gj : (structureModule k n).obj (locDeg [j] d m))
    (hgi : ((structureModule k n).locIncl [i] d m).hom gi =
      c (CechIdx.zeroIdx i))
    (hgj : ((structureModule k n).locIncl [j] d m).hom gj =
      c (CechIdx.zeroIdx j)) :
    (MvPolynomial.X i) ^ m * gj.1 = (MvPolynomial.X j) ^ m * gi.1 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact cocycle_pair_eq d c hc m i j hlt gi gj hgi hgj
  · exact (cocycle_pair_eq d c hc m j i hgt gj gi hgj hgi).symm

/-- **`H⁰(ℙⁿ, 𝒪(d)) = S_d` for `d ≥ 0`**: every `0`-cocycle of the Čech complex of the
structure module is the augmentation of a form of degree `d`. -/
theorem cocycle_structureModule (d : ℤ) (hd : 0 ≤ d)
    (c : (structureModule k n).cechCochain 0 d)
    (hc : ((structureModule k n).cechD 0 d).hom c = 0) :
    ∃ x : (structureModule k n).obj d,
      ((structureModule k n).cechAug₀ d).hom x = c := by
  classical
  -- represent every component at a common stage `m`
  choose ms fs hfs using fun i : Fin (n + 1) =>
    (structureModule k n).locIncl_exists [i] d (c (CechIdx.zeroIdx i))
  set m := Finset.univ.sup ms with hmdef
  have hle : ∀ i, ms i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  set g : ∀ i : Fin (n + 1), (structureModule k n).obj (locDeg [i] d m) :=
    fun i => ((structureModule k n).locTr [i] d (ms i) m (hle i)).hom (fs i)
    with hgdef
  have hgc : ∀ i, ((structureModule k n).locIncl [i] d m).hom (g i) =
      c (CechIdx.zeroIdx i) := by
    intro i
    have h1 := congrArg ModuleCat.Hom.hom
      ((structureModule k n).locTr_locIncl [i] d (ms i) m (hle i))
    simp only [ModuleCat.hom_comp] at h1
    have h2 := LinearMap.congr_fun h1 (fs i)
    simp only [LinearMap.comp_apply] at h2
    rw [hgdef]
    exact h2.trans (hfs i)
  -- each representative is homogeneous of degree `d + m`
  have hhom : ∀ i, ((g i).1).IsHomogeneous (d.toNat + m) := by
    intro i
    have heq : polySubmodule k n (locDeg [i] d m) =
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d.toNat + m) := by
      rw [locDeg_singleton, polySubmodule_of_nonneg k n (by omega),
        show (d + (m : ℤ)).toNat = d.toNat + m from by omega]
    have h2 : ((g i).1 : MvPolynomial (Fin (n + 1)) k) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k (d.toNat + m) :=
      heq ▸ (g i).2
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp h2
  -- each representative is divisible by the corresponding power
  have hdvd : ∀ i, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) ^ m ∣
      (g i).1 := by
    intro i
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
      exact MvPolynomial.X_pow_dvd_of_isHomogeneous_subsingleton i (hhom i)
        (by omega)
    · haveI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨j, hj⟩ := exists_ne i
      exact X_pow_dvd_of_cocycle d c hc m i j (Ne.symm hj) (g i) (g j)
        (hgc i) (hgc j)
  -- extract the quotients and see that they are homogeneous of degree `d`
  choose h hh using hdvd
  have hhhom : ∀ i, (h i).IsHomogeneous d.toNat := fun i =>
    MvPolynomial.IsHomogeneous.of_X_pow_mul (hhom i) (hh i)
  -- the quotients all agree
  have hheq : ∀ i, h i = h 0 := by
    intro i
    by_cases hi0 : i = 0
    · rw [hi0]
    · have hrel := cocycle_ne_eq d c hc m i 0 hi0 (g i) (g 0) (hgc i) (hgc 0)
      rw [hh i, hh 0] at hrel
      have hcalc : ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) ^ m *
            (((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k)) ^ m * h i)
          = ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) ^ m *
            (((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) k)) ^ m * h 0) := by
        rw [hrel]; ring
      exact MvPolynomial.eq_of_X_pow_mul_eq (MvPolynomial.eq_of_X_pow_mul_eq hcalc)
  -- the common quotient is the required global form
  refine ⟨⟨h 0, ?_⟩, ?_⟩
  · rw [polySubmodule_of_nonneg k n hd]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhhom 0)
  · funext τ
    obtain ⟨i, rfl⟩ : ∃ i, τ = CechIdx.zeroIdx i :=
      ⟨τ.elem 0, CechIdx.eq_zeroIdx τ⟩
    show (((structureModule k n).locOf [i]).app d).hom ⟨h 0, _⟩ =
      c (CechIdx.zeroIdx i)
    rw [← hgc i]
    -- both sides are the stage-`m` inclusion of `g i`
    have hstage : ((structureModule k n).locTr [i] d 0 m (Nat.zero_le m)).hom
        ((eqToHom (congrArg (structureModule k n).obj
          (show d = locDeg [i] d 0 by rw [locDeg_def]; push_cast; ring))).hom
            ⟨h 0, by
              rw [polySubmodule_of_nonneg k n hd]
              exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhhom 0)⟩) =
        g i := by
      refine Subtype.ext ?_
      have hval : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) ^ m * h 0 =
          (g i).1 := by
        rw [← hheq i]
        exact (hh i).symm
      rw [locTr, structureModule_mulList_val k n _ _ _ _ _, listPow_singleton,
        List.map_replicate, List.prod_replicate,
        structureModule_eqToHom_val
          (show d = locDeg [i] d 0 by rw [locDeg_def]; push_cast; ring),
        show m - 0 = m from by omega]
      exact hval
    have hfinal := congrArg ModuleCat.Hom.hom
      ((structureModule k n).locTr_locIncl [i] d 0 m (Nat.zero_le m))
    simp only [ModuleCat.hom_comp] at hfinal
    rw [locOf_app]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← hstage]
    exact (LinearMap.congr_fun hfinal _).symm


/-- **`H⁰(ℙⁿ, 𝒪(d)) = 0` for `d < 0`**: the only `0`-cocycle of the Čech complex of the
structure module in a negative degree is zero.

Representing the cocycle at a common tower stage `m`, each component is a form of degree
`d + m < m` divisible by `Xᵢ^m`, hence zero
(`MvPolynomial.eq_zero_of_X_pow_mul_of_isHomogeneous`).  This is the vanishing that
`GradedModule.IsFG` needs in order to see `Γ_*(𝒪(-l)^{⊕r})` as a finitely generated
graded module.

**The hypothesis `0 < n` is necessary.**  On `ℙ⁰ = Spec k` the twisting sheaves are all
trivial, so `H⁰(ℙ⁰, 𝒪(d)) = k` for every `d`; in the graded model `S[1/x₀]_d = k · x₀^d` is
one-dimensional in every degree, and there is no second chart to intersect it with.  The
divisibility step below is exactly where `0 < n` enters, through
`X_pow_dvd_of_cocycle`, which needs a second variable. -/
theorem cocycle_structureModule_of_neg (n : ℕ) (hn : 0 < n) (d : ℤ) (hd : d < 0)
    (c : (structureModule k n).cechCochain 0 d)
    (hc : ((structureModule k n).cechD 0 d).hom c = 0) :
    c = 0 := by
  classical
  choose ms fs hfs using fun i : Fin (n + 1) =>
    (structureModule k n).locIncl_exists [i] d (c (CechIdx.zeroIdx i))
  set m := Finset.univ.sup ms with hmdef
  have hle : ∀ i, ms i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  set g : ∀ i : Fin (n + 1), (structureModule k n).obj (locDeg [i] d m) :=
    fun i => ((structureModule k n).locTr [i] d (ms i) m (hle i)).hom (fs i)
    with hgdef
  have hgc : ∀ i, ((structureModule k n).locIncl [i] d m).hom (g i) =
      c (CechIdx.zeroIdx i) := by
    intro i
    have h1 := congrArg ModuleCat.Hom.hom
      ((structureModule k n).locTr_locIncl [i] d (ms i) m (hle i))
    simp only [ModuleCat.hom_comp] at h1
    have h2 := LinearMap.congr_fun h1 (fs i)
    simp only [LinearMap.comp_apply] at h2
    rw [hgdef]
    exact h2.trans (hfs i)
  have hg0 : ∀ i, g i = 0 := by
    intro i
    rcases lt_or_ge (d + (m : ℤ)) 0 with hneg | hnn
    · have hbot : polySubmodule k n (locDeg [i] d m) = ⊥ := by
        have hlt : ¬ ((0 : ℤ) ≤ locDeg [i] d m) := by
          rw [locDeg_singleton]
          omega
        simp only [polySubmodule, hlt, ↓reduceIte]
      haveI : Subsingleton ((structureModule k n).obj (locDeg [i] d m)) := by
        rw [show (structureModule k n).obj (locDeg [i] d m)
            = ModuleCat.of k (polySubmodule k n (locDeg [i] d m)) from rfl, hbot]
        infer_instance
      exact Subsingleton.elim _ _
    · have hhom : ((g i).1).IsHomogeneous ((d + (m : ℤ)).toNat) := by
        have heq : polySubmodule k n (locDeg [i] d m) =
            MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k ((d + (m : ℤ)).toNat) := by
          rw [locDeg_singleton, polySubmodule_of_nonneg k n hnn]
        have h2 : ((g i).1 : MvPolynomial (Fin (n + 1)) k) ∈
            MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k ((d + (m : ℤ)).toNat) :=
          heq ▸ (g i).2
        exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp h2
      have hdvd : ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)) ^ m ∣ (g i).1 := by
        haveI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
        obtain ⟨j, hj⟩ := exists_ne i
        exact X_pow_dvd_of_cocycle d c hc m i j (Ne.symm hj) (g i) (g j)
          (hgc i) (hgc j)
      obtain ⟨q, hq⟩ := hdvd
      refine Subtype.ext ?_
      exact MvPolynomial.eq_zero_of_X_pow_mul_of_isHomogeneous hhom hq (by omega)
  funext τ
  obtain ⟨i, rfl⟩ : ∃ i, τ = CechIdx.zeroIdx i :=
    ⟨τ.elem 0, CechIdx.eq_zeroIdx τ⟩
  rw [← hgc i, hg0 i, map_zero]
  rfl

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
