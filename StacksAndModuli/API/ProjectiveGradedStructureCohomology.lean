module

public import StacksAndModuli.API.ProjectiveLaurentModel
public import StacksAndModuli.API.SimplicialSignHomotopy
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The cohomology of the twisting sheaves on `ℙⁿ_k`

Supporting API with no Stacks Project counterpart.

This file computes the higher Čech cohomology of `𝒪(d)` on `ℙⁿ_k`, i.e. Hartshorne
III.5.1(b,c) in the vanishing range: `Hⁱ(ℙⁿ, 𝒪(d)) = 0` for `1 ≤ i < n`, and for `i = n`
when `d ≥ -n`.  Together with `StacksAndModuli/API/ProjectiveGradedH0.lean` this settles the
field `subsingleton_Hgr_structureModule` of `CechSerreData`.

The argument is the classical one.  Under the Laurent-monomial model of
`StacksAndModuli/API/ProjectiveLaurentModel.lean` the Čech complex of `𝒪(d)` becomes a complex
of subspaces of one ambient space, with the face restrictions being inclusions, so it
splits as a direct sum over Laurent monomials `x^a` of degree `d`.  The summand at `x^a`
is the simplicial cochain complex of the full simplex on the vertices `i` with `aᵢ ≥ 0`,
which is contractible as soon as there is such a vertex — and there always is, unless
every `aᵢ` is negative, which forces `d ≤ -(n+1)`.

Main declarations:
- `CechIdx.toFinset` and the dictionary with `Finset.simplicialD`;
- `GradedModule.exists_cechD_eq_of_cocycle`;
- `GradedModule.subsingleton_cechHgr_structureModule`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory Finset MvPolynomial

variable {k : Type u} [CommRing k] {n p : ℕ}

/-! ## Čech indices as finite sets -/

namespace CechIdx

/-- The set of variables inverted by a Čech index. -/
def toFinset (τ : CechIdx n p) : Finset (Fin (n + 1)) := τ.toList.toFinset

lemma nodup (τ : CechIdx n p) : τ.toList.Nodup := τ.sorted.nodup

@[simp] lemma mem_toFinset {τ : CechIdx n p} {y : Fin (n + 1)} :
    y ∈ τ.toFinset ↔ y ∈ τ.toList := List.mem_toFinset

@[simp] lemma card_toFinset (τ : CechIdx n p) : #τ.toFinset = p + 1 := by
  rw [toFinset, List.card_toFinset, τ.nodup.dedup, τ.length_eq]

lemma toFinset_injective : Function.Injective (toFinset (n := n) (p := p)) := fun σ τ h =>
  CechIdx.ext (List.Perm.eq_of_pairwise' (σ.sorted.imp le_of_lt) (τ.sorted.imp le_of_lt)
    (List.perm_of_nodup_nodup_toFinset_eq σ.nodup τ.nodup h))

noncomputable instance : Fintype (CechIdx n p) :=
  Fintype.ofInjective toFinset toFinset_injective

/-- Every subset of the right size is the variable set of a Čech index. -/
lemma exists_toFinset_eq (s : Finset (Fin (n + 1))) (h : #s = p + 1) :
    ∃ τ : CechIdx n p, τ.toFinset = s := by
  refine ⟨⟨s.sort (· ≤ ·),
    ((List.sortedLE_iff_pairwise.mpr (Finset.pairwise_sort s (· ≤ ·))).sortedLT_of_nodup
        (Finset.sort_nodup s _)).pairwise,
    by rw [Finset.length_sort, h]⟩, ?_⟩
  exact Finset.sort_toFinset s _

lemma elem_mem (τ : CechIdx n p) (i : Fin (p + 1)) : τ.elem i ∈ τ.toFinset := by
  rw [mem_toFinset, elem]
  exact List.getElem_mem _

lemma elem_lt_elem {τ : CechIdx n p} {i j : Fin (p + 1)} (h : i < j) :
    τ.elem i < τ.elem j := by
  have hp := List.pairwise_iff_getElem.mp τ.sorted
  exact hp (i : ℕ) (j : ℕ) (by rw [τ.length_eq]; exact i.isLt)
    (by rw [τ.length_eq]; exact j.isLt) h

lemma elem_strictMono (τ : CechIdx n p) : StrictMono τ.elem := fun _ _ h => elem_lt_elem h

lemma exists_elem_eq {τ : CechIdx n p} {y : Fin (n + 1)} (hy : y ∈ τ.toFinset) :
    ∃ i, τ.elem i = y := by
  rw [mem_toFinset, List.mem_iff_getElem] at hy
  obtain ⟨m, hm, hmy⟩ := hy
  exact ⟨⟨m, by rw [← τ.length_eq]; exact hm⟩, hmy⟩

/-- Reindexing a sum over the positions of a Čech index as a sum over its variables. -/
lemma sum_elem_bij {V : Type*} [AddCommMonoid V] (τ : CechIdx n p) (f : Fin (p + 1) → V)
    (g : Fin (n + 1) → V) (hfg : ∀ i, f i = g (τ.elem i)) :
    ∑ i : Fin (p + 1), f i = ∑ x ∈ τ.toFinset, g x := by
  refine Finset.sum_bij (fun i _ => τ.elem i) (fun i _ => τ.elem_mem i)
    (fun i _ j _ h => τ.elem_strictMono.injective h)
    (fun y hy => ?_) (fun i _ => hfg i)
  obtain ⟨i, hi⟩ := exists_elem_eq hy
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- The Koszul sign of a variable inside a Čech index is the alternating sign of its
position. -/
lemma koszulSign_elem (τ : CechIdx n p) (i : Fin (p + 1)) :
    Finset.koszulSign (τ.elem i) τ.toFinset = (-1) ^ (i : ℕ) := by
  classical
  have hset : {y ∈ τ.toFinset | y < τ.elem i} = (Finset.Iio i).image τ.elem := by
    refine Finset.ext fun y => ?_
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨j, rfl⟩ := exists_elem_eq hy
      exact ⟨j, τ.elem_strictMono.lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨τ.elem_mem j, τ.elem_strictMono hj⟩
  rw [Finset.koszulSign, hset,
    Finset.card_image_of_injective _ τ.elem_strictMono.injective, Fin.card_Iio]

/-- Taking a face removes the corresponding variable. -/
lemma face_toFinset (τ : CechIdx n (p + 1)) (i : Fin (p + 2)) :
    (τ.face i).toFinset = τ.toFinset.erase (τ.elem i) := by
  classical
  have hperm := τ.perm_face_append i
  have hnd : ((τ.face i).toList ++ [τ.elem i]).Nodup := (hperm.nodup_iff).mp τ.nodup
  have hnotmem : τ.elem i ∉ (τ.face i).toList := by
    rw [List.nodup_append] at hnd
    intro hc
    exact hnd.2.2 _ hc _ (List.mem_singleton_self _) rfl
  refine Finset.ext fun y => ?_
  rw [Finset.mem_erase, mem_toFinset, mem_toFinset, hperm.mem_iff, List.mem_append,
    List.mem_singleton]
  constructor
  · intro hy
    exact ⟨fun hc => hnotmem (hc ▸ hy), Or.inl hy⟩
  · rintro ⟨hne, hy | hy⟩
    · exact hy
    · exact absurd hy hne

end CechIdx

/-! ## The Čech complex of `𝒪(d)` in the Laurent model -/

variable (k) in
/-- A Čech cochain of the structure sheaf, read in the Laurent model and extended by zero
to all finite sets of variables. -/
def cechLaurent (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain p d)
    (s : Finset (Fin (n + 1))) : LaurentSpace k n :=
  ∑ τ : CechIdx n p, if τ.toFinset = s then (laurent τ.toList d).hom (c τ) else 0

lemma cechLaurent_toFinset (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain p d)
    (τ : CechIdx n p) :
    cechLaurent k d c τ.toFinset = (laurent τ.toList d).hom (c τ) := by
  rw [cechLaurent, Finset.sum_eq_single τ ?_ ?_]
  · simp only [↓reduceIte]
  · intro σ _ hσ
    have h : ¬ (σ.toFinset = τ.toFinset) := fun hc => hσ (CechIdx.toFinset_injective hc)
    simp only [h, ↓reduceIte]
  · intro hc
    exact absurd (Finset.mem_univ τ) hc

lemma cechLaurent_eq_zero (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain p d)
    {s : Finset (Fin (n + 1))} (h : ∀ τ : CechIdx n p, τ.toFinset ≠ s) :
    cechLaurent k d c s = 0 := by
  rw [cechLaurent]
  refine Finset.sum_eq_zero fun τ _ => ?_
  simp only [h τ, ↓reduceIte]

lemma cechLaurent_of_card_ne (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain p d)
    {s : Finset (Fin (n + 1))} (h : #s ≠ p + 1) : cechLaurent k d c s = 0 :=
  cechLaurent_eq_zero d c (fun τ hc => h (hc ▸ τ.card_toFinset))

lemma cechLaurent_mem (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain p d)
    (τ : CechIdx n p) :
    cechLaurent k d c τ.toFinset ∈ laurentPiece k τ.toList d := by
  rw [cechLaurent_toFinset]
  exact laurent_mem τ.toList d (c τ)

/-- The Čech differential becomes the simplicial differential in the Laurent model. -/
lemma simplicialD_cechLaurent (d : ℤ) {p : ℕ}
    (c : (structureModule k n).cechCochain p d) (υ : CechIdx n (p + 1)) :
    Finset.simplicialD (cechLaurent k d c) υ.toFinset
      = (laurent υ.toList d).hom (((structureModule k n).cechD p d).hom c υ) := by
  have hstep : ∀ i : Fin (p + 2),
      ((-1 : ℤ) ^ (i : ℕ)) • cechLaurent k d c ((υ.face i).toFinset)
        = (laurent υ.toList d).hom
            (((-1 : ℤ) ^ (i : ℕ)) •
              (((structureModule k n).cechFaceMap υ i).app d).hom (c (υ.face i))) := by
    intro i
    rw [map_zsmul, cechLaurent_toFinset]
    congr 1
    exact (laurent_locRes_apply (υ.perm_face_append i) d (c (υ.face i))).symm
  have hsum : ((structureModule k n).cechD p d).hom c υ
      = ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          (((structureModule k n).cechFaceMap υ i).app d).hom (c (υ.face i)) := rfl
  rw [hsum, map_sum, Finset.simplicialD,
    ← CechIdx.sum_elem_bij υ
      (fun i => ((-1 : ℤ) ^ (i : ℕ)) • cechLaurent k d c ((υ.face i).toFinset))
      (fun x => Finset.koszulSign x υ.toFinset • cechLaurent k d c (υ.toFinset.erase x))
      (fun i => by rw [CechIdx.koszulSign_elem, CechIdx.face_toFinset])]
  exact Finset.sum_congr rfl (fun i _ => hstep i)

lemma simplicialD_cechLaurent_eq_zero (d : ℤ) {p : ℕ}
    (c : (structureModule k n).cechCochain p d)
    (hc : ((structureModule k n).cechD p d).hom c = 0) (s : Finset (Fin (n + 1))) :
    Finset.simplicialD (cechLaurent k d c) s = 0 := by
  by_cases hs : #s = p + 2
  · obtain ⟨υ, rfl⟩ := CechIdx.exists_toFinset_eq s hs
    rw [simplicialD_cechLaurent, hc]
    exact map_zero _
  · refine Finset.sum_eq_zero fun x hx => ?_
    have hcard : #(s.erase x) ≠ p + 1 := by
      rw [Finset.card_erase_of_mem hx]
      have h1 : 1 ≤ #s := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    rw [cechLaurent_of_card_ne d c hcard, smul_zero]

/-! ## The coned homotopy -/

/-- A variable at which a Laurent monomial is regular, when there is one. -/
def regVertex (a : Fin (n + 1) → ℤ) : Fin (n + 1) :=
  if h : ∃ i, 0 ≤ a i then h.choose else 0

lemma regVertex_spec {a : Fin (n + 1) → ℤ} (h : ∃ i, 0 ≤ a i) : 0 ≤ a (regVertex a) := by
  rw [regVertex]
  split
  · rename_i h'
    exact h'.choose_spec
  · rename_i h'
    exact absurd h h'

variable (k) in
/-- Coning off, monomial by monomial, the variable at which the monomial is regular. -/
def cechHomotopy (d : ℤ) {p : ℕ} (c : (structureModule k n).cechCochain (p + 1) d)
    (s : Finset (Fin (n + 1))) : LaurentSpace k n :=
  ∑ i : Fin (n + 1), if i ∈ s then 0 else
    Finset.koszulSign i (insert i s) •
      Finsupp.filter (fun a => regVertex a = i) (cechLaurent k d c (insert i s))

lemma cechHomotopy_apply (d : ℤ) {p : ℕ}
    (c : (structureModule k n).cechCochain (p + 1) d) (s : Finset (Fin (n + 1)))
    (a : Fin (n + 1) → ℤ) :
    cechHomotopy k d c s a
      = Finset.simplicialH (regVertex a) (fun t => cechLaurent k d c t a) s := by
  classical
  rw [cechHomotopy, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (regVertex a) ?_ (fun hc => absurd (Finset.mem_univ _) hc)]
  · by_cases hv : regVertex a ∈ s
    · simp only [hv, ↓reduceIte, Finsupp.coe_zero, Pi.zero_apply,
        Finset.simplicialH_of_mem hv]
    · rw [Finset.simplicialH_of_notMem hv]
      simp only [hv, ↓reduceIte, Finsupp.smul_apply, Finsupp.filter_apply, ↓reduceIte]
  · intro i _ hi
    by_cases hs : i ∈ s
    · simp only [hs, ↓reduceIte, Finsupp.coe_zero, Pi.zero_apply]
    · simp only [hs, ↓reduceIte, Finsupp.smul_apply, Finsupp.filter_apply,
        (Ne.symm hi : ¬ (regVertex a = i)), ↓reduceIte, smul_zero]

lemma simplicialD_apply (F : Finset (Fin (n + 1)) → LaurentSpace k n)
    (s : Finset (Fin (n + 1))) (a : Fin (n + 1) → ℤ) :
    Finset.simplicialD F s a = Finset.simplicialD (fun t => F t a) s := by
  rw [Finset.simplicialD, Finset.simplicialD, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl (fun x _ => Finsupp.smul_apply _ _ _)

/-- The coned homotopy inverts the simplicial differential on cocycles. -/
lemma simplicialD_cechHomotopy (d : ℤ) {p : ℕ}
    (c : (structureModule k n).cechCochain (p + 1) d)
    (hc : ((structureModule k n).cechD (p + 1) d).hom c = 0) (s : Finset (Fin (n + 1))) :
    Finset.simplicialD (cechHomotopy k d c) s = cechLaurent k d c s := by
  refine Finsupp.ext fun a => ?_
  rw [simplicialD_apply]
  have hcoc : Finset.simplicialH (regVertex a)
      (Finset.simplicialD (fun t => cechLaurent k d c t a)) s = 0 := by
    by_cases hv : regVertex a ∈ s
    · exact Finset.simplicialH_of_mem hv _
    · rw [Finset.simplicialH_of_notMem hv, ← simplicialD_apply,
        simplicialD_cechLaurent_eq_zero d c hc]
      simp only [Finsupp.coe_zero, Pi.zero_apply, smul_zero]
  have hid := Finset.simplicialD_simplicialH_add (regVertex a)
    (fun t => cechLaurent k d c t a) s
  rw [hcoc, add_zero] at hid
  rw [← hid]
  exact Finset.sum_congr rfl
    (fun x _ => congrArg _ (cechHomotopy_apply d c (s.erase x) a))

/-! ## Exactness of the Čech complex of `𝒪(d)` -/

/-- **Every Čech cocycle of `𝒪(d)` in positive degree is a coboundary**, provided every
Laurent monomial of degree `d` that can occur is regular at some variable. -/
theorem exists_cechD_eq_of_cocycle (d : ℤ) {p : ℕ}
    (hv : ∀ (τ : CechIdx n (p + 1)) (a : Fin (n + 1) → ℤ),
      a ∈ lexpAdm τ.toList d → ∃ i, 0 ≤ a i)
    (c : (structureModule k n).cechCochain (p + 1) d)
    (hc : ((structureModule k n).cechD (p + 1) d).hom c = 0) :
    ∃ b : (structureModule k n).cechCochain p d,
      ((structureModule k n).cechD p d).hom b = c := by
  classical
  -- the coned homotopy is admissible on every Čech index
  have hmem : ∀ σ : CechIdx n p, ∃ y, (laurent (k := k) σ.toList d).hom y
      = cechHomotopy k d c σ.toFinset := by
    intro σ
    refine LinearMap.mem_range.mp ?_
    rw [range_laurent, laurentPiece, Finsupp.mem_supported]
    intro a ha
    rw [Finset.mem_coe, Finsupp.mem_support_iff, cechHomotopy_apply] at ha
    by_cases hvs : regVertex a ∈ σ.toFinset
    · exact absurd (Finset.simplicialH_of_mem hvs _) ha
    rw [Finset.simplicialH_of_notMem hvs] at ha
    have hne : cechLaurent k d c (insert (regVertex a) σ.toFinset) a ≠ 0 := by
      intro h0
      exact ha (by rw [h0, smul_zero])
    have hcard : #(insert (regVertex a) σ.toFinset) = p + 2 := by
      rw [Finset.card_insert_of_notMem hvs, σ.card_toFinset]
    obtain ⟨τ, hτ⟩ := CechIdx.exists_toFinset_eq _ hcard
    have hmemτ : a ∈ lexpAdm τ.toList d := by
      have h1 := cechLaurent_mem d c τ
      rw [laurentPiece, Finsupp.mem_supported] at h1
      exact h1 (by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hτ]
        exact hne)
    have hreg : 0 ≤ a (regVertex a) := regVertex_spec (hv τ a hmemτ)
    refine ⟨hmemτ.1, fun j hj => ?_⟩
    by_cases hjv : j = regVertex a
    · rw [hjv]; exact hreg
    · refine hmemτ.2 j ?_
      rw [← CechIdx.mem_toFinset, hτ, Finset.mem_insert]
      rintro (h1 | h1)
      · exact hjv h1
      · exact hj (CechIdx.mem_toFinset.mp h1)
  choose b hb using hmem
  refine ⟨b, funext fun τ => ?_⟩
  refine laurent_injective τ.toList d ?_
  have hagree : ∀ x ∈ τ.toFinset,
      Finset.koszulSign x τ.toFinset • cechLaurent k d b (τ.toFinset.erase x)
        = Finset.koszulSign x τ.toFinset • cechHomotopy k d c (τ.toFinset.erase x) := by
    intro x hx
    obtain ⟨σ, hσ⟩ := CechIdx.exists_toFinset_eq (p := p) (τ.toFinset.erase x) (by
      rw [Finset.card_erase_of_mem hx, τ.card_toFinset]
      omega)
    rw [← hσ, cechLaurent_toFinset, hb σ]
  rw [← simplicialD_cechLaurent d b τ, Finset.simplicialD,
    Finset.sum_congr rfl hagree, ← Finset.simplicialD,
    simplicialD_cechHomotopy d c hc, cechLaurent_toFinset]

/-! ## Vanishing -/

/-- **Hartshorne III.5.1(b,c) in the vanishing range.**  The higher Čech cohomology of
`𝒪(d)` on `ℙⁿ_k` vanishes below the top degree, and in the top degree once `d ≥ -n`. -/
theorem subsingleton_cechHgr_structureModule (i : ℕ) (d : ℤ) (hi : 1 ≤ i)
    (h : i ≠ n ∨ -(n : ℤ) ≤ d) :
    Subsingleton (((structureModule k n).cechHgr i).obj d) := by
  classical
  rcases lt_or_ge n i with hni | hni
  · exact subsingleton_cechHgr _ i hni d
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
  -- every Laurent monomial that can occur is regular at some variable
  have hv : ∀ (τ : CechIdx n (p + 1)) (a : Fin (n + 1) → ℤ),
      a ∈ lexpAdm τ.toList d → ∃ j, 0 ≤ a j := by
    intro τ a ha
    by_contra hcon
    simp only [not_exists, Int.not_le] at hcon
    rcases h with hne | hd
    · -- `p + 1 < n`: some variable is not inverted by `τ`
      have hlt : p + 1 < n := by omega
      have hcard : #τ.toFinset < #(Finset.univ : Finset (Fin (n + 1))) := by
        rw [τ.card_toFinset, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      exact absurd (ha.2 j (fun hc => hj (CechIdx.mem_toFinset.mpr hc))) (not_le.mpr (hcon j))
    · -- `d ≥ -n`: a monomial with every exponent negative has degree at most `-(n+1)`
      have hsum : lexpDeg a ≤ -((n : ℤ) + 1) := by
        have h1 : ∑ j, a j ≤ ∑ _j : Fin (n + 1), (-1 : ℤ) :=
          Finset.sum_le_sum (fun j _ => by have := hcon j; omega)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
        simpa [lexpDeg] using h1
      rw [ha.1] at hsum
      omega
  -- exactness of the Čech complex at `p + 1`
  have hex : ((structureModule k n).cechComplex d).ExactAt (p + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro z hz
    have hd1 : ((structureModule k n).cechComplex d).d (p + 1) (p + 2)
        = (structureModule k n).cechD (p + 1) d :=
      CochainComplex.of_d (fun q => (structureModule k n).cechCochain q d)
        (fun q => (structureModule k n).cechD q d) (p + 1)
    have hd0 : ((structureModule k n).cechComplex d).d p (p + 1)
        = (structureModule k n).cechD p d :=
      CochainComplex.of_d (fun q => (structureModule k n).cechCochain q d)
        (fun q => (structureModule k n).cechD q d) p
    have hzc : ((structureModule k n).cechD (p + 1) d).hom z = 0 := by
      rw [← hd1]
      exact hz
    obtain ⟨b, hbz⟩ := exists_cechD_eq_of_cocycle d hv z hzc
    refine ⟨b, ?_⟩
    rw [show (((structureModule k n).cechComplex d).sc' p (p + 1) (p + 2)).f
      = ((structureModule k n).cechComplex d).d p (p + 1) from rfl, hd0]
    exact hbz
  have hzero := hex.isZero_homology
  rw [ModuleCat.isZero_iff_subsingleton] at hzero
  exact hzero

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
