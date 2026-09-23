module

public import StacksAndModuli.API.ProjectiveLaurentModel
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finitely generated graded modules on `ℙⁿ_k`

Supporting API with no Stacks Project counterpart.

`Cohomology.IsCoherent` is currently an abstract field of the cohomology interface.  This
file gives it a concrete meaning in the graded-module model: a graded module is *finitely
generated* if its graded pieces are finite dimensional, it vanishes in all sufficiently
negative degrees, and above some degree each piece is spanned by the variables acting on the
previous one.  For a bounded-below graded module this is exactly finite generation over
`S = k[x₀, …, x_n]`, and it is phrased entirely through `GradedModule.mulSpan`, which the
library already supports.

Main declarations:
- `GradedModule.IsFG`;
- `GradedModule.isFG_structureModule`, `GradedModule.IsFG.twist`, `GradedModule.IsFG.pow`,
  `GradedModule.IsFG.coker`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace MvPolynomial

/-- The space of forms of a fixed degree in finitely many variables is finite
dimensional. -/
instance finiteDimensional_homogeneousSubmodule (σ : Type*) [Fintype σ] [DecidableEq σ]
    (K : Type u) [CommRing K] (e : ℕ) :
    Module.Finite K (homogeneousSubmodule σ K e) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have hfinite : Set.Finite {d : σ →₀ ℕ | Finsupp.degree d = e} := by
    have hfinite' : Set.Finite
        {d : σ →₀ ℕ | Finsupp.weight (1 : σ → ℕ) d = e} :=
      Finsupp.finite_of_nat_weight_eq (1 : σ → ℕ) (fun _ ↦ one_ne_zero) e
    convert hfinite' using 1
    ext d
    simp only [Set.mem_setOf_eq]
    rw [Finsupp.degree_eq_weight_one]
    have hw : (fun _ : σ ↦ (1 : ℕ)) = (1 : σ → ℕ) := by
      funext i
      rfl
    rw [hw]
  letI : Finite {d : σ →₀ ℕ | Finsupp.degree d = e} := hfinite.to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K _)

lemma degree_eq_weight {σ : Type*} (b : σ →₀ ℕ) :
    b.degree = Finsupp.weight (1 : σ → ℕ) b := by
  rw [Finsupp.degree_eq_weight_one]
  congr 1

/-- Multiplying by a form of degree `a` shifts homogeneous components by `a`.  Mathlib has
`homogeneousComponent_C_mul` but no version for a general homogeneous multiplier. -/
lemma homogeneousComponent_isHomogeneous_mul {σ : Type*} [DecidableEq σ] {R : Type*}
    [CommRing R] {a : ℕ} {q : MvPolynomial σ R} (hq : q.IsHomogeneous a)
    (s : MvPolynomial σ R) {m : ℕ} (hm : a ≤ m) :
    homogeneousComponent m (q * s) = q * homogeneousComponent (m - a) s := by
  classical
  refine MvPolynomial.ext _ _ fun b => ?_
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hb : b.degree = m
  · rw [if_pos hb]
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hc : coeff x.1 q = 0
    · rw [hc, zero_mul, zero_mul]
    · have hcd : x.1.degree = a := by
        have h1 := hq hc
        rw [degree_eq_weight]
        exact h1
      have hsum : x.1 + x.2 = b := (Finset.mem_antidiagonal.mp hx)
      have hdeg : x.2.degree = m - a := by
        have := congrArg Finsupp.degree hsum
        rw [map_add, hcd, hb] at this
        omega
      rw [coeff_homogeneousComponent, if_pos hdeg]
  · rw [if_neg hb]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    by_cases hc : coeff x.1 q = 0
    · rw [hc, zero_mul]
    · have hcd : x.1.degree = a := by
        have h1 := hq hc
        rw [degree_eq_weight]
        exact h1
      rw [coeff_homogeneousComponent]
      by_cases hd : x.2.degree = m - a
      · exfalso
        have hsum : x.1 + x.2 = b := (Finset.mem_antidiagonal.mp hx)
        have := congrArg Finsupp.degree hsum
        rw [map_add, hcd, hd] at this
        omega
      · rw [if_neg hd, mul_zero]

/-- A form of degree `a` kills all homogeneous components below `a`. -/
lemma homogeneousComponent_isHomogeneous_mul_of_lt {σ : Type*} [DecidableEq σ] {R : Type*}
    [CommRing R] {a : ℕ} {q : MvPolynomial σ R} (hq : q.IsHomogeneous a)
    (s : MvPolynomial σ R) {m : ℕ} (hm : m < a) :
    homogeneousComponent m (q * s) = 0 := by
  classical
  refine MvPolynomial.ext _ _ fun b => ?_
  rw [coeff_homogeneousComponent, coeff_zero]
  by_cases hb : b.degree = m
  · rw [if_pos hb, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hc : coeff x.1 q = 0
    · rw [hc, zero_mul]
    · exfalso
      have hcd : x.1.degree = a := by
        have h1 := hq hc
        rw [degree_eq_weight]
        exact h1
      have hsum : x.1 + x.2 = b := Finset.mem_antidiagonal.mp hx
      have hle := congrArg Finsupp.degree hsum
      rw [map_add, hcd, hb] at hle
      omega
  · rw [if_neg hb]

/-- The homogeneous components of a homogeneous polynomial. -/
lemma homogeneousComponent_of_isHomogeneous {σ : Type*} [DecidableEq σ] {R : Type*}
    [CommRing R] {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D) (m : ℕ) :
    homogeneousComponent m p = if m = D then p else 0 := by
  classical
  refine MvPolynomial.ext _ _ fun b => ?_
  rw [coeff_homogeneousComponent]
  by_cases hmD : m = D
  · rw [if_pos hmD]
    by_cases hb : b.degree = m
    · rw [if_pos hb]
    · rw [if_neg hb]
      by_contra hc
      refine hb ?_
      have h1 := hp (Ne.symm hc)
      rw [degree_eq_weight, h1, hmD]
  · rw [if_neg hmD, coeff_zero]
    by_cases hb : b.degree = m
    · rw [if_pos hb]
      by_contra hc
      have h1 := hp hc
      rw [degree_eq_weight] at hb
      rw [h1] at hb
      exact hmD hb.symm
    · rw [if_neg hb]

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [CommRing k] [IsNoetherianRing k] {n : ℕ}

lemma degree_eq_weight_one (b : Fin (n + 1) →₀ ℕ) :
    b.degree = Finsupp.weight (1 : Fin (n + 1) → ℕ) b :=
  (sum_univ_eq_degree b).symm.trans (sum_univ_eq_weight b)

omit [IsNoetherianRing k] in
lemma homogeneousSubmodule_le_restrictTotalDegree (m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m
      ≤ MvPolynomial.restrictTotalDegree (Fin (n + 1)) k m := by
  intro p hp
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact hp.totalDegree_le

omit [IsNoetherianRing k] in
instance finiteDimensional_polySubmodule (d : ℤ) :
    Module.Finite k (polySubmodule k n d) := by
  rcases lt_or_ge d 0 with h | h
  · rw [polySubmodule_of_neg k n h]
    infer_instance
  · rw [polySubmodule_of_nonneg k n h]
    infer_instance

omit [IsNoetherianRing k] in
instance finiteDimensional_structureModule_obj (d : ℤ) :
    Module.Finite k ((structureModule k n).obj d) :=
  finiteDimensional_polySubmodule d

/-! ## Finite generation -/

/-- A graded module is **finitely generated** when its pieces are finite dimensional, it
vanishes in all sufficiently negative degrees, and from some degree on each piece is spanned
by the variables acting on the previous one.

The two bounds must be kept **separate**: `S ⊕ S(-5)` vanishes below degree `0` but is not
generated from degree `0` on (its degree-`5` piece needs a new generator), so tying them
together would exclude a finite direct sum of twists. -/
def IsFG (M : GradedModule k n) : Prop :=
  (∀ d : ℤ, Module.Finite k (M.obj d)) ∧
  (∃ a : ℤ, ∀ d : ℤ, d < a → Subsingleton (M.obj d)) ∧
  (∃ b : ℤ, ∀ d : ℤ, b ≤ d → M.mulSpan d (d + 1) = ⊤)

/-! ## The structure sheaf -/

lemma exists_pos_of_degree_pos {b : Fin (n + 1) →₀ ℕ} (hb : 1 ≤ b.degree) :
    ∃ i : Fin (n + 1), 1 ≤ b i := by
  by_contra hc
  simp only [not_exists, Nat.lt_one_iff, Nat.not_le] at hc
  have hb0 : b = 0 := Finsupp.ext fun i => by have := hc i; omega
  rw [hb0] at hb
  simp at hb

omit [IsNoetherianRing k] in
/-- Every form of positive degree is a linear combination of variables times forms of one
degree less: the graded pieces of `S` are generated by the previous one. -/
lemma structureModule_mulSpan_succ (d : ℤ) (hd : 0 ≤ d) :
    (structureModule k n).mulSpan d (d + 1) = ⊤ := by
  classical
  -- every monomial of degree `d+1` is a variable times a monomial of degree `d`
  have hmono : ∀ (b : Fin (n + 1) →₀ ℕ) (c : k)
      (hb : (monomial b c : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n (d + 1)),
      (⟨monomial b c, hb⟩ : (structureModule k n).obj (d + 1))
        ∈ (structureModule k n).mulSpan d (d + 1) := by
    intro b c hb
    rcases eq_or_ne c 0 with rfl | hc
    · have : (⟨monomial b (0 : k), hb⟩ : (structureModule k n).obj (d + 1)) = 0 :=
        Subtype.ext (by simp)
      rw [this]
      exact Submodule.zero_mem _
    have hdeg : b.degree = (d + 1).toNat := by
      have hbmem : (monomial b c : MvPolynomial (Fin (n + 1)) k).IsHomogeneous (d + 1).toNat := by
        rw [polySubmodule_of_nonneg k n (by omega), MvPolynomial.mem_homogeneousSubmodule] at hb
        exact hb
      have hcoeff : coeff b (monomial b c : MvPolynomial (Fin (n + 1)) k) ≠ 0 := by
        rw [coeff_monomial]
        simpa using hc
      have hw := hbmem hcoeff
      rw [← degree_eq_weight_one] at hw
      exact hw
    have hdpos : 1 ≤ b.degree := by omega
    obtain ⟨i, hi⟩ := exists_pos_of_degree_pos hdpos
    have hle : (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) ≤ b := by
      rw [Finsupp.single_le_iff]
      exact hi
    set b' : Fin (n + 1) →₀ ℕ := b - Finsupp.single i 1 with hb'
    have hsum : (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) + b' = b := by
      rw [hb', add_tsub_cancel_of_le hle]
    have hb'deg : b'.degree = d.toNat := by
      have hd1 : (Finsupp.degree (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ)) = 1 := by simp
      have := congrArg Finsupp.degree hsum
      rw [map_add, hd1, hdeg] at this
      omega
    have hb'mem : (monomial b' c : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n d := by
      rw [polySubmodule_of_nonneg k n hd, MvPolynomial.mem_homogeneousSubmodule]
      refine isHomogeneous_monomial c ?_
      exact hb'deg
    have hval : (((structureModule k n).mulX' i d (d + 1) rfl).hom
        ⟨monomial b' c, hb'mem⟩ : (structureModule k n).obj (d + 1))
          = ⟨monomial b c, hb⟩ := by
      refine Subtype.ext ?_
      rw [structureModule_mulX'_val]
      show (X i : MvPolynomial (Fin (n + 1)) k) * monomial b' c = monomial b c
      rw [X, monomial_mul, one_mul, hsum]
    rw [← hval]
    exact range_mulX'_le_mulSpan (structureModule k n) i d (d + 1) rfl
      (LinearMap.mem_range_self _ _)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨p, hp⟩ := x
  have hmem : ∀ b ∈ p.support,
      (monomial b (coeff b p) : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n (d + 1) := by
    intro b hbsupp
    rw [polySubmodule_of_nonneg k n (by omega), MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    refine isHomogeneous_monomial _ ?_
    have hw := hp (MvPolynomial.mem_support_iff.mp hbsupp)
    rw [← degree_eq_weight_one] at hw
    exact hw
  have hx : (⟨p, hp⟩ : (structureModule k n).obj (d + 1))
      = ∑ b ∈ p.support.attach, (⟨monomial b.1 (coeff b.1 p), hmem b.1 b.2⟩ :
          (structureModule k n).obj (d + 1)) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum,
      Finset.sum_attach p.support
        (fun b => (monomial b (coeff b p) : MvPolynomial (Fin (n + 1)) k))]
    exact MvPolynomial.as_sum p
  rw [hx]
  exact Submodule.sum_mem _ fun b _ => hmono b.1 (coeff b.1 p) (hmem b.1 b.2)

/-! ## Closure properties -/

omit [IsNoetherianRing k] in
lemma subsingleton_polySubmodule_lt_zero {d : ℤ} (hd : d < 0) :
    Subsingleton (polySubmodule k n d) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [polySubmodule_of_neg k n hd, Submodule.mem_bot] at hx hy
  exact Subtype.ext (hx.trans hy.symm)

omit [IsNoetherianRing k] in
/-- The structure sheaf is finitely generated. -/
lemma isFG_structureModule : IsFG (structureModule k n) :=
  ⟨fun _ => inferInstance, ⟨0, fun _ hd => subsingleton_polySubmodule_lt_zero hd⟩,
    ⟨0, fun d hd => structureModule_mulSpan_succ d hd⟩⟩

omit [IsNoetherianRing k] in
/-- Multiplication spans transport across a twist. -/
lemma twist_mulSpan (M : GradedModule k n) (a d e : ℤ) :
    (M.twist a).mulSpan d e = M.mulSpan (d + a) (e + a) := by
  refine le_antisymm (iSup_le fun l => ?_) (iSup_le fun l => ?_)
  · have heq : (M.twist a).mulList l.1 d e l.2
        = M.mulList l.1 (d + a) (e + a) (by omega) := twist_mulList M a l.1 d e l.2
    rw [heq]
    exact le_mulSpan M (d + a) (e + a) l.1 (by omega)
  · have heq : M.mulList l.1 (d + a) (e + a) l.2
        = (M.twist a).mulList l.1 d e (by omega) :=
      (twist_mulList M a l.1 d e (by omega)).symm
    rw [heq]
    exact le_mulSpan (M.twist a) d e l.1 (by omega)

omit [IsNoetherianRing k] in
/-- Twists of finitely generated modules are finitely generated. -/
lemma IsFG.twist {M : GradedModule k n} (hM : IsFG M) (a : ℤ) : IsFG (M.twist a) := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := hM
  refine ⟨fun d => hfd (d + a), ⟨lo - a, fun d hd => hlow (d + a) (by omega)⟩,
    ⟨hi - a, fun d hd => ?_⟩⟩
  have key : ∀ e e' : ℤ, e = e' → M.mulSpan (d + a) e = ⊤ → M.mulSpan (d + a) e' = ⊤ := by
    intro e e' hee h
    subst hee
    exact h
  rw [twist_mulSpan]
  exact key _ _ (by ring) (hgen (d + a) (by omega))

omit [IsNoetherianRing k] in
/-- Cokernels of maps into a finitely generated module are finitely generated. -/
lemma IsFG.coker {M N : GradedModule k n} (f : M ⟶ N) (hN : IsFG N) :
    IsFG (GradedModule.coker f) := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := hN
  refine ⟨fun d => ?_, ⟨lo, fun d hd => ?_⟩, ⟨hi, fun d hd => ?_⟩⟩
  · haveI := hfd d
    exact Module.Finite.quotient k _
  · haveI := hlow d hd
    constructor
    intro x y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim a b]
  · exact mulSpan_eq_top_of_surjective (toCoker f)
      (fun e => surjective_toCoker_app f e) d (d + 1) (hgen d hd)

omit [IsNoetherianRing k] in
/-- Multiplication spans are carried into multiplication spans by any morphism. -/
lemma mulSpan_map_le {M N : GradedModule k n} (f : M ⟶ N) (d e : ℤ) :
    Submodule.map (f.app e).hom (M.mulSpan d e) ≤ N.mulSpan d e := by
  rw [Submodule.map_le_iff_le_comap, mulSpan]
  refine iSup_le fun l => ?_
  rintro y ⟨z, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  have hc := congrArg (fun g : M.obj d ⟶ N.obj e => g.hom z) (comm_mulList f l.1 d e l.2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  rw [← hc]
  exact le_mulSpan N d e l.1 l.2 (LinearMap.mem_range_self _ _)

omit [IsNoetherianRing k] in
/-- Finite direct sums of finitely generated modules are finitely generated. -/
lemma IsFG.pow {M : GradedModule k n} (hM : IsFG M) (r : ℕ) : IsFG (M.pow r) := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := hM
  refine ⟨fun d => ?_, ⟨lo, fun d hd => ?_⟩, ⟨hi, fun d hd => ?_⟩⟩
  · haveI := hfd d
    exact inferInstanceAs (Module.Finite k (Fin r → M.obj d))
  · haveI := hlow d hd
    exact inferInstanceAs (Subsingleton (Fin r → M.obj d))
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = ∑ t : Fin r, ((M.powCoord r t).app (d + 1)).hom (x t) :=
      (Finset.univ_sum_single x).symm
    rw [hx]
    refine Submodule.sum_mem _ fun t _ => ?_
    refine mulSpan_map_le (M.powCoord r t) d (d + 1) ⟨x t, ?_, rfl⟩
    rw [hgen d hd]
    trivial

/-! ## Restriction to a hyperplane -/

omit [IsNoetherianRing k] in
/-- Between consecutive degrees the multiplication span is the span of the images of the
individual variables. -/
lemma mulSpan_succ_eq_iSup (M : GradedModule k n) (d : ℤ) :
    M.mulSpan d (d + 1) = ⨆ i : Fin (n + 1), LinearMap.range (M.mulX' i d (d + 1) rfl).hom := by
  refine le_antisymm (iSup_le fun l => ?_) (iSup_le fun i => ?_)
  · obtain ⟨lst, hlst⟩ := l
    obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), lst = [i] := by
      have hlen : lst.length = 1 := by omega
      exact List.length_eq_one_iff.mp hlen
    have heq : M.mulList [i] d (d + 1) hlst = M.mulX' i d (d + 1) rfl :=
      mulList_singleton M i d (d + 1) hlst
    rw [heq]
    exact le_iSup (fun i : Fin (n + 1) =>
      LinearMap.range (M.mulX' i d (d + 1) rfl).hom) i
  · exact range_mulX'_le_mulSpan M i d (d + 1) rfl

omit [IsNoetherianRing k] in
/-- On a module killed by the linear form `L = ∑ cᵢxᵢ` with `c_j` a unit, multiplication by
`x_j` is a combination of the other variables. -/
lemma range_mulX'_le_iSup_succAbove {N : GradedModule k (n + 1)} (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hkill : ∀ (d e : ℤ) (h : d + 1 = e), N.mulL c d e h = 0) (d : ℤ) :
    LinearMap.range (N.mulX' j d (d + 1) rfl).hom
      ≤ ⨆ i : Fin (n + 1),
          LinearMap.range (N.mulX' (j.succAbove i) d (d + 1) rfl).hom := by
  rintro _ ⟨x, rfl⟩
  set U : Submodule k (N.obj (d + 1)) := ⨆ i : Fin (n + 1),
    LinearMap.range (N.mulX' (j.succAbove i) d (d + 1) rfl).hom with hU
  have hzero : (0 : N.obj (d + 1)) = ∑ i, c i • (N.mulX' i d (d + 1) rfl).hom x := by
    rw [← mulL_apply N c d (d + 1) rfl x, hkill d (d + 1) rfl]
    rfl
  rw [Fin.sum_univ_succAbove _ j] at hzero
  have hrest : (∑ i : Fin (n + 1),
      c (j.succAbove i) • (N.mulX' (j.succAbove i) d (d + 1) rfl).hom x) ∈ U :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (le_iSup (fun i : Fin (n + 1) =>
        LinearMap.range (N.mulX' (j.succAbove i) d (d + 1) rfl).hom) i
        (LinearMap.mem_range_self _ _))
  have hjmem : c j • (N.mulX' j d (d + 1) rfl).hom x ∈ U := by
    have heq : c j • (N.mulX' j d (d + 1) rfl).hom x
        = -(∑ i : Fin (n + 1),
            c (j.succAbove i) • (N.mulX' (j.succAbove i) d (d + 1) rfl).hom x) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero.symm
    rw [heq]
    exact Submodule.neg_mem _ hrest
  obtain ⟨u, hu⟩ := hj
  have hsm : (N.mulX' j d (d + 1) rfl).hom x
      = ((↑u⁻¹ : k)) • (c j • (N.mulX' j d (d + 1) rfl).hom x) := by
    rw [smul_smul, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hsm]
  exact Submodule.smul_mem _ _ hjmem

omit [IsNoetherianRing k] in
/-- A finitely generated module killed by a linear form is finitely generated on the
hyperplane. -/
lemma IsFG.dropVar {N : GradedModule k (n + 1)} (hN : IsFG N) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hkill : ∀ (d e : ℤ) (h : d + 1 = e), N.mulL c d e h = 0) : IsFG (N.dropVar j) := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := hN
  refine ⟨hfd, ⟨lo, hlow⟩, ⟨hi, fun d hd => ?_⟩⟩
  have hdrop : (N.dropVar j).mulSpan d (d + 1)
      = ⨆ i : Fin (n + 1),
          LinearMap.range (N.mulX' (j.succAbove i) d (d + 1) rfl).hom := by
    rw [mulSpan_succ_eq_iSup]
    refine iSup_congr fun i => ?_
    congr 1
  rw [hdrop, eq_top_iff, ← hgen d hd, mulSpan_succ_eq_iSup]
  refine iSup_le fun i => ?_
  rcases eq_or_ne i j with rfl | hij
  · exact range_mulX'_le_iSup_succAbove c i hj hkill d
  · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hij
    exact le_iSup (fun t : Fin (n + 1) =>
      LinearMap.range (N.mulX' (j.succAbove t) d (d + 1) rfl).hom) i'

omit [IsNoetherianRing k] in
/-- Finite generation descends from the drop-variable module: the multiplication span only
grows when the variable `x_j` is put back. -/
lemma IsFG.of_dropVar {N : GradedModule k (n + 1)} (j : Fin (n + 2))
    (h : IsFG (N.dropVar j)) : IsFG N := by
  obtain ⟨hfd, ⟨lo, hlow⟩, ⟨hi, hgen⟩⟩ := h
  refine ⟨hfd, ⟨lo, hlow⟩, ⟨hi, fun d hd => ?_⟩⟩
  exact eq_top_iff.mpr ((hgen d hd) ▸ dropVar_mulSpan_le N j d (d + 1))

/-! ## Irrelevant torsion -/

/-- A graded module has **no irrelevant torsion** when no nonzero element is killed by a
power of every variable — that is, `H⁰_m(M) = 0`.  This is the condition under which a
general hyperplane is a nonzerodivisor; a module of finite length fails it completely, while
being invisible to cohomology. -/
def NoIrrelevantTorsion (M : GradedModule k n) : Prop :=
  ∀ (d : ℤ) (x : M.obj d),
    (∀ i : Fin (n + 1), ∃ m : ℕ,
      (M.mulList (listPow [i] m) d (d + (m : ℤ)) (by simp)).hom x = 0) → x = 0

omit [IsNoetherianRing k] in
/-- The product of a single variable repeated `m` times is its `m`-th power. -/
lemma prod_map_X_listPow_singleton (i : Fin (n + 1)) (m : ℕ) :
    ((listPow [i] m).map (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)).prod
      = (MvPolynomial.X i) ^ m := by
  have hrep : listPow [i] m = List.replicate m i := by
    induction m with
    | zero => simp [listPow]
    | succ t ih =>
        rw [show t + 1 = 1 + t from by omega, listPow_add, ih,
          show (listPow [i] 1 : List (Fin (n + 1))) = [i] from by simp [listPow]]
        simp [List.replicate_succ, List.replicate_add]
  rw [hrep, List.map_replicate, List.prod_replicate]

omit [IsNoetherianRing k] in
/-- Finite direct sums of the structure sheaf have no irrelevant torsion: the polynomial ring
is a domain. -/
lemma noIrrelevantTorsion_pow_structureModule [IsDomain k] (r : ℕ) :
    NoIrrelevantTorsion ((structureModule k n).pow r) := by
  intro d x hx
  obtain ⟨m, hm⟩ := hx 0
  funext t
  have hcomp : (((structureModule k n).pow r).mulList (listPow [0] m) d (d + (m : ℤ))
      (by simp)).hom x t = 0 :=
    congrArg (fun y : ((structureModule k n).pow r).obj (d + (m : ℤ)) => y t) hm
  have hval : (((structureModule k n).pow r).mulList (listPow [0] m) d (d + (m : ℤ))
      (by simp)).hom x t
      = ((structureModule k n).mulList (listPow [0] m) d (d + (m : ℤ)) (by simp)).hom (x t) :=
    pow_mulList (structureModule k n) r (listPow [(0 : Fin (n + 1))] m) d (d + (m : ℤ))
      (by simp) x t
  rw [hval] at hcomp
  have hpoly : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ m
      * (x t).1 = 0 := by
    have := congrArg Subtype.val hcomp
    rw [structureModule_mulList_val k n (listPow [0] m) d (d + (m : ℤ)) (by simp) (x t),
      prod_map_X_listPow_singleton] at this
    simpa using this
  have hXne : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ m ≠ 0 :=
    pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  rcases mul_eq_zero.mp hpoly with h0 | h0
  · exact absurd h0 hXne
  · exact Subtype.ext h0

/-! ## Multiplication by a monomial -/

/-- The list of variables of a monomial, with multiplicities. -/
def monoList (b : Fin (n + 1) →₀ ℕ) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).flatMap fun i => List.replicate (b i) i

lemma coe_flatMap_replicate (l : List (Fin (n + 1))) (b : Fin (n + 1) →₀ ℕ) :
    ((l.flatMap fun i => List.replicate (b i) i : List (Fin (n + 1))) :
        Multiset (Fin (n + 1)))
      = (l.map fun i => Multiset.replicate (b i) i).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]
      congr 1

lemma monoList_coe (b : Fin (n + 1) →₀ ℕ) :
    ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = ∑ i : Fin (n + 1), Multiset.replicate (b i) i := by
  rw [monoList, coe_flatMap_replicate, List.finRange, List.map_ofFn, List.sum_ofFn]
  rfl

lemma monoList_length (b : Fin (n + 1) →₀ ℕ) : (monoList b).length = b.degree := by
  have h1 : Multiset.card ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = (monoList b).length := rfl
  have hcard : ∀ s : Finset (Fin (n + 1)),
      Multiset.card (∑ i ∈ s, Multiset.replicate (b i) i) = ∑ i ∈ s, b i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.card_add,
          Multiset.card_replicate, ih]
  rw [← h1, monoList_coe, hcard, ← sum_univ_eq_degree]

lemma monoList_add_single (b : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) :
    ((monoList (b + Finsupp.single i 1) : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = i ::ₘ ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1))) := by
  classical
  rw [monoList_coe, monoList_coe]
  have hterm : ∀ j : Fin (n + 1),
      Multiset.replicate ((b + Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) j) j
        = Multiset.replicate (b j) j
          + Multiset.replicate ((Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) j) j := by
    intro j
    rw [Finsupp.add_apply, Multiset.replicate_add]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  have hsingle : ∑ j : Fin (n + 1),
      Multiset.replicate ((Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) j) j = {i} := by
    rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [Finsupp.single_apply]
      simp only [(Ne.symm hj : ¬ (i = j)), ↓reduceIte, Multiset.replicate_zero])
      (fun hc => absurd (Finset.mem_univ i) hc)]
    rw [Finsupp.single_eq_same]
    rfl
  rw [hsingle, add_comm (∑ j : Fin (n + 1), Multiset.replicate (b j) j)
    ({i} : Multiset (Fin (n + 1))), Multiset.singleton_add]

/-- Multiplication by the monomial `x^b`. -/
noncomputable def mulMono (M : GradedModule k n) (b : Fin (n + 1) →₀ ℕ) (d e : ℤ)
    (h : d + (b.degree : ℤ) = e) : M.obj d ⟶ M.obj e :=
  M.mulList (monoList b) d e (by rw [monoList_length]; exact h)

omit [IsNoetherianRing k] in
/-- Multiplying by `x^b` and then by `xᵢ` is multiplying by `x^{b + eᵢ}`. -/
lemma mulMono_mulX' (M : GradedModule k n) (b : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1))
    (d e f : ℤ) (h : d + (b.degree : ℤ) = e) (h' : e + 1 = f)
    (h'' : d + (((b + Finsupp.single i 1).degree : ℕ) : ℤ) = f) :
    M.mulMono b d e h ≫ M.mulX' i e f h' = M.mulMono (b + Finsupp.single i 1) d f h'' := by
  have hlen : d + ((monoList b ++ [i]).length : ℤ) = f := by
    rw [List.length_append, monoList_length]
    simp only [List.length_singleton, Nat.cast_add, Nat.cast_one]
    omega
  have hstep : M.mulMono b d e h ≫ M.mulX' i e f h'
      = M.mulList (monoList b ++ [i]) d f hlen := by
    rw [mulMono, show M.mulX' i e f h' = M.mulList [i] e f (by simpa using h') from
      (mulList_singleton M i e f (by simpa using h')).symm]
    exact (M.mulList_append (monoList b) [i] d e f _ _ hlen).symm
  rw [hstep, mulMono]
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, monoList_add_single,
    add_comm ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      (([i] : List (Fin (n + 1))) : Multiset (Fin (n + 1)))]
  rfl

/-! ## Multiplication by a homogeneous polynomial -/

/-- Multiplication by a form of degree `D`, as a `k`-bilinear operation.  The sum runs over
*all* exponent vectors of degree `D` — a finite type — rather than over the support of `p`,
which is what makes linearity in `p` immediate. -/
noncomputable def mulForm (M : GradedModule k n) (D : ℕ) (d e : ℤ) (h : d + (D : ℤ) = e) :
    polySubmodule k n (D : ℤ) →ₗ[k] (M.obj d →ₗ[k] M.obj e) where
  toFun p := ∑ b : ↥{b : Fin (n + 1) →₀ ℕ | b.degree = D},
    (MvPolynomial.coeff b.1 p.1) • (M.mulMono b.1 d e (by
      have hb : b.1.degree = D := b.2
      rw [hb]
      exact h)).hom
  map_add' p q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show ((p + q : polySubmodule k n (D : ℤ)) : MvPolynomial (Fin (n + 1)) k)
      = p.1 + q.1 from rfl, MvPolynomial.coeff_add, add_smul]
  map_smul' c p := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show ((c • p : polySubmodule k n (D : ℤ)) : MvPolynomial (Fin (n + 1)) k)
      = c • p.1 from rfl, MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

omit [IsNoetherianRing k] in
lemma mulForm_apply (M : GradedModule k n) (D : ℕ) (d e : ℤ) (h : d + (D : ℤ) = e)
    (p : polySubmodule k n (D : ℤ)) (x : M.obj d) :
    mulForm M D d e h p x
      = ∑ b : ↥{b : Fin (n + 1) →₀ ℕ | b.degree = D},
          (MvPolynomial.coeff b.1 p.1) • (M.mulMono b.1 d e (by
            have hb : b.1.degree = D := b.2
            rw [hb]
            exact h)).hom x := by
  rw [mulForm]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact LinearMap.sum_apply _ _ _

omit [IsNoetherianRing k] in
/-- The form action is compatible with multiplication by a variable: this is what makes it a
morphism of graded modules. -/
lemma mulForm_mulX' (M : GradedModule k n) (D : ℕ) (d e f : ℤ) (h : d + (D : ℤ) = e)
    (h' : e + 1 = f) (h'' : d + ((D + 1 : ℕ) : ℤ) = f) (i : Fin (n + 1))
    (p : polySubmodule k n (D : ℤ)) (q : polySubmodule k n ((D + 1 : ℕ) : ℤ))
    (hq : q.1 = MvPolynomial.X i * p.1) (x : M.obj d) :
    (M.mulX' i e f h').hom (mulForm M D d e h p x) = mulForm M (D + 1) d f h'' q x := by
  classical
  rw [mulForm_apply, mulForm_apply, map_sum]
  refine Finset.sum_of_injOn
    (fun b : ↥{b : Fin (n + 1) →₀ ℕ | b.degree = D} =>
      (⟨b.1 + Finsupp.single i 1, by
        show (b.1 + Finsupp.single i 1).degree = D + 1
        rw [map_add, (b.2 : b.1.degree = D), Finsupp.degree_single]⟩ :
          ↥{b' : Fin (n + 1) →₀ ℕ | b'.degree = D + 1}))
    (fun a _ b _ hab => ?_) (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun b' _ hb' => ?_) (fun b _ => ?_)
  · refine Subtype.ext ?_
    have h1 : a.1 + Finsupp.single i 1 = b.1 + Finsupp.single i 1 := congrArg Subtype.val hab
    exact add_right_cancel h1
  · -- exponent vectors not divisible by `xᵢ` contribute nothing
    have hi0 : b'.1 i = 0 := by
      by_contra hc
      refine hb' ⟨⟨b'.1 - Finsupp.single i 1, ?_⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      · show (b'.1 - Finsupp.single i 1).degree = D
        have hle : (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) ≤ b'.1 :=
          Finsupp.single_le_iff.mpr (by omega)
        have hadd : (b'.1 - Finsupp.single i 1) + Finsupp.single i 1 = b'.1 :=
          tsub_add_cancel_of_le hle
        have hdeg := congrArg Finsupp.degree hadd
        rw [map_add, Finsupp.degree_single, (b'.2 : b'.1.degree = D + 1)] at hdeg
        omega
      · refine Subtype.ext ?_
        exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))
    have hcoeff : MvPolynomial.coeff b'.1 q.1 = 0 := by
      rw [hq, MvPolynomial.coeff_X_mul']
      simp only [Finsupp.mem_support_iff, hi0, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [hcoeff, zero_smul]
  · -- the matching term
    have hbd : b.1.degree = D := b.2
    have hp1 : d + ((b.1.degree : ℕ) : ℤ) = e := by rw [hbd]; exact h
    have hp2 : d + (((b.1 + Finsupp.single i 1).degree : ℕ) : ℤ) = f := by
      rw [map_add, hbd, Finsupp.degree_single]
      push_cast
      omega
    have hc : MvPolynomial.coeff (b.1 + Finsupp.single i 1) q.1
        = MvPolynomial.coeff b.1 p.1 := by
      rw [hq, show b.1 + Finsupp.single i 1 = Finsupp.single i 1 + b.1 from add_comm _ _,
        MvPolynomial.coeff_X_mul]
    have hm := congrArg (fun g : M.obj d ⟶ M.obj f => g.hom x)
      (M.mulMono_mulX' b.1 i d e f hp1 h' hp2)
    rw [map_smul, hc, ← hm]
    rfl

/-! ## Comparing list multiplication with the monomial action -/

lemma listExp_apply (L : List (Fin (n + 1))) (i : Fin (n + 1)) :
    listExp L i = L.count i := by
  classical
  induction L with
  | nil => simp [listExp]
  | cons j t ih =>
      rw [listExp_cons, Finsupp.add_apply, ih, List.count_cons, Finsupp.single_apply]
      rcases eq_or_ne j i with rfl | hji
      · simp only [↓reduceIte, beq_self_eq_true]
        omega
      · simp only [hji, ↓reduceIte, zero_add, beq_iff_eq, ↓reduceIte, add_zero]

lemma monoList_listExp_coe (l : List (Fin (n + 1))) :
    ((monoList (listExp l) : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = (l : Multiset (Fin (n + 1))) := by
  classical
  rw [monoList_coe]
  refine Multiset.ext.mpr fun j => ?_
  rw [Multiset.count_sum', Multiset.coe_count,
    Finset.sum_eq_single j (fun i _ hi => by
      simp [Multiset.count_replicate, Ne.symm hi, hi])
      (fun hc => absurd (Finset.mem_univ j) hc)]
  rw [Multiset.count_replicate]
  simp only [↓reduceIte]
  exact listExp_apply l j

omit [IsNoetherianRing k] in
/-- Multiplying along a list is multiplying by the corresponding monomial. -/
lemma mulList_eq_mulMono (M : GradedModule k n) (l : List (Fin (n + 1))) (d e : ℤ)
    (h : d + (l.length : ℤ) = e) (h' : d + ((listExp l).degree : ℤ) = e) :
    M.mulList l d e h = M.mulMono (listExp l) d e h' := by
  refine mulList_perm M ?_ _ _ _ _
  rw [← Multiset.coe_eq_coe, monoList_listExp_coe]

omit [IsNoetherianRing k] in
/-- The form action on a monomial is a scalar multiple of the monomial action. -/
lemma mulForm_monomial (M : GradedModule k n) (D : ℕ) (d e : ℤ) (h : d + (D : ℤ) = e)
    (b : Fin (n + 1) →₀ ℕ) (hb : b.degree = D) (c : k)
    (hm : (MvPolynomial.monomial b c : MvPolynomial (Fin (n + 1)) k)
      ∈ polySubmodule k n (D : ℤ)) (x : M.obj d) :
    mulForm M D d e h ⟨MvPolynomial.monomial b c, hm⟩ x
      = c • (M.mulMono b d e (by rw [hb]; exact h)).hom x := by
  classical
  rw [mulForm_apply,
    Finset.sum_eq_single (⟨b, hb⟩ : ↥{b : Fin (n + 1) →₀ ℕ | b.degree = D})
      (fun a _ ha => by
        have hne : ¬ (b = a.1) := fun hc => ha (Subtype.ext hc.symm)
        rw [show (MvPolynomial.coeff a.1
            (⟨MvPolynomial.monomial b c, hm⟩ : polySubmodule k n (D : ℤ)).1)
          = MvPolynomial.coeff a.1 (MvPolynomial.monomial b c) from rfl,
          MvPolynomial.coeff_monomial]
        simp only [hne, ↓reduceIte, zero_smul])
      (fun hc => absurd (Finset.mem_univ _) hc)]
  rw [show (MvPolynomial.coeff b
      (⟨MvPolynomial.monomial b c, hm⟩ : polySubmodule k n (D : ℤ)).1)
    = MvPolynomial.coeff b (MvPolynomial.monomial b c) from rfl,
    MvPolynomial.coeff_monomial]
  simp only [↓reduceIte]

/-! ## The comparison map from a finite family of generators -/

/-- The map `(pₜ) ↦ ∑ₜ pₜ · yₜ` from forms of degree `D` in `r` variables to the degree
`d₀ + D` piece, attached to a family `y` in degree `d₀`. -/
noncomputable def genMap (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀)
    (D : ℕ) : (Fin r → polySubmodule k n (D : ℤ)) →ₗ[k] M.obj (d₀ + (D : ℤ)) :=
  ∑ t : Fin r, ((mulForm M D d₀ (d₀ + (D : ℤ)) rfl).flip (y t)).comp (LinearMap.proj t)

omit [IsNoetherianRing k] in
lemma genMap_apply (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀)
    (D : ℕ) (p : Fin r → polySubmodule k n (D : ℤ)) :
    genMap M d₀ y D p = ∑ t : Fin r, mulForm M D d₀ (d₀ + (D : ℤ)) rfl (p t) (y t) := by
  rw [genMap, LinearMap.sum_apply]
  rfl

omit [IsNoetherianRing k] in
/-- Iterating the generation condition: every piece above `d₀` is spanned from degree `d₀`. -/
lemma mulSpan_of_gen (M : GradedModule k n) (d₀ : ℤ)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) (D : ℕ) :
    M.mulSpan d₀ (d₀ + (D : ℤ)) = ⊤ := by
  induction D with
  | zero =>
      rw [Nat.cast_zero, add_zero]
      exact mulSpan_self M d₀
  | succ t ih =>
      have hstep : M.mulSpan (d₀ + (t : ℤ)) (d₀ + (t : ℤ) + 1) = ⊤ :=
        hgen (d₀ + (t : ℤ)) (by omega)
      have h := mulSpan_trans M ih hstep
      have heq : d₀ + (t : ℤ) + 1 = d₀ + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [heq] at h
      exact h

omit [IsNoetherianRing k] in
/-- If `y` spans the degree-`d₀` piece and the module is generated from `d₀` on, the
comparison map is surjective in every degree above `d₀`. -/
lemma surjective_genMap (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀)
    (hy : Submodule.span k (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) (D : ℕ) :
    Function.Surjective (genMap M d₀ y D) := by
  classical
  rw [← LinearMap.range_eq_top]
  refine eq_top_iff.mpr ?_
  rw [← mulSpan_of_gen M d₀ hgen D]
  refine iSup_le fun l => ?_
  rintro _ ⟨z, rfl⟩
  -- express `z` in terms of the spanning family
  obtain ⟨c, hc⟩ : ∃ c : Fin r → k, ∑ t, c t • y t = z := by
    have hz : z ∈ Submodule.span k (Set.range y) := by rw [hy]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun k).mp hz
  have hlen : (listExp l.1).degree = D := by
    rw [← monoList_length]
    have h2 : (monoList (listExp l.1)).length = l.1.length := by
      have := monoList_listExp_coe l.1
      have hc2 := congrArg Multiset.card this
      simpa using hc2
    have h3 : l.1.length = D := by
      have := l.2
      omega
    rw [monoList_length] at h2 ⊢
    omega
  have hdeg : d₀ + ((listExp l.1).degree : ℤ) = d₀ + (D : ℤ) := by rw [hlen]
  have hmem : ∀ t : Fin r,
      (MvPolynomial.monomial (listExp l.1) (c t) : MvPolynomial (Fin (n + 1)) k)
        ∈ polySubmodule k n (D : ℤ) := by
    intro t
    rw [polySubmodule_of_nonneg k n (by positivity), MvPolynomial.mem_homogeneousSubmodule]
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [hlen]
    simp
  refine ⟨fun t => ⟨MvPolynomial.monomial (listExp l.1) (c t), hmem t⟩, ?_⟩
  rw [genMap_apply]
  have hterm : ∀ t : Fin r,
      mulForm M D d₀ (d₀ + (D : ℤ)) rfl
          ⟨MvPolynomial.monomial (listExp l.1) (c t), hmem t⟩ (y t)
        = c t • (M.mulMono (listExp l.1) d₀ (d₀ + (D : ℤ)) hdeg).hom (y t) := by
    intro t
    exact mulForm_monomial M D d₀ (d₀ + (D : ℤ)) rfl (listExp l.1) hlen (c t) (hmem t) (y t)
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  have hml : M.mulList l.1 d₀ (d₀ + (D : ℤ)) l.2
      = M.mulMono (listExp l.1) d₀ (d₀ + (D : ℤ)) hdeg :=
    mulList_eq_mulMono M l.1 d₀ (d₀ + (D : ℤ)) l.2 hdeg
  rw [hml, ← hc, map_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [map_smul]

omit [IsNoetherianRing k] in
/-- The comparison map intertwines multiplication by a variable. -/
lemma genMap_mulX' (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀)
    (D : ℕ) (i : Fin (n + 1)) (p : Fin r → polySubmodule k n (D : ℤ))
    (q : Fin r → polySubmodule k n ((D + 1 : ℕ) : ℤ))
    (hq : ∀ t, (q t).1 = MvPolynomial.X i * (p t).1)
    (hstep : d₀ + (D : ℤ) + 1 = d₀ + ((D + 1 : ℕ) : ℤ)) :
    (M.mulX' i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep).hom (genMap M d₀ y D p)
      = genMap M d₀ y (D + 1) q := by
  rw [genMap_apply, genMap_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact mulForm_mulX' M D d₀ (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) rfl hstep rfl i
    (p t) (q t) (hq t) (y t)

/-! ## The preimage family of a subobject -/

section Noetherian

variable {M N : GradedModule k n}

/-- Multiplying a tuple of forms of degree `D` by the variable `xᵢ`. -/
noncomputable def smulXTuple {r : ℕ} (i : Fin (n + 1)) (D : ℕ)
    (p : Fin r → polySubmodule k n (D : ℤ)) :
    Fin r → polySubmodule k n ((D + 1 : ℕ) : ℤ) := fun t =>
  ⟨MvPolynomial.X i * (p t).1, by
    have hmem := X_mul_mem_polySubmodule k n i (D : ℤ) (p t).2
    have hcast : ((D : ℤ) + 1) = ((D + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at hmem
    exact hmem⟩

omit [IsNoetherianRing k] in
@[simp] lemma smulXTuple_val {r : ℕ} (i : Fin (n + 1)) (D : ℕ)
    (p : Fin r → polySubmodule k n (D : ℤ)) (t : Fin r) :
    (smulXTuple i D p t).1 = MvPolynomial.X i * (p t).1 := rfl

/-- The forms of degree `D` whose value under the comparison map lands in the subobject
`M ⊆ N`. -/
noncomputable def genPre (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ) :
    Submodule k (Fin r → polySubmodule k n (D : ℤ)) :=
  Submodule.comap (genMap N d₀ y D) (LinearMap.range (f.app (d₀ + (D : ℤ))).hom)

omit [IsNoetherianRing k] in
lemma mem_genPre_iff (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ)
    (p : Fin r → polySubmodule k n (D : ℤ)) :
    p ∈ genPre f d₀ y D ↔
      genMap N d₀ y D p ∈ LinearMap.range (f.app (d₀ + (D : ℤ))).hom := Iff.rfl

omit [IsNoetherianRing k] in
/-- The preimage family is closed under multiplication by a variable. -/
lemma genPre_smulXTuple (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ)
    (i : Fin (n + 1)) {p : Fin r → polySubmodule k n (D : ℤ)}
    (hp : p ∈ genPre f d₀ y D) : smulXTuple i D p ∈ genPre f d₀ y (D + 1) := by
  obtain ⟨x, hx⟩ := hp
  have hstep : d₀ + (D : ℤ) + 1 = d₀ + ((D + 1 : ℕ) : ℤ) := by push_cast; ring
  refine ⟨(M.mulX' i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep).hom x, ?_⟩
  have hcomm := congrArg (fun g : M.obj (d₀ + (D : ℤ)) ⟶ N.obj (d₀ + ((D + 1 : ℕ) : ℤ)) =>
    g.hom x) (Hom.comm' f i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm, hx]
  exact genMap_mulX' N d₀ y D i p (smulXTuple i D p) (fun t => rfl) hstep

omit [IsNoetherianRing k] in
/-- The preimage family is closed under multiplication by any form.  Proved by induction on
the degree of the multiplier: a form of positive degree is a sum of variables times forms of
one degree less (`structureModule_mulSpan_succ`), and the variable case is
`genPre_smulXTuple`. -/
lemma genPre_mul (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ) :
    ∀ (m : ℕ) (qv : MvPolynomial (Fin (n + 1)) k), qv ∈ polySubmodule k n (m : ℤ) →
      ∀ {p : Fin r → polySubmodule k n (D : ℤ)}, p ∈ genPre f d₀ y D →
      ∀ w : Fin r → polySubmodule k n ((D + m : ℕ) : ℤ),
        (∀ t, (w t).1 = qv * (p t).1) → w ∈ genPre f d₀ y (D + m) := by
  intro m
  induction m with
  | zero =>
      intro qv hqv p hp w hw
      obtain ⟨c, hc⟩ : ∃ c : k, MvPolynomial.C c = qv := by
        rw [Nat.cast_zero, polySubmodule_of_nonneg k n le_rfl] at hqv
        simpa using hqv
      have heq : w = c • p := by
        funext t
        refine Subtype.ext ?_
        rw [hw t, ← hc]
        simp [MvPolynomial.smul_eq_C_mul]
      rw [heq]
      exact Submodule.smul_mem _ c hp
  | succ m ih =>
      intro qv hqv p hp w hw
      -- decompose the multiplier as a sum of variables times forms of degree `m`
      have hqv' : qv ∈ polySubmodule k n ((m : ℤ) + 1) := by
        have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rwa [hcast] at hqv
      have hmem : (⟨qv, hqv'⟩ : (structureModule k n).obj ((m : ℤ) + 1))
          ∈ ⨆ i : Fin (n + 1),
              LinearMap.range ((structureModule k n).mulX' i (m : ℤ) ((m : ℤ) + 1) rfl).hom := by
        rw [← mulSpan_succ_eq_iSup, structureModule_mulSpan_succ (m : ℤ) (by positivity)]
        trivial
      refine Submodule.iSup_induction _
        (motive := fun z : (structureModule k n).obj ((m : ℤ) + 1) =>
          ∀ w' : Fin r → polySubmodule k n ((D + (m + 1) : ℕ) : ℤ),
          (∀ t, (w' t).1 = z.1 * (p t).1) →
          w' ∈ genPre f d₀ y (D + (m + 1))) hmem ?_ ?_ ?_ w hw
      · -- a variable times a form of degree `m`
        rintro i z ⟨z', rfl⟩ w' hw'
        have hz' : z'.1 ∈ polySubmodule k n (m : ℤ) := z'.2
        have hmul : ∀ t, z'.1 * (p t).1
            ∈ polySubmodule k n ((D + m : ℕ) : ℤ) := by
          intro t
          have := mul_mem_polySubmodule (k := k) (n := n) (q := z'.1) (e := m) hz'
            (d := ((D + m : ℕ) : ℤ)) (p := (p t).1) (by
              have hcast : ((D + m : ℕ) : ℤ) + -(m : ℤ) = (D : ℤ) := by push_cast; ring
              rw [hcast]
              exact (p t).2)
          exact this
        have hu := ih z'.1 hz' hp
          (fun t => ⟨z'.1 * (p t).1, hmul t⟩) (fun t => rfl)
        have hx := genPre_smulXTuple f d₀ y (D + m) i hu
        have hweq : w' = smulXTuple i (D + m)
            (fun t => ⟨z'.1 * (p t).1, hmul t⟩) := by
          funext t
          refine Subtype.ext ?_
          rw [hw' t, smulXTuple_val]
          show (((structureModule k n).mulX' i (m : ℤ) ((m : ℤ) + 1) rfl).hom z').1 *
              (p t).1 = MvPolynomial.X i * (z'.1 * (p t).1)
          rw [structureModule_mulX'_val, mul_assoc]
        rw [hweq]
        exact hx
      · intro w' hw'
        have hzero : w' = 0 := by
          funext t
          refine Subtype.ext ?_
          rw [hw' t]
          simp
        rw [hzero]
        exact Submodule.zero_mem _
      · intro z₁ z₂ h₁ h₂ w' hw'
        have hm₁ : ∀ t, z₁.1 * (p t).1
            ∈ polySubmodule k n ((D + (m + 1) : ℕ) : ℤ) := by
          intro t
          have hz : z₁.1 ∈ polySubmodule k n ((m + 1 : ℕ) : ℤ) := by
            have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
            rw [hcast]
            exact z₁.2
          exact mul_mem_polySubmodule (k := k) (n := n) (e := m + 1) hz (by
            have hcast : ((D + (m + 1) : ℕ) : ℤ) + -((m + 1 : ℕ) : ℤ) = (D : ℤ) := by
              push_cast; ring
            rw [hcast]
            exact (p t).2)
        have hm₂ : ∀ t, z₂.1 * (p t).1
            ∈ polySubmodule k n ((D + (m + 1) : ℕ) : ℤ) := by
          intro t
          have hz : z₂.1 ∈ polySubmodule k n ((m + 1 : ℕ) : ℤ) := by
            have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
            rw [hcast]
            exact z₂.2
          exact mul_mem_polySubmodule (k := k) (n := n) (e := m + 1) hz (by
            have hcast : ((D + (m + 1) : ℕ) : ℤ) + -((m + 1 : ℕ) : ℤ) = (D : ℤ) := by
              push_cast; ring
            rw [hcast]
            exact (p t).2)
        have hsum : w' = (fun t => (⟨z₁.1 * (p t).1, hm₁ t⟩ :
              polySubmodule k n ((D + (m + 1) : ℕ) : ℤ)))
            + (fun t => (⟨z₂.1 * (p t).1, hm₂ t⟩ :
              polySubmodule k n ((D + (m + 1) : ℕ) : ℤ))) := by
          funext t
          refine Subtype.ext ?_
          rw [hw' t]
          show (z₁.1 + z₂.1) * (p t).1 = _
          rw [add_mul]
          rfl
        rw [hsum]
        exact Submodule.add_mem _ (h₁ _ (fun t => rfl)) (h₂ _ (fun t => rfl))

/-! ## The noetherian step -/

omit [IsNoetherianRing k] in
lemma isHomogeneous_of_mem_polySubmodule {D : ℕ} {pv : MvPolynomial (Fin (n + 1)) k}
    (h : pv ∈ polySubmodule k n (D : ℤ)) : pv.IsHomogeneous D := by
  rw [polySubmodule_of_nonneg k n (by positivity), MvPolynomial.mem_homogeneousSubmodule] at h
  simpa using h

/-- The tuple of underlying polynomials. -/
noncomputable def tupleSubtype (D : ℤ) (r : ℕ) :
    (Fin r → polySubmodule k n D) →ₗ[k] (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  LinearMap.pi fun t => (polySubmodule k n D).subtype.comp (LinearMap.proj t)

omit [IsNoetherianRing k] in
@[simp] lemma tupleSubtype_apply (D : ℤ) (r : ℕ) (p : Fin r → polySubmodule k n D) (t : Fin r) :
    tupleSubtype D r p t = (p t).1 := rfl

variable {M N : GradedModule k n}

/-- The preimage family, viewed inside the free module `S^r`. -/
noncomputable def genPreImg (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ) :
    Submodule k (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  Submodule.map (tupleSubtype (D : ℤ) r) (genPre f d₀ y D)

omit [IsNoetherianRing k] in
lemma mem_genPreImg (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ)
    {w : Fin r → MvPolynomial (Fin (n + 1)) k} :
    w ∈ genPreImg f d₀ y D ↔
      ∃ p ∈ genPre f d₀ y D, (∀ t, w t = (p t).1) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun t => rfl⟩
  · rintro ⟨p, hp, hw⟩
    exact ⟨p, hp, funext fun t => (hw t).symm⟩

omit [IsNoetherianRing k] in
/-- Elements of the image family are homogeneous of the expected degree. -/
lemma isHomogeneous_of_mem_genPreImg (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀)
    (D : ℕ) {w : Fin r → MvPolynomial (Fin (n + 1)) k} (hw : w ∈ genPreImg f d₀ y D)
    (t : Fin r) : (w t).IsHomogeneous D := by
  obtain ⟨p, -, hp⟩ := (mem_genPreImg f d₀ y D).mp hw
  rw [hp t]
  exact isHomogeneous_of_mem_polySubmodule (p t).2

omit [IsNoetherianRing k] in
/-- The image family is closed under multiplication by a form. -/
lemma genPreImg_mul (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D m : ℕ)
    (qv : MvPolynomial (Fin (n + 1)) k) (hq : qv ∈ polySubmodule k n (m : ℤ))
    {w : Fin r → MvPolynomial (Fin (n + 1)) k} (hw : w ∈ genPreImg f d₀ y D) :
    (fun t => qv * w t) ∈ genPreImg f d₀ y (D + m) := by
  obtain ⟨p, hp, hwp⟩ := (mem_genPreImg f d₀ y D).mp hw
  have hmem : ∀ t, qv * (p t).1 ∈ polySubmodule k n ((D + m : ℕ) : ℤ) := by
    intro t
    refine mul_mem_polySubmodule (k := k) (n := n) (e := m) hq ?_
    have hcast : ((D + m : ℕ) : ℤ) + -(m : ℤ) = (D : ℤ) := by push_cast; ring
    rw [hcast]
    exact (p t).2
  refine (mem_genPreImg f d₀ y (D + m)).mpr
    ⟨fun t => ⟨qv * (p t).1, hmem t⟩, genPre_mul f d₀ y D m qv hq hp _ (fun t => rfl), ?_⟩
  intro t
  rw [hwp t]

/-- The `S`-span of the degree-`D` image family inside the free module `S^r`. -/
noncomputable def genSpan (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (D : ℕ) :
    Submodule (MvPolynomial (Fin (n + 1)) k) (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  Submodule.span _ ((genPreImg f d₀ y D : Submodule k _) : Set _)

/-- The `S`-span of the image families in degrees at most `e`. -/
noncomputable def genWle (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (e : ℕ) :
    Submodule (MvPolynomial (Fin (n + 1)) k) (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  ⨆ D : ℕ, ⨆ _ : D ≤ e, genSpan f d₀ y D

/-- The `S`-span of all the image families. -/
noncomputable def genW (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) :
    Submodule (MvPolynomial (Fin (n + 1)) k) (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  ⨆ D : ℕ, genSpan f d₀ y D

omit [IsNoetherianRing k] in
lemma genWle_mono (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) {e e' : ℕ}
    (h : e ≤ e') : genWle f d₀ y e ≤ genWle f d₀ y e' := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  exact le_trans (le_iSup (fun _ : D ≤ e' => genSpan f d₀ y D) (le_trans hD h))
    (le_iSup (fun D : ℕ => ⨆ _ : D ≤ e', genSpan f d₀ y D) D)

omit [IsNoetherianRing k] in
lemma iSup_genWle (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) :
    (⨆ e : ℕ, genWle f d₀ y e) = genW f d₀ y := by
  refine le_antisymm (iSup_le fun e => iSup_le fun D => iSup_le fun _ => ?_)
    (iSup_le fun D => ?_)
  · exact le_iSup (fun D : ℕ => genSpan f d₀ y D) D
  · refine le_trans ?_ (le_iSup (fun e : ℕ => genWle f d₀ y e) D)
    exact le_trans (le_iSup (fun _ : D ≤ D => genSpan f d₀ y D) le_rfl)
      (le_iSup (fun D' : ℕ => ⨆ _ : D' ≤ D, genSpan f d₀ y D') D)

/-- **The noetherian bound.**  `S^r` is a finitely generated module over the noetherian ring
`S = k[x₀, …, x_n]`, so the span of all the image families is already spanned in degrees
below some bound. -/
lemma exists_genW_le_genWle (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) :
    ∃ e : ℕ, genW f d₀ y ≤ genWle f d₀ y e := by
  classical
  haveI : IsNoetherian (MvPolynomial (Fin (n + 1)) k)
      (Fin r → MvPolynomial (Fin (n + 1)) k) := isNoetherian_pi
  obtain ⟨G, hG⟩ : (genW f d₀ y).FG := IsNoetherian.noetherian _
  have hdir : Directed (· ≤ ·) (fun e : ℕ => genWle f d₀ y e) := fun a b =>
    ⟨max a b, genWle_mono f d₀ y (le_max_left a b), genWle_mono f d₀ y (le_max_right a b)⟩
  have hsel : ∀ g : Fin r → MvPolynomial (Fin (n + 1)) k,
      ∃ e : ℕ, g ∈ G → g ∈ genWle f d₀ y e := by
    intro g
    by_cases hg : g ∈ G
    · have hmem : g ∈ genW f d₀ y := by
        rw [← hG]
        exact Submodule.subset_span hg
      rw [← iSup_genWle f d₀ y, Submodule.mem_iSup_of_directed _ hdir] at hmem
      obtain ⟨e, he⟩ := hmem
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun hc => absurd hc hg⟩
  choose e he using hsel
  refine ⟨G.sup e, ?_⟩
  rw [← hG, Submodule.span_le]
  intro g hg
  exact genWle_mono f d₀ y (Finset.le_sup hg) (he g hg)

omit [IsNoetherianRing k] in
/-- Every homogeneous component of an element of the span lies in the corresponding image
family.  The `smul` case decomposes the scalar into homogeneous pieces and uses
`homogeneousComponent_isHomogeneous_mul` together with `genPreImg_mul`. -/
lemma homogeneousComponent_mem_genPreImg (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀)
    (e : ℕ) {w : Fin r → MvPolynomial (Fin (n + 1)) k} (hw : w ∈ genWle f d₀ y e) :
    ∀ m : ℕ, (fun t => MvPolynomial.homogeneousComponent m (w t)) ∈ genPreImg f d₀ y m := by
  classical
  induction hw using Submodule.iSup_induction' with
  | mem D w hw =>
      induction hw using Submodule.iSup_induction' with
      | mem hD w hw =>
          induction hw using Submodule.span_induction with
          | mem w hw =>
              intro m
              have hhom : ∀ t, (w t).IsHomogeneous D :=
                fun t => isHomogeneous_of_mem_genPreImg f d₀ y D hw t
              by_cases hmD : m = D
              · have heq : (fun t => MvPolynomial.homogeneousComponent m (w t)) = w := by
                  funext t
                  rw [MvPolynomial.homogeneousComponent_of_isHomogeneous (hhom t), if_pos hmD]
                rw [heq, hmD]
                exact hw
              · have heq : (fun t => MvPolynomial.homogeneousComponent m (w t)) = 0 := by
                  funext t
                  rw [MvPolynomial.homogeneousComponent_of_isHomogeneous (hhom t), if_neg hmD]
                  rfl
                rw [heq]
                exact Submodule.zero_mem _
          | zero =>
              intro m
              have heq : (fun t => MvPolynomial.homogeneousComponent m
                  ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
                funext t
                simp
              rw [heq]
              exact Submodule.zero_mem _
          | add w₁ w₂ _ _ ih₁ ih₂ =>
              intro m
              have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
                  = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
                    + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
                funext t
                show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
                rw [map_add]
                rfl
              rw [heq]
              exact Submodule.add_mem _ (ih₁ m) (ih₂ m)
          | smul q w' _ ih =>
              intro m
              have hterm : ∀ a : ℕ, (fun t => MvPolynomial.homogeneousComponent m
                  (MvPolynomial.homogeneousComponent a q * w' t)) ∈ genPreImg f d₀ y m := by
                intro a
                have hqa : MvPolynomial.homogeneousComponent a q
                    ∈ polySubmodule k n (a : ℤ) := by
                  rw [polySubmodule_of_nonneg k n (by positivity),
                    MvPolynomial.mem_homogeneousSubmodule]
                  simpa using MvPolynomial.homogeneousComponent_isHomogeneous a q
                by_cases ha : a ≤ m
                · have heq : (fun t => MvPolynomial.homogeneousComponent m
                      (MvPolynomial.homogeneousComponent a q * w' t))
                      = (fun t => MvPolynomial.homogeneousComponent a q *
                          MvPolynomial.homogeneousComponent (m - a) (w' t)) := by
                    funext t
                    exact MvPolynomial.homogeneousComponent_isHomogeneous_mul
                      (MvPolynomial.homogeneousComponent_isHomogeneous a q) (w' t) ha
                  rw [heq]
                  have hmem := genPreImg_mul f d₀ y (m - a) a
                    (MvPolynomial.homogeneousComponent a q) hqa (ih (m - a))
                  have hdeg : m - a + a = m := by omega
                  rw [hdeg] at hmem
                  exact hmem
                · have heq : (fun t => MvPolynomial.homogeneousComponent m
                      (MvPolynomial.homogeneousComponent a q * w' t)) = 0 := by
                    funext t
                    exact MvPolynomial.homogeneousComponent_isHomogeneous_mul_of_lt
                      (MvPolynomial.homogeneousComponent_isHomogeneous a q) (w' t) (by omega)
                  rw [heq]
                  exact Submodule.zero_mem _
              have hsum : (fun t => MvPolynomial.homogeneousComponent m ((q • w') t))
                  = ∑ a ∈ Finset.range (q.totalDegree + 1),
                      (fun t => MvPolynomial.homogeneousComponent m
                        (MvPolynomial.homogeneousComponent a q * w' t)) := by
                funext t
                rw [Finset.sum_apply]
                show MvPolynomial.homogeneousComponent m (q * w' t) = _
                conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
                rw [Finset.sum_mul, map_sum]
              rw [hsum]
              exact Submodule.sum_mem _ fun a _ => hterm a
      | zero =>
          intro m
          have heq : (fun t => MvPolynomial.homogeneousComponent m
              ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
            funext t; simp
          rw [heq]
          exact Submodule.zero_mem _
      | add w₁ w₂ _ _ ih₁ ih₂ =>
          intro m
          have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
              = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
                + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
            funext t
            show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
            rw [map_add]; rfl
          rw [heq]
          exact Submodule.add_mem _ (ih₁ m) (ih₂ m)
  | zero =>
      intro m
      have heq : (fun t => MvPolynomial.homogeneousComponent m
          ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
        funext t; simp
      rw [heq]
      exact Submodule.zero_mem _
  | add w₁ w₂ _ _ ih₁ ih₂ =>
      intro m
      have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
          = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
            + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
        funext t
        show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
        rw [map_add]; rfl
      rw [heq]
      exact Submodule.add_mem _ (ih₁ m) (ih₂ m)

/-! ## Factoring out a variable above the noetherian bound -/

/-- Multiplication of a tuple by the variable `xᵢ`. -/
noncomputable def mulXTuple (i : Fin (n + 1)) (r : ℕ) :
    (Fin r → MvPolynomial (Fin (n + 1)) k) →ₗ[k]
      (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  LinearMap.pi fun t =>
    (LinearMap.mulLeft k (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k)).comp
      (LinearMap.proj t)

omit [IsNoetherianRing k] in
@[simp] lemma mulXTuple_apply (i : Fin (n + 1)) (r : ℕ)
    (w : Fin r → MvPolynomial (Fin (n + 1)) k) (t : Fin r) :
    mulXTuple i r w t = MvPolynomial.X i * w t := rfl

/-- Tuples that are a sum of variables times members of the image family one degree down. -/
noncomputable def genPreImgSucc (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) (m : ℕ) :
    Submodule k (Fin r → MvPolynomial (Fin (n + 1)) k) :=
  ⨆ i : Fin (n + 1), Submodule.map (mulXTuple i r) (genPreImg f d₀ y (m - 1))

omit [IsNoetherianRing k] in
/-- A form of positive degree times a member of the image family factors through a
variable. -/
lemma mul_mem_genPreImgSucc (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀)
    (b c : ℕ) (qv : MvPolynomial (Fin (n + 1)) k)
    (hq : qv ∈ polySubmodule k n ((c + 1 : ℕ) : ℤ))
    {v : Fin r → MvPolynomial (Fin (n + 1)) k} (hv : v ∈ genPreImg f d₀ y b) :
    (fun t => qv * v t) ∈ genPreImgSucc f d₀ y (b + (c + 1)) := by
  classical
  have hcast : ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 := by push_cast; ring
  have hq' : qv ∈ polySubmodule k n ((c : ℤ) + 1) := by rwa [hcast] at hq
  have hmem : (⟨qv, hq'⟩ : (structureModule k n).obj ((c : ℤ) + 1))
      ∈ ⨆ i : Fin (n + 1),
          LinearMap.range ((structureModule k n).mulX' i (c : ℤ) ((c : ℤ) + 1) rfl).hom := by
    rw [← mulSpan_succ_eq_iSup, structureModule_mulSpan_succ (c : ℤ) (by positivity)]
    trivial
  refine Submodule.iSup_induction _
    (motive := fun z : (structureModule k n).obj ((c : ℤ) + 1) =>
      (fun t => z.1 * v t) ∈ genPreImgSucc f d₀ y (b + (c + 1))) hmem ?_ ?_ ?_
  · rintro i z ⟨q', rfl⟩
    have hq'mem : q'.1 ∈ polySubmodule k n (c : ℤ) := q'.2
    have hbase := genPreImg_mul f d₀ y b c q'.1 hq'mem hv
    have hdeg : b + c = b + (c + 1) - 1 := by omega
    rw [hdeg] at hbase
    have hval : (fun t => (((structureModule k n).mulX' i (c : ℤ) ((c : ℤ) + 1) rfl).hom q').1
        * v t) = mulXTuple i r (fun t => q'.1 * v t) := by
      funext t
      rw [mulXTuple_apply, structureModule_mulX'_val, mul_assoc]
    rw [hval]
    exact le_iSup (fun i : Fin (n + 1) =>
      Submodule.map (mulXTuple i r) (genPreImg f d₀ y (b + (c + 1) - 1))) i
      ⟨_, hbase, rfl⟩
  · have hzero : (fun t => (0 : (structureModule k n).obj ((c : ℤ) + 1)).1 * v t) = 0 := by
      funext t
      show (0 : MvPolynomial (Fin (n + 1)) k) * v t = 0
      rw [zero_mul]
    rw [hzero]
    exact Submodule.zero_mem _
  · intro z₁ z₂ h₁ h₂
    have hadd : (fun t => (z₁ + z₂).1 * v t)
        = (fun t => z₁.1 * v t) + (fun t => z₂.1 * v t) := by
      funext t
      show (z₁.1 + z₂.1) * v t = _
      rw [add_mul]
      rfl
    rw [hadd]
    exact Submodule.add_mem _ h₁ h₂

omit [IsNoetherianRing k] in
lemma genSpan_le_genWle (f : M ⟶ N) (d₀ : ℤ) {r : ℕ} (y : Fin r → N.obj d₀) {D e : ℕ}
    (h : D ≤ e) : genSpan f d₀ y D ≤ genWle f d₀ y e :=
  le_trans (le_iSup (fun _ : D ≤ e => genSpan f d₀ y D) h)
    (le_iSup (fun D' : ℕ => ⨆ _ : D' ≤ e, genSpan f d₀ y D') D)

omit [IsNoetherianRing k] in
/-- **Above the noetherian bound every homogeneous component factors through a variable.**
This is the step that turns the bound into the generation condition for the subobject. -/
lemma homogeneousComponent_mem_genPreImgSucc (f : M ⟶ N) (d₀ : ℤ) {r : ℕ}
    (y : Fin r → N.obj d₀) (e : ℕ) {w : Fin r → MvPolynomial (Fin (n + 1)) k}
    (hw : w ∈ genWle f d₀ y e) :
    ∀ m : ℕ, e < m →
      (fun t => MvPolynomial.homogeneousComponent m (w t)) ∈ genPreImgSucc f d₀ y m := by
  classical
  induction hw using Submodule.iSup_induction' with
  | mem D w hw =>
      induction hw using Submodule.iSup_induction' with
      | mem hD w hw =>
          induction hw using Submodule.span_induction with
          | mem w hw =>
              intro m hm
              have hhom : ∀ t, (w t).IsHomogeneous D :=
                fun t => isHomogeneous_of_mem_genPreImg f d₀ y D hw t
              have heq : (fun t => MvPolynomial.homogeneousComponent m (w t)) = 0 := by
                funext t
                rw [MvPolynomial.homogeneousComponent_of_isHomogeneous (hhom t),
                  if_neg (by omega : ¬ (m = D))]
                rfl
              rw [heq]
              exact Submodule.zero_mem _
          | zero =>
              intro m _
              have heq : (fun t => MvPolynomial.homogeneousComponent m
                  ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
                funext t; simp
              rw [heq]
              exact Submodule.zero_mem _
          | add w₁ w₂ _ _ ih₁ ih₂ =>
              intro m hm
              have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
                  = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
                    + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
                funext t
                show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
                rw [map_add]; rfl
              rw [heq]
              exact Submodule.add_mem _ (ih₁ m hm) (ih₂ m hm)
          | smul q w' hw' ih =>
              intro m hm
              have hw'le : w' ∈ genWle f d₀ y e := genSpan_le_genWle f d₀ y hD hw'
              have hterm : ∀ a : ℕ, (fun t => MvPolynomial.homogeneousComponent m
                  (MvPolynomial.homogeneousComponent a q * w' t))
                    ∈ genPreImgSucc f d₀ y m := by
                intro a
                have hqa : MvPolynomial.homogeneousComponent a q
                    ∈ polySubmodule k n (a : ℤ) := by
                  rw [polySubmodule_of_nonneg k n (by positivity),
                    MvPolynomial.mem_homogeneousSubmodule]
                  simpa using MvPolynomial.homogeneousComponent_isHomogeneous a q
                rcases Nat.lt_or_ge m a with hlt | hge
                · have heq : (fun t => MvPolynomial.homogeneousComponent m
                      (MvPolynomial.homogeneousComponent a q * w' t)) = 0 := by
                    funext t
                    exact MvPolynomial.homogeneousComponent_isHomogeneous_mul_of_lt
                      (MvPolynomial.homogeneousComponent_isHomogeneous a q) (w' t) hlt
                  rw [heq]
                  exact Submodule.zero_mem _
                have heq : (fun t => MvPolynomial.homogeneousComponent m
                    (MvPolynomial.homogeneousComponent a q * w' t))
                    = (fun t => MvPolynomial.homogeneousComponent a q *
                        MvPolynomial.homogeneousComponent (m - a) (w' t)) := by
                  funext t
                  exact MvPolynomial.homogeneousComponent_isHomogeneous_mul
                    (MvPolynomial.homogeneousComponent_isHomogeneous a q) (w' t) hge
                rw [heq]
                match a, hqa with
                | 0, hq0 =>
                    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : k,
                        MvPolynomial.C c₀ = MvPolynomial.homogeneousComponent 0 q := by
                      rw [Nat.cast_zero, polySubmodule_of_nonneg k n le_rfl] at hq0
                      simpa using hq0
                    have hsm : (fun t => MvPolynomial.homogeneousComponent 0 q *
                        MvPolynomial.homogeneousComponent (m - 0) (w' t))
                        = c₀ • (fun t => MvPolynomial.homogeneousComponent m (w' t)) := by
                      funext t
                      rw [← hc₀, Nat.sub_zero]
                      show MvPolynomial.C c₀ * MvPolynomial.homogeneousComponent m (w' t)
                        = c₀ • MvPolynomial.homogeneousComponent m (w' t)
                      rw [MvPolynomial.smul_eq_C_mul]
                    rw [hsm]
                    exact Submodule.smul_mem _ c₀ (ih m hm)
                | (c + 1), hqc =>
                    have hbase := homogeneousComponent_mem_genPreImg f d₀ y e hw'le (m - (c + 1))
                    have hres := mul_mem_genPreImgSucc f d₀ y (m - (c + 1)) c
                      (MvPolynomial.homogeneousComponent (c + 1) q) hqc hbase
                    have hdeg : m - (c + 1) + (c + 1) = m := by omega
                    rw [hdeg] at hres
                    exact hres
              have hsum : (fun t => MvPolynomial.homogeneousComponent m ((q • w') t))
                  = ∑ a ∈ Finset.range (q.totalDegree + 1),
                      (fun t => MvPolynomial.homogeneousComponent m
                        (MvPolynomial.homogeneousComponent a q * w' t)) := by
                funext t
                rw [Finset.sum_apply]
                show MvPolynomial.homogeneousComponent m (q * w' t) = _
                conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
                rw [Finset.sum_mul, map_sum]
              rw [hsum]
              exact Submodule.sum_mem _ fun a _ => hterm a
      | zero =>
          intro m _
          have heq : (fun t => MvPolynomial.homogeneousComponent m
              ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
            funext t; simp
          rw [heq]
          exact Submodule.zero_mem _
      | add w₁ w₂ _ _ ih₁ ih₂ =>
          intro m hm
          have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
              = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
                + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
            funext t
            show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
            rw [map_add]; rfl
          rw [heq]
          exact Submodule.add_mem _ (ih₁ m hm) (ih₂ m hm)
  | zero =>
      intro m _
      have heq : (fun t => MvPolynomial.homogeneousComponent m
          ((0 : Fin r → MvPolynomial (Fin (n + 1)) k) t)) = 0 := by
        funext t; simp
      rw [heq]
      exact Submodule.zero_mem _
  | add w₁ w₂ _ _ ih₁ ih₂ =>
      intro m hm
      have heq : (fun t => MvPolynomial.homogeneousComponent m ((w₁ + w₂) t))
          = (fun t => MvPolynomial.homogeneousComponent m (w₁ t))
            + (fun t => MvPolynomial.homogeneousComponent m (w₂ t)) := by
        funext t
        show MvPolynomial.homogeneousComponent m (w₁ t + w₂ t) = _
        rw [map_add]; rfl
      rw [heq]
      exact Submodule.add_mem _ (ih₁ m hm) (ih₂ m hm)

/-! ## Hilbert's basis theorem for graded submodules -/

/-- **Subsheaves of coherent sheaves are coherent** — Hilbert's basis theorem in graded form.
The proof transports the subobject into the free module `S^r` through `genMap`, where `S` is
noetherian, and reads the degree bound back off. -/
theorem IsFG.of_injective {M N : GradedModule k n} (f : M ⟶ N)
    (hinj : ∀ d, Function.Injective (f.app d).hom) (hN : IsFG N) : IsFG M := by
  classical
  obtain ⟨hfdN, ⟨lo, hlow⟩, ⟨d₀, hgenN⟩⟩ := hN
  haveI hfd : ∀ d : ℤ, Module.Finite k (N.obj d) := hfdN
  haveI : Module.Finite k (N.obj d₀) := hfd d₀
  obtain ⟨r, y, hyspan⟩ := Module.Finite.exists_fin (R := k) (M := (N.obj d₀ : Type u))
  obtain ⟨e, he⟩ := exists_genW_le_genWle f d₀ y
  have key : ∀ D : ℕ, e ≤ D →
      M.mulSpan (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) = ⊤ := by
    intro D hD
    have hstep : d₀ + (D : ℤ) + 1 = d₀ + ((D + 1 : ℕ) : ℤ) := by push_cast; ring
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨v, hv⟩ := surjective_genMap N d₀ y hyspan hgenN (D + 1)
      ((f.app (d₀ + ((D + 1 : ℕ) : ℤ))).hom z)
    have hvmem : v ∈ genPre f d₀ y (D + 1) := ⟨z, hv.symm⟩
    have hvimg : tupleSubtype (((D + 1 : ℕ) : ℤ)) r v ∈ genPreImg f d₀ y (D + 1) :=
      ⟨v, hvmem, rfl⟩
    have hvW : tupleSubtype (((D + 1 : ℕ) : ℤ)) r v ∈ genWle f d₀ y e :=
      he (le_iSup (fun D' : ℕ => genSpan f d₀ y D') (D + 1)
        (Submodule.subset_span hvimg))
    have hcompv : (fun t => MvPolynomial.homogeneousComponent (D + 1)
        (tupleSubtype (((D + 1 : ℕ) : ℤ)) r v t)) = tupleSubtype (((D + 1 : ℕ) : ℤ)) r v := by
      funext t
      rw [tupleSubtype_apply, MvPolynomial.homogeneousComponent_of_isHomogeneous
        (isHomogeneous_of_mem_polySubmodule (v t).2)]
      simp only [↓reduceIte]
    have hsucc : tupleSubtype (((D + 1 : ℕ) : ℤ)) r v ∈ genPreImgSucc f d₀ y (D + 1) := by
      have := homogeneousComponent_mem_genPreImgSucc f d₀ y e hvW (D + 1) (by omega)
      rwa [hcompv] at this
    -- decompose into variables times members one degree down
    have hmain : ∀ u : Fin r → MvPolynomial (Fin (n + 1)) k,
        u ∈ genPreImgSucc f d₀ y (D + 1) →
        (∀ t, u t ∈ polySubmodule k n ((D + 1 : ℕ) : ℤ)) ∧
        ∀ v' : Fin r → polySubmodule k n ((D + 1 : ℕ) : ℤ), (∀ t, (v' t).1 = u t) →
          genMap N d₀ y (D + 1) v' ∈ Submodule.map
            (f.app (d₀ + ((D + 1 : ℕ) : ℤ))).hom
            (M.mulSpan (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ))) := by
      intro u hu
      have hsimp : (D + 1) - 1 = D := by omega
      rw [genPreImgSucc, hsimp] at hu
      induction hu using Submodule.iSup_induction' with
      | mem i u hu =>
          obtain ⟨w0, hw0, rfl⟩ := hu
          obtain ⟨p, hp, hval⟩ := (mem_genPreImg f d₀ y D).mp hw0
          constructor
          · intro t
            rw [mulXTuple_apply, hval t]
            exact (smulXTuple i D p t).2
          · intro v' hv'
            have hveq : v' = smulXTuple i D p := by
              funext t
              refine Subtype.ext ?_
              rw [hv' t, mulXTuple_apply, hval t, smulXTuple_val]
            rw [hveq, ← genMap_mulX' N d₀ y D i p (smulXTuple i D p) (fun t => rfl) hstep]
            obtain ⟨w, hw⟩ := hp
            rw [← hw]
            refine ⟨(M.mulX' i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep).hom w, ?_, ?_⟩
            · exact range_mulX'_le_mulSpan M i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep
                (LinearMap.mem_range_self _ _)
            · have hc := congrArg
                (fun g : M.obj (d₀ + (D : ℤ)) ⟶ N.obj (d₀ + ((D + 1 : ℕ) : ℤ)) => g.hom w)
                (Hom.comm' f i (d₀ + (D : ℤ)) (d₀ + ((D + 1 : ℕ) : ℤ)) hstep)
              simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
              exact hc.symm
      | zero =>
          refine ⟨fun t => by simpa using Submodule.zero_mem _, fun v' hv' => ?_⟩
          have hv0 : v' = 0 := by
            funext t
            refine Subtype.ext ?_
            rw [hv' t]
            rfl
          rw [hv0, map_zero]
          exact Submodule.zero_mem _
      | add u₁ u₂ h₁ h₂ ih₁ ih₂ =>
          refine ⟨fun t => by
            show u₁ t + u₂ t ∈ _
            exact Submodule.add_mem _ (ih₁.1 t) (ih₂.1 t), fun v' hv' => ?_⟩
          have hsplit : v' = (fun t => (⟨u₁ t, ih₁.1 t⟩ :
                polySubmodule k n ((D + 1 : ℕ) : ℤ)))
              + (fun t => (⟨u₂ t, ih₂.1 t⟩ : polySubmodule k n ((D + 1 : ℕ) : ℤ))) := by
            funext t
            refine Subtype.ext ?_
            rw [hv' t]
            rfl
          rw [hsplit, map_add]
          exact Submodule.add_mem _ (ih₁.2 _ (fun t => rfl)) (ih₂.2 _ (fun t => rfl))
    obtain ⟨w, hwmem, hweq⟩ := (hmain _ hsucc).2 v (fun t => rfl)
    rw [hv] at hweq
    have hzw : z = w := (hinj _ hweq).symm
    rw [hzw]
    exact hwmem
  refine ⟨fun d => Module.Finite.of_injective (f.app d).hom (hinj d),
    ⟨lo, fun d hd => by
      haveI := hlow d hd
      exact ⟨fun a b => hinj d (Subsingleton.elim _ _)⟩⟩,
    ⟨d₀ + (e : ℤ), fun d hd => ?_⟩⟩
  obtain ⟨D, hD, rfl⟩ : ∃ D : ℕ, e ≤ D ∧ d = d₀ + (D : ℤ) := by
    refine ⟨(d - d₀).toNat, ?_, ?_⟩ <;> omega
  have hk := key D hD
  have htr : ∀ a b : ℤ, a = b → M.mulSpan (d₀ + (D : ℤ)) a = ⊤ →
      M.mulSpan (d₀ + (D : ℤ)) b = ⊤ := by
    intro a b hab h
    subst hab
    exact h
  exact htr _ _ (by push_cast; ring) hk

/-! ## The free presentation as a morphism -/

omit [IsNoetherianRing k] in
lemma eq_zero_of_mem_polySubmodule_neg {a : ℤ} (ha : a < 0)
    {pv : MvPolynomial (Fin (n + 1)) k} (h : pv ∈ polySubmodule k n a) : pv = 0 := by
  rw [polySubmodule_of_neg k n ha, Submodule.mem_bot] at h
  exact h

omit [IsNoetherianRing k] in
/-- The form action does not depend on how the degree is presented. -/
lemma mulForm_congr_index (M : GradedModule k n) (D D' : ℕ) (hDD : D = D') (d e : ℤ)
    (h : d + (D : ℤ) = e) (h' : d + (D' : ℤ) = e) (p : polySubmodule k n (D : ℤ))
    (p' : polySubmodule k n (D' : ℤ)) (hp : p.1 = p'.1) (x : M.obj d) :
    mulForm M D d e h p x = mulForm M D' d e h' p' x := by
  subst hDD
  have hpp : p = p' := Subtype.ext hp
  rw [hpp]


/-- Multiplication by a form whose degree is an *integer*: zero in negative degrees, where
the space of forms is trivial anyway.  Packaging it this way keeps the free presentation free
of case splits and of degree transports. -/
noncomputable def mulFormZ (M : GradedModule k n) (a d e : ℤ) (h : d + a = e) :
    polySubmodule k n a →ₗ[k] (M.obj d →ₗ[k] M.obj e) :=
  if ha : 0 ≤ a then
    (mulForm M a.toNat d e (by rw [Int.toNat_of_nonneg ha]; exact h)).comp
      (LinearEquiv.ofEq (polySubmodule k n a) (polySubmodule k n ((a.toNat : ℕ) : ℤ))
        (by congr 1; omega)).toLinearMap
  else 0

omit [IsNoetherianRing k] in
lemma mulFormZ_of_neg (M : GradedModule k n) {a : ℤ} (ha : a < 0) (d e : ℤ) (h : d + a = e) :
    mulFormZ M a d e h = 0 := by
  rw [mulFormZ, dif_neg (by omega)]

omit [IsNoetherianRing k] in
lemma mulFormZ_of_nonneg (M : GradedModule k n) {a : ℤ} (ha : 0 ≤ a) (d e : ℤ) (h : d + a = e)
    (p : polySubmodule k n a) (x : M.obj d) :
    mulFormZ M a d e h p x
      = mulForm M a.toNat d e (by rw [Int.toNat_of_nonneg ha]; exact h)
          ⟨p.1, by
            have hcast : polySubmodule k n a = polySubmodule k n ((a.toNat : ℕ) : ℤ) := by
              congr 1; omega
            exact hcast ▸ p.2⟩ x := by
  rw [mulFormZ, dif_pos ha]
  rfl

omit [IsNoetherianRing k] in
/-- The integer-degree form action is compatible with multiplication by a variable. -/
lemma mulFormZ_mulX' (M : GradedModule k n) (a d e f : ℤ) (h : d + a = e) (h' : e + 1 = f)
    (h'' : d + (a + 1) = f) (i : Fin (n + 1)) (p : polySubmodule k n a)
    (q : polySubmodule k n (a + 1)) (hq : q.1 = MvPolynomial.X i * p.1) (x : M.obj d) :
    (M.mulX' i e f h').hom (mulFormZ M a d e h p x) = mulFormZ M (a + 1) d f h'' q x := by
  rcases lt_or_ge a 0 with ha | ha
  · -- no forms of negative degree, so both sides vanish
    have hp0 : p.1 = 0 := eq_zero_of_mem_polySubmodule_neg ha p.2
    have hq0 : q = 0 := Subtype.ext (by rw [hq, hp0, mul_zero]; rfl)
    rw [mulFormZ_of_neg M ha d e h]
    simp only [LinearMap.zero_apply, map_zero]
    rw [hq0, map_zero]
    rfl
  · have hnn : 0 ≤ a + 1 := by omega
    rw [mulFormZ_of_nonneg M ha d e h, mulFormZ_of_nonneg M hnn d f h'']
    have hstep : a.toNat + 1 = (a + 1).toNat := by omega
    have hdeg : d + ((a.toNat + 1 : ℕ) : ℤ) = f := by
      rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg ha]
      omega
    have hqmem : q.1 ∈ polySubmodule k n ((a.toNat + 1 : ℕ) : ℤ) := by
      have hcast : polySubmodule k n (a + 1)
          = polySubmodule k n ((a.toNat + 1 : ℕ) : ℤ) := by congr 1; omega
      exact hcast ▸ q.2
    have hbase := mulForm_mulX' M a.toNat d e f
      (by rw [Int.toNat_of_nonneg ha]; exact h) h' hdeg i
      ⟨p.1, by
        have hcast : polySubmodule k n a = polySubmodule k n ((a.toNat : ℕ) : ℤ) := by
          congr 1; omega
        exact hcast ▸ p.2⟩
      ⟨q.1, hqmem⟩ hq x
    rw [hbase]
    exact mulForm_congr_index M (a.toNat + 1) (a + 1).toNat hstep d f hdeg
      (by rw [Int.toNat_of_nonneg hnn]; exact h'') ⟨q.1, hqmem⟩ _ rfl x

omit [IsNoetherianRing k] in
lemma mulFormZ_congr_degree (M : GradedModule k n) (a a' : ℤ) (haa : a = a') (d e : ℤ)
    (h : d + a = e) (h' : d + a' = e) (p : polySubmodule k n a) (p' : polySubmodule k n a')
    (hp : p.1 = p'.1) (x : M.obj d) :
    mulFormZ M a d e h p x = mulFormZ M a' d e h' p' x := by
  subst haa
  have hpp : p = p' := Subtype.ext hp
  rw [hpp]

/-- **The free presentation.**  A family `y` in degree `d₀` induces a morphism from the free
graded module `S(-d₀)^{⊕r}`. -/
noncomputable def freeGenHom (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀) :
    ((structureModule k n).twist (-d₀)).pow r ⟶ M where
  app d := ModuleCat.ofHom (∑ t : Fin r,
    ((mulFormZ M (d + -d₀) d₀ d (by ring)).flip (y t)).comp (LinearMap.proj t))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, LinearMap.flip_apply, LinearMap.proj_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show (M.mulX i d).hom (mulFormZ M (d + -d₀) d₀ d (by ring) (p t) (y t))
      = mulFormZ M (d + 1 + -d₀) d₀ (d + 1) (by ring)
          ((((((structureModule k n).twist (-d₀)).pow r).mulX i d).hom p) t) (y t)
    have hval : (((((((structureModule k n).twist (-d₀)).pow r).mulX i d).hom p) t) :
        polySubmodule k n (d + 1 + -d₀)).1 = MvPolynomial.X i * (p t).1 := by
      show (((structureModule k n).mulX' i (d + -d₀) (d + 1 + -d₀) (by ring)).hom (p t)).1 = _
      rw [structureModule_mulX'_val]
    have hmem : (MvPolynomial.X i * (p t).1) ∈ polySubmodule k n ((d + -d₀) + 1) :=
      X_mul_mem_polySubmodule k n i (d + -d₀) (p t).2
    have hstep := mulFormZ_mulX' M (d + -d₀) d₀ d (d + 1) (by ring) rfl (by ring) i
      (p t) ⟨MvPolynomial.X i * (p t).1, hmem⟩ rfl (y t)
    rw [show M.mulX i d = M.mulX' i d (d + 1) rfl from (mulX'_rfl M i d).symm, hstep]
    exact mulFormZ_congr_degree M ((d + -d₀) + 1) (d + 1 + -d₀) (by ring) d₀ (d + 1)
      (by ring) (by ring) ⟨MvPolynomial.X i * (p t).1, hmem⟩ _ hval.symm (y t)

omit [IsNoetherianRing k] in
lemma freeGenHom_app_apply (M : GradedModule k n) (d₀ : ℤ) {r : ℕ} (y : Fin r → M.obj d₀)
    (d : ℤ) (p : (((structureModule k n).twist (-d₀)).pow r).obj d) :
    ((freeGenHom M d₀ y).app d).hom p
      = ∑ t : Fin r, mulFormZ M (d + -d₀) d₀ d (by ring) (p t) (y t) := by
  show (∑ t : Fin r,
      ((mulFormZ M (d + -d₀) d₀ d (by ring)).flip (y t)).comp (LinearMap.proj t)) p = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    LinearMap.proj_apply]

omit [IsNoetherianRing k] in
/-- Generation from `d₀` on, at an arbitrary degree. -/
lemma mulSpan_top_of_gen (M : GradedModule k n) (d₀ : ℤ)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) (d : ℤ) (hd : d₀ ≤ d) :
    M.mulSpan d₀ d = ⊤ := by
  obtain ⟨D, rfl⟩ : ∃ D : ℕ, d = d₀ + (D : ℤ) := ⟨(d - d₀).toNat, by omega⟩
  exact mulSpan_of_gen M d₀ hgen D

omit [IsNoetherianRing k] in
lemma mulFormZ_monomial (M : GradedModule k n) (a d e : ℤ) (h : d + a = e)
    (b : Fin (n + 1) →₀ ℕ) (hb : ((b.degree : ℕ) : ℤ) = a) (c : k)
    (hm : (MvPolynomial.monomial b c : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n a)
    (x : M.obj d) :
    mulFormZ M a d e h ⟨MvPolynomial.monomial b c, hm⟩ x
      = c • (M.mulMono b d e (by rw [hb]; exact h)).hom x := by
  have ha : 0 ≤ a := by omega
  rw [mulFormZ_of_nonneg M ha d e h]
  exact mulForm_monomial M a.toNat d e (by rw [Int.toNat_of_nonneg ha]; exact h) b
    (by omega) c _ x

omit [IsNoetherianRing k] in
/-- The free presentation is surjective in every degree from `d₀` on. -/
lemma surjective_freeGenHom_app (M : GradedModule k n) (d₀ : ℤ) {r : ℕ}
    (y : Fin r → M.obj d₀) (hy : Submodule.span k (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) (d : ℤ) (hd : d₀ ≤ d) :
    Function.Surjective (((freeGenHom M d₀ y).app d).hom) := by
  classical
  rw [← LinearMap.range_eq_top]
  refine eq_top_iff.mpr ?_
  rw [← mulSpan_top_of_gen M d₀ hgen d hd]
  refine iSup_le fun l => ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin r → k, ∑ t, c t • y t = z :=
    (Submodule.mem_span_range_iff_exists_fun k).mp (by rw [hy]; trivial)
  have hlen : ((listExp l.1).degree : ℤ) = d + -d₀ := by
    have h2 : (listExp l.1).degree = l.1.length := by
      have h3 := monoList_listExp_coe l.1
      have h4 := congrArg Multiset.card h3
      rw [← monoList_length]
      simpa using h4
    have h5 := l.2
    omega
  have hdeg : d₀ + ((listExp l.1).degree : ℤ) = d := by omega
  have hmem : ∀ t : Fin r,
      (MvPolynomial.monomial (listExp l.1) (c t) : MvPolynomial (Fin (n + 1)) k)
        ∈ polySubmodule k n (d + -d₀) := by
    intro t
    rw [polySubmodule_of_nonneg k n (by omega), MvPolynomial.mem_homogeneousSubmodule]
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    omega
  refine ⟨fun t => ⟨MvPolynomial.monomial (listExp l.1) (c t), hmem t⟩, ?_⟩
  rw [freeGenHom_app_apply]
  have hterm : ∀ t : Fin r,
      mulFormZ M (d + -d₀) d₀ d (by ring)
          ⟨MvPolynomial.monomial (listExp l.1) (c t), hmem t⟩ (y t)
        = c t • (M.mulMono (listExp l.1) d₀ d hdeg).hom (y t) := fun t =>
    mulFormZ_monomial M (d + -d₀) d₀ d (by ring) (listExp l.1) hlen (c t) (hmem t) (y t)
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  have hml : M.mulList l.1 d₀ d l.2 = M.mulMono (listExp l.1) d₀ d hdeg :=
    mulList_eq_mulMono M l.1 d₀ d l.2 hdeg
  rw [hml, ← hc, map_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [map_smul]

end Noetherian

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
