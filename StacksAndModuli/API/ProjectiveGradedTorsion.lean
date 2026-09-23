module

public import StacksAndModuli.API.ProjectiveGradedSerre

/-!
# Irrelevant torsion and the torsion-free model

Supporting API with no Stacks Project counterpart.

The submodule `Γ_m(M) ⊆ M` of elements killed by a power of every variable is finitely
generated when `M` is, hence vanishes in all large degrees; so it is invisible to Čech
cohomology, and `M ↠ M / Γ_m(M)` is the torsion-free model demanded by the
`exists_noIrrelevantTorsion_quotient` field of `CechSerreData`.

Main declarations:
- `GradedModule.sub`, the graded submodule cut out by a stable degreewise family;
- `GradedModule.irrTors`, the irrelevant torsion;
- `GradedModule.exists_noIrrelevantTorsion_quotient_of_isFG`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k] {n : ℕ}

/-! ## Graded submodules -/

/-- A degreewise family of submodules stable under the variables is itself a graded
module. -/
def sub (M : GradedModule k n) (p : ∀ d : ℤ, Submodule k (M.obj d))
    (hp : ∀ (i : Fin (n + 1)) (d : ℤ), ∀ x ∈ p d, (M.mulX i d).hom x ∈ p (d + 1)) :
    GradedModule k n where
  obj d := ModuleCat.of k (p d)
  mulX i d := ModuleCat.ofHom
    ((M.mulX i d).hom.restrict (p := p d) (q := p (d + 1)) (hp i d))
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact congrArg (fun g : M.obj d ⟶ M.obj (d + 1 + 1) => g.hom x.1) (M.mulX_comm i j d)

/-- The inclusion of a graded submodule. -/
def subι (M : GradedModule k n) (p : ∀ d : ℤ, Submodule k (M.obj d))
    (hp : ∀ (i : Fin (n + 1)) (d : ℤ), ∀ x ∈ p d, (M.mulX i d).hom x ∈ p (d + 1)) :
    sub M p hp ⟶ M where
  app d := ModuleCat.ofHom (p d).subtype
  comm _ _ := rfl

lemma injective_subι (M : GradedModule k n) (p : ∀ d : ℤ, Submodule k (M.obj d))
    (hp : ∀ (i : Fin (n + 1)) (d : ℤ), ∀ x ∈ p d, (M.mulX i d).hom x ∈ p (d + 1)) (d : ℤ) :
    Function.Injective (((subι M p hp).app d).hom) :=
  fun _ _ h => Subtype.val_injective h

/-! ## Powers of a single variable -/

/-- Multiplication by `xᵢ^m`, from degree `d` to a degree `e` presented with a proof. -/
def mulPow (M : GradedModule k n) (i : Fin (n + 1)) (m : ℕ) (d e : ℤ)
    (h : d + (m : ℤ) = e) : M.obj d ⟶ M.obj e :=
  M.mulList (listPow [i] m) d e (by simpa using h)

lemma mulPow_add (M : GradedModule k n) (i : Fin (n + 1)) (a b : ℕ) (d e f : ℤ)
    (h₁ : d + (a : ℤ) = e) (h₂ : e + (b : ℤ) = f) (h : d + ((a + b : ℕ) : ℤ) = f) :
    M.mulPow i (a + b) d f h = M.mulPow i a d e h₁ ≫ M.mulPow i b e f h₂ := by
  have hperm : (listPow [i] (a + b)).Perm (listPow [i] a ++ listPow [i] b) := by
    rw [listPow_add]
  rw [mulPow, mulPow, mulPow,
    M.mulList_perm hperm d f (by simpa using h) (by simp; omega)]
  exact M.mulList_append _ _ d e f (by simpa using h₁) (by simpa using h₂) _

lemma mulPow_eq_zero_of_le (M : GradedModule k n) (i : Fin (n + 1)) {a m : ℕ} (ham : a ≤ m)
    (d e f : ℤ) (h₁ : d + (a : ℤ) = e) (h : d + (m : ℤ) = f) (x : M.obj d)
    (hx : (M.mulPow i a d e h₁).hom x = 0) :
    (M.mulPow i m d f h).hom x = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = a + t := ⟨m - a, by omega⟩
  rw [M.mulPow_add i a t d e f h₁ (by push_cast at h ⊢; omega) h]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]

lemma mulPow_eq_zero_congr (M : GradedModule k n) (i : Fin (n + 1)) (m : ℕ) (d e e' : ℤ)
    (h : d + (m : ℤ) = e) (h' : d + (m : ℤ) = e') (x : M.obj d)
    (hx : (M.mulPow i m d e h).hom x = 0) : (M.mulPow i m d e' h').hom x = 0 := by
  subst h
  subst h'
  exact hx

/-- Multiplication by `xᵢ^m` commutes with multiplication by `x_j`. -/
lemma mulPow_comm_mulX' (M : GradedModule k n) (i j : Fin (n + 1)) (m : ℕ)
    (d e f g : ℤ) (h₁ : d + 1 = e) (h₂ : e + (m : ℤ) = f) (h₃ : d + (m : ℤ) = g)
    (h₄ : g + 1 = f) :
    M.mulX' j d e h₁ ≫ M.mulPow i m e f h₂ = M.mulPow i m d g h₃ ≫ M.mulX' j g f h₄ := by
  have hlen : d + ((([j] ++ listPow [i] m)).length : ℤ) = f := by simp; omega
  have hlen' : d + (((listPow [i] m ++ [j])).length : ℤ) = f := by simp; omega
  have hL : M.mulX' j d e h₁ ≫ M.mulPow i m e f h₂
      = M.mulList ([j] ++ listPow [i] m) d f hlen := by
    rw [mulPow, ← mulList_singleton M j d e (by simpa using h₁)]
    exact (M.mulList_append [j] (listPow [i] m) d e f _ _ hlen).symm
  have hR : M.mulPow i m d g h₃ ≫ M.mulX' j g f h₄
      = M.mulList (listPow [i] m ++ [j]) d f hlen' := by
    rw [mulPow, ← mulList_singleton M j g f (by simpa using h₄)]
    exact (M.mulList_append (listPow [i] m) [j] d g f _ _ hlen').symm
  rw [hL, hR]
  exact M.mulList_perm List.perm_append_comm d f hlen hlen'

/-! ## The irrelevant torsion -/

variable (M : GradedModule k n)

/-- The degree-`d` part of the irrelevant torsion: elements killed by a power of every
variable. -/
def irrTorsSub (d : ℤ) : Submodule k (M.obj d) where
  carrier := {x | ∀ i : Fin (n + 1), ∃ m : ℕ,
    (M.mulPow i m d (d + (m : ℤ)) rfl).hom x = 0}
  add_mem' := by
    intro x z hx hz i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hz i
    refine ⟨max a b, ?_⟩
    rw [map_add,
      M.mulPow_eq_zero_of_le i (le_max_left a b) d (d + (a : ℤ)) _ rfl rfl x ha,
      M.mulPow_eq_zero_of_le i (le_max_right a b) d (d + (b : ℤ)) _ rfl rfl z hb, add_zero]
  zero_mem' := fun i => ⟨0, map_zero _⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨m, hm⟩ := hx i
    exact ⟨m, by rw [map_smul, hm, smul_zero]⟩

lemma mem_irrTorsSub {d : ℤ} {x : M.obj d} :
    x ∈ M.irrTorsSub d ↔
      ∀ i : Fin (n + 1), ∃ m : ℕ, (M.mulPow i m d (d + (m : ℤ)) rfl).hom x = 0 :=
  Iff.rfl

lemma irrTorsSub_mulX (i : Fin (n + 1)) (d : ℤ) :
    ∀ x ∈ M.irrTorsSub d, (M.mulX i d).hom x ∈ M.irrTorsSub (d + 1) := by
  intro x hx j
  obtain ⟨m, hm⟩ := hx j
  refine ⟨m, ?_⟩
  have hcomm := M.mulPow_comm_mulX' j i m d (d + 1) (d + 1 + (m : ℤ)) (d + (m : ℤ))
    rfl rfl rfl (by ring)
  have happ := congrArg (fun g : M.obj d ⟶ M.obj (d + 1 + (m : ℤ)) => g.hom x) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  rw [show M.mulX' i d (d + 1) rfl = M.mulX i d from mulX'_rfl M i d] at happ
  rw [happ, hm, map_zero]

/-- The irrelevant torsion `Γ_m(M)`, as a graded submodule of `M`. -/
def irrTors : GradedModule k n := sub M M.irrTorsSub M.irrTorsSub_mulX

/-- The inclusion of the irrelevant torsion. -/
def irrTorsι : M.irrTors ⟶ M := subι M M.irrTorsSub M.irrTorsSub_mulX

lemma injective_irrTorsι (d : ℤ) : Function.Injective ((M.irrTorsι.app d).hom) :=
  injective_subι M M.irrTorsSub M.irrTorsSub_mulX d

/-- The irrelevant torsion is finitely generated when `M` is: it is a submodule. -/
lemma isFG_irrTors (hM : IsFG M) : IsFG M.irrTors :=
  IsFG.of_injective M.irrTorsι M.injective_irrTorsι hM

/-! ## A monomial of large degree kills an irrelevant torsion element -/

lemma degree_eq_sum_univ (b : Fin (n + 1) →₀ ℕ) :
    b.degree = ∑ i : Fin (n + 1), b i := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => by simpa using hi)

/-- Pigeonhole: a monomial of degree at least `(n+1) * m` has some exponent at least `m`. -/
lemma exists_le_of_le_degree {b : Fin (n + 1) →₀ ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hb : (n + 1) * m ≤ b.degree) : ∃ i, m ≤ b i := by
  by_contra hcon
  push_neg at hcon
  have hle : b.degree ≤ (n + 1) * (m - 1) := by
    rw [degree_eq_sum_univ]
    calc ∑ i : Fin (n + 1), b i ≤ ∑ _i : Fin (n + 1), (m - 1) :=
          Finset.sum_le_sum fun i _ => by have := hcon i; omega
      _ = (n + 1) * (m - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsplit : (n + 1) * m = (n + 1) * (m - 1) + (n + 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 from (Nat.sub_add_cancel hm).symm]
    ring
  omega

/-- Peeling `m` copies of `i` off the monomial list of `c + m • eᵢ`. -/
lemma monoList_add_nsmul_single (c : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (m : ℕ) :
    ((monoList (c + m • Finsupp.single i 1) : List (Fin (n + 1))) :
        Multiset (Fin (n + 1)))
      = Multiset.replicate m i
        + ((monoList c : List (Fin (n + 1))) : Multiset (Fin (n + 1))) := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hstep : c + (t + 1) • Finsupp.single i 1
          = (c + t • Finsupp.single i 1) + Finsupp.single i 1 := by
        rw [succ_nsmul]
        abel
      rw [hstep, monoList_add_single, ih, Multiset.replicate_succ, Multiset.cons_add]

/-- Multiplication by a monomial whose `i`-th exponent is at least `m` kills anything
killed by `xᵢ^m`. -/
lemma mulMono_eq_zero_of_mulPow (M : GradedModule k n) (i : Fin (n + 1)) {m : ℕ}
    {b : Fin (n + 1) →₀ ℕ} (hmb : m ≤ b i) (d e : ℤ) (h : d + (b.degree : ℤ) = e)
    (x : M.obj d) (hx : (M.mulPow i m d (d + (m : ℤ)) rfl).hom x = 0) :
    (M.mulMono b d e h).hom x = 0 := by
  classical
  set c : Fin (n + 1) →₀ ℕ := b - m • Finsupp.single i 1 with hc
  have hb : b = c + m • Finsupp.single i 1 := by
    ext j
    simp only [hc, Finsupp.coe_add, Finsupp.coe_tsub, Finsupp.coe_smul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases hj : i = j
    · subst hj
      simp only [↓reduceIte, mul_one]
      omega
    · simp [hj]
  have hmul : ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = ((listPow [i] m ++ monoList c : List (Fin (n + 1))) :
          Multiset (Fin (n + 1))) := by
    rw [show ((listPow [i] m ++ monoList c : List (Fin (n + 1))) :
        Multiset (Fin (n + 1)))
      = ((listPow [i] m : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
        + ((monoList c : List (Fin (n + 1))) : Multiset (Fin (n + 1))) from
      (Multiset.coe_add _ _).symm, listPow_singleton, Multiset.coe_replicate]
    conv_lhs => rw [hb]
    exact monoList_add_nsmul_single c i m
  have hperm : (monoList b).Perm (listPow [i] m ++ monoList c) :=
    Multiset.coe_eq_coe.mp hmul
  have hlen1 : d + ((listPow [i] m).length : ℤ) = d + (m : ℤ) := by simp
  have hcdeg : (m : ℤ) + (c.degree : ℤ) = (b.degree : ℤ) := by
    have : b.degree = m + c.degree := by
      rw [hb, degree_eq_sum_univ, degree_eq_sum_univ]
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Finsupp.single_apply]
      rw [Finset.sum_add_distrib, add_comm]
      congr 1
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (fun hcon =>
        absurd (Finset.mem_univ i) hcon)]
      simp
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) this.symm
  have hlen2 : d + (m : ℤ) + ((monoList c).length : ℤ) = e := by
    rw [monoList_length]
    omega
  have hlen : d + ((listPow [i] m ++ monoList c).length : ℤ) = e := by
    simp only [List.length_append, listPow_length, monoList_length, List.length_singleton,
      Nat.cast_add, mul_one]
    omega
  rw [mulMono, M.mulList_perm hperm d e (by rw [monoList_length]; exact h) hlen,
    M.mulList_append _ _ d (d + (m : ℤ)) e hlen1 hlen2 hlen]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show M.mulList (listPow [i] m) d (d + (m : ℤ)) hlen1
      = M.mulPow i m d (d + (m : ℤ)) rfl from rfl, hx, map_zero]

/-- A form of degree at least `(n+1) * m` kills anything killed by every `xᵢ^m`. -/
lemma mulForm_eq_zero_of_torsion (M : GradedModule k n) (D : ℕ) (d e : ℤ)
    (h : d + (D : ℤ) = e) (p : polySubmodule k n (D : ℤ)) {m : ℕ} (hm : 1 ≤ m)
    (hD : (n + 1) * m ≤ D) (x : M.obj d)
    (hx : ∀ i : Fin (n + 1), (M.mulPow i m d (d + (m : ℤ)) rfl).hom x = 0) :
    mulForm M D d e h p x = 0 := by
  rw [mulForm_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hdeg : b.1.degree = D := b.2
  obtain ⟨i, hi⟩ := exists_le_of_le_degree hm (by rw [hdeg]; exact hD)
  rw [mulMono_eq_zero_of_mulPow M i hi d e _ x (hx i), smul_zero]

/-- The integer-degree form of the previous lemma. -/
lemma mulFormZ_eq_zero_of_torsion (M : GradedModule k n) (a d e : ℤ) (h : d + a = e)
    (p : polySubmodule k n a) {m : ℕ} (hm : 1 ≤ m) (ha : (((n + 1) * m : ℕ) : ℤ) ≤ a)
    (x : M.obj d)
    (hx : ∀ i : Fin (n + 1), (M.mulPow i m d (d + (m : ℤ)) rfl).hom x = 0) :
    mulFormZ M a d e h p x = 0 := by
  rw [mulFormZ_of_nonneg M (le_trans (Int.natCast_nonneg _) ha) d e h]
  exact mulForm_eq_zero_of_torsion M a.toNat d e _ _ hm (by omega) x hx

/-! ## The irrelevant torsion vanishes in large degrees -/

lemma subι_val_mulPow (M : GradedModule k n) (p : ∀ d : ℤ, Submodule k (M.obj d))
    (hp : ∀ (i : Fin (n + 1)) (d : ℤ), ∀ x ∈ p d, (M.mulX i d).hom x ∈ p (d + 1))
    (i : Fin (n + 1)) (m : ℕ) (d e : ℤ) (h : d + (m : ℤ) = e)
    (x : (sub M p hp).obj d) :
    ((subι M p hp).app e).hom (((sub M p hp).mulPow i m d e h).hom x)
      = (M.mulPow i m d e h).hom (((subι M p hp).app d).hom x) :=
  (congrArg (fun g : (sub M p hp).obj d ⟶ M.obj e => g.hom x)
    (comm_mulList (subι M p hp) (listPow [i] m) d e (by simpa using h))).symm

/-- A finitely generated irrelevant torsion module vanishes in all large degrees: its
finitely many generators are killed by a uniform power of every variable, and every
monomial of large enough degree contains one such power. -/
theorem exists_subsingleton_irrTors (M : GradedModule k n) (hM : IsFG M) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → Subsingleton (M.irrTors.obj d) := by
  classical
  obtain ⟨hfd, hlow, d₀, hgen⟩ := isFG_irrTors M hM
  haveI : FiniteDimensional k (M.irrTors.obj d₀) := hfd d₀
  set s := Module.finrank k (M.irrTors.obj d₀) with hs
  set y : Fin s → M.irrTors.obj d₀ :=
    fun t => (Module.finBasis k (M.irrTors.obj d₀)) t with hy
  have hyspan : Submodule.span k (Set.range y) = ⊤ :=
    (Module.finBasis k (M.irrTors.obj d₀)).span_eq
  choose mm hmm using fun (t : Fin s) (i : Fin (n + 1)) =>
    (M.mem_irrTorsSub.mp (y t).2) i
  set m : ℕ := 1 + (Finset.univ : Finset (Fin s × Fin (n + 1))).sup
    (fun z => mm z.1 z.2) with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmle : ∀ (t : Fin s) (i : Fin (n + 1)), mm t i ≤ m := by
    intro t i
    have hsup : mm t i ≤ (Finset.univ : Finset (Fin s × Fin (n + 1))).sup
        (fun z => mm z.1 z.2) :=
      Finset.le_sup (f := fun z : Fin s × Fin (n + 1) => mm z.1 z.2)
        (Finset.mem_univ (t, i))
    omega
  have hkill : ∀ (t : Fin s) (i : Fin (n + 1)),
      (M.irrTors.mulPow i m d₀ (d₀ + (m : ℤ)) rfl).hom (y t) = 0 := by
    intro t i
    refine Subtype.ext ?_
    show ((subι M M.irrTorsSub M.irrTorsSub_mulX).app (d₀ + (m : ℤ))).hom
      (((sub M M.irrTorsSub M.irrTorsSub_mulX).mulPow i m d₀ (d₀ + (m : ℤ)) rfl).hom
        (y t)) = 0
    rw [subι_val_mulPow M M.irrTorsSub M.irrTorsSub_mulX i m d₀ (d₀ + (m : ℤ)) rfl (y t)]
    exact M.mulPow_eq_zero_of_le i (hmle t i) d₀ (d₀ + ((mm t i : ℕ) : ℤ))
      (d₀ + (m : ℤ)) rfl rfl _ (hmm t i)
  refine ⟨d₀ + (((n + 1) * m : ℕ) : ℤ), fun d hd => ?_⟩
  have hdd₀ : d₀ ≤ d := by
    have : (0 : ℤ) ≤ (((n + 1) * m : ℕ) : ℤ) := Int.natCast_nonneg _
    omega
  have hzero : ∀ z : M.irrTors.obj d, z = 0 := by
    intro z
    obtain ⟨q, hq⟩ := surjective_freeGenHom_app M.irrTors d₀ y hyspan hgen d hdd₀ z
    rw [← hq, freeGenHom_app_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    exact mulFormZ_eq_zero_of_torsion M.irrTors (d + -d₀) d₀ d (by ring) (q t) hm1
      (by omega) (y t) (fun i => hkill t i)
  exact ⟨fun z w => by rw [hzero z, hzero w]⟩

/-! ## The torsion-free model -/

lemma range_irrTorsι (d : ℤ) :
    LinearMap.range ((M.irrTorsι.app d).hom) = M.irrTorsSub d :=
  Submodule.range_subtype _

lemma toCoker_irrTorsι_eq_zero_iff (d : ℤ) (x : M.obj d) :
    ((toCoker M.irrTorsι).app d).hom x = 0 ↔ x ∈ M.irrTorsSub d := by
  rw [toCoker_app]
  show (LinearMap.range (M.irrTorsι.app d).hom).mkQ x = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, range_irrTorsι]

/-- The quotient by the irrelevant torsion has no irrelevant torsion: the torsion
submodule is saturated. -/
theorem noIrrelevantTorsion_coker_irrTorsι :
    NoIrrelevantTorsion (coker M.irrTorsι) := by
  intro d z hz
  obtain ⟨x, rfl⟩ := surjective_toCoker_app M.irrTorsι d z
  rw [toCoker_irrTorsι_eq_zero_iff]
  intro i
  obtain ⟨a, ha⟩ := hz i
  have hcomm := comm_mulList (toCoker M.irrTorsι) (listPow [i] a) d (d + (a : ℤ))
    (by simp)
  have happ := congrArg
    (fun g : M.obj d ⟶ (coker M.irrTorsι).obj (d + (a : ℤ)) => g.hom x) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  have hmem : (M.mulPow i a d (d + (a : ℤ)) rfl).hom x ∈ M.irrTorsSub (d + (a : ℤ)) := by
    rw [← toCoker_irrTorsι_eq_zero_iff]
    rw [show (M.mulPow i a d (d + (a : ℤ)) rfl).hom x
      = (M.mulList (listPow [i] a) d (d + (a : ℤ)) (by simp)).hom x from rfl, ← happ]
    exact ha
  obtain ⟨b, hb⟩ := hmem i
  refine ⟨a + b, M.mulPow_eq_zero_congr i (a + b) d (d + (a : ℤ) + (b : ℤ))
    (d + ((a + b : ℕ) : ℤ)) (by push_cast; ring) rfl x ?_⟩
  rw [M.mulPow_add i a b d (d + (a : ℤ)) (d + (a : ℤ) + (b : ℤ)) rfl rfl
    (by push_cast; ring)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hb

lemma injective_toCoker_irrTorsι {d : ℤ} (h : Subsingleton (M.irrTors.obj d)) :
    Function.Injective (((toCoker M.irrTorsι).app d).hom) := by
  intro a b hab
  have h0 : ((toCoker M.irrTorsι).app d).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [toCoker_irrTorsι_eq_zero_iff] at h0
  haveI : Subsingleton (M.irrTorsSub d) := h
  have hz : (⟨a - b, h0⟩ : M.irrTorsSub d) = 0 := Subsingleton.elim _ _
  have := congrArg Subtype.val hz
  simpa [sub_eq_zero] using this

/-- If the first term of a short exact sequence has no Čech cohomology, the second map is an
isomorphism on cohomology in every degree. -/
lemma bijective_cechHgrMap_of_shortExact_of_subsingleton_left
    {A B C : GradedModule k n} {u : A ⟶ B} {v : B ⟶ C} (hSE : ShortExact u v)
    (hA : ∀ (i : ℕ) (d : ℤ), Subsingleton ((A.cechHgr i).obj d)) (i : ℕ) (d : ℤ) :
    Function.Bijective ((cechHgrMap v i).app d).hom := by
  refine ⟨?_, ?_⟩
  · intro x z hxz
    have h0 : ((cechHgrMap v i).app d).hom (x - z) = 0 := by
      rw [map_sub, hxz, sub_self]
    obtain ⟨w, hw⟩ := (cech_exact_map_map hSE i d _).mp h0
    haveI := hA i d
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact sub_eq_zero.mp hw.symm
  · intro z
    haveI := hA (i + 1) d
    exact (cech_exact_map_δ hSE i d z).mp (Subsingleton.elim _ _)

/-- **The torsion-free model.**  Every finitely generated graded module surjects onto a
finitely generated module with no irrelevant torsion, isomorphically in all large degrees
and isomorphically on Čech cohomology: the `exists_noIrrelevantTorsion_quotient` field of
`CechSerreData`. -/
theorem exists_noIrrelevantTorsion_quotient_of_isFG (hM : IsFG M) :
    ∃ (N : GradedModule k n) (φ : M ⟶ N), IsFG N ∧ NoIrrelevantTorsion N ∧
      (∀ d, Function.Surjective (φ.app d).hom) ∧
      (∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Function.Injective (φ.app d).hom) ∧
      (∀ (i : ℕ) (d : ℤ), Function.Bijective ((cechHgrMap φ i).app d).hom) := by
  obtain ⟨d₁, hd₁⟩ := exists_subsingleton_irrTors M hM
  refine ⟨coker M.irrTorsι, toCoker M.irrTorsι, IsFG.coker M.irrTorsι hM,
    M.noIrrelevantTorsion_coker_irrTorsι, surjective_toCoker_app M.irrTorsι,
    ⟨d₁, fun d hd => M.injective_toCoker_irrTorsι (hd₁ d hd)⟩, fun i d => ?_⟩
  refine bijective_cechHgrMap_of_shortExact_of_subsingleton_left
    (shortExact_toCoker M.irrTorsι M.injective_irrTorsι) ?_ i d
  intro i' d'
  exact subsingleton_cechHgr_of_eventually_zero _ ⟨d₁, hd₁⟩ i' d'

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
