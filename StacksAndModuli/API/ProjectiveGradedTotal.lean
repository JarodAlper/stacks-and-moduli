module

public import StacksAndModuli.API.ProjectiveGradedTorsion
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.GroupTheory.CosetCover

/-!
# The total module of a graded module

Supporting API with no Stacks Project counterpart.

`GradedModule k n` is a diagram of `k`-vector spaces with commuting degree-raising maps.
This file assembles the diagram into a genuine module `Total M = ⨁_d M_d` over
`S = k[x₀,…,x_n]`, so that the commutative algebra of `Mathlib` — noetherianity, finitely
many associated primes, zerodivisors as the union of the associated primes — becomes
available.  Its purpose is the `exists_nonZeroDivisor_linearForm` field of `CechSerreData`:
a general linear form avoids the finitely many associated primes of a finitely generated
module with no irrelevant torsion.

Main declarations:
- `GradedModule.Total`, with its `MvPolynomial`-module structure;
- `GradedModule.exists_nonZeroDivisor_linearForm_of_infinite`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {n : ℕ}

section CommRing

variable {k : Type u} [CommRing k]

/-! ## Multiplication by a monomial is multiplicative -/

lemma monoList_add_multiset (b b' : Fin (n + 1) →₀ ℕ) :
    ((monoList (b + b') : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = ((monoList b : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
        + ((monoList b' : List (Fin (n + 1))) : Multiset (Fin (n + 1))) := by
  rw [monoList_coe, monoList_coe, monoList_coe, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Finsupp.add_apply, Multiset.replicate_add]

lemma finsupp_degree_add (b b' : Fin (n + 1) →₀ ℕ) :
    (b + b').degree = b.degree + b'.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply]
  exact Finset.sum_add_distrib

lemma mulMono_add (M : GradedModule k n) (b b' : Fin (n + 1) →₀ ℕ) (d e f : ℤ)
    (h₁ : d + (b.degree : ℤ) = e) (h₂ : e + (b'.degree : ℤ) = f)
    (h : d + (((b + b').degree : ℕ) : ℤ) = f) :
    M.mulMono (b + b') d f h = M.mulMono b d e h₁ ≫ M.mulMono b' e f h₂ := by
  have hperm : (monoList (b + b')).Perm (monoList b ++ monoList b') :=
    Multiset.coe_eq_coe.mp (by
      rw [monoList_add_multiset, ← Multiset.coe_add])
  have hlen : d + ((monoList b ++ monoList b').length : ℤ) = f := by
    rw [List.length_append, monoList_length, monoList_length]
    push_cast
    omega
  rw [mulMono, M.mulList_perm hperm d f (by rw [monoList_length]; exact h) hlen]
  exact M.mulList_append _ _ d e f (by rw [monoList_length]; exact h₁)
    (by rw [monoList_length]; exact h₂) hlen

lemma mulMono_add' (M : GradedModule k n) (c b b' : Fin (n + 1) →₀ ℕ) (hc : c = b + b')
    (d e f : ℤ) (h₁ : d + (b.degree : ℤ) = e) (h₂ : e + (b'.degree : ℤ) = f)
    (h : d + ((c.degree : ℕ) : ℤ) = f) :
    M.mulMono c d f h = M.mulMono b d e h₁ ≫ M.mulMono b' e f h₂ := by
  subst hc
  exact M.mulMono_add b b' d e f h₁ h₂ h

lemma monoList_zero : (monoList (0 : Fin (n + 1) →₀ ℕ)) = [] := by
  simp [monoList]

lemma mulMono_zero (M : GradedModule k n) (d e : ℤ)
    (h : d + (((0 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ) = e) :
    M.mulMono 0 d e h = eqToHom (congrArg M.obj (by simpa using h)) := by
  have hperm : (monoList (0 : Fin (n + 1) →₀ ℕ)).Perm ([] : List (Fin (n + 1))) := by
    rw [monoList_zero]
  rw [mulMono, M.mulList_perm hperm d e (by rw [monoList_length]; exact h)
    (by simpa using h)]
  rfl

lemma monoList_single (i : Fin (n + 1)) :
    ((monoList (Finsupp.single i 1) : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
      = ({i} : Multiset (Fin (n + 1))) := by
  have := monoList_add_single (0 : Fin (n + 1) →₀ ℕ) i
  rw [zero_add, monoList_zero] at this
  simpa using this

lemma mulMono_single (M : GradedModule k n) (i : Fin (n + 1)) (d e : ℤ)
    (h : d + (((Finsupp.single i 1 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ) = e) :
    M.mulMono (Finsupp.single i 1) d e h = M.mulX' i d e (by simpa using h) := by
  have hperm : (monoList (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ)).Perm [i] :=
    Multiset.coe_eq_coe.mp (by rw [monoList_single]; rfl)
  rw [mulMono, M.mulList_perm hperm d e (by rw [monoList_length]; exact h)
    (by simpa using h), mulList_singleton]

/-! ## The total module -/

/-- The total module `⨁_d M_d` of a graded module, regarded below as a module over
`k[x₀,…,x_n]`. -/
def Total (M : GradedModule k n) : Type u := DirectSum ℤ fun d => (M.obj d : Type u)

namespace Total

variable (M : GradedModule k n)

instance : AddCommGroup (Total M) :=
  inferInstanceAs (AddCommGroup (DirectSum ℤ fun d => (M.obj d : Type u)))

instance : Module k (Total M) :=
  inferInstanceAs (Module k (DirectSum ℤ fun d => (M.obj d : Type u)))

/-- The inclusion of the degree-`d` piece into the total module. -/
def tof (d : ℤ) : M.obj d →ₗ[k] Total M :=
  DirectSum.lof k ℤ (fun d => (M.obj d : Type u)) d

/-- The projection onto the degree-`d` piece. -/
def tcomp (d : ℤ) : Total M →ₗ[k] M.obj d :=
  DirectSum.component k ℤ (fun d => (M.obj d : Type u)) d

@[simp] lemma tcomp_tof (d : ℤ) (x : M.obj d) : tcomp M d (tof M d x) = x := by
  show DirectSum.component k ℤ (fun d => (M.obj d : Type u)) d
    (DirectSum.lof k ℤ (fun d => (M.obj d : Type u)) d x) = x
  simp

lemma injective_tof (d : ℤ) : Function.Injective (tof M d) := by
  intro x z h
  have := congrArg (tcomp M d) h
  rwa [tcomp_tof, tcomp_tof] at this

lemma total_ext {f g : Total M →ₗ[k] Total M}
    (h : ∀ (d : ℤ) (x : M.obj d), f (tof M d x) = g (tof M d x)) : f = g :=
  DirectSum.linearMap_ext k fun d => LinearMap.ext fun x => h d x

/-! ## Multiplication by a monomial on the total module -/

/-- Multiplication by the monomial `x^b`, as an endomorphism of the total module. -/
def actMono (b : Fin (n + 1) →₀ ℕ) : Total M →ₗ[k] Total M :=
  DirectSum.toModule k ℤ (Total M) fun d =>
    (tof M (d + (b.degree : ℤ))).comp (M.mulMono b d (d + (b.degree : ℤ)) rfl).hom

lemma actMono_tof (b : Fin (n + 1) →₀ ℕ) {d e : ℤ} (h : d + (b.degree : ℤ) = e)
    (x : M.obj d) :
    actMono M b (tof M d x) = tof M e ((M.mulMono b d e h).hom x) := by
  subst h
  exact DirectSum.toModule_lof (R := k) (ι := ℤ)
    (M := fun d => (M.obj d : Type u)) (N := Total M) d x

lemma actMono_zero : actMono M 0 = LinearMap.id := by
  refine total_ext M fun d x => ?_
  rw [actMono_tof M 0 (show d + (((0 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ) = d by simp) x,
    mulMono_zero M d d (by simp)]
  simp

lemma actMono_add (b b' : Fin (n + 1) →₀ ℕ) :
    actMono M (b + b') = (actMono M b).comp (actMono M b') := by
  refine total_ext M fun d x => ?_
  have hdeg : (((b + b').degree : ℕ) : ℤ) = ((b'.degree : ℕ) : ℤ) + ((b.degree : ℕ) : ℤ) := by
    rw [finsupp_degree_add]
    push_cast
    ring
  rw [actMono_tof M (b + b') (show d + (((b + b').degree : ℕ) : ℤ)
      = d + (b'.degree : ℤ) + (b.degree : ℤ) from by rw [hdeg]; ring) x,
    LinearMap.comp_apply, actMono_tof M b' (rfl : d + (b'.degree : ℤ) = _) x,
    actMono_tof M b (rfl : d + (b'.degree : ℤ) + (b.degree : ℤ) = _)]
  congr 1
  exact congrArg (fun g : M.obj d ⟶ M.obj (d + (b'.degree : ℤ) + (b.degree : ℤ)) => g.hom x)
    (M.mulMono_add' (b + b') b' b (add_comm b b') d (d + (b'.degree : ℤ))
      (d + (b'.degree : ℤ) + (b.degree : ℤ)) rfl rfl _)

/-- Multiplication by monomials, as a monoid homomorphism. -/
def actMonoHom : Multiplicative (Fin (n + 1) →₀ ℕ) →* Module.End k (Total M) where
  toFun b := actMono M (Multiplicative.toAdd b)
  map_one' := actMono_zero M
  map_mul' b b' := actMono_add M _ _

/-- The action of `k[x₀,…,x_n]` on the total module. -/
def act : MvPolynomial (Fin (n + 1)) k →+* Module.End k (Total M) :=
  (AddMonoidAlgebra.liftNCRingHom (k := k) (G := (Fin (n + 1) →₀ ℕ))
      (algebraMap k (Module.End k (Total M))) (actMonoHom M)
      (fun a y => Algebra.commutes a (actMonoHom M y)) :
    AddMonoidAlgebra k (Fin (n + 1) →₀ ℕ) →+* Module.End k (Total M))

instance : Module (MvPolynomial (Fin (n + 1)) k) (Total M) :=
  Module.compHom _ (act M)

lemma smul_def (p : MvPolynomial (Fin (n + 1)) k) (t : Total M) : p • t = act M p t := rfl

lemma tcomp_tof_ne {d e : ℤ} (hde : e ≠ d) (x : M.obj e) : tcomp M d (tof M e x) = 0 := by
  show DirectSum.component k ℤ (fun d => (M.obj d : Type u)) d
    (DirectSum.lof k ℤ (fun d => (M.obj d : Type u)) e x) = 0
  rw [DirectSum.component.of, dif_neg hde]

/-! ## Computing the action -/

lemma monomial_smul_tof (b : Fin (n + 1) →₀ ℕ) (c : k) {d e : ℤ}
    (h : d + (b.degree : ℤ) = e) (x : M.obj d) :
    (monomial b c : MvPolynomial (Fin (n + 1)) k) • tof M d x
      = c • tof M e ((M.mulMono b d e h).hom x) := by
  rw [smul_def, act]
  show (AddMonoidAlgebra.liftNCRingHom (k := k) (G := (Fin (n + 1) →₀ ℕ))
      (algebraMap k (Module.End k (Total M))) (actMonoHom M)
      (fun a y => Algebra.commutes a (actMonoHom M y)))
    (AddMonoidAlgebra.single b c) (tof M d x) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  show (algebraMap k (Module.End k (Total M)) c) (actMono M b (tof M d x)) = _
  rw [actMono_tof M b h x]
  rfl

lemma X_smul_tof (i : Fin (n + 1)) {d e : ℤ} (h : d + 1 = e) (x : M.obj d) :
    (X i : MvPolynomial (Fin (n + 1)) k) • tof M d x
      = tof M e ((M.mulX' i d e h).hom x) := by
  have hdeg : d + (((Finsupp.single i 1 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ) = e := by
    simpa using h
  rw [show (X i : MvPolynomial (Fin (n + 1)) k)
      = monomial (Finsupp.single i 1) (1 : k) from rfl,
    monomial_smul_tof M _ _ hdeg x, one_smul, mulMono_single M i d e hdeg]

lemma act_C (a : k) : act M (C a) = algebraMap k (Module.End k (Total M)) a := by
  show act M (monomial 0 a) = _
  show (AddMonoidAlgebra.liftNCRingHom (k := k) (G := (Fin (n + 1) →₀ ℕ))
      (algebraMap k (Module.End k (Total M))) (actMonoHom M)
      (fun a y => Algebra.commutes a (actMonoHom M y)))
    (AddMonoidAlgebra.single 0 a) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  show (algebraMap k (Module.End k (Total M))) a * actMono M 0 = _
  rw [actMono_zero]
  exact mul_one _

instance : IsScalarTower k (MvPolynomial (Fin (n + 1)) k) (Total M) where
  smul_assoc a p t := by
    show act M (a • p) t = a • act M p t
    rw [smul_eq_C_mul, map_mul, act_C]
    rfl

/-- The linear form with coefficients `c`, as a polynomial. -/
def linForm (c : Fin (n + 1) → k) : MvPolynomial (Fin (n + 1)) k :=
  ∑ i, monomial (Finsupp.single i 1) (c i)

lemma linForm_eq_sum_X (c : Fin (n + 1) → k) :
    linForm c = ∑ i, c i • (X i : MvPolynomial (Fin (n + 1)) k) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (X i : MvPolynomial (Fin (n + 1)) k)
    = monomial (Finsupp.single i 1) (1 : k) from rfl, smul_monomial, smul_eq_mul, mul_one]

lemma linForm_smul_tof (c : Fin (n + 1) → k) {d e : ℤ} (h : d + 1 = e) (x : M.obj d) :
    linForm c • tof M d x = tof M e ((M.mulL c d e h).hom x) := by
  have hdeg : d + (((Finsupp.single (0 : Fin (n + 1)) 1 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ)
      = e := by simpa using h
  rw [linForm, Finset.sum_smul, mulL]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdeg' : d + (((Finsupp.single i 1 : Fin (n + 1) →₀ ℕ).degree : ℕ) : ℤ) = e := by
    simpa using h
  rw [monomial_smul_tof M (Finsupp.single i 1) (c i) hdeg' x, mulMono_single M i d e hdeg']

lemma tcomp_X_smul (i : Fin (n + 1)) (d : ℤ) (t : Total M) :
    tcomp M (d + 1) ((X i : MvPolynomial (Fin (n + 1)) k) • t)
      = (M.mulX' i d (d + 1) rfl).hom (tcomp M d t) := by
  induction t using DirectSum.induction_on with
  | zero => simp
  | of e y =>
      rw [show (DirectSum.of (fun d => (M.obj d : Type u)) e y : Total M) = tof M e y from rfl,
        X_smul_tof M i (rfl : e + 1 = e + 1) y]
      by_cases he : e = d
      · subst he
        rw [tcomp_tof, tcomp_tof]
      · rw [tcomp_tof_ne M (by omega), tcomp_tof_ne M he, map_zero]
  | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, map_add]

/-! ## The total module of a finitely generated graded module is finitely generated -/

lemma degree_listExp (l : List (Fin (n + 1))) : (listExp l).degree = l.length := by
  have h1 : ((monoList (listExp l) : List (Fin (n + 1))) :
      Multiset (Fin (n + 1))).card = ((l : List (Fin (n + 1))) :
      Multiset (Fin (n + 1))).card := congrArg Multiset.card (monoList_listExp_coe l)
  simpa [monoList_length] using h1

lemma tof_mem_of_le {d₀ d : ℤ} (hd : d₀ ≤ d)
    (hgen : ∀ e : ℤ, d₀ ≤ e → M.mulSpan e (e + 1) = ⊤)
    (W : Submodule (MvPolynomial (Fin (n + 1)) k) (Total M))
    (hW : ∀ z : M.obj d₀, tof M d₀ z ∈ W) (x : M.obj d) : tof M d x ∈ W := by
  have hx : x ∈ M.mulSpan d₀ d := by
    rw [mulSpan_top_of_gen M d₀ hgen d hd]
    trivial
  refine Submodule.iSup_induction (motive := fun y => tof M d y ∈ W) _ hx ?_ ?_ ?_
  · rintro l _ ⟨z, rfl⟩
    have hdeg : d₀ + (((listExp l.1).degree : ℕ) : ℤ) = d := by
      rw [degree_listExp]
      exact l.2
    have hone : tof M d ((M.mulMono (listExp l.1) d₀ d hdeg).hom z)
        = (monomial (listExp l.1) (1 : k) : MvPolynomial (Fin (n + 1)) k) • tof M d₀ z := by
      rw [monomial_smul_tof M (listExp l.1) (1 : k) hdeg z, one_smul]
    rw [mulList_eq_mulMono M l.1 d₀ d l.2 hdeg, hone]
    exact Submodule.smul_mem _ _ (hW z)
  · rw [map_zero]
    exact W.zero_mem
  · intro a b ha hb
    rw [map_add]
    exact W.add_mem ha hb

theorem finite_total (hM : IsFG M) :
    Module.Finite (MvPolynomial (Fin (n + 1)) k) (Total M) := by
  classical
  obtain ⟨hfd, ⟨lo, hlow⟩, d₀, hgen⟩ := hM
  let r : ℤ → ℕ := fun d => Classical.choose
    (Module.Finite.exists_fin (R := k) (M := (M.obj d : Type u)))
  let y : ∀ d : ℤ, Fin (r d) → M.obj d := fun d => Classical.choose
    (Classical.choose_spec
      (Module.Finite.exists_fin (R := k) (M := (M.obj d : Type u))))
  have hy : ∀ d : ℤ, Submodule.span k (Set.range (y d)) = ⊤ := fun d =>
    Classical.choose_spec (Classical.choose_spec
      (Module.Finite.exists_fin (R := k) (M := (M.obj d : Type u))))
  set bs : Finset (Total M) := (Finset.Icc lo d₀).biUnion (fun d =>
    (Finset.univ : Finset (Fin (r d))).image (fun t => tof M d (y d t))) with hbs
  set W : Submodule (MvPolynomial (Fin (n + 1)) k) (Total M) :=
    Submodule.span (MvPolynomial (Fin (n + 1)) k) (bs : Set (Total M)) with hW
  have hmid : ∀ (d : ℤ), lo ≤ d → d ≤ d₀ → ∀ x : M.obj d, tof M d x ∈ W := by
    intro d hlo hhi x
    have hspan : Submodule.map (tof M d)
        (Submodule.span k (Set.range (y d)))
          ≤ (W.restrictScalars k) := by
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine Submodule.subset_span ?_
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨d, ?_, ?_⟩)
      · exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    exact hspan ⟨x, by rw [hy d]; trivial, rfl⟩
  have hlowz : ∀ (d : ℤ), d < lo → ∀ x : M.obj d, tof M d x ∈ W := by
    intro d hd x
    haveI := hlow d hd
    rw [Subsingleton.elim x 0, map_zero]
    exact W.zero_mem
  have hall : ∀ (d : ℤ) (x : M.obj d), tof M d x ∈ W := by
    intro d x
    rcases lt_or_ge d lo with h | h
    · exact hlowz d h x
    rcases le_or_gt d d₀ with h' | h'
    · exact hmid d h h' x
    · refine tof_mem_of_le M (le_of_lt h') hgen W (fun z => ?_) x
      rcases lt_or_ge d₀ lo with h₀ | h₀
      · exact hlowz d₀ h₀ z
      · exact hmid d₀ h₀ le_rfl z
  refine ⟨⟨bs, le_antisymm le_top ?_⟩⟩
  intro t _
  induction t using DirectSum.induction_on with
  | zero => exact W.zero_mem
  | of d x => exact hall d x
  | add t₁ t₂ h₁ h₂ => exact W.add_mem (h₁ trivial) (h₂ trivial)

/-- A total module with no irrelevant torsion has no element killed by all the
variables. -/
lemma eq_zero_of_X_smul_eq_zero (hM : NoIrrelevantTorsion M) (t : Total M)
    (ht : ∀ i : Fin (n + 1), (X i : MvPolynomial (Fin (n + 1)) k) • t = 0) : t = 0 := by
  refine DFinsupp.ext fun d => ?_
  show tcomp M d t = 0
  refine hM d (tcomp M d t) fun i => ⟨1, ?_⟩
  have h := congrArg (tcomp M (d + 1)) (ht i)
  rw [tcomp_X_smul M i d t, map_zero] at h
  show (M.mulList [i] d (d + ((1 : ℕ) : ℤ)) (by simp)).hom (tcomp M d t) = 0
  rw [mulList_singleton M i d (d + ((1 : ℕ) : ℤ)) (by simp)]
  exact h

lemma linForm_single (i : Fin (n + 1)) :
    linForm (Pi.single i (1 : k)) = (X i : MvPolynomial (Fin (n + 1)) k) := by
  rw [linForm, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, map_zero]) (fun hc => absurd (Finset.mem_univ i) hc)]
  rw [Pi.single_eq_same]
  rfl

/-- The linear form with coefficients `c`, as a `k`-linear function of `c`. -/
def linFormHom : (Fin (n + 1) → k) →ₗ[k] MvPolynomial (Fin (n + 1)) k where
  toFun c := linForm c
  map_add' c c' := by
    simp only [linForm, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add]
  map_smul' a c := by
    simp only [linForm, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, ← map_smul, smul_eq_mul]

@[simp] lemma linFormHom_apply (c : Fin (n + 1) → k) : linFormHom c = linForm c := rfl

end Total

end CommRing

/-! ## Prime avoidance: a general linear form is a nonzerodivisor -/

variable {k : Type u} [Field k]

open Total in
/-- **A general hyperplane avoids the associated points.**  Over an infinite field, two
finitely generated graded modules with no irrelevant torsion admit a common linear form
acting injectively in every degree: the `exists_nonZeroDivisor_linearForm` field of
`CechSerreData`.  The proof passes to the total modules over `k[x₀,…,x_{n+1}]`, where the
zerodivisors are the union of the finitely many associated primes, and no associated prime
contains all the variables. -/
theorem exists_nonZeroDivisor_linearForm_of_infinite (hk : Infinite k)
    (M M' : GradedModule k (n + 1)) (hM : IsFG M) (hM' : IsFG M')
    (hT : NoIrrelevantTorsion M) (hT' : NoIrrelevantTorsion M') :
    ∃ (c : Fin (n + 1 + 1) → k) (j : Fin (n + 1 + 1)), IsUnit (c j) ∧
      (∀ d, Function.Injective ((M.mulLHom c).app d).hom) ∧
      (∀ d, Function.Injective ((M'.mulLHom c).app d).hom) := by
  classical
  haveI := hk
  haveI := finite_total M hM
  haveI := finite_total M' hM'
  haveI hfin : Module.Finite (MvPolynomial (Fin (n + 1 + 1)) k) (Total M × Total M') :=
    inferInstance
  set E := Fin (n + 1 + 1) → k with hE
  set Ass := associatedPrimes (MvPolynomial (Fin (n + 1 + 1)) k) (Total M × Total M') with hAss
  have hAssfin : Ass.Finite := associatedPrimes.finite _ _
  set bad : Finset (Submodule k E) :=
    insert (⊥ : Submodule k E)
      (hAssfin.toFinset.image fun p =>
        Submodule.comap (linFormHom (k := k) (n := n + 1)) (p.restrictScalars k)) with hbad
  have htopnot : (⊤ : Submodule k E) ∉ bad := by
    rw [hbad, Finset.mem_insert]
    rintro (hcon | hcon)
    · exact top_ne_bot hcon
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hcon
      rw [Set.Finite.mem_toFinset] at hp
      obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hp
      have hX : ∀ i : Fin (n + 1 + 1), (X i : MvPolynomial (Fin (n + 1 + 1)) k) ∈ p := by
        intro i
        have hmem : (Pi.single i (1 : k) : E)
            ∈ Submodule.comap (linFormHom (k := k) (n := n + 1)) (p.restrictScalars k) := by
          rw [hpe]
          trivial
        have hval : linFormHom (Pi.single i (1 : k)) ∈ p := hmem
        rwa [linFormHom_apply, linForm_single] at hval
      have hkill : ∀ i : Fin (n + 1 + 1),
          (X i : MvPolynomial (Fin (n + 1 + 1)) k) • x = 0 := by
        intro i
        have hmem := hX i
        rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at hmem
        exact hmem
      have hx0 : x = 0 := by
        refine Prod.ext ?_ ?_
        · exact eq_zero_of_X_smul_eq_zero M hT x.1 (fun i => congrArg Prod.fst (hkill i))
        · exact eq_zero_of_X_smul_eq_zero M' hT' x.2 (fun i => congrArg Prod.snd (hkill i))
      have htop : Submodule.colon (⊥ : Submodule (MvPolynomial (Fin (n + 1 + 1)) k)
          (Total M × Total M')) {x} = ⊤ := by
        rw [hx0]
        refine eq_top_iff.mpr fun r _ => ?_
        rw [Submodule.mem_colon_singleton, smul_zero]
        exact Submodule.zero_mem _
      exact hprime.ne_top (hx.trans htop)
  obtain ⟨c, hc⟩ := Set.ne_univ_iff_exists_notMem _
    |>.mp (Subspace.biUnion_ne_univ_of_top_notMem htopnot)
  have hcne : c ≠ 0 := fun hc0 =>
    hc (Set.mem_biUnion (Finset.mem_insert_self _ _)
      (by rw [hc0]; exact Submodule.zero_mem _))
  have hnzd : ∀ t : Total M × Total M', (linForm c) • t = 0 → t = 0 := by
    intro t htz
    by_contra ht0
    have hmem : (linForm c) ∈ ⋃ p ∈ Ass, (p : Set (MvPolynomial (Fin (n + 1 + 1)) k)) := by
      rw [hAss, biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨t, ht0, htz⟩
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨p, hpA, hp⟩ := hmem
    exact hc (Set.mem_biUnion (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨p, (Set.Finite.mem_toFinset _).mpr hpA, rfl⟩)) hp)
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hcne (funext hcon)
  refine ⟨c, j, hj.isUnit, fun d x z hxz => ?_, fun d x z hxz => ?_⟩
  · have h0 : ((M.mulLHom c).app d).hom (x - z) = 0 := by
      rw [map_sub, hxz, sub_self]
    have hsm : (linForm c) • ((tof M (d + -1) (x - z), 0) : Total M × Total M') = 0 := by
      refine Prod.ext ?_ ?_
      · show (linForm c) • tof M (d + -1) (x - z) = 0
        rw [linForm_smul_tof M c (show d + -1 + 1 = d by ring) (x - z),
          show (M.mulL c (d + -1) d (by ring)).hom (x - z) = 0 from h0, map_zero]
      · exact smul_zero _
    have hfst := congrArg Prod.fst (hnzd _ hsm)
    exact sub_eq_zero.mp (injective_tof M (d + -1) (by simpa using hfst))
  · have h0 : ((M'.mulLHom c).app d).hom (x - z) = 0 := by
      rw [map_sub, hxz, sub_self]
    have hsm : (linForm c) • ((0, tof M' (d + -1) (x - z)) : Total M × Total M') = 0 := by
      refine Prod.ext ?_ ?_
      · exact smul_zero _
      · show (linForm c) • tof M' (d + -1) (x - z) = 0
        rw [linForm_smul_tof M' c (show d + -1 + 1 = d by ring) (x - z),
          show (M'.mulL c (d + -1) d (by ring)).hom (x - z) = 0 from h0, map_zero]
    have hsnd := congrArg Prod.snd (hnzd _ hsm)
    exact sub_eq_zero.mp (injective_tof M' (d + -1) (by simpa using hsnd))

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
