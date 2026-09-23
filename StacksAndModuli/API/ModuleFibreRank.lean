module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Support

/-!
# The fibre rank of a module, and its behaviour under base change

For a module `M` over a commutative ring `R` and a prime `p`, the **fibre rank** is the
dimension of `κ(p) ⊗_R M` over the residue field `κ(p)`.  For a finite module this is, by
Nakayama, the minimal number of generators of `M_p`, so it is the function whose sublevel
sets are the open loci of the flattening stratification (Stacks 05P8 (2)).

The main result is that the fibre rank is insensitive to base change: for an `R`-algebra `A`
and a prime `q` of `A` lying over `p`, the fibre rank of `A ⊗_R M` at `q` equals the fibre
rank of `M` at `p`.  This is what makes the sublevel sets represent a functor on all
`R`-algebras rather than merely being subsets of `Spec R`.

Mathlib's `Module.rankAtStalk` is the rank of `M_p` over `R_p`, which agrees with the fibre
rank only when `M` is flat; `Module.rankAtStalk_baseChange` correspondingly assumes
flatness.  The statements here carry no flatness hypothesis.

Main declarations:

* `Module.fibreFinrank`;
* `Module.fibreFinrank_baseChange` — invariance under base change;
* `Module.fibreFinrank_le_iff_exists_smul_mem_span` — Nakayama: the fibre rank at `p` bounds,
  and is bounded by, the number of generators of `M` near `p`;
* `exists_fin_span_eq_top_of_finrank_le` — extracting a `Fin r`-indexed spanning family;
* `Module.fibreFinrank_eq_rankAtStalk` — for a finite flat module the fibre rank agrees with
  `Module.rankAtStalk`, so (`Module.isLocallyConstant_fibreFinrank`) it inherits local
  constancy from `Module.isLocallyConstant_rankAtStalk`;
* `Module.eq_zero_of_forall_residueField_tmul_eq_zero` and
  `LinearMap.eq_zero_of_forall_baseChange_residueField_eq_zero` — over a *reduced*
  ring, an element of, or a map into, a projective module is detected by its fibres.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open TensorProduct

universe u v

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The **fibre rank** of `M` at a prime `p`: the dimension of `κ(p) ⊗_R M` over the
residue field `κ(p)`.

For a finite module this is the minimal number of generators of `M_p`. -/
def fibreFinrank (p : PrimeSpectrum R) : ℕ :=
  Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)

variable {R M}

theorem fibreFinrank_eq_of_equiv {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : PrimeSpectrum R) :
    fibreFinrank R M p = fibreFinrank R N p :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl p.asIdeal.ResidueField p.asIdeal.ResidueField) e).finrank_eq

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A] (M)

/-- **The fibre rank is a base-change invariant.**  For an `R`-algebra `A` and a prime `q` of
`A`, the fibre rank of `A ⊗_R M` at `q` is the fibre rank of `M` at the prime below `q`.

Both fibres are the same vector space up to extension of scalars along `κ(p) → κ(q)`, and
extension of scalars along a field extension preserves dimension.  The algebra structure
`κ(p) → κ(q)` is not an instance in Mathlib; it is produced here by localizing at the two
primes and using that the induced map is local. -/
theorem fibreFinrank_baseChange (q : PrimeSpectrum A) :
    fibreFinrank A (A ⊗[R] M) q =
      fibreFinrank R M (q.comap (algebraMap R A)) := by
  set p : PrimeSpectrum R := q.comap (algebraMap R A) with hp
  haveI : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq
      (p := p.asIdeal) (P := q.asIdeal)]
    infer_instance
  -- `κ(q) ⊗_A (A ⊗_R M) ≅ κ(q) ⊗_R M ≅ κ(q) ⊗_{κ(p)} (κ(p) ⊗_R M)`.
  let e₁ : q.asIdeal.ResidueField ⊗[A] (A ⊗[R] M) ≃ₗ[q.asIdeal.ResidueField]
      q.asIdeal.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R A _ _ M
  let e₂ : q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
        (p.asIdeal.ResidueField ⊗[R] M) ≃ₗ[q.asIdeal.ResidueField]
      q.asIdeal.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R _ _ _ M
  rw [fibreFinrank, fibreFinrank, e₁.finrank_eq, ← e₂.finrank_eq]
  exact Module.finrank_baseChange

end BaseChange

section Flat

/-- **The fibre rank of a finite flat module is its rank at the stalk.**

For a general module the two invariants differ: `fibreFinrank` is the minimal number of
generators of `M_p`, while `rankAtStalk` is the rank of `M_p` over `R_p` (and is `0` unless
`M_p` is free).  They agree exactly when `M_p` is free, which for a finite module is
flatness.

This is `Module.rankAtStalk_eq` of Mathlib, restated in terms of `fibreFinrank`. -/
theorem fibreFinrank_eq_rankAtStalk (A : Type u) [CommRing A] (N : Type v)
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Flat A N]
    (q : PrimeSpectrum A) :
    fibreFinrank A N q = Module.rankAtStalk N q :=
  (Module.rankAtStalk_eq q).symm

/-- **The fibre rank of a finite flat finitely presented module is locally constant.**

This is `Module.isLocallyConstant_rankAtStalk` transported along
`Module.fibreFinrank_eq_rankAtStalk`; stated for the fibre rank it says that the dimension
of `κ(p) ⊗_R M` over `κ(p)` does not jump, which is the form in which local constancy is
used for families. -/
theorem isLocallyConstant_fibreFinrank [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (fibreFinrank R M) := by
  have h : fibreFinrank R M = rankAtStalk M :=
    funext fun p ↦ fibreFinrank_eq_rankAtStalk R M p
  rw [h]
  exact isLocallyConstant_rankAtStalk

end Flat

section Reduced

/-- **Over a reduced ring a projective module embeds into the product of its fibres**: an
element that dies in `κ(p) ⊗ N` for every prime `p` is zero.

For a free module this is the statement that a coordinate lying in every prime lies in the
nilradical, hence is zero; the projective case follows by splitting off a free module.  This
fails without reducedness — over `k[ε]/ε²` the element `ε` dies in the unique fibre. -/
theorem eq_zero_of_forall_residueField_tmul_eq_zero {R : Type u} [CommRing R] [IsReduced R]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N] (n : N)
    (h : ∀ p : PrimeSpectrum R, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] n = 0) : n = 0 := by
  classical
  obtain ⟨F, _, _, _, i, s, hsi⟩ := Module.Projective.iff_split.mp ‹Module.Projective R N›
  set b := Module.Free.chooseBasis R F with hb
  have hi : i n = 0 := by
    refine b.ext_elem fun j ↦ ?_
    rw [map_zero, Finsupp.zero_apply]
    have hmem : ∀ p : PrimeSpectrum R, b.repr (i n) j ∈ p.asIdeal := by
      intro p
      have h1 : (1 : p.asIdeal.ResidueField) ⊗ₜ[R] (i n) = 0 := by
        have := congrArg (LinearMap.baseChange p.asIdeal.ResidueField i) (h p)
        simpa using this
      have h2 := congrArg (fun z ↦ (b.baseChange p.asIdeal.ResidueField).repr z j) h1
      simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
        Algebra.smul_def, mul_one] at h2
      exact Ideal.algebraMap_residueField_eq_zero.mp h2
    have hnil : b.repr (i n) j ∈ nilradical R := by
      rw [nilradical_eq_sInf]
      exact Ideal.mem_sInf.mpr fun {J} hJ ↦ hmem ⟨J, hJ⟩
    simpa [nilradical_eq_zero] using hnil
  have hs : s (i n) = n := by
    have := congrArg (fun (φ : N →ₗ[R] N) ↦ φ n) hsi
    simpa using this
  rw [← hs, hi, map_zero]

/-- **Over a reduced ring a linear map into a projective module is determined by its
fibres**: if every base change `φ ⊗ κ(p)` vanishes, then `φ = 0`.

This is the step at which reducedness enters the fibre-rank criterion of Proposition A.6.6
(condition (4)): an identity between maps of vector bundles that holds on every fibre holds
outright. -/
theorem _root_.LinearMap.eq_zero_of_forall_baseChange_residueField_eq_zero
    {R : Type u} [CommRing R] [IsReduced R] {M : Type*} {N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R N]
    (φ : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R, φ.baseChange p.asIdeal.ResidueField = 0) : φ = 0 := by
  ext x
  refine Module.eq_zero_of_forall_residueField_tmul_eq_zero (R := R) (φ x) fun p ↦ ?_
  have hp := LinearMap.congr_fun (h p) ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] x)
  simpa using hp

end Reduced

section Nakayama

/-- A spanning set of a finite-dimensional vector space contains a spanning family indexed by
`Fin r` as soon as `r` bounds the dimension.  The zero vector is required to be available for
padding. -/
theorem _root_.exists_fin_span_eq_top_of_finrank_le
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {S : Set V} (hS : Submodule.span k S = ⊤) (h0 : (0 : V) ∈ S) {r : ℕ}
    (hr : Module.finrank k V ≤ r) :
    ∃ g : Fin r → V, (∀ i, g i ∈ S) ∧ Submodule.span k (Set.range g) = ⊤ := by
  classical
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent k S
  rw [hS] at hbspan
  let B : Basis b k V := Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  haveI : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = Module.finrank k V := (Module.finrank_eq_card_basis B).symm
  have hle : Fintype.card b ≤ r := hcard ▸ hr
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  set g : Fin r → V :=
    fun i ↦ if h : (i : ℕ) < Fintype.card b then (e ⟨i, h⟩ : V) else 0 with hg
  have hmem : ∀ i, g i ∈ S := by
    intro i
    rw [hg]
    dsimp only
    split_ifs with h
    · exact hbS (e ⟨i, h⟩).2
    · exact h0
  refine ⟨g, hmem, ?_⟩
  refine top_le_iff.mp ?_
  rw [← hbspan]
  refine Submodule.span_le.mpr fun x hx ↦ ?_
  set j : Fin (Fintype.card b) := Fintype.equivFin b ⟨x, hx⟩ with hj
  have hej : (e j : V) = x := by
    rw [hj]
    change ((Fintype.equivFin b).symm (Fintype.equivFin b ⟨x, hx⟩) : V) = x
    rw [Equiv.symm_apply_apply]
  refine Submodule.subset_span ⟨⟨(j : ℕ), lt_of_lt_of_le j.2 hle⟩, ?_⟩
  show g ⟨(j : ℕ), lt_of_lt_of_le j.2 hle⟩ = x
  rw [hg]
  dsimp only
  split_ifs with h
  · rw [← hej]
  · exact absurd j.2 h

variable (R M) in
/-- The fibre `k ⊗_R M` is spanned over `k` by the elements `1 ⊗ m`. -/
theorem span_one_tmul_eq_top (k : Type u) [CommRing k] [Algebra R k] :
    Submodule.span k (Set.range fun m : M ↦ (1 : k) ⊗ₜ[R] m) = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c m =>
      have : c ⊗ₜ[R] m = c • ((1 : k) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

/-- The `R`-span of a family maps into the `k`-span of its image in the fibre. -/
theorem tmul_mem_span_of_mem_span {k : Type u} [CommRing k] [Algebra R k]
    {ι : Type*} (g : ι → M) {x : M} (hx : x ∈ Submodule.span R (Set.range g)) :
    (1 : k) ⊗ₜ[R] x ∈
      Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[R] g i) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp
  · intro y z _ _ hy hz
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hy hz
  · intro a y _ hy
    have : (1 : k) ⊗ₜ[R] (a • y) = algebraMap R k a • ((1 : k) ⊗ₜ[R] y) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, mul_one, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- The image in the residue field of an element outside a prime is nonzero. -/
theorem algebraMap_residueField_ne_zero {p : PrimeSpectrum R} {f : R} (hf : f ∉ p.asIdeal) :
    algebraMap R p.asIdeal.ResidueField f ≠ 0 := fun hcon ↦
  hf (Ideal.algebraMap_residueField_eq_zero.mp hcon)

/-- **Nakayama, in the form used by the flattening stratification.**  If `r` elements of `M`
span the fibre at `p` up to a scalar invertible at `p`, the fibre rank is at most `r`. -/
theorem fibreFinrank_le_of_smul_mem_span {p : PrimeSpectrum R} {r : ℕ} {f : R}
    (hf : f ∉ p.asIdeal) (g : Fin r → M)
    (h : ∀ m : M, f • m ∈ Submodule.span R (Set.range g)) :
    fibreFinrank R M p ≤ r := by
  set k := p.asIdeal.ResidueField
  have hspan : Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[R] g i) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← span_one_tmul_eq_top R M k]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨m, rfl⟩
    have hfm := tmul_mem_span_of_mem_span (k := k) g (h m)
    have hsm : (1 : k) ⊗ₜ[R] (f • m) = algebraMap R k f • ((1 : k) ⊗ₜ[R] m) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, mul_one, Algebra.smul_def, mul_one]
    rw [hsm] at hfm
    have hunit : IsUnit (algebraMap R k f) :=
      (isUnit_iff_ne_zero).mpr (algebraMap_residueField_ne_zero hf)
    obtain ⟨u, hu⟩ := hunit
    rw [← hu] at hfm
    have h2 := (Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[R] g i)).smul_mem
      ((u⁻¹ : kˣ) : k) hfm
    rw [smul_smul, Units.inv_mul, one_smul] at h2
    exact h2
  have : Fintype.card (Fin r) = r := Fintype.card_fin r
  simpa [fibreFinrank, this] using
    (finrank_le_of_span_eq_top (v := fun i ↦ (1 : k) ⊗ₜ[R] g i) hspan)

/-- **Spreading out a fibrewise generating set.**  For a finite module whose fibre rank at `p`
is at most `r`, some `r` elements of `M` generate `M` after multiplying by a single scalar
invertible at `p`; equivalently, `M_p` is generated by `r` elements.

This is the local form of the open condition of the flattening stratification, Stacks
05P8 (2). -/
theorem exists_smul_mem_span_of_fibreFinrank_le [Module.Finite R M]
    {p : PrimeSpectrum R} {r : ℕ} (h : fibreFinrank R M p ≤ r) :
    ∃ f ∉ p.asIdeal, ∃ g : Fin r → M,
      ∀ m : M, f • m ∈ Submodule.span R (Set.range g) := by
  classical
  set k := p.asIdeal.ResidueField
  haveI : Module.Finite k (k ⊗[R] M) := inferInstance
  obtain ⟨v, hvmem, hvspan⟩ :=
    exists_fin_span_eq_top_of_finrank_le (k := k) (V := k ⊗[R] M)
      (S := Set.range fun m : M ↦ (1 : k) ⊗ₜ[R] m)
      (span_one_tmul_eq_top R M k) ⟨0, by simp⟩ h
  choose g hg using fun i ↦ hvmem i
  have hgspan : Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[R] g i) = ⊤ := by
    rw [← hvspan]
    congr 1
    exact congrArg Set.range (funext fun i ↦ hg i)
  -- The quotient by the span of `g` has vanishing fibre at `p`.
  set N : Submodule R M := Submodule.span R (Set.range g) with hN
  have hquot : Subsingleton (k ⊗[R] (M ⧸ N)) := by
    have hsurj : Function.Surjective (LinearMap.baseChange k N.mkQ) :=
      LinearMap.baseChange_surjective k N.mkQ_surjective
    have hzero : ∀ x : k ⊗[R] M, LinearMap.baseChange k N.mkQ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span k (Set.range fun i ↦ (1 : k) ⊗ₜ[R] g i) := by
        rw [hgspan]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro y ⟨i, rfl⟩
        rw [LinearMap.baseChange_tmul]
        have : N.mkQ (g i) = 0 :=
          (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩)
        rw [this, TensorProduct.tmul_zero]
      · exact map_zero _
      · intro y z _ _ hy hz; rw [map_add, hy, hz, add_zero]
      · intro c y _ hy; rw [map_smul, hy, smul_zero]
    exact ⟨fun x y ↦ by
      obtain ⟨x', rfl⟩ := hsurj x
      obtain ⟨y', rfl⟩ := hsurj y
      rw [hzero x', hzero y']⟩
  have hsupp : p ∉ Module.support R (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact fun hcon ↦ (not_subsingleton _) hquot
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus] at hsupp
  obtain ⟨f, hfann, hfp⟩ := Set.not_subset.mp hsupp
  refine ⟨f, hfp, g, fun m ↦ ?_⟩
  have : f • (N.mkQ m) = 0 := Module.mem_annihilator.mp hfann _
  rw [← map_smul] at this
  exact (Submodule.Quotient.mk_eq_zero N).mp this

/-- The fibre rank of a finite module is at most `r` exactly when `r` elements of `M`
generate it after inverting one scalar outside `p`. -/
theorem fibreFinrank_le_iff_exists_smul_mem_span [Module.Finite R M]
    (p : PrimeSpectrum R) (r : ℕ) :
    fibreFinrank R M p ≤ r ↔
      ∃ f ∉ p.asIdeal, ∃ g : Fin r → M,
        ∀ m : M, f • m ∈ Submodule.span R (Set.range g) :=
  ⟨exists_smul_mem_span_of_fibreFinrank_le,
    fun ⟨_, hf, g, hg⟩ ↦ fibreFinrank_le_of_smul_mem_span hf g hg⟩

end Nakayama

end Module

end

end
