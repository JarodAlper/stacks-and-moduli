module

public import StacksAndModuli.API.ProjTildeModule
public import StacksAndModuli.API.ProjectiveSpectrumNullstellensatz
public import StacksAndModuli.API.GradedModuleAnnihilator

/-!
# Sections of `M~(d)` on a basic open are single fractions

Step **9c** of `PLAN-hilbert-quot.md` (Hartshorne II.5.11(b) for graded modules): over the basic
open `D₊(f)` of a homogeneous `f` of positive degree, every section of `M~(d)` is *globally* a
single fraction `m / f^k`, and two such fractions agreeing as sections agree in `M_f`.

The two halves rest on the projective Nullstellensatz
(`ProjectiveSpectrum.exists_pow_mem_of_forall_not_le`), applied to the homogeneous annihilator of
a homogeneous element for the injectivity half.

## Main results

* `ProjectiveSpectrum.TildeModule.exists_pow_smul_eq_zero`: a homogeneous `m` whose image in every
  `M_{(x)}`, `x ∈ D₊(g)`, vanishes is killed by a power of `g`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open HomogeneousLocalization

namespace ProjectiveSpectrum.TildeModule

universe u

variable {A : Type u} {σ : Type*} {M : Type u} {τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubgroupClass τ M]
variable (𝒜 : ℕ → σ) (ℳ : ℕ → τ) [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℳ]

/-- **The injectivity half of Hartshorne II.5.11(b).**  A homogeneous element of `M` whose image
in `M_{(x)}` vanishes at every point of `D₊(g)` is annihilated by a power of `g`.

The proof runs the projective Nullstellensatz on the homogeneous annihilator of `m`: vanishing at
`x` produces *some* element outside `x` killing `m`, and
`SetLike.not_homogeneousAnnihilator_le_of_exists` upgrades it to a homogeneous one. -/
theorem exists_pow_smul_eq_zero {e : ℕ} (he : 0 < e) {g : A} (hg : g ∈ 𝒜 e)
    {j : ℕ} {m : M} (hm : m ∈ ℳ j)
    (h : ∀ x : ProjectiveSpectrum 𝒜, x ∈ ProjectiveSpectrum.basicOpen 𝒜 g →
      LocalizedModule.mk m (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = 0) :
    ∃ N : ℕ, g ^ N • m = 0 := by
  have hnot : ∀ x : ProjectiveSpectrum 𝒜, x ∈ ProjectiveSpectrum.basicOpen 𝒜 g →
      ¬ SetLike.homogeneousAnnihilator 𝒜 m ≤ x.asHomogeneousIdeal.toIdeal := by
    intro x hx
    refine SetLike.not_homogeneousAnnihilator_le_of_exists 𝒜 ℳ hm
      x.asHomogeneousIdeal.isHomogeneous ?_
    have hz := h x hx
    rw [show (0 : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk 1).symm,
      LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨(u : A), u.2, by simpa [Submonoid.smul_def] using hu⟩
  obtain ⟨N, hN⟩ := ProjectiveSpectrum.exists_pow_mem_of_forall_not_le
    (SetLike.isHomogeneous_homogeneousAnnihilator 𝒜 m) he hg hnot
  exact ⟨N, SetLike.homogeneousAnnihilator_le_annihilator 𝒜 m hN⟩

/-- **Positive-degree homogeneous basic opens form a basis.**  Mathlib's basis
`ProjectiveSpectrum.isTopologicalBasis_basic_opens` uses arbitrary ring elements; replacing an
element by a homogeneous component outside the point shrinks the basic open, and multiplying by a
positive-degree element outside the point (which exists because points of `Proj` are relevant)
makes the degree positive.  Positive degree is what the Nullstellensatz needs. -/
theorem exists_homogeneous_basicOpen_le (x : ProjectiveSpectrum 𝒜)
    (V : Opens (ProjectiveSpectrum 𝒜)) (hx : x ∈ V) :
    ∃ (a : ℕ) (h : A), 0 < a ∧ h ∈ 𝒜 a ∧ x ∈ ProjectiveSpectrum.basicOpen 𝒜 h ∧
      ProjectiveSpectrum.basicOpen 𝒜 h ≤ V := by
  classical
  obtain ⟨-, ⟨r, rfl⟩, hxr, hrV⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hx V.isOpen
  have hcomp : ∃ i : ℕ, (DirectSum.decompose 𝒜 r i : A) ∉ x.asHomogeneousIdeal := by
    by_contra hcon
    rw [not_exists] at hcon
    simp only [not_not] at hcon
    refine hxr ?_
    show r ∈ x.asHomogeneousIdeal
    rw [← DirectSum.sum_support_decompose 𝒜 r]
    exact Ideal.sum_mem _ fun i _ ↦ hcon i
  obtain ⟨i, hi⟩ := hcomp
  obtain ⟨b, hb1, y, hy, hyx⟩ :=
    HomogeneousLocalization.HasLargeDegrees.exists_homogeneous_mem
      (𝒜 := 𝒜) (x := x.asHomogeneousIdeal.toIdeal.primeCompl) 1
  have hsub : ProjectiveSpectrum.basicOpen 𝒜 (DirectSum.decompose 𝒜 r i : A) ≤
      ProjectiveSpectrum.basicOpen 𝒜 r := by
    intro z hz hzr
    exact hz (z.asHomogeneousIdeal.2 i hzr)
  refine ⟨i + b, (DirectSum.decompose 𝒜 r i : A) * y, by omega,
    SetLike.mul_mem_graded (DirectSum.decompose 𝒜 r i).2 hy, ?_, ?_⟩
  · intro hmem
    rcases x.isPrime.mem_or_mem hmem with h | h
    · exact hi h
    · exact hyx h
  · refine le_trans ?_ (le_trans hsub (fun z hz ↦ hrV hz))
    rw [ProjectiveSpectrum.basicOpen_mul]
    exact inf_le_left

variable {d : ℤ}

omit [DirectSum.Decomposition ℳ] in
/-- **Local normalization of a section.**  Near any point, a section of `M~(d)` is a fraction
whose denominator is a *single homogeneous element of positive degree* and whose domain of
validity is exactly that element's basic open.

Three steps: shrink to a positive-degree homogeneous basic open `D₊(h)`
(`exists_homogeneous_basicOpen_le`); note `D₊(h) ⊆ D₊(s₀)` for the local denominator
`s₀`, so the Nullstellensatz gives `h^N = c₀ s₀` with `c₀` homogeneous
(`exists_mem_mul_eq_of_mem_span_singleton`); and rewrite `r / s₀` as `c₀ r / h^N`. -/
theorem exists_homogeneous_denominator {U : Opens (ProjectiveSpectrum 𝒜)}
    (t : ∀ z : U, atDeg 𝒜 ℳ d z.1) (ht : (isLocallyFraction 𝒜 ℳ d).pred t) (x : U) :
    ∃ (c bdeg : ℕ) (g : A) (m : M),
      0 < c ∧ g ∈ 𝒜 c ∧ m ∈ ℳ bdeg ∧ (bdeg : ℤ) = c + d ∧
      (x : ProjectiveSpectrum 𝒜) ∈ ProjectiveSpectrum.basicOpen 𝒜 g ∧
      ProjectiveSpectrum.basicOpen 𝒜 g ≤ U ∧
      ∀ (y : ProjectiveSpectrum 𝒜) (hy : y ∈ ProjectiveSpectrum.basicOpen 𝒜 g)
        (hyU : y ∈ U),
        ((t ⟨y, hyU⟩ : atDeg 𝒜 ℳ d y) :
            LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
          = LocalizedModule.mk m ⟨g, hy⟩ := by
  obtain ⟨V, mV, iV, i, j, hij, ⟨r, hr⟩, ⟨s₀, hs₀⟩, s₀_nin, w⟩ := ht x
  obtain ⟨a, h, ha, hh, hxh, hhV⟩ := exists_homogeneous_basicOpen_le 𝒜 x.1 V mV
  have hspanS : (Ideal.span ({s₀} : Set A)).IsHomogeneous 𝒜 :=
    Ideal.homogeneous_span 𝒜 _ (by rintro _ rfl; exact ⟨i, hs₀⟩)
  have hnot : ∀ z : ProjectiveSpectrum 𝒜, z ∈ ProjectiveSpectrum.basicOpen 𝒜 h →
      ¬ Ideal.span ({s₀} : Set A) ≤ z.asHomogeneousIdeal.toIdeal := by
    intro z hz hle
    exact (s₀_nin ⟨z, hhV hz⟩) (hle (Ideal.subset_span rfl))
  obtain ⟨N, hN⟩ := ProjectiveSpectrum.exists_pow_mem_of_forall_not_le hspanS ha hh hnot
  set N' := max (max N i) 1 with hN'def
  have hNN' : N ≤ N' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hiN' : i ≤ N' := le_trans (le_max_right _ _) (le_max_left _ _)
  have h1N' : 1 ≤ N' := le_max_right _ _
  have hpow : h ^ N' ∈ Ideal.span ({s₀} : Set A) := by
    have hsplit : h ^ N' = h ^ (N' - N) * h ^ N := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ hN
  have hdeg : i ≤ N' * a := le_trans hiN' (Nat.le_mul_of_pos_right _ ha)
  have hhpow : h ^ N' ∈ 𝒜 (N' * a) := by simpa using SetLike.pow_mem_graded N' hh
  obtain ⟨c₀, hc₀, hc₀eq⟩ :=
    SetLike.exists_mem_mul_eq_of_mem_span_singleton 𝒜 hs₀ hhpow hdeg hpow
  have hposN : 0 < N' := by omega
  have hopen : ProjectiveSpectrum.basicOpen 𝒜 (h ^ N') = ProjectiveSpectrum.basicOpen 𝒜 h :=
    ProjectiveSpectrum.basicOpen_pow 𝒜 h N' hposN
  refine ⟨N' * a, (N' * a - i) + j, h ^ N', c₀ • r,
    Nat.mul_pos hposN ha, hhpow, SetLike.GradedSMul.smul_mem hc₀ hr, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_sub hdeg, hij]
    push_cast
    ring
  · rw [hopen]; exact hxh
  · rw [hopen]; exact le_trans hhV (leOfHom iV)
  · intro y hy hyU
    have hyh : y ∈ ProjectiveSpectrum.basicOpen 𝒜 h := hopen ▸ hy
    have hyV : y ∈ V := hhV hyh
    have hw := w ⟨y, hyV⟩
    have hstep : (LocalizedModule.mk r ⟨s₀, s₀_nin ⟨y, hyV⟩⟩
        : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk (c₀ • r) ⟨h ^ N', hy⟩ := by
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      show (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) • _ • r
        = (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) • _ • (c₀ • r)
      simp only [one_smul, Submonoid.smul_def]
      rw [hc₀eq, mul_smul, smul_comm]
    rw [← hstep]
    exact hw

/-- **Algebraic core of the gluing.**  A finite family of numerators that is pairwise compatible
(`g z' • m z = g z • m z'`) assembles, against any representation `F = ∑ λ z g z`, into
a single numerator `∑ λ z • m z` whose fraction over `F` restricts to `m z / g z` on each
piece. -/
theorem smul_sum_eq_of_compat {ι : Type*} (S : Finset ι) (g : ι → A) (m : ι → M)
    (hcompat : ∀ z ∈ S, ∀ z' ∈ S, g z' • m z = g z • m z')
    (lam : ι → A) {F : A} (hF : F = ∑ z ∈ S, lam z * g z) {z : ι} (hz : z ∈ S) :
    g z • (∑ z' ∈ S, lam z' • m z') = F • m z := by
  rw [hF, Finset.smul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z' hz' ↦ ?_
  calc g z • (lam z' • m z') = lam z' • (g z • m z') := smul_comm _ _ _
    _ = lam z' • (g z' • m z) := by rw [hcompat z' hz' z hz]
    _ = (lam z' * g z') • m z := (mul_smul _ _ _).symm

omit [DirectSum.Decomposition ℳ] in
/-- **Gluing a finite compatible family into one fraction.**  Given finitely many homogeneous
fractions `m z / g z` of shift `d` that are pairwise compatible and whose basic opens cover
`D₊(f)`, there is a single numerator `M₀` of the right degree with `g z • M₀ = f^L • m z`
for every `z`; that is, `M₀ / f^L` restricts to `m z / g z` on `D₊(g z)`.

The covering hypothesis enters only through the Nullstellensatz, which puts a power of `f` in the
ideal generated by the `g z`; homogenizing the coefficients of that representation
(`SetLike.eq_sum_proj_mul`) is what makes the assembled numerator homogeneous. -/
theorem exists_numerator_of_compatible_family {e : ℕ} (he : 0 < e) {f : A} (hf : f ∈ 𝒜 e)
    {ι : Type*} [Finite ι] [Nonempty ι]
    (c b : ι → ℕ) (g : ι → A) (m : ι → M)
    (hg : ∀ z, g z ∈ 𝒜 (c z)) (hm : ∀ z, m z ∈ ℳ (b z))
    (hdeg : ∀ z, (b z : ℤ) = c z + d)
    (hcompat : ∀ z z', g z' • m z = g z • m z')
    (hcover : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ z, ProjectiveSpectrum.basicOpen 𝒜 (g z)) :
    ∃ (L B : ℕ) (M₀ : M), M₀ ∈ ℳ B ∧ (B : ℤ) = L * e + d ∧
      ∀ z : ι, g z • M₀ = f ^ L • m z := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨L₀, hL₀⟩ :=
    ProjectiveSpectrum.exists_pow_mem_span_of_basicOpen_le_iSup (𝒜 := 𝒜) hg he hf hcover
  set L := max L₀ (Finset.univ.sup c) with hLdef
  have hL₀L : L₀ ≤ L := le_max_left _ _
  have hcL : ∀ z : ι, c z ≤ L := fun z ↦
    le_trans (Finset.le_sup (f := c) (Finset.mem_univ z)) (le_max_right _ _)
  have hcLe : ∀ z : ι, c z ≤ L * e := fun z ↦
    le_trans (hcL z) (Nat.le_mul_of_pos_right _ he)
  have hfL : f ^ L ∈ Ideal.span (Set.range g) := by
    have hsplit : f ^ L = f ^ (L - L₀) * f ^ L₀ := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ hL₀
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hfL
  have hfLdeg : f ^ L ∈ 𝒜 (L * e) := by simpa using SetLike.pow_mem_graded L hf
  have hsum : f ^ L = ∑ z : ι, lam z * g z := by
    rw [← hlam]
    simp [smul_eq_mul]
  have hhom := SetLike.eq_sum_proj_mul 𝒜 Finset.univ hg lam hfLdeg hsum
    (fun z _ ↦ hcLe z)
  set lam' : ι → A := fun z ↦ GradedRing.proj 𝒜 (L * e - c z) (lam z) with hlam'def
  have hlam'mem : ∀ z : ι, lam' z ∈ 𝒜 (L * e - c z) := fun z ↦
    (DirectSum.decompose 𝒜 (lam z) (L * e - c z)).2
  obtain ⟨z₀⟩ := ‹Nonempty ι›
  have hBnn : (0 : ℤ) ≤ L * e + d := by
    have h1 := hdeg z₀
    have h2 : (c z₀ : ℤ) ≤ (L * e : ℕ) := by exact_mod_cast hcLe z₀
    push_cast at h2 ⊢
    omega
  refine ⟨L, ((L * e : ℕ) + d).toNat, ∑ z : ι, lam' z • m z, ?_, ?_, ?_⟩
  · refine sum_mem fun z _ ↦ ?_
    have hd : (L * e - c z) + b z = ((L * e : ℕ) + d).toNat := by
      have h1 := hdeg z
      have h2 : (c z : ℤ) ≤ (L * e : ℕ) := by exact_mod_cast hcLe z
      have h3 : ((L * e - c z : ℕ) : ℤ) = (L * e : ℕ) - c z := by
        rw [Nat.cast_sub (hcLe z)]
      omega
    exact hd ▸ SetLike.GradedSMul.smul_mem (hlam'mem z) (hm z)
  · rw [Int.toNat_of_nonneg (by push_cast at hBnn ⊢; omega)]
    push_cast
    ring
  · intro z
    exact smul_sum_eq_of_compat Finset.univ g m (fun _ _ _ _ ↦ hcompat _ _) lam'
      hhom (Finset.mem_univ z)

/-- **Hartshorne II.5.11(b), surjectivity half.**  Every section of `M~(d)` over the basic open of
a homogeneous `f` of positive degree is a single fraction `M₀ / f^L`.

The proof normalizes the section locally (`exists_homogeneous_denominator`), extracts a *finite*
subfamily from the Nullstellensatz — membership of `f^N` in the ideal generated by the local
denominators is witnessed by finitely many of them, and that subfamily automatically still covers
`D₊(f)` — clears the pairwise discrepancies by a single power `K` supplied by
`exists_pow_smul_eq_zero`, and glues with `exists_numerator_of_compatible_family`. -/
theorem exists_global_fraction {e : ℕ} (he : 0 < e) {f : A} (hf : f ∈ 𝒜 e)
    (t : ∀ z : (ProjectiveSpectrum.basicOpen 𝒜 f : Opens (ProjectiveSpectrum 𝒜)),
      atDeg 𝒜 ℳ d z.1)
    (ht : (isLocallyFraction 𝒜 ℳ d).pred t) :
    ∃ (L B : ℕ) (M₀ : M), M₀ ∈ ℳ B ∧ (B : ℤ) = L * e + d ∧
      ∀ (y : ProjectiveSpectrum 𝒜) (hy : y ∈ ProjectiveSpectrum.basicOpen 𝒜 f),
        ((t ⟨y, hy⟩ : atDeg 𝒜 ℳ d y) :
            LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
          = LocalizedModule.mk M₀
              ⟨f ^ L, Submonoid.pow_mem y.asHomogeneousIdeal.toIdeal.primeCompl hy L⟩ := by
  classical
  by_cases hne : ∃ y : ProjectiveSpectrum 𝒜, y ∈ ProjectiveSpectrum.basicOpen 𝒜 f
  swap
  · rw [not_exists] at hne
    refine ⟨(-d).toNat, (((-d).toNat * e : ℕ) + d).toNat, 0, zero_mem _, ?_, ?_⟩
    · have h1 : -d ≤ ((-d).toNat : ℤ) := Int.self_le_toNat _
      have h2 : (-d).toNat ≤ (-d).toNat * e := Nat.le_mul_of_pos_right _ he
      have h2' : (((-d).toNat : ℤ)) ≤ (((-d).toNat * e : ℕ) : ℤ) := by exact_mod_cast h2
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    · intro y hy
      exact absurd hy (hne y)
  -- Local data at every point of `D₊(f)`
  choose c₀ b₀ g₀ m₀ hcpos hg₀ hm₀ hdeg₀ hmem₀ hle₀ hfrac₀ using
    fun z : (ProjectiveSpectrum.basicOpen 𝒜 f : Opens (ProjectiveSpectrum 𝒜)) =>
      exists_homogeneous_denominator 𝒜 ℳ t ht z
  have hcover₀ : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ z : (ProjectiveSpectrum.basicOpen 𝒜 f : Opens (ProjectiveSpectrum 𝒜)),
        ProjectiveSpectrum.basicOpen 𝒜 (g₀ z) := fun y hy ↦
    Opens.mem_iSup.2 ⟨⟨y, hy⟩, hmem₀ ⟨y, hy⟩⟩
  obtain ⟨N₀, hN₀⟩ :=
    ProjectiveSpectrum.exists_pow_mem_span_of_basicOpen_le_iSup (𝒜 := 𝒜) hg₀ he hf hcover₀
  obtain ⟨μ, hμ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hN₀
  set S := μ.support with hSdef
  have hSsum : ∑ z ∈ S, μ z * g₀ z = f ^ N₀ := by
    rw [← hμ, Finsupp.sum]
    exact Finset.sum_congr rfl fun z _ ↦ by simp [smul_eq_mul]
  -- The finite subfamily still covers `D₊(f)`
  have hcoverS : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ z : {x // x ∈ S}, ProjectiveSpectrum.basicOpen 𝒜 (g₀ z.1) := by
    intro y hy
    by_contra hcon
    have hall : ∀ z ∈ S, g₀ z ∈ y.asHomogeneousIdeal := by
      intro z hz
      by_contra hgz
      exact hcon (Opens.mem_iSup.2 ⟨⟨z, hz⟩, hgz⟩)
    have hpow : f ^ N₀ ∈ y.asHomogeneousIdeal.toIdeal := by
      rw [← hSsum]
      exact Ideal.sum_mem _ fun z hz ↦ Ideal.mul_mem_left _ _ (hall z hz)
    exact hy (y.isPrime.mem_of_pow_mem N₀ hpow)
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨z₀, -⟩ := Opens.mem_iSup.1 (hcoverS hy₀)
  haveI : Nonempty {x // x ∈ S} := ⟨z₀⟩
  -- A single exponent clearing all pairwise discrepancies
  have hKex : ∀ z z' : {x // x ∈ S}, ∃ Kp : ℕ,
      (g₀ z.1 * g₀ z'.1) ^ Kp • (g₀ z'.1 • m₀ z.1 - g₀ z.1 • m₀ z'.1) = 0 := by
    intro z z'
    have hdegeq : c₀ z.1 + b₀ z'.1 = c₀ z'.1 + b₀ z.1 := by
      have h1 := hdeg₀ z.1
      have h2 := hdeg₀ z'.1
      omega
    have hwmem : g₀ z'.1 • m₀ z.1 - g₀ z.1 • m₀ z'.1 ∈ ℳ (c₀ z'.1 + b₀ z.1) :=
      sub_mem (SetLike.GradedSMul.smul_mem (hg₀ z'.1) (hm₀ z.1))
        (hdegeq ▸ SetLike.GradedSMul.smul_mem (hg₀ z.1) (hm₀ z'.1))
    refine exists_pow_smul_eq_zero 𝒜 ℳ (e := c₀ z.1 + c₀ z'.1)
      (by have := hcpos z.1; omega) (SetLike.mul_mem_graded (hg₀ z.1) (hg₀ z'.1)) hwmem ?_
    intro y hy
    rw [ProjectiveSpectrum.basicOpen_mul] at hy
    obtain ⟨hyz, hyz'⟩ := hy
    have hyf : y ∈ ProjectiveSpectrum.basicOpen 𝒜 f := hle₀ z.1 hyz
    have heq := (hfrac₀ z.1 y hyz hyf).symm.trans (hfrac₀ z'.1 y hyz' hyf)
    rw [LocalizedModule.mk_eq] at heq
    obtain ⟨u, hu⟩ := heq
    rw [show (0 : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
    refine ⟨u, ?_⟩
    simp only [one_smul, smul_zero, Submonoid.smul_def] at hu ⊢
    rw [smul_sub, sub_eq_zero]
    exact hu
  choose Kf hKf using hKex
  set K := Finset.univ.sup (fun p : {x // x ∈ S} × {x // x ∈ S} => Kf p.1 p.2) with hKdef
  have hmono : ∀ (a : A) (w : M) (K1 K2 : ℕ), K1 ≤ K2 →
      a ^ K1 • w = 0 → a ^ K2 • w = 0 := by
    intro a w K1 K2 hK12 h0
    have hsplit : a ^ K2 = a ^ (K2 - K1) * a ^ K1 := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_smul, h0, smul_zero]
  have hKbig : ∀ z z' : {x // x ∈ S},
      (g₀ z.1 * g₀ z'.1) ^ K • (g₀ z'.1 • m₀ z.1 - g₀ z.1 • m₀ z'.1) = 0 :=
    fun z z' ↦ hmono _ _ _ _
      (Finset.le_sup (f := fun p : {x // x ∈ S} × {x // x ∈ S} => Kf p.1 p.2)
        (Finset.mem_univ (z, z'))) (hKf z z')
  -- The adjusted family
  set g : {x // x ∈ S} → A := fun z ↦ g₀ z.1 ^ (K + 1) with hgdef
  set m : {x // x ∈ S} → M := fun z ↦ g₀ z.1 ^ K • m₀ z.1 with hmdef
  have hgmem : ∀ z : {x // x ∈ S}, g z ∈ 𝒜 ((K + 1) * c₀ z.1) := fun z ↦ by
    simpa [hgdef] using SetLike.pow_mem_graded (K + 1) (hg₀ z.1)
  have hmmem : ∀ z : {x // x ∈ S}, m z ∈ ℳ (K * c₀ z.1 + b₀ z.1) := fun z ↦ by
    simpa [hmdef] using
      SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded K (hg₀ z.1)) (hm₀ z.1)
  have hdegm : ∀ z : {x // x ∈ S},
      ((K * c₀ z.1 + b₀ z.1 : ℕ) : ℤ) = ((K + 1) * c₀ z.1 : ℕ) + d := fun z ↦ by
    have := hdeg₀ z.1
    push_cast
    linarith
  have hopen : ∀ z : {x // x ∈ S},
      ProjectiveSpectrum.basicOpen 𝒜 (g z)
        = ProjectiveSpectrum.basicOpen 𝒜 (g₀ z.1) := fun z ↦
    ProjectiveSpectrum.basicOpen_pow 𝒜 _ (K + 1) (by omega)
  have hcompat : ∀ z z' : {x // x ∈ S}, g z' • m z = g z • m z' := by
    intro z z'
    have hK := hKbig z z'
    rw [smul_sub, sub_eq_zero] at hK
    calc g z' • m z = (g₀ z'.1 ^ (K + 1) * g₀ z.1 ^ K) • m₀ z.1 := by
          simp only [hgdef, hmdef, smul_smul]
      _ = (g₀ z.1 * g₀ z'.1) ^ K • (g₀ z'.1 • m₀ z.1) := by
            rw [smul_smul]; congr 1; ring
      _ = (g₀ z.1 * g₀ z'.1) ^ K • (g₀ z.1 • m₀ z'.1) := hK
      _ = (g₀ z.1 ^ (K + 1) * g₀ z'.1 ^ K) • m₀ z'.1 := by rw [smul_smul]; congr 1; ring
      _ = g z • m z' := by simp only [hgdef, hmdef, smul_smul]
  have hcover : ProjectiveSpectrum.basicOpen 𝒜 f ≤
      ⨆ z : {x // x ∈ S}, ProjectiveSpectrum.basicOpen 𝒜 (g z) := by
    refine le_trans hcoverS (iSup_mono fun z ↦ ?_)
    rw [hopen z]
  obtain ⟨L, B, M₀, hM₀, hB, hglue⟩ :=
    exists_numerator_of_compatible_family 𝒜 ℳ he hf (fun z ↦ (K + 1) * c₀ z.1)
      (fun z ↦ K * c₀ z.1 + b₀ z.1) g m hgmem hmmem hdegm hcompat hcover
  refine ⟨L, B, M₀, hM₀, hB, ?_⟩
  intro y hy
  obtain ⟨z, hz⟩ := Opens.mem_iSup.1 (hcover hy)
  have hz₀ : y ∈ ProjectiveSpectrum.basicOpen 𝒜 (g₀ z.1) := (hopen z) ▸ hz
  have hadj : (LocalizedModule.mk (m₀ z.1) ⟨g₀ z.1, hz₀⟩
      : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
      = LocalizedModule.mk (m z) ⟨g z, hz⟩ := by
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, hgdef, hmdef]
    rw [smul_smul, ← pow_succ']
  have hgl : (LocalizedModule.mk (m z) ⟨g z, hz⟩
      : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
      = LocalizedModule.mk M₀
          ⟨f ^ L, Submonoid.pow_mem y.asHomogeneousIdeal.toIdeal.primeCompl hy L⟩ := by
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simpa only [one_smul, Submonoid.smul_def] using (hglue z).symm
  exact (hfrac₀ z.1 y hz₀ hy).trans (hadj.trans hgl)

/-- **Hartshorne II.5.11(b), uniqueness.**  Two fractions over powers of `f` that induce the same
section of `M~(d)` on `D₊(f)` are already equal in `M_f`.

Together with `exists_global_fraction` this identifies `Γ(D₊(f), M~(d))` with the degree-`d` part
of `M_f`, without having to construct the comparison map: existence is the surjectivity, this is
the injectivity. -/
theorem mk_eq_mk_of_sections_eq {e : ℕ} (he : 0 < e) {f : A} (hf : f ∈ 𝒜 e)
    {B₁ B₂ L₁ L₂ : ℕ} {m₁ m₂ : M} (hm₁ : m₁ ∈ ℳ B₁) (hm₂ : m₂ ∈ ℳ B₂)
    (hdeg : L₂ * e + B₁ = L₁ * e + B₂)
    (h : ∀ (y : ProjectiveSpectrum 𝒜) (hy : y ∈ ProjectiveSpectrum.basicOpen 𝒜 f),
      (LocalizedModule.mk m₁ ⟨f ^ L₁, Submonoid.pow_mem _ hy L₁⟩
        : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk m₂ ⟨f ^ L₂, Submonoid.pow_mem _ hy L₂⟩) :
    (LocalizedModule.mk m₁ ⟨f ^ L₁, ⟨L₁, rfl⟩⟩ : LocalizedModule (Submonoid.powers f) M)
      = (LocalizedModule.mk m₂ ⟨f ^ L₂, ⟨L₂, rfl⟩⟩
          : LocalizedModule (Submonoid.powers f) M) := by
  have hfL₁ : (f ^ L₁ : A) ∈ 𝒜 (L₁ * e) := by simpa using SetLike.pow_mem_graded L₁ hf
  have hfL₂ : (f ^ L₂ : A) ∈ 𝒜 (L₂ * e) := by simpa using SetLike.pow_mem_graded L₂ hf
  have hw : (f ^ L₂ • m₁ - f ^ L₁ • m₂) ∈ ℳ (L₂ * e + B₁) :=
    sub_mem (SetLike.GradedSMul.smul_mem hfL₂ hm₁)
      (hdeg ▸ SetLike.GradedSMul.smul_mem hfL₁ hm₂)
  have hzero : ∀ y : ProjectiveSpectrum 𝒜, y ∈ ProjectiveSpectrum.basicOpen 𝒜 f →
      LocalizedModule.mk (f ^ L₂ • m₁ - f ^ L₁ • m₂)
        (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) = 0 := by
    intro y hy
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 (h y hy)
    rw [show (0 : LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk 0 1 from (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
    refine ⟨u, ?_⟩
    simp only [one_smul, smul_zero, Submonoid.smul_def] at hu ⊢
    rw [smul_sub, sub_eq_zero]
    exact hu
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero 𝒜 ℳ he hf hw hzero
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨f ^ N, ⟨N, rfl⟩⟩, ?_⟩
  simp only [Submonoid.smul_def]
  rw [smul_sub, sub_eq_zero] at hN
  exact hN

/-- **The stalk of `M~(d)`.**  Evaluation at a point is a bijection from the stalk of the
sheaf of types onto `atDeg 𝒜 ℳ d x`, the degree-`d` part of the homogeneous localization of `ℳ`
at `x`.

Surjectivity is immediate — a fraction `m / s` is already a section on `D₊(s)`.  Injectivity is
where gradedness enters: two fractions agreeing at `x` are equalized by *some* `u ∉ x`, and
`SetLike.exists_homogeneous_smul_eq_zero` replaces it by a homogeneous one, whose basic open is
the neighbourhood on which the two sections agree. -/
theorem bijective_stalkToFiber (x : ProjectiveSpectrum.top 𝒜) :
    Function.Bijective (TopCat.stalkToFiber (isLocallyFraction 𝒜 ℳ d) x) := by
  constructor
  · refine TopCat.stalkToFiber_injective _ x ?_
    rintro U V fU hU fV hV heq
    obtain ⟨W₁, mW₁, i₁, dd₁, dn₁, hd₁, ⟨r₁, hr₁⟩, ⟨s₁, hs₁⟩, s₁_nin, w₁⟩ := hU ⟨x, U.2⟩
    obtain ⟨W₂, mW₂, i₂, dd₂, dn₂, hd₂, ⟨r₂, hr₂⟩, ⟨s₂, hs₂⟩, s₂_nin, w₂⟩ := hV ⟨x, V.2⟩
    have hdegeq : dd₂ + dn₁ = dd₁ + dn₂ := by omega
    have hwmem : (s₂ • r₁ - s₁ • r₂) ∈ ℳ (dd₂ + dn₁) :=
      sub_mem (SetLike.GradedSMul.smul_mem hs₂ hr₁)
        (hdegeq ▸ SetLike.GradedSMul.smul_mem hs₁ hr₂)
    have hcoe : (LocalizedModule.mk (r₁ : M) ⟨(s₁ : A), s₁_nin ⟨x, mW₁⟩⟩
        : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl M)
        = LocalizedModule.mk (r₂ : M) ⟨(s₂ : A), s₂_nin ⟨x, mW₂⟩⟩ := by
      rw [← w₁ ⟨x, mW₁⟩, ← w₂ ⟨x, mW₂⟩]
      exact congrArg Subtype.val heq
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hcoe
    have hukill : (u : A) • (s₂ • r₁ - s₁ • r₂) = 0 := by
      simp only [Submonoid.smul_def] at hu
      rw [smul_sub, sub_eq_zero]
      exact hu
    obtain ⟨i, u', hu'mem, hu'nin, hu'kill⟩ :=
      SetLike.exists_homogeneous_smul_eq_zero 𝒜 ℳ hwmem x.asHomogeneousIdeal.isHomogeneous
        u.2 hukill
    refine ⟨⟨W₁ ⊓ W₂ ⊓ ProjectiveSpectrum.basicOpen 𝒜 u', ⟨⟨mW₁, mW₂⟩, hu'nin⟩⟩, ?_, ?_, ?_⟩
    · change W₁ ⊓ W₂ ⊓ ProjectiveSpectrum.basicOpen 𝒜 u' ⟶ U.val
      exact Opens.infLELeft _ _ ≫ Opens.infLELeft _ _ ≫ i₁
    · change W₁ ⊓ W₂ ⊓ ProjectiveSpectrum.basicOpen 𝒜 u' ⟶ V.val
      exact Opens.infLELeft _ _ ≫ Opens.infLERight _ _ ≫ i₂
    rintro ⟨y, ⟨⟨hy₁, hy₂⟩, hyu⟩⟩
    refine Subtype.ext ((w₁ ⟨y, hy₁⟩).trans (Eq.trans ?_ (w₂ ⟨y, hy₂⟩).symm))
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨u', hyu⟩, ?_⟩
    simp only [Submonoid.smul_def]
    rw [← sub_eq_zero, ← smul_sub]
    exact hu'kill
  · refine TopCat.stalkToFiber_surjective _ x ?_
    intro t
    obtain ⟨p, hp⟩ := t.2
    refine ⟨⟨ProjectiveSpectrum.basicOpen 𝒜 (p.den : A), p.den_mem⟩,
      fun y ↦ ⟨LocalizedModule.mk (p.num : M) ⟨(p.den : A), y.2⟩,
        ⟨{ degDen := p.degDen
           degNum := p.degNum
           num := p.num
           den := p.den
           den_mem := y.2
           deg_eq := p.deg_eq }, rfl⟩⟩,
      PrelocalPredicate.sheafifyOf
        ⟨p.degDen, p.degNum, p.deg_eq, p.num, p.den, fun y ↦ y.2, fun _ ↦ rfl⟩, ?_⟩
    exact Subtype.ext hp

/-- The stalk of `M~(d)` at `x`, as an equivalence with the degree-`d` part of the homogeneous
localization of `ℳ` at `x`. -/
noncomputable def stalkEquiv (x : ProjectiveSpectrum.top 𝒜) :
    (sheafInType 𝒜 ℳ d).presheaf.stalk x ≃ atDeg 𝒜 ℳ d x :=
  Equiv.ofBijective _ (bijective_stalkToFiber 𝒜 ℳ x)

end ProjectiveSpectrum.TildeModule
