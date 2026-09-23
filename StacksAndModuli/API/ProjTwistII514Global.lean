module

public import StacksAndModuli.API.ProjTwistII514

/-!
# Hartshorne II.5.14, the global assembly

The chart-level statements of `StacksAndModuli.API.ProjTwistII514` are glued here into the two global
halves of Hartshorne II.5.14 for a homogeneous coordinate `x i₀` of degree one:

* injectivity — `AlgebraicGeometry.Proj.exists_pow_app_top_eq_zero` (already in the chart file);
* surjectivity — every section of `F(e)` over `D₊(x i₀)` becomes, after multiplication by a
  power of `x i₀`, the restriction of a *global* section of a twist of `F`.

The surjectivity assembly needs one ingredient that the chart file does not provide: on the
overlap `D₊(f) ⊓ D₊(h)` of two charts — itself affine, being `D₊(f h)` — a section vanishing on
`D₊(f) ⊓ D₊(h) ⊓ D₊(g)` is killed by a power of `g`.  That is
`AlgebraicGeometry.Proj.exists_app_twistModuleMulHom_eq_zero_inf`, obtained from the qcqs
module-localization lemma applied on the affine open `D₊(f h)` to the restriction of the ratio
section `g/f`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false
set_option linter.style.show false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- On a compact quasi-separated open `U`, a section of a quasicoherent sheaf that vanishes on
`D(r)` is killed by a power of `r`.  This is the `IsLocalizedModule.eq_zero_iff` reading of
`Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap_of_qcqs`. -/
theorem Scheme.Modules.exists_pow_smul_eq_zero_of_res_zero {X : Scheme.{u}}
    (P : X.Modules) [P.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1) (r : Γ(X, U))
    (t : Γ(P, U))
    (ht : (P.presheaf.map (homOfLE (X.basicOpen_le r)).op) t = 0) :
    ∃ n : ℕ, r ^ n • t = 0 := by
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom).toAlgebra
  letI : Module Γ(X, U) Γ(P, X.basicOpen r) :=
    Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom)
  haveI := Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap_of_qcqs P hU hU' r
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers r)
      (Scheme.Modules.resBasicOpenLinearMap P r)).1 ht
  exact ⟨n, hn⟩

namespace Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The overlap of two degree-one charts is affine: it is `D₊(f h)`. -/
theorem isAffineOpen_inf_basicOpen {f h : A} (hf : f ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    IsAffineOpen (basicOpen 𝒜 f ⊓ basicOpen 𝒜 h) := by
  rw [← basicOpen_mul 𝒜 f h]
  exact isAffineOpen_basicOpen 𝒜 (f * h) (SetLike.mul_mem_graded hf hh) (by norm_num)

/-- **Overlap injectivity.**  A section of `F(e)` over the overlap `D₊(f) ⊓ D₊(h)` of two
degree-one charts, vanishing on every open of the overlap contained in `D₊(g)`, is killed by
multiplication by a power of `g`. -/
theorem exists_app_twistModuleMulHom_eq_zero_inf
    {f h g : A} (hf : f ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [(ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 f ⊓ basicOpen 𝒜 h))
    (ht : ∀ (V : (Proj 𝒜).Opens) (hVU : V ≤ basicOpen 𝒜 f ⊓ basicOpen 𝒜 h),
      V ≤ basicOpen 𝒜 g →
      ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVU).op) t = 0) :
    ∃ M : ℕ, ∀ (hgM : g ^ M ∈ 𝒜 M) (ec : ℤ) (hec : ec = e + (M : ℤ)),
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ M, hgM⟩ : 𝒜 M) e ec hec)
        (basicOpen 𝒜 f ⊓ basicOpen 𝒜 h) t = 0 := by
  have hUf : basicOpen 𝒜 f ⊓ basicOpen 𝒜 h ≤ basicOpen 𝒜 f := inf_le_left
  have hratg : (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg) ≤ basicOpen 𝒜 g := by
    rw [basicOpen_ratioSection 𝒜 hf hg Nat.one_pos]
    exact inf_le_right
  have hrg : (Proj 𝒜).basicOpen
      (((Proj 𝒜).presheaf.map (homOfLE hUf).op).hom (ratioSection 𝒜 hf hg))
      ≤ basicOpen 𝒜 g := by
    rw [Scheme.basicOpen_res]
    exact le_trans inf_le_right hratg
  obtain ⟨n, hn⟩ := Scheme.Modules.exists_pow_smul_eq_zero_of_res_zero
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F e)
    (isAffineOpen_inf_basicOpen 𝒜 hf hh).isCompact
    (isAffineOpen_inf_basicOpen 𝒜 hf hh).isQuasiSeparated
    (((Proj 𝒜).presheaf.map (homOfLE hUf).op).hom (ratioSection 𝒜 hf hg)) t
    (ht _ ((Proj 𝒜).basicOpen_le _) hrg)
  refine ⟨n, fun hgM ec hec ↦ ?_⟩
  have hfn : f ^ n ∈ 𝒜 n := by simpa using SetLike.pow_mem_graded _ hf
  refine app_twistModuleMulHom_eq_zero_of_le 𝒜 hf hg F n e ec hec hfn hgM
    (basicOpen 𝒜 f ⊓ basicOpen 𝒜 h) hUf t ?_
  rw [map_pow]
  exact hn

/-- **Chart lift with a uniform power.**  Beyond a threshold `N₀`, for *every* `N ≥ N₀` the
section `t` of `F(e)` over `D₊(g)`, restricted to the overlap `D₊(u) ⊓ D₊(g)`, becomes after
multiplication by `g^N` the restriction of a section of `F(e+N)` over the chart `D₊(u)`.

The threshold is raised by multiplying the chart lift by `g^{N-N₀}`; the degree bookkeeping is
absorbed by `ProjectiveSpectrum.Twist.twistModuleMulHom_congr`, which says that the degree index
recorded on the multiplier is irrelevant. -/
theorem exists_uniform_chart_lift {u g : A} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [(ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (hBg : (Proj 𝒜).basicOpen (ratioSection 𝒜 hu hg) ≤ basicOpen 𝒜 g)
    (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 g)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ m : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ)), basicOpen 𝒜 u),
        ∀ (hgN : g ^ N ∈ 𝒜 N),
          (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
              (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hu hg))).op m
            = Scheme.Modules.Hom.app
                (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N)
                  e (e + (N : ℤ)) rfl)
                ((Proj 𝒜).basicOpen (ratioSection 𝒜 hu hg))
                ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
                  (homOfLE hBg).op t) := by
  obtain ⟨N₀, m₀, hm₀⟩ := exists_app_twistModuleMulHom_eq_res 𝒜 hu hg F e
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hBg).op t)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, N = N₀ + K := ⟨N - N₀, (Nat.add_sub_cancel' hN).symm⟩
  have huN₀ : u ^ N₀ ∈ 𝒜 N₀ := by simpa using SetLike.pow_mem_graded _ hu
  have hgN₀ : g ^ N₀ ∈ 𝒜 N₀ := by simpa using SetLike.pow_mem_graded _ hg
  have hgK : g ^ K ∈ 𝒜 K := by simpa using SetLike.pow_mem_graded _ hg
  have hd1 : (e + (N : ℤ)) = (e + (N₀ : ℤ)) + (K : ℤ) := by rw [hK]; push_cast; ring
  have hd2 : (e + (N : ℤ)) = e + ((N₀ + K : ℕ) : ℤ) := by rw [hK]
  refine ⟨Scheme.Modules.Hom.app
    (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
      (⟨u ^ N₀ * g ^ K, SetLike.mul_mem_graded huN₀ hgK⟩ : 𝒜 (N₀ + K)) e (e + (N : ℤ)) hd2)
    (basicOpen 𝒜 u) m₀, fun hgN ↦ ?_⟩
  have hpow : (g : A) ^ N = g ^ N₀ * g ^ K := by rw [hK, pow_add]
  have hstep : Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
        (⟨u ^ N₀ * g ^ K, SetLike.mul_mem_graded huN₀ hgK⟩ : 𝒜 (N₀ + K)) e (e + (N : ℤ)) hd2)
      (basicOpen 𝒜 u) m₀
      = Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ K, hgK⟩ : 𝒜 K)
          (e + (N₀ : ℤ)) (e + (N : ℤ)) hd1) (basicOpen 𝒜 u)
        (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨u ^ N₀, huN₀⟩ : 𝒜 N₀)
            e (e + (N₀ : ℤ)) rfl) (basicOpen 𝒜 u) m₀) := by
    rw [← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨u ^ N₀, huN₀⟩ : 𝒜 N₀)
      (⟨g ^ K, hgK⟩ : 𝒜 K) e (e + (N₀ : ℤ)) (e + (N : ℤ)) rfl hd1 hd2]
    rfl
  rw [hstep, ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N)
      (⟨g ^ N₀ * g ^ K, SetLike.mul_mem_graded hgN₀ hgK⟩ : 𝒜 (N₀ + K)) hpow e (e + (N : ℤ))
      rfl hd2,
    ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨g ^ N₀, hgN₀⟩ : 𝒜 N₀)
      (⟨g ^ K, hgK⟩ : 𝒜 K) e (e + (N₀ : ℤ)) (e + (N : ℤ)) rfl hd1 hd2,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    hm₀ (e + (N₀ : ℤ)) rfl huN₀ hgN₀, Scheme.Modules.app_restrict]

/-- Multiplying by `a^n` and then by `a^K` is multiplying by `a^(n+K)`, at the level of sections
over a fixed open. -/
theorem app_twistModuleMulHom_pow_add {a : A} (F : (Proj 𝒜).Modules) (e : ℤ)
    (V : (Proj 𝒜).Opens) (n K : ℕ)
    (han : a ^ n ∈ 𝒜 n) (haK : a ^ K ∈ 𝒜 K) (hanK : a ^ (n + K) ∈ 𝒜 (n + K))
    (ecn ec : ℤ) (hecn : ecn = e + (n : ℤ)) (hec : ec = e + ((n + K : ℕ) : ℤ))
    (hd1 : ec = ecn + (K : ℤ))
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V)) :
    Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨a ^ K, haK⟩ : 𝒜 K) ecn ec hd1) V
        (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨a ^ n, han⟩ : 𝒜 n) e ecn hecn) V σ)
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨a ^ (n + K), hanK⟩ : 𝒜 (n + K))
            e ec hec) V σ := by
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨a ^ (n + K), hanK⟩ : 𝒜 (n + K))
      (⟨a ^ n * a ^ K, SetLike.mul_mem_graded han haK⟩ : 𝒜 (n + K)) (pow_add a n K)
      e ec hec hec,
    ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨a ^ n, han⟩ : 𝒜 n)
      (⟨a ^ K, haK⟩ : 𝒜 K) e ecn ec hecn hd1 hec]
  rfl

/-- **Multiplying twice is multiplying by the product**, at the level of sections over a fixed
open, in full generality: the three degree indices are unconstrained, only the underlying
elements must multiply correctly.  This is the workhorse behind every power-raising step. -/
theorem app_twistModuleMulHom_mul_eq {m m' m'' : ℕ} (F : (Proj 𝒜).Modules) (e : ℤ)
    (V : (Proj 𝒜).Opens) (p : 𝒜 m) (q : 𝒜 m') (r : 𝒜 m'')
    (hpq : (p : A) * (q : A) = (r : A))
    (ecn ec : ℤ) (hecn : ecn = e + (m : ℤ)) (hd1 : ec = ecn + (m' : ℤ))
    (hec : ec = e + (m'' : ℤ))
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V)) :
    Scheme.Modules.Hom.app (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F q ecn ec hd1) V
        (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F p e ecn hecn) V σ)
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F r e ec hec) V σ := by
  have hec' : ec = e + ((m + m' : ℕ) : ℤ) := by rw [hd1, hecn]; push_cast; ring
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F r
      (⟨(p : A) * (q : A), SetLike.mul_mem_graded p.2 q.2⟩ : 𝒜 (m + m')) hpq.symm e ec hec hec',
    ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F p q e ecn ec hecn hd1 hec']
  rfl

/-- A vanishing `a^n · σ = 0` persists to every larger power. -/
theorem app_twistModuleMulHom_pow_eq_zero_of_le {a : A} (ha : a ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (e : ℤ) (V : (Proj 𝒜).Opens)
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V)) (n M : ℕ) (hnM : n ≤ M)
    (han : a ^ n ∈ 𝒜 n) (haM : a ^ M ∈ 𝒜 M)
    (ecn ec : ℤ) (hecn : ecn = e + (n : ℤ)) (hec : ec = e + (M : ℤ))
    (h : Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨a ^ n, han⟩ : 𝒜 n) e ecn hecn) V σ = 0) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨a ^ M, haM⟩ : 𝒜 M) e ec hec) V σ = 0 := by
  obtain ⟨K, rfl⟩ : ∃ K, M = n + K := ⟨M - n, (Nat.add_sub_cancel' hnM).symm⟩
  have haK : a ^ K ∈ 𝒜 K := by simpa using SetLike.pow_mem_graded _ ha
  have hd1 : ec = ecn + (K : ℤ) := by rw [hec, hecn]; push_cast; ring
  rw [← app_twistModuleMulHom_pow_add 𝒜 F e V n K han haK haM ecn ec hecn hec hd1 σ, h, map_zero]

/-- The chart-lift identity, restricted to an arbitrary open contained in both `D₊(u)` and
`D₊(g)`.  Only the inequality `V ≤ D₊(u) ⊓ D₊(g) = D₊(g/u)` is transported, never a section. -/
theorem res_of_chart_lift {u g : A} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (e : ℤ) (N : ℕ) (hgN : g ^ N ∈ 𝒜 N)
    (hBg : (Proj 𝒜).basicOpen (ratioSection 𝒜 hu hg) ≤ basicOpen 𝒜 g)
    (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 g))
    (m : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ)), basicOpen 𝒜 u))
    (hm : (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hu hg))).op m
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N)
            e (e + (N : ℤ)) rfl)
          ((Proj 𝒜).basicOpen (ratioSection 𝒜 hu hg))
          ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hBg).op t))
    (V : (Proj 𝒜).Opens) (hVu : V ≤ basicOpen 𝒜 u) (hVg : V ≤ basicOpen 𝒜 g) :
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map (homOfLE hVu).op m
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N)
            e (e + (N : ℤ)) rfl) V
          ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVg).op t) := by
  have hVBr : V ≤ (Proj 𝒜).basicOpen (ratioSection 𝒜 hu hg) := by
    rw [basicOpen_ratioSection 𝒜 hu hg Nat.one_pos]
    exact le_inf hVu hVg
  have hcong := congrArg
    ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map (homOfLE hVBr).op) hm
  rw [← Scheme.Modules.app_restrict] at hcong
  have hL : ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
        (homOfLE hVBr).op)
      (((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hu hg))).op) m)
      = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
        (homOfLE hVu).op) m := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  have hR : ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVBr).op)
      (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hBg).op) t)
      = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVg).op) t := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hL, hR] at hcong
  exact hcong

/-- **Hartshorne II.5.14, surjectivity.**  If `Proj 𝒜` is covered by the degree-one charts
`D₊(x i)`, then every section of `F(e)` over the chart `D₊(x i₀)` becomes, after multiplication by
a power of `x i₀`, the restriction of a *global* section of a twist of `F`.

Together with `AlgebraicGeometry.Proj.exists_pow_app_top_eq_zero` this says that
`Γ(D₊(x i₀), F(e))` is the degree-`e` part of the localization of `⨁_d Γ(Proj 𝒜, F(d))` away from
`x i₀`. -/
theorem exists_global_lift {ι : Type*} [Finite ι] (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ i, basicOpen 𝒜 (x i))
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [∀ d : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).IsQuasicoherent]
    (i₀ : ι) (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 (x i₀))) :
    ∃ (L : ℕ) (hgL : (x i₀) ^ L ∈ 𝒜 L)
      (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (L : ℤ)), ⊤)),
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (L : ℤ))).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op s
        = Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₀) ^ L, hgL⟩ : 𝒜 L)
              e (e + (L : ℤ)) rfl) (basicOpen 𝒜 (x i₀)) t := by
  classical
  haveI := Fintype.ofFinite ι
  have hBg : ∀ j : ι,
      (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)) ≤ basicOpen 𝒜 (x i₀) := by
    intro j
    rw [basicOpen_ratioSection 𝒜 (hx j) (hx i₀) Nat.one_pos]
    exact inf_le_right
  have hBj : ∀ j : ι,
      (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)) ≤ basicOpen 𝒜 (x j) :=
    fun j ↦ (Proj 𝒜).basicOpen_le _
  choose N₀ hN₀ using fun j : ι ↦ exists_uniform_chart_lift 𝒜 (hx j) (hx i₀) F e (hBg j) t
  obtain ⟨N, hNle⟩ : ∃ N : ℕ, ∀ j, N₀ j ≤ N :=
    ⟨Finset.univ.sup N₀, fun j ↦ Finset.le_sup (Finset.mem_univ j)⟩
  choose m hm using fun j : ι ↦ hN₀ j N (hNle j)
  have hgN : (x i₀) ^ N ∈ 𝒜 N := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  -- The chart lifts, restricted to an arbitrary open of `D₊(x j) ⊓ D₊(x i₀)`.
  have hres : ∀ (j : ι) (V : (Proj 𝒜).Opens) (hVj : V ≤ basicOpen 𝒜 (x j))
      (hVg : V ≤ basicOpen 𝒜 (x i₀)),
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
          (homOfLE hVj).op (m j)
        = Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₀) ^ N, hgN⟩ : 𝒜 N)
              e (e + (N : ℤ)) rfl) V
            ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVg).op t) :=
    fun j V hVj hVg ↦ res_of_chart_lift 𝒜 (hx j) (hx i₀) F e N hgN (hBg j) t (m j) (hm j hgN)
      V hVj hVg
  -- On the overlap of two charts the two lifts differ by a section supported away from
  -- `D₊(x i₀)`, hence killed by a power of `x i₀`.
  have hovl : ∀ j k : ι, ∃ M : ℕ, ∀ (hgM : (x i₀) ^ M ∈ 𝒜 M) (ec : ℤ)
      (hec : ec = (e + (N : ℤ)) + (M : ℤ)),
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₀) ^ M, hgM⟩ : 𝒜 M)
          (e + (N : ℤ)) ec hec) (basicOpen 𝒜 (x j) ⊓ basicOpen 𝒜 (x k))
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
            (homOfLE (inf_le_left : basicOpen 𝒜 (x j) ⊓ basicOpen 𝒜 (x k) ≤
              basicOpen 𝒜 (x j))).op) (m j)
          - ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
            (homOfLE (inf_le_right : basicOpen 𝒜 (x j) ⊓ basicOpen 𝒜 (x k) ≤
              basicOpen 𝒜 (x k))).op) (m k)) = 0 := by
    intro j k
    refine exists_app_twistModuleMulHom_eq_zero_inf 𝒜 (hx j) (hx k) (hx i₀) F (e + (N : ℤ)) _ ?_
    intro V hVU hVg
    have hVj : V ≤ basicOpen 𝒜 (x j) := le_trans hVU inf_le_left
    have hVk : V ≤ basicOpen 𝒜 (x k) := le_trans hVU inf_le_right
    have hL : ∀ (l : ι) (hl : basicOpen 𝒜 (x j) ⊓ basicOpen 𝒜 (x k) ≤ basicOpen 𝒜 (x l))
        (hVl : V ≤ basicOpen 𝒜 (x l)),
        ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map (homOfLE hVU).op)
          (((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
            (homOfLE hl).op) (m l))
          = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (N : ℤ))).presheaf.map
            (homOfLE hVl).op) (m l) := by
      intro l hl hVl
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    rw [map_sub, hL j inf_le_left hVj, hL k inf_le_right hVk, hres j V hVj hVg,
      hres k V hVk hVg, sub_self]
  choose Mjk hMjk using hovl
  obtain ⟨M, hMle⟩ : ∃ M : ℕ, ∀ j k, Mjk j k ≤ M :=
    ⟨Finset.univ.sup fun p : ι × ι ↦ Mjk p.1 p.2,
      fun j k ↦ Finset.le_sup (f := fun p : ι × ι ↦ Mjk p.1 p.2) (Finset.mem_univ (j, k))⟩
  have hgM : (x i₀) ^ M ∈ 𝒜 M := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  have hgL : (x i₀) ^ (N + M) ∈ 𝒜 (N + M) := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  have hdL : e + ((N + M : ℕ) : ℤ) = (e + (N : ℤ)) + (M : ℤ) := by push_cast; ring
  -- the glueing data
  have hcompat : TopCat.Presheaf.IsCompatible
      (Scheme.Modules.abSheaf
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ)))).1
      (fun j : ι ↦ basicOpen 𝒜 (x j))
      (fun j : ι ↦ Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₀) ^ M, hgM⟩ : 𝒜 M)
          (e + (N : ℤ)) (e + ((N + M : ℕ) : ℤ)) hdL) (basicOpen 𝒜 (x j)) (m j)) := by
    intro j k
    have hLj : (Opens.infLELeft (basicOpen 𝒜 (x j)) (basicOpen 𝒜 (x k)))
        = homOfLE inf_le_left := Subsingleton.elim _ _
    have hRk : (Opens.infLERight (basicOpen 𝒜 (x j)) (basicOpen 𝒜 (x k)))
        = homOfLE inf_le_right := Subsingleton.elim _ _
    rw [hLj, hRk, ← Scheme.Modules.app_restrict, ← Scheme.Modules.app_restrict,
      ← sub_eq_zero, ← map_sub]
    exact app_twistModuleMulHom_pow_eq_zero_of_le 𝒜 (hx i₀) F (e + (N : ℤ)) _ _
      (Mjk j k) M (hMle j k) (by simpa using SetLike.pow_mem_graded _ (hx i₀)) hgM
      _ _ rfl hdL (hMjk j k _ _ rfl)
  obtain ⟨s, hs, -⟩ := (Scheme.Modules.abSheaf
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ)))).existsUnique_gluing'
      (fun j : ι ↦ basicOpen 𝒜 (x j)) ⊤ (fun _ ↦ homOfLE le_top) hcover _ hcompat
  refine ⟨N + M, hgL, s, ?_⟩
  -- the `D₊(x j) ⊓ D₊(x i₀)` cover `D₊(x i₀)`
  have hcov2 : basicOpen 𝒜 (x i₀)
      ≤ ⨆ j : ι, (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)) := by
    intro p hp
    obtain ⟨j, hj⟩ : ∃ j, p ∈ basicOpen 𝒜 (x j) := by
      have hmem := hcover (show p ∈ (⊤ : (Proj 𝒜).Opens) from trivial)
      simpa using hmem
    have : p ∈ (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)) := by
      rw [basicOpen_ratioSection 𝒜 (hx j) (hx i₀) Nat.one_pos]
      exact ⟨hj, hp⟩
    exact Opens.mem_iSup.mpr ⟨j, this⟩
  refine (Scheme.Modules.abSheaf
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ)))).eq_of_locally_eq'
      (fun j : ι ↦ (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)))
      (basicOpen 𝒜 (x i₀)) (fun j ↦ homOfLE (hBg j)) hcov2 _ _ ?_
  intro j
  have hsl : ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ))).presheaf.map
        (homOfLE (hBg j)).op)
      (((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ))).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op) s)
      = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ))).presheaf.map
        (homOfLE (hBj j)).op)
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + ((N + M : ℕ) : ℤ))).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x j) ≤ ⊤)).op) s) := by
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  rw [hsl, hs j, ← Scheme.Modules.app_restrict, ← Scheme.Modules.app_restrict,
    hres j _ (hBj j) (hBg j),
    app_twistModuleMulHom_pow_add 𝒜 F e _ N M hgN hgM hgL (e + (N : ℤ))
      (e + ((N + M : ℕ) : ℤ)) rfl rfl hdL]

/-- `exists_global_lift`, with the target degree taken as a parameter together with the equation
that pins it down.  Consumers can then instantiate it at whatever term the ambient construction
produces — `GradedModule.locDeg [i] d L`, say — instead of transporting the section along
`locDeg [i] d L = d + L`. -/
theorem exists_global_lift' {ι : Type*} [Finite ι] (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ i, basicOpen 𝒜 (x i))
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [∀ d : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).IsQuasicoherent]
    (i₀ : ι) (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 (x i₀))) :
    ∃ (L : ℕ) (hgL : (x i₀) ^ L ∈ 𝒜 L),
      ∀ (ec : ℤ) (hec : ec = e + (L : ℤ)),
        ∃ s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F ec, ⊤),
          (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec).presheaf.map
              (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op s
            = Scheme.Modules.Hom.app
                (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₀) ^ L, hgL⟩ : 𝒜 L)
                  e ec hec) (basicOpen 𝒜 (x i₀)) t := by
  obtain ⟨L, hgL, s, hs⟩ := exists_global_lift 𝒜 x hx hcover F e i₀ t
  refine ⟨L, hgL, fun ec hec ↦ ?_⟩
  subst hec
  exact ⟨s, hs⟩

/-! ## The chart trivialization in every degree -/

/-- Multiplication by `f` is bijective on sections over any open of the chart `D₊(f)`.
This is `ProjectiveSpectrum.Twist.bijective_twistModuleMulHom_app` with the open written as a
plain open of `Proj 𝒜` rather than as `ι ''ᵁ W`. -/
theorem bijective_app_twistModuleMulHom_one {f : A} (hf : f ∈ 𝒜 1) (F : (Proj 𝒜).Modules)
    (d ec : ℤ) (hec : ec = d + ((1 : ℕ) : ℤ))
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f) :
    Function.Bijective (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f, hf⟩ : 𝒜 1) d ec hec) V) := by
  subst hec
  obtain ⟨W, hW⟩ : ∃ W : (basicOpen 𝒜 f).toScheme.Opens, V = (basicOpen 𝒜 f).ι ''ᵁ W :=
    ⟨_, eq_image_preimage_of_le hV⟩
  subst hW
  exact ProjectiveSpectrum.Twist.bijective_twistModuleMulHom_app 𝒜 hf d rfl F W

/-- **The chart trivialization.**  Over any open of `D₊(f)`, multiplication by `f^{k+1}` is a
bijection `Γ(F(d)) ≃ Γ(F(d + k + 1))`: on `D₊(f)` the twist `𝒪(1)` is trivialized by `f`.

Stated for the exponent `k + 1` rather than `k`: at exponent `0` the multiplier lives in `𝒜 0`
and the statement would carry a transport along `d + 0 = d`, which no consumer needs. -/
theorem bijective_app_twistModuleMulHom_pow {f : A} (hf : f ∈ 𝒜 1) (F : (Proj 𝒜).Modules)
    (d : ℤ) :
    ∀ (k : ℕ) (hfk : f ^ (k + 1) ∈ 𝒜 (k + 1)) (ec : ℤ) (hec : ec = d + ((k + 1 : ℕ) : ℤ))
      (V : (Proj 𝒜).Opens), V ≤ basicOpen 𝒜 f →
      Function.Bijective (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ (k + 1), hfk⟩ : 𝒜 (k + 1))
          d ec hec) V) := by
  intro k
  induction k with
  | zero =>
    intro hfk ec hec V hV
    rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨f ^ (0 + 1), hfk⟩ : 𝒜 (0 + 1)) (⟨f, hf⟩ : 𝒜 1) (pow_one f) d ec hec (by rw [hec])]
    exact bijective_app_twistModuleMulHom_one 𝒜 hf F d ec (by rw [hec]) V hV
  | succ k ih =>
    intro hfk ec hec V hV
    have hfk1 : f ^ (k + 1) ∈ 𝒜 (k + 1) := by simpa using SetLike.pow_mem_graded _ hf
    have hd1 : d + ((k + 1 : ℕ) : ℤ) = d + ((k + 1 : ℕ) : ℤ) := rfl
    have hd2 : ec = (d + ((k + 1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ) := by rw [hec]; push_cast; ring
    have hd3 : ec = d + ((k + 1 + 1 : ℕ) : ℤ) := hec
    rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
        (⟨f ^ (k + 1 + 1), hfk⟩ : 𝒜 (k + 1 + 1))
        (⟨f ^ (k + 1) * f, SetLike.mul_mem_graded hfk1 hf⟩ : 𝒜 (k + 1 + 1))
        (pow_succ f (k + 1)) d ec hec hd3,
      ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨f ^ (k + 1), hfk1⟩ : 𝒜 (k + 1))
        (⟨f, hf⟩ : 𝒜 1) d (d + ((k + 1 : ℕ) : ℤ)) ec hd1 hd2 hd3,
      Scheme.Modules.Hom.comp_app]
    haveI : IsIso (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ (k + 1), hfk1⟩ : 𝒜 (k + 1))
          d (d + ((k + 1 : ℕ) : ℤ)) hd1) V) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (ih hfk1 (d + ((k + 1 : ℕ) : ℤ)) hd1 V hV)
    haveI : IsIso (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f, hf⟩ : 𝒜 1)
          (d + ((k + 1 : ℕ) : ℤ)) ec hd2) V) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_app_twistModuleMulHom_one 𝒜 hf F (d + ((k + 1 : ℕ) : ℤ)) ec hd2 V hV)
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- Multiplication by `f^0 = 1` is bijective on sections over any open: it is the identity. -/
theorem bijective_app_twistModuleMulHom_zero {f : A} (F : (Proj 𝒜).Modules)
    (d dc : ℤ) (hdc : dc = d + ((0 : ℕ) : ℤ)) (h0 : f ^ 0 ∈ 𝒜 0) (V : (Proj 𝒜).Opens) :
    Function.Bijective (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ 0, h0⟩ : 𝒜 0) d dc hdc) V) := by
  have hdd : dc = d := by rw [hdc]; simp
  subst hdd
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F (⟨f ^ 0, h0⟩ : 𝒜 0)
      (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) (pow_zero f) dc dc hdc hdc,
    ProjectiveSpectrum.Twist.twistModuleMulHom_one]
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- **The chart trivialization, all exponents.**  Over any open of `D₊(f)`, multiplication by
`f^k` is a bijection `Γ(F(d)) ≃ Γ(F(d + k))`. -/
theorem bijective_app_twistModuleMulHom_natPow {f : A} (hf : f ∈ 𝒜 1) (F : (Proj 𝒜).Modules)
    (d : ℤ) (k : ℕ) (hfk : f ^ k ∈ 𝒜 k) (ec : ℤ) (hec : ec = d + (k : ℤ))
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f) :
    Function.Bijective (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ k, hfk⟩ : 𝒜 k) d ec hec) V) := by
  cases k with
  | zero => exact bijective_app_twistModuleMulHom_zero 𝒜 F d ec hec hfk V
  | succ k => exact bijective_app_twistModuleMulHom_pow 𝒜 hf F d k hfk ec hec V hV

/-- The chart trivialization as an equivalence. -/
noncomputable def chartTwistEquiv {f : A} (hf : f ∈ 𝒜 1) (F : (Proj 𝒜).Modules)
    (d : ℤ) (k : ℕ) (hfk : f ^ k ∈ 𝒜 k) (ec : ℤ) (hec : ec = d + (k : ℤ))
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f) :
    Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, V)
      ≃ Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F ec, V) :=
  Equiv.ofBijective _ (bijective_app_twistModuleMulHom_natPow 𝒜 hf F d k hfk ec hec V hV)

@[simp]
theorem chartTwistEquiv_apply {f : A} (hf : f ∈ 𝒜 1) (F : (Proj 𝒜).Modules)
    (d : ℤ) (k : ℕ) (hfk : f ^ k ∈ 𝒜 k) (ec : ℤ) (hec : ec = d + (k : ℤ))
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f)
    (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, V)) :
    chartTwistEquiv 𝒜 hf F d k hfk ec hec V hV s
      = Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ k, hfk⟩ : 𝒜 k) d ec hec) V s :=
  rfl

/-- Multiplication by `f^k g^k` is bijective on any open contained in both `D₊(f)` and `D₊(g)`:
the twist is trivialized there by either variable. -/
theorem bijective_app_twistModuleMulHom_mul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (d : ℤ) (k : ℕ) (hfg : f ^ k * g ^ k ∈ 𝒜 (k + k))
    (ec : ℤ) (hec : ec = d + ((k + k : ℕ) : ℤ))
    (V : (Proj 𝒜).Opens) (hVf : V ≤ basicOpen 𝒜 f) (hVg : V ≤ basicOpen 𝒜 g) :
    Function.Bijective (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ k * g ^ k, hfg⟩ : 𝒜 (k + k))
        d ec hec) V) := by
  have hfk : f ^ k ∈ 𝒜 k := by simpa using SetLike.pow_mem_graded _ hf
  have hgk : g ^ k ∈ 𝒜 k := by simpa using SetLike.pow_mem_graded _ hg
  have hmid : d + (k : ℤ) = d + (k : ℤ) := rfl
  have hd2 : ec = (d + (k : ℤ)) + (k : ℤ) := by rw [hec]; push_cast; ring
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨f ^ k * g ^ k, hfg⟩ : 𝒜 (k + k))
      (⟨f ^ k * g ^ k, SetLike.mul_mem_graded hfk hgk⟩ : 𝒜 (k + k)) rfl d ec hec hec,
    ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨f ^ k, hfk⟩ : 𝒜 k)
      (⟨g ^ k, hgk⟩ : 𝒜 k) d (d + (k : ℤ)) ec hmid hd2 hec,
    Scheme.Modules.Hom.comp_app]
  haveI : IsIso (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ k, hfk⟩ : 𝒜 k) d (d + (k : ℤ))
        hmid) V) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_app_twistModuleMulHom_natPow 𝒜 hf F d k hfk (d + (k : ℤ)) hmid V hVf)
  haveI : IsIso (Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ k, hgk⟩ : 𝒜 k) (d + (k : ℤ)) ec
        hd2) V) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_app_twistModuleMulHom_natPow 𝒜 hg F (d + (k : ℤ)) k hgk ec hd2 V hVg)
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- **Hartshorne II.5.14, injectivity on a two-variable chart.**  A global section of `F(e)`
vanishing on the overlap `D₊(x i₀) ⊓ D₊(x i₁)` is killed by a power of `x i₀ · x i₁`.

Only degree-one tools are used: restrict to the chart `D₊(x i₀)`, kill by a power of the ratio
`x i₁ / x i₀` (`exists_pow_ratioSection_smul_eq_zero`), trade that for a power of `x i₁`
(`app_twistModuleMulHom_eq_zero_of_le`), and then apply the one-variable injectivity. -/
theorem exists_pow_app_top_eq_zero_pair {ι : Type*} [Finite ι] (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ i, basicOpen 𝒜 (x i))
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [∀ d : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).IsQuasicoherent]
    (i₀ i₁ : ι) (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, ⊤))
    (ht : (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 (x i₀) ⊓ basicOpen 𝒜 (x i₁) ≤ ⊤)).op t = 0) :
    ∃ N : ℕ, ∀ (hN : (x i₀) ^ N * (x i₁) ^ N ∈ 𝒜 (N + N)) (ec : ℤ)
      (hec : ec = e + ((N + N : ℕ) : ℤ)),
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
          (⟨(x i₀) ^ N * (x i₁) ^ N, hN⟩ : 𝒜 (N + N)) e ec hec) ⊤ t = 0 := by
  classical
  -- Step 1: on the chart `D₊(x i₀)`, a power of the ratio kills `t`.
  have hle : (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx i₀) (hx i₁))
      ≤ basicOpen 𝒜 (x i₀) ⊓ basicOpen 𝒜 (x i₁) :=
    le_of_eq (basicOpen_ratioSection 𝒜 (hx i₀) (hx i₁) Nat.one_pos)
  have hz : (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
      (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 (hx i₀) (hx i₁)))).op
      ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op t) = 0 := by
    have hrestr := congrArg ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
      (homOfLE hle).op) ht
    rw [map_zero, ← CategoryTheory.comp_apply, ← Functor.map_comp] at hrestr
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    exact hrestr
  obtain ⟨M, hM⟩ := exists_pow_ratioSection_smul_eq_zero 𝒜 (hx i₀) (hx i₁)
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F e) _ hz
  -- Step 2: trade the ratio for a power of `x i₁`, on the chart.
  have hbM : (x i₁) ^ M ∈ 𝒜 M := by simpa using SetLike.pow_mem_graded _ (hx i₁)
  have haM : (x i₀) ^ M ∈ 𝒜 M := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  have hchart : Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₁) ^ M, hbM⟩ : 𝒜 M)
        e (e + (M : ℤ)) rfl) (basicOpen 𝒜 (x i₀))
      ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op t) = 0 := by
    refine app_twistModuleMulHom_eq_zero_of_le 𝒜 (hx i₀) (hx i₁) F M e (e + (M : ℤ)) rfl
      haM hbM (basicOpen 𝒜 (x i₀)) le_rfl _ ?_
    simpa using hM
  -- Step 3: the one-variable injectivity applied to `x i₁ ^ M · t`.
  have hres : (ProjectiveSpectrum.Twist.twistModule 𝒜 F (e + (M : ℤ))).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op
      (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨(x i₁) ^ M, hbM⟩ : 𝒜 M)
          e (e + (M : ℤ)) rfl) ⊤ t) = 0 := by
    rw [← Scheme.Modules.app_restrict]
    exact hchart
  obtain ⟨N₀, hN₀⟩ := exists_pow_app_top_eq_zero 𝒜 x hx hcover F (e + (M : ℤ)) i₀ _ hres
  refine ⟨max M N₀, fun hN ec hec ↦ ?_⟩
  set N := max M N₀ with hNdef
  have hleM : M ≤ N := le_max_left _ _
  have hle₀ : N₀ ≤ N := le_max_right _ _
  have haN₀ : (x i₀) ^ N₀ ∈ 𝒜 N₀ := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  have haS : (x i₀) ^ (N - N₀) ∈ 𝒜 (N - N₀) := by simpa using SetLike.pow_mem_graded _ (hx i₀)
  have hbS : (x i₁) ^ (N - M) ∈ 𝒜 (N - M) := by simpa using SetLike.pow_mem_graded _ (hx i₁)
  -- the two-step multiplier `x i₁ ^ M * x i₀ ^ N₀`
  have hstep1 : Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
        (⟨(x i₁) ^ M * (x i₀) ^ N₀, SetLike.mul_mem_graded hbM haN₀⟩ : 𝒜 (M + N₀))
        e (e + ((M + N₀ : ℕ) : ℤ)) (by push_cast; ring)) ⊤ t = 0 := by
    rw [← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F (⟨(x i₁) ^ M, hbM⟩ : 𝒜 M)
        (⟨(x i₀) ^ N₀, haN₀⟩ : 𝒜 N₀) e (e + (M : ℤ)) (e + ((M + N₀ : ℕ) : ℤ)) rfl
        (by push_cast; ring) (by push_cast; ring),
      Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    exact hN₀ haN₀ (e + ((M + N₀ : ℕ) : ℤ)) (by push_cast; ring)
  -- multiply further to reach the exponent `N` in both variables
  have h1 : (x i₀) ^ N₀ * (x i₀) ^ (N - N₀) = (x i₀) ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hle₀]
  have h2 : (x i₁) ^ M * (x i₁) ^ (N - M) = (x i₁) ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hleM]
  have hpp : ((x i₁) ^ M * (x i₀) ^ N₀) * ((x i₀) ^ (N - N₀) * (x i₁) ^ (N - M))
      = (x i₀) ^ N * (x i₁) ^ N := by
    rw [← h1, ← h2]; ring
  rw [ProjectiveSpectrum.Twist.twistModuleMulHom_congr 𝒜 F
      (⟨(x i₀) ^ N * (x i₁) ^ N, hN⟩ : 𝒜 (N + N))
      (⟨((x i₁) ^ M * (x i₀) ^ N₀) * ((x i₀) ^ (N - N₀) * (x i₁) ^ (N - M)),
        SetLike.mul_mem_graded (SetLike.mul_mem_graded hbM haN₀)
          (SetLike.mul_mem_graded haS hbS)⟩ : 𝒜 ((M + N₀) + ((N - N₀) + (N - M))))
      hpp.symm e ec hec (by rw [hec]; push_cast [Nat.cast_sub hle₀, Nat.cast_sub hleM]; ring),
    ← ProjectiveSpectrum.Twist.twistModuleMulHom_comp 𝒜 F
      (⟨(x i₁) ^ M * (x i₀) ^ N₀, SetLike.mul_mem_graded hbM haN₀⟩ : 𝒜 (M + N₀))
      (⟨(x i₀) ^ (N - N₀) * (x i₁) ^ (N - M), SetLike.mul_mem_graded haS hbS⟩ :
        𝒜 ((N - N₀) + (N - M)))
      e (e + ((M + N₀ : ℕ) : ℤ)) ec (by push_cast; ring)
      (by rw [hec]; push_cast [Nat.cast_sub hle₀, Nat.cast_sub hleM]; ring)
      (by rw [hec]; push_cast [Nat.cast_sub hle₀, Nat.cast_sub hleM]; ring),
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hstep1, map_zero]

end Proj

end AlgebraicGeometry
