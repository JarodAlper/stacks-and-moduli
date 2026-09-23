module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Exactness loci over Noetherian rings

For two consecutive maps `M → N → P` over a Noetherian ring, with `N` finite, ordinary
exactness after localization at a prime spreads to one principal localization.  Equivalently,
the ordinary exactness locus is open.  The proof packages the middle homology as the quotient
of the kernel by the image and uses the closed support of a finite module.

This supplies the first neighbourhood reduction in the proof of Stacks Project tag 00RB:
once a finite free complex is exact at a localization, it is exact after one principal
localization.  It does **not** prove the relative fibre-exactness locus of 00RB.  In that locus
the residue field of the contracted coefficient prime varies with the point, so its homology
is not the localization of one fixed finite module.  The remaining step is the determinantal
rank-and-grade argument, including openness of the relative regular-sequence condition in
Cohen–Macaulay fibres.

Main declarations:

* `LinearMap.exact_localizedMap_iff_baseChange`;
* `LinearMap.exists_away_exact_of_atPrime_exact`;
* `LinearMap.exists_basicOpen_exact_of_atPrime_exact`;
* `LinearMap.isOpen_exactLocalizationLocus`.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u v

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Submodule

/-- If a submodule of a finite module becomes the whole module at a prime, it becomes the
whole module after localization away from one element outside that prime. -/
theorem exists_localized_eq_top_away_of_localized_eq_top
    [Module.Finite R M] (P : Submodule R M) (p : Ideal R) [p.IsPrime]
    (hp : P.localized p.primeCompl = ⊤) :
    ∃ f ∉ p, P.localized (Submonoid.powers f) = ⊤ := by
  let Q := M ⧸ P
  let eₚ := localizedQuotientEquiv p.primeCompl P
  haveI : Subsingleton
      (LocalizedModule p.primeCompl M ⧸ P.localized p.primeCompl) := by
    rw [hp]
    exact inferInstance
  haveI : Subsingleton (LocalizedModule p.primeCompl Q) :=
    eₚ.toEquiv.subsingleton_congr.mp inferInstance
  letI : Module.Finite R Q :=
    Module.Finite.of_surjective P.mkQ (Submodule.mkQ_surjective P)
  obtain ⟨f, hf, hQ⟩ := LocalizedModule.exists_subsingleton_away (M := Q) p
  refine ⟨f, hf, ?_⟩
  let eₑ := localizedQuotientEquiv (Submonoid.powers f) P
  haveI : Subsingleton
      (LocalizedModule (Submonoid.powers f) M ⧸ P.localized (Submonoid.powers f)) :=
    eₑ.toEquiv.subsingleton_congr.mpr hQ
  exact Submodule.Quotient.subsingleton_iff.mp inferInstance

/-- If a submodule becomes the whole module away from `a`, it becomes the whole module at
every prime not containing `a`. -/
theorem localized_eq_top_atPrime_of_localized_eq_top_away
    (P : Submodule R M) (a : R) (p : Ideal R) [p.IsPrime]
    (ha : P.localized (Submonoid.powers a) = ⊤) (hap : a ∉ p) :
    P.localized p.primeCompl = ⊤ := by
  let Q := M ⧸ P
  let eₐ := localizedQuotientEquiv (Submonoid.powers a) P
  haveI : Subsingleton
      (LocalizedModule (Submonoid.powers a) M ⧸
        P.localized (Submonoid.powers a)) := by
    rw [ha]
    exact inferInstance
  have hQa : Subsingleton (LocalizedModule (Submonoid.powers a) Q) :=
    eₐ.toEquiv.subsingleton_congr.mp inferInstance
  have hdisj : Disjoint
      (↑(PrimeSpectrum.basicOpen a) : Set (PrimeSpectrum R))
      (Module.support R Q) :=
    LocalizedModule.subsingleton_iff_disjoint.mp hQa
  have hpOpen : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.basicOpen a := hap
  have hpNotSupport : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉
      Module.support R Q := fun hpSupport ↦
    Set.disjoint_left.mp hdisj hpOpen hpSupport
  have hQp : Subsingleton (LocalizedModule p.primeCompl Q) :=
    Module.notMem_support_iff.mp hpNotSupport
  let eₚ := localizedQuotientEquiv p.primeCompl P
  haveI : Subsingleton
      (LocalizedModule p.primeCompl M ⧸ P.localized p.primeCompl) :=
    eₚ.toEquiv.subsingleton_congr.mpr hQp
  exact Submodule.Quotient.subsingleton_iff.mp inferInstance

end Submodule

variable {N P : Type v}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

namespace LinearMap

/-- Exactness of localized-module maps is equivalent to exactness of the corresponding
scalar extensions to the localization ring. -/
theorem exact_localizedMap_iff_baseChange
    (W : Submonoid R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Function.Exact (LocalizedModule.map W f) (LocalizedModule.map W g) ↔
      Function.Exact (f.baseChange (Localization W))
        (g.baseChange (Localization W)) := by
  let eM := LocalizedModule.equivTensorProduct W M
  let eN := LocalizedModule.equivTensorProduct W N
  let eP := LocalizedModule.equivTensorProduct W P
  have hf :
      (f.baseChange (Localization W)).comp eM.toLinearMap =
        eN.toLinearMap.comp (LocalizedModule.map W f) := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      dsimp only [eM, eN]
      simp only [LinearMap.comp_apply, LocalizedModule.map_mk]
      change f.baseChange (Localization W)
          (LocalizedModule.equivTensorProduct W M
            (LocalizedModule.mk m s)) =
        LocalizedModule.equivTensorProduct W N
          (LocalizedModule.mk (f m) s)
      rw [LocalizedModule.equivTensorProduct_apply_mk,
        LocalizedModule.equivTensorProduct_apply_mk,
        LinearMap.baseChange_tmul]
  have hg :
      (g.baseChange (Localization W)).comp eN.toLinearMap =
        eP.toLinearMap.comp (LocalizedModule.map W g) := by
    apply LinearMap.ext
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      dsimp only [eN, eP]
      simp only [LinearMap.comp_apply, LocalizedModule.map_mk]
      change g.baseChange (Localization W)
          (LocalizedModule.equivTensorProduct W N
            (LocalizedModule.mk m s)) =
        LocalizedModule.equivTensorProduct W P
          (LocalizedModule.mk (g m) s)
      rw [LocalizedModule.equivTensorProduct_apply_mk,
        LocalizedModule.equivTensorProduct_apply_mk,
        LinearMap.baseChange_tmul]
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := LocalizedModule.map W f)
    (f₂₃ := LocalizedModule.map W g)
    (g₁₂ := f.baseChange (Localization W))
    (g₂₃ := g.baseChange (Localization W))
    (e₁ := eM) (e₂ := eN) (e₃ := eP) hf hg).symm

/-- Localization of a composite, evaluated on an element. -/
lemma localizedMap_comp_apply (S : Submonoid R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (x : LocalizedModule S M) :
    LocalizedModule.map S g (LocalizedModule.map S f x) =
      LocalizedModule.map S (g.comp f) x := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp

/-- Exactness after localization makes the localized map into the original kernel
surjective. -/
lemma surjective_localizedMap_codRestrict_of_exact
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (fK : M →ₗ[R] LinearMap.ker g)
    (hfK : (LinearMap.ker g).subtype.comp fK = f)
    (S : Submonoid R)
    (h : Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g)) :
    Function.Surjective (LocalizedModule.map S fK) := by
  intro y
  have hyg : LocalizedModule.map S g
      (LocalizedModule.map S (LinearMap.ker g).subtype y) = 0 := by
    rw [localizedMap_comp_apply]
    have hzero : g.comp (LinearMap.ker g).subtype = 0 := by
      ext z
      exact z.property
    rw [hzero]
    simp
  obtain ⟨x, hx⟩ := (h _).mp hyg
  refine ⟨x, LocalizedModule.map_injective S (LinearMap.ker g).subtype
    Subtype.val_injective ?_⟩
  rw [localizedMap_comp_apply, hfK]
  exact hx

/-- If the map into the original kernel is surjective after localization, then the two
localized maps are exact. -/
lemma exact_localizedMap_of_codRestrict_range_eq_top
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (fK : M →ₗ[R] LinearMap.ker g)
    (hfK : (LinearMap.ker g).subtype.comp fK = f)
    (S : Submonoid R)
    (hTop : (LinearMap.range fK).localized S = ⊤) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) := by
  have hfKS : Function.Surjective (LocalizedModule.map S fK) := by
    rw [← LinearMap.range_eq_top]
    have hrange : LinearMap.range (LocalizedModule.map S fK) =
        (LinearMap.range fK).localized S := by
      change LinearMap.range (LocalizedModule.map S fK) =
        (LinearMap.range fK).localized'
          (Localization S) S (LocalizedModule.mkLinearMap S (LinearMap.ker g))
      exact (LinearMap.localized'_range_eq_range_localizedMap
        (Localization S) S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S (LinearMap.ker g)) fK).symm
    rw [hrange, hTop]
  intro y
  constructor
  · intro hy
    have hy' : y ∈ (LinearMap.ker g).localized'
        (Localization S) S (LocalizedModule.mkLinearMap S N) := by
      rw [LinearMap.localized'_ker_eq_ker_localizedMap
        (Localization S) S (LocalizedModule.mkLinearMap S N)
        (LocalizedModule.mkLinearMap S P) g]
      exact hy
    obtain ⟨k, hk, s, hks⟩ := hy'
    let yK : LocalizedModule S (LinearMap.ker g) :=
      LocalizedModule.mk ⟨k, hk⟩ s
    obtain ⟨x, hx⟩ := hfKS yK
    refine ⟨x, ?_⟩
    have hx' := congrArg
      (LocalizedModule.map S (LinearMap.ker g).subtype) hx
    rw [localizedMap_comp_apply, hfK] at hx'
    change LocalizedModule.map S f x = y
    rw [← hks, ← IsLocalizedModule.mk_eq_mk']
    exact hx'.trans (by
      dsimp [yK]
      rw [LocalizedModule.map_mk]
      rfl)
  · rintro ⟨x, rfl⟩
    rw [localizedMap_comp_apply]
    have hgf : g.comp f = 0 := by
      rw [← hfK]
      ext z
      exact (fK z).property
    rw [hgf]
    simp

/-- Over a Noetherian ring, exactness after localization at a prime spreads to exactness
after localization away from one element outside that prime. -/
theorem exists_away_exact_of_atPrime_exact
    [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : g.comp f = 0) (p : Ideal R) [p.IsPrime]
    (hp : Function.Exact
      (LocalizedModule.map p.primeCompl f)
      (LocalizedModule.map p.primeCompl g)) :
    ∃ a ∉ p, Function.Exact
      (LocalizedModule.map (Submonoid.powers a) f)
      (LocalizedModule.map (Submonoid.powers a) g) := by
  let K := LinearMap.ker g
  let fK : M →ₗ[R] K := f.codRestrict K fun x ↦ by
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hgf x
  have hfK : K.subtype.comp fK = f := by
    ext z
    rfl
  have hfKp : Function.Surjective (LocalizedModule.map p.primeCompl fK) :=
    surjective_localizedMap_codRestrict_of_exact f g fK hfK p.primeCompl hp
  haveI : Module.Finite R K :=
    Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker g))
  have hpTop : (LinearMap.range fK).localized p.primeCompl = ⊤ := by
    change (LinearMap.range fK).localized'
      (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl K) = ⊤
    rw [LinearMap.localized'_range_eq_range_localizedMap
      (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M)
      (LocalizedModule.mkLinearMap p.primeCompl K) fK]
    exact LinearMap.range_eq_top.mpr hfKp
  obtain ⟨a, ha, haTop⟩ :=
    Submodule.exists_localized_eq_top_away_of_localized_eq_top
      (LinearMap.range fK) p hpTop
  refine ⟨a, ha, ?_⟩
  exact exact_localizedMap_of_codRestrict_range_eq_top
    f g fK hfK (Submonoid.powers a) haTop

/-- Exactness at a prime has a basic-open neighbourhood on which the two maps are exact at
every prime. -/
theorem exists_basicOpen_exact_of_atPrime_exact
    [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : g.comp f = 0) (p : Ideal R) [p.IsPrime]
    (hp : Function.Exact
      (LocalizedModule.map p.primeCompl f)
      (LocalizedModule.map p.primeCompl g)) :
    ∃ a ∉ p, ∀ (q : Ideal R) (_ : q.IsPrime), a ∉ q →
      Function.Exact
        (LocalizedModule.map q.primeCompl f)
        (LocalizedModule.map q.primeCompl g) := by
  obtain ⟨a, ha, hAway⟩ :=
    exists_away_exact_of_atPrime_exact f g hgf p hp
  let K := LinearMap.ker g
  let fK : M →ₗ[R] K := f.codRestrict K fun x ↦ by
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hgf x
  have hfK : K.subtype.comp fK = f := by
    ext z
    rfl
  have hfKa : Function.Surjective
      (LocalizedModule.map (Submonoid.powers a) fK) :=
    surjective_localizedMap_codRestrict_of_exact
      f g fK hfK (Submonoid.powers a) hAway
  have haTop : (LinearMap.range fK).localized (Submonoid.powers a) = ⊤ := by
    change (LinearMap.range fK).localized'
      (Localization (Submonoid.powers a)) (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) K) = ⊤
    rw [LinearMap.localized'_range_eq_range_localizedMap
      (Localization (Submonoid.powers a)) (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) K) fK]
    exact LinearMap.range_eq_top.mpr hfKa
  refine ⟨a, ha, fun q hq haq ↦ ?_⟩
  letI : q.IsPrime := hq
  have hqTop : (LinearMap.range fK).localized q.primeCompl = ⊤ :=
    Submodule.localized_eq_top_atPrime_of_localized_eq_top_away
      (LinearMap.range fK) a q haTop haq
  exact exact_localizedMap_of_codRestrict_range_eq_top
    f g fK hfK q.primeCompl hqTop

/-- The locus where two consecutive linear maps are exact after localization. -/
def exactLocalizationLocus (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Set (PrimeSpectrum R) :=
  {p | Function.Exact
    (LocalizedModule.map p.asIdeal.primeCompl f)
    (LocalizedModule.map p.asIdeal.primeCompl g)}

@[simp]
theorem mem_exactLocalizationLocus
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (p : PrimeSpectrum R) :
    p ∈ exactLocalizationLocus f g ↔
      Function.Exact
        (LocalizedModule.map p.asIdeal.primeCompl f)
        (LocalizedModule.map p.asIdeal.primeCompl g) :=
  Iff.rfl

/-- The ordinary exactness locus of two consecutive maps with finite middle module over a
Noetherian ring is open. -/
theorem isOpen_exactLocalizationLocus
    [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    IsOpen (exactLocalizationLocus f g) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨a, ha, hbasic⟩ :=
    exists_basicOpen_exact_of_atPrime_exact f g hgf p.asIdeal hp
  refine ⟨PrimeSpectrum.basicOpen a, ?_, (PrimeSpectrum.basicOpen a).2, ha⟩
  intro q hqa
  exact hbasic q.asIdeal q.isPrime hqa

end LinearMap

end
