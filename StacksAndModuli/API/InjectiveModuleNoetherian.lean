module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Injective modules over a noetherian ring

Two facts about an injective module `I` over a noetherian commutative ring `R`, both of them
inputs to Hartshorne III.3.4 (`Ĩ` is a flasque sheaf on `Spec R`), which is in turn the
engine of the acyclicity of quasicoherent sheaves on affine schemes.

* `Module.Injective.surjective_of_isLocalizedModule_powers`: the localization map
  `I → I_f` is *surjective*.  The proof is the classical one: the annihilators of the powers
  of `f` stabilise because `R` is noetherian, so `a ↦ f^r a x` is a well-defined map on the
  principal ideal `(f^{n+r})`, and Baer's criterion extends it to `R`.
* `Module.Injective.exists_add_of_smul_eq_zero`: if an element `d` of `I` is killed by
  `𝔞 * 𝔟`, then `d = d₁ + d₂` with `d₁` killed by `𝔟` and `d₂` killed by a power of `𝔞`.
  Geometrically: a section supported on `V(𝔞) ∪ V(𝔟)` splits as a section supported on
  `V(𝔟)` plus one supported on `V(𝔞)`.  The proof injects `R/(𝔞^n ⊓ 𝔟)` into
  `R/𝔞^n × R/𝔟` — which is where the Artin–Rees lemma enters — and extends `t ↦ t • d`
  across it.

Both are stated for `Module.Injective`, so they apply to the terms of any injective
resolution in `ModuleCat R`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

open scoped Pointwise

namespace Module.Injective

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Type v} [AddCommGroup I] [Module R I]

/-! ## Stabilisation of the annihilators of the powers of an element -/

/-- The annihilator of `f ^ m`, as a monotone family of ideals. -/
def annPow (f : R) : ℕ →o Ideal R where
  toFun m := LinearMap.ker (LinearMap.toSpanSingleton R R (f ^ m))
  monotone' m m' h := by
    intro a ha
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul] at ha ⊢
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, ← mul_assoc, ha, zero_mul]

omit [IsNoetherianRing R] in
lemma mem_annPow {f : R} {m : ℕ} {a : R} : a ∈ annPow f m ↔ a * f ^ m = 0 := by
  show a ∈ LinearMap.ker (LinearMap.toSpanSingleton R R (f ^ m)) ↔ _
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- Over a noetherian ring the annihilators of the powers of `f` stabilise. -/
lemma exists_annPow_stable (f : R) : ∃ r : ℕ, ∀ m ≥ r, annPow f r = annPow f m :=
  monotone_stabilizes_iff_noetherian.mpr inferInstance (annPow f)

/-! ## Localization of an injective module is a quotient of it -/

/-- **Localizing an injective module at an element is surjective.**  For `R` noetherian and
`I` an injective (equivalently Baer) `R`-module, every element of `I_f` is the image of an
element of `I`.

This is the basic-open case of Hartshorne III.3.4: `Γ(Spec R, Ĩ) = I` surjects onto
`Γ(D(f), Ĩ) = I_f`. -/
theorem surjective_of_isLocalizedModule_powers (hI : Module.Baer R I) (f : R)
    {N : Type v} [AddCommGroup N] [Module R N] (loc : I →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers f) loc] :
    Function.Surjective loc := by
  obtain ⟨r, hr⟩ := exists_annPow_stable (R := R) f
  intro ξ
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) loc ξ
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, f ^ n = s := hs
  -- `hx : f ^ n • ξ = loc x`
  set c : R := f ^ (n + r) with hc
  set T : R →ₗ[R] R := LinearMap.toSpanSingleton R R c with hT
  set u : R →ₗ[R] I := LinearMap.toSpanSingleton R I (f ^ r • x) with hu
  have hK : LinearMap.ker T ≤ LinearMap.ker u := by
    intro a ha
    have ha' : a * f ^ (n + r) = 0 := by
      simpa [hT, LinearMap.toSpanSingleton_apply, smul_eq_mul, hc] using ha
    have : a ∈ annPow f r := by
      rw [hr (n + r) (Nat.le_add_left r n)]
      exact mem_annPow.mpr ha'
    have haf : a * f ^ r = 0 := mem_annPow.mp this
    simp only [LinearMap.mem_ker, hu, LinearMap.toSpanSingleton_apply, smul_smul]
    rw [haf, zero_smul]
  obtain ⟨g', hg'⟩ := hI (LinearMap.range T)
    (((LinearMap.ker T).liftQ u hK).comp T.quotKerEquivRange.symm.toLinearMap)
  have hT1 : T 1 = c := by simp [hT, LinearMap.toSpanSingleton_apply]
  have hmem : c ∈ LinearMap.range T := ⟨1, hT1⟩
  have hcy : c • g' 1 = f ^ r • x := by
    have h1 : g' c = c • g' 1 := by
      conv_lhs => rw [show c = c • (1 : R) by simp]
      rw [map_smul]
    have h2 : T.quotKerEquivRange (Submodule.Quotient.mk 1) = ⟨c, hmem⟩ :=
      Subtype.ext (by rw [LinearMap.quotKerEquivRange_apply_mk]; exact hT1)
    have h2' : T.quotKerEquivRange.symm ⟨c, hmem⟩ = Submodule.Quotient.mk 1 := by
      rw [← h2, LinearEquiv.symm_apply_apply]
    rw [← h1, hg' c hmem]
    show ((LinearMap.ker T).liftQ u hK) (T.quotKerEquivRange.symm ⟨c, hmem⟩) = _
    rw [h2', Submodule.liftQ_apply]
    simp [hu, LinearMap.toSpanSingleton_apply]
  refine ⟨g' 1, ?_⟩
  have hinj : Function.Injective ((f ^ (n + r)) • · : N → N) := by
    have hu' := IsLocalizedModule.map_units (S := Submonoid.powers f) loc
      ⟨f ^ (n + r), n + r, rfl⟩
    rw [Module.End.isUnit_iff] at hu'
    exact hu'.1
  apply hinj
  show f ^ (n + r) • loc (g' 1) = f ^ (n + r) • ξ
  rw [← map_smul, ← hc, hcy, map_smul, ← hx]
  show f ^ r • f ^ n • ξ = f ^ (n + r) • ξ
  rw [smul_smul, ← pow_add, add_comm]

/-! ## Splitting an element supported on a union of two closed sets -/

omit [IsNoetherianRing R] in
/-- An ideal acts on `R` itself with `J • ⊤ = J`. -/
lemma ideal_smul_top (J : Ideal R) : J • (⊤ : Submodule R R) = J := by
  refine le_antisymm (Submodule.smul_le.mpr fun r hr t _ => ?_) fun a ha => ?_
  · exact J.mul_mem_right t hr
  · simpa using Submodule.smul_mem_smul ha (Submodule.mem_top (R := R) (x := (1 : R)))

/-- **Artin–Rees in the form used by Hartshorne III.3.4.**  For ideals `𝔞`, `𝔟` of a
noetherian ring there is an exponent `n` with `𝔞 ^ n ⊓ 𝔟 ≤ 𝔞 * 𝔟`. -/
lemma exists_pow_inf_le_mul (𝔞 𝔟 : Ideal R) : ∃ n : ℕ, (𝔞 ^ n) ⊓ 𝔟 ≤ 𝔞 * 𝔟 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := R) 𝔞 (𝔟 : Submodule R R)
  refine ⟨k + 1, ?_⟩
  have h := hk (k + 1) (Nat.le_succ k)
  rw [ideal_smul_top] at h
  rw [h]
  simp only [Nat.add_sub_cancel_left, pow_one]
  refine le_trans (Submodule.smul_mono le_rfl inf_le_right) ?_
  rw [Ideal.smul_eq_mul]

variable {J : Type u} [AddCommGroup J] [Module R J]

/-- **Splitting a section supported on `V(𝔞) ∪ V(𝔟)`.**  Let `J` be an injective module over
a noetherian ring and let `d ∈ J` be killed by `𝔞 * 𝔟`.  Then `d = d₁ + d₂` where `d₁` is
killed by `𝔟` and `d₂` is killed by a power of `𝔞`.

Geometrically, `d` is a section of `J~` supported on `V(𝔞) ∪ V(𝔟)` and the conclusion splits
it into a piece supported on `V(𝔟)` and a piece supported on `V(𝔞)`.  This is the inductive
step of Hartshorne III.3.4: it is what corrects two local lifts into one global lift. -/
theorem exists_add_of_mul_smul_eq_zero (hJ : Module.Baer R J) (𝔞 𝔟 : Ideal R) (d : J)
    (hd : 𝔞 * 𝔟 ≤ LinearMap.ker (LinearMap.toSpanSingleton R J d)) :
    ∃ (n : ℕ) (d₁ d₂ : J), d = d₁ + d₂ ∧ (∀ b ∈ 𝔟, b • d₁ = 0) ∧
      (∀ a ∈ 𝔞 ^ n, a • d₂ = 0) := by
  have : Module.Injective R J := hJ.injective
  obtain ⟨n, hn⟩ := exists_pow_inf_le_mul (R := R) 𝔞 𝔟
  refine ⟨n, ?_⟩
  set A : Ideal R := 𝔞 ^ n with hA
  set B : Ideal R := 𝔟 with hB
  set C : Ideal R := A ⊓ B with hC
  have hCd : C ≤ LinearMap.ker (LinearMap.toSpanSingleton R J d) := le_trans hn hd
  set p : R →ₗ[R] (R ⧸ A) × (R ⧸ B) := (A.mkQ).prod (B.mkQ) with hp
  have hker : LinearMap.ker p = C := by
    rw [hp, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  set α : (R ⧸ C) →ₗ[R] (R ⧸ A) × (R ⧸ B) := C.liftQ p (le_of_eq hker.symm) with hα
  have hαinj : Function.Injective α :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' C p hker.symm)
  set v : (R ⧸ C) →ₗ[R] J := C.liftQ (LinearMap.toSpanSingleton R J d) hCd with hv
  obtain ⟨w, hw⟩ := Module.Injective.out α hαinj v
  refine ⟨w (0, B.mkQ 1), w (A.mkQ 1, 0), ?_, ?_, ?_⟩
  · have : α (C.mkQ 1) = (A.mkQ 1, B.mkQ 1) := rfl
    have hsum : w (0, B.mkQ 1) + w (A.mkQ 1, 0) = w (A.mkQ 1, B.mkQ 1) := by
      rw [← map_add]
      congr 1
      simp
    rw [hsum, ← this, hw, hv, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, one_smul]
  · intro b hb
    have : b • ((0 : R ⧸ A), B.mkQ 1) = (0, 0) := by
      refine Prod.ext (by simp) ?_
      show b • B.mkQ 1 = 0
      rw [← map_smul]
      simpa using (Submodule.Quotient.mk_eq_zero B).mpr (by simpa using hb)
    rw [← map_smul, this]
    exact map_zero w
  · intro a ha
    have : a • (A.mkQ 1, (0 : R ⧸ B)) = (0, 0) := by
      refine Prod.ext ?_ (by simp)
      show a • A.mkQ 1 = 0
      rw [← map_smul]
      simpa using (Submodule.Quotient.mk_eq_zero A).mpr (by simpa using ha)
    rw [← map_smul, this]
    exact map_zero w

end Module.Injective
