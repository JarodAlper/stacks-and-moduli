module

public import StacksAndModuli.API.ProjBasicOpenRatio
public import StacksAndModuli.API.ProjTwistMulHom

/-!
# `g^N` is the ratio to the `N` times `f^N` on `D₊(f)`

For `f, g` homogeneous of degree one and `U ≤ D₊(f)`, the constant section `g^N` of `𝒪(N)` over
`U` equals `(g/f)^N · f^N`, where `g/f` is the regular function `ratioSection 𝒜 hf hg` restricted
to `U`.

This identity is what lets the argument of Hartshorne II.5.14 pass from a *function* on `D₊(f)`
(where the local module-localization statement lives) to a *section of a twist* (where the graded
module lives), for an arbitrary sheaf `F`: tensoring it with `F` turns
"`(g/f)^N q = 0`" into "`g^N · q = 0`" with no monoidal-restriction machinery.  See
`PLAN-hilbert-quot.md`, "9e′.c refined".

The identity is stated *pointwise*, in the homogeneous localization at a point: packaging it as an
equality of sections runs into the `Γ(twist 𝒜 N, unop V)` versus `(sheafInType 𝒜 N).1.obj V`
mismatch, which the `•` elaborates through before any type ascription can bite.  At a use site the
types are already in the right shape, so the packaging is free there.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace ProjectiveSpectrum.Twist

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The pointwise identity behind `g^N = (g/f)^N · f^N`.**  At any point where `f` does not
vanish, the `N`-th power of the ratio `g/f` times the fraction `f^N / 1` is `g^N / 1`. -/
theorem ratio_pow_mul_homogeneous {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ)
    (x : ProjectiveSpectrum 𝒜) (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (((AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg).1 ⟨x, hfx⟩).val) ^ N
        * Localization.mk (f ^ N) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)
      = Localization.mk (g ^ N) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
  rw [AlgebraicGeometry.Proj.ratioSection_apply_val 𝒜 hf hg x hfx, Localization.mk_pow,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  ring

end ProjectiveSpectrum.Twist
