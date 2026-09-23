module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Exact

/-!
# Dimensions along an exact sequence of vector spaces

Rank–nullity, phrased for `Function.Exact` chains, and the alternating-sum identity for a
six-term exact sequence. The latter is the linear algebra behind the additivity of the
Euler characteristic: a short exact sequence of sheaves on a curve gives a six-term exact
sequence

`0 → H⁰(F₁) → H⁰(F₂) → H⁰(F₃) → H¹(F₁) → H¹(F₂) → H¹(F₃) → 0`

and the identity below turns it into `χ(F₂) = χ(F₁) + χ(F₃)`.

Mathlib has the rank–nullity theorem (`LinearMap.finrank_range_add_finrank_ker`) and the
`Function.Exact` predicate but nothing connecting them, and its
`Mathlib/Algebra/Homology/EulerCharacteristic.lean` is about homological complexes of
`ModuleCat R`, which is not the shape cohomology groups arrive in.

## Main results

* `Module.finrank_range_add_finrank_range_of_exact`: `dim (im f) + dim (im g) = dim V₂` for
  `f ⟶ V₂ ⟶ g` exact at `V₂`.
* `Module.finrank_add_finrank_range_of_exact`, `…_of_surjective`: the two end cases, where
  `f` is injective resp. `g` is surjective.
* `Module.finrank_alternating_eq_zero_of_exact₆`: the alternating sum of dimensions along a
  six-term exact sequence vanishes.
-/

@[expose] public section

universe u

namespace Module

open Module LinearMap

variable {k : Type*} [Field k]

section ThreeTerm

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₂]

/-- **Rank–nullity along an exact sequence.** If `V₁ →f V₂ →g V₃` is exact at `V₂`, then the
dimensions of the two images add up to `dim V₂`. -/
theorem finrank_range_add_finrank_range_of_exact {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hfg : Function.Exact f g) :
    finrank k (LinearMap.range f) + finrank k (LinearMap.range g) = finrank k V₂ := by
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.exact_iff.mp hfg] at h
  omega

/-- The left end of an exact sequence: if moreover `f` is injective, its image may be
replaced by `V₁`. -/
theorem finrank_add_finrank_range_of_exact {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    finrank k V₁ + finrank k (LinearMap.range g) = finrank k V₂ := by
  have h := finrank_range_add_finrank_range_of_exact hfg
  rwa [LinearMap.finrank_range_of_inj hf] at h

/-- The right end of an exact sequence: if moreover `g` is surjective, its image may be
replaced by `V₃`. -/
theorem finrank_range_add_finrank_of_exact_of_surjective {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    finrank k (LinearMap.range f) + finrank k V₃ = finrank k V₂ := by
  have h := finrank_range_add_finrank_range_of_exact hfg
  rwa [LinearMap.range_eq_top.mpr hg, finrank_top] at h

end ThreeTerm

section SixTerm

variable {V₁ V₂ V₃ V₄ V₅ V₆ : Type*}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄] [Module k V₄]
  [AddCommGroup V₅] [Module k V₅] [AddCommGroup V₆] [Module k V₆]
  [FiniteDimensional k V₂] [FiniteDimensional k V₃] [FiniteDimensional k V₄]
  [FiniteDimensional k V₅]

/-- **The alternating sum of dimensions along a six-term exact sequence vanishes.**

For `0 → V₁ →a V₂ →b V₃ →c V₄ →d V₅ →e V₆ → 0` exact,

`dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ - dim V₆ = 0`.

Only the four middle spaces are required to be finite dimensional: `V₁` embeds in `V₂` and
`V₆` is a quotient of `V₅`. -/
theorem finrank_alternating_eq_zero_of_exact₆
    {a : V₁ →ₗ[k] V₂} {b : V₂ →ₗ[k] V₃} {c : V₃ →ₗ[k] V₄} {d : V₄ →ₗ[k] V₅} {e : V₅ →ₗ[k] V₆}
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hcd : Function.Exact c d) (hde : Function.Exact d e) (he : Function.Surjective e) :
    (finrank k V₁ : ℤ) - finrank k V₂ + finrank k V₃ - finrank k V₄ + finrank k V₅ -
      finrank k V₆ = 0 := by
  have h₂ : finrank k V₁ + finrank k (LinearMap.range b) = finrank k V₂ :=
    finrank_add_finrank_range_of_exact ha hab
  have h₃ : finrank k (LinearMap.range b) + finrank k (LinearMap.range c) = finrank k V₃ :=
    finrank_range_add_finrank_range_of_exact hbc
  have h₄ : finrank k (LinearMap.range c) + finrank k (LinearMap.range d) = finrank k V₄ :=
    finrank_range_add_finrank_range_of_exact hcd
  have h₅ : finrank k (LinearMap.range d) + finrank k V₆ = finrank k V₅ :=
    finrank_range_add_finrank_of_exact_of_surjective hde he
  omega

end SixTerm

end Module
