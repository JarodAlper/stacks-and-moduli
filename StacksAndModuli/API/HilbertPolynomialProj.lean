module

public import «StacksProject».«Constructions».«InvertibleSheavesOnProj».«definition-twist»
public import StacksAndModuli.API.GlobalSectionsOverBase
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Hilbert functions and Hilbert polynomials of sheaves on `Proj`

The Hilbert polynomial of a coherent sheaf `F` on `ℙⁿ` over a field is the polynomial
agreeing with `d ↦ χ(F(d))` — equivalently, since the higher cohomology vanishes in large
degree, with `d ↦ dim_k H⁰(ℙⁿ, F(d))` for `d ≫ 0`. This file takes the second description
as the definition, which needs only global sections and so avoids Euler characteristics and
the finiteness of higher cohomology, neither of which the library has.

The base ring is `𝒜 0`, along the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)`; for the
standard graded polynomial ring over a field `k` this is `k` up to the canonical
isomorphism `MvPolynomial.degreeZeroRingEquiv`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.globalSectionsModuleZero`: the `𝒜 0`-module
  structure on `H⁰(Proj 𝒜, F)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.hilbertFunction`: `d ↦ dim_{𝒜 0} H⁰(Proj 𝒜, F(d))`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.HasHilbertPolynomial`: `F` has Hilbert
  polynomial `P` when its Hilbert function agrees with `P` in all large degrees.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.HasHilbertPolynomial.unique`: the Hilbert
  polynomial is unique when it exists, since two polynomials over `ℚ` agreeing at
  infinitely many points are equal.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace Opposite Filter

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The `𝒜 0`-module structure on the global sections of a sheaf of modules on `Proj 𝒜`,
along the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)`.

Not an instance: see `AlgebraicGeometry.Scheme.Modules.globalSectionsModule`. -/
@[instance_reducible]
noncomputable def globalSectionsModuleZero (F : (Proj 𝒜).Modules) :
    Module (𝒜 0) Γ(F, ⊤) :=
  Scheme.Modules.globalSectionsModule (_root_.AlgebraicGeometry.Proj.toSpecZero 𝒜) F

/-- The **Hilbert function** of a sheaf of modules on `Proj 𝒜`:
`d ↦ dim_{𝒜 0} H⁰(Proj 𝒜, F(d))`. -/
noncomputable def hilbertFunction (F : (Proj 𝒜).Modules) (d : ℤ) : ℕ :=
  letI := globalSectionsModuleZero 𝒜 (_root_.ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
  Module.finrank (𝒜 0) Γ(_root_.ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤)

/-- `F` has **Hilbert polynomial** `P ∈ ℚ[z]` when its Hilbert function agrees with `P` in
all sufficiently large degrees.

For a coherent sheaf on `ℙⁿ` over a field this is the usual Hilbert polynomial: the higher
cohomology of `F(d)` vanishes for `d ≫ 0` (Serre), so `χ(F(d)) = h⁰(F(d))` there, and a
polynomial is determined by its values in large degree. -/
def HasHilbertPolynomial (F : (Proj 𝒜).Modules) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ d : ℕ in atTop, (hilbertFunction 𝒜 F (d : ℤ) : ℚ) = P.eval (d : ℚ)

/-- The Hilbert polynomial is unique when it exists: two polynomials over `ℚ` that agree at
all large natural numbers agree at infinitely many points, hence are equal. -/
theorem HasHilbertPolynomial.unique {F : (Proj 𝒜).Modules} {P Q : Polynomial ℚ}
    (hP : HasHilbertPolynomial 𝒜 F P) (hQ : HasHilbertPolynomial 𝒜 F Q) : P = Q := by
  have hPQ : ∀ᶠ d : ℕ in atTop, P.eval (d : ℚ) = Q.eval (d : ℚ) := by
    filter_upwards [hP, hQ] with d hd hd' using hd ▸ hd'
  obtain ⟨N, hN⟩ := eventually_atTop.mp hPQ
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := (fun d : ℕ ↦ (d : ℚ)) '' {d | N ≤ d})
  · rintro _ ⟨d, hd, rfl⟩
    exact hN d hd
  · refine Set.Infinite.image ?_ (Set.Ici_infinite N)
    exact Set.injOn_of_injective (fun _ _ h ↦ by exact_mod_cast h)

end AlgebraicGeometry.ProjectiveSpectrum.Proj
