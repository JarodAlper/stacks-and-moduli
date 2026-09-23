module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import StacksAndModuli.API.KernelBaseChange
public import StacksProject.Algebra.LociMaps.«lemma-cokernel-flat»
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksAndModuli.API.FibreComplexSemicontinuity
public import StacksAndModuli.API.FibreCohomology
public import StacksAndModuli.API.SemicontinuityTransport
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksAndModuli.API.SchemeModulesTensor

/-!
# Cohomology and base change: linear algebra

This module begins the formalization of §A.6 (Cohomology and Base Change) of Appendix A
of *Stacks and Moduli*. The section carries no
`sec:` label in the LaTeX source. Per-label completeness for this folder is tracked in
`STATUS.md`.

This part covers the two results of the subsection *Formulations of Cohomology and Base
Change* whose content is linear algebra: the Semicontinuity Theorem **A.6.4**
(`thm:semicontinuity`) and **Proposition A.6.6** (`prop:linear-algebra`).

Theorem A.6.4 states that for a proper morphism `X → Y` of noetherian schemes and a
coherent sheaf `F` on `X` flat over `Y`, the fibrewise cohomology dimensions
`y ↦ hⁱ(X_y, F_y)` are upper semicontinuous and their alternating sum
`y ↦ χ(X_y, F_y)` is locally constant.  Both parts are stated and proved here
(`Scheme.Hom.upperSemicontinuous_fibreH`, `Scheme.Hom.isLocallyConstant_fibreEulerChar`)
from a single recorded obligation,
`Scheme.Hom.exists_fibreCohomologyLocallyComputedByComplex`, which is Theorem A.6.2
(Cohomology and Base Change I, Stacks tag `07VK`) in the form the proof consumes.  The
linear algebra lives in `StacksAndModuli/API/FibreComplexSemicontinuity.lean`, the vocabulary
(`hⁱ(X_y, F_y)`, coherence, relative flatness) in `StacksAndModuli/API/FibreCohomology.lean`, and
the affine-to-global passage in `StacksAndModuli/API/SemicontinuityTransport.lean`; see this
folder's COMMENTARY.md.

The second subject is **Proposition A.6.6** (`prop:linear-algebra`): for a map
`φ : E → F` of vector bundles of ranks `e` and `f` on a scheme, a point `x`, and an
integer `r ≤ min(e, f)`, the following are equivalent — (1) `coker φ` is a vector
bundle of rank `f - r` near `x`; (2) local trivializations near `x` put `φ` in the
standard block form `O^e ↠ O^r ↪ O^f` onto the first `r` summands; (3) the canonical
map `ker(φ) ⊗ κ(x) → ker(φ ⊗ κ(x))` is surjective — plus, over a reduced base, a
fourth fiber-rank condition, and the assertion that when these hold the kernel, image,
and cokernel are vector bundles whose formation commutes with base change.

The formalization is affine-local: `φ` becomes a map `f : M → N` of finite projective
modules over a commutative ring, condition (2) becomes the basis-free existence of a
generalized inverse `g` with `f ∘ g ∘ f = f`, and open neighborhoods become basic
opens `D(a)` (see this folder's COMMENTARY.md for this rendering decision). The
kernel/base-change comparison machinery is imported from
`StacksAndModuli.API.KernelBaseChange`, and the open-locus core is Stacks Project tag 00O0,
formalized in `StacksProject.Algebra.LociMaps.«lemma-cokernel-flat»`.

## Canonical declarations for Proposition A.6.6

- `LinearMap.kernelCommutesWithResidueFieldAt_iff_exists_scaled_innerInverse`:
  conditions (2) ⟺ (3) at a point, in the denominator-cleared neighborhood form.
- `LinearMap.tfae_projective_coker_innerInverse_kernelResidueField`: conditions
  (1) ⟺ (2) ⟺ (3) over a local ring.
- `LinearMap.projective_ker_range_coker_baseChange_of_innerInverse`: the closing
  assertion — kernel, image, and cokernel are projective and stay so after every base
  change, and the kernel comparison is bijective for every base change.
- `LinearMap.kernelCommutesWithResidueFieldAt_of_isReduced_of_constant_finrank`:
  condition (4), the reduced constant-fiber-rank criterion (statement recorded, proof
  an outstanding obligation).

Supporting declarations include the one-way implications in local-ring, point-local,
and basic-open forms (`exists_innerInverse_of_kernelCommutesWithLocalResidueField`,
`KernelCommutesWithResidueFieldAt.exists_basicOpen_innerInverse`, …), the split-form
projectivity lemmas (`projective_coker_of_innerInverse`,
`projective_ker_of_innerInverse`, `projective_range_of_innerInverse`,
`exists_innerInverse_of_projective_coker`), and the full-rank case of condition (1)
(`exists_basicOpen_projective_cokernel_of_injective_baseChange_residueField`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

section ThmCbcAlgebraic

open Module AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

/-- **Theorem A.6.2** (`thm:cbc-algebraic`) (Cohomology and Base Change I): for a proper
morphism `X → Spec A` of noetherian schemes and a coherent sheaf `F` on `X` flat over `A`,
there is a bounded complex

`K^• : 0 → K⁰ → K¹ → ⋯ → Kⁿ → 0`

of finite locally free `A`-modules with `Hⁱ(X, F) = Hⁱ(K^•)`, and moreover
`Hⁱ(X, F ⊗_A M) = Hⁱ(K^• ⊗_A M)` for every `A`-module `M`.

"Finite and locally free" over a commutative ring is finite projective, recorded as
`Module.FinitePresentation` together with `Module.Projective`.  The book's equalities of
cohomology are rendered as `A`-linear isomorphisms; `Hⁱ(X, F)` is
`AlgebraicGeometry.Scheme.Modules.H`, an `A`-module through the structure morphism, and
`F ⊗_A M` is `F ⊗ p^* M~` for `p : X → Spec A`.  A complex indexed by all of `ℕ` with
`dⁿ = 0` is the same data as a complex vanishing above `n`, so no separate truncation
clause is needed.

Taking `M = A` recovers the first equality from the second, but both are stated, as in the
book.  The specialization to `M = B` for a ring map `A → B` — the "in particular" clause,
which is what the Semicontinuity Theorem consumes — is
`Scheme.Hom.exists_fibreCohomologyLocallyComputedByComplex` below, recorded separately
because passing from `Hⁱ(X, F ⊗_A κ(y))` to `Hⁱ(X_y, F_y)` needs the affine base-change
comparison for cohomology, which is not available here.

The proof (deferred) takes the alternating Čech complex of a finite affine cover, a finite
complex of flat but not finitely generated `A`-modules computing `Hⁱ(X, F)`, and refines it
inductively to a bounded complex of finite flat modules quasi-isomorphic to it
(Stacks tag `07VK`; Mumford, *Abelian Varieties*, p. 46). -/
theorem AlgebraicGeometry.Scheme.exists_boundedComplex_computing_cohomology
    {A : Type u} [CommRing A] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))]
    [IsProper (X ↘ Spec (CommRingCat.of A))] [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (hflat : (X ↘ Spec (CommRingCat.of A)).ModulesFlat F) :
    ∃ (n : ℕ) (K : ℕ → ModuleCat.{u} A)
      (d : ∀ i, (K i : Type u) →ₗ[A] (K (i + 1) : Type u)),
      (∀ i, Module.FinitePresentation A (K i)) ∧ (∀ i, Module.Projective A (K i)) ∧
      (∀ j, d (j + 1) ∘ₗ d j = 0) ∧ d n = 0 ∧
      (Nonempty (Scheme.Modules.H F 0 ≃ₗ[A] LinearMap.ker (d 0)) ∧
        ∀ i : ℕ, Nonempty (Scheme.Modules.H F (i + 1) ≃ₗ[A]
          BoundedComplex.cohomology d i)) ∧
      ∀ M : ModuleCat.{u} A,
        Nonempty (Scheme.Modules.H
            (F ⊗ₘ (Scheme.Modules.pullback (X ↘ Spec (CommRingCat.of A))).obj (tilde M)) 0
          ≃ₗ[A] LinearMap.ker (LinearMap.rTensor M (d 0))) ∧
        ∀ i : ℕ, Nonempty (Scheme.Modules.H
            (F ⊗ₘ (Scheme.Modules.pullback (X ↘ Spec (CommRingCat.of A))).obj (tilde M))
              (i + 1)
          ≃ₗ[A] BoundedComplex.cohomology (fun j ↦ LinearMap.rTensor M (d j)) i) := by
  sorry

end ThmCbcAlgebraic

section ThmSemicontinuity

open Module TensorProduct AlgebraicGeometry AlgebraicGeometry.FibrewiseRank

universe u

/-- API theorem for Theorem A.6.4 (the complete reduction of the Semicontinuity Theorem to
Theorem A.6.2, over an affine base): suppose the fibrewise cohomology dimensions
`hⁱ(y)` of a family over `Spec A` are computed by a bounded complex

`K⁰ →[d 0] K¹ → ⋯ → Kⁿ → 0`

of finite projective `A`-modules, in the sense that `h⁰(y) = dim ker(d⁰ ⊗ κ(y))` and
`hⁱ⁺¹(y) = dim Hⁱ⁺¹(K^• ⊗ κ(y))`.  Then every `hⁱ` is upper semicontinuous and the
alternating sum `∑ (-1)ⁱ hⁱ` is locally constant.

This is exactly what the book's proof of the Semicontinuity Theorem establishes once
Theorem A.6.2 has produced the complex: the hypotheses `h0` and `hsucc` are the conclusion
`Hⁱ(X_y, F_y) = Hⁱ(K^• ⊗_A κ(y))` of Theorem A.6.2, and the two conclusions are the two
parts of the theorem.  Nothing of the book's proof is missing.

This affine form is the core of
`semicontinuity_of_fibreCohomologyLocallyComputedByComplex` below, which adds the passage
to an arbitrary noetherian base; the only remaining gap is Theorem A.6.2 itself, in its
"in particular" form at `B = κ(y)`. -/
theorem semicontinuity_of_cohomologyComputedByComplex
    {A : Type u} [CommRing A] (n : ℕ) (h : ℕ → PrimeSpectrum A → ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
    [∀ i, Module.FinitePresentation A (K i)] [∀ i, Module.Projective A (K i)]
    (d : ∀ i, K i →ₗ[A] K (i + 1))
    (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (hn : d n = 0)
    (h0 : ∀ y : PrimeSpectrum A,
      h 0 y = finrank y.residueField (LinearMap.ker (fibreDiff K d y 0)))
    (hsucc : ∀ (i : ℕ) (y : PrimeSpectrum A),
      h (i + 1) y =
        finrank y.residueField (BoundedComplex.cohomology (fibreDiff K d y) i)) :
    (∀ i, UpperSemicontinuous fun y : PrimeSpectrum A ↦ (h i y : ℤ)) ∧
      IsLocallyConstant fun y : PrimeSpectrum A ↦
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * h i y := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · cases i with
    | zero =>
      simpa only [h0] using
        upperSemicontinuous_finrank_ker_fibreDiff (K := K) (d := d) 0
    | succ i =>
      simpa only [hsucc] using
        upperSemicontinuous_finrank_cohomology_fibre (K := K) (d := d) hd i
  · have key : ∀ y : PrimeSpectrum A,
        (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * h i y) =
          (finrank y.residueField (LinearMap.ker (fibreDiff K d y 0)) : ℤ) +
            ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) *
              finrank y.residueField (BoundedComplex.cohomology (fibreDiff K d y) i) := by
      intro y
      rw [Finset.sum_range_succ' (fun i ↦ (-1 : ℤ) ^ i * (h i y : ℤ)) n, add_comm]
      simp only [h0, hsucc, pow_zero, one_mul]
    simp only [key]
    exact isLocallyConstant_eulerChar_fibre (K := K) (d := d) n hd hn

/-- Background definition for Theorem A.6.4 (the conclusion of Theorem A.6.2 in the form
the Semicontinuity Theorem consumes): the fibrewise cohomology of `F` along `f` is
*locally computed by a bounded complex of length `n`* if every point of the base has an
affine open neighbourhood `V` carrying a complex

`K⁰ → K¹ → ⋯ → Kⁿ → 0`

of finite projective `Γ(Y, V)`-modules whose fibre at the prime of `y` computes
`hⁱ(X_y, F_y)` for every `y ∈ V`.

Theorem A.6.2 (Cohomology and Base Change I) supplies exactly this: over an affine base it
produces the complex, and its "in particular" clause at `B = κ(y)` is the identification of
the fibrewise cohomology.  The `y` occurring here is a point of `Y` itself, not of a
restriction of `f`, so no comparison between `(f ∣_ V).fiber y` and `f.fiber y` is
involved. -/
def AlgebraicGeometry.Scheme.Hom.FibreCohomologyLocallyComputedByComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ) : Prop :=
  ∀ y₀ : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V) (_ : y₀ ∈ V)
      (K : ℕ → ModuleCat.{u} Γ(Y, V))
      (d : ∀ i, (K i : Type u) →ₗ[Γ(Y, V)] (K (i + 1) : Type u)),
      (∀ i, Module.FinitePresentation Γ(Y, V) (K i)) ∧
      (∀ i, Module.Projective Γ(Y, V) (K i)) ∧
      (∀ j, d (j + 1) ∘ₗ d j = 0) ∧ d n = 0 ∧
      (∀ y : V, f.fibreH F y.1 0 =
        finrank (hV.primeIdealOf y).residueField
          (LinearMap.ker (fibreDiff (fun i ↦ (K i : Type u)) d (hV.primeIdealOf y) 0))) ∧
      (∀ (i : ℕ) (y : V), f.fibreH F y.1 (i + 1) =
        finrank (hV.primeIdealOf y).residueField
          (BoundedComplex.cohomology
            (fibreDiff (fun i ↦ (K i : Type u)) d (hV.primeIdealOf y)) i))

/-- Deferred obligation for Theorem A.6.4, supplied by **Theorem A.6.2** (Cohomology and
Base Change I, Stacks tag `07VK`): for a proper morphism of noetherian schemes and a
coherent sheaf flat over the base, the fibrewise cohomology is locally computed by a
bounded complex of finite projective modules, and vanishes above the length of that
complex.

This is the *only* input the Semicontinuity Theorem needs beyond linear algebra: the book's
proof reduces to `Y = Spec A`, applies A.6.2 to obtain the complex `K^•`, and then argues
entirely with Equation A.6.5.  Both of those steps are carried out below without any further
assumption.  A.6.2 itself — the inductive refinement of the Čech complex of a finite affine
cover to a bounded complex of finite flat modules — is not formalized. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_fibreCohomologyLocallyComputedByComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (F : X.Modules) [Scheme.Modules.IsCoherent F] (hflat : f.ModulesFlat F) :
    ∃ n : ℕ, (∀ (y : Y) (i : ℕ), n < i → f.fibreH F y i = 0) ∧
      f.FibreCohomologyLocallyComputedByComplex F n := by
  sorry

/-- API theorem for Theorem A.6.4 (the geometric half of the reduction): both conclusions of
the Semicontinuity Theorem hold as soon as the fibrewise cohomology is locally computed by a
bounded complex of finite projective modules.

The proof is the passage from the affine case to an arbitrary base.  Upper semicontinuity
and local constancy are conditions at each point, so they may be checked on the affine
neighbourhood supplied by the hypothesis
(`upperSemicontinuous_of_forall_exists_isOpen`, `isLocallyConstant_of_forall_exists_isOpen`);
on that neighbourhood the statement is transported from `Spec Γ(Y, V)` along the continuous
map `y ↦ 𝔭_y` underlying `IsAffineOpen.isoSpec`, where it is the algebraic semicontinuity
already proved in `StacksAndModuli/API/FibreComplexSemicontinuity.lean`. -/
theorem semicontinuity_of_fibreCohomologyLocallyComputedByComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ)
    (H : f.FibreCohomologyLocallyComputedByComplex F n) :
    (∀ i, UpperSemicontinuous fun y : Y ↦ (f.fibreH F y i : ℤ)) ∧
      IsLocallyConstant (f.fibreEulerChar F n) := by
  constructor
  · intro i
    refine upperSemicontinuous_of_forall_exists_isOpen fun y₀ ↦ ?_
    obtain ⟨V, hV, hy₀, K, d, hfp, hproj, hd, hzero, h0, hsucc⟩ := H y₀
    refine ⟨(V : Set Y), V.2, hy₀, ?_⟩
    have : ∀ i, Module.FinitePresentation Γ(Y, V) (K i) := hfp
    have : ∀ i, Module.Projective Γ(Y, V) (K i) := hproj
    have hcont : Continuous (fun v : V ↦ hV.primeIdealOf v) := by
      show Continuous (fun v : V ↦ hV.isoSpec.hom.base v)
      exact hV.isoSpec.hom.base.hom.continuous
    cases i with
    | zero =>
      have hus := (upperSemicontinuous_finrank_ker_fibreDiff
        (K := fun i ↦ (K i : Type u)) (d := d) 0).comp hcont
      have heq : (fun v : (V : Set Y) ↦ (f.fibreH F v.1 0 : ℤ)) =
          (fun p : PrimeSpectrum Γ(Y, V) ↦
            (finrank p.residueField
              (LinearMap.ker (fibreDiff (fun i ↦ (K i : Type u)) d p 0)) : ℤ)) ∘
            (fun v : V ↦ hV.primeIdealOf v) := by
        funext v
        simpa using congrArg (Nat.cast (R := ℤ)) (h0 v)
      rw [heq]
      exact hus
    | succ i =>
      have hus := (upperSemicontinuous_finrank_cohomology_fibre
        (K := fun i ↦ (K i : Type u)) (d := d) hd i).comp hcont
      have heq : (fun v : (V : Set Y) ↦ (f.fibreH F v.1 (i + 1) : ℤ)) =
          (fun p : PrimeSpectrum Γ(Y, V) ↦
            (finrank p.residueField
              (BoundedComplex.cohomology
                (fibreDiff (fun i ↦ (K i : Type u)) d p) i) : ℤ)) ∘
            (fun v : V ↦ hV.primeIdealOf v) := by
        funext v
        simpa using congrArg (Nat.cast (R := ℤ)) (hsucc i v)
      rw [heq]
      exact hus
  · refine isLocallyConstant_of_forall_exists_isOpen fun y₀ ↦ ?_
    obtain ⟨V, hV, hy₀, K, d, hfp, hproj, hd, hzero, h0, hsucc⟩ := H y₀
    refine ⟨(V : Set Y), V.2, hy₀, ?_⟩
    have : ∀ i, Module.FinitePresentation Γ(Y, V) (K i) := hfp
    have : ∀ i, Module.Projective Γ(Y, V) (K i) := hproj
    have hcont : Continuous (fun v : V ↦ hV.primeIdealOf v) := by
      show Continuous (fun v : V ↦ hV.isoSpec.hom.base v)
      exact hV.isoSpec.hom.base.hom.continuous
    have hlc := (isLocallyConstant_eulerChar_fibre
      (K := fun i ↦ (K i : Type u)) (d := d) n hd hzero).comp_continuous hcont
    have heq : (fun v : (V : Set Y) ↦ f.fibreEulerChar F n v.1) =
        (fun p : PrimeSpectrum Γ(Y, V) ↦
          (finrank p.residueField
            (LinearMap.ker (fibreDiff (fun i ↦ (K i : Type u)) d p 0)) : ℤ) +
            ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) *
              finrank p.residueField
                (BoundedComplex.cohomology
                  (fibreDiff (fun i ↦ (K i : Type u)) d p) i)) ∘
          (fun v : V ↦ hV.primeIdealOf v) := by
      funext v
      show f.fibreEulerChar F n v.1 = _
      rw [Scheme.Hom.fibreEulerChar,
        Finset.sum_range_succ' (fun i ↦ (-1 : ℤ) ^ i * (f.fibreH F v.1 i : ℤ)) n, add_comm]
      simp only [h0 v, hsucc _ v, pow_zero, one_mul]
      rfl
    rw [heq]
    exact hlc

/-- **Theorem A.6.4** (`thm:semicontinuity`) (Semicontinuity Theorem, part (1)): for a
proper morphism `f : X ⟶ Y` of noetherian schemes and a coherent sheaf `F` on `X` flat over
`Y`, each function `y ↦ hⁱ(X_y, F_y)` is upper semicontinuous on `Y`.

Here `X_y` is the scheme-theoretic fibre and `hⁱ(X_y, F_y)` is the dimension over `κ(y)` of
the `i`-th cohomology of the restriction of `F` to it (`AlgebraicGeometry.Scheme.Hom.fibreH`).

The proof is the book's, with Theorem A.6.2 as its single recorded obligation
(`exists_fibreCohomologyLocallyComputedByComplex`): the complex it supplies converts the
statement into the algebraic semicontinuity of Equation A.6.5, which is proved outright. -/
theorem AlgebraicGeometry.Scheme.Hom.upperSemicontinuous_fibreH
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (F : X.Modules) [Scheme.Modules.IsCoherent F] (hflat : f.ModulesFlat F) (i : ℕ) :
    UpperSemicontinuous fun y : Y ↦ (f.fibreH F y i : ℤ) := by
  obtain ⟨n, -, hn⟩ := f.exists_fibreCohomologyLocallyComputedByComplex F hflat
  exact (semicontinuity_of_fibreCohomologyLocallyComputedByComplex f F n hn).1 i

/-- **Theorem A.6.4** (`thm:semicontinuity`) (Semicontinuity Theorem, part (2)): for a
proper morphism `f : X ⟶ Y` of noetherian schemes and a coherent sheaf `F` on `X` flat over
`Y`, the Euler characteristic `y ↦ χ(X_y, F_y) = ∑ (-1)ⁱ hⁱ(X_y, F_y)` is locally constant
on `Y`.

The book writes the alternating sum as an infinite one; it is recorded here as a sum over
`Finset.range (n + 1)` together with the assertion that `hⁱ(X_y, F_y) = 0` for `i > n`, so
the truncation is the whole sum.  The bound `n` comes from the same obligation as the
complex. -/
theorem AlgebraicGeometry.Scheme.Hom.isLocallyConstant_fibreEulerChar
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (F : X.Modules) [Scheme.Modules.IsCoherent F] (hflat : f.ModulesFlat F) :
    ∃ n : ℕ, (∀ (y : Y) (i : ℕ), n < i → f.fibreH F y i = 0) ∧
      IsLocallyConstant (f.fibreEulerChar F n) := by
  obtain ⟨n, hvanish, hn⟩ := f.exists_fibreCohomologyLocallyComputedByComplex F hflat
  exact ⟨n, hvanish, (semicontinuity_of_fibreCohomologyLocallyComputedByComplex f F n hn).2⟩

/-- API corollary of Theorem A.6.4 (part (1) in the form it is applied): for a proper
morphism of noetherian schemes and a coherent sheaf flat over the base, the locus where the
`i`-th fibrewise cohomology has dimension at least `c` is closed.

This is what makes a condition such as "`h⁰(X_y, L_y) > 0`" cut out a closed subset of the
base, which is how the Semicontinuity Theorem enters §A.6's study of line bundles and the
construction of the tricanonical locus in the Hilbert scheme. -/
theorem AlgebraicGeometry.Scheme.Hom.isClosed_setOf_le_fibreH
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (F : X.Modules) [Scheme.Modules.IsCoherent F] (hflat : f.ModulesFlat F) (i c : ℕ) :
    IsClosed {y : Y | c ≤ f.fibreH F y i} := by
  have h := (f.upperSemicontinuous_fibreH F hflat i).isClosed_setOf_le c
  have hset : {y : Y | c ≤ f.fibreH F y i} =
      {y : Y | (c : ℤ) ≤ (f.fibreH F y i : ℤ)} := by
    ext y
    exact (Int.ofNat_le (m := c) (n := f.fibreH F y i)).symm
  rw [hset]
  exact h

/-- API corollary of Theorem A.6.4 (part (1) in its open form): for a proper morphism of
noetherian schemes and a coherent sheaf flat over the base, the locus where the `i`-th
fibrewise cohomology has dimension at most `c` is open.

With `c = 0` this is the openness of the vanishing locus `{y | hⁱ(X_y, F_y) = 0}`, which is
the form in which the theorem enters Exercise A.6.9 and the construction of the tricanonical
locus in the Hilbert scheme. -/
theorem AlgebraicGeometry.Scheme.Hom.isOpen_setOf_fibreH_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y]
    (F : X.Modules) [Scheme.Modules.IsCoherent F] (hflat : f.ModulesFlat F) (i c : ℕ) :
    IsOpen {y : Y | f.fibreH F y i ≤ c} := by
  have h := (f.upperSemicontinuous_fibreH F hflat i).isOpen_setOf_lt (c + 1)
  have hset : {y : Y | f.fibreH F y i ≤ c} =
      {y : Y | (f.fibreH F y i : ℤ) < (c : ℤ) + 1} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hset]
  exact h

end ThmSemicontinuity

section PropLinearAlgebra

open PrimeSpectrum
open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- The local ring of `R` at a point of its prime spectrum. -/
abbrev PrimeSpectrum.localizationRing (p : PrimeSpectrum R) :=
  Localization.AtPrime p.asIdeal

/-- Scalar extension of a module to the local ring at a point. -/
abbrev PrimeSpectrum.localizedTensor (p : PrimeSpectrum R) (L : Type*)
    [AddCommGroup L] [Module R L] := TensorProduct R p.localizationRing L

/-- Background definition for Proposition A.6.6 (the implicit definition of condition
(3)): the kernel of a linear map `f` commutes surjectively with passage to the residue
field at `p`, i.e. the canonical map `κ(p) ⊗ ker(f) → ker(κ(p) ⊗ f)` is surjective. For
a map between vector bundles this is the fiberwise condition equivalent to the local
constant-rank normal form. The book states the condition at the given point `x`; here
the prime `p` is arbitrary. -/
def LinearMap.KernelCommutesWithResidueFieldAt (f : M →ₗ[R] N)
    (p : PrimeSpectrum R) : Prop :=
  Function.Surjective (f.kerBaseChangeHom (S := p.residueField))

/-- The fiberwise kernel condition holds exactly when the canonical kernel base-change
comparison to the residue field is surjective. -/
lemma LinearMap.kernelCommutesWithResidueFieldAt_iff (f : M →ₗ[R] N)
    (p : PrimeSpectrum R) :
    f.KernelCommutesWithResidueFieldAt p ↔
      Function.Surjective (f.kerBaseChangeHom (S := p.residueField)) :=
  Iff.rfl

/-- Partial result toward Proposition A.6.6 ((2) implies (3)): a map admitting a
generalized inverse (`f ∘ g ∘ f = f`) satisfies the fiberwise kernel condition at
every prime. The standard block matrix in condition (2) admits such an inverse by
including and projecting its first `r` summands, so this is the basis-free algebraic
content of the implication. -/
lemma LinearMap.KernelCommutesWithResidueFieldAt.of_innerInverse
    {f : M →ₗ[R] N} (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f)
    (p : PrimeSpectrum R) : f.KernelCommutesWithResidueFieldAt p :=
  (f.kerBaseChangeHom_bijective_of_innerInverse (S := p.residueField) g h).surjective

/-- Partial result toward Proposition A.6.6 ((3) implies (2), local-ring form):
over a local ring, surjectivity of the canonical kernel comparison after passage to
the residue field implies the basis-free split constant-rank normal form. -/
theorem LinearMap.exists_innerInverse_of_kernelCommutesWithLocalResidueField
    [IsLocalRing R] [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (hker : Function.Surjective
      (f.kerBaseChangeHom (S := IsLocalRing.ResidueField R))) :
    ∃ g : N →ₗ[R] M, f.comp (g.comp f) = f :=
  f.exists_innerInverse_of_kerBaseChangeHom_residueField_surjective hker

/-- Partial result toward Proposition A.6.6 ((3) implies (2), localization at a
point): let `f` be a map of finite projective modules and localize it at a prime `p`.
If the kernel of this localized map commutes surjectively with passage to the residue
field of `Rₚ`, then the localized map admits a generalized inverse. Spreading the
finitely many coefficients of the inverse then gives the neighborhood form. -/
theorem LinearMap.exists_innerInverse_localizationAtPrime_of_kernel_surjective
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (p : PrimeSpectrum R)
    (hker : Function.Surjective
      ((f.baseChange p.localizationRing).kerBaseChangeHom
        (S := p.residueField))) :
    ∃ g : p.localizedTensor N →ₗ[p.localizationRing] p.localizedTensor M,
      (f.baseChange p.localizationRing).comp
          (g.comp (f.baseChange p.localizationRing)) =
        f.baseChange p.localizationRing := by
  letI : Module.Finite p.localizationRing
      (p.localizedTensor M) := inferInstance
  letI : Module.Finite p.localizationRing
      (p.localizedTensor N) := inferInstance
  letI : Module.Projective p.localizationRing
      (p.localizedTensor N) := inferInstance
  letI : Module.Free p.localizationRing
      (p.localizedTensor N) := Module.free_of_flat_of_isLocalRing
  exact LinearMap.exists_innerInverse_of_kerBaseChangeHom_residueField_surjective
    (f.baseChange p.localizationRing) hker

/-- Partial result toward Proposition A.6.6 ((3) implies (2), point-local form):
the fiberwise kernel condition for the original `R`-linear map at `p` produces a
generalized inverse after localization at `p`. The tower comparison for kernels
supplies the bridge from `κ(p) ⊗[R] f` to the residue-field base change of
`Rₚ ⊗[R] f`. -/
theorem LinearMap.KernelCommutesWithResidueFieldAt.exists_innerInverse_localizationAtPrime
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {f : M →ₗ[R] N} {p : PrimeSpectrum R}
    (hker : f.KernelCommutesWithResidueFieldAt p) :
    ∃ g : p.localizedTensor N →ₗ[p.localizationRing] p.localizedTensor M,
      (f.baseChange p.localizationRing).comp
          (g.comp (f.baseChange p.localizationRing)) =
        f.baseChange p.localizationRing := by
  apply f.exists_innerInverse_localizationAtPrime_of_kernel_surjective p
  exact f.kerBaseChangeHom_surjective_of_tower_of_flat
    (S := p.localizationRing) (T := p.residueField) hker

/-- Partial result toward Proposition A.6.6 ((3) implies (2), spreading to a
neighborhood): the fiberwise kernel condition spreads algebraically to a basic
neighborhood — there is an element `a ∉ p` and a map `h` such that `f h f = a f`.
Since `a` is invertible on `D(a)`, the localized map there has the generalized inverse
`a⁻¹h`. This is the denominator-cleared form of condition (2) on an open
neighborhood. -/
theorem LinearMap.KernelCommutesWithResidueFieldAt.exists_scaled_innerInverse
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {f : M →ₗ[R] N} {p : PrimeSpectrum R}
    (hker : f.KernelCommutesWithResidueFieldAt p) :
    ∃ (a : R) (_ : a ∉ p.asIdeal) (h : N →ₗ[R] M),
      f.comp (h.comp f) = a • f := by
  obtain ⟨g, hg⟩ := hker.exists_innerInverse_localizationAtPrime
  exact LinearMap.exists_scaled_innerInverse_of_innerInverse_baseChange_atPrime f p g hg

/-- Partial result toward Proposition A.6.6 ((3) implies (2), basic-open
neighborhood form): the fiberwise kernel condition gives an honest generalized inverse
on a basic open neighborhood of the point. Thus the map has the split constant-rank
normal form after restriction to `D(a)`. -/
theorem LinearMap.KernelCommutesWithResidueFieldAt.exists_basicOpen_innerInverse
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {f : M →ₗ[R] N} {p : PrimeSpectrum R}
    (hker : f.KernelCommutesWithResidueFieldAt p) :
    ∃ (a : R) (_ : a ∉ p.asIdeal),
      ∃ g : LinearMap (RingHom.id (Localization.Away a))
          (TensorProduct R (Localization.Away a) N)
          (TensorProduct R (Localization.Away a) M),
        f.baseChange (Localization.Away a) ∘ₗ
            (g ∘ₗ f.baseChange (Localization.Away a)) =
          f.baseChange (Localization.Away a) := by
  obtain ⟨a, ha, h, hh⟩ := hker.exists_scaled_innerInverse
  exact ⟨a, ha, f.exists_innerInverse_baseChange_away_of_scaled_innerInverse a h hh⟩

/-- Partial result toward Proposition A.6.6 (full-rank case of condition (1)):
let `f : M → N` be a map of finite projective modules over a ring `R`. If the map on
the fiber at a prime `p` is injective — the full-rank case `r = rank(M)`, in which
condition (3) holds automatically — then there is a basic open neighborhood `D(a)` of
`p` on which the cokernel of `f` is projective. -/
theorem LinearMap.exists_basicOpen_projective_cokernel_of_injective_baseChange_residueField
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (p : PrimeSpectrum R)
    (hp : Function.Injective (LinearMap.lTensor p.residueField f)) :
    ∃ a : R, a ∉ p.asIdeal ∧
      Module.Projective (Localization.Away a)
        (LocalizedModule.Away a (N ⧸ LinearMap.range f)) := by
  have hp' : p ∈ f.tensorInjectiveLocus := hp
  obtain ⟨U, ⟨a, rfl⟩, hpU, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp'
      (LinearMap.isOpen_tensorInjectiveLocus f)
  refine ⟨a, PrimeSpectrum.mem_basicOpen a p |>.mp hpU, ?_⟩
  exact LinearMap.projective_coker_of_mem_tensorInjectiveLocus f a hU

/-! ### The split normal form: kernel, image, and cokernel -/

/-- Partial result toward Proposition A.6.6 ((2) implies (1)): a map admitting a
generalized inverse (`f ∘ g ∘ f = f`) into a projective module has projective
cokernel — the quotient projection is split by the map induced by `1 - f ∘ g`. -/
theorem LinearMap.projective_coker_of_innerInverse [Module.Projective R N]
    {f : M →ₗ[R] N} (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f) :
    Module.Projective R (N ⧸ LinearMap.range f) := by
  have hrange : LinearMap.range f ≤
      LinearMap.ker ((LinearMap.id : N →ₗ[R] N) - f ∘ₗ g) := by
    rintro _ ⟨x, rfl⟩
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hx, sub_self]
  refine Module.Projective.of_split
    ((LinearMap.range f).liftQ _ hrange) (LinearMap.range f).mkQ ?_
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    change (LinearMap.range f).mkQ (((LinearMap.id : N →ₗ[R] N) - f ∘ₗ g) y) =
      Submodule.Quotient.mk y
    have hzero : (LinearMap.range f).mkQ (f (g y)) = 0 := by
      simp [Submodule.Quotient.mk_eq_zero]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hzero, sub_zero]
    rfl

/-- Partial result toward Proposition A.6.6 (the closing assertion, kernel): a map
of projective modules admitting a generalized inverse has projective kernel — the
kernel is split off `M` by `1 - g ∘ f`. -/
theorem LinearMap.projective_ker_of_innerInverse [Module.Projective R M]
    {f : M →ₗ[R] N} (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f) :
    Module.Projective R (LinearMap.ker f) := by
  have hker : ∀ x : M, f (((LinearMap.id : M →ₗ[R] M) - g ∘ₗ f) x) = 0 := by
    intro x
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hx, sub_self]
  refine Module.Projective.of_split (LinearMap.ker f).subtype
    (LinearMap.codRestrict _ ((LinearMap.id : M →ₗ[R] M) - g ∘ₗ f)
      fun x ↦ LinearMap.mem_ker.mpr (hker x)) ?_
  ext x
  change ((LinearMap.id : M →ₗ[R] M) - g ∘ₗ f) x.1 = x.1
  simp [LinearMap.mem_ker.mp x.2]

/-- Partial result toward Proposition A.6.6 (the closing assertion, image): a map
into a projective module admitting a generalized inverse has projective image — the
image is split off `N` by `f ∘ g`. -/
theorem LinearMap.projective_range_of_innerInverse [Module.Projective R N]
    {f : M →ₗ[R] N} (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f) :
    Module.Projective R (LinearMap.range f) := by
  refine Module.Projective.of_split (LinearMap.range f).subtype
    (LinearMap.codRestrict _ (f ∘ₗ g) fun y ↦ ⟨g y, rfl⟩) ?_
  ext y
  obtain ⟨x, hx⟩ := y.2
  change f (g y.1) = y.1
  rw [← hx]
  exact LinearMap.congr_fun h x

/-- Partial result toward Proposition A.6.6 ((1) implies (2)): if the cokernel of a
map into a projective module is projective, the map admits a generalized inverse:
the quotient projection splits, `1` minus the splitting retracts `N` onto the image,
and the retraction lifts through `M` by projectivity of `N`. -/
theorem LinearMap.exists_innerInverse_of_projective_coker [Module.Projective R N]
    (f : M →ₗ[R] N) (hcoker : Module.Projective R (N ⧸ LinearMap.range f)) :
    ∃ g : N →ₗ[R] M, f.comp (g.comp f) = f := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ
    LinearMap.id (Submodule.mkQ_surjective _)
  have hτ : ∀ y : N,
      ((LinearMap.id : N →ₗ[R] N) - σ ∘ₗ (LinearMap.range f).mkQ) y ∈
        LinearMap.range f := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero (LinearMap.range f)]
    have hσy := LinearMap.congr_fun hσ ((LinearMap.range f).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hσy
    change (LinearMap.range f).mkQ
      (((LinearMap.id : N →ₗ[R] N) - σ ∘ₗ (LinearMap.range f).mkQ) y) = 0
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub]
    rw [show (LinearMap.range f).mkQ (σ ((LinearMap.range f).mkQ y)) =
      (LinearMap.range f).mkQ y from hσy, sub_self]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hτ) f.surjective_rangeRestrict
  refine ⟨g, ?_⟩
  ext x
  have hgx := congrArg Subtype.val (LinearMap.congr_fun hg (f x))
  have hmk : (LinearMap.range f).mkQ (f x) = 0 := by
    simp [Submodule.Quotient.mk_eq_zero]
  change f (g (f x)) = f x
  calc f (g (f x)) =
      (((LinearMap.id : N →ₗ[R] N) - σ ∘ₗ (LinearMap.range f).mkQ) (f x)) := hgx
    _ = f x := by
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          hmk, map_zero, sub_zero]

/-- Partial result toward Proposition A.6.6 ((2) implies (3), denominator-cleared
form): a scaled generalized inverse `f ∘ h ∘ f = a • f` with `a ∉ p` forces the
fiberwise kernel condition at `p`. The `R`-linear map `a • 1 - h ∘ f` lands in
`ker f` and, over the residue field where `a` is invertible, retracts onto the
kernel of the fiber map. -/
theorem LinearMap.kernelCommutesWithResidueFieldAt_of_scaled_innerInverse
    {f : M →ₗ[R] N} {p : PrimeSpectrum R} (a : R) (ha : a ∉ p.asIdeal)
    (h : N →ₗ[R] M) (hh : f.comp (h.comp f) = a • f) :
    f.KernelCommutesWithResidueFieldAt p := by
  have hE : ∀ x : M, f ((a • (LinearMap.id : M →ₗ[R] M) - h ∘ₗ f) x) = 0 := by
    intro x
    have hx := LinearMap.congr_fun hh x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_smul, hx, sub_self]
  set E : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict _ (a • (LinearMap.id : M →ₗ[R] M) - h ∘ₗ f)
      (fun x ↦ LinearMap.mem_ker.mpr (hE x)) with hEdef
  have haU : IsUnit (algebraMap R p.residueField a) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact ha (Ideal.algebraMap_residueField_eq_zero.mp h0)
  obtain ⟨u, hu⟩ := haU
  rintro ⟨w, hw⟩
  refine ⟨(↑u⁻¹ : p.residueField) • (E.baseChange p.residueField) w, ?_⟩
  apply Subtype.ext
  change (LinearMap.baseChange p.residueField (LinearMap.ker f).subtype)
    ((↑u⁻¹ : p.residueField) • (E.baseChange p.residueField) w) = w
  rw [map_smul]
  have hcomp : (LinearMap.baseChange p.residueField (LinearMap.ker f).subtype)
      ((E.baseChange p.residueField) w) =
      (LinearMap.baseChange p.residueField
        (a • (LinearMap.id : M →ₗ[R] M) - h ∘ₗ f)) w := by
    have h1 := LinearMap.congr_fun
      (LinearMap.baseChange_comp E (LinearMap.ker f).subtype
        (A := p.residueField)) w
    rw [hEdef, LinearMap.subtype_comp_codRestrict] at h1
    simpa [hEdef] using h1.symm
  rw [hcomp]
  have hfw : (f.baseChange p.residueField) w = 0 := LinearMap.mem_ker.mp hw
  have hval : (LinearMap.baseChange p.residueField
      (a • (LinearMap.id : M →ₗ[R] M) - h ∘ₗ f)) w =
      algebraMap R p.residueField a • w := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_comp,
      LinearMap.baseChange_id]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hfw, map_zero, sub_zero, algebraMap_smul]
  rw [hval, ← hu, smul_smul, Units.inv_mul, one_smul]

/-- **Proposition A.6.6** (`prop:linear-algebra`) (equivalence of conditions (2) and
(3), affine denominator-cleared rendering): for a map `f` of finite projective modules
and a point `p` of the spectrum, the fiberwise kernel condition at `p` — surjectivity
of `κ(p) ⊗ ker f → ker (κ(p) ⊗ f)` — holds if and only if `f` admits a scaled
generalized inverse `f ∘ h ∘ f = a • f` for some `a ∉ p`; inverting `a` gives an
honest generalized inverse, the basis-free split constant-rank normal form of
condition (2), on the basic open neighborhood `D(a)` of `p`. -/
theorem LinearMap.kernelCommutesWithResidueFieldAt_iff_exists_scaled_innerInverse
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (p : PrimeSpectrum R) :
    f.KernelCommutesWithResidueFieldAt p ↔
      ∃ (a : R) (_ : a ∉ p.asIdeal) (h : N →ₗ[R] M),
        f.comp (h.comp f) = a • f :=
  ⟨fun hk ↦ hk.exists_scaled_innerInverse,
    fun ⟨a, ha, h, hh⟩ ↦
      kernelCommutesWithResidueFieldAt_of_scaled_innerInverse a ha h hh⟩

/-- **Proposition A.6.6** (`prop:linear-algebra`) (equivalence of conditions (1), (2),
and (3), local form): over a local ring, for a map `f : M → N` of finite modules with
`N` free, the following are equivalent — the cokernel of `f` is projective (condition
(1)); `f` admits a generalized inverse (the split constant-rank normal form of
condition (2)); and the kernel of `f` commutes surjectively with passage to the
residue field (condition (3)). Together with the spreading results this gives the
neighborhood equivalences of the proposition at any point of the spectrum. -/
theorem LinearMap.tfae_projective_coker_innerInverse_kernelResidueField
    [IsLocalRing R] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N) :
    List.TFAE
      [Module.Projective R (N ⧸ LinearMap.range f),
        ∃ g : N →ₗ[R] M, f.comp (g.comp f) = f,
        Function.Surjective (f.kerBaseChangeHom (IsLocalRing.ResidueField R))] := by
  tfae_have 1 → 2 := fun h ↦ f.exists_innerInverse_of_projective_coker h
  tfae_have 2 → 3 := fun ⟨g, hg⟩ ↦
    (f.kerBaseChangeHom_bijective_of_innerInverse
      (IsLocalRing.ResidueField R) g hg).surjective
  tfae_have 3 → 2 := fun h ↦
    f.exists_innerInverse_of_kerBaseChangeHom_residueField_surjective h
  tfae_have 2 → 1 := fun ⟨g, hg⟩ ↦ LinearMap.projective_coker_of_innerInverse g hg
  tfae_finish

/-- **Proposition A.6.6** (`prop:linear-algebra`) (the closing assertion, split
rendering): when the equivalent conditions hold — witnessed by a generalized inverse
`f ∘ g ∘ f = f` of the map `f` of projective modules — the kernel, image, and
cokernel of `f` are projective, they remain projective after every base change
`R → S` (applied to the base-changed map), and the formation of the kernel commutes
with every base change. The cokernel always commutes with base change by right
exactness of the tensor product, and the image comparisons follow from the
base-changed splitting. -/
theorem LinearMap.projective_ker_range_coker_baseChange_of_innerInverse
    [Module.Projective R M] [Module.Projective R N]
    {f : M →ₗ[R] N} (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f)
    (S : Type*) [CommRing S] [Algebra R S] :
    Module.Projective S (LinearMap.ker (f.baseChange S)) ∧
      Module.Projective S (LinearMap.range (f.baseChange S)) ∧
        Module.Projective S (TensorProduct R S N ⧸ LinearMap.range (f.baseChange S)) ∧
          Function.Bijective (f.kerBaseChangeHom S) := by
  have hS : (f.baseChange S).comp ((g.baseChange S).comp (f.baseChange S)) =
      f.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]
  exact ⟨LinearMap.projective_ker_of_innerInverse (g.baseChange S) hS,
    LinearMap.projective_range_of_innerInverse (g.baseChange S) hS,
    LinearMap.projective_coker_of_innerInverse (g.baseChange S) hS,
    f.kerBaseChangeHom_bijective_of_innerInverse S g h⟩

/-- Partial result toward Proposition A.6.6 (condition (4), the fiberwise image
comparison): at a point where `f ∘ u` is fiberwise injective and the fiber of `f` has rank
`r`, the fiberwise images of `f` and of `f ∘ u` coincide.

Both are subspaces of the same fiber, the second contained in the first, and both have
dimension `r` — the first by hypothesis, the second because a fiberwise injective map out
of `κ(q)^r` has image of dimension `r`. -/
theorem LinearMap.range_baseChange_eq_of_constant_finrank
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) {r : ℕ} {u : (Fin r → R) →ₗ[R] M} {q : PrimeSpectrum R}
    (hq : q ∈ (f ∘ₗ u).tensorInjectiveLocus)
    (hr : Module.finrank q.residueField
      (LinearMap.range (f.baseChange q.residueField)) = r) :
    LinearMap.range ((f ∘ₗ u).baseChange q.residueField) =
      LinearMap.range (f.baseChange q.residueField) := by
  have hle : LinearMap.range ((f ∘ₗ u).baseChange q.residueField) ≤
      LinearMap.range (f.baseChange q.residueField) := by
    rw [LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have hinj : Function.Injective ((f ∘ₗ u).baseChange q.residueField) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.mem_tensorInjectiveLocus.mp hq
  have hdim : Module.finrank q.residueField
      (LinearMap.range ((f ∘ₗ u).baseChange q.residueField)) = r := by
    rw [LinearMap.finrank_range_of_inj hinj,
      AlgebraicGeometry.FibrewiseRank.finrank_baseChange_pi]
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hr])

/-- Partial result toward Proposition A.6.6 (condition (4), the fiberwise inner-inverse
identity): if `s` is a scaled left inverse of `g` and the fiberwise images of `f` and `g`
agree at `q`, then `g ∘ s ∘ f = c • f` on the fiber at `q`.

On the fiber, `g ∘ s` is the projection onto the image of `g` scaled by `c`, and every
value of `f` lies in that image, so it is scaled by `c` and returned. -/
theorem LinearMap.baseChange_sub_eq_zero_of_range_eq
    (f : M →ₗ[R] N) {P : Type*} [AddCommGroup P] [Module R P]
    (g : P →ₗ[R] N) {c : R} {s : N →ₗ[R] P}
    (hs : s.comp g = c • (LinearMap.id : P →ₗ[R] P)) {q : PrimeSpectrum R}
    (hrange : LinearMap.range (g.baseChange q.residueField) =
      LinearMap.range (f.baseChange q.residueField)) :
    ((g ∘ₗ (s ∘ₗ f)) - c • f).baseChange q.residueField = 0 := by
  have hsg : (s.baseChange q.residueField).comp (g.baseChange q.residueField) =
      c • (LinearMap.id :
        q.residueField ⊗[R] P →ₗ[q.residueField] q.residueField ⊗[R] P) := by
    rw [← LinearMap.baseChange_comp, hs, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨w, hw⟩ : f.baseChange q.residueField z ∈
      LinearMap.range (g.baseChange q.residueField) := by
    rw [hrange]
    exact LinearMap.mem_range_self _ z
  have h1 : (((g ∘ₗ (s ∘ₗ f)) - c • f).baseChange q.residueField) z =
      (g.baseChange q.residueField) ((s.baseChange q.residueField)
        ((f.baseChange q.residueField) z)) - c • (f.baseChange q.residueField) z := by
    simp [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_comp]
  have h2 := LinearMap.congr_fun hsg w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
  rw [LinearMap.zero_apply, h1, ← hw, h2, LinearMap.map_smul_of_tower, hw, sub_self]

/-- **Proposition A.6.6** (`prop:linear-algebra`) (condition (4), reduced case):
over a reduced ring, if the rank of the fiber of `f` is constant equal to some `r` on
a basic open neighborhood of `p`, then the fiberwise kernel condition (3) — and with
it the other equivalent conditions — holds at `p`. -/
theorem LinearMap.kernelCommutesWithResidueFieldAt_of_isReduced_of_constant_finrank
    [IsReduced R] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (p : PrimeSpectrum R) (r : ℕ) (a : R) (ha : a ∉ p.asIdeal)
    (hconst : ∀ q : PrimeSpectrum R, a ∉ q.asIdeal →
      Module.finrank q.residueField
        (LinearMap.range (f.baseChange q.residueField)) = r) :
    f.KernelCommutesWithResidueFieldAt p := by
  classical
  have hrp : r ≤ AlgebraicGeometry.FibrewiseRank.rankAt f p := (hconst p ha).ge
  obtain ⟨u, hu⟩ :=
    AlgebraicGeometry.FibrewiseRank.exists_mem_tensorInjectiveLocus_of_le_rankAt f r hrp
  obtain ⟨U, ⟨e, rfl⟩, hpU, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hu
      (LinearMap.isOpen_tensorInjectiveLocus (f ∘ₗ u))
  have he : e ∉ p.asIdeal := (PrimeSpectrum.mem_basicOpen e p).mp hpU
  obtain ⟨c, hc, s, hs⟩ := LinearMap.exists_scaled_leftInverse_of_lTensor_injective
    (f ∘ₗ u) p (LinearMap.mem_tensorInjectiveLocus.mp hu)
  have key : ((a * e) • (((f ∘ₗ u) ∘ₗ (s ∘ₗ f)) - c • f) : M →ₗ[R] N) = 0 := by
    apply LinearMap.eq_zero_of_forall_baseChange_residueField_eq_zero
    intro q
    rw [LinearMap.baseChange_smul]
    by_cases hq : a * e ∈ q.asIdeal
    · rw [← algebraMap_smul q.residueField (a * e),
        Ideal.algebraMap_residueField_eq_zero.mpr hq, zero_smul]
    · have haq : a ∉ q.asIdeal := fun h ↦ hq (Ideal.mul_mem_right e _ h)
      have heq : e ∉ q.asIdeal := fun h ↦ hq (Ideal.mul_mem_left _ a h)
      have hqloc : q ∈ (f ∘ₗ u).tensorInjectiveLocus :=
        hU ((PrimeSpectrum.mem_basicOpen e q).mpr heq)
      rw [LinearMap.baseChange_sub_eq_zero_of_range_eq f (f ∘ₗ u) hs
        (LinearMap.range_baseChange_eq_of_constant_finrank f hqloc (hconst q haq)),
        smul_zero]
  refine LinearMap.kernelCommutesWithResidueFieldAt_of_scaled_innerInverse
    (a * e * c) ?_ ((a * e) • (u ∘ₗ s)) ?_
  · exact p.asIdeal.primeCompl.mul_mem (p.asIdeal.primeCompl.mul_mem ha he) hc
  · have h0 : ((a * e) • ((f ∘ₗ u) ∘ₗ (s ∘ₗ f)) : M →ₗ[R] N) = (a * e) • (c • f) := by
      rw [← sub_eq_zero, ← smul_sub]
      exact key
    calc f.comp ((((a * e) • (u ∘ₗ s)) : N →ₗ[R] M).comp f)
        = (a * e) • (((f ∘ₗ u) ∘ₗ (s ∘ₗ f)) : M →ₗ[R] N) := by
          rw [LinearMap.smul_comp, LinearMap.comp_smul]
          rfl
      _ = (a * e) • (c • f) := h0
      _ = (a * e * c) • f := by rw [smul_smul]

end PropLinearAlgebra
