module

public import StacksAndModuli.«Section2.3-Regularity».«part2.3.2-regularity-bounds»

/-!
# An invitation to the geometry of Hilbert schemes

This module corresponds to §2.5 (An invitation to the geometry of Hilbert schemes) of
Chapter 2 of *Stacks and Moduli*. The
`\section` heading of this file carries no `sec:` label; its labelled subdivisions are
the subsection `sec:hilbert-scheme-geometric-properties` (Section 2.5.2, "Geometric
properties") and the example `sec:hilbert-scheme-surface` (2.5.3, Hilbert scheme of
points on a surface).

The section is a survey ("we will not attempt a systematic exposition") and almost all of
its content depends on the polynomially-refined Hilbert scheme `Hilb^P(ℙ^n)`, which is not
yet formalizable (see the §2.1 ledger): the hypersurface/linear-subspace exercise, the
Hilbert schemes of points on curves (`Sym^n C`) and surfaces
(`sec:hilbert-scheme-surface`, Fogarty), twisted cubics (Piene–Schlessinger), the
tangent-space exercise `exer:quot-tangent-space`, Hartshorne's non-emptiness and
connectedness theorems, Vakil's Murphy's Law, and the Skjelnes–Smith smoothness
classification. All are recorded with references in the chapter ledger
(`docbuild/chapter2-hilber-and-quot/summaries/ch2-5-geometry.md`).

What is formalizable now is the combinatorial normal form of Hilbert polynomials used in
Hartshorne's non-emptiness criterion (`eq:hilbert-polynomial-partition`): the polynomial
attached to a partition `λ₁ ≥ λ₂ ≥ ⋯ ≥ λᵣ ≥ 1`,
`P(z) = ∑ᵢ C(z + λᵢ - i, λᵢ - 1)`. `Hilb^P(ℙ^n)` is non-empty precisely when `P` has
this form (Hartshorne); the equivalence is ledgered with the Hilbert scheme itself.

Main declarations:
- `Polynomial.hilbertPartitionPoly` (`eq:hilbert-polynomial-partition`, Equation
  (2.5.7)): the Hilbert polynomial of a partition.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section EqHilbertPolynomialPartition

open Polynomial

/-- **Equation (2.5.7)** (`eq:hilbert-polynomial-partition`) (the implicit definition of
the partition polynomial): the polynomial
`P(z) = ∑_{i=1}^{r} C(z + λᵢ - i, λᵢ - 1) ∈ ℚ[z]` attached to a list
`λ = (λ₁, …, λᵣ)` of positive integers. By a theorem of Hartshorne, for a decreasing list
`λ` these are exactly the Hilbert polynomials of nonempty closed subschemes of projective
space, i.e. `Hilb^P(ℙ^n)` is non-empty if and only if `P` is of this form; the
equivalence itself awaits `Hilb^P(ℙ^n)` and is recorded in the chapter ledger.

Defined for an arbitrary `List ℕ`: the book's ordering and positivity hypotheses
`λ₁ ≥ λ₂ ≥ ⋯ ≥ λᵣ ≥ 1` are not imposed here and would enter only in Hartshorne's
criterion (see this section's COMMENTARY.md).

The book displays this polynomial twice: here, and in **Remark 2.3.15** as Gotzmann's
normal form. It is the same object, and
`Polynomial.hilbertPartitionPoly_eq_gotzmannPoly` records that. -/
noncomputable def Polynomial.hilbertPartitionPoly (l : List ℕ) : Polynomial ℚ :=
  (l.zipIdx.map fun p ↦
    (binomialPoly (p.1 - 1)).comp (X + C ((p.1 : ℚ) - (p.2 + 1)))).sum

/-- API lemma for Equation (2.5.7): the partition polynomial of
Hartshorne's non-emptiness criterion is Gotzmann's normal form of **Remark 2.3.15**. In
particular it is a numerical polynomial
(`Polynomial.isNumerical_gotzmannPoly`), and its values are the sums of binomial
coefficients of the book's display (`Polynomial.gotzmannPoly_eval`). -/
lemma Polynomial.hilbertPartitionPoly_eq_gotzmannPoly (l : List ℕ) :
    hilbertPartitionPoly l = gotzmannPoly l := rfl

end EqHilbertPolynomialPartition
