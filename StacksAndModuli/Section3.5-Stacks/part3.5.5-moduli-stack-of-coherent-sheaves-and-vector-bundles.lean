module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.4-moduli-stack-of-curves»
public import StacksAndModuli.API.QuasicoherentFamilyStacks

/-!
# Moduli stack of coherent sheaves and vector bundles

This module follows the subsection "Moduli stack of coherent sheaves and vector bundles"
of §3.5 (Stacks) of *Stacks and Moduli*,
section label `sec:stacks`. Formalization state per
label: see this folder's STATUS.md.

**Proposition 3.5.17** (`prop:mss-is-a-stack`) asserts that the prestacks `QCoh(X)`,
`Coh(X)` and `Bun(X)` of **Example 3.4.12** (`ex:moduli-prestack-of-vector-bundles`) —
families of quasi-coherent, finitely presented, respectively finite locally free modules
on `X ×_S T`, flat over `T` — are stacks over `(Sch/S)_ét`.

The book's proof is one sentence: it "follows directly from Fpqc Descent for Quasi-Coherent
Sheaves (`prop:fpqc-descent-for-quasi-coherent-sheaves`) and Fpqc Descent of Properties of
Quasi-Coherent Sheaves (`prop:fpqc-descent-for-properties-of-quasi-coherent-sheaves`)".
That structure is reproduced exactly, in `StacksAndModuli/API/QuasicoherentFamilyStacks.lean`:
the first cited result is `isStack_familyModulesPseudofunctor`, which is
`prop:fpqc-descent-for-quasi-coherent-sheaves` transported along `T ↦ X ×_S T` by
`Pseudofunctor.isStack_precomp_of_coverPreserving`; the second is
`prop:fpqc-descent-for-properties-of-quasi-coherent-sheaves` in the form
`Pseudofunctor.ObjectProperty.IsLocal` consumes, one instance per property
(`flatFamilyProperty_isLocal_etale` and its coherent and vector-bundle companions). The
three conclusions then follow by the route already used for **Example 3.5.9**
(`ex:stack-of-quasi-coherent-sheaves`) — `fullsubcategory_isStack` to cut down by a local
object property, then `core_isStack` to restrict the fibre arrows to isomorphisms.

Main results:
- `AlgebraicGeometry.Scheme.Modules.isStack_flatFamilyPseudofunctor`,
  `isStack_coherentFamilyPseudofunctor`, `isStack_vectorBundleFamilyPseudofunctor`:
  **Proposition 3.5.17** (`prop:mss-is-a-stack`) for `QCoh(X)`, `Coh(X)`, `Bun(X)`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropMssIsAStack

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (X : Over S)

/-- **Proposition 3.5.17** (`prop:mss-is-a-stack`) for `QCoh(X)`: the prestack of
quasi-coherent families on `X ×_S T` flat over `T`, with isomorphisms as fibre arrows, is
a stack over `(Sch/S)_ét`. -/
theorem isStack_flatFamilyPseudofunctor :
    (flatFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
  isStack_flatFamilyPseudofunctor_etale X

/-- **Proposition 3.5.17** (`prop:mss-is-a-stack`) for `Coh(X)`: the prestack of coherent
families is a stack over `(Sch/S)_ét`. -/
theorem isStack_coherentFamilyPseudofunctor :
    (coherentFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
  isStack_coherentFamilyPseudofunctor_etale X

/-- **Proposition 3.5.17** (`prop:mss-is-a-stack`) for `Bun(X)`: the prestack of
vector-bundle families is a stack over `(Sch/S)_ét`. -/
theorem isStack_vectorBundleFamilyPseudofunctor :
    (vectorBundleFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
  isStack_vectorBundleFamilyPseudofunctor_etale X

/-- Convenience conjunction derived from Proposition 3.5.17: if `X` is a scheme over a base
scheme `S`, the prestacks `QCoh(X)`, `Coh(X)`, and `Bun(X)` of respectively flat
quasicoherent families, flat finitely presented quasicoherent families, and
vector-bundle families on `X ×_S T` are stacks over the étale site of schemes over
`S`. The book states the case in which `S` is the spectrum of its base field; the
same descent proof works over an arbitrary base scheme. -/
theorem isStack_familyModuliPseudofunctors :
    (flatFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) ∧
      (coherentFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) ∧
      (vectorBundleFamilyPseudofunctor X).IsStack
        (Scheme.etaleTopology.over S) := by
  exact ⟨isStack_flatFamilyPseudofunctor X, isStack_coherentFamilyPseudofunctor X,
    isStack_vectorBundleFamilyPseudofunctor X⟩

end AlgebraicGeometry.Scheme.Modules

end PropMssIsAStack
