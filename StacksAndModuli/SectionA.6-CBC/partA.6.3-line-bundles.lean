module

public import StacksAndModuli.«SectionA.6-CBC».«partA.6.1-linear-algebra»
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»

/-!
# Cohomology and base change: applications to line bundles

This part formalizes the subsection *Applications to line bundles* of §A.6 of
*Stacks and Moduli*, which answers, in three versions of
increasing strength, the question: for a proper flat morphism `f : X → Y` and a line bundle
`L` on `X`, when is `L` the pullback of a line bundle on `Y`, and is there a largest
subscheme of `Y` over which it is?

The subsection opens with **Lemma A.6.13** (`lem:line-bundle-conditions`), which compares
the fibre conditions the three versions rest on, and that is what is recorded here.  Its
statement is the point at which the Semicontinuity Theorem of `partA.6.1` meets the
geometry of `ℳ_g`: condition (3), `𝒪_Y = f_* 𝒪_X` universally, is exactly the hypothesis
that Proposition 6.1.16 establishes for a family of smooth curves
(`AlgebraicGeometry.Scheme.isIso_unit_structureModule`).

**Version 2** (`prop:line-bundles-version2`) is stated here as well: its statement needs
only a line bundle and the triviality of its fibres, both of which are expressible
(`Modules.IsProjectiveOfRank 1` and an isomorphism with the structure sheaf of the fibre);
its *proof* is what needs the dual `L^∨`, which does not exist.  Version 1 (unlabelled) and
**Version 3** (`prop:line-bundle-version3`) are not stated: Version 1 quantifies over duals
in its statement, and Version 3 asserts representability by a locally closed subscheme.  See
this folder's COMMENTARY.md.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

section LemLineBundleConditions

/-- Background definition for Lemma A.6.13 (condition (3)): the canonical map
`𝒪_Y → f_* 𝒪_X` is an isomorphism, and remains one after an arbitrary base change
`T → Y`.

`f_* 𝒪_X` is written as `f_* f^* 𝒪_Y`, so that the comparison map of the book is literally
the unit of the adjunction `f^* ⊣ f_*` at the structure sheaf; this is the same rendering
used for Proposition 6.1.16 in §6.1. -/
def AlgebraicGeometry.Scheme.Hom.StructurePushforwardUniversallyTrivial
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (T XT : Scheme.{u}) (g : T ⟶ Y) (fT : XT ⟶ T) (g' : XT ⟶ X),
    IsPullback g' fT f g →
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction fT).unit.app
        (Scheme.structureModule T))

/-- **Lemma A.6.13** (`lem:line-bundle-conditions`) (the implication (1) ⇒ (2)): for a
proper flat morphism of noetherian schemes whose geometric fibres are non-empty, connected
and reduced, every fibre satisfies `h⁰(X_y, 𝒪_{X_y}) = 1`.

"Non-empty geometric fibres" is surjectivity of `f`.  The book's proof passes to an
algebraic closure of `κ(y)` by Flat Base Change and uses that a connected reduced proper
scheme over an algebraically closed field has only constant functions.

**Deferred**: flat base change for cohomology and the constancy of global functions on a
connected reduced proper scheme over an algebraically closed field are both absent from the
library. -/
theorem AlgebraicGeometry.Scheme.Hom.fibreH_structureModule_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Flat f] [IsNoetherian X] [IsNoetherian Y]
    [Surjective f] [GeometricallyConnected f] [GeometricallyReduced f] (y : Y) :
    f.fibreH (Scheme.structureModule X) y 0 = 1 := by
  sorry

/-- **Lemma A.6.13** (`lem:line-bundle-conditions`) (the equivalence (2) ⟺ (3)): for a
proper flat morphism of noetherian schemes, every fibre satisfies
`h⁰(X_y, 𝒪_{X_y}) = 1` if and only if `𝒪_Y = f_* 𝒪_X` universally.

**Deferred**: the forward direction is Cohomology and Base Change II (Theorem A.6.8) in
degree `0`: the comparison map `f_* 𝒪_X ⊗ κ(y) → H⁰(X_y, 𝒪_{X_y}) = κ(y)` is
surjective
because `1` is a global section, so A.6.8 makes `f_* 𝒪_X` a line bundle, and a surjection
of line bundles is an isomorphism.  The converse is the case `T = Spec κ(y)`.  Theorem
A.6.8 is not formalized: it needs the higher direct images `Rⁱ f_* F` as `𝒪_Y`-modules and
their base-change comparison maps. -/
theorem AlgebraicGeometry.Scheme.Hom.fibreH_structureModule_eq_one_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Flat f] [IsNoetherian X] [IsNoetherian Y] :
    (∀ y : Y, f.fibreH (Scheme.structureModule X) y 0 = 1) ↔
      f.StructurePushforwardUniversallyTrivial := by
  sorry

end LemLineBundleConditions

section PropLineBundlesVersion2

/-- **Proposition A.6.16** (`prop:line-bundles-version2`) (Version 2): for a proper flat
morphism of noetherian schemes with integral geometric fibres and a line bundle `L` on the
source, the locus of points of the base over which `L` restricts to the trivial bundle is
closed.

"Line bundle" is `Modules.IsProjectiveOfRank 1` (§2.1); "`L_y` is trivial on `X_y`" is the
existence of an isomorphism between the restriction of `L` to the scheme-theoretic fibre and
the structure sheaf of that fibre.  No dual sheaf occurs in the statement.

The proof (deferred) is: over a geometrically integral proper `Z/k`, a line bundle `M` is
trivial exactly when `h⁰(Z, M) > 0` and `h⁰(Z, M^∨) > 0`; both conditions are closed by the
Semicontinuity Theorem, whose closed-locus form
(`Scheme.Hom.isClosed_setOf_le_fibreH`, proved in `partA.6.1`) is exactly what is needed.
**Blocked on** the dual `L^∨` of an `𝒪_X`-module, which exists neither in Mathlib nor here,
and on the triviality criterion itself. -/
theorem AlgebraicGeometry.Scheme.Hom.isClosed_setOf_fibre_trivial
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Flat f] [IsNoetherian X] [IsNoetherian Y]
    [GeometricallyIntegral f] (L : X.Modules)
    (hL : Scheme.Modules.IsProjectiveOfRank 1 L) :
    IsClosed {y : Y | Nonempty (f.fibreModule L y ≅ Scheme.structureModule (f.fiber y))} := by
  sorry

end PropLineBundlesVersion2
