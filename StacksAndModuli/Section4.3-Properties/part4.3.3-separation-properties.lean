module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.2-properties-of-spaces-and-stacks»
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Separation properties

This module covers `def:quasi-separated-noetherian` (=
`def:separated-for-representable-morphism`), `lem:quotient-stack-diagonal`, and
`ex:moduli-affine-diagonal` of §4.3 (First properties) of *Stacks and Moduli*
(the section carries no `sec:` label). It
corresponds to the subsection "Separation properties" (Subsection 4.3.3, label
`separation-properties`).

All separation notions of this subsection are defined in terms of the diagonal
`Δ : 𝒳 ⥤ᵇ 𝒳 ×_𝒴 𝒳` of a morphism of algebraic stacks (`CategoryTheory.BasedFunctor.diag`,
§4.2). Each item is built from a notion that only becomes available later — quasi-compact
morphisms in part 4.3.4, proper representable morphisms in §4.8 — so Definition 4.3.11 is
formalized in `StacksAndModuli/Section4.8-Properness/part4.8.1-definitions.lean`, in the block
`DefSeparatedForRepresentableMorphism`; the block below points there. What can be stated
already at the level of schemes —
the remark that the separatedness of a morphism of schemes can be tested by the
properness of its diagonal — is formalized as
`AlgebraicGeometry.Scheme.Hom.isClosedImmersion_diagonal_iff_isProper`.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefQuasiSeparatedNoetherian

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Relocation note for Definition 4.3.11 (with the book's alias and item labels
`def:separated-for-representable-morphism:quasi-separated` and
`…:finite-presentation` for its parts (2) and (3)): it is formalized **in
`StacksAndModuli/Section4.8-Properness/part4.8.1-definitions.lean`**, in the section block
`DefSeparatedForRepresentableMorphism`. All four items are conditions on the diagonal
`Δ_F : 𝒳 ⥤ᵇ fiberProduct F F` of a morphism of algebraic stacks
(`CategoryTheory.BasedFunctor.diag`, §4.2), and each is built from a notion that becomes
available only later:

1. affine / quasi-affine / separated diagonal — `BasedFunctor.HasAffineDiagonal`,
   `…HasQuasiAffineDiagonal`, `…HasSeparatedDiagonal`, with absolute forms in
   `AlgebraicGeometry.BasedCategory`;
2. quasi-separated — `BasedFunctor.QuasiSeparated`, and `BasedCategory.IsQuasiSeparated`
   in part4.8.3; it needs `BasedFunctor.QuasiCompact`, which is part 4.3.4;
3. finite presentation — `BasedFunctor.FinitePresentation`;
4. separatedness of a representable morphism — `BasedFunctor.IsSeparatedRepresentable`;
   it needs properness of a representable morphism, which is §4.8.

The translation of conditions on the diagonal into conditions on the `Isom` sheaves
(the base change of `Δ` along `(a, b) : S → 𝒳 × 𝒳` is `Isom_{𝒳(S)}(a, b)`) is still
blocked on `exer:isom-presheaf` (§3.4 ledger).

LEDGER (unlabeled remark): a quasi-separated Deligne–Mumford stack has finite and
reduced stabilizer groups (`exer:deligne-mumford-unramified-diagonal`, §4.2 ledger). -/

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- API theorem from the first unnumbered remark in §4.3.3, after Definition 4.3.11:
let $f \colon X \to Y$ be a morphism of
schemes. The diagonal $\Delta_f \colon X \to X \times_Y X$ is a closed immersion if and
only if it is proper. Hence the definition of separatedness for (representable)
morphisms of algebraic stacks via the properness of the diagonal agrees, for schemes,
with the usual notion. -/
theorem isClosedImmersion_diagonal_iff_isProper :
    IsClosedImmersion (pullback.diagonal f) ↔ IsProper (pullback.diagonal f) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact IsClosedImmersion.of_isPreimmersion _
      (pullback.diagonal f).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.Hom

end DefQuasiSeparatedNoetherian


section LemQuotientStackDiagonal

/- Relocation note for Lemma 4.3.14: for `S` an affine scheme and `G → S` a
smooth affine group scheme acting on `U` over `S`, if `U` has affine (resp. quasi-affine)
diagonal, then so does `[U/G]`.

Both parts are stated in
`StacksAndModuli/Section4.8-Properness/part4.8.1-definitions.lean`, block
`LemQuotientStackDiagonal` (`hasAffineDiagonal_toBase_quotientPrestack_ofAction` and
`hasQuasiAffineDiagonal_toBase_quotientPrestack_ofAction`, proofs deferred): `[U/G]` is the
action-groupoid quotient prestack of §4.4 — the rendering Theorem 4.1.10
(`thm:quotient-stack-is-algebraic`) is stated for — and `HasAffineDiagonal` for a morphism
of prestacks is defined in that §4.8 file, so this file can import neither. `U` is taken to
be a scheme rather than an algebraic space, as everywhere `ofAction` is used. -/

end LemQuotientStackDiagonal


section ExModuliAffineDiagonal

/- Relocation note for Example 4.3.15: the moduli stacks `𝓜_g` and
`Bun_{r,d}(C)` have affine diagonal and are thus quasi-separated.

The `𝓜_g` half is stated in
`StacksAndModuli/Section4.6-Characterization/part4.6.2-equivalent-characterizations.lean`, block
`ExModuliAffineDiagonal` (`hasAffineDiagonal_moduliOfCurves`, proof deferred): `𝓜_g` is
built in §4.1 part4.1.4 and the diagonal-free form of "affine diagonal" is §4.5's
`BasedCategory.HasAffineDiagonal`, so neither fits in this file.

LEDGER — the `Bun_{r,d}(C)` half is still blocked on the moduli stack of bundles
(`thm:bunC-is-algebraic`, §4.1 ledger) and on quotient stack presentations.

LEDGER (unlabeled example): non-quasi-separated examples — the algebraic space
`[𝔸¹/ℤ]` (`ex:non-quasi-separated-algebraic-space`) and the algebraic stack `Bℤ`
(`ex:classifying-stack-BZ`). Blocked on quotient and classifying stacks (§3.4/§3.5
ledgers) and on quasi-separatedness (§4.2 diagonal). -/

end ExModuliAffineDiagonal
