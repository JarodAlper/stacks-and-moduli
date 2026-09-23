module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksAndModuli.API.QuasiFiniteSourceLocal

/-!
# Quasi-finite morphisms

This module covers `def:quasi-finite` and `exer:quasi-finite` of §4.3 (First
properties) of *Stacks and Moduli* (the
section carries no `sec:` label). It corresponds to the subsection "Quasi-finite
morphisms" (Subsection 4.3.5, label `subsec:quasi-finite-definition`).

A morphism of schemes is locally quasi-finite if it is locally of finite type with
discrete fibers; this is Mathlib's `AlgebraicGeometry.LocallyQuasiFinite`, recalled
below, and it is étale local on the source and target
(`AlgebraicGeometry.isEtaleLocal_locallyQuasiFinite`). Locally quasi-finite
representable morphisms of algebraic stacks (`def:quasi-finite` (1)) are the
representable morphisms with property `@LocallyQuasiFinite` in the sense of §4.1's
`AlgebraicGeometry.BasedFunctor.RepresentableWith`. The general definition for
morphisms of algebraic stacks (`def:quasi-finite` (2), (3)) requires the locally
quasi-finite diagonal and is ledgered pending §4.2.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefQuasiFinite

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

/- Background example from §4.3.5 (locally quasi-finite
morphisms of schemes, from the introductory paragraph): a morphism of schemes is
*locally quasi-finite* if it is locally of finite type and every fiber is discrete.
This is Mathlib's `AlgebraicGeometry.LocallyQuasiFinite`. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyQuasiFinite f

/-- API theorem from §4.3.5 (local quasi-finiteness is
étale local, from the introductory paragraph): local quasi-finiteness of morphisms of
schemes is étale local on the source and target, so it extends to morphisms of
algebraic spaces (and to representable morphisms of algebraic stacks) by Definition 4.3.2.

Both localities come from `locallyQuasiFinite_of_comp_of_smooth_surjective`, which descends
quasi-finiteness along a *smooth* surjection (the ring-level input needs only faithful
flatness; see `StacksAndModuli/API/QuasiFiniteFaithfullyFlatDescent.lean`). Target-locality does not
need fppf descent: `pullback.fst f g` is an étale surjection, being the base change of `g`,
and `pullback.fst f g ≫ f = pullback.snd f g ≫ g`, so source-locality applies — the same
route as for flatness in `isSmoothLocal_flat`. -/
theorem isEtaleLocal_locallyQuasiFinite :
    IsEtaleLocal (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Etale g := hg.2
    haveI : Smooth g := inferInstance
    refine ⟨fun hf => MorphismProperty.comp_mem @LocallyQuasiFinite _ _ inferInstance hf,
      fun hgf => locallyQuasiFinite_of_comp_of_smooth_surjective g f hgf⟩
  isLocalOnTargetAlong := fun {X} {Y} {Y'} f g hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Etale g := hg.2
    haveI hfs : Surjective (Limits.pullback.fst f g) :=
      MorphismProperty.pullback_fst _ _ ‹Surjective g›
    haveI hfe : Etale (Limits.pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
    haveI : Smooth (Limits.pullback.fst f g) := inferInstance
    refine ⟨fun hf => MorphismProperty.pullback_snd _ _ hf, fun hsnd => ?_⟩
    have h1 : LocallyQuasiFinite (Limits.pullback.snd f g ≫ g) :=
      MorphismProperty.comp_mem @LocallyQuasiFinite _ _ hsnd inferInstance
    rw [← Limits.pullback.condition] at h1
    exact locallyQuasiFinite_of_comp_of_smooth_surjective (Limits.pullback.fst f g) f h1

/- **Definition 4.3.34** (`def:quasi-finite`) (part (1)): let $\cX \to \cY$ be a
representable morphism of algebraic stacks. Then $\cX \to \cY$ is *locally
quasi-finite* if for every morphism $T \to \cY$ from a scheme, the algebraic space
$\cX \times_{\cY} T$ is locally quasi-finite over $T$. This is §4.1's
`AlgebraicGeometry.BasedFunctor.RepresentableWith` with the property
`@LocallyQuasiFinite` (which tests the property on étale presentations of the algebraic
space, i.e. via the étale-locality on the source recorded above). -/
example {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
    (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  BasedFunctor.RepresentableWith (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) F

/- LEDGER — **Definition 4.3.34** (`def:quasi-finite`) (parts (2), the item label
`def:quasi-finite2`, and (3)): a morphism `𝒳 → 𝒴` of algebraic stacks is
*locally quasi-finite* if it is locally of finite type
(`BasedFunctor.LocallyOfFiniteType`, part 4.3.1), the diagonal `𝒳 → 𝒳 ×_𝒴 𝒳` is locally
quasi-finite (as a representable morphism, item (1)), and for every field-valued point
`Spec k → 𝒴` the space `|𝒳 ×_𝒴 Spec k|` is discrete
(`DiscreteTopology (pointSpace (fiberProduct F g))`, part 4.3.4); it is *quasi-finite*
if it is in addition quasi-compact (`BasedFunctor.QuasiCompact`, part 4.3.4). The
diagonal requires §4.2 (`exer:diagonal-of-morphisms`) — to be completed once
Section4.2-Representability lands.

LEDGER (discussion after `def:quasi-finite`): the diagonal is quasi-finite (resp.
locally quasi-finite) if and only if for every field-valued point `x ∈ 𝒳(k)` with image
`y ∈ 𝒴(k)`, the kernel `ker(G_x → G_y)` of the induced map of stabilizer groups is
finite (resp. discrete); in particular for `𝒴` a scheme the diagonal is quasi-finite iff
all stabilizers are finite, `B G → Spec k` is quasi-finite for finite group schemes `G`
(e.g. `μ_p`), and `B 𝔾_m → Spec k` is not quasi-finite although `|B 𝔾_m|` is a point.
Blocked on stabilizer groups and `exer:fiber-products-and-stabilizers` (§4.2) and on
classifying stacks (§3.4/§3.5 ledgers). -/

end AlgebraicGeometry

end DefQuasiFinite


section ExerQuasiFinite

/- LEDGER — **Exercise 4.3.35** (`exer:quasi-finite`): a finite type morphism
`f : 𝒳 → 𝒴` of algebraic stacks
is quasi-finite if and only if `|𝒳| → |𝒴|` has finite fibers and for every field-valued
point `x ∈ 𝒳(k)` the map `Aut_{𝒳(k)}(x) → Aut_{𝒴(k)}(f(x))` has finite cokernel.
Blocked on `def:quasi-finite` (2)–(3) (§4.2 diagonal, see above) and on cokernels of
group algebraic spaces.

The forward reference `prop:factorization-into-open-and-affine-algebraic-spaces` (every
representable, quasi-finite, separated morphism is quasi-affine) belongs to a later
section. -/

end ExerQuasiFinite
