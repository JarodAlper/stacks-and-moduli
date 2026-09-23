module

public import «StacksProject».«Constructions».«InvertibleSheavesOnProj».«definition-twist»
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

/-!
# `m`-regularity

Stacks Project tag **08A3**, label `varieties-definition-regularity`, in `varieties.tex`,
§`08A2` (Regularity).

> Let `k` be a field. Let `n ≥ 0`. Let `ℱ` be a coherent sheaf on `𝐏ⁿ_k`. We say `ℱ` is
> *`m`-regular* if `Hⁱ(𝐏ⁿ_k, ℱ(m - i)) = 0` for `i = 1, …, n`.

This is Castelnuovo–Mumford regularity, though the Stacks Project never calls it that. Note
that it lives in `varieties.tex`, not `coherent.tex`.

## Generality

The tag is stated for a coherent sheaf on `𝐏ⁿ` over a field. It is formalized here for an
arbitrary sheaf of modules on `Proj 𝒜` of an arbitrary graded ring, since that is where the
twisting sheaves `𝒪(d)` of tag 01MN live and nothing in the definition needs either the
field, the coherence, or the bound `n`. Two consequences:

* The vanishing is asked for **all** `i ≥ 1` rather than `i = 1, …, n`. Over `𝐏ⁿ_k` the two
  agree, because `Hⁱ(𝐏ⁿ_k, -) = 0` for `i > n`; in the stated generality the unbounded form
  is the right one. This also matches the phrasing of *Stacks and Moduli*
  Definition 2.3.1, which asks for all `i ≥ 1`.
* Nothing here is claimed about the *behaviour* of the notion — that `m`-regular implies
  `m'`-regular for `m' ≥ m`, that regularity is insensitive to field extension, and so on.
  Those need the long exact cohomology sequence, which is reachable through the covariant
  `Ext` long exact sequence but not yet wired up to `CategoryTheory.Sheaf.H`; see the root
  INSIGHTS.md of StacksAndModuli.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.IsMRegular`: `m`-regularity of a sheaf of
  modules on `Proj 𝒜`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Stacks 08A3** (`varieties-definition-regularity`): a sheaf of modules `ℱ` on
`Proj 𝒜` is **`m`-regular** when `Hⁱ(Proj 𝒜, ℱ(m - i)) = 0` for every `i ≥ 1`.

This is Castelnuovo–Mumford regularity. The Stacks Project states it for a coherent sheaf
on `𝐏ⁿ` over a field and for `i = 1, …, n`; see this file's module docstring for why the
`Proj`-level, unbounded-`i` form is used here, and why the two agree over `𝐏ⁿ_k`.

Vanishing of the cohomology group is expressed as `Subsingleton`: `Sheaf.H` is an `Ext`
group, whose `AddCommGroup` instance is not currently available at this universe (see the
§2.3 INSIGHTS.md of StacksAndModuli), and a subsingleton abelian group is exactly a zero one. -/
@[stacks 08A3]
def IsMRegular (F : (Proj 𝒜).Modules) (m : ℤ) : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    Subsingleton (((SheafOfModules.toSheaf _).obj
      (_root_.ProjectiveSpectrum.Twist.twistModule 𝒜 F (m - (i : ℤ)))).H i)

/-- Unfolding lemma for `m`-regularity. -/
theorem isMRegular_iff (F : (Proj 𝒜).Modules) (m : ℤ) :
    IsMRegular 𝒜 F m ↔ ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (_root_.ProjectiveSpectrum.Twist.twistModule 𝒜 F (m - (i : ℤ)))).H i) :=
  Iff.rfl

end AlgebraicGeometry.ProjectiveSpectrum.Proj
