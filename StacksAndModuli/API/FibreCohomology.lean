module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Flat.Basic
public import StacksAndModuli.API.SheafCohomologyModule

/-!
# Coherence, relative flatness, and the cohomology of the fibres of a morphism

This file supplies the three notions in which Cohomology and Base Change is stated but
which are absent from Mathlib and from the rest of this library:

* `AlgebraicGeometry.Scheme.Modules.IsCoherent`: an `𝒪_X`-module is **coherent** if it is
  quasi-coherent and of finite type.  On a locally noetherian scheme — the only setting in
  which §A.6 uses the word — this is the classical notion.
* `AlgebraicGeometry.Scheme.Hom.ModulesFlat`: an `𝒪_X`-module is **flat over `Y`** along
  `f : X ⟶ Y` if its sections over every affine open of `X` are a flat module over the
  sections of `𝒪_Y` over an affine open of `Y` containing the image.
* `AlgebraicGeometry.Scheme.Hom.fibreModule`, `…fibreH`, `…fibreEulerChar`: the restriction
  `F_y` of `F` to the scheme-theoretic fibre `X_y`, its cohomology dimensions
  `hⁱ(X_y, F_y)` over the residue field `κ(y)`, and their alternating sum `χ(X_y, F_y)`,
  together with their invariance under isomorphism of the coefficient sheaf
  (`…fibreH_eq_of_iso`, `…fibreEulerChar_eq_of_iso`).

The fibre is Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, which comes with its canonical
morphism to `Spec κ(y)`; that morphism is what makes `Hⁱ(X_y, F_y)` a `κ(y)`-vector space,
via `AlgebraicGeometry.Scheme.Modules.h`.  Because the `Over (Spec κ(y))` structure is a
`def` in Mathlib rather than an instance, it is supplied locally in the definitions below.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- An `𝒪_X`-module is **coherent** if it is quasi-coherent and of finite type.

On a locally noetherian scheme this agrees with the classical definition (a quasi-coherent
module of finite type over a noetherian ring is finitely presented, and every submodule of
a finite module is finite), which is the only setting in which §A.6 uses the word. -/
class Scheme.Modules.IsCoherent (F : X.Modules) : Prop extends
  F.IsQuasicoherent, F.IsFiniteType

instance (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Scheme.Modules.IsCoherent F where

/-- An `𝒪_X`-module `F` is **flat over `Y`** along `f : X ⟶ Y` if for every affine open
`V ⊆ Y` and every affine open `U ⊆ f⁻¹(V)` the sections `Γ(F, U)` form a flat module over
the ring `Γ(Y, V)`, acting through `f`.

Restriction of scalars is written out explicitly because the `Γ(Y, V)`-module structure on
`Γ(F, U)` is not an instance: it comes from the ring map `f.appLE V U e`. -/
def Scheme.Hom.ModulesFlat (f : X ⟶ Y) (F : X.Modules) : Prop :=
  ∀ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
    (e : U ≤ f ⁻¹ᵁ V),
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Module.Flat Γ(Y, V) (RestrictScalars Γ(Y, V) Γ(X, U) Γ(F, U))

/-- The restriction `F_y` of an `𝒪_X`-module `F` to the scheme-theoretic fibre `X_y`. -/
noncomputable def Scheme.Hom.fibreModule (f : X ⟶ Y) (F : X.Modules) (y : Y) :
    (f.fiber y).Modules :=
  (Scheme.Modules.pullback (f.fiberι y)).obj F

/-- `hⁱ(X_y, F_y)`: the dimension over the residue field `κ(y)` of the `i`-th cohomology of
the restriction of `F` to the fibre of `f` over `y`. -/
noncomputable def Scheme.Hom.fibreH (f : X ⟶ Y) (F : X.Modules) (y : Y) (i : ℕ) : ℕ :=
  letI : (f.fiber y).Over (Spec (CommRingCat.of (Y.residueField y))) :=
    ⟨f.fiberToSpecResidueField y⟩
  Scheme.Modules.h (Y.residueField y) (f.fibreModule F y) i

/-- `χ(X_y, F_y) = ∑_{i ≤ n} (-1)ⁱ hⁱ(X_y, F_y)`, the Euler characteristic of the fibre in
the range `[0, n]`.

The range is explicit because Grothendieck vanishing — which would make the sum finite
automatically — is not available; for a proper morphism of noetherian schemes any `n` at
least the dimension of the fibres computes the full alternating sum. -/
noncomputable def Scheme.Hom.fibreEulerChar (f : X ⟶ Y) (F : X.Modules) (n : ℕ) (y : Y) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * f.fibreH F y i

/-- Isomorphic `𝒪_X`-modules have the same fibrewise cohomology dimensions.

Needed whenever a sheaf is replaced by an isomorphic one before its fibre cohomology is
computed — for instance `Ω_{𝒞/S}^{⊗ k}` by the pullback of a pluricanonical bundle. -/
lemma Scheme.Hom.fibreH_eq_of_iso (f : X ⟶ Y) {F G : X.Modules} (e : F ≅ G) (y : Y) (i : ℕ) :
    f.fibreH F y i = f.fibreH G y i := by
  let _ : (f.fiber y).Over (Spec (CommRingCat.of (Y.residueField y))) :=
    ⟨f.fiberToSpecResidueField y⟩
  exact Scheme.Modules.h_eq_of_iso (Y.residueField y)
    ((Scheme.Modules.pullback (f.fiberι y)).mapIso e) i

/-- Isomorphic `𝒪_X`-modules have the same fibrewise Euler characteristic. -/
lemma Scheme.Hom.fibreEulerChar_eq_of_iso (f : X ⟶ Y) {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    f.fibreEulerChar F n = f.fibreEulerChar G n := by
  funext y
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [f.fibreH_eq_of_iso e y i]

end AlgebraicGeometry
