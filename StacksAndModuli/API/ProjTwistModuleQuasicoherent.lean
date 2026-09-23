module

public import StacksAndModuli.API.ProjTwistMulHom
public import StacksAndModuli.API.ProjectiveTwistBaseChange

/-!
# Quasicoherence of the twists `F(d)` on `Proj 𝒜`

Every result of `StacksAndModuli/API/ProjTwistII514.lean`, `…II514Global.lean` and
`…ProjGammaStarChart.lean` takes `[(ProjectiveSpectrum.Twist.twistModule 𝒜 F d).IsQuasicoherent]`
as a hypothesis.  This file discharges it: if `Proj 𝒜` is covered by degree-one basic opens and
`F` is finitely presented, then so is every twist `F(d)`, hence quasicoherent.

The two inputs are already in the library:

* `ProjectiveSpectrum.Twist.restrictTwistIsoUnit` — on a degree-one basic open `D₊(f)` the
  twisting sheaf `𝒪(d)` is trivialized by `f^d`;
* `Scheme.Modules.tensor_isFinitePresentation_of_iSup_iso_unit` — tensoring a finitely presented
  sheaf with one that is trivial on an open cover preserves finite presentation.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The twists of a finitely presented sheaf are finitely presented**, given a cover of
`Proj 𝒜` by degree-one basic opens. -/
theorem twistModule_isFinitePresentation {J : Type u} (y : J → A) (hy : ∀ j, y j ∈ 𝒜 1)
    (hcover : ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒜 (y j) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] (d : ℤ) :
    (twistModule 𝒜 F d).IsFinitePresentation :=
  Scheme.Modules.tensor_isFinitePresentation_of_iSup_iso_unit F (twist 𝒜 d)
    (fun j ↦ AlgebraicGeometry.Proj.basicOpen 𝒜 (y j)) hcover
    (fun j ↦ restrictTwistIsoUnit (hy j) d)

/-- **The twists of a finitely presented sheaf are quasicoherent.** -/
theorem twistModule_isQuasicoherent {J : Type u} (y : J → A) (hy : ∀ j, y j ∈ 𝒜 1)
    (hcover : ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒜 (y j) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] (d : ℤ) :
    (twistModule 𝒜 F d).IsQuasicoherent := by
  letI := twistModule_isFinitePresentation 𝒜 y hy hcover F d
  infer_instance

end ProjectiveSpectrum.Twist
