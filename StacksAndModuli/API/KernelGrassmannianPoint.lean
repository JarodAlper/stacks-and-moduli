module

public import StacksAndModuli.API.FreeSheafSections

/-!
# The Grassmannian point attached to a map out of a finite free sheaf

`API/FreeSheafSections.lean` turns a morphism `φ : 𝒪_X^m ⟶ M` into
`Scheme.Modules.kernelSubmoduleSheafData φ`, an unconditional `SubmoduleSheafData` once `M`
is quasicoherent.  A *point of the Grassmannian* is more: `grassmannianFunctor q m` asks the
submodule data to satisfy `SubmoduleSheafData.QuotientProjectiveOfRank q`, i.e. that the
quotients `Γ(X,U)^m / K(U)` be projective of rank `q` near every point.

For the kernel of `φ` that quotient is `Γ(X,U)^m / ker φ_U`, which the first isomorphism
theorem identifies with the *image* of `φ_U`.  So the condition splits into exactly the two
inputs one expects:

* `φ` is **surjective on sections** over the affine opens in question — for
  `φ : 𝒪_T^m ⟶ π_*(F(d))` this is global generation, and holds for `d ≫ 0`;
* `M` is **locally free of rank `q`** there — for `π_*(F(d))` this is
  `Scheme.Modules.isProjectiveOfRank_pushforward_of_globalSections`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.quotientProjectiveOfRank_kernelSubmoduleSheafData` — the
  general form, taking the two inputs on a common affine open per point;
* `AlgebraicGeometry.Scheme.Modules.quotientProjectiveOfRank_kernel_of_isProjectiveOfRank` —
  the form actually used, from `IsProjectiveOfRank` plus surjectivity on every affine open;
* `AlgebraicGeometry.Scheme.Modules.kernelGrassmannianPoint` — the resulting element of
  `grassmannianFunctor q m`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- **The kernel data is a point of the Grassmannian**, given surjectivity on sections and
local freeness of `M` on a common affine open through each point.

`Γ(X,U)^m / ker φ_U ≃ₗ Γ(M,U)` by the first isomorphism theorem, and both `Module.Projective`
and `Module.rankAtStalk` transport along that equivalence. -/
theorem quotientProjectiveOfRank_kernelSubmoduleSheafData
    {X : Scheme.{u}} {m q : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Function.Surjective (finFreeSectionsMap' φ U.1) ∧
      Module.Projective ↥Γ(X, U.1) ↥Γ(M, U.1) ∧
      ∀ p : PrimeSpectrum ↥Γ(X, U.1), Module.rankAtStalk ↥Γ(M, U.1) p = q) :
    (kernelSubmoduleSheafData φ).QuotientProjectiveOfRank q := by
  intro x
  obtain ⟨U, hxU, hsurj, hproj, hrank⟩ := h x
  refine ⟨U, hxU, ?_, ?_⟩
  · exact Module.Projective.of_equiv
      (LinearMap.quotKerEquivOfSurjective _ hsurj).symm
  · intro p
    change Module.rankAtStalk
      ((Fin m → ↥Γ(X, U.1)) ⧸ LinearMap.ker (finFreeSectionsMap' φ U.1)) p = q
    rw [Module.rankAtStalk_eq_of_equiv (LinearMap.quotKerEquivOfSurjective _ hsurj)]
    exact hrank p

/-- **The kernel data is a point of the Grassmannian**, from local freeness of `M` and
surjectivity of `φ` on sections over every affine open. -/
theorem quotientProjectiveOfRank_kernel_of_isProjectiveOfRank
    {X : Scheme.{u}} {m q : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (hM : IsProjectiveOfRank q M)
    (hsurj : ∀ U : X.affineOpens, Function.Surjective (finFreeSectionsMap' φ U.1)) :
    (kernelSubmoduleSheafData φ).QuotientProjectiveOfRank q :=
  quotientProjectiveOfRank_kernelSubmoduleSheafData φ fun x => by
    obtain ⟨U, hxU, _hfin, hproj, hrank⟩ := hM x
    exact ⟨U, hxU, hsurj U, hproj, hrank⟩

/-- **The `X`-point of `Gr(q, m)` attached to `φ : 𝒪_X^m ⟶ M`.** -/
def kernelGrassmannianPoint {X : Scheme.{u}} {m q : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (hM : IsProjectiveOfRank q M)
    (hsurj : ∀ U : X.affineOpens, Function.Surjective (finFreeSectionsMap' φ U.1)) :
    (grassmannianFunctor q m).obj (op X) :=
  ⟨kernelSubmoduleSheafData φ,
    quotientProjectiveOfRank_kernel_of_isProjectiveOfRank φ hM hsurj⟩

end AlgebraicGeometry.Scheme.Modules
