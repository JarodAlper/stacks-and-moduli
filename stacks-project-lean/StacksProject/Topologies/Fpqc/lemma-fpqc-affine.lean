module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sieves

/-!
# An fpqc covering of an affine scheme is refined by a finite affine one

Stacks Project tag **022E**, label `topologies-lemma-fpqc-affine`, in `topologies.tex`,
§`022A` (The fpqc topology).

> Let `T` be an affine scheme. Let `{T_i → T}_{i ∈ I}` be an fpqc covering of `T`. Then there
> exists an fpqc covering `{U_j → T}_{j = 1, …, n}` which is a refinement of `{T_i → T}` such
> that each `U_j` is an affine scheme. Moreover, we may choose each `U_j` to be open affine in
> one of the `T_i`.

The Stacks proof is a single line — *"This follows directly from the definition"* — but the
definition it follows from (`022B`, `topologies-definition-fpqc-covering`) is exactly the
quasi-compactness condition: over the affine `T`, finitely many quasi-compact opens of the `T_i`
already cover. Mathlib packages that condition as `QuasiCompactCover` (which it tags
`@[stacks 022B]`), so the work is in extracting a finite affine family from it and checking the
result is again an fpqc covering.

This is the keystone of the whole "local properties" development: the general
local-on-the-target machinery of Stacks `02KP`/`0349` routes through it, and in this repository
it is what `part3.1.2-descent-quasi-coherent` needs in order to reduce an arbitrary fpqc
covering of an affine to a finite affine one.

Mathlib has the Zariski analogue (`Scheme.OpenCover.affineRefinement`) and the cover-density
tool `Scheme.isCoverDense_toOver_Spec`, but neither is instantiated at `@Flat`/fpqc.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

/-- **Stacks 022E** (`topologies-lemma-fpqc-affine`). An fpqc covering of an affine scheme is
refined by a finite family of affine schemes, flat over the base, which is itself an fpqc
covering. -/
@[stacks 022E]
theorem exists_finite_affine_refinement_of_mem_fpqcPrecoverage {S : Scheme.{u}} [IsAffine S]
    {R : Presieve S} (hR : R ∈ Scheme.fpqcPrecoverage.coverings S) :
    ∃ (n : ℕ) (X : Fin n → Scheme.{u}) (p : ∀ i, X i ⟶ S),
      (∀ i, IsAffine (X i)) ∧ (∀ i, Flat (p i)) ∧
        (∀ i, (Sieve.generate R).arrows (p i)) ∧
        Presieve.ofArrows X p ∈ Scheme.fpqcPrecoverage.coverings S := by
  classical
  -- split the fpqc membership into its quasi-compact and flat parts
  have hqc : R ∈ Scheme.qcPrecoverage S := hR.1
  have hflat : R ∈ Scheme.precoverage @Flat S := hR.2
  -- present the covering by a quasi-compact pre-`0`-hypercover
  obtain ⟨E, hEqc, hEeq⟩ := PreZeroHypercoverFamily.mem_precoverage_iff.mp hqc
  haveI hqcE : QuasiCompactCover E := hEqc
  -- assemble the flat cover on the same underlying hypercover
  let 𝒰 : S.Cover (Scheme.precoverage @Flat) := ⟨E, by rw [← hEeq]; exact hflat⟩
  haveI : QuasiCompactCover 𝒰.toPreZeroHypercover := hqcE
  -- refine by a finite affine cover
  obtain ⟨𝒱, φ, hfin, -⟩ := QuasiCompactCover.exists_hom (P := @Flat) 𝒰
  haveI : Finite 𝒱.I₀ := hfin
  letI : Fintype 𝒱.I₀ := Fintype.ofFinite _
  let e : Fin (Fintype.card 𝒱.I₀) ≃ 𝒱.I₀ := (Fintype.equivFin 𝒱.I₀).symm
  refine ⟨Fintype.card 𝒱.I₀, fun i ↦ Spec (𝒱.X (e i)), fun i ↦ 𝒱.f (e i),
    fun i ↦ inferInstance, fun i ↦ 𝒱.map_prop (e i), ?_, ?_⟩
  · intro i
    refine ⟨_, φ.h₀ (e i), 𝒰.f (φ.s₀ (e i)), ?_, φ.w₀ (e i)⟩
    rw [hEeq]
    exact ⟨φ.s₀ (e i)⟩
  · -- the finite affine family is itself an fpqc covering
    have hofeq : Presieve.ofArrows (fun i ↦ Spec (𝒱.X (e i))) (fun i ↦ 𝒱.f (e i)) =
        Presieve.ofArrows (fun j ↦ Spec (𝒱.X j)) 𝒱.f := by
      funext T
      ext g
      constructor
      · rintro ⟨i⟩
        exact ⟨e i⟩
      · rintro ⟨j⟩
        have hj : e (e.symm j) = j := e.apply_symm_apply j
        exact hj ▸ ⟨e.symm j⟩
    rw [hofeq]
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff
      (E := 𝒱.cover.toPreZeroHypercover).mpr inferInstance, 𝒱.cover.mem₀⟩

end AlgebraicGeometry.Scheme
