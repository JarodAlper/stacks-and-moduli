module

public import StacksAndModuli.API.ChartAtlasFunctor
public import StacksAndModuli.API.OpenCoverMonoLift
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Affine charts of a closed subscheme

An ideal sheaf `I` on `X` is assembled from the affine closed schemes
`Spec (Γ(U, 𝒪_X) ⧸ I(U))`.  This file records the corresponding functorial universal
property: a morphism to `X` factors through `I.subschemeι` exactly when it locally
factors through those affine closed charts.

The forward implication uses the canonical affine open cover of `I.subscheme`.  The
reverse implication glues the local lifts through the monomorphism `I.subschemeι`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The affine closed chart `Spec (Γ(U)/I(U))`, regarded as an object over `X`. -/
noncomputable def IdealSheafData.affineChart (I : X.IdealSheafData)
    (U : X.affineOpens) : Over X :=
  Over.mk (I.glueDataObjι U ≫ U.1.ι)

namespace IdealSheafData

variable (I : X.IdealSheafData)

/-- The closed subscheme itself, regarded as an object over its ambient scheme. -/
noncomputable def subschemeOver : Over X :=
  Over.mk I.subschemeι

/-- The canonical map from an affine closed chart into the global closed subscheme. -/
noncomputable def affineChartToSubscheme (U : X.affineOpens) :
    I.affineChart U ⟶ I.subschemeOver :=
  Over.homMk (I.subschemeCover.f U) (I.subschemeCover_map_subschemeι U)

@[simp]
lemma affineChartToSubscheme_left (U : X.affineOpens) :
    (I.affineChartToSubscheme U).left = I.subschemeCover.f U :=
  rfl

/-- The global closed subscheme locally factors through its affine closed charts. -/
lemma locallyFactors_affineChart_subschemeOver :
    LocallyFactors I.affineChart I.subschemeOver := by
  intro x
  let U := I.subschemeCover.idx x
  let V : Over X := I.affineChart U
  let k : V ⟶ I.subschemeOver := I.affineChartToSubscheme U
  refine ⟨V, k, ?_, ?_, U, 𝟙 V.left, ?_⟩
  · change IsOpenImmersion (I.subschemeCover.f U)
    exact I.subschemeCover.map_prop U
  · exact I.subschemeCover.covers x
  · simp [V]

/-- A morphism locally factoring through the affine closed charts factors through the
global closed subscheme. -/
lemma exists_subschemeLift_of_locallyFactors
    {W : Scheme.{u}} (g : W ⟶ X)
    (h : LocallyFactors I.affineChart (Over.mk g)) :
    ∃ k : W ⟶ I.subscheme, k ≫ I.subschemeι = g := by
  choose V j hj hx U a ha using h
  let 𝒰 : W.OpenCover :=
    openCoverOfMaps (fun x ↦ (V x).left) (fun x ↦ (j x).left) hj
      (fun x ↦ ⟨x, (hx x).choose, (hx x).choose_spec⟩)
  let k : ∀ x, 𝒰.X x ⟶ I.subscheme :=
    fun x ↦ a x ≫ I.subschemeCover.f (U x)
  apply exists_lift_of_openCover I.subschemeι g 𝒰
  intro x
  refine ⟨k x, ?_⟩
  change (a x ≫ I.subschemeCover.f (U x)) ≫ I.subschemeι =
    (j x).left ≫ g
  rw [Category.assoc, I.subschemeCover_map_subschemeι]
  exact (ha x).trans (Over.w (j x)).symm

/-- A morphism factors through a closed subscheme exactly when it locally factors
through the canonical affine closed charts. -/
lemma locallyFactors_affineChart_iff_exists_subschemeLift
    {W : Scheme.{u}} (g : W ⟶ X) :
    LocallyFactors I.affineChart (Over.mk g) ↔
      ∃ k : W ⟶ I.subscheme, k ≫ I.subschemeι = g := by
  constructor
  · exact I.exists_subschemeLift_of_locallyFactors g
  · rintro ⟨k, hk⟩
    let φ : Over.mk g ⟶ I.subschemeOver := Over.homMk k hk
    exact LocallyFactors.comp φ I.locallyFactors_affineChart_subschemeOver

end IdealSheafData

end AlgebraicGeometry.Scheme
