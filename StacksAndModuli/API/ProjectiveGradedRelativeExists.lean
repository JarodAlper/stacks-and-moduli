module

public import StacksAndModuli.API.ProjectiveGradedRelativeGlobGen
public import StacksAndModuli.API.ProjectiveGradedCohomologyExists
public import StacksAndModuli.API.ProjectiveGradedBaseChange

/-!
# The relative cohomology of `ℙⁿ_R` exists

Supporting API with no Stacks Project counterpart: the construction discharging
`RelativeCohomology.nonempty` for a noetherian base ring `R`.

Everything is the graded Čech complex of the standard affine cover, now over `R` rather than
over a field:

* `Hgr M i := M.cechHgr i`, with the long exact sequence from `API/ProjectiveGradedCech.lean`;
* `IsCoherent := GradedModule.IsFG` with its closure properties
  (`API/ProjectiveGradedCoherent.lean`, which holds over any noetherian ring);
* `IsFlat := GradedModule.IsFlat`, degreewise flatness (`API/ProjectiveGradedFlat.lean`);
* `fibre κ := Cohomology.cech κ`, the absolute theory of W1;
* Serre finiteness and vanishing over `R` (`API/ProjectiveGradedSerre.lean`);
* Cohomology and Base Change (`API/ProjectiveGradedRelativeCBC.lean`).

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.RelativeCohomology.cech`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open CategoryTheory GradedModule TensorProduct

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- **The relative graded Čech cohomology of `ℙⁿ_R`**, for a noetherian ring `R`. -/
noncomputable def RelativeCohomology.cech : RelativeCohomology R where
  Hgr M i := M.cechHgr i
  IsCoherent M := GradedModule.IsFG M
  IsFlat M := GradedModule.IsFlat M
  fibre κ := Cohomology.cech κ
  fibre_hasInfiniteBaseChange κ := Cohomology.hasInfiniteBaseChange_cech κ
  isCoherent_fibre _ hM κ := IsFG.baseChange κ hM
  isCoherent_structureModule := GradedModule.isFG_structureModule
  isCoherent_twist := fun hM a => hM.twist a
  isCoherent_pow := fun hM r => hM.pow r
  isCoherent_coker := fun f _ hN => IsFG.coker f hN
  isCoherent_of_injective := fun f hf hN => IsFG.of_injective f hf hN
  isFlat_structureModule := GradedModule.isFlat_structureModule
  isFlat_twist := fun hM a => hM.twist a
  isFlat_pow := fun hM r => hM.pow r
  isFlat_of_shortExact := fun h hN hP => IsFlat.of_shortExact h hN hP
  uniform_serre_vanishing M hM hflat := by
    obtain ⟨d₀, hd₀⟩ := exists_uniform_subsingleton_cechHgr_baseChange hM hflat
    exact ⟨d₀, fun κ _ _ i hi d hd => hd₀ κ i hi d hd⟩
  CommutesWithBaseChange M d := ∀ (A : Type u) [CommRing A] [Algebra R A],
    Nonempty ((A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A] (((M.baseChange A).cechHgr 0).obj d))
  baseChangeIso M d h κ := ((h κ).some).toModuleIso
  IsGloballyGenerated M d := ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e → (M.cechHgr 0).mulSpan d e = ⊤
  map φ i := cechHgrMap φ i
  δ h i d := cechδ h i d
  exact_map_δ h i d := cech_exact_map_δ h i d
  shortExact_fibre h hP κ := shortExact_baseChangeMap h hP κ
  cbc M d hM hflat hfib :=
    ⟨fun i hi => subsingleton_cechHgr_of_fibrewise M d hM hflat hfib i hi,
      finiteDimensional_cechHgr_of_isFG M hM 0 d,
      projective_cechHgr_zero hM hflat hfib,
      fun A _ _ => ⟨cechHgrZeroBaseChangeEquiv hM hflat hfib A⟩⟩
  isGloballyGenerated_of_fibres M d hM hflat hvan hfib :=
    isGloballyGenerated_of_fibres_cech hM hflat
      (fun κ _ _ e hde i hi => hvan κ e hde i hi)
      (fun κ _ _ e hde => hfib κ e hde)

/-- **The relative cohomology of families on `ℙⁿ_R` exists**, for a noetherian ring `R`. -/
theorem RelativeCohomology.nonempty (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Nonempty (RelativeCohomology R) :=
  ⟨RelativeCohomology.cech R⟩

end AlgebraicGeometry.ProjectiveSpace

end
