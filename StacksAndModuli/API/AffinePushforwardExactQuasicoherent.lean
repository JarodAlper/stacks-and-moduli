module

public import StacksAndModuli.API.AffinePushforwardQuasicoherent
public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Exactness of affine pushforward on quasicoherent modules

Pushforward of arbitrary sheaves along an affine morphism need not be exact.  On
quasicoherent module sheaves it is exact: locally on an affine open of the target,
surjectivity reduces to surjectivity on global sections of an affine scheme.

## Main results

* `AlgebraicGeometry.Scheme.Modules.appTop_surjective_of_epi_of_isAffine`:
  an epimorphism between quasicoherent modules on an affine scheme is surjective on
  global sections.
* `AlgebraicGeometry.Scheme.Modules.epi_map_pushforward_of_isAffineHom`:
  affine pushforward preserves epimorphisms between quasicoherent modules.
* `AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_isAffineHom`:
  affine pushforward preserves short exact sequences of quasicoherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : Scheme.{u}}

/-- The sections over the top open of a restriction along an open immersion identify
with sections over any chosen open equal to the image of that immersion. -/
noncomputable def restrictTopSectionsIsoOfRangeEq
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsOpenImmersion i]
    (U : T.Opens) (hU : i.opensRange = U) (M : T.Modules) :
    Γ((restrictFunctor i).obj M, ⊤) ≅ Γ(M, U) :=
  M.restrictAppIso i ⊤ ≪≫
    M.presheaf.mapIso
      (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op

/-- The top-sections comparison for restriction is natural in the module sheaf. -/
theorem restrictTopSectionsIsoOfRangeEq_naturality
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsOpenImmersion i]
    (U : T.Opens) (hU : i.opensRange = U)
    {M N : T.Modules} (g : M ⟶ N) :
    ((restrictFunctor i).map g).app ⊤ ≫
        (restrictTopSectionsIsoOfRangeEq i U hU N).hom =
      (restrictTopSectionsIsoOfRangeEq i U hU M).hom ≫ g.app U := by
  have hr :
      ((restrictFunctor i).map g).app ⊤ ≫ (N.restrictAppIso i ⊤).hom =
        (M.restrictAppIso i ⊤).hom ≫ g.app (i ''ᵁ ⊤) := by
    rfl
  have hn :
      g.app (i ''ᵁ ⊤) ≫ N.presheaf.map
          (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op.hom =
        M.presheaf.map
            (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op.hom ≫
          g.app U := by
    change g.mapPresheaf.app (op (i ''ᵁ ⊤)) ≫
        N.presheaf.map
            (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op.hom =
      M.presheaf.map
          (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op.hom ≫
        g.mapPresheaf.app (op U)
    exact (g.mapPresheaf.naturality
      (eqToIso (i.image_top_eq_opensRange.trans hU).symm).op.hom).symm
  dsimp only [restrictTopSectionsIsoOfRangeEq]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hr, Category.assoc, hn, ← Category.assoc]

/-- An epimorphism between quasicoherent module sheaves on an affine scheme is
surjective on global sections. -/
theorem appTop_surjective_of_epi_of_isAffine (Z : Scheme.{u}) [IsAffine Z]
    {M N : Z.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (g : M ⟶ N) [Epi g] :
    Function.Surjective (g.app ⊤).hom := by
  let e : Spec Γ(Z, ⊤) ⟶ Z := Z.isoSpec.inv
  let g' := (restrictFunctor e).map g
  let _ : Epi g' := by dsimp [g']; infer_instance
  let _ : ((restrictFunctor e).obj M).IsQuasicoherent := by infer_instance
  let _ : ((restrictFunctor e).obj N).IsQuasicoherent := by infer_instance
  have hsurj :=
    AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_map_surjective_of_epi g'
  change Function.Surjective (g'.app ⊤).hom at hsurj
  have hrange : e.opensRange = ⊤ := Scheme.Hom.opensRange_of_isIso e
  let eM := restrictTopSectionsIsoOfRangeEq e ⊤ hrange M
  let eN := restrictTopSectionsIsoOfRangeEq e ⊤ hrange N
  have hn : g'.app ⊤ ≫ eN.hom = eM.hom ≫ g.app ⊤ := by
    exact restrictTopSectionsIsoOfRangeEq_naturality e ⊤ hrange g
  intro y
  obtain ⟨x', hx'⟩ := hsurj (eN.inv y)
  refine ⟨eM.hom x', ?_⟩
  have hnx := ConcreteCategory.congr_hom hn x'
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hx'] at hnx
  exact hnx.symm.trans (eN.inv_hom_id_apply y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along an affine morphism preserves epimorphisms between
quasicoherent module sheaves. -/
theorem epi_map_pushforward_of_isAffineHom (f : X ⟶ Y) [IsAffineHom f]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (g : M ⟶ N) [Epi g] : Epi ((pushforward f).map g) := by
  let G := (SheafOfModules.toSheaf Y.ringCatSheaf).map
    ((pushforward f).map g)
  have hG : Epi G := by
    rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro V s y hyV
    obtain ⟨_, ⟨U, hUaff, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
    let W : X.Opens := f ⁻¹ᵁ U
    let i : W.toScheme ⟶ X := W.ι
    let _ : IsOpenImmersion i := by dsimp [i]; infer_instance
    let g' := (restrictFunctor i).map g
    let _ : PreservesFiniteColimits (restrictFunctor i) := by infer_instance
    let _ : Epi g' := by
      dsimp [g']
      infer_instance
    let hW : IsAffineOpen W := IsAffineHom.isAffine_preimage U hUaff
    let _ : IsAffine W.toScheme := hW
    let _ : ((restrictFunctor i).obj M).IsQuasicoherent := by infer_instance
    let _ : ((restrictFunctor i).obj N).IsQuasicoherent := by infer_instance
    have hsurj := show Function.Surjective (g'.app ⊤).hom from
      appTop_surjective_of_epi_of_isAffine W.toScheme g'
    have hirange : i.opensRange = W := by dsimp [i]; simp
    let eM := restrictTopSectionsIsoOfRangeEq i W hirange M
    let eN := restrictTopSectionsIsoOfRangeEq i W hirange N
    let sU : Γ(N, W) :=
      N.presheaf.map ((Opens.map f.base).map (homOfLE hUV)).op s
    obtain ⟨r, hr⟩ := hsurj (eN.inv sU)
    let rU : Γ(M, W) := eM.hom r
    have hn : g'.app ⊤ ≫ eN.hom = eM.hom ≫ g.app W := by
      exact restrictTopSectionsIsoOfRangeEq_naturality i W hirange g
    have hrU : g.app W rU = sU := by
      have hnr := ConcreteCategory.congr_hom hn r
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hr] at hnr
      exact hnr.symm.trans (eN.inv_hom_id_apply sU)
    refine ⟨U, hUV, ⟨rU, ?_⟩, hyU⟩
    change g.app W rU =
      N.presheaf.map ((Opens.map f.base).map (homOfLE hUV)).op s
    exact hrU
  constructor
  intro Z a b hab
  apply (SheafOfModules.toSheaf Y.ringCatSheaf).map_injective
  apply (cancel_epi G).1
  simpa [G] using congrArg
    (fun q ↦ (SheafOfModules.toSheaf Y.ringCatSheaf).map q) hab

/-- Pushforward along an affine morphism preserves short exact sequences whose
three terms are quasicoherent module sheaves. -/
theorem shortExact_map_pushforward_of_isAffineHom (f : X ⟶ Y) [IsAffineHom f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] : (S.map (pushforward f)).ShortExact := by
  let _ : Mono S.f := hS.mono_f
  let _ : Epi S.g := hS.epi_g
  let _ : Epi ((S.map (pushforward f)).g) := by
    exact epi_map_pushforward_of_isAffineHom f S.g
  let _ : Mono ((S.map (pushforward f)).f) := by
    change Mono ((pushforward f).map S.f)
    exact preserves_mono_of_preservesLimit (pushforward f) S.f
  let hExact := hS.exact.map_of_mono_of_preservesKernel
    (pushforward f) (by infer_instance) (by infer_instance)
  exact ShortComplex.ShortExact.mk' hExact (by infer_instance) (by infer_instance)

end

end AlgebraicGeometry.Scheme.Modules
