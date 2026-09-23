module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Flat base change of scheme-theoretic images

This file proves that the scheme-theoretic image of a quasi-compact morphism
commutes with flat base change.  The proof uses flat stability of
scheme-theoretically dominant morphisms and therefore avoids a separate
quasi-coherent pushforward base-change theorem.
-/

@[expose] public section

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- The canonical map from a quasi-compact morphism to its scheme-theoretic
image is scheme-theoretically dominant. -/
instance Scheme.Hom.toImage_isSchemeTheoreticallyDominant
    (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let U' (U : Y.affineOpens) : f.image.affineOpens :=
    ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U'
  · exact f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  · intro U
    rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

/-- The kernel ideal of the second projection from the base change of a
quasi-compact morphism along a flat morphism is the pulled-back kernel ideal. -/
lemma Scheme.Hom.ker_pullback_snd_of_flat (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [Flat g] :
    (pullback.snd f g).ker = f.ker.comap g := by
  let a : pullback f g ⟶ pullback f.imageι g :=
    pullback.map f g f.imageι g f.toImage (𝟙 _) (𝟙 _)
      (by simp) (by simp)
  have ha : IsPullback a (pullback.fst f g)
      (pullback.fst f.imageι g) f.toImage := by
    exact .of_right (t := .flip <| .of_hasPullback f.imageι g)
      (by simpa [a] using (.flip <| .of_hasPullback f g)) (by cat_disch)
  have ha' : IsSchemeTheoreticallyDominant a :=
    IsSchemeTheoreticallyDominant.of_isPullback ha.flip
  calc
    (pullback.snd f g).ker = (a ≫ pullback.snd f.imageι g).ker := by
      congr 1
      simp [a]
    _ = a.ker.map (pullback.snd f.imageι g) := Scheme.Hom.ker_comp _ _
    _ = (pullback.snd f.imageι g).ker := by
      rw [ha'.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    _ = f.imageι.ker.comap g := by
      calc
        (pullback.snd f.imageι g).ker =
            ((pullbackSymmetry f.imageι g).hom ≫
              pullback.fst g f.imageι).ker := by
          congr 1
          rw [pullbackSymmetry_hom_comp_fst]
        _ = (pullback.fst g f.imageι).ker :=
          Scheme.Hom.ker_comp_of_isIso _ _
        _ = f.imageι.ker.comap g :=
          Scheme.IdealSheafData.ker_fst_of_isClosedImmersion f.imageι g
    _ = f.ker.comap g := by rw [Scheme.IdealSheafData.ker_subschemeι]

/-- The kernel ideal of the first projection from a flat base change of a
quasi-compact morphism is the pulled-back kernel ideal. -/
lemma Scheme.Hom.ker_pullback_fst_of_flat (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [QuasiCompact g] :
    (pullback.fst f g).ker = g.ker.comap f := by
  calc
    (pullback.fst f g).ker =
        ((pullbackSymmetry f g).hom ≫ pullback.snd g f).ker := by
      congr 1
      rw [pullbackSymmetry_hom_comp_snd]
    _ = (pullback.snd g f).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = g.ker.comap f := Scheme.Hom.ker_pullback_snd_of_flat g f

/-- Equal ideal sheaves define canonically isomorphic closed subschemes. -/
noncomputable def Scheme.IdealSheafData.subschemeIsoOfEq
    {I J : Scheme.IdealSheafData X} (h : I = J) :
    I.subscheme ≅ J.subscheme where
  hom := Scheme.IdealSheafData.inclusion h.ge
  inv := Scheme.IdealSheafData.inclusion h.le
  hom_inv_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    simp
  inv_hom_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    simp

/-- The isomorphism of closed subschemes induced by equality of ideal sheaves
commutes with their inclusions into the ambient scheme. -/
@[reassoc]
lemma Scheme.IdealSheafData.subschemeIsoOfEq_hom_subschemeι
    {I J : Scheme.IdealSheafData X} (h : I = J) :
    (Scheme.IdealSheafData.subschemeIsoOfEq h).hom ≫ J.subschemeι =
      I.subschemeι := by
  exact Scheme.IdealSheafData.inclusion_subschemeι h.ge

/-- The scheme-theoretic image of a quasi-compact morphism commutes with flat
base change. -/
noncomputable def Scheme.Hom.imagePullbackIsoOfFlat
    (f : X ⟶ S) (g : Y ⟶ S) [Flat f] [QuasiCompact g] :
    (pullback.fst f g).image ≅ pullback f g.imageι :=
  Scheme.IdealSheafData.subschemeIsoOfEq
      (Scheme.Hom.ker_pullback_fst_of_flat f g) ≪≫ g.ker.comapIso f

/-- The flat-base-change isomorphism for scheme-theoretic images commutes with
the closed immersions into the base-changed target. -/
@[reassoc]
lemma Scheme.Hom.imagePullbackIsoOfFlat_hom_fst
    (f : X ⟶ S) (g : Y ⟶ S) [Flat f] [QuasiCompact g] :
    (f.imagePullbackIsoOfFlat g).hom ≫ pullback.fst f g.imageι =
      (pullback.fst f g).imageι := by
  rw [Scheme.Hom.imagePullbackIsoOfFlat, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst,
    Scheme.IdealSheafData.subschemeIsoOfEq_hom_subschemeι]

/-- Under the flat-base-change isomorphism for scheme-theoretic images, the
map to the image is the canonical pullback map. -/
@[reassoc]
lemma Scheme.Hom.toImage_imagePullbackIsoOfFlat_hom
    (f : X ⟶ S) (g : Y ⟶ S) [Flat f] [QuasiCompact g] :
    (pullback.fst f g).toImage ≫ (f.imagePullbackIsoOfFlat g).hom =
      pullback.map f g f g.imageι (𝟙 _) g.toImage (𝟙 _)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp [Scheme.Hom.imagePullbackIsoOfFlat_hom_fst]
  · rw [← cancel_mono g.imageι]
    calc
      (pullback.fst f g).toImage ≫ (f.imagePullbackIsoOfFlat g).hom ≫
          pullback.snd f g.imageι ≫ g.imageι =
          (pullback.fst f g).toImage ≫ (f.imagePullbackIsoOfFlat g).hom ≫
            pullback.fst f g.imageι ≫ f := by rw [pullback.condition]
      _ = (pullback.fst f g).toImage ≫
          (pullback.fst f g).imageι ≫ f := by
        rw [Scheme.Hom.imagePullbackIsoOfFlat_hom_fst_assoc]
      _ = pullback.fst f g ≫ f := by
        rw [Scheme.Hom.toImage_imageι_assoc]
      _ = pullback.snd f g ≫ g := pullback.condition
      _ = (pullback.map f g f g.imageι (𝟙 _) g.toImage (𝟙 _)
          (by simp) (by simp) ≫ pullback.snd f g.imageι) ≫
            g.imageι := by simp

end AlgebraicGeometry
