module

public import StacksAndModuli.API.AffineFiberRepresentationCriterion
public import StacksAndModuli.API.QuotientGeometricPresentation
public import StacksAndModuli.API.RelativePresheafOver
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.6-criterion-for-sheaf-to-be-scheme»

/-!
# Affine presentations of quotient stacks

If the source map of a groupoid is representable by affine morphisms, then the
canonical map from its object presheaf to a local stackification of the quotient
prestack is representable by affine morphisms.  The proof constructs a small sheaf
for each fiber, identifies its pullback along a surjective étale cover with the
affine local quotient chart, and applies effective descent for affine schemes.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {G : PresheafGroupoid.{u}}
  {Xst : BasedCategory.{v₂, u₂} Scheme.{u}}
  {i : BasedFunctor G.quotientPrestack Xst}

/-- An affine groupoid source makes the canonical quotient presentation
representable by affine morphisms. -/
theorem relativelyRepresentableWith_isAffineHom_quotientPresentation_of_isLocalStackification
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i)
    (hU : Presieve.IsSheaf Scheme.etaleTopology G.U)
    (hs : MorphismProperty.presheaf
      (@IsAffineHom : MorphismProperty Scheme.{u}) G.s) :
    (G.quotientPresentation.comp i).RelativelyRepresentableWith
      (@IsAffineHom : MorphismProperty Scheme.{u}) := by
  let _ : Xst.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  let _ : BasedCategory.IsStack Scheme.etaleTopology Xst := hi.isStack
  let A := G.quotientPresentation.comp i
  let hUz : Presieve.IsSheaf Scheme.zariskiTopology G.U :=
    Presieve.isSheaf_of_le G.U
      Scheme.zariskiTopology_le_etaleTopology hU
  let hglue : CoproductLiftsGlue (i := i) :=
    coproductLiftsGlue_of_isStack hi.isStack hUz
  let D := fun (T : Scheme.{u}) (g : BasedFunctor (overBased T) Xst) ↦
    etaleLocalFiberChart_of_coproductLiftsGlue hi hglue hU hs T g
  apply BasedFunctor.relativelyRepresentableWith_isAffineHom_of_goodRepresentations A
  intro T g
  let d := D T g
  let E := d.fiber.representation
  let _ : E.toFunctor.IsEquivalence := d.fiber.representation_isEquivalence
  let p := d.fiber.localMap
  let _ : Etale p := d.fiber.localMap_etale
  let _ : Surjective p := d.fiber.localMap_surjective
  let eta := representedFiberSecondBaseMap A g E
  let L := representedFiberSecondBaseChangeRepresentation A g E p
  let K := d.chart
  let _ : K.toFunctor.IsEquivalence := d.chart_isEquivalence
  let K' := (ofPresheafYonedaToOverBased d.W).comp K
  let _ : K'.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (ofPresheafYonedaToOverBased d.W).toFunctor K.toFunctor
  let e := ofPresheaf.comparisonIso L K'
  let k := (K.comp (fiberProductSnd A ((overBased.map p).comp g))).overHom
  have he : e.hom ≫ pullback.snd eta (yoneda.map p) = yoneda.map k := by
    rw [← representedFiberSecondBaseMap_baseChangeRepresentation A g E p]
    exact comparisonIso_hom_comp_representedFiberSecondBaseMap A
      ((overBased.map p).comp g) L K
  let eOver : Over.mk (yoneda.map k) ≅
      Over.mk (pullback.snd eta (yoneda.map p)) :=
    Over.isoMk e he
  let eLocal : yoneda.obj (Over.mk k) ≅
      (Over.map p).op ⋙ Presheaf.relativeOver eta :=
    Presheaf.relativeOverYonedaIso (Over.mk k) ≪≫
      Presheaf.relativeOverMapIso eOver ≪≫
        Presheaf.relativeOverPullbackIso p eta
  let Frel : Sheaf (Scheme.etaleTopology.over T) (Type u) :=
    ⟨Presheaf.relativeOver eta,
      (isSheaf_iff_isSheaf_of_type _ _).2
        (Presheaf.relativeOver_isSheaf Scheme.etaleTopology eta
          d.fiber.isSheaf)⟩
  have hLocal :
      (Scheme.etaleTopology.representableByProperty
        (@IsAffineHom : MorphismProperty Scheme.{u})).prop
          (.mk (op d.fiber.localBase))
          ((Scheme.etaleTopology.overMapPullback (Type u) p).obj Frel) := by
    refine ⟨Over.mk k, d.chart_property, ⟨?_⟩⟩
    exact eLocal
  obtain ⟨Z, hZAffine, ⟨eZ⟩⟩ :=
    MorphismProperty.presheaf_isAffineHom_of_pullback p Frel hLocal
  let eArrow := Presheaf.relativeOverRepresentationArrowIso eta Z eZ
  let eSource : yoneda.obj Z.left ⟶ d.fiber.X := eArrow.hom.left
  let Q : BasedFunctor (overBased Z.left) (fiberProduct A g) :=
    (overBasedToOfPresheafYoneda Z.left).comp
      ((ofPresheaf.map eSource).comp E)
  have hQ : Q.toFunctor.IsEquivalence := by
    let _ : (ofPresheaf.map eSource).toFunctor.IsEquivalence := inferInstance
    let _ : ((ofPresheaf.map eSource).comp E).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans (ofPresheaf.map eSource).toFunctor E.toFunctor
    exact Functor.isEquivalence_trans
      (overBasedToOfPresheafYoneda Z.left).toFunctor
      ((ofPresheaf.map eSource).comp E).toFunctor
  let _ : Q.toFunctor.IsEquivalence := hQ
  let Q' := (ofPresheafYonedaToOverBased Z.left).comp Q
  let _ : Q'.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (ofPresheafYonedaToOverBased Z.left).toFunctor Q.toFunctor
  let ec := ofPresheaf.comparisonIso E Q'
  let qstruct := (Q.comp (fiberProductSnd A g)).overHom
  have hc : ec.hom ≫ eta = yoneda.map qstruct := by
    exact comparisonIso_hom_comp_representedFiberSecondBaseMap A g E Q
  have hSource : eSource ≫ eta = yoneda.map Z.hom := by
    have hw := eArrow.hom.w
    change eSource ≫ eta = yoneda.map Z.hom ≫ eArrow.hom.right at hw
    simpa only [show eArrow.hom.right = 𝟙 (yoneda.obj T) from rfl,
      Category.comp_id] using hw
  let aNat : yoneda.obj Z.left ⟶ yoneda.obj Z.left :=
    ec.hom ≫ CategoryTheory.inv eSource
  let a : Z.left ⟶ Z.left := yonedaEquiv aNat
  have haMap : yoneda.map a = aNat := yoneda_map_yonedaEquiv aNat
  let _ : IsIso aNat := inferInstance
  let _ : IsIso (yoneda.map a) := haMap ▸ inferInstance
  let _ : IsIso a := isIso_of_reflects_iso a yoneda
  have hqstruct : qstruct = a ≫ Z.hom := by
    apply yoneda.map_injective
    calc
      yoneda.map qstruct = ec.hom ≫ eta := hc.symm
      _ = (ec.hom ≫ CategoryTheory.inv eSource) ≫
          (eSource ≫ eta) := by simp
      _ = yoneda.map a ≫ yoneda.map Z.hom := by rw [haMap, hSource]
      _ = yoneda.map (a ≫ Z.hom) := by rw [yoneda.map_comp]
  let _ : IsAffineHom Z.hom := hZAffine
  have hqAffine : IsAffineHom qstruct := by
    rw [hqstruct]
    infer_instance
  exact ⟨Z.left, Q, hQ, hqAffine⟩

end AlgebraicGeometry.PresheafGroupoid
