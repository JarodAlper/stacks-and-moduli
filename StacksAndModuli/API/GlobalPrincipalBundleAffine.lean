module

public import StacksAndModuli.API.GlobalPrincipalBundle
public import StacksAndModuli.API.RepresentableSheafProperty
public import StacksAndModuli.API.SchemeRepresentableSheafDescent

/-!
# Affineness of principal-bundle projections

An fppf principal bundle under an affine group scheme has affine projection.
The self-pullback of the bundle is identified by the torsor isomorphism with
the base change of the group.  Affineness then descends along the fppf bundle
projection.  The theorem is parameterized by the geometric locality instance
for affine representability, so this API remains independent of Chapter 3's
linear-order files.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G T : Over S} [GrpObj G]

/-- A principal bundle under an affine group scheme has affine projection,
provided affine representability is known to be fppf-local. -/
theorem GlobalPrincipalBundle.isAffineHom_projection [IsAffineHom G.hom]
    [Pseudofunctor.ObjectProperty.IsLocal
      (fppfTopology.representableByProperty
        (@IsAffineHom : MorphismProperty Scheme.{u})) fppfTopology]
    (B : GlobalPrincipalBundle G T) : IsAffineHom B.p.left := by
  let Q : MorphismProperty Scheme.{u} :=
    @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation
  letI : MorphismProperty.DescendsAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) Q :=
    fppfTopology.representableByProperty_descendsAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) Q (fun f hf => by
        letI : Surjective f := hf.1.1
        letI : Flat f := hf.1.2
        letI : LocallyOfFinitePresentation f := hf.2
        exact generate_singleton_mem_fppfTopology_of_fppf f)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (Q := Q) (f := B.p.left) (g := B.p.left)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · let e : (Limits.pullback B.p B.p).left ≅
        Limits.pullback B.p.left B.p.left :=
      PreservesPullback.iso (Over.forget S) B.p B.p
    let t := ModObj.torsorMap B.p B.invariant
    letI : IsIso t.left := by
      refine ⟨⟨(inv t).left, ?_, ?_⟩⟩
      · exact congrArg Over.Hom.left (IsIso.hom_inv_id t)
      · exact congrArg Over.Hom.left (IsIso.inv_hom_id_assoc t (𝟙 _))
    have hcomp : IsAffineHom
        (t.left ≫ e.hom ≫ pullback.snd B.p.left B.p.left) := by
      rw [show e.hom ≫ pullback.snd B.p.left B.p.left =
        (pullback.snd B.p B.p).left from
          PreservesPullback.iso_hom_snd (Over.forget S) B.p B.p]
      rw [show t = ModObj.torsorMap B.p B.invariant from rfl,
        ← Over.comp_left, ModObj.torsorMap_snd]
      change IsAffineHom (pullback.snd G.hom B.P.hom)
      exact MorphismProperty.pullback_snd
        (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
        G.hom B.P.hom inferInstance
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
      (t.left ≫ e.hom) (pullback.snd B.p.left B.p.left)).mp hcomp

end AlgebraicGeometry.Scheme
