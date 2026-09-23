module

public import StacksAndModuli.API.PullbackPushforwardCounitIsoTransport
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Base change of epimorphic pullback--pushforward evaluation

For an arbitrary commutative square of schemes, the canonical pushforward base-change
morphism is defined as the mate of the pullback of the original evaluation counit.  The
adjunction triangle therefore factors that pulled-back evaluation through the evaluation
on the new source.  Consequently relative global generation is preserved by arbitrary
base change; invertibility of the pushforward base-change morphism is not needed.

The final forms transport the pulled-back module through an epimorphism, or through a chosen
isomorphism as a convenient corollary.  This is the interface used when the kernel of a
normalized base-changed presentation is an epimorphic image of the pulled-back old kernel.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical pushforward base-change mate followed by the new evaluation is the
pullback of the old evaluation, up to the structural pullback isomorphisms. -/
@[reassoc]
lemma pullback_pushforwardBaseChangeHomOfComm_comp_counit
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules) :
    (pullback p').map (pushforwardBaseChangeHomOfComm p p' g G h M) ≫
        (pullbackPushforwardAdjunction p').counit.app ((pullback G).obj M) =
      (pullbackComp p' g).hom.app ((pushforward p).obj M) ≫
        (pullbackCongr h.symm).hom.app ((pushforward p).obj M) ≫
        (pullbackComp G p).inv.app ((pushforward p).obj M) ≫
        (pullback G).map ((pullbackPushforwardAdjunction p).counit.app M) := by
  let k := (pullbackComp p' g).hom.app ((pushforward p).obj M) ≫
    (pullbackCongr h.symm).hom.app ((pushforward p).obj M) ≫
    (pullbackComp G p).inv.app ((pushforward p).obj M) ≫
    (pullback G).map ((pullbackPushforwardAdjunction p).counit.app M)
  change (pullback p').map
      ((pullbackPushforwardAdjunction p').homEquiv _ _ k) ≫
        (pullbackPushforwardAdjunction p').counit.app ((pullback G).obj M) = k
  exact ((pullbackPushforwardAdjunction p').homEquiv_counit _ _
    ((pullbackPushforwardAdjunction p').homEquiv _ _ k)).symm.trans
      (Equiv.symm_apply_apply _ k)

/-- An epimorphic pullback--pushforward evaluation remains epimorphic after arbitrary
base change around a commutative square.  No cartesianness and no Cohomology-and-Base-Change
isomorphism are required. -/
theorem pullbackPushforwardCounit_epi_pullback_of_comm
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules)
    [Epi ((pullbackPushforwardAdjunction p).counit.app M)] :
    Epi ((pullbackPushforwardAdjunction p').counit.app ((pullback G).obj M)) := by
  let bc := pushforwardBaseChangeHomOfComm p p' g G h M
  let e := ((pullbackComp p' g).app ((pushforward p).obj M)).trans
    (((pullbackCongr h.symm).app ((pushforward p).obj M)).trans
      ((pullbackComp G p).symm.app ((pushforward p).obj M)))
  haveI : Epi ((pullback G).map
      ((pullbackPushforwardAdjunction p).counit.app M)) := Functor.map_epi _ _
  haveI : Epi (e.hom ≫ (pullback G).map
      ((pullbackPushforwardAdjunction p).counit.app M)) := epi_comp _ _
  have heq : (pullback p').map bc ≫
        (pullbackPushforwardAdjunction p').counit.app ((pullback G).obj M) =
      e.hom ≫ (pullback G).map
        ((pullbackPushforwardAdjunction p).counit.app M) := by
    exact pullback_pushforwardBaseChangeHomOfComm_comp_counit p p' g G h M
  haveI : Epi ((pullback p').map bc ≫
      (pullbackPushforwardAdjunction p').counit.app ((pullback G).obj M)) :=
    heq ▸ inferInstance
  exact epi_of_epi ((pullback p').map bc) _

/-- Relative global generation descends from the pulled-back module to any epimorphic
quotient on the new source. -/
theorem pullbackPushforwardCounit_epi_of_epi_pullback_of_comm
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules) (M' : X'.Modules)
    (e : (pullback G).obj M ⟶ M') [Epi e]
    [Epi ((pullbackPushforwardAdjunction p).counit.app M)] :
    Epi ((pullbackPushforwardAdjunction p').counit.app M') := by
  haveI : Epi ((pullbackPushforwardAdjunction p').counit.app
      ((pullback G).obj M)) :=
    pullbackPushforwardCounit_epi_pullback_of_comm p p' g G h M
  haveI : Epi ((pullbackPushforwardAdjunction p').counit.app
      ((pullback G).obj M) ≫ e) := epi_comp _ _
  have hn := (pullbackPushforwardAdjunction p').counit.naturality e
  haveI : Epi ((pullback p').map ((pushforward p').map e) ≫
      (pullbackPushforwardAdjunction p').counit.app M') := hn ▸ inferInstance
  exact epi_of_epi ((pullback p').map ((pushforward p').map e)) _

/-- Relative global generation survives arbitrary base change after identifying the
pulled-back module with the normalized module on the new source. -/
theorem pullbackPushforwardCounit_epi_of_iso_pullback_of_comm
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules) (M' : X'.Modules)
    (e : (pullback G).obj M ≅ M')
    [Epi ((pullbackPushforwardAdjunction p).counit.app M)] :
    Epi ((pullbackPushforwardAdjunction p').counit.app M') := by
  haveI : Epi ((pullbackPushforwardAdjunction p').counit.app
      ((pullback G).obj M)) :=
    pullbackPushforwardCounit_epi_pullback_of_comm p p' g G h M
  exact CategoryTheory.Adjunction.epi_counit_of_iso _ e.symm

end AlgebraicGeometry.Scheme.Modules

end

end
