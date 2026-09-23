module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The pentagon for restriction versus pullback of sheaves of modules

Supporting API with no Stacks Project counterpart.

`Scheme.Modules.restrictFunctorIsoPullback` identifies restriction along an open
immersion with the abstract inverse image, through uniqueness of left adjoints. This
file proves the compatibility of that identification with composition of open
immersions — the pentagon relating `restrictFunctorIsoPullback`, `pullbackComp` and
`restrictFunctorComp` — which is the missing coherence in §2.2.3's
`normalizedAmbientIso_comp`.

Main declarations:
- `Modules.restrictFunctorIsoPullback_comp_inv_app`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

set_option maxHeartbeats 1600000 in
-- the adjunction-uniqueness reductions unfold heavy functor composites
/-- The pentagon: transporting the composite of the restrict-vs-pullback
identifications along composition agrees with the composition identifications on
both sides. -/
lemma restrictFunctorIsoPullback_comp_inv_app (M : Z.Modules) :
    (restrictFunctorIsoPullback f).inv.app ((pullback g).obj M) ≫
      (restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app M) =
    (pullbackComp f g).hom.app M ≫
      (restrictFunctorIsoPullback (f ≫ g)).inv.app M ≫
      (restrictFunctorComp f g).hom.app M := by
  refine (((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)).homEquiv M
      ((restrictFunctor g ⋙ restrictFunctor f).obj M)).injective ?_
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  have hu : ∀ {W W' : Scheme.{u}} (h : W ⟶ W') [IsOpenImmersion h]
      (x : W'.Modules),
      (pullbackPushforwardAdjunction h).unit.app x ≫
        (pushforward h).map ((restrictFunctorIsoPullback h).inv.app x) =
      (restrictAdjunction h).unit.app x := by
    intro W W' h _ x
    exact Adjunction.unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction h) (restrictAdjunction h) x
  -- reduce the left-hand transpose to the restrict-side units
  have hLHS : ((pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f)).unit.app M ≫
      (pushforward f ⋙ pushforward g).map
        ((restrictFunctorIsoPullback f).inv.app ((pullback g).obj M) ≫
          (restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app M)) =
      (restrictAdjunction g).unit.app M ≫
        (pushforward g).map ((restrictAdjunction f).unit.app
          ((restrictFunctor g).obj M)) := by
    rw [show ((pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f)).unit.app M =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app
          ((pullback g).obj M)) from by
        simp [Adjunction.comp]]
    rw [Functor.comp_map, Functor.map_comp, Functor.map_comp]
    slice_lhs 2 3 => rw [← Functor.map_comp, hu f ((pullback g).obj M)]
    slice_lhs 2 3 => rw [← Functor.map_comp,
      show (restrictAdjunction f).unit.app ((pullback g).obj M) ≫
          (pushforward f).map ((restrictFunctor f).map
            ((restrictFunctorIsoPullback g).inv.app M)) =
        (restrictFunctorIsoPullback g).inv.app M ≫
          (restrictAdjunction f).unit.app ((restrictFunctor g).obj M) from
        ((restrictAdjunction f).unit.naturality _).symm,
      Functor.map_comp]
    slice_lhs 1 2 => rw [hu g M]
  rw [hLHS]
  -- expand the right-hand transpose
  rw [Functor.map_comp, Functor.map_comp]
  -- the mate identity for `pullbackComp`
  have hconj := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at hconj
  -- isolate the composite unit
  have hunit : ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)).unit.app M =
      (pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app M) ≫
        (pushforwardComp f g).inv.app ((pullback g ⋙ pullback f).obj M) := by
    rw [← Category.assoc, ← hconj, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [hunit]
  -- collapse the conjugation round-trip
  slice_rhs 3 4 => rw [← (pushforwardComp f g).inv.naturality]
  slice_rhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [show 𝟙 ((pushforward (f ≫ g)).obj ((pullback (f ≫ g)).obj M)) ≫
      (pushforwardComp f g).inv.app ((pullback (f ≫ g)).obj M) ≫
      (pushforward f ⋙ pushforward g).map
        ((restrictFunctorIsoPullback (f ≫ g)).inv.app M) ≫
      (pushforward f ⋙ pushforward g).map ((restrictFunctorComp f g).hom.app M) =
    (pushforwardComp f g).inv.app ((pullback (f ≫ g)).obj M) ≫
      (pushforward f ⋙ pushforward g).map
        ((restrictFunctorIsoPullback (f ≫ g)).inv.app M) ≫
      (pushforward f ⋙ pushforward g).map ((restrictFunctorComp f g).hom.app M) from
    Category.id_comp _]
  rw [← NatTrans.naturality_assoc (pushforwardComp f g).inv
    ((restrictFunctorIsoPullback (f ≫ g)).inv.app M)]
  have hu' : ∀ {W W' : Scheme.{u}} (h : W ⟶ W') [IsOpenImmersion h]
      (x : W'.Modules) {T : W'.Modules}
      (t : (pushforward h).obj ((restrictFunctor h).obj x) ⟶ T),
      (pullbackPushforwardAdjunction h).unit.app x ≫
        (pushforward h).map ((restrictFunctorIsoPullback h).inv.app x) ≫ t =
      (restrictAdjunction h).unit.app x ≫ t := by
    intro W W' h _ x T t
    rw [← Category.assoc, hu h x]
  rw [hu' (f ≫ g) M]
  refine Modules.hom_ext _ _ fun U ↦ ?_
  simp only [Modules.Hom.comp_app, Functor.comp_map, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_inv_app_app,
    restrictFunctorComp_hom_app_app]
  refine Eq.trans ?_ ((congrArg (fun t ↦ M.presheaf.map
    (homOfLE ((f ≫ g).image_preimage_le U)).op ≫ t) (Category.id_comp _)).symm)
  rw [restrict_map]
  exact ((M.presheaf.map_comp _ _).symm.trans
    (congrArg M.presheaf.map (Subsingleton.elim _ _))).trans
    (M.presheaf.map_comp _ _)

end AlgebraicGeometry.Scheme.Modules
