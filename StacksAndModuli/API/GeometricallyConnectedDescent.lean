module

public import StacksAndModuli.API.EtaleTargetLocal
public import StacksAndModuli.API.GeometricallyConnectedOpenLocus
public import StacksAndModuli.«Section3.1-Descent».«part3.1.5-descending-properties»

/-!
# Descent of geometric connectedness

Geometric connectedness descends through an arbitrary surjective base change.  Given a
field-valued point of the original base, pull back the surjective cover and choose a point
above it.  The residue field of that point gives a field-valued point upstairs.  The
corresponding geometric fiber is connected by hypothesis and maps surjectively to the
original fiber, which is therefore connected.

Combining this with fpqc-sieve descent gives target-locality for arbitrary étale covers.

## Main declarations

- `AlgebraicGeometry.geometricallyConnected_descendsAlong_surjective`
- `AlgebraicGeometry.Scheme.geometricallyConnected_isLocalAtTarget_etalePrecoverage`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Geometric connectedness descends through arbitrary surjective base change. -/
instance geometricallyConnected_descendsAlong_surjective :
    MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (@Surjective : MorphismProperty Scheme.{u}) := by
  let _ : MorphismProperty.RespectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfg
  let _ : Surjective f := hf
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms] at hfg ⊢
  intro K _ y
  let T := pullback f y
  let p : T ⟶ Spec (CommRingCat.of K) := pullback.snd f y
  let _ : Surjective p := by
    dsimp only [p]
    infer_instance
  obtain ⟨t⟩ : Nonempty T := by
    obtain ⟨t, -⟩ := p.surjective (Nonempty.some inferInstance)
    exact ⟨t⟩
  let a : Spec (T.residueField t) ⟶ T := T.fromSpecResidueField t
  let x : Spec (T.residueField t) ⟶ X := a ≫ pullback.fst f y
  let k : Spec (T.residueField t) ⟶ Spec (CommRingCat.of K) := a ≫ p
  have hx' : ConnectedSpace ↥(pullback (pullback.fst f g) x) :=
    hfg (T.residueField t) x
  let _ : ConnectedSpace ↥(pullback (pullback.fst f g) x) := hx'
  have hx : ConnectedSpace ↥(pullback x (pullback.fst f g)) :=
    (pullbackSymmetry (pullback.fst f g) x).hom.homeomorph.surjective.connectedSpace
      (pullbackSymmetry (pullback.fst f g) x).hom.continuous
  have hxf : x ≫ f = k ≫ y := by
    dsimp only [x, k, p]
    simp only [Category.assoc, pullback.condition]
  let _ : ConnectedSpace ↥(pullback x (pullback.fst f g)) := hx
  have hbase : ConnectedSpace ↥(pullback (x ≫ f) g) :=
    (pullbackRightPullbackFstIso f g x).hom.homeomorph.surjective.connectedSpace
      (pullbackRightPullbackFstIso f g x).hom.continuous
  rw [hxf] at hbase
  let _ : ConnectedSpace ↥(pullback (k ≫ y) g) := hbase
  let _ : Surjective k := by
    constructor
    intro z
    exact ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩
  have htarget : ConnectedSpace ↥(pullback y g) :=
    (k.precompBaseChangeMap y g).surjective.connectedSpace
      (k.precompBaseChangeMap y g).continuous
  let _ : ConnectedSpace ↥(pullback y g) := htarget
  exact (pullbackSymmetry y g).hom.homeomorph.surjective.connectedSpace
    (pullbackSymmetry y g).hom.continuous

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Geometric connectedness is local at the target for arbitrary étale covering
families. -/
theorem geometricallyConnected_isLocalAtTarget_etalePrecoverage :
    MorphismProperty.IsLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      etalePrecoverage := by
  let _ : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.DescendsAlong.of_le
      (P := (@GeometricallyConnected : MorphismProperty Scheme.{u}))
      (Q := (@Surjective : MorphismProperty Scheme.{u}))
      (W := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (fun _ _ _ h ↦ h.1.1)
  exact isLocalAtTarget_etalePrecoverage_of_descendsAlong _

end AlgebraicGeometry.Scheme
