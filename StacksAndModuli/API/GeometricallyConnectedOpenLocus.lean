module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The maximal geometrically connected open locus

For a morphism of schemes `f : X ⟶ Y`, this file constructs the largest open subset
of `Y` over which the restriction of `f` is geometrically connected.  The construction
only uses that geometric connectedness is Zariski-local on the target: take the supremum
of all opens with geometrically connected restriction, then glue the property across
that open cover.

This construction deliberately does not assert that a point belongs to this open merely
because its geometric fibre is connected.  That converse is the geometric openness
theorem proved by Stein factorization for proper, finitely presented families; it is a
separate input.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Hom.geometricallyConnectedFiberSet`: the set of target
  points whose geometric fibres are connected.
* `AlgebraicGeometry.Scheme.Hom.geometricallyConnectedOpenLocus`: the largest open over
  which a morphism is geometrically connected.
* `AlgebraicGeometry.Scheme.Hom.geometricallyConnected_restrict_openLocus`: the
  restriction to this open is geometrically connected.
* `AlgebraicGeometry.Scheme.Hom.le_geometricallyConnectedOpenLocus`: every open with
  geometrically connected restriction is contained in the maximal one.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Geometric connectedness is Zariski-local on the target. -/
instance GeometricallyConnected.instIsZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @GeometricallyConnected := by
  rw [GeometricallyConnected.eq_geometrically]
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restricting `f` first to `V` and then along an inclusion `U ≤ V` gives the
pullback square formed by the direct restriction to `U`. -/
lemma isPullback_morphismRestrict_of_le {U V : Y.Opens} (hUV : U ≤ V) :
    IsPullback (f ∣_ U) (X.homOfLE (f.preimage_mono hUV))
      (Y.homOfLE hUV) (f ∣_ V) := by
  apply IsOpenImmersion.isPullback
  · exact (morphismRestrict_homOfLE f U V hUV).symm
  · rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
    ext x
    change ((f ∣_ V) x).1 ∈ U ↔ f x.1 ∈ U
    rw [morphismRestrict_base_coe]

/-- Geometric connectedness remains true after restricting to a smaller target open. -/
lemma geometricallyConnected_restrict_of_le {U V : Y.Opens}
    (hV : GeometricallyConnected (f ∣_ V)) (hUV : U ≤ V) :
    GeometricallyConnected (f ∣_ U) :=
  IsZariskiLocalAtTarget.of_isPullback
    (f.isPullback_morphismRestrict_of_le hUV).flip hV

/-- The set of target points whose fibres are geometrically connected. -/
def geometricallyConnectedFiberSet : Set Y :=
  {y | GeometricallyConnected (f.fiberToSpecResidueField y)}

/-- A morphism is geometrically connected exactly when every point lies in its
geometrically connected fibre set. -/
lemma geometricallyConnected_iff_fiberSet_eq_univ :
    GeometricallyConnected f ↔ f.geometricallyConnectedFiberSet = Set.univ := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  simp [geometricallyConnectedFiberSet, Set.eq_univ_iff_forall]

/-- Passing to a target open does not change whether the geometric fibre at a point is
connected. -/
lemma geometricallyConnected_fiber_morphismRestrict_iff
    (U : Y.Opens) (y : U.toScheme) :
    GeometricallyConnected ((f ∣_ U).fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (U.ι y)) := by
  let h := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f U).flip y
  let e : (f ∣_ U).fiber y ⟶ f.fiber (U.ι y) :=
    pullback.map _ _ _ _ (f ⁻¹ᵁ U).ι
      (Spec.map (U.ι.residueFieldMap y)) U.ι
      (isPullback_morphismRestrict f U).w
      (U.ι.SpecMap_residueFieldMap_fromSpecResidueField y).symm
  have he : IsIso e := h.isIso_fst_of_isIso
  let _ : IsIso e := he
  calc
    GeometricallyConnected ((f ∣_ U).fiberToSpecResidueField y) ↔
        GeometricallyConnected
          ((f ∣_ U).fiberToSpecResidueField y ≫
            Spec.map (U.ι.residueFieldMap y)) :=
      (MorphismProperty.cancel_right_of_respectsIso
        (P := @GeometricallyConnected) _ _).symm
    _ ↔ GeometricallyConnected
          (e ≫ f.fiberToSpecResidueField (U.ι y)) := by rw [h.w]
    _ ↔ GeometricallyConnected (f.fiberToSpecResidueField (U.ι y)) :=
      MorphismProperty.cancel_left_of_respectsIso
        (P := @GeometricallyConnected) _ _

/-- A restriction is geometrically connected exactly when its target open is contained
in the geometrically connected fibre set. -/
lemma geometricallyConnected_restrict_iff_subset_fiberSet (U : Y.Opens) :
    GeometricallyConnected (f ∣_ U) ↔
      (U : Set Y) ⊆ f.geometricallyConnectedFiberSet := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  constructor
  · intro h y hy
    exact (f.geometricallyConnected_fiber_morphismRestrict_iff U ⟨y, hy⟩).mp
      (h ⟨y, hy⟩)
  · intro h y
    exact (f.geometricallyConnected_fiber_morphismRestrict_iff U y).mpr
      (h y.2)

/-- The largest open subset of the target over which `f` is geometrically connected.

It is defined as the supremum of all opens `U` for which `f ∣_ U` is geometrically
connected. -/
noncomputable def geometricallyConnectedOpenLocus : Y.Opens :=
  ⨆ U : {U : Y.Opens // GeometricallyConnected (f ∣_ U)}, U.1

/-- Every open over which `f` is geometrically connected lies in the maximal
geometrically connected open locus. -/
lemma le_geometricallyConnectedOpenLocus (U : Y.Opens)
    (hU : GeometricallyConnected (f ∣_ U)) :
    U ≤ f.geometricallyConnectedOpenLocus :=
  le_iSup (fun V : {V : Y.Opens // GeometricallyConnected (f ∣_ V)} ↦ V.1) ⟨U, hU⟩

/-- The restriction of `f` to its maximal geometrically connected open locus is
geometrically connected. -/
theorem geometricallyConnected_restrict_openLocus :
    GeometricallyConnected (f ∣_ f.geometricallyConnectedOpenLocus) := by
  let I := {U : Y.Opens // GeometricallyConnected (f ∣_ U)}
  let V : I → Y.Opens := fun U ↦ U.1
  let W : Y.Opens := ⨆ U, V U
  change GeometricallyConnected (f ∣_ W)
  let 𝒰 : W.toScheme.OpenCover := Scheme.Opens.iSupOpenCover V
  refine IsZariskiLocalAtTarget.of_openCover
    (P := @GeometricallyConnected) 𝒰 ?_
  change ∀ U : I,
    GeometricallyConnected (pullback.snd (f ∣_ W)
      (Y.homOfLE (le_iSup V U)))
  intro U
  let hU : V U ≤ W := le_iSup V U
  let iX : (f ⁻¹ᵁ V U).toScheme ⟶ (f ⁻¹ᵁ W).toScheme :=
    X.homOfLE (f.preimage_mono hU)
  let iY : (V U).toScheme ⟶ W.toScheme := Y.homOfLE hU
  have hsquare : IsPullback (f ∣_ V U) iX iY (f ∣_ W) :=
    f.isPullback_morphismRestrict_of_le hU
  change GeometricallyConnected (pullback.snd (f ∣_ W) iY)
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) hsquare.flip.isoPullback.hom]
  rw [hsquare.flip.isoPullback_hom_snd]
  exact U.2

/-- The maximal geometrically connected open locus is contained in the exact
geometrically connected fibre set. -/
lemma coe_geometricallyConnectedOpenLocus_subset_fiberSet :
    (f.geometricallyConnectedOpenLocus : Set Y) ⊆
      f.geometricallyConnectedFiberSet :=
  (f.geometricallyConnected_restrict_iff_subset_fiberSet
    f.geometricallyConnectedOpenLocus).mp
      f.geometricallyConnected_restrict_openLocus

/-- If the exact geometrically connected fibre set is open, then it is precisely the
maximal geometrically connected open locus.  Thus the geometric content of openness is
isolated from the formal construction of the open subscheme. -/
lemma coe_geometricallyConnectedOpenLocus_eq_fiberSet
    (hopen : IsOpen f.geometricallyConnectedFiberSet) :
    (f.geometricallyConnectedOpenLocus : Set Y) =
      f.geometricallyConnectedFiberSet := by
  apply Set.Subset.antisymm
  · exact f.coe_geometricallyConnectedOpenLocus_subset_fiberSet
  · let U : Y.Opens := ⟨f.geometricallyConnectedFiberSet, hopen⟩
    have hU : GeometricallyConnected (f ∣_ U) :=
      (f.geometricallyConnected_restrict_iff_subset_fiberSet U).mpr Set.Subset.rfl
    exact show (U : Set Y) ⊆ f.geometricallyConnectedOpenLocus from
      f.le_geometricallyConnectedOpenLocus U hU

/-- An open is contained in the maximal geometrically connected open locus if and only
if the restriction of `f` to that open is geometrically connected. -/
lemma le_geometricallyConnectedOpenLocus_iff (U : Y.Opens) :
    U ≤ f.geometricallyConnectedOpenLocus ↔
      GeometricallyConnected (f ∣_ U) := by
  constructor
  · intro hU
    exact f.geometricallyConnected_restrict_of_le
      f.geometricallyConnected_restrict_openLocus hU
  · exact f.le_geometricallyConnectedOpenLocus U

/-- The maximal geometrically connected open locus is the whole target exactly when
`f` itself is geometrically connected. -/
lemma geometricallyConnectedOpenLocus_eq_top_iff :
    f.geometricallyConnectedOpenLocus = ⊤ ↔ GeometricallyConnected f := by
  constructor
  · intro h
    have hf := f.geometricallyConnected_restrict_openLocus
    rw [h] at hf
    apply IsZariskiLocalAtTarget.of_iSup_eq_top
      (P := @GeometricallyConnected) (fun _ : PUnit.{u} ↦ (⊤ : Y.Opens)) (by simp)
    intro _
    exact hf
  · intro hf
    exact top_unique (f.le_geometricallyConnectedOpenLocus ⊤ (by
      simpa using IsZariskiLocalAtTarget.restrict hf ⊤))

end AlgebraicGeometry.Scheme.Hom
