module

public import StacksAndModuli.API.OverPullbackDescentCartesian
public import StacksAndModuli.API.SchemeRelationSaturation

/-!
# Kernel-pair relations from scheme-arrow descent data

This file extracts the internal equivalence relation carried by coherent descent data
for scheme arrows. Given an arrow of the indexing sieve, the associated cartesian
diagram over its double and triple overlaps supplies the identity, inverse, and
composition maps on its kernel-pair relation object.

The construction is phrased through the cartesian-arrow functor associated to the
descent datum.  Consequently the three relation laws follow from ordinary functoriality,
without unfolding the coherence maps of the pullback pseudofunctor.

## Main definitions

- `AlgebraicGeometry.OverPullbackDescent.kernelPairDescentRelationOfFunctor`: the
  internal kernel-pair equivalence relation attached to a selected sieve arrow in a
  coherent descent datum, constructed through its cartesian-arrow functor.
- `AlgebraicGeometry.OverPullbackDescent.kernelPairDescentRelation`: the canonical
  kernel-pair relation attached to a coherent descent datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.OverPullbackDescent

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {R : Sieve S}
variable (D : Data (R := R))
variable (q : R.arrows.category)

/-- The kernel-pair overlap of a selected arrow, regarded as another object of the
indexing sieve. -/
noncomputable abbrev kernelPairObj : R.arrows.category :=
  R.arrows.categoryMk
    (pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom)
    (R.downward_closed q.property (pullback.fst q.obj.hom q.obj.hom))

/-- The first kernel-pair projection as a map in the sieve category. -/
def kernelPairFst : kernelPairObj q ⟶ q :=
  ⟨Over.homMk (pullback.fst q.obj.hom q.obj.hom)⟩

/-- The second kernel-pair projection as a map in the sieve category. -/
def kernelPairSnd : kernelPairObj q ⟶ q :=
  ⟨Over.homMk (pullback.snd q.obj.hom q.obj.hom) pullback.condition.symm⟩

/-- The total space assigned by the descent datum to the kernel-pair overlap. -/
abbrev kernelPairTotal : Scheme.{u} := (D.obj (kernelPairObj q)).left

/-- The transition on total spaces over the first kernel-pair projection. -/
def kernelPairSourceRaw : kernelPairTotal D q ⟶ (D.obj q).left :=
  ((cartesianFunctor D).map (kernelPairFst q)).left

/-- The transition on total spaces over the second kernel-pair projection. -/
def kernelPairTargetRaw : kernelPairTotal D q ⟶ (D.obj q).left :=
  ((cartesianFunctor D).map (kernelPairSnd q)).left

/-- The raw source transition is a pullback square. -/
lemma kernelPairSourceRaw_isPullback :
    IsPullback (kernelPairSourceRaw D q) (D.obj (kernelPairObj q)).hom
      (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) :=
  ((cartesianFunctor D).map (kernelPairFst q)).isPullback

/-- The raw target transition is a pullback square. -/
lemma kernelPairTargetRaw_isPullback :
    IsPullback (kernelPairTargetRaw D q) (D.obj (kernelPairObj q)).hom
      (D.obj q).hom (pullback.snd q.obj.hom q.obj.hom) :=
  ((cartesianFunctor D).map (kernelPairSnd q)).isPullback

/-- The canonical identification of the descent datum's overlap total space with the
standard kernel-pair relation object. -/
noncomputable def kernelPairSourceIso :
    kernelPairTotal D q ≅
      (D.obj q).hom.kernelPairRelationObject q.obj.hom :=
  (kernelPairSourceRaw_isPullback D q).isoPullback

/-- The source projection of `kernelPairSourceIso` is the raw source transition. -/
lemma kernelPairSourceIso_hom_fst :
    (kernelPairSourceIso D q).hom ≫
      pullback.fst (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) =
      kernelPairSourceRaw D q := by
  exact (kernelPairSourceRaw_isPullback D q).isoPullback_hom_fst

/-- The inverse of `kernelPairSourceIso` respects the overlap projection to the base. -/
lemma kernelPairSourceIso_inv_snd :
    (kernelPairSourceIso D q).inv ≫ (D.obj (kernelPairObj q)).hom =
      pullback.snd (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) := by
  exact (kernelPairSourceRaw_isPullback D q).isoPullback_inv_snd

/-- The inverse of `kernelPairSourceIso` followed by the raw source is the standard
source projection. -/
lemma kernelPairSourceIso_inv_fst :
    (kernelPairSourceIso D q).inv ≫ kernelPairSourceRaw D q =
      pullback.fst (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) := by
  exact (kernelPairSourceRaw_isPullback D q).isoPullback_inv_fst

/-- The kernel-pair descent isomorphism obtained by comparing the two cartesian
transitions out of the overlap object. -/
noncomputable def kernelPairAlpha :
    (Over.pullback (pullback.fst q.obj.hom q.obj.hom)).obj (D.obj q) ≅
      (Over.pullback (pullback.snd q.obj.hom q.obj.hom)).obj (D.obj q) :=
  Over.isoMk
    ((kernelPairSourceIso D q).symm ≪≫
      (kernelPairTargetRaw_isPullback D q).isoPullback)
    (by
      change ((kernelPairSourceIso D q).inv ≫
          (kernelPairTargetRaw_isPullback D q).isoPullback.hom) ≫
          pullback.snd (D.obj q).hom (pullback.snd q.obj.hom q.obj.hom) =
        pullback.snd (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom)
      rw [Category.assoc,
        (kernelPairTargetRaw_isPullback D q).isoPullback_hom_snd,
        kernelPairSourceIso_inv_snd])

/-- The target relation map is the raw second transition transported across the
canonical source identification. -/
lemma kernelPairRelationTarget_eq :
    (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) =
      (kernelPairSourceIso D q).inv ≫ kernelPairTargetRaw D q := by
  dsimp [Scheme.Hom.kernelPairRelationTarget, kernelPairAlpha]
  change ((kernelPairSourceIso D q).inv ≫
      (kernelPairTargetRaw_isPullback D q).isoPullback.hom) ≫
      pullback.fst (D.obj q).hom (pullback.snd q.obj.hom q.obj.hom) = _
  rw [Category.assoc,
    (kernelPairTargetRaw_isPullback D q).isoPullback_hom_fst]

/-- The diagonal into the kernel pair of the selected sieve arrow. -/
noncomputable def kernelPairDiagonal : q.obj.left ⟶ pullback q.obj.hom q.obj.hom :=
  pullback.lift (f := q.obj.hom) (g := q.obj.hom) (𝟙 _) (𝟙 _) (by simp)

/-- The diagonal as a morphism from the selected sieve arrow to its overlap. -/
def kernelPairUnitMap : q ⟶ kernelPairObj q :=
  ⟨Over.homMk (kernelPairDiagonal q) (by
    change kernelPairDiagonal q ≫
      (pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom) = q.obj.hom
    rw [← Category.assoc, show kernelPairDiagonal q ≫
      pullback.fst q.obj.hom q.obj.hom = 𝟙 _ from pullback.lift_fst _ _ _,
      Category.id_comp])⟩

/-- The total-space map induced by the diagonal in the sieve. -/
def kernelPairUnitRaw : (D.obj q).left ⟶ kernelPairTotal D q :=
  ((cartesianFunctor D).map (kernelPairUnitMap q)).left

/-- The raw unit is a section of the raw source. -/
lemma kernelPairUnitRaw_source :
    kernelPairUnitRaw D q ≫ kernelPairSourceRaw D q = 𝟙 _ := by
  have h := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp (kernelPairUnitMap q) (kernelPairFst q))
  have hk : kernelPairUnitMap q ≫ kernelPairFst q = 𝟙 q := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hid := congrArg CartesianArrowHom.left ((cartesianFunctor D).map_id q)
  calc
    kernelPairUnitRaw D q ≫ kernelPairSourceRaw D q =
        (((cartesianFunctor D).map (kernelPairUnitMap q)) ≫
          ((cartesianFunctor D).map (kernelPairFst q))).left := rfl
    _ = ((cartesianFunctor D).map
          (kernelPairUnitMap q ≫ kernelPairFst q)).left := h.symm
    _ = ((cartesianFunctor D).map (𝟙 q)).left := by rw [hk]
    _ = CartesianArrowHom.left (𝟙 ((cartesianFunctor D).obj q)) := hid
    _ = 𝟙 _ := rfl

/-- The raw unit is a section of the raw target. -/
lemma kernelPairUnitRaw_target :
    kernelPairUnitRaw D q ≫ kernelPairTargetRaw D q = 𝟙 _ := by
  have h := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp (kernelPairUnitMap q) (kernelPairSnd q))
  have hk : kernelPairUnitMap q ≫ kernelPairSnd q = 𝟙 q := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have hid := congrArg CartesianArrowHom.left ((cartesianFunctor D).map_id q)
  calc
    kernelPairUnitRaw D q ≫ kernelPairTargetRaw D q =
        (((cartesianFunctor D).map (kernelPairUnitMap q)) ≫
          ((cartesianFunctor D).map (kernelPairSnd q))).left := rfl
    _ = ((cartesianFunctor D).map
          (kernelPairUnitMap q ≫ kernelPairSnd q)).left := h.symm
    _ = ((cartesianFunctor D).map (𝟙 q)).left := by rw [hk]
    _ = CartesianArrowHom.left (𝟙 ((cartesianFunctor D).obj q)) := hid
    _ = 𝟙 _ := rfl

/-- The identity-arrow map of the kernel-pair relation. -/
def kernelPairUnit :
    (D.obj q).left ⟶ (D.obj q).hom.kernelPairRelationObject q.obj.hom :=
  kernelPairUnitRaw D q ≫ (kernelPairSourceIso D q).hom

/-- The relation source of an identity arrow is the original point. -/
lemma kernelPairUnit_source :
    kernelPairUnit D q ≫
      (D.obj q).hom.kernelPairRelationSource q.obj.hom = 𝟙 _ := by
  change (kernelPairUnitRaw D q ≫ (kernelPairSourceIso D q).hom) ≫
    pullback.fst (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) = 𝟙 _
  rw [Category.assoc, kernelPairSourceIso_hom_fst,
    kernelPairUnitRaw_source]

/-- The relation target of an identity arrow is the original point. -/
lemma kernelPairUnit_target :
    kernelPairUnit D q ≫
      (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) = 𝟙 _ := by
  rw [kernelPairRelationTarget_eq]
  simp only [kernelPairUnit, Category.assoc, Iso.hom_inv_id_assoc,
    kernelPairUnitRaw_target]

/-- Transposition of the kernel pair as an endomorphism in the sieve category. -/
def kernelPairSwapMap : kernelPairObj q ⟶ kernelPairObj q :=
  ⟨Over.homMk (pullbackSymmetry q.obj.hom q.obj.hom).hom (by
    change (pullbackSymmetry q.obj.hom q.obj.hom).hom ≫
      (pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom) =
        pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullback.condition])⟩

/-- The total-space map induced by transposing the kernel pair. -/
def kernelPairInverseRaw : kernelPairTotal D q ⟶ kernelPairTotal D q :=
  ((cartesianFunctor D).map (kernelPairSwapMap q)).left

/-- Transposition followed by the first projection is the second projection. -/
lemma kernelPairSwapMap_fst :
    kernelPairSwapMap q ≫ kernelPairFst q = kernelPairSnd q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullbackSymmetry_hom_comp_fst _ _

/-- Transposition followed by the second projection is the first projection. -/
lemma kernelPairSwapMap_snd :
    kernelPairSwapMap q ≫ kernelPairSnd q = kernelPairFst q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullbackSymmetry_hom_comp_snd _ _

/-- The raw inverse exchanges source with target. -/
lemma kernelPairInverseRaw_source :
    kernelPairInverseRaw D q ≫ kernelPairSourceRaw D q =
      kernelPairTargetRaw D q := by
  have h := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp (kernelPairSwapMap q) (kernelPairFst q))
  calc
    kernelPairInverseRaw D q ≫ kernelPairSourceRaw D q =
        (((cartesianFunctor D).map (kernelPairSwapMap q)) ≫
          ((cartesianFunctor D).map (kernelPairFst q))).left := rfl
    _ = ((cartesianFunctor D).map
          (kernelPairSwapMap q ≫ kernelPairFst q)).left := h.symm
    _ = ((cartesianFunctor D).map (kernelPairSnd q)).left := by
      rw [kernelPairSwapMap_fst]
    _ = kernelPairTargetRaw D q := rfl

/-- The raw inverse exchanges target with source. -/
lemma kernelPairInverseRaw_target :
    kernelPairInverseRaw D q ≫ kernelPairTargetRaw D q =
      kernelPairSourceRaw D q := by
  have h := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp (kernelPairSwapMap q) (kernelPairSnd q))
  calc
    kernelPairInverseRaw D q ≫ kernelPairTargetRaw D q =
        (((cartesianFunctor D).map (kernelPairSwapMap q)) ≫
          ((cartesianFunctor D).map (kernelPairSnd q))).left := rfl
    _ = ((cartesianFunctor D).map
          (kernelPairSwapMap q ≫ kernelPairSnd q)).left := h.symm
    _ = ((cartesianFunctor D).map (kernelPairFst q)).left := by
      rw [kernelPairSwapMap_snd]
    _ = kernelPairSourceRaw D q := rfl

/-- The inversion map of the kernel-pair relation. -/
def kernelPairInverse :
    (D.obj q).hom.kernelPairRelationObject q.obj.hom ⟶
      (D.obj q).hom.kernelPairRelationObject q.obj.hom :=
  (kernelPairSourceIso D q).inv ≫ kernelPairInverseRaw D q ≫
    (kernelPairSourceIso D q).hom

/-- Inversion exchanges the relation source with its target. -/
lemma kernelPairInverse_source :
    kernelPairInverse D q ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom =
      (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) := by
  rw [kernelPairRelationTarget_eq]
  change ((kernelPairSourceIso D q).inv ≫ kernelPairInverseRaw D q ≫
      (kernelPairSourceIso D q).hom) ≫
      pullback.fst (D.obj q).hom (pullback.fst q.obj.hom q.obj.hom) = _
  rw [Category.assoc, Category.assoc, kernelPairSourceIso_hom_fst,
    kernelPairInverseRaw_source]

/-- Inversion exchanges the relation target with its source. -/
lemma kernelPairInverse_target :
    kernelPairInverse D q ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) =
      (D.obj q).hom.kernelPairRelationSource q.obj.hom := by
  rw [kernelPairRelationTarget_eq]
  change ((kernelPairSourceIso D q).inv ≫ kernelPairInverseRaw D q ≫
      (kernelPairSourceIso D q).hom) ≫
      ((kernelPairSourceIso D q).inv ≫ kernelPairTargetRaw D q) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    kernelPairInverseRaw_target]
  exact kernelPairSourceIso_inv_fst D q

/-- The base of two composable kernel-pair arrows. -/
noncomputable abbrev kernelPairTripleBase : Scheme.{u} :=
  pullback (pullback.snd q.obj.hom q.obj.hom)
    (pullback.fst q.obj.hom q.obj.hom)

/-- The twofold overlap indexing a composable pair, regarded as an object of the
sieve category. -/
noncomputable abbrev kernelPairTripleObj : R.arrows.category :=
  R.arrows.categoryMk
    ((pullback.fst (pullback.snd q.obj.hom q.obj.hom)
        (pullback.fst q.obj.hom q.obj.hom) ≫
      pullback.fst q.obj.hom q.obj.hom) ≫ q.obj.hom)
    (R.downward_closed q.property
      (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
          (pullback.fst q.obj.hom q.obj.hom) ≫
        pullback.fst q.obj.hom q.obj.hom))

/-- Projection from a composable pair to its first arrow. -/
def kernelPairTripleFstMap : kernelPairTripleObj q ⟶ kernelPairObj q :=
  ⟨Over.homMk
    (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom))⟩

/-- Projection from a composable pair to its second arrow. -/
def kernelPairTripleSndMap : kernelPairTripleObj q ⟶ kernelPairObj q :=
  ⟨Over.homMk
    (pullback.snd (pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom)) (by
      change
        pullback.snd (pullback.snd q.obj.hom q.obj.hom)
            (pullback.fst q.obj.hom q.obj.hom) ≫
          (pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom) =
        (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
            (pullback.fst q.obj.hom q.obj.hom) ≫
          pullback.fst q.obj.hom q.obj.hom) ≫ q.obj.hom
      have hPair := pullback.condition (f := q.obj.hom) (g := q.obj.hom)
      have hTriple := pullback.condition
        (f := pullback.snd q.obj.hom q.obj.hom)
        (g := pullback.fst q.obj.hom q.obj.hom)
      simpa only [Category.assoc] using
        ((hTriple.symm =≫ q.obj.hom).trans
          (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
            (pullback.fst q.obj.hom q.obj.hom) ≫= hPair.symm)))⟩

/-- The base map sending a composable pair `(s₁,s₂),(s₂,s₃)` to
`(s₁,s₃)`. -/
noncomputable def kernelPairTripleThirteenBase :
    kernelPairTripleBase q ⟶ pullback q.obj.hom q.obj.hom :=
  pullback.lift
    (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom) ≫
        pullback.fst q.obj.hom q.obj.hom)
    (pullback.snd (pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom) ≫
        pullback.snd q.obj.hom q.obj.hom)
    (by
      have hPair := pullback.condition (f := q.obj.hom) (g := q.obj.hom)
      have hTriple := pullback.condition
        (f := pullback.snd q.obj.hom q.obj.hom)
        (g := pullback.fst q.obj.hom q.obj.hom)
      simpa only [Category.assoc] using
        ((pullback.fst (pullback.snd q.obj.hom q.obj.hom)
              (pullback.fst q.obj.hom q.obj.hom) ≫= hPair).trans
          ((hTriple =≫ q.obj.hom).trans
            (pullback.snd (pullback.snd q.obj.hom q.obj.hom)
              (pullback.fst q.obj.hom q.obj.hom) ≫= hPair))))

/-- The first coordinate of the `(1,3)` projection. -/
lemma kernelPairTripleThirteenBase_fst :
    kernelPairTripleThirteenBase q ≫ pullback.fst q.obj.hom q.obj.hom =
      pullback.fst (pullback.snd q.obj.hom q.obj.hom)
        (pullback.fst q.obj.hom q.obj.hom) ≫
          pullback.fst q.obj.hom q.obj.hom := by
  exact pullback.lift_fst _ _ _

/-- The second coordinate of the `(1,3)` projection. -/
lemma kernelPairTripleThirteenBase_snd :
    kernelPairTripleThirteenBase q ≫ pullback.snd q.obj.hom q.obj.hom =
      pullback.snd (pullback.snd q.obj.hom q.obj.hom)
        (pullback.fst q.obj.hom q.obj.hom) ≫
          pullback.snd q.obj.hom q.obj.hom := by
  exact pullback.lift_snd _ _ _

/-- The `(1,3)` projection from a composable pair to its composite base arrow. -/
def kernelPairTripleThirteenMap : kernelPairTripleObj q ⟶ kernelPairObj q :=
  ⟨Over.homMk (kernelPairTripleThirteenBase q) (by
    change kernelPairTripleThirteenBase q ≫
      (pullback.fst q.obj.hom q.obj.hom ≫ q.obj.hom) =
        (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
            (pullback.fst q.obj.hom q.obj.hom) ≫
          pullback.fst q.obj.hom q.obj.hom) ≫ q.obj.hom
    rw [← Category.assoc, kernelPairTripleThirteenBase_fst])⟩

/-- The total-space transition to the first arrow of a composable pair. -/
def kernelPairTripleFirstRaw :
    (D.obj (kernelPairTripleObj q)).left ⟶ kernelPairTotal D q :=
  ((cartesianFunctor D).map (kernelPairTripleFstMap q)).left

/-- The total-space transition to the second arrow of a composable pair. -/
def kernelPairTripleSecondRaw :
    (D.obj (kernelPairTripleObj q)).left ⟶ kernelPairTotal D q :=
  ((cartesianFunctor D).map (kernelPairTripleSndMap q)).left

/-- The total-space transition to the `(1,3)` composite arrow. -/
def kernelPairTripleCompositeRaw :
    (D.obj (kernelPairTripleObj q)).left ⟶ kernelPairTotal D q :=
  ((cartesianFunctor D).map (kernelPairTripleThirteenMap q)).left

/-- The second transition respects the projection of the descent object to its base. -/
lemma kernelPairTripleSecondRaw_w :
    kernelPairTripleSecondRaw D q ≫ (D.obj (kernelPairObj q)).hom =
      (D.obj (kernelPairTripleObj q)).hom ≫
        pullback.snd (pullback.snd q.obj.hom q.obj.hom)
          (pullback.fst q.obj.hom q.obj.hom) := by
  exact ((cartesianFunctor D).map (kernelPairTripleSndMap q)).isPullback.w

/-- The raw target transition respects the projection of the descent object to its base. -/
lemma kernelPairTargetRaw_w :
    kernelPairTargetRaw D q ≫ (D.obj q).hom =
      (D.obj (kernelPairObj q)).hom ≫
        pullback.snd q.obj.hom q.obj.hom := by
  exact ((cartesianFunctor D).map (kernelPairSnd q)).isPullback.w

/-- The middle endpoint of the first arrow is the middle endpoint of the second. -/
lemma kernelPairTripleFstMap_snd_eq_sndMap_fst :
    kernelPairTripleFstMap q ≫ kernelPairSnd q =
      kernelPairTripleSndMap q ≫ kernelPairFst q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The source coordinate of the `(1,3)` projection is that of the first arrow. -/
lemma kernelPairTripleThirteenMap_fst :
    kernelPairTripleThirteenMap q ≫ kernelPairFst q =
      kernelPairTripleFstMap q ≫ kernelPairFst q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The target coordinate of the `(1,3)` projection is that of the second arrow. -/
lemma kernelPairTripleThirteenMap_snd :
    kernelPairTripleThirteenMap q ≫ kernelPairSnd q =
      kernelPairTripleSndMap q ≫ kernelPairSnd q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- On total spaces, the target of the first arrow equals the source of the second. -/
lemma kernelPairTripleRaw_comm :
    kernelPairTripleFirstRaw D q ≫ kernelPairTargetRaw D q =
      kernelPairTripleSecondRaw D q ≫ kernelPairSourceRaw D q := by
  have h₁ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleFstMap q) (kernelPairSnd q))
  have h₂ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleSndMap q) (kernelPairFst q))
  calc
    kernelPairTripleFirstRaw D q ≫ kernelPairTargetRaw D q =
        ((cartesianFunctor D).map
          (kernelPairTripleFstMap q ≫ kernelPairSnd q)).left := h₁.symm
    _ = ((cartesianFunctor D).map
          (kernelPairTripleSndMap q ≫ kernelPairFst q)).left := by
      rw [kernelPairTripleFstMap_snd_eq_sndMap_fst]
    _ = kernelPairTripleSecondRaw D q ≫ kernelPairSourceRaw D q := h₂

/-- The descent object over the triple overlap represents the pullback of raw target
and raw source. -/
lemma kernelPairTripleRaw_isPullback :
    IsPullback (kernelPairTripleFirstRaw D q)
      (kernelPairTripleSecondRaw D q)
      (kernelPairTargetRaw D q) (kernelPairSourceRaw D q) := by
  let hFirst := ((cartesianFunctor D).map
    (kernelPairTripleFstMap q)).isPullback
  let hBase : IsPullback
      (pullback.fst (pullback.snd q.obj.hom q.obj.hom)
        (pullback.fst q.obj.hom q.obj.hom))
      (pullback.snd (pullback.snd q.obj.hom q.obj.hom)
        (pullback.fst q.obj.hom q.obj.hom))
      (pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom) :=
    IsPullback.of_hasPullback _ _
  let hOuter := hFirst.paste_vert hBase
  have hOuter' : IsPullback (kernelPairTripleFirstRaw D q)
      (kernelPairTripleSecondRaw D q ≫
        (D.obj (kernelPairObj q)).hom)
      (kernelPairTargetRaw D q ≫ (D.obj q).hom)
      (pullback.fst q.obj.hom q.obj.hom) := by
    change IsPullback (kernelPairTripleFirstRaw D q)
      ((D.obj (kernelPairTripleObj q)).hom ≫
        pullback.snd (pullback.snd q.obj.hom q.obj.hom)
          (pullback.fst q.obj.hom q.obj.hom))
      ((D.obj (kernelPairObj q)).hom ≫ pullback.snd q.obj.hom q.obj.hom)
      (pullback.fst q.obj.hom q.obj.hom) at hOuter
    rw [← kernelPairTripleSecondRaw_w, ← kernelPairTargetRaw_w] at hOuter
    exact hOuter
  exact hOuter'.of_bot (kernelPairTripleRaw_comm D q)
    (kernelPairSourceRaw_isPullback D q)

/-- The canonical identification carries the standard source to the raw source. -/
lemma kernelPairSourceIso_hom_source :
    (kernelPairSourceIso D q).hom ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom =
      kernelPairSourceRaw D q := by
  exact kernelPairSourceIso_hom_fst D q

/-- The canonical identification carries the standard target to the raw target. -/
lemma kernelPairSourceIso_hom_target :
    (kernelPairSourceIso D q).hom ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) =
      kernelPairTargetRaw D q := by
  rw [kernelPairRelationTarget_eq]
  simp

/-- Transporting both factors to the standard relation object preserves the
triple-overlap pullback square. -/
lemma kernelPairTriple_isPullback :
    IsPullback
      (kernelPairTripleFirstRaw D q ≫ (kernelPairSourceIso D q).hom)
      (kernelPairTripleSecondRaw D q ≫ (kernelPairSourceIso D q).hom)
      ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
      ((D.obj q).hom.kernelPairRelationSource q.obj.hom) := by
  apply (kernelPairTripleRaw_isPullback D q).of_iso
    (Iso.refl _) (kernelPairSourceIso D q) (kernelPairSourceIso D q) (Iso.refl _)
  · simp
  · simp
  · change kernelPairTargetRaw D q ≫ 𝟙 _ =
      (kernelPairSourceIso D q).hom ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q)
    rw [Category.comp_id]
    exact (kernelPairSourceIso_hom_target D q).symm
  · change kernelPairSourceRaw D q ≫ 𝟙 _ =
      (kernelPairSourceIso D q).hom ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom
    rw [Category.comp_id]
    exact (kernelPairSourceIso_hom_source D q).symm

/-- The canonical identification of the triple-overlap total space with the space of
composable relation arrows. -/
noncomputable def kernelPairTripleIso :
    (D.obj (kernelPairTripleObj q)).left ≅
      pullback
        ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
        ((D.obj q).hom.kernelPairRelationSource q.obj.hom) :=
  (kernelPairTriple_isPullback D q).isoPullback

/-- The inverse triple-overlap identification followed by its first projection is the
standard first projection. -/
lemma kernelPairTripleIso_inv_fst :
    (kernelPairTripleIso D q).inv ≫
        (kernelPairTripleFirstRaw D q ≫ (kernelPairSourceIso D q).hom) =
      pullback.fst
        ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
        ((D.obj q).hom.kernelPairRelationSource q.obj.hom) := by
  exact (kernelPairTriple_isPullback D q).isoPullback_inv_fst

/-- The inverse triple-overlap identification followed by its second projection is the
standard second projection. -/
lemma kernelPairTripleIso_inv_snd :
    (kernelPairTripleIso D q).inv ≫
        (kernelPairTripleSecondRaw D q ≫ (kernelPairSourceIso D q).hom) =
      pullback.snd
        ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
        ((D.obj q).hom.kernelPairRelationSource q.obj.hom) := by
  exact (kernelPairTriple_isPullback D q).isoPullback_inv_snd

/-- The raw composite has the same source as the first arrow. -/
lemma kernelPairTripleCompositeRaw_source :
    kernelPairTripleCompositeRaw D q ≫ kernelPairSourceRaw D q =
      kernelPairTripleFirstRaw D q ≫ kernelPairSourceRaw D q := by
  have h₁ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleThirteenMap q) (kernelPairFst q))
  have h₂ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleFstMap q) (kernelPairFst q))
  calc
    kernelPairTripleCompositeRaw D q ≫ kernelPairSourceRaw D q =
        ((cartesianFunctor D).map
          (kernelPairTripleThirteenMap q ≫ kernelPairFst q)).left := h₁.symm
    _ = ((cartesianFunctor D).map
          (kernelPairTripleFstMap q ≫ kernelPairFst q)).left := by
      rw [kernelPairTripleThirteenMap_fst]
    _ = kernelPairTripleFirstRaw D q ≫ kernelPairSourceRaw D q := h₂

/-- The raw composite has the same target as the second arrow. -/
lemma kernelPairTripleCompositeRaw_target :
    kernelPairTripleCompositeRaw D q ≫ kernelPairTargetRaw D q =
      kernelPairTripleSecondRaw D q ≫ kernelPairTargetRaw D q := by
  have h₁ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleThirteenMap q) (kernelPairSnd q))
  have h₂ := congrArg CartesianArrowHom.left
    ((cartesianFunctor D).map_comp
      (kernelPairTripleSndMap q) (kernelPairSnd q))
  calc
    kernelPairTripleCompositeRaw D q ≫ kernelPairTargetRaw D q =
        ((cartesianFunctor D).map
          (kernelPairTripleThirteenMap q ≫ kernelPairSnd q)).left := h₁.symm
    _ = ((cartesianFunctor D).map
          (kernelPairTripleSndMap q ≫ kernelPairSnd q)).left := by
      rw [kernelPairTripleThirteenMap_snd]
    _ = kernelPairTripleSecondRaw D q ≫ kernelPairTargetRaw D q := h₂

/-- Composition of two composable arrows in the standard kernel-pair relation object. -/
def kernelPairComposition :
    pullback
        ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
        ((D.obj q).hom.kernelPairRelationSource q.obj.hom) ⟶
      (D.obj q).hom.kernelPairRelationObject q.obj.hom :=
  (kernelPairTripleIso D q).inv ≫ kernelPairTripleCompositeRaw D q ≫
    (kernelPairSourceIso D q).hom

/-- The source of a composite relation arrow is the source of its first factor. -/
lemma kernelPairComposition_source :
    kernelPairComposition D q ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom =
      pullback.fst
          ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
          ((D.obj q).hom.kernelPairRelationSource q.obj.hom) ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom := by
  let source := (D.obj q).hom.kernelPairRelationSource q.obj.hom
  let target := (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q)
  calc
    kernelPairComposition D q ≫ source =
        (kernelPairTripleIso D q).inv ≫
          (kernelPairTripleCompositeRaw D q ≫ kernelPairSourceRaw D q) := by
      simp only [kernelPairComposition, source, Category.assoc,
        kernelPairSourceIso_hom_source]
    _ = (kernelPairTripleIso D q).inv ≫
          (kernelPairTripleFirstRaw D q ≫ kernelPairSourceRaw D q) := by
      rw [kernelPairTripleCompositeRaw_source]
    _ = ((kernelPairTripleIso D q).inv ≫
          (kernelPairTripleFirstRaw D q ≫ (kernelPairSourceIso D q).hom)) ≫
            source := by
      dsimp [source]
      simpa only [Category.assoc] using
        (((kernelPairTripleIso D q).inv ≫ kernelPairTripleFirstRaw D q) ≫=
          (kernelPairSourceIso_hom_source D q)).symm
    _ = pullback.fst target source ≫ source := by
      dsimp [target, source]
      exact congrArg (fun k ↦ k ≫
        (D.obj q).hom.kernelPairRelationSource q.obj.hom)
          (kernelPairTripleIso_inv_fst D q)

/-- The target of a composite relation arrow is the target of its second factor. -/
lemma kernelPairComposition_target :
    kernelPairComposition D q ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) =
      pullback.snd
          ((D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
          ((D.obj q).hom.kernelPairRelationSource q.obj.hom) ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q) := by
  let source := (D.obj q).hom.kernelPairRelationSource q.obj.hom
  let target := (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q)
  calc
    kernelPairComposition D q ≫ target =
        (kernelPairTripleIso D q).inv ≫
          (kernelPairTripleCompositeRaw D q ≫ kernelPairTargetRaw D q) := by
      simp only [kernelPairComposition, target, Category.assoc,
        kernelPairSourceIso_hom_target]
    _ = (kernelPairTripleIso D q).inv ≫
          (kernelPairTripleSecondRaw D q ≫ kernelPairTargetRaw D q) := by
      rw [kernelPairTripleCompositeRaw_target]
    _ = ((kernelPairTripleIso D q).inv ≫
          (kernelPairTripleSecondRaw D q ≫ (kernelPairSourceIso D q).hom)) ≫
            target := by
      dsimp [target]
      simpa only [Category.assoc] using
        (((kernelPairTripleIso D q).inv ≫ kernelPairTripleSecondRaw D q) ≫=
          (kernelPairSourceIso_hom_target D q)).symm
    _ = pullback.snd target source ≫ target := by
      dsimp [target, source]
      exact congrArg (fun k ↦ k ≫
        (D.obj q).hom.kernelPairRelationTarget q.obj.hom (kernelPairAlpha D q))
          (kernelPairTripleIso_inv_snd D q)

/-- The cartesian-arrow functor of coherent scheme-arrow descent data supplies the
internal equivalence-relation structure on the relation attached to the kernel pair
of any selected sieve arrow. -/
noncomputable def kernelPairDescentRelationOfFunctor :
    (D.obj q).hom.KernelPairDescentRelation q.obj.hom where
  alpha := kernelPairAlpha D q
  unit := kernelPairUnit D q
  unit_source := kernelPairUnit_source D q
  unit_target := kernelPairUnit_target D q
  inverse := kernelPairInverse D q
  inverse_source := kernelPairInverse_source D q
  inverse_target := kernelPairInverse_target D q
  composition := kernelPairComposition D q
  composition_source := kernelPairComposition_source D q
  composition_target := kernelPairComposition_target D q

/-- A coherent scheme-arrow descent datum supplies the internal equivalence-relation
structure on the relation attached to the kernel pair of any selected sieve arrow. -/
noncomputable def kernelPairDescentRelation
    (E : Data (R := R)) (q : R.arrows.category) :
    (E.obj q).hom.KernelPairDescentRelation q.obj.hom :=
  kernelPairDescentRelationOfFunctor E q

end

end AlgebraicGeometry.OverPullbackDescent
