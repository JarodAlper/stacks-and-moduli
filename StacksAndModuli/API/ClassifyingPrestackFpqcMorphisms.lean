module

public import StacksAndModuli.API.ClassifyingPrestack
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Fpqc gluing of morphisms between principal bundles

This file proves the morphism-gluing half of fpqc descent for the classifying
prestack of principal bundles. The proof glues the maps of total spaces using
subcanonicity, checks equivariance on the pulled-back cover, and obtains
cartesianness from the local pullback criterion for a universe-small fpqc cover.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace ClassifyingObj

variable {G}

/-- Pull a classifying object back along a morphism to its base. -/
noncomputable def pullback (a : ClassifyingObj G) {T : Over S}
    (f : T ⟶ a.base) : ClassifyingObj G where
  base := T
  bundle := a.bundle.pullback f

/-- The canonical cartesian morphism from a pulled-back principal bundle. -/
noncomputable def pullbackHom (a : ClassifyingObj G) {T : Over S}
    (f : T ⟶ a.base) : pullback a f ⟶ a where
  base := f
  total := Limits.pullback.fst a.bundle.p f
  isPullback := IsPullback.of_hasPullback a.bundle.p f
  equivariant := by
    constructor
    exact Limits.pullback.lift_fst _ _ _

/-- The canonical morphism from a pulled-back bundle lifts the base-change map. -/
lemma pullbackHom_isHomLift (a : ClassifyingObj G) {T : Over S}
    (f : T ⟶ a.base) :
    IsHomLift (classifyingPrestack G).p f (pullbackHom a f) :=
  Functor.IsHomLift.map (p := (classifyingPrestack G).p) (pullbackHom a f)

end ClassifyingObj

namespace ClassifyingPrestackMorphisms

variable {G}

/-- The classifying object obtained by pulling `a` back along `g`. -/
noncomputable def pullObj (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) : ClassifyingObj G :=
  a.pullback g

/-- The canonical cartesian morphism from `pullObj a g` to `a`. -/
noncomputable def pullTo (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) : pullObj a g ⟶ a :=
  a.pullbackHom g

/-- `pullTo a g` lies over `g`. -/
lemma pullTo_isHomLift (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    IsHomLift (classifyingPrestack G).p g (pullTo a g) :=
  ClassifyingObj.pullbackHom_isHomLift a g

/-- The square underlying `pullTo a g` commutes with the stated base map. -/
lemma pullTo_comm (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    (pullTo a g).total ≫ a.bundle.p = (pullObj a g).bundle.p ≫ g := by
  letI := pullTo_isHomLift a g
  have hbase : g = (pullTo a g).base :=
    IsHomLift.eq_of_isHomLift (classifyingPrestack G).p g (pullTo a g)
  calc
    (pullTo a g).total ≫ a.bundle.p =
        (pullObj a g).bundle.p ≫ (pullTo a g).base :=
      (pullTo a g).isPullback.w
    _ = (pullObj a g).bundle.p ≫ g := by rw [← hbase]

/-- A point of a torsor induces the tautological section of its pullback. -/
noncomputable def pointSection (a : ClassifyingObj G) {Z : Over S}
    (k : Z ⟶ a.bundle.P) :
    Z ⟶ (pullObj a (k ≫ a.bundle.p)).bundle.P :=
  Limits.pullback.lift k (𝟙 Z) (by simp)

/-- The tautological section projects to the original point. -/
@[reassoc (attr := simp)]
lemma pointSection_fst (a : ClassifyingObj G) {Z : Over S}
    (k : Z ⟶ a.bundle.P) :
    pointSection a k ≫ Limits.pullback.fst a.bundle.p (k ≫ a.bundle.p) = k :=
  Limits.pullback.lift_fst _ _ _

/-- The tautological section is a section of the pullback projection. -/
@[reassoc (attr := simp)]
lemma pointSection_snd (a : ClassifyingObj G) {Z : Over S}
    (k : Z ⟶ a.bundle.P) :
    pointSection a k ≫ Limits.pullback.snd a.bundle.p (k ≫ a.bundle.p) = 𝟙 Z :=
  Limits.pullback.lift_snd _ _ _

/-- The canonical comparison between two iterated pullbacks of a principal bundle. -/
noncomputable def transition (a : ClassifyingObj G) {W Z : Over S}
    (h : W ⟶ Z) (k : Z ⟶ a.bundle.P) :
    pullObj a ((h ≫ k) ≫ a.bundle.p) ⟶ pullObj a (k ≫ a.bundle.p) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  let xi := pullTo a ((h ≫ k) ≫ a.bundle.p)
  letI hXi : IsHomLift (classifyingPrestack G).p
      ((h ≫ k) ≫ a.bundle.p) xi :=
    pullTo_isHomLift a ((h ≫ k) ≫ a.bundle.p)
  exact IsStronglyCartesian.map (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
    (g := h) (f' := (h ≫ k) ≫ a.bundle.p) (Category.assoc _ _ _) xi

/-- The pullback comparison lies over the map between the two bases. -/
lemma transition_isHomLift (a : ClassifyingObj G) {W Z : Over S}
    (h : W ⟶ Z) (k : Z ⟶ a.bundle.P) :
    IsHomLift (classifyingPrestack G).p h (transition a h k) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((h ≫ k) ≫ a.bundle.p)
  unfold transition
  exact IsStronglyCartesian.map_isHomLift (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
      (g := h) (f' := (h ≫ k) ≫ a.bundle.p) (Category.assoc _ _ _)
      (pullTo a ((h ≫ k) ≫ a.bundle.p))

/-- The pullback comparison followed by the canonical map is the canonical composite. -/
@[simp]
lemma transition_comp_pullTo (a : ClassifyingObj G) {W Z : Over S}
    (h : W ⟶ Z) (k : Z ⟶ a.bundle.P) :
    transition a h k ≫ pullTo a (k ≫ a.bundle.p) =
      pullTo a ((h ≫ k) ≫ a.bundle.p) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((h ≫ k) ≫ a.bundle.p)
  unfold transition
  exact IsStronglyCartesian.fac (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
      (g := h) (f' := (h ≫ k) ≫ a.bundle.p) (Category.assoc _ _ _)
      (pullTo a ((h ≫ k) ≫ a.bundle.p))

/-- Tautological sections are natural under the pullback comparison. -/
lemma pointSection_transition (a : ClassifyingObj G) {W Z : Over S}
    (h : W ⟶ Z) (k : Z ⟶ a.bundle.P) :
    pointSection a (h ≫ k) ≫ (transition a h k).total = h ≫ pointSection a k := by
  apply Limits.pullback.hom_ext
  · have H := congrArg ClassifyingHom.total (transition_comp_pullTo a h k)
    change (transition a h k).total ≫
        Limits.pullback.fst a.bundle.p (k ≫ a.bundle.p) =
      Limits.pullback.fst a.bundle.p ((h ≫ k) ≫ a.bundle.p) at H
    dsimp [pointSection, pullObj, ClassifyingObj.pullback,
      GlobalPrincipalBundle.pullback]
    rw [Category.assoc, H]
    simp
  · have H := (transition a h k).isPullback.w
    dsimp [pullObj, ClassifyingObj.pullback, GlobalPrincipalBundle.pullback] at H
    letI hTransition := transition_isHomLift a h k
    have hbase : h = (transition a h k).base := by
      exact IsHomLift.eq_of_isHomLift (classifyingPrestack G).p h (transition a h k)
    rw [← hbase] at H
    change (transition a h k).total ≫
        Limits.pullback.snd a.bundle.p (k ≫ a.bundle.p) =
      Limits.pullback.snd a.bundle.p ((h ≫ k) ≫ a.bundle.p) ≫ h at H
    dsimp [pointSection, pullObj, ClassifyingObj.pullback,
      GlobalPrincipalBundle.pullback]
    rw [Category.assoc, H]
    simp only [Limits.pullback.lift_snd_assoc, Category.assoc,
      Category.id_comp]
    rw [Limits.pullback.lift_snd, Category.comp_id]

/-- Acting on a point does not change its image in the base of a principal bundle. -/
lemma smul_comp_bundleProjection (a : ClassifyingObj G) {W : Over S}
    (r : W ⟶ G) (k : W ⟶ a.bundle.P) :
    (r • k) ≫ a.bundle.p = k ≫ a.bundle.p := by
  rw [CategoryTheory.Hom.smul_def, Category.assoc, a.bundle.invariant]
  simp

/-- The pullback comparison induced by acting on a point of a torsor. -/
noncomputable def actionTransition (a : ClassifyingObj G) {W : Over S}
    (r : W ⟶ G) (k : W ⟶ a.bundle.P) :
    pullObj a ((r • k) ≫ a.bundle.p) ⟶ pullObj a (k ≫ a.bundle.p) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  let xi := pullTo a ((r • k) ≫ a.bundle.p)
  letI hXi : IsHomLift (classifyingPrestack G).p
      ((r • k) ≫ a.bundle.p) xi :=
    pullTo_isHomLift a ((r • k) ≫ a.bundle.p)
  exact IsStronglyCartesian.map (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
    (g := 𝟙 W) (f' := (r • k) ≫ a.bundle.p)
    (by simpa using smul_comp_bundleProjection a r k) xi

/-- The action-induced comparison is vertical over the identity. -/
lemma actionTransition_isHomLift (a : ClassifyingObj G) {W : Over S}
    (r : W ⟶ G) (k : W ⟶ a.bundle.P) :
    IsHomLift (classifyingPrestack G).p (𝟙 W) (actionTransition a r k) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((r • k) ≫ a.bundle.p)
  unfold actionTransition
  exact IsStronglyCartesian.map_isHomLift (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
    (g := 𝟙 W) (f' := (r • k) ≫ a.bundle.p)
    (by simpa using smul_comp_bundleProjection a r k)
    (pullTo a ((r • k) ≫ a.bundle.p))

/-- The action-induced comparison is compatible with the canonical pullback map. -/
@[simp]
lemma actionTransition_comp_pullTo (a : ClassifyingObj G) {W : Over S}
    (r : W ⟶ G) (k : W ⟶ a.bundle.P) :
    actionTransition a r k ≫ pullTo a (k ≫ a.bundle.p) =
      pullTo a ((r • k) ≫ a.bundle.p) := by
  letI hLift := pullTo_isHomLift a (k ≫ a.bundle.p)
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p
      (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p)) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((r • k) ≫ a.bundle.p)
  unfold actionTransition
  exact IsStronglyCartesian.fac (classifyingPrestack G).p
    (k ≫ a.bundle.p) (pullTo a (k ≫ a.bundle.p))
    (g := 𝟙 W) (f' := (r • k) ≫ a.bundle.p)
    (by simpa using smul_comp_bundleProjection a r k)
    (pullTo a ((r • k) ≫ a.bundle.p))

/-- The action comparison carries the acted-on section to the acted-on section. -/
lemma pointSection_actionTransition (a : ClassifyingObj G) {W : Over S}
    (r : W ⟶ G) (k : W ⟶ a.bundle.P) :
    pointSection a (r • k) ≫ (actionTransition a r k).total =
      r • pointSection a k := by
  apply Limits.pullback.hom_ext
  · have H := congrArg ClassifyingHom.total (actionTransition_comp_pullTo a r k)
    change (actionTransition a r k).total ≫
        (pullTo a (k ≫ a.bundle.p)).total =
      (pullTo a ((r • k) ≫ a.bundle.p)).total at H
    change (pointSection a (r • k) ≫ (actionTransition a r k).total) ≫
        (pullTo a (k ≫ a.bundle.p)).total =
      (r • pointSection a k) ≫ (pullTo a (k ≫ a.bundle.p)).total
    rw [Category.assoc, H]
    letI : IsModHom G (pullTo a (k ≫ a.bundle.p)).total :=
      (pullTo a (k ≫ a.bundle.p)).equivariant
    calc
      pointSection a (r • k) ≫
          (pullTo a ((r • k) ≫ a.bundle.p)).total = r • k := by
        change pointSection a (r • k) ≫
          Limits.pullback.fst a.bundle.p ((r • k) ≫ a.bundle.p) = r • k
        rw [pointSection_fst]
      _ = r • (pointSection a k ≫
          (pullTo a (k ≫ a.bundle.p)).total) := by
        change r • k = r • (pointSection a k ≫
          Limits.pullback.fst a.bundle.p (k ≫ a.bundle.p))
        rw [pointSection_fst]
      _ = (r • pointSection a k) ≫
          (pullTo a (k ≫ a.bundle.p)).total :=
        (IsModHom.map_smul (pullTo a (k ≫ a.bundle.p)).total r
          (pointSection a k)).symm
  · change (pointSection a (r • k) ≫ (actionTransition a r k).total) ≫
        (pullObj a (k ≫ a.bundle.p)).bundle.p =
      (r • pointSection a k) ≫
        (pullObj a (k ≫ a.bundle.p)).bundle.p
    letI hTransition := actionTransition_isHomLift a r k
    have hbase : 𝟙 W = (actionTransition a r k).base := by
      exact IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
        (𝟙 W) (actionTransition a r k)
    have hright : (r • pointSection a k) ≫
        (pullObj a (k ≫ a.bundle.p)).bundle.p = 𝟙 W := by
      calc
        (r • pointSection a k) ≫
            (pullObj a (k ≫ a.bundle.p)).bundle.p =
          pointSection a k ≫
            (pullObj a (k ≫ a.bundle.p)).bundle.p :=
              smul_comp_bundleProjection (pullObj a (k ≫ a.bundle.p)) r
                (pointSection a k)
        _ = 𝟙 W := pointSection_snd a k
    have hsection : pointSection a (r • k) ≫
        (pullObj a ((r • k) ≫ a.bundle.p)).bundle.p = 𝟙 W := by
      exact pointSection_snd a (r • k)
    rw [hright]
    calc
      (pointSection a (r • k) ≫ (actionTransition a r k).total) ≫
          (pullObj a (k ≫ a.bundle.p)).bundle.p =
        pointSection a (r • k) ≫
          ((actionTransition a r k).total ≫
            (pullObj a (k ≫ a.bundle.p)).bundle.p) :=
              Category.assoc _ _ _
      _ = pointSection a (r • k) ≫
          ((pullObj a ((r • k) ≫ a.bundle.p)).bundle.p ≫
            (actionTransition a r k).base) := by
              rw [(actionTransition a r k).isPullback.w]
      _ = (pointSection a (r • k) ≫
          (pullObj a ((r • k) ≫ a.bundle.p)).bundle.p) ≫
            (actionTransition a r k).base :=
              (Category.assoc _ _ _).symm
      _ = 𝟙 W ≫ (actionTransition a r k).base := by
              rw [hsection]
      _ = (actionTransition a r k).base := Category.id_comp _
      _ = 𝟙 W := hbase.symm

/-- The comparison from pulling a pullback bundle back along its projection. -/
noncomputable def selfTransition (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    pullObj a ((pullTo a g).total ≫ a.bundle.p) ⟶ pullObj a g := by
  letI hLift := pullTo_isHomLift a g
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p g (pullTo a g) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  let xi := pullTo a ((pullTo a g).total ≫ a.bundle.p)
  letI hXi : IsHomLift (classifyingPrestack G).p
      ((pullTo a g).total ≫ a.bundle.p) xi :=
    pullTo_isHomLift a ((pullTo a g).total ≫ a.bundle.p)
  exact IsStronglyCartesian.map (classifyingPrestack G).p g (pullTo a g)
    (g := (pullObj a g).bundle.p)
    (f' := (pullTo a g).total ≫ a.bundle.p)
    (pullTo_comm a g) xi

/-- The self-pullback comparison lies over the pulled-back bundle projection. -/
lemma selfTransition_isHomLift (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    IsHomLift (classifyingPrestack G).p (pullObj a g).bundle.p
      (selfTransition a g) := by
  letI hLift := pullTo_isHomLift a g
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p g (pullTo a g) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((pullTo a g).total ≫ a.bundle.p)
  unfold selfTransition
  exact IsStronglyCartesian.map_isHomLift (classifyingPrestack G).p g
    (pullTo a g) (g := (pullObj a g).bundle.p)
    (f' := (pullTo a g).total ≫ a.bundle.p)
    (pullTo_comm a g)
    (pullTo a ((pullTo a g).total ≫ a.bundle.p))

/-- The self-pullback comparison is compatible with the canonical pullback map. -/
@[simp]
lemma selfTransition_comp_pullTo (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    selfTransition a g ≫ pullTo a g =
      pullTo a ((pullTo a g).total ≫ a.bundle.p) := by
  letI hLift := pullTo_isHomLift a g
  letI hCart : IsStronglyCartesian (classifyingPrestack G).p g (pullTo a g) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  letI hXi := pullTo_isHomLift a ((pullTo a g).total ≫ a.bundle.p)
  unfold selfTransition
  exact IsStronglyCartesian.fac (classifyingPrestack G).p g (pullTo a g)
    (g := (pullObj a g).bundle.p)
    (f' := (pullTo a g).total ≫ a.bundle.p)
    (pullTo_comm a g)
    (pullTo a ((pullTo a g).total ≫ a.bundle.p))

/-- The tautological section followed by the self-pullback comparison is the identity. -/
lemma pointSection_selfTransition (a : ClassifyingObj G) {Z : Over S}
    (g : Z ⟶ a.base) :
    pointSection a (pullTo a g).total ≫ (selfTransition a g).total =
      𝟙 (pullObj a g).bundle.P := by
  apply Limits.pullback.hom_ext
  · have H := congrArg ClassifyingHom.total (selfTransition_comp_pullTo a g)
    change (selfTransition a g).total ≫ (pullTo a g).total =
      (pullTo a ((pullTo a g).total ≫ a.bundle.p)).total at H
    change (pointSection a (pullTo a g).total ≫
        (selfTransition a g).total) ≫ (pullTo a g).total =
      𝟙 (pullObj a g).bundle.P ≫ (pullTo a g).total
    rw [Category.assoc, H]
    change pointSection a (pullTo a g).total ≫
        Limits.pullback.fst a.bundle.p
          ((pullTo a g).total ≫ a.bundle.p) = _
    rw [pointSection_fst, Category.id_comp]
  · change (pointSection a (pullTo a g).total ≫
        (selfTransition a g).total) ≫ (pullObj a g).bundle.p =
      𝟙 (pullObj a g).bundle.P ≫ (pullObj a g).bundle.p
    letI hTransition := selfTransition_isHomLift a g
    have hbase : (pullObj a g).bundle.p = (selfTransition a g).base := by
      exact IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
        (pullObj a g).bundle.p (selfTransition a g)
    rw [Category.assoc, (selfTransition a g).isPullback.w]
    rw [← hbase]
    have hs : pointSection a (pullTo a g).total ≫
        (pullObj a ((pullTo a g).total ≫ a.bundle.p)).bundle.p =
          𝟙 (pullObj a g).bundle.P := by
      exact pointSection_snd a (pullTo a g).total
    rw [← Category.assoc, hs, Category.id_comp]

/-- Morphisms of principal `G`-bundles glue uniquely for the fpqc topology. -/
theorem morphismsGlue_fpqc :
    (classifyingPrestack G).p.MorphismsGlue (Scheme.fpqcTopology.over S) := by
  intro T R hR a b ha hb phi hphi hcompat
  change ClassifyingObj G at a b
  subst T
  let J := Scheme.fpqcTopology.over S
  let R' : Sieve a.bundle.P := R.pullback a.bundle.p
  have hR' : R' ∈ J a.bundle.P := J.pullback_stable a.bundle.p hR
  let localHom : ∀ {Z : Over S} (k : Z ⟶ a.bundle.P), R' k →
      (pullObj a (k ≫ a.bundle.p) ⟶ b) := fun {Z} k hk ↦
    phi hk (pullTo a (k ≫ a.bundle.p)) (pullTo_isHomLift a (k ≫ a.bundle.p))
  have localHom_isHomLift : ∀ {Z : Over S} (k : Z ⟶ a.bundle.P) (hk : R' k),
      IsHomLift (classifyingPrestack G).p (k ≫ a.bundle.p) (localHom k hk) := by
    intro Z k hk
    exact hphi hk (pullTo a (k ≫ a.bundle.p))
      (pullTo_isHomLift a (k ≫ a.bundle.p))
  let fam : Presieve.FamilyOfElements (yoneda.obj b.bundle.P) R'.arrows :=
    fun Z k hk ↦ pointSection a k ≫ (localHom k hk).total
  have fam_compatible : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W k h hk
    let chi := transition a h k
    have hchi := transition_isHomLift a h k
    have hfac := transition_comp_pullTo a h k
    have hcompLift : IsHomLift (classifyingPrestack G).p
        (h ≫ (k ≫ a.bundle.p))
        (chi ≫ pullTo a (k ≫ a.bundle.p)) := by
      letI := hchi
      letI := pullTo_isHomLift a (k ≫ a.bundle.p)
      exact IsHomLift.comp (classifyingPrestack G).p h (k ≫ a.bundle.p)
        chi (pullTo a (k ≫ a.bundle.p))
    have hcompLift' : IsHomLift (classifyingPrestack G).p
        ((h ≫ k) ≫ a.bundle.p)
        (chi ≫ pullTo a (k ≫ a.bundle.p)) := by
      simpa [Category.assoc] using hcompLift
    let Lifted := { q : pullObj a ((h ≫ k) ≫ a.bundle.p) ⟶ a //
      IsHomLift (classifyingPrestack G).p ((h ≫ k) ≫ a.bundle.p) q }
    have hpairs :
        (⟨chi ≫ pullTo a (k ≫ a.bundle.p), hcompLift'⟩ : Lifted) =
          ⟨pullTo a ((h ≫ k) ≫ a.bundle.p),
            pullTo_isHomLift a ((h ≫ k) ≫ a.bundle.p)⟩ := by
      apply Subtype.ext
      exact hfac
    have hsame := congrArg
      (fun q : Lifted ↦ phi (R'.downward_closed hk h) q.1 q.2) hpairs
    have hnat := hcompat hk chi (pullTo a (k ≫ a.bundle.p))
      (pullTo_isHomLift a (k ≫ a.bundle.p)) hchi
    have hlocal : localHom (h ≫ k) (R'.downward_closed hk h) =
        chi ≫ localHom k hk := by
      exact hsame.symm.trans (by simpa [localHom, Category.assoc] using hnat)
    change pointSection a (h ≫ k) ≫
        (localHom (h ≫ k) (R'.downward_closed hk h)).total =
      (yoneda.obj b.bundle.P).map h.op
        (pointSection a k ≫ (localHom k hk).total)
    change _ = h ≫ (pointSection a k ≫ (localHom k hk).total)
    rw [hlocal]
    change pointSection a (h ≫ k) ≫
        ((transition a h k).total ≫ (localHom k hk).total) =
      h ≫ (pointSection a k ≫ (localHom k hk).total)
    rw [← Category.assoc, pointSection_transition, Category.assoc]
  have hB : Presieve.IsSheaf J (yoneda.obj b.bundle.P) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let PhiTotal : a.bundle.P ⟶ b.bundle.P :=
    (hB R' hR').amalgamate fam fam_compatible
  have PhiTotal_local {Z : Over S} (k : Z ⟶ a.bundle.P) (hk : R' k) :
      k ≫ PhiTotal = pointSection a k ≫ (localHom k hk).total := by
    exact (hB R' hR').valid_glue fam_compatible k hk
  have localHom_base {Z : Over S} (k : Z ⟶ a.bundle.P) (hk : R' k) :
      (localHom k hk).base = (k ≫ a.bundle.p) ≫ eqToHom hb.symm := by
    letI := localHom_isHomLift k hk
    have H := IsHomLift.fac' (classifyingPrestack G).p
      (k ≫ a.bundle.p) (localHom k hk)
    simpa using H
  have hBase : Presieve.IsSheaf J (yoneda.obj b.base) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have PhiTotal_base : PhiTotal ≫ b.bundle.p =
      a.bundle.p ≫ eqToHom hb.symm := by
    apply ((hBase R' hR').isSeparatedFor).ext
    intro Z k hk
    change k ≫ (PhiTotal ≫ b.bundle.p) =
      k ≫ (a.bundle.p ≫ eqToHom hb.symm)
    calc
      k ≫ (PhiTotal ≫ b.bundle.p) =
          (k ≫ PhiTotal) ≫ b.bundle.p := (Category.assoc _ _ _).symm
      _ = (pointSection a k ≫ (localHom k hk).total) ≫
          b.bundle.p := by rw [PhiTotal_local]
      _ = pointSection a k ≫
          ((localHom k hk).total ≫ b.bundle.p) := Category.assoc _ _ _
      _ = pointSection a k ≫
          ((pullObj a (k ≫ a.bundle.p)).bundle.p ≫
            (localHom k hk).base) := by
              rw [(localHom k hk).isPullback.w]
      _ = (pointSection a k ≫
          (pullObj a (k ≫ a.bundle.p)).bundle.p) ≫
            (localHom k hk).base := (Category.assoc _ _ _).symm
      _ = (localHom k hk).base := by
        change (pointSection a k ≫
          Limits.pullback.snd a.bundle.p (k ≫ a.bundle.p)) ≫
            (localHom k hk).base = (localHom k hk).base
        simpa only [Category.assoc] using
          pointSection_snd_assoc a k (localHom k hk).base
      _ = (k ≫ a.bundle.p) ≫ eqToHom hb.symm := localHom_base k hk
      _ = k ≫ (a.bundle.p ≫ eqToHom hb.symm) := Category.assoc _ _ _
  let RG : Sieve (G ⊗ a.bundle.P) := R'.pullback (snd G a.bundle.P)
  have hRG : RG ∈ J (G ⊗ a.bundle.P) :=
    J.pullback_stable (snd G a.bundle.P) hR'
  have PhiTotal_equivariant : IsModHom G PhiTotal := by
    constructor
    apply ((hB RG hRG).isSeparatedFor).ext
    intro W l hl
    let r : W ⟶ G := l ≫ fst G a.bundle.P
    let k : W ⟶ a.bundle.P := l ≫ snd G a.bundle.P
    have hk : R' k := hl
    have hkact : R' (r • k) := by
      change R ((r • k) ≫ a.bundle.p)
      rw [smul_comp_bundleProjection]
      exact hk
    let chi := actionTransition a r k
    have hchi : IsHomLift (classifyingPrestack G).p (𝟙 W) chi :=
      actionTransition_isHomLift a r k
    have hlocalAction : localHom (r • k) hkact =
        chi ≫ localHom k hk := by
      have hnat := hcompat hk chi (pullTo a (k ≫ a.bundle.p))
        (pullTo_isHomLift a (k ≫ a.bundle.p)) hchi
      simpa [localHom, chi, Category.assoc,
        smul_comp_bundleProjection] using hnat
    have hactA : l ≫ γ[G, a.bundle.P] = r • k := by
      rw [CategoryTheory.Hom.smul_def]
      change l ≫ γ[G, a.bundle.P] =
        lift (l ≫ fst G a.bundle.P) (l ≫ snd G a.bundle.P) ≫
          γ[G, a.bundle.P]
      rw [lift_comp_fst_snd]
    have hactB : (l ≫ (G ◁ PhiTotal)) ≫ γ[G, b.bundle.P] =
        r • (k ≫ PhiTotal) := by
      rw [CategoryTheory.Hom.smul_def]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp [r, k, Category.assoc]
      · simp [r, k, Category.assoc]
    change l ≫ (γ[G, a.bundle.P] ≫ PhiTotal) =
      l ≫ ((G ◁ PhiTotal) ≫ γ[G, b.bundle.P])
    calc
      l ≫ (γ[G, a.bundle.P] ≫ PhiTotal) =
          (l ≫ γ[G, a.bundle.P]) ≫ PhiTotal :=
            (Category.assoc _ _ _).symm
      _ = (r • k) ≫ PhiTotal := by rw [hactA]
      _ = pointSection a (r • k) ≫
          (localHom (r • k) hkact).total := PhiTotal_local (r • k) hkact
      _ = pointSection a (r • k) ≫
          (chi.total ≫ (localHom k hk).total) := by
            rw [hlocalAction]
            rfl
      _ = (pointSection a (r • k) ≫ chi.total) ≫
          (localHom k hk).total := (Category.assoc _ _ _).symm
      _ = (r • pointSection a k) ≫
          (localHom k hk).total := by
            rw [pointSection_actionTransition]
      _ = r • (pointSection a k ≫ (localHom k hk).total) := by
        letI : IsModHom G (localHom k hk).total := (localHom k hk).equivariant
        exact IsModHom.map_smul (localHom k hk).total r (pointSection a k)
      _ = r • (k ≫ PhiTotal) := by rw [PhiTotal_local]
      _ = (l ≫ (G ◁ PhiTotal)) ≫ γ[G, b.bundle.P] := hactB.symm
      _ = l ≫ ((G ◁ PhiTotal) ≫ γ[G, b.bundle.P]) :=
        Category.assoc _ _ _
  have canonical_local {Z : Over S} (g : Z ⟶ a.base) (hg : R g) :
      (pullTo a g).total ≫ PhiTotal =
        (phi hg (pullTo a g) (pullTo_isHomLift a g)).total := by
    let k : (pullObj a g).bundle.P ⟶ a.bundle.P := (pullTo a g).total
    have hk : R' k := by
      change R (k ≫ a.bundle.p)
      rw [pullTo_comm a g]
      exact R.downward_closed hg (pullObj a g).bundle.p
    let chi := selfTransition a g
    have hchi : IsHomLift (classifyingPrestack G).p
        (pullObj a g).bundle.p chi := selfTransition_isHomLift a g
    let theta := phi hg (pullTo a g) (pullTo_isHomLift a g)
    have hlocal : localHom k hk = chi ≫ theta := by
      have hnat := hcompat hg chi (pullTo a g) (pullTo_isHomLift a g) hchi
      simpa [localHom, k, chi, theta, pullTo_comm, Category.assoc] using hnat
    calc
      (pullTo a g).total ≫ PhiTotal = k ≫ PhiTotal := rfl
      _ = pointSection a k ≫ (localHom k hk).total := PhiTotal_local k hk
      _ = pointSection a k ≫ (chi.total ≫ theta.total) := by
        rw [hlocal]
        rfl
      _ = (pointSection a k ≫ chi.total) ≫ theta.total :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 (pullObj a g).bundle.P ≫ theta.total := by
        rw [pointSection_selfTransition]
      _ = theta.total := Category.id_comp _
      _ = (phi hg (pullTo a g) (pullTo_isHomLift a g)).total := rfl
  let K : Precoverage (Over S) :=
    Scheme.fpqcPrecoverage.comap (Over.forget S)
  have hJK : J = K.toGrothendieck := by
    dsimp [J, K]
    exact over_toGrothendieck_eq_toGrothendieck_comap_forget
      Scheme.fpqcPrecoverage S
  have hRK : R ∈ K.toGrothendieck a.base := by
    rw [← hJK]
    exact hR
  obtain ⟨Q, hQ, hQR⟩ :=
    K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hRK
  let Ebig : K.ZeroHypercover a.base :=
    { __ := Q.preZeroHypercover
      mem₀ := by simpa using hQ }
  letI : Precoverage.Small.{u} Scheme.fpqcPrecoverage := by
    unfold Scheme.fpqcPrecoverage
    infer_instance
  letI : Precoverage.Small.{u} K := by
    dsimp [K]
    infer_instance
  letI : Precoverage.ZeroHypercover.Small.{u} Ebig := inferInstance
  let E : K.ZeroHypercover.{u} a.base :=
    Precoverage.ZeroHypercover.restrictIndexOfSmall.{u} Ebig
  letI : K.toGrothendieck.Subcanonical := by
    rw [← hJK]
    infer_instance
  have PhiTotal_cartesian : IsPullback PhiTotal a.bundle.p b.bundle.p
      (eqToHom hb.symm) := by
    apply IsPullback.flip
    apply E.isPullback_of_forall_isPullback a.bundle.p PhiTotal
      (eqToHom hb.symm) b.bundle.p
    intro i
    let g : E.X i ⟶ a.base := E.f i
    have hg : R g := by
      apply hQR
      change Q ((Q.preZeroHypercover).f
        (Precoverage.ZeroHypercover.Small.restrictFun.{u} Ebig i))
      exact (Precoverage.ZeroHypercover.Small.restrictFun.{u} Ebig i).2
    let theta := phi hg (pullTo a g) (pullTo_isHomLift a g)
    have htheta_base : theta.base = g ≫ eqToHom hb.symm := by
      letI := hphi hg (pullTo a g) (pullTo_isHomLift a g)
      have H := IsHomLift.fac' (classifyingPrestack G).p g theta
      simpa [theta] using H
    change IsPullback (pullObj a g).bundle.p
      ((pullTo a g).total ≫ PhiTotal) (g ≫ eqToHom hb.symm) b.bundle.p
    rw [canonical_local g hg, ← htheta_base]
    exact theta.isPullback.flip
  let Phi : a ⟶ b :=
    { base := eqToHom hb.symm
      total := PhiTotal
      isPullback := PhiTotal_cartesian
      equivariant := PhiTotal_equivariant }
  have hPhiLift : IsHomLift (classifyingPrestack G).p (𝟙 a.base) Phi := by
    apply IsHomLift.of_fac' (classifyingPrestack G).p (𝟙 a.base) Phi rfl hb
    simp [Phi]
  have canonical_local_hom {Z : Over S} (g : Z ⟶ a.base) (hg : R g) :
      phi hg (pullTo a g) (pullTo_isHomLift a g) = pullTo a g ≫ Phi := by
    apply ClassifyingHom.ext
    · letI := hphi hg (pullTo a g) (pullTo_isHomLift a g)
      have H := IsHomLift.fac' (classifyingPrestack G).p g
        (phi hg (pullTo a g) (pullTo_isHomLift a g))
      change (phi hg (pullTo a g) (pullTo_isHomLift a g)).base =
        (pullTo a g).base ≫ Phi.base
      change (phi hg (pullTo a g) (pullTo_isHomLift a g)).base =
        g ≫ eqToHom hb.symm
      simpa [Phi, pullTo, ClassifyingObj.pullbackHom] using H
    · change (phi hg (pullTo a g) (pullTo_isHomLift a g)).total =
        (pullTo a g).total ≫ PhiTotal
      exact (canonical_local g hg).symm
  have factorization : ∀ {T : Over S} {g : T ⟶ a.base} (hg : R g)
      {x : ClassifyingObj G} (xi : x ⟶ a)
      (hxi : IsHomLift (classifyingPrestack G).p g xi),
      phi hg xi hxi = xi ≫ Phi := by
    intro T g hg x xi hxi
    letI hpull := pullTo_isHomLift a g
    letI hcart : IsStronglyCartesian (classifyingPrestack G).p g (pullTo a g) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
    letI hxi' := hxi
    let chi : x ⟶ pullObj a g :=
      IsStronglyCartesian.map (classifyingPrestack G).p g (pullTo a g)
        (g := 𝟙 T) (f' := g) (Category.id_comp g) xi
    have hchi : IsHomLift (classifyingPrestack G).p (𝟙 T) chi := by
      exact IsStronglyCartesian.map_isHomLift (classifyingPrestack G).p g
        (pullTo a g) (g := 𝟙 T) (f' := g) (Category.id_comp g) xi
    have hfac : chi ≫ pullTo a g = xi := by
      exact IsStronglyCartesian.fac (classifyingPrestack G).p g (pullTo a g)
        (g := 𝟙 T) (f' := g) (Category.id_comp g) xi
    have hnat := hcompat hg chi (pullTo a g) (pullTo_isHomLift a g) hchi
    have hlocal : phi hg xi hxi =
        chi ≫ phi hg (pullTo a g) (pullTo_isHomLift a g) := by
      simpa [hfac] using hnat
    calc
      phi hg xi hxi =
          chi ≫ phi hg (pullTo a g) (pullTo_isHomLift a g) := hlocal
      _ = chi ≫ (pullTo a g ≫ Phi) := by rw [canonical_local_hom]
      _ = (chi ≫ pullTo a g) ≫ Phi := (Category.assoc _ _ _).symm
      _ = xi ≫ Phi := by rw [hfac]
  refine ⟨Phi, ⟨hPhiLift, factorization⟩, ?_⟩
  intro Psi hPsi
  apply ClassifyingHom.ext
  · have hPsiBase : Psi.base = eqToHom hb.symm := by
      letI := hPsi.1
      have H := IsHomLift.fac' (classifyingPrestack G).p (𝟙 a.base) Psi
      simpa using H
    change Psi.base = Phi.base
    simpa [Phi] using hPsiBase
  · apply ((hB R' hR').isSeparatedFor).ext
    intro Z k hk
    let g : Z ⟶ a.base := k ≫ a.bundle.p
    let theta := phi hk (pullTo a g) (pullTo_isHomLift a g)
    have hPsiTotal := congrArg ClassifyingHom.total
      (hPsi.2 hk (pullTo a g) (pullTo_isHomLift a g))
    change theta.total = (pullTo a g).total ≫ Psi.total at hPsiTotal
    change k ≫ Psi.total = k ≫ PhiTotal
    calc
      k ≫ Psi.total =
          (pointSection a k ≫ (pullTo a g).total) ≫ Psi.total := by
        change k ≫ Psi.total =
          (pointSection a k ≫
            Limits.pullback.fst a.bundle.p (k ≫ a.bundle.p)) ≫ Psi.total
        rw [pointSection_fst]
      _ = pointSection a k ≫ ((pullTo a g).total ≫ Psi.total) :=
        Category.assoc _ _ _
      _ = pointSection a k ≫ theta.total := by rw [← hPsiTotal]
      _ = pointSection a k ≫ ((pullTo a g).total ≫ PhiTotal) := by
        rw [canonical_local g hk]
      _ = (pointSection a k ≫ (pullTo a g).total) ≫ PhiTotal :=
        (Category.assoc _ _ _).symm
      _ = k ≫ PhiTotal := by
        change (pointSection a k ≫
          Limits.pullback.fst a.bundle.p (k ≫ a.bundle.p)) ≫ PhiTotal =
            k ≫ PhiTotal
        rw [pointSection_fst]

end ClassifyingPrestackMorphisms

end AlgebraicGeometry.Scheme
