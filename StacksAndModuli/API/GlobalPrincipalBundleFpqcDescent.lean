module

public import StacksAndModuli.API.ClassifyingPrestack
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# FPQC descent of principal-bundle structure

This file supplies the structured part of effective fpqc descent for global
principal bundles. Starting from a cartesian gluing of the underlying total
spaces and projections, it constructs and descends the group action, proves the
action laws and invariance, constructs the local comparison morphisms, and
packages the resulting object-gluing theorem. It deliberately has no dependency
on Chapter 3's later stack vocabulary.
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

/-- The underlying cartesian gluing of the total spaces and projections in a
descent datum of principal bundles. -/
structure UnderlyingGluing {T : Over S} {R : Sieve T}
    (D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G))
    (hDobj : ∀ q : R.arrows.category,
      (classifyingPrestack G).p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift (classifyingPrestack G).p k.hom.left (D.map k)) where
  /-- The glued total space. -/
  P : Over S
  /-- The glued projection. -/
  p : P ⟶ T
  /-- The cartesian comparison from each local total space. -/
  total : ∀ q : R.arrows.category, (D.obj q).bundle.P ⟶ P
  /-- Each comparison square is cartesian. -/
  isPullback : ∀ q : R.arrows.category,
    IsPullback (total q) (D.obj q).bundle.p p
      (eqToHom (hDobj q) ≫ q.obj.hom)
  /-- The comparisons respect the transition maps of the descent datum. -/
  naturality : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    (D.map k).total ≫ total r = total q

namespace UnderlyingGluing

variable {T : Over S} {R : Sieve T}
  {D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G)}
  {hDobj : ∀ q : R.arrows.category,
    (classifyingPrestack G).p.obj (D.obj q) = q.obj.left}
  {hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    IsHomLift (classifyingPrestack G).p k.hom.left (D.map k)}
  (A : UnderlyingGluing D hDobj hDmap)

lemma local_mem {W Z : Over S} (h : W ⟶ Z) (k : Z ⟶ A.P)
    (hk : R (k ≫ A.p)) : R ((h ≫ k) ≫ A.p) := by
  simpa only [Category.assoc] using R.downward_closed hk h

/-- The object of the descent sieve associated to an arrow into the glued total
space whose composite with the projection belongs to the base sieve. -/
abbrev localObj {Z : Over S} (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    R.arrows.category :=
  R.arrows.categoryMk (k ≫ A.p) hk

/-- The tautological lift of a point of the glued total space to the corresponding
local total space. -/
noncomputable def point {Z : Over S} (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    Z ⟶ (D.obj (A.localObj k hk)).bundle.P :=
  (A.isPullback (A.localObj k hk)).lift k
    (eqToHom (hDobj (A.localObj k hk)).symm) (by simp [localObj])

@[reassoc (attr := simp)]
lemma point_total {Z : Over S} (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    A.point k hk ≫ A.total (A.localObj k hk) = k :=
  (A.isPullback (A.localObj k hk)).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma point_projection {Z : Over S} (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    A.point k hk ≫ (D.obj (A.localObj k hk)).bundle.p =
      eqToHom (hDobj (A.localObj k hk)).symm :=
  (A.isPullback (A.localObj k hk)).lift_snd _ _ _

/-- The morphism between local objects induced by precomposition. -/
def localMap {W Z : Over S} (h : W ⟶ Z) (k : Z ⟶ A.P)
    (hk : R (k ≫ A.p)) :
    A.localObj (h ≫ k) (A.local_mem h k hk) ⟶ A.localObj k hk :=
  ⟨Over.homMk h⟩

@[simp]
lemma localMap_hom_left {W Z : Over S} (h : W ⟶ Z) (k : Z ⟶ A.P)
    (hk : R (k ≫ A.p)) :
    (A.localMap h k hk).hom.left = h := rfl

lemma point_naturality {W Z : Over S} (h : W ⟶ Z) (k : Z ⟶ A.P)
    (hk : R (k ≫ A.p)) :
    A.point (h ≫ k) (A.local_mem h k hk) ≫
        (D.map (A.localMap h k hk)).total =
      h ≫ A.point k hk := by
  apply (A.isPullback (A.localObj k hk)).hom_ext
  · rw [Category.assoc, A.naturality (A.localMap h k hk)]
    calc
      A.point (h ≫ k) (A.local_mem h k hk) ≫
          A.total (A.localObj (h ≫ k) (A.local_mem h k hk)) = h ≫ k :=
        A.point_total (h ≫ k) (A.local_mem h k hk)
      _ = h ≫ (A.point k hk ≫ A.total (A.localObj k hk)) := by
        rw [A.point_total]
      _ = (h ≫ A.point k hk) ≫ A.total (A.localObj k hk) :=
        (Category.assoc _ _ _).symm
  · rw [Category.assoc, (D.map (A.localMap h k hk)).isPullback.w]
    simp only [← Category.assoc, A.point_projection]
    have hLift : IsHomLift (classifyingPrestack G).p h
        (D.map (A.localMap h k hk)) := by
      simpa [localMap] using hDmap (A.localMap h k hk)
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p h
      (D.map (A.localMap h k hk))
    change (D.map (A.localMap h k hk)).base = _ at H
    calc
      eqToHom (hDobj (A.localObj (h ≫ k) (A.local_mem h k hk))).symm ≫
          (D.map (A.localMap h k hk)).base =
          h ≫ eqToHom (hDobj (A.localObj k hk)).symm := by
        rw [H]
        simp [Category.assoc]
      _ = h ≫ (A.point k hk ≫
          (D.obj (A.localObj k hk)).bundle.p) := by
        rw [A.point_projection]
      _ = (h ≫ A.point k hk) ≫
          (D.obj (A.localObj k hk)).bundle.p :=
        (Category.assoc _ _ _).symm

/-- The pullback of the base descent sieve to the glued total space. -/
def totalSieve : Sieve A.P := R.pullback A.p

/-- The further pullback to `G ×_S P`, used to glue the action map. -/
noncomputable def actionSieve : Sieve (G ⊗ A.P) :=
  A.totalSieve.pullback (snd G A.P)

lemma actionSieve_mem (hR : R ∈ Scheme.fpqcTopology.over S T) :
    A.actionSieve ∈ Scheme.fpqcTopology.over S (G ⊗ A.P) := by
  exact (Scheme.fpqcTopology.over S).pullback_stable (snd G A.P)
    ((Scheme.fpqcTopology.over S).pullback_stable A.p hR)

/-- The local action value attached to an arrow of the action-cover sieve. -/
noncomputable def localAction {Z : Over S} (l : Z ⟶ G ⊗ A.P)
    (hl : A.actionSieve l) : Z ⟶ A.P :=
  let r : Z ⟶ G := l ≫ fst G A.P
  let k : Z ⟶ A.P := l ≫ snd G A.P
  (r • A.point k hl) ≫ A.total (A.localObj k hl)

lemma localAction_naturality {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    A.localAction (h ≫ l) (A.actionSieve.downward_closed hl h) =
      h ≫ A.localAction l hl := by
  let r : Z ⟶ G := l ≫ fst G A.P
  let k : Z ⟶ A.P := l ≫ snd G A.P
  have hpoint := A.point_naturality h k hl
  let q := A.localObj k hl
  let q' := A.localObj (h ≫ k) (A.local_mem h k hl)
  let m := A.localMap h k hl
  have hmEq :
      (D.map m).total ≫ A.total q = A.total q' := A.naturality m
  letI : IsModHom G (D.map m).total := (D.map m).equivariant
  change (((h ≫ r) •
      A.point (h ≫ k) (A.local_mem h k hl)) ≫
        A.total q' =
    h ≫ ((r • A.point k hl) ≫ A.total q))
  calc
    ((h ≫ r) • A.point (h ≫ k) (A.local_mem h k hl)) ≫
        A.total q' =
      (((h ≫ r) • A.point (h ≫ k) (A.local_mem h k hl)) ≫
        (D.map m).total) ≫ A.total q := by
          rw [Category.assoc, hmEq]
    _ = ((h ≫ r) •
        (A.point (h ≫ k) (A.local_mem h k hl) ≫
          (D.map m).total)) ≫ A.total q := by
          rw [IsModHom.map_smul]
    _ = ((h ≫ r) • (h ≫ A.point k hl)) ≫ A.total q := by
          rw [hpoint]
    _ = (h ≫ (r • A.point k hl)) ≫ A.total q := by
          rw [ModObj.comp_smul]
    _ = h ≫ ((r • A.point k hl) ≫ A.total q) :=
      Category.assoc _ _ _

/-- The action map obtained by fpqc gluing from the local principal-bundle actions. -/
noncomputable def descendedAction
    (hR : R ∈ Scheme.fpqcTopology.over S T) : G ⊗ A.P ⟶ A.P :=
  let fam : Presieve.FamilyOfElements (yoneda.obj A.P) A.actionSieve.arrows :=
    fun _ l hl ↦ A.localAction l hl
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj A.P) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  (hP A.actionSieve (A.actionSieve_mem hR)).amalgamate fam (by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W l h hl
    exact A.localAction_naturality h l hl)

lemma descendedAction_local
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    l ≫ A.descendedAction hR = A.localAction l hl := by
  let fam : Presieve.FamilyOfElements (yoneda.obj A.P) A.actionSieve.arrows :=
    fun _ l hl ↦ A.localAction l hl
  let hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W l h hl
    exact A.localAction_naturality h l hl
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj A.P) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  exact (hP A.actionSieve (A.actionSieve_mem hR)).valid_glue hcompat l hl

lemma comparison_total_mem (q : R.arrows.category) :
    R (((G ◁ A.total q) ≫ snd G A.P) ≫ A.p) := by
  change R (((G ◁ A.total q) ≫ snd G A.P) ≫ A.p)
  rw [whiskerLeft_snd, Category.assoc, (A.isPullback q).w]
  exact R.downward_closed q.property
    (snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
      eqToHom (hDobj q))

lemma comparison_action_mem (q : R.arrows.category) :
    A.actionSieve (G ◁ A.total q) :=
  A.comparison_total_mem q

/-- The transition from the canonical local object associated to the comparison
map `G × P_q → G × P` back to the original sieve object `q`. -/
noncomputable def actionComparisonMap (q : R.arrows.category) :
    A.localObj ((G ◁ A.total q) ≫ snd G A.P)
      (A.comparison_total_mem q) ⟶ q :=
  ⟨Over.homMk
    (snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
      eqToHom (hDobj q)) (by
        change (snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
            eqToHom (hDobj q)) ≫ q.obj.hom =
          ((G ◁ A.total q) ≫ snd G A.P) ≫ A.p
        calc
          (snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
              eqToHom (hDobj q)) ≫ q.obj.hom =
              snd G (D.obj q).bundle.P ≫
                ((D.obj q).bundle.p ≫
                  (eqToHom (hDobj q) ≫ q.obj.hom)) := by
                    simp only [Category.assoc]
          _ = snd G (D.obj q).bundle.P ≫ (A.total q ≫ A.p) := by
                rw [(A.isPullback q).w]
          _ = (snd G (D.obj q).bundle.P ≫ A.total q) ≫ A.p :=
                (Category.assoc _ _ _).symm
          _ = ((G ◁ A.total q) ≫ snd G A.P) ≫ A.p := by
                rw [whiskerLeft_snd])⟩

@[simp]
lemma actionComparisonMap_hom_left (q : R.arrows.category) :
    (A.actionComparisonMap q).hom.left =
      snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
        eqToHom (hDobj q) := rfl

lemma point_actionComparisonMap (q : R.arrows.category) :
    A.point ((G ◁ A.total q) ≫ snd G A.P)
        (A.comparison_total_mem q) ≫
      (D.map (A.actionComparisonMap q)).total =
        snd G (D.obj q).bundle.P := by
  apply (A.isPullback q).hom_ext
  · rw [Category.assoc, A.naturality (A.actionComparisonMap q)]
    exact (A.point_total _ _).trans (whiskerLeft_snd G (A.total q))
  · rw [Category.assoc, (D.map (A.actionComparisonMap q)).isPullback.w]
    have hLift : IsHomLift (classifyingPrestack G).p
        (A.actionComparisonMap q).hom.left
        (D.map (A.actionComparisonMap q)) := hDmap (A.actionComparisonMap q)
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p
      (A.actionComparisonMap q).hom.left
      (D.map (A.actionComparisonMap q))
    change (D.map (A.actionComparisonMap q)).base = _ at H
    calc
      A.point ((G ◁ A.total q) ≫ snd G A.P)
          (A.comparison_total_mem q) ≫
          ((D.obj (A.localObj ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q))).bundle.p ≫
              (D.map (A.actionComparisonMap q)).base) =
          (A.point ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q) ≫
              (D.obj (A.localObj ((G ◁ A.total q) ≫ snd G A.P)
                (A.comparison_total_mem q))).bundle.p) ≫
                  (D.map (A.actionComparisonMap q)).base :=
            (Category.assoc _ _ _).symm
      _ = eqToHom (hDobj (A.localObj
            ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q))).symm ≫
          (D.map (A.actionComparisonMap q)).base := by
            rw [A.point_projection]
      _ = eqToHom (hDobj (A.localObj
            ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q))).symm ≫
          (eqToHom (hDobj (A.localObj
            ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q))) ≫
              (A.actionComparisonMap q).hom.left ≫
                eqToHom (hDobj q).symm) := by rw [H]
      _ = (A.actionComparisonMap q).hom.left ≫
          eqToHom (hDobj q).symm := by simp [Category.assoc]
      _ = (snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p ≫
          eqToHom (hDobj q)) ≫ eqToHom (hDobj q).symm := by
            rw [A.actionComparisonMap_hom_left]
      _ = snd G (D.obj q).bundle.P ≫ (D.obj q).bundle.p := by
            simp [Category.assoc]

/-- Every local comparison map intertwines the local action with the descended
action map. -/
lemma total_smul (hR : R ∈ Scheme.fpqcTopology.over S T)
    (q : R.arrows.category) :
    γ[G, (D.obj q).bundle.P] ≫ A.total q =
      (G ◁ A.total q) ≫ A.descendedAction hR := by
  rw [A.descendedAction_local hR (G ◁ A.total q)
    (A.comparison_action_mem q)]
  dsimp only [localAction]
  rw [whiskerLeft_fst]
  change γ[G, (D.obj q).bundle.P] ≫ A.total q =
    (((fst G (D.obj q).bundle.P) •
      A.point ((G ◁ A.total q) ≫ snd G A.P)
        (A.comparison_total_mem q)) ≫
      A.total (A.localObj ((G ◁ A.total q) ≫ snd G A.P)
        (A.comparison_total_mem q)))
  let m := A.actionComparisonMap q
  have hm := A.naturality m
  calc
    γ[G, (D.obj q).bundle.P] ≫ A.total q =
        ((fst G (D.obj q).bundle.P) • snd G (D.obj q).bundle.P) ≫
          A.total q := by
            simp [CategoryTheory.Hom.smul_def]
    _ = ((fst G (D.obj q).bundle.P) •
          (A.point ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q) ≫ (D.map m).total)) ≫
          A.total q := by rw [A.point_actionComparisonMap q]
    _ = (((fst G (D.obj q).bundle.P) •
          A.point ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q)) ≫ (D.map m).total) ≫
          A.total q := by
            letI : IsModHom G (D.map m).total := (D.map m).equivariant
            rw [IsModHom.map_smul (D.map m).total]
    _ = ((fst G (D.obj q).bundle.P) •
          A.point ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q)) ≫
          ((D.map m).total ≫ A.total q) := Category.assoc _ _ _
    _ = ((fst G (D.obj q).bundle.P) •
          A.point ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q)) ≫
          A.total (A.localObj ((G ◁ A.total q) ≫ snd G A.P)
            (A.comparison_total_mem q)) := by rw [hm]

lemma descendedAction_one
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    (η[G] ▷ A.P) ≫ A.descendedAction hR = (λ_ A.P).hom := by
  let U : Sieve (𝟙_ (Over S) ⊗ A.P) :=
    A.totalSieve.pullback ((λ_ A.P).hom)
  have hU : U ∈ Scheme.fpqcTopology.over S (𝟙_ (Over S) ⊗ A.P) :=
    (Scheme.fpqcTopology.over S).pullback_stable (λ_ A.P).hom
      ((Scheme.fpqcTopology.over S).pullback_stable A.p hR)
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj A.P) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply ((hP U hU).isSeparatedFor).ext
  intro Z l hl
  have hmem : A.actionSieve (l ≫ (η[G] ▷ A.P)) := by
    change R (((l ≫ (η[G] ▷ A.P)) ≫ snd G A.P) ≫ A.p)
    simpa [U, totalSieve, leftUnitor_hom, Category.assoc] using hl
  change l ≫ ((η[G] ▷ A.P) ≫ A.descendedAction hR) =
    l ≫ (λ_ A.P).hom
  rw [← Category.assoc, A.descendedAction_local hR _ hmem]
  dsimp only [localAction]
  have hr : (l ≫ (η[G] ▷ A.P)) ≫ fst G A.P =
      (1 : Z ⟶ G) := by
    rw [CategoryTheory.Hom.one_def]
    calc
      (l ≫ (η[G] ▷ A.P)) ≫ fst G A.P =
          (l ≫ fst (𝟙_ (Over S)) A.P) ≫ η[G] := by
            simp only [Category.assoc, whiskerRight_fst]
      _ = toUnit Z ≫ η[G] := by
            rw [toUnit_unique (l ≫ fst (𝟙_ (Over S)) A.P) (toUnit Z)]
  have hk : (l ≫ (η[G] ▷ A.P)) ≫ snd G A.P =
      l ≫ (λ_ A.P).hom := by
    simp only [Category.assoc, whiskerRight_snd]
    rw [leftUnitor_hom]
  let k : Z ⟶ A.P := (l ≫ (η[G] ▷ A.P)) ≫ snd G A.P
  have hkR : R (k ≫ A.p) := hmem
  change (((l ≫ (η[G] ▷ A.P)) ≫ fst G A.P) •
      A.point k hkR) ≫ A.total (A.localObj k hkR) =
        l ≫ (λ_ A.P).hom
  rw [hr, one_smul]
  exact (A.point_total k hkR).trans hk

lemma descendedAction_mul
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    (μ[G] ▷ A.P) ≫ A.descendedAction hR =
      (α_ G G A.P).hom ≫ G ◁ A.descendedAction hR ≫
        A.descendedAction hR := by
  let U : Sieve ((G ⊗ G) ⊗ A.P) :=
    A.totalSieve.pullback (snd (G ⊗ G) A.P)
  have hU : U ∈ Scheme.fpqcTopology.over S ((G ⊗ G) ⊗ A.P) :=
    (Scheme.fpqcTopology.over S).pullback_stable (snd (G ⊗ G) A.P)
      ((Scheme.fpqcTopology.over S).pullback_stable A.p hR)
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj A.P) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply ((hP U hU).isSeparatedFor).ext
  intro Z l hl
  change l ≫ ((μ[G] ▷ A.P) ≫ A.descendedAction hR) =
    l ≫ ((α_ G G A.P).hom ≫ G ◁ A.descendedAction hR ≫
      A.descendedAction hR)
  let k : Z ⟶ A.P := l ≫ snd (G ⊗ G) A.P
  have hkR : R (k ≫ A.p) := hl
  let q := A.localObj k hkR
  let lq : Z ⟶ (G ⊗ G) ⊗ (D.obj q).bundle.P :=
    lift (l ≫ fst (G ⊗ G) A.P) (A.point k hkR)
  have hlq : lq ≫ ((G ⊗ G) ◁ A.total q) = l := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
    · rw [Category.assoc, whiskerLeft_snd]
      calc
        lq ≫ (snd (G ⊗ G) (D.obj q).bundle.P ≫ A.total q) =
            (lq ≫ snd (G ⊗ G) (D.obj q).bundle.P) ≫
              A.total q := (Category.assoc _ _ _).symm
        _ = A.point k hkR ≫ A.total q := by rw [lift_snd]
        _ = k := A.point_total k hkR
        _ = l ≫ snd (G ⊗ G) A.P := rfl
  rw [← hlq]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [MonoidalCategory.whisker_exchange]
  slice_lhs 3 4 => rw [← A.total_smul hR q]
  slice_rhs 2 3 => rw [MonoidalCategory.associator_naturality_right]
  slice_rhs 3 4 => rw [← MonoidalCategory.whiskerLeft_comp]
  rw [← A.total_smul hR q]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_rhs 4 5 => rw [← A.total_smul hR q]
  have hmul := ModObj.mul_smul (M := G) (D.obj q).bundle.P
  change (μ[G] ▷ (D.obj q).bundle.P) ≫ γ[G, (D.obj q).bundle.P] =
    (α_ G G (D.obj q).bundle.P).hom ≫
      G ◁ γ[G, (D.obj q).bundle.P] ≫ γ[G, (D.obj q).bundle.P] at hmul
  have H := congrArg
    (fun f : ((G ⊗ G) ⊗ (D.obj q).bundle.P ⟶ (D.obj q).bundle.P) ↦
      lq ≫ f ≫ A.total q)
    hmul
  simpa only [Category.assoc] using H

/-- The descended action as a module-object structure. -/
@[instance_reducible]
noncomputable def descendedModObj
    (hR : R ∈ Scheme.fpqcTopology.over S T) : ModObj G A.P where
  smul := A.descendedAction hR
  one_smul := A.descendedAction_one hR
  mul_smul := A.descendedAction_mul hR

lemma total_equivariant
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (q : R.arrows.category) :
    letI := A.descendedModObj hR
    IsModHom G (A.total q) := by
  letI := A.descendedModObj hR
  constructor
  exact A.total_smul hR q

lemma descended_invariant
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    A.descendedAction hR ≫ A.p = snd G A.P ≫ A.p := by
  let hT : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj T) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply ((hT A.actionSieve (A.actionSieve_mem hR)).isSeparatedFor).ext
  intro Z l hl
  change l ≫ (A.descendedAction hR ≫ A.p) =
    l ≫ (snd G A.P ≫ A.p)
  rw [← Category.assoc, A.descendedAction_local hR l hl]
  let r : Z ⟶ G := l ≫ fst G A.P
  let k : Z ⟶ A.P := l ≫ snd G A.P
  let q := A.localObj k hl
  let s : Z ⟶ (D.obj q).bundle.P := A.point k hl
  have hlocal : (r • s) ≫ (D.obj q).bundle.p =
      s ≫ (D.obj q).bundle.p := by
    rw [CategoryTheory.Hom.smul_def, Category.assoc,
      (D.obj q).bundle.invariant]
    simp
  have hs : s ≫ (D.obj q).bundle.p = eqToHom (hDobj q).symm := by
    exact A.point_projection k hl
  dsimp only [localAction]
  change ((r • s) ≫ A.total q) ≫ A.p =
    l ≫ snd G A.P ≫ A.p
  calc
    ((r • s) ≫ A.total q) ≫ A.p =
        (r • s) ≫ (A.total q ≫ A.p) := Category.assoc _ _ _
    _ = (r • s) ≫ ((D.obj q).bundle.p ≫
        (eqToHom (hDobj q) ≫ q.obj.hom)) := by rw [(A.isPullback q).w]
    _ = ((r • s) ≫ (D.obj q).bundle.p) ≫
        (eqToHom (hDobj q) ≫ q.obj.hom) :=
      (Category.assoc _ _ _).symm
    _ = (s ≫ (D.obj q).bundle.p) ≫
        (eqToHom (hDobj q) ≫ q.obj.hom) := by rw [hlocal]
    _ = (eqToHom (hDobj q).symm) ≫
        (eqToHom (hDobj q) ≫ q.obj.hom) := by rw [hs]
    _ = q.obj.hom := by simp
    _ = k ≫ A.p := rfl
    _ = l ≫ snd G A.P ≫ A.p := rfl

/-- Package the descended action as a principal bundle once the fpqc-local
geometric properties and torsor isomorphism have been supplied. -/
noncomputable def descendedBundle
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR))) :
    GlobalPrincipalBundle G T := by
  letI := A.descendedModObj hR
  letI : Flat A.p.left := hflat
  letI : Surjective A.p.left := hsurjective
  letI : LocallyOfFinitePresentation A.p.left := hlfp
  letI : Smooth A.p.left := hsmooth
  letI : IsIso (ModObj.torsorMap A.p (A.descended_invariant hR)) := htorsor
  exact
    { P := A.P
      p := A.p
      action := inferInstance
      invariant := A.descended_invariant hR
      flat := inferInstance
      surjective := inferInstance
      locallyOfFinitePresentation := inferInstance
      smooth := inferInstance
      torsor := inferInstance }

/-- The descended classifying object over the original base. -/
noncomputable def descendedObj
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR))) :
    ClassifyingObj G where
  base := T
  bundle := A.descendedBundle hR hflat hsurjective hlfp hsmooth htorsor

/-- The cartesian equivariant comparison from a local bundle to the descended
bundle. -/
noncomputable def comparison
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR)))
    (q : R.arrows.category) :
    D.obj q ⟶ A.descendedObj hR hflat hsurjective hlfp hsmooth htorsor where
  base := eqToHom (hDobj q) ≫ q.obj.hom
  total := A.total q
  isPullback := A.isPullback q
  equivariant := by
    letI := A.descendedModObj hR
    change IsModHom G (A.total q)
    exact A.total_equivariant hR q

lemma comparison_isHomLift
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR)))
    (q : R.arrows.category) :
    IsHomLift (classifyingPrestack G).p q.obj.hom
      (A.comparison hR hflat hsurjective hlfp hsmooth htorsor q) := by
  let hb : (classifyingPrestack G).p.obj
      (A.descendedObj hR hflat hsurjective hlfp hsmooth htorsor) = T := rfl
  apply IsHomLift.of_fac' (classifyingPrestack G).p q.obj.hom
    (A.comparison hR hflat hsurjective hlfp hsmooth htorsor q)
    (hDobj q) hb
  cases hb
  change eqToHom (hDobj q) ≫ q.obj.hom =
    eqToHom (hDobj q) ≫ q.obj.hom ≫ 𝟙 T
  simp

lemma comparison_naturality
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR)))
    {q r : R.arrows.category} (k : q ⟶ r) :
    D.map k ≫ A.comparison hR hflat hsurjective hlfp hsmooth htorsor r =
      A.comparison hR hflat hsurjective hlfp hsmooth htorsor q := by
  apply ClassifyingHom.ext
  · have hLift := hDmap k
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p k.hom.left (D.map k)
    change (D.map k).base = _ at H
    change (D.map k).base ≫ (eqToHom (hDobj r) ≫ r.obj.hom) =
      eqToHom (hDobj q) ≫ q.obj.hom
    rw [H]
    simp only [Category.assoc]
    simp
  · exact A.naturality k

end UnderlyingGluing

/-- Effective descent of the structured principal-bundle data, reduced to a
cartesian gluing of its underlying total spaces and the global geometric and
torsor properties of the descended projection. -/
theorem exists_gluing_of_underlying {T : Over S} {R : Sieve T}
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G))
    (hDobj : ∀ q : R.arrows.category,
      (classifyingPrestack G).p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift (classifyingPrestack G).p k.hom.left (D.map k))
    (A : UnderlyingGluing D hDobj hDmap)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left)
    (htorsor : letI := A.descendedModObj hR
      IsIso (ModObj.torsorMap A.p (A.descended_invariant hR))) :
    ∃ (a : ClassifyingObj G)
      (_ : (classifyingPrestack G).p.obj a = T)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q : R.arrows.category,
        IsHomLift (classifyingPrestack G).p q.obj.hom (ε q)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r),
        D.map k ≫ ε r = ε q := by
  refine ⟨A.descendedObj hR hflat hsurjective hlfp hsmooth htorsor,
    rfl, fun q => A.comparison hR hflat hsurjective hlfp hsmooth htorsor q,
    ?_, ?_⟩
  · exact fun q =>
      A.comparison_isHomLift hR hflat hsurjective hlfp hsmooth htorsor q
  · exact fun k =>
      A.comparison_naturality hR hflat hsurjective hlfp hsmooth htorsor k

end ClassifyingObj

end AlgebraicGeometry.Scheme
