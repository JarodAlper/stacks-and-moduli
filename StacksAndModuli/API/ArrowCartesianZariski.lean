module

public import StacksAndModuli.API.ArrowCartesian
public import StacksAndModuli.API.ZariskiSieveBasis

/-!
# Zariski descent for the cartesian-arrow fibration of schemes

This file proves the raw gluing theorems for scheme morphisms with cartesian
squares as morphisms.  It uses a locally directed open-cover basis inside an
arbitrary Zariski covering sieve, relative gluing of schemes for object descent,
and ordinary Zariski morphism gluing for the fully faithful part.  The later
`BasedCategory.IsStack` wrapper lives in `ArrowCartesianZariskiStack` so that
the raw construction is available before the stack vocabulary of §3.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.ArrowCartesianZariski

noncomputable section

variable {S : Scheme.{u}} {R : Sieve S} (hR : R ∈ Scheme.zariskiTopology S)
variable (D : R.arrows.category ⥤ CategoryTheory.ArrowCartesian Scheme.{u})
variable (hD : ∀ q : R.arrows.category,
  (CategoryTheory.arrowCartesian Scheme.{u}).p.obj (D.obj q) = q.obj.left)
variable (hDlift : ∀ {q r : R.arrows.category} (k : q ⟶ r),
  IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left (D.map k))

include hDlift in
lemma normalizedIsPullback {a b : R.arrows.category} (k : a ⟶ b) :
    IsPullback (D.map k).left
      ((D.obj a : Arrow Scheme.{u}).hom ≫ eqToHom (hD a))
      ((D.obj b : Arrow Scheme.{u}).hom ≫ eqToHom (hD b)) k.hom.left := by
  have hlift := hDlift k
  letI := hlift
  have hcomm := (IsHomLift.commSq
    (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left (D.map k)).w
  change (D.map k).right ≫ eqToHom _ = eqToHom _ ≫ k.hom.left at hcomm
  apply (D.map k).isPullback.of_iso (Iso.refl _) (Iso.refl _)
      (eqToIso (hD a)) (eqToIso (hD b))
  · change (D.map k).left = (D.map k).left
    rfl
  · change (D.obj a : Arrow Scheme.{u}).hom ≫ eqToHom (hD a) =
      (D.obj a : Arrow Scheme.{u}).hom ≫ eqToHom (hD a)
    rfl
  · change (D.obj b : Arrow Scheme.{u}).hom ≫ eqToHom (hD b) =
      (D.obj b : Arrow Scheme.{u}).hom ≫ eqToHom (hD b)
    rfl
  · change (D.map k).right ≫ eqToHom (hD b) = eqToHom (hD a) ≫ k.hom.left
    exact hcomm

abbrev cover : S.OpenCover := Scheme.zariskiBasisCoverOfSieve R hR

def q (i : (cover hR).I₀) : R.arrows.category :=
  R.arrows.categoryMk ((cover hR).f i) (Scheme.zariskiBasisCoverOfSieve_mem R hR i)

def qMap {i j : (cover hR).I₀} (f : i ⟶ j) : q hR i ⟶ q hR j :=
  ObjectProperty.homMk (Over.homMk ((cover hR).trans f) ((cover hR).trans_map f))

@[simp]
lemma qMap_id (i : (cover hR).I₀) : qMap hR (𝟙 i) = 𝟙 (q hR i) := by
  apply ObjectProperty.hom_ext
  ext
  change (cover hR).trans (𝟙 i) = 𝟙 _
  simp

@[simp]
lemma qMap_comp {i j k : (cover hR).I₀} (f : i ⟶ j) (g : j ⟶ k) :
    qMap hR (f ≫ g) = qMap hR f ≫ qMap hR g := by
  apply ObjectProperty.hom_ext
  ext
  change (cover hR).trans (f ≫ g) = (cover hR).trans f ≫ (cover hR).trans g
  simp

def localFunctor
    (_hD : ∀ q : R.arrows.category,
      (CategoryTheory.arrowCartesian Scheme.{u}).p.obj (D.obj q) = q.obj.left)
    (_hDlift : ∀ {a b : R.arrows.category} (k : a ⟶ b),
      IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left (D.map k)) :
    (cover hR).I₀ ⥤ Scheme.{u} where
  obj i := (D.obj (q hR i) : Arrow Scheme.{u}).left
  map {i j} f := (D.map (qMap hR f)).left
  map_id i := by
    rw [qMap_id]
    have h := congrArg CategoryTheory.CartesianArrowHom.left (D.map_id (q hR i))
    change (D.map (𝟙 (q hR i))).left = 𝟙 _ at h
    exact h
  map_comp f g := by
    rw [qMap_comp]
    have h := congrArg CategoryTheory.CartesianArrowHom.left
      (D.map_comp (qMap hR f) (qMap hR g))
    change (D.map (qMap hR f ≫ qMap hR g)).left =
      (D.map (qMap hR f)).left ≫ (D.map (qMap hR g)).left at h
    exact h

@[simp]
lemma localFunctor_map_eq
    (_hD : ∀ q : R.arrows.category,
      (CategoryTheory.arrowCartesian Scheme.{u}).p.obj (D.obj q) = q.obj.left)
    (_hDlift : ∀ {a b : R.arrows.category} (k : a ⟶ b),
      IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left (D.map k))
    {i j : (cover hR).I₀} (f : i ⟶ j) :
    (localFunctor hR D _hD _hDlift).map f = (D.map (qMap hR f)).left :=
  rfl

def localToBase : localFunctor hR D hD hDlift ⟶ (cover hR).functorOfLocallyDirected where
  app i := (D.obj (q hR i) : Arrow Scheme.{u}).hom ≫ eqToHom (hD (q hR i))
  naturality {i j} f := by
    have hlift := hDlift (qMap hR f)
    change IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).trans f) (D.map (qMap hR f)) at hlift
    letI := hlift
    have hcomm := (IsHomLift.commSq
      (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).trans f)
        (D.map (qMap hR f))).w
    change (D.map (qMap hR f)).right ≫ eqToHom _ =
      eqToHom _ ≫ (cover hR).trans f at hcomm
    have hright : (D.map (qMap hR f)).right ≫ eqToHom (hD (q hR j)) =
        eqToHom (hD (q hR i)) ≫ (cover hR).trans f := by
      simpa only using hcomm
    change (D.map (qMap hR f)).left ≫
        ((D.obj (q hR j) : Arrow Scheme.{u}).hom ≫ eqToHom (hD (q hR j))) =
      ((D.obj (q hR i) : Arrow Scheme.{u}).hom ≫ eqToHom (hD (q hR i))) ≫
        (cover hR).trans f
    calc
      _ = ((D.map (qMap hR f)).left ≫
          (D.obj (q hR j) : Arrow Scheme.{u}).hom) ≫ eqToHom (hD (q hR j)) :=
        (Category.assoc _ _ _).symm
      _ = ((D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          (D.map (qMap hR f)).right) ≫ eqToHom (hD (q hR j)) := by
        rw [(D.map (qMap hR f)).isPullback.w]
      _ = (D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          ((D.map (qMap hR f)).right ≫ eqToHom (hD (q hR j))) :=
        Category.assoc _ _ _
      _ = (D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          (eqToHom (hD (q hR i)) ≫ (cover hR).trans f) := by rw [hright]
      _ = ((D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (q hR i))) ≫ (cover hR).trans f :=
        (Category.assoc _ _ _).symm

@[simp]
lemma localToBase_app_eq (i : (cover hR).I₀) :
    (localToBase hR D hD hDlift).app i =
      (D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
        eqToHom (hD (q hR i)) :=
  rfl

lemma localToBase_equifibered : (localToBase hR D hD hDlift).Equifibered := by
  intro i j f
  exact normalizedIsPullback D hD hDlift (qMap hR f)

def relativeData : (cover hR).RelativeGluingData where
  functor := localFunctor hR D hD hDlift
  natTrans := localToBase hR D hD hDlift
  equifibered := localToBase_equifibered hR D hD hDlift

instance localFunctor_map_isOpenImmersion {i j : (cover hR).I₀} (f : i ⟶ j) :
    IsOpenImmersion ((localFunctor hR D hD hDlift).map f) := by
  apply MorphismProperty.of_isPullback
    (normalizedIsPullback D hD hDlift (qMap hR f)).flip
  change IsOpenImmersion ((cover hR).trans f)
  infer_instance

instance localFunctor_isLocallyDirected :
    ((localFunctor hR D hD hDlift).comp Scheme.forget).IsLocallyDirected := by
  apply Scheme.isLocallyDirected_of_equifibered_of_injective
    (localToBase hR D hD hDlift) (localToBase_equifibered hR D hD hDlift)
  intro i j f
  exact ((localFunctor hR D hD hDlift).map f).injective

def basePullCover (a : R.arrows.category) : a.obj.left.OpenCover :=
  (cover hR).pullback₁ a.obj.hom

instance basePullCover_category (a : R.arrows.category) :
    Category (basePullCover hR a).I₀ :=
  inferInstanceAs (Category (cover hR).I₀)

instance basePullCover_locallyDirected (a : R.arrows.category) :
    (basePullCover hR a).LocallyDirected := by
  dsimp [basePullCover]
  infer_instance

def r (a : R.arrows.category) (i : (basePullCover hR a).I₀) : R.arrows.category :=
  R.arrows.categoryMk ((basePullCover hR a).f i ≫ a.obj.hom)
    (R.downward_closed a.property ((basePullCover hR a).f i))

def rToA (a : R.arrows.category) (i : (basePullCover hR a).I₀) :
    r hR a i ⟶ a :=
  ObjectProperty.homMk (Over.homMk ((basePullCover hR a).f i) rfl)

def rToQ (a : R.arrows.category) (i : (basePullCover hR a).I₀) :
    r hR a i ⟶ q hR i :=
  ObjectProperty.homMk (Over.homMk ((cover hR).pullbackHom a.obj.hom i)
    (by exact (cover hR).pullbackHom_map a.obj.hom i))

@[simp]
lemma rToQ_hom_left (a : R.arrows.category)
    (i : (basePullCover hR a).I₀) :
    (rToQ hR a i).hom.left = (cover hR).pullbackHom a.obj.hom i :=
  rfl

def rMap (a : R.arrows.category) {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    r hR a i ⟶ r hR a j :=
  ObjectProperty.homMk (Over.homMk ((basePullCover hR a).trans f)
    (by
      change (basePullCover hR a).trans f ≫
        ((basePullCover hR a).f j ≫ a.obj.hom) =
          (basePullCover hR a).f i ≫ a.obj.hom
      rw [← Category.assoc, (basePullCover hR a).trans_map]))

@[simp]
lemma rMap_rToA (a : R.arrows.category) {i j : (basePullCover hR a).I₀}
    (f : i ⟶ j) : rMap hR a f ≫ rToA hR a j = rToA hR a i := by
  apply ObjectProperty.hom_ext
  ext
  change (basePullCover hR a).trans f ≫ (basePullCover hR a).f j =
    (basePullCover hR a).f i
  simp

@[simp]
lemma rMap_rToQ (a : R.arrows.category) {i j : (basePullCover hR a).I₀}
    (f : i ⟶ j) :
    rMap hR a f ≫ rToQ hR a j = rToQ hR a i ≫ qMap hR f := by
  apply ObjectProperty.hom_ext
  ext
  change (basePullCover hR a).trans f ≫ (cover hR).pullbackHom a.obj.hom j =
    (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).trans f
  rw [← cancel_mono ((cover hR).f j)]
  calc
    ((basePullCover hR a).trans f ≫ (cover hR).pullbackHom a.obj.hom j) ≫
        (cover hR).f j =
      (basePullCover hR a).trans f ≫
        ((basePullCover hR a).f j ≫ a.obj.hom) := by
          rw [Category.assoc]
          congr 1
          exact (cover hR).pullbackHom_map a.obj.hom j
    _ = ((basePullCover hR a).trans f ≫ (basePullCover hR a).f j) ≫
        a.obj.hom := (Category.assoc _ _ _).symm
    _ = (basePullCover hR a).f i ≫ a.obj.hom := by
      rw [(basePullCover hR a).trans_map]
    _ = (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i := by
      exact ((cover hR).pullbackHom_map a.obj.hom i).symm
    _ = (cover hR).pullbackHom a.obj.hom i ≫
        ((cover hR).trans f ≫ (cover hR).f j) := by
      rw [(cover hR).trans_map]
    _ = ((cover hR).pullbackHom a.obj.hom i ≫ (cover hR).trans f) ≫
        (cover hR).f j := (Category.assoc _ _ _).symm

def totalMap (a : R.arrows.category) :
    (D.obj a : Arrow Scheme.{u}).left ⟶ a.obj.left :=
  (D.obj a : Arrow Scheme.{u}).hom ≫ eqToHom (hD a)

def totalPullCover (a : R.arrows.category) :
    (D.obj a : Arrow Scheme.{u}).left.OpenCover :=
  (basePullCover hR a).pullback₁ (totalMap D hD a)

instance totalPullCover_category (a : R.arrows.category) :
    Category (totalPullCover hR D hD a).I₀ :=
  inferInstanceAs (Category (basePullCover hR a).I₀)

instance totalPullCover_locallyDirected (a : R.arrows.category) :
    (totalPullCover hR D hD a).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover
    (basePullCover hR a) (totalMap D hD a)

include hDlift in
def rIsoTotalPull (a : R.arrows.category) (i : (totalPullCover hR D hD a).I₀) :
    (D.obj (r hR a i) : Arrow Scheme.{u}).left ≅
      (totalPullCover hR D hD a).X i :=
  (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback

@[reassoc]
lemma rIsoTotalPull_inv_f (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).inv ≫
      (D.map (rToA hR a i)).left = (totalPullCover hR D hD a).f i := by
  exact (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback_inv_fst

@[reassoc]
lemma rIsoTotalPull_inv_toBase (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).inv ≫
      ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫ eqToHom (hD (r hR a i))) =
        (basePullCover hR a).pullbackHom (totalMap D hD a) i := by
  exact (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback_inv_snd

@[reassoc]
lemma rIsoTotalPull_hom_f (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).hom ≫
      pullback.fst (totalMap D hD a) ((basePullCover hR a).f i) =
        (D.map (rToA hR a i)).left := by
  exact (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback_hom_fst

@[reassoc]
lemma rIsoTotalPull_hom_toBase (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).hom ≫
      pullback.snd (totalMap D hD a) ((basePullCover hR a).f i) =
        (D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i)) := by
  exact (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback_hom_snd

@[reassoc]
lemma rIsoTotalPull_hom_toBaseCover (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).hom ≫
      (basePullCover hR a).pullbackHom (totalMap D hD a) i =
        (D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i)) := by
  exact (normalizedIsPullback D hD hDlift (rToA hR a i)).isoPullback_hom_snd

def localMapToGlued (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (totalPullCover hR D hD a).X i ⟶ (relativeData hR D hD hDlift).glued :=
    (rIsoTotalPull hR D hD hDlift a i).inv ≫
    (D.map (rToQ hR a i)).left ≫
      colimit.ι (localFunctor hR D hD hDlift) i

@[reassoc]
lemma totalPullCover_trans_fst (a : R.arrows.category)
    {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    (totalPullCover hR D hD a).trans f ≫
        pullback.fst (totalMap D hD a) ((basePullCover hR a).f j) =
      pullback.fst (totalMap D hD a) ((basePullCover hR a).f i) := by
  exact (totalPullCover hR D hD a).trans_map f

@[reassoc]
lemma totalPullCover_trans_snd (a : R.arrows.category)
    {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    (totalPullCover hR D hD a).trans f ≫
        pullback.snd (totalMap D hD a) ((basePullCover hR a).f j) =
      pullback.snd (totalMap D hD a) ((basePullCover hR a).f i) ≫
        (basePullCover hR a).trans f := by
  rw [← cancel_mono ((basePullCover hR a).f j)]
  simp only [Category.assoc]
  rw [← pullback.condition,
    totalPullCover_trans_fst_assoc hR D hD a f,
    (basePullCover hR a).trans_map f, ← pullback.condition]

include hDlift in
@[reassoc]
lemma rIsoTotalPull_hom_naturality (a : R.arrows.category)
    {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    (D.map (rMap hR a f)).left ≫
        (rIsoTotalPull hR D hD hDlift a j).hom =
      (rIsoTotalPull hR D hD hDlift a i).hom ≫
        (totalPullCover hR D hD a).trans f := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [rIsoTotalPull_hom_f, totalPullCover_trans_fst, rIsoTotalPull_hom_f]
    have hr := rMap_rToA hR a f
    exact (congrArg CategoryTheory.CartesianArrowHom.left
      (D.map_comp (rMap hR a f) (rToA hR a j))).symm |>.trans
        (congrArg (fun k ↦ (D.map k).left) hr)
  · simp only [Category.assoc]
    rw [rIsoTotalPull_hom_toBase, totalPullCover_trans_snd,
      rIsoTotalPull_hom_toBase_assoc]
    exact (normalizedIsPullback D hD hDlift (rMap hR a f)).w

include hDlift in
@[reassoc]
lemma rIsoTotalPull_inv_naturality (a : R.arrows.category)
    {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    (totalPullCover hR D hD a).trans f ≫
        (rIsoTotalPull hR D hD hDlift a j).inv =
      (rIsoTotalPull hR D hD hDlift a i).inv ≫
        (D.map (rMap hR a f)).left := by
  rw [← cancel_epi (rIsoTotalPull hR D hD hDlift a i).hom]
  rw [← rIsoTotalPull_hom_naturality_assoc hR D hD hDlift a f]
  simp

@[reassoc]
lemma D_left_rMap_rToQ (a : R.arrows.category)
    {i j : (basePullCover hR a).I₀} (f : i ⟶ j) :
    (D.map (rMap hR a f)).left ≫ (D.map (rToQ hR a j)).left =
      (D.map (rToQ hR a i)).left ≫ (D.map (qMap hR f)).left := by
  calc
    _ = (D.map (rMap hR a f ≫ rToQ hR a j)).left :=
      (congrArg CategoryTheory.CartesianArrowHom.left
        (D.map_comp (rMap hR a f) (rToQ hR a j))).symm
    _ = (D.map (rToQ hR a i ≫ qMap hR f)).left :=
      congrArg (fun k ↦ (D.map k).left) (rMap_rToQ hR a f)
    _ = _ := congrArg CategoryTheory.CartesianArrowHom.left
      (D.map_comp (rToQ hR a i) (qMap hR f))

lemma localMapToGlued_compatible (a : R.arrows.category)
    {i j : (totalPullCover hR D hD a).I₀} (f : i ⟶ j) :
    (totalPullCover hR D hD a).trans f ≫
        localMapToGlued hR D hD hDlift a j =
      localMapToGlued hR D hD hDlift a i := by
  unfold localMapToGlued
  rw [rIsoTotalPull_inv_naturality_assoc hR D hD hDlift a f]
  rw [D_left_rMap_rToQ_assoc hR D a f]
  rw [← localFunctor_map_eq hR D hD hDlift]
  rw [colimit.w]

def mapToGlued (a : R.arrows.category) :
    (D.obj a : Arrow Scheme.{u}).left ⟶
      (relativeData hR D hD hDlift).glued :=
  (totalPullCover hR D hD a).glueMorphismsOfLocallyDirected
    (localMapToGlued hR D hD hDlift a)
    (localMapToGlued_compatible hR D hD hDlift a)

@[reassoc (attr := simp)]
lemma totalPullCover_f_mapToGlued (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (totalPullCover hR D hD a).f i ≫ mapToGlued hR D hD hDlift a =
      localMapToGlued hR D hD hDlift a i := by
  unfold mapToGlued
  exact (totalPullCover hR D hD a).map_glueMorphismsOfLocallyDirected
    (localMapToGlued hR D hD hDlift a)
    (localMapToGlued_compatible hR D hD hDlift a) i

lemma rIsoTotalPull_hom_f_mapToGlued (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).hom ≫
        (totalPullCover hR D hD a).f i ≫
          mapToGlued hR D hD hDlift a =
      (D.map (rToQ hR a i)).left ≫
        colimit.ι (localFunctor hR D hD hDlift) i := by
  simpa only [localMapToGlued, Category.assoc, Iso.hom_inv_id_assoc] using congrArg
    (fun k ↦ (rIsoTotalPull hR D hD hDlift a i).hom ≫ k)
    (totalPullCover_f_mapToGlued hR D hD hDlift a i)

include hDlift in
@[reassoc]
lemma D_left_rToQ_toBase (a : R.arrows.category)
    (i : (basePullCover hR a).I₀) :
    (D.map (rToQ hR a i)).left ≫
        ((D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (q hR i))) =
      ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i))) ≫
        (cover hR).pullbackHom a.obj.hom i := by
  exact (normalizedIsPullback D hD hDlift (rToQ hR a i)).w

lemma localPreMap_toBase (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).inv ≫
        (D.map (rToQ hR a i)).left ≫
        ((D.obj (q hR i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (q hR i))) ≫ (cover hR).f i =
      (rIsoTotalPull hR D hD hDlift a i).inv ≫
        ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i))) ≫
        (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i := by
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (rIsoTotalPull hR D hD hDlift a i).inv ≫
      k ≫ (cover hR).f i) (D_left_rToQ_toBase hR D hD hDlift a i)

lemma cover_pullbackHom_map_base (a : R.arrows.category)
    (i : (basePullCover hR a).I₀) :
    (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i =
      (basePullCover hR a).f i ≫ a.obj.hom := by
  exact (cover hR).pullbackHom_map a.obj.hom i

lemma totalPull_condition (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
        (basePullCover hR a).f i =
      (totalPullCover hR D hD a).f i ≫ totalMap D hD a := by
  exact (pullback.condition (f := totalMap D hD a)
    (g := (basePullCover hR a).f i)).symm

lemma localPreMap_to_totalBase (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    (rIsoTotalPull hR D hD hDlift a i).inv ≫
        ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i))) ≫
        (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i =
      (totalPullCover hR D hD a).f i ≫
        totalMap D hD a ≫ a.obj.hom := by
  calc
    _ = (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
        (cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (cover hR).pullbackHom a.obj.hom i ≫
          (cover hR).f i)
        (rIsoTotalPull_inv_toBase hR D hD hDlift a i)
    _ = (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
        (basePullCover hR a).f i ≫ a.obj.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫ k)
        (cover_pullbackHom_map_base hR a i)
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ a.obj.hom)
        (totalPull_condition hR D hD a i)

@[reassoc]
lemma relativeData_ι_toBase (i : (cover hR).I₀) :
    colimit.ι (localFunctor hR D hD hDlift) i ≫
        (relativeData hR D hD hDlift).toBase =
      (localToBase hR D hD hDlift).app i ≫ (cover hR).f i := by
  exact (relativeData hR D hD hDlift).ι_toBase i

lemma localMapToGlued_toBase (a : R.arrows.category)
    (i : (totalPullCover hR D hD a).I₀) :
    localMapToGlued hR D hD hDlift a i ≫
        (relativeData hR D hD hDlift).toBase =
      (totalPullCover hR D hD a).f i ≫
        totalMap D hD a ≫ a.obj.hom := by
  unfold localMapToGlued
  simp only [Category.assoc]
  rw [relativeData_ι_toBase hR D hD hDlift]
  rw [localToBase_app_eq]
  rw [localPreMap_toBase hR D hD hDlift a i]
  exact localPreMap_to_totalBase hR D hD hDlift a i

lemma mapToGlued_toBase (a : R.arrows.category) :
    mapToGlued hR D hD hDlift a ≫
        (relativeData hR D hD hDlift).toBase =
      totalMap D hD a ≫ a.obj.hom := by
  apply (totalPullCover hR D hD a).hom_ext
  intro i
  rw [totalPullCover_f_mapToGlued_assoc hR D hD hDlift a i]
  exact localMapToGlued_toBase hR D hD hDlift a i

lemma localCoreIsPullback (a : R.arrows.category)
    (i : (basePullCover hR a).I₀) :
    IsPullback
      ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
        eqToHom (hD (r hR a i)))
      ((D.map (rToQ hR a i)).left ≫
        colimit.ι (localFunctor hR D hD hDlift) i)
      ((cover hR).pullbackHom a.obj.hom i ≫ (cover hR).f i)
      (relativeData hR D hD hDlift).toBase := by
  have h₁ := (normalizedIsPullback D hD hDlift (rToQ hR a i)).flip
  have h₂ := (relativeData hR D hD hDlift).isPullback_natTrans_ι_toBase i
  simpa only [localToBase_app_eq, relativeData, rToQ_hom_left] using h₁.paste_vert h₂

lemma localIsPullback (a : R.arrows.category)
    (i : (basePullCover hR a).I₀) :
    IsPullback
      ((basePullCover hR a).pullbackHom (totalMap D hD a) i)
      ((totalPullCover hR D hD a).f i ≫ mapToGlued hR D hD hDlift a)
      ((basePullCover hR a).f i ≫ a.obj.hom)
      (relativeData hR D hD hDlift).toBase := by
  have h := localCoreIsPullback hR D hD hDlift a i
  rw [cover_pullbackHom_map_base hR a i] at h
  refine h.of_iso (rIsoTotalPull hR D hD hDlift a i)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (rIsoTotalPull_hom_toBaseCover hR D hD hDlift a i).symm
  · exact (rIsoTotalPull_hom_f_mapToGlued hR D hD hDlift a i).symm

lemma normalizedIsPullbackToGlued (a : R.arrows.category) :
    IsPullback (totalMap D hD a) (mapToGlued hR D hD hDlift a)
      a.obj.hom (relativeData hR D hD hDlift).toBase := by
  apply Scheme.isPullback_of_openCover (totalMap D hD a)
    (mapToGlued hR D hD hDlift a) a.obj.hom
    (relativeData hR D hD hDlift).toBase (basePullCover hR a)
  intro i
  exact localIsPullback hR D hD hDlift a i

lemma isPullbackToGlued (a : R.arrows.category) :
    IsPullback (mapToGlued hR D hD hDlift a)
      (D.obj a : Arrow Scheme.{u}).hom
      (relativeData hR D hD hDlift).toBase
      (eqToHom (hD a) ≫ a.obj.hom) := by
  refine (normalizedIsPullbackToGlued hR D hD hDlift a).flip.of_iso'
    (Iso.refl _) (Iso.refl _) (eqToIso (hD a)) (Iso.refl _)
    (by simp) ?_ (by simp) (by simp)
  rfl

def coconeMap (a : R.arrows.category) :
    D.obj a ⟶ CategoryTheory.ArrowCartesian.mk
      (relativeData hR D hD hDlift).toBase where
  left := mapToGlued hR D hD hDlift a
  right := eqToHom (hD a) ≫ a.obj.hom
  isPullback := isPullbackToGlued hR D hD hDlift a

def baseK {a b : R.arrows.category} (k : a ⟶ b) (i : (cover hR).I₀) :
    (basePullCover hR a).X i ⟶ (basePullCover hR b).X i :=
  pullback.lift ((basePullCover hR a).f i ≫ k.hom.left)
    ((cover hR).pullbackHom a.obj.hom i) (by
      rw [Category.assoc, Over.w k.hom]
      exact ((cover hR).pullbackHom_map a.obj.hom i).symm)

@[reassoc (attr := simp)]
lemma baseK_f {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    baseK hR k i ≫ (basePullCover hR b).f i =
      (basePullCover hR a).f i ≫ k.hom.left := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseK_pullbackHom {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    baseK hR k i ≫ (cover hR).pullbackHom b.obj.hom i =
      (cover hR).pullbackHom a.obj.hom i := by
  exact pullback.lift_snd _ _ _

def rK {a b : R.arrows.category} (k : a ⟶ b) (i : (cover hR).I₀) :
    r hR a i ⟶ r hR b i :=
  ObjectProperty.homMk (Over.homMk (baseK hR k i) (by
    change baseK hR k i ≫ ((basePullCover hR b).f i ≫ b.obj.hom) =
      (basePullCover hR a).f i ≫ a.obj.hom
    rw [← Category.assoc, baseK_f, Category.assoc, Over.w k.hom]))

@[simp]
lemma rK_rToA {a b : R.arrows.category} (k : a ⟶ b) (i : (cover hR).I₀) :
    rK hR k i ≫ rToA hR b i = rToA hR a i ≫ k := by
  apply ObjectProperty.hom_ext
  ext
  exact baseK_f hR k i

@[simp]
lemma rK_rToQ {a b : R.arrows.category} (k : a ⟶ b) (i : (cover hR).I₀) :
    rK hR k i ≫ rToQ hR b i = rToQ hR a i := by
  apply ObjectProperty.hom_ext
  ext
  exact baseK_pullbackHom hR k i

include hDlift in
lemma D_left_totalMap {a b : R.arrows.category} (k : a ⟶ b) :
    (D.map k).left ≫ totalMap D hD b =
      totalMap D hD a ≫ k.hom.left := by
  exact (normalizedIsPullback D hD hDlift k).w

def totalK {a b : R.arrows.category} (k : a ⟶ b) (i : (cover hR).I₀) :
    (totalPullCover hR D hD a).X i ⟶
      (totalPullCover hR D hD b).X i :=
  pullback.lift
    ((totalPullCover hR D hD a).f i ≫ (D.map k).left)
    ((basePullCover hR a).pullbackHom (totalMap D hD a) i ≫ baseK hR k i)
    (by
      calc
        ((totalPullCover hR D hD a).f i ≫ (D.map k).left) ≫
            totalMap D hD b =
          (totalPullCover hR D hD a).f i ≫
            (totalMap D hD a ≫ k.hom.left) := by
              simpa only [Category.assoc] using congrArg
                (fun z ↦ (totalPullCover hR D hD a).f i ≫ z)
                (D_left_totalMap D hD hDlift k)
        _ = ((basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
              (basePullCover hR a).f i) ≫ k.hom.left := by
          simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ k.hom.left)
            (totalPull_condition hR D hD a i).symm
        _ = (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
            (baseK hR k i ≫ (basePullCover hR b).f i) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫ z)
            (baseK_f hR k i).symm
        _ = ((basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
              baseK hR k i) ≫ (basePullCover hR b).f i :=
          (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
lemma totalK_f {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫ (totalPullCover hR D hD b).f i =
      (totalPullCover hR D hD a).f i ≫ (D.map k).left := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma totalK_fst {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫
        pullback.fst (totalMap D hD b) ((basePullCover hR b).f i) =
      pullback.fst (totalMap D hD a) ((basePullCover hR a).f i) ≫
        (D.map k).left := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma totalK_pullbackHom {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫
        (basePullCover hR b).pullbackHom (totalMap D hD b) i =
      (basePullCover hR a).pullbackHom (totalMap D hD a) i ≫
        baseK hR k i := by
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma totalK_snd {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫
        pullback.snd (totalMap D hD b) ((basePullCover hR b).f i) =
      pullback.snd (totalMap D hD a) ((basePullCover hR a).f i) ≫
        baseK hR k i := by
  exact pullback.lift_snd _ _ _

lemma D_left_rK_rToA {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    (D.map (rK hR k i)).left ≫ (D.map (rToA hR b i)).left =
      (D.map (rToA hR a i)).left ≫ (D.map k).left := by
  calc
    _ = (D.map (rK hR k i ≫ rToA hR b i)).left :=
      (congrArg CategoryTheory.CartesianArrowHom.left
        (D.map_comp (rK hR k i) (rToA hR b i))).symm
    _ = (D.map (rToA hR a i ≫ k)).left :=
      congrArg (fun z ↦ (D.map z).left) (rK_rToA hR k i)
    _ = _ := congrArg CategoryTheory.CartesianArrowHom.left
      (D.map_comp (rToA hR a i) k)

include hDlift in
lemma D_left_rK_toBase {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    (D.map (rK hR k i)).left ≫
        ((D.obj (r hR b i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR b i))) =
      ((D.obj (r hR a i) : Arrow Scheme.{u}).hom ≫
          eqToHom (hD (r hR a i))) ≫ baseK hR k i := by
  exact (normalizedIsPullback D hD hDlift (rK hR k i)).w

@[reassoc]
lemma rIsoTotalPull_hom_naturality_k {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    (D.map (rK hR k i)).left ≫
        (rIsoTotalPull hR D hD hDlift b i).hom =
      (rIsoTotalPull hR D hD hDlift a i).hom ≫
        totalK hR D hD hDlift k i := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [rIsoTotalPull_hom_f, totalK_fst, rIsoTotalPull_hom_f_assoc]
    exact D_left_rK_rToA hR D k i
  · simp only [Category.assoc]
    rw [rIsoTotalPull_hom_toBase, totalK_snd,
      rIsoTotalPull_hom_toBase_assoc]
    exact D_left_rK_toBase hR D hD hDlift k i

@[reassoc]
lemma rIsoTotalPull_inv_naturality_k {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫
        (rIsoTotalPull hR D hD hDlift b i).inv =
      (rIsoTotalPull hR D hD hDlift a i).inv ≫
        (D.map (rK hR k i)).left := by
  rw [← cancel_epi (rIsoTotalPull hR D hD hDlift a i).hom]
  rw [← rIsoTotalPull_hom_naturality_k_assoc hR D hD hDlift k i]
  simp

@[reassoc]
lemma D_left_rK_rToQ {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    (D.map (rK hR k i)).left ≫ (D.map (rToQ hR b i)).left =
      (D.map (rToQ hR a i)).left := by
  calc
    _ = (D.map (rK hR k i ≫ rToQ hR b i)).left :=
      (congrArg CategoryTheory.CartesianArrowHom.left
        (D.map_comp (rK hR k i) (rToQ hR b i))).symm
    _ = _ := congrArg (fun z ↦ (D.map z).left) (rK_rToQ hR k i)

lemma totalK_localMapToGlued {a b : R.arrows.category} (k : a ⟶ b)
    (i : (cover hR).I₀) :
    totalK hR D hD hDlift k i ≫
        localMapToGlued hR D hD hDlift b i =
      localMapToGlued hR D hD hDlift a i := by
  unfold localMapToGlued
  rw [rIsoTotalPull_inv_naturality_k_assoc hR D hD hDlift k i]
  rw [D_left_rK_rToQ_assoc hR D k i]

lemma mapToGlued_naturality_left {a b : R.arrows.category} (k : a ⟶ b) :
    (D.map k).left ≫ mapToGlued hR D hD hDlift b =
      mapToGlued hR D hD hDlift a := by
  apply (totalPullCover hR D hD a).hom_ext
  intro i
  rw [← totalK_f_assoc hR D hD hDlift k i]
  rw [totalPullCover_f_mapToGlued]
  rw [totalK_localMapToGlued hR D hD hDlift k i]
  rw [totalPullCover_f_mapToGlued]

include hDlift in
lemma coconeMap_naturality_right {a b : R.arrows.category} (k : a ⟶ b) :
    (D.map k).right ≫ (eqToHom (hD b) ≫ b.obj.hom) =
      eqToHom (hD a) ≫ a.obj.hom := by
  have hlift := hDlift k
  letI := hlift
  have hcomm := (IsHomLift.commSq
    (CategoryTheory.arrowCartesian Scheme.{u}).p k.hom.left (D.map k)).w
  change (D.map k).right ≫ eqToHom (hD b) =
    eqToHom (hD a) ≫ k.hom.left at hcomm
  calc
    _ = ((D.map k).right ≫ eqToHom (hD b)) ≫ b.obj.hom :=
      (Category.assoc _ _ _).symm
    _ = (eqToHom (hD a) ≫ k.hom.left) ≫ b.obj.hom := by rw [hcomm]
    _ = eqToHom (hD a) ≫ (k.hom.left ≫ b.obj.hom) :=
      Category.assoc _ _ _
    _ = _ := by rw [Over.w k.hom]

lemma coconeMap_naturality {a b : R.arrows.category} (k : a ⟶ b) :
    D.map k ≫ coconeMap hR D hD hDlift b =
      coconeMap hR D hD hDlift a := by
  apply CategoryTheory.CartesianArrowHom.ext
  · exact mapToGlued_naturality_left hR D hD hDlift k
  · exact coconeMap_naturality_right D hD hDlift k

lemma coconeMap_isHomLift (a : R.arrows.category) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p a.obj.hom
      (coconeMap hR D hD hDlift a) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p a.obj.hom
      (coconeMap hR D hD hDlift a) (hD a) rfl
  rfl

include hR hD hDlift in
theorem existsGluingObject :
    ∃ (A : CategoryTheory.ArrowCartesian Scheme.{u})
      (_ : (CategoryTheory.arrowCartesian Scheme.{u}).p.obj A = S)
      (ε : ∀ a : R.arrows.category, D.obj a ⟶ A),
      (∀ a : R.arrows.category,
        IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p a.obj.hom (ε a)) ∧
      ∀ {a b : R.arrows.category} (k : a ⟶ b), D.map k ≫ ε b = ε a := by
  refine ⟨CategoryTheory.ArrowCartesian.mk
    (relativeData hR D hD hDlift).toBase, rfl,
    coconeMap hR D hD hDlift, ?_, ?_⟩
  · exact coconeMap_isHomLift hR D hD hDlift
  · exact coconeMap_naturality hR D hD hDlift

namespace MorphismGluing

variable (A B : CategoryTheory.ArrowCartesian Scheme.{u})
variable (hA : (CategoryTheory.arrowCartesian Scheme.{u}).p.obj A = S)
variable (hB : (CategoryTheory.arrowCartesian Scheme.{u}).p.obj B = S)

def normalizedHom : (A : Arrow Scheme.{u}).left ⟶ S :=
  (A : Arrow Scheme.{u}).hom ≫ eqToHom hA

def objectCover : (A : Arrow Scheme.{u}).left.OpenCover :=
  (cover hR).pullback₁ (normalizedHom A hA)

instance objectCover_category : Category (objectCover hR A hA).I₀ :=
  inferInstanceAs (Category (cover hR).I₀)

instance objectCover_locallyDirected : (objectCover hR A hA).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover (cover hR) (normalizedHom A hA)

def liftObject (i : (cover hR).I₀) :
    CategoryTheory.ArrowCartesian Scheme.{u} :=
  CategoryTheory.ArrowCartesian.mk
    ((cover hR).pullbackHom (normalizedHom A hA) i)

lemma objectCover_f_eq (i : (cover hR).I₀) :
    (objectCover hR A hA).f i =
      pullback.fst (normalizedHom A hA) ((cover hR).f i) :=
  rfl

lemma liftObject_hom_eq (i : (cover hR).I₀) :
    (liftObject hR A hA i : Arrow Scheme.{u}).hom =
      pullback.snd (normalizedHom A hA) ((cover hR).f i) :=
  rfl

def liftTo (i : (cover hR).I₀) : liftObject hR A hA i ⟶ A where
  left := (objectCover hR A hA).f i
  right := (cover hR).f i ≫ eqToHom hA.symm
  isPullback := by
    let hp := IsPullback.of_hasPullback (normalizedHom A hA) ((cover hR).f i)
    refine hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (eqToIso hA).symm ?_ ?_ ?_ (by simp)
    · exact (objectCover_f_eq hR A hA i).symm
    · exact (liftObject_hom_eq hR A hA i).symm
    simp [normalizedHom]

lemma liftTo_isHomLift (i : (cover hR).I₀) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).f i)
      (liftTo hR A hA i) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).f i)
      (liftTo hR A hA i) rfl hA
  change ((cover hR).f i ≫ eqToHom hA.symm) ≫ eqToHom hA =
    (cover hR).f i
  simp

@[reassoc]
lemma objectCover_trans_fst {i j : (cover hR).I₀} (f : i ⟶ j) :
    (objectCover hR A hA).trans f ≫
        pullback.fst (normalizedHom A hA) ((cover hR).f j) =
      pullback.fst (normalizedHom A hA) ((cover hR).f i) := by
  exact (objectCover hR A hA).trans_map f

@[reassoc]
lemma objectCover_trans_snd {i j : (cover hR).I₀} (f : i ⟶ j) :
    (objectCover hR A hA).trans f ≫
        pullback.snd (normalizedHom A hA) ((cover hR).f j) =
      pullback.snd (normalizedHom A hA) ((cover hR).f i) ≫
        (cover hR).trans f := by
  rw [← cancel_mono ((cover hR).f j)]
  simp only [Category.assoc]
  rw [← pullback.condition,
    objectCover_trans_fst_assoc hR A hA f,
    (cover hR).trans_map f, ← pullback.condition]

lemma liftTransition_isPullback {i j : (cover hR).I₀} (f : i ⟶ j) :
    IsPullback ((objectCover hR A hA).trans f)
      (liftObject hR A hA i : Arrow Scheme.{u}).hom
      (liftObject hR A hA j : Arrow Scheme.{u}).hom
      ((cover hR).trans f) := by
  have hi₀ := IsPullback.of_hasPullback (normalizedHom A hA) ((cover hR).f i)
  have hj₀ := IsPullback.of_hasPullback (normalizedHom A hA) ((cover hR).f j)
  have hi : IsPullback ((objectCover hR A hA).f i)
      (liftObject hR A hA i : Arrow Scheme.{u}).hom
      (normalizedHom A hA) ((cover hR).f i) := by
    simpa only [objectCover_f_eq, liftObject_hom_eq] using hi₀
  have hj : IsPullback ((objectCover hR A hA).f j)
      (liftObject hR A hA j : Arrow Scheme.{u}).hom
      (normalizedHom A hA) ((cover hR).f j) := by
    simpa only [objectCover_f_eq, liftObject_hom_eq] using hj₀
  have hcomp : IsPullback
      ((objectCover hR A hA).trans f ≫ (objectCover hR A hA).f j)
      (liftObject hR A hA i : Arrow Scheme.{u}).hom
      (normalizedHom A hA)
      ((cover hR).trans f ≫ (cover hR).f j) := by
    simpa only [(objectCover hR A hA).trans_map,
      (cover hR).trans_map] using hi
  apply hcomp.of_right
  · simpa only [liftObject_hom_eq] using objectCover_trans_snd hR A hA f
  · exact hj

def liftTransition {i j : (cover hR).I₀} (f : i ⟶ j) :
    liftObject hR A hA i ⟶ liftObject hR A hA j where
  left := (objectCover hR A hA).trans f
  right := (cover hR).trans f
  isPullback := liftTransition_isPullback hR A hA f

lemma liftTransition_isHomLift {i j : (cover hR).I₀} (f : i ⟶ j) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).trans f)
      (liftTransition hR A hA f) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).trans f)
      (liftTransition hR A hA f) rfl rfl
  rfl

@[simp]
lemma liftTransition_comp_liftTo {i j : (cover hR).I₀} (f : i ⟶ j) :
    liftTransition hR A hA f ≫ liftTo hR A hA j = liftTo hR A hA i := by
  apply CategoryTheory.CartesianArrowHom.ext
  · exact (objectCover hR A hA).trans_map f
  · change (cover hR).trans f ≫
      ((cover hR).f j ≫ eqToHom hA.symm) =
        (cover hR).f i ≫ eqToHom hA.symm
    rw [← Category.assoc, (cover hR).trans_map]

variable (phi : ∀ {T : Scheme.{u}} {g : T ⟶ S}, R g →
  ∀ {x : CategoryTheory.ArrowCartesian Scheme.{u}} (xi : x ⟶ A),
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi → (x ⟶ B))
variable (hphi : ∀ {T : Scheme.{u}} {g : T ⟶ S} (hg : R g)
  {x : CategoryTheory.ArrowCartesian Scheme.{u}} (xi : x ⟶ A)
  (hxi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi),
  IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g (phi hg xi hxi))
variable (hcompat : ∀ {T' T : Scheme.{u}} {g : T ⟶ S} (hg : R g)
  {f : T' ⟶ T} {x' x : CategoryTheory.ArrowCartesian Scheme.{u}}
  (chi : x' ⟶ x) (xi : x ⟶ A)
  (hxi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi)
  (hchi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p f chi),
  phi (R.downward_closed hg f) (chi ≫ xi) inferInstance =
    chi ≫ phi hg xi hxi)

def localTheta (i : (cover hR).I₀) : liftObject hR A hA i ⟶ B :=
  phi (Scheme.zariskiBasisCoverOfSieve_mem R hR i)
    (liftTo hR A hA i) (liftTo_isHomLift hR A hA i)

include hphi in
lemma localTheta_isHomLift (i : (cover hR).I₀) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).f i)
      (localTheta hR A B hA phi i) :=
  hphi (Scheme.zariskiBasisCoverOfSieve_mem R hR i)
    (liftTo hR A hA i) (liftTo_isHomLift hR A hA i)

include hcompat in
lemma liftTransition_comp_localTheta {i j : (cover hR).I₀} (f : i ⟶ j) :
    liftTransition hR A hA f ≫ localTheta hR A B hA phi j =
      localTheta hR A B hA phi i := by
  have H := hcompat (Scheme.zariskiBasisCoverOfSieve_mem R hR j)
    (liftTransition hR A hA f) (liftTo hR A hA j)
    (liftTo_isHomLift hR A hA j) (liftTransition_isHomLift hR A hA f)
  simp only [liftTransition_comp_liftTo, (cover hR).trans_map] at H
  unfold localTheta
  convert H.symm using 1

include hcompat in
lemma localTheta_left_compatible {i j : (cover hR).I₀} (f : i ⟶ j) :
    (objectCover hR A hA).trans f ≫ (localTheta hR A B hA phi j).left =
      (localTheta hR A B hA phi i).left := by
  exact congrArg CategoryTheory.CartesianArrowHom.left
    (liftTransition_comp_localTheta hR A B hA phi hcompat f)

def PhiLeft : (A : Arrow Scheme.{u}).left ⟶ (B : Arrow Scheme.{u}).left :=
  (objectCover hR A hA).glueMorphismsOfLocallyDirected
    (fun i ↦ (localTheta hR A B hA phi i).left)
    (localTheta_left_compatible hR A B hA phi hcompat)

@[reassoc (attr := simp)]
lemma objectCover_f_PhiLeft (i : (cover hR).I₀) :
    (objectCover hR A hA).f i ≫ PhiLeft hR A B hA phi hcompat =
      (localTheta hR A B hA phi i).left := by
  unfold PhiLeft
  exact (objectCover hR A hA).map_glueMorphismsOfLocallyDirected
    (fun i ↦ (localTheta hR A B hA phi i).left)
    (localTheta_left_compatible hR A B hA phi hcompat) i

include hphi in
lemma localTheta_normalizedIsPullback (i : (cover hR).I₀) :
    IsPullback (localTheta hR A B hA phi i).left
      (liftObject hR A hA i : Arrow Scheme.{u}).hom
      (normalizedHom B hB) ((cover hR).f i) := by
  have ht := localTheta_isHomLift hR A B hA phi hphi i
  letI := ht
  have hcomm := (IsHomLift.commSq
    (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).f i)
      (localTheta hR A B hA phi i)).w
  change (localTheta hR A B hA phi i).right ≫ eqToHom hB =
    (cover hR).f i at hcomm
  refine (localTheta hR A B hA phi i).isPullback.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso hB)
    (by simp) (by simp) ?_ hcomm
  rfl

include hphi in
lemma PhiLeft_localIsPullback (i : (cover hR).I₀) :
    IsPullback ((cover hR).pullbackHom (normalizedHom A hA) i)
      ((objectCover hR A hA).f i ≫ PhiLeft hR A B hA phi hcompat)
      ((cover hR).f i ≫ 𝟙 S) (normalizedHom B hB) := by
  have H := (localTheta_normalizedIsPullback hR A B hA hB phi hphi i).flip
  change IsPullback ((cover hR).pullbackHom (normalizedHom A hA) i)
    (localTheta hR A B hA phi i).left ((cover hR).f i)
      (normalizedHom B hB) at H
  simpa only [objectCover_f_PhiLeft, Category.comp_id] using H

include hphi in
lemma normalizedPhiIsPullback :
    IsPullback (normalizedHom A hA) (PhiLeft hR A B hA phi hcompat)
      (𝟙 S) (normalizedHom B hB) := by
  apply Scheme.isPullback_of_openCover (normalizedHom A hA)
    (PhiLeft hR A B hA phi hcompat) (𝟙 S) (normalizedHom B hB)
    (cover hR)
  intro i
  exact PhiLeft_localIsPullback hR A B hA hB phi hphi hcompat i

def baseIsoHom : (A : Arrow Scheme.{u}).right ⟶ (B : Arrow Scheme.{u}).right :=
  eqToHom hA ≫ eqToHom hB.symm

include hphi in
lemma PhiIsPullback :
    IsPullback (PhiLeft hR A B hA phi hcompat) (A : Arrow Scheme.{u}).hom
      (B : Arrow Scheme.{u}).hom (baseIsoHom A B hA hB) := by
  exact (normalizedPhiIsPullback hR A B hA hB phi hphi hcompat).flip.of_iso'
    (Iso.refl _) (Iso.refl _) (eqToIso hA) (eqToIso hB)
    (by simp) (by rfl) (by rfl) (by simp [baseIsoHom])

include hR hphi hcompat in
def Phi : A ⟶ B where
  left := PhiLeft hR A B hA phi hcompat
  right := baseIsoHom A B hA hB
  isPullback := PhiIsPullback hR A B hA hB phi hphi hcompat

include hR hphi hcompat in
lemma Phi_isHomLift :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S)
      (Phi hR A B hA hB phi hphi hcompat) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S)
      (Phi hR A B hA hB phi hphi hcompat) hA hB
  change baseIsoHom A B hA hB ≫ eqToHom hB = eqToHom hA
  simp [baseIsoHom]

include hphi in
lemma localTheta_right_eq (i : (cover hR).I₀) :
    (localTheta hR A B hA phi i).right =
      (cover hR).f i ≫ eqToHom hB.symm := by
  have ht := localTheta_isHomLift hR A B hA phi hphi i
  letI := ht
  have hcomm := (IsHomLift.commSq
    (CategoryTheory.arrowCartesian Scheme.{u}).p ((cover hR).f i)
      (localTheta hR A B hA phi i)).w
  change (localTheta hR A B hA phi i).right ≫ eqToHom hB =
    (cover hR).f i at hcomm
  rw [← cancel_mono (eqToHom hB)]
  simpa using hcomm

@[simp]
lemma liftTo_comp_Phi (i : (cover hR).I₀) :
    liftTo hR A hA i ≫ Phi hR A B hA hB phi hphi hcompat =
      localTheta hR A B hA phi i := by
  apply CategoryTheory.CartesianArrowHom.ext
  · exact objectCover_f_PhiLeft hR A B hA phi hcompat i
  · change ((cover hR).f i ≫ eqToHom hA.symm) ≫
        baseIsoHom A B hA hB = (localTheta hR A B hA phi i).right
    rw [localTheta_right_eq hR A B hA hB phi hphi i]
    simp [baseIsoHom]

/-! We next compare the glued morphism with the prescribed morphism over an
arbitrary member of the covering sieve.  The comparison is made on the pullback
of the fixed locally directed cover. -/

def pullObject {T : Scheme.{u}} (g : T ⟶ S) :
    CategoryTheory.ArrowCartesian Scheme.{u} :=
  CategoryTheory.ArrowCartesian.mk
    (pullback.snd (normalizedHom A hA) g)

def pullTo {T : Scheme.{u}} (g : T ⟶ S) : pullObject A hA g ⟶ A where
  left := pullback.fst (normalizedHom A hA) g
  right := g ≫ eqToHom hA.symm
  isPullback := by
    let hp := IsPullback.of_hasPullback (normalizedHom A hA) g
    refine hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (eqToIso hA).symm (by rfl) (by rfl) (by simp [normalizedHom]) (by rfl)

lemma pullTo_isHomLift {T : Scheme.{u}} (g : T ⟶ S) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g (pullTo A hA g) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p g (pullTo A hA g) rfl hA
  change (g ≫ eqToHom hA.symm) ≫ eqToHom hA = g
  simp

def baseCover {T : Scheme.{u}} (g : T ⟶ S) : T.OpenCover :=
  (cover hR).pullback₁ g

instance baseCover_category {T : Scheme.{u}} (g : T ⟶ S) :
    Category (baseCover hR g).I₀ :=
  inferInstanceAs (Category (cover hR).I₀)

instance baseCover_locallyDirected {T : Scheme.{u}} (g : T ⟶ S) :
    (baseCover hR g).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover (cover hR) g

def sourceCover {T : Scheme.{u}} (g : T ⟶ S) :
    ((pullObject A hA g : Arrow Scheme.{u}).left).OpenCover :=
  (baseCover hR g).pullback₁ (pullObject A hA g : Arrow Scheme.{u}).hom

instance sourceCover_category {T : Scheme.{u}} (g : T ⟶ S) :
    Category (sourceCover hR A hA g).I₀ :=
  inferInstanceAs (Category (cover hR).I₀)

instance sourceCover_locallyDirected {T : Scheme.{u}} (g : T ⟶ S) :
    (sourceCover hR A hA g).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover (baseCover hR g)
    (pullObject A hA g : Arrow Scheme.{u}).hom

def restrictedObject {T : Scheme.{u}} (g : T ⟶ S)
    (i : (cover hR).I₀) : CategoryTheory.ArrowCartesian Scheme.{u} :=
  CategoryTheory.ArrowCartesian.mk
    ((baseCover hR g).pullbackHom
      (pullObject A hA g : Arrow Scheme.{u}).hom i)

def restrictTo {T : Scheme.{u}} (g : T ⟶ S) (i : (cover hR).I₀) :
    restrictedObject hR A hA g i ⟶ pullObject A hA g where
  left := (sourceCover hR A hA g).f i
  right := (baseCover hR g).f i
  isPullback := by
    exact IsPullback.of_hasPullback
      (pullObject A hA g : Arrow Scheme.{u}).hom ((baseCover hR g).f i)

lemma restrictTo_isHomLift {T : Scheme.{u}} (g : T ⟶ S)
    (i : (cover hR).I₀) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i) (restrictTo hR A hA g i) := by
  apply IsHomLift.of_commsq
      (CategoryTheory.arrowCartesian Scheme.{u}).p ((baseCover hR g).f i)
      (restrictTo hR A hA g i) rfl rfl
  rfl

def basisFactor {T : Scheme.{u}} (g : T ⟶ S) (i : (cover hR).I₀) :
    restrictedObject hR A hA g i ⟶ liftObject hR A hA i := by
  haveI := liftTo_isHomLift hR A hA i
  haveI : IsStronglyCartesian (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).f i) (liftTo hR A hA i) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  haveI := restrictTo_isHomLift hR A hA g i
  haveI := pullTo_isHomLift A hA g
  haveI hcomp : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i ≫ g)
      (restrictTo hR A hA g i ≫ pullTo A hA g) :=
    IsHomLift.comp (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i) g (restrictTo hR A hA g i) (pullTo A hA g)
  exact IsStronglyCartesian.map
    (p := (CategoryTheory.arrowCartesian Scheme.{u}).p)
    (f := (cover hR).f i) (φ := liftTo hR A hA i)
    (g := (cover hR).pullbackHom g i)
    (f' := (baseCover hR g).f i ≫ g)
    ((cover hR).pullbackHom_map g i).symm
    (restrictTo hR A hA g i ≫ pullTo A hA g)

lemma basisFactor_isHomLift {T : Scheme.{u}} (g : T ⟶ S)
    (i : (cover hR).I₀) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).pullbackHom g i) (basisFactor hR A hA g i) := by
  unfold basisFactor
  infer_instance

@[simp]
lemma basisFactor_comp_liftTo {T : Scheme.{u}} (g : T ⟶ S)
    (i : (cover hR).I₀) :
    basisFactor hR A hA g i ≫ liftTo hR A hA i =
      restrictTo hR A hA g i ≫ pullTo A hA g := by
  haveI := liftTo_isHomLift hR A hA i
  haveI : IsStronglyCartesian (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).f i) (liftTo hR A hA i) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  haveI := restrictTo_isHomLift hR A hA g i
  haveI := pullTo_isHomLift A hA g
  haveI hcomp : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i ≫ g)
      (restrictTo hR A hA g i ≫ pullTo A hA g) :=
    IsHomLift.comp (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i) g (restrictTo hR A hA g i) (pullTo A hA g)
  exact @IsStronglyCartesian.fac Scheme.{u}
    (CategoryTheory.ArrowCartesian Scheme.{u}) inferInstance inferInstance
    (CategoryTheory.arrowCartesian Scheme.{u}).p _ _ _ _
    ((cover hR).f i) (liftTo hR A hA i) (by infer_instance)
    _ _ _ _ ((cover hR).pullbackHom_map g i).symm
    (restrictTo hR A hA g i ≫ pullTo A hA g) hcomp

def canonicalTheta {T : Scheme.{u}} {g : T ⟶ S} (hg : R g) :
    pullObject A hA g ⟶ B :=
  phi hg (pullTo A hA g) (pullTo_isHomLift A hA g)

include hphi in
lemma canonicalTheta_isHomLift {T : Scheme.{u}} {g : T ⟶ S} (hg : R g) :
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (canonicalTheta A B hA phi hg) :=
  hphi hg (pullTo A hA g) (pullTo_isHomLift A hA g)

include hphi hcompat in
lemma restrictTo_comp_canonicalTheta {T : Scheme.{u}} {g : T ⟶ S}
    (hg : R g) (i : (cover hR).I₀) :
    restrictTo hR A hA g i ≫ canonicalTheta A B hA phi hg =
      (restrictTo hR A hA g i ≫ pullTo A hA g) ≫
        Phi hR A B hA hB phi hphi hcompat := by
  have hres := restrictTo_isHomLift hR A hA g i
  have hpull := pullTo_isHomLift A hA g
  have H₁ := hcompat hg (restrictTo hR A hA g i) (pullTo A hA g) hpull hres
  have hbasis : R ((cover hR).f i) :=
    Scheme.zariskiBasisCoverOfSieve_mem R hR i
  have hfac := basisFactor_isHomLift hR A hA g i
  have hlift := liftTo_isHomLift hR A hA i
  have H₂ := hcompat hbasis (basisFactor hR A hA g i)
    (liftTo hR A hA i) hlift hfac
  have hcompR : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i ≫ g)
      (restrictTo hR A hA g i ≫ pullTo A hA g) := by
    letI := hres
    letI := hpull
    exact IsHomLift.comp (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((baseCover hR g).f i) g (restrictTo hR A hA g i) (pullTo A hA g)
  have hcompQ : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).pullbackHom g i ≫ (cover hR).f i)
      (restrictTo hR A hA g i ≫ pullTo A hA g) := by
    rw [(cover hR).pullbackHom_map g i]
    exact hcompR
  let LiftedQ := { z : restrictedObject hR A hA g i ⟶ A //
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      ((cover hR).pullbackHom g i ≫ (cover hR).f i) z }
  have hpairs :
      (⟨basisFactor hR A hA g i ≫ liftTo hR A hA i,
        IsHomLift.comp (CategoryTheory.arrowCartesian Scheme.{u}).p
          ((cover hR).pullbackHom g i) ((cover hR).f i)
          (basisFactor hR A hA g i) (liftTo hR A hA i)⟩ : LiftedQ) =
        ⟨restrictTo hR A hA g i ≫ pullTo A hA g, hcompQ⟩ := by
    apply Subtype.ext
    exact basisFactor_comp_liftTo hR A hA g i
  have hphisame := congrArg
    (fun z : LiftedQ ↦ phi (R.downward_closed hbasis
      ((cover hR).pullbackHom g i)) z.1 z.2) hpairs
  have H₂' :
      phi (R.downward_closed hbasis ((cover hR).pullbackHom g i))
          (restrictTo hR A hA g i ≫ pullTo A hA g) hcompQ =
        basisFactor hR A hA g i ≫
          phi hbasis (liftTo hR A hA i) hlift := by
    exact hphisame.symm.trans (by simpa only using H₂)
  have H₂'' :
      phi (R.downward_closed hg ((baseCover hR g).f i))
          (restrictTo hR A hA g i ≫ pullTo A hA g) hcompR =
        basisFactor hR A hA g i ≫
          phi hbasis (liftTo hR A hA i) hlift := by
    simpa only [(cover hR).pullbackHom_map g i] using H₂'
  calc
    restrictTo hR A hA g i ≫ canonicalTheta A B hA phi hg =
        phi (R.downward_closed hg ((baseCover hR g).f i))
          (restrictTo hR A hA g i ≫ pullTo A hA g) hcompR := by
      simpa only [canonicalTheta] using H₁.symm
    _ = basisFactor hR A hA g i ≫ localTheta hR A B hA phi i := by
      simpa only [localTheta] using H₂''
    _ = basisFactor hR A hA g i ≫
        (liftTo hR A hA i ≫ Phi hR A B hA hB phi hphi hcompat) := by
      rw [liftTo_comp_Phi hR A B hA hB phi hphi hcompat i]
    _ = (basisFactor hR A hA g i ≫ liftTo hR A hA i) ≫
        Phi hR A B hA hB phi hphi hcompat := Category.assoc _ _ _ |>.symm
    _ = (restrictTo hR A hA g i ≫ pullTo A hA g) ≫
        Phi hR A B hA hB phi hphi hcompat := by
      rw [basisFactor_comp_liftTo hR A hA g i]

include hphi hcompat in
lemma canonicalTheta_left_eq {T : Scheme.{u}} {g : T ⟶ S} (hg : R g) :
    (canonicalTheta A B hA phi hg).left =
      (pullTo A hA g ≫ Phi hR A B hA hB phi hphi hcompat).left := by
  apply (sourceCover hR A hA g).hom_ext
  intro i
  have H := congrArg CategoryTheory.CartesianArrowHom.left
    (restrictTo_comp_canonicalTheta hR A B hA hB phi hphi hcompat hg i)
  exact H

include hphi hcompat in
lemma canonicalTheta_eq {T : Scheme.{u}} {g : T ⟶ S} (hg : R g) :
    canonicalTheta A B hA phi hg =
      pullTo A hA g ≫ Phi hR A B hA hB phi hphi hcompat := by
  apply CategoryTheory.CartesianArrowHom.ext
  · exact canonicalTheta_left_eq hR A B hA hB phi hphi hcompat hg
  · have htheta := canonicalTheta_isHomLift A B hA phi hphi hg
    have hpull := pullTo_isHomLift A hA g
    have hPhi := Phi_isHomLift hR A B hA hB phi hphi hcompat
    letI := hpull
    letI := hPhi
    have hcomp : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g
        (pullTo A hA g ≫ Phi hR A B hA hB phi hphi hcompat) := inferInstance
    letI := htheta
    letI := hcomp
    have hthetaComm := (IsHomLift.commSq
      (CategoryTheory.arrowCartesian Scheme.{u}).p g
        (canonicalTheta A B hA phi hg)).w
    have hcompComm := (IsHomLift.commSq
      (CategoryTheory.arrowCartesian Scheme.{u}).p g
        (pullTo A hA g ≫ Phi hR A B hA hB phi hphi hcompat)).w
    change (canonicalTheta A B hA phi hg).right ≫ eqToHom hB = g at hthetaComm
    change (pullTo A hA g ≫
      Phi hR A B hA hB phi hphi hcompat).right ≫ eqToHom hB = g at hcompComm
    rw [← cancel_mono (eqToHom hB)]
    exact hthetaComm.trans hcompComm.symm

include hphi hcompat in
lemma factorization {T : Scheme.{u}} {g : T ⟶ S} (hg : R g)
    {x : CategoryTheory.ArrowCartesian Scheme.{u}} (xi : x ⟶ A)
    (hxi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi) :
    phi hg xi hxi = xi ≫ Phi hR A B hA hB phi hphi hcompat := by
  letI := hxi
  letI := pullTo_isHomLift A hA g
  letI : IsStronglyCartesian (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (pullTo A hA g) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
  let chi : x ⟶ pullObject A hA g :=
    IsStronglyCartesian.map (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (pullTo A hA g) (Category.id_comp g).symm xi
  have hchi_fac : chi ≫ pullTo A hA g = xi :=
    IsStronglyCartesian.fac (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (pullTo A hA g) (Category.id_comp g).symm xi
  have hchi_lift : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p
      (𝟙 T) chi := by
    simpa [chi] using IsStronglyCartesian.map_isHomLift
      (CategoryTheory.arrowCartesian Scheme.{u}).p g (pullTo A hA g)
        (Category.id_comp g).symm xi
  have hcompLift : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (chi ≫ pullTo A hA g) := by
    letI := hchi_lift
    change IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g
      (chi ≫ pullTo A hA g)
    simpa only [Category.id_comp] using
      IsHomLift.comp (CategoryTheory.arrowCartesian Scheme.{u}).p
        (𝟙 T) g chi (pullTo A hA g)
  let Lifted := { q : x ⟶ A //
    IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g q }
  have hpairs : (⟨chi ≫ pullTo A hA g, hcompLift⟩ : Lifted) = ⟨xi, hxi⟩ := by
    apply Subtype.ext
    exact hchi_fac
  have hphisame := congrArg (fun q : Lifted ↦ phi hg q.1 q.2) hpairs
  have hcompat' := hcompat hg chi (pullTo A hA g)
    (pullTo_isHomLift A hA g) hchi_lift
  simp only [Category.id_comp] at hcompat'
  have hfirst : phi hg xi hxi = chi ≫ canonicalTheta A B hA phi hg := by
    exact hphisame.symm.trans (by simpa only [canonicalTheta] using hcompat')
  calc
    phi hg xi hxi = chi ≫ canonicalTheta A B hA phi hg := hfirst
    _ = chi ≫ (pullTo A hA g ≫
        Phi hR A B hA hB phi hphi hcompat) := by
      rw [canonicalTheta_eq hR A B hA hB phi hphi hcompat hg]
    _ = (chi ≫ pullTo A hA g) ≫
        Phi hR A B hA hB phi hphi hcompat := Category.assoc _ _ _ |>.symm
    _ = xi ≫ Phi hR A B hA hB phi hphi hcompat := by rw [hchi_fac]

include hphi hcompat in
lemma uniqueness (Psi : A ⟶ B)
    (hPsi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S) Psi ∧
      ∀ {T : Scheme.{u}} {g : T ⟶ S} (hg : R g)
        {x : CategoryTheory.ArrowCartesian Scheme.{u}} (xi : x ⟶ A)
        (hxi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi),
          phi hg xi hxi = xi ≫ Psi) :
    Psi = Phi hR A B hA hB phi hphi hcompat := by
  apply CategoryTheory.CartesianArrowHom.ext
  · apply (objectCover hR A hA).hom_ext
    intro i
    have hbasis : R ((cover hR).f i) :=
      Scheme.zariskiBasisCoverOfSieve_mem R hR i
    have hlocal := hPsi.2 hbasis (liftTo hR A hA i)
      (liftTo_isHomLift hR A hA i)
    have hlocalLeft := congrArg CategoryTheory.CartesianArrowHom.left hlocal
    have hPhiLocal := congrArg CategoryTheory.CartesianArrowHom.left
      (liftTo_comp_Phi hR A B hA hB phi hphi hcompat i)
    exact hlocalLeft.symm.trans hPhiLocal.symm
  · have hPhiLift := Phi_isHomLift hR A B hA hB phi hphi hcompat
    letI := hPsi.1
    letI := hPhiLift
    have hPsiComm := (IsHomLift.commSq
      (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S) Psi).w
    have hPhiComm := (IsHomLift.commSq
      (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S)
        (Phi hR A B hA hB phi hphi hcompat)).w
    change Psi.right ≫ eqToHom hB = eqToHom hA at hPsiComm
    change (Phi hR A B hA hB phi hphi hcompat).right ≫ eqToHom hB =
      eqToHom hA at hPhiComm
    rw [← cancel_mono (eqToHom hB)]
    exact hPsiComm.trans hPhiComm.symm

include hR hA hB hphi hcompat in
theorem existsUniqueGluingHom :
    ∃! Psi : A ⟶ B,
      IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p (𝟙 S) Psi ∧
      ∀ {T : Scheme.{u}} {g : T ⟶ S} (hg : R g)
        {x : CategoryTheory.ArrowCartesian Scheme.{u}} (xi : x ⟶ A)
        (hxi : IsHomLift (CategoryTheory.arrowCartesian Scheme.{u}).p g xi),
          phi hg xi hxi = xi ≫ Psi := by
  refine ⟨Phi hR A B hA hB phi hphi hcompat, ⟨?_, ?_⟩, ?_⟩
  · exact Phi_isHomLift hR A B hA hB phi hphi hcompat
  · exact factorization hR A B hA hB phi hphi hcompat
  · intro Psi hPsi
    exact uniqueness hR A B hA hB phi hphi hcompat Psi hPsi

end MorphismGluing

end

end AlgebraicGeometry.Scheme.ArrowCartesianZariski
