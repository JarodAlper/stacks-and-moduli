module

public import StacksAndModuli.API.ActionQuotientFpqcMorphisms
public import StacksAndModuli.API.GlobalPrincipalBundleFpqcProperties

/-!
# FPQC descent of objects in action quotient prestacks

This file lifts effective descent of principal bundles to principal bundles
equipped with an equivariant map to a fixed target. The map to the target is
glued on the pullback of the covering sieve to the descended total space.
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

variable {S : Scheme.{u}} {G U : Over S} [GrpObj G] [ModObj G U]
variable {T : Over S} {R : Sieve T}
variable (D : R.arrows.category ⥤ ActionQuotientObj G U)
variable (hDobj : ∀ q : R.arrows.category,
  (actionQuotientPrestack G U).p.obj (D.obj q) = q.obj.left)
variable (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
  IsHomLift (actionQuotientPrestack G U).p k.hom.left (D.map k))

namespace ActionQuotientObjectDescent

/-- Forget an action-quotient descent diagram to its principal bundles. -/
def carrierFunctor : R.arrows.category ⥤ ClassifyingObj G :=
  D ⋙ (actionQuotientPrestack.forget (G := G) (U := U)).toFunctor

include hDobj in
lemma carrierFunctor_obj (q : R.arrows.category) :
    (classifyingPrestack G).p.obj ((carrierFunctor D).obj q) = q.obj.left :=
  hDobj q

include hDmap in
lemma carrierFunctor_map {q r : R.arrows.category} (k : q ⟶ r) :
    IsHomLift (classifyingPrestack G).p k.hom.left
      ((carrierFunctor D).map k) := by
  letI := hDmap k
  exact (actionQuotientPrestack.forget (G := G) (U := U)).preserves_isHomLift
    k.hom.left (D.map k)

variable (A : ClassifyingObj.UnderlyingGluing (carrierFunctor D)
  (carrierFunctor_obj D hDobj) (carrierFunctor_map D hDmap))

/-- The local map to `U` selected by a point of the glued total space. -/
noncomputable def quotientLocalMap {Z : Over S} (k : Z ⟶ A.P)
    (hk : R (k ≫ A.p)) : Z ⟶ U :=
  A.point k hk ≫ (D.obj (A.localObj k hk)).map

lemma quotientLocalMap_naturality {W Z : Over S} (h : W ⟶ Z)
    (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    quotientLocalMap D hDobj hDmap A (h ≫ k) (A.local_mem h k hk) =
      h ≫ quotientLocalMap D hDobj hDmap A k hk := by
  let q := A.localObj k hk
  let q' := A.localObj (h ≫ k) (A.local_mem h k hk)
  let m := A.localMap h k hk
  change (A.point (h ≫ k) (A.local_mem h k hk) ≫
      (D.obj q').map) = h ≫ (A.point k hk ≫ (D.obj q).map)
  have hpoint := A.point_naturality h k hk
  have hmap := (D.map m).map_naturality
  change ((carrierFunctor D).map m).total ≫ (D.obj q).map =
    (D.obj q').map at hmap
  rw [← hmap, ← Category.assoc, hpoint, Category.assoc]

/-- The descended equivariant map from the glued total space to `U`. -/
noncomputable def descendedQuotientMap
    (hR : R ∈ Scheme.fpqcTopology.over S T) : A.P ⟶ U :=
  let fam : Presieve.FamilyOfElements (yoneda.obj U) A.totalSieve.arrows :=
    fun _ k hk ↦ quotientLocalMap D hDobj hDmap A k hk
  let hU : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj U) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  (hU A.totalSieve
    ((Scheme.fpqcTopology.over S).pullback_stable A.p hR)).amalgamate fam (by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Z W k h hk
      exact quotientLocalMap_naturality D hDobj hDmap A h k hk)

lemma descendedQuotientMap_local
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (k : Z ⟶ A.P) (hk : R (k ≫ A.p)) :
    k ≫ descendedQuotientMap D hDobj hDmap A hR =
      quotientLocalMap D hDobj hDmap A k hk := by
  let fam : Presieve.FamilyOfElements (yoneda.obj U) A.totalSieve.arrows :=
    fun _ k hk ↦ quotientLocalMap D hDobj hDmap A k hk
  let hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W k h hk
    exact quotientLocalMap_naturality D hDobj hDmap A h k hk
  let hU : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj U) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  exact (hU A.totalSieve
    ((Scheme.fpqcTopology.over S).pullback_stable A.p hR)).valid_glue
      hcompat k hk

lemma comparison_mem (q : R.arrows.category) {Z : Over S}
    (h : Z ⟶ ((carrierFunctor D).obj q).bundle.P) :
    R ((h ≫ A.total q) ≫ A.p) := by
  rw [Category.assoc, (A.isPullback q).w]
  exact R.downward_closed q.property
    (h ≫ ((carrierFunctor D).obj q).bundle.p ≫
      eqToHom (carrierFunctor_obj D hDobj q))

/-- The selected local object for a point mapping through the `q`-th comparison
maps canonically back to `q`. -/
noncomputable def pointComparisonMap (q : R.arrows.category) {Z : Over S}
    (h : Z ⟶ ((carrierFunctor D).obj q).bundle.P) :
    A.localObj (h ≫ A.total q) (comparison_mem D hDobj hDmap A q h) ⟶ q :=
  ⟨Over.homMk
    (h ≫ ((carrierFunctor D).obj q).bundle.p ≫
      eqToHom (carrierFunctor_obj D hDobj q)) (by
        change (h ≫ ((carrierFunctor D).obj q).bundle.p ≫
            eqToHom (carrierFunctor_obj D hDobj q)) ≫ q.obj.hom =
          (h ≫ A.total q) ≫ A.p
        rw [Category.assoc, Category.assoc, ← (A.isPullback q).w]
        simp only [Category.assoc])⟩

@[simp]
lemma pointComparisonMap_hom_left (q : R.arrows.category) {Z : Over S}
    (h : Z ⟶ ((carrierFunctor D).obj q).bundle.P) :
    (pointComparisonMap D hDobj hDmap A q h).hom.left =
      h ≫ ((carrierFunctor D).obj q).bundle.p ≫
        eqToHom (carrierFunctor_obj D hDobj q) := rfl

lemma point_pointComparisonMap (q : R.arrows.category) {Z : Over S}
    (h : Z ⟶ ((carrierFunctor D).obj q).bundle.P) :
    A.point (h ≫ A.total q) (comparison_mem D hDobj hDmap A q h) ≫
        ((carrierFunctor D).map
          (pointComparisonMap D hDobj hDmap A q h)).total = h := by
  apply (A.isPullback q).hom_ext
  · rw [Category.assoc, A.naturality
      (pointComparisonMap D hDobj hDmap A q h)]
    exact A.point_total _ _
  · rw [Category.assoc,
      ((carrierFunctor D).map
        (pointComparisonMap D hDobj hDmap A q h)).isPullback.w]
    have hLift : IsHomLift (classifyingPrestack G).p
        (pointComparisonMap D hDobj hDmap A q h).hom.left
        ((carrierFunctor D).map
          (pointComparisonMap D hDobj hDmap A q h)) :=
      carrierFunctor_map D hDmap _
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p
      (pointComparisonMap D hDobj hDmap A q h).hom.left
      ((carrierFunctor D).map
        (pointComparisonMap D hDobj hDmap A q h))
    change ((carrierFunctor D).map
      (pointComparisonMap D hDobj hDmap A q h)).base = _ at H
    calc
      A.point (h ≫ A.total q) (comparison_mem D hDobj hDmap A q h) ≫
          (((carrierFunctor D).obj
            (A.localObj (h ≫ A.total q)
              (comparison_mem D hDobj hDmap A q h))).bundle.p ≫
            ((carrierFunctor D).map
              (pointComparisonMap D hDobj hDmap A q h)).base) =
        (A.point (h ≫ A.total q)
          (comparison_mem D hDobj hDmap A q h) ≫
            ((carrierFunctor D).obj
              (A.localObj (h ≫ A.total q)
                (comparison_mem D hDobj hDmap A q h))).bundle.p) ≫
          ((carrierFunctor D).map
            (pointComparisonMap D hDobj hDmap A q h)).base :=
              (Category.assoc _ _ _).symm
      _ = eqToHom (carrierFunctor_obj D hDobj
            (A.localObj (h ≫ A.total q)
              (comparison_mem D hDobj hDmap A q h))).symm ≫
          ((carrierFunctor D).map
            (pointComparisonMap D hDobj hDmap A q h)).base := by
              rw [A.point_projection]
      _ = eqToHom (carrierFunctor_obj D hDobj
            (A.localObj (h ≫ A.total q)
              (comparison_mem D hDobj hDmap A q h))).symm ≫
          (eqToHom (carrierFunctor_obj D hDobj
            (A.localObj (h ≫ A.total q)
              (comparison_mem D hDobj hDmap A q h))) ≫
            (pointComparisonMap D hDobj hDmap A q h).hom.left ≫
              eqToHom (carrierFunctor_obj D hDobj q).symm) := by
                rw [H]
      _ = (pointComparisonMap D hDobj hDmap A q h).hom.left ≫
          eqToHom (carrierFunctor_obj D hDobj q).symm := by
            simp [Category.assoc]
      _ = (h ≫ ((carrierFunctor D).obj q).bundle.p ≫
          eqToHom (carrierFunctor_obj D hDobj q)) ≫
            eqToHom (carrierFunctor_obj D hDobj q).symm := by
              rw [pointComparisonMap_hom_left D hDobj hDmap A q h]
      _ = h ≫ ((carrierFunctor D).obj q).bundle.p := by simp [Category.assoc]

lemma total_descendedQuotientMap
    (hR : R ∈ Scheme.fpqcTopology.over S T) (q : R.arrows.category) :
    A.total q ≫ descendedQuotientMap D hDobj hDmap A hR =
      (D.obj q).map := by
  change (𝟙 _ ≫ A.total q) ≫
    descendedQuotientMap D hDobj hDmap A hR = (D.obj q).map
  rw [descendedQuotientMap_local D hDobj hDmap A hR
    (𝟙 _ ≫ A.total q) (comparison_mem D hDobj hDmap A q (𝟙 _))]
  let m := pointComparisonMap D hDobj hDmap A q (𝟙 _)
  have hmap := (D.map m).map_naturality
  change ((carrierFunctor D).map m).total ≫ (D.obj q).map =
    (D.obj (A.localObj (𝟙 _ ≫ A.total q)
      (comparison_mem D hDobj hDmap A q (𝟙 _)))).map at hmap
  unfold quotientLocalMap
  rw [← hmap, ← Category.assoc,
    point_pointComparisonMap D hDobj hDmap A q (𝟙 _), Category.id_comp]

lemma descendedQuotientMap_equivariant
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    letI := A.descendedModObj hR
    IsModHom G (descendedQuotientMap D hDobj hDmap A hR) := by
  letI := A.descendedModObj hR
  constructor
  let hU : Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj U) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply ((hU A.actionSieve (A.actionSieve_mem hR)).isSeparatedFor).ext
  intro Z l hl
  let r : Z ⟶ G := l ≫ fst G A.P
  let k : Z ⟶ A.P := l ≫ snd G A.P
  let q := A.localObj k hl
  let s : Z ⟶ ((carrierFunctor D).obj q).bundle.P := A.point k hl
  have hactU : (l ≫ (G ◁ descendedQuotientMap D hDobj hDmap A hR)) ≫
      γ[G, U] = r • (k ≫ descendedQuotientMap D hDobj hDmap A hR) := by
    rw [CategoryTheory.Hom.smul_def]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp [r, k, Category.assoc]
    · simp [r, k, Category.assoc]
  change l ≫ (γ[G, A.P] ≫
      descendedQuotientMap D hDobj hDmap A hR) =
    l ≫ ((G ◁ descendedQuotientMap D hDobj hDmap A hR) ≫ γ[G, U])
  rw [← Category.assoc]
  change (l ≫ A.descendedAction hR) ≫
      descendedQuotientMap D hDobj hDmap A hR = _
  rw [A.descendedAction_local hR l hl]
  dsimp only [ClassifyingObj.UnderlyingGluing.localAction]
  change ((r • s) ≫ A.total q) ≫
      descendedQuotientMap D hDobj hDmap A hR =
    l ≫ ((G ◁ descendedQuotientMap D hDobj hDmap A hR) ≫ γ[G, U])
  calc
    ((r • s) ≫ A.total q) ≫
        descendedQuotientMap D hDobj hDmap A hR =
      (r • s) ≫ (A.total q ≫
        descendedQuotientMap D hDobj hDmap A hR) :=
          Category.assoc _ _ _
    _ = (r • s) ≫ (D.obj q).map := by
      rw [total_descendedQuotientMap D hDobj hDmap A hR q]
    _ = r • (s ≫ (D.obj q).map) := by
      letI : IsModHom G (D.obj q).map := (D.obj q).equivariant
      rw [IsModHom.map_smul]
    _ = r • (k ≫ descendedQuotientMap D hDobj hDmap A hR) := by
      rw [descendedQuotientMap_local D hDobj hDmap A hR k hl]
      rfl
    _ = (l ≫ (G ◁ descendedQuotientMap D hDobj hDmap A hR)) ≫
        γ[G, U] := hactU.symm
    _ = l ≫ ((G ◁ descendedQuotientMap D hDobj hDmap A hR) ≫ γ[G, U]) :=
      Category.assoc _ _ _

/-- The descended quotient-stack object attached to an underlying gluing. -/
noncomputable def descendedObj
    (hR : R ∈ Scheme.fpqcTopology.over S T) : ActionQuotientObj G U where
  carrier := A.descendedObj hR (A.descended_flat hR)
    (A.descended_surjective hR) (A.descended_locallyOfFinitePresentation hR)
    (A.descended_smooth hR) (A.descended_torsor_isIso hR)
  map := descendedQuotientMap D hDobj hDmap A hR
  equivariant := descendedQuotientMap_equivariant D hDobj hDmap A hR

/-- The local comparison into the descended quotient-stack object. -/
noncomputable def comparison
    (hR : R ∈ Scheme.fpqcTopology.over S T) (q : R.arrows.category) :
    D.obj q ⟶ descendedObj D hDobj hDmap A hR where
  carrier := A.comparison hR (A.descended_flat hR)
    (A.descended_surjective hR) (A.descended_locallyOfFinitePresentation hR)
    (A.descended_smooth hR) (A.descended_torsor_isIso hR) q
  map_naturality := total_descendedQuotientMap D hDobj hDmap A hR q

lemma comparison_isHomLift
    (hR : R ∈ Scheme.fpqcTopology.over S T) (q : R.arrows.category) :
    IsHomLift (actionQuotientPrestack G U).p q.obj.hom
      (comparison D hDobj hDmap A hR q) := by
  let hb : (actionQuotientPrestack G U).p.obj
      (descendedObj D hDobj hDmap A hR) = T := rfl
  apply IsHomLift.of_fac' (actionQuotientPrestack G U).p q.obj.hom
    (comparison D hDobj hDmap A hR q) (hDobj q) hb
  cases hb
  change eqToHom (hDobj q) ≫ q.obj.hom =
    eqToHom (hDobj q) ≫ q.obj.hom ≫ 𝟙 T
  simp

lemma comparison_naturality
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {q r : R.arrows.category} (k : q ⟶ r) :
    D.map k ≫ comparison D hDobj hDmap A hR r =
      comparison D hDobj hDmap A hR q := by
  apply ActionQuotientHom.ext
  exact A.comparison_naturality hR (A.descended_flat hR)
    (A.descended_surjective hR) (A.descended_locallyOfFinitePresentation hR)
    (A.descended_smooth hR) (A.descended_torsor_isIso hR) k

include A in
/-- Quotient-stack objects glue once their underlying total spaces glue. -/
theorem exists_gluing
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    ∃ (a : ActionQuotientObj G U)
      (_ : (actionQuotientPrestack G U).p.obj a = T)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q : R.arrows.category,
        IsHomLift (actionQuotientPrestack G U).p q.obj.hom (ε q)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r),
        D.map k ≫ ε r = ε q := by
  refine ⟨descendedObj D hDobj hDmap A hR, rfl,
    comparison D hDobj hDmap A hR, ?_, ?_⟩
  · exact comparison_isHomLift D hDobj hDmap A hR
  · exact comparison_naturality D hDobj hDmap A hR

end ActionQuotientObjectDescent

end AlgebraicGeometry.Scheme
