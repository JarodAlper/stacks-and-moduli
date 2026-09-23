module

public import StacksAndModuli.API.RepresentableSheafStack
public import StacksAndModuli.API.CoreCoGrothendieckPrestack
public import StacksAndModuli.API.RelativeYonedaTotalULift
public import StacksAndModuli.API.OverPullbackDescentCartesian
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# Cartesian arrows and pointwise representable sheaves

For a base-change-stable morphism property `P`, this file identifies two categories over
schemes.  The first is the category of `P`-morphisms with Cartesian squares.  The second is
the Grothendieck construction of the pointwise core of sheaves that are representable by a
`P`-morphism.  The equivalence is the relative Yoneda embedding.

The explicit construction is useful for transporting the stack condition between the
geometric category of Cartesian arrows and the sheaf-valued pseudofunctor used in
representability arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe w u

namespace CategoryTheory.GrothendieckTopology

variable (J : GrothendieckTopology AlgebraicGeometry.Scheme.{u}) [J.Subcanonical]
variable (P : MorphismProperty AlgebraicGeometry.Scheme.{u}) [P.IsStableUnderBaseChange]

/-- The total category of pointwise-core sheaves represented by `P`-morphisms. -/
abbrev RepresentableCoreTotal :=
  Pseudofunctor.CoGrothendieck
    ((J.representableByPropertyULift.{w} P).fullsubcategory).core

/-- The Grothendieck construction of pointwise-core `P`-representable sheaves, based over
schemes. -/
abbrev RepresentableCoreBased := BasedCategory.ofFunctor
  (Pseudofunctor.CoGrothendieck.forget
    ((J.representableByPropertyULift.{w} P).fullsubcategory).core)

/-- Composition in the core of a full subcategory agrees with composition of the
underlying morphisms. -/
lemma coreFullSubcategory_comp_hom
    {C : Type*} [Category C] {Q : ObjectProperty C}
    {X Y Z : Core Q.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).iso.hom.hom = f.iso.hom.hom ≫ g.iso.hom.hom := rfl

/-- Equality transport in the core of a full subcategory agrees with equality transport
of the underlying objects. -/
lemma coreFullSubcategory_eqToHom_hom
    {C : Type*} [Category C] {Q : ObjectProperty C}
    {X Y : Core Q.FullSubcategory} (h : X = Y) :
    (eqToHom h : X ⟶ Y).iso.hom.hom =
      eqToHom (congrArg (fun Z ↦ Z.of.obj) h) := by
  subst h
  rfl

/-- Every underlying morphism of a morphism in the core of a full subcategory is an
isomorphism. -/
noncomputable instance coreFullSubcategoryUnderlyingHom_isIso
    {C : Type*} [Category C] {Q : ObjectProperty C}
    {X Y : Core Q.FullSubcategory} (f : X ⟶ Y) :
    IsIso f.iso.hom.hom :=
  ((Q.ι).mapIso f.iso).isIso_hom

/-- The isomorphism in the relevant over category induced by a Cartesian square. -/
noncomputable def cartesianOverHom
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    Over.mk (A.obj : Arrow _).hom ⟶
      (Over.pullback f.hom.right).obj (Over.mk (B.obj : Arrow _).hom) := by
  refine Over.homMk
    (pullback.lift f.hom.left (A.obj : Arrow _).hom
      f.hom.isPullback.w) ?_
  exact pullback.lift_snd _ _ _

omit [P.IsStableUnderBaseChange] in
lemma cartesianOverHom_eq_isoPullback_hom
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    cartesianOverHom P f =
      (Over.isoMk f.hom.isPullback.isoPullback (by simp)).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans
      f.hom.isPullback.isoPullback_hom_fst.symm
  · exact (pullback.lift_snd _ _ _).trans
      f.hom.isPullback.isoPullback_hom_snd.symm

/-- The over-category morphism induced by a Cartesian square is invertible. -/
noncomputable instance cartesianOverHom_isIso
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    IsIso (cartesianOverHom P f) := by
  rw [cartesianOverHom_eq_isoPullback_hom]
  infer_instance

/-- The over-category isomorphism induced by a Cartesian square. -/
noncomputable def cartesianOverIso
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    Over.mk (A.obj : Arrow _).hom ≅
      (Over.pullback f.hom.right).obj (Over.mk (B.obj : Arrow _).hom) :=
  asIso (cartesianOverHom P f)

/-- The total category of the pseudofunctor of schemes over a varying scheme. -/
abbrev ArrowTotal := AlgebraicGeometry.RelativeYoneda.ArrowTotal

/-- Regard a `P`-morphism as an object of the total over-category. -/
noncomputable def arrowTotalObj
    (A : (arrowCartesianProperty P).obj) : ArrowTotal.{u} :=
  ⟨(A.obj : Arrow _).right, Over.mk (A.obj : Arrow _).hom⟩

/-- Regard a Cartesian square as a morphism of the total over-category. -/
noncomputable def arrowTotalMap
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    arrowTotalObj P A ⟶ arrowTotalObj P B where
  base := f.hom.right
  fiber := cartesianOverHom P f

lemma overPullbackPseudofunctor_mapId_inv_app
    {X : AlgebraicGeometry.Scheme.{u}} (Z : Over X) :
    (AlgebraicGeometry.overPullbackPseudofunctor.mapId
      ⟨op X⟩).inv.toNatTrans.app Z =
        (Over.pullbackId (X := X)).inv.app Z := rfl

lemma pullbackId_inv_left_fst
    {X : AlgebraicGeometry.Scheme.{u}} (Z : Over X) :
    ((Over.pullbackId (X := X)).inv.app Z).left ≫
        pullback.fst Z.hom (𝟙 X) = 𝟙 Z.left := by
  change ((Over.pullbackId (X := X)).inv.app Z).left ≫
      ((Over.pullbackId (X := X)).hom.app Z).left = 𝟙 Z.left
  exact congrArg Over.Hom.left
    ((Over.pullbackId (X := X)).inv_hom_id_app Z)

omit [P.IsStableUnderBaseChange] in
lemma cartesianOverHom_id
    (A : (arrowCartesianProperty P).obj) :
    cartesianOverHom P (𝟙 A) =
      (Over.pullbackId (X := (A.obj : Arrow _).right)).inv.app
        (Over.mk (A.obj : Arrow _).hom) := by
  change cartesianOverHom P
      (ObjectProperty.homMk (CartesianArrowHom.id A.obj)) = _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change pullback.lift (𝟙 (A.obj : Arrow _).left)
        (A.obj : Arrow _).hom _ ≫
      pullback.fst (A.obj : Arrow _).hom
        (𝟙 (A.obj : Arrow _).right) =
      ((Over.pullbackId (X := (A.obj : Arrow _).right)).inv.app
        (Over.mk (A.obj : Arrow _).hom)).left ≫
          pullback.fst (A.obj : Arrow _).hom
            (𝟙 (A.obj : Arrow _).right)
    exact (pullback.lift_fst _ _ _).trans
      (pullbackId_inv_left_fst
        (Over.mk (A.obj : Arrow _).hom)).symm
  · change pullback.lift (𝟙 (A.obj : Arrow _).left)
        (A.obj : Arrow _).hom _ ≫
      pullback.snd (A.obj : Arrow _).hom
        (𝟙 (A.obj : Arrow _).right) =
      ((Over.pullbackId (X := (A.obj : Arrow _).right)).inv.app
        (Over.mk (A.obj : Arrow _).hom)).left ≫
          pullback.snd (A.obj : Arrow _).hom
            (𝟙 (A.obj : Arrow _).right)
    exact (pullback.lift_snd _ _ _).trans
      (Over.w ((Over.pullbackId
        (X := (A.obj : Arrow _).right)).inv.app
          (Over.mk (A.obj : Arrow _).hom))).symm

omit [P.IsStableUnderBaseChange] in
lemma cartesianOverHom_comp
    {A B C : (arrowCartesianProperty P).obj}
    (f : A ⟶ B) (g : B ⟶ C) :
    cartesianOverHom P (f ≫ g) =
      cartesianOverHom P f ≫
        (Over.pullback f.hom.right).map (cartesianOverHom P g) ≫
          (Over.pullbackComp f.hom.right g.hom.right).inv.app
            (Over.mk (C.obj : Arrow _).hom) := by
  change cartesianOverHom P
      (ObjectProperty.homMk (f.hom.comp g.hom)) = _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change pullback.lift (f.hom.left ≫ g.hom.left)
        (A.obj : Arrow _).hom _ ≫
      pullback.fst (C.obj : Arrow _).hom
        (f.hom.right ≫ g.hom.right) =
      (cartesianOverHom P f ≫
        (Over.pullback f.hom.right).map (cartesianOverHom P g) ≫
          (Over.pullbackComp f.hom.right g.hom.right).inv.app
            (Over.mk (C.obj : Arrow _).hom)).left ≫
        pullback.fst (C.obj : Arrow _).hom
          (f.hom.right ≫ g.hom.right)
    refine (pullback.lift_fst _ _ _).trans ?_
    symm
    let eF := cartesianOverHom P f
    let eG := (Over.pullback f.hom.right).map (cartesianOverHom P g)
    let eComp := (Over.pullbackComp f.hom.right g.hom.right).inv.app
      (Over.mk (C.obj : Arrow _).hom)
    have hComp : eComp.left ≫
        pullback.fst (C.obj : Arrow _).hom
          (f.hom.right ≫ g.hom.right) =
      pullback.fst (pullback.snd (C.obj : Arrow _).hom g.hom.right)
          f.hom.right ≫
        pullback.fst (C.obj : Arrow _).hom g.hom.right :=
      AlgebraicGeometry.OverPullbackDescent.pullbackComp_inv_left_fst
        f.hom.right g.hom.right (Over.mk (C.obj : Arrow _).hom)
    calc
      (eF ≫ eG ≫ eComp).left ≫
          pullback.fst (C.obj : Arrow _).hom
            (f.hom.right ≫ g.hom.right) =
        eF.left ≫ eG.left ≫
          (eComp.left ≫ pullback.fst (C.obj : Arrow _).hom
            (f.hom.right ≫ g.hom.right)) := by
              simp only [Over.comp_left, Category.assoc]
      _ = eF.left ≫ eG.left ≫
          (pullback.fst (pullback.snd (C.obj : Arrow _).hom g.hom.right)
              f.hom.right ≫
            pullback.fst (C.obj : Arrow _).hom g.hom.right) := by
              exact congrArg (fun k ↦ eF.left ≫ eG.left ≫ k) hComp
      _ = f.hom.left ≫ g.hom.left := by
        let LF := pullback.lift f.hom.left (A.obj : Arrow _).hom
          f.hom.isPullback.w
        let LG := pullback.lift g.hom.left (B.obj : Arrow _).hom
          g.hom.isPullback.w
        let LFG := pullback.lift
          (pullback.fst (B.obj : Arrow _).hom f.hom.right ≫ LG)
          (pullback.snd (B.obj : Arrow _).hom f.hom.right) (by
            rw [Category.assoc, pullback.lift_snd]
            exact pullback.condition)
        have hLFG : LFG ≫
            pullback.fst
              (pullback.snd (C.obj : Arrow _).hom g.hom.right)
              f.hom.right =
          pullback.fst (B.obj : Arrow _).hom f.hom.right ≫ LG :=
            pullback.lift_fst _ _ _
        have hLF : LF ≫
            pullback.fst (B.obj : Arrow _).hom f.hom.right =
          f.hom.left := pullback.lift_fst _ _ _
        have hLG : LG ≫
            pullback.fst (C.obj : Arrow _).hom g.hom.right =
          g.hom.left := pullback.lift_fst _ _ _
        change LF ≫ LFG ≫
            pullback.fst
              (pullback.snd (C.obj : Arrow _).hom g.hom.right)
              f.hom.right ≫
            pullback.fst (C.obj : Arrow _).hom g.hom.right =
          f.hom.left ≫ g.hom.left
        calc
          LF ≫ LFG ≫
              pullback.fst
                (pullback.snd (C.obj : Arrow _).hom g.hom.right)
                f.hom.right ≫
              pullback.fst (C.obj : Arrow _).hom g.hom.right =
            LF ≫ ((LFG ≫
              pullback.fst
                (pullback.snd (C.obj : Arrow _).hom g.hom.right)
                f.hom.right) ≫
              pullback.fst (C.obj : Arrow _).hom g.hom.right) := by
                simp only [Category.assoc]
          _ = LF ≫
              ((pullback.fst (B.obj : Arrow _).hom f.hom.right ≫ LG) ≫
                pullback.fst (C.obj : Arrow _).hom g.hom.right) := by
                  rw [hLFG]
          _ = (LF ≫ pullback.fst (B.obj : Arrow _).hom f.hom.right) ≫
              (LG ≫ pullback.fst (C.obj : Arrow _).hom g.hom.right) := by
                simp only [Category.assoc]
          _ = f.hom.left ≫ g.hom.left := by rw [hLF, hLG]
  · exact (Over.w (cartesianOverHom P (f ≫ g))).trans
      (Over.w (cartesianOverHom P f ≫
        (Over.pullback f.hom.right).map (cartesianOverHom P g) ≫
          (Over.pullbackComp f.hom.right g.hom.right).inv.app
          (Over.mk (C.obj : Arrow _).hom))).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Reconstruct a Cartesian square from a morphism in the total over-category whose
fiber component is invertible. -/
noncomputable def cartesianPreimage
    {A B : (arrowCartesianProperty P).obj}
    (f : arrowTotalObj P A ⟶ arrowTotalObj P B) [IsIso f.fiber] :
    A ⟶ B := by
  let k : Over.mk (A.obj : Arrow _).hom ⟶
      (Over.pullback f.base).obj (Over.mk (B.obj : Arrow _).hom) := f.fiber
  letI : IsIso k := by
    dsimp only [k]
    infer_instance
  let e : Over.mk (A.obj : Arrow _).hom ≅
      (Over.pullback f.base).obj (Over.mk (B.obj : Arrow _).hom) := asIso k
  refine ObjectProperty.homMk
    { left := k.left ≫
        pullback.fst (B.obj : Arrow _).hom f.base
      right := f.base
      isPullback := by
        have hk : k.left ≫
            pullback.snd (B.obj : Arrow _).hom f.base =
            (A.obj : Arrow _).hom := by
          exact Over.w k
        refine IsPullback.of_iso_pullback ?_
          ((Over.forget (A.obj : Arrow _).right).mapIso e) ?_ ?_
        · constructor
          change (k.left ≫
              pullback.fst (B.obj : Arrow _).hom f.base) ≫
              (B.obj : Arrow _).hom =
            (A.obj : Arrow _).hom ≫ f.base
          rw [Category.assoc, pullback.condition, ← Category.assoc,
            hk]
        · rfl
        · exact hk }

set_option backward.isDefEq.respectTransparency false in
omit [P.IsStableUnderBaseChange] in
/-- Mapping the reconstructed Cartesian square recovers the original total morphism. -/
lemma arrowTotalMap_cartesianPreimage
    {A B : (arrowCartesianProperty P).obj}
    (f : arrowTotalObj P A ⟶ arrowTotalObj P B) [IsIso f.fiber] :
    arrowTotalMap P (cartesianPreimage P f) = f := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext
    (arrowTotalMap P (cartesianPreimage P f)) f rfl
  simp only [eqToHom_refl, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans (Over.w f.fiber).symm

set_option backward.isDefEq.respectTransparency false in
omit [P.IsStableUnderBaseChange] in
/-- Reconstructing a Cartesian square from its total morphism is the identity. -/
lemma cartesianPreimage_arrowTotalMap
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    @cartesianPreimage P A B (arrowTotalMap P f) (by
      change IsIso (cartesianOverHom P f)
      infer_instance) = f := by
  apply ObjectProperty.hom_ext
  apply CartesianArrowHom.ext
  · exact pullback.lift_fst _ _ _
  · rfl

set_option maxHeartbeats 400000 in
-- CoGrothendieck composition unfolds two layers of pseudofunctor coherence here.
set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a `P`-morphism and Cartesian square to the corresponding object
and morphism of the total over-category. -/
noncomputable def arrowTotalFunctor :
    (arrowCartesianProperty P).obj ⥤ ArrowTotal.{u} where
  obj := arrowTotalObj P
  map := arrowTotalMap P
  map_id A := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (arrowTotalMap P (𝟙 A)) (𝟙 (arrowTotalObj P A)) rfl
    change cartesianOverHom P (𝟙 A) =
      (AlgebraicGeometry.overPullbackPseudofunctor.mapId
        ⟨op (A.obj : Arrow _).right⟩).inv.toNatTrans.app
          (Over.mk (A.obj : Arrow _).hom)
    rw [overPullbackPseudofunctor_mapId_inv_app]
    exact cartesianOverHom_id P A
  map_comp {A B C} f g := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (arrowTotalMap P (f ≫ g))
      (arrowTotalMap P f ≫ arrowTotalMap P g) rfl
    simp only [eqToHom_refl, Category.comp_id]
    change cartesianOverHom P (f ≫ g) = _
    exact cartesianOverHom_comp P f g

set_option backward.isDefEq.respectTransparency false in
/-- The total-over-category functor is faithful. -/
noncomputable instance arrowTotalFunctor_faithful :
    (arrowTotalFunctor P).Faithful where
  map_injective {X Y} f g h := by
    rw [← cartesianPreimage_arrowTotalMap P f,
      ← cartesianPreimage_arrowTotalMap P g]
    change arrowTotalMap P f = arrowTotalMap P g at h
    let kf : { k : arrowTotalObj P X ⟶ arrowTotalObj P Y //
        IsIso k.fiber } := ⟨arrowTotalMap P f, by
          change IsIso (cartesianOverHom P f)
          infer_instance⟩
    let kg : { k : arrowTotalObj P X ⟶ arrowTotalObj P Y //
        IsIso k.fiber } := ⟨arrowTotalMap P g, by
          change IsIso (cartesianOverHom P g)
          infer_instance⟩
    have hkg : kf = kg := Subtype.ext h
    simpa only [kf, kg] using congrArg
      (fun k : { k : arrowTotalObj P X ⟶ arrowTotalObj P Y //
          IsIso k.fiber } ↦
        @cartesianPreimage P X Y k.1 k.2) hkg

/-- The pointwise representable sheaf associated by relative Yoneda to a `P`-morphism. -/
noncomputable def representableCoreObj
    (A : (arrowCartesianProperty P).obj) : RepresentableCoreTotal J P := by
  refine ⟨(A.obj : Arrow _).right, ⟨⟨?_, ?_⟩⟩⟩
  · exact (J.over (A.obj : Arrow _).right).uliftYoneda.{w}.obj
      (Over.mk (A.obj : Arrow _).hom)
  · exact ⟨Over.mk (A.obj : Arrow _).hom, A.property, ⟨Iso.refl _⟩⟩

/-- A Cartesian square induces the comparison isomorphism between the corresponding
representable sheaves after pullback. -/
noncomputable def cartesianSheafIso
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    ((representableCoreObj J P A).fiber.of.obj) ≅
      ((((J.representableByPropertyULift.{w} P).fullsubcategory).core.map
        f.hom.right.op.toLoc).toFunctor.obj
          (representableCoreObj J P B).fiber).of.obj := by
  change (J.over (A.obj : Arrow _).right).uliftYoneda.{w}.obj
      (Over.mk (A.obj : Arrow _).hom) ≅
    (J.overMapPullback (Type max u w) f.hom.right).obj
      ((J.over (B.obj : Arrow _).right).uliftYoneda.{w}.obj
        (Over.mk (B.obj : Arrow _).hom))
  exact (J.over (A.obj : Arrow _).right).uliftYoneda.{w}.mapIso
      (cartesianOverIso P f) ≪≫
    overMapPullbackULiftYonedaIso J f.hom.right
      (Over.mk (B.obj : Arrow _).hom)

/-- The morphism of pointwise representable sheaves induced by a Cartesian square. -/
noncomputable def representableCoreMap
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    representableCoreObj J P A ⟶ representableCoreObj J P B where
  base := f.hom.right
  fiber := CoreHom.mk (ObjectProperty.isoMk
    (P := (J.representableByPropertyULift.{w} P).prop
      (.mk (op (A.obj : Arrow _).right)))
    (cartesianSheafIso J P f))

lemma representableCoreMap_fiber_hom
    {A B : (arrowCartesianProperty P).obj} (f : A ⟶ B) :
    (representableCoreMap J P f).fiber.iso.hom.hom =
      (AlgebraicGeometry.RelativeYonedaULift.map.{w} J
        (arrowTotalMap P f)).fiber := by
  rfl

lemma representableCoreId_fiber_hom
    (A : (arrowCartesianProperty P).obj) :
    (Pseudofunctor.CoGrothendieck.Hom.fiber
      (F := ((J.representableByPropertyULift.{w} P).fullsubcategory).core)
      (𝟙 (representableCoreObj J P A))).iso.hom.hom =
      Pseudofunctor.CoGrothendieck.Hom.fiber
        (F := J.pseudofunctorOver (Type max u w))
        (𝟙 (AlgebraicGeometry.RelativeYonedaULift.obj.{w} J
          (arrowTotalObj P A))) := by
  rfl

lemma representableCoreComp_fiber_hom
    {A B C : (arrowCartesianProperty P).obj} (f : A ⟶ B) (g : B ⟶ C) :
    (representableCoreMap J P f ≫
        representableCoreMap J P g).fiber.iso.hom.hom =
      (AlgebraicGeometry.RelativeYonedaULift.map.{w} J
          (arrowTotalMap P f) ≫
        AlgebraicGeometry.RelativeYonedaULift.map.{w} J
          (arrowTotalMap P g)).fiber := by
  rfl

noncomputable def representableCoreUnderlyingObj
    (X : RepresentableCoreTotal J P) :
    AlgebraicGeometry.RelativeYonedaULift.SheafTotal.{w} J :=
  ⟨X.base, X.fiber.of.obj⟩

noncomputable def representableCoreUnderlyingMap
    {X Y : RepresentableCoreTotal J P} (f : X ⟶ Y) :
    representableCoreUnderlyingObj J P X ⟶
      representableCoreUnderlyingObj J P Y where
  base := f.base
  fiber := f.fiber.iso.hom.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Forget the full-subcategory and core wrappers from a pointwise representable sheaf. -/
noncomputable def representableCoreUnderlyingFunctor :
    RepresentableCoreTotal J P ⥤
      AlgebraicGeometry.RelativeYonedaULift.SheafTotal.{w} J where
  obj := representableCoreUnderlyingObj J P
  map := representableCoreUnderlyingMap J P
  map_id X := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (representableCoreUnderlyingMap J P (𝟙 X))
      (𝟙 (representableCoreUnderlyingObj J P X)) rfl
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  map_comp {X Y Z} f g := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (representableCoreUnderlyingMap J P (f ≫ g))
      (representableCoreUnderlyingMap J P f ≫
        representableCoreUnderlyingMap J P g) rfl
    simp only [eqToHom_refl, Category.comp_id]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance representableCoreUnderlyingFunctor_faithful :
    (representableCoreUnderlyingFunctor J P).Faithful where
  map_injective {X Y} f g h := by
    let hbase := congrArg Pseudofunctor.CoGrothendieck.Hom.base h
    apply Pseudofunctor.CoGrothendieck.Hom.ext f g hbase
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    have hfiber := Pseudofunctor.CoGrothendieck.Hom.congr h
    rw [coreFullSubcategory_comp_hom,
      coreFullSubcategory_eqToHom_hom]
    exact hfiber

/-- The relative Yoneda functor from `P`-morphisms and Cartesian squares to the
pointwise-core Grothendieck construction of `P`-representable sheaves. -/
noncomputable def representableCoreFunctor :
    (arrowCartesianProperty P).obj ⥤ RepresentableCoreTotal J P where
  obj := representableCoreObj J P
  map := representableCoreMap J P
  map_id A := by
    apply (representableCoreUnderlyingFunctor J P).map_injective
    exact ((arrowTotalFunctor P ⋙
      AlgebraicGeometry.RelativeYonedaULift.functor.{w} J).map_id A)
  map_comp {A B C} f g := by
    apply (representableCoreUnderlyingFunctor J P).map_injective
    exact ((arrowTotalFunctor P ⋙
      AlgebraicGeometry.RelativeYonedaULift.functor.{w} J).map_comp f g)

/-- The relative Yoneda functor on Cartesian arrows is faithful. -/
noncomputable instance representableCoreFunctor_faithful :
    (representableCoreFunctor.{w} J P).Faithful where
  map_injective {X Y} f g h := by
    apply (arrowTotalFunctor P).map_injective
    apply (AlgebraicGeometry.RelativeYonedaULift.functor.{w} J).map_injective
    exact (representableCoreUnderlyingFunctor.{w} J P).congr_map h

/-- The relative Yoneda functor on Cartesian arrows is full. -/
noncomputable instance representableCoreFunctor_full :
    (representableCoreFunctor.{w} J P).Full where
  map_surjective {X Y} f := by
    let fu : AlgebraicGeometry.RelativeYonedaULift.obj.{w} J
          (arrowTotalObj P X) ⟶
        AlgebraicGeometry.RelativeYonedaULift.obj.{w} J
          (arrowTotalObj P Y) :=
      representableCoreUnderlyingMap J P f
    let ef :
        (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.obj
            (arrowTotalObj P X).fiber ≅
          (J.overMapPullback (Type max u w) fu.base).obj
            ((J.over (arrowTotalObj P Y).base).uliftYoneda.{w}.obj
              (arrowTotalObj P Y).fiber) :=
      (((J.representableByPropertyULift.{w} P).prop
        (.mk (op (arrowTotalObj P X).base))).ι).mapIso f.fiber.iso
    let c := J.overMapPullbackULiftYonedaIso.{w} fu.base
      (arrowTotalObj P Y).fiber
    let eq :
        (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.obj
            (arrowTotalObj P X).fiber ≅
          (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.obj
            ((Over.pullback fu.base).obj (arrowTotalObj P Y).fiber) :=
      Iso.trans ef c.symm
    let q : (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.obj
          (arrowTotalObj P X).fiber ⟶
        (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.obj
          ((Over.pullback fu.base).obj (arrowTotalObj P Y).fiber) := eq.hom
    let h := AlgebraicGeometry.RelativeYonedaULift.preimage.{w} J fu
    have hh : IsIso h.fiber := by
      change IsIso ((J.over (arrowTotalObj P X).base).uliftYoneda.{w}.preimage q)
      let hF := GrothendieckTopology.fullyFaithfulUliftYoneda.{w}
        (J.over (arrowTotalObj P X).base)
      let F := (J.over (arrowTotalObj P X).base).uliftYoneda.{w}
      let hT := Functor.FullyFaithful.ofFullyFaithful F
      let epre := hF.preimageIso
          (X := (arrowTotalObj P X).fiber)
          (Y := (Over.pullback fu.base).obj (arrowTotalObj P Y).fiber)
          eq
      have he : (J.over (arrowTotalObj P X).base).uliftYoneda.{w}.preimage q =
          epre.hom := by
        change hT.preimage q = hF.preimage eq.hom
        rw [show hT = hF from Subsingleton.elim _ _]
      rw [he]
      exact epre.isIso_hom
    let g : X ⟶ Y := @cartesianPreimage P X Y h hh
    refine ⟨g, ?_⟩
    apply (representableCoreUnderlyingFunctor.{w} J P).map_injective
    change AlgebraicGeometry.RelativeYonedaULift.map.{w} J
        (arrowTotalMap P g) = fu
    rw [show arrowTotalMap P g = h from
      arrowTotalMap_cartesianPreimage P h]
    exact AlgebraicGeometry.RelativeYonedaULift.map_preimage.{w} J fu

set_option linter.style.haveILetI false in
/-- Every pointwise `P`-representable sheaf comes from a `P`-morphism. -/
noncomputable instance representableCoreFunctor_essSurj :
    (representableCoreFunctor.{w} J P).EssSurj where
  mem_essImage M := by
    obtain ⟨Z, hZ, ⟨e⟩⟩ := M.fiber.of.property
    let A : (arrowCartesianProperty P).obj :=
      ⟨ArrowCartesian.mk Z.hom, hZ⟩
    let eSheaf :
        (J.over M.base).uliftYoneda.{w}.obj Z ≅ M.fiber.of.obj :=
      (fullyFaithfulSheafToPresheaf (J.over M.base)
        (Type max u w)).preimageIso e
    let eFull : (representableCoreObj J P A).fiber.of ≅ M.fiber.of :=
      ObjectProperty.isoMk
        ((J.representableByPropertyULift.{w} P).prop (.mk (op M.base)))
        eSheaf
    let eCore : (representableCoreObj J P A).fiber ≅ M.fiber :=
      Core.isoMk eFull
    let RF := ((J.representableByPropertyULift.{w} P).fullsubcategory).core
    let m : representableCoreObj J P A ⟶ M :=
      { base := 𝟙 M.base
        fiber := eCore.hom ≫
          (RF.mapId ⟨op M.base⟩).inv.toNatTrans.app M.fiber }
    let p := Pseudofunctor.CoGrothendieck.forget RF
    letI : Functor.IsHomLift p (𝟙 M.base) m := by
      change Functor.IsHomLift p (p.map m) m
      infer_instance
    let fm := Functor.Fiber.homMk p M.base m
    letI : Groupoid (p.Fiber M.base) :=
      Pseudofunctor.CoGrothendieck.coreFiberGroupoid
        ((J.representableByPropertyULift.{w} P).fullsubcategory) M.base
    haveI : IsIso fm := by infer_instance
    have hm : IsIso (Functor.Fiber.fiberInclusion.map fm) := by
      infer_instance
    have hm' : IsIso m := by simpa [fm] using hm
    exact ⟨A, ⟨@asIso _ _ _ _ m hm'⟩⟩

/-- Cartesian `P`-arrows are equivalent to the pointwise core of `P`-representable
sheaves. -/
noncomputable instance representableCoreFunctor_isEquivalence :
    (representableCoreFunctor.{w} J P).IsEquivalence where

/-- The relative Yoneda equivalence as a functor of categories based over schemes. -/
noncomputable def representableCoreBasedFunctor :
    arrowCartesianProperty P ⥤ᵇ RepresentableCoreBased J P where
  toFunctor := representableCoreFunctor.{w} J P
  w := rfl

/-- The based relative Yoneda functor is an equivalence on underlying categories. -/
noncomputable instance representableCoreBasedFunctor_isEquivalence :
    (representableCoreBasedFunctor.{w} J P).toFunctor.IsEquivalence :=
  representableCoreFunctor_isEquivalence J P

end CategoryTheory.GrothendieckTopology
