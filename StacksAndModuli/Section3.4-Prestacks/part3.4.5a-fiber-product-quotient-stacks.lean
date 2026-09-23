module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4a-quotient-stack-presentations»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»
public import StacksAndModuli.API.PrincipalBundlePointTrivialization
public import StacksAndModuli.API.PrestackProducts

/-!
# Fiber products with quotient prestacks

This module formalizes `exer:fiber-product-quotient-stacks` (Exercise 3.4.37)
of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

For a principal `G`-bundle `P → T` with an equivariant map `P → U`, we use
the explicit pullback family as a concrete representative of the morphism
`T → [U/G]` supplied by the 2-Yoneda lemma.  Pulling this family back along the
canonical presentation `U → [U/G]` recovers `P`.

Main declarations:

* `QuotientFiberProduct.isCartesianSquare_totalSpace`: the first cartesian
  square of Exercise 3.4.37;
* `QuotientFiberProduct.isCartesianSquare_quotientPresentation` and
  `QuotientFiberProduct.isEquivalence_quotientPresentationDiagonal`: the two
  displayed quotient-presentation squares.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerFiberProductQuotientStacks

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory.BasedCategory

variable {S : Scheme.{u}} {G U T : Over S} [GrpObj G] [ModObj G U]
  [Smooth G.hom] [IsAffineHom G.hom]

namespace QuotientFiberProduct

/-! ### Explicit pullback families -/

/-- Composition with `f` as a morphism between representable prestacks. -/
@[simps! toFunctor]
def overMap {X Y : Over S} (f : X ⟶ Y) : overBased X ⥤ᵇ overBased Y where
  toFunctor := Over.map f
  w := Over.mapForget_eq f

variable (B : GlobalPrincipalBundle G T)

/-- The canonical map between two pullbacks of a principal bundle induced by
a morphism of their bases over `T`. -/
noncomputable def pullbackTotalMap {X Y : Over T} (f : X ⟶ Y) :
    (B.pullback X.hom).P ⟶ (B.pullback Y.hom).P :=
  pullback.lift (pullback.fst B.p X.hom)
    (pullback.snd B.p X.hom ≫ f.left) (by
      rw [Category.assoc, Over.w f]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma pullbackTotalMap_fst {X Y : Over T} (f : X ⟶ Y) :
    pullbackTotalMap B f ≫ pullback.fst B.p Y.hom =
      pullback.fst B.p X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackTotalMap_snd {X Y : Over T} (f : X ⟶ Y) :
    pullbackTotalMap B f ≫ pullback.snd B.p Y.hom =
      pullback.snd B.p X.hom ≫ f.left :=
  pullback.lift_snd _ _ _

lemma pullbackTotalMap_id (X : Over T) :
    pullbackTotalMap B (X := X) (Y := X) (𝟙 X) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

lemma pullbackTotalMap_comp {X Y Z : Over T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackTotalMap B f ≫ pullbackTotalMap B g =
      pullbackTotalMap B (f ≫ g) := by
  apply pullback.hom_ext
  · simp
  · simp [Category.assoc]

lemma pullbackTotalMap_isPullback {X Y : Over T} (f : X ⟶ Y) :
    IsPullback (pullbackTotalMap B f) (pullback.snd B.p X.hom)
      (pullback.snd B.p Y.hom) f.left := by
  apply IsPullback.mk'
  · exact pullbackTotalMap_snd B f
  · intro Q a b hab hbase
    apply pullback.hom_ext
    · have h := congrArg (fun q ↦ q ≫ pullback.fst B.p Y.hom) hab
      simpa only [Category.assoc, pullbackTotalMap_fst] using h
    · exact hbase
  · intro Q a b hab
    let l : Q ⟶ (B.pullback X.hom).P :=
      pullback.lift (a ≫ pullback.fst B.p Y.hom) b (by
        calc
          (a ≫ pullback.fst B.p Y.hom) ≫ B.p =
              a ≫ (pullback.snd B.p Y.hom ≫ Y.hom) := by
                rw [Category.assoc, pullback.condition]
          _ = (a ≫ pullback.snd B.p Y.hom) ≫ Y.hom :=
                (Category.assoc _ _ _).symm
          _ = (b ≫ f.left) ≫ Y.hom := by rw [hab]
          _ = b ≫ X.hom := by rw [Category.assoc, Over.w f])
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [l]
      · change l ≫ pullbackTotalMap B f ≫ pullback.snd B.p Y.hom =
          a ≫ pullback.snd B.p Y.hom
        rw [pullbackTotalMap_snd]
        simpa [l, Category.assoc] using hab.symm
    · exact pullback.lift_snd _ _ _

lemma pullbackTotalMap_equivariant {X Y : Over T} (f : X ⟶ Y) :
    IsModHom G (pullbackTotalMap B f) := by
  letI : ModObj G T := ModObj.trivialAction G T
  letI : ModObj G X.left := ModObj.trivialAction G X.left
  letI : ModObj G Y.left := ModObj.trivialAction G Y.left
  letI : IsModHom G B.p := by
    constructor
    change γ[G, B.P] ≫ B.p = (G ◁ B.p) ≫ snd G T
    rw [B.invariant]
    simp
  letI : IsModHom G X.hom := ModObj.isModHom_trivialAction G X.hom
  letI : IsModHom G Y.hom := ModObj.isModHom_trivialAction G Y.hom
  letI : IsModHom G f.left := ModObj.isModHom_trivialAction G f.left
  letI : ModObj G (pullback B.p X.hom) :=
    ModObj.pullbackTorsorAction B.p X.hom B.invariant
  letI : ModObj G (pullback B.p Y.hom) :=
    ModObj.pullbackTorsorAction B.p Y.hom B.invariant
  letI : IsModHom G (pullback.fst B.p X.hom) :=
    ModObj.isModHom_pullback_fst G B.p X.hom
  letI : IsModHom G (pullback.snd B.p X.hom) :=
    ModObj.isModHom_pullback_snd G B.p X.hom
  exact ModObj.isModHom_pullback_lift G B.p Y.hom
    (pullback.fst B.p X.hom) (pullback.snd B.p X.hom ≫ f.left) _

/-- The explicit pullback of a quotient-stack object to an object over its
base. -/
noncomputable def familyObj (A : ActionQuotientObj G U)
    (X : Over A.carrier.base) : ActionQuotientObj G U where
  carrier :=
    { base := X.left
      bundle := A.carrier.bundle.pullback X.hom }
  map := pullback.fst A.carrier.bundle.p X.hom ≫ A.map
  equivariant := by
    letI : ModObj G A.carrier.base :=
      ModObj.trivialAction G A.carrier.base
    letI : ModObj G X.left := ModObj.trivialAction G X.left
    letI : IsModHom G A.carrier.bundle.p := by
      constructor
      change γ[G, A.carrier.bundle.P] ≫ A.carrier.bundle.p =
        (G ◁ A.carrier.bundle.p) ≫ snd G A.carrier.base
      rw [A.carrier.bundle.invariant]
      simp
    letI : IsModHom G X.hom :=
      ModObj.isModHom_trivialAction G X.hom
    letI : ModObj G (pullback A.carrier.bundle.p X.hom) :=
      ModObj.pullbackTorsorAction A.carrier.bundle.p X.hom
        A.carrier.bundle.invariant
    letI : IsModHom G (pullback.fst A.carrier.bundle.p X.hom) :=
      ModObj.isModHom_pullback_fst G A.carrier.bundle.p X.hom
    letI : IsModHom G A.map := A.equivariant
    infer_instance

/-- The cartesian quotient morphism between two explicit pullbacks. -/
noncomputable def familyMap (A : ActionQuotientObj G U)
    {X Y : Over A.carrier.base} (f : X ⟶ Y) :
    familyObj A X ⟶ familyObj A Y where
  carrier :=
    { base := f.left
      total := pullbackTotalMap A.carrier.bundle f
      isPullback := pullbackTotalMap_isPullback A.carrier.bundle f
      equivariant := pullbackTotalMap_equivariant A.carrier.bundle f }
  map_naturality := by simp [familyObj, Category.assoc]

/-- Pulling back a quotient-stack object along all maps to its base gives a
concrete representative of its 2-Yoneda morphism. -/
noncomputable def family (A : ActionQuotientObj G U) :
    overBased A.carrier.base ⥤ᵇ actionQuotientPrestack G U where
  obj X := familyObj A X
  map f := familyMap A f
  map_id X := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · change 𝟙 X.left = (ClassifyingHom.id (familyObj A X).carrier).base
      rfl
    · change pullbackTotalMap A.carrier.bundle (𝟙 X) =
        (ClassifyingHom.id (familyObj A X).carrier).total
      rw [pullbackTotalMap_id]
      rfl
  map_comp f g := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · change (f ≫ g).left =
        (ClassifyingHom.comp
          (familyMap A f).carrier (familyMap A g).carrier).base
      rfl
    · change pullbackTotalMap A.carrier.bundle (f ≫ g) =
        (ClassifyingHom.comp
          (familyMap A f).carrier (familyMap A g).carrier).total
      exact (pullbackTotalMap_comp A.carrier.bundle f g).symm
  w := rfl

/-! ### The explicit quotient presentation -/

/-- The canonical map between trivial torsors induced by a map of bases. -/
noncomputable def trivialTotalMap {X Y : Over S} (f : X ⟶ Y) :
    (GlobalPrincipalBundle.trivial G X).P ⟶
      (GlobalPrincipalBundle.trivial G Y).P :=
  pullback.lift (GlobalPrincipalBundle.trivialFst G X)
    (GlobalPrincipalBundle.trivialSnd G X ≫ f)
    (by apply toUnit_unique)

@[reassoc (attr := simp)]
lemma trivialTotalMap_fst {X Y : Over S} (f : X ⟶ Y) :
    trivialTotalMap (G := G) f ≫ GlobalPrincipalBundle.trivialFst G Y =
      GlobalPrincipalBundle.trivialFst G X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma trivialTotalMap_snd {X Y : Over S} (f : X ⟶ Y) :
    trivialTotalMap (G := G) f ≫ GlobalPrincipalBundle.trivialSnd G Y =
      GlobalPrincipalBundle.trivialSnd G X ≫ f :=
  pullback.lift_snd _ _ _

lemma trivialTotalMap_id (X : Over S) :
    trivialTotalMap (G := G) (𝟙 X) = 𝟙 _ := by
  apply GlobalPrincipalBundle.trivial_hom_ext <;> simp

lemma trivialTotalMap_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    trivialTotalMap (G := G) f ≫ trivialTotalMap (G := G) g =
      trivialTotalMap (G := G) (f ≫ g) := by
  apply GlobalPrincipalBundle.trivial_hom_ext
  · simp
  · simp [Category.assoc]

lemma trivialTotalMap_equivariant {X Y : Over S} (f : X ⟶ Y) :
    IsModHom G (trivialTotalMap (G := G) f) := by
  constructor
  apply GlobalPrincipalBundle.trivial_hom_ext
  · calc
      (γ[G, (GlobalPrincipalBundle.trivial G X).P] ≫
          trivialTotalMap (G := G) f) ≫
          GlobalPrincipalBundle.trivialFst G Y =
        γ[G, (GlobalPrincipalBundle.trivial G X).P] ≫
          GlobalPrincipalBundle.trivialFst G X := by simp
      _ = (G ◁ GlobalPrincipalBundle.trivialFst G X) ≫ μ[G] :=
        GlobalPrincipalBundle.trivialFst_smul G X
      _ = (G ◁ (trivialTotalMap (G := G) f ≫
          GlobalPrincipalBundle.trivialFst G Y)) ≫ μ[G] := by
            rw [trivialTotalMap_fst]
      _ = ((G ◁ trivialTotalMap (G := G) f) ≫
          (G ◁ GlobalPrincipalBundle.trivialFst G Y)) ≫ μ[G] := by
            exact congrArg (fun q ↦ q ≫ μ[G])
              (MonoidalLeftAction.actionHomRight_comp G
                (trivialTotalMap (G := G) f)
                (GlobalPrincipalBundle.trivialFst G Y))
      _ = ((G ◁ trivialTotalMap (G := G) f) ≫
          γ[G, (GlobalPrincipalBundle.trivial G Y).P]) ≫
          GlobalPrincipalBundle.trivialFst G Y := by
            rw [Category.assoc]
            exact congrArg (fun q ↦ (G ◁ trivialTotalMap (G := G) f) ≫ q)
              (GlobalPrincipalBundle.trivialFst_smul G Y).symm
  · calc
      (γ[G, (GlobalPrincipalBundle.trivial G X).P] ≫
          trivialTotalMap (G := G) f) ≫
          GlobalPrincipalBundle.trivialSnd G Y =
        γ[G, (GlobalPrincipalBundle.trivial G X).P] ≫
          (GlobalPrincipalBundle.trivialSnd G X ≫ f) := by simp
      _ = (snd G (GlobalPrincipalBundle.trivial G X).P ≫
          GlobalPrincipalBundle.trivialSnd G X) ≫ f := by
            rw [← Category.assoc]
            exact congrArg (fun q ↦ q ≫ f)
              (GlobalPrincipalBundle.trivialSnd_invariant G X)
      _ = snd G (GlobalPrincipalBundle.trivial G X).P ≫
          (GlobalPrincipalBundle.trivialSnd G X ≫ f) :=
            Category.assoc _ _ _
      _ = snd G (GlobalPrincipalBundle.trivial G X).P ≫
          (trivialTotalMap (G := G) f ≫
            GlobalPrincipalBundle.trivialSnd G Y) := by
              rw [trivialTotalMap_snd]
      _ = ((G ◁ trivialTotalMap (G := G) f) ≫
          snd G (GlobalPrincipalBundle.trivial G Y).P) ≫
          GlobalPrincipalBundle.trivialSnd G Y := by
            rw [whiskerLeft_snd, Category.assoc]
      _ = ((G ◁ trivialTotalMap (G := G) f) ≫
          γ[G, (GlobalPrincipalBundle.trivial G Y).P]) ≫
          GlobalPrincipalBundle.trivialSnd G Y := by
            exact congrArg
              (fun q ↦ (G ◁ trivialTotalMap (G := G) f) ≫ q)
              (GlobalPrincipalBundle.trivialSnd_invariant G Y).symm

lemma trivialTotalMap_isPullback {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (trivialTotalMap (G := G) f)
      (GlobalPrincipalBundle.trivialSnd G X)
      (GlobalPrincipalBundle.trivialSnd G Y) f := by
  apply IsPullback.mk'
  · exact trivialTotalMap_snd (G := G) f
  · intro Q a b hab hbase
    apply GlobalPrincipalBundle.trivial_hom_ext
    · have h := congrArg
        (fun q ↦ q ≫ GlobalPrincipalBundle.trivialFst G Y) hab
      simpa only [Category.assoc, trivialTotalMap_fst] using h
    · exact hbase
  · intro Q a b hab
    let l : Q ⟶ (GlobalPrincipalBundle.trivial G X).P :=
      pullback.lift (a ≫ GlobalPrincipalBundle.trivialFst G Y) b
        (by apply toUnit_unique)
    refine ⟨l, ?_, ?_⟩
    · apply GlobalPrincipalBundle.trivial_hom_ext
      · rw [Category.assoc, trivialTotalMap_fst]
        dsimp only [l, GlobalPrincipalBundle.trivialFst]
        exact pullback.lift_fst
          (a ≫ GlobalPrincipalBundle.trivialFst G Y) b _
      · change l ≫ trivialTotalMap (G := G) f ≫
          GlobalPrincipalBundle.trivialSnd G Y =
          a ≫ GlobalPrincipalBundle.trivialSnd G Y
        rw [trivialTotalMap_snd]
        have hl : l ≫ GlobalPrincipalBundle.trivialSnd G X = b := by
          dsimp only [l, GlobalPrincipalBundle.trivialSnd]
          exact pullback.lift_snd
            (a ≫ GlobalPrincipalBundle.trivialFst G Y) b _
        calc
          l ≫ GlobalPrincipalBundle.trivialSnd G X ≫ f = b ≫ f := by
            rw [← Category.assoc, hl]
          _ = a ≫ GlobalPrincipalBundle.trivialSnd G Y := hab.symm
    · exact pullback.lift_snd _ _ _

lemma trivialTotalMap_actionMapTo {X Y : Over S} (f : X ⟶ Y)
    (y : Y ⟶ U) :
    trivialTotalMap (G := G) f ≫
        GlobalPrincipalBundle.trivialActionMapTo (G := G) y =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) (f ≫ y) := by
  simp only [GlobalPrincipalBundle.trivialActionMapTo, ModObj.comp_smul,
    trivialTotalMap_fst, trivialTotalMap_snd_assoc, Category.assoc]

/-- The explicit value of the quotient presentation on `X → U`. -/
noncomputable def presentationObj (X : Over U) : ActionQuotientObj G U where
  carrier :=
    { base := X.left
      bundle := GlobalPrincipalBundle.trivial G X.left }
  map := GlobalPrincipalBundle.trivialActionMapTo (G := G) X.hom
  equivariant :=
    GlobalPrincipalBundle.trivialActionMapTo_equivariant (G := G) X.hom

/-- The quotient morphism between two values of the explicit presentation. -/
noncomputable def presentationMap {X Y : Over U} (f : X ⟶ Y) :
    presentationObj (G := G) (U := U) X ⟶
      presentationObj (G := G) (U := U) Y where
  carrier :=
    { base := f.left
      total := trivialTotalMap (G := G) f.left
      isPullback := trivialTotalMap_isPullback (G := G) f.left
      equivariant := trivialTotalMap_equivariant (G := G) f.left }
  map_naturality := by
    change trivialTotalMap (G := G) f.left ≫
        GlobalPrincipalBundle.trivialActionMapTo (G := G) Y.hom =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) X.hom
    rw [trivialTotalMap_actionMapTo (G := G)]
    congr 1
    exact Over.w f

/-- The explicit family of trivial torsors representing `U → [U/G]`. -/
noncomputable def presentationFamily :
    overBased U ⥤ᵇ actionQuotientPrestack G U where
  obj X := presentationObj (G := G) (U := U) X
  map f := presentationMap (G := G) (U := U) f
  map_id X := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change trivialTotalMap (G := G) (𝟙 X.left) = 𝟙 _
      exact trivialTotalMap_id (G := G) X.left
  map_comp f g := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change trivialTotalMap (G := G) (f.left ≫ g.left) =
        trivialTotalMap (G := G) f.left ≫ trivialTotalMap (G := G) g.left
      exact (trivialTotalMap_comp (G := G) f.left g.left).symm
  w := rfl

/-! ### The comparison over the total space -/

variable (A : ActionQuotientObj G U)

/-- The point-induced isomorphism from the trivial torsor to the pullback
torsor. -/
noncomputable def pointTotalIso (x : Over A.carrier.bundle.P) :
    (GlobalPrincipalBundle.trivial G x.left).P ≅
      pullback A.carrier.bundle.p (x.hom ≫ A.carrier.bundle.p) where
  hom := GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom
  inv := GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom
  hom_inv_id := GlobalPrincipalBundle.pointPullbackTotal_hom_inv
    A.carrier.bundle x.hom
  inv_hom_id := GlobalPrincipalBundle.pointPullbackTotal_inv_hom
    A.carrier.bundle x.hom

/-- The point-induced trivialization, oriented from the pulled-back family to
the trivial presentation family. -/
noncomputable def pointHom (x : Over A.carrier.bundle.P) :
    familyObj A ((overMap A.carrier.bundle.p).obj x) ⟶
      presentationObj (G := G) (U := U) ((overMap A.map).obj x) where
  carrier :=
    { base := 𝟙 x.left
      total := (pointTotalIso A x).inv
      isPullback := by
        letI : IsIso (𝟙 x.left) := by infer_instance
        apply IsPullback.of_horiz_isIso
        constructor
        change (pointTotalIso A x).inv ≫
            GlobalPrincipalBundle.trivialSnd G x.left =
          pullback.snd A.carrier.bundle.p
              (x.hom ≫ A.carrier.bundle.p) ≫ 𝟙 x.left
        rw [show (pointTotalIso A x).inv =
          GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom from rfl]
        simp
      equivariant := by
        letI : ModObj G
            (pullback A.carrier.bundle.p
              (x.hom ≫ A.carrier.bundle.p)) :=
          ModObj.pullbackTorsorAction A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p)
            A.carrier.bundle.invariant
        let e := pointTotalIso A x
        letI : IsModHom G e.hom :=
          GlobalPrincipalBundle.pointPullbackTotal_equivariant
            A.carrier.bundle x.hom
        exact inferInstance }
  map_naturality := by
    letI : IsModHom G A.map := A.equivariant
    change GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom ≫
        GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (x.hom ≫ A.map) =
      pullback.fst A.carrier.bundle.p
          (x.hom ≫ A.carrier.bundle.p) ≫ A.map
    rw [← cancel_epi (GlobalPrincipalBundle.pointPullbackTotal
      A.carrier.bundle x.hom)]
    calc
      GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          (GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom ≫
            GlobalPrincipalBundle.trivialActionMapTo
              (G := G) (x.hom ≫ A.map)) =
        (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom) ≫
            GlobalPrincipalBundle.trivialActionMapTo
              (G := G) (x.hom ≫ A.map) :=
          (Category.assoc _ _ _).symm
      _ = GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (x.hom ≫ A.map) := by
            rw [GlobalPrincipalBundle.pointPullbackTotal_hom_inv,
              Category.id_comp]
      _ = GlobalPrincipalBundle.trivialActionMapTo (G := G) x.hom ≫
          A.map :=
        (GlobalPrincipalBundle.trivialActionMapTo_comp
          (G := G) x.hom A.map).symm
      _ = (GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle x.hom ≫
          pullback.fst A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p)) ≫ A.map := by
              rw [GlobalPrincipalBundle.pointPullbackTotal_fst]
      _ = GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle x.hom ≫
          (pullback.fst A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p) ≫ A.map) :=
        Category.assoc _ _ _

/-- The inverse point-induced trivialization. -/
noncomputable def pointInv (x : Over A.carrier.bundle.P) :
    presentationObj (G := G) (U := U) ((overMap A.map).obj x) ⟶
      familyObj A ((overMap A.carrier.bundle.p).obj x) where
  carrier :=
    { base := 𝟙 x.left
      total := (pointTotalIso A x).hom
      isPullback := by
        letI : IsIso (𝟙 x.left) := by infer_instance
        apply IsPullback.of_horiz_isIso
        constructor
        change (pointTotalIso A x).hom ≫
            pullback.snd A.carrier.bundle.p
              (x.hom ≫ A.carrier.bundle.p) =
          GlobalPrincipalBundle.trivialSnd G x.left ≫ 𝟙 x.left
        rw [show (pointTotalIso A x).hom =
          GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom from rfl]
        simp
      equivariant :=
        GlobalPrincipalBundle.pointPullbackTotal_equivariant
          A.carrier.bundle x.hom }
  map_naturality := by
    letI : IsModHom G A.map := A.equivariant
    change GlobalPrincipalBundle.pointPullbackTotal
        A.carrier.bundle x.hom ≫
          pullback.fst A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p) ≫ A.map =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) (x.hom ≫ A.map)
    rw [← Category.assoc,
      GlobalPrincipalBundle.pointPullbackTotal_fst]
    exact GlobalPrincipalBundle.trivialActionMapTo_comp
      (G := G) x.hom A.map

/-- The canonical isomorphism between the two pulled-back quotient objects. -/
noncomputable def pointIso (x : Over A.carrier.bundle.P) :
    familyObj A ((overMap A.carrier.bundle.p).obj x) ≅
      presentationObj (G := G) (U := U) ((overMap A.map).obj x) where
  hom := pointHom A x
  inv := pointInv A x
  hom_inv_id := by
    change ActionQuotientHom.comp (pointHom A x) (pointInv A x) =
      ActionQuotientHom.id _
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · simp only [ActionQuotientHom.comp_carrier,
        ActionQuotientHom.id_carrier, ClassifyingHom.comp_base,
        ClassifyingHom.id_base]
      change (𝟙 x.left : x.left ⟶ x.left) ≫ 𝟙 x.left = 𝟙 x.left
      simp
    · simp only [ActionQuotientHom.comp_carrier,
        ActionQuotientHom.id_carrier, ClassifyingHom.comp_total,
        ClassifyingHom.id_total]
      exact GlobalPrincipalBundle.pointPullbackTotal_inv_hom
          A.carrier.bundle x.hom
  inv_hom_id := by
    change ActionQuotientHom.comp (pointInv A x) (pointHom A x) =
      ActionQuotientHom.id _
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · simp only [ActionQuotientHom.comp_carrier,
        ActionQuotientHom.id_carrier, ClassifyingHom.comp_base,
        ClassifyingHom.id_base]
      change (𝟙 x.left : x.left ⟶ x.left) ≫ 𝟙 x.left = 𝟙 x.left
      simp
    · simp only [ActionQuotientHom.comp_carrier,
        ActionQuotientHom.id_carrier, ClassifyingHom.comp_total,
        ClassifyingHom.id_total]
      exact GlobalPrincipalBundle.pointPullbackTotal_hom_inv
          A.carrier.bundle x.hom

/-- Point-induced trivializations commute with change of the chosen point. -/
lemma pointPullbackTotal_naturality {x y : Over A.carrier.bundle.P}
    (f : x ⟶ y) :
    trivialTotalMap (G := G) f.left ≫
        GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle y.hom =
      GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
        pullbackTotalMap A.carrier.bundle
          ((overMap A.carrier.bundle.p).map f) := by
  apply pullback.hom_ext
  · calc
      (trivialTotalMap (G := G) f.left ≫
          GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle y.hom) ≫
          pullback.fst A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p) =
        trivialTotalMap (G := G) f.left ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) y.hom := by simp
      _ = GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (f.left ≫ y.hom) :=
        trivialTotalMap_actionMapTo (G := G) f.left y.hom
      _ = GlobalPrincipalBundle.trivialActionMapTo (G := G) x.hom := by
        rw [Over.w f]
      _ = GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
          pullback.fst A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p) :=
        (GlobalPrincipalBundle.pointPullbackTotal_fst
          A.carrier.bundle x.hom).symm
      _ = GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
            (pullbackTotalMap A.carrier.bundle
              ((overMap A.carrier.bundle.p).map f) ≫
          pullback.fst A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p)) := by
        congr 1
        simpa only [overMap, Over.map_obj_hom] using
          (pullbackTotalMap_fst A.carrier.bundle
            ((overMap A.carrier.bundle.p).map f)).symm
      _ = (GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
            pullbackTotalMap A.carrier.bundle
              ((overMap A.carrier.bundle.p).map f)) ≫
          pullback.fst A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p) :=
        (Category.assoc _ _ _).symm
  · calc
      (trivialTotalMap (G := G) f.left ≫
          GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle y.hom) ≫
          pullback.snd A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p) =
        trivialTotalMap (G := G) f.left ≫
          GlobalPrincipalBundle.trivialSnd G y.left := by
            rw [Category.assoc,
              GlobalPrincipalBundle.pointPullbackTotal_snd]
      _ = GlobalPrincipalBundle.trivialSnd G x.left ≫ f.left :=
        trivialTotalMap_snd (G := G) f.left
      _ = (GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
          pullback.snd A.carrier.bundle.p
            (x.hom ≫ A.carrier.bundle.p)) ≫ f.left := by
        rw [GlobalPrincipalBundle.pointPullbackTotal_snd]
      _ = GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
            (pullback.snd A.carrier.bundle.p
              (x.hom ≫ A.carrier.bundle.p) ≫ f.left) :=
        Category.assoc _ _ _
      _ = GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
            (pullbackTotalMap A.carrier.bundle
              ((overMap A.carrier.bundle.p).map f) ≫
          pullback.snd A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p)) := by
        congr 1
        simpa only [overMap, Over.map_obj_hom, Over.map_obj_left,
          Over.map_map_left] using
          (pullbackTotalMap_snd A.carrier.bundle
            ((overMap A.carrier.bundle.p).map f)).symm
      _ = (GlobalPrincipalBundle.pointPullbackTotal
          A.carrier.bundle x.hom ≫
            pullbackTotalMap A.carrier.bundle
              ((overMap A.carrier.bundle.p).map f)) ≫
          pullback.snd A.carrier.bundle.p
            (y.hom ≫ A.carrier.bundle.p) :=
        (Category.assoc _ _ _).symm

lemma pointPullbackInv_naturality {x y : Over A.carrier.bundle.P}
    (f : x ⟶ y) :
    pullbackTotalMap A.carrier.bundle
          ((overMap A.carrier.bundle.p).map f) ≫
        GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle y.hom =
      GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom ≫
        trivialTotalMap (G := G) f.left := by
  rw [← cancel_epi (GlobalPrincipalBundle.pointPullbackTotal
    A.carrier.bundle x.hom)]
  have hnat := pointPullbackTotal_naturality A f
  calc
    GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          (pullbackTotalMap A.carrier.bundle
            ((overMap A.carrier.bundle.p).map f) ≫
              GlobalPrincipalBundle.pointPullbackInv
                A.carrier.bundle y.hom) =
        (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          pullbackTotalMap A.carrier.bundle
            ((overMap A.carrier.bundle.p).map f)) ≫
          GlobalPrincipalBundle.pointPullbackInv
            A.carrier.bundle y.hom := (Category.assoc _ _ _).symm
    _ =
        (trivialTotalMap (G := G) f.left ≫
            GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle y.hom) ≫
          GlobalPrincipalBundle.pointPullbackInv
            A.carrier.bundle y.hom := by rw [← hnat]
    _ = trivialTotalMap (G := G) f.left ≫
        (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle y.hom ≫
          GlobalPrincipalBundle.pointPullbackInv
            A.carrier.bundle y.hom) := Category.assoc _ _ _
    _ = trivialTotalMap (G := G) f.left := by
      rw [GlobalPrincipalBundle.pointPullbackTotal_hom_inv,
        Category.comp_id]
    _ = (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom) ≫
        trivialTotalMap (G := G) f.left := by
      rw [GlobalPrincipalBundle.pointPullbackTotal_hom_inv,
        Category.id_comp]
    _ = GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
        (GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom ≫
          trivialTotalMap (G := G) f.left) := Category.assoc _ _ _

lemma pointIso_naturality {x y : Over A.carrier.bundle.P} (f : x ⟶ y) :
    (family A).map ((overMap A.carrier.bundle.p).map f) ≫
        (pointIso A y).hom =
      (pointIso A x).hom ≫
        presentationFamily.map ((overMap A.map).map f) := by
  apply ActionQuotientHom.ext
  apply ClassifyingHom.ext
  · rfl
  · exact pointPullbackInv_naturality A f

/-- The 2-isomorphism making the total-space square commute. -/
noncomputable def squareIso :
    (overMap A.carrier.bundle.p).comp (family A) ≅
      (overMap A.map).comp (presentationFamily (G := G) (U := U)) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (pointIso A) (fun f ↦ pointIso_naturality A f))
    (fun x ↦ by
      exact Functor.IsHomLift.map
        (p := (actionQuotientPrestack G U).p) (pointIso A x).hom)

/-- The canonical comparison from `P` to the 2-fiber product
`T ×_[U/G] U`. -/
noncomputable abbrev comparison :
    overBased A.carrier.bundle.P ⥤ᵇ
      fiberProduct (family A) (presentationFamily (G := G) (U := U)) :=
  fiberProductLift (overMap A.carrier.bundle.p) (overMap A.map) (squareIso A)

instance comparison_faithful : (comparison A).toFunctor.Faithful where
  map_injective {_ _} f g h := by
    apply Over.OverMorphism.ext
    have hfst := congrArg FiberProductHom.fst h
    have hleft := congrArg Over.Hom.left hfst
    exact hleft

lemma comparisonHom_base_eq {x y : Over A.carrier.bundle.P}
    (q : (comparison A).obj x ⟶ (comparison A).obj y) :
    q.fst.left = q.snd.left := by
  letI hq : IsHomLift (overBased U).p
      ((overBased A.carrier.base).p.map q.fst) q.snd := q.isHomLift
  have h := IsHomLift.fac' (overBased U).p
    ((overBased A.carrier.base).p.map q.fst) q.snd
  have hd : IsHomLift.domain_eq (overBased U).p
      ((overBased A.carrier.base).p.map q.fst) q.snd = rfl :=
    Subsingleton.elim _ _
  have hc : IsHomLift.codomain_eq (overBased U).p
      ((overBased A.carrier.base).p.map q.fst) q.snd = rfl :=
    Subsingleton.elim _ _
  rw [hd, hc] at h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
  change q.snd.left = q.fst.left at h
  exact h.symm

lemma comparisonHom_over_w {x y : Over A.carrier.bundle.P}
    (q : (comparison A).obj x ⟶ (comparison A).obj y) :
    q.fst.left ≫ y.hom = x.hom := by
  let k : x.left ⟶ y.left := q.snd.left
  have hk : q.fst.left = k := comparisonHom_base_eq A q
  have hw := congrArg
    (fun z ↦ (ActionQuotientHom.carrier z).total) q.w
  change pullbackTotalMap A.carrier.bundle q.fst ≫
        GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle y.hom =
      GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle x.hom ≫
        trivialTotalMap (G := G) k at hw
  have htriv :
      GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle x.hom ≫
          pullbackTotalMap A.carrier.bundle q.fst =
        trivialTotalMap (G := G) k ≫
          GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle y.hom := by
    letI : IsIso (GlobalPrincipalBundle.pointPullbackInv
        A.carrier.bundle y.hom) :=
      ⟨⟨GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle y.hom,
        GlobalPrincipalBundle.pointPullbackTotal_inv_hom
          A.carrier.bundle y.hom,
        GlobalPrincipalBundle.pointPullbackTotal_hom_inv
          A.carrier.bundle y.hom⟩⟩
    rw [← cancel_mono (GlobalPrincipalBundle.pointPullbackInv
      A.carrier.bundle y.hom)]
    calc
      (GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle x.hom ≫
          pullbackTotalMap A.carrier.bundle q.fst) ≫
          GlobalPrincipalBundle.pointPullbackInv
            A.carrier.bundle y.hom =
        GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle x.hom ≫
          (pullbackTotalMap A.carrier.bundle q.fst ≫
            GlobalPrincipalBundle.pointPullbackInv
              A.carrier.bundle y.hom) := Category.assoc _ _ _
      _ = GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle x.hom ≫
          (GlobalPrincipalBundle.pointPullbackInv
              A.carrier.bundle x.hom ≫
            trivialTotalMap (G := G) k) := by rw [hw]
      _ = (GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle x.hom ≫
            GlobalPrincipalBundle.pointPullbackInv
              A.carrier.bundle x.hom) ≫
          trivialTotalMap (G := G) k :=
        (Category.assoc _ _ _).symm
      _ = trivialTotalMap (G := G) k := by
        rw [GlobalPrincipalBundle.pointPullbackTotal_hom_inv,
          Category.id_comp]
      _ = (trivialTotalMap (G := G) k ≫
          GlobalPrincipalBundle.pointPullbackTotal
            A.carrier.bundle y.hom) ≫
          GlobalPrincipalBundle.pointPullbackInv
            A.carrier.bundle y.hom := by
        rw [Category.assoc,
          GlobalPrincipalBundle.pointPullbackTotal_hom_inv,
          Category.comp_id]
  have haction :
      GlobalPrincipalBundle.trivialActionMapTo (G := G) x.hom =
        GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (k ≫ y.hom) := by
    calc
      GlobalPrincipalBundle.trivialActionMapTo (G := G) x.hom =
          GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle x.hom ≫
            pullback.fst A.carrier.bundle.p
              (x.hom ≫ A.carrier.bundle.p) :=
        (GlobalPrincipalBundle.pointPullbackTotal_fst
          A.carrier.bundle x.hom).symm
      _ = GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle x.hom ≫
            (pullbackTotalMap A.carrier.bundle q.fst ≫
              pullback.fst A.carrier.bundle.p
                (y.hom ≫ A.carrier.bundle.p)) := by
        congr 1
        simpa only [comparison, fiberProductLift, overMap,
          Over.map_obj_hom] using
          (pullbackTotalMap_fst A.carrier.bundle q.fst).symm
      _ = (GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle x.hom ≫
            pullbackTotalMap A.carrier.bundle q.fst) ≫
              pullback.fst A.carrier.bundle.p
                (y.hom ≫ A.carrier.bundle.p) :=
        (Category.assoc _ _ _).symm
      _ = (trivialTotalMap (G := G) k ≫
            GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle y.hom) ≫
              pullback.fst A.carrier.bundle.p
                (y.hom ≫ A.carrier.bundle.p) := by rw [htriv]
      _ = trivialTotalMap (G := G) k ≫
          (GlobalPrincipalBundle.pointPullbackTotal
              A.carrier.bundle y.hom ≫
            pullback.fst A.carrier.bundle.p
              (y.hom ≫ A.carrier.bundle.p)) := Category.assoc _ _ _
      _ = trivialTotalMap (G := G) k ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) y.hom := by
        rw [GlobalPrincipalBundle.pointPullbackTotal_fst]
      _ = GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (k ≫ y.hom) :=
        trivialTotalMap_actionMapTo (G := G) k y.hom
  calc
    q.fst.left ≫ y.hom = k ≫ y.hom := by rw [hk]
    _ = GlobalPrincipalBundle.trivialSection
          (G := G) (T := x.left) ≫
        GlobalPrincipalBundle.trivialActionMapTo
          (G := G) (k ≫ y.hom) :=
      (GlobalPrincipalBundle.trivialSection_actionMapTo
        (G := G) (k ≫ y.hom)).symm
    _ = GlobalPrincipalBundle.trivialSection
          (G := G) (T := x.left) ≫
        GlobalPrincipalBundle.trivialActionMapTo (G := G) x.hom := by
      rw [haction]
    _ = x.hom :=
      GlobalPrincipalBundle.trivialSection_actionMapTo (G := G) x.hom

instance comparison_full : (comparison A).toFunctor.Full where
  map_surjective {x y} q := by
    let f : x ⟶ y := Over.homMk q.fst.left (comparisonHom_over_w A q)
    refine ⟨f, ?_⟩
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      exact comparisonHom_base_eq A q

/-! ### Essential surjectivity of the comparison -/

variable (q : FiberProductObj (family A)
  (presentationFamily (G := G) (U := U)))

/-- The isomorphism between the bases underlying the comparison isomorphism. -/
noncomputable def preimageBaseIso : q.snd.left ≅ q.fst.left := by
  exact ((actionQuotientPrestack G U).p.mapIso q.iso).symm

/-- Recover a point of `P` by applying the inverse comparison isomorphism to
the unit section of the trivial torsor. -/
noncomputable def preimageMap : q.snd.left ⟶ A.carrier.bundle.P :=
  GlobalPrincipalBundle.trivialSection (G := G) (T := q.snd.left) ≫
    q.iso.inv.carrier.total ≫
      pullback.fst A.carrier.bundle.p q.fst.hom

/-- The recovered point, as an object of the representable prestack `P`. -/
noncomputable abbrev preimageObj : Over A.carrier.bundle.P :=
  Over.mk (preimageMap A q)

lemma preimageMap_comp_p :
    preimageMap A q ≫ A.carrier.bundle.p =
      (preimageBaseIso A q).hom ≫ q.fst.hom := by
  have hbase : q.iso.inv.carrier.total ≫
        pullback.snd A.carrier.bundle.p q.fst.hom =
      GlobalPrincipalBundle.trivialSnd G q.snd.left ≫
        q.iso.inv.carrier.base := by
    simpa only [family, familyObj, presentationFamily, presentationObj,
      GlobalPrincipalBundle.pullback, GlobalPrincipalBundle.trivial,
      GlobalPrincipalBundle.universal, GlobalPrincipalBundle.trivialSnd] using
      q.iso.inv.carrier.isPullback.w
  calc
    preimageMap A q ≫ A.carrier.bundle.p =
        GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          q.iso.inv.carrier.total ≫
            (pullback.fst A.carrier.bundle.p q.fst.hom ≫
              A.carrier.bundle.p) := by
      simp only [preimageMap, Category.assoc]
    _ = GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          q.iso.inv.carrier.total ≫
            (pullback.snd A.carrier.bundle.p q.fst.hom ≫
              q.fst.hom) := by rw [pullback.condition]
    _ = GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          (q.iso.inv.carrier.total ≫
            pullback.snd A.carrier.bundle.p q.fst.hom) ≫
              q.fst.hom := by simp only [Category.assoc]
    _ = GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          (GlobalPrincipalBundle.trivialSnd G q.snd.left ≫
            q.iso.inv.carrier.base) ≫ q.fst.hom := by
      rw [hbase]
    _ = (GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          GlobalPrincipalBundle.trivialSnd G q.snd.left) ≫
        q.iso.inv.carrier.base ≫ q.fst.hom := by
      simp only [Category.assoc]
    _ = q.iso.inv.carrier.base ≫ q.fst.hom := by
      rw [GlobalPrincipalBundle.trivialSection_snd,
        Category.id_comp]
    _ = (preimageBaseIso A q).hom ≫ q.fst.hom := rfl

lemma preimageMap_comp_map :
    preimageMap A q ≫ A.map = q.snd.hom := by
  have hmap : q.iso.inv.carrier.total ≫
        (pullback.fst A.carrier.bundle.p q.fst.hom ≫ A.map) =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) q.snd.hom := by
    simpa only [family, familyObj, presentationFamily, presentationObj] using
      q.iso.inv.map_naturality
  calc
    preimageMap A q ≫ A.map =
        GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          (q.iso.inv.carrier.total ≫
            (pullback.fst A.carrier.bundle.p q.fst.hom ≫ A.map)) := by
      simp only [preimageMap, Category.assoc]
    _ = GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) q.snd.hom := by
      rw [hmap]
    _ = q.snd.hom :=
      GlobalPrincipalBundle.trivialSection_actionMapTo
        (G := G) q.snd.hom

/-- The first component of the recovered comparison is isomorphic to the
given object over `T`. -/
noncomputable def preimageFstIso :
    ((comparison A).obj (preimageObj A q)).fst ≅ q.fst :=
  Over.isoMk (preimageBaseIso A q) (by
    exact (preimageMap_comp_p A q).symm)

/-- The second component of the recovered comparison is the given object over
`U`, up to the identity-base isomorphism. -/
noncomputable def preimageSndIso :
    ((comparison A).obj (preimageObj A q)).snd ≅ q.snd :=
  Over.isoMk (Iso.refl q.snd.left) (by
    change (𝟙 q.snd.left) ≫ q.snd.hom = preimageMap A q ≫ A.map
    simpa only [Category.id_comp] using (preimageMap_comp_map A q).symm)

/-- The point-induced trivialization attached to the recovered point agrees
with the inverse of the given comparison isomorphism. -/
lemma preimagePointTotal_comp :
    GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
          (preimageMap A q) ≫
        pullbackTotalMap A.carrier.bundle (preimageFstIso A q).hom =
      q.iso.inv.carrier.total := by
  letI : ModObj G
      (pullback A.carrier.bundle.p
        (preimageMap A q ≫ A.carrier.bundle.p)) :=
    ModObj.pullbackTorsorAction A.carrier.bundle.p
      (preimageMap A q ≫ A.carrier.bundle.p)
      A.carrier.bundle.invariant
  letI : ModObj G
      (pullback A.carrier.bundle.p q.fst.hom) :=
    ModObj.pullbackTorsorAction A.carrier.bundle.p q.fst.hom
      A.carrier.bundle.invariant
  letI hpoint : IsModHom G
      (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
        (preimageMap A q)) :=
    GlobalPrincipalBundle.pointPullbackTotal_equivariant
      A.carrier.bundle (preimageMap A q)
  letI hchange : IsModHom G
      (pullbackTotalMap A.carrier.bundle (preimageFstIso A q).hom) :=
    pullbackTotalMap_equivariant A.carrier.bundle (preimageFstIso A q).hom
  letI hleft : IsModHom G
      (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
          (preimageMap A q) ≫
        pullbackTotalMap A.carrier.bundle (preimageFstIso A q).hom) :=
    inferInstance
  letI hright : IsModHom G q.iso.inv.carrier.total :=
    q.iso.inv.carrier.equivariant
  have hsection :
      GlobalPrincipalBundle.trivialSection
          (G := G) (T := q.snd.left) ≫
        (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
            (preimageMap A q) ≫
          pullbackTotalMap A.carrier.bundle (preimageFstIso A q).hom) =
      GlobalPrincipalBundle.trivialSection
          (G := G) (T := q.snd.left) ≫
        q.iso.inv.carrier.total := by
    have hfst : pullbackTotalMap A.carrier.bundle
          (preimageFstIso A q).hom ≫
        pullback.fst A.carrier.bundle.p q.fst.hom =
      pullback.fst A.carrier.bundle.p
        (preimageMap A q ≫ A.carrier.bundle.p) := by
      simpa only [comparison, fiberProductLift, overMap,
        Over.map_obj_hom, preimageObj, Over.mk_hom] using
          (pullbackTotalMap_fst A.carrier.bundle
            (preimageFstIso A q).hom)
    have hsnd : pullbackTotalMap A.carrier.bundle
          (preimageFstIso A q).hom ≫
        pullback.snd A.carrier.bundle.p q.fst.hom =
      pullback.snd A.carrier.bundle.p
          (preimageMap A q ≫ A.carrier.bundle.p) ≫
        (preimageFstIso A q).hom.left := by
      simpa only [comparison, fiberProductLift, overMap,
        Over.map_obj_hom, preimageObj, Over.mk_hom] using
          (pullbackTotalMap_snd A.carrier.bundle
            (preimageFstIso A q).hom)
    apply pullback.hom_ext
    · calc
        (GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              pullbackTotalMap A.carrier.bundle
                (preimageFstIso A q).hom)) ≫
            pullback.fst A.carrier.bundle.p q.fst.hom =
          GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              (pullbackTotalMap A.carrier.bundle
                  (preimageFstIso A q).hom ≫
                pullback.fst A.carrier.bundle.p q.fst.hom) := by
            simp only [Category.assoc]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              pullback.fst A.carrier.bundle.p
                (preimageMap A q ≫ A.carrier.bundle.p) := by rw [hfst]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.trivialActionMapTo
              (G := G) (preimageMap A q) := by
          rw [GlobalPrincipalBundle.pointPullbackTotal_fst]
        _ = preimageMap A q :=
          GlobalPrincipalBundle.trivialSection_actionMapTo
            (G := G) (preimageMap A q)
        _ = (GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            q.iso.inv.carrier.total) ≫
              pullback.fst A.carrier.bundle.p q.fst.hom := rfl
    · have hbase : q.iso.inv.carrier.total ≫
            pullback.snd A.carrier.bundle.p q.fst.hom =
          GlobalPrincipalBundle.trivialSnd G q.snd.left ≫
            q.iso.inv.carrier.base := by
        simpa only [family, familyObj, presentationFamily, presentationObj,
          GlobalPrincipalBundle.pullback, GlobalPrincipalBundle.trivial,
          GlobalPrincipalBundle.universal,
          GlobalPrincipalBundle.trivialSnd] using
            q.iso.inv.carrier.isPullback.w
      calc
        (GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              pullbackTotalMap A.carrier.bundle
                (preimageFstIso A q).hom)) ≫
            pullback.snd A.carrier.bundle.p q.fst.hom =
          GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              (pullbackTotalMap A.carrier.bundle
                  (preimageFstIso A q).hom ≫
                pullback.snd A.carrier.bundle.p q.fst.hom) := by
            simp only [Category.assoc]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              (pullback.snd A.carrier.bundle.p
                  (preimageMap A q ≫ A.carrier.bundle.p) ≫
                (preimageFstIso A q).hom.left) := by rw [hsnd]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
                (preimageMap A q) ≫
              pullback.snd A.carrier.bundle.p
                (preimageMap A q ≫ A.carrier.bundle.p)) ≫
                (preimageFstIso A q).hom.left := by
            simp only [Category.assoc]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            GlobalPrincipalBundle.trivialSnd G q.snd.left ≫
              (preimageFstIso A q).hom.left := by
          rw [GlobalPrincipalBundle.pointPullbackTotal_snd]
        _ = (preimageFstIso A q).hom.left := by
          rw [← Category.assoc,
            GlobalPrincipalBundle.trivialSection_snd,
            Category.id_comp]
        _ = q.iso.inv.carrier.base := rfl
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            (GlobalPrincipalBundle.trivialSnd G q.snd.left ≫
              q.iso.inv.carrier.base) := by
          rw [← Category.assoc,
            GlobalPrincipalBundle.trivialSection_snd,
            Category.id_comp]
        _ = GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            (q.iso.inv.carrier.total ≫
              pullback.snd A.carrier.bundle.p q.fst.hom) := by rw [hbase]
        _ = (GlobalPrincipalBundle.trivialSection
              (G := G) (T := q.snd.left) ≫
            q.iso.inv.carrier.total) ≫
              pullback.snd A.carrier.bundle.p q.fst.hom :=
          (Category.assoc _ _ _).symm
  calc
    GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
          (preimageMap A q) ≫
        pullbackTotalMap A.carrier.bundle (preimageFstIso A q).hom =
      GlobalPrincipalBundle.trivialActionMapTo (G := G)
        (GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
              (preimageMap A q) ≫
            pullbackTotalMap A.carrier.bundle
              (preimageFstIso A q).hom)) :=
        (GlobalPrincipalBundle.trivialActionMapTo_section_comp _).symm
    _ = GlobalPrincipalBundle.trivialActionMapTo (G := G)
        (GlobalPrincipalBundle.trivialSection
            (G := G) (T := q.snd.left) ≫
          q.iso.inv.carrier.total) := by rw [hsection]
    _ = q.iso.inv.carrier.total :=
      GlobalPrincipalBundle.trivialActionMapTo_section_comp _

lemma preimageIso_w :
    (family A).map (preimageFstIso A q).hom ≫ q.iso.hom =
      (pointIso A (preimageObj A q)).hom ≫
        presentationFamily.map (preimageSndIso A q).hom := by
  apply ActionQuotientHom.ext
  apply ClassifyingHom.ext
  · simp only [ActionQuotientHom.comp_carrier,
      ClassifyingHom.comp_base]
    have hbase := congrArg
      (fun z ↦ (ActionQuotientHom.carrier z).base) q.iso.inv_hom_id
    change q.iso.inv.carrier.base ≫ q.iso.hom.carrier.base =
      𝟙 q.snd.left at hbase
    change q.iso.inv.carrier.base ≫ q.iso.hom.carrier.base =
      (𝟙 q.snd.left : q.snd.left ⟶ q.snd.left) ≫ 𝟙 q.snd.left
    simpa only [Category.id_comp] using hbase
  · simp only [ActionQuotientHom.comp_carrier,
      ClassifyingHom.comp_total]
    have htotal := congrArg
      (fun z ↦ (ActionQuotientHom.carrier z).total) q.iso.inv_hom_id
    change q.iso.inv.carrier.total ≫ q.iso.hom.carrier.total =
      𝟙 (GlobalPrincipalBundle.trivial G q.snd.left).P at htotal
    have htrivial : trivialTotalMap (G := G)
        (preimageSndIso A q).hom.left =
          𝟙 (GlobalPrincipalBundle.trivial G q.snd.left).P := by
      change trivialTotalMap (G := G) (𝟙 q.snd.left) = 𝟙 _
      exact trivialTotalMap_id (G := G) q.snd.left
    change pullbackTotalMap A.carrier.bundle
          (preimageFstIso A q).hom ≫
        q.iso.hom.carrier.total =
      GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle
          (preimageMap A q) ≫
        trivialTotalMap (G := G) (preimageSndIso A q).hom.left
    rw [← cancel_epi (GlobalPrincipalBundle.pointPullbackTotal
      A.carrier.bundle (preimageMap A q))]
    calc
      GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
            (preimageMap A q) ≫
          (pullbackTotalMap A.carrier.bundle
              (preimageFstIso A q).hom ≫
            q.iso.hom.carrier.total) =
        (GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
              (preimageMap A q) ≫
            pullbackTotalMap A.carrier.bundle
              (preimageFstIso A q).hom) ≫
          q.iso.hom.carrier.total := (Category.assoc _ _ _).symm
      _ = q.iso.inv.carrier.total ≫
          q.iso.hom.carrier.total := by rw [preimagePointTotal_comp A q]
      _ = 𝟙 (GlobalPrincipalBundle.trivial G q.snd.left).P := htotal
      _ = GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
            (preimageMap A q) ≫
          GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle
            (preimageMap A q) :=
        (GlobalPrincipalBundle.pointPullbackTotal_hom_inv
          A.carrier.bundle (preimageMap A q)).symm
      _ = GlobalPrincipalBundle.pointPullbackTotal A.carrier.bundle
            (preimageMap A q) ≫
          (GlobalPrincipalBundle.pointPullbackInv A.carrier.bundle
              (preimageMap A q) ≫
            trivialTotalMap (G := G) (preimageSndIso A q).hom.left) := by
        rw [htrivial, Category.comp_id]

lemma fiberProductIso_hom_base_eq :
    q.iso.hom.carrier.base = eqToHom q.over_eq.symm := by
  letI hq : IsHomLift (actionQuotientPrestack G U).p
      (𝟙 q.fst.left) q.iso.hom := q.isHomLift
  have h := IsHomLift.fac' (actionQuotientPrestack G U).p
    (𝟙 q.fst.left) q.iso.hom
  have hd : IsHomLift.domain_eq (actionQuotientPrestack G U).p
      (𝟙 q.fst.left) q.iso.hom = rfl := Subsingleton.elim _ _
  have hc : IsHomLift.codomain_eq (actionQuotientPrestack G U).p
      (𝟙 q.fst.left) q.iso.hom = q.over_eq := Subsingleton.elim _ _
  rw [hd, hc] at h
  simp only [eqToHom_refl, Category.id_comp] at h
  simpa only [actionQuotientPrestack] using h

lemma preimageIso_isHomLift :
    IsHomLift (overBased U).p
      ((overBased A.carrier.base).p.map (preimageFstIso A q).hom)
      (preimageSndIso A q).hom := by
  apply IsHomLift.of_fac' (overBased U).p
    ((overBased A.carrier.base).p.map (preimageFstIso A q).hom)
    (preimageSndIso A q).hom rfl q.over_eq
  have hbase := congrArg
    (fun z ↦ (ActionQuotientHom.carrier z).base) q.iso.inv_hom_id
  change q.iso.inv.carrier.base ≫ q.iso.hom.carrier.base =
    𝟙 q.snd.left at hbase
  rw [fiberProductIso_hom_base_eq A q] at hbase
  change (𝟙 q.snd.left : q.snd.left ⟶ q.snd.left) =
    eqToHom rfl ≫ q.iso.inv.carrier.base ≫ eqToHom q.over_eq.symm
  simpa only [eqToHom_refl, Category.id_comp] using hbase.symm

/-- The comparison sends the recovered point to an object isomorphic to the
original fiber-product object. -/
noncomputable def preimageIso :
    (comparison A).obj (preimageObj A q) ≅ q :=
  fiberProductObjIsoMk (preimageFstIso A q) (preimageSndIso A q)
    (preimageIso_isHomLift A q) (preimageIso_w A q)

instance comparison_essSurj : (comparison A).toFunctor.EssSurj where
  mem_essImage q :=
    ⟨preimageObj A q, ⟨preimageIso A q⟩⟩

/-- **Exercise 3.4.37** (`exer:fiber-product-quotient-stacks`) (part (a)):
for an object `P → T` of `[U/G]`, pulling the universal presentation
`U → [U/G]` back along its classifying morphism recovers the total space
`P`. -/
theorem isCartesianSquare_totalSpace :
    IsCartesianSquare (overMap A.carrier.bundle.p) (overMap A.map)
      (squareIso A) := by
  letI : (comparison A).toFunctor.Faithful := comparison_faithful A
  letI : (comparison A).toFunctor.Full := comparison_full A
  letI : (comparison A).toFunctor.EssSurj := comparison_essSurj A
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- The comparison for the square obtained by pairing the bundle projection
and its equivariant map, with the diagonal of `[U/G]`. -/
noncomputable abbrev diagonalComparison :
    overBased A.carrier.bundle.P ⥤ᵇ
      fiberProduct
        (prodMap (family A) (presentationFamily (G := G) (U := U)))
        (diag (actionQuotientPrestack G U)) :=
  (comparison A).comp
    (fiberProductToProdMapDiag (family A)
      (presentationFamily (G := G) (U := U)))

/-- API generalization used in the proof of Exercise 3.4.37 (part (b),
diagonal form): pairing `P → T` with the equivariant map `P → U`
identifies `P` with the pullback of the diagonal of `[U/G]` along the product
of the two associated morphisms. -/
theorem isEquivalence_diagonalComparison :
    (diagonalComparison A).toFunctor.IsEquivalence := by
  letI : (comparison A).toFunctor.IsEquivalence :=
    isCartesianSquare_totalSpace A
  letI : (fiberProductToProdMapDiag (family A)
      (presentationFamily (G := G) (U := U))).toFunctor.IsEquivalence := by
    letI : (fiberProductToProdMapDiag (family A)
        (presentationFamily (G := G) (U := U))).toFunctor.Faithful :=
      fiberProductToProdMapDiag_faithful (family A)
        (presentationFamily (G := G) (U := U))
    letI : (fiberProductToProdMapDiag (family A)
        (presentationFamily (G := G) (U := U))).toFunctor.Full :=
      fiberProductToProdMapDiag_full (family A)
        (presentationFamily (G := G) (U := U))
    letI : (fiberProductToProdMapDiag (family A)
        (presentationFamily (G := G) (U := U))).toFunctor.EssSurj :=
      fiberProductToProdMapDiag_essSurj (family A)
        (presentationFamily (G := G) (U := U))
    exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  change ((comparison A).toFunctor ⋙
    (fiberProductToProdMapDiag (family A)
      (presentationFamily (G := G) (U := U))).toFunctor).IsEquivalence
  infer_instance

/-- **Exercise 3.4.37** (`exer:fiber-product-quotient-stacks`) (part (b),
first diagram): for the universal trivial-torsor object, the action graph
`G ×_S U → U ×_S U` is the self-pullback of the quotient presentation. -/
theorem isCartesianSquare_quotientPresentation :
    IsCartesianSquare
      (overMap (quotientPresentationObject G U).carrier.bundle.p)
      (overMap (quotientPresentationObject G U).map)
      (squareIso (quotientPresentationObject G U)) :=
  isCartesianSquare_totalSpace (quotientPresentationObject G U)

/-- **Exercise 3.4.37** (`exer:fiber-product-quotient-stacks`) (part (b),
second diagram): the action graph `(σ,p₂) : G ×_S U → U ×_S U`
presents the pullback of the diagonal of `[U/G]` along the product of the
quotient presentation with itself. -/
theorem isEquivalence_quotientPresentationDiagonal :
    (diagonalComparison (quotientPresentationObject G U)).toFunctor.IsEquivalence :=
  isEquivalence_diagonalComparison (quotientPresentationObject G U)

end QuotientFiberProduct

end AlgebraicGeometry.Scheme

end ExerFiberProductQuotientStacks
