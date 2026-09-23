module

public import StacksAndModuli.API.ActionQuotientStack
public import StacksAndModuli.API.BasedFunctorLocalEssentialSurjectivity
public import StacksAndModuli.API.PrincipalBundlePointTrivialization
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksProject.MoreOnMorphisms.SlicingSmooth.«lemma-etale-nbhd-dominates-smooth»

/-!
# Representable action quotient prestacks

An internal action of a group object on an object of a cartesian category induces
an action of the corresponding representable presheaves.  This file relates that
ordinary action quotient prestack to the principal-bundle quotient prestack used
for quotient stacks of schemes.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G U : C) [GrpObj G] [ModObj G U]

/-- An internal group action induces the pointwise action of the represented
group presheaf on the represented object presheaf. -/
abbrev representablePresheafAction : PresheafAction.{v} C where
  G := yonedaGrpObj G
  U := yoneda.obj U
  action T := Hom.mulAction (unop T)
  map_smul f g x := by
    exact ModObj.comp_smul f.unop g x

@[simp]
lemma representablePresheafAction_G :
    (representablePresheafAction G U).G = yonedaGrpObj G := rfl

@[simp]
lemma representablePresheafAction_U :
    (representablePresheafAction G U).U = yoneda.obj U := rfl

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G U : Over S) [GrpObj G] [ModObj G U]
  [Smooth G.hom] [IsAffineHom G.hom]

namespace GlobalPrincipalBundle

variable {G U} {T T' T'' : Over S}

/-- The canonical map `G ×ₛ T → G ×ₛ T'` of trivial principal
bundles induced by a map of bases `T → T'`. -/
noncomputable def trivialBaseMap (f : T ⟶ T') :
    (trivial G T).P ⟶ (trivial G T').P :=
  pullback.lift (trivialFst G T) (trivialSnd G T ≫ f)
    (by apply toUnit_unique)

@[reassoc (attr := simp)]
lemma trivialBaseMap_fst (f : T ⟶ T') :
    trivialBaseMap (G := G) f ≫ trivialFst G T' = trivialFst G T :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma trivialBaseMap_snd (f : T ⟶ T') :
    trivialBaseMap (G := G) f ≫ trivialSnd G T' = trivialSnd G T ≫ f :=
  pullback.lift_snd _ _ _

lemma trivialBaseMap_id :
    trivialBaseMap (G := G) (T := T) (T' := T) (𝟙 T) = 𝟙 _ := by
  apply trivial_hom_ext
  · simp
  · simp

lemma trivialBaseMap_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    trivialBaseMap (G := G) f ≫ trivialBaseMap (G := G) g =
      trivialBaseMap (G := G) (f ≫ g) := by
  apply trivial_hom_ext
  · simp
  · simp [Category.assoc]

/-- The canonical map between trivial bundles is equivariant. -/
lemma trivialBaseMap_equivariant (f : T ⟶ T') :
    IsModHom G (trivialBaseMap (G := G) f) := by
  constructor
  apply trivial_hom_ext
  · calc
      (γ[G, (trivial G T).P] ≫ trivialBaseMap (G := G) f) ≫
          trivialFst G T' = γ[G, (trivial G T).P] ≫ trivialFst G T := by
            rw [Category.assoc, trivialBaseMap_fst]
      _ = (G ◁ trivialFst G T) ≫ μ[G] := trivialFst_smul G T
      _ = (G ◁ (trivialBaseMap (G := G) f ≫ trivialFst G T')) ≫
          μ[G] := congrArg (fun q ↦ (G ◁ q) ≫ μ[G])
            (trivialBaseMap_fst (G := G) f).symm
      _ = ((G ◁ trivialBaseMap (G := G) f) ≫
          (G ◁ trivialFst G T')) ≫ μ[G] :=
            congrArg (fun q ↦ q ≫ μ[G])
              (MonoidalLeftAction.actionHomRight_comp G
                (trivialBaseMap (G := G) f) (trivialFst G T'))
      _ = (G ◁ trivialBaseMap (G := G) f) ≫
          ((G ◁ trivialFst G T') ≫ μ[G]) := Category.assoc _ _ _
      _ = (G ◁ trivialBaseMap (G := G) f) ≫
          (γ[G, (trivial G T').P] ≫ trivialFst G T') :=
            congrArg (fun q ↦ (G ◁ trivialBaseMap (G := G) f) ≫ q)
              (trivialFst_smul G T').symm
      _ = ((G ◁ trivialBaseMap (G := G) f) ≫
          γ[G, (trivial G T').P]) ≫ trivialFst G T' :=
            (Category.assoc _ _ _).symm
  · calc
      (γ[G, (trivial G T).P] ≫ trivialBaseMap (G := G) f) ≫
          trivialSnd G T' = γ[G, (trivial G T).P] ≫
            (trivialSnd G T ≫ f) := by rw [Category.assoc, trivialBaseMap_snd]
      _ = (γ[G, (trivial G T).P] ≫ trivialSnd G T) ≫ f :=
            (Category.assoc _ _ _).symm
      _ = (snd G (trivial G T).P ≫ trivialSnd G T) ≫ f :=
            congrArg (fun q ↦ q ≫ f) (trivialSnd_invariant G T)
      _ = snd G (trivial G T).P ≫ (trivialSnd G T ≫ f) :=
            Category.assoc _ _ _
      _ = snd G (trivial G T).P ≫
          (trivialBaseMap (G := G) f ≫ trivialSnd G T') :=
            congrArg (fun q ↦ snd G (trivial G T).P ≫ q)
              (trivialBaseMap_snd (G := G) f).symm
      _ = (snd G (trivial G T).P ≫ trivialBaseMap (G := G) f) ≫
          trivialSnd G T' := (Category.assoc _ _ _).symm
      _ = ((G ◁ trivialBaseMap (G := G) f) ≫
          snd G (trivial G T').P) ≫ trivialSnd G T' :=
            congrArg (fun q ↦ q ≫ trivialSnd G T')
              (whiskerLeft_snd G (trivialBaseMap (G := G) f)).symm
      _ = (G ◁ trivialBaseMap (G := G) f) ≫
          (snd G (trivial G T').P ≫ trivialSnd G T') := Category.assoc _ _ _
      _ = (G ◁ trivialBaseMap (G := G) f) ≫
          (γ[G, (trivial G T').P] ≫ trivialSnd G T') :=
            congrArg (fun q ↦ (G ◁ trivialBaseMap (G := G) f) ≫ q)
              (trivialSnd_invariant G T').symm
      _ = ((G ◁ trivialBaseMap (G := G) f) ≫
          γ[G, (trivial G T').P]) ≫ trivialSnd G T' :=
            (Category.assoc _ _ _).symm

/-- The square of bundle projections induced by a map between the bases of
trivial bundles is cartesian. -/
lemma trivialBaseMap_isPullback (f : T ⟶ T') :
    IsPullback (trivialBaseMap (G := G) f) (trivialSnd G T)
      (trivialSnd G T') f := by
  apply IsPullback.mk'
  · exact trivialBaseMap_snd (G := G) f
  · intro Q a b hab hbase
    apply trivial_hom_ext
    · have h := congrArg (fun q ↦ q ≫ trivialFst G T') hab
      simpa only [Category.assoc, trivialBaseMap_fst] using h
    · exact hbase
  · intro Q a b hab
    let l : Q ⟶ (trivial G T).P :=
      pullback.lift (a ≫ trivialFst G T') b (by apply toUnit_unique)
    refine ⟨l, ?_, ?_⟩
    · apply trivial_hom_ext
      · change (pullback.lift (a ≫ trivialFst G T') b _) ≫
          trivialBaseMap (G := G) f ≫ trivialFst G T' =
            a ≫ trivialFst G T'
        rw [trivialBaseMap_fst]
        exact pullback.lift_fst _ _ _
      · change (pullback.lift (a ≫ trivialFst G T') b _) ≫
          trivialBaseMap (G := G) f ≫ trivialSnd G T' =
            a ≫ trivialSnd G T'
        calc
          (pullback.lift (a ≫ trivialFst G T') b _ ≫
              trivialBaseMap (G := G) f) ≫ trivialSnd G T' =
              (pullback.lift (a ≫ trivialFst G T') b _ ≫
                trivialSnd G T) ≫ f := by
                  rw [Category.assoc, trivialBaseMap_snd, ← Category.assoc]
          _ = b ≫ f := congrArg (fun q ↦ q ≫ f) (pullback.lift_snd _ _ _)
          _ = a ≫ trivialSnd G T' := hab.symm
    · change pullback.lift (a ≫ trivialFst G T') b _ ≫
        trivialSnd G T = b
      exact pullback.lift_snd _ _ _

/-- Formation of the equivariant map represented by a point commutes with
change of the base of a trivial bundle. -/
lemma trivialBaseMap_actionMapTo (f : T ⟶ T') (u : T' ⟶ U) :
  trivialBaseMap (G := G) f ≫ trivialActionMapTo (G := G) u =
      trivialActionMapTo (G := G) (f ≫ u) := by
  simp only [trivialActionMapTo, ModObj.comp_smul, trivialBaseMap_fst,
    trivialBaseMap_snd_assoc]

/-- Changing the base of a trivial bundle commutes with right translation,
with the translating section pulled back to the new base. -/
lemma trivialBaseMap_comp_rightTranslate (f : T ⟶ T') (m : T' ⟶ G) :
    trivialBaseMap (G := G) f ≫ trivialRightTranslate (G := G) m =
      trivialRightTranslate (G := G) (f ≫ m) ≫ trivialBaseMap (G := G) f := by
  apply trivial_hom_ext
  · simp only [Category.assoc, trivialRightTranslate_fst,
      trivialBaseMap_fst, MonObj.comp_mul, trivialBaseMap_snd_assoc]
  · calc
      (trivialBaseMap (G := G) f ≫ trivialRightTranslate (G := G) m) ≫
          trivialSnd G T' = trivialBaseMap (G := G) f ≫
            (trivialRightTranslate (G := G) m ≫ trivialSnd G T') :=
              Category.assoc _ _ _
      _ = trivialBaseMap (G := G) f ≫ trivialSnd G T' :=
            congrArg (fun q ↦ trivialBaseMap (G := G) f ≫ q)
              (trivialRightTranslate_snd (G := G) m)
      _ = trivialSnd G T ≫ f := trivialBaseMap_snd (G := G) f
      _ = (trivialRightTranslate (G := G) (f ≫ m) ≫
          trivialBaseMap (G := G) f) ≫ trivialSnd G T' := by
            rw [Category.assoc, trivialBaseMap_snd, ← Category.assoc,
              trivialRightTranslate_snd]

/-- A principal bundle admits sections on a covering sieve for the relative
etale topology.  Equivalently, every arrow in that sieve factors through the
bundle projection. -/
theorem exists_etale_trivializing_sieve (B : GlobalPrincipalBundle G T) :
    ∃ R : Sieve T, R ∈ (Scheme.etaleTopology.over S) T ∧
      ∀ {Z : Over S} (f : Z ⟶ T), R f → ∃ z : Z ⟶ B.P, z ≫ B.p = f := by
  obtain ⟨R, hR, hle⟩ :=
    Scheme.Hom.exists_etale_sieve_le_of_hasEtaleLocalSections B.p.left
      (Scheme.Hom.hasEtaleLocalSections_of_smooth' B.p.left)
  refine ⟨(Sieve.overEquiv T).symm R,
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _ hR, ?_⟩
  intro Z f hf
  have hf' : R f.left := (Sieve.overEquiv_symm_iff R f).mp hf
  obtain ⟨W, z, p, hp, hfac⟩ := hle f.left hf'
  cases hp
  let zOver : Z ⟶ B.P := Over.homMk z (by
    rw [← Over.w B.p, ← Category.assoc, hfac, Over.w f])
  refine ⟨zOver, ?_⟩
  ext
  exact hfac

end GlobalPrincipalBundle

namespace ActionQuotientHom

variable {G U} {Z : Over S}

/-- A point of the total space of a quotient-stack object's principal bundle
gives a cartesian arrow from the corresponding trivial-torsor object. -/
noncomputable def trivializationAtPoint (x : ActionQuotientObj G U)
    (z : Z ⟶ x.carrier.bundle.P) :
    ActionQuotientHom G U
      (ActionQuotientObj.trivial (G := G) (z ≫ x.map)) x where
  carrier :=
    { base := z ≫ x.carrier.bundle.p
      total := GlobalPrincipalBundle.trivialActionMapTo (G := G) z
      isPullback := by
        change IsPullback
          (GlobalPrincipalBundle.trivialActionMapTo (G := G) z)
          (GlobalPrincipalBundle.trivialSnd G Z)
          x.carrier.bundle.p (z ≫ x.carrier.bundle.p)
        let B := x.carrier.bundle
        have hleft : IsPullback
            (GlobalPrincipalBundle.pointPullbackTotal B z)
            (GlobalPrincipalBundle.trivialSnd G Z)
            (pullback.snd B.p (z ≫ B.p)) (𝟙 Z) := by
          apply IsPullback.of_horiz_isIso
          constructor
          simpa using GlobalPrincipalBundle.pointPullbackTotal_snd B z
        have hright : IsPullback (pullback.fst B.p (z ≫ B.p))
            (pullback.snd B.p (z ≫ B.p)) B.p (z ≫ B.p) :=
          IsPullback.of_hasPullback B.p (z ≫ B.p)
        simpa only [GlobalPrincipalBundle.pointPullbackTotal_fst,
          Category.id_comp] using hleft.paste_horiz hright
      equivariant :=
        GlobalPrincipalBundle.trivialActionMapTo_equivariant (G := G) z }
  map_naturality := by
    change GlobalPrincipalBundle.trivialActionMapTo (G := G) z ≫ x.map =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) (z ≫ x.map)
    letI : IsModHom G x.map := x.equivariant
    exact GlobalPrincipalBundle.trivialActionMapTo_comp z x.map

end ActionQuotientHom

/-- The trivial-principal-bundle quotient prestack associated to an action of
`G` on `U`. -/
noncomputable abbrev trivialActionQuotientPrestack : BasedCategory (Over S) :=
  (CategoryTheory.representablePresheafAction G U).quotientPrestack

namespace TrivialActionQuotient

variable {G U}

/-- The represented presheaf action, abbreviated inside the trivial-quotient
comparison API. -/
noncomputable abbrev action := CategoryTheory.representablePresheafAction G U

/-- A point of the represented presheaf, viewed as a morphism to `U`. -/
abbrev point (x : (action (G := G) (U := U)).QuotientObj) : x.base ⟶ U :=
  x.point

/-- The gauge section of a quotient-prestack arrow, viewed as a morphism to
the internal group object. -/
abbrev gauge {x y : (action (G := G) (U := U)).QuotientObj}
    (q : (action (G := G) (U := U)).QuotientHom x y) : x.base ⟶ G :=
  q.gauge

/-- The relation defining a represented quotient-prestack arrow, in internal
action notation. -/
lemma relation {x y : (action (G := G) (U := U)).QuotientObj}
    (q : (action (G := G) (U := U)).QuotientHom x y) :
    q.base ≫ point y = gauge q • point x := by
  exact q.relation

@[simp]
lemma gauge_comp {x y z : (action (G := G) (U := U)).QuotientObj}
    (f : x ⟶ y) (g : y ⟶ z) :
    gauge (f ≫ g) =
      (f.base ≫ gauge g) * gauge f := rfl

/-- A representable point determines the corresponding object with trivial
principal bundle in the principal-bundle quotient prestack. -/
noncomputable abbrev obj (x : (action (G := G) (U := U)).QuotientObj) :
    ActionQuotientObj G U :=
  ActionQuotientObj.trivial (G := G) (point x)

/-- A gauge arrow between representable points induces the cartesian arrow
between their trivial principal bundles.  The inverse appears because the
book's quotient-prestack relation pulls `u` back along `f`, whereas right translation
by `r` carries the object `r · u` to the object `u`. -/
noncomputable def hom {x y : (action (G := G) (U := U)).QuotientObj}
    (q : (action (G := G) (U := U)).QuotientHom x y) :
    ActionQuotientHom G U (obj x) (obj y) where
  carrier :=
    { base := q.base
      total := GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹ ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) q.base
      isPullback := by
        change IsPullback
          (GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹ ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) q.base)
          (GlobalPrincipalBundle.trivialSnd G x.base)
          (GlobalPrincipalBundle.trivialSnd G y.base) q.base
        have htranslate : IsPullback
            (GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹)
            (GlobalPrincipalBundle.trivialSnd G x.base)
            (GlobalPrincipalBundle.trivialSnd G x.base) (𝟙 x.base) := by
          apply IsPullback.of_horiz_isIso
          constructor
          simpa using GlobalPrincipalBundle.trivialRightTranslate_snd
            (G := G) (gauge q)⁻¹
        have hbase := GlobalPrincipalBundle.trivialBaseMap_isPullback
          (G := G) q.base
        simpa only [Category.id_comp] using htranslate.paste_horiz hbase
      equivariant := by
        letI : IsModHom G
            (GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹) :=
          GlobalPrincipalBundle.trivialRightTranslate_equivariant (G := G) (gauge q)⁻¹
        letI : IsModHom G
            (GlobalPrincipalBundle.trivialBaseMap (G := G) q.base) :=
          GlobalPrincipalBundle.trivialBaseMap_equivariant (G := G) q.base
        infer_instance }
  map_naturality := by
    change (GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹ ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) q.base) ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) (point y) =
        GlobalPrincipalBundle.trivialActionMapTo (G := G) (point x)
    rw [Category.assoc, GlobalPrincipalBundle.trivialBaseMap_actionMapTo,
      GlobalPrincipalBundle.trivialRightTranslate_actionMap]
    congr 1
    rw [relation q, inv_smul_smul]

@[simp]
lemma hom_carrier_base {x y : (action (G := G) (U := U)).QuotientObj}
    (q : (action (G := G) (U := U)).QuotientHom x y) :
    (hom q).carrier.base = q.base := by simp [hom]

@[simp]
lemma hom_carrier_total {x y : (action (G := G) (U := U)).QuotientObj}
    (q : (action (G := G) (U := U)).QuotientHom x y) :
    (hom q).carrier.total =
      GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge q)⁻¹ ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) q.base := by simp [hom]

/-- The functor from the quotient prestack of representable points to the
principal-bundle quotient prestack, sending every point to its trivial torsor. -/
noncomputable def functor : (action (G := G) (U := U)).QuotientObj ⥤
    ActionQuotientObj G U where
  obj := obj
  map := hom
  map_id x := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change GlobalPrincipalBundle.trivialRightTranslate (G := G) (1⁻¹) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) (𝟙 x.base) = 𝟙 _
      rw [inv_one, GlobalPrincipalBundle.trivialRightTranslate_one,
        GlobalPrincipalBundle.trivialBaseMap_id, Category.id_comp]
  map_comp {x y z} f g := by
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change (hom (f ≫ g)).carrier.total =
        (hom f).carrier.total ≫ (hom g).carrier.total
      rw [hom_carrier_total, hom_carrier_total, hom_carrier_total, gauge_comp]
      slice_rhs 2 3 =>
        rw [GlobalPrincipalBundle.trivialBaseMap_comp_rightTranslate]
      slice_rhs 1 2 => rw [GlobalPrincipalBundle.trivialRightTranslate_comp]
      slice_rhs 2 3 => rw [GlobalPrincipalBundle.trivialBaseMap_comp]
      congr 2
      change ((f.base ≫ gauge g) * gauge f)⁻¹ =
        (gauge f)⁻¹ * (f.base ≫ (gauge g)⁻¹)
      rw [mul_inv_rev, GrpObj.comp_inv]

/-- The inclusion of the trivial-bundle quotient is a functor over `Scheme/S`. -/
noncomputable def inclusion : trivialActionQuotientPrestack G U ⥤ᵇ
    actionQuotientPrestack G U where
  toFunctor := functor
  w := rfl

/-- The base map of an arrow between two objects in the image of the trivial
torsor inclusion. -/
abbrev imageBase {x y : (action (G := G) (U := U)).QuotientObj}
    (q : obj x ⟶ obj y) : x.base ⟶ y.base :=
  q.carrier.base

/-- The total-space map of an arrow between two objects in the image of the
trivial torsor inclusion. -/
abbrev imageTotal {x y : (action (G := G) (U := U)).QuotientObj}
    (q : obj x ⟶ obj y) :
    (GlobalPrincipalBundle.trivial G x.base).P ⟶
      (GlobalPrincipalBundle.trivial G y.base).P :=
  q.carrier.total

/-- The trivial-torsor inclusion is faithful. -/
noncomputable instance functor_faithful : (functor (G := G) (U := U)).Faithful where
  map_injective {x y} f g h := by
    have hcarrier : (hom f).carrier = (hom g).carrier :=
      congrArg ActionQuotientHom.carrier h
    have hbase : f.base = g.base := by
      exact congrArg ClassifyingHom.base hcarrier
    have htotal : (hom f).carrier.total = (hom g).carrier.total :=
      congrArg ClassifyingHom.total hcarrier
    apply CategoryTheory.PresheafAction.QuotientHom.ext
    · exact hbase
    · have hfst := congrArg
          (fun q ↦ q ≫ GlobalPrincipalBundle.trivialFst G y.base) htotal
      rw [hom_carrier_total, hom_carrier_total] at hfst
      simp only [Category.assoc, GlobalPrincipalBundle.trivialBaseMap_fst] at hfst
      have htranslate :
          GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge f)⁻¹ =
            GlobalPrincipalBundle.trivialRightTranslate (G := G) (gauge g)⁻¹ := by
        apply GlobalPrincipalBundle.trivial_hom_ext
        · exact hfst
        · simp
      have hinv : (gauge f)⁻¹ = (gauge g)⁻¹ :=
        GlobalPrincipalBundle.trivialRightTranslate_injective htranslate
      exact inv_injective hinv

/-- The trivial-torsor inclusion is full: every cartesian equivariant map
between trivial torsors is uniquely a gauge arrow. -/
noncomputable instance functor_full : (functor (G := G) (U := U)).Full where
  map_surjective {x y} q := by
    let unitSection := GlobalPrincipalBundle.trivialSection (G := G) (T := x.base)
    let r : x.base ⟶ G :=
      (unitSection ≫ imageTotal q) ≫ GlobalPrincipalBundle.trivialFst G y.base
    have hsquare : imageTotal q ≫ GlobalPrincipalBundle.trivialSnd G y.base =
        GlobalPrincipalBundle.trivialSnd G x.base ≫ imageBase q := by
      exact q.carrier.isPullback.w
    have hsnd : (unitSection ≫ imageTotal q) ≫
        GlobalPrincipalBundle.trivialSnd G y.base = imageBase q := by
      calc
        (unitSection ≫ imageTotal q) ≫
            GlobalPrincipalBundle.trivialSnd G y.base =
            unitSection ≫ (imageTotal q ≫
              GlobalPrincipalBundle.trivialSnd G y.base) := Category.assoc _ _ _
        _ = unitSection ≫
            (GlobalPrincipalBundle.trivialSnd G x.base ≫ imageBase q) :=
              congrArg (fun a ↦ unitSection ≫ a) hsquare
        _ = (unitSection ≫ GlobalPrincipalBundle.trivialSnd G x.base) ≫
            imageBase q := (Category.assoc _ _ _).symm
        _ = 𝟙 x.base ≫ imageBase q :=
              congrArg (fun a ↦ a ≫ imageBase q)
                (GlobalPrincipalBundle.trivialSection_snd (G := G) (T := x.base))
        _ = imageBase q := Category.id_comp _
    have hnat : imageTotal q ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) (point y) =
        GlobalPrincipalBundle.trivialActionMapTo (G := G) (point x) := by
      exact q.map_naturality
    have hnatSection := congrArg (fun a ↦ unitSection ≫ a) hnat
    have hnatSection' : (unitSection ≫ imageTotal q) ≫
          GlobalPrincipalBundle.trivialActionMapTo (G := G) (point y) =
        unitSection ≫ GlobalPrincipalBundle.trivialActionMapTo (G := G) (point x) := by
      simpa only [Category.assoc] using hnatSection
    rw [GlobalPrincipalBundle.trivialSection_actionMapTo] at hnatSection'
    rw [GlobalPrincipalBundle.trivialActionMapTo, ModObj.comp_smul] at hnatSection'
    have hact : r • (imageBase q ≫ point y) = point x := by
      change r •
        (((unitSection ≫ imageTotal q) ≫
          GlobalPrincipalBundle.trivialSnd G y.base) ≫ point y) = point x at hnatSection'
      rw [hsnd] at hnatSection'
      exact hnatSection'
    have hrelation : imageBase q ≫ point y = r⁻¹ • point x := by
      calc
        imageBase q ≫ point y = r⁻¹ •
            (r • (imageBase q ≫ point y)) :=
              (inv_smul_smul r (imageBase q ≫ point y)).symm
        _ = r⁻¹ • point x := congrArg (fun a ↦ r⁻¹ • a) hact
    let preimage : x ⟶ y :=
      { base := imageBase q
        gauge := r⁻¹
        relation := hrelation }
    let candidate : (GlobalPrincipalBundle.trivial G x.base).P ⟶
        (GlobalPrincipalBundle.trivial G y.base).P :=
      GlobalPrincipalBundle.trivialRightTranslate (G := G) r ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) (imageBase q)
    have candidate_equivariant : IsModHom G candidate := by
      letI : IsModHom G
          (GlobalPrincipalBundle.trivialRightTranslate (G := G) r) :=
        GlobalPrincipalBundle.trivialRightTranslate_equivariant (G := G) r
      letI : IsModHom G
          (GlobalPrincipalBundle.trivialBaseMap (G := G) (imageBase q)) :=
        GlobalPrincipalBundle.trivialBaseMap_equivariant (G := G) (imageBase q)
      infer_instance
    have hsection : unitSection ≫ candidate = unitSection ≫ imageTotal q := by
      apply GlobalPrincipalBundle.trivial_hom_ext
      · dsimp only [candidate, r, unitSection]
        simp only [Category.assoc, GlobalPrincipalBundle.trivialBaseMap_fst,
          GlobalPrincipalBundle.trivialRightTranslate_fst, MonObj.comp_mul,
          GlobalPrincipalBundle.trivialSection_fst,
          GlobalPrincipalBundle.trivialSection_snd_assoc]
        change (1 : x.base ⟶ G) *
          (GlobalPrincipalBundle.trivialSection (G := G) (T := x.base) ≫
            imageTotal q ≫ GlobalPrincipalBundle.trivialFst G y.base) = _
        exact _root_.one_mul _
      · dsimp only [candidate, unitSection]
        simp only [Category.assoc, GlobalPrincipalBundle.trivialBaseMap_snd,
          GlobalPrincipalBundle.trivialRightTranslate_snd_assoc]
        rw [GlobalPrincipalBundle.trivialSection_snd_assoc]
        exact hsnd.symm
    have hcandidate : candidate = imageTotal q := by
      letI : IsModHom G candidate := candidate_equivariant
      letI : IsModHom G (imageTotal q) := q.carrier.equivariant
      calc
        candidate = GlobalPrincipalBundle.trivialActionMapTo (G := G)
            (unitSection ≫ candidate) :=
              (GlobalPrincipalBundle.trivialActionMapTo_section_comp candidate).symm
        _ = GlobalPrincipalBundle.trivialActionMapTo (G := G)
            (unitSection ≫ imageTotal q) := congrArg
              (GlobalPrincipalBundle.trivialActionMapTo (G := G)) hsection
        _ = imageTotal q :=
              GlobalPrincipalBundle.trivialActionMapTo_section_comp (imageTotal q)
    refine ⟨preimage, ?_⟩
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change GlobalPrincipalBundle.trivialRightTranslate (G := G) (r⁻¹)⁻¹ ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) (imageBase q) = imageTotal q
      rw [inv_inv]
      exact hcandidate

/-- Every object of the principal-bundle quotient is etale-locally in the
image of the trivial-torsor quotient. -/
theorem inclusion_locallyEssentiallySurjective_etale :
    CategoryTheory.BasedFunctor.IsLocallyEssentiallySurjective
      (J := Scheme.etaleTopology.over S) (inclusion (G := G) (U := U)) := by
  intro x
  obtain ⟨R, hR, hfactor⟩ :=
    GlobalPrincipalBundle.exists_etale_trivializing_sieve x.carrier.bundle
  refine ⟨R, hR, ?_⟩
  intro Z f hf
  obtain ⟨z, hz⟩ := hfactor f hf
  let source : (action (G := G) (U := U)).QuotientObj :=
    { base := Z
      point := z ≫ x.map }
  let q : ActionQuotientHom G U (obj source) x :=
    ActionQuotientHom.trivializationAtPoint x z
  refine ⟨source, q, ?_⟩
  rw [← hz]
  exact Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p) q

/-- Once the principal-bundle quotient is known to be an etale stack, the
trivial-torsor inclusion satisfies the local-equivalence characterization of its
stackification. -/
theorem inclusion_isLocalStackification_etale
    (hstack : CategoryTheory.BasedCategory.IsStack
      (Scheme.etaleTopology.over S) (actionQuotientPrestack G U)) :
    CategoryTheory.BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology.over S) (inclusion (G := G) (U := U)) := by
  exact
    { isStack := hstack
      full := by
        change (functor (G := G) (U := U)).Full
        infer_instance
      faithful := by
        change (functor (G := G) (U := U)).Faithful
        infer_instance
      locallyEssentiallySurjective :=
        inclusion_locallyEssentiallySurjective_etale (G := G) (U := U) }

end TrivialActionQuotient

end AlgebraicGeometry.Scheme
