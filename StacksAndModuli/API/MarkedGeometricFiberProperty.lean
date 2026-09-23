module

public import StacksAndModuli.API.GeometricFiberProperty
public import StacksAndModuli.API.NMarkedCartesianFamily
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Geometric-fibre properties of marked cartesian families

This file combines indexed marked families with predicates on geometric fibres.  A
`MarkedGeometricFiberPredicate I` sees an algebraically closed field, a scheme over its
spectrum, and `I` bundled sections of that scheme.  The object property
`markedGeometricallyOver Q` requires `Q` on every pullback presentation of every geometric
fibre of a marked family.

The definition uses arbitrary pullback presentations.  Consequently it is stable under
pulling back marked families without assuming that `Q` is invariant under isomorphisms.
Isomorphism invariance is needed only for the convenient test using Mathlib's chosen
pullbacks.

The final part packages any pullback-stable object property as a full sub-prestack of the
prestack of marked cartesian families.

## Main declarations

* `AlgebraicGeometry.MarkedGeometricFiberPredicate`;
* `AlgebraicGeometry.MarkedGeometricFiberPredicate.ofUnmarked`;
* `CategoryTheory.MarkedCartesianObj.geometricFiberSection`;
* `AlgebraicGeometry.markedGeometricallyOver`;
* `CategoryTheory.MarkedCartesianObjectProperty.IsStableUnderPullback`;
* `CategoryTheory.markedCartesianProperty.fullSubprestack`;
* `AlgebraicGeometry.markedGeometricSubprestack`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CommRingCat

universe w v u

namespace CategoryTheory

namespace MarkedCartesianObj

variable {I : Type w} {P : MorphismProperty AlgebraicGeometry.Scheme.{u}}

/-- The raw marking induced on an arbitrary pullback fibre of a marked family. -/
noncomputable def geometricFiberMark (a : MarkedCartesianObj I P) {K : Type u} [Field K]
    [IsAlgClosed K] (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    AlgebraicGeometry.Spec (.of K) ⟶ Z :=
  h.lift (y ≫ a.mark i) (𝟙 _) (by
    rw [Category.assoc, a.mark_fac i, Category.comp_id, Category.id_comp])

/-- The induced raw marking has the prescribed map to the total space. -/
@[reassoc]
lemma geometricFiberMark_fst (a : MarkedCartesianObj I P) {K : Type u} [Field K]
    [IsAlgClosed K] (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    a.geometricFiberMark y fst h i ≫ fst = y ≫ a.mark i :=
  h.lift_fst _ _ _

/-- The induced raw marking is a section of the fibre's structure morphism. -/
@[reassoc]
lemma geometricFiberMark_fac (a : MarkedCartesianObj I P) {K : Type u} [Field K]
    [IsAlgClosed K] (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    a.geometricFiberMark y fst h i ≫ (Z ↘ AlgebraicGeometry.Spec (.of K)) = 𝟙 _ :=
  h.lift_snd _ _ _

/-- The marking induced on an arbitrary pullback fibre, bundled as a morphism over
`Spec K`.  This is the form expected by predicates on marked schemes over a field. -/
noncomputable def geometricFiberSection (a : MarkedCartesianObj I P) {K : Type u} [Field K]
    [IsAlgClosed K] (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    Over.mk (𝟙 (AlgebraicGeometry.Spec (.of K))) ⟶
      Z.asOver (AlgebraicGeometry.Spec (.of K)) :=
  Over.homMk (a.geometricFiberMark y fst h i) (a.geometricFiberMark_fac y fst h i)

@[simp]
lemma geometricFiberSection_left (a : MarkedCartesianObj I P) {K : Type u} [Field K]
    [IsAlgClosed K] (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    (a.geometricFiberSection y fst h i).left = a.geometricFiberMark y fst h i :=
  rfl

/-- The marking on Mathlib's chosen pullback fibre, bundled over `Spec K`. -/
noncomputable def pullbackGeometricFiberSection (a : MarkedCartesianObj I P)
    (K : Type u) [Field K] [IsAlgClosed K]
    (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right) (i : I) :
    Over.mk (𝟙 (AlgebraicGeometry.Spec (.of K))) ⟶
      Over.mk (pullback.snd a.hom y) :=
  @geometricFiberSection I P a K _ _ y (pullback a.hom y)
    ⟨pullback.snd a.hom y⟩ (pullback.fst a.hom y) (by
      change IsPullback (pullback.fst a.hom y) (pullback.snd a.hom y) a.hom y
      exact .of_hasPullback a.hom y) i

/-- The chosen pullback-fibre marking has the prescribed projection to the total
space. -/
@[reassoc]
lemma pullbackGeometricFiberSection_fst (a : MarkedCartesianObj I P)
    (K : Type u) [Field K] [IsAlgClosed K]
    (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right) (i : I) :
    (a.pullbackGeometricFiberSection K y i).left ≫ pullback.fst a.hom y =
      y ≫ a.mark i := by
  unfold pullbackGeometricFiberSection
  exact geometricFiberMark_fst _ _ _ _ _

/-- Passing a marked family through a cartesian morphism does not change the sections
induced on a fibre. -/
lemma geometricFiberSection_naturality {a b : MarkedCartesianObj I P} (φ : a ⟶ b)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    b.geometricFiberSection (y ≫ φ.right) (fst ≫ φ.left)
      (h.paste_horiz φ.isPullback) i = a.geometricFiberSection y fst h i := by
  apply CostructuredArrow.hom_ext
  change b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
      (h.paste_horiz φ.isPullback) i = a.geometricFiberMark y fst h i
  apply h.hom_ext
  · apply φ.isPullback.hom_ext
    · calc
        (b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
            (h.paste_horiz φ.isPullback) i ≫ fst) ≫ φ.left =
            b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
              (h.paste_horiz φ.isPullback) i ≫ (fst ≫ φ.left) :=
          Category.assoc _ _ _
        _ = (y ≫ φ.right) ≫ b.mark i :=
          b.geometricFiberMark_fst _ _ _ _
        _ = y ≫ (φ.right ≫ b.mark i) := Category.assoc _ _ _
        _ = y ≫ (a.mark i ≫ φ.left) := by rw [φ.mark_naturality i]
        _ = (y ≫ a.mark i) ≫ φ.left := (Category.assoc _ _ _).symm
        _ = (a.geometricFiberMark y fst h i ≫ fst) ≫ φ.left :=
          congrArg (fun q ↦ q ≫ φ.left) (a.geometricFiberMark_fst y fst h i).symm
    · calc
        (b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
            (h.paste_horiz φ.isPullback) i ≫ fst) ≫ a.hom =
            b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
              (h.paste_horiz φ.isPullback) i ≫ (fst ≫ a.hom) :=
          Category.assoc _ _ _
        _ = b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
              (h.paste_horiz φ.isPullback) i ≫
                ((Z ↘ AlgebraicGeometry.Spec (.of K)) ≫ y) := by rw [h.w]
        _ = (b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
              (h.paste_horiz φ.isPullback) i ≫
                (Z ↘ AlgebraicGeometry.Spec (.of K))) ≫ y :=
          (Category.assoc _ _ _).symm
        _ = y := by rw [b.geometricFiberMark_fac, Category.id_comp]
        _ = y ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = y ≫ (a.mark i ≫ a.hom) := by rw [a.mark_fac i]
        _ = (y ≫ a.mark i) ≫ a.hom := (Category.assoc _ _ _).symm
        _ = (a.geometricFiberMark y fst h i ≫ fst) ≫ a.hom :=
          congrArg (fun q ↦ q ≫ a.hom) (a.geometricFiberMark_fst y fst h i).symm
  · calc
      b.geometricFiberMark (y ≫ φ.right) (fst ≫ φ.left)
          (h.paste_horiz φ.isPullback) i ≫
          (Z ↘ AlgebraicGeometry.Spec (.of K)) = 𝟙 _ :=
        b.geometricFiberMark_fac _ _ _ _
      _ = a.geometricFiberMark y fst h i ≫
          (Z ↘ AlgebraicGeometry.Spec (.of K)) :=
        (a.geometricFiberMark_fac _ _ _ _).symm

/-- The chosen pullback section transported along the canonical comparison with an
arbitrary pullback presentation is the section induced directly on that presentation. -/
lemma pullbackGeometricFiberSection_comp_isoPullback (a : MarkedCartesianObj I P)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : AlgebraicGeometry.Spec (.of K) ⟶ a.right)
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (.of K))]
    (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ AlgebraicGeometry.Spec (.of K)) a.hom y) (i : I) :
    a.pullbackGeometricFiberSection K y i ≫
        (Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd).hom =
      a.geometricFiberSection y fst h i := by
  apply CostructuredArrow.hom_ext
  apply h.hom_ext
  · change ((a.pullbackGeometricFiberSection K y i).left ≫ h.isoPullback.inv) ≫ fst =
      (a.geometricFiberSection y fst h i).left ≫ fst
    rw [Category.assoc, h.isoPullback_inv_fst,
      a.pullbackGeometricFiberSection_fst]
    change y ≫ a.mark i = a.geometricFiberMark y fst h i ≫ fst
    exact (a.geometricFiberMark_fst y fst h i).symm
  · change ((a.pullbackGeometricFiberSection K y i).left ≫ h.isoPullback.inv) ≫
        (Z ↘ AlgebraicGeometry.Spec (.of K)) =
      a.geometricFiberMark y fst h i ≫ (Z ↘ AlgebraicGeometry.Spec (.of K))
    rw [Category.assoc, h.isoPullback_inv_snd]
    exact (Over.w (a.pullbackGeometricFiberSection K y i)).trans
      (a.geometricFiberMark_fac y fst h i).symm

end MarkedCartesianObj

namespace MarkedCartesianObjectProperty

variable {C : Type u} [Category.{v} C] {I : Type w} {P : MorphismProperty C}

/-- An object property of marked cartesian families is stable under pullback when it
passes from the target to the source of every cartesian morphism of marked families. -/
class IsStableUnderPullback (Q : ObjectProperty (MarkedCartesianObj I P)) : Prop where
  of_hom {a b : MarkedCartesianObj I P} (φ : a ⟶ b) : Q b → Q a

/-- Pull a stable object property back along a morphism of marked families. -/
lemma prop_of_hom (Q : ObjectProperty (MarkedCartesianObj I P))
    [IsStableUnderPullback Q] {a b : MarkedCartesianObj I P} (φ : a ⟶ b)
    (hb : Q b) : Q a :=
  IsStableUnderPullback.of_hom φ hb

/-- A pullback-stable object property of marked families is invariant under
isomorphisms. -/
instance stable_isClosedUnderIsomorphisms
    (Q : ObjectProperty (MarkedCartesianObj I P)) [IsStableUnderPullback Q] :
    ObjectProperty.IsClosedUnderIsomorphisms Q where
  of_iso e ha := prop_of_hom Q e.inv ha

end MarkedCartesianObjectProperty

namespace markedCartesianProperty

variable {C : Type u} [Category.{v} C] (I : Type w) (P : MorphismProperty C)

/-- The full based subcategory of marked families satisfying an object property. -/
def fullSubprestack (Q : ObjectProperty (MarkedCartesianObj I P)) : BasedCategory C where
  obj := Q.FullSubcategory
  p := Q.ι ⋙ (markedCartesianProperty I P).p

/-- The inclusion of a full subcategory of marked families. -/
def fullSubprestackι (Q : ObjectProperty (MarkedCartesianObj I P)) :
    BasedFunctor (fullSubprestack I P Q) (markedCartesianProperty I P) where
  toFunctor := Q.ι
  w := rfl

instance fullSubprestackι_full (Q : ObjectProperty (MarkedCartesianObj I P)) :
    (fullSubprestackι I P Q).toFunctor.Full :=
  inferInstanceAs Q.ι.Full

instance fullSubprestackι_faithful (Q : ObjectProperty (MarkedCartesianObj I P)) :
    (fullSubprestackι I P Q).toFunctor.Faithful :=
  inferInstanceAs Q.ι.Faithful

@[simp]
lemma fullSubprestackι_obj (Q : ObjectProperty (MarkedCartesianObj I P))
    (a : (fullSubprestack I P Q).obj) :
    (fullSubprestackι I P Q).obj a = a.obj :=
  rfl

/-- A pullback-stable full subcategory of pullback-stable marked families is itself a
prestack. -/
instance fullSubprestack_isFiberedInGroupoids [HasPullbacks C]
    [P.IsStableUnderBaseChange] (Q : ObjectProperty (MarkedCartesianObj I P))
    [MarkedCartesianObjectProperty.IsStableUnderPullback Q] :
    (fullSubprestack I P Q).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    change Q.FullSubcategory at a
    change R ⟶ a.obj.right at f
    let pb : IsPullback (pullback.fst a.obj.hom f) (pullback.snd a.obj.hom f)
        a.obj.hom f := IsPullback.of_hasPullback a.obj.hom f
    let bMark (i : I) : R ⟶ pullback a.obj.hom f :=
      pullback.lift (f ≫ a.obj.mark i) (𝟙 R) (by
        rw [Category.assoc, a.obj.mark_fac i, Category.comp_id, Category.id_comp])
    have hbMark (i : I) : bMark i ≫ pullback.snd a.obj.hom f = 𝟙 R :=
      pullback.lift_snd _ _ _
    have hbProperty : P (pullback.snd a.obj.hom f) :=
      P.of_isPullback pb a.obj.property
    let b₀ : MarkedCartesianObj I P :=
      { left := pullback a.obj.hom f
        right := R
        hom := pullback.snd a.obj.hom f
        property := hbProperty
        mark := bMark
        mark_fac := hbMark }
    let φ₀ : b₀ ⟶ a.obj :=
      { left := pullback.fst a.obj.hom f
        right := f
        isPullback := pb
        mark_naturality := fun _ ↦ pullback.lift_fst _ _ _ }
    have hb₀ : Q b₀ := MarkedCartesianObjectProperty.prop_of_hom Q φ₀ a.property
    let b : Q.FullSubcategory := ⟨b₀, hb₀⟩
    let φ : b ⟶ a := ObjectProperty.homMk φ₀
    refine ⟨b, φ, ?_⟩
    change IsHomLift (Q.ι ⋙ (markedCartesianProperty I P).p) f φ
    have hf : f = (Q.ι ⋙ (markedCartesianProperty I P).p).map φ := rfl
    rw [hf]
    infer_instance
  · intro a b φ
    let φ₀ : a.obj ⟶ b.obj := φ.hom
    let _ : IsHomLift (markedCartesianProperty I P).p φ₀.right φ₀ := by
      change IsHomLift (markedCartesianProperty I P).p
        ((markedCartesianProperty I P).p.map φ₀) φ₀
      exact Functor.IsHomLift.map (p := (markedCartesianProperty I P).p) φ₀
    let _ : IsStronglyCartesian (markedCartesianProperty I P).p φ₀.right φ₀ :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
    constructor
    intro c g ψ hψ
    let _ : IsHomLift (Q.ι ⋙ (markedCartesianProperty I P).p)
        (g ≫ (Q.ι ⋙ (markedCartesianProperty I P).p).map φ) ψ := hψ
    let ψ₀ : c.obj ⟶ b.obj := ψ.hom
    have hgfac : g ≫ φ₀.right = ψ₀.right := by
      have hbase := IsHomLift.eq_of_isHomLift
        (Q.ι ⋙ (markedCartesianProperty I P).p)
        (g ≫ (Q.ι ⋙ (markedCartesianProperty I P).p).map φ) ψ
      exact hbase
    let _ : IsHomLift (markedCartesianProperty I P).p (g ≫ φ₀.right) ψ₀ := by
      rw [hgfac]
      change IsHomLift (markedCartesianProperty I P).p
        ((markedCartesianProperty I P).p.map ψ₀) ψ₀
      exact Functor.IsHomLift.map (p := (markedCartesianProperty I P).p) ψ₀
    obtain ⟨χ₀, hχ₀, huniq⟩ :=
      IsStronglyCartesian.universal_property' (p := (markedCartesianProperty I P).p)
        (f := φ₀.right) (φ := φ₀) g ψ₀
    let χ : c ⟶ a := ObjectProperty.homMk χ₀
    let _ : IsHomLift (markedCartesianProperty I P).p g χ₀ := hχ₀.1
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · change IsHomLift (Q.ι ⋙ (markedCartesianProperty I P).p) g χ
      have hg : g = (Q.ι ⋙ (markedCartesianProperty I P).p).map χ :=
        IsHomLift.eq_of_isHomLift (markedCartesianProperty I P).p g χ₀
      rw [hg]
      infer_instance
    · apply ObjectProperty.hom_ext
      exact hχ₀.2
    · intro χ' hχ'
      apply ObjectProperty.hom_ext
      apply huniq χ'.hom
      refine ⟨?_, ?_⟩
      · have h := hχ'.1
        change IsHomLift (Q.ι ⋙ (markedCartesianProperty I P).p) g χ' at h
        have hg : g = (Q.ι ⋙ (markedCartesianProperty I P).p).map χ' :=
          @IsHomLift.eq_of_isHomLift _ _ _ _
            (Q.ι ⋙ (markedCartesianProperty I P).p) _ _ g χ' h
        apply IsHomLift.of_fac (markedCartesianProperty I P).p g χ'.hom rfl rfl
        simpa using hg
      · exact congrArg InducedCategory.Hom.hom hχ'.2

end markedCartesianProperty

end CategoryTheory

namespace AlgebraicGeometry

/-- A predicate on a scheme over an algebraically closed field equipped with an indexed
collection of bundled sections. -/
abbrev MarkedGeometricFiberPredicate (I : Type w) :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (Z : Scheme.{u})
    [Z.Over (Spec (.of K))],
      (I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Z.asOver (Spec (.of K)))) → Prop

namespace MarkedGeometricFiberPredicate

/-- Regard an unmarked geometric-fibre predicate as a marked predicate which ignores
the marking family. -/
def ofUnmarked (I : Type w) (P : GeometricFiberPredicate.{u}) :
    MarkedGeometricFiberPredicate.{w, u} I :=
  fun K _ _ Z _ _ ↦ P K Z

/-- Evaluating an unmarked predicate regarded as a marked predicate simply forgets the
markings. -/
@[simp]
lemma ofUnmarked_apply (I : Type w) (P : GeometricFiberPredicate.{u})
    (K : Type u) [Field K] [IsAlgClosed K] (Z : Scheme.{u})
    [Z.Over (Spec (.of K))]
    (p : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Z.asOver (Spec (.of K)))) :
    ofUnmarked I P K Z p ↔ P K Z :=
  Iff.rfl

/-- A marked geometric-fibre predicate is invariant under isomorphisms over the field
which carry every source marking to the corresponding target marking. -/
class IsClosedUnderIsomorphisms (Q : MarkedGeometricFiberPredicate.{w, u} I) : Prop where
  of_iso {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    {p : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ X.asOver (Spec (.of K)))}
    {q : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Y.asOver (Spec (.of K)))}
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K)))
    (hmark : ∀ i, p i ≫ e.hom = q i) : Q K X p → Q K Y q

/-- Ignoring markings preserves isomorphism invariance of a geometric-fibre
predicate. -/
instance ofUnmarked_isClosedUnderIsomorphisms
    (I : Type w) (P : GeometricFiberPredicate.{u})
    [GeometricFiberPredicate.IsClosedUnderIsomorphisms P] :
    (ofUnmarked I P).IsClosedUnderIsomorphisms where
  of_iso e _ h := P.prop_of_iso e h

/-- Transport a marked geometric-fibre predicate across an isomorphism preserving all
markings. -/
lemma prop_of_iso (Q : MarkedGeometricFiberPredicate.{w, u} I)
    [Q.IsClosedUnderIsomorphisms] {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    {p : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ X.asOver (Spec (.of K)))}
    {q : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Y.asOver (Spec (.of K)))}
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K)))
    (hmark : ∀ i, p i ≫ e.hom = q i) (hX : Q K X p) : Q K Y q :=
  IsClosedUnderIsomorphisms.of_iso e hmark hX

/-- An invariant marked geometric-fibre predicate holds on either side of an isomorphism
which identifies the markings. -/
lemma prop_iff_of_iso (Q : MarkedGeometricFiberPredicate.{w, u} I)
    [Q.IsClosedUnderIsomorphisms] {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    {p : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ X.asOver (Spec (.of K)))}
    {q : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Y.asOver (Spec (.of K)))}
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K)))
    (hmark : ∀ i, p i ≫ e.hom = q i) : Q K X p ↔ Q K Y q := by
  constructor
  · exact Q.prop_of_iso e hmark
  · refine Q.prop_of_iso e.symm ?_
    intro i
    calc
      q i ≫ e.inv = (p i ≫ e.hom) ≫ e.inv :=
        congrArg (fun r ↦ r ≫ e.inv) (hmark i).symm
      _ = p i ≫ (e.hom ≫ e.inv) := Category.assoc _ _ _
      _ = p i ≫ 𝟙 _ := by rw [e.hom_inv_id]
      _ = p i := Category.comp_id _

/-- Pointwise conjunction of marked geometric-fibre predicates. -/
def inf (Q R : MarkedGeometricFiberPredicate.{w, u} I) :
    MarkedGeometricFiberPredicate.{w, u} I :=
  fun K _ _ Z _ p ↦ Q K Z p ∧ R K Z p

@[simp]
lemma inf_apply (Q R : MarkedGeometricFiberPredicate.{w, u} I)
    (K : Type u) [Field K] [IsAlgClosed K] (Z : Scheme.{u}) [Z.Over (Spec (.of K))]
    (p : I → (Over.mk (𝟙 (Spec (.of K))) ⟶ Z.asOver (Spec (.of K)))) :
    (Q.inf R) K Z p ↔ Q K Z p ∧ R K Z p :=
  Iff.rfl

instance inf_isClosedUnderIsomorphisms (Q R : MarkedGeometricFiberPredicate.{w, u} I)
    [Q.IsClosedUnderIsomorphisms] [R.IsClosedUnderIsomorphisms] :
    (Q.inf R).IsClosedUnderIsomorphisms where
  of_iso e hmark h := ⟨Q.prop_of_iso e hmark h.1, R.prop_of_iso e hmark h.2⟩

end MarkedGeometricFiberPredicate

/-- The object property asserting that a marked family satisfies `Q` on every geometric
fibre, using every pullback presentation of that fibre. -/
def markedGeometricallyOver {I : Type w} {P : MorphismProperty Scheme.{u}}
    (Q : MarkedGeometricFiberPredicate.{w, u} I) :
    ObjectProperty (MarkedCartesianObj I P) :=
  fun a ↦ ∀ ⦃K : Type u⦄ [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ a.right) ⦃Z : Scheme.{u}⦄ [Z.Over (Spec (.of K))]
    (fst : Z ⟶ a.left) (h : IsPullback fst (Z ↘ Spec (.of K)) a.hom y),
      Q K Z (fun i ↦ a.geometricFiberSection y fst h i)

/-- Requiring two predicates on every marked geometric fibre is the conjunction of the
two associated object properties. -/
lemma markedGeometricallyOver_inf {I : Type w} {P : MorphismProperty Scheme.{u}}
    (Q R : MarkedGeometricFiberPredicate.{w, u} I) :
    markedGeometricallyOver (Q.inf R) =
      markedGeometricallyOver (P := P) Q ⊓ markedGeometricallyOver R := by
  ext a
  constructor
  · intro h
    constructor
    · intro K _ _ y Z _ fst sq
      exact (h y fst sq).1
    · intro K _ _ y Z _ fst sq
      exact (h y fst sq).2
  · rintro ⟨hQ, hR⟩ K _ _ y Z _ fst sq
    exact ⟨hQ y fst sq, hR y fst sq⟩

/-- Evaluate a marked geometric-fibre object property on an arbitrary pullback
presentation. -/
lemma of_markedGeometricallyOver {I : Type w} {P : MorphismProperty Scheme.{u}}
    {Q : MarkedGeometricFiberPredicate.{w, u} I} {a : MarkedCartesianObj I P}
    (ha : markedGeometricallyOver Q a) {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ a.right) {Z : Scheme.{u}} [Z.Over (Spec (.of K))]
    (fst : Z ⟶ a.left) (h : IsPullback fst (Z ↘ Spec (.of K)) a.hom y) :
    Q K Z (fun i ↦ a.geometricFiberSection y fst h i) :=
  ha y fst h

/-- Evaluate a marked geometric-fibre object property on Mathlib's chosen pullback. -/
lemma pullback_of_markedGeometricallyOver {I : Type w}
    {P : MorphismProperty Scheme.{u}} {Q : MarkedGeometricFiberPredicate.{w, u} I}
    {a : MarkedCartesianObj I P} (ha : markedGeometricallyOver Q a)
    (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ a.right) :
    @Q K _ _ (pullback a.hom y) ⟨pullback.snd a.hom y⟩
      (a.pullbackGeometricFiberSection K y) :=
  by
    have hpb : @IsPullback Scheme _ (pullback a.hom y) a.left (Spec (.of K)) a.right
        (pullback.fst a.hom y)
        (CategoryTheory.over (pullback a.hom y) (Spec (.of K))
          ⟨pullback.snd a.hom y⟩)
        a.hom y := by
      change IsPullback (pullback.fst a.hom y) (pullback.snd a.hom y) a.hom y
      exact .of_hasPullback a.hom y
    have hsections :
        (fun i ↦ @MarkedCartesianObj.geometricFiberSection I P a K _ _ y
          (pullback a.hom y) ⟨pullback.snd a.hom y⟩
          (pullback.fst a.hom y) hpb i) =
          a.pullbackGeometricFiberSection K y := by
      funext i
      rfl
    rw [← hsections]
    exact @ha K _ _ y (pullback a.hom y) ⟨pullback.snd a.hom y⟩
      (pullback.fst a.hom y) hpb

/-- A marked geometric-fibre predicate can be tested on Mathlib's chosen pullbacks once
it is invariant under marked isomorphisms over the field. -/
lemma markedGeometricallyOver_iff {I : Type w} {P : MorphismProperty Scheme.{u}}
    {Q : MarkedGeometricFiberPredicate.{w, u} I}
    [Q.IsClosedUnderIsomorphisms] {a : MarkedCartesianObj I P} :
    markedGeometricallyOver Q a ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (y : Spec (.of K) ⟶ a.right),
        @Q K _ _ (pullback a.hom y) ⟨pullback.snd a.hom y⟩
          (a.pullbackGeometricFiberSection K y) := by
  refine ⟨fun h K _ _ y ↦ pullback_of_markedGeometricallyOver h K y, fun H ↦ ?_⟩
  intro K _ _ y Z _ fst h
  let e : Over.mk (pullback.snd a.hom y) ≅ Z.asOver (Spec (.of K)) :=
    Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd
  exact @MarkedGeometricFiberPredicate.prop_of_iso I Q _ K _ _
    (pullback a.hom y) Z ⟨pullback.snd a.hom y⟩ inferInstance
    (a.pullbackGeometricFiberSection K y)
    (fun i ↦ a.geometricFiberSection y fst h i) e
    (fun i ↦ a.pullbackGeometricFiberSection_comp_isoPullback y fst h i) (H K y)

/-- Geometric-fibre properties of marked families are stable under pulling back the
marked family. -/
instance markedGeometricallyOver_isStableUnderPullback {I : Type w}
    {P : MorphismProperty Scheme.{u}} (Q : MarkedGeometricFiberPredicate.{w, u} I) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (markedGeometricallyOver (P := P) Q) where
  of_hom {a b} φ hb := by
    change MarkedCartesianHom a b at φ
    intro K _ _ y Z _ fst h
    let hout : IsPullback (fst ≫ φ.left) (Z ↘ Spec (.of K)) b.hom
        (y ≫ φ.right) := h.paste_horiz φ.isPullback
    have hQ := hb (y ≫ φ.right) (fst ≫ φ.left) hout
    have hsections :
        (fun i ↦ b.geometricFiberSection (y ≫ φ.right) (fst ≫ φ.left) hout i) =
          (fun i ↦ a.geometricFiberSection y fst h i) := by
      funext i
      exact MarkedCartesianObj.geometricFiberSection_naturality φ y fst h i
    rw [← hsections]
    exact hQ

/-- The full sub-prestack of marked `P`-families satisfying `Q` on every geometric
fibre. -/
abbrev markedGeometricSubprestack {I : Type w} (P : MorphismProperty Scheme.{u})
    (Q : MarkedGeometricFiberPredicate.{w, u} I) : BasedCategory Scheme.{u} :=
  markedCartesianProperty.fullSubprestack I P (markedGeometricallyOver Q)

/-- The inclusion of the marked geometric-fibre sub-prestack into all marked
`P`-families. -/
def markedGeometricSubprestackι {I : Type w} (P : MorphismProperty Scheme.{u})
    (Q : MarkedGeometricFiberPredicate.{w, u} I) :
    BasedFunctor (markedGeometricSubprestack P Q) (markedCartesianProperty I P) :=
  markedCartesianProperty.fullSubprestackι I P (markedGeometricallyOver Q)

/-- Pullback-stable marked families satisfying a geometric-fibre predicate form a
prestack. -/
instance markedGeometricSubprestack_isFiberedInGroupoids {I : Type w}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (Q : MarkedGeometricFiberPredicate.{w, u} I) :
    (markedGeometricSubprestack P Q).p.IsFiberedInGroupoids :=
  inferInstance

end AlgebraicGeometry
