module

public import StacksAndModuli.API.RelativeYonedaTotal
public import StacksAndModuli.API.RepresentableSheafProperty
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Cartesian-arrow diagrams from local representatives

Suppose that a sheaf on an over-site becomes representable over every arrow of a
covering sieve.  This file chooses those local representatives and uses the canonical
strongly cartesian comparisons with the original sheaf to assemble them into a
coherent diagram of scheme arrows.  Relative Yoneda faithfulness supplies the identity
and composition laws after the sheaf-side transitions have been constructed.

## Main definitions

- `CategoryTheory.GrothendieckTopology.localRepresentativeArrowFunctor`: the diagram
  of locally representing scheme arrows.
- `CategoryTheory.GrothendieckTopology.localRepresentativeArrowMap_isPullback`: every
  transition in that diagram induces a pullback square of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Bicategory Opposite

universe u

namespace CategoryTheory.GrothendieckTopology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (J : GrothendieckTopology AlgebraicGeometry.Scheme.{u}) [J.Subcanonical]
variable (P : MorphismProperty AlgebraicGeometry.Scheme.{u})
variable {S : AlgebraicGeometry.Scheme.{u}} (R : Sieve S)
variable (M : Sheaf (J.over S) (Type u))
variable (hM : ∀ q : R.arrows.category,
  (J.representableByProperty P).prop _
    (((J.pseudofunctorOver (Type u)).map q.obj.hom.op.toLoc).toFunctor.obj M))

/-- A chosen representative of the pullback of `M` over an arrow of the sieve. -/
noncomputable def localRepresentative (q : R.arrows.category) : Over q.obj.left :=
  (hM q).choose

/-- The chosen local representative has the requested morphism property. -/
lemma localRepresentative_property (q : R.arrows.category) :
    P (localRepresentative J P R M hM q).hom :=
  (hM q).choose_spec.1

noncomputable def localRepresentativePresheafIso
    (q : R.arrows.category) :
    CategoryTheory.yoneda.obj (localRepresentative J P R M hM q) ≅
      (((J.pseudofunctorOver (Type u)).map
        q.obj.hom.op.toLoc).toFunctor.obj M).obj :=
  (hM q).choose_spec.2.some

noncomputable def localRepresentativeSheafIso
    (q : R.arrows.category) :
    (J.over q.obj.left).yoneda.obj (localRepresentative J P R M hM q) ≅
      (J.overMapPullback (Type u) q.obj.hom).obj M :=
  (fullyFaithfulSheafToPresheaf (J.over q.obj.left) (Type u)).preimageIso
    (localRepresentativePresheafIso J P R M hM q)

abbrev SheafTotal :=
  Pseudofunctor.CoGrothendieck (J.pseudofunctorOver (Type u))

/-- The represented sheaf over a sieve arrow, regarded as an object of the total
category of sheaves on over-sites. -/
noncomputable def localSheafTotalObj (q : R.arrows.category) : SheafTotal J :=
  ⟨q.obj.left,
    (J.over q.obj.left).yoneda.obj (localRepresentative J P R M hM q)⟩

noncomputable abbrev globalSheafTotalObj : SheafTotal J := ⟨S, M⟩

noncomputable def localSheafVerticalIso (q : R.arrows.category) :
    localSheafTotalObj J P R M hM q ≅
      Pseudofunctor.CoGrothendieck.domainCartesianLift M q.obj.hom :=
  (Pseudofunctor.CoGrothendieck.ι
    (J.pseudofunctorOver (Type u)) q.obj.left).mapIso
      (localRepresentativeSheafIso J P R M hM q)

noncomputable def localSheafEpsilon (q : R.arrows.category) :
    localSheafTotalObj J P R M hM q ⟶ globalSheafTotalObj J M :=
  (localSheafVerticalIso J P R M hM q).hom ≫
    Pseudofunctor.CoGrothendieck.cartesianLift
      (F := J.pseudofunctorOver (Type u)) M q.obj.hom

instance localSheafEpsilon_fiber_isIso (q : R.arrows.category) :
    IsIso (localSheafEpsilon J P R M hM q).fiber := by
  dsimp [localSheafEpsilon, localSheafVerticalIso]
  apply IsIso.comp_isIso'
  · apply IsIso.comp_isIso'
    · infer_instance
    · change IsIso ((Cat.Hom.toNatIso
          ((J.pseudofunctorOver (Type u)).mapId
            ⟨op q.obj.left⟩)).inv.app _)
      infer_instance
  · apply IsIso.comp_isIso'
    · infer_instance
    · change IsIso ((Cat.Hom.toNatIso
          ((J.pseudofunctorOver (Type u)).mapComp
            q.obj.hom.op.toLoc (𝟙 q.obj.left).op.toLoc)).inv.app M)
      infer_instance

instance localSheafEpsilon_isHomLift (q : R.arrows.category) :
    IsHomLift
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      q.obj.hom (localSheafEpsilon J P R M hM q) := by
  letI : IsHomLift
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      (𝟙 q.obj.left) (localSheafVerticalIso J P R M hM q).hom := by
    apply IsHomLift.of_fac _ _ _ rfl rfl
    simp [localSheafVerticalIso]
  have hcomp : IsHomLift
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      (𝟙 q.obj.left ≫ q.obj.hom)
      ((localSheafVerticalIso J P R M hM q).hom ≫
        Pseudofunctor.CoGrothendieck.cartesianLift
          (F := J.pseudofunctorOver (Type u)) M q.obj.hom) := inferInstance
  simpa [localSheafEpsilon] using hcomp

instance localSheafEpsilon_isStronglyCartesian
    (q : R.arrows.category) :
    IsStronglyCartesian
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      q.obj.hom (localSheafEpsilon J P R M hM q) := by
  letI : IsHomLift
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      (𝟙 q.obj.left) (localSheafVerticalIso J P R M hM q).hom := by
    apply IsHomLift.of_fac _ _ _ rfl rfl
    simp [localSheafVerticalIso]
  haveI : IsStronglyCartesian
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      (𝟙 q.obj.left) (localSheafVerticalIso J P R M hM q).hom :=
    IsStronglyCartesian.of_iso _ _ _
  haveI : IsStronglyCartesian
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      q.obj.hom
      (Pseudofunctor.CoGrothendieck.cartesianLift
        (F := J.pseudofunctorOver (Type u)) M q.obj.hom) :=
    Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
      (F := J.pseudofunctorOver (Type u)) M q.obj.hom
  haveI hcomp : IsStronglyCartesian
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      (𝟙 q.obj.left ≫ q.obj.hom)
      ((localSheafVerticalIso J P R M hM q).hom ≫
        Pseudofunctor.CoGrothendieck.cartesianLift
          (F := J.pseudofunctorOver (Type u)) M q.obj.hom) := inferInstance
  change IsStronglyCartesian _ _
    ((localSheafVerticalIso J P R M hM q).hom ≫
      Pseudofunctor.CoGrothendieck.cartesianLift
        (F := J.pseudofunctorOver (Type u)) M q.obj.hom)
  simpa using hcomp

noncomputable def localSheafTransitionRaw
    {q r : R.arrows.category} (k : q ⟶ r) :
    localSheafTotalObj J P R M hM q ⟶ localSheafTotalObj J P R M hM r :=
  IsStronglyCartesian.map
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
    r.obj.hom (localSheafEpsilon J P R M hM r) k.hom.w.symm
    (localSheafEpsilon J P R M hM q)

instance localSheafTransitionRaw_isHomLift
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsHomLift
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      k.hom.left (localSheafTransitionRaw J P R M hM k) := by
  dsimp [localSheafTransitionRaw]
  infer_instance

lemma localSheafTransitionRaw_base
    {q r : R.arrows.category} (k : q ⟶ r) :
    (localSheafTransitionRaw J P R M hM k).base = k.hom.left := by
  have h := IsHomLift.fac'
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
    k.hom.left (localSheafTransitionRaw J P R M hM k)
  simpa using h

noncomputable def rebase {A B : SheafTotal J} (f : A ⟶ B)
    {g : A.base ⟶ B.base} (h : f.base = g) : A ⟶ B where
  base := g
  fiber := f.fiber ≫ eqToHom (by rw [← h])

lemma rebase_eq {A B : SheafTotal J} (f : A ⟶ B)
    {g : A.base ⟶ B.base} (h : f.base = g) : rebase J f h = f := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h.symm
  rfl

lemma localSheafEpsilon_base (q : R.arrows.category) :
    (localSheafEpsilon J P R M hM q).base = q.obj.hom := by
  have h := IsHomLift.fac'
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
    q.obj.hom (localSheafEpsilon J P R M hM q)
  simpa using h

noncomputable def localSheafEpsilonNormalized
    (q : R.arrows.category) :
    localSheafTotalObj J P R M hM q ⟶ globalSheafTotalObj J M :=
  rebase J (localSheafEpsilon J P R M hM q)
    (localSheafEpsilon_base J P R M hM q)

@[simp] lemma localSheafEpsilonNormalized_base
    (q : R.arrows.category) :
    (localSheafEpsilonNormalized J P R M hM q).base = q.obj.hom := rfl

lemma localSheafEpsilonNormalized_eq (q : R.arrows.category) :
    localSheafEpsilonNormalized J P R M hM q =
      localSheafEpsilon J P R M hM q :=
  rebase_eq J _ _

instance localSheafEpsilonNormalized_fiber_isIso
    (q : R.arrows.category) :
    IsIso (localSheafEpsilonNormalized J P R M hM q).fiber := by
  dsimp [localSheafEpsilonNormalized, rebase]
  apply IsIso.comp_isIso'
  · exact localSheafEpsilon_fiber_isIso J P R M hM q
  · infer_instance

/-- The sheaf-side transition between two chosen local representatives.  Its base
field is normalized to the map of sieve arrows. -/
noncomputable def localSheafTransition {q r : R.arrows.category} (k : q ⟶ r) :
    localSheafTotalObj J P R M hM q ⟶ localSheafTotalObj J P R M hM r :=
  rebase J (localSheafTransitionRaw J P R M hM k)
    (localSheafTransitionRaw_base J P R M hM k)

/-- The base of a normalized sheaf transition is the map of sieve arrows. -/
@[simp] lemma localSheafTransition_base {q r : R.arrows.category} (k : q ⟶ r) :
    (localSheafTransition J P R M hM k).base = k.hom.left := rfl

lemma localSheafTransition_eq_raw
    {q r : R.arrows.category} (k : q ⟶ r) :
    localSheafTransition J P R M hM k =
      localSheafTransitionRaw J P R M hM k :=
  rebase_eq J _ _

lemma localSheafTransition_fac
    {q r : R.arrows.category} (k : q ⟶ r) :
    localSheafTransition J P R M hM k ≫
        localSheafEpsilonNormalized J P R M hM r =
      localSheafEpsilonNormalized J P R M hM q := by
  rw [localSheafTransition_eq_raw, localSheafEpsilonNormalized_eq,
    localSheafEpsilonNormalized_eq]
  exact IsStronglyCartesian.fac
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
    r.obj.hom (localSheafEpsilon J P R M hM r) k.hom.w.symm
    (localSheafEpsilon J P R M hM q)

/-- The fiber component of every sheaf-side transition is an isomorphism. -/
instance localSheafTransition_fiber_isIso
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsIso (localSheafTransition J P R M hM k).fiber := by
  let F := J.pseudofunctorOver (Type u)
  let φ := localSheafTransition J P R M hM k
  let ψ := localSheafEpsilonNormalized J P R M hM r
  let χ := localSheafEpsilonNormalized J P R M hM q
  have hfac : φ ≫ ψ = χ := localSheafTransition_fac J P R M hM k
  have hfiber := Pseudofunctor.CoGrothendieck.Hom.congr hfac
  dsimp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber] at hfiber
  change
    φ.fiber ≫ (F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber ≫
        (F.mapComp r.obj.hom.op.toLoc k.hom.left.op.toLoc).inv.toNatTrans.app M =
      χ.fiber ≫ eqToHom _ at hfiber
  haveI hψ : IsIso ψ.fiber := by
    dsimp [ψ]
    exact localSheafEpsilonNormalized_fiber_isIso J P R M hM r
  haveI hχ : IsIso χ.fiber := by
    dsimp [χ]
    exact localSheafEpsilonNormalized_fiber_isIso J P R M hM q
  haveI : IsIso ((F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber) := by
    infer_instance
  haveI : IsIso
      ((F.mapComp r.obj.hom.op.toLoc k.hom.left.op.toLoc).inv.toNatTrans.app M) := by
    change IsIso ((Cat.Hom.toNatIso
      (F.mapComp r.obj.hom.op.toLoc k.hom.left.op.toLoc)).inv.app M)
    infer_instance
  haveI hwhole : IsIso
      ((φ.fiber ≫ (F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber) ≫
        (F.mapComp r.obj.hom.op.toLoc k.hom.left.op.toLoc).inv.toNatTrans.app M) := by
    rw [Category.assoc, hfiber]
    infer_instance
  haveI hpair : IsIso
      (φ.fiber ≫ (F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber) :=
    IsIso.of_isIso_comp_right
      (φ.fiber ≫ (F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber)
      ((F.mapComp r.obj.hom.op.toLoc k.hom.left.op.toLoc).inv.toNatTrans.app M)
  haveI hφ : IsIso φ.fiber := IsIso.of_isIso_comp_right φ.fiber
    ((F.map k.hom.left.op.toLoc).toFunctor.map ψ.fiber)
  change IsIso φ.fiber
  exact hφ

noncomputable def localSheafTotalFunctor :
    R.arrows.category ⥤ SheafTotal J where
  obj q := localSheafTotalObj J P R M hM q
  map k := localSheafTransition J P R M hM k
  map_id q := by
    rw [localSheafTransition_eq_raw]
    dsimp [localSheafTransitionRaw]
    simpa using IsStronglyCartesian.map_self
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      q.obj.hom (localSheafEpsilon J P R M hM q)
  map_comp {q r t} k l := by
    rw [localSheafTransition_eq_raw, localSheafTransition_eq_raw,
      localSheafTransition_eq_raw]
    dsimp [localSheafTransitionRaw]
    simpa using IsStronglyCartesian.map_comp_map
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type u)))
      l.hom.w.symm k.hom.w.symm
      (localSheafEpsilon J P R M hM r)
      (localSheafEpsilon J P R M hM q)

abbrev LocalRepresentativeArrowTotal :=
  AlgebraicGeometry.RelativeYoneda.ArrowTotal

/-- A chosen local representing scheme arrow as an object of the arrow total
category. -/
noncomputable def localRepresentativeArrowObj (q : R.arrows.category) :
    LocalRepresentativeArrowTotal.{u} :=
  ⟨q.obj.left, localRepresentative J P R M hM q⟩

/-- The scheme-arrow transition obtained by fully faithful relative Yoneda preimage. -/
noncomputable def localRepresentativeArrowMap
    {q r : R.arrows.category} (k : q ⟶ r) :
    localRepresentativeArrowObj J P R M hM q ⟶
      localRepresentativeArrowObj J P R M hM r :=
  AlgebraicGeometry.RelativeYoneda.preimage J
    (localSheafTransition J P R M hM k)

/-- The base of a local representing-arrow transition. -/
@[simp] lemma localRepresentativeArrowMap_base
    {q r : R.arrows.category} (k : q ⟶ r) :
    (localRepresentativeArrowMap J P R M hM k).base = k.hom.left := rfl

/-- Relative Yoneda sends a local representing-arrow transition back to the
sheaf-side transition from which it was constructed. -/
lemma localRepresentativeArrowMap_relativeYoneda
    {q r : R.arrows.category} (k : q ⟶ r) :
    (AlgebraicGeometry.RelativeYoneda.functor J).map
        (localRepresentativeArrowMap J P R M hM k) =
      localSheafTransition J P R M hM k := by
  exact AlgebraicGeometry.RelativeYoneda.map_preimage J _

lemma isIso_of_fullyFaithful_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (hF : F.FullyFaithful) {X Y : C} (f : X ⟶ Y)
    [IsIso (F.map f)] : IsIso f := by
  let g := hF.preimage (inv (F.map f))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply hF.map_injective
    rw [F.map_comp, hF.map_preimage,
      IsIso.hom_inv_id, F.map_id]
  · apply hF.map_injective
    rw [F.map_comp, hF.map_preimage,
      IsIso.inv_hom_id, F.map_id]

/-- The fiber component of a local representing-arrow transition is an isomorphism. -/
instance localRepresentativeArrowMap_fiber_isIso
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsIso (localRepresentativeArrowMap J P R M hM k).fiber := by
  let f := (localRepresentativeArrowMap J P R M hM k).fiber
  let F := (J.over (localRepresentativeArrowObj J P R M hM q).base).yoneda
  haveI : IsIso (F.map f) := by
    dsimp [F, f, localRepresentativeArrowMap,
      AlgebraicGeometry.RelativeYoneda.preimage]
    rw [Functor.map_preimage]
    apply IsIso.comp_isIso'
    · exact localSheafTransition_fiber_isIso J P R M hM k
    · infer_instance
  exact isIso_of_fullyFaithful_map F
    (J.over (localRepresentativeArrowObj J P R M hM q).base).yonedaFullyFaithful f

/-- The transition between chosen local representing arrows induces a pullback square
of schemes. -/
lemma localRepresentativeArrowMap_isPullback
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsPullback
      ((localRepresentativeArrowMap J P R M hM k).fiber.left ≫
        pullback.fst (localRepresentative J P R M hM r).hom k.hom.left)
      (localRepresentative J P R M hM q).hom
      (localRepresentative J P R M hM r).hom k.hom.left := by
  letI hfiber : IsIso (localRepresentativeArrowMap J P R M hM k).fiber :=
    localRepresentativeArrowMap_fiber_isIso J P R M hM k
  letI : IsIso (localRepresentativeArrowMap J P R M hM k).fiber.left := by
    change IsIso ((Over.forget q.obj.left).map
      (localRepresentativeArrowMap J P R M hM k).fiber)
    infer_instance
  have hvertical : IsPullback
      (localRepresentativeArrowMap J P R M hM k).fiber.left
      (localRepresentative J P R M hM q).hom
      ((Over.pullback k.hom.left).obj
        (localRepresentative J P R M hM r)).hom
      (𝟙 q.obj.left) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨(localRepresentativeArrowMap J P R M hM k).fiber.w⟩
  exact hvertical.paste_horiz
    (IsPullback.of_hasPullback
      (localRepresentative J P R M hM r).hom k.hom.left)

/-- The coherent diagram of scheme arrows representing the pullbacks of `M` over all
arrows of the sieve. -/
noncomputable def localRepresentativeArrowFunctor :
    R.arrows.category ⥤ LocalRepresentativeArrowTotal.{u} where
  obj q := localRepresentativeArrowObj J P R M hM q
  map k := localRepresentativeArrowMap J P R M hM k
  map_id q := by
    apply (AlgebraicGeometry.RelativeYoneda.functor J).map_injective
    rw [Functor.map_id, localRepresentativeArrowMap_relativeYoneda]
    exact (localSheafTotalFunctor J P R M hM).map_id q
  map_comp {q r t} k l := by
    apply (AlgebraicGeometry.RelativeYoneda.functor J).map_injective
    rw [Functor.map_comp, localRepresentativeArrowMap_relativeYoneda,
      localRepresentativeArrowMap_relativeYoneda,
      localRepresentativeArrowMap_relativeYoneda]
    exact (localSheafTotalFunctor J P R M hM).map_comp k l

/-- The base of the local representative at `q`. -/
@[simp] lemma localRepresentativeArrowFunctor_obj_base
    (q : R.arrows.category) :
    ((localRepresentativeArrowFunctor J P R M hM).obj q).base = q.obj.left := rfl

/-- The fiber of the local representative at `q`. -/
@[simp] lemma localRepresentativeArrowFunctor_obj_fiber
    (q : R.arrows.category) :
    ((localRepresentativeArrowFunctor J P R M hM).obj q).fiber =
      localRepresentative J P R M hM q := rfl

/-- Every object of the local representative diagram has property `P`. -/
lemma localRepresentativeArrowFunctor_obj_property
    (q : R.arrows.category) :
    P ((localRepresentativeArrowFunctor J P R M hM).obj q).fiber.hom :=
  localRepresentative_property J P R M hM q

/-- The base component of every map in the local representative diagram is the
corresponding map of sieve arrows. -/
@[simp] lemma localRepresentativeArrowFunctor_map_base
    {q r : R.arrows.category} (k : q ⟶ r) :
    ((localRepresentativeArrowFunctor J P R M hM).map k).base = k.hom.left := rfl

/-- Every map in the local representative diagram is cartesian on its fiber
component. -/
instance localRepresentativeArrowFunctor_map_fiber_isIso
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsIso ((localRepresentativeArrowFunctor J P R M hM).map k).fiber :=
  localRepresentativeArrowMap_fiber_isIso J P R M hM k

end CategoryTheory.GrothendieckTopology
