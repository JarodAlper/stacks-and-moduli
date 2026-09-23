module

public import StacksAndModuli.API.PseudofunctorObjectProperty
public import StacksAndModuli.API.SheafOverCover
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Comma.Basic

/-!
# Representable objects in the pseudofunctor of sheaves on over-sites

For a morphism property `P` on a category `C`, this file defines the object property on
`J.pseudofunctorOver (Type v)` saying that a sheaf on `C/S` is represented by an object
`Z ⟶ S` whose structure morphism has `P`.

The property is stable under pullback whenever `P` is stable under base change, and it is
invariant under isomorphism.  Once a geometric argument supplies the corresponding
`Pseudofunctor.ObjectProperty.IsLocal` instance, the final theorem reduces descent from a
singleton cover to that locality statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)

/-- The property that a sheaf on the over-site of `S` is represented by an object
`Z ⟶ S` whose structure morphism satisfies `P`. -/
def representableByProperty (P : MorphismProperty C) :
    (J.pseudofunctorOver (Type v)).ObjectProperty where
  prop X F := ∃ (Z : Over X.as.unop), P Z.hom ∧
    Nonempty (CategoryTheory.yoneda.obj Z ≅ F.obj)

instance (P : MorphismProperty C) [P.IsStableUnderBaseChange] :
    (J.representableByProperty P).IsClosedUnderMapObj where
  map_obj hF f := by
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hF
    refine ⟨(Over.pullback f.as.unop).obj Z,
      P.pullback_snd Z.hom f.as.unop hZ, ?_⟩
    let e₁ := (Over.mapPullbackAdj f.as.unop).compYonedaIso.app Z
    exact ⟨e₁ ≪≫ Functor.isoWhiskerLeft (Over.map f.as.unop).op e⟩

instance (P : MorphismProperty C) :
    (J.representableByProperty P).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := by
    constructor
    intro F G e hF
    obtain ⟨Z, hZ, ⟨eF⟩⟩ := hF
    exact ⟨Z, hZ, ⟨eF ≪≫ (sheafToPresheaf _ _).mapIso e⟩⟩

/-- If representability by `P` is local for `J`, a sheaf on `C/S` which becomes
represented by a `P`-morphism after pullback along a singleton cover is itself represented
by a `P`-morphism over `S`. -/
theorem representableByProperty_of_map_obj (P : MorphismProperty C)
    [P.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal (J.representableByProperty P) J]
    {X S : C} (f : X ⟶ S)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J S)
    (F : Sheaf (J.over S) (Type v))
    (hF : (J.representableByProperty P).prop (.mk (op X))
      (((J.pseudofunctorOver (Type v)).map f.op.toLoc).toFunctor.obj F)) :
    (J.representableByProperty P).prop (.mk (op S)) F := by
  let Q := J.representableByProperty P
  let PF := J.pseudofunctorOver (Type v)
  apply Pseudofunctor.ObjectProperty.IsLocal.of_sieve
    (P := Q) (Sieve.generate (Presieve.singleton f)) hf F
  intro q
  obtain ⟨W, h, _, ⟨⟩, eq⟩ := q.property
  rw [← eq]
  let hdouble := Pseudofunctor.ObjectProperty.map_obj (P := Q) hF h.op.toLoc
  exact ObjectProperty.prop_of_iso (Q.prop _)
    ((Cat.Hom.toNatIso (PF.mapComp f.op.toLoc h.op.toLoc)).symm.app F) hdouble

/-- If representability by `P` is local for a subcanonical topology `J`, then `P`
descends along every morphism which generates a `J`-covering sieve. -/
theorem representableByProperty_descendsAlong (P Q : MorphismProperty C)
    [J.Subcanonical] [P.RespectsIso] [P.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal (J.representableByProperty P) J]
    (hQ : ∀ {X S : C} (f : X ⟶ S), Q f →
      Sieve.generate (Presieve.singleton f) ∈ J S) :
    P.DescendsAlong Q := by
  constructor
  intro A X Y Z fst snd f g h hf hfst
  let F : Sheaf (J.over Z) (Type v) := (J.over Z).yoneda.obj (Over.mk g)
  have hfst' : P ((Over.pullback f).obj (Over.mk g)).hom := by
    change P (pullback.snd g f)
    rw [← h.flip.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at hfst
    exact hfst
  have hlocal : (J.representableByProperty P).prop (.mk (op X))
      (((J.pseudofunctorOver (Type v)).map f.op.toLoc).toFunctor.obj F) := by
    refine ⟨(Over.pullback f).obj (Over.mk g), hfst', ⟨?_⟩⟩
    change CategoryTheory.yoneda.obj ((Over.pullback f).obj (Over.mk g)) ≅
      (Over.map f).op ⋙ CategoryTheory.yoneda.obj (Over.mk g)
    exact (Over.mapPullbackAdj f).compYonedaIso.app (Over.mk g)
  obtain ⟨W, hW, ⟨e⟩⟩ :=
    J.representableByProperty_of_map_obj P f (hQ f hf) F hlocal
  let eOver : W ≅ Over.mk g := Yoneda.fullyFaithful.preimageIso e
  letI : IsIso eOver.hom.left := by
    refine ⟨⟨eOver.inv.left, ?_, ?_⟩⟩
    · exact congrArg Over.Hom.left eOver.hom_inv_id
    · exact congrArg Over.Hom.left eOver.inv_hom_id
  have hcomp : P (eOver.hom.left ≫ g) := by
    convert hW using 1
    exact eOver.hom.w
  exact (P.cancel_left_of_respectsIso eOver.hom.left g).mp hcomp

end CategoryTheory.GrothendieckTopology
