module

public import StacksAndModuli.API.RepresentableSheafOverlap
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.3-morphisms-gluing-epimorphisms»

/-!
# Singleton descent for sheaves represented by monomorphisms

If the pullback of a sheaf along a singleton cover is represented by a monomorphism,
and that monomorphism descends geometrically, then the descended object represents the
original sheaf.  Compatibility of the local representing isomorphism is automatic
because every further pullback of the local representative is subterminal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe t v' v u' u

namespace CategoryTheory.GrothendieckTopology

/-- The constant singleton family of objects associated to `f : X ⟶ S`. -/
def singletonObjects (X : AlgebraicGeometry.Scheme.{u}) :
    PUnit.{1} → AlgebraicGeometry.Scheme.{u} := fun _ ↦ X

/-- A morphism regarded as a family indexed by a one-element type. -/
def singletonFamily {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    (i : PUnit.{1}) → singletonObjects X i ⟶ S := fun _ ↦ f

/-- Descent data obtained by restricting a sheaf along a singleton family. -/
abbrev singletonDescentData
    (J : GrothendieckTopology AlgebraicGeometry.Scheme.{u})
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf (J.over S) (Type u)) :=
  ((J.pseudofunctorOver (Type u)).toDescentData (singletonFamily f)).obj F

/-- Construct an isomorphism of descent data when every relevant hom-set into the
target datum is a subsingleton. -/
noncomputable def Pseudofunctor.DescentData.isoMkOfSubsingleton
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {X : ι → C} {f : (i : ι) → X i ⟶ S}
    {D₁ D₂ : F.DescentData f}
    (e : (i : ι) → D₁.obj i ≅ D₂.obj i)
    (hsub : ∀ {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι}
      (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (_hf₁ : f₁ ≫ f i₁ = q) (_hf₂ : f₂ ≫ f i₂ = q),
      Subsingleton
        ((F.map f₁.op.toLoc).toFunctor.obj (D₁.obj i₁) ⟶
          (F.map f₂.op.toLoc).toFunctor.obj (D₂.obj i₂))) :
    D₁ ≅ D₂ :=
  Pseudofunctor.DescentData.isoMk e (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    exact (hsub q f₁ f₂ hf₁ hf₂).elim _ _)

variable (J : GrothendieckTopology AlgebraicGeometry.Scheme.{u}) [J.Subcanonical]

/-- The hom-sets occurring in the target of singleton descent data are subsingletons
when the local sheaf is represented by a monomorphism. -/
lemma singletonDescentData_hom_subsingleton
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (F A : Sheaf (J.over S) (Type u)) (Z : Over X) [Mono Z.hom]
    (e : CategoryTheory.yoneda.obj Z ≅
      ((J.overMapPullback (Type u) f).obj F).obj)
    {Y : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ S)
    {i₁ i₂ : PUnit.{1}}
    (f₁ : Y ⟶ singletonObjects X i₁)
    (f₂ : Y ⟶ singletonObjects X i₂)
    (_hf₁ : f₁ ≫ singletonFamily f i₁ = q)
    (_hf₂ : f₂ ≫ singletonFamily f i₂ = q) :
    Subsingleton
      (((J.pseudofunctorOver (Type u)).map f₁.op.toLoc).toFunctor.obj
          ((singletonDescentData J f A).obj i₁) ⟶
        ((J.pseudofunctorOver (Type u)).map f₂.op.toLoc).toFunctor.obj
          ((singletonDescentData J f F).obj i₂)) := by
  change Y ⟶ X at f₁ f₂
  change Subsingleton
    (((J.pseudofunctorOver (Type u)).map f₁.op.toLoc).toFunctor.obj
        ((singletonDescentData J f A).obj i₁) ⟶
      ((J.pseudofunctorOver (Type u)).map f₂.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type u)).map f.op.toLoc).toFunctor.obj F))
  exact J.subsingleton_hom_to_pullback_of_representedBy_mono f f₂ F Z e _

/-- A geometrically descended monomorphism represents the original sheaf. -/
noncomputable def representableSheafIsoOfSingletonDescent
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J S)
    (F : Sheaf (J.over S) (Type u)) (Z : Over X) [Mono Z.hom]
    (e : CategoryTheory.yoneda.obj Z ≅
      ((J.overMapPullback (Type u) f).obj F).obj)
    (W : Over S) (a : Z ≅ (Over.pullback f).obj W) :
    CategoryTheory.yoneda.obj W ≅ F.obj := by
  let eS : (J.over X).yoneda.obj Z ≅
      (J.overMapPullback (Type u) f).obj F :=
    (fullyFaithfulSheafToPresheaf (J.over X) (Type u)).preimageIso e
  let eLoc : (J.overMapPullback (Type u) f).obj ((J.over S).yoneda.obj W) ≅
      (J.overMapPullback (Type u) f).obj F :=
    (J.overMapPullbackYonedaIso f W).symm ≪≫
      (J.over X).yoneda.mapIso a.symm ≪≫ eS
  let eD : singletonDescentData J f ((J.over S).yoneda.obj W) ≅
      singletonDescentData J f F :=
    Pseudofunctor.DescentData.isoMkOfSubsingleton
      (F := J.pseudofunctorOver (Type u))
      (ι := PUnit.{1}) (S := S) (X := singletonObjects X)
      (f := singletonFamily f)
      (D₁ := singletonDescentData J f ((J.over S).yoneda.obj W))
      (D₂ := singletonDescentData J f F) (fun _ : PUnit.{1} ↦ eLoc) (by
        intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        exact J.singletonDescentData_hom_subsingleton f F
          ((J.over S).yoneda.obj W) Z e q f₁ f₂ hf₁ hf₂)
  have hcover : Sieve.ofArrows (singletonObjects X) (singletonFamily f) ∈ J S := by
    change Sieve.generate
      (Presieve.ofArrows (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) ∈ J S
    simpa only [Presieve.ofArrows_pUnit] using hf
  let eGlobal : (J.over S).yoneda.obj W ≅ F :=
    ((J.pseudofunctorOver (Type u)).fullyFaithfulToDescentData
      (singletonFamily f) hcover).preimageIso eD
  exact (sheafToPresheaf (J.over S) (Type u)).mapIso eGlobal

end CategoryTheory.GrothendieckTopology
