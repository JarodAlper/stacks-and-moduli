module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Transport and comparison of representability

Supporting API with no Stacks Project counterpart of its own. Two facts about
`Functor.RepresentableBy` that Mathlib does not carry:

* if `L ⊣ R` is an adjunction and the presheaf `F` on the target category is
  representable by `P`, then the restricted presheaf `L.op ⋙ F` is representable by
  `R.obj P`;
* the comparison isomorphism between two representing objects, in the form that
  classifies points: `e'.homEquiv (t ≫ e.classifyingHom e') = e.homEquiv t`. (Mathlib's
  `uniqueUpToIso` is the same isomorphism, but its `hom` is packaged through
  `Yoneda.ext`, from which this identity is not directly available.);
* under a representation, bijectivity of the presheaf restriction map is equivalent to
  unique extension of morphisms into the representing object.
* a natural isomorphism between type-valued functors preserves bijectivity of every map.

Consumed by the relative Grassmannian of §2.2: for an open immersion `j : U ⟶ S` the
adjunction `Over.map j ⊣ Over.pullback j` turns a representative of `Gr(q, V)` over `S`
into a representative of the restricted functor over `U`, namely the base change of the
representative along `j`.

Main declarations:
- `CategoryTheory.Adjunction.compRepresentableBy`;
- `CategoryTheory.Adjunction.compRepresentableBy_homEquiv_symm`;
- `CategoryTheory.Functor.RepresentableBy.classifyingIso` and
  `CategoryTheory.Functor.RepresentableBy.homEquiv_comp_classifyingHom`;
- `CategoryTheory.Functor.RepresentableBy.map_bijective_iff_precomp`.
- `CategoryTheory.Functor.map_bijective_iff_of_iso`.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- Representability transports along an adjunction `L ⊣ R`: if the presheaf `F` on `D` is
representable by `P`, then the presheaf `L.op ⋙ F` on `C` is representable by `R.obj P`.
The bijection is the adjunction transpose followed by the given one. -/
def compRepresentableBy (adj : L ⊣ R) {F : Dᵒᵖ ⥤ Type v} {P : D}
    (h : F.RepresentableBy P) : (L.op ⋙ F).RepresentableBy (R.obj P) where
  homEquiv {T} := (adj.homEquiv T P).symm.trans h.homEquiv
  homEquiv_comp {T T'} f g := by
    dsimp
    rw [adj.homEquiv_naturality_left_symm, h.homEquiv_comp]

@[simp]
lemma compRepresentableBy_homEquiv (adj : L ⊣ R) {F : Dᵒᵖ ⥤ Type v} {P : D}
    (h : F.RepresentableBy P) {T : C} (g : T ⟶ R.obj P) :
    (adj.compRepresentableBy h).homEquiv g = h.homEquiv ((adj.homEquiv T P).symm g) :=
  rfl

@[simp]
lemma compRepresentableBy_homEquiv_symm (adj : L ⊣ R) {F : Dᵒᵖ ⥤ Type v} {P : D}
    (h : F.RepresentableBy P) {T : C} (z : F.obj (op (L.obj T))) :
    (adj.compRepresentableBy h).homEquiv.symm z =
      adj.homEquiv T P (h.homEquiv.symm z) :=
  rfl

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v} {Y Y' : C}

/-- Under a representation of `F` by `Y`, bijectivity of restriction along `f` is
equivalent to unique extension of morphisms into `Y` along `f`. -/
lemma map_bijective_iff_precomp (e : F.RepresentableBy Y) {X X' : C} (f : X ⟶ X') :
    Function.Bijective (F.map f.op) ↔
      Function.Bijective (fun g : X' ⟶ Y ↦ f ≫ g) := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro g g' hgg'
      change f ≫ g = f ≫ g' at hgg'
      apply e.homEquiv.injective
      apply hinj
      rw [← e.homEquiv_comp, ← e.homEquiv_comp, hgg']
    · intro g
      obtain ⟨x, hx⟩ := hsurj (e.homEquiv g)
      refine ⟨e.homEquiv.symm x, ?_⟩
      apply e.homEquiv.injective
      rw [e.homEquiv_comp, Equiv.apply_symm_apply, hx]
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x x' hxx'
      apply e.homEquiv.symm.injective
      apply hinj
      apply e.homEquiv.injective
      rw [e.homEquiv_comp, e.homEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, hxx']
    · intro x
      obtain ⟨g, hg⟩ := hsurj (e.homEquiv.symm x)
      change f ≫ g = e.homEquiv.symm x at hg
      refine ⟨e.homEquiv g, ?_⟩
      rw [← e.homEquiv_comp, hg, Equiv.apply_symm_apply]

/-- The comparison morphism of two representing objects: the morphism classified by the
universal point of the source. -/
def classifyingHom (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ⟶ Y' :=
  e'.homEquiv.symm (e.homEquiv (𝟙 Y))

/-- The comparison morphism classifies the same points as the identity: this is the
defining property, and it determines `classifyingHom` uniquely. -/
lemma homEquiv_comp_classifyingHom (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y')
    {T : C} (t : T ⟶ Y) : e'.homEquiv (t ≫ e.classifyingHom e') = e.homEquiv t := by
  rw [classifyingHom, e'.comp_homEquiv_symm, Equiv.apply_symm_apply, ← e.homEquiv_comp,
    Category.comp_id]

/-- Two representing objects of the same functor are canonically isomorphic, by the
morphisms classifying the two universal points. -/
@[simps]
def classifyingIso (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ≅ Y' where
  hom := e.classifyingHom e'
  inv := e'.classifyingHom e
  hom_inv_id := by
    apply e.homEquiv.injective
    rw [homEquiv_comp_classifyingHom, classifyingHom, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply e'.homEquiv.injective
    rw [homEquiv_comp_classifyingHom, classifyingHom, Equiv.apply_symm_apply]

end CategoryTheory.Functor.RepresentableBy

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
  {F G : _root_.CategoryTheory.Functor C (Type v)}

/-- A natural isomorphism of type-valued functors preserves bijectivity of the map
attached to every morphism. -/
lemma map_bijective_iff_of_iso (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    Function.Bijective (F.map f) ↔ Function.Bijective (G.map f) := by
  rw [← Function.Bijective.of_comp_iff'
      (e.app Y).toEquiv.bijective (F.map f),
    ← Function.Bijective.of_comp_iff (G.map f)
      (e.app X).toEquiv.bijective]
  change Function.Bijective ((e.hom.app Y) ∘ F.map f) ↔
    Function.Bijective (G.map f ∘ (e.hom.app X))
  have hfun : ((e.hom.app Y) : F.obj Y → G.obj Y) ∘ F.map f =
      G.map f ∘ ((e.hom.app X) : F.obj X → G.obj X) := by
    funext x
    have h := types_congr_hom (e.hom.naturality f) x
    simpa only [types_comp_apply, Function.comp_apply] using h
  rw [hfun]

end CategoryTheory.Functor
