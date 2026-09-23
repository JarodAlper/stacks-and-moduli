module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Injective abelian sheaves are flasque

The classical proof that a flasque sheaf has vanishing higher cohomology runs by embedding
it in an injective sheaf and dimension-shifting; the step that makes the induction close is
that **injective sheaves are flasque**, so that the quotient stays flasque.

The proof is the familiar one. For an object `U` of the site let `ℤ_U` be the free abelian
sheaf on the representable presheaf of `U` — the same sheaf Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheaf` is built from. Then

* `Hom(ℤ_U, F) ≅ F(U)`, naturally in `U` (`freeYonedaEquiv`, `freeYonedaEquiv_naturality`),
  by composing the sheafification adjunction, the free–forgetful adjunction whiskered on
  the right, and the Yoneda lemma;
* `ℤ_U ⟶ ℤ_V` is a monomorphism for `U ⟶ V` in the site, because `yoneda.obj U ⟶
  yoneda.obj V` is pointwise injective when hom-sets of the site are subsingletons (which
  they are for the opens of a topological space), the free abelian group functor preserves
  injections, and sheafification is exact.

Injectivity of `F` then makes `F(V) ⟶ F(U)` surjective, which is flasqueness.

## Main definitions

* `CategoryTheory.Sheaf.freeAt`: the free abelian sheaf `ℤ_U` on an object of the site.
* `CategoryTheory.Sheaf.freeYonedaEquiv`: `Hom(ℤ_U, F) ≃ F(U)`.

## Main results

* `CategoryTheory.Sheaf.freeYonedaEquiv_naturality`: the equivalence turns precomposition
  with `ℤ_U ⟶ ℤ_V` into restriction `F(V) ⟶ F(U)`.
* `TopCat.Sheaf.isFlasque_of_injective`: an injective abelian sheaf on a topological space
  is flasque.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The free abelian sheaf on the representable presheaf of an object `U` of the site.

Over the site of opens of a topological space this is the extension by zero `j_! ℤ_U` of the
constant sheaf `ℤ` on `U`; it is the sheaf Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheaf` is built from. -/
noncomputable abbrev freeAt (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Functoriality of `freeAt` in the object of the site. -/
noncomputable def freeAtMap {U V : C} (i : U ⟶ V) : freeAt J U ⟶ freeAt J V :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

/-- The free–forgetful adjunction between abelian groups and types, whiskered on the right
so that it relates presheaves of abelian groups to presheaves of types. -/
noncomputable def freePresheafAdj :
    (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free ⊣
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj
        (forget AddCommGrpCat.{v}) :=
  AddCommGrpCat.adj.whiskerRight Cᵒᵖ

/-- The free–forgetful hom bijection for presheaves, with its two hom-types written as
composites rather than as values of `Functor.whiskeringRight`. The wrapper exists so that
`rw` can match `whiskerFreeHomEquiv_naturality` syntactically; the two spellings are
definitionally equal but not syntactically so, and `rw` fails on the raw form. -/
noncomputable def whiskerFreeHomEquiv (P : Cᵒᵖ ⥤ Type v)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (P ⋙ AddCommGrpCat.free ⟶ G) ≃ (P ⟶ G ⋙ forget AddCommGrpCat.{v}) :=
  (freePresheafAdj (C := C)).homEquiv P G

/-- Naturality of the free–forgetful hom bijection in the presheaf of types. -/
lemma whiskerFreeHomEquiv_naturality {P Q : Cᵒᵖ ⥤ Type v}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (α : P ⟶ Q)
    (g : Q ⋙ AddCommGrpCat.free ⟶ G) :
    whiskerFreeHomEquiv (C := C) P G (Functor.whiskerRight α AddCommGrpCat.free ≫ g) =
      α ≫ whiskerFreeHomEquiv (C := C) Q G g :=
  Adjunction.homEquiv_naturality_left _ _ _

/-- **`Hom(ℤ_U, F) ≅ F(U)`.** Sections of an abelian sheaf over `U` are the same thing as
maps from the free abelian sheaf on `U`. -/
noncomputable def freeYonedaEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeAt J U ⟶ F) ≃ (F.obj.obj (op U) : Type v) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _).trans
    ((whiskerFreeHomEquiv (yoneda.obj U)
      ((sheafToPresheaf J AddCommGrpCat.{v}).obj F)).trans yonedaEquiv)

/-- The equivalence `Hom(ℤ_U, F) ≃ F(U)` turns precomposition with `ℤ_U ⟶ ℤ_V` into
restriction of sections along `U ⟶ V`. -/
lemma freeYonedaEquiv_naturality {U V : C} (i : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (f : freeAt J V ⟶ F) :
    freeYonedaEquiv J U F (freeAtMap J i ≫ f) =
      F.obj.map i.op (freeYonedaEquiv J V F f) := by
  unfold freeYonedaEquiv freeAtMap
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, whiskerFreeHomEquiv_naturality]
  exact (yonedaEquiv_naturality _ i).symm

/-- The equivalence `Hom(ℤ_U, F) ≃ F(U)` is natural in the sheaf: postcomposition with
`F ⟶ G` becomes the action of that map on sections. -/
lemma freeYonedaEquiv_naturality_sheaf (U : C) {F G : Sheaf J AddCommGrpCat.{v}} (g : F ⟶ G)
    (f : freeAt J U ⟶ F) :
    freeYonedaEquiv J U G (f ≫ g) = g.hom.app (op U) (freeYonedaEquiv J U F f) := by
  unfold freeYonedaEquiv
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- For a *thin* site — one whose hom-sets are subsingletons, such as the opens of a
topological space — the map `ℤ_U ⟶ ℤ_V` induced by `U ⟶ V` is a monomorphism.

`yoneda.obj U ⟶ yoneda.obj V` is pointwise injective because its source is a subsingleton;
`AddCommGrpCat.free` preserves monomorphisms; and sheafification is left exact. -/
instance mono_freeAtMap [Quiver.IsThin C] [HasSheafify J AddCommGrpCat.{v}]
    {U V : C} (i : U ⟶ V) : Mono (freeAtMap J i) := by
  have happ : ∀ W : Cᵒᵖ, Mono ((yoneda.map i).app W) := by
    intro W
    rw [mono_iff_injective]
    exact fun a b _ ↦ Subsingleton.elim a b
  have h1 : ∀ W : Cᵒᵖ,
      Mono ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free).app W) := by
    intro W
    haveI := happ W
    exact AddCommGrpCat.free.map_mono _
  have : Mono (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) := by
    haveI := h1
    exact NatTrans.mono_of_mono_app _
  exact (presheafToSheaf J AddCommGrpCat.{v}).map_mono _

end CategoryTheory.Sheaf

namespace TopCat.Sheaf

open CategoryTheory Sheaf

universe w

variable {X : TopCat.{w}}

/-- **An injective abelian sheaf is flasque.**

Given `U ⟶ V` of opens and a section over the smaller one, present it as a map from the
free abelian sheaf `ℤ_U` (`freeYonedaEquiv`), extend along the monomorphism
`ℤ_U ⟶ ℤ_V` by injectivity, and read the extension off as a section over `V` restricting to
the original one (`freeYonedaEquiv_naturality`).

This is the step that closes the induction in the classical proof that flasque sheaves have
vanishing higher cohomology: it is what keeps the quotient by a flasque subsheaf flasque
when the ambient sheaf is chosen injective. -/
theorem isFlasque_of_injective (F : TopCat.Sheaf AddCommGrpCat.{w} X)
    [CategoryTheory.Injective F] : F.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    set J := Opens.grothendieckTopology X with hJ
    refine ⟨freeYonedaEquiv J U.unop F
      (CategoryTheory.Injective.factorThru
        ((freeYonedaEquiv J V.unop F).symm t) (freeAtMap J i.unop)), ?_⟩
    have := freeYonedaEquiv_naturality J i.unop F
      (CategoryTheory.Injective.factorThru
        ((freeYonedaEquiv J V.unop F).symm t) (freeAtMap J i.unop))
    rw [CategoryTheory.Injective.comp_factorThru] at this
    exact this.symm.trans (Equiv.apply_symm_apply _ t)

end TopCat.Sheaf
