module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksAndModuli.API.PresheafSeparation

/-!
# Sheafification

This module formalizes the "Sheafification" subsection (Subsection 3.3.3,
`subsec:sheafication`) of §3.3 (Presheaves and sheaves) of *Stacks and Moduli*,
section label `sec:sheaves`: the
sheafification theorem (Theorem 3.3.15, `thm:sheafification`), together with the notion of
separated presheaf and the two reflections appearing in its proof. The exact first
reflection (quotienting by local equality) and its universal property are supplied by
`StacksAndModuli.API.PresheafSeparation`; the second is Mathlib's plus construction. This file
records the following main results:

- `CategoryTheory.sheafificationAdjunction`: the sheafification functor
  `presheafToSheaf J A` is left adjoint to the forgetful functor `sheafToPresheaf J A`;

-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmSheafification

open CategoryTheory

universe w v u

/- Background functor used in the proof of Theorem 3.3.15 (full-subcategory inclusion):
the category of separated presheaves includes fully faithfully into the category of
presheaves. -/
example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    CategoryTheory.SeparatedPresheaf J ⥤ (𝒮ᵒᵖ ⥤ Type max u v) :=
  separatedPresheafToPresheaf J

/- **Theorem 3.3.15** (`thm:sheafification`): let $(\cS, J)$ be a site. The forgetful
functor $\Sh(\cS) \to \Pre(\cS)$ admits a left adjoint $F \mapsto F^{\sh}$, the
sheafification. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    presheafToSheaf J (Type max u v) ⊣ sheafToPresheaf J (Type max u v) :=
  sheafificationAdjunction J (Type max u v)

/- API construction associated to Theorem 3.3.15 (the functor and unit): the sheafification
functor itself, and the adjunction unit `F ⟶ F^sh` on a presheaf. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    (𝒮ᵒᵖ ⥤ Type max u v) ⥤ Sheaf J (Type max u v) :=
  presheafToSheaf J (Type max u v)

noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) :
    F ⟶ ((presheafToSheaf J (Type max u v)).obj F).obj :=
  (sheafificationAdjunction J (Type max u v)).unit.app F

/- API equivalence derived from Theorem 3.3.15 (the universal property): morphisms from the
sheafification to a sheaf correspond to morphisms from the presheaf. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) (G : Sheaf J (Type max u v)) :
    ((presheafToSheaf J (Type max u v)).obj F ⟶ G) ≃ (F ⟶ (sheafToPresheaf J _).obj G) :=
  (sheafificationAdjunction J (Type max u v)).homEquiv F G

/- Background definition used in the proof of Theorem 3.3.15 (separated presheaf
in the proof): a presheaf $F$ is *separated* if for every covering $\{S_i \to S\}$ the map
$F(S) \to \prod_i F(S_i)$ is injective, i.e. amalgamations are unique when they exist. In
the book's proof the first step $\sh_1$ makes a presheaf separated and the second step
$\sh_2$ makes a separated presheaf a sheaf. -/
example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) : Prop :=
  Presieve.IsSeparated J F

/- Proof-stage adjunction for Theorem 3.3.15 (the first left adjoint):
$\sh_1(F)$ is obtained by quotienting each $F(S)$ by equality on a covering family, and
this defines a reflection from presheaves to separated presheaves. -/
example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    presheafToSeparatedPresheaf J ⊣ separatedPresheafToPresheaf J :=
  separationAdjunction J

/- Proof-stage adjunction for Theorem 3.3.15 (the second left adjoint):
$\sh_2(F)$ is the matching-family plus construction, and on separated presheaves it is a
reflection into sheaves. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    separatedPresheafToSheaf J ⊣ sheafToSeparatedPresheaf J :=
  plusSeparatedAdjunction J

/- Proof-stage adjunction for Theorem 3.3.15 (the composite adjunction): composing
the two reflections gives a sheafification functor left adjoint to the forgetful functor. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    presheafToSeparatedPresheaf J ⋙ separatedPresheafToSheaf J ⊣
      sheafToSeparatedPresheaf J ⋙ separatedPresheafToPresheaf J :=
  (separationAdjunction J).comp (plusSeparatedAdjunction J)

/- Alternative construction associated to Theorem 3.3.15: Mathlib
also constructs sheafification by applying the plus construction twice. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) : 𝒮ᵒᵖ ⥤ Type max u v :=
  J.plusObj F

/- Helper lemma used in the proof of Theorem 3.3.15 (first step): one
application of the plus construction always produces a separated presheaf. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) :
    Presieve.IsSeparated J (J.plusObj F) := by
  intro X S hS x t₁ t₂ ht₁ ht₂
  apply GrothendieckTopology.Plus.sep F ⟨S, hS⟩
  intro I
  exact (ht₁ I.f I.hf).trans (ht₂ I.f I.hf).symm

/- Helper lemma used in the proof of Theorem 3.3.15 (second step): applying
the plus construction to a separated presheaf produces a sheaf. -/
noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) (hF : Presieve.IsSeparated J F) :
    Presheaf.IsSheaf J (J.plusObj F) := by
  apply GrothendieckTopology.Plus.isSheaf_of_sep (J := J) F
  intro X S x y hxy
  apply (hF S.1 S.2).ext
  intro Y f hf
  exact hxy ⟨Y, f, hf⟩

noncomputable example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮)
    (F : 𝒮ᵒᵖ ⥤ Type max u v) :
    Presheaf.IsSheaf J (J.plusObj (J.plusObj F)) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus J F

end ThmSheafification

section RmkTopos

open CategoryTheory

universe w vC uC vE uE

/-- Background definition from the unlabeled Topos
remark): at fixed universe levels, a Grothendieck topos is a category equivalent to the
category of set-valued sheaves on some site. -/
def CategoryTheory.IsGrothendieckTopos (E : Type uE) [Category.{vE} E] : Prop :=
  ∃ (C : Type uC) (_ : Category.{vC} C) (J : GrothendieckTopology C),
    Nonempty (E ≌ Sheaf J (Type w))

/-- Background definition from the second clause of the unlabeled Topos remark:
two sites present the same topos when their categories of set-valued sheaves are
equivalent. -/
def CategoryTheory.SitesPresentSameTopos {C : Type uC} [Category.{vC} C]
    {D : Type uE} [Category.{vE} D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop :=
  Nonempty (Sheaf J (Type w) ≌ Sheaf K (Type w))

-- STATUS: remark-complete

end RmkTopos
