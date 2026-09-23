module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.5-moduli-stack-of-coherent-sheaves-and-vector-bundles»
public import StacksAndModuli.API.RepresentableActionQuotient
public import StacksAndModuli.API.FreeStackCompletionUniversal
public import StacksAndModuli.API.PrestackProducts
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4b-action-quotient-universal-property»

/-!
# Stackification

This module formalizes `thm:stackification` of §3.5 (Stacks) of *Stacks and Moduli*,
label `sec:stacks`. Formalization state per
label: see this folder's STATUS.md.

Every prestack `𝒳` over a site admits a stackification: a stack `𝒳ˢᵗ` with a morphism
`i : 𝒳 → 𝒳ˢᵗ` through which every morphism to a stack factors uniquely up to 2-isomorphism.
The universal property is phrased through precomposition on morphism categories.

Main result:
- `CategoryTheory.BasedCategory.exists_stackification`: **Theorem 3.5.18**
  (`thm:stackification`), the existence and universal property of stackification.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmStackification

open CategoryTheory Functor Opposite

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (J : GrothendieckTopology 𝒮)

/-- Background construction for Theorem 3.5.18 (the general precomposition functor):
precomposition with a morphism of based categories `i : 𝒳 ⥤ᵇ 𝒳'`, as a functor
`MOR(𝒳', 𝒴) ⥤ MOR(𝒳, 𝒴)` between morphism categories. The book's displayed functor
`MOR(𝒳ˢᵗ, 𝒴) → MOR(𝒳, 𝒴)` is the instance at the stackification morphism `i : 𝒳 → 𝒳ˢᵗ`. -/
@[simps]
def _root_.CategoryTheory.BasedFunctor.precompFunctor {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒳' : BasedCategory.{v₃, u₃} 𝒮} (i : 𝒳 ⥤ᵇ 𝒳') (𝒴 : BasedCategory.{v₄, u₄} 𝒮) :
    (𝒳' ⥤ᵇ 𝒴) ⥤ (𝒳 ⥤ᵇ 𝒴) where
  obj F := i.comp F
  map {F G} α :=
    { toNatTrans := Functor.whiskerLeft i.toFunctor α.toNatTrans
      isHomLift' := fun a ↦ α.isHomLift (Functor.congr_obj i.w a) }
  map_id F := by
    apply BasedNatTrans.homCategory.ext
    rfl
  map_comp α β := by
    apply BasedNatTrans.homCategory.ext
    rfl

/-- **Theorem 3.5.18** (`thm:stackification`), including **Equation 3.5.19**
(`eqn:stackification`) (Stackification): let `𝒳` be a prestack
over a site `(𝒮, J)`. There exist a stack `𝒳ˢᵗ` and a morphism of prestacks `i : 𝒳 → 𝒳ˢᵗ`
such that for every stack `𝒴`, composition with `i` (Equation 3.5.19)
is an equivalence `MOR(𝒳ˢᵗ, 𝒴) ≌ MOR(𝒳, 𝒴)`. The universal property
is quantified over stacks `𝒴` at a fixed universe level. The hom universe is the
four-way maximum because the free syntax stores base objects, total-category objects,
and arrows together; this is implementation-level universe bookkeeping, invisible in
the book. See the Theorem 3.5.18 entry of this folder's COMMENTARY.md. -/
theorem exists_stackification (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
    [𝒳.p.IsFiberedInGroupoids] :
    ∃ (𝒳st : BasedCategory.{max u₁ v₁ u₂ v₂, max u₁ u₂ v₁ v₂} 𝒮) (_ : IsStack J 𝒳st)
      (i : 𝒳 ⥤ᵇ 𝒳st),
      ∀ (𝒴 : BasedCategory.{max u₁ v₁ u₂ v₂, max u₁ u₂ v₁ v₂} 𝒮), IsStack J 𝒴 →
        (i.precompFunctor 𝒴).IsEquivalence := by
  refine ⟨FreeStackCompletion.completion J 𝒳, inferInstance,
    FreeStackCompletion.inclusion J 𝒳, ?_⟩
  intro 𝒴 h𝒴
  letI := h𝒴
  let P := (FreeStackCompletion.inclusion J 𝒳).precompFunctor 𝒴
  letI : P.Full := by
    constructor
    intro H K alpha
    refine ⟨FreeStackCompletion.UniversalGraph.extendNatTrans H K alpha, ?_⟩
    apply BasedNatTrans.homCategory.ext
    ext a
    exact FreeStackCompletion.UniversalGraph.extendNatTrans_inclusion_app H K alpha a
  letI : P.Faithful := by
    constructor
    intro H K alpha beta hab
    apply BasedNatTrans.homCategory.ext
    ext a
    apply FreeStackCompletion.UniversalGraph.component_ext H K alpha beta
      (fun b ↦ congrArg (fun gamma ↦ gamma.app b) hab)
      (Classical.choice a.valid)
  letI : P.EssSurj := by
    constructor
    intro F
    exact ⟨FreeStackCompletion.Interpretation.extension (J := J) F,
      ⟨FreeStackCompletion.Interpretation.extensionInclusionIso (J := J) F⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedCategory

end ThmStackification

section ExerQuotientPrestackProperties

open CategoryTheory Functor Opposite

universe w v u

namespace CategoryTheory.PresheafAction

variable {C : Type u} [Category.{v} C] (A : PresheafAction.{w} C)

/-- API generalization used in Exercise 3.5.21 (part (a), in
presheaf-action form): if the acting group presheaf and the acted-on presheaf are
sheaves, then the action quotient prestack `[U/G]ᵖʳᵉ` satisfies the morphism-gluing
axiom of a stack. For representable presheaves on the étale site, the two sheaf
hypotheses follow from subcanonicity, giving the book's assertion for trivial
principal `G`-bundles. -/
theorem quotientPrestack_morphismsGlue (J : GrothendieckTopology C)
    (hG : Presieve.IsSheaf J (A.G ⋙ forget GrpCat))
    (hU : Presieve.IsSheaf J A.U) :
    A.quotientProj.MorphismsGlue J :=
  A.quotientProj_morphismsGlue_of_sheaves J hG hU

end CategoryTheory.PresheafAction

end ExerQuotientPrestackProperties

section ExerQuotientPrestackProperties

open CategoryTheory Functor Opposite
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G U : Over S) [GrpObj G] [ModObj G U]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- **Exercise 3.5.21** (`exer:quotient-prestack-properties`) (part (a)): the
quotient prestack whose objects over `T` are maps `T → U` and whose arrows are
gauge transformations satisfies the morphism-gluing axiom for the relative etale
topology.  This is the first stack axiom in Definition 3.5.1. -/
theorem trivialActionQuotientPrestack_morphismsGlue_etale :
    (CategoryTheory.representablePresheafAction G U).quotientProj.MorphismsGlue
      (Scheme.etaleTopology.over S) := by
  apply CategoryTheory.PresheafAction.quotientProj_morphismsGlue_of_sheaves
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (CategoryTheory.yoneda.obj G)
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (CategoryTheory.yoneda.obj U)

end AlgebraicGeometry.Scheme

end ExerQuotientPrestackProperties

section ExerQuotientPrestackProperties

open CategoryTheory Functor Opposite
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G U : Over S) [GrpObj G] [ModObj G U]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- **Exercise 3.5.21** (`exer:quotient-prestack-properties`) (part (b), fully
faithful assertion): the functor sending a representable point to its trivial
principal bundle is fully faithful. -/
theorem trivialActionQuotient_inclusion_isMonomorphism :
    (TrivialActionQuotient.inclusion (G := G) (U := U)).IsMonomorphism := by
  constructor
  · change (TrivialActionQuotient.functor (G := G) (U := U)).Full
    infer_instance
  · change (TrivialActionQuotient.functor (G := G) (U := U)).Faithful
    infer_instance

/-- **Exercise 3.5.21** (`exer:quotient-prestack-properties`) (part (b), local
stackification criterion): the principal-bundle quotient is an étale stack, and the
fully faithful trivial-torsor inclusion is locally essentially surjective.  It
therefore satisfies the standard local-equivalence characterization of the assertion
that `[U/G]` is the stackification of `[U/G]ᵖʳᵉ`. -/
theorem trivialActionQuotient_inclusion_isLocalStackification :
    BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology.over S)
      (TrivialActionQuotient.inclusion (G := G) (U := U)) :=
  TrivialActionQuotient.inclusion_isLocalStackification_etale
    (G := G) (U := U) (Scheme.isStack_actionQuotientPrestack G U)

end AlgebraicGeometry.Scheme

end ExerQuotientPrestackProperties

section ExerActionQuotientCategoricalAmongStacks

open CategoryTheory Functor Opposite

universe w v u v' u'

namespace CategoryTheory.PresheafAction.CoherentQuotientDatum

variable {C : Type u} [Category.{v} C] (A : PresheafAction.{w} C)
  {Q : BasedCategory.{v', u'} C} {Z : BasedCategory.{v', u'} C}
  (i : A.quotientPrestack ⥤ᵇ Q)
  (phi : A.elementPrestack ⥤ᵇ Z)

/-- Result of the unlabeled
exercise following Exercise 3.5.21): if `i : [U/G]ᵖʳᵉ → Q` has the
stackification universal property against a stack `Z`, every coherent
`G`-invariant morphism `U → Z` factors through `Q`, up to a 2-isomorphism. -/
theorem exists_factorization_through_stackification
    (D : A.CoherentQuotientDatum phi)
    (hi : (i.precompFunctor Z).IsEquivalence) :
    ∃ chi : Q ⥤ᵇ Z,
      Nonempty (phi ≅ (A.quotientMap.comp i).comp chi) := by
  letI : (i.precompFunctor Z).IsEquivalence := hi
  obtain ⟨chi, ⟨alpha⟩⟩ := Functor.EssSurj.mem_essImage
    (i.precompFunctor Z) (descend A phi D)
  refine ⟨chi, ⟨?_⟩⟩
  let gamma := BasedCategory.whiskerLeftIso A.quotientMap alpha
  exact (descendIso A phi D).trans gamma.symm

end CategoryTheory.PresheafAction.CoherentQuotientDatum

end ExerActionQuotientCategoricalAmongStacks
