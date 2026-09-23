module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.3-morphisms-gluing-epimorphisms»
public import StacksAndModuli.API.PseudofunctorCore
public import StacksAndModuli.API.PseudofunctorStack
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.ArrowCartesianZariskiStack
public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# First examples of stacks

This module formalizes `ex:stack-of-sheaves`, `ex:stack-of-schemes` and the related
material of the subsection "First examples of stacks" of §3.5 (Stacks) of *Stacks and
Moduli*, section label `sec:stacks` (the
subsection carries no label of its own). Formalization state per label: see this
folder's STATUS.md.

Main results:
- `CategoryTheory.Functor.isStack_proj_yoneda_iff`: for a presheaf `F`, the associated
  prestack is a stack if and only if `F` is a sheaf (the unlabeled example "Sheaves and
  schemes as stacks"; both directions proved);
- `CategoryTheory.CartesianArrowHom` and `CategoryTheory.arrowCartesian`: the fibered
  category of morphisms of a category with pullbacks, where morphisms are cartesian
  squares — the prestack `\underline{Schemes}` of the book when instantiated at the
  category of schemes;
- `AlgebraicGeometry.Scheme.isStack_arrowCartesian_zariskiTopology`: **Example 3.5.12**
  (`ex:stack-of-schemes`), morphisms of schemes form a stack for the Zariski topology
  (statement; proof deferred);
- `CategoryTheory.GrothendieckTopology.isStack_core_pseudofunctorOver`: sheaves form the
  groupoid-valued stack of **Example 3.5.8** (`ex:stack-of-sheaves`).
- `AlgebraicGeometry.Scheme.Modules.isStack_core_quasicoherentPseudofunctor`:
  **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`), fpqc descent for the
  groupoid-valued quasi-coherent prestack, with its explicitly stated étale consequence;
- `AlgebraicGeometry.Scheme.Modules.isStack_core_coherentPseudofunctor`:
  the same fpqc stack theorem for finitely presented quasicoherent sheaves.
- `AlgebraicGeometry.Scheme.Modules.isStack_core_vectorBundlePseudofunctor`:
  the same fpqc stack theorem for finite locally free quasicoherent sheaves.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExStackOfSheaves

open CategoryTheory Functor Opposite

universe v u

namespace CategoryTheory.CostructuredArrow

variable {𝒮 : Type u} [Category.{v} 𝒮] {F : 𝒮ᵒᵖ ⥤ Type v}

/-- Let $F$ be a presheaf on a category $\cS$ and let $a = (S', \alpha)$ be an object of
the associated prestack lying over $S$ (i.e. with $S' = S$). The element of $F(S)$
classified by $a$ via the Yoneda lemma. -/
def yonedaElement (a : CostructuredArrow yoneda F) {S : 𝒮} (ha : a.left = S) :
    F.obj (op S) :=
  yonedaEquiv (yoneda.map (eqToHom ha.symm) ≫ a.hom)

/-- The element classified by `CostructuredArrow.mk η` is the element corresponding to
`η` under the Yoneda lemma. -/
@[simp]
lemma yonedaElement_mk {S : 𝒮} (η : yoneda.obj S ⟶ F) :
    (CostructuredArrow.mk η).yonedaElement rfl = yonedaEquiv η := by
  simp [yonedaElement]

/-- Two objects of the prestack of a presheaf lying over `S` and classifying the same
element of `F(S)` have equal structure morphisms (after transport). -/
lemma hom_eq_of_yonedaElement_eq {a b : CostructuredArrow yoneda F} {S : 𝒮}
    (ha : a.left = S) (hb : b.left = S)
    (h : a.yonedaElement ha = b.yonedaElement hb) :
    yoneda.map (eqToHom ha.symm) ≫ a.hom = yoneda.map (eqToHom hb.symm) ≫ b.hom :=
  yonedaEquiv.injective h

/-- Let $\psi \colon c \to a$ be a morphism of the prestack of a presheaf $F$ lying over
$g \colon T \to S$. Then the restriction along $g$ of the element classified by $a$ is
the element classified by $c$. -/
lemma map_op_yonedaElement {c a : CostructuredArrow yoneda F} {T S : 𝒮} {g : T ⟶ S}
    (ψ : c ⟶ a) (hlift : IsHomLift (CostructuredArrow.proj yoneda F) g ψ)
    (hc : c.left = T) (ha : a.left = S) :
    F.map g.op (a.yonedaElement ha) = c.yonedaElement hc := by
  have hfac : ψ.left = eqToHom hc ≫ g ≫ eqToHom ha.symm := by
    have h := IsHomLift.fac' (CostructuredArrow.proj yoneda F) g ψ
    exact h
  have hw := CostructuredArrow.w ψ
  simp only [yonedaElement]
  rw [yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  rw [← hw, hfac]
  simp

/-- Let $c, a$ be objects of the prestack of a presheaf $F$ over $T$ resp. $S$, and let
$g \colon T \to S$. If the element classified by $c$ is the restriction along $g$ of the
element classified by $a$, then there is a (unique) morphism $c \to a$ lying over $g$. -/
def homMkOfElementEq {c a : CostructuredArrow yoneda F} {T S : 𝒮} (g : T ⟶ S)
    (hc : c.left = T) (ha : a.left = S)
    (h : F.map g.op (a.yonedaElement ha) = c.yonedaElement hc) : c ⟶ a :=
  CostructuredArrow.homMk (eqToHom hc ≫ g ≫ eqToHom ha.symm) (by
    have h' : yoneda.map g ≫ yoneda.map (eqToHom ha.symm) ≫ a.hom =
        yoneda.map (eqToHom hc.symm) ≫ c.hom := by
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality]
      exact h
    calc yoneda.map (eqToHom hc ≫ g ≫ eqToHom ha.symm) ≫ a.hom
        = yoneda.map (eqToHom hc) ≫ yoneda.map g ≫ yoneda.map (eqToHom ha.symm) ≫
            a.hom := by simp
      _ = yoneda.map (eqToHom hc) ≫ yoneda.map (eqToHom hc.symm) ≫ c.hom := by rw [h']
      _ = c.hom := by simp [eqToHom_map])

/-- The morphism `CostructuredArrow.homMkOfElementEq` lies over `g`. -/
lemma homMkOfElementEq_isHomLift {c a : CostructuredArrow yoneda F} {T S : 𝒮}
    (g : T ⟶ S) (hc : c.left = T) (ha : a.left = S)
    (h : F.map g.op (a.yonedaElement ha) = c.yonedaElement hc) :
    IsHomLift (CostructuredArrow.proj yoneda F) g (homMkOfElementEq g hc ha h) := by
  apply IsHomLift.of_commSq (ha := hc) (hb := ha)
  constructor
  simp [homMkOfElementEq]

/-- Two morphisms of the prestack of a presheaf lying over the same morphism of the base
are equal: the prestack of a presheaf is fibered in sets. -/
lemma proj_yoneda_hom_ext {c d : CostructuredArrow yoneda F} {T S : 𝒮} (g : T ⟶ S)
    (ψ ψ' : c ⟶ d) (h : IsHomLift (CostructuredArrow.proj yoneda F) g ψ)
    (h' : IsHomLift (CostructuredArrow.proj yoneda F) g ψ') : ψ = ψ' := by
  have h1 : ψ.left = eqToHom (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ψ) ≫
      g ≫ eqToHom (IsHomLift.codomain_eq (CostructuredArrow.proj yoneda F) g ψ).symm := by
    exact IsHomLift.fac' (CostructuredArrow.proj yoneda F) g ψ
  have h2 : ψ'.left = eqToHom (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ψ') ≫
      g ≫ eqToHom (IsHomLift.codomain_eq (CostructuredArrow.proj yoneda F) g ψ').symm := by
    exact IsHomLift.fac' (CostructuredArrow.proj yoneda F) g ψ'
  ext
  rw [h1, h2]

end CategoryTheory.CostructuredArrow

/-- Result of the unlabeled "Sheaves and schemes as stacks" example opening the
subsection "First examples of stacks": let `F` be a presheaf on a site
`(𝒮, J)`. The prestack associated to `F` (the category of pairs `(S, a ∈ F(S))`, realized
as `CostructuredArrow yoneda F`, see Example 3.4.7) is a stack if and only
if `F` is a sheaf. Both directions are proved: separatedness of `F` glues morphisms and
the sheaf condition glues objects, and conversely the stack axioms yield amalgamations
and their uniqueness. See the Example 3.5.8 entry of this folder's
COMMENTARY.md for the attribution. -/
theorem CategoryTheory.Functor.isStack_proj_yoneda_iff {𝒮 : Type u} [Category.{v} 𝒮]
    (J : GrothendieckTopology 𝒮) (F : 𝒮ᵒᵖ ⥤ Type v) :
    (CostructuredArrow.proj yoneda F).IsStack J ↔ Presieve.IsSheaf J F := by
  constructor
  · intro hstack X R hR fam hcompat
    have hSC := hcompat.to_sieveCompatible
    have hcongr : ∀ {Y : 𝒮} {u v : Y ⟶ X} (_ : u = v) (hu : R.arrows u)
        (hv : R.arrows v), fam u hu = fam v hv := by
      intro Y u v huv hu hv
      subst huv
      rfl
    -- the descent functor associated to the compatible family
    let D : R.arrows.category ⥤ CostructuredArrow yoneda F :=
      { obj := fun f => CostructuredArrow.mk (yonedaEquiv.symm (fam f.obj.hom f.property))
        map := fun {f₁ f₂} h => CostructuredArrow.homMk h.hom.left (by
          simp only [CostructuredArrow.mk_hom_eq_self]
          exact (yonedaEquiv_symm_naturality_left h.hom.left F
            (fam f₂.obj.hom f₂.property)).trans (congrArg yonedaEquiv.symm
              ((hSC f₂.obj.hom h.hom.left f₂.property).symm.trans
                (hcongr (Over.w h.hom) _ _))))
        map_id := fun f => by ext; simp
        map_comp := fun h₁ h₂ => by ext; simp }
    obtain ⟨a, ha, ε, hεlift, hεnat⟩ := hstack.exists_gluing_obj hR D (fun f => rfl)
      (fun {f₁ f₂} h => by
        apply IsHomLift.of_commSq (ha := rfl) (hb := rfl)
        constructor
        simp [D])
    have ha' : a.left = X := ha
    have hamalg : fam.IsAmalgamation (a.yonedaElement ha') := by
      intro T g hg
      have hres := CostructuredArrow.map_op_yonedaElement (ε (R.arrows.categoryMk g hg))
        (hεlift _) rfl ha'
      have hD2 : (D.obj (R.arrows.categoryMk g hg)).yonedaElement rfl = fam g hg := by
        simp [D]
      exact hres.trans hD2
    refine ⟨a.yonedaElement ha', hamalg, ?_⟩
    intro t' ht'
    -- compare the two candidate amalgamations via the morphism-gluing axiom
    have hprf : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ X⦄ (hg : R.arrows g) ⦃x : CostructuredArrow yoneda F⦄
        (ξ : x ⟶ CostructuredArrow.mk (yonedaEquiv.symm t'))
        (hξ : IsHomLift (CostructuredArrow.proj yoneda F) g ξ),
        F.map g.op (a.yonedaElement ha') =
          x.yonedaElement
            (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) := by
      intro T g hg x ξ hξ
      have h₁ := CostructuredArrow.map_op_yonedaElement ξ hξ
        (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) rfl
      have h₂ : (CostructuredArrow.mk (yonedaEquiv.symm t')).yonedaElement rfl = t' := by
        simp
      exact (hamalg g hg).trans ((ht' g hg).symm.trans
        ((congrArg _ h₂.symm).trans h₁))
    obtain ⟨Φ, ⟨hΦlift, -⟩, -⟩ := hstack.existsUnique_gluing_hom hR
      (a := CostructuredArrow.mk (yonedaEquiv.symm t')) (b := a) rfl ha
      (fun T g hg x ξ hξ => CostructuredArrow.homMkOfElementEq g
        (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) ha'
        (hprf hg ξ hξ))
      (fun T g hg x ξ hξ => CostructuredArrow.homMkOfElementEq_isHomLift g
        (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) ha'
        (hprf hg ξ hξ))
      (fun T' T g hg h x' x χ ξ hξ hχ => by
        refine CostructuredArrow.proj_yoneda_hom_ext (h ≫ g) _ _
          (CostructuredArrow.homMkOfElementEq_isHomLift (h ≫ g)
            (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) (h ≫ g) (χ ≫ ξ))
            ha' (hprf (R.downward_closed hg h) (χ ≫ ξ) inferInstance)) ?_
        haveI := CostructuredArrow.homMkOfElementEq_isHomLift g
          (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) ha'
          (hprf hg ξ hξ)
        exact IsHomLift.comp (p := CostructuredArrow.proj yoneda F) h g χ
          (CostructuredArrow.homMkOfElementEq g
            (IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ) ha'
            (hprf hg ξ hξ)))
    have hfinal := CostructuredArrow.map_op_yonedaElement Φ hΦlift rfl ha'
    simpa using hfinal.symm
  · intro hF
    constructor
    · -- morphisms glue: separatedness of `F`
      intro S R hR a b ha hb φ hφlift hφcompat
      have hagree : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄, R g →
          F.map g.op (a.yonedaElement ha) = F.map g.op (b.yonedaElement hb) := by
        intro T g hg
        -- the canonical lift of `g` with target `a`
        have hx : (CostructuredArrow.mk
            (yoneda.map g ≫ yoneda.map (eqToHom ha.symm) ≫ a.hom)).left = T := rfl
        have hwξ : yoneda.map (g ≫ eqToHom ha.symm) ≫ a.hom =
            yoneda.map g ≫ yoneda.map (eqToHom ha.symm) ≫ a.hom := by
          simp
        set ξ : CostructuredArrow.mk (yoneda.map g ≫ yoneda.map (eqToHom ha.symm) ≫
            a.hom) ⟶ a :=
          CostructuredArrow.homMk (g ≫ eqToHom ha.symm) hwξ with hξdef
        have hξ : IsHomLift (CostructuredArrow.proj yoneda F) g ξ := by
          apply IsHomLift.of_commSq (ha := hx) (hb := ha)
          constructor
          simp [hξdef]
        have hm := hφlift hg ξ hξ
        rw [CostructuredArrow.map_op_yonedaElement (φ hg ξ hξ) hm hx hb,
          CostructuredArrow.map_op_yonedaElement ξ hξ hx ha]
      have hsep : a.yonedaElement ha = b.yonedaElement hb := by
        refine ((hF R hR).isSeparatedFor).ext ?_
        intro T g hg
        exact hagree hg
      have hkey := CostructuredArrow.hom_eq_of_yonedaElement_eq ha hb hsep
      have hwΦ : yoneda.map (eqToHom (ha.trans hb.symm)) ≫ b.hom = a.hom := by
        calc yoneda.map (eqToHom (ha.trans hb.symm)) ≫ b.hom
            = yoneda.map (eqToHom ha) ≫ yoneda.map (eqToHom hb.symm) ≫ b.hom := by
              simp [eqToHom_map]
          _ = yoneda.map (eqToHom ha) ≫ yoneda.map (eqToHom ha.symm) ≫ a.hom := by
              rw [hkey]
          _ = a.hom := by simp [eqToHom_map]
      refine ⟨CostructuredArrow.homMk (eqToHom (ha.trans hb.symm)) hwΦ, ⟨?_, ?_⟩, ?_⟩
      · apply IsHomLift.of_commSq (ha := ha) (hb := hb)
        constructor
        simp
      · intro T g hg x ξ hξ
        have hxT := IsHomLift.domain_eq (CostructuredArrow.proj yoneda F) g ξ
        refine CostructuredArrow.proj_yoneda_hom_ext g _ _ (hφlift hg ξ hξ) ?_
        have h1 : IsHomLift (CostructuredArrow.proj yoneda F) (𝟙 S)
            (CostructuredArrow.homMk (eqToHom (ha.trans hb.symm)) hwΦ : a ⟶ b) := by
          apply IsHomLift.of_commSq (ha := ha) (hb := hb)
          constructor
          simp
        have := IsHomLift.comp (p := CostructuredArrow.proj yoneda F) g (𝟙 S) ξ
          (CostructuredArrow.homMk (eqToHom (ha.trans hb.symm)) hwΦ)
        simpa using this
      · intro Φ' hΦ'
        refine CostructuredArrow.proj_yoneda_hom_ext (𝟙 S) _ _ hΦ'.1 ?_
        apply IsHomLift.of_commSq (ha := ha) (hb := hb)
        constructor
        simp
    · -- objects glue: the sheaf condition for `F`
      intro S R hR D hD hDlift
      set fam : Presieve.FamilyOfElements F R.arrows := fun T g hg =>
        (D.obj (R.arrows.categoryMk g hg)).yonedaElement (hD _) with hfam
      have hcompat : fam.Compatible := by
        rw [Presieve.compatible_iff_sieveCompatible]
        intro T Z f g hf
        have hmain := (CostructuredArrow.map_op_yonedaElement
          (D.map (⟨Over.homMk g⟩ :
            R.arrows.categoryMk (g ≫ f) (R.downward_closed hf g) ⟶
              R.arrows.categoryMk f hf))
          (hDlift _) (hD _) (hD _)).symm
        simp only [hfam]
        exact hmain
      obtain ⟨t, ht, -⟩ := (hF R hR) fam hcompat
      have hε : ∀ f : R.arrows.category,
          yoneda.map (eqToHom (hD f) ≫ f.obj.hom) ≫
            (CostructuredArrow.mk (yonedaEquiv.symm t)).hom = (D.obj f).hom := by
        intro f
        have hamalg : F.map f.obj.hom.op t = (D.obj f).yonedaElement (hD f) :=
          ht f.obj.hom f.property
        have hsymm : yoneda.map f.obj.hom ≫ yonedaEquiv.symm t =
            yoneda.map (eqToHom (hD f).symm) ≫ (D.obj f).hom := by
          rw [yonedaEquiv_symm_naturality_left, hamalg]
          simp only [CostructuredArrow.yonedaElement, Equiv.symm_apply_apply]
        simp only [CostructuredArrow.mk_hom_eq_self, yoneda.map_comp, Category.assoc,
          hsymm]
        simp
      refine ⟨CostructuredArrow.mk (yonedaEquiv.symm t), rfl,
        fun f => CostructuredArrow.homMk (eqToHom (hD f) ≫ f.obj.hom) (hε f), ?_, ?_⟩
      · intro f
        apply IsHomLift.of_commSq (ha := hD f) (hb := rfl)
        constructor
        simp
      · intro f g' h
        have hliftg' : IsHomLift (CostructuredArrow.proj yoneda F) g'.obj.hom
            (CostructuredArrow.homMk (eqToHom (hD g') ≫ g'.obj.hom) (hε g') :
              D.obj g' ⟶ CostructuredArrow.mk (yonedaEquiv.symm t)) := by
          apply IsHomLift.of_commSq (ha := hD g') (hb := rfl)
          constructor
          simp
        have hliftf : IsHomLift (CostructuredArrow.proj yoneda F) f.obj.hom
            (CostructuredArrow.homMk (eqToHom (hD f) ≫ f.obj.hom) (hε f) :
              D.obj f ⟶ CostructuredArrow.mk (yonedaEquiv.symm t)) := by
          apply IsHomLift.of_commSq (ha := hD f) (hb := rfl)
          constructor
          simp
        refine CostructuredArrow.proj_yoneda_hom_ext f.obj.hom _ _ ?_ hliftf
        have hcomp := IsHomLift.comp (p := CostructuredArrow.proj yoneda F)
          h.hom.left g'.obj.hom (D.map h)
          (CostructuredArrow.homMk (eqToHom (hD g') ≫ g'.obj.hom) (hε g') :
            D.obj g' ⟶ CostructuredArrow.mk (yonedaEquiv.symm t))
        rwa [show h.hom.left ≫ g'.obj.hom = f.obj.hom from Over.w h.hom] at hcomp

/- Background category-valued statement for Example 3.5.8: sheaves on a site glue — the pseudofunctor
`X ↦ Sheaf (J.over X) A` is a stack. This is
`CategoryTheory.GrothendieckTopology.isStack_pseudofunctorOver`, stated with
Exercise 3.3.10 in `part3.3.3-morphisms-gluing-epimorphisms`;
the book's example, stated for the big Zariski site of schemes, is an instance of this
general-site version (see COMMENTARY.md). Plain comment: `example`s cannot carry
docstrings. -/
example {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    (J.pseudofunctorOver (Type max u v)).IsStack J :=
  J.isStack_pseudofunctorOver

/-- **Example 3.5.8** (`ex:stack-of-sheaves`) (groupoid-valued form): taking the
pointwise core retains every sheaf and restricts morphisms to isomorphisms; this is the
stack of sheaves used in the book. -/
theorem CategoryTheory.GrothendieckTopology.isStack_core_pseudofunctorOver
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (J.pseudofunctorOver (Type max u v)).core.IsStack J := by
  letI : (J.pseudofunctorOver (Type max u v)).IsStack J :=
    J.isStack_pseudofunctorOver
  exact Pseudofunctor.core_isStack _

end ExStackOfSheaves

section ExStackOfSheaves

open CategoryTheory Functor Opposite CategoryTheory.BasedCategory

universe v₁ u₁

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {V : 𝒮}

/-- The morphism `T ⟶ V` classified by an object of the representable prestack `𝒮/V`
lying over `T`. (The analogue for `𝒮/V` of `CostructuredArrow.yonedaElement`.) -/
def overElt (a : Over V) {T : 𝒮} (ha : a.left = T) : T ⟶ V :=
  eqToHom ha.symm ≫ a.hom

@[simp]
lemma overElt_mk {T : 𝒮} (f : T ⟶ V) : overElt (Over.mk f) rfl = f := by
  simp [overElt]

/-- A morphism of `𝒮/V` lying over `g : T ⟶ S` exhibits the morphism classified by its
source as the restriction along `g` of the morphism classified by its target. -/
lemma map_overElt {c a : Over V} {T S : 𝒮} {g : T ⟶ S} (ψ : c ⟶ a)
    (hlift : IsHomLift (Over.forget V) g ψ) (hc : c.left = T) (ha : a.left = S) :
    g ≫ overElt a ha = overElt c hc := by
  have hfac : ψ.left = eqToHom hc ≫ g ≫ eqToHom ha.symm := by
    have h := IsHomLift.fac' (Over.forget V) g ψ
    exact h
  have hw : ψ.left ≫ a.hom = c.hom := Over.w ψ
  simp only [overElt]
  rw [← hw, hfac]
  simp

/-- The representable prestack `𝒮/V` is fibered in sets: two morphisms lying over the
same morphism of the base are equal. -/
lemma over_hom_ext {c d : Over V} {T S : 𝒮} (g : T ⟶ S) (ψ ψ' : c ⟶ d)
    (h : IsHomLift (Over.forget V) g ψ) (h' : IsHomLift (Over.forget V) g ψ') : ψ = ψ' := by
  have h1 : ψ.left = eqToHom (IsHomLift.domain_eq (Over.forget V) g ψ) ≫
      g ≫ eqToHom (IsHomLift.codomain_eq (Over.forget V) g ψ).symm :=
    IsHomLift.fac' (Over.forget V) g ψ
  have h2 : ψ'.left = eqToHom (IsHomLift.domain_eq (Over.forget V) g ψ') ≫
      g ≫ eqToHom (IsHomLift.codomain_eq (Over.forget V) g ψ').symm :=
    IsHomLift.fac' (Over.forget V) g ψ'
  ext
  rw [h1, h2]

/-- Helper lemma for the unlabeled example "Sheaves and schemes as
stacks", first stack axiom for `𝒮/V`): morphisms of the representable prestack `𝒮/V`
glue along covering sieves. Only the separatedness of `Mor(-, V)` is used. -/
theorem existsUnique_gluing_hom_overBased (J : GrothendieckTopology 𝒮) (V : 𝒮)
    (hV : Presieve.IsSheaf J (yoneda.obj V)) :
    ∀ {S : 𝒮} {R : Sieve S}, R ∈ J S →
    ∀ {a b : Over V}, (Over.forget V).obj a = S → (Over.forget V).obj b = S →
    ∀ (φ : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄, R g → ∀ ⦃x : Over V⦄ (ξ : x ⟶ a),
        IsHomLift (Over.forget V) g ξ → (x ⟶ b)),
      (∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Over V⦄ (ξ : x ⟶ a)
          (hξ : IsHomLift (Over.forget V) g ξ),
        IsHomLift (Over.forget V) g (φ hg ξ hξ)) →
      (∀ ⦃T' T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃h : T' ⟶ T⦄ ⦃x' x : Over V⦄ (χ : x' ⟶ x)
        (ξ : x ⟶ a) (hξ : IsHomLift (Over.forget V) g ξ)
        (_hχ : IsHomLift (Over.forget V) h χ),
        φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) →
      ∃! Φ : a ⟶ b, IsHomLift (Over.forget V) (𝟙 S) Φ ∧
        ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Over V⦄ (ξ : x ⟶ a)
          (hξ : IsHomLift (Over.forget V) g ξ), φ hg ξ hξ = ξ ≫ Φ := by
  intro S R hR a b ha hb φ hφlift _hφcompat
  have hagree : ∀ ⦃T : 𝒮⦄ ⦃g : T ⟶ S⦄, R g →
      (yoneda.obj V).map g.op (overElt a ha) = (yoneda.obj V).map g.op (overElt b hb) := by
    intro T g hg
    have hx : (Over.mk (g ≫ overElt a ha)).left = T := rfl
    set ξ : Over.mk (g ≫ overElt a ha) ⟶ a :=
      Over.homMk (g ≫ eqToHom ha.symm) (by simp [overElt]) with hξdef
    have hξ : IsHomLift (Over.forget V) g ξ := by
      apply IsHomLift.of_commSq (ha := hx) (hb := ha)
      constructor
      simp [hξdef]
    have hm := hφlift hg ξ hξ
    have e1 := map_overElt (φ hg ξ hξ) hm hx hb
    have e2 := map_overElt ξ hξ hx ha
    show g ≫ overElt a ha = g ≫ overElt b hb
    exact e2.trans e1.symm
  have hsep : overElt a ha = overElt b hb := by
    refine ((hV R hR).isSeparatedFor).ext ?_
    intro T g hg
    exact hagree hg
  have hwΦ : eqToHom (ha.trans hb.symm) ≫ b.hom = a.hom := by
    have hs : eqToHom ha.symm ≫ a.hom = eqToHom hb.symm ≫ b.hom := hsep
    calc eqToHom (ha.trans hb.symm) ≫ b.hom
        = eqToHom ha ≫ eqToHom hb.symm ≫ b.hom := by simp
      _ = eqToHom ha ≫ eqToHom ha.symm ≫ a.hom := by rw [hs]
      _ = a.hom := by simp
  refine ⟨Over.homMk (eqToHom (ha.trans hb.symm)) hwΦ, ⟨?_, ?_⟩, ?_⟩
  · apply IsHomLift.of_commSq (ha := ha) (hb := hb)
    constructor
    simp
  · intro T g hg x ξ hξ
    refine over_hom_ext g _ _ (hφlift hg ξ hξ) ?_
    have h1 : IsHomLift (Over.forget V) (𝟙 S)
        (Over.homMk (eqToHom (ha.trans hb.symm)) hwΦ : a ⟶ b) := by
      apply IsHomLift.of_commSq (ha := ha) (hb := hb)
      constructor
      simp
    have hcm := IsHomLift.comp (p := Over.forget V) g (𝟙 S) ξ
      (Over.homMk (eqToHom (ha.trans hb.symm)) hwΦ : a ⟶ b)
    simpa using hcm
  · intro Φ' hΦ'
    refine over_hom_ext (𝟙 S) _ _ hΦ'.1 ?_
    apply IsHomLift.of_commSq (ha := ha) (hb := hb)
    constructor
    simp

/-- Helper lemma for the unlabeled example "Sheaves and schemes as
stacks", second stack axiom for `𝒮/V`): objects of the representable prestack `𝒮/V`
glue along covering sieves. This is exactly the sheaf condition for `Mor(-, V)`. -/
theorem exists_gluing_obj_overBased (J : GrothendieckTopology 𝒮) (V : 𝒮)
    (hV : Presieve.IsSheaf J (yoneda.obj V)) :
    ∀ {S : 𝒮} {R : Sieve S}, R ∈ J S →
    ∀ (D : R.arrows.category ⥤ Over V),
      (∀ f : R.arrows.category, (Over.forget V).obj (D.obj f) = f.obj.left) →
      (∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g),
        IsHomLift (Over.forget V) h.hom.left (D.map h)) →
      ∃ (a : Over V) (_ : (Over.forget V).obj a = S)
        (ε : ∀ f : R.arrows.category, D.obj f ⟶ a),
        (∀ f : R.arrows.category, IsHomLift (Over.forget V) f.obj.hom (ε f)) ∧
        ∀ ⦃f g : R.arrows.category⦄ (h : f ⟶ g), D.map h ≫ ε g = ε f := by
  intro S R hR D hD hDlift
  set fam : Presieve.FamilyOfElements (yoneda.obj V) R.arrows := fun T g hg =>
    overElt (D.obj (R.arrows.categoryMk g hg)) (hD _) with hfam
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T Z f g hf
    have hmain := (map_overElt
      (D.map (⟨Over.homMk g⟩ :
        R.arrows.categoryMk (g ≫ f) (R.downward_closed hf g) ⟶
          R.arrows.categoryMk f hf))
      (hDlift _) (hD _) (hD _)).symm
    simp only [hfam]
    exact hmain
  obtain ⟨t, ht, -⟩ := (hV R hR) fam hcompat
  have hε : ∀ f : R.arrows.category,
      (eqToHom (hD f) ≫ f.obj.hom) ≫ (Over.mk t).hom = (D.obj f).hom := by
    intro f
    have hamalg : (yoneda.obj V).map f.obj.hom.op t = overElt (D.obj f) (hD f) :=
      ht f.obj.hom f.property
    have hamalg' : f.obj.hom ≫ t = eqToHom (hD f).symm ≫ (D.obj f).hom := hamalg
    show (eqToHom (hD f) ≫ f.obj.hom) ≫ t = (D.obj f).hom
    rw [Category.assoc, hamalg']
    simp
  refine ⟨Over.mk t, rfl, fun f => Over.homMk (eqToHom (hD f) ≫ f.obj.hom) (hε f), ?_, ?_⟩
  · intro f
    apply IsHomLift.of_commSq (ha := hD f) (hb := rfl)
    constructor
    simp
  · intro f g' h
    have hliftf : IsHomLift (Over.forget V) f.obj.hom
        (Over.homMk (eqToHom (hD f) ≫ f.obj.hom) (hε f) : D.obj f ⟶ Over.mk t) := by
      apply IsHomLift.of_commSq (ha := hD f) (hb := rfl)
      constructor
      simp
    have hliftg' : IsHomLift (Over.forget V) g'.obj.hom
        (Over.homMk (eqToHom (hD g') ≫ g'.obj.hom) (hε g') : D.obj g' ⟶ Over.mk t) := by
      apply IsHomLift.of_commSq (ha := hD g') (hb := rfl)
      constructor
      simp
    refine over_hom_ext f.obj.hom _ _ ?_ hliftf
    have hcomp := IsHomLift.comp (p := Over.forget V) h.hom.left g'.obj.hom (D.map h)
      (Over.homMk (eqToHom (hD g') ≫ g'.obj.hom) (hε g') : D.obj g' ⟶ Over.mk t)
    rwa [show h.hom.left ≫ g'.obj.hom = f.obj.hom from Over.w h.hom] at hcomp

/-- Result of the unlabeled example "Sheaves and schemes as
stacks"): the representable prestack `𝒮/V` is a stack for every topology `J` for which
the presheaf `Mor(-, V)` is a sheaf — in particular, by
`CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`, for every
subcanonical topology.

Stated for `BasedCategory.overBased V` rather than deduced from
`CategoryTheory.Functor.isStack_proj_yoneda_iff` at `F = Mor(-, V)`: the equivalence
`ofPresheafYonedaToOverBased V` is only an *equivalence* of based categories, and the
repo has no transport of `IsStack` along one (see the "`IsAlgebraicStack (overBased X)`
spine" entry of `Section4.1-Definitions/COMMENTARY.md`); the two axioms are cheaper
directly, because `𝒮/V` is fibered in sets. -/
theorem isStack_overBased (J : GrothendieckTopology 𝒮) (V : 𝒮)
    (hV : Presieve.IsSheaf J (yoneda.obj V)) : IsStack J (overBased V) where
  isFiberedInGroupoids := inferInstance
  isStack :=
    { existsUnique_gluing_hom := existsUnique_gluing_hom_overBased J V hV
      exists_gluing_obj := exists_gluing_obj_overBased J V hV }

end CategoryTheory.BasedCategory

end ExStackOfSheaves

section ExStackOfQuasiCoherentSheaves

open CategoryTheory AlgebraicGeometry

universe u

/- Background category-valued statement for Example 3.5.9:
fpqc descent for quasi-coherent sheaves says that the pseudofunctor
`X ↦ QCoh(X)`, with arbitrary module morphisms in its fibres, is a stack.  This is the
scheme-level form of Proposition 3.1.4, recalled here. -/
example :
    Scheme.Modules.quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
  Scheme.Modules.isStack_quasicoherentPseudofunctor

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`): the prestack whose objects
over a scheme are quasi-coherent sheaves and whose fibrewise arrows are isomorphisms is
a stack for the fpqc topology (and hence for the fppf and étale topologies).  It is the
pointwise core of the category-valued quasi-coherent pseudofunctor. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_quasicoherentPseudofunctor :
    quasicoherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology := by
  letI : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_quasicoherentPseudofunctor
  exact Pseudofunctor.core_isStack _

/-- Supporting fppf consequence of Example 3.5.9. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_quasicoherentPseudofunctor_fppf :
    quasicoherentPseudofunctor.{u}.core.IsStack Scheme.fppfTopology := by
  letI : quasicoherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_quasicoherentPseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.fppfTopology_le_fpqcTopology

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`) (étale consequence). -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_quasicoherentPseudofunctor_etale :
    quasicoherentPseudofunctor.{u}.core.IsStack Scheme.etaleTopology := by
  letI : quasicoherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_quasicoherentPseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.etaleTopology_le_fpqcTopology

/-- Background category-valued statement for Example 3.5.9 (coherent sheaves,
category-valued form): finitely presented quasicoherent sheaves and arbitrary morphisms
form an fpqc stack. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_coherentPseudofunctor :
    coherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology := by
  letI : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_quasicoherentPseudofunctor
  exact finitePresentationProperty.fullsubcategory_isStack

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`) (coherent sheaves):
the prestack of finitely presented quasicoherent sheaves with fibrewise isomorphisms
is an fpqc stack. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_coherentPseudofunctor :
    coherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology := by
  letI : coherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_coherentPseudofunctor
  exact Pseudofunctor.core_isStack _

/-- Supporting fppf consequence of Example 3.5.9 (coherent sheaves). -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_coherentPseudofunctor_fppf :
    coherentPseudofunctor.{u}.core.IsStack Scheme.fppfTopology := by
  letI : coherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_coherentPseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.fppfTopology_le_fpqcTopology

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`) (coherent sheaves,
étale consequence). -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_coherentPseudofunctor_etale :
    coherentPseudofunctor.{u}.core.IsStack Scheme.etaleTopology := by
  letI : coherentPseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_coherentPseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.etaleTopology_le_fpqcTopology

/-- Background category-valued statement for Example 3.5.9 (vector bundles,
category-valued form): finite locally free quasicoherent sheaves and arbitrary
morphisms form an fpqc stack. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_vectorBundlePseudofunctor :
    vectorBundlePseudofunctor.{u}.IsStack Scheme.fpqcTopology := by
  letI : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_quasicoherentPseudofunctor
  exact finiteLocallyFreeProperty.fullsubcategory_isStack

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`) (vector bundles):
the prestack of finite locally free quasicoherent sheaves with fibrewise
isomorphisms is an fpqc stack. -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_vectorBundlePseudofunctor :
    vectorBundlePseudofunctor.{u}.core.IsStack Scheme.fpqcTopology := by
  letI : vectorBundlePseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_vectorBundlePseudofunctor
  exact Pseudofunctor.core_isStack _

/-- Supporting fppf consequence of Example 3.5.9 (vector bundles). -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_vectorBundlePseudofunctor_fppf :
    vectorBundlePseudofunctor.{u}.core.IsStack Scheme.fppfTopology := by
  letI : vectorBundlePseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_vectorBundlePseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.fppfTopology_le_fpqcTopology

/-- **Example 3.5.9** (`ex:stack-of-quasi-coherent-sheaves`) (vector bundles,
étale consequence). -/
theorem AlgebraicGeometry.Scheme.Modules.isStack_core_vectorBundlePseudofunctor_etale :
    vectorBundlePseudofunctor.{u}.core.IsStack Scheme.etaleTopology := by
  letI : vectorBundlePseudofunctor.{u}.core.IsStack Scheme.fpqcTopology :=
    isStack_core_vectorBundlePseudofunctor
  exact Pseudofunctor.IsStack.of_le Scheme.etaleTopology_le_fpqcTopology

end ExStackOfQuasiCoherentSheaves

section ExStackOfSchemes

open CategoryTheory Functor Limits

universe v u

variable {C : Type u} [Category.{v} C]

/- Background definitions for Example 3.5.12:
`CategoryTheory.ArrowCartesian`, `CategoryTheory.CartesianArrowHom`, and
`CategoryTheory.arrowCartesian` package arrows and cartesian squares as a category
fibered in groupoids.  Their reusable definitions and prestack proof live in
`StacksAndModuli.API.ArrowCartesian`. -/

/-- **Example 3.5.12** (`ex:stack-of-schemes`): the stack of schemes in the Zariski
topology — schemes glue in the Zariski topology, so the fibered category of morphisms of
schemes is a stack over `Sch_Zar`. (It is *not* a stack over `Sch_ét`; see
Example 3.1.16.) -/
theorem AlgebraicGeometry.Scheme.isStack_arrowCartesian_zariskiTopology :
    (arrowCartesian AlgebraicGeometry.Scheme.{u}).p.IsStack
      AlgebraicGeometry.Scheme.zariskiTopology := by
  exact AlgebraicGeometry.Scheme.ArrowCartesianZariski.isStack

end ExStackOfSchemes
