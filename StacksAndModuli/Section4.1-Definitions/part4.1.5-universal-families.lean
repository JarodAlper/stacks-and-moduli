module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.4-algebraicity-of-mg»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.7-universal-family»
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.6-stackification»

/-!
# Universal families and the generalized 2-Yoneda lemma

This module formalizes **Lemma 4.1.27** (`lem:generalized-2-yoneda-lemma`),
**Definition 4.1.29** (`def:universal-family-over-algebraic-stack`), and the subsequent
unlabeled pullback exercise, from the subsection "Universal families" (Section 4.1.7,
`sec:universal-families`) of §4.1
(Definitions of algebraic spaces and stacks) of *Stacks and Moduli*,
section label `sec:algebraic-spaces-and-stacks`.

For a morphism of prestacks `q : 𝒬 ⥤ᵇ 𝒯` (a presentation) and a prestack `𝒳`, the
category of descent data `CategoryTheory.BasedCategory.DescentData q 𝒳` has objects the
pairs `(a, α)` of a morphism `a : 𝒬 ⥤ᵇ 𝒳` and a 2-isomorphism `α : p₁^* a ≅ p₂^* a` over
`𝒬 ×_𝒯 𝒬` satisfying the cocycle condition over `𝒬 ×_𝒯 𝒬 ×_𝒯 𝒬` (stated componentwise via
the pair projections `CategoryTheory.BasedCategory.FiberProductObj.pair₂₃`/`pair₁₃`).

Main book results:
- `CategoryTheory.BasedCategory.toDescentData`: **Equation 4.1.28**
  (`eqn:generalized-yoneda-2-lemma`), the restriction functor
  `(𝒯 ⥤ᵇ 𝒳) ⥤ DescentData q 𝒳`;
- `AlgebraicGeometry.isEquivalence_toDescentData_of_representableWith`: **Lemma 4.1.27**
  (`lem:generalized-2-yoneda-lemma`), the restriction functor is an equivalence when `𝒳`
  is a stack and `q` is a smooth presentation of an algebraic stack (statement only; the
  proof is a `sorry`, as are two coherence obligations in
  `CategoryTheory.BasedCategory.restrictionDescentIso`);
- `CategoryTheory.BasedCategory.universalFamily`: **Definition 4.1.29**
  (`def:universal-family-over-algebraic-stack`), the universal family of an algebraic
  stack, taken on the `MOR(𝒳, 𝒳)` side of the equivalence as the identity morphism; its
  pullback along any `f` recovers the object classified by `f` (the unlabeled pullback
  exercise, recalled by `example`s).
- `AlgebraicGeometry.Scheme.universalFamilyMg` and
  `AlgebraicGeometry.Scheme.universalFamilyMgFiberEquiv`: **Example 4.1.31**
  (`ex:universal-family-mg`), the universal family `𝒰_g = ℳ_{g,1} → ℳ_g` and its fibers.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section LemGeneralized2YonedaLemma

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒬 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒯 : BasedCategory.{v₃, u₃} 𝒮}

/-- Let $q \colon \cQ \to \cT$ be a morphism of prestacks over a category $\cS$. The
*triple self-fiber product* $\cQ \times_{\cT} \cQ \times_{\cT} \cQ$, realized as
$(\cQ \times_{\cT} \cQ) \times_{\cT} \cQ$ where the first factor maps to $\cT$ through
the second projection. -/
abbrev selfFiberProductTriple (q : 𝒬 ⥤ᵇ 𝒯) : BasedCategory 𝒮 :=
  fiberProduct ((fiberProductSnd q q).comp q) q

variable {q : 𝒬 ⥤ᵇ 𝒯}

/-- The (2,3)-pair of an object of the triple self-fiber product
$\cQ \times_{\cT} \cQ \times_{\cT} \cQ$: the object of $\cQ \times_{\cT} \cQ$ formed by
the second and third components with their comparison isomorphism. -/
@[simps]
def FiberProductObj.pair₂₃ (t : FiberProductObj ((fiberProductSnd q q).comp q) q) :
    FiberProductObj q q where
  fst := t.fst.snd
  snd := t.snd
  over_eq := t.over_eq.trans t.fst.over_eq.symm
  iso := t.iso
  isHomLift := by
    have h := t.isHomLift
    rwa [show (fiberProduct q q).p.obj t.fst = 𝒬.p.obj t.fst.snd from t.fst.over_eq.symm]
      at h

/-- The (1,3)-pair of an object of the triple self-fiber product
$\cQ \times_{\cT} \cQ \times_{\cT} \cQ$: the object of $\cQ \times_{\cT} \cQ$ formed by
the first and third components, with the composite comparison isomorphism. -/
@[simps]
def FiberProductObj.pair₁₃ (t : FiberProductObj ((fiberProductSnd q q).comp q) q) :
    FiberProductObj q q where
  fst := t.fst.fst
  snd := t.snd
  over_eq := t.over_eq
  iso := t.fst.iso ≪≫ t.iso
  isHomLift := by
    haveI h₂ : IsHomLift 𝒯.p (𝟙 (𝒬.p.obj t.fst.fst)) t.iso.hom := t.isHomLift
    simp only [Iso.trans_hom]
    have h := IsHomLift.comp (p := 𝒯.p) (𝟙 (𝒬.p.obj t.fst.fst)) (𝟙 (𝒬.p.obj t.fst.fst))
      t.fst.iso.hom t.iso.hom
    simpa using h

variable (q) in
/-- Let $q \colon \cQ \to \cT$ be a morphism of prestacks and let
$a \colon \cQ \to \cX$ be a morphism to a prestack $\cX$. A 2-morphism
$\alpha \colon p_1^* a \to p_2^* a$ over $\cQ \times_{\cT} \cQ$ evaluated at an object
$z = (z_1, z_2, \gamma)$, viewed as a morphism $a(z_1) \to a(z_2)$ in $\cX$. -/
def descentComparisonApp {𝒳 : BasedCategory.{v₄, u₄} 𝒮} {a : 𝒬 ⥤ᵇ 𝒳}
    (α : (fiberProductFst q q).comp a ⟶ (fiberProductSnd q q).comp a)
    (z : FiberProductObj q q) : a.obj z.fst ⟶ a.obj z.snd :=
  α.toNatTrans.app z

variable (q) in
/-- Background definition for Lemma 4.1.27 (the implicit definition of the
category $\cX(\cT)$): let $q \colon \cQ \to \cT$ be a morphism of prestacks over $\cS$
and let $\cX$ be a
prestack over $\cS$. A *descent datum* on $\cX$ along $q$ is a pair $(a, \alpha)$ of a
morphism $a \colon \cQ \to \cX$ and a 2-isomorphism $\alpha \colon p_1^* a \cong p_2^* a$
over $\cQ \times_{\cT} \cQ$ satisfying the cocycle condition
$p_{23}^* \alpha \circ p_{12}^* \alpha = p_{13}^* \alpha$ over
$\cQ \times_{\cT} \cQ \times_{\cT} \cQ$ (stated componentwise). For an algebraic stack
$\cT$ with presentation $U \to \cT$ this is the category denoted $\cX(\cT)$ in the book;
the formalization allows an arbitrary morphism of prestacks $q$ (see this folder's
COMMENTARY.md). -/
structure DescentData (𝒳 : BasedCategory.{v₄, u₄} 𝒮) where
  /-- The underlying morphism of prestacks `𝒬 ⥤ᵇ 𝒳`. -/
  obj : 𝒬 ⥤ᵇ 𝒳
  /-- The comparison 2-isomorphism `p₁^* a ≅ p₂^* a` over `𝒬 ×_𝒯 𝒬`. -/
  iso : (fiberProductFst q q).comp obj ≅ (fiberProductSnd q q).comp obj
  /-- The cocycle condition over `𝒬 ×_𝒯 𝒬 ×_𝒯 𝒬`, stated componentwise. -/
  cocycle : ∀ t : FiberProductObj ((fiberProductSnd q q).comp q) q,
    descentComparisonApp q iso.hom t.fst ≫ descentComparisonApp q iso.hom t.pair₂₃ =
      descentComparisonApp q iso.hom t.pair₁₃

namespace DescentData

variable {𝒳 : BasedCategory.{v₄, u₄} 𝒮}

/-- Background definition for Lemma 4.1.27 (the implicit definition of the
morphisms of $\cX(\cT)$): a morphism of descent data $(a, \alpha) \to (b, \beta)$ along
$q$ is a 2-morphism
$a \to b$ compatible with the comparison isomorphisms. -/
@[ext]
structure Hom (D E : DescentData q 𝒳) where
  /-- The underlying 2-morphism of based functors. -/
  hom : D.obj ⟶ E.obj
  /-- Compatibility with the comparison isomorphisms, stated componentwise. -/
  w : ∀ z : FiberProductObj q q,
    descentComparisonApp q D.iso.hom z ≫ hom.toNatTrans.app z.snd =
      hom.toNatTrans.app z.fst ≫ descentComparisonApp q E.iso.hom z := by cat_disch

/-- The composition of two morphisms of descent data satisfies the compatibility with
the comparison isomorphisms. -/
lemma Hom.comp_w {D E F : DescentData q 𝒳} (φ : Hom D E) (ψ : Hom E F)
    (z : FiberProductObj q q) :
    descentComparisonApp q D.iso.hom z ≫
        (φ.hom ≫ ψ.hom).toNatTrans.app z.snd =
      (φ.hom ≫ ψ.hom).toNatTrans.app z.fst ≫ descentComparisonApp q F.iso.hom z := by
  have h : ∀ x, (φ.hom ≫ ψ.hom).toNatTrans.app x =
      φ.hom.toNatTrans.app x ≫ ψ.hom.toNatTrans.app x := fun x => rfl
  rw [h, h, ← Category.assoc, φ.w z, Category.assoc, ψ.w z, ← Category.assoc]

instance : Category (DescentData q 𝒳) where
  Hom D E := Hom D E
  id D := { hom := 𝟙 D.obj, w := fun z => by simp [descentComparisonApp] }
  comp φ ψ := { hom := φ.hom ≫ ψ.hom, w := φ.comp_w ψ }
  id_comp φ := by
    apply Hom.ext
    exact Category.id_comp φ.hom
  comp_id φ := by
    apply Hom.ext
    exact Category.comp_id φ.hom
  assoc φ ψ χ := by
    apply Hom.ext
    exact Category.assoc φ.hom ψ.hom χ.hom

/-- The underlying 2-morphism of the identity of a descent datum is the identity. -/
@[simp]
lemma id_hom (D : DescentData q 𝒳) : Hom.hom (𝟙 D) = 𝟙 D.obj :=
  rfl

/-- The underlying 2-morphism of a composition of morphisms of descent data is the
composition of the underlying 2-morphisms. -/
@[simp]
lemma comp_hom {D E F : DescentData q 𝒳} (φ : D ⟶ E) (ψ : E ⟶ F) :
    Hom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom :=
  rfl

end DescentData

variable (q) in
/-- Let `q : 𝒬 ⥤ᵇ 𝒯` be a morphism of prestacks and let `f : 𝒯 ⥤ᵇ 𝒳`. The canonical
comparison 2-isomorphism `p₁^*(q ∘ f) ≅ p₂^*(q ∘ f)` over `𝒬 ×_𝒯 𝒬`, with component the
image under `f` of the comparison isomorphism of the fiber product. -/
def restrictionDescentIso {𝒳 : BasedCategory.{v₄, u₄} 𝒮} (f : 𝒯 ⥤ᵇ 𝒳) :
    (fiberProductFst q q).comp (q.comp f) ≅ (fiberProductSnd q q).comp (q.comp f) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun z => f.toFunctor.mapIso z.iso) (fun {z z'} φ => by
      change f.toFunctor.map (q.toFunctor.map (FiberProductHom.fst φ)) ≫
          f.toFunctor.map z'.iso.hom =
        f.toFunctor.map z.iso.hom ≫
          f.toFunctor.map (q.toFunctor.map (FiberProductHom.snd φ))
      rw [← f.toFunctor.map_comp, ← f.toFunctor.map_comp, FiberProductHom.w]))
    (fun z => BasedFunctor.preserves_isHomLift f (𝟙 (𝒬.p.obj z.fst)) z.iso.hom)

/-- The component of the canonical comparison isomorphism of a restricted descent datum
at an object `z` of `𝒬 ×_𝒯 𝒬` is the image under `f` of the comparison isomorphism of
`z`. -/
@[simp]
lemma restrictionDescentIso_hom_app {𝒳 : BasedCategory.{v₄, u₄} 𝒮} (f : 𝒯 ⥤ᵇ 𝒳)
    (z : FiberProductObj q q) :
    (restrictionDescentIso q f).hom.toNatTrans.app z = f.toFunctor.map z.iso.hom :=
  rfl

variable (q) in
/-- **Equation 4.1.28** (`eqn:generalized-yoneda-2-lemma`) (the functor
`MOR(𝒯, 𝒳) → 𝒳(𝒯)`): restriction along a morphism of prestacks `q : 𝒬 ⥤ᵇ 𝒯` — the
functor sending a
morphism `f : 𝒯 ⥤ᵇ 𝒳` to the descent datum `(q ∘ f, canonical isomorphism)` on `𝒳` along
`q`, and a 2-morphism to its whiskering with `q`. -/
def toDescentData (𝒳 : BasedCategory.{v₄, u₄} 𝒮) :
    (𝒯 ⥤ᵇ 𝒳) ⥤ DescentData q 𝒳 where
  obj f :=
    { obj := q.comp f
      iso := restrictionDescentIso q f
      cocycle := fun t => by
        simp only [descentComparisonApp, restrictionDescentIso_hom_app,
          FiberProductObj.pair₂₃_iso, FiberProductObj.pair₁₃_iso, Iso.trans_hom]
        simp [← Functor.map_comp] }
  map {f g} η :=
    { hom := BasedCategory.whiskerLeft q η
      w := fun z => by
        simp only [descentComparisonApp, restrictionDescentIso_hom_app]
        exact η.toNatTrans.naturality z.iso.hom }
  map_id f := by
    apply DescentData.Hom.ext
    apply BasedNatTrans.homCategory.ext
    ext x
    simp
    rfl
  map_comp η θ := by
    apply DescentData.Hom.ext
    apply BasedNatTrans.homCategory.ext
    ext x
    simp

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.BasedCategory

/-- **Lemma 4.1.27** (`lem:generalized-2-yoneda-lemma`) (Generalized 2-Yoneda lemma): let
$\cX$ be a stack over $\Sch_{\ét}$, let $\cT$ be
an algebraic stack and let $q \colon \Sch/U \to \cT$ be a smooth presentation. Then
restriction along $q$ is an equivalence from $\MOR(\cT, \cX)$ to the category
$\cX(\cT)$ of descent data on $\cX$ along $q$. In particular $\cX(\cT)$ is independent
of the choice of presentation. -/
theorem isEquivalence_toDescentData_of_representableWith
    {𝒯 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒳 : BasedCategory.{v₃, u₃} Scheme.{u}}
    [IsAlgebraicStack 𝒯] [BasedCategory.IsStack Scheme.etaleTopology 𝒳] {U : Scheme.{u}}
    (q : overBased U ⥤ᵇ 𝒯)
    (hq : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) q) :
    (toDescentData q 𝒳).IsEquivalence := by
  sorry

end AlgebraicGeometry

end LemGeneralized2YonedaLemma

section DefUniversalFamilyOverAlgebraicStack

open CategoryTheory CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- **Definition 4.1.29** (`def:universal-family-over-algebraic-stack`): let $\cX$ be an
algebraic stack. Under the identification $\cX(\cT) = \MOR(\cT, \cX)$
of the generalized 2-Yoneda lemma, the *universal family over $\cX$* is the object of
$\cX(\cX)$ corresponding to the identity morphism $\operatorname{id} \colon \cX \to \cX$.
The formalization records it on the $\MOR(\cX, \cX)$ side of the equivalence, as the
identity morphism of any prestack (see this folder's COMMENTARY.md). -/
abbrev universalFamily (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ 𝒳 :=
  BasedFunctor.id 𝒳

/- Background examples for the unlabeled pullback exercise following Definition 4.1.29:
for a morphism `g : 𝒮' ⥤ᵇ 𝒯` of prestacks, the pullback functor
`g^* : 𝒳(𝒯) → 𝒳(𝒮')` is precomposition with `g` (this is
`CategoryTheory.BasedFunctor.precompFunctor` from §3.5); the pullback of the universal
family along a morphism `f : 𝒳' ⥤ᵇ 𝒳` is `f` itself, i.e. the object classified by
`f`. -/
example {𝒮' : BasedCategory.{v₂, u₂} 𝒮} {𝒯 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒳 : BasedCategory.{v₃, u₃} 𝒮} (g : 𝒮' ⥤ᵇ 𝒯) : (𝒯 ⥤ᵇ 𝒳) ⥤ (𝒮' ⥤ᵇ 𝒳) :=
  BasedFunctor.precompFunctor g 𝒳

example {𝒳' : BasedCategory.{v₂, u₂} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮} (f : 𝒳' ⥤ᵇ 𝒳) :
    (BasedFunctor.precompFunctor f 𝒳).obj (universalFamily 𝒳) =
      f.comp (universalFamily 𝒳) :=
  rfl

/- Relocation note for Example 4.1.31: it is formalized in its own section block
below; the universal family of `Bun_{r,d}(C)` (the universal vector bundle) is not, since
`Bun_{r,d}(C)` needs quasi-coherent sheaves on products — see the row for
`thm:bunC-is-algebraic` in this folder's STATUS.md. -/

end CategoryTheory.BasedCategory

end DefUniversalFamilyOverAlgebraicStack

section ExUniversalFamilyMg

open CategoryTheory CategoryTheory.BasedCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Background definition for Example 4.1.31 (the implicit definition of `ℳ_{g,1}`):
the prestack of `1`-pointed smooth curves of genus `g` — families of smooth curves of
genus `g` equipped with a section.

Exercise 3.4.42 (§3.4) built this for an abstract
base-change-stable genus class `Q`; here `Q` is `Scheme.genusProperty g`. -/
noncomputable abbrev moduliOfPointedCurves (g : ℕ) : BasedCategory Scheme.{u} :=
  pointedSmoothCurveSubprestack (genusProperty.{u} g)

/-- **Example 4.1.31** (`ex:universal-family-mg`): the universal family `𝒰_g → ℳ_g` is the
morphism `ℳ_{g,1} → ℳ_g` forgetting the marked point. -/
noncomputable def universalFamilyMg (g : ℕ) :
    moduliOfPointedCurves.{u} g ⥤ᵇ moduliOfCurves.{u} g :=
  forgetMarkedPoint (genusProperty.{u} g)

/-- **Example 4.1.31** (`ex:universal-family-mg`) (the cartesian square): for a family
`𝒞 → S` of smooth curves of genus `g` classified by a morphism `S → ℳ_g`, the sections of
the family pulled back along `T → S` correspond to lifts `T → 𝒞`.

This is the fibrewise content of the assertion that

```
𝒞  ⟶ 𝒰_g = ℳ_{g,1}
↓            ↓
S  ⟶ ℳ_g
```

is cartesian; it is Exercise 3.4.42's `universalFamilyFiberEquiv` specialized to the
concrete genus class. -/
noncomputable def universalFamilyMgFiberEquiv {g : ℕ} {C S T : Scheme.{u}} (f : C ⟶ S)
    (hf : smoothCurveGenusProperty.{u} g f) (q : T ⟶ S) :
    CategoryTheory.PullbackSection f q ≃ CategoryTheory.LiftOver f q :=
  universalFamilyFiberEquiv (Q := genusProperty.{u} g) f hf q

/-- Background definition for Example 4.1.31 (the implicit definition): a *family of
smooth curves of genus `g`* over a prestack `𝒯` is a morphism `𝒞 → 𝒯` representable by
schemes such that every base change by a scheme is a family of smooth curves of genus `g`.

The book asks for "representable by schemes, proper, flat, and finitely presented such
that for every geometric point `Spec k̄ → 𝒯` the fibre is a smooth, connected, projective
curve of genus `g`". Flatness and finite presentation are implied by smoothness, and the
fibrewise conditions are exactly `Scheme.smoothCurveGenusProperty g` on each base change,
so the single morphism property suffices; see this folder's COMMENTARY.md. -/
def IsFamilyOfSmoothCurvesOver (g : ℕ) {𝒞 𝒯 : BasedCategory.{u + 1, u + 1} Scheme.{u}}
    (F : 𝒞 ⥤ᵇ 𝒯) : Prop :=
  F.RelativelyRepresentableWith (smoothCurveGenusProperty.{u} g)

lemma IsFamilyOfSmoothCurvesOver.relativelyRepresentable {g : ℕ}
    {𝒞 𝒯 : BasedCategory.{u + 1, u + 1} Scheme.{u}} {F : 𝒞 ⥤ᵇ 𝒯}
    (h : IsFamilyOfSmoothCurvesOver g F) : F.RelativelyRepresentable :=
  h.1

end AlgebraicGeometry.Scheme

end ExUniversalFamilyMg
