module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.2-properties-of-spaces-and-stacks»
public import StacksAndModuli.API.CommonFieldExtension
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.NoetherianSpace
public import StacksAndModuli.API.OpenSubstackUnion
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.QuasiCompactSpecialization
public import StacksAndModuli.API.RepresentableWithComposition
public import StacksAndModuli.API.SurjectiveEtaleSourceLocal

/-!
# The topological space of a stack

This module formalizes `def:topology-of-stacks`, `exer:closed-subsets-and-substacks`,
`exer:surjective-equivalences`, `exer:fppf-morphisms-are-open`,
`exer:specialization-properties`, `def:quasi-compact` and the surrounding unlabeled
definitions and exercises of §4.3 (First properties) of *Stacks and Moduli*
(the section carries no `sec:` label). It
corresponds to the subsection "The topological space of a stack".

A *field-valued point* of a prestack `𝒳` over `Sch` is a field `K` together with a
morphism `overBased (Spec K) ⥤ᵇ 𝒳` of prestacks (this is the single spelling of
field-valued points used throughout): see
`AlgebraicGeometry.BasedCategory.FieldPoint`. Two field-valued points are equivalent
(`FieldPoint.Equiv`) if they become 2-isomorphic after a common field extension. The
topological space `|𝒳|` is the quotient `AlgebraicGeometry.BasedCategory.pointSpace 𝒳`,
topologized by declaring the point images of open substacks to be open
(`AlgebraicGeometry.BasedCategory.pointTopology`). Morphisms of prestacks act on points
via `AlgebraicGeometry.BasedFunctor.mapPoints`.

Quasi-compact, connected, and irreducible algebraic stacks are defined through `|𝒳|`
(`def:quasi-compact`); quasi-compact and finite type morphisms via base change to
affine schemes. The noetherian property of stacks is ledgered (it requires
quasi-separatedness, i.e. the §4.2 diagonal).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefTopologyOfStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Definition 4.3.17** (`def:topology-of-stacks`) (the implicit definition of a
field-valued point): a *field-valued point* of a prestack $\cX$ over $\Sch$ is a field
$K$ together with a morphism of prestacks $x \colon \Sch/\Spec K \to \cX$ (equivalently,
by the 2-Yoneda lemma, an object of $\cX$ over $\Spec K$). -/
structure FieldPoint (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) where
  /-- The coefficient field of the point. -/
  carrier : Type u
  /-- The field structure on the coefficient field. -/
  [instField : Field carrier]
  /-- The morphism of prestacks `Sch/Spec K ⥤ᵇ 𝒳` classifying the point. -/
  hom : overBased (Spec (CommRingCat.of carrier)) ⥤ᵇ 𝒳

attribute [instance] FieldPoint.instField

namespace FieldPoint

/-- The restriction of a field-valued point $x \colon \Spec K \to \cX$ along a field
extension $i \colon K \to L$: the composition
$\Spec L \to \Spec K \xrightarrow{x} \cX$. -/
noncomputable def restrict (x : FieldPoint 𝒳) {L : Type u} [Field L]
    (i : x.carrier →+* L) :
    overBased (Spec (CommRingCat.of L)) ⥤ᵇ 𝒳 :=
  (overBased.map (Spec.map (CommRingCat.ofHom i))).comp x.hom

/-- Restricting a field-valued point along a composite `K → L → M` of field extensions is
restricting first to `L` and then to `M`. (An equality, not merely an isomorphism, because
`𝒮/(-)` is functorial on the nose — `CategoryTheory.BasedCategory.overBased.map_comp`.) -/
lemma restrict_comp (x : FieldPoint 𝒳) {L M : Type u} [Field L] [Field M]
    (i : x.carrier →+* L) (j : L →+* M) :
    x.restrict (j.comp i) =
      (overBased.map (Spec.map (CommRingCat.ofHom j))).comp (x.restrict i) := by
  show (overBased.map (Spec.map (CommRingCat.ofHom (j.comp i)))).comp x.hom =
    (overBased.map (Spec.map (CommRingCat.ofHom j))).comp
      ((overBased.map (Spec.map (CommRingCat.ofHom i))).comp x.hom)
  rw [← BasedFunctor.comp_assoc, ← overBased.map_comp, ← Spec.map_comp]
  rfl

/-- Restricting a field-valued point along the identity of its coefficient field does
nothing. -/
lemma restrict_id (x : FieldPoint 𝒳) : x.restrict (RingHom.id x.carrier) = x.hom := by
  change (overBased.map (Spec.map (CommRingCat.ofHom (RingHom.id x.carrier)))).comp x.hom
    = x.hom
  rw [CommRingCat.ofHom_id, Spec.map_id,
    show overBased.map (𝟙 (Spec (CommRingCat.of x.carrier)))
      = CategoryTheory.BasedFunctor.id _ from
        CategoryTheory.BasedFunctor.ext_of_toFunctor_eq (Over.mapId_eq _)]
  rfl

/-- **Definition 4.3.17** (`def:topology-of-stacks`) (the identification of
field-valued points): two field-valued points $x_1 \colon \Spec K_1 \to \cX$ and
$x_2 \colon \Spec K_2 \to \cX$ are *equivalent* if there exist field extensions
$K_1 \to L$ and $K_2 \to L$ such that the restrictions $x_1|_{\Spec L}$ and
$x_2|_{\Spec L}$ are 2-isomorphic as morphisms $\Spec L \to \cX$. -/
def Equiv (x₁ x₂ : FieldPoint 𝒳) : Prop :=
  ∃ (L : Type u) (_ : Field L) (i₁ : x₁.carrier →+* L) (i₂ : x₂.carrier →+* L),
    Nonempty (x₁.restrict i₁ ≅ x₂.restrict i₂)

/-- The equivalence of field-valued points is reflexive. -/
lemma Equiv.refl (x : FieldPoint 𝒳) : Equiv x x :=
  ⟨x.carrier, inferInstance, RingHom.id _, RingHom.id _, ⟨Iso.refl _⟩⟩

/-- The equivalence of field-valued points is symmetric. -/
lemma Equiv.symm {x₁ x₂ : FieldPoint 𝒳} (h : Equiv x₁ x₂) : Equiv x₂ x₁ := by
  obtain ⟨L, hL, i₁, i₂, ⟨e⟩⟩ := h
  exact ⟨L, hL, i₂, i₁, ⟨e.symm⟩⟩

/-- The equivalence of field-valued points is transitive. (This is the detail omitted in
the book: given a common extension $L$ of $K_1, K_2$ and a common extension $L'$ of
$K_2, K_3$, the tensor product $L \otimes_{K_2} L'$ is a nonzero ring, hence has a
maximal ideal whose quotient is a common field extension of $L$ and $L'$ over $K_2$; the
two 2-isomorphisms restrict to this common extension and compose.) -/
lemma Equiv.trans {x₁ x₂ x₃ : FieldPoint 𝒳} (h₁ : Equiv x₁ x₂) (h₂ : Equiv x₂ x₃) :
    Equiv x₁ x₃ := by
  obtain ⟨L, hL, i₁, i₂, ⟨e⟩⟩ := h₁
  obtain ⟨L', hL', i₂', i₃, ⟨e'⟩⟩ := h₂
  obtain ⟨M, hM, j, j', hj⟩ := Field.exists_common_extension i₂ i₂'
  refine ⟨M, hM, j.comp i₁, j'.comp i₃, ⟨?_⟩⟩
  have E₁ : x₁.restrict (j.comp i₁) ≅ x₂.restrict (j.comp i₂) := by
    rw [restrict_comp, restrict_comp]
    exact isoWhiskerLeft _ e
  have E₂ : x₂.restrict (j'.comp i₂') ≅ x₃.restrict (j'.comp i₃) := by
    rw [restrict_comp, restrict_comp]
    exact isoWhiskerLeft _ e'
  rw [hj] at E₁
  exact E₁.trans E₂

/-- The image of a field-valued point of $\cX$ under a morphism of prestacks
$F \colon \cX \to \cY$: the composition $\Spec K \to \cX \to \cY$. -/
noncomputable def map (F : 𝒳 ⥤ᵇ 𝒴) (x : FieldPoint 𝒳) : FieldPoint 𝒴 where
  carrier := x.carrier
  hom := x.hom.comp F

/-- A field-valued point and its restriction along a field extension are equivalent: they
already agree over the larger field. -/
lemma equiv_restrict (x : FieldPoint 𝒳) {L : Type u} [Field L] (i : x.carrier →+* L) :
    Equiv ⟨L, x.restrict i⟩ x :=
  ⟨L, inferInstance, RingHom.id L, i, ⟨eqToIso (restrict_id ⟨L, x.restrict i⟩)⟩⟩

/-- Morphisms of prestacks preserve the equivalence of field-valued points. -/
lemma Equiv.map {x₁ x₂ : FieldPoint 𝒳} (h : Equiv x₁ x₂) (F : 𝒳 ⥤ᵇ 𝒴) :
    Equiv (x₁.map F) (x₂.map F) := by
  obtain ⟨L, hL, i₁, i₂, ⟨e⟩⟩ := h
  exact ⟨L, hL, i₁, i₂, ⟨CategoryTheory.BasedCategory.isoWhiskerRight e F⟩⟩

end FieldPoint

/-- **Definition 4.3.17** (`def:topology-of-stacks`) (the underlying set): the
*topological space* $|\cX|$ of a prestack $\cX$ over $\Sch$ is the set of field-valued
points of $\cX$ modulo the equivalence identifying two points that become 2-isomorphic
after a common field extension. (The topology is
`AlgebraicGeometry.BasedCategory.pointTopology`.) -/
def pointSpace (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :=
  Quot (FieldPoint.Equiv (𝒳 := 𝒳))

namespace pointSpace

/-- The point of $|\cX|$ determined by a field-valued point of $\cX$. -/
def mk (x : FieldPoint 𝒳) : pointSpace 𝒳 :=
  Quot.mk _ x

/-- Equivalent field-valued points determine the same point of $|\cX|$. -/
lemma sound {x₁ x₂ : FieldPoint 𝒳} (h : FieldPoint.Equiv x₁ x₂) : mk x₁ = mk x₂ :=
  Quot.sound h

/-- Every point of $|\cX|$ comes from a field-valued point of $\cX$. -/
lemma ind {motive : pointSpace 𝒳 → Prop} (h : ∀ x : FieldPoint 𝒳, motive (mk x)) :
    ∀ q : pointSpace 𝒳, motive q :=
  Quot.ind h

/-- Two field-valued points determine the same point of `|𝒳|` exactly when they are
equivalent. (The `Quot` is a quotient by a genuine equivalence relation — reflexivity,
symmetry and transitivity are `FieldPoint.Equiv.refl`, `.symm` and `.trans` — so no
transitive closure is needed.) -/
lemma mk_eq_mk_iff {x₁ x₂ : FieldPoint 𝒳} :
    mk x₁ = mk x₂ ↔ FieldPoint.Equiv x₁ x₂ :=
  ⟨fun h => (Equivalence.eqvGen_iff
      ⟨FieldPoint.Equiv.refl, FieldPoint.Equiv.symm, FieldPoint.Equiv.trans⟩).mp (Quot.eq.mp h),
    sound⟩

end pointSpace

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

open AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Background construction following Definition 4.3.17 (functoriality, from the unlabeled
sentence after the definition): the map $|\cX| \to |\cY|$ on topological spaces induced
by a morphism of prestacks $F \colon \cX \to \cY$, sending the class of a field-valued
point to the class of its composition with $F$. -/
noncomputable def mapPoints (F : 𝒳 ⥤ᵇ 𝒴) : pointSpace 𝒳 → pointSpace 𝒴 :=
  Quot.map (FieldPoint.map F) (fun _ _ h => h.map F)

/-- The map on points sends the class of a field-valued point to the class of its
image. -/
@[simp]
lemma mapPoints_mk (F : 𝒳 ⥤ᵇ 𝒴) (x : FieldPoint 𝒳) :
    mapPoints F (pointSpace.mk x) = pointSpace.mk (x.map F) :=
  rfl

/-- The map on points induced by the identity is the identity. -/
@[simp]
lemma mapPoints_id (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :
    mapPoints (BasedFunctor.id 𝒳) = id := by
  funext q
  induction q using pointSpace.ind with
  | _ x => rfl

/-- Two 2-isomorphic morphisms from the same field determine the same point. -/
lemma pointSpace.mk_eq_mk_of_iso {K : Type u} [Field K]
    {A B : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳} (e : A ≅ B) :
    pointSpace.mk (⟨K, A⟩ : FieldPoint 𝒳) = pointSpace.mk ⟨K, B⟩ :=
  pointSpace.sound ⟨K, inferInstance, RingHom.id K, RingHom.id K,
    ⟨eqToIso (FieldPoint.restrict_id ⟨K, A⟩) ≪≫ e ≪≫
      eqToIso (FieldPoint.restrict_id ⟨K, B⟩).symm⟩⟩

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **The point set of the intersection substack is the intersection of the point sets.**

Both inclusions avoid the 2-Yoneda lemma. For `⊆`, a point of the intersection substack
gives an object of `𝒳` lying in both fiber-essential images, and
`AlgebraicGeometry.exists_lift_of_fiberEssImage` turns each of those into an actual
factorization through `i₁` (resp. `i₂`). For `⊇`, pass to a common field extension
(`pointSpace.mk_eq_mk_iff`) and corestrict the resulting morphism to the full
sub-based-category. -/
theorem range_mapPoints_restrictι_inf {𝒰₁ 𝒰₂ : BasedCategory.{v₃, u₃} Scheme.{u}}
    (i₁ : 𝒰₁ ⥤ᵇ 𝒳) (i₂ : 𝒰₂ ⥤ᵇ 𝒳)
    [BasedFunctor.IsOpenSubstackInclusion i₁]
    [BasedFunctor.IsOpenSubstackInclusion i₂] :
    Set.range (BasedFunctor.mapPoints
        (𝒳.restrictι (i₁.fiberEssImage ⊓ i₂.fiberEssImage)))
      = Set.range (BasedFunctor.mapPoints i₁) ∩ Set.range (BasedFunctor.mapPoints i₂) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using pointSpace.ind with
    | _ x =>
      have h1 : i₁.fiberEssImage
          ((x.hom.comp (𝒳.restrictι (i₁.fiberEssImage ⊓ i₂.fiberEssImage))).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))) :=
        (x.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))).property.1
      have h2 : i₂.fiberEssImage
          ((x.hom.comp (𝒳.restrictι (i₁.fiberEssImage ⊓ i₂.fiberEssImage))).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))) :=
        (x.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))).property.2
      obtain ⟨H₁, ⟨e₁⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage i₁ _ _ h1
      obtain ⟨H₂, ⟨e₂⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage i₂ _ _ h2
      exact ⟨⟨pointSpace.mk ⟨x.carrier, H₁⟩,
          BasedFunctor.pointSpace.mk_eq_mk_of_iso e₁⟩,
        ⟨pointSpace.mk ⟨x.carrier, H₂⟩,
          BasedFunctor.pointSpace.mk_eq_mk_of_iso e₂⟩⟩
  · rintro ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩
    induction p₁ using pointSpace.ind with
    | _ x₁ =>
    induction p₂ using pointSpace.ind with
    | _ x₂ =>
    subst hp₁
    obtain ⟨L, hL, ψ₁, ψ₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp hp₂
    have hg1 : ∀ X, i₁.fiberEssImage (((FieldPoint.map i₁ x₁).restrict ψ₂).obj X) :=
      fun X => fiberEssImage_comp_obj i₁
        ((overBased.map (Spec.map (CommRingCat.ofHom ψ₂))).comp x₁.hom) X
    have hg2 : ∀ X, i₂.fiberEssImage (((FieldPoint.map i₁ x₁).restrict ψ₂).obj X) :=
      fun X => fiberEssImage_obj_of_iso i₂ e X
        (fiberEssImage_comp_obj i₂
          ((overBased.map (Spec.map (CommRingCat.ofHom ψ₁))).comp x₂.hom) X)
    refine ⟨pointSpace.mk ⟨L, corestrict ((FieldPoint.map i₁ x₁).restrict ψ₂)
      (i₁.fiberEssImage ⊓ i₂.fiberEssImage) (fun X => ⟨hg1 X, hg2 X⟩)⟩, ?_⟩
    change pointSpace.mk (⟨L, _⟩ : FieldPoint 𝒳) = _
    rw [corestrict_comp_restrictι]
    exact pointSpace.sound (FieldPoint.equiv_restrict (FieldPoint.map i₁ x₁) ψ₂)

/-- **The point set of the preimage substack is the preimage of the point set.**

Same two techniques as `range_mapPoints_restrictι_inf`:
`AlgebraicGeometry.exists_lift_of_fiberEssImage` for `⊆`, a common field extension and
`corestrict` for `⊇`. -/
theorem range_mapPoints_restrictι_comap {𝒱 : BasedCategory.{v₄, u₄} Scheme.{u}}
    (F : 𝒳 ⥤ᵇ 𝒴) (j : 𝒱 ⥤ᵇ 𝒴) [BasedFunctor.IsOpenSubstackInclusion j] :
    Set.range (BasedFunctor.mapPoints
        (𝒳.restrictι (fun a => j.fiberEssImage (F.obj a))))
      = BasedFunctor.mapPoints F ⁻¹' Set.range (BasedFunctor.mapPoints j) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using pointSpace.ind with
    | _ x =>
      have h1 : j.fiberEssImage
          (((x.hom.comp (𝒳.restrictι (fun a => j.fiberEssImage (F.obj a)))).comp F).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))) :=
        (x.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))).property
      obtain ⟨H, ⟨e⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage j _ _ h1
      exact ⟨pointSpace.mk ⟨x.carrier, H⟩, BasedFunctor.pointSpace.mk_eq_mk_of_iso e⟩
  · rintro ⟨p, hp⟩
    induction q using pointSpace.ind with
    | _ x =>
    induction p using pointSpace.ind with
    | _ y =>
    obtain ⟨L, hL, ψ₁, ψ₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp hp.symm
    have hg : ∀ X, j.fiberEssImage (F.obj ((x.restrict ψ₁).obj X)) := fun X =>
      fiberEssImage_obj_of_iso j e.symm X
        (fiberEssImage_comp_obj j
          ((overBased.map (Spec.map (CommRingCat.ofHom ψ₂))).comp y.hom) X)
    refine ⟨pointSpace.mk ⟨L, corestrict (x.restrict ψ₁)
      (fun a => j.fiberEssImage (F.obj a)) hg⟩, ?_⟩
    change pointSpace.mk (⟨L, _⟩ : FieldPoint 𝒳) = _
    rw [corestrict_comp_restrictι]
    exact pointSpace.sound (FieldPoint.equiv_restrict x ψ₁)

/-- **The point set of the covered substack is the union of the point sets.** -/
theorem range_mapPoints_restrictι_covered [𝒳.p.IsFiberedInGroupoids] {κ : Type w}
    {𝒰 : κ → BasedCategory.{v₃, u₃} Scheme.{u}} (i : ∀ k, 𝒰 k ⥤ᵇ 𝒳)
    [∀ k, BasedFunctor.IsOpenSubstackInclusion (i k)] :
    Set.range (BasedFunctor.mapPoints (𝒳.restrictι (coveredProperty i)))
      = ⋃ k, Set.range (BasedFunctor.mapPoints (i k)) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using pointSpace.ind with
    | _ x =>
      have hcov : coveredProperty i
          ((x.hom.comp (𝒳.restrictι (coveredProperty i))).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))) :=
        (x.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))).property
      have hlift : Functor.IsHomLift 𝒳.p
          (eqToHom ((x.hom.comp (𝒳.restrictι (coveredProperty i))).w_obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier))))).symm)
          (𝟙 ((x.hom.comp (𝒳.restrictι (coveredProperty i))).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of x.carrier)))))) := by
        refine IsHomLift.of_fac' 𝒳.p _ _
          ((x.hom.comp (𝒳.restrictι (coveredProperty i))).w_obj _) rfl ?_
        simp
      obtain ⟨k, hk⟩ := hcov x.carrier inferInstance _ _ _ hlift
      obtain ⟨H, ⟨e⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage (i k) _ _ hk
      exact Set.mem_iUnion.mpr ⟨k, pointSpace.mk ⟨x.carrier, H⟩,
        BasedFunctor.pointSpace.mk_eq_mk_of_iso e⟩
  · intro hq
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hq
    obtain ⟨p, hp⟩ := hk
    induction p using pointSpace.ind with
    | _ y =>
      refine ⟨pointSpace.mk ⟨y.carrier, corestrict (y.hom.comp (i k)) (coveredProperty i)
        (fun X => coveredProperty_comp i k _ y.hom X)⟩, ?_⟩
      change pointSpace.mk (⟨y.carrier, _⟩ : FieldPoint 𝒳) = _
      rw [corestrict_comp_restrictι]
      exact hp

/-- **Definition 4.3.17** (`def:topology-of-stacks`) (open subsets): a subset of
$|\cX|$ is *open* if it is the image of the points of an open substack
$\cU \subseteq \cX$. (The open substacks are quantified in the same universes as $\cX$;
see this folder's COMMENTARY.md.) -/
def IsOpenPointSet (V : Set (pointSpace 𝒳)) : Prop :=
  ∃ (𝒰 : BasedCategory.{v₂, u₂} Scheme.{u}) (i : 𝒰 ⥤ᵇ 𝒳),
    BasedFunctor.IsOpenSubstackInclusion i ∧ V = Set.range (BasedFunctor.mapPoints i)

variable (𝒳) in
/-- **Definition 4.3.17** (`def:topology-of-stacks`) (the topology): the Zariski-like
topology on the space $|\cX|$ of a prestack $\cX$ over $\Sch$: a subset is open if and
only if it is the image of the points of an open substack of $\cX$. (That this defines
a topology uses that $\cX$ is an open substack of itself, that the intersection of two
open substacks is the open substack given by their fiber product, and that a family of
open substacks has a union; these three facts are deferred.) -/
@[instance_reducible]
def pointTopology [𝒳.p.IsFiberedInGroupoids] : TopologicalSpace (pointSpace 𝒳) where
  IsOpen := IsOpenPointSet
  isOpen_univ := by
    refine ⟨𝒳, BasedFunctor.id 𝒳, inferInstance, ?_⟩
    rw [BasedFunctor.mapPoints_id, Set.range_id]
  isOpen_inter := by
    rintro V₁ V₂ ⟨𝒰₁, i₁, hi₁, rfl⟩ ⟨𝒰₂, i₂, hi₂, rfl⟩
    haveI := hi₁
    haveI := hi₂
    exact ⟨𝒳.restrict (i₁.fiberEssImage ⊓ i₂.fiberEssImage), 𝒳.restrictι _,
      isOpenSubstackInclusion_restrictι_inf i₁ i₂,
      (range_mapPoints_restrictι_inf i₁ i₂).symm⟩
  isOpen_sUnion := by
    intro S hS
    have hS' : ∀ t : ↥S, ∃ (𝒰 : BasedCategory.{v₂, u₂} Scheme.{u}) (j : 𝒰 ⥤ᵇ 𝒳),
        BasedFunctor.IsOpenSubstackInclusion j ∧
          (t : Set (pointSpace 𝒳)) = Set.range (BasedFunctor.mapPoints j) :=
      fun t => hS t t.2
    choose 𝒰 j hj hEq using hS'
    haveI : ∀ t, BasedFunctor.IsOpenSubstackInclusion (j t) := hj
    refine ⟨𝒳.restrict (coveredProperty j), 𝒳.restrictι _,
      isOpenSubstackInclusion_restrictι_covered j, ?_⟩
    rw [range_mapPoints_restrictι_covered j]
    ext q
    constructor
    · intro hq
      obtain ⟨t, htS, hqt⟩ := Set.mem_sUnion.mp hq
      refine Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ?_⟩
      rw [← hEq ⟨t, htS⟩]
      exact hqt
    · intro hq
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hq
      refine Set.mem_sUnion.mpr ⟨(t : Set (pointSpace 𝒳)), t.2, ?_⟩
      rw [hEq t]
      exact ht

/- The topology on `|𝒳|` is registered as a global instance: it is the canonical
topology of Definition 4.3.17 and `pointSpace` is an StacksAndModuli-local type, so no
diamonds can arise. -/
instance [𝒳.p.IsFiberedInGroupoids] : TopologicalSpace (pointSpace 𝒳) :=
  pointTopology 𝒳

/-- A subset of $|\cX|$ is open if and only if it is the image of the points of an open
substack of $\cX$ (restating Definition 4.3.17 for the registered topology instance). -/
lemma isOpen_pointSpace_iff [𝒳.p.IsFiberedInGroupoids] (V : Set (pointSpace 𝒳)) :
    IsOpen V ↔ ∃ (𝒰 : BasedCategory.{v₂, u₂} Scheme.{u}) (i : 𝒰 ⥤ᵇ 𝒳),
      BasedFunctor.IsOpenSubstackInclusion i ∧ V = Set.range (BasedFunctor.mapPoints i) :=
  Iff.rfl

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry

open AlgebraicGeometry.BasedCategory

/-- API theorem following Definition 4.3.17 (continuity, from the unlabeled
sentence after the definition): a morphism of algebraic stacks induces a continuous map
$|\cX| \to |\cY|$ on topological spaces. -/
theorem BasedFunctor.continuous_mapPoints {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}} [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
    (F : 𝒳 ⥤ᵇ 𝒴) : Continuous (BasedFunctor.mapPoints F) := by
  rw [continuous_def]
  rintro V ⟨𝒱, j, hj, rfl⟩
  haveI := hj
  exact ⟨𝒳.restrict (fun a => j.fiberEssImage (F.obj a)), 𝒳.restrictι _,
    isOpenSubstackInclusion_restrictι_comap F j,
    (range_mapPoints_restrictι_comap F j).symm⟩

/-- The field-valued point of the prestack $\Sch/X$ of a scheme $X$ determined by a
point $x \in X$: the coefficient field is the residue field $\kappa(x)$ and the morphism
is induced by the canonical map $\Spec \kappa(x) \to X$. -/
noncomputable def Scheme.fieldPointOfPoint (X : Scheme.{u}) (x : X) :
    FieldPoint (overBased X) where
  carrier := X.residueField x
  hom := overBased.map (X.fromSpecResidueField x)

/-- The comparison map from the points of a scheme $X$ to the topological space
$|\Sch/X|$ of the associated prestack, sending $x$ to the class of
$\Spec \kappa(x) \to X$. -/
noncomputable def Scheme.toPointSpace (X : Scheme.{u}) : X → pointSpace (overBased X) :=
  fun x => pointSpace.mk (X.fieldPointOfPoint x)

/-- API lemma supporting Definition 4.3.17 (comparison with schemes, injectivity
half): two points of a scheme with the same class in $|\Sch/X|$ are equal. If the two
canonical points $\Spec \kappa(x) \to X$ and $\Spec \kappa(y) \to X$ become
2-isomorphic over a common extension $L$, the two composites $\Spec L \to X$ agree
(`overHom_eq_of_iso`), and their image is $\{x\}$ resp. $\{y\}$
(`Scheme.range_fromSpecResidueField`). -/
theorem Scheme.injective_toPointSpace (X : Scheme.{u}) :
    Function.Injective X.toPointSpace := by
  intro x y h
  obtain ⟨L, hL, i₁, i₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp h
  have hover : Spec.map (CommRingCat.ofHom i₁) ≫ X.fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom i₂) ≫ X.fromSpecResidueField y :=
    calc Spec.map (CommRingCat.ofHom i₁) ≫ X.fromSpecResidueField x
        = ((X.fieldPointOfPoint x).restrict i₁).overHom :=
          (CategoryTheory.BasedFunctor.overHom_map_comp_map _ _).symm
      _ = ((X.fieldPointOfPoint y).restrict i₂).overHom :=
          CategoryTheory.BasedFunctor.overHom_eq_of_iso e
      _ = _ := CategoryTheory.BasedFunctor.overHom_map_comp_map _ _
  have hpt := congrArg (fun φ : Spec (CommRingCat.of L) ⟶ X =>
    φ.base (IsLocalRing.closedPoint L)) hover
  have hx : (Spec.map (CommRingCat.ofHom i₁) ≫ X.fromSpecResidueField x)
      (IsLocalRing.closedPoint L) = x := by
    have hmem : (Spec.map (CommRingCat.ofHom i₁) ≫ X.fromSpecResidueField x)
        (IsLocalRing.closedPoint L) ∈ Set.range (X.fromSpecResidueField x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecResidueField] at hmem
  have hy : (Spec.map (CommRingCat.ofHom i₂) ≫ X.fromSpecResidueField y)
      (IsLocalRing.closedPoint L) = y := by
    have hmem : (Spec.map (CommRingCat.ofHom i₂) ≫ X.fromSpecResidueField y)
        (IsLocalRing.closedPoint L) ∈ Set.range (X.fromSpecResidueField y) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecResidueField] at hmem
  exact hx.symm.trans (hpt.trans hy)

/-- API lemma supporting Definition 4.3.17 (comparison with schemes, surjectivity
half): every field-valued point `Spec K → X` of a scheme is equivalent to the canonical
point `Spec κ(p) → X` at its image `p`, because it factors through the residue field of
`p` (`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`) and every morphism
of representable prestacks is 2-isomorphic to the one induced by the morphism it
classifies (`CategoryTheory.BasedFunctor.nonempty_iso_overBased_map`). -/
theorem Scheme.surjective_toPointSpace (X : Scheme.{u}) :
    Function.Surjective X.toPointSpace := by
  refine pointSpace.ind fun x => ?_
  set f : Spec (CommRingCat.of x.carrier) ⟶ X := x.hom.overHom with hf
  refine ⟨f.base (IsLocalRing.closedPoint x.carrier), pointSpace.sound ?_⟩
  refine ⟨x.carrier, inferInstance,
    (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom, RingHom.id _, ?_⟩
  have hL : (X.fieldPointOfPoint (f.base (IsLocalRing.closedPoint x.carrier))).restrict
      (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom = overBased.map f := by
    change (overBased.map (Spec.map (CommRingCat.ofHom
      (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom))).comp
        (overBased.map (X.fromSpecResidueField _)) = _
    rw [← overBased.map_comp]
    congr 1
    simpa using
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField x.carrier X f
  rw [hL, FieldPoint.restrict_id]
  exact (CategoryTheory.BasedFunctor.nonempty_iso_overBased_map x.hom).map Iso.symm

/-- API theorem supporting Definition 4.3.17 (comparison with schemes, implicit
in the definition): the comparison map from the points of a scheme $X$ to $|\Sch/X|$ is
a bijection: every field-valued point $\Spec K \to X$ factors through the residue field
of its image point. -/
theorem Scheme.bijective_toPointSpace (X : Scheme.{u}) :
    Function.Bijective X.toPointSpace :=
  ⟨X.injective_toPointSpace, X.surjective_toPointSpace⟩

namespace homeomorphPointSpace

/-- Composing with an `eqToHom` does not change the range on points. -/
lemma range_eqToHom_comp_base {Y Z V : Scheme.{u}} (h : Y = Z) (φ : Z ⟶ V) :
    Set.range (CategoryTheory.eqToHom h ≫ φ).base = Set.range φ.base := by
  subst h
  simp

/-- The point range of the value of `G : Sch/S ⥤ᵇ Sch/X` at `A` is the point range of
`A.hom ≫ G.overHom`. -/
lemma range_obj_hom_base {S X : Scheme.{u}}
    (G : overBased S ⥤ᵇ overBased X) (A : Over S) :
    Set.range (G.obj A).hom.base = Set.range (A.hom ≫ G.overHom).base := by
  rw [CategoryTheory.BasedFunctor.obj_hom_eq_overHom G A]
  exact range_eqToHom_comp_base _ _

/-- The point of `X` underlying a field-valued point of `Sch/X`: the image of the closed
point of `Spec K` under the classified morphism. (This is the computation inside
`AlgebraicGeometry.Scheme.surjective_toPointSpace`.) -/
lemma toPointSpace_overHom_closedPoint (X : Scheme.{u}) (y : FieldPoint (overBased X)) :
    X.toPointSpace
        ((CategoryTheory.BasedFunctor.overHom y.hom).base
          (IsLocalRing.closedPoint y.carrier)) = pointSpace.mk y := by
  set f : Spec (CommRingCat.of y.carrier) ⟶ X := y.hom.overHom with hf
  refine pointSpace.sound ?_
  refine ⟨y.carrier, inferInstance,
    (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom, RingHom.id _, ?_⟩
  have hL : (X.fieldPointOfPoint (f.base (IsLocalRing.closedPoint y.carrier))).restrict
      (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom = overBased.map f := by
    change (overBased.map (Spec.map (CommRingCat.ofHom
      (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom))).comp
        (overBased.map (X.fromSpecResidueField _)) = _
    rw [← overBased.map_comp]
    congr 1
    simpa using
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField y.carrier X f
  rw [hL, FieldPoint.restrict_id]
  exact (CategoryTheory.BasedFunctor.nonempty_iso_overBased_map y.hom).map Iso.symm

/-- **(⇒)** The preimage under `X.toPointSpace` of the point range of an open substack of
`Sch/X` is the open subscheme that the substack cuts out of `X`. -/
lemma preimage_range_mapPoints (X : Scheme.{u})
    {𝒰 : BasedCategory.{v₃, u₃} Scheme.{u}} (i : 𝒰 ⥤ᵇ overBased X)
    [BasedFunctor.IsOpenSubstackInclusion i] :
    IsOpen (X.toPointSpace ⁻¹' Set.range (BasedFunctor.mapPoints i)) := by
  obtain ⟨W, hW⟩ := AlgebraicGeometry.exists_opens_fiberEssImage i X
    (CategoryTheory.BasedFunctor.id (overBased X))
  have hW' : ∀ A : Over X,
      i.fiberEssImage A ↔ Set.range A.hom.base ⊆ (W : Set X) := hW
  have hset : X.toPointSpace ⁻¹' Set.range (BasedFunctor.mapPoints i) = (W : Set X) := by
    ext x
    constructor
    · rintro ⟨p, hp⟩
      induction p using pointSpace.ind with
      | _ y =>
      have hp' : pointSpace.mk (FieldPoint.map i y)
          = pointSpace.mk (X.fieldPointOfPoint x) := hp
      obtain ⟨L, hL, ψ₁, ψ₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp hp'
      set Z : Over (Spec (CommRingCat.of L)) := Over.mk (𝟙 (Spec (CommRingCat.of L))) with hZ
      have h1 : i.fiberEssImage (((FieldPoint.map i y).restrict ψ₁).obj Z) :=
        fiberEssImage_comp_obj i
          ((overBased.map (Spec.map (CommRingCat.ofHom ψ₁))).comp y.hom) Z
      have h2 : i.fiberEssImage (((X.fieldPointOfPoint x).restrict ψ₂).obj Z) :=
        fiberEssImage_obj_of_iso i e Z h1
      set G : overBased (Spec (CommRingCat.of L)) ⥤ᵇ overBased X :=
        (overBased.map (Spec.map (CommRingCat.ofHom ψ₂))).comp
          (overBased.map (X.fromSpecResidueField x)) with hG
      have h3 : i.fiberEssImage (G.obj Z) := h2
      have h4 := (hW' (G.obj Z)).mp h3
      rw [range_obj_hom_base G Z] at h4
      have hoh : CategoryTheory.BasedFunctor.overHom G
          = Spec.map (CommRingCat.ofHom ψ₂) ≫ X.fromSpecResidueField x := by
        rw [hG]
        exact CategoryTheory.BasedFunctor.overHom_map_comp_map _ _
      rw [hoh] at h4
      refine h4 ⟨IsLocalRing.closedPoint L, ?_⟩
      change X.fromSpecResidueField x
          (Spec.map (CommRingCat.ofHom ψ₂) (Z.hom (IsLocalRing.closedPoint L))) = x
      exact Scheme.fromSpecResidueField_apply _ _
    · intro hx
      set f : Spec (CommRingCat.of (X.residueField x)) ⟶ X := X.fromSpecResidueField x with hf
      set G : overBased (Spec (CommRingCat.of (X.residueField x))) ⥤ᵇ overBased X :=
        overBased.map f with hG
      have h1 : i.fiberEssImage
          (G.obj (Over.mk (𝟙 (Spec (CommRingCat.of (X.residueField x)))))) := by
        refine (hW' _).mpr ?_
        rw [range_obj_hom_base G _]
        have hoh : CategoryTheory.BasedFunctor.overHom G = f := by
          rw [hG]; exact CategoryTheory.BasedFunctor.overHom_map _
        rw [hoh]
        rintro z ⟨t, rfl⟩
        have : (Over.mk (𝟙 (Spec (CommRingCat.of (X.residueField x))))).hom ≫ f = f := by
          simp
        rw [this]
        have hz : f t = x := Scheme.fromSpecResidueField_apply _ _
        exact Set.mem_of_eq_of_mem hz hx
      obtain ⟨H, ⟨e⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage i _ G h1
      exact ⟨pointSpace.mk ⟨X.residueField x, H⟩,
        AlgebraicGeometry.BasedFunctor.pointSpace.mk_eq_mk_of_iso e⟩
  rw [hset]
  exact W.2

/-- The object property of `Sch/X` cut out by an open subset `U ⊆ X`: the objects whose
structure morphism has image inside `U`. -/
def opensProperty (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.ObjectProperty (overBased X).obj :=
  fun A => Set.range A.hom.base ⊆ (U : Set X)

lemma fiberClosed_opensProperty (X : Scheme.{u}) (U : X.Opens) :
    BasedCategory.FiberClosed (opensProperty X U) := by
  intro a b e _ ha
  rintro z ⟨t, rfl⟩
  have hw : e.inv.left ≫ a.hom = b.hom := Over.w e.inv
  have hb : b.hom t = a.hom (e.inv.left t) := by rw [← hw]; rfl
  exact Set.mem_of_eq_of_mem hb (ha ⟨e.inv.left t, rfl⟩)

lemma key_opensProperty (X : Scheme.{u}) (U : X.Opens) (T : Scheme.{u})
    (g : overBased T ⥤ᵇ overBased X) :
    ∃ W : T.Opens, ∀ A : Over T,
      opensProperty X U (g.obj A) ↔ Set.range A.hom.base ⊆ (W : Set T) := by
  refine ⟨(CategoryTheory.BasedFunctor.overHom g) ⁻¹ᵁ U, fun A => ?_⟩
  change Set.range (g.obj A).hom.base ⊆ (U : Set X) ↔ _
  rw [range_obj_hom_base g A]
  constructor
  · rintro h z ⟨t, rfl⟩
    exact h ⟨t, rfl⟩
  · rintro h z ⟨t, rfl⟩
    exact h ⟨t, rfl⟩

lemma isOpenSubstack_opensProperty (X : Scheme.{u}) (U : X.Opens) :
    BasedFunctor.IsOpenSubstackInclusion
      ((overBased X).restrictι (opensProperty X U)) :=
  AlgebraicGeometry.isOpenSubstackInclusion_restrictι _ (fiberClosed_opensProperty X U)
    (key_opensProperty X U)

lemma range_mapPoints_opensProperty (X : Scheme.{u}) (U : X.Opens) :
    Set.range (BasedFunctor.mapPoints ((overBased X).restrictι (opensProperty X U)))
      = X.toPointSpace '' (U : Set X) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using pointSpace.ind with
    | _ y =>
    set G : overBased (Spec (CommRingCat.of y.carrier)) ⥤ᵇ overBased X :=
      y.hom.comp ((overBased X).restrictι (opensProperty X U)) with hG
    have hQ : Set.range
        (G.obj (Over.mk (𝟙 (Spec (CommRingCat.of y.carrier))))).hom.base ⊆ (U : Set X) :=
      (y.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of y.carrier))))).property
    rw [range_obj_hom_base G _] at hQ
    refine ⟨(CategoryTheory.BasedFunctor.overHom G) (IsLocalRing.closedPoint y.carrier),
      ?_, ?_⟩
    · refine hQ ⟨IsLocalRing.closedPoint y.carrier, ?_⟩
      simp
    · exact toPointSpace_overHom_closedPoint X ⟨y.carrier, G⟩
  · rintro ⟨x, hxU, rfl⟩
    set f : Spec (CommRingCat.of (X.residueField x)) ⟶ X := X.fromSpecResidueField x with hf
    set G : overBased (Spec (CommRingCat.of (X.residueField x))) ⥤ᵇ overBased X :=
      overBased.map f with hG
    have hoh : CategoryTheory.BasedFunctor.overHom G = f := by
      rw [hG]; exact CategoryTheory.BasedFunctor.overHom_map _
    have hGQ : ∀ Z, opensProperty X U (G.obj Z) := by
      intro Z
      change Set.range (G.obj Z).hom.base ⊆ (U : Set X)
      rw [range_obj_hom_base G Z, hoh]
      rintro z ⟨t, rfl⟩
      have heq : (Z.hom ≫ f) t = x := by
        change X.fromSpecResidueField x (Z.hom t) = x
        exact Scheme.fromSpecResidueField_apply _ _
      exact Set.mem_of_eq_of_mem heq hxU
    refine ⟨pointSpace.mk ⟨X.residueField x,
      corestrict G (opensProperty X U) hGQ⟩, ?_⟩
    change pointSpace.mk (⟨X.residueField x, _⟩ : FieldPoint (overBased X)) = _
    rw [corestrict_comp_restrictι, hG, hf]
    rfl

end homeomorphPointSpace

open homeomorphPointSpace in
/-- API theorem supporting Definition 4.3.17 (comparison with schemes, implicit
in the definition): for a scheme $X$, the topological space $|\Sch/X|$ of the
associated prestack is homeomorphic to the underlying topological space of $X$.

The bijection is `Scheme.bijective_toPointSpace`; what makes it a homeomorphism is the
open-substack description of both topologies. Continuity is
`AlgebraicGeometry.exists_opens_fiberEssImage` applied to the identity of `Sch/X` — an open
substack of `Sch/X` cuts an open subscheme out of `X`, and that open is exactly the preimage
of its point range. Openness is the converse construction: an open `U ⊆ X` gives the
fiber-closed object property `fun A => Set.range A.hom.base ⊆ U`, which is an open substack by
`AlgebraicGeometry.isOpenSubstackInclusion_restrictι` and whose point range is
`X.toPointSpace '' U`. -/
theorem Scheme.nonempty_homeomorph_pointSpace (X : Scheme.{u}) :
    Nonempty (pointSpace (overBased X) ≃ₜ X) := by
  have hcont : Continuous X.toPointSpace := by
    rw [continuous_def]
    intro V hV
    rw [AlgebraicGeometry.BasedCategory.isOpen_pointSpace_iff] at hV
    obtain ⟨𝒰, i, hi, rfl⟩ := hV
    have := hi
    exact preimage_range_mapPoints X i
  have hopen : IsOpenMap X.toPointSpace := by
    intro s hs
    rw [AlgebraicGeometry.BasedCategory.isOpen_pointSpace_iff]
    exact ⟨(overBased X).restrict (opensProperty X ⟨s, hs⟩),
      (overBased X).restrictι _, isOpenSubstack_opensProperty X ⟨s, hs⟩,
      (range_mapPoints_opensProperty X ⟨s, hs⟩).symm⟩
  exact ⟨((Equiv.ofBijective X.toPointSpace
    X.bijective_toPointSpace).toHomeomorphOfContinuousOpen hcont hopen).symm⟩

/-- The comparison map `X → |Sch/X|` of a scheme is an open map: the image of an open
`s ⊆ X` is the point set of the open substack of `Sch/X` cut out by `s`
(`AlgebraicGeometry.homeomorphPointSpace.opensProperty`). This is the openness half of
`AlgebraicGeometry.Scheme.nonempty_homeomorph_pointSpace`, isolated so that it can be
used on its own. -/
theorem Scheme.isOpenMap_toPointSpace (X : Scheme.{u}) : IsOpenMap X.toPointSpace := by
  intro s hs
  rw [AlgebraicGeometry.BasedCategory.isOpen_pointSpace_iff]
  exact ⟨(overBased X).restrict (homeomorphPointSpace.opensProperty X ⟨s, hs⟩),
    (overBased X).restrictι _,
    homeomorphPointSpace.isOpenSubstack_opensProperty X ⟨s, hs⟩,
    (homeomorphPointSpace.range_mapPoints_opensProperty X ⟨s, hs⟩).symm⟩

end AlgebraicGeometry

end DefTopologyOfStacks

section ExerClosedSubsetsAndSubstacks

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ u

/-- **Exercise 4.3.18** (`exer:closed-subsets-and-substacks`): let $\cX$ be an
algebraic stack and let $U \subseteq |\cX|$ be an open subset. Then there exists a
reduced closed substack $\cZ \hookrightarrow \cX$ with $|\cZ| = |\cX| \setminus U$. -/
theorem AlgebraicGeometry.BasedCategory.exists_isClosedSubstackInclusion_isReduced_compl
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]
    {U : Set (pointSpace 𝒳)} (hU : IsOpen U) :
    ∃ (𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}) (i : 𝒵 ⥤ᵇ 𝒳),
      BasedFunctor.IsClosedSubstackInclusion i ∧ BasedCategory.IsReduced 𝒵 ∧
      Set.range (BasedFunctor.mapPoints i) = Uᶜ := by
  sorry

/- LEDGER (unlabeled example after `exer:closed-subsets-and-substacks`): the topological
space `|[𝔸¹/𝔾ₘ]|` of the quotient stack of the scaling action over a field consists of
two points, the classes of the origin and of the open orbit. Blocked on quotient stacks
`[U/G]` (§3.4/§3.5 ledgers). -/

end ExerClosedSubsetsAndSubstacks

section ExerStabilizerProperties

/- LEDGER — **Exercise 4.3.20** (`exer:stabilizer-properties`, and the preceding and
following unlabeled discussion): for a point
`x ∈ |𝒳|` with representatives `x₁ : Spec k₁ → 𝒳` and `x₂ : Spec k₂ → 𝒳`, the
stabilizer group `G_{x₁}` is smooth (resp. étale, unramified, affine, finite) if and
only if `G_{x₂}` is; `dim G_{x₁} = dim G_{x₂}`; and for a Deligne–Mumford stack and
algebraically closed fields the abstract groups agree. Consequently one may speak of
points with smooth (étale, unramified, affine, finite) stabilizer, and of the geometric
stabilizer of a point of a Deligne–Mumford stack. Blocked on stabilizer groups, which
require the Isom presheaf (`exer:isom-presheaf`, §3.4 ledger) and the §4.2 inertia and
stabilizer constructions — to be completed once Section4.2-Representability lands. -/

end ExerStabilizerProperties

section DefQuasiCompact

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedCategory

variable (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})

/-- **Definition 4.3.21** (`def:quasi-compact`) (quasi-compact stacks): an algebraic
stack $\cX$ is *quasi-compact* if its topological space $|\cX|$ is. -/
abbrev IsQuasiCompact [𝒳.p.IsFiberedInGroupoids] : Prop :=
  CompactSpace (pointSpace 𝒳)

/-- **Definition 4.3.21** (`def:quasi-compact`) (connected stacks): an algebraic stack
$\cX$ is *connected* if its topological space $|\cX|$ is. -/
abbrev IsConnected [𝒳.p.IsFiberedInGroupoids] : Prop :=
  ConnectedSpace (pointSpace 𝒳)

/-- **Definition 4.3.21** (`def:quasi-compact`) (irreducible stacks): an algebraic
stack $\cX$ is *irreducible* if its topological space $|\cX|$ is. -/
abbrev IsIrreducible [𝒳.p.IsFiberedInGroupoids] : Prop :=
  IrreducibleSpace (pointSpace 𝒳)
namespace quotientMapOfPresentation

open CategoryTheory.Functor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒵 : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- Functoriality of `mapPoints` for composition. -/
lemma mapPoints_comp (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) (x : pointSpace 𝒳) :
    BasedFunctor.mapPoints (F.comp G) x
      = BasedFunctor.mapPoints G (BasedFunctor.mapPoints F x) := by
  induction x using pointSpace.ind with
  | _ x =>
    show pointSpace.mk (⟨x.carrier, x.hom.comp (F.comp G)⟩ : FieldPoint 𝒵)
      = pointSpace.mk ⟨x.carrier, (x.hom.comp F).comp G⟩
    rw [CategoryTheory.BasedFunctor.comp_assoc]

/-- 2-isomorphic morphisms of prestacks induce the same map on points. -/
lemma mapPoints_eq_of_iso {F G : 𝒳 ⥤ᵇ 𝒴} (e : F ≅ G) :
    BasedFunctor.mapPoints F = BasedFunctor.mapPoints G := by
  funext x
  induction x using pointSpace.ind with
  | _ x =>
    exact BasedFunctor.pointSpace.mk_eq_mk_of_iso
      (CategoryTheory.BasedCategory.isoWhiskerLeft x.hom e)

/-- The point of `|Sch/Spec K|` attached to the (unique) point of `Spec K` is the class of
the identity. -/
lemma toPointSpace_spec_field (K : Type u) [Field K]
    (t : Spec (CommRingCat.of K)) :
    (Spec (CommRingCat.of K)).toPointSpace t
      = pointSpace.mk (⟨K, CategoryTheory.BasedFunctor.id _⟩ :
          FieldPoint (overBased (Spec (CommRingCat.of K)))) := by
  obtain ⟨s, hs⟩ := (Spec (CommRingCat.of K)).surjective_toPointSpace
    (pointSpace.mk (⟨K, CategoryTheory.BasedFunctor.id _⟩ :
      FieldPoint (overBased (Spec (CommRingCat.of K)))))
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rw [Subsingleton.elim t s]
  exact hs

/-- Naturality of the comparison map `X → |Sch/X|`. -/
lemma mapPoints_overBased_map_toPointSpace {X Y : Scheme.{u}} (f : X ⟶ Y) (t : X) :
    BasedFunctor.mapPoints (overBased.map f) (X.toPointSpace t)
      = Y.toPointSpace (f.base t) := by
  have h1 : (overBased.map (X.fromSpecResidueField t)).comp (overBased.map f)
      = overBased.map (X.fromSpecResidueField t ≫ f) := (overBased.map_comp _ _).symm
  have h2 : X.fromSpecResidueField t ≫ f
      = Spec.map (f.residueFieldMap t) ≫ Y.fromSpecResidueField (f.base t) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f t).symm
  have h3 : (Y.fieldPointOfPoint (f.base t)).restrict (f.residueFieldMap t).hom
      = overBased.map (X.fromSpecResidueField t ≫ f) := by
    show (overBased.map (Spec.map (CommRingCat.ofHom (f.residueFieldMap t).hom))).comp
      (overBased.map (Y.fromSpecResidueField (f.base t)))
      = overBased.map (X.fromSpecResidueField t ≫ f)
    rw [← overBased.map_comp, CommRingCat.ofHom_hom, h2]
  show pointSpace.mk ((X.fieldPointOfPoint t).map (overBased.map f)) = _
  have h4 : (X.fieldPointOfPoint t).map (overBased.map f)
      = ⟨X.residueField t, (Y.fieldPointOfPoint (f.base t)).restrict
          (f.residueFieldMap t).hom⟩ := by
    rw [h3]
    show (⟨X.residueField t, (overBased.map (X.fromSpecResidueField t)).comp
      (overBased.map f)⟩ : FieldPoint (overBased Y)) = _
    rw [h1]
  rw [h4]
  exact pointSpace.sound
    (FieldPoint.equiv_restrict (Y.fieldPointOfPoint (f.base t)) (f.residueFieldMap t).hom)

/-- The point of `|𝒳|` attached to a point `t` of a scheme `T` mapping to `𝒳`. -/
noncomputable def nu {T : Scheme.{u}} (g : overBased T ⥤ᵇ 𝒳) (t : T) : pointSpace 𝒳 :=
  BasedFunctor.mapPoints g (T.toPointSpace t)

lemma nu_comp_map {T T' : Scheme.{u}} (f : T' ⟶ T) (g : overBased T ⥤ᵇ 𝒳) (t : T') :
    nu ((overBased.map f).comp g) t = nu g (f.base t) := by
  show BasedFunctor.mapPoints ((overBased.map f).comp g) (T'.toPointSpace t) = _
  rw [mapPoints_comp, mapPoints_overBased_map_toPointSpace]
  rfl

lemma nu_eq_of_iso {T : Scheme.{u}} {g g' : overBased T ⥤ᵇ 𝒳} (e : g ≅ g') :
    nu g = nu g' := by
  funext t
  show BasedFunctor.mapPoints g _ = BasedFunctor.mapPoints g' _
  rw [mapPoints_eq_of_iso e]

/-- A smooth presentation `q : Sch/U ⥤ᵇ 𝒳` base-changes, along any `g : Sch/T ⥤ᵇ 𝒳`, to a
scheme `T'` with a surjective smooth map to `T` and a map to `U` making the square
2-commute. -/
lemma exists_cover_of_representableWith {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) :
    ∃ (T' : Scheme.{u}) (a : T' ⟶ T) (b : T' ⟶ U),
      _root_.AlgebraicGeometry.Surjective a ∧ _root_.AlgebraicGeometry.Smooth a ∧
      Nonempty ((overBased.map b).comp q ≅ (overBased.map a).comp g) := by
  obtain ⟨X, hX, E, hE⟩ := hq.1 T g
  haveI := hX
  haveI := hE
  obtain ⟨T', p, hp⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  set Φ : overBased T' ⥤ᵇ fiberProduct q g :=
    (overBasedToOfPresheafYoneda T').comp ((ofPresheaf.map p).comp E) with hΦ
  have hprop : (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
      MorphismProperty Scheme.{u}) (Φ.comp (fiberProductSnd q g)).overHom := by
    have := hq.2 T g X hX E hE T' p hp
    rw [hΦ, CategoryTheory.BasedFunctor.comp_assoc,
      CategoryTheory.BasedFunctor.comp_assoc]
    exact this
  refine ⟨T', (Φ.comp (fiberProductSnd q g)).overHom,
    (Φ.comp (fiberProductFst q g)).overHom, hprop.1, hprop.2, ?_⟩
  obtain ⟨αa⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductSnd q g))
  obtain ⟨αb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductFst q g))
  have hcomm : (Φ.comp (fiberProductFst q g)).comp q
      ≅ (Φ.comp (fiberProductSnd q g)).comp g := by
    rw [CategoryTheory.BasedFunctor.comp_assoc, CategoryTheory.BasedFunctor.comp_assoc]
    exact BasedCategory.isoWhiskerLeft Φ (fiberProductIsoComm q g)
  exact ⟨((BasedCategory.isoWhiskerRight αb.symm q).trans hcomm).trans
    (BasedCategory.isoWhiskerRight αa g)⟩

lemma nu_spec_field (K : Type u) [Field K]
    (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) (t : Spec (CommRingCat.of K)) :
    nu x t = pointSpace.mk (⟨K, x⟩ : FieldPoint 𝒳) := by
  show BasedFunctor.mapPoints x ((Spec (CommRingCat.of K)).toPointSpace t) = _
  rw [toPointSpace_spec_field K t]
  show pointSpace.mk (⟨K, (CategoryTheory.BasedFunctor.id _).comp x⟩ : FieldPoint 𝒳) = _
  rw [CategoryTheory.BasedFunctor.id_comp]

lemma mk_comp_map_eq_nu {T : Scheme.{u}} (K : Type u) [Field K]
    (f : Spec (CommRingCat.of K) ⟶ T) (g : overBased T ⥤ᵇ 𝒳)
    (t : Spec (CommRingCat.of K)) :
    pointSpace.mk (⟨K, (overBased.map f).comp g⟩ : FieldPoint 𝒳) = nu g (f.base t) := by
  rw [← nu_comp_map f g t]
  show _ = BasedFunctor.mapPoints ((overBased.map f).comp g)
    ((Spec (CommRingCat.of K)).toPointSpace t)
  rw [toPointSpace_spec_field K t]
  show _ = pointSpace.mk (⟨K, (CategoryTheory.BasedFunctor.id _).comp
    ((overBased.map f).comp g)⟩ : FieldPoint 𝒳)
  rw [CategoryTheory.BasedFunctor.id_comp]

/-- The preimage in a scheme `X` of the point set of an open substack of `Sch/X` is an
open subset of `X`. -/
lemma exists_opens_preimage_range_mapPoints {X : Scheme.{u}}
    {𝒰 : BasedCategory.{v₃, u₃} Scheme.{u}} (i : 𝒰 ⥤ᵇ overBased X)
    [BasedFunctor.IsOpenSubstackInclusion i] :
    ∃ W : X.Opens,
      X.toPointSpace ⁻¹' (Set.range (BasedFunctor.mapPoints i)) = (W : Set X) := by
  obtain ⟨W, hW⟩ := AlgebraicGeometry.exists_opens_fiberEssImage i X
    (CategoryTheory.BasedFunctor.id (overBased X))
  refine ⟨W, ?_⟩
  ext x
  have hres : ∀ w : ↥(Spec (X.residueField x)), (X.fromSpecResidueField x).base w = x := by
    intro w
    have h0 : (X.fromSpecResidueField x).base w
        ∈ Set.range (X.fromSpecResidueField x).base := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at h0
    exact h0
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨p, hp⟩
    induction p using pointSpace.ind with
    | _ y =>
      obtain ⟨M, hM, ψ₁, ψ₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp hp
      have hfe : ∀ Z, i.fiberEssImage
          (((X.fieldPointOfPoint x).restrict ψ₂).obj Z) := by
        intro Z
        refine fiberEssImage_obj_of_iso i e Z ?_
        show i.fiberEssImage
          (((overBased.map (Spec.map (CommRingCat.ofHom ψ₁))).comp (y.hom.comp i)).obj Z)
        rw [← CategoryTheory.BasedFunctor.comp_assoc]
        exact fiberEssImage_comp_obj i _ Z
      have h2 := hfe (Over.mk (𝟙 (Spec (CommRingCat.of M))))
      have h3 := (hW _).mp h2
      obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of M)) := inferInstance
      refine h3 ⟨pt, ?_⟩
      change ((𝟙 _ ≫ Spec.map (CommRingCat.ofHom ψ₂)) ≫ X.fromSpecResidueField x).base pt = x
      simp
      exact hres _
  · intro hx
    have h1 : i.fiberEssImage ((X.fieldPointOfPoint x).hom.obj
        (Over.mk (𝟙 (Spec (X.residueField x))))) := by
      refine (hW _).mpr ?_
      change Set.range ⇑(𝟙 _ ≫ X.fromSpecResidueField x) ⊆ (W : Set X)
      rw [Set.range_subset_iff]
      intro v
      rw [show (𝟙 _ ≫ X.fromSpecResidueField x).base v = x from by simp [hres]]
      exact hx
    obtain ⟨H, ⟨e⟩⟩ := AlgebraicGeometry.exists_lift_of_fiberEssImage i _
      (X.fieldPointOfPoint x).hom h1
    exact ⟨pointSpace.mk ⟨X.residueField x, H⟩,
      BasedFunctor.pointSpace.mk_eq_mk_of_iso e⟩

/-- The comparison map `X → |Sch/X|` is continuous. -/
lemma continuous_toPointSpace (X : Scheme.{u}) : Continuous X.toPointSpace := by
  rw [continuous_def]
  rintro V ⟨𝒰, i, hi, rfl⟩
  haveI := hi
  obtain ⟨W, hW⟩ := exists_opens_preimage_range_mapPoints i
  rw [hW]
  exact W.2

/-- Smooth descent of openness for the sets cut out in a scheme by a subset of `|𝒳|`. -/
lemma isOpen_nu_preimage_of_presentation {V : Set (pointSpace 𝒳)} {U : Scheme.{u}}
    (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    (hV : IsOpen (nu q ⁻¹' V)) (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) :
    IsOpen (nu g ⁻¹' V) := by
  obtain ⟨T', a, b, hsurj, hsm, ⟨e⟩⟩ := exists_cover_of_representableWith q hq T g
  haveI := hsurj
  haveI := hsm
  haveI : _root_.AlgebraicGeometry.UniversallyOpen a := inferInstance
  have hcompose : ∀ t' : T', nu q (b.base t') = nu g (a.base t') := by
    intro t'
    rw [← nu_comp_map b q t', ← nu_comp_map a g t', nu_eq_of_iso e]
  have hpre : (⇑a) ⁻¹' (nu g ⁻¹' V) = (⇑b) ⁻¹' (nu q ⁻¹' V) := by
    ext t'
    simp only [Set.mem_preimage]
    rw [hcompose t']
  have hq' : Topology.IsQuotientMap (⇑a) :=
    IsOpenMap.isQuotientMap a.isOpenMap a.continuous a.surjective
  refine hq'.isOpen_preimage.mp ?_
  rw [hpre]
  exact hV.preimage b.continuous

/-- Two morphisms `Sch/S ⥤ᵇ 𝒳` with isomorphic (over the identity) values at `𝟙 S` are
2-isomorphic. This is the 2-Yoneda lemma. -/
lemma nonempty_iso_of_fiber_iso [𝒳.p.IsFiberedInGroupoids] {S : Scheme.{u}}
    (y z : overBased S ⥤ᵇ 𝒳)
    (e : y.obj (Over.mk (𝟙 S)) ≅ z.obj (Over.mk (𝟙 S)))
    (he : Functor.IsHomLift 𝒳.p (𝟙 S) e.hom) : Nonempty (y ≅ z) := by
  haveI := he
  haveI := CategoryTheory.BasedCategory.isEquivalence_twoYonedaEval (𝒳 := 𝒳) S
  refine ⟨(twoYonedaEval (𝒳 := 𝒳) S).preimageIso ?_⟩
  refine ⟨Fiber.homMk 𝒳.p S e.hom, Fiber.homMk 𝒳.p S e.inv, ?_, ?_⟩
  · apply Fiber.hom_ext
    simp only [Fiber.fiberInclusion, Functor.comp_map]
    exact e.hom_inv_id
  · apply Fiber.hom_ext
    simp only [Fiber.fiberInclusion, Functor.comp_map]
    exact e.inv_hom_id

/-- **Key lemma.** Any field-valued point of `𝒳` that receives a lift into `g.obj X` over
some morphism from `Spec K` is one of the points `nu g` attached to the image of `X`. -/
lemma exists_nu_eq [𝒳.p.IsFiberedInGroupoids] {T : Scheme.{u}} (g : overBased T ⥤ᵇ 𝒳)
    (X : Over T) (K : Type u) [Field K]
    (h : Spec (CommRingCat.of K) ⟶ 𝒳.p.obj (g.obj X))
    (y : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳)
    (φ : y.obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶ g.obj X)
    (hφ : Functor.IsHomLift 𝒳.p h φ) :
    ∃ t : X.left, pointSpace.mk (⟨K, y⟩ : FieldPoint 𝒳) = nu g (X.hom.base t) := by
  haveI := hφ
  have hAA : Functor.IsHomLift 𝒳.p
      ((Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)).left (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) :=
    CategoryTheory.BasedCategory.basedMap_isHomLift_left T (F := g) _
  haveI hA : Functor.IsHomLift 𝒳.p (h ≫ eqToHom (g.w_obj X)) (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) := by
    simpa using hAA
  haveI hB : Functor.IsHomLift 𝒳.p
      ((h ≫ eqToHom (g.w_obj X)) ≫ eqToHom (g.w_obj X).symm) (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) := inferInstance
  haveI hC : Functor.IsHomLift 𝒳.p h (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) := by
    simpa using hB
  obtain ⟨e⟩ := nonempty_iso_of_fiber_iso y
    ((overBased.map ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)).comp g)
    (CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso
      (p := 𝒳.p) h (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) φ)
    (CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso_hom_isHomLift
      (p := 𝒳.p) h (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (CommRingCat.of K)) ≫ ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom)) : Over T) ⟶ X)) φ)
  obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstance
  refine ⟨(h ≫ eqToHom (g.w_obj X)).base pt, ?_⟩
  rw [BasedFunctor.pointSpace.mk_eq_mk_of_iso e,
    mk_comp_map_eq_nu K ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) g pt]
  congr 1

/-- The object property attached to a subset `V ⊆ |𝒳|`: every field-valued point mapping
into the object lands in `V`. -/
def pointProperty (V : Set (pointSpace 𝒳)) : ObjectProperty 𝒳.obj := fun A =>
  ∀ (K : Type u) (_ : Field K) (h : Spec (CommRingCat.of K) ⟶ 𝒳.p.obj A)
    (y : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳)
    (φ : y.obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ⟶ A),
    Functor.IsHomLift 𝒳.p h φ → pointSpace.mk (⟨K, y⟩ : FieldPoint 𝒳) ∈ V

lemma fiberClosed_pointProperty (V : Set (pointSpace 𝒳)) :
    BasedCategory.FiberClosed (pointProperty V) := by
  intro A A' e _ hA K hK f y φ hφ
  haveI := hφ
  refine hA K hK (f ≫ 𝒳.p.map e.inv) y (φ ≫ e.inv) ?_
  haveI : Functor.IsHomLift 𝒳.p (𝒳.p.map e.inv) e.inv := inferInstance
  infer_instance

/-- Every point in the image of `X` is captured by the point property. -/
lemma nu_mem_of_pointProperty [𝒳.p.IsFiberedInGroupoids] {V : Set (pointSpace 𝒳)}
    {T : Scheme.{u}} (g : overBased T ⥤ᵇ 𝒳) (X : Over T)
    (hQ : pointProperty V (g.obj X)) (t : X.left) : nu g (X.hom.base t) ∈ V := by
  have hAA : Functor.IsHomLift 𝒳.p ((Over.homMk (X.left.fromSpecResidueField t) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (X.left.residueField t)) ≫
          (X.left.fromSpecResidueField t ≫ X.hom)) : Over T) ⟶ X)).left (g.map (Over.homMk (X.left.fromSpecResidueField t) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (X.left.residueField t)) ≫
          (X.left.fromSpecResidueField t ≫ X.hom)) : Over T) ⟶ X)) :=
    CategoryTheory.BasedCategory.basedMap_isHomLift_left T (F := g) _
  haveI hA : Functor.IsHomLift 𝒳.p (X.left.fromSpecResidueField t) (g.map (Over.homMk (X.left.fromSpecResidueField t) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (X.left.residueField t)) ≫
          (X.left.fromSpecResidueField t ≫ X.hom)) : Over T) ⟶ X)) := by
    simpa using hAA
  haveI hC : Functor.IsHomLift 𝒳.p
      (X.left.fromSpecResidueField t ≫ eqToHom (g.w_obj X).symm) (g.map (Over.homMk (X.left.fromSpecResidueField t) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (X.left.residueField t)) ≫
          (X.left.fromSpecResidueField t ≫ X.hom)) : Over T) ⟶ X)) :=
    inferInstance
  have hmem := hQ (X.left.residueField t) inferInstance
    (X.left.fromSpecResidueField t ≫ eqToHom (g.w_obj X).symm)
    ((overBased.map (X.left.fromSpecResidueField t ≫ X.hom)).comp g)
    (g.map (Over.homMk (X.left.fromSpecResidueField t) (Category.id_comp _).symm :
        (Over.mk (𝟙 (Spec (X.left.residueField t)) ≫
          (X.left.fromSpecResidueField t ≫ X.hom)) : Over T) ⟶ X)) hC
  obtain ⟨pt⟩ : Nonempty ↥(Spec (X.left.residueField t)) := inferInstance
  have hpt : (X.left.fromSpecResidueField t).base pt = t := by
    have h0 : (X.left.fromSpecResidueField t).base pt
        ∈ Set.range (X.left.fromSpecResidueField t).base := ⟨pt, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at h0
    exact h0
  rw [mk_comp_map_eq_nu (X.left.residueField t)
    (X.left.fromSpecResidueField t ≫ X.hom) g pt] at hmem
  refine Set.mem_of_eq_of_mem ?_ hmem
  congr 1
  exact congrArg (fun s => X.hom.base s) hpt.symm

/-- The point set of the substack cut out by `pointProperty V` is `V`. -/
lemma range_mapPoints_pointProperty [𝒳.p.IsFiberedInGroupoids] (V : Set (pointSpace 𝒳)) :
    Set.range (BasedFunctor.mapPoints (𝒳.restrictι (pointProperty V))) = V := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    induction p using pointSpace.ind with
    | _ z =>
      have hlift : Functor.IsHomLift 𝒳.p
          (eqToHom ((z.hom.comp (𝒳.restrictι (pointProperty V))).w_obj
            (Over.mk (𝟙 (Spec (CommRingCat.of z.carrier))))).symm)
          (𝟙 ((z.hom.comp (𝒳.restrictι (pointProperty V))).obj
            (Over.mk (𝟙 (Spec (CommRingCat.of z.carrier)))))) := by
        refine IsHomLift.of_fac' 𝒳.p _ _
          ((z.hom.comp (𝒳.restrictι (pointProperty V))).w_obj _) rfl ?_
        simp
      have hQ : pointProperty V ((z.hom.comp (𝒳.restrictι (pointProperty V))).obj
          (Over.mk (𝟙 (Spec (CommRingCat.of z.carrier))))) :=
        (z.hom.obj (Over.mk (𝟙 (Spec (CommRingCat.of z.carrier))))).property
      exact hQ z.carrier inferInstance _ (z.hom.comp (𝒳.restrictι (pointProperty V))) _ hlift
  · intro hv
    induction v using pointSpace.ind with
    | _ x =>
      have hall : ∀ Z : Over (Spec (CommRingCat.of x.carrier)),
          pointProperty V (x.hom.obj Z) := by
        intro Z K' hK' h y φ hφ
        obtain ⟨t, ht⟩ := exists_nu_eq x.hom Z K' h y φ hφ
        rw [ht, nu_spec_field]
        exact hv
      refine ⟨pointSpace.mk ⟨x.carrier,
        BasedCategory.corestrict x.hom (pointProperty V) hall⟩, ?_⟩
      show pointSpace.mk (⟨x.carrier, _⟩ : FieldPoint 𝒳) = _
      rw [BasedCategory.corestrict_comp_restrictι]

/-- If the preimage of `V` in `|Sch/U|` is open, so is `V`. -/
theorem isOpen_of_isOpen_preimage [𝒳.p.IsFiberedInGroupoids] {U : Scheme.{u}}
    (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    {V : Set (pointSpace 𝒳)} (hV : IsOpen (BasedFunctor.mapPoints q ⁻¹' V)) :
    IsOpen V := by
  have hUopen : IsOpen (nu q ⁻¹' V) := by
    have hset : nu q ⁻¹' V = U.toPointSpace ⁻¹' (BasedFunctor.mapPoints q ⁻¹' V) := rfl
    rw [hset]
    exact hV.preimage (continuous_toPointSpace U)
  have hkey : ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳), ∃ W : T.Opens, ∀ X : Over T,
      pointProperty V (g.obj X) ↔ Set.range X.hom.base ⊆ (W : Set T) := by
    intro T g
    refine ⟨⟨nu g ⁻¹' V, isOpen_nu_preimage_of_presentation q hq hUopen T g⟩, fun X => ?_⟩
    constructor
    · intro hQ
      rintro s ⟨t, rfl⟩
      exact nu_mem_of_pointProperty g X hQ t
    · intro hsub K hK h y φ hφ
      obtain ⟨t, ht⟩ := exists_nu_eq g X K h y φ hφ
      rw [ht]
      exact hsub ⟨t, rfl⟩
  exact ⟨𝒳.restrict (pointProperty V), 𝒳.restrictι _,
    AlgebraicGeometry.isOpenSubstackInclusion_restrictι _ (fiberClosed_pointProperty V) hkey,
    (range_mapPoints_pointProperty V).symm⟩

end quotientMapOfPresentation

open quotientMapOfPresentation in
/-- API lemma supporting Definition 4.3.21 (the affine-presentation
criterion): a morphism from a scheme that is representable by surjective smooth
morphisms induces a surjection on point spaces. -/
lemma surjective_mapPoints_of_smooth_presentation
    {𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}} {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒵)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    Function.Surjective (BasedFunctor.mapPoints q) := by
  intro v
  induction v using pointSpace.ind with
  | _ x =>
    obtain ⟨T', a, b, hsurj, -, ⟨e⟩⟩ := exists_cover_of_representableWith q hq
      (Spec (CommRingCat.of x.carrier)) x.hom
    have := hsurj
    obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of x.carrier)) := inferInstance
    obtain ⟨t', -⟩ := a.surjective pt
    refine ⟨U.toPointSpace (b.base t'), ?_⟩
    show nu q (b.base t') = _
    rw [← nu_comp_map b q t', nu_eq_of_iso e, nu_comp_map a x.hom t', nu_spec_field]

/-- Every pair of points with matching images lifts to the point space of the fiber
product.  This hypothesis-free form is supporting material for the point-map openness
used in the quasi-compactness criterion. -/
lemma exists_mapPoints_fiberProduct_eq_aux
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
    {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : pointSpace 𝒳) (y' : pointSpace 𝒴')
    (h : BasedFunctor.mapPoints F x = BasedFunctor.mapPoints G y') :
    ∃ z : pointSpace (fiberProduct F G),
      BasedFunctor.mapPoints (fiberProductFst F G) z = x ∧
        BasedFunctor.mapPoints (fiberProductSnd F G) z = y' := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep x
  obtain ⟨y', rfl⟩ := Quot.exists_rep y'
  obtain ⟨L, hL, i, i', ⟨α⟩⟩ := pointSpace.mk_eq_mk_iff.mp h
  have τ : (x.restrict i).comp F ≅ (y'.restrict i').comp G := α
  refine ⟨pointSpace.mk ⟨L, fiberProductLift (x.restrict i) (y'.restrict i') τ⟩, ?_, ?_⟩
  · exact pointSpace.sound (FieldPoint.equiv_restrict x i)
  · exact pointSpace.sound (FieldPoint.equiv_restrict y' i')

open quotientMapOfPresentation in
/-- The induced point map of a smooth presentation is a quotient map.  This unlabelled
form is placed before the affine-presentation criterion; the numbered Exercise 4.3.24
statement below delegates to it. -/
lemma isQuotientMap_mapPoints_of_presentation_aux
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]
    {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    Topology.IsQuotientMap (BasedFunctor.mapPoints q) := by
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen (fun V => ⟨?_, ?_⟩), ?_⟩
  · intro hV
    exact isOpen_of_isOpen_preimage q hq hV
  · rintro ⟨𝒱, j, hj, rfl⟩
    haveI := hj
    exact ⟨(overBased U).restrict (fun a => j.fiberEssImage (q.obj a)),
      (overBased U).restrictι _,
      AlgebraicGeometry.isOpenSubstackInclusion_restrictι_comap q j,
      (range_mapPoints_restrictι_comap q j).symm⟩
  · exact surjective_mapPoints_of_smooth_presentation q hq

/-- A smooth presentation of a fiber product may be chosen so that it realizes every
pair of matching scheme points. -/
lemma quotientMapOfPresentation.exists_cover_lift_aux
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [𝒳.p.IsFiberedInGroupoids]
    {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) :
    ∃ (T' : Scheme.{u}) (a : T' ⟶ T) (b : T' ⟶ U),
      _root_.AlgebraicGeometry.Surjective a ∧ _root_.AlgebraicGeometry.Smooth a ∧
      (∀ t' : T', quotientMapOfPresentation.nu q (b.base t') =
        quotientMapOfPresentation.nu g (a.base t')) ∧
      (∀ (t : T) (u : U), quotientMapOfPresentation.nu g t =
          quotientMapOfPresentation.nu q u →
        ∃ t' : T', a.base t' = t ∧ b.base t' = u) := by
  obtain ⟨X, hX, E, hE⟩ := hq.1 T g
  let _ : IsAlgebraicSpace X := hX
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨T', pres, hpres⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  set Ψ : overBased T' ⥤ᵇ ofPresheaf X :=
    (overBasedToOfPresheafYoneda T').comp (ofPresheaf.map pres) with hΨdef
  set Φ : overBased T' ⥤ᵇ fiberProduct q g := Ψ.comp E with hΦdef
  have hΨrel : Ψ.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) :=
    (BasedFunctor.relativelyRepresentableWith_ofPresheaf_map hpres).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda T')
  have hΨpres : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) Ψ :=
    BasedFunctor.RelativelyRepresentableWith.representableWith le_rfl hΨrel
  have hΦ : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) Φ :=
    (hΨpres.comp_target_isEquivalence E).mono (inf_le_inf le_rfl etale_le_smooth)
  have hsurjΦ : Function.Surjective (BasedFunctor.mapPoints Φ) :=
    surjective_mapPoints_of_smooth_presentation Φ hΦ
  have hprop : (@_root_.AlgebraicGeometry.Surjective ⊓
      @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})
      (Φ.comp (fiberProductSnd q g)).overHom := by
    simpa only [hΦdef, hΨdef, CategoryTheory.BasedFunctor.comp_assoc] using
      hq.2 T g X hX E hE T' pres hpres
  obtain ⟨αa⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductSnd q g))
  obtain ⟨αb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductFst q g))
  have hmapa : ∀ t' : T', BasedFunctor.mapPoints (Φ.comp (fiberProductSnd q g))
      (T'.toPointSpace t') =
        T.toPointSpace ((Φ.comp (fiberProductSnd q g)).overHom.base t') := by
    intro t'
    rw [quotientMapOfPresentation.mapPoints_eq_of_iso αa,
      quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace]
  have hmapb : ∀ t' : T', BasedFunctor.mapPoints (Φ.comp (fiberProductFst q g))
      (T'.toPointSpace t') =
        U.toPointSpace ((Φ.comp (fiberProductFst q g)).overHom.base t') := by
    intro t'
    rw [quotientMapOfPresentation.mapPoints_eq_of_iso αb,
      quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace]
  refine ⟨T', (Φ.comp (fiberProductSnd q g)).overHom,
    (Φ.comp (fiberProductFst q g)).overHom, hprop.1, hprop.2, ?_, ?_⟩
  · intro t'
    show BasedFunctor.mapPoints q (U.toPointSpace _) =
      BasedFunctor.mapPoints g (T.toPointSpace _)
    rw [← hmapb t', ← hmapa t', ← quotientMapOfPresentation.mapPoints_comp,
      ← quotientMapOfPresentation.mapPoints_comp,
      CategoryTheory.BasedFunctor.comp_assoc, CategoryTheory.BasedFunctor.comp_assoc]
    have heq := congrFun (quotientMapOfPresentation.mapPoints_eq_of_iso
      (CategoryTheory.BasedCategory.isoWhiskerLeft Φ (fiberProductIsoComm q g)))
      (T'.toPointSpace t')
    simpa only [hΦdef, CategoryTheory.BasedFunctor.comp_assoc] using heq
  · intro t u h
    obtain ⟨z, hz1, hz2⟩ := exists_mapPoints_fiberProduct_eq_aux q g
      (U.toPointSpace u) (T.toPointSpace t) h.symm
    obtain ⟨z₀, hz₀⟩ := hsurjΦ z
    obtain ⟨t', ht'⟩ := T'.surjective_toPointSpace z₀
    subst ht'
    refine ⟨t', ?_, ?_⟩
    · refine T.injective_toPointSpace ?_
      rw [← hmapa t', quotientMapOfPresentation.mapPoints_comp, hz₀, hz2]
    · refine U.injective_toPointSpace ?_
      rw [← hmapb t', quotientMapOfPresentation.mapPoints_comp, hz₀, hz1]

/-- The point map `U → |𝒳|` of a smooth presentation is open. -/
theorem quotientMapOfPresentation.isOpenMap_nu_aux
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]
    {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    IsOpenMap (quotientMapOfPresentation.nu q) := by
  obtain ⟨T', a, b, hsurj, hsm, hcomp, hlift⟩ :=
    quotientMapOfPresentation.exists_cover_lift_aux q hq U q
  have := hsm
  have hao : _root_.AlgebraicGeometry.UniversallyOpen a := inferInstance
  have hquot := isQuotientMap_mapPoints_of_presentation_aux q hq
  intro W hW
  have hsat : quotientMapOfPresentation.nu q ⁻¹'
      (quotientMapOfPresentation.nu q '' W) = a.base '' (b.base ⁻¹' W) := by
    ext x
    constructor
    · rintro ⟨w, hw, hxw⟩
      obtain ⟨t', ht'a, ht'b⟩ := hlift x w hxw.symm
      exact ⟨t', by rw [Set.mem_preimage, ht'b]; exact hw, ht'a⟩
    · rintro ⟨t', ht', rfl⟩
      exact ⟨b.base t', ht', hcomp t'⟩
  refine hquot.isOpen_preimage.mp ?_
  have h1 : BasedFunctor.mapPoints q ⁻¹' (quotientMapOfPresentation.nu q '' W) =
      U.toPointSpace '' (quotientMapOfPresentation.nu q ⁻¹'
        (quotientMapOfPresentation.nu q '' W)) := by
    rw [show (quotientMapOfPresentation.nu q ⁻¹'
          (quotientMapOfPresentation.nu q '' W)) =
        U.toPointSpace ⁻¹' (BasedFunctor.mapPoints q ⁻¹'
          (quotientMapOfPresentation.nu q '' W)) from rfl,
      Set.image_preimage_eq _ U.surjective_toPointSpace]
  rw [h1, hsat]
  exact U.isOpenMap_toPointSpace _ (a.isOpenMap _ (hW.preimage b.continuous))

open quotientMapOfPresentation in
/-- Point-surjectivity implies surjectivity in the presentation-theoretic sense used for
morphisms of prestacks.  This is the direction of Exercise 4.3.24 needed by the
quasi-compactness criterion; unlike the numbered algebraic-stack statement below, it
does not require algebraicity of either prestack. -/
lemma surjective_of_surjective_mapPoints_aux
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
    {F : 𝒳 ⥤ᵇ 𝒴} (hs : Function.Surjective (BasedFunctor.mapPoints F)) :
    BasedFunctor.Surjective F := by
  intro V g hg U q hq
  refine ⟨fun v => ?_⟩
  obtain ⟨x, hx⟩ := hs (BasedFunctor.mapPoints g (V.toPointSpace v))
  obtain ⟨z, hz2⟩ : ∃ z : pointSpace (fiberProduct F g),
      BasedFunctor.mapPoints (fiberProductSnd F g) z = V.toPointSpace v := by
    obtain ⟨x, rfl⟩ := Quot.exists_rep x
    obtain ⟨y', hy'⟩ := Quot.exists_rep (V.toPointSpace v)
    rw [← hy'] at hx ⊢
    obtain ⟨L, hL, i, i', ⟨α⟩⟩ := pointSpace.mk_eq_mk_iff.mp hx
    have τ : (x.restrict i).comp F ≅ (y'.restrict i').comp g := α
    exact ⟨pointSpace.mk ⟨L, fiberProductLift (x.restrict i) (y'.restrict i') τ⟩,
      pointSpace.sound (FieldPoint.equiv_restrict y' i')⟩
  obtain ⟨p₀, hp₀⟩ := surjective_mapPoints_of_smooth_presentation q hq z
  obtain ⟨u, hu⟩ := U.surjective_toPointSpace p₀
  refine ⟨u, ?_⟩
  obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (q.comp (fiberProductSnd F g))
  apply V.injective_toPointSpace
  have key : BasedFunctor.mapPoints (q.comp (fiberProductSnd F g)) (U.toPointSpace u)
      = V.toPointSpace v := by
    rw [mapPoints_comp, hu, hp₀, hz2]
  rw [mapPoints_eq_of_iso e] at key
  rw [← key, mapPoints_overBased_map_toPointSpace]

/-- An étale refinement of the source of a smooth presentation is again a smooth
presentation as soon as its map on point spaces is surjective. -/
lemma representableWith_surjective_smooth_comp_of_etale_of_surjective_mapPoints
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]
    {U W : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    (rho : W ⟶ U) (hrho : @_root_.AlgebraicGeometry.Etale W U rho)
    (hsurj : Function.Surjective
      (BasedFunctor.mapPoints ((overBased.map rho).comp q))) :
    BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) ((overBased.map rho).comp q) := by
  let i : overBased W ⥤ᵇ overBased U := overBased.map rho
  have hiEtale : i.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    BasedFunctor.relativelyRepresentableWith_of_overHom i (by simpa [i] using hrho)
  have hqSmooth : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) q :=
    hq.mono inf_le_right
  have hcompSmooth : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) (i.comp q) :=
    BasedFunctor.RelativelyRepresentableWith.comp_representableWith
      etale_le_smooth hiEtale hqSmooth
      (fun {S' S T} p f hp => isSmoothLocal_smooth.isLocalOnSourceAlong
        (X' := S') (X := S) (Y := T) p f ⟨hp.1, etale_le_smooth _ _ _ hp.2⟩)
  have hcompSmooth' : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})
      ((overBased.map rho).comp q) := by
    simpa [i] using hcompSmooth
  have hstackSurj : BasedFunctor.Surjective ((overBased.map rho).comp q) :=
    surjective_of_surjective_mapPoints_aux hsurj
  refine ⟨hcompSmooth'.1, ?_⟩
  intro T g A hA E hE V r hr
  let chart : overBased V ⥤ᵇ fiberProduct ((overBased.map rho).comp q) g :=
    (overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map r).comp E)
  have hchartRel : chart.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) :=
    ((BasedFunctor.relativelyRepresentableWith_ofPresheaf_map hr).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda V)).comp_target_isEquivalence E
  have hchartEtale : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) chart :=
    BasedFunctor.RelativelyRepresentableWith.representableWith le_rfl hchartRel
  have hchartSmooth : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) chart :=
    hchartEtale.mono (inf_le_inf le_rfl etale_le_smooth)
  have hsurjChart :=
    BasedFunctor.HasProperty.arbitraryBaseChart isSmoothLocal_surjective
      hstackSurj g chart hchartSmooth
  have hsmoothChart := hcompSmooth'.2 T g A hA E hE V r hr
  change @_root_.AlgebraicGeometry.Surjective V T
      (chart.comp (fiberProductSnd ((overBased.map rho).comp q) g)).overHom ∧
    @_root_.AlgebraicGeometry.Smooth V T
      (chart.comp (fiberProductSnd ((overBased.map rho).comp q) g)).overHom
  exact ⟨hsurjChart, by
    simpa only [chart, CategoryTheory.BasedFunctor.comp_assoc] using hsmoothChart⟩

/- LEDGER — **Definition 4.3.21** (`def:quasi-compact`) (noetherian stacks): an
algebraic stack is *noetherian* if it is
locally noetherian (`BasedCategory.IsLocallyNoetherian`, part 4.3.2), quasi-separated,
and quasi-compact. Quasi-separatedness requires the §4.2 diagonal
(`def:separated-for-representable-morphism` (2), ledgered in part 4.3.3) — to be
completed once Section4.2-Representability lands. The same applies to the second half of
the unlabeled exercise below (a quasi-separated algebraic stack is noetherian if and
only if it admits a smooth presentation by the spectrum of a noetherian ring). -/

variable {𝒳} in
/-- Reduction step for the unnumbered exercise following Definition 4.3.21: a smooth
presentation of an algebraic stack by an affine scheme
implies that the stack is quasi-compact. -/
theorem isQuasiCompact_of_exists_presentation_spec [IsAlgebraicStack 𝒳]
    (h : ∃ (A : CommRingCat.{u}) (p : overBased (Spec A) ⥤ᵇ 𝒳),
      BasedFunctor.RepresentableWith
        (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) p) :
    IsQuasiCompact 𝒳 := by
  obtain ⟨A, p, hp⟩ := h
  have hsurj : Function.Surjective (BasedFunctor.mapPoints p) :=
    surjective_mapPoints_of_smooth_presentation p hp
  have hcompactSource : CompactSpace (pointSpace (overBased (Spec A))) := by
    obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace (Spec A)
    exact e.symm.compactSpace
  let _ := hcompactSource
  change CompactSpace (pointSpace 𝒳)
  rw [← isCompact_univ_iff, ← hsurj.range_eq]
  exact isCompact_range (BasedFunctor.continuous_mapPoints p)

variable {𝒳} in
/-- API theorem for the unnumbered exercise following Definition 4.3.21: an algebraic
stack $\cX$ is quasi-compact if and only if there exists a smooth
presentation $\Spec A \to \cX$ from an affine scheme.

For the reverse implication, start from any smooth presentation `U → 𝒳`. Its point map
`U → |𝒳|` is open and surjective. The images of the affine opens of `U` therefore form
an open cover of the compact space `|𝒳|`; a finite subcover gives an affine finite
coproduct `W`, and the étale refinement `W → U` is still a smooth presentation. -/
theorem isQuasiCompact_iff_exists_presentation_spec [IsAlgebraicStack 𝒳] :
    IsQuasiCompact 𝒳 ↔ ∃ (A : CommRingCat.{u}) (p : overBased (Spec A) ⥤ᵇ 𝒳),
      BasedFunctor.RepresentableWith
        (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) p := by
  constructor
  · intro h𝒳
    classical
    let _ : CompactSpace (pointSpace 𝒳) := h𝒳
    obtain ⟨U, q, hq⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒳)
    let 𝒰 := U.affineCover
    have hopenNu : IsOpenMap (quotientMapOfPresentation.nu q) :=
      quotientMapOfPresentation.isOpenMap_nu_aux q hq
    have hsurjNu : Function.Surjective (quotientMapOfPresentation.nu q) :=
      (surjective_mapPoints_of_smooth_presentation q hq).comp U.surjective_toPointSpace
    have hopen : ∀ i, IsOpen
        (quotientMapOfPresentation.nu q '' Set.range (𝒰.f i).base) := fun i ↦
      hopenNu _ (𝒰.f i).isOpenEmbedding.isOpen_range
    have hcover : (Set.univ : Set (pointSpace 𝒳)) ⊆ ⋃ i,
        quotientMapOfPresentation.nu q '' Set.range (𝒰.f i).base := by
      intro x _
      obtain ⟨u, hu⟩ := hsurjNu x
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
      exact Set.mem_iUnion.mpr ⟨i, ⟨u, ⟨y, hy⟩, hu⟩⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
    let W : Scheme.{u} := ∐ (fun i : t ↦ 𝒰.X i.1)
    let rho₀ : (∐ (fun i : t ↦ 𝒰.X i.1)) ⟶ U :=
      CategoryTheory.Limits.Sigma.desc (f := fun i : t ↦ 𝒰.X i.1)
        (fun i : t ↦ 𝒰.f i.1)
    let rho : W ⟶ U := rho₀
    have hWaffine : IsAffine W := inferInstance
    let _ : IsAffine W := hWaffine
    have hrho : @_root_.AlgebraicGeometry.Etale W U rho := by
      exact IsZariskiLocalAtSource.sigmaDesc (P := @_root_.AlgebraicGeometry.Etale)
        (fun _ ↦ inferInstance)
    let pW : overBased W ⥤ᵇ 𝒳 := (overBased.map rho).comp q
    have hsurjPW : Function.Surjective (BasedFunctor.mapPoints pW) := by
      intro x
      have hx := ht (Set.mem_univ x)
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi, u, ⟨y, hy⟩, huy⟩ := hx
      let j : t := ⟨i, hi⟩
      let w : W :=
        (CategoryTheory.Limits.Sigma.ι (fun k : t ↦ 𝒰.X k.1) j).base y
      refine ⟨W.toPointSpace w, ?_⟩
      rw [show pW = (overBased.map rho).comp q from rfl,
        quotientMapOfPresentation.mapPoints_comp,
        quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace]
      change quotientMapOfPresentation.nu q (rho.base w) = x
      have hw : rho.base w = (𝒰.f i).base y := by
        change (CategoryTheory.Limits.Sigma.ι (fun k : t ↦ 𝒰.X k.1) j ≫ rho).base y = _
        simp [rho, rho₀, j]
      rw [hw, hy]
      exact huy
    have hpW : BasedFunctor.RepresentableWith
        (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) pW := by
      exact representableWith_surjective_smooth_comp_of_etale_of_surjective_mapPoints
        q hq rho hrho hsurjPW
    let A : CommRingCat.{u} := Γ(W, ⊤)
    let I : overBased (Spec A) ⥤ᵇ overBased W := overBased.map W.isoSpec.inv
    have hI : I.toFunctor.IsEquivalence := by
      change (Over.map W.isoSpec.inv).IsEquivalence
      infer_instance
    let _ : I.toFunctor.IsEquivalence := hI
    let p : overBased (Spec A) ⥤ᵇ 𝒳 := I.comp pW
    refine ⟨A, p, ?_⟩
    exact hpW.comp_source_isEquivalence I
  · exact isQuasiCompact_of_exists_presentation_spec

/- LEDGER (unlabeled example after the quasi-compactness exercise): the moduli stack
`𝓜_g` is noetherian, in particular quasi-compact, by the quotient presentation
`𝓜_g = [H'/PGL_{5g-5}]`; the stack `Bun_{r,d}(C)` is quasi-separated and locally
noetherian but not quasi-compact. Blocked on the moduli stacks (§3.4/§3.5/§4.1 ledgers,
`thm:mg-is-algebraic`, `thm:bunC-is-algebraic`). -/

end AlgebraicGeometry.BasedCategory

end DefQuasiCompact

section ExerSurjectiveEquivalences

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}} [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
  [IsAlgebraicStack 𝒴']

/-- **Exercise 4.3.24** (`exer:surjective-equivalences`) (part (b)): for morphisms of
algebraic stacks $\cX \to \cY$ and $\cY' \to \cY$, the canonical map
$|\cX \times_{\cY} \cY'| \to |\cX| \times_{|\cY|} |\cY'|$ is surjective: every pair of
points with the same image in $|\cY|$ lifts to a point of the fiber product. -/
theorem exists_mapPoints_fiberProduct_eq (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : pointSpace 𝒳) (y' : pointSpace 𝒴')
    (h : mapPoints F x = mapPoints G y') :
    ∃ z : pointSpace (fiberProduct F G),
      mapPoints (fiberProductFst F G) z = x ∧ mapPoints (fiberProductSnd F G) z = y' := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep x
  obtain ⟨y', rfl⟩ := Quot.exists_rep y'
  obtain ⟨L, hL, i, i', ⟨α⟩⟩ := pointSpace.mk_eq_mk_iff.mp h
  have τ : (x.restrict i).comp F ≅ (y'.restrict i').comp G := α
  refine ⟨pointSpace.mk ⟨L, fiberProductLift (x.restrict i) (y'.restrict i') τ⟩, ?_, ?_⟩
  · exact pointSpace.sound (FieldPoint.equiv_restrict x i)
  · exact pointSpace.sound (FieldPoint.equiv_restrict y' i')

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- API theorem from the first unnumbered exercise following Exercise 4.3.24
exercise following it): if $\cX$ is a quasi-compact and locally noetherian algebraic
stack, then $|\cX|$ is a noetherian topological space.

The proof uses the quasi-compact-to-affine-presentation implication of
`isQuasiCompact_iff_exists_presentation_spec`, whose finite affine-refinement argument
is axiom-clean. -/
theorem noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian [IsAlgebraicStack 𝒳]
    (h₁ : IsQuasiCompact 𝒳) (h₂ : IsLocallyNoetherian 𝒳) :
    TopologicalSpace.NoetherianSpace (pointSpace 𝒳) := by
  obtain ⟨A, p, hp⟩ := isQuasiCompact_iff_exists_presentation_spec.mp h₁
  have hloc : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec A) := h₂ (Spec A) p hp
  have hring : IsNoetherianRing A := AlgebraicGeometry.isLocallyNoetherian_Spec.mp hloc
  let _ := hring
  have hsource : TopologicalSpace.NoetherianSpace
      (pointSpace (overBased (Spec A))) := by
    obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace (Spec A)
    exact (TopologicalSpace.noetherianSpace_iff_of_homeomorph e).mpr inferInstance
  let _ := hsource
  exact TopologicalSpace.noetherianSpace_of_surjective (BasedFunctor.mapPoints p)
    (BasedFunctor.continuous_mapPoints p)
    (surjective_mapPoints_of_smooth_presentation p hp)

namespace quotientMapOfPresentation

open CategoryTheory.Functor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒵 : BasedCategory.{v₄, u₄} Scheme.{u}}

end quotientMapOfPresentation

open quotientMapOfPresentation in
/-- API theorem from the second unnumbered exercise following Exercise 4.3.24
exercise following it; submersiveness of presentations): if $U \to \cX$ is a smooth
presentation of an algebraic stack, then the induced map $|\Sch/U| \to |\cX|$ is
submersive: it is surjective and $|\cX|$ carries the quotient topology. (Identify
$|\Sch/U|$ with the underlying space of $U$ via
`AlgebraicGeometry.Scheme.toPointSpace`.) -/
theorem isQuotientMap_mapPoints_of_presentation [IsAlgebraicStack 𝒳] {U : Scheme.{u}}
    (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) q) :
    Topology.IsQuotientMap (BasedFunctor.mapPoints q) := by
  exact isQuotientMap_mapPoints_of_presentation_aux q hq

end AlgebraicGeometry.BasedCategory

end ExerSurjectiveEquivalences

section ExerSurjectiveEquivalences

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedCategory

open quotientMapOfPresentation in
/-- Helper theorem from the second unnumbered exercise following Exercise 4.3.24
exercise following it): a smooth presentation of a prestack induces a *surjection* on
points. This is the surjectivity half of `isQuotientMap_mapPoints_of_presentation`, split
off because it needs no `[IsAlgebraicStack _]` hypothesis — which is what makes it usable
for the fiber product `𝒳 ×_𝒴 (Sch/V)`, whose algebraicity is not available. (The proof is
verbatim the third bullet of `isQuotientMap_mapPoints_of_presentation`, which can now be
replaced by `exact surjective_mapPoints_of_representableWith q hq`.) -/
lemma surjective_mapPoints_of_representableWith
    {𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}} {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒵)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    Function.Surjective (BasedFunctor.mapPoints q) := by
  exact surjective_mapPoints_of_smooth_presentation q hq

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- Reduction step for Exercise 4.3.24, part (a), the direction "⇐":
if $|\cX| \to |\cY|$ is surjective then $\cX \to \cY$ is a surjective morphism of
prestacks — for every pair of smooth presentations $V \to \cY$ and
$U \to \cX \times_{\cY} V$ the induced morphism of schemes $U \to V$ is surjective. No
algebraicity hypothesis is needed: the two presentations are *given* by the definition of
`BasedFunctor.Surjective`.

Given $v \in V$, surjectivity of $|\cX| \to |\cY|$ produces $x \in |\cX|$ over the point
$\nu_g(v) \in |\cY|$; part (b) of the exercise lifts the pair $(x, v)$ to a point of
$|\cX \times_{\cY} V|$; the presentation $U \to \cX \times_{\cY} V$ is surjective on
points (`surjective_mapPoints_of_representableWith`), so that point comes from some
$u \in U$ (`Scheme.surjective_toPointSpace`); and $|U| \to |V|$ is computed by
$U \to V$ because `q.comp (fiberProductSnd F g) ≅ overBased.map _` — whence
$u \mapsto v$ by injectivity of `V.toPointSpace`. -/
theorem surjective_of_surjective_mapPoints {F : 𝒳 ⥤ᵇ 𝒴}
    (hs : Function.Surjective (mapPoints F)) : Surjective F := by
  exact AlgebraicGeometry.BasedCategory.surjective_of_surjective_mapPoints_aux hs

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- Reduction step for Exercise 4.3.24, part (a), the direction "⇒",
with the presentations supplied): if $\cX \to \cY$ is surjective and $V \to \cY$,
$U \to \cX \times_{\cY} V$ are smooth presentations, then $|\cX| \to |\cY|$ is surjective.
No algebraicity hypothesis is needed — the presentations are the hypotheses.

Every point of $|\cY|$ is $\nu_g(v)$ for some $v \in V$
(`surjective_mapPoints_of_representableWith` for $g$, then
`Scheme.surjective_toPointSpace`); surjectivity of $U \to V$ lifts $v$ to $u \in U$; and
the image in $|\cX|$ of $u$ under $U \to \cX \times_{\cY} V \to \cX$ maps to $\nu_g(v)$ by
the 2-commutativity `fiberProductIsoComm`. -/
theorem surjective_mapPoints_of_surjective_of_presentation {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : Surjective F) {V : Scheme.{u}} {g : overBased V ⥤ᵇ 𝒴}
    (hg : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) g)
    {U : Scheme.{u}} {q : overBased U ⥤ᵇ BasedCategory.fiberProduct F g}
    (hq : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    Function.Surjective (mapPoints F) := by
  intro y
  obtain ⟨p, hp⟩ :=
    AlgebraicGeometry.BasedCategory.surjective_mapPoints_of_representableWith g hg y
  obtain ⟨v, hv⟩ := V.surjective_toPointSpace p
  obtain ⟨u, hu⟩ := (hF V g hg U q hq).surj v
  obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (q.comp (fiberProductSnd F g))
  have hcomm : (q.comp (fiberProductFst F g)).comp F
      ≅ (q.comp (fiberProductSnd F g)).comp g := by
    rw [CategoryTheory.BasedFunctor.comp_assoc, CategoryTheory.BasedFunctor.comp_assoc]
    exact BasedCategory.isoWhiskerLeft q (fiberProductIsoComm F g)
  refine ⟨mapPoints (q.comp (fiberProductFst F g)) (U.toPointSpace u), ?_⟩
  rw [← mapPoints_comp, mapPoints_eq_of_iso hcomm, mapPoints_comp,
    mapPoints_eq_of_iso e, mapPoints_overBased_map_toPointSpace, hu, hv, hp]

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

/-- **Exercise 4.3.24** (`exer:surjective-equivalences`) (part (a)): a morphism of
algebraic stacks $\cX \to \cY$ is surjective (in the sense of Definition 4.3.2, part
(2)) if and only if the induced map
$|\cX| \to |\cY|$ is surjective.

"⇐" is `surjective_of_surjective_mapPoints` and needs no algebraicity. "⇒" is
`surjective_mapPoints_of_surjective_of_presentation` applied to a smooth presentation
$V \to \cY$ of $\cY$ together with one of $\cX \times_{\cY} V$; producing the latter is
where algebraicity enters, through `IsAlgebraicStack.fiberProduct` (§4.1's unlabeled
fiber-products exercise) and `isAlgebraicStack_overBased`. Both inputs are now proved
without `sorry`; consequently both directions are unconditional and axiom-clean. -/
theorem surjective_iff_surjective_mapPoints (F : 𝒳 ⥤ᵇ 𝒴) :
    Surjective F ↔ Function.Surjective (mapPoints F) := by
  refine ⟨fun hF => ?_, surjective_of_surjective_mapPoints⟩
  obtain ⟨V, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
  have : IsAlgebraicStack (overBased V) := isAlgebraicStack_overBased V
  have : IsAlgebraicStack (BasedCategory.fiberProduct F g) :=
    IsAlgebraicStack.fiberProduct F g
  obtain ⟨U, q, hq⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := BasedCategory.fiberProduct F g)
  exact surjective_mapPoints_of_surjective_of_presentation hF hg hq

end AlgebraicGeometry.BasedFunctor

end ExerSurjectiveEquivalences

section ExerFppfMorphismsAreOpen

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry

/-- API lemma used for Exercise 4.3.27 (universally open is smooth
local): universal openness of morphisms of schemes is smooth local (on the source and
the target), so universally open morphisms of algebraic stacks can be defined by
Definition 4.3.2, part (2). (Source-locality is missing from Mathlib and
is deferred.) -/
theorem isSmoothLocal_universallyOpen :
    IsSmoothLocal (@UniversallyOpen : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := by
    intro A X Y g f hg
    obtain ⟨hgs, hgsm⟩ := hg
    have : Surjective g := hgs
    have : Smooth g := hgsm
    refine ⟨fun hf => by have := hf; infer_instance, fun hgf => ?_⟩
    have := hgf
    refine ⟨fun {P Q} i₁ i₂ f' hsq => ?_⟩
    have s : IsPullback (Limits.pullback.snd g i₁) (Limits.pullback.fst g i₁) i₁ g :=
      (IsPullback.of_hasPullback g i₁).flip
    have hopen : IsOpenMap (Limits.pullback.snd g i₁ ≫ f').base :=
      UniversallyOpen.universally_isOpenMap (f := g ≫ f) _ _ _ (s.paste_horiz hsq)
    have hsurj : Function.Surjective (Limits.pullback.snd g i₁).base :=
      (MorphismProperty.pullback_snd g i₁ ‹Surjective g›).surj
    intro U hU
    have h1 : f'.base '' U
        = (Limits.pullback.snd g i₁ ≫ f').base '' ((Limits.pullback.snd g i₁).base ⁻¹' U) := by
      rw [Scheme.Hom.comp_base]
      simp only [TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp]
      rw [Set.image_preimage_eq _ hsurj]
    rw [h1]
    exact hopen _ (hU.preimage (Limits.pullback.snd g i₁).base.hom.continuous)
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

namespace BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- Background definition used in Exercise 4.3.27: a morphism of algebraic stacks is
*universally open* if it
has the (smooth local) property of universal openness of morphisms of schemes. -/
abbrev UniversallyOpen (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty (@_root_.AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u}) F

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] [IsAlgebraicStack 𝒴']

/-- **Exercise 4.3.27** (`exer:fppf-morphisms-are-open`) (fppf morphisms are
universally open): a flat morphism of algebraic stacks which is locally of finite
presentation is universally open. (The book says "faithfully flat morphisms locally of
finite presentation are universally open"; surjectivity is not needed for openness, so
it is dropped here — see this folder's COMMENTARY.md.) -/
theorem universallyOpen_of_flat_of_locallyOfFinitePresentation {F : 𝒳 ⥤ᵇ 𝒴}
    (h₁ : Flat F) (h₂ : LocallyOfFinitePresentation F) : UniversallyOpen F := by
  intro V g hg U q hq
  have := h₁ V g hg U q hq
  have := h₂ V g hg U q hq
  infer_instance

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- **Exercise 4.3.27** (`exer:fppf-morphisms-are-open`) (openness of the image): if
$f \colon \cX \to \cY$ is a universally open morphism of algebraic stacks, then the
image $f(|\cX|) \subseteq |\cY|$ is open. -/
theorem isOpen_range_mapPoints_of_universallyOpen {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : UniversallyOpen F) : IsOpen (Set.range (mapPoints F)) := by
  obtain ⟨V, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
  apply isOpen_of_isOpen_preimage g hg
  have : IsAlgebraicStack (fiberProduct F g) := IsAlgebraicStack.fiberProduct F g
  obtain ⟨U, q, hq⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := fiberProduct F g)
  let p := fiberProductSnd F g
  let f := (q.comp p).overHom
  have hf : _root_.AlgebraicGeometry.UniversallyOpen f := hF V g hg U q hq
  let _ : _root_.AlgebraicGeometry.UniversallyOpen f := hf
  have hqsurj : Function.Surjective (mapPoints q) :=
    AlgebraicGeometry.BasedCategory.surjective_mapPoints_of_representableWith q hq
  have hpre : mapPoints g ⁻¹' Set.range (mapPoints F) =
      Set.range (mapPoints p) := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨z, -, hz⟩ := exists_mapPoints_fiberProduct_eq F g x y hx
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      refine ⟨mapPoints (fiberProductFst F g) z, ?_⟩
      rw [← mapPoints_comp, ← mapPoints_comp,
        mapPoints_eq_of_iso (fiberProductIsoComm F g)]
  have hpresentation : Set.range (mapPoints p) =
      Set.range (mapPoints (q.comp p)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, rfl⟩
      obtain ⟨u, hu⟩ := hqsurj z
      refine ⟨u, ?_⟩
      rw [mapPoints_comp, hu]
    · rintro y ⟨u, rfl⟩
      exact ⟨mapPoints q u, (mapPoints_comp q p u).symm⟩
  obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map (q.comp p)
  have hscheme : Set.range (mapPoints (q.comp p)) =
      V.toPointSpace '' Set.range f.base := by
    rw [AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso e]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨u, rfl⟩ := U.surjective_toPointSpace a
      exact ⟨f.base u, ⟨u, rfl⟩,
        (mapPoints_overBased_map_toPointSpace f u).symm⟩
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      exact ⟨U.toPointSpace u, mapPoints_overBased_map_toPointSpace f u⟩
  rw [hpre, hpresentation, hscheme]
  apply V.isOpenMap_toPointSpace
  simpa only [Set.image_univ] using f.isOpenMap Set.univ isOpen_univ

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- **Exercise 4.3.27** (`exer:fppf-morphisms-are-open`) (the concluding statement): if
$f \colon \cX \to \cY$ is a universally open morphism of algebraic stacks, then for
every morphism $\cY' \to \cY$ of algebraic stacks the map
$|\cX \times_{\cY} \cY'| \to |\cY'|$ is open. -/
theorem isOpenMap_mapPoints_fiberProductSnd_of_universallyOpen {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : UniversallyOpen F) (G : 𝒴' ⥤ᵇ 𝒴) :
    IsOpenMap (mapPoints (fiberProductSnd F G)) := by
  let H := fiberProductSnd F G
  intro V hV
  obtain ⟨T, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴')
  apply AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.isOpen_of_isOpen_preimage
    g hg
  let _ : IsAlgebraicStack (fiberProduct F G) :=
    IsAlgebraicStack.fiberProduct F G
  let _ : IsAlgebraicStack (fiberProduct H g) :=
    IsAlgebraicStack.fiberProduct H g
  obtain ⟨U, q, hq⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := fiberProduct H g)
  let A := fiberProductAssoc F G g
  let _ : A.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F G g
  have hqA : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) (q.comp A) :=
    hq.comp_target_isEquivalence A
  have hf' : _root_.AlgebraicGeometry.UniversallyOpen
      ((q.comp A).comp (fiberProductSnd F (g.comp G))).overHom :=
    HasProperty.arbitraryBaseChart isSmoothLocal_universallyOpen hF
      (g.comp G) (q.comp A) hqA
  let b := q.comp (fiberProductSnd H g)
  let f := b.overHom
  have hstruct : (q.comp A).comp (fiberProductSnd F (g.comp G)) = b := by
    change q.comp ((fiberProductAssoc F G g).comp
      (fiberProductSnd F (g.comp G))) =
        q.comp (fiberProductSnd (fiberProductSnd F G) g)
    rw [fiberProductAssoc_comp_snd]
  have hf : _root_.AlgebraicGeometry.UniversallyOpen f := by
    rw [hstruct] at hf'
    exact hf'
  let _ : _root_.AlgebraicGeometry.UniversallyOpen f := hf
  let l := q.comp (fiberProductFst H g)
  let W : Set U := U.toPointSpace ⁻¹' (mapPoints l ⁻¹' V)
  have hW : IsOpen W := by
    exact (hV.preimage (continuous_mapPoints l)).preimage
      (AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.continuous_toPointSpace U)
  have hqsurj : Function.Surjective (mapPoints q) :=
    AlgebraicGeometry.BasedCategory.surjective_mapPoints_of_representableWith q hq
  obtain ⟨eb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map b
  have hcomm : l.comp H ≅ b.comp g := by
    exact BasedCategory.isoWhiskerLeft q (fiberProductIsoComm H g)
  have hset : mapPoints g ⁻¹' (mapPoints H '' V) =
      T.toPointSpace '' (f.base '' W) := by
    ext y
    constructor
    · rintro ⟨z, hzV, hz⟩
      obtain ⟨w, hwfst, hwsnd⟩ :=
        exists_mapPoints_fiberProduct_eq H g z y hz
      obtain ⟨u, hu⟩ := hqsurj w
      obtain ⟨x, hx⟩ := U.surjective_toPointSpace u
      refine ⟨f.base x, ⟨x, ?_, rfl⟩, ?_⟩
      · change mapPoints l (U.toPointSpace x) ∈ V
        rw [hx, mapPoints_comp, hu, hwfst]
        exact hzV
      · have hb : mapPoints b (U.toPointSpace x) = T.toPointSpace (f.base x) := by
          rw [mapPoints_eq_of_iso eb, mapPoints_overBased_map_toPointSpace]
        rw [← hb, hx, mapPoints_comp, hu, hwsnd]
    · rintro ⟨t, ⟨x, hxW, rfl⟩, rfl⟩
      refine ⟨mapPoints l (U.toPointSpace x), hxW, ?_⟩
      rw [← mapPoints_comp, mapPoints_eq_of_iso hcomm, mapPoints_comp,
        mapPoints_eq_of_iso eb, mapPoints_overBased_map_toPointSpace]
  rw [hset]
  exact T.isOpenMap_toPointSpace _ (f.isOpenMap _ hW)

end BasedFunctor

end AlgebraicGeometry

end ExerFppfMorphismsAreOpen

section ExerSpecializationProperties

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Background definition of quasi-compact morphisms following Exercise 4.3.27: a morphism
$\cX \to \cY$ of algebraic stacks is *quasi-compact* if for every morphism
$\Spec B \to \cY$, the fiber product $\cX \times_{\cY} \Spec B$ is a quasi-compact
algebraic stack. -/
def QuasiCompact [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids] (F : 𝒳 ⥤ᵇ 𝒴) :
    Prop :=
  ∀ (B : CommRingCat.{u}) (g : overBased (Spec B) ⥤ᵇ 𝒴),
    BasedCategory.IsQuasiCompact (fiberProduct F g)

/-- Background definition of finite type morphisms following Exercise 4.3.27: a morphism
$\cX \to \cY$
of algebraic stacks is of *finite type* if it is locally of finite type and
quasi-compact. -/
def FiniteType [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids] (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  LocallyOfFiniteType F ∧ QuasiCompact F

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedCategory

variable {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A point of a prestack has a *quasi-compact representative* if it is represented by
a field-valued morphism `Spec K → 𝒴` which is quasi-compact after every affine base
change. This is the pointwise quasi-compactness condition also called decency of the
chosen representative in the modern treatment of points of algebraic stacks. -/
def HasQuasiCompactRepresentative [𝒴.p.IsFiberedInGroupoids]
    (y : pointSpace 𝒴) : Prop :=
  ∃ p : FieldPoint 𝒴, pointSpace.mk p = y ∧ BasedFunctor.QuasiCompact p.hom

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/- LEDGER (unlabeled example): `𝓜_g` is of finite type over `ℤ`, while `Bun_{r,d}(C)`
is locally of finite type but not of finite type. Blocked on the moduli stacks
(§3.4/§3.5/§4.1 ledgers). -/

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- **Exercise 4.3.31** (`exer:specialization-properties`) (part (a)): let
$f \colon \cX \to \cY$ be a quasi-compact
morphism of algebraic stacks and let $y \in |\cY|$. Then $y$ lies in the closure of the
image of $|\cX|$ if and only if there exists $x \in |\cX|$ with a specialization
$f(x) \rightsquigarrow y$. -/
theorem mem_closure_range_mapPoints_iff_specializes {F : 𝒳 ⥤ᵇ 𝒴} (hF : QuasiCompact F)
    (y : pointSpace 𝒴) :
    y ∈ closure (Set.range (mapPoints F)) ↔ ∃ x : pointSpace 𝒳, mapPoints F x ⤳ y := by
  constructor
  · intro hy
    obtain ⟨U, q, hq⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
    have hsurjNu : Function.Surjective
        (AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu q) :=
      (AlgebraicGeometry.BasedCategory.surjective_mapPoints_of_smooth_presentation q hq).comp
        U.surjective_toPointSpace
    obtain ⟨u, hu⟩ := hsurjNu y
    let C := U.affineCover
    obtain ⟨i, w, rfl⟩ := C.exists_eq u
    let B : CommRingCat.{u} := Γ(C.X i, ⊤)
    let rho : Spec B ⟶ U := (C.X i).isoSpec.inv ≫ C.f i
    let b : Spec B := (C.X i).isoSpec.hom.base w
    have hrhob : rho.base b = (C.f i).base w := by
      change ((C.X i).isoSpec.hom ≫ (C.X i).isoSpec.inv ≫ C.f i).base w = _
      rw [Iso.hom_inv_id_assoc]
    let g : overBased (Spec B) ⥤ᵇ 𝒴 := (overBased.map rho).comp q
    have hgb : AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu g b = y := by
      rw [AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu_comp_map,
        hrhob, hu]
    have hopenRho : IsOpenMap rho.base := by
      have hopenIso : IsOpenMap (C.X i).isoSpec.inv.base :=
        (TopCat.homeoOfIso (asIso (C.X i).isoSpec.inv.base)).isOpenMap
      exact (C.f i).isOpenEmbedding.isOpenMap.comp hopenIso
    have hopenG : IsOpenMap
        (AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu g) := by
      have hopenQ :=
        AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.isOpenMap_nu_aux q hq
      intro V hV
      rw [show AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu g '' V =
          AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu q ''
            (rho.base '' V) by
        ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨rho.base t, ⟨t, ht, rfl⟩,
            by simpa only [g] using
              (AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu_comp_map
                rho q t).symm⟩
        · rintro ⟨-, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t, ht, by simpa only [g] using
            AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu_comp_map rho q t⟩]
      exact hopenQ _ (hopenRho _ hV)
    let P := fiberProduct F g
    let p₂ : P ⥤ᵇ overBased (Spec B) := fiberProductSnd F g
    have hPqc : BasedCategory.IsQuasiCompact P := hF B g
    let _ : IsAlgebraicStack P := IsAlgebraicStack.fiberProduct F g
    obtain ⟨A, p, hp⟩ :=
      BasedCategory.isQuasiCompact_iff_exists_presentation_spec.mp hPqc
    have hpSurj : Function.Surjective (mapPoints p) :=
      AlgebraicGeometry.BasedCategory.surjective_mapPoints_of_smooth_presentation p hp
    let r : Spec A ⟶ Spec B := (p.comp p₂).overHom
    obtain ⟨er⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map (p.comp p₂)
    have hpre : mapPoints g ⁻¹' Set.range (mapPoints F) =
        Set.range (mapPoints p₂) := by
      ext t
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨z, -, hz⟩ := exists_mapPoints_fiberProduct_eq F g x t hx
        exact ⟨z, hz⟩
      · rintro ⟨z, rfl⟩
        refine ⟨mapPoints (fiberProductFst F g) z, ?_⟩
        rw [← mapPoints_comp, ← mapPoints_comp,
          mapPoints_eq_of_iso (fiberProductIsoComm F g)]
    have hpRange : Set.range (mapPoints p₂) =
        Set.range (mapPoints (p.comp p₂)) := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, rfl⟩
        obtain ⟨a, rfl⟩ := hpSurj t
        exact ⟨a, mapPoints_comp p p₂ a⟩
      · rintro z ⟨a, rfl⟩
        exact ⟨mapPoints p a, (mapPoints_comp p p₂ a).symm⟩
    have hrScheme : Set.range (mapPoints (p.comp p₂)) =
        (Spec B).toPointSpace '' Set.range r.base := by
      rw [mapPoints_eq_of_iso er]
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨a, rfl⟩ := (Spec A).surjective_toPointSpace a
        exact ⟨r.base a, ⟨a, rfl⟩,
          (mapPoints_overBased_map_toPointSpace r a).symm⟩
      · rintro ⟨-, ⟨a, rfl⟩, rfl⟩
        exact ⟨(Spec A).toPointSpace a,
          mapPoints_overBased_map_toPointSpace r a⟩
    have hrange :
        AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu g ⁻¹'
            Set.range (mapPoints F) = Set.range r.base := by
      ext t
      change (Spec B).toPointSpace t ∈ mapPoints g ⁻¹'
          Set.range (mapPoints F) ↔ t ∈ Set.range r.base
      rw [hpre, hpRange, hrScheme]
      constructor
      · rintro ⟨t', ⟨a, ha⟩, ht'⟩
        refine ⟨a, (Spec B).injective_toPointSpace ?_⟩
        rw [ha]
        exact ht'
      · rintro ⟨a, rfl⟩
        exact ⟨r.base a, ⟨a, rfl⟩, rfl⟩
    have hbClosure : b ∈ closure (Set.range r.base) := by
      rw [← hrange]
      exact hopenG.preimage_closure_subset_closure_preimage (by
        change AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nu g b ∈
          closure (Set.range (mapPoints F))
        rwa [hgb])
    let _ : _root_.AlgebraicGeometry.QuasiCompact r := inferInstance
    obtain ⟨a, ha⟩ :=
      Scheme.Hom.exists_specializes_of_mem_closure_range_of_quasiCompact_of_isAffine
        r hbClosure
    let z : pointSpace P := mapPoints p ((Spec A).toPointSpace a)
    refine ⟨mapPoints (fiberProductFst F g) z, ?_⟩
    have hpa : mapPoints p₂ z = (Spec B).toPointSpace (r.base a) := by
      rw [show z = mapPoints p ((Spec A).toPointSpace a) from rfl,
        ← mapPoints_comp, mapPoints_eq_of_iso er,
        mapPoints_overBased_map_toPointSpace]
    have hs := (ha.map
      (continuous_toPointSpace (Spec B))).map (continuous_mapPoints g)
    have hgb' : mapPoints g ((Spec B).toPointSpace b) = y := hgb
    rw [← hpa, hgb'] at hs
    have hcomm : mapPoints F (mapPoints (fiberProductFst F g) z) =
        mapPoints g (mapPoints p₂ z) := by
      simpa only [mapPoints_comp] using
        congrFun (mapPoints_eq_of_iso (fiberProductIsoComm F g)) z
    rw [hcomm]
    exact hs
  · rintro ⟨x, hx⟩
    have hsub : ({mapPoints F x} : Set (pointSpace 𝒴)) ⊆ Set.range (mapPoints F) :=
      Set.singleton_subset_iff.mpr ⟨x, rfl⟩
    exact closure_mono hsub hx.mem_closure

/- LEDGER — **Exercise 4.3.31** (`exer:specialization-properties`) (parts (c),
`exer:specialization-sober`, and (d), `exer:specialization-chevalley`): (c) for a quasi-separated
algebraic stack `𝒳`, the space `|𝒳|` is sober (`QuasiSober (pointSpace 𝒳)`); (d)
Chevalley's criterion: the image of a finitely presented morphism of algebraic stacks is
constructible (`Topology.IsConstructible`). Both hypotheses (quasi-separatedness, finite
presentation) require the §4.2 diagonal (part 4.3.3 ledger) — to be completed once
Section4.2-Representability lands. See also Stacks 0DQQ–0GVY. -/

end AlgebraicGeometry.BasedFunctor

end ExerSpecializationProperties

section ExerGenericFlatnessAlgebraicStacks

/- LEDGER — **Exercise 4.3.32** (`exer:generic-flatness-algebraic-stacks`): generic
flatness for algebraic
stacks — for a finite type morphism `𝒳 → 𝒴` of algebraic stacks with `𝒴` reduced, there
is a dense open substack `𝒰 ⊆ 𝒴` over which the base change is flat and of finite
presentation. Blocked on generic flatness for morphisms of schemes
(`thm:generic-flatness`, appendix A.2, absent from both Mathlib and StacksAndModuli; Stacks
052A) and on the notion of dense open substacks. -/

end ExerGenericFlatnessAlgebraicStacks

section ExerLocallyOfFinitePresentationAlgebraicStacks

/- LEDGER — **Exercise 4.3.33**
(`exer:locally-of-finite-presentation-algebraic-stacks`): the functorial
characterization of locally of finite presentation morphisms — `𝒳 → 𝒴` is locally of
finite presentation if and only if for every directed system `{Spec A_λ}` of affine
schemes over `𝒴`, the functor `colim_λ MOR_𝒴(Spec A_λ, 𝒳) → MOR_𝒴(Spec (colim A_λ), 𝒳)`
is an equivalence of categories. Blocked on 2-categorical filtered colimits of the
hom-categories `MOR_𝒴(Spec A_λ, 𝒳)` (cf. LMB 4.15, Stacks 0CMY region) and on
`prop:finite-presentation-functorial` (appendix). -/

end ExerLocallyOfFinitePresentationAlgebraicStacks

section PointSpaceSupport

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory
  AlgebraicGeometry.BasedCategory.quotientMapOfPresentation

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry

namespace BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- A morphism of prestacks fibered in groupoids induces a continuous map on points.
This is `AlgebraicGeometry.BasedFunctor.continuous_mapPoints` with `IsAlgebraicStack`
weakened to `IsFiberedInGroupoids` (the proof never uses algebraicity); the weaker form
is useful independently of algebraicity and applies to arbitrary prestacks fibered in
groupoids. -/
theorem continuous_mapPoints' [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    (F : 𝒳 ⥤ᵇ 𝒴) : Continuous (BasedFunctor.mapPoints F) := by
  rw [continuous_def]
  rintro V ⟨𝒱, j, hj, rfl⟩
  have := hj
  exact ⟨𝒳.restrict (fun a => j.fiberEssImage (F.obj a)), 𝒳.restrictι _,
    isOpenSubstackInclusion_restrictι_comap F j,
    (range_mapPoints_restrictι_comap F j).symm⟩

/-- An equivalence of prestacks fibered in groupoids induces a closed map on point
spaces. -/
theorem isClosedMap_mapPoints_of_isEquivalence
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    (E : 𝒳 ⥤ᵇ 𝒴) (hE : E.toFunctor.IsEquivalence) :
    IsClosedMap (BasedFunctor.mapPoints E) := by
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨I, ⟨α⟩, ⟨β⟩⟩ := CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  have hleft (x : pointSpace 𝒳) :
      mapPoints I (mapPoints E x) = x := by
    rw [← quotientMapOfPresentation.mapPoints_comp E I,
      quotientMapOfPresentation.mapPoints_eq_of_iso α, mapPoints_id]
    rfl
  have hright (y : pointSpace 𝒴) :
      mapPoints E (mapPoints I y) = y := by
    rw [← quotientMapOfPresentation.mapPoints_comp I E,
      quotientMapOfPresentation.mapPoints_eq_of_iso β, mapPoints_id]
    rfl
  intro C hC
  rw [show mapPoints E '' C = mapPoints I ⁻¹' C by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change mapPoints I (mapPoints E x) ∈ C
      rw [hleft]
      exact hx
    · intro hy
      exact ⟨mapPoints I y, hy, hright y⟩]
  exact hC.preimage (continuous_mapPoints' I)

/-- The canonical map `|𝒳 ×_𝒴 𝒴'| → |𝒳| ×_{|𝒴|} |𝒴'|` is surjective. This is
`AlgebraicGeometry.BasedFunctor.exists_mapPoints_fiberProduct_eq` with the
`IsAlgebraicStack` hypotheses dropped (its proof only uses the description of the fiber
product of prestacks). -/
theorem exists_mapPoints_fiberProduct_eq' (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : pointSpace 𝒳) (y' : pointSpace 𝒴')
    (h : mapPoints F x = mapPoints G y') :
    ∃ z : pointSpace (fiberProduct F G),
      mapPoints (fiberProductFst F G) z = x ∧ mapPoints (fiberProductSnd F G) z = y' := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep x
  obtain ⟨y', rfl⟩ := Quot.exists_rep y'
  obtain ⟨L, hL, i, i', ⟨α⟩⟩ := pointSpace.mk_eq_mk_iff.mp h
  have τ : (x.restrict i).comp F ≅ (y'.restrict i').comp G := α
  refine ⟨pointSpace.mk ⟨L, fiberProductLift (x.restrict i) (y'.restrict i') τ⟩, ?_, ?_⟩
  · exact pointSpace.sound (FieldPoint.equiv_restrict x i)
  · exact pointSpace.sound (FieldPoint.equiv_restrict y' i')

/-- **An equivalence of prestacks fibered in groupoids is surjective on points.**

Given a field-valued point `y : Spec K → ℬ`, its value at `𝟙 (Spec K)` is an object `d`
of `ℬ` over `Spec K`. Essential surjectivity of `E` produces an object `c₀` of `𝒜` and an
isomorphism `E c₀ ≅ d`; the induced isomorphism `θ` of the base objects is then lifted
cartesianly (`IsFiberedInGroupoids.exists_isHomLift`) to an object `c₁` of `𝒜` lying over
`Spec K` together with an isomorphism `E c₁ ≅ d` over `𝟙 (Spec K)`. The 2-Yoneda lemma
turns `c₁` into a field-valued point of `𝒜` mapping to `y`. -/
theorem surjective_mapPoints_of_isEquivalence
    {𝒜 : BasedCategory.{v₂, u₂} Scheme.{u}} {ℬ : BasedCategory.{v₃, u₃} Scheme.{u}}
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    (E : 𝒜 ⥤ᵇ ℬ) (hE : E.toFunctor.IsEquivalence) :
    Function.Surjective (mapPoints E) := by
  have := hE
  intro v
  induction v using pointSpace.ind with
  | _ y =>
  set S : Scheme.{u} := Spec (CommRingCat.of y.carrier) with hS
  set d : ℬ.obj := y.hom.obj (Over.mk (𝟙 S)) with hd_def
  have hd : ℬ.p.obj d = S := y.hom.w_obj _
  set c₀ : 𝒜.obj := E.toFunctor.objPreimage d with hc₀
  set φ : E.obj c₀ ≅ d := E.toFunctor.objObjPreimageIso d with hφ
  have hE0 : ℬ.p.obj (E.obj c₀) = 𝒜.p.obj c₀ := E.w_obj c₀
  set θ : 𝒜.p.obj c₀ ⟶ S := eqToHom hE0.symm ≫ ℬ.p.map φ.hom ≫ eqToHom hd with hθ
  have hθiso : _root_.CategoryTheory.IsIso θ := by
    rw [hθ]; infer_instance
  have hlift : Functor.IsHomLift ℬ.p θ φ.hom :=
    _root_.CategoryTheory.IsHomLift.of_fac ℬ.p θ φ.hom hE0 hd rfl
  have := hlift
  obtain ⟨c₁, χ, hχ⟩ := Functor.IsFiberedInGroupoids.exists_isHomLift (p := 𝒜.p)
    (CategoryTheory.inv θ)
  have := hχ
  have hcS : 𝒜.p.obj c₁ = S :=
    _root_.CategoryTheory.IsHomLift.domain_eq 𝒜.p (CategoryTheory.inv θ) χ
  have h1 : Functor.IsHomLift ℬ.p (CategoryTheory.inv θ) (E.map χ) := inferInstance
  have h2 : Functor.IsHomLift ℬ.p (CategoryTheory.inv θ ≫ θ) (E.map χ ≫ φ.hom) :=
    _root_.CategoryTheory.IsHomLift.comp ℬ.p _ _ _ _
  rw [CategoryTheory.IsIso.inv_hom_id] at h2
  have hTY := CategoryTheory.BasedCategory.isEquivalence_twoYonedaEval (𝒳 := 𝒜) S
  have := hTY
  set z : overBased S ⥤ᵇ 𝒜 :=
    (twoYonedaEval (𝒳 := 𝒜) S).objPreimage (Functor.Fiber.mk hcS) with hz
  set ι : (twoYonedaEval (𝒳 := 𝒜) S).obj z ≅ Functor.Fiber.mk hcS :=
    (twoYonedaEval (𝒳 := 𝒜) S).objObjPreimageIso (Functor.Fiber.mk hcS) with hι
  have hι2 : Functor.IsHomLift 𝒜.p (𝟙 S) (Functor.Fiber.fiberInclusion.map ι.hom) :=
    ι.hom.2
  have := hι2
  have h3 : Functor.IsHomLift ℬ.p (𝟙 S)
      (E.map (Functor.Fiber.fiberInclusion.map ι.hom)) := inferInstance
  have := h2
  have h4 : Functor.IsHomLift ℬ.p (𝟙 S ≫ 𝟙 S)
      (E.map (Functor.Fiber.fiberInclusion.map ι.hom) ≫ (E.map χ ≫ φ.hom)) :=
    _root_.CategoryTheory.IsHomLift.comp ℬ.p _ _ _ _
  rw [Category.comp_id] at h4
  have := h4
  have h5 : _root_.CategoryTheory.IsIso
      (E.map (Functor.Fiber.fiberInclusion.map ι.hom) ≫ (E.map χ ≫ φ.hom)) :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := ℬ.p) (S := S) _
  have := h5
  obtain ⟨e⟩ := nonempty_iso_of_fiber_iso (z.comp E) y.hom
    (CategoryTheory.asIso
      (E.map (Functor.Fiber.fiberInclusion.map ι.hom) ≫ (E.map χ ≫ φ.hom))) (by
        simpa using h4)
  refine ⟨pointSpace.mk (⟨y.carrier, z⟩ : FieldPoint 𝒜), ?_⟩
  show pointSpace.mk (⟨y.carrier, z.comp E⟩ : FieldPoint ℬ) = pointSpace.mk y
  exact pointSpace.mk_eq_mk_of_iso e

/-- **An étale presentation of an algebraic space is surjective on points.**

Let `p : Mor(-, T') ⟶ X` be representable by schemes, surjective and étale. A
field-valued point `y : Spec K → 𝒳_X` of the associated prestack is, by evaluation at
`𝟙 (Spec K)`, an element `g ∈ X(Spec K)`. Base changing `p` along `g` gives a scheme `b`
with a surjective map `b → Spec K` and a map `b → T'`; choosing a point `s ∈ b` and
passing to its residue field `M` produces a field-valued point of `Sch/T'` whose image in
`𝒳_X` agrees, over `M`, with the restriction of `y`. -/
theorem surjective_mapPoints_ofPresheaf
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {T' : Scheme.{u}} (p : yoneda.obj T' ⟶ X)
    (hp : MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) p) :
    Function.Surjective (mapPoints
      ((overBasedToOfPresheafYoneda T').comp (ofPresheaf.map p))) := by
  intro v
  induction v using pointSpace.ind with
  | _ y =>
  set S : Scheme.{u} := Spec (CommRingCat.of y.carrier) with hS
  set c : CostructuredArrow yoneda X := y.hom.obj (Over.mk (𝟙 S)) with hc
  have hcl : c.left = S := y.hom.w_obj _
  set g : yoneda.obj S ⟶ X := yoneda.map (eqToHom hcl.symm) ≫ c.hom with hg
  set bb : Scheme.{u} := hp.rep.pullback g with hbb
  set sndm : bb ⟶ S := hp.rep.snd g with hsndm
  set fstm : bb ⟶ T' := hp.rep.fst' g with hfstm
  have hw : yoneda.map fstm ≫ p = yoneda.map sndm ≫ g := by
    rw [hfstm, Functor.relativelyRepresentable.map_fst']
    exact hp.rep.w g
  have hprop := hp.property_snd g
  have hsurj : _root_.AlgebraicGeometry.Surjective sndm := hprop.1
  have := hsurj
  obtain ⟨pt⟩ : Nonempty ↥S := inferInstance
  obtain ⟨s, hs⟩ := sndm.surjective pt
  set M : CommRingCat.{u} := bb.residueField s with hM
  set ρ : Spec M ⟶ bb := bb.fromSpecResidueField s with hρ
  set Φ : overBased T' ⥤ᵇ ofPresheaf X :=
    (overBasedToOfPresheafYoneda T').comp (ofPresheaf.map p) with hΦ
  have hΦobj : ∀ Z : Over T', Φ.obj Z = CostructuredArrow.mk (yoneda.map Z.hom ≫ p) :=
    fun _ => rfl
  refine ⟨pointSpace.mk (⟨↥M, overBased.map (ρ ≫ fstm)⟩ : FieldPoint (overBased T')), ?_⟩
  show pointSpace.mk (⟨↥M, (overBased.map (ρ ≫ fstm)).comp Φ⟩ : FieldPoint (ofPresheaf X))
    = pointSpace.mk y
  have hcomm : yoneda.map ((ρ ≫ sndm) ≫ eqToHom hcl.symm) ≫ c.hom
      = yoneda.map ((𝟙 (Spec M)) ≫ (ρ ≫ fstm)) ≫ p := by
    have h1 : yoneda.map ((ρ ≫ sndm) ≫ eqToHom hcl.symm) ≫ c.hom
        = yoneda.map ρ ≫ (yoneda.map sndm ≫ g) := by
      rw [hg]; simp
    have h2 : yoneda.map ((𝟙 (Spec M)) ≫ (ρ ≫ fstm)) ≫ p
        = yoneda.map ρ ≫ (yoneda.map fstm ≫ p) := by simp
    rw [h1, h2, hw]
  set A₀ : CostructuredArrow yoneda X :=
    CostructuredArrow.mk (yoneda.map ((𝟙 (Spec M)) ≫ (ρ ≫ fstm)) ≫ p) with hA₀
  set μ : A₀ ⟶ c := CostructuredArrow.homMk ((ρ ≫ sndm) ≫ eqToHom hcl.symm) hcomm with hμ
  set t : (Over.mk ((𝟙 (Spec M)) ≫ (ρ ≫ sndm)) : Over S) ⟶ Over.mk (𝟙 S) :=
    Over.homMk (ρ ≫ sndm) (by simp) with ht
  have hμlift : Functor.IsHomLift (ofPresheaf X).p ((ρ ≫ sndm) ≫ eqToHom hcl.symm) μ :=
    _root_.CategoryTheory.IsHomLift.of_fac (ofPresheaf X).p _ μ rfl rfl (by simp [hμ])
  have htlift0 : Functor.IsHomLift (ofPresheaf X).p (ρ ≫ sndm) (y.hom.map t) := by
    have := CategoryTheory.BasedCategory.basedMap_isHomLift_left S (F := y.hom) t
    simpa [ht] using this
  have := htlift0
  have htlift : Functor.IsHomLift (ofPresheaf X).p ((ρ ≫ sndm) ≫ eqToHom hcl.symm)
      (y.hom.map t) := inferInstance
  have := hμlift
  have := htlift
  set e := Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso
    (p := (ofPresheaf X).p) ((ρ ≫ sndm) ≫ eqToHom hcl.symm) μ (y.hom.map t) with he
  have hehom : Functor.IsHomLift (ofPresheaf X).p (𝟙 (Spec M)) e.hom := by
    rw [he]; infer_instance
  obtain ⟨eBA⟩ := nonempty_iso_of_fiber_iso
    ((overBased.map (ρ ≫ sndm)).comp y.hom)
    ((overBased.map (ρ ≫ fstm)).comp Φ) e hehom
  set i₂ : y.carrier →+* ↥M := (Spec.preimage (ρ ≫ sndm)).hom with hi₂
  have hspec : Spec.map (CommRingCat.ofHom i₂) = ρ ≫ sndm := by
    rw [hi₂, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hrestrict : y.restrict i₂ = (overBased.map (ρ ≫ sndm)).comp y.hom := by
    show (overBased.map (Spec.map (CommRingCat.ofHom i₂))).comp y.hom = _
    rw [hspec]
  refine Eq.trans (pointSpace.mk_eq_mk_of_iso eBA.symm) ?_
  rw [← hrestrict]
  exact pointSpace.sound (FieldPoint.equiv_restrict y i₂)

end BasedFunctor

namespace BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- **The smooth cover of a fiber product realizes every pair of matching points.**

This refines `AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.exists_cover_of_representableWith`:
for a smooth presentation `q : Sch/U ⥤ᵇ 𝒳` and a morphism `g : Sch/T ⥤ᵇ 𝒳`, the smooth
surjective cover `T' → T` of the base change comes with a map `T' → U` such that not only
do the two induced maps to `|𝒳|` agree, but every pair `(t, u) ∈ T × U` with the same
image in `|𝒳|` is realized by a point of `T'`.

The extra clause comes from the surjectivity of `|T'| → |𝒳 ×_𝒳 Sch/T|`
(`AlgebraicGeometry.BasedFunctor.surjective_mapPoints_ofPresheaf` for the étale
presentation of the representing algebraic space, then
`AlgebraicGeometry.BasedFunctor.surjective_mapPoints_of_isEquivalence` for the
equivalence with the fiber product) combined with the surjectivity of
`|𝒳 ×_𝒳 Sch/T| → |Sch/U| ×_{|𝒳|} |Sch/T|`
(`AlgebraicGeometry.BasedFunctor.exists_mapPoints_fiberProduct_eq'`). -/
lemma quotientMapOfPresentation.exists_cover_lift [𝒳.p.IsFiberedInGroupoids]
    {U : Scheme.{u}} (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q)
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) :
    ∃ (T' : Scheme.{u}) (a : T' ⟶ T) (b : T' ⟶ U),
      _root_.AlgebraicGeometry.Surjective a ∧ _root_.AlgebraicGeometry.Smooth a ∧
      (∀ t' : T', nu q (b.base t') = nu g (a.base t')) ∧
      (∀ (t : T) (u : U), nu g t = nu q u →
        ∃ t' : T', a.base t' = t ∧ b.base t' = u) := by
  obtain ⟨X, hX, E, hE⟩ := hq.1 T g
  have := hX
  have := hE
  obtain ⟨T', pres, hpres⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  set Ψ : overBased T' ⥤ᵇ ofPresheaf X :=
    (overBasedToOfPresheafYoneda T').comp (ofPresheaf.map pres) with hΨ
  set Φ : overBased T' ⥤ᵇ fiberProduct q g := Ψ.comp E with hΦ
  have hsurjΦ : Function.Surjective (BasedFunctor.mapPoints Φ) := by
    rw [hΦ]
    intro z
    obtain ⟨z₁, hz₁⟩ := BasedFunctor.surjective_mapPoints_of_isEquivalence E hE z
    obtain ⟨z₂, hz₂⟩ := BasedFunctor.surjective_mapPoints_ofPresheaf pres hpres z₁
    refine ⟨z₂, ?_⟩
    rw [mapPoints_comp, hΨ, hz₂, hz₁]
  have hprop : (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
      MorphismProperty Scheme.{u}) (Φ.comp (fiberProductSnd q g)).overHom := by
    have := hq.2 T g X hX E hE T' pres hpres
    rw [hΦ, hΨ, CategoryTheory.BasedFunctor.comp_assoc,
      CategoryTheory.BasedFunctor.comp_assoc]
    exact this
  clear_value Φ
  obtain ⟨αa⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductSnd q g))
  obtain ⟨αb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductFst q g))
  have hmapa : ∀ t' : T', BasedFunctor.mapPoints (Φ.comp (fiberProductSnd q g))
      (T'.toPointSpace t')
      = T.toPointSpace ((Φ.comp (fiberProductSnd q g)).overHom.base t') := by
    intro t'
    rw [mapPoints_eq_of_iso αa, mapPoints_overBased_map_toPointSpace]
  have hmapb : ∀ t' : T', BasedFunctor.mapPoints (Φ.comp (fiberProductFst q g))
      (T'.toPointSpace t')
      = U.toPointSpace ((Φ.comp (fiberProductFst q g)).overHom.base t') := by
    intro t'
    rw [mapPoints_eq_of_iso αb, mapPoints_overBased_map_toPointSpace]
  refine ⟨T', (Φ.comp (fiberProductSnd q g)).overHom,
    (Φ.comp (fiberProductFst q g)).overHom, hprop.1, hprop.2, ?_, ?_⟩
  · intro t'
    show BasedFunctor.mapPoints q (U.toPointSpace _)
      = BasedFunctor.mapPoints g (T.toPointSpace _)
    rw [← hmapb t', ← hmapa t', ← mapPoints_comp, ← mapPoints_comp,
      CategoryTheory.BasedFunctor.comp_assoc, CategoryTheory.BasedFunctor.comp_assoc,
      mapPoints_eq_of_iso
        (CategoryTheory.BasedCategory.isoWhiskerLeft Φ (fiberProductIsoComm q g))]
  · intro t u h
    obtain ⟨z, hz1, hz2⟩ := BasedFunctor.exists_mapPoints_fiberProduct_eq' q g
      (U.toPointSpace u) (T.toPointSpace t) h.symm
    obtain ⟨z₀, hz₀⟩ := hsurjΦ z
    obtain ⟨t', ht'⟩ := T'.surjective_toPointSpace z₀
    subst ht'
    refine ⟨t', ?_, ?_⟩
    · refine T.injective_toPointSpace ?_
      rw [← hmapa t', mapPoints_comp, hz₀, hz2]
    · refine U.injective_toPointSpace ?_
      rw [← hmapb t', mapPoints_comp, hz₀, hz1]

/-- **The point map of a smooth presentation is open.**

If `q : Sch/U ⥤ᵇ 𝒳` is a smooth presentation of an algebraic stack, the map
`ν : U → |𝒳|` is open. Indeed `|𝒳|` carries the quotient topology
(`AlgebraicGeometry.BasedCategory.isQuotientMap_mapPoints_of_presentation`), so it
suffices to see that the saturation `ν⁻¹(ν(W))` of an open `W ⊆ U` is open; and
`quotientMapOfPresentation.exists_cover_lift` identifies that saturation with
`a(b⁻¹(W))` for the smooth surjective cover `a : T' → U` of `U ×_𝒳 U` and its second
projection `b : T' → U`. Smooth morphisms of schemes are open, so `a(b⁻¹(W))` is
open. -/
theorem quotientMapOfPresentation.isOpenMap_nu [IsAlgebraicStack 𝒳] {U : Scheme.{u}}
    (q : overBased U ⥤ᵇ 𝒳)
    (hq : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    IsOpenMap (nu q) := by
  obtain ⟨T', a, b, hsurj, hsm, hcomp, hlift⟩ :=
    quotientMapOfPresentation.exists_cover_lift q hq U q
  have := hsm
  have hao : _root_.AlgebraicGeometry.UniversallyOpen a := inferInstance
  have hquot := isQuotientMap_mapPoints_of_presentation q hq
  intro W hW
  have hsat : nu q ⁻¹' (nu q '' W) = a.base '' (b.base ⁻¹' W) := by
    ext x
    constructor
    · rintro ⟨w, hw, hxw⟩
      obtain ⟨t', ht'a, ht'b⟩ := hlift x w hxw.symm
      exact ⟨t', by rw [Set.mem_preimage, ht'b]; exact hw, ht'a⟩
    · rintro ⟨t', ht', rfl⟩
      exact ⟨b.base t', ht', hcomp t'⟩
  refine hquot.isOpen_preimage.mp ?_
  have h1 : BasedFunctor.mapPoints q ⁻¹' (nu q '' W)
      = U.toPointSpace '' (nu q ⁻¹' (nu q '' W)) := by
    rw [show (nu q ⁻¹' (nu q '' W))
        = U.toPointSpace ⁻¹' (BasedFunctor.mapPoints q ⁻¹' (nu q '' W)) from rfl,
      Set.image_preimage_eq _ U.surjective_toPointSpace]
  rw [h1, hsat]
  exact U.isOpenMap_toPointSpace _ (a.isOpenMap _ (hW.preimage b.continuous))

end BasedCategory

namespace BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- The point set of a scheme mapping to `𝒳` through a morphism `f : T' ⟶ T` is the
image under `ν` of the image of `f`. -/
lemma range_mapPoints_comp_overBased_map {T T' : Scheme.{u}} (f : T' ⟶ T)
    (g : overBased T ⥤ᵇ 𝒳) :
    Set.range (mapPoints ((overBased.map f).comp g)) = nu g '' Set.range f.base := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t', rfl⟩ := T'.surjective_toPointSpace w
    exact ⟨f.base t', ⟨t', rfl⟩, (nu_comp_map f g t').symm⟩
  · rintro ⟨s, ⟨t', rfl⟩, rfl⟩
    exact ⟨T'.toPointSpace t', nu_comp_map f g t'⟩

/-- The preimage under `|𝒳| → |𝒴|` of the point set of `𝒴' → 𝒴` is the point set of the
first projection of the fiber product. -/
lemma preimage_range_mapPoints_eq_range_fiberProductFst (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    mapPoints F ⁻¹' Set.range (mapPoints G)
      = Set.range (mapPoints (fiberProductFst F G)) := by
  ext x
  constructor
  · rintro ⟨y', hy'⟩
    obtain ⟨z, hz1, _⟩ := exists_mapPoints_fiberProduct_eq' F G x y' hy'.symm
    exact ⟨z, hz1⟩
  · rintro ⟨z, rfl⟩
    refine ⟨mapPoints (fiberProductSnd F G) z, ?_⟩
    rw [← mapPoints_comp, ← mapPoints_comp,
      mapPoints_eq_of_iso (fiberProductIsoComm F G)]

end BasedFunctor

end AlgebraicGeometry

end PointSpaceSupport

section ExerSpecializationProperties

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation

open AlgebraicGeometry.BasedCategory.quotientMapOfPresentation in
/-- API theorem from the unnumbered remark preceding Exercise 4.3.31
preceding it): a quasi-compact morphism of algebraic stacks induces a quasi-compact map
$|\cX| \to |\cY|$: the preimage of a quasi-compact open subset is quasi-compact. (The
converse holds when $\cY$ is quasi-separated but not in general, e.g.
$\Spec k \to B\mathbb{Z}$; this converse is ledgered with quasi-separatedness, §4.2.) -/
theorem isCompact_preimage_mapPoints_of_quasiCompact {F : 𝒳 ⥤ᵇ 𝒴} (hF : QuasiCompact F)
    {V : Set (pointSpace 𝒴)} (h₁ : IsOpen V) (h₂ : IsCompact V) :
    IsCompact (mapPoints F ⁻¹' V) := by
  obtain ⟨U, q, hq⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
  have hquot := isQuotientMap_mapPoints_of_presentation q hq
  have hcont : Continuous (nu q) :=
    hquot.continuous.comp (continuous_toPointSpace U)
  have hsurj : Function.Surjective (nu q) :=
    hquot.surjective.comp U.surjective_toPointSpace
  have hopen : IsOpenMap (nu q) := isOpenMap_nu q hq
  set Ω : U.Opens := ⟨nu q ⁻¹' V, h₁.preimage hcont⟩ with hΩ
  have hcov : V ⊆ ⋃ W : { W : U.Opens // W ∈ U.affineOpens ∧ W ≤ Ω },
      nu q '' (W.1 : Set U) := by
    intro v hv
    obtain ⟨u, rfl⟩ := hsurj v
    have huΩ : u ∈ Ω := hv
    obtain ⟨W, hWaff, huW, hWΩ⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) huΩ
    exact Set.mem_iUnion.mpr ⟨⟨W, hWaff, hWΩ⟩, ⟨u, huW, rfl⟩⟩
  obtain ⟨s, hs⟩ := h₂.elim_finite_subcover
    (fun W : { W : U.Opens // W ∈ U.affineOpens ∧ W ≤ Ω } => nu q '' (W.1 : Set U))
    (fun W => hopen _ W.1.2) hcov
  have heq : mapPoints F ⁻¹' V
      = ⋃ W ∈ s, mapPoints F ⁻¹' (nu q '' (W.1 : Set U)) := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [← Set.preimage_iUnion₂]
      exact Set.preimage_mono hs
    · refine Set.iUnion₂_subset fun W _ => Set.preimage_mono ?_
      rintro v ⟨u, huW, rfl⟩
      exact W.2.2 huW
  rw [heq]
  refine s.finite_toSet.isCompact_biUnion ?_
  intro W _
  have hWaff : IsAffineOpen W.1 := W.2.1
  set B : CommRingCat.{u} := Γ(U, W.1) with hB
  set g : overBased (Spec B) ⥤ᵇ 𝒴 := (overBased.map hWaff.fromSpec).comp q with hg
  have hrange : Set.range (mapPoints g) = nu q '' (W.1 : Set U) := by
    rw [hg, range_mapPoints_comp_overBased_map, hWaff.range_fromSpec]
  have hcompact : CompactSpace (pointSpace (fiberProduct F g)) := hF B g
  have := hcompact
  rw [← hrange, preimage_range_mapPoints_eq_range_fiberProductFst F g]
  exact isCompact_range (continuous_mapPoints' (fiberProductFst F g))

/-- Quasi-compactness of the point space is preserved by an equivalence of prestacks
fibered in groupoids. -/
lemma isQuasiCompact_of_equivalence
    {𝒜 : BasedCategory.{v₂, u₂} Scheme.{u}} {ℬ : BasedCategory.{v₃, u₃} Scheme.{u}}
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    (E : 𝒜 ⥤ᵇ ℬ) (hE : E.toFunctor.IsEquivalence)
    (h𝒜 : BasedCategory.IsQuasiCompact 𝒜) :
    BasedCategory.IsQuasiCompact ℬ := by
  have hc : IsCompact (Set.range (mapPoints E)) :=
    isCompact_range (continuous_mapPoints' E)
  rw [(surjective_mapPoints_of_isEquivalence E hE).range_eq] at hc
  exact isCompact_univ_iff.mp hc

/-- Quasi-compact morphisms of prestacks are stable under base change. This is the
orientation in which the original morphism becomes the second projection. -/
lemma QuasiCompact.fiberProductSnd
    {𝒜 : BasedCategory.{v₂, u₂} Scheme.{u}} {ℬ : BasedCategory.{v₃, u₃} Scheme.{u}}
    {𝒞 : BasedCategory.{v₄, u₄} Scheme.{u}}
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    [𝒞.p.IsFiberedInGroupoids]
    {F : 𝒜 ⥤ᵇ ℬ} (hF : QuasiCompact F) (G : 𝒞 ⥤ᵇ ℬ) :
    QuasiCompact (fiberProductSnd F G) := by
  intro B g
  let E := fiberProductAssocInv F G g
  exact isQuasiCompact_of_equivalence E
    (isEquivalence_fiberProductAssocInv F G g) (hF B (g.comp G))

/-- **Exercise 4.3.31** (`exer:specialization-properties`) (part (b), corrected
statement): an open morphism
$f \colon \cX \to \cY$ of algebraic stacks lifts a generalization
$y' \rightsquigarrow f(x)$ provided that $y'$ has a quasi-compact field-valued
representative.

**Erratum (high confidence).** The printed exercise omits the hypothesis on $y'$.
Under the modern convention allowing arbitrary non-quasi-separated algebraic stacks,
quasi-compactness of a field-valued representative is not automatic; it is exactly the
decency hypothesis used when lifting a generalization through a smooth chart. The
familiar unqualified formulation is recovered for quasi-separated stacks once the
standard bridge from quasi-separatedness to quasi-compact field-valued points is
available. The converse for finitely presented morphisms remains ledgered. -/
theorem exists_specializes_of_isOpenMap_mapPoints {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : IsOpenMap (mapPoints F)) (x : pointSpace 𝒳) {y' : pointSpace 𝒴}
    (hy' : BasedCategory.HasQuasiCompactRepresentative y')
    (h : y' ⤳ mapPoints F x) :
    ∃ x' : pointSpace 𝒳, x' ⤳ x ∧ mapPoints F x' = y' := by
  obtain ⟨p, hp, hpqc⟩ := hy'
  let P := fiberProductSnd p.hom F
  let _ : IsAlgebraicStack (overBased (Spec (CommRingCat.of p.carrier))) := inferInstance
  let _ : IsAlgebraicStack (fiberProduct p.hom F) :=
    IsAlgebraicStack.fiberProduct p.hom F
  have hPqc : QuasiCompact P := hpqc.fiberProductSnd F
  let t : pointSpace (overBased (Spec (CommRingCat.of p.carrier))) :=
    pointSpace.mk (⟨p.carrier, CategoryTheory.BasedFunctor.id _⟩ :
      FieldPoint (overBased (Spec (CommRingCat.of p.carrier))))
  have ht : mapPoints p.hom t = y' := by
    rw [show t = pointSpace.mk
      (⟨p.carrier, CategoryTheory.BasedFunctor.id _⟩ :
        FieldPoint (overBased (Spec (CommRingCat.of p.carrier)))) from rfl,
      mapPoints_mk]
    exact hp
  have hxcl : x ∈ closure (Set.range (mapPoints P)) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hFxU : mapPoints F x ∈ mapPoints F '' U := ⟨x, hxU, rfl⟩
    have hy'U : y' ∈ mapPoints F '' U := h.mem_open (hF U hU) hFxU
    obtain ⟨x', hx'U, hx'y'⟩ := hy'U
    obtain ⟨z, -, hz⟩ := exists_mapPoints_fiberProduct_eq'
      p.hom F t x' (ht.trans hx'y'.symm)
    exact ⟨mapPoints P z, ⟨by simpa [P] using hz ▸ hx'U, z, rfl⟩⟩
  obtain ⟨z, hz⟩ :=
    (mem_closure_range_mapPoints_iff_specializes hPqc x).mp hxcl
  refine ⟨mapPoints P z, hz, ?_⟩
  obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace
    (Spec (CommRingCat.of p.carrier))
  let _ : Subsingleton (pointSpace (overBased (Spec (CommRingCat.of p.carrier)))) :=
    Function.Injective.subsingleton e.injective
  calc
    mapPoints F (mapPoints P z) =
        mapPoints p.hom (mapPoints (fiberProductFst p.hom F) z) := by
      rw [← mapPoints_comp, ← mapPoints_comp,
        mapPoints_eq_of_iso (fiberProductIsoComm p.hom F)]
    _ = mapPoints p.hom t :=
      congrArg (mapPoints p.hom) (Subsingleton.elim _ t)
    _ = y' := ht

end AlgebraicGeometry.BasedFunctor

end ExerSpecializationProperties
