module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Fiber products of prestacks

This module formalizes `constr:fiber-product-prestacks` and `thm:fiber-product-prestacks`
of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks` (subsection label `subsec:prestack-fiber-products`); the
construction for groupoids, `constr:fiber-product-groupoids`, is the special case of
based categories over a point.

Given morphisms of based categories `F : 𝒳 ⥤ᵇ 𝒴` and `G : 𝒴' ⥤ᵇ 𝒴` over `𝒮`, the fiber
product `𝒳 ×_𝒴 𝒴'` has objects the triples `(x, y', γ)` where `x` and `y'` lie over the
same object of `𝒮` and `γ : F(x) ≅ G(y')` is an isomorphism lying over the identity, and
morphisms the pairs of morphisms over a common base morphism compatible with the `γ`s.

Main declarations:
- `CategoryTheory.GroupoidFiberProductObj` and `.GroupoidFiberProductHom`: the
  2-categorical fiber product of groupoids from Construction 3.4.28;
- `CategoryTheory.groupoidFiberProductLift` and
  `CategoryTheory.groupoidFiberProductLift_unique`: the full universal property
  requested in the unlabeled exercise following Construction 3.4.28;
- `CategoryTheory.FreeActionQuotientFiberProduct.equivalence` and
  `CategoryTheory.ActionGroupoidDiagonalFiberProduct.equivalence`: the two
  action-groupoid cartesian-square computations following Construction 3.4.28;
- `CategoryTheory.NormalSubgroupLeftFiberProduct.equivalence`,
  `CategoryTheory.NormalSubgroupRightFiberProduct.equivalence`, and
  `CategoryTheory.StabilizerGroupoidFiberProduct.equivalence`: the exact-sequence
  and stabilizer/orbit cartesian-square computations in the same exercise;
- `CategoryTheory.BasedCategory.FiberProductObj` and `.FiberProductHom`: objects and
  morphisms of the fiber product;
- `CategoryTheory.BasedCategory.fiberProduct F G : BasedCategory 𝒮` with its projections
  `fiberProductFst`, `fiberProductSnd` and the 2-isomorphism `fiberProductIsoComm` making
  the square 2-commutative;
- `CategoryTheory.BasedCategory.fiberProductLift`: the universal lift of a 2-commutative
  square, with `fiberProductLift_fst`, `fiberProductLift_snd` (strict equalities) and the
  compatibility `fiberProductLift_isoComm`;
- `CategoryTheory.BasedCategory.fiberProductLift_unique`: the full uniqueness-up-to-
  unique-2-isomorphism clause of Theorem 3.4.35;
- `CategoryTheory.Functor.IsFiberedInGroupoids.fiberProduct`: the fiber product of
  prestacks is a prestack.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ConstrFiberProductGroupoids

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃}
  [Groupoid.{v₁} C] [Groupoid.{v₂} D] [Groupoid.{v₃} C']
  (F : C ⥤ D) (G : C' ⥤ D)

/-- **Construction 3.4.28** (`constr:fiber-product-groupoids`) (objects): an object of
the fiber product of groupoids `C ×_D C'` is a triple `(c, c', gamma)` with
`gamma : F(c) ≅ G(c')`. -/
structure GroupoidFiberProductObj where
  /-- The object in the first groupoid. -/
  fst : C
  /-- The object in the second groupoid. -/
  snd : C'
  /-- The comparison isomorphism in the target groupoid. -/
  iso : F.obj fst ≅ G.obj snd

variable {F G}

/-- **Construction 3.4.28** (`constr:fiber-product-groupoids`) (morphisms): a morphism
of `C ×_D C'` is a pair of morphisms whose images commute with the comparison
isomorphisms. -/
@[ext]
structure GroupoidFiberProductHom (a b : GroupoidFiberProductObj F G) where
  /-- The morphism in the first groupoid. -/
  fst : a.fst ⟶ b.fst
  /-- The morphism in the second groupoid. -/
  snd : a.snd ⟶ b.snd
  /-- Compatibility with the comparison isomorphisms. -/
  w : F.map fst ≫ b.iso.hom = a.iso.hom ≫ G.map snd := by cat_disch

/-- Identity morphisms in the fiber product of groupoids. -/
@[simps]
def GroupoidFiberProductHom.id (a : GroupoidFiberProductObj F G) :
    GroupoidFiberProductHom a a where
  fst := 𝟙 a.fst
  snd := 𝟙 a.snd
  w := by simp

/-- Composition in the fiber product of groupoids. -/
@[simps]
def GroupoidFiberProductHom.comp {a b c : GroupoidFiberProductObj F G}
    (f : GroupoidFiberProductHom a b) (g : GroupoidFiberProductHom b c) :
    GroupoidFiberProductHom a c where
  fst := f.fst ≫ g.fst
  snd := f.snd ≫ g.snd
  w := by
    rw [F.map_comp, G.map_comp, Category.assoc, g.w, ← Category.assoc, f.w,
      Category.assoc]

instance : Category (GroupoidFiberProductObj F G) where
  Hom := GroupoidFiberProductHom
  id := GroupoidFiberProductHom.id
  comp := GroupoidFiberProductHom.comp
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

/-- The componentwise inverse of a morphism in the fiber product of groupoids. -/
noncomputable def GroupoidFiberProductHom.inverse {a b : GroupoidFiberProductObj F G}
    (f : GroupoidFiberProductHom a b) : GroupoidFiberProductHom b a where
  fst := inv f.fst
  snd := inv f.snd
  w := by
    rw [← cancel_mono (G.map f.snd), Category.assoc, Category.assoc,
      ← G.map_comp, IsIso.inv_hom_id, G.map_id, Category.comp_id, ← f.w,
      ← Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id,
      Category.id_comp]

instance {a b : GroupoidFiberProductObj F G} (f : a ⟶ b) : IsIso f :=
  ⟨⟨GroupoidFiberProductHom.inverse f,
    by
      apply GroupoidFiberProductHom.ext
      · change f.fst ≫ inv f.fst = 𝟙 _
        exact IsIso.hom_inv_id _
      · change f.snd ≫ inv f.snd = 𝟙 _
        exact IsIso.hom_inv_id _,
    by
      apply GroupoidFiberProductHom.ext
      · change inv f.fst ≫ f.fst = 𝟙 _
        exact IsIso.inv_hom_id _
      · change inv f.snd ≫ f.snd = 𝟙 _
        exact IsIso.inv_hom_id _⟩⟩

/-- **Construction 3.4.28** (`constr:fiber-product-groupoids`): the category of triples
`(c, c', gamma)` is a groupoid. -/
noncomputable instance : Groupoid (GroupoidFiberProductObj F G) :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

/-- The first projection from the fiber product of groupoids. -/
@[simps]
def groupoidFiberProductFst : GroupoidFiberProductObj F G ⥤ C where
  obj x := x.fst
  map f := f.fst

/-- The second projection from the fiber product of groupoids. -/
@[simps]
def groupoidFiberProductSnd : GroupoidFiberProductObj F G ⥤ C' where
  obj x := x.snd
  map f := f.snd

/-- Background construction for Construction 3.4.28 (the implicit
2-isomorphism in its universal property): the two composites from the fiber product to
the target groupoid are naturally isomorphic. -/
def groupoidFiberProductIsoComm :
    groupoidFiberProductFst (F := F) (G := G) ⋙ F ≅
      groupoidFiberProductSnd (F := F) (G := G) ⋙ G :=
  NatIso.ofComponents (fun x ↦ x.iso) (fun f ↦ f.w)

variable {T : Type*} [Category T]

/-- API for the unlabelled universal-property exercise following Construction 3.4.28 (the lift in the
unlabeled universal-property exercise following the construction): a pair of functors
and a natural isomorphism between their composites induces a functor to the fiber
product groupoid. -/
@[simps]
def groupoidFiberProductLift (q₁ : T ⥤ C) (q₂ : T ⥤ C')
    (tau : q₁ ⋙ F ≅ q₂ ⋙ G) : T ⥤ GroupoidFiberProductObj F G where
  obj t := ⟨q₁.obj t, q₂.obj t, tau.app t⟩
  map phi := ⟨q₁.map phi, q₂.map phi, tau.hom.naturality phi⟩

/-- The canonical lift projects strictly to its first input functor. -/
lemma groupoidFiberProductLift_fst (q₁ : T ⥤ C) (q₂ : T ⥤ C')
    (tau : q₁ ⋙ F ≅ q₂ ⋙ G) :
    groupoidFiberProductLift q₁ q₂ tau ⋙
      groupoidFiberProductFst (F := F) (G := G) = q₁ :=
  rfl

/-- The canonical lift projects strictly to its second input functor. -/
lemma groupoidFiberProductLift_snd (q₁ : T ⥤ C) (q₂ : T ⥤ C')
    (tau : q₁ ⋙ F ≅ q₂ ⋙ G) :
    groupoidFiberProductLift q₁ q₂ tau ⋙
      groupoidFiberProductSnd (F := F) (G := G) = q₂ :=
  rfl

/-- A componentwise isomorphism between two objects of a groupoid fiber product. -/
def groupoidFiberProductObjIsoMk {a b : GroupoidFiberProductObj F G}
    (e₁ : a.fst ≅ b.fst) (e₂ : a.snd ≅ b.snd)
    (w : F.map e₁.hom ≫ b.iso.hom = a.iso.hom ≫ G.map e₂.hom) : a ≅ b where
  hom := ⟨e₁.hom, e₂.hom, w⟩
  inv :=
    { fst := e₁.inv
      snd := e₂.inv
      w := by
        rw [← cancel_mono (G.map e₂.hom), Category.assoc, Category.assoc,
          ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id, ← w,
          ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id,
          Category.id_comp] }
  hom_inv_id := by
    apply GroupoidFiberProductHom.ext
    · change e₁.hom ≫ e₁.inv = 𝟙 _
      exact e₁.hom_inv_id
    · change e₂.hom ≫ e₂.inv = 𝟙 _
      exact e₂.hom_inv_id
  inv_hom_id := by
    apply GroupoidFiberProductHom.ext
    · change e₁.inv ≫ e₁.hom = 𝟙 _
      exact e₁.inv_hom_id
    · change e₂.inv ≫ e₂.hom = 𝟙 _
      exact e₂.inv_hom_id

/-- API for the unlabelled universal-property exercise following Construction 3.4.28 (the unlabeled
universal-property exercise following the construction): any other lift of the same
2-commutative diagram is uniquely naturally isomorphic to the canonical lift, with
the prescribed isomorphisms on both projections. -/
theorem groupoidFiberProductLift_unique (q₁ : T ⥤ C) (q₂ : T ⥤ C')
    (tau : q₁ ⋙ F ≅ q₂ ⋙ G)
    (h : T ⥤ GroupoidFiberProductObj F G)
    (beta : q₁ ≅ h ⋙ groupoidFiberProductFst (F := F) (G := G))
    (rho : q₂ ≅ h ⋙ groupoidFiberProductSnd (F := F) (G := G))
    (comm : ∀ t : T, F.map (beta.hom.app t) ≫ (h.obj t).iso.hom =
      tau.hom.app t ≫ G.map (rho.hom.app t)) :
    ∃! eta : h ≅ groupoidFiberProductLift q₁ q₂ tau,
      (∀ t : T, (eta.hom.app t).fst = beta.inv.app t) ∧
      (∀ t : T, (eta.hom.app t).snd = rho.inv.app t) := by
  let app (t : T) : h.obj t ≅ (groupoidFiberProductLift q₁ q₂ tau).obj t :=
    groupoidFiberProductObjIsoMk
      ((beta.app t).symm) ((rho.app t).symm)
      (by
        show F.map (beta.inv.app t) ≫ tau.hom.app t =
          (h.obj t).iso.hom ≫ G.map (rho.inv.app t)
        rw [← cancel_mono (G.map (rho.hom.app t))]
        calc
          (F.map (beta.inv.app t) ≫ tau.hom.app t) ≫ G.map (rho.hom.app t) =
              F.map (beta.inv.app t) ≫
                (tau.hom.app t ≫ G.map (rho.hom.app t)) := Category.assoc _ _ _
          _ = F.map (beta.inv.app t) ≫
                (F.map (beta.hom.app t) ≫ (h.obj t).iso.hom) := by
              rw [comm t]
          _ = F.map (beta.inv.app t ≫ beta.hom.app t) ≫
                (h.obj t).iso.hom := by rw [F.map_comp, Category.assoc]
          _ = (h.obj t).iso.hom := by simp
          _ = (h.obj t).iso.hom ≫
                G.map (rho.inv.app t ≫ rho.hom.app t) := by
              have hrho : rho.inv.app t ≫ rho.hom.app t =
                  𝟙 (h.obj t).snd := by
                have hrho' := rho.inv_hom_id_app t
                change rho.inv.app t ≫ rho.hom.app t =
                  𝟙 (h.obj t).snd at hrho'
                exact hrho'
              calc
                (h.obj t).iso.hom = (h.obj t).iso.hom ≫ 𝟙 _ :=
                  (Category.comp_id _).symm
                _ = (h.obj t).iso.hom ≫ G.map (𝟙 (h.obj t).snd) := by
                  rw [G.map_id]
                _ = (h.obj t).iso.hom ≫
                    G.map (rho.inv.app t ≫ rho.hom.app t) :=
                  congrArg (fun k ↦ (h.obj t).iso.hom ≫ G.map k) hrho.symm
          _ = ((h.obj t).iso.hom ≫ G.map (rho.inv.app t)) ≫
                G.map (rho.hom.app t) := by rw [G.map_comp, Category.assoc])
  let eta : h ≅ groupoidFiberProductLift q₁ q₂ tau :=
    NatIso.ofComponents app (fun {t t'} phi ↦ by
      apply GroupoidFiberProductHom.ext
      · exact beta.inv.naturality phi
      · exact rho.inv.naturality phi)
  refine ⟨eta, ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩, ?_⟩
  intro eta' heta'
  apply Iso.ext
  apply NatTrans.ext
  funext t
  apply GroupoidFiberProductHom.ext
  · exact (heta'.1 t).trans (show beta.inv.app t = (eta.hom.app t).fst from rfl)
  · exact (heta'.2 t).trans (show rho.inv.app t = (eta.hom.app t).snd from rfl)

/-- A zigzag in a groupoid can be composed, reversing its backwards arrows, to
produce a morphism between its endpoints. -/
lemma groupoidHomNonemptyOfZigzag {J : Type*} [Groupoid J] {a b : J}
    (h : Zigzag a b) : Nonempty (a ⟶ b) := by
  induction h with
  | refl => exact ⟨𝟙 _⟩
  | tail h hz ih =>
    obtain ⟨phi⟩ := ih
    rcases hz with ⟨⟨psi⟩⟩ | ⟨⟨psi⟩⟩
    · exact ⟨phi ≫ psi⟩
    · exact ⟨phi ≫ inv psi⟩

/-- The canonical functor from a groupoid to the discrete category of its connected
components. -/
def groupoidComponentsFunctor (J : Type*) [Groupoid J] :
    J ⥤ Discrete (ConnectedComponents J) :=
  ConnectedComponents.functorToDiscrete _ id

instance groupoidComponentsFunctor_full (J : Type*) [Groupoid J] :
    (groupoidComponentsFunctor J).Full where
  map_surjective {a b} f := by
    have hab : ConnectedComponents.mk a = ConnectedComponents.mk b :=
      Discrete.eq_of_hom f
    obtain ⟨g⟩ := groupoidHomNonemptyOfZigzag (Quotient.exact' hab)
    exact ⟨g, Subsingleton.elim _ _⟩

instance groupoidComponentsFunctor_essSurj (J : Type*) [Groupoid J] :
    (groupoidComponentsFunctor J).EssSurj where
  mem_essImage x := by
    obtain ⟨j⟩ := x
    obtain ⟨a, ha⟩ := Quotient.exists_rep j
    refine ⟨a, ⟨eqToIso ?_⟩⟩
    exact congrArg Discrete.mk ha

/-- A groupoid is *equivalent to a set* when it is equivalent to a discrete category. -/
abbrev GroupoidIsEquivalentToSet (J : Type u₁) [Groupoid.{v₁} J] : Prop :=
  ∃ X : Type u₁, Nonempty (J ≌ Discrete X)

/-- The diagonal of a thin category is full. -/
lemma diag_full_of_isThin {J : Type*} [Category J] [Quiver.IsThin J] :
    (Functor.diag J).Full where
  map_surjective {a b} f := by
    refine ⟨f.1, ?_⟩
    apply Prod.hom_ext
    · rfl
    · exact Subsingleton.elim _ _

/-- The diagonal functor of any category is faithful. -/
lemma diag_faithful (J : Type*) [Category J] : (Functor.diag J).Faithful where
  map_injective {_ _} _ _ h := by
    exact congrArg (fun q ↦ q.1) h

/-- Fullness of the diagonal forces a category to be thin. -/
lemma isThin_of_diag_full {J : Type*} [Category J] [(Functor.diag J).Full] :
    Quiver.IsThin J := by
  intro a b
  constructor
  intro f g
  obtain ⟨h, hh⟩ := (Functor.diag J).map_surjective
    (CategoryTheory.Prod.mkHom f g)
  have hfst : h = f := congrArg (fun q ↦ q.1) hh
  have hsnd : h = g := congrArg (fun q ↦ q.2) hh
  exact hfst.symm.trans hsnd

/-- The carrier of the quotient groupoid of a group action. It is kept distinct from
the acted-on type so that its category structure cannot conflict with unrelated
category instances on that type. -/
def ActionGroupoid (G : Type*) (U : Type*) := U

namespace ActionGroupoid

variable {G : Type*} {U : Type*} [Group G] [MulAction G U]

/-- Regard an element of an acted-on type as an object of its action groupoid. -/
def mk (u : U) : ActionGroupoid G U := u

/-- The underlying element of an object of an action groupoid. -/
def as (u : ActionGroupoid G U) : U := u

@[simp] lemma as_mk (u : U) : as (mk (G := G) u) = u := rfl

/-- A morphism `u ⟶ v` in an action groupoid is a group element carrying `u` to
`v`. -/
@[ext]
structure Hom (u v : ActionGroupoid G U) where
  /-- The group element defining the arrow. -/
  gauge : G
  /-- The group element carries the source to the target. -/
  smul_eq : gauge • as u = as v

/-- Identity arrows in an action groupoid. -/
@[simps]
def Hom.id (u : ActionGroupoid G U) : Hom u u where
  gauge := 1
  smul_eq := one_smul _ _

/-- Composition in an action groupoid. -/
@[simps]
def Hom.comp {u v w : ActionGroupoid G U} (f : Hom u v) (g : Hom v w) : Hom u w where
  gauge := g.gauge * f.gauge
  smul_eq := by rw [mul_smul, f.smul_eq, g.smul_eq]

/-- The inverse of an arrow in an action groupoid. -/
def Hom.inverse {u v : ActionGroupoid G U} (f : Hom u v) : Hom v u where
  gauge := f.gauge⁻¹
  smul_eq := by rw [← f.smul_eq, inv_smul_smul]

instance : Groupoid (ActionGroupoid G U) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [mul_assoc]
  inv := Hom.inverse
  inv_comp f := by
    apply Hom.ext
    simp [Hom.comp, Hom.inverse, Hom.id]
  comp_inv f := by
    apply Hom.ext
    simp [Hom.comp, Hom.inverse, Hom.id]

@[simp]
lemma gauge_comp {u v w : ActionGroupoid G U} (f : u ⟶ v) (g : v ⟶ w) :
    (f ≫ g).gauge = g.gauge * f.gauge :=
  rfl

/-- The projection from a set to its action groupoid. -/
def projection : Discrete U ⥤ ActionGroupoid G U where
  obj u := mk u.as
  map f :=
    { gauge := 1
      smul_eq := by
        simpa only [one_smul, as_mk] using Discrete.eq_of_hom f }
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by
    apply Hom.ext
    change 1 = 1 * 1
    simp

end ActionGroupoid

namespace ActionGroupoidFiberProduct

variable {G : Type*} {U : Type*} [Group G] [MulAction G U]

/-- The 2-fiber of the quotient projection with itself. -/
abbrev Obj := GroupoidFiberProductObj
  (ActionGroupoid.projection (G := G) (U := U))
  (ActionGroupoid.projection (G := G) (U := U))

/-- The comparison from the action graph to the 2-fiber of the quotient projection
with itself. -/
noncomputable def comparisonObj (gu : Discrete (G × U)) : Obj (G := G) (U := U) where
  fst := Discrete.mk gu.as.2
  snd := Discrete.mk (gu.as.1 • gu.as.2)
  iso := asIso
    { gauge := gu.as.1
      smul_eq := rfl }

/-- The functor induced by `comparisonObj`. -/
noncomputable def comparison : Discrete (G × U) ⥤ Obj (G := G) (U := U) where
  obj := comparisonObj
  map {x y} f := eqToHom (congrArg comparisonObj
    (Discrete.ext (Discrete.eq_of_hom f)))

@[simp]
lemma comparison_fst_obj (gu : Discrete (G × U)) :
    (comparison.obj gu).fst = Discrete.mk gu.as.2 :=
  rfl

@[simp]
lemma comparison_snd_obj (gu : Discrete (G × U)) :
    (comparison.obj gu).snd = Discrete.mk (gu.as.1 • gu.as.2) :=
  rfl

@[simp]
lemma comparison_iso_gauge (gu : Discrete (G × U)) :
    (comparison.obj gu).iso.hom.gauge = gu.as.1 :=
  rfl

@[simp]
lemma projection_map_gauge {u v : Discrete U} (f : u ⟶ v) :
    ((ActionGroupoid.projection (G := G) (U := U)).map f).gauge = 1 := by
  rfl

instance comparison_faithful : (comparison (G := G) (U := U)).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance comparison_full : (comparison (G := G) (U := U)).Full where
  map_surjective {a b} f := by
    have hw := congrArg ActionGroupoid.Hom.gauge f.w
    dsimp only [comparison, comparisonObj] at hw
    change b.as.1 *
        ((ActionGroupoid.projection (G := G) (U := U)).map f.fst).gauge =
      ((ActionGroupoid.projection (G := G) (U := U)).map f.snd).gauge * a.as.1 at hw
    simp only [projection_map_gauge, mul_one, one_mul] at hw
    have hab : a.as = b.as := by
      apply Prod.ext
      · exact hw.symm
      · exact Discrete.eq_of_hom f.fst
    refine ⟨eqToHom (congrArg Discrete.mk hab), ?_⟩
    apply GroupoidFiberProductHom.ext <;> exact Subsingleton.elim _ _

instance comparison_essSurj : (comparison (G := G) (U := U)).EssSurj where
  mem_essImage x := by
    let gu : Discrete (G × U) :=
      Discrete.mk (x.iso.hom.gauge, x.fst.as)
    have hx := x.iso.hom.smul_eq
    change x.iso.hom.gauge • x.fst.as = x.snd.as at hx
    let e₁ : (comparison.obj gu).fst ≅ x.fst :=
      eqToIso (Discrete.mk_as x.fst)
    let e₂ : (comparison.obj gu).snd ≅ x.snd :=
      eqToIso (congrArg Discrete.mk hx)
    refine ⟨gu, ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    apply ActionGroupoid.Hom.ext
    simp only [ActionGroupoid.gauge_comp, projection_map_gauge,
      comparison_iso_gauge, mul_one, one_mul]
    change x.iso.hom.gauge = x.iso.hom.gauge
    rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (b) of the
unlabeled quotient-groupoid exercise): for a group action, the action graph
`G × U → U × U` presents the 2-fiber product
`U ×_[U/G] U`. -/
noncomputable def equivalence :
    Discrete (G × U) ≌ Obj (G := G) (U := U) := by
  letI : (comparison (G := G) (U := U)).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison (G := G) (U := U)).asEquivalence

end ActionGroupoidFiberProduct

namespace FreeActionQuotientFiberProduct

universe uG uP uU

variable {G : Type uG} {P : Type uP} {U : Type uU}
  [Group G] [MulAction G P] [MulAction G U] [IsCancelSMul G P]
  (f : P →[G] U)

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the set-theoretic quotient `P/G` of a free
`G`-set `P`. -/
abbrev OrbitQuotient := MulAction.orbitRel.Quotient G P

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): a chosen representative of an orbit in `P/G`. -/
noncomputable def representative (t : OrbitQuotient (G := G) (P := P)) : P :=
  Quotient.out t

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): a group element carrying `p` to the chosen
representative of its orbit. -/
noncomputable def gaugeToRepresentative (p : P) : G :=
  Classical.choose (MulAction.mem_orbit_iff.mp
    (show representative (G := G) (P := P) ⟦p⟧ ∈ MulAction.orbit G p from
      (MulAction.orbitRel_apply.mp
        (Quotient.exact (Quotient.out_eq' (⟦p⟧ : OrbitQuotient (G := G) (P := P)))))))

omit [IsCancelSMul G P] in
/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the chosen gauge carries a point to its chosen
orbit representative. -/
lemma gaugeToRepresentative_smul (p : P) :
    gaugeToRepresentative (G := G) (P := P) p • p =
      representative (G := G) (P := P) ⟦p⟧ :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp
    (show representative (G := G) (P := P) ⟦p⟧ ∈ MulAction.orbit G p from
      (MulAction.orbitRel_apply.mp
        (Quotient.exact (Quotient.out_eq' (⟦p⟧ : OrbitQuotient (G := G) (P := P)))))))

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the map `P/G → [U/G]` determined by an
equivariant map `P → U`, after choosing one point in every orbit. -/
noncomputable def quotientMap :
    Discrete (OrbitQuotient (G := G) (P := P)) ⥤ ActionGroupoid G U :=
  Discrete.functor fun t ↦
    ActionGroupoid.mk (f (representative (G := G) (P := P) t))

omit [IsCancelSMul G P] in
/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): arrows from the discrete quotient map have
trivial gauge. -/
@[simp]
lemma quotientMap_map_gauge {s t : Discrete (OrbitQuotient (G := G) (P := P))}
    (k : s ⟶ t) : ((quotientMap (G := G) (P := P) f).map k).gauge = 1 := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  rcases k with ⟨⟨h⟩⟩
  change s = t at h
  subst t
  rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the groupoid `U ×_[U/G] (P/G)`. -/
abbrev Obj := GroupoidFiberProductObj
  (ActionGroupoid.projection (G := G) (U := U))
  (quotientMap (G := G) (P := P) f)

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the object of `U ×_[U/G] (P/G)` attached to
`p : P`. -/
noncomputable def comparisonObj (p : P) : Obj (G := G) (P := P) f where
  fst := Discrete.mk (f p)
  snd := Discrete.mk (⟦p⟧ : OrbitQuotient (G := G) (P := P))
  iso := asIso
    { gauge := gaugeToRepresentative (G := G) (P := P) p
      smul_eq := by
        change gaugeToRepresentative (G := G) (P := P) p • f p =
          f (representative (G := G) (P := P) ⟦p⟧)
        rw [← f.map_smul, gaugeToRepresentative_smul (G := G) (P := P)] }

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): the comparison `P → U ×_[U/G] (P/G)`. -/
noncomputable def comparison : Discrete P ⥤ Obj (G := G) (P := P) f :=
  Discrete.functor (comparisonObj (G := G) f)

@[simp]
lemma comparison_fst (p : P) :
    (comparisonObj (G := G) f p).fst = Discrete.mk (f p) := rfl

@[simp]
lemma comparison_snd (p : P) :
    (comparisonObj (G := G) f p).snd =
      Discrete.mk (⟦p⟧ : OrbitQuotient (G := G) (P := P)) := rfl

@[simp]
lemma comparison_gauge (p : P) :
    (comparisonObj (G := G) f p).iso.hom.gauge =
      gaugeToRepresentative (G := G) (P := P) p := rfl

instance comparison_faithful : (comparison (G := G) f).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance comparison_full : (comparison (G := G) f).Full where
  map_surjective {a b} k := by
    have hsnd := Discrete.eq_of_hom k.snd
    change (⟦a.as⟧ : OrbitQuotient (G := G) (P := P)) = ⟦b.as⟧ at hsnd
    have habq : (⟦a.as⟧ : OrbitQuotient (G := G) (P := P)) = ⟦b.as⟧ := hsnd
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact habq))
    have hw := congrArg ActionGroupoid.Hom.gauge k.w
    dsimp only [comparison, comparisonObj] at hw
    simp only [ActionGroupoid.gauge_comp,
      ActionGroupoidFiberProduct.projection_map_gauge,
      quotientMap_map_gauge (G := G) (P := P) f, mul_one, one_mul] at hw
    have hga : gaugeToRepresentative (G := G) (P := P) a.as * g =
        gaugeToRepresentative (G := G) (P := P) b.as := by
      apply IsCancelSMul.right_cancel (c := b.as)
      rw [mul_smul]
      rw [hg, gaugeToRepresentative_smul (G := G) (P := P)]
      rw [gaugeToRepresentative_smul (G := G) (P := P)]
      exact congrArg (representative (G := G) (P := P)) habq
    have hg_one : g = 1 := by
      have hmul : gaugeToRepresentative (G := G) (P := P) a.as * g =
          gaugeToRepresentative (G := G) (P := P) a.as := hga.trans hw
      apply mul_left_cancel (a := gaugeToRepresentative (G := G) (P := P) a.as)
      simpa using hmul
    have hab : a.as = b.as := by simpa [hg_one] using hg.symm
    refine ⟨eqToHom (congrArg Discrete.mk hab), ?_⟩
    apply GroupoidFiberProductHom.ext <;> exact Subsingleton.elim _ _

instance comparison_essSurj : (comparison (G := G) f).EssSurj where
  mem_essImage x := by
    let p : P := x.iso.hom.gauge⁻¹ •
      representative (G := G) (P := P) x.snd.as
    have hpq : (⟦p⟧ : OrbitQuotient (G := G) (P := P)) = x.snd.as := by
      calc
        (⟦p⟧ : OrbitQuotient (G := G) (P := P)) =
            ⟦representative (G := G) (P := P) x.snd.as⟧ :=
          MulAction.orbitRel.Quotient.quotient_smul_eq
        _ = x.snd.as := Quotient.out_eq' x.snd.as
    have hfp : f p = x.fst.as := by
      change f (x.iso.hom.gauge⁻¹ •
        representative (G := G) (P := P) x.snd.as) = x.fst.as
      rw [f.map_smul]
      have hx := x.iso.hom.smul_eq
      change x.iso.hom.gauge • x.fst.as =
        f (representative (G := G) (P := P) x.snd.as) at hx
      rw [← hx]
      simp
    have hgauge : gaugeToRepresentative (G := G) (P := P) p =
        x.iso.hom.gauge := by
      apply IsCancelSMul.right_cancel (c := p)
      rw [gaugeToRepresentative_smul (G := G) (P := P)]
      change representative (G := G) (P := P) ⟦p⟧ =
        x.iso.hom.gauge •
          (x.iso.hom.gauge⁻¹ • representative (G := G) (P := P) x.snd.as)
      rw [smul_inv_smul]
      exact congrArg (representative (G := G) (P := P)) hpq
    let e₁ : ((comparison (G := G) f).obj (Discrete.mk p)).fst ≅ x.fst :=
      eqToIso (congrArg Discrete.mk hfp)
    let e₂ : ((comparison (G := G) f).obj (Discrete.mk p)).snd ≅ x.snd :=
      eqToIso (congrArg Discrete.mk hpq)
    refine ⟨Discrete.mk p, ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    apply ActionGroupoid.Hom.ext
    simp only [ActionGroupoid.gauge_comp,
      ActionGroupoidFiberProduct.projection_map_gauge,
      quotientMap_map_gauge (G := G) (P := P) f, mul_one, one_mul]
    exact hgauge.symm

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled quotient-groupoid exercise): if `P` is a free `G`-set and `P → U` is
equivariant, then the square
`P → U`, `P/G → [U/G]` is cartesian: concretely,
`P ≃ U ×_[U/G] (P/G)`. -/
noncomputable def equivalence :
    Discrete P ≌ Obj (G := G) (P := P) f := by
  letI : (comparison (G := G) f).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison (G := G) f).asEquivalence

end FreeActionQuotientFiberProduct

namespace ActionGroupoidDiagonalFiberProduct

universe uG uU

variable {G : Type uG} {U : Type uU} [Group G] [MulAction G U]

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the product of two quotient
projections `U × U → [U/G] × [U/G]`. -/
noncomputable def quotientPair :
    Discrete (U × U) ⥤ ActionGroupoid G U × ActionGroupoid G U :=
  Discrete.functor fun uv ↦
    (ActionGroupoid.mk uv.1, ActionGroupoid.mk uv.2)

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the first component of an
arrow induced by `quotientPair` has trivial gauge. -/
@[simp]
lemma quotientPair_map_fst_gauge {x y : Discrete (U × U)} (k : x ⟶ y) :
    ((quotientPair (G := G) (U := U)).map k).1.gauge = 1 := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases k with ⟨⟨h⟩⟩
  change x = y at h
  subst y
  rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the second component of an
arrow induced by `quotientPair` has trivial gauge. -/
@[simp]
lemma quotientPair_map_snd_gauge {x y : Discrete (U × U)} (k : x ⟶ y) :
    ((quotientPair (G := G) (U := U)).map k).2.gauge = 1 := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases k with ⟨⟨h⟩⟩
  change x = y at h
  subst y
  rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the 2-fiber product of
`U × U → [U/G] × [U/G]` with the diagonal of `[U/G]`. -/
abbrev Obj := GroupoidFiberProductObj
  (quotientPair (G := G) (U := U)) (Functor.diag (ActionGroupoid G U))

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the fiber-product object
attached to `(g,u)`, whose image in `U × U` is `(g•u,u)`. -/
noncomputable def comparisonObj (gu : G × U) : Obj (G := G) (U := U) where
  fst := Discrete.mk (gu.1 • gu.2, gu.2)
  snd := ActionGroupoid.mk gu.2
  iso := by
    let h : ActionGroupoid.mk (G := G) (gu.1 • gu.2) ⟶
        ActionGroupoid.mk (G := G) gu.2 :=
      { gauge := gu.1⁻¹
        smul_eq := inv_smul_smul gu.1 gu.2 }
    exact (asIso h).prod (Iso.refl _)

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the comparison from the action
graph to the pullback of the diagonal. -/
noncomputable def comparison : Discrete (G × U) ⥤ Obj (G := G) (U := U) :=
  Discrete.functor (comparisonObj (G := G) (U := U))

@[simp]
lemma comparisonObj_iso_fst_gauge (gu : G × U) :
    (comparisonObj (G := G) (U := U) gu).iso.hom.1.gauge = gu.1⁻¹ := rfl

@[simp]
lemma comparisonObj_iso_snd_gauge (gu : G × U) :
    (comparisonObj (G := G) (U := U) gu).iso.hom.2.gauge = 1 := rfl

@[simp]
lemma comparison_map_snd_gauge {a b : Discrete (G × U)} (k : a ⟶ b) :
    ((comparison (G := G) (U := U)).map k).snd.gauge = 1 := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases k with ⟨⟨h⟩⟩
  change a = b at h
  subst b
  rfl

instance comparison_faithful : (comparison (G := G) (U := U)).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance comparison_full : (comparison (G := G) (U := U)).Full where
  map_surjective {a b} k := by
    have hfst := Discrete.eq_of_hom k.fst
    dsimp only [comparison, comparisonObj] at hfst
    change (a.as.1 • a.as.2, a.as.2) = (b.as.1 • b.as.2, b.as.2) at hfst
    have hu : a.as.2 = b.as.2 := congrArg (fun z : U × U ↦ z.2) hfst
    have hw1cat := congrArg (fun m ↦ m.1) k.w
    have hw2cat := congrArg (fun m ↦ m.2) k.w
    dsimp only [comparison] at hw1cat hw2cat
    change ActionGroupoid.Hom.comp
        ((quotientPair (G := G) (U := U)).map k.fst).1
        (comparisonObj (G := G) (U := U) b.as).iso.hom.1 =
      ActionGroupoid.Hom.comp
        (comparisonObj (G := G) (U := U) a.as).iso.hom.1 k.snd at hw1cat
    change ActionGroupoid.Hom.comp
        ((quotientPair (G := G) (U := U)).map k.fst).2
        (comparisonObj (G := G) (U := U) b.as).iso.hom.2 =
      ActionGroupoid.Hom.comp
        (comparisonObj (G := G) (U := U) a.as).iso.hom.2 k.snd at hw2cat
    have hw1 := congrArg ActionGroupoid.Hom.gauge hw1cat
    have hw2 := congrArg ActionGroupoid.Hom.gauge hw2cat
    change b.as.1⁻¹ *
        ((quotientPair (G := G) (U := U)).map k.fst).1.gauge =
      k.snd.gauge * a.as.1⁻¹ at hw1
    change (1 : G) *
        ((quotientPair (G := G) (U := U)).map k.fst).2.gauge =
      k.snd.gauge * 1 at hw2
    simp only [quotientPair_map_fst_gauge, quotientPair_map_snd_gauge,
      mul_one] at hw1 hw2
    have hks : k.snd.gauge = 1 := hw2.symm
    have hg_inv : b.as.1⁻¹ = a.as.1⁻¹ := by simpa [hks] using hw1
    have hg : a.as.1 = b.as.1 := inv_injective hg_inv.symm
    have hab : a.as = b.as := Prod.ext hg hu
    refine ⟨eqToHom (congrArg Discrete.mk hab), ?_⟩
    apply GroupoidFiberProductHom.ext
    · exact Subsingleton.elim _ _
    · apply ActionGroupoid.Hom.ext
      simpa [hks] using comparison_map_snd_gauge (G := G) (U := U)
        (eqToHom (congrArg Discrete.mk hab))

instance comparison_essSurj : (comparison (G := G) (U := U)).EssSurj where
  mem_essImage x := by
    let a : G := x.iso.hom.1.gauge
    let b : G := x.iso.hom.2.gauge
    let g : G := a⁻¹ * b
    let u : U := x.fst.as.2
    have hx1 := x.iso.hom.1.smul_eq
    have hx2 := x.iso.hom.2.smul_eq
    change a • x.fst.as.1 = ActionGroupoid.as x.snd at hx1
    change b • x.fst.as.2 = ActionGroupoid.as x.snd at hx2
    have hgu : g • u = x.fst.as.1 := by
      change (a⁻¹ * b) • x.fst.as.2 = x.fst.as.1
      rw [mul_smul, hx2, ← hx1, inv_smul_smul]
    have hpair : (g • u, u) = x.fst.as := by
      apply Prod.ext
      · exact hgu
      · rfl
    let e₁ : (comparisonObj (G := G) (U := U) (g, u)).fst ≅ x.fst := by
      change Discrete.mk (g • u, u) ≅ x.fst
      exact eqToIso (congrArg Discrete.mk hpair)
    let e₂' : ((quotientPair (G := G) (U := U)).obj x.fst).2 ≅
        ((Functor.diag (ActionGroupoid G U)).obj x.snd).2 :=
      { hom := x.iso.hom.2
        inv := x.iso.inv.2
        hom_inv_id := congrArg (fun m ↦ m.2) x.iso.hom_inv_id
        inv_hom_id := congrArg (fun m ↦ m.2) x.iso.inv_hom_id }
    let e₂ : (comparisonObj (G := G) (U := U) (g, u)).snd ≅ x.snd := by
      change ActionGroupoid.mk (G := G) u ≅ x.snd
      change ((quotientPair (G := G) (U := U)).obj x.fst).2 ≅
        ((Functor.diag (ActionGroupoid G U)).obj x.snd).2 at e₂'
      exact e₂'
    refine ⟨Discrete.mk (g, u), ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    apply Prod.hom_ext
    · apply ActionGroupoid.Hom.ext
      dsimp only [comparison]
      change (ActionGroupoid.Hom.comp
          ((quotientPair (G := G) (U := U)).map e₁.hom).1
          x.iso.hom.1).gauge =
        (ActionGroupoid.Hom.comp
          (comparisonObj (G := G) (U := U) (g, u)).iso.hom.1 e₂.hom).gauge
      change x.iso.hom.1.gauge *
          ((quotientPair (G := G) (U := U)).map e₁.hom).1.gauge =
        e₂.hom.gauge *
          (comparisonObj (G := G) (U := U) (g, u)).iso.hom.1.gauge
      simp only [quotientPair_map_fst_gauge,
        comparisonObj_iso_fst_gauge, mul_one]
      change a = b * (a⁻¹ * b)⁻¹
      simp
    · apply ActionGroupoid.Hom.ext
      dsimp only [comparison]
      change (ActionGroupoid.Hom.comp
          ((quotientPair (G := G) (U := U)).map e₁.hom).2
          x.iso.hom.2).gauge =
        (ActionGroupoid.Hom.comp
          (comparisonObj (G := G) (U := U) (g, u)).iso.hom.2 e₂.hom).gauge
      change x.iso.hom.2.gauge *
          ((quotientPair (G := G) (U := U)).map e₁.hom).2.gauge =
        e₂.hom.gauge *
          (comparisonObj (G := G) (U := U) (g, u)).iso.hom.2.gauge
      simp only [quotientPair_map_snd_gauge,
        comparisonObj_iso_snd_gauge, mul_one]
      dsimp only [e₂, e₂']
      change x.iso.hom.2.gauge = x.iso.hom.2.gauge
      rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (the second square in
part (b) of the unlabeled quotient-groupoid exercise): the action graph
`G × U → U × U` is the pullback of the diagonal
`[U/G] → [U/G] × [U/G]`; concretely, its canonical comparison is an equivalence. -/
noncomputable def equivalence :
    Discrete (G × U) ≌ Obj (G := G) (U := U) := by
  letI : (comparison (G := G) (U := U)).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison (G := G) (U := U)).asEquivalence

end ActionGroupoidDiagonalFiberProduct

/-- The right-quotient action associated to a homomorphism `phi : H → G`, written
as a left action by `h • g = g * phi(h)⁻¹`. -/
def HomRightAction {H G : Type*} [Group H] [Group G] (phi : H →* G) := G

namespace HomRightAction

variable {H G : Type*} [Group H] [Group G] (phi : H →* G)

/-- Regard an element of `G` as an element of the right-quotient action. -/
def mk (g : G) : HomRightAction phi := g

/-- The underlying group element. -/
def as (g : HomRightAction phi) : G := g

instance : MulAction H (HomRightAction phi) where
  smul h g := mk phi (as phi g * (phi h)⁻¹)
  one_smul g := by
    change as phi g * (phi 1)⁻¹ = as phi g
    rw [map_one, inv_one, mul_one]
  mul_smul h k g := by
    change as phi g * (phi (h * k))⁻¹ =
      (as phi g * (phi k)⁻¹) * (phi h)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]

@[simp]
lemma smul_as (h : H) (g : HomRightAction phi) :
    as phi (h • g) = as phi g * (phi h)⁻¹ :=
  rfl

end HomRightAction

/-- The unique homomorphism from the trivial group. -/
def trivialGroupHom (G : Type*) [Group G] : Unit →* G where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

/-- The point of the classifying groupoid `BG`, viewed as the functor from the
trivial classifying groupoid. -/
abbrev pointToClassifyingGroupoid (G : Type*) [Group G] :
    SingleObj Unit ⥤ SingleObj G :=
  (trivialGroupHom G).toFunctor

/-- The functor `BH → BG` induced by a group homomorphism. -/
abbrev classifyingGroupoidMap {H G : Type*} [Group H] [Group G]
    (phi : H →* G) : SingleObj H ⥤ SingleObj G :=
  phi.toFunctor

namespace ClassifyingGroupoidFiberProduct

variable {H G : Type*} [Group H] [Group G] (phi : H →* G)

abbrev Obj := GroupoidFiberProductObj
  (classifyingGroupoidMap phi) (pointToClassifyingGroupoid G)

/-- The comparison from `BH ×_BG pt` to the right action groupoid `[G/H]`. -/
def comparison : Obj phi ⥤ ActionGroupoid H (HomRightAction phi) where
  obj x := ActionGroupoid.mk (HomRightAction.mk phi x.iso.hom)
  map {a b} f :=
    { gauge := f.fst
      smul_eq := by
        change a.iso.hom * (phi f.fst)⁻¹ = b.iso.hom
        have hw0 := f.w
        have hw : b.iso.hom * phi f.fst = a.iso.hom := by
          change b.iso.hom * phi f.fst = 1 * a.iso.hom at hw0
          simpa only [one_mul] using hw0
        rw [← hw]
        simp [mul_assoc] }
  map_id x := by apply ActionGroupoid.Hom.ext; rfl
  map_comp f g := by apply ActionGroupoid.Hom.ext; rfl

instance comparison_faithful : (comparison phi).Faithful where
  map_injective {_ _} f g h := by
    apply GroupoidFiberProductHom.ext
    · exact congrArg ActionGroupoid.Hom.gauge h
    · cases f.snd
      cases g.snd
      rfl

instance comparison_full : (comparison phi).Full where
  map_surjective {a b} f := by
    let q : a ⟶ b :=
      { fst := f.gauge
        snd := 𝟙 _
        w := by
          change b.iso.hom * phi f.gauge = 1 * a.iso.hom
          rw [one_mul]
          have hf : a.iso.hom * (phi f.gauge)⁻¹ = b.iso.hom := f.smul_eq
          rw [← hf]
          simp [mul_assoc] }
    exact ⟨q, by apply ActionGroupoid.Hom.ext; rfl⟩

instance comparison_essSurj : (comparison phi).EssSurj where
  mem_essImage x := by
    let a : Obj phi :=
      { fst := SingleObj.star H
        snd := SingleObj.star Unit
        iso := asIso (HomRightAction.as phi (ActionGroupoid.as x)) }
    refine ⟨a, ⟨eqToIso ?_⟩⟩
    rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (a) of the
unlabeled classifying-groupoid exercise): a homomorphism `H → G` induces
`BH → BG`, and its 2-fiber over the point is equivalent to the quotient groupoid
`[G/H]` for the right action `h • g = g phi(h)⁻¹`. -/
noncomputable def equivalence :
    Obj phi ≌ ActionGroupoid H (HomRightAction phi) := by
  letI : (comparison phi).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison phi).asEquivalence

end ClassifyingGroupoidFiberProduct

namespace NormalSubgroupLeftFiberProduct

universe uG

variable {G : Type uG} [Group G] (K : Subgroup G) [K.Normal]

/-- Result of an unlabelled exercise following Construction 3.4.28 (the left square in
part (b) of the unlabeled classifying-groupoid exercise): the quotient group `G/K`. -/
abbrev Q := G ⧸ K

/-- Result of an unlabelled exercise following Construction 3.4.28 (the left square in
part (b) of the unlabeled classifying-groupoid exercise): the fiber
`B K ×_{B G} pt`. -/
abbrev Obj := ClassifyingGroupoidFiberProduct.Obj K.subtype

/-- Result of an unlabelled exercise following Construction 3.4.28 (the left square in
part (b) of the unlabeled classifying-groupoid exercise): the fiber object attached
to a coset, using a chosen representative. -/
noncomputable def comparisonObj (q : Q K) : Obj K where
  fst := SingleObj.star K
  snd := SingleObj.star Unit
  iso := asIso (Quotient.out q : G)

/-- Result of an unlabelled exercise following Construction 3.4.28 (the left square in
part (b) of the unlabeled classifying-groupoid exercise): the comparison
`G/K → B K ×_{B G} pt`. -/
noncomputable def comparison : Discrete (Q K) ⥤ Obj K :=
  Discrete.functor (comparisonObj K)

omit [K.Normal] in
@[simp]
lemma comparison_map_fst {a b : Discrete (Q K)} (f : a ⟶ b) :
    ((comparison K).map f).fst = 𝟙 _ := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases f with ⟨⟨h⟩⟩
  change a = b at h
  subst b
  rfl

instance comparison_faithful : (comparison K).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance comparison_full : (comparison K).Full where
  map_surjective {a b} f := by
    let kf : K := f.fst
    have hw0 := f.w
    change (b.as.out : G) * (kf : G) = 1 * (a.as.out : G) at hw0
    simp only [one_mul] at hw0
    have habq : b.as = a.as := by
      calc
        b.as = ((b.as.out : G) : Q K) := (Quotient.out_eq' b.as).symm
        _ = ((a.as.out : G) : Q K) := by
          rw [← hw0]
          simp
        _ = a.as := Quotient.out_eq' a.as
    have hf_one : f.fst = 𝟙 _ := by
      change kf = 1
      apply Subtype.ext
      apply mul_left_cancel (a := b.as.out)
      simpa [habq] using hw0
    have hab : a.as = b.as := habq.symm
    let l : a ⟶ b := eqToHom (congrArg Discrete.mk hab)
    refine ⟨l, ?_⟩
    apply GroupoidFiberProductHom.ext
    · rw [comparison_map_fst, hf_one]
    · change (show Unit from ((comparison K).map l).snd) = (show Unit from f.snd)
      exact Subsingleton.elim _ _

instance comparison_essSurj : (comparison K).EssSurj where
  mem_essImage x := by
    let q : Q K := (x.iso.hom : G)
    have hq : ((q.out : G) : Q K) = ((x.iso.hom : G) : Q K) := Quotient.out_eq' q
    obtain ⟨k, hk, hgk⟩ := (QuotientGroup.«mk'_eq_mk'» K).mp hq.symm
    let e₁ : ((comparison K).obj (Discrete.mk q)).fst ≅ x.fst :=
      asIso (show ((comparison K).obj (Discrete.mk q)).fst ⟶ x.fst from
        (⟨k, hk⟩ : K))
    let e₂ : ((comparison K).obj (Discrete.mk q)).snd ≅ x.snd := Iso.refl _
    refine ⟨Discrete.mk q, ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    dsimp only [e₁, e₂]
    rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
    dsimp [classifyingGroupoidMap, pointToClassifyingGroupoid,
      MonoidHom.toFunctor, SingleObj.mapHom, comparison, comparisonObj, trivialGroupHom]
    change (show G from x.iso.hom) * k = 1 * q.out
    simpa using hgk

/-- Result of an unlabelled exercise following Construction 3.4.28 (the left cartesian
square in part (b) of the unlabeled classifying-groupoid exercise): if `K ◁ G`, then
`G/K ≃ B K ×_{B G} pt`. -/
noncomputable def equivalence : Discrete (Q K) ≌ Obj K := by
  letI : (comparison K).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison K).asEquivalence

end NormalSubgroupLeftFiberProduct

namespace NormalSubgroupRightFiberProduct

universe uG

variable {G : Type uG} [Group G] (K : Subgroup G) [K.Normal]

/-- Result of an unlabelled exercise following Construction 3.4.28 (the right square in
part (b) of the unlabeled classifying-groupoid exercise): the quotient group `G/K`. -/
abbrev Q := G ⧸ K

/-- Result of an unlabelled exercise following Construction 3.4.28 (the right square in
part (b) of the unlabeled classifying-groupoid exercise): the fiber
`B G ×_{B(G/K)} pt`. -/
abbrev Obj := GroupoidFiberProductObj
  (classifyingGroupoidMap (QuotientGroup.mk' K)) (pointToClassifyingGroupoid (Q K))

/-- Result of an unlabelled exercise following Construction 3.4.28 (the right square in
part (b) of the unlabeled classifying-groupoid exercise): the distinguished fiber
object over the identity coset. -/
def comparisonObj : Obj K where
  fst := SingleObj.star G
  snd := SingleObj.star Unit
  iso := Iso.refl _

/-- Result of an unlabelled exercise following Construction 3.4.28 (the right square in
part (b) of the unlabeled classifying-groupoid exercise): the kernel comparison
`B K → B G ×_{B(G/K)} pt`. -/
def comparison : SingleObj K ⥤ Obj K where
  obj _ := comparisonObj K
  map k := by
    change K at k
    exact
      { fst := (k : G)
        snd := 𝟙 _
        w := by
          rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
          dsimp [classifyingGroupoidMap, pointToClassifyingGroupoid,
            MonoidHom.toFunctor, SingleObj.mapHom, comparisonObj, trivialGroupHom]
          change (1 : Q K) * (QuotientGroup.mk' K (k : G)) = 1 * 1
          simp }
  map_id _ := by apply GroupoidFiberProductHom.ext <;> rfl
  map_comp f g := by apply GroupoidFiberProductHom.ext <;> rfl

instance comparison_faithful : (comparison K).Faithful where
  map_injective {_ _} f g h := by
    change K at f g
    have hfg := congrArg (fun m ↦ m.fst) h
    change (f : G) = (g : G) at hfg
    exact Subtype.ext hfg

instance comparison_full : (comparison K).Full where
  map_surjective {a b} f := by
    let g : G := f.fst
    have hw0 := f.w
    rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul] at hw0
    dsimp [classifyingGroupoidMap, pointToClassifyingGroupoid,
      MonoidHom.toFunctor, SingleObj.mapHom, comparison, comparisonObj,
      trivialGroupHom] at hw0
    change (1 : Q K) * (QuotientGroup.mk' K g) = 1 * 1 at hw0
    have hw0' : QuotientGroup.mk' K g = 1 := by simpa using hw0
    let k : K := ⟨g, (QuotientGroup.eq_one_iff g).mp hw0'⟩
    refine ⟨k, ?_⟩
    apply GroupoidFiberProductHom.ext
    · rfl
    · change (show Unit from ((comparison K).map k).snd) = (show Unit from f.snd)
      exact Subsingleton.elim _ _

instance comparison_essSurj : (comparison K).EssSurj where
  mem_essImage x := by
    obtain ⟨g, hg⟩ := QuotientGroup.«mk'_surjective» K x.iso.hom⁻¹
    let e₁ : (comparisonObj K).fst ≅ x.fst :=
      asIso (show (comparisonObj K).fst ⟶ x.fst from g)
    let e₂ : (comparisonObj K).snd ≅ x.snd := Iso.refl _
    refine ⟨SingleObj.star K, ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    dsimp only [e₁, e₂]
    rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
    dsimp [classifyingGroupoidMap, pointToClassifyingGroupoid,
      MonoidHom.toFunctor, SingleObj.mapHom, comparison, comparisonObj,
      trivialGroupHom]
    change (show Q K from x.iso.hom) * (QuotientGroup.mk' K g) = 1 * 1
    rw [hg]
    simp

/-- Result of an unlabelled exercise following Construction 3.4.28 (the right cartesian
square in part (b) of the unlabeled classifying-groupoid exercise): if `K ◁ G`, then
`B K ≃ B G ×_{B(G/K)} pt`. -/
noncomputable def equivalence : SingleObj K ≌ Obj K := by
  letI : (comparison K).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison K).asEquivalence

end NormalSubgroupRightFiberProduct

namespace StabilizerGroupoidFiberProduct

universe uG uU

variable {G : Type uG} {U : Type uU} [Group G] [MulAction G U] (u : U)

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the stabilizer subgroup `G_u`. -/
abbrev Stabilizer := MulAction.stabilizer G u

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the functor `B G_u → [U/G]` sends its
unique object to `u` and a stabilizer element to the corresponding arrow at `u`. -/
def stabilizerMap : SingleObj (Stabilizer (G := G) u) ⥤ ActionGroupoid G U where
  obj _ := ActionGroupoid.mk u
  map h := by
    change Stabilizer (G := G) u at h
    exact
      { gauge := (h : G)
        smul_eq := MulAction.mem_stabilizer_iff.mp h.property }
  map_id _ := by apply ActionGroupoid.Hom.ext; rfl
  map_comp f g := by apply ActionGroupoid.Hom.ext; rfl

@[simp]
lemma stabilizerMap_gauge {a b : SingleObj (Stabilizer (G := G) u)}
    (h : a ⟶ b) : ((stabilizerMap (G := G) u).map h).gauge =
      ((show Stabilizer (G := G) u from h) : G) := rfl

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the 2-fiber product
`U ×_[U/G] B G_u`. -/
abbrev Obj := GroupoidFiberProductObj
  (ActionGroupoid.projection (G := G) (U := U)) (stabilizerMap (G := G) u)

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): a chosen group element carrying an orbit
point back to `u`. -/
noncomputable def orbitGauge (v : MulAction.orbit G u) : G :=
  (Classical.choose (MulAction.mem_orbit_iff.mp v.property))⁻¹

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the chosen orbit gauge carries `v` to `u`. -/
lemma orbitGauge_smul (v : MulAction.orbit G u) : orbitGauge (G := G) u v • v.1 = u := by
  let g := Classical.choose (MulAction.mem_orbit_iff.mp v.property)
  have hg := Classical.choose_spec (MulAction.mem_orbit_iff.mp v.property)
  change g⁻¹ • v.1 = u
  rw [← hg, inv_smul_smul]

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the fiber-product object associated to a
point of the orbit `G u`. -/
noncomputable def comparisonObj (v : MulAction.orbit G u) : Obj (G := G) u where
  fst := Discrete.mk v.1
  snd := SingleObj.star (Stabilizer (G := G) u)
  iso := asIso
    { gauge := orbitGauge (G := G) u v
      smul_eq := orbitGauge_smul (G := G) u v }

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): the comparison
`G u → U ×_[U/G] B G_u`. -/
noncomputable def comparison :
    Discrete (MulAction.orbit G u) ⥤ Obj (G := G) u :=
  Discrete.functor (comparisonObj (G := G) u)

@[simp]
lemma comparison_gauge (v : MulAction.orbit G u) :
    (comparisonObj (G := G) u v).iso.hom.gauge = orbitGauge (G := G) u v := rfl

@[simp]
lemma comparison_map_snd {a b : Discrete (MulAction.orbit G u)}
    (k : a ⟶ b) : ((comparison (G := G) u).map k).snd = 𝟙 _ := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases k with ⟨⟨h⟩⟩
  change a = b at h
  subst b
  rfl

instance comparison_faithful : (comparison (G := G) u).Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

instance comparison_full : (comparison (G := G) u).Full where
  map_surjective {a b} k := by
    have hv := Discrete.eq_of_hom k.fst
    change a.as.1 = b.as.1 at hv
    have hab0 : a.as = b.as := Subtype.ext hv
    have hw := congrArg ActionGroupoid.Hom.gauge k.w
    dsimp only [comparison, comparisonObj] at hw
    simp only [ActionGroupoid.gauge_comp,
      ActionGroupoidFiberProduct.projection_map_gauge, stabilizerMap_gauge,
      mul_one] at hw
    let ks : Stabilizer (G := G) u := k.snd
    have hks_val : (ks : G) = 1 := by
      apply mul_right_cancel (b := orbitGauge (G := G) u a.as)
      simpa [hab0] using hw.symm
    have hks : k.snd = 𝟙 _ := by
      change ks = 1
      exact Subtype.ext hks_val
    let l : a ⟶ b := eqToHom (congrArg Discrete.mk hab0)
    refine ⟨l, ?_⟩
    apply GroupoidFiberProductHom.ext
    · exact Subsingleton.elim _ _
    · rw [comparison_map_snd, hks]

instance comparison_essSurj : (comparison (G := G) u).EssSurj where
  mem_essImage x := by
    have hx := x.iso.hom.smul_eq
    change x.iso.hom.gauge • x.fst.as = u at hx
    let v : MulAction.orbit G u :=
      ⟨x.fst.as, MulAction.mem_orbit_iff.mpr
        ⟨x.iso.hom.gauge⁻¹, by
          calc
            x.iso.hom.gauge⁻¹ • u =
                x.iso.hom.gauge⁻¹ • (x.iso.hom.gauge • x.fst.as) :=
              congrArg (fun z ↦ x.iso.hom.gauge⁻¹ • z) hx.symm
            _ = x.fst.as := inv_smul_smul _ _⟩⟩
    let hval : G := x.iso.hom.gauge * (orbitGauge (G := G) u v)⁻¹
    have hh : hval • u = u := by
      change (x.iso.hom.gauge * (orbitGauge (G := G) u v)⁻¹) • u = u
      calc
        (x.iso.hom.gauge * (orbitGauge (G := G) u v)⁻¹) • u =
            x.iso.hom.gauge • ((orbitGauge (G := G) u v)⁻¹ • u) := mul_smul _ _ _
        _ = x.iso.hom.gauge • ((orbitGauge (G := G) u v)⁻¹ •
              (orbitGauge (G := G) u v • v.1)) :=
          congrArg (fun z ↦ x.iso.hom.gauge •
            ((orbitGauge (G := G) u v)⁻¹ • z))
            (orbitGauge_smul (G := G) u v).symm
        _ = x.iso.hom.gauge • v.1 := by rw [inv_smul_smul]
        _ = u := hx
    let h : Stabilizer (G := G) u := ⟨hval, MulAction.mem_stabilizer_iff.mpr hh⟩
    let e₁ : ((comparison (G := G) u).obj (Discrete.mk v)).fst ≅ x.fst :=
      eqToIso (Discrete.mk_as x.fst)
    let e₂ : ((comparison (G := G) u).obj (Discrete.mk v)).snd ≅ x.snd :=
      asIso (show ((comparison (G := G) u).obj (Discrete.mk v)).snd ⟶ x.snd from h)
    refine ⟨Discrete.mk v, ⟨groupoidFiberProductObjIsoMk e₁ e₂ ?_⟩⟩
    apply ActionGroupoid.Hom.ext
    simp only [ActionGroupoid.gauge_comp,
      ActionGroupoidFiberProduct.projection_map_gauge, stabilizerMap_gauge,
      mul_one]
    change x.iso.hom.gauge =
      (x.iso.hom.gauge * (orbitGauge (G := G) u v)⁻¹) * orbitGauge (G := G) u v
    simp [mul_assoc]

/-- Result of an unlabelled exercise following Construction 3.4.28 (part (c) of the
unlabeled classifying-groupoid exercise): for `u : U` with stabilizer `G_u` and orbit
`G u`, the square `G u → U`, `B G_u → [U/G]` is cartesian; concretely,
`G u ≃ U ×_[U/G] B G_u`. -/
noncomputable def equivalence :
    Discrete (MulAction.orbit G u) ≌ Obj (G := G) u := by
  letI : (comparison (G := G) u).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison (G := G) u).asEquivalence

end StabilizerGroupoidFiberProduct

/-- Result of an unlabelled exercise following Construction 3.4.28 (the final unlabeled
exercise of the groupoid warmup): a groupoid is equivalent to a set exactly when its
diagonal to its product with itself is fully faithful. -/
theorem groupoid_isEquivalentToSet_iff_diag_full_and_faithful (J : Type u₁)
    [Groupoid.{v₁} J] :
    GroupoidIsEquivalentToSet J ↔
      (Functor.diag J).Full ∧ (Functor.diag J).Faithful := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    let hthin : Quiver.IsThin J := fun a b ↦
      ⟨fun f g ↦ e.functor.map_injective (Subsingleton.elim _ _)⟩
    letI : Quiver.IsThin J := hthin
    exact ⟨diag_full_of_isThin, diag_faithful J⟩
  · rintro ⟨hfull, _⟩
    letI : (Functor.diag J).Full := hfull
    letI : Quiver.IsThin J := isThin_of_diag_full
    letI : (groupoidComponentsFunctor J).IsEquivalence :=
      Functor.IsEquivalence.mk
    exact ⟨ConnectedComponents J,
      ⟨(groupoidComponentsFunctor J).asEquivalence⟩⟩

end CategoryTheory

end ConstrFiberProductGroupoids


section ConstrFiberProductPrestacks

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}

/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) (objects): an object of
the fiber product `𝒳 ×_𝒴 𝒴'` of two morphisms `F : 𝒳 ⥤ᵇ 𝒴` and `G : 𝒴' ⥤ᵇ 𝒴` of based
categories — a pair of objects `fst : 𝒳`, `snd : 𝒴'` lying over the same object of the
base, together with an isomorphism `iso : F(fst) ≅ G(snd)` lying over the identity. -/
structure FiberProductObj (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) where
  /-- The first component, an object of `𝒳`. -/
  fst : 𝒳.obj
  /-- The second component, an object of `𝒴'`. -/
  snd : 𝒴'.obj
  /-- The two components lie over the same object of the base. -/
  over_eq : 𝒴'.p.obj snd = 𝒳.p.obj fst
  /-- The comparison isomorphism `F(fst) ≅ G(snd)`. -/
  iso : F.obj fst ≅ G.obj snd
  /-- The comparison isomorphism lies over the identity. -/
  isHomLift : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj fst)) iso.hom

attribute [instance] FiberProductObj.isHomLift

variable {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}

/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) (morphisms): a morphism of
the fiber product `𝒳 ×_𝒴 𝒴'` — a pair of morphisms in `𝒳` and `𝒴'` lying over a common
morphism of the base and compatible with the comparison isomorphisms. -/
@[ext]
structure FiberProductHom (a b : FiberProductObj F G) where
  /-- The first component. -/
  fst : a.fst ⟶ b.fst
  /-- The second component. -/
  snd : a.snd ⟶ b.snd
  /-- The second component lies over the image in the base of the first. -/
  isHomLift : IsHomLift 𝒴'.p (𝒳.p.map fst) snd
  /-- Compatibility with the comparison isomorphisms. -/
  w : F.map fst ≫ b.iso.hom = a.iso.hom ≫ G.map snd := by cat_disch

attribute [instance] FiberProductHom.isHomLift
attribute [reassoc] FiberProductHom.w

/-- The identity morphism of the fiber product. -/
@[simps]
def FiberProductHom.id (a : FiberProductObj F G) : FiberProductHom a a where
  fst := 𝟙 a.fst
  snd := 𝟙 a.snd
  isHomLift := by
    rw [𝒳.p.map_id]
    exact IsHomLift.id a.over_eq
  w := by simp

/-- Composition of morphisms of the fiber product. -/
@[simps]
def FiberProductHom.comp {a b c : FiberProductObj F G} (φ : FiberProductHom a b)
    (ψ : FiberProductHom b c) : FiberProductHom a c where
  fst := φ.fst ≫ ψ.fst
  snd := φ.snd ≫ ψ.snd
  isHomLift := by
    rw [𝒳.p.map_comp]
    infer_instance
  w := by
    rw [F.toFunctor.map_comp, G.toFunctor.map_comp, Category.assoc, ψ.w, φ.w_assoc]

instance FiberProductObj.instCategory : Category (FiberProductObj F G) where
  Hom a b := FiberProductHom a b
  id a := FiberProductHom.id a
  comp φ ψ := φ.comp ψ
  id_comp φ := by ext <;> simp
  comp_id φ := by ext <;> simp
  assoc φ ψ χ := by ext <;> simp

@[simp]
lemma FiberProductObj.id_fst (a : FiberProductObj F G) :
    FiberProductHom.fst (𝟙 a) = 𝟙 a.fst :=
  rfl

@[simp]
lemma FiberProductObj.id_snd (a : FiberProductObj F G) :
    FiberProductHom.snd (𝟙 a) = 𝟙 a.snd :=
  rfl

@[simp]
lemma FiberProductObj.comp_fst {a b c : FiberProductObj F G} (φ : a ⟶ b) (ψ : b ⟶ c) :
    FiberProductHom.fst (φ ≫ ψ) = φ.fst ≫ ψ.fst :=
  rfl

@[simp]
lemma FiberProductObj.comp_snd {a b c : FiberProductObj F G} (φ : a ⟶ b) (ψ : b ⟶ c) :
    FiberProductHom.snd (φ ≫ ψ) = φ.snd ≫ ψ.snd :=
  rfl

variable (F G) in
/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`): the fiber product of two
morphisms `F : 𝒳 ⥤ᵇ 𝒴`, `G : 𝒴' ⥤ᵇ 𝒴` of based categories over `𝒮`, as a based category
over `𝒮` — an object over `S` is a triple `(x, y', γ)` of objects `x` of `𝒳` and `y'` of
`𝒴'` over `S` and an isomorphism `γ : F(x) ≅ G(y')` over the identity of `S`. -/
abbrev fiberProduct : BasedCategory.{max v₂ v₄, max u₂ u₄ v₃} 𝒮 where
  obj := FiberProductObj F G
  p :=
    { obj := fun a ↦ 𝒳.p.obj a.fst
      map := fun φ ↦ 𝒳.p.map (FiberProductHom.fst φ)
      map_id := fun a ↦ by rw [FiberProductObj.id_fst, 𝒳.p.map_id]
      map_comp := fun φ ψ ↦ by rw [FiberProductObj.comp_fst, 𝒳.p.map_comp] }

@[simp]
lemma fiberProduct_p_obj (a : FiberProductObj F G) :
    (fiberProduct F G).p.obj a = 𝒳.p.obj a.fst :=
  rfl

@[simp]
lemma fiberProduct_p_map {a b : FiberProductObj F G} (φ : a ⟶ b) :
    (fiberProduct F G).p.map φ = 𝒳.p.map (FiberProductHom.fst φ) :=
  rfl

variable (F G) in
/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) (the first projection
`p₁`): the projection `𝒳 ×_𝒴 𝒴' ⥤ᵇ 𝒳`, `(x, y', γ) ↦ x`. -/
def fiberProductFst : fiberProduct F G ⥤ᵇ 𝒳 where
  obj a := a.fst
  map φ := FiberProductHom.fst φ
  w := rfl

variable (F G) in
/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) (the second projection
`p₂`): the projection `𝒳 ×_𝒴 𝒴' ⥤ᵇ 𝒴'`, `(x, y', γ) ↦ y'`. -/
def fiberProductSnd : fiberProduct F G ⥤ᵇ 𝒴' where
  obj a := a.snd
  map φ := FiberProductHom.snd φ
  w := by
    refine Functor.ext_of_iso (NatIso.ofComponents (fun a ↦ eqToIso a.over_eq) ?_)
      (fun a ↦ a.over_eq)
    intro a b φ
    have h := IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst φ)) (FiberProductHom.snd φ)
    simp only [Functor.comp_map, h]
    simp

@[simp]
lemma fiberProductFst_obj (a : FiberProductObj F G) : (fiberProductFst F G).obj a = a.fst :=
  rfl

@[simp]
lemma fiberProductFst_map {a b : FiberProductObj F G} (φ : a ⟶ b) :
    (fiberProductFst F G).map φ = FiberProductHom.fst φ :=
  rfl

@[simp]
lemma fiberProductSnd_obj (a : FiberProductObj F G) : (fiberProductSnd F G).obj a = a.snd :=
  rfl

@[simp]
lemma fiberProductSnd_map {a b : FiberProductObj F G} (φ : a ⟶ b) :
    (fiberProductSnd F G).map φ = FiberProductHom.snd φ :=
  rfl

variable (F G) in
/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) / **Equation 3.4.34**
(`eqn:fiber-product-prestacks`): the 2-isomorphism `α : F ∘ p₁ ≅ G ∘ p₂` making the fiber
product square 2-commutative; on an object `(x, y', γ)` it is the comparison isomorphism
`γ`. -/
def fiberProductIsoComm :
    (fiberProductFst F G).comp F ≅ (fiberProductSnd F G).comp G :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun a ↦ a.iso) (fun φ ↦ FiberProductHom.w φ))
    (fun a ↦ a.isHomLift)

/-- Two morphisms of based categories with equal underlying functors are equal. -/
lemma _root_.CategoryTheory.BasedFunctor.ext_of_toFunctor_eq {𝒜 : BasedCategory.{v₂, u₂} 𝒮}
    {ℬ : BasedCategory.{v₃, u₃} 𝒮} {F G : 𝒜 ⥤ᵇ ℬ} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  cases F
  cases G
  cases h
  rfl

section ThmFiberProductPrestacks

variable {𝒯 : BasedCategory.{v₅, u₅} 𝒮} (q₁ : 𝒯 ⥤ᵇ 𝒳) (q₂ : 𝒯 ⥤ᵇ 𝒴')
  (τ : q₁.comp F ≅ q₂.comp G)

/-- **Theorem 3.4.35** (`thm:fiber-product-prestacks`) (the implicit definition of the
lift `h`): given a 2-commutative square, i.e. morphisms `q₁ : 𝒯 ⥤ᵇ 𝒳` and `q₂ : 𝒯 ⥤ᵇ 𝒴'`
together with a 2-isomorphism `τ : F ∘ q₁ ≅ G ∘ q₂`, the induced morphism
`𝒯 ⥤ᵇ 𝒳 ×_𝒴 𝒴'`. -/
def fiberProductLift : 𝒯 ⥤ᵇ fiberProduct F G where
  obj t :=
    { fst := q₁.obj t
      snd := q₂.obj t
      over_eq := (Functor.congr_obj q₂.w t).trans (Functor.congr_obj q₁.w t).symm
      iso := ((BasedNatTrans.forgetful 𝒯 𝒴).mapIso τ).app t
      isHomLift := by
        have h := τ.hom.isHomLift' t
        rwa [show 𝒯.p.obj t = 𝒳.p.obj (q₁.obj t) from (Functor.congr_obj q₁.w t).symm] at h }
  map {t t'} φ :=
    { fst := q₁.map φ
      snd := q₂.map φ
      isHomLift := by
        have h1 : 𝒳.p.map (q₁.map φ) =
            eqToHom (Functor.congr_obj q₁.w t) ≫ 𝒯.p.map φ ≫
              eqToHom (Functor.congr_obj q₁.w t').symm := by
          have := Functor.congr_hom q₁.w φ
          simp only [Functor.comp_map] at this
          rw [this]
        rw [h1]
        have : IsHomLift 𝒴'.p (𝒯.p.map φ) (q₂.map φ) := inferInstance
        infer_instance
      w := τ.hom.toNatTrans.naturality φ }
  map_id t := by
    apply FiberProductHom.ext <;> simp
  map_comp φ ψ := by
    apply FiberProductHom.ext <;> simp
  w := q₁.w

/-- **Theorem 3.4.35** (`thm:fiber-product-prestacks`) (the 2-isomorphism `β`, which per
the proof is an equality): the composite of the universal lift with the first projection
is `q₁` on the nose. -/
@[simp]
lemma fiberProductLift_comp_fst :
    (fiberProductLift q₁ q₂ τ).comp (fiberProductFst F G) = q₁ := by
  apply BasedFunctor.ext_of_toFunctor_eq
  exact Functor.ext (fun t ↦ rfl)

/-- **Theorem 3.4.35** (`thm:fiber-product-prestacks`) (the 2-isomorphism `ρ`, which per
the proof is an equality): the composite of the universal lift with the second projection
is `q₂` on the nose. -/
@[simp]
lemma fiberProductLift_comp_snd :
    (fiberProductLift q₁ q₂ τ).comp (fiberProductSnd F G) = q₂ := by
  apply BasedFunctor.ext_of_toFunctor_eq
  exact Functor.ext (fun t ↦ rfl)

/-- **Theorem 3.4.35** (`thm:fiber-product-prestacks`) (the compatibility square for `τ`
and `α`): the given 2-isomorphism `τ` is recovered from the canonical 2-isomorphism of
the fiber product along the universal lift. -/
lemma fiberProductLift_isoComm (t : 𝒯.obj) :
    (fiberProductIsoComm F G).hom.toNatTrans.app ((fiberProductLift q₁ q₂ τ).obj t) =
      (((BasedNatTrans.forgetful 𝒯 𝒴).mapIso τ).app t).hom :=
  rfl

end ThmFiberProductPrestacks


section IsFiberedInGroupoids

/-- A morphism of the fiber product `𝒳 ×_𝒴 𝒴'` whose first component lies over a
morphism `f` of the base lies over `f`. -/
lemma FiberProductHom.isHomLift_of_fst {t' t : FiberProductObj F G} (φ : t' ⟶ t)
    {R S : 𝒮} (f : R ⟶ S) (h : IsHomLift 𝒳.p f (FiberProductHom.fst φ)) :
    IsHomLift (fiberProduct F G).p f φ := by
  have ha : (fiberProduct F G).p.obj t' = R :=
    IsHomLift.domain_eq 𝒳.p f (FiberProductHom.fst φ)
  have hb : (fiberProduct F G).p.obj t = S :=
    IsHomLift.codomain_eq 𝒳.p f (FiberProductHom.fst φ)
  apply IsHomLift.of_commSq (fiberProduct F G).p f φ ha hb
  constructor
  have hfac : (fiberProduct F G).p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm :=
    IsHomLift.fac' 𝒳.p f (FiberProductHom.fst φ)
  rw [hfac]
  simp

/-- The first component of a morphism of the fiber product `𝒳 ×_𝒴 𝒴'` lying over a
morphism `f` of the base lies over `f`. -/
lemma FiberProductHom.isHomLift_fst {t' t : FiberProductObj F G} (φ : t' ⟶ t)
    {R S : 𝒮} (f : R ⟶ S) (h : IsHomLift (fiberProduct F G).p f φ) :
    IsHomLift 𝒳.p f (FiberProductHom.fst φ) := by
  have ha : 𝒳.p.obj t'.fst = R := IsHomLift.domain_eq (fiberProduct F G).p f φ
  have hb : 𝒳.p.obj t.fst = S := IsHomLift.codomain_eq (fiberProduct F G).p f φ
  apply IsHomLift.of_commSq 𝒳.p f (FiberProductHom.fst φ) ha hb
  constructor
  have hfac : 𝒳.p.map (FiberProductHom.fst φ) = eqToHom ha ≫ f ≫ eqToHom hb.symm :=
    IsHomLift.fac' (fiberProduct F G).p f φ
  rw [hfac]
  simp

open Functor.IsFiberedInGroupoids in
/-- **Construction 3.4.33** (`constr:fiber-product-prestacks`) (the constructed category
is a prestack): the fiber product of prestacks is a prestack — if `𝒳`, `𝒴`, `𝒴'` are
fibered in groupoids over `𝒮`, so is `𝒳 ×_𝒴 𝒴'`. -/
instance fiberProduct_isFiberedInGroupoids [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] [𝒴'.p.IsFiberedInGroupoids] :
    (fiberProduct F G).p.IsFiberedInGroupoids where
  exists_isHomLift {t R} f := by
    let f₁ : R ⟶ 𝒳.p.obj t.fst := f
    -- componentwise lifts in `𝒳` and `𝒴'`
    obtain ⟨x', φx, hφx⟩ := Functor.IsFiberedInGroupoids.exists_isHomLift (p := 𝒳.p) f₁
    obtain ⟨y', φy, hφy⟩ := Functor.IsFiberedInGroupoids.exists_isHomLift (p := 𝒴'.p)
      (f₁ ≫ eqToHom t.over_eq.symm)
    -- the comparison morphism `F(φx) ≫ γ_t`, lying over `f₁ ≫ eqToHom`
    haveI := hφx
    haveI := hφy
    haveI hψ : IsHomLift 𝒴.p (f₁ ≫ eqToHom t.over_eq.symm)
        ((F.map φx ≫ t.iso.hom) ≫ 𝟙 (G.obj t.snd)) := by
      haveI h₁ : IsHomLift 𝒴.p (f₁ ≫ 𝟙 (𝒳.p.obj t.fst)) (F.map φx ≫ t.iso.hom) :=
        IsHomLift.comp 𝒴.p f₁ (𝟙 (𝒳.p.obj t.fst)) (F.map φx) t.iso.hom
      haveI h₂ : IsHomLift 𝒴.p (f₁ ≫ 𝟙 (𝒳.p.obj t.fst) ≫ eqToHom t.over_eq.symm)
          ((F.map φx ≫ t.iso.hom) ≫ 𝟙 (G.obj t.snd)) := by
        haveI h₃ : IsHomLift 𝒴.p (eqToHom t.over_eq.symm) (𝟙 (G.obj t.snd)) :=
          IsHomLift.id_lift_eqToHom_codomain t.over_eq.symm (G.w_obj t.snd)
        have h₄ := IsHomLift.comp 𝒴.p (f₁ ≫ 𝟙 (𝒳.p.obj t.fst))
          (eqToHom t.over_eq.symm) (F.map φx ≫ t.iso.hom) (𝟙 (G.obj t.snd))
        simpa using h₄
      simpa using h₂
    -- factor it through the strongly cartesian `G(φy)`
    haveI hGφy : IsStronglyCartesian 𝒴.p (f₁ ≫ eqToHom t.over_eq.symm) (G.map φy) :=
      inferInstance
    set u := IsStronglyCartesian.map 𝒴.p (f₁ ≫ eqToHom t.over_eq.symm) (G.map φy)
      (Category.id_comp (f₁ ≫ eqToHom t.over_eq.symm)).symm
      ((F.map φx ≫ t.iso.hom) ≫ 𝟙 (G.obj t.snd)) with hu
    haveI hu_lift : IsHomLift 𝒴.p (𝟙 R) u :=
      IsStronglyCartesian.map_isHomLift 𝒴.p (f₁ ≫ eqToHom t.over_eq.symm) (G.map φy)
        (Category.id_comp (f₁ ≫ eqToHom t.over_eq.symm)).symm
        ((F.map φx ≫ t.iso.hom) ≫ 𝟙 (G.obj t.snd))
    haveI : IsIso u :=
      Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := 𝒴.p) (S := R) u
    have hu_lift' : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj x')) u := by
      rwa [← IsHomLift.domain_eq 𝒳.p f₁ φx] at hu_lift
    have hover : 𝒴'.p.obj y' = 𝒳.p.obj x' :=
      (IsHomLift.domain_eq 𝒴'.p (f₁ ≫ eqToHom t.over_eq.symm) φy).trans
        (IsHomLift.domain_eq 𝒳.p f₁ φx).symm
    -- assemble the object and the morphism of the fiber product
    have h₇ : u ≫ G.map φy = F.map φx ≫ t.iso.hom := by
      rw [hu, IsStronglyCartesian.fac]
      simp
    refine ⟨⟨x', y', hover, asIso u, by simpa using hu_lift'⟩,
      ⟨φx, φy, ?_, ?_⟩, ?_⟩
    · -- the second component lies over the image of the first
      have ha : 𝒴'.p.obj y' = 𝒳.p.obj x' := hover
      have hb : 𝒴'.p.obj t.snd = 𝒳.p.obj t.fst := t.over_eq
      apply IsHomLift.of_commSq 𝒴'.p (𝒳.p.map φx) φy ha hb
      constructor
      have h₅ := IsHomLift.fac' 𝒴'.p (f₁ ≫ eqToHom t.over_eq.symm) φy
      have h₆ := IsHomLift.fac' 𝒳.p f₁ φx
      rw [h₅, h₆]
      simp
    · -- compatibility with the comparison isomorphisms
      simpa using h₇.symm
    · -- the assembled morphism lies over `f`
      exact FiberProductHom.isHomLift_of_fst _ f hφx
  isStronglyCartesian {t' t} Φ := by
    constructor
    intro t'' g ψ hψ
    let g₁ : 𝒳.p.obj t''.fst ⟶ 𝒳.p.obj t'.fst := g
    haveI hΦfst : IsHomLift 𝒴'.p (𝒳.p.map (FiberProductHom.fst Φ))
        (FiberProductHom.snd Φ) := Φ.isHomLift
    haveI hψs : IsHomLift 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ))
        (FiberProductHom.snd ψ) := ψ.isHomLift
    haveI hψfst : IsHomLift 𝒳.p (g₁ ≫ 𝒳.p.map (FiberProductHom.fst Φ))
        (FiberProductHom.fst ψ) :=
      FiberProductHom.isHomLift_fst ψ (g ≫ (fiberProduct F G).p.map Φ) inferInstance
    -- the first component of the filler
    let χfst : t''.fst ⟶ t'.fst :=
      IsStronglyCartesian.map 𝒳.p (𝒳.p.map (FiberProductHom.fst Φ))
        (FiberProductHom.fst Φ)
        (show g₁ ≫ 𝒳.p.map (FiberProductHom.fst Φ) =
          g₁ ≫ 𝒳.p.map (FiberProductHom.fst Φ) from rfl) (FiberProductHom.fst ψ)
    haveI hχfst : IsHomLift 𝒳.p g₁ χfst :=
      IsStronglyCartesian.map_isHomLift 𝒳.p _ _ _ _
    have hχfst_fac : χfst ≫ FiberProductHom.fst Φ = FiberProductHom.fst ψ :=
      IsStronglyCartesian.fac 𝒳.p _ _ _ _
    -- the second component of the filler
    let gsnd : 𝒴'.p.obj t''.snd ⟶ 𝒴'.p.obj t'.snd :=
      eqToHom t''.over_eq ≫ g₁ ≫ eqToHom t'.over_eq.symm
    haveI hψsnd' : IsHomLift 𝒴'.p
        (eqToHom t''.over_eq ≫ 𝒳.p.map (FiberProductHom.fst ψ) ≫
          eqToHom t.over_eq.symm) (FiberProductHom.snd ψ) := by
      apply IsHomLift.of_commSq 𝒴'.p _ (FiberProductHom.snd ψ) rfl rfl
      constructor
      have h := IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ))
        (FiberProductHom.snd ψ)
      rw [h]
      simp
    have hfsnd : eqToHom t''.over_eq ≫ 𝒳.p.map (FiberProductHom.fst ψ) ≫
        eqToHom t.over_eq.symm = gsnd ≫ 𝒴'.p.map (FiberProductHom.snd Φ) := by
      have h₁ := IsHomLift.fac' 𝒳.p (g₁ ≫ 𝒳.p.map (FiberProductHom.fst Φ))
        (FiberProductHom.fst ψ)
      have h₂ := IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst Φ))
        (FiberProductHom.snd Φ)
      rw [h₁, h₂]
      simp [gsnd]
    let χsnd : t''.snd ⟶ t'.snd :=
      IsStronglyCartesian.map 𝒴'.p (𝒴'.p.map (FiberProductHom.snd Φ))
        (FiberProductHom.snd Φ) hfsnd (FiberProductHom.snd ψ)
    haveI hχsnd : IsHomLift 𝒴'.p gsnd χsnd :=
      IsStronglyCartesian.map_isHomLift 𝒴'.p _ _ _ _
    have hχsnd_fac : χsnd ≫ FiberProductHom.snd Φ = FiberProductHom.snd ψ :=
      IsStronglyCartesian.fac 𝒴'.p _ _ _ _
    -- the two candidate compatibility morphisms agree after the cartesian `G(Φ.snd)`
    haveI hα : IsHomLift 𝒴.p g₁ (F.map χfst ≫ t'.iso.hom) := by
      have h := IsHomLift.comp 𝒴.p g₁ (𝟙 (𝒳.p.obj t'.fst)) (F.map χfst) t'.iso.hom
      simpa using h
    haveI hβ : IsHomLift 𝒴.p g₁ (t''.iso.hom ≫ G.map χsnd) := by
      apply IsHomLift.of_commSq 𝒴.p g₁ (t''.iso.hom ≫ G.map χsnd) (F.w_obj t''.fst)
        ((G.w_obj t'.snd).trans t'.over_eq)
      constructor
      have h₁ : 𝒴.p.map (t''.iso.hom ≫ G.map χsnd) =
          𝒴.p.map t''.iso.hom ≫ 𝒴.p.map (G.map χsnd) := 𝒴.p.map_comp _ _
      have h₂ := IsHomLift.fac' 𝒴.p (𝟙 (𝒳.p.obj t''.fst)) t''.iso.hom
      have h₃ := IsHomLift.fac' 𝒴.p gsnd (G.map χsnd)
      rw [h₁, h₂, h₃]
      simp [gsnd]
    have hαβ : (F.map χfst ≫ t'.iso.hom) ≫ G.map (FiberProductHom.snd Φ) =
        (t''.iso.hom ≫ G.map χsnd) ≫ G.map (FiberProductHom.snd Φ) := by
      calc (F.map χfst ≫ t'.iso.hom) ≫ G.map (FiberProductHom.snd Φ)
          = F.map χfst ≫ F.map (FiberProductHom.fst Φ) ≫ t.iso.hom := by
            rw [Category.assoc, FiberProductHom.w]
        _ = F.map (χfst ≫ FiberProductHom.fst Φ) ≫ t.iso.hom := by
            rw [F.toFunctor.map_comp, Category.assoc]
        _ = F.map (FiberProductHom.fst ψ) ≫ t.iso.hom := by rw [hχfst_fac]
        _ = t''.iso.hom ≫ G.map (FiberProductHom.snd ψ) := FiberProductHom.w ψ
        _ = t''.iso.hom ≫ G.map (χsnd ≫ FiberProductHom.snd Φ) := by rw [hχsnd_fac]
        _ = (t''.iso.hom ≫ G.map χsnd) ≫ G.map (FiberProductHom.snd Φ) := by
            rw [G.toFunctor.map_comp, Category.assoc]
    haveI hGSC : IsStronglyCartesian 𝒴.p (𝒴'.p.map (FiberProductHom.snd Φ))
        (G.map (FiberProductHom.snd Φ)) := inferInstance
    -- retarget the two candidates over the common base `g₁ ≫ eqToHom`
    haveI hα' : IsHomLift 𝒴.p (g₁ ≫ eqToHom t'.over_eq.symm)
        (F.map χfst ≫ t'.iso.hom) := by
      apply IsHomLift.of_commSq 𝒴.p _ (F.map χfst ≫ t'.iso.hom) (F.w_obj t''.fst)
        (G.w_obj t'.snd)
      constructor
      have h := IsHomLift.fac' 𝒴.p g₁ (F.map χfst ≫ t'.iso.hom)
      rw [h]
      simp
    haveI hβ' : IsHomLift 𝒴.p (g₁ ≫ eqToHom t'.over_eq.symm)
        (t''.iso.hom ≫ G.map χsnd) := by
      apply IsHomLift.of_commSq 𝒴.p _ (t''.iso.hom ≫ G.map χsnd) (F.w_obj t''.fst)
        (G.w_obj t'.snd)
      constructor
      have h := IsHomLift.fac' 𝒴.p g₁ (t''.iso.hom ≫ G.map χsnd)
      rw [h]
      simp
    haveI hαm : IsHomLift 𝒴.p
        ((g₁ ≫ eqToHom t'.over_eq.symm) ≫ 𝒴'.p.map (FiberProductHom.snd Φ))
        ((F.map χfst ≫ t'.iso.hom) ≫ G.map (FiberProductHom.snd Φ)) :=
      IsHomLift.comp 𝒴.p (g₁ ≫ eqToHom t'.over_eq.symm)
        (𝒴'.p.map (FiberProductHom.snd Φ))
        (F.map χfst ≫ t'.iso.hom) (G.map (FiberProductHom.snd Φ))
    have hw : F.map χfst ≫ t'.iso.hom = t''.iso.hom ≫ G.map χsnd := by
      have hu₁ := IsStronglyCartesian.map_uniq 𝒴.p
        (𝒴'.p.map (FiberProductHom.snd Φ)) (G.map (FiberProductHom.snd Φ))
        (show (g₁ ≫ eqToHom t'.over_eq.symm) ≫ 𝒴'.p.map (FiberProductHom.snd Φ) =
          (g₁ ≫ eqToHom t'.over_eq.symm) ≫ 𝒴'.p.map (FiberProductHom.snd Φ) from rfl)
        ((F.map χfst ≫ t'.iso.hom) ≫ G.map (FiberProductHom.snd Φ))
        (F.map χfst ≫ t'.iso.hom) rfl
      have hu₂ := IsStronglyCartesian.map_uniq 𝒴.p
        (𝒴'.p.map (FiberProductHom.snd Φ)) (G.map (FiberProductHom.snd Φ))
        (show (g₁ ≫ eqToHom t'.over_eq.symm) ≫ 𝒴'.p.map (FiberProductHom.snd Φ) =
          (g₁ ≫ eqToHom t'.over_eq.symm) ≫ 𝒴'.p.map (FiberProductHom.snd Φ) from rfl)
        ((F.map χfst ≫ t'.iso.hom) ≫ G.map (FiberProductHom.snd Φ))
        (t''.iso.hom ≫ G.map χsnd) hαβ.symm
      rw [hu₁, hu₂]
    -- assemble the filler and prove uniqueness
    refine ⟨⟨χfst, χsnd, ?_, hw⟩, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_commSq 𝒴'.p (𝒳.p.map χfst) χsnd t''.over_eq t'.over_eq
      constructor
      have h₁ := IsHomLift.fac' 𝒴'.p gsnd χsnd
      have h₂ := IsHomLift.fac' 𝒳.p g₁ χfst
      rw [h₁, h₂]
      simp [gsnd]
    · exact FiberProductHom.isHomLift_of_fst _ g hχfst
    · apply FiberProductHom.ext
      · simpa using hχfst_fac
      · simpa using hχsnd_fac
    · intro χ' hχ'
      obtain ⟨hχ'lift, hχ'fac⟩ := hχ'
      haveI hχ'fst : IsHomLift 𝒳.p g₁ (FiberProductHom.fst χ') :=
        FiberProductHom.isHomLift_fst χ' g hχ'lift
      have hfstu : FiberProductHom.fst χ' = χfst := by
        apply IsStronglyCartesian.map_uniq 𝒳.p (𝒳.p.map (FiberProductHom.fst Φ))
          (FiberProductHom.fst Φ) _ (FiberProductHom.fst ψ) (FiberProductHom.fst χ')
        have h := congrArg FiberProductHom.fst hχ'fac
        simpa using h
      haveI hχ'snd : IsHomLift 𝒴'.p gsnd (FiberProductHom.snd χ') := by
        apply IsHomLift.of_commSq 𝒴'.p gsnd (FiberProductHom.snd χ') rfl rfl
        constructor
        have h₁ := IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst χ'))
          (FiberProductHom.snd χ')
        have h₂ := IsHomLift.fac' 𝒳.p g₁ (FiberProductHom.fst χ')
        rw [h₁]
        simp only [h₂]
        simp [gsnd]
      have hsndu : FiberProductHom.snd χ' = χsnd := by
        apply IsStronglyCartesian.map_uniq 𝒴'.p (𝒴'.p.map (FiberProductHom.snd Φ))
          (FiberProductHom.snd Φ) hfsnd (FiberProductHom.snd ψ) (FiberProductHom.snd χ')
        have h := congrArg FiberProductHom.snd hχ'fac
        simpa using h
      apply FiberProductHom.ext
      · exact hfstu
      · exact hsndu

/-- A prescribed lift in the first component can be completed to a lift in the fiber
product. This is the componentwise lifting bridge used when gluing morphisms in a fiber
product of stacks. -/
lemma exists_fiberProduct_lift_of_fst [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] [𝒴'.p.IsFiberedInGroupoids]
    {t : FiberProductObj F G} {R : 𝒮} {x : 𝒳.obj} (f : R ⟶ 𝒳.p.obj t.fst)
    (ξ : x ⟶ t.fst) (hξ : IsHomLift 𝒳.p f ξ) :
    ∃ (z : FiberProductObj F G) (ψ : z ⟶ t) (hz : z.fst = x),
      eqToHom hz.symm ≫ FiberProductHom.fst ψ = ξ ∧
        IsHomLift (fiberProduct F G).p f ψ := by
  letI := hξ
  obtain ⟨z, ψ, hψ⟩ :=
    Functor.IsFiberedInGroupoids.exists_isHomLift (p := (fiberProduct F G).p) f
  haveI := hψ
  haveI hψfst : IsHomLift 𝒳.p f (FiberProductHom.fst ψ) :=
    FiberProductHom.isHomLift_fst ψ f hψ
  let δ : x ⟶ z.fst :=
    IsStronglyCartesian.map 𝒳.p f (FiberProductHom.fst ψ)
      (Category.id_comp f).symm ξ
  haveI hδ : IsHomLift 𝒳.p (𝟙 R) δ :=
    IsStronglyCartesian.map_isHomLift 𝒳.p f (FiberProductHom.fst ψ)
      (Category.id_comp f).symm ξ
  have hδfac : δ ≫ FiberProductHom.fst ψ = ξ :=
    IsStronglyCartesian.fac 𝒳.p f (FiberProductHom.fst ψ)
      (Category.id_comp f).symm ξ
  haveI : IsIso δ :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := 𝒳.p) (S := R) δ
  have hover : 𝒴'.p.obj z.snd = 𝒳.p.obj x :=
    z.over_eq.trans (IsHomLift.codomain_eq 𝒳.p (𝟙 R) δ) |>.trans
      (IsHomLift.domain_eq 𝒳.p (𝟙 R) δ).symm
  let e : F.obj x ≅ G.obj z.snd := asIso (F.map δ) ≪≫ z.iso
  have heLift : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj x)) e.hom := by
    apply IsHomLift.of_fac 𝒴.p (𝟙 (𝒳.p.obj x)) e.hom
      (F.w_obj x) ((G.w_obj z.snd).trans hover)
    dsimp [e]
    rw [𝒴.p.map_comp, IsHomLift.fac' 𝒴.p (𝟙 R) (F.map δ),
      IsHomLift.fac' 𝒴.p (𝟙 (𝒳.p.obj z.fst)) z.iso.hom]
    simp
  let z' : FiberProductObj F G := ⟨x, z.snd, hover, e, heLift⟩
  let ψsnd : z'.snd ⟶ t.snd := by
    change z.snd ⟶ t.snd
    exact FiberProductHom.snd ψ
  have hsndLift : IsHomLift 𝒴'.p (𝒳.p.map ξ) (FiberProductHom.snd ψ) := by
    apply IsHomLift.of_fac 𝒴'.p (𝒳.p.map ξ) (FiberProductHom.snd ψ)
      hover t.over_eq
    rw [IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ))
      (FiberProductHom.snd ψ), ← hδfac, 𝒳.p.map_comp,
      IsHomLift.fac' 𝒳.p (𝟙 R) δ]
    simp
  let ψ' : z' ⟶ t :=
    { fst := ξ
      snd := ψsnd
      isHomLift := hsndLift
      w := by
        dsimp [z', e]
        change F.map ξ ≫ t.iso.hom =
          (F.map δ ≫ z.iso.hom) ≫ G.map (FiberProductHom.snd ψ)
        calc
          F.map ξ ≫ t.iso.hom = F.map (δ ≫ FiberProductHom.fst ψ) ≫ t.iso.hom := by
            rw [hδfac]
          _ = F.map δ ≫ (F.map (FiberProductHom.fst ψ) ≫ t.iso.hom) := by
            rw [F.toFunctor.map_comp, Category.assoc]
          _ = F.map δ ≫ (z.iso.hom ≫ G.map (FiberProductHom.snd ψ)) := by
            rw [ψ.w]
          _ = (F.map δ ≫ z.iso.hom) ≫ G.map (FiberProductHom.snd ψ) := by
            rw [Category.assoc] }
  refine ⟨z', ψ', rfl, ?_, ?_⟩
  · dsimp [ψ']
    simp
  exact FiberProductHom.isHomLift_of_fst ψ' f hξ

/-- A prescribed lift in the second component can be completed to a lift in the fiber
product. -/
lemma exists_fiberProduct_lift_of_snd [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] [𝒴'.p.IsFiberedInGroupoids]
    {t : FiberProductObj F G} {R : 𝒮} {y : 𝒴'.obj} (f : R ⟶ 𝒳.p.obj t.fst)
    (ξ : y ⟶ t.snd)
    (hξ : IsHomLift 𝒴'.p (f ≫ eqToHom t.over_eq.symm) ξ) :
    ∃ (z : FiberProductObj F G) (ψ : z ⟶ t) (hz : z.snd = y),
      eqToHom hz.symm ≫ FiberProductHom.snd ψ = ξ ∧
        IsHomLift (fiberProduct F G).p f ψ := by
  letI := hξ
  obtain ⟨z, ψ, hψ⟩ :=
    Functor.IsFiberedInGroupoids.exists_isHomLift (p := (fiberProduct F G).p) f
  haveI := hψ
  haveI hψfst : IsHomLift 𝒳.p f (FiberProductHom.fst ψ) :=
    FiberProductHom.isHomLift_fst ψ f hψ
  haveI hψsnd : IsHomLift 𝒴'.p (f ≫ eqToHom t.over_eq.symm)
      (FiberProductHom.snd ψ) := by
    apply IsHomLift.of_commSq 𝒴'.p (f ≫ eqToHom t.over_eq.symm)
      (FiberProductHom.snd ψ)
      (z.over_eq.trans (IsHomLift.domain_eq 𝒳.p f (FiberProductHom.fst ψ))) rfl
    constructor
    simpa using (calc
      𝒴'.p.map (FiberProductHom.snd ψ) =
          eqToHom z.over_eq ≫ 𝒳.p.map (FiberProductHom.fst ψ) ≫
            eqToHom t.over_eq.symm :=
        IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ))
          (FiberProductHom.snd ψ)
      _ = eqToHom (z.over_eq.trans
            (IsHomLift.domain_eq 𝒳.p f (FiberProductHom.fst ψ))) ≫
          (f ≫ eqToHom t.over_eq.symm) := by
        rw [IsHomLift.fac' 𝒳.p f (FiberProductHom.fst ψ)]
        simp)
  let δ : y ⟶ z.snd :=
    IsStronglyCartesian.map 𝒴'.p (f ≫ eqToHom t.over_eq.symm)
      (FiberProductHom.snd ψ) (Category.id_comp _).symm ξ
  haveI hδ : IsHomLift 𝒴'.p (𝟙 R) δ :=
    IsStronglyCartesian.map_isHomLift 𝒴'.p (f ≫ eqToHom t.over_eq.symm)
      (FiberProductHom.snd ψ) (Category.id_comp _).symm ξ
  have hδfac : δ ≫ FiberProductHom.snd ψ = ξ :=
    IsStronglyCartesian.fac 𝒴'.p (f ≫ eqToHom t.over_eq.symm)
      (FiberProductHom.snd ψ) (Category.id_comp _).symm ξ
  haveI : IsIso δ :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := 𝒴'.p) (S := R) δ
  have hover : 𝒴'.p.obj y = 𝒳.p.obj z.fst :=
    (IsHomLift.domain_eq 𝒴'.p (𝟙 R) δ).trans
      (IsHomLift.codomain_eq 𝒴'.p (𝟙 R) δ).symm |>.trans z.over_eq
  let e : F.obj z.fst ≅ G.obj y := z.iso ≪≫ (asIso (G.map δ)).symm
  have heLift : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj z.fst)) e.hom := by
    apply IsHomLift.of_fac 𝒴.p (𝟙 (𝒳.p.obj z.fst)) e.hom
      (F.w_obj z.fst) ((G.w_obj y).trans hover)
    dsimp [e]
    rw [𝒴.p.map_comp, IsHomLift.fac' 𝒴.p (𝟙 (𝒳.p.obj z.fst)) z.iso.hom]
    have hInv := IsHomLift.fac' 𝒴.p (𝟙 R) (inv (G.map δ))
    rw [hInv]
    simp
  let z' : FiberProductObj F G := ⟨z.fst, y, hover, e, heLift⟩
  let ψfst : z'.fst ⟶ t.fst := by
    change z.fst ⟶ t.fst
    exact FiberProductHom.fst ψ
  have hsndLift : IsHomLift 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ)) ξ := by
    apply IsHomLift.of_fac 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ)) ξ hover t.over_eq
    rw [← hδfac, 𝒴'.p.map_comp,
      IsHomLift.fac' 𝒴'.p (𝟙 R) δ,
      IsHomLift.fac' 𝒴'.p (𝒳.p.map (FiberProductHom.fst ψ))
        (FiberProductHom.snd ψ)]
    simp
  let ψ' : z' ⟶ t :=
    { fst := ψfst
      snd := ξ
      isHomLift := hsndLift
      w := by
        dsimp [z', e]
        change F.map (FiberProductHom.fst ψ) ≫ t.iso.hom =
          (z.iso.hom ≫ inv (G.map δ)) ≫ G.map ξ
        calc
          F.map (FiberProductHom.fst ψ) ≫ t.iso.hom =
              z.iso.hom ≫ G.map (FiberProductHom.snd ψ) := ψ.w
          _ = (z.iso.hom ≫ inv (G.map δ)) ≫ G.map ξ := by
            symm
            calc
              (z.iso.hom ≫ inv (G.map δ)) ≫ G.map ξ =
                  (z.iso.hom ≫ inv (G.map δ)) ≫
                    G.map (δ ≫ FiberProductHom.snd ψ) := by rw [hδfac]
              _ = z.iso.hom ≫ G.map (FiberProductHom.snd ψ) := by
                rw [G.toFunctor.map_comp]
                simp }
  refine ⟨z', ψ', rfl, ?_, ?_⟩
  · dsimp [ψ']
    simp
  exact FiberProductHom.isHomLift_of_fst ψ' f hψfst

end IsFiberedInGroupoids

end CategoryTheory.BasedCategory

end ConstrFiberProductPrestacks


section ThmFiberProductPrestacks

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {Sbase : Type u₁} [Category.{v₁} Sbase]
  {X : BasedCategory.{v₂, u₂} Sbase} {Y : BasedCategory.{v₃, u₃} Sbase}
  {Y' : BasedCategory.{v₄, u₄} Sbase} {T : BasedCategory.{v₅, u₅} Sbase}
  {F : BasedFunctor X Y} {G : BasedFunctor Y' Y}
  (q₁ : BasedFunctor T X) (q₂ : BasedFunctor T Y') (tau : q₁.comp F ≅ q₂.comp G)

/-- A componentwise isomorphism between objects of a fiber product. This is the local
glue needed for the uniqueness clause of Theorem 3.4.35. -/
def fiberProductObjIsoMk {a b : FiberProductObj F G} (e₁ : a.fst ≅ b.fst)
    (e₂ : a.snd ≅ b.snd) (hl : IsHomLift Y'.p (X.p.map e₁.hom) e₂.hom)
    (w : F.map e₁.hom ≫ b.iso.hom = a.iso.hom ≫ G.map e₂.hom) : a ≅ b where
  hom := ⟨e₁.hom, e₂.hom, hl, w⟩
  inv :=
    { fst := e₁.inv
      snd := e₂.inv
      isHomLift := by
        have h₁ : IsHomLift Y'.p (X.p.mapIso e₁).hom e₂.hom := hl
        have h₂ := IsHomLift.inv_lift_inv (p := Y'.p) (f := X.p.mapIso e₁) (φ := e₂)
        simpa using h₂
      w := by
        rw [← cancel_mono (G.map e₂.hom), Category.assoc, Category.assoc,
          ← G.toFunctor.map_comp, Iso.inv_hom_id, G.toFunctor.map_id, Category.comp_id,
          ← w, ← Category.assoc, ← F.toFunctor.map_comp, Iso.inv_hom_id,
          F.toFunctor.map_id, Category.id_comp] }
  hom_inv_id := by
    apply FiberProductHom.ext <;> simp
  inv_hom_id := by
    apply FiberProductHom.ext <;> simp

/-- **Theorem 3.4.35** (`thm:fiber-product-prestacks`) (uniqueness): let `h` be any
lift of a 2-commutative square to `𝒳 ×_𝒴 𝒴'`, with 2-isomorphisms
`beta : q₁ ≅ p₁ h` and `rho : q₂ ≅ p₂ h` satisfying the compatibility square.
There is a unique 2-isomorphism from `h` to the canonical lift whose projections are
`beta⁻¹` and `rho⁻¹`. Thus the data `(h, beta, rho)` is unique up to unique
isomorphism. -/
theorem fiberProductLift_unique (h : BasedFunctor T (fiberProduct F G))
    (beta : q₁ ≅ h.comp (fiberProductFst F G))
    (rho : q₂ ≅ h.comp (fiberProductSnd F G))
    (comm : ∀ t : T.obj,
      F.map (beta.hom.toNatTrans.app t) ≫ (h.obj t).iso.hom =
        (((BasedNatTrans.forgetful T Y).mapIso tau).app t).hom ≫
          G.map (rho.hom.toNatTrans.app t)) :
    ∃! eta : h ≅ fiberProductLift q₁ q₂ tau,
      (∀ t : T.obj,
        FiberProductHom.fst (eta.hom.toNatTrans.app t) = beta.inv.toNatTrans.app t) ∧
      (∀ t : T.obj,
        FiberProductHom.snd (eta.hom.toNatTrans.app t) = rho.inv.toNatTrans.app t) := by
  let app (t : T.obj) : h.obj t ≅ (fiberProductLift q₁ q₂ tau).obj t :=
    fiberProductObjIsoMk
      (((BasedNatTrans.forgetful T X).mapIso beta).app t).symm
      (((BasedNatTrans.forgetful T Y').mapIso rho).app t).symm
      (by
        apply IsHomLift.of_commSq Y'.p (X.p.map (beta.inv.toNatTrans.app t))
          (rho.inv.toNatTrans.app t) (h.obj t).over_eq
          ((fiberProductLift q₁ q₂ tau).obj t).over_eq
        constructor
        have hrho := IsHomLift.fac' Y'.p (𝟙 (T.p.obj t))
          (rho.inv.toNatTrans.app t)
        have hbeta' := IsHomLift.fac' X.p (𝟙 (T.p.obj t))
          (beta.inv.toNatTrans.app t)
        rw [hrho, hbeta']
        simp)
      (by
        show F.map (beta.inv.toNatTrans.app t) ≫
            (((BasedNatTrans.forgetful T Y).mapIso tau).app t).hom =
          (h.obj t).iso.hom ≫ G.map (rho.inv.toNatTrans.app t)
        rw [← cancel_mono (G.map (rho.hom.toNatTrans.app t))]
        have hbeta : beta.inv.toNatTrans.app t ≫ beta.hom.toNatTrans.app t =
            𝟙 (h.obj t).fst := by
          have hbeta' := congrArg (fun k ↦ k.toNatTrans.app t) beta.inv_hom_id
          change beta.inv.toNatTrans.app t ≫ beta.hom.toNatTrans.app t =
            𝟙 (h.obj t).fst at hbeta'
          exact hbeta'
        have hrho : rho.inv.toNatTrans.app t ≫ rho.hom.toNatTrans.app t =
            𝟙 (h.obj t).snd := by
          have hrho' := congrArg (fun k ↦ k.toNatTrans.app t) rho.inv_hom_id
          change rho.inv.toNatTrans.app t ≫ rho.hom.toNatTrans.app t =
            𝟙 (h.obj t).snd at hrho'
          exact hrho'
        have hFid : F.map (𝟙 (h.obj t).fst) = 𝟙 (F.obj (h.obj t).fst) :=
          F.toFunctor.map_id _
        have hGid : G.map (𝟙 (h.obj t).snd) = 𝟙 (G.obj (h.obj t).snd) :=
          G.toFunctor.map_id _
        calc
          (F.map (beta.inv.toNatTrans.app t) ≫
                (((BasedNatTrans.forgetful T Y).mapIso tau).app t).hom) ≫
              G.map (rho.hom.toNatTrans.app t) =
              F.map (beta.inv.toNatTrans.app t) ≫
                ((((BasedNatTrans.forgetful T Y).mapIso tau).app t).hom ≫
                  G.map (rho.hom.toNatTrans.app t)) := Category.assoc _ _ _
          _ = F.map (beta.inv.toNatTrans.app t) ≫
                (F.map (beta.hom.toNatTrans.app t) ≫ (h.obj t).iso.hom) := by
              rw [comm t]
          _ = F.map (beta.inv.toNatTrans.app t ≫ beta.hom.toNatTrans.app t) ≫
                (h.obj t).iso.hom := by
              rw [F.toFunctor.map_comp, Category.assoc]
          _ = (h.obj t).iso.hom := by
              rw [hbeta, hFid]
              show 𝟙 (F.obj (h.obj t).fst) ≫ (h.obj t).iso.hom = (h.obj t).iso.hom
              simp
          _ = (h.obj t).iso.hom ≫
                G.map (rho.inv.toNatTrans.app t ≫ rho.hom.toNatTrans.app t) := by
              rw [hrho, hGid]
              show (h.obj t).iso.hom = (h.obj t).iso.hom ≫ 𝟙 (G.obj (h.obj t).snd)
              simp
          _ = ((h.obj t).iso.hom ≫ G.map (rho.inv.toNatTrans.app t)) ≫
                G.map (rho.hom.toNatTrans.app t) := by
              rw [G.toFunctor.map_comp, Category.assoc])
  let eta : h ≅ fiberProductLift q₁ q₂ tau :=
    BasedNatIso.mkNatIso
      (NatIso.ofComponents app (fun {t t'} phi ↦ by
        apply FiberProductHom.ext
        · exact beta.inv.toNatTrans.naturality phi
        · exact rho.inv.toNatTrans.naturality phi))
      (fun t ↦ FiberProductHom.isHomLift_of_fst _ (𝟙 (T.p.obj t))
        (beta.inv.isHomLift' t))
  refine ⟨eta, ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩, ?_⟩
  intro eta' heta'
  apply Iso.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext t
  apply FiberProductHom.ext
  · exact (heta'.1 t).trans (show beta.inv.toNatTrans.app t =
      FiberProductHom.fst (eta.hom.toNatTrans.app t) from rfl)
  · exact (heta'.2 t).trans (show rho.inv.toNatTrans.app t =
      FiberProductHom.snd (eta.hom.toNatTrans.app t) from rfl)

/-- Background definition following Theorem 3.4.35 (the unlabeled definition
following the theorem): a 2-commutative square is cartesian when its canonical
comparison to the explicit fiber product is an equivalence of categories. By
`fiberProductLift_unique`, this is equivalent to satisfying the theorem's universal
property. -/
abbrev IsCartesianSquare (q₁ : BasedFunctor T X) (q₂ : BasedFunctor T Y')
    (tau : q₁.comp F ≅ q₂.comp G) : Prop :=
  (fiberProductLift q₁ q₂ tau).toFunctor.IsEquivalence

end CategoryTheory.BasedCategory

end ThmFiberProductPrestacks
