module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2a-action-quotient-prestacks»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»

/-!
# The action quotient as a categorical quotient

This module formalizes the true categorical content of
`exer:prestack-quotient-categorical` (Exercise 3.4.27) of §3.4 (Prestacks) of
*Stacks and Moduli*, section label
`sec:prestacks`.

For a group-valued presheaf `G` acting on a set-valued presheaf `U`, it constructs the
map from the prestack associated to `U` to the action quotient `[U/G]^pre`, together
with the canonical 2-isomorphism identifying the action and projection after passing to
the quotient. The printed universal property omits the unit and cocycle coherence on its
input 2-isomorphism and is false as stated; see the section commentary.

Main declarations:
- `CategoryTheory.PresheafAction.quotientMap`;
- `CategoryTheory.PresheafAction.quotientActionIso`;
- `CategoryTheory.PresheafAction.CoherentQuotientDatum.descend` and `.descendIso`;
- `CategoryTheory.PresheafAction.CoherentQuotientDatum.descendIso_compatibility`;
- `CategoryTheory.PresheafAction.CoherentQuotientDatum.CoherentFactorization.comparison`
  and `.comparison_unique`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerPrestackQuotientCategorical

open CategoryTheory Functor

universe w v u

namespace CategoryTheory.PresheafAction

open Opposite

variable {C : Type u} [Category.{v} C] (A : PresheafAction.{w} C)

/-- An object in the category of elements of the acted-on presheaf `U`. This is kept
as a distinct type from `QuotientObj`, since the two categories have different
morphisms. -/
structure ElementObj where
  /-- The object of the base category. -/
  base : C
  /-- The section over that base object. -/
  point : A.U.obj (op base)

/-- The morphisms in the category of elements of the acted-on presheaf `U`. -/
@[ext]
structure ElementHom (x y : A.ElementObj) where
  /-- The underlying morphism in the base. -/
  base : x.base ⟶ y.base
  /-- Pullback of the target section is the source section. -/
  relation : A.U.map base.op y.point = x.point

/-- Identity morphisms in the category of elements of `U`. -/
@[simps]
def ElementHom.id (x : A.ElementObj) : A.ElementHom x x where
  base := 𝟙 x.base
  relation := by
    simpa using congrArg (fun q ↦ q x.point) (A.U.map_id (op x.base))

/-- Composition in the category of elements of `U`. -/
@[simps]
def ElementHom.comp {x y z : A.ElementObj} (f : A.ElementHom x y)
    (g : A.ElementHom y z) : A.ElementHom x z where
  base := f.base ≫ g.base
  relation := by
    calc
      A.U.map (f.base ≫ g.base).op z.point =
          A.U.map f.base.op (A.U.map g.base.op z.point) := by
        exact congrArg (fun q ↦ q z.point) (A.U.map_comp g.base.op f.base.op)
      _ = A.U.map f.base.op y.point := by rw [g.relation]
      _ = x.point := f.relation

instance elementCategory : Category A.ElementObj where
  Hom := A.ElementHom
  id := ElementHom.id A
  comp := ElementHom.comp A
  id_comp f := by ext; simp [ElementHom.comp, ElementHom.id]
  comp_id f := by ext; simp [ElementHom.comp, ElementHom.id]
  assoc f g h := by ext; simp [ElementHom.comp]

@[simp]
lemma ElementObj.id_base (x : A.ElementObj) :
    ElementHom.base (𝟙 x) = 𝟙 x.base :=
  rfl

@[simp]
lemma ElementObj.comp_base {x y z : A.ElementObj} (f : x ⟶ y) (g : y ⟶ z) :
    ElementHom.base (f ≫ g) = f.base ≫ g.base :=
  rfl

/-- The projection from the category of elements of `U` to the base. -/
@[simps]
def elementProj : A.ElementObj ⥤ C where
  obj x := x.base
  map f := f.base

/-- A morphism in the category of elements lies over its stored base morphism. -/
instance elementHom_isHomLift {x y : A.ElementObj} (f : A.ElementHom x y) :
    A.elementProj.IsHomLift f.base f := by
  apply IsHomLift.of_fac' A.elementProj f.base f rfl rfl
  simp [elementProj]

/-- The prestack associated to the set-valued presheaf `U`. -/
abbrev elementPrestack : BasedCategory C :=
  BasedCategory.ofFunctor A.elementProj

/-- The category of elements of `U` is a prestack. -/
instance elementProj_isFiberedInGroupoids : A.elementProj.IsFiberedInGroupoids where
  exists_isHomLift {y R} f := by
    let x : A.ElementObj :=
      { base := R
        point := A.U.map f.op y.point }
    let phi : A.ElementHom x y :=
      { base := f
        relation := rfl }
    refine ⟨x, phi, ?_⟩
    apply IsHomLift.of_fac' A.elementProj f phi rfl rfl
    simp [elementProj, phi]
  isStronglyCartesian {x y} phi := by
    change A.ElementHom x y at phi
    constructor
    intro z f psi hpsi
    letI : A.elementProj.IsHomLift (f ≫ A.elementProj.map phi) psi := hpsi
    change A.ElementHom z y at psi
    change z.base ⟶ x.base at f
    have hbase : f ≫ phi.base = psi.base := by
      have h := IsHomLift.eq_of_isHomLift A.elementProj
        (f ≫ A.elementProj.map phi) psi
      exact h
    let chi : A.ElementHom z x :=
      { base := f
        relation := by
          calc
            A.U.map f.op x.point =
                A.U.map f.op (A.U.map phi.base.op y.point) := by rw [phi.relation]
            _ = A.U.map (phi.base.op ≫ f.op) y.point := by
              exact congrArg (fun q ↦ q y.point)
                (A.U.map_comp phi.base.op f.op).symm
            _ = A.U.map psi.base.op y.point := by
              rw [show phi.base.op ≫ f.op = psi.base.op by rw [← op_comp, hbase]]
            _ = z.point := psi.relation }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_fac' A.elementProj f chi rfl rfl
      simp [elementProj, chi]
    · apply ElementHom.ext
      exact hbase
    · intro chi' hchi'
      change A.ElementHom z x at chi'
      apply ElementHom.ext
      letI : A.elementProj.IsHomLift f chi' := hchi'.1
      have h := IsHomLift.eq_of_isHomLift A.elementProj f chi'
      exact h.symm

/-- An object of the presheaf `G × U` parametrizing an action arrow. -/
structure ActionObj where
  /-- The base object. -/
  base : C
  /-- The acting group element. -/
  gauge : A.G.obj (op base)
  /-- The point acted on. -/
  point : A.U.obj (op base)

/-- A morphism in the category of elements of `G × U`. -/
@[ext]
structure ActionHom (x y : A.ActionObj) where
  /-- The underlying morphism in the base. -/
  base : x.base ⟶ y.base
  /-- The group element is obtained by restriction. -/
  gauge_relation : A.G.map base.op y.gauge = x.gauge
  /-- The point is obtained by restriction. -/
  point_relation : A.U.map base.op y.point = x.point

/-- Identity morphisms in the category of elements of `G × U`. -/
@[simps]
def ActionHom.id (x : A.ActionObj) : A.ActionHom x x where
  base := 𝟙 x.base
  gauge_relation := by
    simpa using congrArg (fun q ↦ q x.gauge) (A.G.map_id (op x.base))
  point_relation := by
    simpa using congrArg (fun q ↦ q x.point) (A.U.map_id (op x.base))

/-- Composition in the category of elements of `G × U`. -/
@[simps]
def ActionHom.comp {x y z : A.ActionObj} (f : A.ActionHom x y)
    (g : A.ActionHom y z) : A.ActionHom x z where
  base := f.base ≫ g.base
  gauge_relation := by
    calc
      A.G.map (f.base ≫ g.base).op z.gauge =
          A.G.map f.base.op (A.G.map g.base.op z.gauge) := by
        exact congrArg (fun q ↦ q z.gauge) (A.G.map_comp g.base.op f.base.op)
      _ = A.G.map f.base.op y.gauge := by rw [g.gauge_relation]
      _ = x.gauge := f.gauge_relation
  point_relation := by
    calc
      A.U.map (f.base ≫ g.base).op z.point =
          A.U.map f.base.op (A.U.map g.base.op z.point) := by
        exact congrArg (fun q ↦ q z.point) (A.U.map_comp g.base.op f.base.op)
      _ = A.U.map f.base.op y.point := by rw [g.point_relation]
      _ = x.point := f.point_relation

instance actionCategory : Category A.ActionObj where
  Hom := A.ActionHom
  id := ActionHom.id A
  comp := ActionHom.comp A
  id_comp f := by ext <;> simp [ActionHom.comp, ActionHom.id]
  comp_id f := by ext <;> simp [ActionHom.comp, ActionHom.id]
  assoc f g h := by ext <;> simp [ActionHom.comp]

/-- The projection from the category of elements of `G × U` to the base. -/
@[simps]
def actionProj : A.ActionObj ⥤ C where
  obj x := x.base
  map f := f.base

/-- A morphism in the category of elements of `G × U` lies over its stored base
morphism. -/
instance actionHom_isHomLift {x y : A.ActionObj} (f : A.ActionHom x y) :
    A.actionProj.IsHomLift f.base f := by
  apply IsHomLift.of_fac' A.actionProj f.base f rfl rfl
  simp [actionProj]

/-- The prestack associated to the presheaf `G × U`. -/
abbrev actionPrestack : BasedCategory C :=
  BasedCategory.ofFunctor A.actionProj

/-- The category of elements of `G × U` is a prestack. -/
instance actionProj_isFiberedInGroupoids : A.actionProj.IsFiberedInGroupoids where
  exists_isHomLift {y R} f := by
    let x : A.ActionObj :=
      { base := R
        gauge := A.G.map f.op y.gauge
        point := A.U.map f.op y.point }
    let phi : A.ActionHom x y :=
      { base := f
        gauge_relation := rfl
        point_relation := rfl }
    refine ⟨x, phi, ?_⟩
    apply IsHomLift.of_fac' A.actionProj f phi rfl rfl
    simp [actionProj, phi]
  isStronglyCartesian {x y} phi := by
    change A.ActionHom x y at phi
    constructor
    intro z f psi hpsi
    letI : A.actionProj.IsHomLift (f ≫ A.actionProj.map phi) psi := hpsi
    change A.ActionHom z y at psi
    change z.base ⟶ x.base at f
    have hbase : f ≫ phi.base = psi.base := by
      have h := IsHomLift.eq_of_isHomLift A.actionProj
        (f ≫ A.actionProj.map phi) psi
      exact h
    let chi : A.ActionHom z x :=
      { base := f
        gauge_relation := by
          calc
            A.G.map f.op x.gauge =
                A.G.map f.op (A.G.map phi.base.op y.gauge) := by
              rw [phi.gauge_relation]
            _ = A.G.map (phi.base.op ≫ f.op) y.gauge := by
              exact congrArg (fun q ↦ q y.gauge)
                (A.G.map_comp phi.base.op f.op).symm
            _ = A.G.map psi.base.op y.gauge := by
              rw [show phi.base.op ≫ f.op = psi.base.op by rw [← op_comp, hbase]]
            _ = z.gauge := psi.gauge_relation
        point_relation := by
          calc
            A.U.map f.op x.point =
                A.U.map f.op (A.U.map phi.base.op y.point) := by
              rw [phi.point_relation]
            _ = A.U.map (phi.base.op ≫ f.op) y.point := by
              exact congrArg (fun q ↦ q y.point)
                (A.U.map_comp phi.base.op f.op).symm
            _ = A.U.map psi.base.op y.point := by
              rw [show phi.base.op ≫ f.op = psi.base.op by rw [← op_comp, hbase]]
            _ = z.point := psi.point_relation }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_fac' A.actionProj f chi rfl rfl
      simp [actionProj, chi]
    · apply ActionHom.ext
      exact hbase
    · intro chi' hchi'
      change A.ActionHom z x at chi'
      apply ActionHom.ext
      letI : A.actionProj.IsHomLift f chi' := hchi'.1
      have h := IsHomLift.eq_of_isHomLift A.actionProj f chi'
      exact h.symm

/-- The action map `G × U → U` as a morphism of prestacks. -/
@[simps]
def actionMap : A.actionPrestack ⥤ᵇ A.elementPrestack where
  obj x :=
    { base := x.base
      point := letI := A.action (op x.base); x.gauge • x.point }
  map {x y} f :=
    { base := f.base
      relation := by
        letI := A.action (op x.base)
        letI := A.action (op y.base)
        rw [A.map_smul, f.gauge_relation, f.point_relation] }
  w := rfl

/-- The second projection `G × U → U` as a morphism of prestacks. -/
@[simps]
def actionSnd : A.actionPrestack ⥤ᵇ A.elementPrestack where
  obj x :=
    { base := x.base
      point := x.point }
  map f :=
    { base := f.base
      relation := f.point_relation }
  w := rfl

/-- Background coercion used in Exercise 3.4.27 (part (a), the map
`p`): the canonical morphism from `U` to its action quotient `[U/G]^pre`. -/
abbrev asQuotient (x : A.ElementObj) : A.QuotientObj :=
  { base := x.base
    point := x.point }

/-- The quotient arrow associated to an arrow of the category of elements. -/
abbrev quotientOfElementHom {x y : A.ElementObj} (f : A.ElementHom x y) :
    A.QuotientHom (A.asQuotient x) (A.asQuotient y) where
  base := f.base
  gauge := 1
  relation := by
    letI := A.action (op x.base)
    simpa using f.relation

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (a), the map
`p`): the canonical morphism from `U` to its action quotient `[U/G]^pre`. -/
@[simps!]
abbrev quotientMap : A.elementPrestack ⥤ᵇ A.quotientPrestack where
  obj x := A.asQuotient x
  map f := A.quotientOfElementHom f
  map_id x := by
    apply QuotientHom.ext
    · change 𝟙 x.base = 𝟙 x.base
      rfl
    · change 1 = 1
      rfl
  map_comp f g := by
    apply QuotientHom.ext
    · change f.base ≫ g.base = f.base ≫ g.base
      rfl
    · change 1 = A.G.map f.base.op 1 * 1
      simp
  w := rfl

lemma quotientMap_map {x y : A.ElementObj} (f : A.ElementHom x y) :
    A.quotientMap.map f = A.quotientOfElementHom f :=
  rfl

/-- The component of the canonical 2-isomorphism between the action and second
projection after passing to `[U/G]^pre`. -/
def quotientActionIsoApp (x : A.ActionObj) :
    (A.actionMap.comp A.quotientMap).obj x ≅
      (A.actionSnd.comp A.quotientMap).obj x := by
  letI := A.action (op x.base)
  change
    ({ base := x.base, point := x.gauge • x.point } : A.QuotientObj) ≅
      ({ base := x.base, point := x.point } : A.QuotientObj)
  refine
    { hom :=
        { base := 𝟙 x.base
          gauge := x.gauge⁻¹
          relation := by
            rw [show A.U.map (𝟙 x.base).op x.point = x.point by
              simpa using congrArg (fun q ↦ q x.point) (A.U.map_id (op x.base))]
            exact (inv_smul_smul x.gauge x.point).symm }
      inv :=
        { base := 𝟙 x.base
          gauge := x.gauge
          relation := by
            rw [show A.U.map (𝟙 x.base).op (x.gauge • x.point) =
                x.gauge • x.point by
              simpa using congrArg (fun q ↦ q (x.gauge • x.point))
                (A.U.map_id (op x.base))] }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply QuotientHom.ext
    · change (𝟙 x.base ≫ 𝟙 x.base) = 𝟙 x.base
      simp
    · change A.G.map (𝟙 x.base).op x.gauge * x.gauge⁻¹ = 1
      simp
  · apply QuotientHom.ext
    · change (𝟙 x.base ≫ 𝟙 x.base) = 𝟙 x.base
      simp
    · change A.G.map (𝟙 x.base).op x.gauge⁻¹ * x.gauge = 1
      simp

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (a), the
2-cell `α`): after mapping to `[U/G]^pre`, the action `σ : G × U → U` and second
projection `p₂ : G × U → U` are canonically 2-isomorphic. -/
def quotientActionIso :
    A.actionMap.comp A.quotientMap ≅ A.actionSnd.comp A.quotientMap :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (A.quotientActionIsoApp) (fun {x y} f ↦ by
      apply QuotientHom.ext
      · change f.base ≫ 𝟙 y.base = 𝟙 x.base ≫ f.base
        simp
      · change A.G.map f.base.op y.gauge⁻¹ * 1 =
          A.G.map (𝟙 x.base).op 1 * x.gauge⁻¹
        rw [_root_.map_inv, f.gauge_relation]
        simp))
    (fun x ↦ by
      apply IsHomLift.of_fac' A.quotientProj (𝟙 x.base)
        (A.quotientActionIsoApp x).hom
        (by
          change ((A.actionMap.comp A.quotientMap).obj x).base = x.base
          rfl)
        (by
          change ((A.actionSnd.comp A.quotientMap).obj x).base = x.base
          rfl)
      simpa [quotientProj, quotientActionIsoApp, BasedFunctor.comp,
        actionMap, actionSnd, quotientMap])

/-- Regard an object of the action quotient as an object of the category of elements. -/
abbrev asElement (x : A.QuotientObj) : A.ElementObj :=
  { base := x.base
    point := x.point }

/-- The point obtained by applying `g` to an object of the prestack associated to `U`. -/
abbrev actedElement (x : A.ElementObj) (g : A.G.obj (op x.base)) : A.ElementObj :=
  { base := x.base
    point := letI := A.action (op x.base); g • x.point }

/-- The object `(g, u)` of the action prestack. -/
abbrev actionAt (x : A.ElementObj) (g : A.G.obj (op x.base)) : A.ActionObj :=
  { base := x.base
    gauge := g
    point := x.point }

@[simp]
lemma actionMap_obj_actionAt (x : A.ElementObj) (g : A.G.obj (op x.base)) :
    A.actionMap.obj (A.actionAt x g) = A.actedElement x g :=
  rfl

@[simp]
lemma actionSnd_obj_actionAt (x : A.ElementObj) (g : A.G.obj (op x.base)) :
    A.actionSnd.obj (A.actionAt x g) = x :=
  rfl

/-- The canonical arrow `1 · u → u` in the prestack associated to `U`. -/
def actionUnitHom (x : A.ElementObj) :
    A.ElementHom (A.actedElement x 1) x := by
  letI := A.action (op x.base)
  refine
    { base := 𝟙 x.base
      relation := ?_ }
  rw [show A.U.map (𝟙 x.base).op x.point = x.point by
    simpa using congrArg (fun q ↦ q x.point) (A.U.map_id (op x.base))]
  exact one_smul _ _ |>.symm

/-- The canonical associativity arrow `(h * g) · u → h · (g · u)` in the prestack
associated to `U`. -/
def actionAssocHom (x : A.ElementObj) (g h : A.G.obj (op x.base)) :
    A.ElementHom (A.actedElement x (h * g))
      (A.actedElement (A.actedElement x g) h) := by
  letI := A.action (op x.base)
  refine
    { base := 𝟙 x.base
      relation := ?_ }
  rw [show A.U.map (𝟙 x.base).op (h • g • x.point) = h • g • x.point by
    simpa using congrArg (fun q ↦ q (h • g • x.point)) (A.U.map_id (op x.base))]
  exact (mul_smul h g x.point).symm

/-- The arrow `g · u → v` in `U` associated to an arrow `(f,g) : u → v` of the action
quotient. -/
abbrev quotientFactorHom {x y : A.QuotientObj} (q : A.QuotientHom x y) :
    A.ElementHom (A.actedElement (A.asElement x) q.gauge) (A.asElement y) where
  base := q.base
  relation := q.relation

/-- The factor arrow of the inverse canonical action arrow is the identity of the
acted element. -/
lemma quotientActionIsoApp_inv_factor (x : A.ActionObj) :
    A.quotientFactorHom (A.quotientActionIsoApp x).inv =
      𝟙 (A.actionMap.obj x) := by
  cases x
  apply ElementHom.ext
  rfl

lemma quotientFactorHom_id (x : A.QuotientObj) :
    A.quotientFactorHom (QuotientHom.id A x) =
      A.actionUnitHom (A.asElement x) := by
  apply ElementHom.ext
  rfl

/-- Restricting an action arrow along an arrow `q : x → y` in the quotient. -/
def actionNaturalityHom {x y : A.QuotientObj} (q : A.QuotientHom x y)
    (h : A.G.obj (op y.base)) :
    A.ActionHom
      (A.actionAt (A.actedElement (A.asElement x) q.gauge) (A.G.map q.base.op h))
      (A.actionAt (A.asElement y) h) where
  base := q.base
  gauge_relation := rfl
  point_relation := q.relation

lemma actionSnd_map_actionNaturalityHom {x y : A.QuotientObj}
    (q : A.QuotientHom x y) (h : A.G.obj (op y.base)) :
    A.actionSnd.map (A.actionNaturalityHom q h) = A.quotientFactorHom q := by
  apply ElementHom.ext
  rfl

/-- The element-category composite appearing in the multiplication coherence agrees
with the factor arrow for the composite quotient morphism. -/
lemma actionAssoc_naturality_factor {x y z : A.QuotientObj}
    (q : A.QuotientHom x y) (r : A.QuotientHom y z) :
    A.actionAssocHom (A.asElement x) q.gauge (A.G.map q.base.op r.gauge) ≫
        A.actionMap.map (A.actionNaturalityHom q r.gauge) ≫
          A.quotientFactorHom r =
      A.quotientFactorHom (QuotientHom.comp A q r) := by
  apply ElementHom.ext
  rw [ElementObj.comp_base, ElementObj.comp_base]
  simp [actionAssocHom, actionMap, actionNaturalityHom, quotientFactorHom,
    QuotientHom.comp]

/-- Converting an element object to a quotient object and back gives the original
element object. -/
lemma asElement_asQuotient (x : A.ElementObj) :
    A.asElement (A.asQuotient x) = x := by
  cases x
  rfl

/-- The canonical isomorphism from the round-trip element object back to the original
one. -/
def elementRoundtripIso (x : A.ElementObj) :
    A.asElement (A.asQuotient x) ≅ x :=
  eqToIso (A.asElement_asQuotient x)

lemma asQuotient_asElement (x : A.QuotientObj) :
    A.asQuotient (A.asElement x) = x := by
  cases x
  rfl

/-- The canonical isomorphism from the round-trip quotient object back to the
original quotient object. -/
def quotientRoundtripIso (x : A.QuotientObj) :
    A.asQuotient (A.asElement x) ≅ x :=
  eqToIso (A.asQuotient_asElement x)

instance quotientRoundtripIso_hom_isHomLift (x : A.QuotientObj) :
    A.quotientProj.IsHomLift (𝟙 x.base) (A.quotientRoundtripIso x).hom := by
  cases x
  exact IsHomLift.id rfl

/-- Every quotient arrow is the composite of the inverse canonical action arrow and
the image of its factor arrow, up to the round-trip identifications of its endpoints. -/
lemma quotientActionIsoApp_inv_comp_factor {x y : A.QuotientObj}
    (q : A.QuotientHom x y) :
    (A.quotientActionIsoApp
          (A.actionAt (A.asElement x) q.gauge)).inv ≫
        A.quotientOfElementHom (A.quotientFactorHom q) =
      (A.quotientRoundtripIso x).hom ≫ q ≫
        (A.quotientRoundtripIso y).inv := by
  cases x
  cases y
  rw [show (A.quotientRoundtripIso _).hom = 𝟙 _ by rfl]
  rw [show (A.quotientRoundtripIso _).inv = 𝟙 _ by rfl]
  rw [Category.id_comp, Category.comp_id]
  apply QuotientHom.ext
  · change (QuotientHom.comp A _ _).base = q.base
    simp [QuotientHom.comp, quotientActionIsoApp]
  · change (QuotientHom.comp A _ _).gauge = q.gauge
    simp [QuotientHom.comp, quotientActionIsoApp, quotientOfElementHom]

instance elementRoundtripIso_inv_isHomLift (x : A.ElementObj) :
    A.elementProj.IsHomLift (𝟙 x.base) (A.elementRoundtripIso x).inv := by
  cases x
  exact A.elementHom_isHomLift (A.elementRoundtripIso _).inv

/-- The unit arrow, the round-trip identifications, and an element arrow compose to the
factor arrow associated to its image in the quotient. -/
lemma actionUnit_roundtrip_factor {x y : A.ElementObj} (f : A.ElementHom x y) :
    A.actionUnitHom (A.asElement (A.asQuotient x)) ≫
        (A.elementRoundtripIso x).hom ≫ f ≫ (A.elementRoundtripIso y).inv =
      A.quotientFactorHom (A.quotientOfElementHom f) := by
  apply ElementHom.ext
  rw [ElementObj.comp_base, ElementObj.comp_base, ElementObj.comp_base]
  simp [actionUnitHom, elementRoundtripIso, quotientOfElementHom]

/-- A coherent 2-isomorphism identifying `φ(g · u)` with `φ(u)`. The fields `unit`
and `mul` are exactly the unit and action-cocycle conditions omitted from the printed
statement of Exercise 3.4.27(b). They are written in the inverse orientation used to
construct arrows out of the quotient. -/
structure CoherentQuotientDatum {Z : BasedCategory C}
    (phi : A.elementPrestack ⥤ᵇ Z) where
  /-- The displayed 2-isomorphism in the book. -/
  tau : A.actionMap.comp phi ≅ A.actionSnd.comp phi
  /-- Unit coherence. -/
  unit (x : A.QuotientObj) :
    tau.inv.toNatTrans.app (A.actionAt (A.asElement x) 1) ≫
        phi.map (A.actionUnitHom (A.asElement x)) =
      𝟙 (phi.obj (A.asElement x))
  /-- Multiplication/cocycle coherence. -/
  mul (x : A.QuotientObj) (g h : A.G.obj (op x.base)) :
    tau.inv.toNatTrans.app (A.actionAt (A.asElement x) g) ≫
        tau.inv.toNatTrans.app (A.actionAt (A.actedElement (A.asElement x) g) h) =
      tau.inv.toNatTrans.app (A.actionAt (A.asElement x) (h * g)) ≫
        phi.map (A.actionAssocHom (A.asElement x) g h)

namespace CoherentQuotientDatum

variable {Z : BasedCategory C} (phi : A.elementPrestack ⥤ᵇ Z)
  (D : A.CoherentQuotientDatum phi)

/-- The arrow assigned by a coherent quotient datum to an arrow of `[U/G]^pre`. -/
def descendMap {x y : A.QuotientObj} (q : A.QuotientHom x y) :
    phi.obj (A.asElement x) ⟶ phi.obj (A.asElement y) :=
  D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge) ≫
    phi.map (A.quotientFactorHom q)

@[simp]
lemma map_id (x : A.QuotientObj) :
    descendMap A phi D (QuotientHom.id A x) = 𝟙 (phi.obj (A.asElement x)) := by
  change D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) 1) ≫
      phi.map (A.quotientFactorHom (QuotientHom.id A x)) =
    𝟙 (phi.obj (A.asElement x))
  rw [A.quotientFactorHom_id]
  exact D.unit x

lemma map_comp {x y z : A.QuotientObj} (q : A.QuotientHom x y)
    (r : A.QuotientHom y z) :
    descendMap A phi D q ≫ descendMap A phi D r =
      descendMap A phi D (QuotientHom.comp A q r) := by
  let h : A.G.obj (op x.base) := A.G.map q.base.op r.gauge
  let m : A.ActionHom
      (A.actionAt (A.actedElement (A.asElement x) q.gauge) h)
      (A.actionAt (A.asElement y) r.gauge) :=
    A.actionNaturalityHom q r.gauge
  have hnat := D.tau.inv.toNatTrans.naturality m
  change phi.map (A.actionSnd.map m) ≫
        D.tau.inv.toNatTrans.app (A.actionAt (A.asElement y) r.gauge) =
      D.tau.inv.toNatTrans.app
          (A.actionAt (A.actedElement (A.asElement x) q.gauge) h) ≫
        phi.map (A.actionMap.map m) at hnat
  have hsnd : A.actionSnd.map m = A.quotientFactorHom q := by
    exact A.actionSnd_map_actionNaturalityHom q r.gauge
  rw [hsnd] at hnat
  change
    (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge) ≫
        phi.map (A.quotientFactorHom q)) ≫
      (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement y) r.gauge) ≫
        phi.map (A.quotientFactorHom r)) =
    D.tau.inv.toNatTrans.app
        (A.actionAt (A.asElement x) (h * q.gauge)) ≫
      phi.map (A.quotientFactorHom (QuotientHom.comp A q r))
  rw [Category.assoc, ← Category.assoc (phi.map (A.quotientFactorHom q)), hnat,
    Category.assoc, ← Category.assoc
      (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge))]
  rw [D.mul x q.gauge h]
  simp only [Category.assoc]
  rw [← phi.toFunctor.map_comp, ← phi.toFunctor.map_comp]
  rw [A.actionAssoc_naturality_factor q r]

/-- The descended arrow lies over the underlying base arrow of the quotient morphism. -/
lemma descendMap_isHomLift {x y : A.QuotientObj} (q : A.QuotientHom x y) :
    IsHomLift Z.p q.base (descendMap A phi D q) := by
  haveI hτ : IsHomLift Z.p (𝟙 x.base)
      (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge)) := by
    have h := D.tau.inv.isHomLift' (A.actionAt (A.asElement x) q.gauge)
    change IsHomLift Z.p (𝟙 x.base)
      (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge)) at h
    exact h
  haveI hfactor : IsHomLift Z.p q.base (phi.map (A.quotientFactorHom q)) :=
    by
      have h := A.elementHom_isHomLift (A.quotientFactorHom q)
      change IsHomLift A.elementPrestack.p q.base (A.quotientFactorHom q) at h
      letI : IsHomLift A.elementPrestack.p q.base (A.quotientFactorHom q) := h
      exact BasedFunctor.preserves_isHomLift phi q.base (A.quotientFactorHom q)
  have hcomp := IsHomLift.comp Z.p (𝟙 x.base) q.base
    (D.tau.inv.toNatTrans.app (A.actionAt (A.asElement x) q.gauge))
    (phi.map (A.quotientFactorHom q))
  simpa [descendMap] using hcomp

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (b), corrected
coherent version): a morphism `φ : U → Z` equipped with a 2-isomorphism between its
pullbacks along the action and projection, satisfying the omitted unit and cocycle
conditions, descends to a morphism `[U/G]^pre → Z`.

This adds the coherence missing from the printed statement; see `COMMENTARY.md`. -/
def descend : A.quotientPrestack ⥤ᵇ Z where
  obj x := phi.obj (A.asElement x)
  map q := descendMap A phi D q
  map_id x := by
    change descendMap A phi D (QuotientHom.id A x) =
      𝟙 (phi.obj (A.asElement x))
    exact map_id A phi D x
  map_comp q r := by
    change descendMap A phi D (QuotientHom.comp A q r) =
      descendMap A phi D q ≫ descendMap A phi D r
    exact (map_comp A phi D q r).symm
  w := by
    refine Functor.ext_of_iso
      (NatIso.ofComponents
        (fun x ↦ eqToIso (phi.w_obj (A.asElement x))) ?_)
      (fun x ↦ phi.w_obj (A.asElement x))
    intro x y q
    haveI hq : IsHomLift Z.p q.base (descendMap A phi D q) :=
      descendMap_isHomLift A phi D q
    have hfac := IsHomLift.fac' Z.p q.base (descendMap A phi D q)
    simp only [Functor.comp_map, hfac]
    rw [show A.quotientPrestack.p.map q = q.base from rfl]
    simp

lemma descend_map_quotientActionIsoApp_inv (x : A.ActionObj) :
    (descend A phi D).map (A.quotientActionIsoApp x).inv =
      D.tau.inv.toNatTrans.app x := by
  cases x
  change D.tau.inv.toNatTrans.app _ ≫
      phi.map (A.quotientFactorHom (A.quotientActionIsoApp _).inv) =
    D.tau.inv.toNatTrans.app _
  rw [A.quotientActionIsoApp_inv_factor]
  rw [phi.toFunctor.map_id]
  exact Category.comp_id _

lemma descend_map_quotientActionIsoApp_hom (x : A.ActionObj) :
    (descend A phi D).map (A.quotientActionIsoApp x).hom =
      D.tau.hom.toNatTrans.app x := by
  apply (cancel_epi (D.tau.inv.toNatTrans.app x)).mp
  calc
    D.tau.inv.toNatTrans.app x ≫
          (descend A phi D).map (A.quotientActionIsoApp x).hom =
        (descend A phi D).map (A.quotientActionIsoApp x).inv ≫
          (descend A phi D).map (A.quotientActionIsoApp x).hom := by
      rw [descend_map_quotientActionIsoApp_inv A phi D x]
    _ = (descend A phi D).map
          ((A.quotientActionIsoApp x).inv ≫
            (A.quotientActionIsoApp x).hom) := by
      rw [(descend A phi D).toFunctor.map_comp]
    _ = 𝟙 ((descend A phi D).obj
          ((A.actionSnd.comp A.quotientMap).obj x)) := by
      rw [Iso.inv_hom_id, (descend A phi D).toFunctor.map_id]
    _ = D.tau.inv.toNatTrans.app x ≫ D.tau.hom.toNatTrans.app x := by
      exact (((BasedNatTrans.forgetful _ _).mapIso D.tau).app x).inv_hom_id.symm

lemma descendIso_naturality {x y : A.ElementObj} (f : A.ElementHom x y) :
    phi.map f ≫ phi.map (A.elementRoundtripIso y).inv =
      phi.map (A.elementRoundtripIso x).inv ≫
        (D.tau.inv.toNatTrans.app
            (A.actionAt (A.asElement (A.asQuotient x)) 1) ≫
          phi.map (A.quotientFactorHom (A.quotientOfElementHom f))) := by
  rw [← A.actionUnit_roundtrip_factor f]
  simp only [phi.toFunctor.map_comp, Category.assoc]
  slice_rhs 2 3 => exact D.unit (A.asQuotient x)
  slice_rhs 1 2 => exact Category.comp_id _
  slice_rhs 1 2 =>
    rw [← phi.toFunctor.map_comp, Iso.inv_hom_id, phi.toFunctor.map_id]
  simp

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (b), corrected
coherent version, factorization): the original morphism `φ : U → Z` is canonically
2-isomorphic to the quotient map followed by its descent. -/
def descendIso : phi ≅ A.quotientMap.comp (descend A phi D) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ by
        change A.ElementObj at x
        exact phi.toFunctor.mapIso (A.elementRoundtripIso x) |>.symm)
      (fun {x y} f ↦ by
        change A.ElementObj at x y
        change A.ElementHom x y at f
        exact descendIso_naturality A phi D f))
    (fun x ↦ by
      change A.ElementObj at x
      have hsource : IsHomLift A.elementPrestack.p (𝟙 x.base)
          (A.elementRoundtripIso x).inv := by
        change IsHomLift A.elementProj (𝟙 x.base) (A.elementRoundtripIso x).inv
        infer_instance
      letI : IsHomLift A.elementPrestack.p (𝟙 x.base)
          (A.elementRoundtripIso x).inv := hsource
      exact BasedFunctor.preserves_isHomLift phi (𝟙 x.base)
        (A.elementRoundtripIso x).inv)

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (b), corrected
coherent version, compatibility): the canonical factorization identifies the supplied
action 2-cell with the image of the canonical action 2-cell of `[U/G]^pre`. -/
lemma descendIso_compatibility (x : A.ActionObj) :
    (descendIso A phi D).hom.toNatTrans.app (A.actionMap.obj x) ≫
        (descend A phi D).map (A.quotientActionIsoApp x).hom =
      D.tau.hom.toNatTrans.app x ≫
        (descendIso A phi D).hom.toNatTrans.app (A.actionSnd.obj x) := by
  rw [descend_map_quotientActionIsoApp_hom A phi D]
  cases x
  rw [show (descendIso A phi D).hom.toNatTrans.app (A.actionMap.obj _) =
      phi.map (𝟙 _) by rfl]
  rw [show (descendIso A phi D).hom.toNatTrans.app (A.actionSnd.obj _) =
      phi.map (𝟙 _) by rfl]
  rw [phi.toFunctor.map_id, phi.toFunctor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- A factorization through `[U/G]^pre` compatible with a coherent quotient datum.
This is the comparison object whose uniqueness is asserted in the corrected form of
Exercise 3.4.27(b). -/
structure CoherentFactorization where
  /-- The morphism out of the quotient prestack. -/
  chi : A.quotientPrestack ⥤ᵇ Z
  /-- The factorization 2-isomorphism. -/
  beta : phi ≅ A.quotientMap.comp chi
  /-- Compatibility with the action 2-cell. -/
  compatibility (x : A.ActionObj) :
    beta.hom.toNatTrans.app (A.actionMap.obj x) ≫
        chi.map (A.quotientActionIsoApp x).hom =
      D.tau.hom.toNatTrans.app x ≫
        beta.hom.toNatTrans.app (A.actionSnd.obj x)

/-- The descended morphism and its factorization form the canonical coherent
factorization. -/
def canonicalFactorization : CoherentFactorization A phi D where
  chi := descend A phi D
  beta := descendIso A phi D
  compatibility := descendIso_compatibility A phi D

namespace CoherentFactorization

variable (Q : CoherentFactorization A phi D)

/-- The compatibility square in the inverse orientation used by descent. -/
lemma compatibility_inv (x : A.ActionObj) :
    D.tau.inv.toNatTrans.app x ≫
        Q.beta.hom.toNatTrans.app (A.actionMap.obj x) =
      Q.beta.hom.toNatTrans.app (A.actionSnd.obj x) ≫
        Q.chi.map (A.quotientActionIsoApp x).inv := by
  apply (cancel_mono (Q.chi.map (A.quotientActionIsoApp x).hom)).mp
  calc
    (D.tau.inv.toNatTrans.app x ≫
          Q.beta.hom.toNatTrans.app (A.actionMap.obj x)) ≫
        Q.chi.map (A.quotientActionIsoApp x).hom =
      D.tau.inv.toNatTrans.app x ≫
        (Q.beta.hom.toNatTrans.app (A.actionMap.obj x) ≫
          Q.chi.map (A.quotientActionIsoApp x).hom) :=
        Category.assoc _ _ _
    _ = D.tau.inv.toNatTrans.app x ≫
        (D.tau.hom.toNatTrans.app x ≫
          Q.beta.hom.toNatTrans.app (A.actionSnd.obj x)) := by
      rw [Q.compatibility x]
    _ = Q.beta.hom.toNatTrans.app (A.actionSnd.obj x) := by
      exact (((BasedNatTrans.forgetful _ _).mapIso D.tau).app x).inv_hom_id_assoc _
    _ = Q.beta.hom.toNatTrans.app (A.actionSnd.obj x) ≫
        Q.chi.map ((A.quotientActionIsoApp x).inv ≫
          (A.quotientActionIsoApp x).hom) := by
      rw [Iso.inv_hom_id, Q.chi.toFunctor.map_id]
      exact (Category.comp_id _).symm
    _ = (Q.beta.hom.toNatTrans.app (A.actionSnd.obj x) ≫
          Q.chi.map (A.quotientActionIsoApp x).inv) ≫
        Q.chi.map (A.quotientActionIsoApp x).hom := by
      rw [Q.chi.toFunctor.map_comp, Category.assoc]

/-- The canonical component of the comparison from the descended factorization to
any coherent factorization. -/
def comparisonApp (x : A.QuotientObj) :
    (descend A phi D).obj x ≅ Q.chi.obj x :=
  (((BasedNatTrans.forgetful _ _).mapIso Q.beta).app (A.asElement x)) ≪≫
    Q.chi.toFunctor.mapIso (A.quotientRoundtripIso x)

lemma comparison_naturality {x y : A.QuotientObj} (q : A.QuotientHom x y) :
    (descend A phi D).map q ≫ (comparisonApp A phi D Q y).hom =
      (comparisonApp A phi D Q x).hom ≫ Q.chi.map q := by
  change
    (D.tau.inv.toNatTrans.app
          (A.actionAt (A.asElement x) q.gauge) ≫
        phi.map (A.quotientFactorHom q)) ≫
      (Q.beta.hom.toNatTrans.app (A.asElement y) ≫
        Q.chi.map (A.quotientRoundtripIso y).hom) =
    (Q.beta.hom.toNatTrans.app (A.asElement x) ≫
        Q.chi.map (A.quotientRoundtripIso x).hom) ≫ Q.chi.map q
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    exact Q.beta.hom.toNatTrans.naturality (A.quotientFactorHom q)
  slice_lhs 1 2 =>
    exact compatibility_inv A phi D Q (A.actionAt (A.asElement x) q.gauge)
  rw [show (A.quotientMap.comp Q.chi).map (A.quotientFactorHom q) =
      Q.chi.map (A.quotientOfElementHom (A.quotientFactorHom q)) from rfl]
  slice_lhs 2 4 =>
    rw [← Q.chi.toFunctor.map_comp, ← Q.chi.toFunctor.map_comp,
      ← Category.assoc,
      A.quotientActionIsoApp_inv_comp_factor q,
      ← Category.assoc (A.quotientRoundtripIso x).hom q
        (A.quotientRoundtripIso y).inv,
      Category.assoc ((A.quotientRoundtripIso x).hom ≫ q)
        (A.quotientRoundtripIso y).inv
        (A.quotientRoundtripIso y).hom,
      Iso.inv_hom_id, Category.comp_id]
  slice_rhs 2 3 =>
    rw [← Q.chi.toFunctor.map_comp]
  simpa only [A.actionSnd_obj_actionAt]

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (b), corrected
coherent version, uniqueness): every coherent factorization is canonically
2-isomorphic to the descended factorization. -/
def comparison : descend A phi D ≅ Q.chi :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ by
        change A.QuotientObj at x
        exact comparisonApp A phi D Q x)
      (fun {x y} q ↦ by
        change A.QuotientObj at x y
        change A.QuotientHom x y at q
        exact comparison_naturality A phi D Q q))
    (fun x ↦ by
      change A.QuotientObj at x
      haveI hbeta : IsHomLift Z.p (𝟙 x.base)
          (Q.beta.hom.toNatTrans.app (A.asElement x)) := by
        have h := Q.beta.hom.isHomLift' (A.asElement x)
        change IsHomLift Z.p (𝟙 x.base)
          (Q.beta.hom.toNatTrans.app (A.asElement x)) at h
        exact h
      haveI hroundtripSource : IsHomLift A.quotientPrestack.p (𝟙 x.base)
          (A.quotientRoundtripIso x).hom := by
        change IsHomLift A.quotientProj (𝟙 x.base)
          (A.quotientRoundtripIso x).hom
        infer_instance
      haveI hroundtrip : IsHomLift Z.p (𝟙 x.base)
          (Q.chi.map (A.quotientRoundtripIso x).hom) :=
        BasedFunctor.preserves_isHomLift Q.chi (𝟙 x.base)
          (A.quotientRoundtripIso x).hom
      have hcomp := IsHomLift.comp Z.p (𝟙 x.base) (𝟙 x.base)
        (Q.beta.hom.toNatTrans.app (A.asElement x))
        (Q.chi.map (A.quotientRoundtripIso x).hom)
      change IsHomLift Z.p (𝟙 x.base)
        (Q.beta.hom.toNatTrans.app (A.asElement x) ≫
          Q.chi.map (A.quotientRoundtripIso x).hom)
      simpa using hcomp)

/-- The canonical comparison respects the two factorization 2-isomorphisms. -/
lemma comparison_factorization (x : A.ElementObj) :
    (descendIso A phi D).hom.toNatTrans.app x ≫
        (comparison A phi D Q).hom.toNatTrans.app (A.asQuotient x) =
      Q.beta.hom.toNatTrans.app x := by
  cases x
  change phi.map (𝟙 _) ≫
      (Q.beta.hom.toNatTrans.app _ ≫ Q.chi.map (𝟙 _)) =
    Q.beta.hom.toNatTrans.app _
  rw [phi.toFunctor.map_id, Q.chi.toFunctor.map_id, Category.id_comp]
  exact Category.comp_id _

/-- **Exercise 3.4.27** (`exer:prestack-quotient-categorical`) (part (b), corrected
coherent version, unique 2-isomorphism): the canonical comparison is the only
2-isomorphism compatible with the factorization 2-cells. -/
lemma comparison_unique (eta : descend A phi D ≅ Q.chi)
    (h : ∀ x : A.ElementObj,
      (descendIso A phi D).hom.toNatTrans.app x ≫
          eta.hom.toNatTrans.app (A.asQuotient x) =
        Q.beta.hom.toNatTrans.app x) :
    eta = comparison A phi D Q := by
  apply Iso.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change A.QuotientObj at x
  have heta := h (A.asElement x)
  have hcomparison := comparison_factorization A phi D Q (A.asElement x)
  cases x
  have hc := (cancel_epi
    ((descendIso A phi D).hom.toNatTrans.app (A.asElement _))).mp
      (heta.trans hcomparison.symm)
  simpa only [A.asQuotient_asElement] using hc

end CoherentFactorization

end CoherentQuotientDatum

end CategoryTheory.PresheafAction

end ExerPrestackQuotientCategorical
