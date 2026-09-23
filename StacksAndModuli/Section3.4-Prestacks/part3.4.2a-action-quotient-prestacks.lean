module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import StacksAndModuli.API.ClassifyingPrestack
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Action quotient prestacks

This module formalizes Definition 3.4.15
(`def:quotient-prestack-and-stack`) in a category-independent form. A group-valued
presheaf `G` acts naturally on a set-valued presheaf `U`; the resulting category over
the base has objects `(T, u)` and arrows `(f, g) : (T', u') → (T, u)` satisfying
`f* u = g · u'`, exactly as in the book. For schemes it also constructs the
principal-bundle quotient stack and proves that it is a prestack.

Main declarations:
- `CategoryTheory.PresheafAction.quotientPrestack`: the resulting prestack over the
  base category.
- `AlgebraicGeometry.Scheme.quotientStack`: the principal-bundle quotient stack.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefQuotientPrestackAndStack

open CategoryTheory Functor

universe w v u

namespace CategoryTheory

open Opposite

variable (C : Type u) [Category.{v} C]

/-- The categorical data underlying an action used to form an action quotient
prestack: a group-valued presheaf `G`, a set-valued presheaf `U`, pointwise actions,
and compatibility of restriction with the actions. -/
structure PresheafAction where
  /-- The acting group-valued presheaf. -/
  G : Cᵒᵖ ⥤ GrpCat.{w}
  /-- The acted-on set-valued presheaf. -/
  U : Cᵒᵖ ⥤ Type w
  /-- The action on sections over each object. -/
  action (T : Cᵒᵖ) : MulAction (G.obj T) (U.obj T)
  /-- Restriction maps are equivariant. -/
  map_smul {T T' : Cᵒᵖ} (f : T ⟶ T') (g : G.obj T) (x : U.obj T) :
    U.map f (letI := action T; g • x) =
      (letI := action T'; G.map f g • U.map f x)

namespace PresheafAction

variable {C} (A : PresheafAction.{w} C)

/-- Background structure for Definition 3.4.15 (quotient-prestack
objects): a pair `(T, u)` with `T` in the base and `u ∈ U(T)`. -/
structure QuotientObj where
  /-- The object of the base category. -/
  base : C
  /-- The section of `U` over the base object. -/
  point : A.U.obj (op base)

/-- Background structure for Definition 3.4.15 (quotient-prestack
morphisms): an arrow `(T', u') → (T, u)` is an arrow `f : T' → T` and an element
`g ∈ G(T')` such that `f* u = g · u'`. -/
@[ext]
structure QuotientHom (x y : A.QuotientObj) where
  /-- The underlying arrow in the base. -/
  base : x.base ⟶ y.base
  /-- The gauge element over the source. -/
  gauge : A.G.obj (op x.base)
  /-- The defining action-quotient relation. -/
  relation : A.U.map base.op y.point =
    (letI := A.action (op x.base); gauge • x.point)

/-- The identity arrow in an action quotient. -/
@[simps]
def QuotientHom.id (x : A.QuotientObj) : A.QuotientHom x x where
  base := 𝟙 x.base
  gauge := 1
  relation := by
    letI := A.action (op x.base)
    simpa using congrArg (fun q ↦ q x.point) (A.U.map_id (op x.base))

/-- Composition of arrows in an action quotient. -/
@[simps]
def QuotientHom.comp {x y z : A.QuotientObj} (f : A.QuotientHom x y)
    (g : A.QuotientHom y z) : A.QuotientHom x z where
  base := f.base ≫ g.base
  gauge := A.G.map f.base.op g.gauge * f.gauge
  relation := by
    letI := A.action (op x.base)
    letI := A.action (op y.base)
    letI := A.action (op z.base)
    calc
      A.U.map (f.base ≫ g.base).op z.point =
          A.U.map f.base.op (A.U.map g.base.op z.point) := by
        exact congrArg (fun q ↦ q z.point) (A.U.map_comp g.base.op f.base.op)
      _ = A.U.map f.base.op (g.gauge • y.point) := by rw [g.relation]
      _ = A.G.map f.base.op g.gauge • A.U.map f.base.op y.point :=
        A.map_smul f.base.op g.gauge y.point
      _ = (A.G.map f.base.op g.gauge * f.gauge) • x.point := by
        rw [f.relation, mul_smul]

instance : Category A.QuotientObj where
  Hom := A.QuotientHom
  id := QuotientHom.id A
  comp := QuotientHom.comp A
  id_comp f := by
    apply QuotientHom.ext
    · simp
    · simp [QuotientHom.comp, QuotientHom.id]
  comp_id f := by
    apply QuotientHom.ext
    · simp
    · simp [QuotientHom.comp, QuotientHom.id]
  assoc f g h := by
    apply QuotientHom.ext
    · simp
    · simp [QuotientHom.comp, mul_assoc, Functor.map_comp]

/-- The projection from the action quotient to its base category. -/
@[simps]
def quotientProj : A.QuotientObj ⥤ C where
  obj x := x.base
  map f := f.base

/-- **Definition 3.4.15** (`def:quotient-prestack-and-stack`) (the quotient-prestack
half): the action quotient `[U/G]^pre`, as a based category over `C`. -/
abbrev quotientPrestack : BasedCategory C :=
  BasedCategory.ofFunctor A.quotientProj

/-- The action quotient `[U/G]^pre` is a prestack. -/
instance quotientProj_isFiberedInGroupoids : A.quotientProj.IsFiberedInGroupoids where
  exists_isHomLift {y R} f := by
    letI := A.action (op R)
    let x : A.QuotientObj :=
      { base := R
        point := A.U.map f.op y.point }
    let phi : A.QuotientHom x y :=
      { base := f
        gauge := 1
        relation := by
          simp only [one_smul]
          change A.U.map f.op y.point = A.U.map f.op y.point
          rfl }
    refine ⟨x, phi, ?_⟩
    apply IsHomLift.of_fac' A.quotientProj f phi rfl rfl
    simp [quotientProj, phi]
  isStronglyCartesian {x y} phi := by
    change A.QuotientHom x y at phi
    constructor
    intro z f psi hpsi
    letI : A.quotientProj.IsHomLift (f ≫ A.quotientProj.map phi) psi := hpsi
    change A.QuotientHom z y at psi
    change z.base ⟶ x.base at f
    have hbase : f ≫ phi.base = psi.base := by
      have hbase' := IsHomLift.eq_of_isHomLift A.quotientProj
        (f ≫ A.quotientProj.map phi) psi
      change f ≫ phi.base = psi.base at hbase'
      exact hbase'
    letI := A.action (op z.base)
    letI := A.action (op x.base)
    letI := A.action (op y.base)
    let pulled : A.G.obj (op z.base) := A.G.map f.op phi.gauge
    let gauge : A.G.obj (op z.base) := pulled⁻¹ * psi.gauge
    have hpoint : A.U.map f.op x.point = gauge • z.point := by
      have hrel : pulled • A.U.map f.op x.point = psi.gauge • z.point := by
        calc
          pulled • A.U.map f.op x.point =
              A.U.map f.op (phi.gauge • x.point) := by
            exact (A.map_smul f.op phi.gauge x.point).symm
          _ = A.U.map f.op (A.U.map phi.base.op y.point) := by
            rw [phi.relation]
          _ = A.U.map (phi.base.op ≫ f.op) y.point := by
            exact (congrArg (fun q ↦ q y.point)
              (A.U.map_comp phi.base.op f.op)).symm
          _ = A.U.map psi.base.op y.point := by rw [show phi.base.op ≫ f.op =
              psi.base.op by rw [← op_comp, hbase]]
          _ = psi.gauge • z.point := psi.relation
      calc
        A.U.map f.op x.point =
            pulled⁻¹ • (pulled • A.U.map f.op x.point) :=
          (inv_smul_smul pulled (A.U.map f.op x.point)).symm
        _ = pulled⁻¹ • (psi.gauge • z.point) := by rw [hrel]
        _ = gauge • z.point := by simp only [gauge, mul_smul]
    let chi : A.QuotientHom z x :=
      { base := f
        gauge := gauge
        relation := hpoint }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_fac' A.quotientProj f chi rfl rfl
      simp [quotientProj, chi]
    · apply QuotientHom.ext
      · exact hbase
      · change A.G.map f.op phi.gauge * gauge = psi.gauge
        dsimp [gauge, pulled]
        simp
    · intro chi' hchi'
      change A.QuotientHom z x at chi'
      have hchiBase : f = chi'.base := by
        letI : A.quotientProj.IsHomLift f chi' := hchi'.1
        exact IsHomLift.eq_of_isHomLift A.quotientProj f chi'
      cases hchiBase
      apply QuotientHom.ext
      · rfl
      · have hgauge : A.G.map chi'.base.op phi.gauge * chi'.gauge = psi.gauge := by
          have hgauge' := congrArg QuotientHom.gauge hchi'.2
          change A.G.map chi'.base.op phi.gauge * chi'.gauge = psi.gauge at hgauge'
          exact hgauge'
        change chi'.gauge = gauge
        dsimp [gauge, pulled]
        rw [← hgauge, ← mul_assoc]
        simp

end PresheafAction

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.ModObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [Smooth G.hom]
  [IsAffineHom G.hom]
variable (U : Over S) [ModObj G U]

/-- **Definition 3.4.15** (`def:quotient-prestack-and-stack`) (quotient-stack
half): `[U/G]` is the category over `Scheme/S` whose objects over `T` are principal
`G`-bundles `P → T` equipped with a `G`-equivariant map `P → U`; morphisms are
commutative equivariant cartesian squares. -/
noncomputable abbrev quotientStack : BasedCategory (Over S) :=
  actionQuotientPrestack G U

/-- Supporting instance for Definition 3.4.15 (prestack assertion):
base change of principal bundles and equivariant maps makes `[U/G]` a prestack. -/
noncomputable instance quotientStack_isFiberedInGroupoids :
    (quotientStack G U).p.IsFiberedInGroupoids :=
  inferInstance

end AlgebraicGeometry.Scheme

end DefQuotientPrestackAndStack
