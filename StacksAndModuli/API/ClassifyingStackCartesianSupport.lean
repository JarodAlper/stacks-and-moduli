module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5a-fiber-product-quotient-stacks»

/-!
# Support for cartesian diagrams of classifying prestacks

This file supplies the no-gap part of the comparison between classifying prestacks
and homogeneous-space quotient prestacks.  An internal homomorphism `H ⟶ G`
induces the right action `h • g = g * φ(h)⁻¹`, hence the principal-bundle quotient
prestack `[G/H]` and its quotient-presentation square.  On every scheme of
generalized points, the abstract groupoid fiber calculation identifies
`BH(T) ×_BG(T) pt` with the corresponding right action groupoid.

Constructing the morphism `BH ⟶ BG` on arbitrary principal bundles still requires
the representable contracted product `(G × P)/H`; that effective descent input is
deliberately not postulated here.

Main declarations:

* `CategoryTheory.ModObj.rightCoset`: the internal right action attached to a
  homomorphism of group objects;
* `AlgebraicGeometry.Scheme.ClassifyingStackCartesian.quotientPrestack`: the
  principal-bundle quotient prestack `[G/H]`;
* `AlgebraicGeometry.Scheme.ClassifyingStackCartesian.pointFamily`: the trivial
  principal-bundle point `S ⟶ BG`;
* `AlgebraicGeometry.Scheme.ClassifyingStackCartesian.pointFiberEquivalence`: the
  classifying-groupoid fiber calculation on every scheme of generalized points.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {H G : C} [GrpObj H] [GrpObj G]

/-- The right-coset action associated to a homomorphism `φ : H ⟶ G` of group
objects.  It is obtained by restricting the regular `G`-action along `φ` and
transporting that action through inversion on `G`; on generalized points it is
`h • g = g * φ(h)⁻¹`. -/
@[instance_reducible]
noncomputable def ModObj.rightCoset (phi : H ⟶ G) [IsMonHom phi] :
    ModObj H G := by
  letI : ModObj G G := ModObj.regular G
  letI : ModObj H G := Mod.scalarRestriction phi G
  letI : IsMonHom (Iso.refl H).hom := by
    change IsMonHom (𝟙 H)
    infer_instance
  exact ModObj.ofIso (Iso.refl H) (asIso ι[G])

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory CategoryTheory.BasedCategory
open scoped CategoryTheory.ModObj

namespace ClassifyingStackCartesian

variable {S : Scheme.{u}} {H G T : Over S} [GrpObj H] [GrpObj G]
  (phi : H ⟶ G) [IsMonHom phi]

/-- The homomorphism on groups of generalized points induced by an internal
homomorphism of group schemes. -/
noncomputable abbrev pointHom (T : Over S) : (T ⟶ H) →* (T ⟶ G) :=
  IsMonHom.monoidHom phi T

/-- The principal-bundle quotient prestack `[G/H]` for the right-coset action
attached to `φ : H ⟶ G`. -/
noncomputable abbrev quotientPrestack : BasedCategory (Over S) :=
  letI : ModObj H G := ModObj.rightCoset phi
  actionQuotientPrestack H G

/-- The right-coset quotient `[G/H]` is a prestack. -/
noncomputable instance quotientPrestack_isFiberedInGroupoids :
    (quotientPrestack phi).p.IsFiberedInGroupoids := by
  dsimp only [quotientPrestack]
  infer_instance

/-- The point `S ⟶ BG`, represented by the family of trivial principal
`G`-bundles. -/
noncomputable def pointFamily [Smooth G.hom] [IsAffineHom G.hom] :
    overBased (𝟙_ (Over S)) ⥤ᵇ classifyingPrestack G := by
  letI : ModObj G (𝟙_ (Over S)) := ModObj.trivialAction G _
  exact (QuotientFiberProduct.presentationFamily
    (G := G) (U := 𝟙_ (Over S))).comp actionQuotientPrestack.forget

/-- The quotient presentation `G ⟶ [G/H]` for the right-coset action. -/
noncomputable def quotientPresentation [Smooth H.hom] [IsAffineHom H.hom] :
    overBased G ⥤ᵇ quotientPrestack phi := by
  letI : ModObj H G := ModObj.rightCoset phi
  exact QuotientFiberProduct.presentationFamily (G := H) (U := G)

/-- The action graph of the right-coset action is the self-pullback of the
quotient presentation `G ⟶ [G/H]`. -/
theorem quotientPresentation_isCartesian [Smooth H.hom] [IsAffineHom H.hom] :
    letI : ModObj H G := ModObj.rightCoset phi
    IsCartesianSquare
      (QuotientFiberProduct.overMap
        (quotientPresentationObject H G).carrier.bundle.p)
      (QuotientFiberProduct.overMap (quotientPresentationObject H G).map)
      (QuotientFiberProduct.squareIso (quotientPresentationObject H G)) := by
  let haction : ModObj H G := ModObj.rightCoset phi
  exact @QuotientFiberProduct.isCartesianSquare_quotientPresentation
    S H G _ haction _ _

/-- The internal right-coset action induces the formula
`h • g = g * φ(h)⁻¹` on generalized points. -/
lemma point_smul (h : T ⟶ H) (g : T ⟶ G) :
    letI : ModObj H G := ModObj.rightCoset phi
    h • g = g * (h ≫ phi)⁻¹ := by
  change lift h g ≫
    (((Iso.refl H).inv ⊗ₘ (asIso ι[G]).inv) ≫
      ((phi ▷ G) ≫ μ[G]) ≫ (asIso ι[G]).hom) = _
  simp only [Iso.refl_inv, id_tensorHom, asIso_inv, asIso_hom,
    GrpObj.inv_inv, lift_whiskerLeft_assoc]
  slice_lhs 1 2 => rw [lift_whiskerRight]
  rw [← Hom.mul_def]
  rw [← Hom.inv_def, ← Hom.inv_def]
  rw [_root_.mul_inv_rev, inv_inv]

/-- On every generalized-point groupoid, the fiber of the homomorphism
`BH(T) ⟶ BG(T)` over the point is equivalent to the right action groupoid
`[G(T)/H(T)]`. -/
noncomputable def pointFiberEquivalence (T : Over S) :
    ClassifyingGroupoidFiberProduct.Obj (pointHom phi T) ≌
      ActionGroupoid (T ⟶ H) (HomRightAction (pointHom phi T)) :=
  ClassifyingGroupoidFiberProduct.equivalence (pointHom phi T)

end ClassifyingStackCartesian

end AlgebraicGeometry.Scheme
