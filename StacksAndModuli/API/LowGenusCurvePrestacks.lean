module

public import StacksAndModuli.API.BrauerSeveri
public import StacksAndModuli.API.EllipticGroupFamily

/-!
# Low-genus curve prestack models

This file gives the two model-level prestacks used in Exercise 3.5.15 of
*Stacks and Moduli* without asserting the geometric comparison theorems that
are still missing from the library.

For genus zero, the model is the prestack of Brauer--Severi curves: families
which become relative projective one-space after a surjective étale base
change.  For pointed genus one, the model is the prestack of smooth proper
geometrically connected commutative group schemes of relative dimension one,
with the unit as marked section.

The names deliberately include `Form` and `GroupModel`.  Identifying these
models with the book's fiberwise definitions of `M₀` and `M₁,₁` requires,
respectively, the genus-zero/Brauer--Severi comparison and the theorem that a
pointed genus-one family carries a unique compatible group law.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The Brauer--Severi model for families of genus-zero curves: étale forms of
relative projective one-space. -/
abbrev genusZeroFormProperty : MorphismProperty Scheme.{u} :=
  brauerSeveriProperty 1

lemma mem_genusZeroFormProperty_iff {P S : Scheme.{u}} (f : P ⟶ S) :
    genusZeroFormProperty f ↔ IsBrauerSeveri 1 f :=
  Iff.rfl

/-- The Brauer--Severi prestack model for `M₀`.  The comparison with the
fiberwise genus-zero definition is not part of this abbreviation. -/
abbrev genusZeroFormPrestack : BasedCategory Scheme.{u} :=
  brauerSeveriPrestack 1

instance genusZeroFormPrestack_isFiberedInGroupoids :
    genusZeroFormPrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- The commutative-group-scheme prestack model for `M₁,₁`.  Objects are
`EllipticGroupFamily`s and morphisms are cartesian maps of their underlying
pointed smooth curves. -/
noncomputable abbrev pointedEllipticGroupModelPrestack :
    BasedCategory Scheme.{u} :=
  ellipticGroupPrestack

instance pointedEllipticGroupModelPrestack_isFiberedInGroupoids :
    pointedEllipticGroupModelPrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- Forget the auxiliary commutative group operations and retain the pointed
smooth proper family. -/
noncomputable abbrev pointedEllipticGroupModelForget :
    BasedFunctor pointedEllipticGroupModelPrestack.{u}
      (CategoryTheory.pointedCartesianProperty smoothCurveProperty.{u}) :=
  ellipticGroupPrestackForget

/-- The group-model forgetful functor is fully faithful.  After restricting
the target to fiberwise genus-one objects, the missing comparison with the
book's `M₁,₁` is therefore an object-level essential-surjectivity theorem. -/
noncomputable def pointedEllipticGroupModelForgetFullyFaithful :
    pointedEllipticGroupModelForget.{u}.toFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.Scheme
