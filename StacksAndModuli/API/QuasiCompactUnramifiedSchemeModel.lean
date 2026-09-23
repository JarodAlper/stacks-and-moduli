module

public import StacksAndModuli.API.FiberProductIdentity
public import StacksAndModuli.API.RepresentableWithSchemeModel
public import StacksAndModuli.API.UnramifiedQuasiFinite
public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»

/-!
# Quasi-compact unramified morphisms with a scheme model

This file records two reductions for a quasi-compact morphism of prestacks to an affine
scheme. A scheme equivalent to its source is quasi-compact. If the morphism is also
representable by locally finite-type, formally unramified scheme morphisms and the base
is a field, the structural morphism of that scheme model is finite and formally
unramified.

These statements do not produce a scheme model from an algebraic-space model. They
isolate the scheme-representability theorem needed before ordinary scheme finiteness can
be applied.

## Main results

* `BasedFunctor.QuasiCompact.compactSpace_of_scheme_representation_over_affine`
* `BasedFunctor.RepresentableWith.isFinite_of_quasiCompact_scheme_representation_over_field`
-/

@[expose] public section

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₁ u₁ u

namespace AlgebraicGeometry.BasedFunctor

/-- A scheme equivalent to the source of a quasi-compact morphism to an affine scheme
is quasi-compact. -/
theorem QuasiCompact.compactSpace_of_scheme_representation_over_affine
    {A : CommRingCat.{u}}
    {Xcat : BasedCategory.{v₁, u₁} Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids]
    {F : Xcat ⥤ᵇ overBased (Spec A)}
    (hF : QuasiCompact F)
    (U : Scheme.{u}) (E : overBased U ⥤ᵇ Xcat)
    (hE : E.toFunctor.IsEquivalence) :
    CompactSpace U := by
  have hfiber : BasedCategory.IsQuasiCompact
      (fiberProduct F (BasedFunctor.id (overBased (Spec A)))) :=
    hF A (BasedFunctor.id _)
  have hX : BasedCategory.IsQuasiCompact Xcat :=
    isQuasiCompact_of_equivalence
      (fiberProductFst F (BasedFunctor.id (overBased (Spec A))))
      (isEquivalence_fiberProductFst_id F) hfiber
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  have hJ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  have hU : BasedCategory.IsQuasiCompact (overBased U) :=
    isQuasiCompact_of_equivalence J hJ hX
  let _ : CompactSpace (BasedCategory.pointSpace (overBased U)) := hU
  obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace U
  exact e.compactSpace

/-- A locally finite-type, formally unramified and quasi-compact morphism to a field is
finite on every scheme model of its source. The conclusion also retains formal
unramifiedness for later use. -/
theorem RepresentableWith.isFinite_of_quasiCompact_scheme_representation_over_field
    {K : Type u} [Field K]
    {Xcat : BasedCategory.{v₁, u₁} Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids]
    {F : Xcat ⥤ᵇ overBased (Spec (CommRingCat.of K))}
    (hF : RepresentableWith
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType ⊓
        @_root_.AlgebraicGeometry.FormallyUnramified :
        MorphismProperty Scheme.{u}) F)
    (hqc : QuasiCompact F)
    (G : Scheme.{u}) (E : overBased G ⥤ᵇ Xcat)
    (hE : E.toFunctor.IsEquivalence) :
    _root_.AlgebraicGeometry.IsFinite (E.comp F).overHom ∧
      _root_.AlgebraicGeometry.FormallyUnramified (E.comp F).overHom := by
  let I := fiberProductFstIdInv F
  have hI : I.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductFstIdInv F
  have hEI : (E.comp I).toFunctor.IsEquivalence := by
    change (E.toFunctor ⋙ I.toFunctor).IsEquivalence
    exact Functor.isEquivalence_trans E.toFunctor I.toFunctor
  have hP :
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType ⊓
        @_root_.AlgebraicGeometry.FormallyUnramified :
        MorphismProperty Scheme.{u})
        ((E.comp I).comp
          (CategoryTheory.BasedCategory.fiberProductSnd F (BasedFunctor.id
            (overBased (Spec (CommRingCat.of K)))))).overHom :=
    hF.property_of_scheme_representation
      (Spec (CommRingCat.of K)) (BasedFunctor.id _) G (E.comp I) hEI
  have hP' :
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType ⊓
        @_root_.AlgebraicGeometry.FormallyUnramified :
        MorphismProperty Scheme.{u})
        (E.comp F).overHom := by
    simpa only [BasedFunctor.comp_assoc, I, fiberProductFstIdInv_comp_snd] using hP
  let _ : CompactSpace G :=
    hqc.compactSpace_of_scheme_representation_over_affine G E hE
  let f := (E.comp F).overHom
  let _ : _root_.AlgebraicGeometry.LocallyOfFiniteType f := hP'.1
  let _ : _root_.AlgebraicGeometry.FormallyUnramified f := hP'.2
  let _ : _root_.AlgebraicGeometry.LocallyQuasiFinite f :=
    _root_.AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType f
  let _ : _root_.AlgebraicGeometry.QuasiCompact f := by infer_instance
  exact ⟨_root_.AlgebraicGeometry.IsFinite.of_locallyQuasiFinite f, hP'.2⟩

end AlgebraicGeometry.BasedFunctor
