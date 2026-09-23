module

public import StacksAndModuli.API.FormalBranchComponents
public import StacksAndModuli.API.IrreducibleComponentGeometricGenus

/-!
# Stalk kernels along irreducible components

This file identifies the kernel of a stalk map induced by an integral scheme mapping densely
onto an irreducible component.  At every source point, that kernel is a minimal prime of the
target stalk.  The proof maps the generic point of the source local spectrum to the generic
point of the component, compares it with a minimal prime below the kernel, and uses the
embedding `Spec 𝒪_{X,x} ⟶ X` to identify the two local points.

No Noetherian or reducedness hypothesis on the target is required.

## Main results

* `Scheme.Hom.stalkMap_ker_mem_minimalPrimes_of_closure_range_eq_irreducibleComponent`:
  the stalk kernel of an integral scheme dense in a component is a minimal prime.
* `AlgebraicGeometry.Scheme.reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes`:
  the specialization to the reduced induced structure on an irreducible component.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The generic point of the spectrum of an integral scheme's local ring maps to the
generic point of the scheme. -/
lemma fromSpecStalk_genericPoint_of_isIntegral
    (Y : Scheme.{u}) [IsIntegral Y] (y : Y) :
    Y.fromSpecStalk y (genericPoint (Spec (Y.presheaf.stalk y))) = genericPoint Y := by
  have hgenericSpecializes : genericPoint Y ∈ {w | Specializes w y} :=
    genericPoint_specializes y
  rw [← Y.range_fromSpecStalk] at hgenericSpecializes
  obtain ⟨q, hq⟩ := hgenericSpecializes
  have hsource : Specializes (genericPoint (Spec (Y.presheaf.stalk y))) q :=
    genericPoint_specializes q
  have himage := hsource.map (Y.fromSpecStalk y).continuous
  rw [hq] at himage
  exact (himage.antisymm (genericPoint_specializes _)).eq

/-- An integral scheme whose image is dense in an irreducible component maps its generic
point to the generic point of that component. -/
lemma Hom.map_genericPoint_eq_of_closure_range_eq_irreducibleComponent
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y]
    (Z : irreducibleComponents X) (hZ : closure (Set.range f) = Z.1) :
    f (genericPoint Y) = Z.property.1.genericPoint := by
  have hgeneric := (genericPoint_spec Y).image f.continuous
  have hclosure : closure (f '' (Set.univ : Set Y)) = Z.1 := by
    rw [Set.image_univ]
    exact hZ
  have himage : IsGenericPoint (f (genericPoint Y)) Z.1 := by
    rwa [hclosure] at hgeneric
  exact himage.eq (Z.property.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z.1 Z.property))

/-- If an integral scheme maps densely onto an irreducible component, the kernel of the
induced map from the target stalk at any source point is a minimal prime.

This needs no finiteness, Noetherianity, or reducedness hypothesis on the target. -/
theorem Hom.stalkMap_ker_mem_minimalPrimes_of_closure_range_eq_irreducibleComponent
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y]
    (Z : irreducibleComponents X) (hZ : closure (Set.range f) = Z.1) (y : Y) :
    RingHom.ker (f.stalkMap y).hom ∈ minimalPrimes (X.presheaf.stalk (f y)) := by
  let ξ : Spec (Y.presheaf.stalk y) := genericPoint (Spec (Y.presheaf.stalk y))
  let pPoint : Spec (X.presheaf.stalk (f y)) := Spec.map (f.stalkMap y) ξ
  let p : Ideal (X.presheaf.stalk (f y)) := RingHom.ker (f.stalkMap y).hom
  let _ : p.IsPrime := RingHom.ker_isPrime (f.stalkMap y).hom
  obtain ⟨q, hqmin, hqp⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := p) bot_le
  let q' : minimalPrimes (X.presheaf.stalk (f y)) := ⟨q, hqmin⟩
  have hpPoint_asIdeal : pPoint.asIdeal = p := by
    change Ideal.comap (f.stalkMap y).hom
      (genericPoint (Spec (Y.presheaf.stalk y))).asIdeal = _
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have hqpPoint : q'.1 ≤ pPoint.asIdeal := hpPoint_asIdeal.symm ▸ hqp
  have hspecializes : Specializes (X.stalkBranchPoint (f y) q') pPoint :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hqpPoint
  have hpPoint_image : X.fromSpecStalk (f y) pPoint = Z.property.1.genericPoint := by
    change X.fromSpecStalk (f y) (Spec.map (f.stalkMap y) ξ) = _
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]
    change f (Y.fromSpecStalk y ξ) = _
    rw [show Y.fromSpecStalk y ξ = genericPoint Y from
      fromSpecStalk_genericPoint_of_isIntegral Y y]
    exact f.map_genericPoint_eq_of_closure_range_eq_irreducibleComponent Z hZ
  have hspecializes' := hspecializes.map (X.fromSpecStalk (f y)).continuous
  rw [hpPoint_image] at hspecializes'
  let W := X.stalkBranchComponent (f y) q'
  have hgeneric_mem : Z.property.1.genericPoint ∈ W.1 := by
    change Z.property.1.genericPoint ∈
      closure ({X.fromSpecStalk (f y) (X.stalkBranchPoint (f y) q')} : Set X)
    exact hspecializes'.mem_closure
  have hZW : Z.1 ⊆ W.1 := by
    rw [← (Z.property.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents Z.1 Z.property)).def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hgeneric_mem)
      (isClosed_of_mem_irreducibleComponents W.1 W.property)
  have hWZ : W = Z := by
    apply Subtype.ext
    exact Set.Subset.antisymm (Z.property.2 W.property.1 hZW) hZW
  have hqPoint_image :
      X.fromSpecStalk (f y) (X.stalkBranchPoint (f y) q') =
        Z.property.1.genericPoint := by
    have hgeneric : IsGenericPoint
        (X.fromSpecStalk (f y) (X.stalkBranchPoint (f y) q')) Z.1 := by
      change closure
        ({X.fromSpecStalk (f y) (X.stalkBranchPoint (f y) q')} : Set X) = Z.1
      rw [← X.stalkBranchComponent_val (f y) q']
      exact congrArg Subtype.val hWZ
    exact hgeneric.eq (Z.property.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents Z.1 Z.property))
  have hpoints : X.stalkBranchPoint (f y) q' = pPoint :=
    (X.fromSpecStalk (f y)).isEmbedding.injective
      (hqPoint_image.trans hpPoint_image.symm)
  have hideals := congrArg PrimeSpectrum.asIdeal hpoints
  rw [show (X.stalkBranchPoint (f y) q').asIdeal = q'.1 from rfl,
    hpPoint_asIdeal] at hideals
  have hpmin : p ∈ minimalPrimes (X.presheaf.stalk (f y)) := hideals ▸ q'.2
  simpa only [p] using hpmin

/-- The kernel of the stalk map from an ambient scheme to the reduced induced structure on
one of its irreducible components is the corresponding minimal prime of the ambient stalk. -/
theorem reducedIrreducibleComponent_stalkMap_ker_mem_minimalPrimes
    (X : Scheme.{u}) (Z : irreducibleComponents X)
    (z : X.reducedIrreducibleComponent Z) :
    RingHom.ker ((X.reducedIrreducibleComponentι Z).stalkMap z).hom ∈
      minimalPrimes (X.presheaf.stalk (X.reducedIrreducibleComponentι Z z)) := by
  apply Hom.stalkMap_ker_mem_minimalPrimes_of_closure_range_eq_irreducibleComponent
    (X.reducedIrreducibleComponentι Z) Z
  rw [X.range_reducedIrreducibleComponentι Z]
  exact (isClosed_of_mem_irreducibleComponents Z.1 Z.property).closure_eq

end AlgebraicGeometry.Scheme
