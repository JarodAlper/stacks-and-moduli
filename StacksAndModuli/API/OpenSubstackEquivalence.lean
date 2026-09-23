module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»

/-!
# Point-surjective open substacks

An open substack inclusion which is surjective on the point spaces of the source and
target is an equivalence.  The proof pulls the inclusion back along the morphism from a
scheme classified by an arbitrary target object.  The pullback is an open subscheme;
surjectivity on field-valued points shows that it contains every residue-field point, so
it is the whole scheme and the target object lies in the essential image.

## Main results

* `AlgebraicGeometry.BasedFunctor.isEquivalence_of_isOpenSubstackInclusion_of_surjective_mapPoints`
* `AlgebraicGeometry.BasedFunctor.isEquivalence_iff_surjective_mapPoints_of_isOpenSubstackInclusion`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite AlgebraicGeometry
  CategoryTheory.BasedCategory AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒜 : BasedCategory.{v₂, u₂} Scheme.{u}}
  {ℬ : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- An open substack inclusion which is surjective on field-valued point classes is an
equivalence of its underlying categories. -/
theorem isEquivalence_of_isOpenSubstackInclusion_of_surjective_mapPoints
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    (F : 𝒜 ⥤ᵇ ℬ) [hF : IsOpenSubstackInclusion F]
    (hsurj : Function.Surjective (mapPoints F)) :
    F.toFunctor.IsEquivalence := by
  let _ : F.toFunctor.Full := hF.full
  let _ : F.toFunctor.Faithful := hF.faithful
  refine { full := inferInstance, faithful := inferInstance, essSurj := ?_ }
  constructor
  intro y
  let S : Scheme.{u} := ℬ.p.obj y
  let E := twoYonedaEval (𝒳 := ℬ) S
  let _ : E.IsEquivalence := isEquivalence_twoYonedaEval (𝒳 := ℬ) S
  let gy : overBased S ⥤ᵇ ℬ := E.objPreimage (Functor.Fiber.mk rfl)
  let ey : E.obj gy ≅ Functor.Fiber.mk rfl :=
    E.objObjPreimageIso (Functor.Fiber.mk rfl)
  obtain ⟨W, hW⟩ := exists_opens_fiberEssImage F S gy
  have hWS : (W : Set S) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    let K := S.residueField s
    let f : Spec (CommRingCat.of K) ⟶ S := S.fromSpecResidueField s
    let z : FieldPoint ℬ := ⟨K, (overBased.map f).comp gy⟩
    obtain ⟨p, hp⟩ := hsurj (pointSpace.mk z)
    obtain ⟨p, rfl⟩ := Quot.exists_rep p
    obtain ⟨L, hL, ψ₁, ψ₂, ⟨e⟩⟩ := pointSpace.mk_eq_mk_iff.mp hp
    let Z : Over (Spec (CommRingCat.of L)) :=
      Over.mk (𝟙 (Spec (CommRingCat.of L)))
    have hsource : F.fiberEssImage (((FieldPoint.map F p).restrict ψ₁).obj Z) :=
      fiberEssImage_comp_obj F
        ((overBased.map (Spec.map (CommRingCat.ofHom ψ₁))).comp p.hom) Z
    have htarget : F.fiberEssImage ((z.restrict ψ₂).obj Z) :=
      fiberEssImage_obj_of_iso F e Z hsource
    have hrange := (hW _).mp htarget
    change Set.range
      (((𝟙 (Spec (CommRingCat.of L))) ≫ Spec.map (CommRingCat.ofHom ψ₂)) ≫ f).base
        ⊆ (W : Set S) at hrange
    simp only [Category.id_comp] at hrange
    obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of L)) := inferInstance
    have hs : f.base ((Spec.map (CommRingCat.ofHom ψ₂)).base pt) = s :=
      Scheme.fromSpecResidueField_apply _ _
    exact Set.mem_of_eq_of_mem hs.symm (hrange ⟨pt, rfl⟩)
  have hgy : F.fiberEssImage (gy.obj (Over.mk (𝟙 S))) := by
    apply (hW _).mpr
    rw [hWS]
    exact Set.subset_univ _
  obtain ⟨x, ex, -⟩ := hgy
  exact ⟨x, ⟨ex.trans (Fiber.fiberInclusion.mapIso ey)⟩⟩

/-- For an open substack inclusion between prestacks, equivalence of the underlying
categories is equivalent to surjectivity on field-valued point classes. -/
theorem isEquivalence_iff_surjective_mapPoints_of_isOpenSubstackInclusion
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    (F : 𝒜 ⥤ᵇ ℬ) [IsOpenSubstackInclusion F] :
    F.toFunctor.IsEquivalence ↔ Function.Surjective (mapPoints F) := by
  exact ⟨surjective_mapPoints_of_isEquivalence F,
    isEquivalence_of_isOpenSubstackInclusion_of_surjective_mapPoints F⟩

end AlgebraicGeometry.BasedFunctor
