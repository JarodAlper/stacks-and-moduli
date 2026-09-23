module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Flatness is fpqc local on the source

Stacks Project tag **036K**, label `descent-lemma-flat-fpqc-local-source`, in `descent.tex`,
§`036J` (Properties of morphisms local in the fpqc topology on the source).

> The property `P(f) = "f is flat"` is fpqc local on the source.

The form needed by §3.1 is the two-out-of-three statement for a surjective flat `g`: given
`g : X' ⟶ X` surjective, flat and quasi-compact and `f : X ⟶ Y`, the composite `g ≫ f` is flat
if and only if `f` is.

**Proof route (Stacks Project).** The lemma reduces to the ring-theoretic statement: if
`A → B → C` are local homomorphisms of local rings with `B → C` flat and faithfully flat, then
`A → B` is flat if and only if `A → C` is. The Stacks proof cites
`algebra-lemma-composition-flat` (one direction), `algebra-lemma-local-flat-ff` and
`algebra-lemma-flat-permanence` (the converse). Mathlib has the composition direction as
`Module.Flat.comp`/`Module.Flat.trans` and has `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
the permanence direction (`algebra-lemma-flat-permanence`) is the piece to check for.

Mathlib already provides the *target*-side companion of this in
`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, where `@Flat` is shown to descend along
fpqc covers; what is missing is this source-side two-out-of-three form.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- Flatness permanence (Stacks `algebra-lemma-flat-permanence`): in a tower `A → B → C` with
`C` flat over `A` and faithfully flat over `B`, the middle ring `B` is flat over `A`. -/
theorem Module.Flat.of_faithfullyFlat_tower (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Flat A C] [Module.FaithfullyFlat B C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have hB : Function.Injective (f.baseChange B) ↔
      Function.Injective (LinearMap.lTensor B f) := Iff.rfl
  rw [← hB, ← Module.FaithfullyFlat.lTensor_injective_iff_injective B C]
  have hC : Function.Injective (LinearMap.lTensor C (f.baseChange B)) ↔
      Function.Injective ((f.baseChange B).baseChange C) := Iff.rfl
  rw [hC]
  have key : ((f.baseChange B).baseChange C) =
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C P).symm.toLinearMap.comp
        ((f.baseChange C).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N).toLinearMap)) := by
    ext n
    simp
  rw [key]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C P).symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap (M := C) f hf).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N).injective)

/-- **Stacks 036K** (`descent-lemma-flat-fpqc-local-source`), two-out-of-three form. For
`g : X' ⟶ X` surjective, flat and quasi-compact, the composite `g ≫ f` is flat if and only if
`f` is. -/
@[stacks 036K]
theorem flat_comp_iff_of_surjective_flat {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] : Flat (g ≫ f) ↔ Flat f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  apply Flat.of_stalkMap
  intro x
  obtain ⟨x', rfl⟩ := g.surjective x
  have hχ : ((g ≫ f).stalkMap x').hom.Flat := Flat.stalkMap (g ≫ f) x'
  rw [Scheme.Hom.stalkMap_comp] at hχ
  have hψ : (g.stalkMap x').hom.Flat := Flat.stalkMap g x'
  rw [CommRingCat.hom_comp] at hχ
  -- pass to the local rings at the stalks
  algebraize [(f.stalkMap (g x')).hom, (g.stalkMap x').hom,
    (g.stalkMap x').hom.comp (f.stalkMap (g x')).hom]
  haveI : IsLocalHom (algebraMap ↑(X.presheaf.stalk (g x'))
      ↑(X'.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x').hom)
  haveI : Module.Flat (X.presheaf.stalk (g x')) (X'.presheaf.stalk x') := hψ
  haveI : Module.FaithfullyFlat (X.presheaf.stalk (g x'))
      (X'.presheaf.stalk x') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat (Y.presheaf.stalk (f (g x'))) (X'.presheaf.stalk x') := hχ
  exact Module.Flat.of_faithfullyFlat_tower
    (Y.presheaf.stalk (f (g x'))) (X.presheaf.stalk (g x'))
    (X'.presheaf.stalk x')

end AlgebraicGeometry
