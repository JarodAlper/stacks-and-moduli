module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Faithfully flat descent for commutative algebras

Base change of commutative algebras is the pushout functor between under-categories
of commutative rings.  This file proves that faithfully flat base change reflects
isomorphisms and is comonadic.  It is the categorical algebraic core of effective
fpqc descent for affine morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Comonad
open TensorProduct

universe u

noncomputable section

namespace CommRingCat

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Tensor base change of commutative algebras reflects isomorphisms along a
faithfully flat ring map. -/
lemma reflectsIsomorphisms_tensorProd_of_faithfullyFlat
    [Algebra R S] (hf : (algebraMap R S).FaithfullyFlat) :
    (tensorProd R S).ReflectsIsomorphisms := by
  refine ⟨fun {A B} g hg ↦ ?_⟩
  rw [← isIso_iff_of_reflects_iso g (Under.forget R)]
  rw [← isIso_iff_of_reflects_iso ((tensorProd R S).map g)
    (Under.forget S)] at hg
  rw [ConcreteCategory.isIso_iff_bijective] at hg ⊢
  change Function.Bijective
    (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom g)) at hg
  change Function.Bijective g.right.hom
  let M : ModuleCat R := ModuleCat.of R A
  let N : ModuleCat R := ModuleCat.of R B
  let hl : M →ₗ[R] N :=
    { toFun := g.right.hom
      map_add' := g.right.hom.map_add
      map_smul' := fun r a ↦ by
        change g.right.hom (A.hom.hom r * a) =
          B.hom.hom r * g.right.hom a
        rw [map_mul]
        congr 1
        have hw := congrArg (fun k : R ⟶ B.right ↦ k.hom r) (Under.w g)
        exact hw }
  let h : M ⟶ N := ModuleCat.ofHom hl
  have hh : Function.Bijective (LinearMap.lTensor S h.hom) := by
    convert hg using 1
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul s a => simp [h, hl, LinearMap.lTensor_tmul,
        Algebra.TensorProduct.map_tmul]
  letI : Module.FaithfullyFlat R S :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hf
  exact
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S h.hom).mp hh

/-- Pushout base change of commutative algebras reflects isomorphisms along a
faithfully flat ring map. -/
lemma reflectsIsomorphisms_pushout_of_faithfullyFlat
    (hf : f.hom.FaithfullyFlat) :
    (Under.pushout f).ReflectsIsomorphisms := by
  letI : Algebra R S := f.hom.toAlgebra
  letI : (tensorProd R S).ReflectsIsomorphisms :=
    reflectsIsomorphisms_tensorProd_of_faithfullyFlat hf
  have hEq : CommRingCat.ofHom (algebraMap R S) = f := by
    ext
    rfl
  rw [← hEq]
  exact reflectsIsomorphisms_of_iso (tensorProdIsoPushout R S)

/-- Faithfully flat base change of commutative algebras is comonadic. -/
@[instance_reducible]
def comonadicPushoutOfFaithfullyFlat
    (hf : f.hom.FaithfullyFlat) :
    ComonadicLeftAdjoint (Under.pushout f) := by
  letI : (Under.pushout f).ReflectsIsomorphisms :=
    reflectsIsomorphisms_pushout_of_faithfullyFlat f hf
  letI : PreservesFiniteLimits (Under.pushout f) :=
    Under.preservesFiniteLimits_of_flat f hf.flat
  convert!
    Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
      (Under.mapPushoutAdj f)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩

end CommRingCat
