module

public import StacksAndModuli.API.ModuleDescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Chosen kernel-pair descent data for modules

This file records the comparison between singleton affine descent data written on a
chosen kernel pair and Beck coalgebras.  The ordinary `DescentData` category is
equivalent to the chosen-pullback `DescentData'` category; the latter exposes the
single overlap square needed for the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

noncomputable def affineChosenPullback :
    ChosenPullback (CommRingCat.ofHom f).op (CommRingCat.ofHom f).op := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : CommRingCat.of B ⟶ CommRingCat.of C :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let r : CommRingCat.of B ⟶ CommRingCat.of C :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let h : IsPullback l.op r.op (CommRingCat.ofHom f).op
      (CommRingCat.ofHom f).op :=
    (CommRingCat.isPushout_tensorProduct A B B).op.flip
  exact
    { pullback := op (CommRingCat.of C)
      p₁ := l.op
      p₂ := r.op
      condition := h.w
      isLimit := h.isLimit }

noncomputable def affineChosenPullback₃ :
    ChosenPullback₃ (affineChosenPullback f) (affineChosenPullback f)
      (affineChosenPullback f) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : CommRingCat.of B ⟶ CommRingCat.of C :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let r : CommRingCat.of B ⟶ CommRingCat.of C :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let cp : ChosenPullback r.op l.op := by
    let h : IsPullback (pushout.inl r l).op (pushout.inr r l).op r.op l.op :=
      (IsPushout.of_hasPushout r l).op.flip
    exact
      { pullback := op (pushout r l)
        p₁ := (pushout.inl r l).op
        p₂ := (pushout.inr r l).op
        condition := h.w
        isLimit := h.isLimit }
  let cp' : ChosenPullback (affineChosenPullback f).p₂
      (affineChosenPullback f).p₁ := by
    simpa only [affineChosenPullback] using cp
  refine { chosenPullback := cp', l := ?_ }
  exact Classical.choice (ChosenPullback.LiftStruct.nonempty
    (h := affineChosenPullback f) (by
      rw [Category.assoc, (affineChosenPullback f).condition,
        ← Category.assoc, cp'.condition, Category.assoc,
        (affineChosenPullback f).condition]
      rfl) (by cat_disch))

abbrev AffinePrimeDescentData :=
  let F := extendScalarsPseudofunctorOpOp.{u}
  @Pseudofunctor.DescentData' (CommRingCat.{u})ᵒᵖ _ F Unit
    (op (CommRingCat.of A)) (fun _ ↦ op (CommRingCat.of B))
    (fun _ ↦ (CommRingCat.ofHom f).op)
    (fun (_ _ : Unit) ↦ affineChosenPullback f)
    (fun (_ _ _ : Unit) ↦ affineChosenPullback₃ f)

noncomputable def affinePrimeDescentEquivalence :
    AffinePrimeDescentData f ≌ AffineStandardDescentData f :=
  Pseudofunctor.DescentData'.descentDataEquivalence
    extendScalarsPseudofunctorOpOp
    (fun (_ _ : Unit) ↦ affineChosenPullback f)
    (fun (_ _ _ : Unit) ↦ affineChosenPullback₃ f)

noncomputable def affinePrimeToCoalgebra :
    AffinePrimeDescentData f ⥤
      (extendRestrictScalarsAdj f).toComonad.Coalgebra :=
  (affinePrimeDescentEquivalence f).functor ⋙
    AffineStandardDescentData.toCoalgebra f

lemma affinePrimeToCoalgebra_obj_a (D : AffinePrimeDescentData f) :
    ((affinePrimeToCoalgebra f).obj D).a =
      overlapHomEquiv f (D.obj default) (D.hom default default) := by
  letI : Algebra A B := f.toAlgebra
  change overlapHomEquiv f (D.obj default)
    (AffineStandardDescentData.overlapHom f
      ((affinePrimeDescentEquivalence f).functor.obj D)) = _
  refine (overlapHomEquiv f (D.obj default)).apply_eq_iff_eq.mpr ?_
  change Pseudofunctor.DescentData'.pullHom' D.hom
    (affineChosenPullback f).p (affineChosenPullback f).p₁
    (affineChosenPullback f).p₂ (by simp) (by simp) = D.hom default default
  exact Pseudofunctor.DescentData'.pullHom'_p₁_p₂ D.hom default default

noncomputable def affinePrimePreimage {D E : AffinePrimeDescentData f}
    (h : (affinePrimeToCoalgebra f).obj D ⟶ (affinePrimeToCoalgebra f).obj E) : D ⟶ E where
  hom _ := h.f
  comm i j := by
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    letI : Algebra A B := f.toAlgebra
    change (extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B)).map h.f ≫
        E.hom default default = D.hom default default ≫
      (extendScalars
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* B ⊗[A] B)).map h.f
    apply (overlap_comm_iff_coaction_comm f (D.obj default) (E.obj default) h.f
      (D.hom default default) (E.hom default default)).mpr
    have hh := h.h
    change overlapHomEquiv f (D.obj default)
        (Pseudofunctor.DescentData'.pullHom' D.hom
          (affineChosenPullback f).p (affineChosenPullback f).p₁
          (affineChosenPullback f).p₂ (by simp) (by simp)) ≫
        (extendRestrictScalarsAdj f).toComonad.map h.f =
      h.f ≫ overlapHomEquiv f (E.obj default)
        (Pseudofunctor.DescentData'.pullHom' E.hom
          (affineChosenPullback f).p (affineChosenPullback f).p₁
          (affineChosenPullback f).p₂ (by simp) (by simp)) at hh
    rw [Pseudofunctor.DescentData'.pullHom'_p₁_p₂,
      Pseudofunctor.DescentData'.pullHom'_p₁_p₂] at hh
    exact hh

noncomputable def affinePrimeToCoalgebraFullyFaithful :
    (affinePrimeToCoalgebra f).FullyFaithful where
  preimage h := affinePrimePreimage f h
  map_preimage h := by
    apply Comonad.Coalgebra.Hom.ext'
    rfl
  preimage_map h := by
    apply Pseudofunctor.DescentData'.hom_ext
    intro i
    obtain rfl : i = default := Subsingleton.elim _ _
    rfl

noncomputable def affineStandardToCoalgebraFullyFaithful :
    (AffineStandardDescentData.toCoalgebra f).FullyFaithful := by
  let e := affinePrimeDescentEquivalence f
  let F := AffineStandardDescentData.toCoalgebra f
  have hcomp : (e.functor ⋙ F).FullyFaithful := by
    simpa only [e, F, affinePrimeToCoalgebra] using
      affinePrimeToCoalgebraFullyFaithful f
  letI : F.Full := by
    apply Functor.full_of_comp_essSurj F e.functor
    intro X Y φ
    obtain ⟨g, hg⟩ := hcomp.map_surjective φ
    exact ⟨e.functor.map g, hg⟩
  letI : F.Faithful := by
    apply Functor.faithful_of_comp_essSurj F e.functor
    intro X Y g h hgh
    obtain ⟨g', hg'⟩ := e.fullyFaithfulFunctor.map_surjective g
    obtain ⟨h', hh'⟩ := e.fullyFaithfulFunctor.map_surjective h
    have gh' : g' = h' := by
      apply hcomp.map_injective
      change F.map (e.functor.map g') = F.map (e.functor.map h')
      simpa only [hg', hh'] using hgh
    rw [← hg', ← hh', gh']
  exact Functor.FullyFaithful.ofFullyFaithful F

end ModuleCat
