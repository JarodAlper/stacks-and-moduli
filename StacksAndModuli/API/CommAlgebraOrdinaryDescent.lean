module

public import StacksAndModuli.API.CommAlgebraPushoutPseudofunctor
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Ordinary singleton descent for commutative algebras

This file compares the kernel-pair presentation of singleton descent for
commutative algebras with its multiplicative coaction presentation.  The
key cancellation identifies base change along the right projection of
`B ⊗[A] B` with the comonadic target `B ⊗[A] D` while retaining the
left `B`-algebra structure.

## Main declarations

- `CommRingCat.overlapCancelAlgIso`: cancellation of the right overlap
  base change.
- `CommRingCat.overlapHomEquiv`: overlap morphisms are equivalent to
  multiplicative coactions.
- `CommRingCat.overlapCoaction`: the coaction attached to an overlap
  morphism.
- `CommRingCat.overlapCounit`: contraction of the tensor-product
  coaction target.
- `CommRingCat.AffineStandardDescentData`: ordinary singleton descent
  data for commutative algebras.
- `CommRingCat.AffineStandardDescentData.overlapHom`: the selected
  tensor-square transition of such a datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

universe u

namespace CommRingCat

noncomputable section

/-- Cancellation of the right base change over the tensor-square overlap.

The source is first formed as a pushout along the right projection
`B → B ⊗[A] B`, then restricted along the left projection.  It is
canonically the `B`-algebra `B ⊗[A] D`. -/
def overlapCancelAlgIso {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (Under.map (CommRingCat.ofHom l)).obj
        ((Under.pushout (CommRingCat.ofHom r)).obj N) ≅
      CommRingCat.mkUnder B (B ⊗[A] N) := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B N :=
    @IsScalarTower.of_algebraMap_eq' A B N _ _ _ f.hom.toAlgebra
      (RingHom.toAlgebra N.hom.hom) (N.hom.hom.comp f.hom).toAlgebra (by
        simp [RingHom.algebraMap_toAlgebra])
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let algL : Algebra B C := inferInstance
  let algR : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let hAC : Algebra A C := inferInstance
  let hAL : @IsScalarTower A B C f.hom.toAlgebra.toSMul algL.toSMul hAC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.hom.toAlgebra algL hAC rfl
  let hAR : @IsScalarTower A B C f.hom.toAlgebra.toSMul algR.toSMul hAC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.hom.toAlgebra algR hAC (by
      ext a
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
  let hPush : @Algebra.IsPushout A B _ _ f.hom.toAlgebra B C _ _
      f.hom.toAlgebra algL algR hAC hAR hAL := by
    exact @TensorProduct.isPushout A B B _ _ _ f.hom.toAlgebra f.hom.toAlgebra
  let eCancel := @Algebra.IsPushout.cancelBaseChangeAlg A B _ _
    f.hom.toAlgebra B C _ _ f.hom.toAlgebra hAC algR algL hAR hAL hPush
    N _ (N.hom.hom.comp f.hom).toAlgebra (RingHom.toAlgebra N.hom.hom)
    (IsScalarTower.of_algebraMap_eq' rfl)
  let nAlg : Algebra B N := RingHom.toAlgebra N.hom.hom
  let hcomm : @SMulCommClass B B C algR.toSMul algL.toSMul :=
    @SMulCommClass.mk B B C algR.toSMul algL.toSMul (fun b₁ b₂ x ↦ by
      rw [@Algebra.smul_def B C _ _ algR b₁,
        @Algebra.smul_def B C _ _ algL b₂,
        @Algebra.smul_def B C _ _ algL b₂,
        @Algebra.smul_def B C _ _ algR b₁]
      ac_rfl)
  let sourceAlg : Algebra B (@TensorProduct B _ C N _ _
      algR.toModule nAlg.toModule) :=
    @Algebra.TensorProduct.leftAlgebra B B C N _ _ algR _ nAlg _ algL hcomm
  let algBB : Algebra B B := inferInstance
  let hcommTarget : @SMulCommClass A B B f.hom.toAlgebra.toSMul algBB.toSMul :=
    inferInstance
  let targetAlg : Algebra B (B ⊗[A] N) :=
    @Algebra.TensorProduct.leftAlgebra A B B N _ _ f.hom.toAlgebra _
      (N.hom.hom.comp f.hom).toAlgebra _ algBB hcommTarget
  letI : Algebra B C := algR
  let ePush := CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of C) N
  let eMapped := (Under.map (CommRingCat.ofHom l)).mapIso ePush.symm
  refine eMapped ≪≫ ?_
  let eRing := @AlgEquiv.toRingEquiv B _ _ _ _ _ sourceAlg targetAlg eCancel
  refine Under.isoMk eRing.toCommRingCatIso ?_
  ext b
  exact @AlgEquiv.commutes B _ _ _ _ _ sourceAlg targetAlg eCancel b

/-- An overlap morphism between the two pushouts of a `B`-algebra is
equivalently a morphism from that algebra to `B ⊗[A] D` over `B`. -/
def overlapHomEquiv {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (((Under.pushout (CommRingCat.ofHom l)).obj N ⟶
        (Under.pushout (CommRingCat.ofHom r)).obj N) ≃
      (N ⟶ CommRingCat.mkUnder B (B ⊗[A] N))) := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  exact ((Under.mapPushoutAdj (CommRingCat.ofHom l)).homEquiv N
    ((Under.pushout (CommRingCat.ofHom r)).obj N)).trans
      (Iso.homCongr (Iso.refl N) (overlapCancelAlgIso f N))

/-- The multiplicative coaction attached to a kernel-pair overlap morphism. -/
def overlapCoaction {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B)
    (theta :
      letI : Algebra A B := f.hom.toAlgebra
      let C := B ⊗[A] B
      let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (Under.pushout (CommRingCat.ofHom l)).obj N ⟶
        (Under.pushout (CommRingCat.ofHom r)).obj N) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    N →ₐ[B] B ⊗[A] N := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  let k := overlapHomEquiv f N theta
  refine
    { __ := k.right.hom
      commutes' := fun b ↦ ?_ }
  exact congrArg (fun h : B ⟶ (CommRingCat.mkUnder B (B ⊗[A] N)).right ↦ h.hom b)
    (Under.w k)

/-- The underlying ring map of `overlapHomEquiv` first inserts the
algebra into the left pullback, applies the overlap morphism, and then
cancels the right base change. -/
lemma overlapHomEquiv_right {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ∀ (theta : (Under.pushout (CommRingCat.ofHom l)).obj N ⟶
        (Under.pushout (CommRingCat.ofHom r)).obj N),
      (overlapHomEquiv f N theta).right =
        pushout.inl N.hom (CommRingCat.ofHom l) ≫ theta.right ≫
          (overlapCancelAlgIso f N).hom.right := by
  dsimp only
  intro theta
  rfl

/-- Elementwise formula for the multiplicative coaction attached to an
overlap morphism. -/
lemma overlapCoaction_apply {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ∀ (theta : (Under.pushout (CommRingCat.ofHom l)).obj N ⟶
        (Under.pushout (CommRingCat.ofHom r)).obj N) (n : N),
      overlapCoaction f N theta n =
        (overlapCancelAlgIso f N).hom.right.hom
          (theta.right.hom ((pushout.inl N.hom (CommRingCat.ofHom l)).hom n)) := by
  dsimp only
  intro theta n
  change (overlapHomEquiv f N theta).right.hom n = _
  rw [overlapHomEquiv_right]
  rfl

/-- Contract the tensor-product target of a multiplicative coaction. -/
def overlapCounit {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    CommRingCat.mkUnder B (B ⊗[A] N) ⟶ N := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra B N := RingHom.toAlgebra N.hom.hom
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
  let e : B ⊗[A] N →ₐ[B] N :=
    Algebra.TensorProduct.lift (Algebra.ofId B N) (AlgHom.id A N)
      (fun _ _ ↦ Commute.all _ _)
  exact Under.homMk (CommRingCat.ofHom e.toRingHom) (by
    ext b
    exact e.commutes b)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- After cancellation, contraction is the identity on the algebra
generator of the right overlap pushout. -/
lemma overlapCancelAlgIso_hom_counit_inl {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    pushout.inl N.hom (CommRingCat.ofHom r) ≫
        (overlapCancelAlgIso f N).hom.right ≫
        (overlapCounit f N).right = 𝟙 N.right := by
  dsimp only
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  let C := B ⊗[A] B
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let algL : Algebra B C := inferInstance
  let algR : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let hAC : Algebra A C := inferInstance
  let hAL : @IsScalarTower A B C f.hom.toAlgebra.toSMul algL.toSMul hAC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.hom.toAlgebra algL hAC rfl
  let hAR : @IsScalarTower A B C f.hom.toAlgebra.toSMul algR.toSMul hAC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.hom.toAlgebra algR hAC (by
      ext a
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul a)
  let hPush : @Algebra.IsPushout A B _ _ f.hom.toAlgebra B C _ _
      f.hom.toAlgebra algL algR hAC hAR hAL := by
    exact @TensorProduct.isPushout A B B _ _ _ f.hom.toAlgebra f.hom.toAlgebra
  let nAlg : Algebra B N := RingHom.toAlgebra N.hom.hom
  let hN : @IsScalarTower A B N f.hom.toAlgebra.toSMul nAlg.toSMul
      ((N.hom.hom.comp f.hom).toAlgebra).toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eCancel := @Algebra.IsPushout.cancelBaseChangeAlg A B _ _
    f.hom.toAlgebra B C _ _ f.hom.toAlgebra hAC algR algL hAR hAL hPush
    N _ (N.hom.hom.comp f.hom).toAlgebra nAlg hN
  letI : Algebra B C := algR
  have hpush :
      pushout.inl N.hom (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B →+* B ⊗[A] B)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj
          (CommRingCat.of (B ⊗[A] B)) N).symm.hom.right =
        CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom := by
    ext n
    simp [CommRingCat.tensorProdObjIsoPushoutObj]
  unfold overlapCancelAlgIso
  dsimp only
  simp only [Iso.trans_hom, Functor.mapIso_hom, Under.comp_right,
    Under.map_map_right, Category.assoc]
  simp only [← Category.assoc]
  rw [hpush]
  simp only [Under.isoMk_hom_right]
  ext n
  change (overlapCounit f N).right.hom
    (eCancel ((1 : C) ⊗ₜ[B,r] n)) = n
  rw [@Algebra.IsPushout.cancelBaseChangeAlg_tmul A B _ _
    f.hom.toAlgebra B C _ _ f.hom.toAlgebra hAC algR algL hAR hAL hPush
    N _ (N.hom.hom.comp f.hom).toAlgebra nAlg hN n]
  letI : Algebra B N := nAlg
  letI : IsScalarTower A B N := hN
  change (Algebra.TensorProduct.lift (Algebra.ofId B N)
    (AlgHom.id A N) (fun _ _ ↦ Commute.all _ _)) ((1 : B) ⊗ₜ[A] n) = n
  rw [Algebra.TensorProduct.lift_tmul]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- After cancellation, contraction on the overlap-ring generator is
the original structure map precomposed with tensor multiplication. -/
lemma overlapCancelAlgIso_hom_counit_inr {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    pushout.inr N.hom (CommRingCat.ofHom r) ≫
        (overlapCancelAlgIso f N).hom.right ≫
        (overlapCounit f N).right =
      CommRingCat.ofHom (N.hom.hom.comp mul) := by
  dsimp only
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : Algebra B (B ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  have hleft :
      CommRingCat.ofHom l ≫ pushout.inr N.hom (CommRingCat.ofHom r) ≫
          (overlapCancelAlgIso f N).hom.right ≫
          (overlapCounit f N).right = N.hom := by
    calc
      _ = ((Under.map (CommRingCat.ofHom l)).obj
              ((Under.pushout (CommRingCat.ofHom r)).obj N)).hom ≫
            (overlapCancelAlgIso f N).hom.right ≫
            (overlapCounit f N).right := by rfl
      _ = (CommRingCat.mkUnder B (B ⊗[A] N)).hom ≫
            (overlapCounit f N).right := by
          simpa [l, r, Category.assoc] using congrArg
            (fun k : B ⟶ (CommRingCat.mkUnder B (B ⊗[A] N)).right ↦
              k ≫ (overlapCounit f N).right)
            (Under.w (overlapCancelAlgIso f N).hom)
      _ = N.hom := Under.w (overlapCounit f N)
  have hright :
      CommRingCat.ofHom r ≫ pushout.inr N.hom (CommRingCat.ofHom r) ≫
          (overlapCancelAlgIso f N).hom.right ≫
          (overlapCounit f N).right = N.hom := by
    calc
      _ = N.hom ≫ pushout.inl N.hom (CommRingCat.ofHom r) ≫
            (overlapCancelAlgIso f N).hom.right ≫
            (overlapCounit f N).right := by
          rw [← Category.assoc, ← pushout.condition]
          simp only [Category.assoc]
      _ = N.hom := by
          simpa [r, Category.assoc] using congrArg
            (fun k : N.right ⟶ N.right ↦ N.hom ≫ k)
            (overlapCancelAlgIso_hom_counit_inl f N)
  apply CommRingCat.hom_ext
  apply Algebra.TensorProduct.ringHom_ext
  · calc
      _ = N.hom.hom := by
        simpa [l, r, Category.assoc] using congrArg CommRingCat.Hom.hom hleft
      _ = _ := by
        apply RingHom.ext
        intro b
        simp
  · calc
      _ = N.hom.hom := by
        simpa [r, Category.assoc] using congrArg CommRingCat.Hom.hom hright
      _ = _ := by
        apply RingHom.ext
        intro b
        simp

/-- Ordinary singleton descent data for commutative algebras along a ring
map. -/
abbrev AffineStandardDescentData {A B : CommRingCat.{u}} (f : A ⟶ B) :=
  let F := underPushoutPseudofunctorOpOp.{u}
  @Pseudofunctor.DescentData (CommRingCat.{u})ᵒᵖ _ F Unit
    (.op A) (fun _ ↦ .op B) (fun _ ↦ f.op)

/-- The left tensor-factor map lies over the original affine ring map. -/
lemma affineOverlapLeft_comp {A B : CommRingCat.{u}} (f : A ⟶ B) :
    letI : Algebra A B := f.hom.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    (CommRingCat.ofHom l).op ≫ f.op =
      (CommRingCat.ofHom (algebraMap A C)).op := by
  letI : Algebra A B := f.hom.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  calc
    _ = (f ≫ CommRingCat.ofHom l).op := rfl
    _ = (CommRingCat.ofHom (l.comp f.hom)).op := rfl
    _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2

/-- The right tensor-factor map lies over the original affine ring map. -/
lemma affineOverlapRight_comp {A B : CommRingCat.{u}} (f : A ⟶ B) :
    letI : Algebra A B := f.hom.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (CommRingCat.ofHom r).op ≫ f.op =
      (CommRingCat.ofHom (algebraMap A C)).op := by
  letI : Algebra A B := f.hom.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  calc
    _ = (f ≫ CommRingCat.ofHom r).op := rfl
    _ = (CommRingCat.ofHom (r.comp f.hom)).op := rfl
    _ = (CommRingCat.ofHom (l.comp f.hom)).op := by
      congr 2
      change r.comp f.hom = l.comp f.hom
      simpa only [show f.hom = algebraMap A B from rfl] using
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2

/-- The selected tensor-square transition of ordinary singleton descent
data for commutative algebras. -/
noncomputable def AffineStandardDescentData.overlapHom
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (Under.pushout (CommRingCat.ofHom l)).obj (D.obj default) ⟶
      (Under.pushout (CommRingCat.ofHom r)).obj (D.obj default) := by
  letI : Algebra A B := f.hom.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let q : CommRingCatᵒᵖ := .op (CommRingCat.of C)
  let qA : q ⟶ .op A := (CommRingCat.ofHom (algebraMap A C)).op
  exact D.hom qA (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op
    (affineOverlapLeft_comp f) (affineOverlapRight_comp f)

/-- The multiplicative coaction of ordinary singleton descent data for
commutative algebras. -/
noncomputable def AffineStandardDescentData.coaction
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    let N : Under B := D.obj default
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    N →ₐ[B] B ⊗[A] N :=
  overlapCoaction f (D.obj default) (D.overlapHom f)

end

end CommRingCat
