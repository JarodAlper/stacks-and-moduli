module

public import StacksAndModuli.API.CommAlgebraOrdinaryDescent
public import StacksAndModuli.API.CommAlgebraDescent
public import StacksAndModuli.API.ModuleDescentData
public import StacksAndModuli.API.PseudofunctorDescentStrongTrans
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Forgetting commutative-algebra descent data to module descent data

The underlying module of a pushout commutative algebra is extension of
scalars.  This file packages that comparison as a strong transformation of
the corresponding pseudofunctors, including its unit and composition
coherences.

## Main declarations

- `CommRingCat.pushoutForgetModuleIso`: the fiberwise pushout/tensor-product
  comparison.
- `CommRingCat.underForgetModuleStrongTrans`: forgetting multiplication is a
  strong transformation from pushout algebras to extension-of-scalars
  modules.
- `CommRingCat.AffineStandardDescentData.toCommAlgebraDescentData`: convert
  ordinary affine descent data into a multiplicative coaction suitable for
  effective faithfully flat descent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CommRingCat

noncomputable section

/-- Forget a commutative algebra to its underlying module. -/
def underForgetModule (R : CommRingCat.{u}) :
    CategoryTheory.Functor (Under R) (ModuleCat.{u} R) where
  obj N := ModuleCat.of R N
  map {M N} f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap
  map_id N := by
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    rfl

/-- The underlying module of a pushout algebra is extension of scalars. -/
def pushoutForgetModuleIso {R S : CommRingCat.{u}} (g : R ⟶ S)
    (N : Under R) :
    ModuleCat.of S ((Under.pushout g).obj N) ≅
      (ModuleCat.extendScalars g.hom).obj (ModuleCat.of R N) := by
  letI : Algebra R S := g.hom.toAlgebra
  let e := (tensorProdObjIsoPushoutObj S N).symm
  let eAlg : ((Under.pushout g).obj N : Type u) ≃ₐ[S]
      S ⊗[R] (N : Type u) :=
    { toFun := e.hom.right
      invFun := e.inv.right
      left_inv := fun x ↦ ConcreteCategory.congr_hom
        (congrArg Under.Hom.right (e.hom_inv_id)) x
      right_inv := fun x ↦ ConcreteCategory.congr_hom
        (congrArg Under.Hom.right (e.inv_hom_id)) x
      map_add' := e.hom.right.hom.map_add
      map_mul' := e.hom.right.hom.map_mul
      commutes' := fun s ↦ by
        change e.hom.right.hom (((Under.pushout g).obj N).hom.hom s) =
          (CommRingCat.mkUnder S (S ⊗[R] (N : Type u))).hom.hom s
        exact ConcreteCategory.congr_hom (Under.w e.hom) s }
  exact eAlg.toLinearEquiv.toModuleIso

lemma tensorProdObjIsoPushoutObj_hom_one_tmul
    {R S : CommRingCat.{u}} [Algebra R S] (N : Under R) (n : N) :
    (tensorProdObjIsoPushoutObj S N).hom.right.hom
        ((1 : S) ⊗ₜ[R] n) =
      (pushout.inl N.hom (CommRingCat.ofHom (algebraMap R S))).hom n := by
  apply (ConcreteCategory.bijective_of_isIso
    (tensorProdObjIsoPushoutObj S N).inv.right).injective
  have hcancelMorph : (tensorProdObjIsoPushoutObj S N).hom.right ≫
      (tensorProdObjIsoPushoutObj S N).inv.right = 𝟙 _ := by
    simpa only [Under.comp_right, Under.id_right] using
      congrArg Under.Hom.right
        ((tensorProdObjIsoPushoutObj S N).hom_inv_id)
  have hcancel := ConcreteCategory.congr_hom hcancelMorph
    ((1 : S) ⊗ₜ[R] n)
  have hinvMorph :=
    pushout_inl_tensorProdObjIsoPushoutObj_inv_right (R := R) (S := S) N
  have hinv := ConcreteCategory.congr_hom hinvMorph n
  exact hcancel.trans hinv.symm

lemma tensorProdObjIsoPushoutObj_inv_inl_apply
    {R S : CommRingCat.{u}} [Algebra R S] (N : Under R) (n : N) :
    (tensorProdObjIsoPushoutObj S N).inv.right.hom
        ((pushout.inl N.hom
          (CommRingCat.ofHom (algebraMap R S))).hom n) =
      (1 : S) ⊗ₜ[R] n := by
  have h := pushout_inl_tensorProdObjIsoPushoutObj_inv_right
    (R := R) (S := S) N
  exact ConcreteCategory.congr_hom h n

lemma pushoutComp_hom_inl {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (N : Under R) :
    pushout.inl N.hom (f ≫ g) ≫
        ((Under.pushoutComp f g).hom.app N).right =
      pushout.inl N.hom f ≫
        pushout.inl ((Under.pushout f).obj N).hom g := by
  simp [Under.pushoutComp]

lemma pushoutForgetModuleIso_inv_one_tmul
    {R S : CommRingCat.{u}} (g : R ⟶ S) (N : Under R) (n : N) :
    (pushoutForgetModuleIso g N).inv.hom
        ((1 : S) ⊗ₜ[R,g.hom] n) =
      (pushout.inl N.hom g).hom n := by
  letI : Algebra R S := g.hom.toAlgebra
  change (tensorProdObjIsoPushoutObj S N).hom.right.hom
      ((1 : S) ⊗ₜ[R] n) = _
  have h := tensorProdObjIsoPushoutObj_hom_one_tmul
    (R := R) (S := S) N n
  exact h

lemma pushoutForgetModuleIso_hom_inl_apply
    {R S : CommRingCat.{u}} (g : R ⟶ S) (N : Under R) (n : N) :
    (pushoutForgetModuleIso g N).hom.hom
        ((pushout.inl N.hom g).hom n) =
      (1 : S) ⊗ₜ[R,g.hom] n := by
  letI : Algebra R S := g.hom.toAlgebra
  change (tensorProdObjIsoPushoutObj S N).inv.right.hom
      ((pushout.inl N.hom g).hom n) = _
  have h := tensorProdObjIsoPushoutObj_inv_inl_apply
    (R := R) (S := S) N n
  exact h

/-- The pushout/extension comparison, naturally in the algebra. -/
def pushoutForgetModuleNatIso {R S : CommRingCat.{u}} (g : R ⟶ S) :
    Under.pushout g ⋙ underForgetModule S ≅
      underForgetModule R ⋙ ModuleCat.extendScalars g.hom := by
  letI : Algebra R S := g.hom.toAlgebra
  refine NatIso.ofComponents (pushoutForgetModuleIso g) ?_
  intro M N h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    ((tensorProdIsoPushout R S).inv.app N).right.hom
        (((Under.pushout g).map h).right.hom x) =
      (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom h))
        (((tensorProdIsoPushout R S).inv.app M).right.hom x)
  have hn := (tensorProdIsoPushout R S).inv.naturality h
  have hn' := congrArg (fun k ↦ k.right.hom x) hn
  exact hn'

lemma extendScalarsId_hom_eq_lmul (R : CommRingCat.{u}) (N : Under R)
    (x : R ⊗[R] (N : Type u)) :
    (ModuleCat.extendScalarsId R).hom.app (ModuleCat.of R N) x =
      Algebra.TensorProduct.lift (Algebra.ofId R N) (AlgHom.id R N)
        (fun _ _ ↦ Commute.all _ _) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  | tmul r n =>
      calc
        _ = (ModuleCat.extendScalarsId R).hom.app (ModuleCat.of R N)
            (r • ((1 : R) ⊗ₜ[R] n)) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul]
        _ = r • n := by
          rw [map_smul, ModuleCat.extendScalarsId_hom_app_one_tmul]
        _ = _ := by
          rw [Algebra.TensorProduct.lift_tmul]
          simp [Algebra.smul_def]

def tensorIdEval (R : CommRingCat.{u}) (N : Under R) :
    CommRingCat.mkUnder R (R ⊗[R] (N : Type u)) ⟶ N :=
  (Algebra.TensorProduct.lift (Algebra.ofId R N) (AlgHom.id R N)
    (fun _ _ ↦ Commute.all _ _)).toUnder

lemma pushoutId_hom_inl (R : CommRingCat.{u}) (N : Under R) :
    pushout.inl N.hom (𝟙 R) ≫
        ((Under.pushoutId (X := R)).hom.app N).right = (𝟙 N.right) := by
  simp [Under.pushoutId]

lemma pushoutId_hom_inr (R : CommRingCat.{u}) (N : Under R) :
    pushout.inr N.hom (𝟙 R) ≫
        ((Under.pushoutId (X := R)).hom.app N).right = N.hom := by
  exact Under.w ((Under.pushoutId (X := R)).hom.app N)

lemma tensorProdIsoPushout_inv_comp_tensorIdEval
    (R : CommRingCat.{u}) (N : Under R) :
    (tensorProdObjIsoPushoutObj R N).inv ≫ tensorIdEval R N =
      (Under.pushoutId (X := R)).hom.app N := by
  ext : 1
  apply pushout.hom_ext
  · calc
      pushout.inl N.hom (𝟙 R) ≫
          ((tensorProdObjIsoPushoutObj R N).inv ≫
            tensorIdEval R N).right =
        pushout.inl N.hom (𝟙 R) ≫
          (tensorProdObjIsoPushoutObj R N).inv.right ≫
            (tensorIdEval R N).right := rfl
      _ = CommRingCat.ofHom
            Algebra.TensorProduct.includeRight.toRingHom ≫
          (tensorIdEval R N).right := by
        have hid : CommRingCat.ofHom (algebraMap R R) = (𝟙 R) := by
          apply CommRingCat.hom_ext
          rfl
        have hinl :=
          pushout_inl_tensorProdObjIsoPushoutObj_inv_right (R := R) (S := R) N
        have htail := congrArg (fun z ↦ z ≫ (tensorIdEval R N).right) hinl
        apply CommRingCat.hom_ext
        ext n
        exact ConcreteCategory.congr_hom htail n
      _ = 𝟙 N.right := by
        apply CommRingCat.hom_ext
        ext n
        change Algebra.TensorProduct.lift (Algebra.ofId R N)
          (AlgHom.id R N) (fun _ _ ↦ Commute.all _ _)
            ((1 : R) ⊗ₜ[R] n) = n
        rw [Algebra.TensorProduct.lift_tmul]
        simp
      _ = pushout.inl N.hom (𝟙 R) ≫
          ((Under.pushoutId (X := R)).hom.app N).right :=
        (pushoutId_hom_inl R N).symm
  · calc
      pushout.inr N.hom (𝟙 R) ≫
          ((tensorProdObjIsoPushoutObj R N).inv ≫
            tensorIdEval R N).right =
        pushout.inr N.hom (𝟙 R) ≫
          (tensorProdObjIsoPushoutObj R N).inv.right ≫
            (tensorIdEval R N).right := rfl
      _ = CommRingCat.ofHom
            Algebra.TensorProduct.includeLeftRingHom ≫
          (tensorIdEval R N).right := by
        have hid : CommRingCat.ofHom (algebraMap R R) = (𝟙 R) := by
          apply CommRingCat.hom_ext
          rfl
        have hinr :=
          pushout_inr_tensorProdObjIsoPushoutObj_inv_right (R := R) (S := R) N
        have htail := congrArg (fun z ↦ z ≫ (tensorIdEval R N).right) hinr
        apply CommRingCat.hom_ext
        ext r
        exact ConcreteCategory.congr_hom htail r
      _ = N.hom := by
        apply CommRingCat.hom_ext
        ext r
        change Algebra.TensorProduct.lift (Algebra.ofId R N)
          (AlgHom.id R N) (fun _ _ ↦ Commute.all _ _)
            (r ⊗ₜ[R] (1 : N)) = N.hom.hom r
        rw [Algebra.TensorProduct.lift_tmul]
        simp only [Algebra.ofId_apply, AlgHom.id_apply, mul_one,
          RingHom.algebraMap_toAlgebra]
      _ = pushout.inr N.hom (𝟙 R) ≫
          ((Under.pushoutId (X := R)).hom.app N).right :=
        (pushoutId_hom_inr R N).symm

lemma pushoutForgetModule_comp_apply {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (N : Under R)
    (x : ((Under.pushout (f ≫ g)).obj N : Type u)) :
    (ModuleCat.extendScalarsComp f.hom g.hom).hom.app
        (ModuleCat.of R N)
        ((pushoutForgetModuleIso (f ≫ g) N).hom x) =
      ((ModuleCat.extendScalars g.hom).map
          (pushoutForgetModuleIso f N).hom)
        ((pushoutForgetModuleIso g ((Under.pushout f).obj N)).hom
          (((Under.pushoutComp f g).hom.app N).right.hom x)) := by
  letI : Algebra R S := f.hom.toAlgebra
  letI : Algebra S T := g.hom.toAlgebra
  letI : Algebra R T := (g.hom.comp f.hom).toAlgebra
  let e := pushoutForgetModuleIso (f ≫ g) N
  let y := e.hom x
  have hy : e.inv y = x := by
    exact ConcreteCategory.congr_hom (e.hom_inv_id) x
  rw [← hy]
  change ((ModuleCat.extendScalars (g.hom.comp f.hom)).obj
    (ModuleCat.of R N) : Type u) at y
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [Functor.comp_obj, Under.pushout_obj, Under.mk_right,
        hom_comp, Iso.inv_hom_id_apply, Under.mk_hom, e]
      erw [(pushoutForgetModuleIso (f ≫ g) N).inv.hom.map_zero]
      erw [((Under.pushoutComp f g).hom.app N).right.hom.map_zero]
      erw [(pushoutForgetModuleIso g ((Under.pushout f).obj N)).hom.hom.map_zero]
      erw [((ModuleCat.extendScalars g.hom).map
        (pushoutForgetModuleIso f N).hom).hom.map_zero]
  | add y z hy hz => simpa only [map_add] using congrArg₂ (· + ·) hy hz
  | tmul t n =>
      change T at t
      change (N : Type u) at n
      have ht :
          (t ⊗ₜ[R,g.hom.comp f.hom] n :
              (ModuleCat.extendScalars (g.hom.comp f.hom)).obj
                (ModuleCat.of R N)) =
            t • ((1 : T) ⊗ₜ[R,g.hom.comp f.hom] n) :=
        TensorProduct.tmul_eq_smul_one_tmul t n
      erw [ht]
      simp only [map_smul]
      have hk (z : ((Under.pushout (f ≫ g)).obj N : Type u)) :
          ((Under.pushoutComp f g).hom.app N).right.hom (t • z) =
            t • ((Under.pushoutComp f g).hom.app N).right.hom z :=
        (CommRingCat.toAlgHom ((Under.pushoutComp f g).hom.app N)).toLinearMap.map_smul t z
      rw [hk]
      simp only [map_smul]
      congr 1
      erw [pushoutForgetModuleIso_inv_one_tmul (f ≫ g) N n]
      rw [pushoutForgetModuleIso_hom_inl_apply (f ≫ g) N n]
      rw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
      have hc := ConcreteCategory.congr_hom
        (pushoutComp_hom_inl f g N) n
      simp only [ConcreteCategory.comp_apply] at hc
      erw [hc]
      erw [pushoutForgetModuleIso_hom_inl_apply g
        ((Under.pushout f).obj N) ((pushout.inl N.hom f).hom n)]
      erw [ModuleCat.ExtendScalars.map_tmul]
      erw [pushoutForgetModuleIso_hom_inl_apply f N n]

/-- Forgetting multiplication commutes pseudonaturally with base change. -/
def underForgetModuleStrongTrans :
    Pseudofunctor.StrongTrans underPushoutPseudofunctorOpOp.{u}
      ModuleCat.extendScalarsPseudofunctorOpOp.{u} where
  app R := Cat.Hom.ofFunctor (underForgetModule R.as.unop.unop)
  naturality f := Cat.Hom.isoMk (pushoutForgetModuleNatIso f.as.unop.unop)
  naturality_naturality := by
    intro a b f g η
    have hfg := LocallyDiscrete.eq_of_hom η
    subst g
    apply Cat.Hom₂.ext
    ext N
    rfl
  naturality_id := by
    intro R
    apply Cat.Hom₂.ext
    ext N
    change Under R.as.unop.unop at N
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [pushoutForgetModuleNatIso, pushoutForgetModuleIso,
      underForgetModule]
    let R₀ := R.as.unop.unop
    let y : R₀ ⊗[R₀] (N : Type u) :=
      (tensorProdObjIsoPushoutObj R₀ N).inv.right.hom x
    have hext := extendScalarsId_hom_eq_lmul R₀ N y
    have h := congrArg (fun k ↦ k.right.hom x)
      (tensorProdIsoPushout_inv_comp_tensorIdEval
        R₀ N)
    exact hext.trans h
  naturality_comp := by
    intro R S T f g
    apply Cat.Hom₂.ext
    ext N
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [pushoutForgetModuleNatIso, pushoutForgetModuleIso,
      underForgetModule]
    exact pushoutForgetModule_comp_apply f.as.unop.unop
      g.as.unop.unop N x

/-- Forget multiplication in ordinary affine commutative-algebra descent
data. -/
def AffineStandardDescentData.underlyingModule
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    ModuleCat.AffineStandardDescentData f.hom :=
  (Pseudofunctor.mapDescentData underForgetModuleStrongTrans
    (fun (_ : Unit) ↦ f.op)).obj D

@[simp]
lemma AffineStandardDescentData.underlyingModule_obj
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    (D.underlyingModule f).obj default =
      ModuleCat.of B (D.obj default).right := by
  rfl

/-- The module cancellation is the underlying map of the algebra
cancellation after the pushout/tensor-product comparison. -/
lemma overlapCancel_forget_apply {A B : CommRingCat.{u}}
    (f : A ⟶ B) (N : Under B) :
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ∀ y : ((Under.pushout (CommRingCat.ofHom r)).obj N : Type u),
      (ModuleCat.overlapCancel f.hom
        (ModuleCat.of B N.right)).hom
          ((pushoutForgetModuleIso (CommRingCat.ofHom r) N).hom.hom y) =
        (overlapCancelAlgIso f N).hom.right.hom y := by
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  let C := B ⊗[A] B
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  dsimp only
  intro y
  rfl

/-- The module coaction obtained by forgetting multiplication is the
underlying linear map of the multiplicative algebra coaction. -/
lemma AffineStandardDescentData.underlyingModule_coaction_apply
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    let N : Under B := D.obj default
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    ∀ n : N,
      ModuleCat.overlapHomEquiv f.hom
          ((D.underlyingModule f).obj default)
          ((D.underlyingModule f).overlapHom f.hom) n =
        D.coaction f n := by
  letI : Algebra A B := f.hom.toAlgebra
  let N : Under B := D.obj default
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  dsimp only
  intro n
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  rw [ModuleCat.overlapHomEquiv_apply]
  dsimp [underlyingModule,
    ModuleCat.AffineStandardDescentData.overlapHom,
    Pseudofunctor.mapDescentData,
    Pseudofunctor.mapDescentDataObj,
    Pseudofunctor.mapDescentDataObjHom,
    underForgetModuleStrongTrans]
  change (ModuleCat.overlapCancel f.hom
      (ModuleCat.of B N.right)).hom
        ((pushoutForgetModuleIso (CommRingCat.ofHom r) N).hom.hom
          ((D.overlapHom f).right.hom
            ((pushoutForgetModuleIso
              (CommRingCat.ofHom l) N).inv.hom
                ((1 : C) ⊗ₜ[B,l] n)))) = D.coaction f n
  rw [pushoutForgetModuleIso_inv_one_tmul]
  rw [overlapCancel_forget_apply]
  exact (overlapCoaction_apply f N (D.overlapHom f) n).symm

set_option maxHeartbeats 1000000 in
-- The final normalization crosses both pseudofunctor coherences and tensor products.
/-- The cocycle identity for ordinary affine algebra descent gives the
pointwise coassociativity identity for its multiplicative coaction. -/
lemma AffineStandardDescentData.coaction_coassoc
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    let N : Under B := D.obj default
    letI : Algebra B N := RingHom.toAlgebra N.hom.hom
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
    ∀ d : N,
      Algebra.TensorProduct.map (AlgHom.id B B)
          ((D.coaction f).restrictScalars A) (D.coaction f d) =
        Algebra.TensorProduct.map (AlgHom.id B B)
          (Algebra.TensorProduct.includeRight
            (R := A) (A := B) (B := N)) (D.coaction f d) := by
  letI : Algebra A B := f.hom.toAlgebra
  let N : Under B := D.obj default
  letI : Algebra B N := RingHom.toAlgebra N.hom.hom
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro d
  let E := D.underlyingModule f
  let a := ModuleCat.overlapHomEquiv f.hom
    (E.obj default) (E.overlapHom f.hom)
  have ha : a = ModuleCat.ofHom (D.coaction f).toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    exact D.underlyingModule_coaction_apply f n
  have h := ModuleCat.AffineStandardDescentData.coaction_coassoc f.hom E
  have hd := congrArg (fun k ↦ k.hom d) h
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] at hd
  change _ = _ at hd
  rw [D.underlyingModule_coaction_apply f d] at hd
  change ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.δ.app
      (E.obj default)).hom (D.coaction f d) =
    ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.map a).hom
      (D.coaction f d) at hd
  rw [ha] at hd
  change Algebra.TensorProduct.map (AlgHom.id B B)
      (Algebra.TensorProduct.includeRight
        (R := A) (A := B) (B := N)) (D.coaction f d) =
    Algebra.TensorProduct.map (AlgHom.id B B)
      ((D.coaction f).restrictScalars A) (D.coaction f d) at hd
  exact hd.symm

/-- The identity transition of ordinary affine algebra descent gives the
pointwise counit identity for its multiplicative coaction. -/
lemma AffineStandardDescentData.coaction_counit
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    let N : Under B := D.obj default
    letI : Algebra B N := RingHom.toAlgebra N.hom.hom
    letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
    ∀ d : N,
      Algebra.TensorProduct.lift (Algebra.ofId B N)
          (AlgHom.id A N) (fun _ _ ↦ Commute.all _ _)
          (D.coaction f d) = d := by
  letI : Algebra A B := f.hom.toAlgebra
  let N : Under B := D.obj default
  letI : Algebra B N := RingHom.toAlgebra N.hom.hom
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro d
  let E := D.underlyingModule f
  let a := ModuleCat.overlapHomEquiv f.hom
    (E.obj default) (E.overlapHom f.hom)
  have ha : a = ModuleCat.ofHom (D.coaction f).toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    exact D.underlyingModule_coaction_apply f n
  have h := ModuleCat.AffineStandardDescentData.coaction_counit f.hom E
  change a ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).counit.app
      (E.obj default) = 𝟙 _ at h
  rw [ha] at h
  have hd := congrArg (fun k ↦ k.hom d) h
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.hom_id] at hd
  change Algebra.TensorProduct.lift (Algebra.ofId B N)
      (AlgHom.id A N) (fun _ _ ↦ Commute.all _ _)
        (D.coaction f d) = d at hd
  exact hd

/-- Convert ordinary affine commutative-algebra descent data into the
multiplicative coaction used by effective faithfully flat descent. -/
noncomputable def AffineStandardDescentData.toCommAlgebraDescentData
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.hom.toAlgebra
    Algebra.CommAlgebraDescentData A B := by
  letI : Algebra A B := f.hom.toAlgebra
  let N : Under B := D.obj default
  letI : Algebra B N := RingHom.toAlgebra N.hom.hom
  letI : Algebra A N := (N.hom.hom.comp f.hom).toAlgebra
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_eq' rfl
  exact
    { carrier := N
      commRingD := inferInstance
      algebraBD := inferInstance
      algebraAD := inferInstance
      towerABD := inferInstance
      coaction := D.coaction f
      counit := D.coaction_counit f
      coassoc := D.coaction_coassoc f }

end

end CommRingCat
