module

public import StacksAndModuli.API.ModuleDescentData.TripleFormulas

/-!
# Effective affine descent for modules

An ordinary singleton descent datum for extension of scalars determines a Beck
coalgebra.  The cocycle identity becomes the coalgebra coassociativity identity
after the explicit tensor-cube comparison developed in the imported API.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The cocycle of an ordinary singleton affine descent datum is exactly the
coassociativity law for its associated extension/restriction coalgebra. -/
lemma AffineStandardDescentData.coaction_coassoc
    (D : AffineStandardDescentData f) :
    overlapHomEquiv f (D.obj default) (D.overlapHom f) ≫
      (extendRestrictScalarsAdj f).toComonad.δ.app (D.obj default) =
    overlapHomEquiv f (D.obj default) (D.overlapHom f) ≫
      (extendRestrictScalarsAdj f).toComonad.map
        (overlapHomEquiv f (D.obj default) (D.overlapHom f)) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let T := B ⊗[A] C
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₂ : B →+* T := tR.comp cL
  let i₃ : B →+* T := tR.comp cR
  let cLA : B →ₐ[A] C := Algebra.TensorProduct.includeLeft
  let cRA : B →ₐ[A] C := Algebra.TensorProduct.includeRight
  let j₁₂ : C →+* T :=
    (Algebra.TensorProduct.map (AlgHom.id A B) cLA).toRingHom
  let j₂₃ : C →+* T := tR
  let j₁₃ : C →+* T :=
    (Algebra.TensorProduct.map (AlgHom.id A B) cRA).toRingHom
  let q : op (CommRingCat.of T) ⟶ op (CommRingCat.of A) :=
    (CommRingCat.ofHom (algebraMap A T)).op
  have h₁ : (CommRingCat.ofHom i₁).op ≫ (CommRingCat.ofHom f).op = q := by
    calc
      _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom i₁).op := rfl
      _ = (CommRingCat.ofHom (i₁.comp f)).op := rfl
      _ = _ := by congr 2
  have h₂ : (CommRingCat.ofHom i₂).op ≫ (CommRingCat.ofHom f).op = q := by
    calc
      _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom i₂).op := rfl
      _ = (CommRingCat.ofHom (i₂.comp f)).op := rfl
      _ = _ := by
        congr 2
        ext a
        change Algebra.TensorProduct.includeRight (algebraMap A C a) = algebraMap A T a
        exact Algebra.TensorProduct.includeRight.commutes a
  have h₃ : (CommRingCat.ofHom i₃).op ≫ (CommRingCat.ofHom f).op = q := by
    calc
      _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom i₃).op := rfl
      _ = (CommRingCat.ofHom (i₃.comp f)).op := rfl
      _ = _ := by
        congr 2
        ext a
        change Algebra.TensorProduct.includeRight
          (Algebra.TensorProduct.includeRight (f a)) = algebraMap A T a
        have hi : (Algebra.TensorProduct.includeRight : B →ₐ[A] C) (f a) =
            algebraMap A C a := by
          change Algebra.TensorProduct.includeRight (algebraMap A B a) = algebraMap A C a
          exact Algebra.TensorProduct.includeRight.commutes a
        rw [hi]
        exact Algebra.TensorProduct.includeRight.commutes a
  have hcomp := D.hom_comp q (i₁ := default) (i₂ := default) (i₃ := default)
    (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₂).op
    (CommRingCat.ofHom i₃).op h₁ h₂ h₃
  have hj₁₂l : j₁₂.comp cL = i₁ := by
    ext b
    change (Algebra.TensorProduct.map (AlgHom.id A B) cLA)
      (b ⊗ₜ[A] (1 : B)) = b ⊗ₜ[A] (1 : C)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hj₁₂r : j₁₂.comp cR = i₂ := by
    ext b
    change (Algebra.TensorProduct.map (AlgHom.id A B) cLA)
      ((1 : B) ⊗ₜ[A] b) = (1 : B) ⊗ₜ[A] cLA b
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hj₂₃l : j₂₃.comp cL = i₂ := by rfl
  have hj₂₃r : j₂₃.comp cR = i₃ := by rfl
  have hj₁₃l : j₁₃.comp cL = i₁ := by
    ext b
    change (Algebra.TensorProduct.map (AlgHom.id A B) cRA)
      (b ⊗ₜ[A] (1 : B)) = b ⊗ₜ[A] (1 : C)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hj₁₃r : j₁₃.comp cR = i₃ := by
    ext b
    change (Algebra.TensorProduct.map (AlgHom.id A B) cRA)
      ((1 : B) ⊗ₜ[A] b) = (1 : B) ⊗ₜ[A] cRA b
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let qC : op (CommRingCat.of C) ⟶ op (CommRingCat.of A) :=
    (CommRingCat.ofHom (algebraMap A C)).op
  let lOp : op (CommRingCat.of C) ⟶ op (CommRingCat.of B) :=
    (CommRingCat.ofHom cL).op
  let rOp : op (CommRingCat.of C) ⟶ op (CommRingCat.of B) :=
    (CommRingCat.ofHom cR).op
  let g₁₂ : op (CommRingCat.of T) ⟶ op (CommRingCat.of C) :=
    (CommRingCat.ofHom j₁₂).op
  let g₂₃ : op (CommRingCat.of T) ⟶ op (CommRingCat.of C) :=
    (CommRingCat.ofHom j₂₃).op
  let g₁₃ : op (CommRingCat.of T) ⟶ op (CommRingCat.of C) :=
    (CommRingCat.ofHom j₁₃).op
  have hCl : lOp ≫ (CommRingCat.ofHom f).op = qC := by
    calc
      _ = (CommRingCat.ofHom (cL.comp f)).op := rfl
      _ = _ := by congr 2
  have hCr : rOp ≫ (CommRingCat.ofHom f).op = qC := by
    calc
      _ = (CommRingCat.ofHom (cR.comp f)).op := rfl
      _ = (CommRingCat.ofHom (cL.comp f)).op := by
        congr 2
        simpa only [show f = algebraMap A B from rfl] using
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
      _ = _ := by congr 2
  have hg₁₂q : g₁₂ ≫ qC = q := by
    change (CommRingCat.ofHom (j₁₂.comp (algebraMap A C))).op =
      (CommRingCat.ofHom (algebraMap A T)).op
    congr 2
  have hg₂₃q : g₂₃ ≫ qC = q := by
    change (CommRingCat.ofHom (j₂₃.comp (algebraMap A C))).op =
      (CommRingCat.ofHom (algebraMap A T)).op
    congr 2
    ext a
    exact (Algebra.TensorProduct.includeRight : C →ₐ[A] T).commutes a
  have hg₁₃q : g₁₃ ≫ qC = q := by
    change (CommRingCat.ofHom (j₁₃.comp (algebraMap A C))).op =
      (CommRingCat.ofHom (algebraMap A T)).op
    congr 2
  have hg₁₂l : g₁₂ ≫ lOp = (CommRingCat.ofHom i₁).op := by
    change (CommRingCat.ofHom (j₁₂.comp cL)).op = _
    rw [hj₁₂l]
  have hg₁₂r : g₁₂ ≫ rOp = (CommRingCat.ofHom i₂).op := by
    change (CommRingCat.ofHom (j₁₂.comp cR)).op = _
    rw [hj₁₂r]
  have hg₂₃l : g₂₃ ≫ lOp = (CommRingCat.ofHom i₂).op := by
    change (CommRingCat.ofHom (j₂₃.comp cL)).op = _
    rw [hj₂₃l]
  have hg₂₃r : g₂₃ ≫ rOp = (CommRingCat.ofHom i₃).op := by
    change (CommRingCat.ofHom (j₂₃.comp cR)).op = _
    rw [hj₂₃r]
  have hg₁₃l : g₁₃ ≫ lOp = (CommRingCat.ofHom i₁).op := by
    change (CommRingCat.ofHom (j₁₃.comp cL)).op = _
    rw [hj₁₃l]
  have hg₁₃r : g₁₃ ≫ rOp = (CommRingCat.ofHom i₃).op := by
    change (CommRingCat.ofHom (j₁₃.comp cR)).op = _
    rw [hj₁₃r]
  have hp₁₂ : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := lOp) (f₂ := rOp)
      (D.overlapHom f) g₁₂ (CommRingCat.ofHom i₁).op
        (CommRingCat.ofHom i₂).op hg₁₂l hg₁₂r =
      D.hom q (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₂).op h₁ h₂ := by
    exact D.pullHom_hom g₁₂ qC q hg₁₂q lOp rOp hCl hCr
      (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₂).op hg₁₂l hg₁₂r
  have hp₂₃ : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := lOp) (f₂ := rOp)
      (D.overlapHom f) g₂₃ (CommRingCat.ofHom i₂).op
        (CommRingCat.ofHom i₃).op hg₂₃l hg₂₃r =
      D.hom q (CommRingCat.ofHom i₂).op (CommRingCat.ofHom i₃).op h₂ h₃ := by
    exact D.pullHom_hom g₂₃ qC q hg₂₃q lOp rOp hCl hCr
      (CommRingCat.ofHom i₂).op (CommRingCat.ofHom i₃).op hg₂₃l hg₂₃r
  have hp₁₃ : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := lOp) (f₂ := rOp)
      (D.overlapHom f) g₁₃ (CommRingCat.ofHom i₁).op
        (CommRingCat.ofHom i₃).op hg₁₃l hg₁₃r =
      D.hom q (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₃).op h₁ h₃ := by
    exact D.pullHom_hom g₁₃ qC q hg₁₃q lOp rOp hCl hCr
      (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₃).op hg₁₃l hg₁₃r
  have hpcomp :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
          (D.overlapHom f) g₁₂ (CommRingCat.ofHom i₁).op
            (CommRingCat.ofHom i₂).op hg₁₂l hg₁₂r ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
          (D.overlapHom f) g₂₃ (CommRingCat.ofHom i₂).op
            (CommRingCat.ofHom i₃).op hg₂₃l hg₂₃r =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
          (D.overlapHom f) g₁₃ (CommRingCat.ofHom i₁).op
            (CommRingCat.ofHom i₃).op hg₁₃l hg₁₃r := by
    rw [hp₁₂, hp₂₃, hp₁₃]
    exact hcomp
  let N : ModuleCat B := D.obj default
  let θ := D.overlapHom f
  let a : N ⟶ (extendScalars f).obj ((restrictScalars f).obj N) :=
    overlapHomEquiv f N θ
  let p₁₂ : (extendScalars i₁).obj N ⟶ (extendScalars i₂).obj N :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
      θ g₁₂ (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₂).op
        hg₁₂l hg₁₂r
  let p₂₃ : (extendScalars i₂).obj N ⟶ (extendScalars i₃).obj N :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
      θ g₂₃ (CommRingCat.ofHom i₂).op (CommRingCat.ofHom i₃).op
        hg₂₃l hg₂₃r
  let p₁₃ : (extendScalars i₁).obj N ⟶ (extendScalars i₃).obj N :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp) (f₁ := lOp) (f₂ := rOp)
      θ g₁₃ (CommRingCat.ofHom i₁).op (CommRingCat.ofHom i₃).op
        hg₁₃l hg₁₃r
  change a ≫ (extendRestrictScalarsAdj f).toComonad.δ.app N =
    a ≫ (extendRestrictScalarsAdj f).toComonad.map a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  have hp₁₂unit : p₁₂.hom ((1 : T) ⊗ₜ[B,i₁] n) =
      (extendScalarsComp cR j₁₂).inv.app N
        ((1 : T) ⊗ₜ[C,j₁₂] (θ ((1 : C) ⊗ₜ[B,cL] n))) := by
    dsimp only [p₁₂, θ, lOp, rOp, g₁₂, i₁, i₂]
    exact pullHom_apply_unit cL cR j₁₂ N (D.overlapHom f) n
  have hp₁₃unit : p₁₃.hom ((1 : T) ⊗ₜ[B,i₁] n) =
      (extendScalarsComp cR j₁₃).inv.app N
        ((1 : T) ⊗ₜ[C,j₁₃] (θ ((1 : C) ⊗ₜ[B,cL] n))) := by
    dsimp only [p₁₃, θ, lOp, rOp, g₁₃, i₁, i₃]
    exact pullHom_apply_unit cL cR j₁₃ N (D.overlapHom f) n
  have hfaces := congrArg (fun k => (tripleCancel f N).hom
      (k.hom ((1 : T) ⊗ₜ[B,i₁] n))) hpcomp
  change (tripleCancel f N).hom (p₂₃.hom (p₁₂.hom
      ((1 : T) ⊗ₜ[B,i₁] n))) =
    (tripleCancel f N).hom (p₁₃.hom
      ((1 : T) ⊗ₜ[B,i₁] n)) at hfaces
  rw [hp₁₂unit] at hfaces
  rw [tripleCancel_pull₂₃_after_j₁₂ f N θ] at hfaces
  rw [hp₁₃unit] at hfaces
  rw [tripleCancel_after_j₁₃ f N] at hfaces
  have ha : a n = (overlapCancel f N).hom
      (θ ((1 : C) ⊗ₜ[B,cL] n)) := overlapHomEquiv_apply f N θ n
  change (extendRestrictScalarsAdj f).toComonad.δ.app N (a n) =
    (extendRestrictScalarsAdj f).toComonad.map a (a n)
  rw [ha]
  exact hfaces.symm

/-- The Beck coalgebra canonically attached to an ordinary singleton affine
descent datum. -/
noncomputable def AffineStandardDescentData.toCoalgebraObj
    (D : AffineStandardDescentData f) :
    (extendRestrictScalarsAdj f).toComonad.Coalgebra where
  A := D.obj default
  a := overlapHomEquiv f (D.obj default) (D.overlapHom f)
  counit := D.coaction_counit f
  coassoc := D.coaction_coassoc f

/-- A two-object variant of `overlapHomEquiv`, used to transport morphisms of
ordinary affine descent data to morphisms of Beck coalgebras. -/
noncomputable def overlapHomEquiv₂ (M N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (((extendScalars l).obj M ⟶ (extendScalars r).obj N) ≃
      (M ⟶ (extendScalars f).obj ((restrictScalars f).obj N))) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  exact ((extendRestrictScalarsAdj l).homEquiv M ((extendScalars r).obj N)).trans
    (CategoryTheory.Iso.homCongr (Iso.refl M) (overlapCancel f N))

@[simp]
lemma overlapHomEquiv₂_self (N : ModuleCat B) :
    overlapHomEquiv₂ f N N = overlapHomEquiv f N := by
  rfl

/-- Naturality of overlap cancellation with respect to a module morphism. -/
lemma overlapCancel_naturality (M N : ModuleCat B) (h : M ⟶ N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (restrictScalars l).map ((extendScalars r).map h) ≫
        (overlapCancel f N).hom =
      (overlapCancel f M).hom ≫
        (extendRestrictScalarsAdj f).toComonad.map h := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simpa only [map_add] using congrArg₂ (.+.) hy hy'
  | tmul c m =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | add c c' hc hc' =>
          simpa only [add_tmul, map_add] using congrArg₂ (.+.) hc hc'
      | tmul b₁ b₂ =>
          change (overlapCancel f N).hom
              ((extendScalars r).map h
                ((b₁ ⊗ₜ[A] b₂ : C) ⊗ₜ[B,r] m)) =
            (extendRestrictScalarsAdj f).toComonad.map h
              ((overlapCancel f M).hom
                ((b₁ ⊗ₜ[A] b₂ : C) ⊗ₜ[B,r] m))
          rw [ExtendScalars.map_tmul, overlapCancel_tmul_tmul,
            overlapCancel_tmul_tmul]
          change _ = (extendScalars f).map ((restrictScalars f).map h)
            (b₁ ⊗ₜ[A]
              (show (restrictScalars f).obj M from b₂ • m))
          rw [ExtendScalars.map_tmul]
          congr 1
          change b₂ • h m = h (b₂ • m)
          exact (h.hom.map_smul b₂ m).symm

lemma overlapHomEquiv₂_comp_left (M N : ModuleCat B) (h : M ⟶ N)
    (θ :
      letI : Algebra A B := f.toAlgebra
      let C := B ⊗[A] B
      let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (extendScalars l).obj N ⟶ (extendScalars r).obj N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    overlapHomEquiv₂ f M N ((extendScalars l).map h ≫ θ) =
      h ≫ overlapHomEquiv f N θ := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  simp only [overlapHomEquiv₂, overlapHomEquiv, Equiv.trans_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rw [(extendRestrictScalarsAdj
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B)).homEquiv_naturality_left]
  rfl

lemma overlapHomEquiv₂_comp_right (M N : ModuleCat B) (h : M ⟶ N)
    (θ :
      letI : Algebra A B := f.toAlgebra
      let C := B ⊗[A] B
      let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (extendScalars l).obj M ⟶ (extendScalars r).obj M) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    overlapHomEquiv₂ f M N (θ ≫ (extendScalars r).map h) =
      overlapHomEquiv f M θ ≫
        (extendRestrictScalarsAdj f).toComonad.map h := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  simp only [overlapHomEquiv₂, overlapHomEquiv, Equiv.trans_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rw [(extendRestrictScalarsAdj
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B)).homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [overlapCancel_naturality f M N h]

/-- The kernel-pair commutativity condition is precisely the Beck-coalgebra
commutativity condition under `overlapHomEquiv`. -/
lemma overlap_comm_iff_coaction_comm (M N : ModuleCat B) (h : M ⟶ N)
    (θM :
      letI : Algebra A B := f.toAlgebra
      let C := B ⊗[A] B
      let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (extendScalars l).obj M ⟶ (extendScalars r).obj M)
    (θN :
      letI : Algebra A B := f.toAlgebra
      let C := B ⊗[A] B
      let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (extendScalars l).obj N ⟶ (extendScalars r).obj N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ((extendScalars l).map h ≫ θN = θM ≫ (extendScalars r).map h) ↔
      overlapHomEquiv f M θM ≫
          (extendRestrictScalarsAdj f).toComonad.map h =
        h ≫ overlapHomEquiv f N θN := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  constructor
  · intro w
    have hw := congrArg (overlapHomEquiv₂ f M N) w
    rw [overlapHomEquiv₂_comp_left, overlapHomEquiv₂_comp_right] at hw
    exact hw.symm
  · intro w
    apply (overlapHomEquiv₂ f M N).injective
    rw [overlapHomEquiv₂_comp_left, overlapHomEquiv₂_comp_right]
    exact w.symm

/-- The functor sending ordinary singleton affine descent data to the Beck
coalgebra obtained from its kernel-pair comparison. -/
noncomputable def AffineStandardDescentData.toCoalgebra :
    AffineStandardDescentData f ⥤
      (extendRestrictScalarsAdj f).toComonad.Coalgebra where
  obj D := D.toCoalgebraObj f
  map {D E} h :=
    { f := h.hom default
      h := by
        change overlapHomEquiv f (D.obj default) (D.overlapHom f) ≫
            (extendRestrictScalarsAdj f).toComonad.map (h.hom default) =
          h.hom default ≫ overlapHomEquiv f (E.obj default) (E.overlapHom f)
        apply (overlap_comm_iff_coaction_comm f _ _ (h.hom default)
          (D.overlapHom f) (E.overlapHom f)).mp
        letI : Algebra A B := f.toAlgebra
        let C := B ⊗[A] B
        let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
        let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
        let q : op (CommRingCat.of C) ⟶ op (CommRingCat.of A) :=
          (CommRingCat.ofHom (algebraMap A C)).op
        have hl : (CommRingCat.ofHom l).op ≫ (CommRingCat.ofHom f).op = q := by
          calc
            _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom l).op := rfl
            _ = (CommRingCat.ofHom (l.comp f)).op := rfl
            _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2
        have hr : (CommRingCat.ofHom r).op ≫ (CommRingCat.ofHom f).op = q := by
          calc
            _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom r).op := rfl
            _ = (CommRingCat.ofHom (r.comp f)).op := rfl
            _ = (CommRingCat.ofHom (l.comp f)).op := by
              congr 2
              change r.comp f = l.comp f
              simpa only [show f = algebraMap A B from rfl] using
                Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
            _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2
        change (extendScalars l).map (h.hom default) ≫
            E.hom q (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op hl hr =
          D.hom q (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op hl hr ≫
            (extendScalars r).map (h.hom default)
        exact h.comm (i₁ := default) (i₂ := default)
          q (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op hl hr }

end ModuleCat
