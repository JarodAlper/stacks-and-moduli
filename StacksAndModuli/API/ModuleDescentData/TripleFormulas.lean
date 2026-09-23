module

public import StacksAndModuli.API.ModuleDescentData.PullFormula

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

lemma overlapCancel_tmul_tmul (N : ModuleCat.{u} B)
    (b₁ b : B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (overlapCancel f N).hom
        ((b₁ ⊗ₜ[A] b : C) ⊗ₜ[B,cR] n) =
      b₁ ⊗ₜ[A] (show (restrictScalars f).obj N from b • n) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  dsimp only
  have hc : (b₁ ⊗ₜ[A] b : C) = cL b₁ * cR b := by
    change b₁ ⊗ₜ[A] b =
      (b₁ ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hmove :
      (b₁ ⊗ₜ[A] b : C) ⊗ₜ[B,cR] n =
        cL b₁ ⊗ₜ[B,cR] (b • n) := by
    rw [hc, mul_comm]
    let modBC : Module B C := Module.compHom C cR
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <|
      @TensorProduct.Eqv.of_smul B _ C N _ _ modBC N.isModule
        b (cL b₁) n
  rw [hmove, ← overlapCancel_inv_tmul f N b₁ (b • n)]
  exact (overlapCancel f N).inv_hom_id_apply _

lemma tripleCancel_j₁₃_tmul_tmul (N : ModuleCat.{u} B)
    (b₁ b₃ : B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₃ : B →+* T := tR.comp cR
    let cRA : B →ₐ[A] C := Algebra.TensorProduct.includeRight
    let j₁₃ : C →+* T :=
      (Algebra.TensorProduct.map (AlgHom.id A B) cRA).toRingHom
    (tripleCancel f N).hom
        (j₁₃ (b₁ ⊗ₜ[A] b₃) ⊗ₜ[B,i₃] n) =
      b₁ ⊗ₜ[A]
        (show (restrictScalars f).obj ((extendScalars f).obj
          ((restrictScalars f).obj N)) from
          (1 : B) ⊗ₜ[A]
            (show (restrictScalars f).obj N from b₃ • n)) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₃ : B →+* T := tR.comp cR
  let cRA : B →ₐ[A] C := Algebra.TensorProduct.includeRight
  let j₁₃ : C →+* T :=
    (Algebra.TensorProduct.map (AlgHom.id A B) cRA).toRingHom
  dsimp only
  have hj : j₁₃ (b₁ ⊗ₜ[A] b₃) = i₁ b₁ * i₃ b₃ := by
    change (Algebra.TensorProduct.map (AlgHom.id A B) cRA)
      (b₁ ⊗ₜ[A] b₃) =
        (b₁ ⊗ₜ[A] (1 : C)) *
          ((1 : B) ⊗ₜ[A] cRA b₃)
    rw [Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  let source : ModuleCat B :=
    (restrictScalars i₁).obj ((extendScalars i₃).obj N)
  have hmove : (show source from
        j₁₃ (b₁ ⊗ₜ[A] b₃) ⊗ₜ[B,i₃] n) =
      b₁ • (show source from
        (1 : T) ⊗ₜ[B,i₃] (b₃ • n)) := by
    rw [hj]
    have hrel : (show (extendScalars i₃).obj N from
          (i₁ b₁ * i₃ b₃) ⊗ₜ[B,i₃] n) =
        i₁ b₁ ⊗ₜ[B,i₃] (b₃ • n) := by
      rw [mul_comm]
      let modBT : Module B T := Module.compHom T i₃
      exact Quotient.sound' <| AddConGen.Rel.of _ _ <|
        @TensorProduct.Eqv.of_smul B _ T N _ _ modBT N.isModule
          b₃ (i₁ b₁) n
    calc
      _ = (show source from
          i₁ b₁ ⊗ₜ[B,i₃] (b₃ • n)) := hrel
      _ = _ := by
        change i₁ b₁ ⊗ₜ[B,i₃] (b₃ • n) =
          i₁ b₁ •
            ((1 : T) ⊗ₜ[B,i₃] (b₃ • n))
        symm
        simpa only [mul_one] using
          ExtendScalars.smul_tmul i₃ (i₁ b₁) 1 (b₃ • n)
  let target : ModuleCat B :=
    (extendScalars f).obj ((restrictScalars f).obj
      ((extendScalars f).obj ((restrictScalars f).obj N)))
  let M : ModuleCat A :=
    (restrictScalars f).obj ((extendScalars f).obj ((restrictScalars f).obj N))
  calc
    _ = (tripleCancel f N).hom
        (b₁ • (show source from
          (1 : T) ⊗ₜ[B,i₃] (b₃ • n))) :=
      congrArg (fun x : source ↦ (tripleCancel f N).hom x) hmove
    _ = b₁ • (tripleCancel f N).hom
        ((1 : T) ⊗ₜ[B,i₃] (b₃ • n)) := by
      exact LinearMap.map_smul (tripleCancel f N).hom.hom b₁ _
    _ = b₁ • (show target from (1 : B) ⊗ₜ[A]
        (show M from (1 : B) ⊗ₜ[A] (b₃ • n))) :=
      congrArg (fun z : target ↦ b₁ • z)
        (tripleCancel_one_tmul f N (b₃ • n))
    _ = _ := (TensorProduct.tmul_eq_smul_one_tmul b₁
      (show M from (1 : B) ⊗ₜ[A] (b₃ • n))).symm

lemma comonad_delta_apply_tmul (N : ModuleCat.{u} B) (b : B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    ((extendRestrictScalarsAdj f).toComonad.δ.app N)
        (b ⊗ₜ[A] (show (restrictScalars f).obj N from n)) =
      b ⊗ₜ[A]
        (show (restrictScalars f).obj ((extendScalars f).obj
          ((restrictScalars f).obj N)) from
          (1 : B) ⊗ₜ[A] (show (restrictScalars f).obj N from n)) := by
  letI : Algebra A B := f.toAlgebra
  change (extendScalars f).map
      ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj N))
        (b ⊗ₜ[A] (show (restrictScalars f).obj N from n)) = _
  exact ExtendScalars.map_tmul f
    ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj N)) b n

lemma comonad_map_apply_tmul (N : ModuleCat.{u} B)
    (a : N ⟶ (extendScalars f).obj ((restrictScalars f).obj N))
    (b : B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    (extendRestrictScalarsAdj f).toComonad.map a
        (b ⊗ₜ[A] (show (restrictScalars f).obj N from n)) =
      b ⊗ₜ[A]
        (show (restrictScalars f).obj ((extendScalars f).obj
          ((restrictScalars f).obj N)) from a n) := by
  letI : Algebra A B := f.toAlgebra
  change (extendScalars f).map ((restrictScalars f).map a)
    (b ⊗ₜ[A] (show (restrictScalars f).obj N from n)) = _
  exact ExtendScalars.map_tmul f ((restrictScalars f).map a) b n

lemma tripleCancel_after_j₁₃ (N : ModuleCat.{u} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₃ : B →+* T := tR.comp cR
    let cRA : B →ₐ[A] C := Algebra.TensorProduct.includeRight
    let j₁₃ : C →+* T :=
      (Algebra.TensorProduct.map (AlgHom.id A B) cRA).toRingHom
    ∀ y : (extendScalars cR).obj N,
      (tripleCancel f N).hom
          ((extendScalarsComp cR j₁₃).inv.app N
            ((1 : T) ⊗ₜ[C,j₁₃] y)) =
        (extendRestrictScalarsAdj f).toComonad.δ.app N
          ((overlapCancel f N).hom y) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₃ : B →+* T := tR.comp cR
  let cRA : B →ₐ[A] C := Algebra.TensorProduct.includeRight
  let j₁₃ : C →+* T :=
    (Algebra.TensorProduct.map (AlgHom.id A B) cRA).toRingHom
  dsimp only
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add y y' hy hy' =>
      simpa only [tmul_add, map_add] using congrArg₂ (.+.) hy hy'
  | tmul c n =>
      induction c using TensorProduct.induction_on with
      | zero => simp only [zero_tmul, map_zero, tmul_zero]
      | add c c' hc hc' =>
          simpa only [add_tmul, map_add, tmul_add] using congrArg₂ (.+.) hc hc'
      | tmul b₁ b₃ =>
          rw [extendScalarsComp_inv_app_tmul_tmul cR j₁₃ N 1
            (b₁ ⊗ₜ[A] b₃) n, one_mul]
          rw [tripleCancel_j₁₃_tmul_tmul f N b₁ b₃ n]
          rw [overlapCancel_tmul_tmul f N b₁ b₃ n]
          exact (comonad_delta_apply_tmul f N b₁ (b₃ • n)).symm

lemma tripleCancel_after_tR (N : ModuleCat.{u} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₃ : B →+* T := tR.comp cR
    ∀ y : (extendScalars cR).obj N,
      (tripleCancel f N).hom
          ((extendScalarsComp cR tR).inv.app N
            ((1 : T) ⊗ₜ[C,tR] y)) =
        (1 : B) ⊗ₜ[A]
          (show (restrictScalars f).obj ((extendScalars f).obj
            ((restrictScalars f).obj N)) from
            (overlapCancel f N).hom y) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₃ : B →+* T := tR.comp cR
  let g : A →+* C := algebraMap A C
  let X : ModuleCat.{u} C := (extendScalars cR).obj N
  let e₁ : (restrictScalars i₁).obj ((extendScalars i₃).obj N) ≅
      (restrictScalars tL).obj ((extendScalars tR).obj X) :=
    (restrictScalars tL).mapIso ((extendScalarsComp cR tR).app N)
  let e : (restrictScalars tL).obj ((extendScalars tR).obj X) ≅
      (extendScalars f).obj ((restrictScalars g).obj X) :=
    by simpa only [g, tL, tR, T] using tensorPushoutCancelRightAlgebra f X
  let eA : (restrictScalars g).obj X ≅
      (restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N)) :=
    (restrictScalarsComp f cL).app X ≪≫
      (restrictScalars f).mapIso (overlapCancel f N)
  let e₃ : (extendScalars f).obj ((restrictScalars g).obj X) ≅
      (extendScalars f).obj ((restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N))) :=
    (extendScalars f).mapIso eA
  dsimp only
  intro y
  change e₃.hom (e.hom (e₁.hom
    ((extendScalarsComp cR tR).inv.app N
      ((1 : T) ⊗ₜ[C,tR] y)))) = _
  rw [show e₁.hom ((extendScalarsComp cR tR).inv.app N
      ((1 : T) ⊗ₜ[C,tR] y)) = (1 : T) ⊗ₜ[C,tR] y by
    exact ((extendScalarsComp cR tR).app N).inv_hom_id_apply _]
  rw [show e.hom ((1 : T) ⊗ₜ[C,tR] y) =
      (1 : B) ⊗ₜ[A] (show (restrictScalars g).obj X from y) by
    dsimp only [e]
    change (tensorPushoutCancelRightAlgebra f X).hom
      ((1 : T) ⊗ₜ[C,tR] y) = _
    exact tensorPushoutCancelRightAlgebra_one_tmul f X y]
  rw [show e₃.hom ((1 : B) ⊗ₜ[A]
      (show (restrictScalars g).obj X from y)) =
      (1 : B) ⊗ₜ[A] (eA.hom y) by
    exact ExtendScalars.map_tmul f eA.hom 1 y]
  congr 1

lemma tripleCancel_pull₂₃_after_j₁₂ (N : ModuleCat.{u} B)
    (θ :
      letI : Algebra A B := f.toAlgebra
      let C := B ⊗[A] B
      let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
      let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
      (extendScalars cL).obj N ⟶ (extendScalars cR).obj N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₂ : B →+* T := tR.comp cL
    let i₃ : B →+* T := tR.comp cR
    let cLA : B →ₐ[A] C := Algebra.TensorProduct.includeLeft
    let j₁₂ : C →+* T :=
      (Algebra.TensorProduct.map (AlgHom.id A B) cLA).toRingHom
    let p₂₃ : (extendScalars i₂).obj N ⟶ (extendScalars i₃).obj N :=
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := extendScalarsPseudofunctorOpOp)
        (f₁ := (CommRingCat.ofHom cL).op) (f₂ := (CommRingCat.ofHom cR).op)
        θ (CommRingCat.ofHom tR).op (CommRingCat.ofHom i₂).op
          (CommRingCat.ofHom i₃).op rfl rfl
    let a : N ⟶ (extendScalars f).obj ((restrictScalars f).obj N) :=
      overlapHomEquiv f N θ
    ∀ y : (extendScalars cR).obj N,
      (tripleCancel f N).hom
          (p₂₃ ((extendScalarsComp cR j₁₂).inv.app N
            ((1 : T) ⊗ₜ[C,j₁₂] y))) =
        (extendRestrictScalarsAdj f).toComonad.map a
          ((overlapCancel f N).hom y) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₂ : B →+* T := tR.comp cL
  let i₃ : B →+* T := tR.comp cR
  let cLA : B →ₐ[A] C := Algebra.TensorProduct.includeLeft
  let j₁₂ : C →+* T :=
    (Algebra.TensorProduct.map (AlgHom.id A B) cLA).toRingHom
  let p₂₃ : (extendScalars i₂).obj N ⟶ (extendScalars i₃).obj N :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom cL).op) (f₂ := (CommRingCat.ofHom cR).op)
      θ (CommRingCat.ofHom tR).op (CommRingCat.ofHom i₂).op
        (CommRingCat.ofHom i₃).op rfl rfl
  let a : N ⟶ (extendScalars f).obj ((restrictScalars f).obj N) :=
    overlapHomEquiv f N θ
  let source : ModuleCat B :=
    (restrictScalars i₁).obj ((extendScalars i₂).obj N)
  let target : ModuleCat B :=
    (extendScalars f).obj ((restrictScalars f).obj
      ((extendScalars f).obj ((restrictScalars f).obj N)))
  let k : source ⟶ target :=
    (restrictScalars i₁).map p₂₃ ≫ (tripleCancel f N).hom
  dsimp only
  intro y
  change k ((extendScalarsComp cR j₁₂).inv.app N
      ((1 : T) ⊗ₜ[C,j₁₂] y)) =
    (extendRestrictScalarsAdj f).toComonad.map a
      ((overlapCancel f N).hom y)
  induction y using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add y y' hy hy' =>
      simpa only [tmul_add, map_add] using congrArg₂ (.+.) hy hy'
  | tmul c n =>
      induction c using TensorProduct.induction_on with
      | zero => simp only [zero_tmul, map_zero, tmul_zero]
      | add c c' hc hc' =>
          simpa only [add_tmul, map_add, tmul_add] using congrArg₂ (.+.) hc hc'
      | tmul b₁ b =>
          rw [extendScalarsComp_inv_app_tmul_tmul cR j₁₂ N 1
            (b₁ ⊗ₜ[A] b) n, one_mul]
          have hj : j₁₂ (b₁ ⊗ₜ[A] b) =
              i₁ b₁ * i₂ b := by
            change (Algebra.TensorProduct.map (AlgHom.id A B) cLA)
              (b₁ ⊗ₜ[A] b) =
                (b₁ ⊗ₜ[A] (1 : C)) *
                  ((1 : B) ⊗ₜ[A] cLA b)
            rw [Algebra.TensorProduct.map_tmul,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rfl
          have hmove : (show source from
                j₁₂ (b₁ ⊗ₜ[A] b) ⊗ₜ[B,i₂] n) =
              b₁ • (show source from
                (1 : T) ⊗ₜ[B,i₂] (b • n)) := by
            rw [hj]
            have hrel : (show (extendScalars i₂).obj N from
                  (i₁ b₁ * i₂ b) ⊗ₜ[B,i₂] n) =
                i₁ b₁ ⊗ₜ[B,i₂] (b • n) := by
              rw [mul_comm]
              let modBT : Module B T := Module.compHom T i₂
              exact Quotient.sound' <| AddConGen.Rel.of _ _ <|
                @TensorProduct.Eqv.of_smul B _ T N _ _ modBT N.isModule
                  b (i₁ b₁) n
            calc
              _ = (show source from
                  i₁ b₁ ⊗ₜ[B,i₂] (b • n)) := hrel
              _ = _ := by
                change i₁ b₁ ⊗ₜ[B,i₂] (b • n) =
                  i₁ b₁ •
                    ((1 : T) ⊗ₜ[B,i₂] (b • n))
                symm
                simpa only [mul_one] using
                  ExtendScalars.smul_tmul i₂ (i₁ b₁) 1 (b • n)
          have hpunit : p₂₃
                ((1 : T) ⊗ₜ[B,i₂] (b • n)) =
              (extendScalarsComp cR tR).inv.app N
                ((1 : T) ⊗ₜ[C,tR]
                  (θ ((1 : C) ⊗ₜ[B,cL] (b • n)))) := by
            dsimp only [p₂₃, i₂, i₃]
            exact pullHom_apply_unit cL cR tR N θ (b • n)
          have hkunit : k (show source from
                (1 : T) ⊗ₜ[B,i₂] (b • n)) =
              (1 : B) ⊗ₜ[A]
                (show (restrictScalars f).obj ((extendScalars f).obj
                  ((restrictScalars f).obj N)) from a (b • n)) := by
            change (tripleCancel f N).hom
              (p₂₃ ((1 : T) ⊗ₜ[B,i₂] (b • n))) = _
            rw [hpunit, tripleCancel_after_tR f N]
            congr 1
          calc
            k (j₁₂ (b₁ ⊗ₜ[A] b) ⊗ₜ[B,i₂] n) =
                k (b₁ • (show source from
                  (1 : T) ⊗ₜ[B,i₂] (b • n))) :=
              congrArg (fun x : source ↦ k x) hmove
            _ = b₁ • k (show source from
                  (1 : T) ⊗ₜ[B,i₂] (b • n)) :=
              LinearMap.map_smul k.hom b₁ _
            _ = b₁ ⊗ₜ[A]
                (show (restrictScalars f).obj ((extendScalars f).obj
                  ((restrictScalars f).obj N)) from a (b • n)) := by
              rw [hkunit]
              exact (TensorProduct.tmul_eq_smul_one_tmul b₁
                (show (restrictScalars f).obj ((extendScalars f).obj
                  ((restrictScalars f).obj N)) from a (b • n))).symm
            _ = _ := by
              rw [overlapCancel_tmul_tmul f N b₁ b n]
              exact (comonad_map_apply_tmul f N a b₁ (b • n)).symm

end ModuleCat
