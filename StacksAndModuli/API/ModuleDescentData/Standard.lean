module

public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
public import StacksAndModuli.API.ModuleDescent

/-!
# Ordinary affine module descent data as Beck coalgebras

This file supplies the comparison left open in Mathlib's
`DescentDataAsCoalgebra`: for the extension-of-scalars pseudofunctor and a
singleton affine cover, an ordinary kernel-pair descent datum determines the
coalgebra for the extension/restriction comonad.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxHeartbeats 100000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

@[simps! obj map mapId mapComp]
noncomputable abbrev extendScalarsPseudofunctorOpOp :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{u} R.unop.unop))
    (fun g ↦ (extendScalars g.unop.unop.hom).toCatHom)
    (fun R ↦ Cat.Hom.isoMk (extendScalarsId R.unop.unop))
    (fun g h ↦ Cat.Hom.isoMk (extendScalarsComp g.unop.unop.hom h.unop.unop.hom)) ?_ ?_ ?_
  · intros; ext1; apply extendScalars_assoc'
  · intros; ext1; apply extendScalars_id_comp
  · intros; ext1; apply extendScalars_comp_id

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

lemma splitOpEq {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (h : S →+* R) (e : h.comp g = RingHom.id R) :
    (CommRingCat.ofHom h).op ≫ (CommRingCat.ofHom g).op =
      𝟙 (op (CommRingCat.of R)) := by
  calc
    _ = (CommRingCat.ofHom g ≫ CommRingCat.ofHom h).op := rfl
    _ = (CommRingCat.ofHom (h.comp g)).op := rfl
    _ = _ := by rw [e]; rfl

lemma tensorMul_comp_left :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    mul.comp l = RingHom.id B := by
  letI : Algebra A B := f.toAlgebra
  ext b
  change (Algebra.TensorProduct.lmul' A) (b ⊗ₜ[A] (1 : B)) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

lemma tensorMul_comp_right :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    mul.comp r = RingHom.id B := by
  letI : Algebra A B := f.toAlgebra
  ext b
  change (Algebra.TensorProduct.lmul' A) ((1 : B) ⊗ₜ[A] b) = b
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

lemma doubleOpCompEq {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h : S →+* T) (k : R →+* T) (e : h.comp g = k) :
    (CommRingCat.ofHom g).op.op.toLoc ≫ (CommRingCat.ofHom h).op.op.toLoc =
      (CommRingCat.ofHom k).op.op.toLoc := by
  subst k
  rfl

lemma mapComp'_hom_app_unit
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h : S →+* T) (k : R →+* T) (e : h.comp g = k)
    (M : ModuleCat R) (m : M) :
    ((extendScalarsPseudofunctorOpOp.mapComp'
      (CommRingCat.ofHom g).op.op.toLoc
      (CommRingCat.ofHom h).op.op.toLoc
      (CommRingCat.ofHom k).op.op.toLoc
      (doubleOpCompEq g h k e)).hom.toNatTrans.app M).hom
        ((extendRestrictScalarsAdj k).unit.app M m) =
      (extendRestrictScalarsAdj h).unit.app ((extendScalars g).obj M)
        ((extendRestrictScalarsAdj g).unit.app M m) := by
  subst k
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S T := h.toAlgebra
  letI : Algebra R T := (h.comp g).toAlgebra
  change (extendScalarsComp g h).hom.app M ((1 : T) ⊗ₜ[R] m) =
    (1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)
  exact extendScalarsComp_hom_app_one_tmul g h M m

lemma mapComp'_hom_after_extendScalarsId_inv_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (h : S →+* R) (e : h.comp g = RingHom.id R)
    (M : ModuleCat R) (m : M) :
    ((extendScalarsId R).inv.app M ≫
      (extendScalarsPseudofunctorOpOp.mapComp'
        (CommRingCat.ofHom g).op.op.toLoc
        (CommRingCat.ofHom h).op.op.toLoc
        (𝟙 (op (op (CommRingCat.of R)))).toLoc
        (doubleOpCompEq g h (RingHom.id R) e)).hom.toNatTrans.app M) m =
      (extendRestrictScalarsAdj h).unit.app ((extendScalars g).obj M)
        ((extendRestrictScalarsAdj g).unit.app M m) := by
  change ((extendScalarsPseudofunctorOpOp.mapComp'
      (CommRingCat.ofHom g).op.op.toLoc
      (CommRingCat.ofHom h).op.op.toLoc
      (𝟙 (op (op (CommRingCat.of R)))).toLoc
      (doubleOpCompEq g h (RingHom.id R) e)).hom.toNatTrans.app M).hom
        ((extendScalarsId R).inv.app M m) = _
  rw [extendScalarsId_inv_app_apply]
  exact mapComp'_hom_app_unit g h (RingHom.id R) e M m

lemma extendScalarsComp_inv_app_tmul_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h : S →+* T) (M : ModuleCat R)
    (t : T) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h.toAlgebra
    letI : Algebra R T := (h.comp g).toAlgebra
    (extendScalarsComp g h).inv.app M
        (t ⊗ₜ[S] (s ⊗ₜ[R] m)) =
      (t * h s) ⊗ₜ[R] m := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S T := h.toAlgebra
  letI : Algebra R T := (h.comp g).toAlgebra
  apply (ConcreteCategory.bijective_of_isIso
    ((extendScalarsComp g h).hom.app M)).1
  change (((extendScalarsComp g h).inv.app M ≫
    (extendScalarsComp g h).hom.app M).hom)
      (t ⊗ₜ[S] (s ⊗ₜ[R] m)) = _
  rw [Iso.inv_hom_id_app]
  rw [show (t * h s) ⊗ₜ[R] m =
      (t * h s) • ((1 : T) ⊗ₜ[R] m) by
        rw [TensorProduct.tmul_eq_smul_one_tmul]]
  rw [map_smul, extendScalarsComp_hom_app_one_tmul]
  change t ⊗ₜ[S] (s ⊗ₜ[R] m) =
    (t * h s) • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))
  rw [TensorProduct.tmul_eq_smul_one_tmul s]
  rw [TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul']
  change (h s * t) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) =
    ((t * h s) * 1) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)
  rw [mul_one, mul_comm]

lemma mapComp'_inv_app_tmul_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h : S →+* T) (k : R →+* T) (e : h.comp g = k)
    (M : ModuleCat R) (t : T) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h.toAlgebra
    letI : Algebra R T := k.toAlgebra
    ((extendScalarsPseudofunctorOpOp.mapComp'
      (CommRingCat.ofHom g).op.op.toLoc
      (CommRingCat.ofHom h).op.op.toLoc
      (CommRingCat.ofHom k).op.op.toLoc
      (doubleOpCompEq g h k e)).inv.toNatTrans.app M).hom
        (t ⊗ₜ[S] (s ⊗ₜ[R] m)) =
      (t * h s) ⊗ₜ[R] m := by
  subst k
  exact extendScalarsComp_inv_app_tmul_tmul g h M t s m

lemma extendScalarsId_hom_after_mapComp'_inv_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (h : S →+* R) (e : h.comp g = RingHom.id R)
    (M : ModuleCat R) (r : R) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S R := h.toAlgebra
    letI : Algebra R R := (RingHom.id R).toAlgebra
    (((extendScalarsPseudofunctorOpOp.mapComp'
      (CommRingCat.ofHom g).op.op.toLoc
      (CommRingCat.ofHom h).op.op.toLoc
      (CommRingCat.ofHom (RingHom.id R)).op.op.toLoc
      (doubleOpCompEq g h (RingHom.id R) e)).inv.toNatTrans.app M) ≫
        (extendScalarsId R).hom.app M).hom
          (r ⊗ₜ[S] (s ⊗ₜ[R] m)) =
      (r * h s) • m := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S R := h.toAlgebra
  letI : Algebra R R := (RingHom.id R).toAlgebra
  change (extendScalarsId R).hom.app M
      (((extendScalarsPseudofunctorOpOp.mapComp'
        (CommRingCat.ofHom g).op.op.toLoc
        (CommRingCat.ofHom h).op.op.toLoc
        (CommRingCat.ofHom (RingHom.id R)).op.op.toLoc
        (doubleOpCompEq g h (RingHom.id R) e)).inv.toNatTrans.app M).hom
          (r ⊗ₜ[S] (s ⊗ₜ[R] m))) = _
  rw [mapComp'_inv_app_tmul_tmul g h (RingHom.id R) e]
  rw [show (r * h s) ⊗ₜ[R] m =
      (r * h s) • ((1 : R) ⊗ₜ[R] m) by
        rw [TensorProduct.tmul_eq_smul_one_tmul]]
  rw [map_smul, extendScalarsId_hom_app_one_tmul]

noncomputable def overlapPullHomMul (N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ((extendScalars l).obj N ⟶ (extendScalars r).obj N) → (N ⟶ N) := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  intro θ
  exact (extendScalarsId B).inv.app N ≫
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
      θ (CommRingCat.ofHom mul).op
      (𝟙 (op (CommRingCat.of B))) (𝟙 (op (CommRingCat.of B)))
      (hgf₁ := splitOpEq l mul (tensorMul_comp_left f))
      (hgf₂ := splitOpEq r mul (tensorMul_comp_right f)) ≫
    (extendScalarsId B).hom.app N

noncomputable def overlapCounitComposite (N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ((extendScalars l).obj N ⟶ (extendScalars r).obj N) → (N ⟶ N) := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  intro θ
  exact overlapHomEquiv f N θ ≫ (extendRestrictScalarsAdj f).counit.app N

noncomputable def overlapRightEvaluation (N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    (extendScalars mul).obj ((extendScalars r).obj N) ⟶ N := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  exact (extendScalarsPseudofunctorOpOp.mapComp'
    (CommRingCat.ofHom r).op.op.toLoc
    (CommRingCat.ofHom mul).op.op.toLoc
    (CommRingCat.ofHom (RingHom.id B)).op.op.toLoc
    (doubleOpCompEq r mul (RingHom.id B)
      (tensorMul_comp_right f))).inv.toNatTrans.app N ≫
      (extendScalarsId B).hom.app N

noncomputable def overlapLeftCoevaluation (N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    N ⟶ (extendScalars mul).obj ((extendScalars l).obj N) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  exact (extendScalarsId B).inv.app N ≫
    (extendScalarsPseudofunctorOpOp.mapComp'
      (CommRingCat.ofHom l).op.op.toLoc
      (CommRingCat.ofHom mul).op.op.toLoc
      (CommRingCat.ofHom (RingHom.id B)).op.op.toLoc
      (doubleOpCompEq l mul (RingHom.id B)
        (tensorMul_comp_left f))).hom.toNatTrans.app N

set_option maxHeartbeats 200000 in
lemma overlapCounit_after_cancel (N : ModuleCat B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    ∀ y : (extendScalars r).obj N,
      (extendRestrictScalarsAdj f).counit.app N ((overlapCancel f N).hom y) =
        overlapRightEvaluation f N ((1 : B) ⊗ₜ[C,mul] y) := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  let eL : mul.comp l = RingHom.id B := tensorMul_comp_left f
  let eR : mul.comp r = RingHom.id B := tensorMul_comp_right f
  intro y
  have H' : ∀ z : (extendScalars f).obj ((restrictScalars f).obj N),
      (extendRestrictScalarsAdj f).counit.app N
          ((overlapCancel f N).hom ((overlapCancel f N).inv z)) =
        overlapRightEvaluation f N
          ((1 : B) ⊗ₜ[C,mul] ((overlapCancel f N).inv z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero, tmul_zero, map_zero, map_zero]
    | add z z' hz hz' =>
        simpa only [map_add, tmul_add] using congrArg₂ (.+.) hz hz'
    | tmul b n =>
        rw [Iso.inv_hom_id_apply]
        let b' : B := b
        let n' : N := n
        change (extendRestrictScalarsAdj f).counit.app N (b' ⊗ₜ[A,f] n') =
          overlapRightEvaluation f N ((1 : B) ⊗ₜ[C,mul]
            ((overlapCancel f N).inv (b' ⊗ₜ[A,f] n')))
        rw [overlapCancel_inv_tmul f N b' n']
        change b' • n' = overlapRightEvaluation f N
          ((1 : B) ⊗ₜ[C,mul]
            (Algebra.TensorProduct.includeLeftRingHom b' ⊗ₜ[B,r] n'))
        calc
          b' • n' =
              (1 * mul (Algebra.TensorProduct.includeLeftRingHom b')) • n' := by
            have hLb : mul (Algebra.TensorProduct.includeLeftRingHom b') = b' :=
              DFunLike.congr_fun eL b'
            rw [hLb, one_mul]
          _ = overlapRightEvaluation f N ((1 : B) ⊗ₜ[C,mul]
              (Algebra.TensorProduct.includeLeftRingHom b' ⊗ₜ[B,r] n')) := by
            have hq := extendScalarsId_hom_after_mapComp'_inv_apply
              r mul eR N 1 (Algebra.TensorProduct.includeLeftRingHom b') n'
            symm
            unfold overlapRightEvaluation
            exact hq
  simpa using (H' ((overlapCancel f N).hom y))

structure AffineOverlapMorphism (N : ModuleCat B) where
  hom :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (extendScalars l).obj N ⟶ (extendScalars r).obj N

noncomputable def AffineOverlapMorphism.counitComposite
    (datum : AffineOverlapMorphism f N) : N ⟶ N :=
  overlapCounitComposite f N datum.hom

noncomputable def AffineOverlapMorphism.pullHomMul
    (datum : AffineOverlapMorphism f N) : N ⟶ N := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  exact overlapLeftCoevaluation f N ≫
    (extendScalars mul).map datum.hom ≫ overlapRightEvaluation f N

noncomputable def AffineOverlapMorphism.normalForm
    (datum : AffineOverlapMorphism f N) : N ⟶ N := datum.pullHomMul

lemma AffineOverlapMorphism.pullHomMul_eq_normalForm
    (datum : AffineOverlapMorphism f N) :
    datum.pullHomMul = datum.normalForm := by
  rfl

set_option maxHeartbeats 300000 in
lemma overlapHomEquiv_comp_counit_apply (N : ModuleCat B)
    (datum : AffineOverlapMorphism f N) (n : N) :
    datum.counitComposite.hom n = datum.normalForm.hom n := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  let θ : (extendScalars l).obj N ⟶ (extendScalars r).obj N := datum.hom
  let eL : mul.comp l = RingHom.id B := tensorMul_comp_left f
  let q : (extendScalars mul).obj ((extendScalars r).obj N) ⟶ N :=
    overlapRightEvaluation f N
  let p : N ⟶ (extendScalars mul).obj ((extendScalars l).obj N) :=
    overlapLeftCoevaluation f N
  unfold AffineOverlapMorphism.counitComposite
  unfold overlapCounitComposite
  change (extendRestrictScalarsAdj f).counit.app N
      ((overlapCancel f N).hom
        (θ ((extendRestrictScalarsAdj l).unit.app N n))) = _
  rw [overlapCounit_after_cancel f N]
  unfold AffineOverlapMorphism.normalForm
  unfold AffineOverlapMorphism.pullHomMul
  change q.hom ((1 : B) ⊗ₜ[C,mul]
      (θ ((extendRestrictScalarsAdj l).unit.app N n))) =
    q.hom ((extendScalars mul).map θ (p.hom n))
  congr 1
  rw [show p.hom n =
      (extendRestrictScalarsAdj mul).unit.app ((extendScalars l).obj N)
        ((extendRestrictScalarsAdj l).unit.app N n) by
    dsimp [p, overlapLeftCoevaluation]
    exact mapComp'_hom_after_extendScalarsId_inv_apply l mul eL N n]
  let x : (extendScalars l).obj N :=
    (extendRestrictScalarsAdj l).unit.app N n
  exact (ExtendScalars.map_tmul mul θ 1 x).symm

lemma overlapHomEquiv_comp_counit (N : ModuleCat B)
    (datum : AffineOverlapMorphism f N) :
    datum.counitComposite = datum.pullHomMul := by
  calc
    datum.counitComposite = datum.normalForm := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      exact overlapHomEquiv_comp_counit_apply f N datum n
    _ = datum.pullHomMul := datum.pullHomMul_eq_normalForm.symm

abbrev AffineStandardDescentData :=
  let F := extendScalarsPseudofunctorOpOp.{u}
  @Pseudofunctor.DescentData (CommRingCat.{u})ᵒᵖ _ F Unit
    (op (CommRingCat.of A)) (fun _ ↦ op (CommRingCat.of B))
    (fun _ ↦ (CommRingCat.ofHom f).op)

/-- The left tensor-factor map lies over the original affine ring map. -/
lemma affineOverlapLeft_comp :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    (CommRingCat.ofHom l).op ≫ (CommRingCat.ofHom f).op =
      (CommRingCat.ofHom (algebraMap A C)).op := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  calc
    _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom l).op := rfl
    _ = (CommRingCat.ofHom (l.comp f)).op := rfl
    _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2

/-- The right tensor-factor map lies over the original affine ring map. -/
lemma affineOverlapRight_comp :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (CommRingCat.ofHom r).op ≫ (CommRingCat.ofHom f).op =
      (CommRingCat.ofHom (algebraMap A C)).op := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  calc
    _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom r).op := rfl
    _ = (CommRingCat.ofHom (r.comp f)).op := rfl
    _ = (CommRingCat.ofHom (l.comp f)).op := by
      congr 2
      change r.comp f = l.comp f
      simpa only [show f = algebraMap A B from rfl] using
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2

noncomputable def AffineStandardDescentData.overlapHom
    (D : AffineStandardDescentData f) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (extendScalars l).obj (D.obj default) ⟶
      (extendScalars r).obj (D.obj default) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let q : op (CommRingCat.of C) ⟶ op (CommRingCat.of A) :=
    (CommRingCat.ofHom (algebraMap A C)).op
  exact D.hom q (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op
    (affineOverlapLeft_comp f) (affineOverlapRight_comp f)

noncomputable def AffineStandardDescentData.overlapDatum
    (D : AffineStandardDescentData f) :
    AffineOverlapMorphism f (D.obj default) :=
  ⟨D.overlapHom f⟩

noncomputable def AffineStandardDescentData.overlapPullHomMul
    (D : AffineStandardDescentData f) : D.obj default ⟶ D.obj default := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  exact (extendScalarsId B).inv.app (D.obj default) ≫
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
      (D.overlapHom f) (CommRingCat.ofHom mul).op
      (𝟙 (op (CommRingCat.of B))) (𝟙 (op (CommRingCat.of B)))
      (hgf₁ := splitOpEq l mul (tensorMul_comp_left f))
      (hgf₂ := splitOpEq r mul (tensorMul_comp_right f)) ≫
    (extendScalarsId B).hom.app (D.obj default)

lemma AffineStandardDescentData.overlapPullHom_mul_eq_id
    (D : AffineStandardDescentData f) : D.overlapPullHomMul f = 𝟙 _ := by
  change
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
    (extendScalarsId B).inv.app (D.obj default) ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := extendScalarsPseudofunctorOpOp)
        (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
        (D.overlapHom f) (CommRingCat.ofHom mul).op
        (𝟙 (op (CommRingCat.of B))) (𝟙 (op (CommRingCat.of B)))
        (hgf₁ := splitOpEq l mul (tensorMul_comp_left f))
        (hgf₂ := splitOpEq r mul (tensorMul_comp_right f)) ≫
      (extendScalarsId B).hom.app (D.obj default) = 𝟙 _
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let mul : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  let qC : op (CommRingCat.of C) ⟶ op (CommRingCat.of A) :=
    (CommRingCat.ofHom (algebraMap A C)).op
  let qB : op (CommRingCat.of B) ⟶ op (CommRingCat.of A) :=
    (CommRingCat.ofHom f).op
  let d : op (CommRingCat.of B) ⟶ op (CommRingCat.of C) :=
    (CommRingCat.ofHom mul).op
  have hl : (CommRingCat.ofHom l).op ≫ qB = qC := by
    change (CommRingCat.ofHom l).op ≫ (CommRingCat.ofHom f).op = _
    calc
      _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom l).op := rfl
      _ = (CommRingCat.ofHom (l.comp f)).op := rfl
      _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2
  have hr : (CommRingCat.ofHom r).op ≫ qB = qC := by
    change (CommRingCat.ofHom r).op ≫ (CommRingCat.ofHom f).op = _
    calc
      _ = (CommRingCat.ofHom f ≫ CommRingCat.ofHom r).op := rfl
      _ = (CommRingCat.ofHom (r.comp f)).op := rfl
      _ = (CommRingCat.ofHom (l.comp f)).op := by
        congr 2
        change r.comp f = l.comp f
        simpa only [show f = algebraMap A B from rfl] using
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
      _ = (CommRingCat.ofHom (algebraMap A C)).op := by congr 2
  have hdq : d ≫ qC = qB := by
    change (CommRingCat.ofHom mul).op ≫
      (CommRingCat.ofHom (algebraMap A C)).op = (CommRingCat.ofHom f).op
    calc
      _ = (CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom mul).op := rfl
      _ = (CommRingCat.ofHom (mul.comp (algebraMap A C))).op := rfl
      _ = (CommRingCat.ofHom f).op := by
        congr 2
        ext a
        change (Algebra.TensorProduct.lmul' A)
          ((algebraMap A B a) ⊗ₜ[A] (1 : B)) = f a
        rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
        rfl
  have hdl : d ≫ (CommRingCat.ofHom l).op = 𝟙 _ := by
    change (CommRingCat.ofHom mul).op ≫ (CommRingCat.ofHom l).op = _
    calc
      _ = (CommRingCat.ofHom l ≫ CommRingCat.ofHom mul).op := rfl
      _ = (CommRingCat.ofHom (mul.comp l)).op := rfl
      _ = (CommRingCat.ofHom (RingHom.id B)).op := by
        congr 2
        ext b
        change (Algebra.TensorProduct.lmul' A) (b ⊗ₜ[A] (1 : B)) = b
        rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
      _ = _ := rfl
  have hdr : d ≫ (CommRingCat.ofHom r).op = 𝟙 _ := by
    change (CommRingCat.ofHom mul).op ≫ (CommRingCat.ofHom r).op = _
    calc
      _ = (CommRingCat.ofHom r ≫ CommRingCat.ofHom mul).op := rfl
      _ = (CommRingCat.ofHom (mul.comp r)).op := rfl
      _ = (CommRingCat.ofHom (RingHom.id B)).op := by
        congr 2
        ext b
        change (Algebra.TensorProduct.lmul' A) ((1 : B) ⊗ₜ[A] b) = b
        rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
      _ = _ := rfl
  have hpull : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
      (D.overlapHom f) d (𝟙 _) (𝟙 _)
      (hgf₁ := hdl) (hgf₂ := hdr) = 𝟙 _ := by
    calc
      _ = D.hom qB (𝟙 _) (𝟙 _) :=
        D.pullHom_hom d qC qB hdq
          (CommRingCat.ofHom l).op (CommRingCat.ofHom r).op hl hr
          (𝟙 _) (𝟙 _) hdl hdr
      _ = 𝟙 _ := D.hom_self qB (𝟙 _) (by dsimp [qB]; simp)
  change (extendScalarsId B).inv.app (D.obj default) ≫
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
      (D.overlapHom f) d (𝟙 _) (𝟙 _)
      (hgf₁ := hdl) (hgf₂ := hdr) ≫
    (extendScalarsId B).hom.app (D.obj default) = 𝟙 _
  have hpullIso : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := extendScalarsPseudofunctorOpOp)
      (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
      (D.overlapHom f) d (𝟙 _) (𝟙 _)
      (hgf₁ := hdl) (hgf₂ := hdr) =
        (extendScalarsId B).hom.app (D.obj default) ≫
          (extendScalarsId B).inv.app (D.obj default) := by
    rw [hpull]
    exact ((extendScalarsId B).hom_inv_id_app (D.obj default)).symm
  rw [hpullIso]
  simp

set_option maxHeartbeats 500000 in
lemma AffineStandardDescentData.overlapDatum_pullHomMul_eq_id
    (D : AffineStandardDescentData f) :
    (D.overlapDatum f).pullHomMul = 𝟙 _ := by
  change D.overlapPullHomMul f = 𝟙 _
  exact D.overlapPullHom_mul_eq_id f

lemma AffineStandardDescentData.coaction_counit
    (D : AffineStandardDescentData f) :
    overlapHomEquiv f (D.obj default) (D.overlapHom f) ≫
      (extendRestrictScalarsAdj f).counit.app (D.obj default) = 𝟙 _ := by
  calc
    _ = (D.overlapDatum f).counitComposite := rfl
    _ = (D.overlapDatum f).pullHomMul :=
      overlapHomEquiv_comp_counit f _ (D.overlapDatum f)
    _ = 𝟙 _ := D.overlapDatum_pullHomMul_eq_id f

end ModuleCat
