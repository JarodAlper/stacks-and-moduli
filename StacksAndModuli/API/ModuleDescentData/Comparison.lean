module

public import StacksAndModuli.API.ModuleDescentData.Prime
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# The canonical affine descent datum and the Beck comparison

This file identifies the ordinary singleton descent datum obtained by extension
of scalars with the coalgebra produced by the Beck comparison functor.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The extension-of-scalars compositor does not depend on the proof of the
underlying equality of composite morphisms. -/
lemma mapComp'_inv_app_eq_of_proof_irrel
    {X Y Z : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (p p' : a ≫ b = c) (M : extendScalarsPseudofunctorOpOp.obj X) :
    (extendScalarsPseudofunctorOpOp.mapComp' a b c p).inv.toNatTrans.app M =
      (extendScalarsPseudofunctorOpOp.mapComp' a b c p').inv.toNatTrans.app M := by
  obtain rfl : p = p' := Subsingleton.elim _ _
  rfl

/-- The forward direction of the extension-of-scalars compositor does not
depend on the proof of the underlying equality of composite morphisms. -/
lemma mapComp'_hom_app_eq_of_proof_irrel
    {X Y Z : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (p p' : a ≫ b = c) (M : extendScalarsPseudofunctorOpOp.obj X) :
    (extendScalarsPseudofunctorOpOp.mapComp' a b c p).hom.toNatTrans.app M =
      (extendScalarsPseudofunctorOpOp.mapComp' a b c p').hom.toNatTrans.app M := by
  obtain rfl : p = p' := Subsingleton.elim _ _
  rfl

/-- The two pseudofunctor compositors for extension of scalars act on a pure
tensor by moving the middle scalar to the outer tensor factor. -/
lemma mapComp'_inv_hom_app_tmul_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h₁ h₂ : S →+* T) (k : R →+* T)
    (e₁ : h₁.comp g = k) (e₂ : h₂.comp g = k)
    (M : ModuleCat R) (t : T) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h₁.toAlgebra
    letI : Algebra R T := k.toAlgebra
    (show (extendScalars h₂).obj ((extendScalars g).obj M) from
      (((extendScalarsPseudofunctorOpOp.mapComp'
          (CommRingCat.ofHom g).op.op.toLoc
          (CommRingCat.ofHom h₁).op.op.toLoc
          (CommRingCat.ofHom k).op.op.toLoc
          (doubleOpCompEq g h₁ k e₁)).inv.toNatTrans.app M) ≫
        ((extendScalarsPseudofunctorOpOp.mapComp'
          (CommRingCat.ofHom g).op.op.toLoc
          (CommRingCat.ofHom h₂).op.op.toLoc
          (CommRingCat.ofHom k).op.op.toLoc
          (doubleOpCompEq g h₂ k e₂)).hom.toNatTrans.app M)).hom
          (t ⊗ₜ[S,h₁] (s ⊗ₜ[R,g] m))) =
      (t * h₁ s) ⊗ₜ[S,h₂] ((1 : S) ⊗ₜ[R,g] m) := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S T := h₁.toAlgebra
  letI : Algebra R T := k.toAlgebra
  let p := (extendScalarsPseudofunctorOpOp.mapComp'
    (CommRingCat.ofHom g).op.op.toLoc
    (CommRingCat.ofHom h₁).op.op.toLoc
    (CommRingCat.ofHom k).op.op.toLoc
    (doubleOpCompEq g h₁ k e₁)).inv.toNatTrans.app M
  let q := (extendScalarsPseudofunctorOpOp.mapComp'
    (CommRingCat.ofHom g).op.op.toLoc
    (CommRingCat.ofHom h₂).op.op.toLoc
    (CommRingCat.ofHom k).op.op.toLoc
    (doubleOpCompEq g h₂ k e₂)).hom.toNatTrans.app M
  let x := t * h₁ s
  change q.hom (p.hom (t ⊗ₜ[S,h₁] (s ⊗ₜ[R,g] m))) = _
  rw [show p.hom (t ⊗ₜ[S,h₁] (s ⊗ₜ[R,g] m)) =
      x ⊗ₜ[R,k] m by
    simpa only [p, x] using
      mapComp'_inv_app_tmul_tmul g h₁ k e₁ M t s m]
  rw [show (x ⊗ₜ[R,k] m) = x • ((1 : T) ⊗ₜ[R,k] m) by
    rw [TensorProduct.tmul_eq_smul_one_tmul]]
  rw [map_smul]
  rw [show q.hom ((1 : T) ⊗ₜ[R,k] m) =
      (1 : T) ⊗ₜ[S,h₂] ((1 : S) ⊗ₜ[R,g] m) by
    have hu := mapComp'_hom_app_unit g h₂ k e₂ M m
    rw [extendRestrictScalarsAdj_unit_app_apply,
      extendRestrictScalarsAdj_unit_app_apply,
      extendRestrictScalarsAdj_unit_app_apply] at hu
    simpa only [q] using hu]
  letI : Algebra S T := h₂.toAlgebra
  letI : Module S T := Module.compHom T h₂
  simpa only [smul_eq_mul, mul_one] using
    (TensorProduct.smul_tmul' (R := S) (R' := T) x (1 : T)
      ((1 : S) ⊗ₜ[R,g] m))

/-- The pure-tensor formula for a pair of extension-of-scalars compositors,
with the actual equality proofs occurring in a descent datum accepted as
parameters. This avoids normalizing proof-dependent `Cat` morphisms. -/
lemma mapComp'_inv_hom_app_tmul_tmul_of_comp_eq
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h₁ h₂ : S →+* T) (k : R →+* T)
    (e₁ : h₁.comp g = k) (e₂ : h₂.comp g = k)
    (p₁ : (CommRingCat.ofHom g).op.op.toLoc ≫
      (CommRingCat.ofHom h₁).op.op.toLoc =
        (CommRingCat.ofHom k).op.op.toLoc)
    (p₂ : (CommRingCat.ofHom g).op.op.toLoc ≫
      (CommRingCat.ofHom h₂).op.op.toLoc =
        (CommRingCat.ofHom k).op.op.toLoc)
    (M : ModuleCat R) (t : T) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h₁.toAlgebra
    letI : Algebra R T := k.toAlgebra
    (show (extendScalars h₂).obj ((extendScalars g).obj M) from
      (((extendScalarsPseudofunctorOpOp.mapComp'
          (CommRingCat.ofHom g).op.op.toLoc
          (CommRingCat.ofHom h₁).op.op.toLoc
          (CommRingCat.ofHom k).op.op.toLoc p₁).inv.toNatTrans.app M) ≫
        ((extendScalarsPseudofunctorOpOp.mapComp'
          (CommRingCat.ofHom g).op.op.toLoc
          (CommRingCat.ofHom h₂).op.op.toLoc
          (CommRingCat.ofHom k).op.op.toLoc p₂).hom.toNatTrans.app M)).hom
          (t ⊗ₜ[S,h₁] (s ⊗ₜ[R,g] m))) =
      (t * h₁ s) ⊗ₜ[S,h₂] ((1 : S) ⊗ₜ[R,g] m) := by
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S T := h₁.toAlgebra
  letI : Algebra R T := k.toAlgebra
  rw [mapComp'_inv_app_eq_of_proof_irrel p₁
      (doubleOpCompEq g h₁ k e₁) M,
    mapComp'_hom_app_eq_of_proof_irrel p₂
      (doubleOpCompEq g h₂ k e₂) M]
  exact mapComp'_inv_hom_app_tmul_tmul g h₁ h₂ k e₁ e₂ M t s m

/-- The ordinary singleton affine descent datum canonically attached to a
module over the base ring. -/
noncomputable abbrev AffineStandardDescentData.ofModule
    (M : ModuleCat A) : AffineStandardDescentData f :=
  Pseudofunctor.DescentData.ofObj M

/-- The carrier of the canonical affine descent datum is extension of scalars. -/
lemma AffineStandardDescentData.ofModule_obj_eq (M : ModuleCat A) :
    (AffineStandardDescentData.ofModule f M).obj default =
      (extendScalars f).obj M := by
  rfl

/-- The carrier identification for the canonical affine descent datum. -/
noncomputable def AffineStandardDescentData.ofModuleIso (M : ModuleCat A) :
    (AffineStandardDescentData.ofModule f M).obj default ≅
      (extendScalars f).obj M :=
  eqToIso (AffineStandardDescentData.ofModule_obj_eq f M)

/-- After any further extension of scalars, the carrier identification for the
canonical affine descent datum is still the identity on the underlying tensor
product. -/
noncomputable def AffineStandardDescentData.ofModuleExtendIso
    {C : Type u} [CommRing C] (M : ModuleCat A) (g : B →+* C) :
    (extendScalars g).obj
        ((AffineStandardDescentData.ofModule f M).obj default) ≅
      (extendScalars g).obj ((extendScalars f).obj M) :=
  (extendScalars g).mapIso (AffineStandardDescentData.ofModuleIso f M)

/-- The left tensor-factor map composed with the original affine map is the
canonical map to the tensor square. -/
lemma affineOverlapLeftRingHom_comp :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    l.comp f = algebraMap A C := by
  rfl

/-- The right tensor-factor map composed with the original affine map is the
canonical map to the tensor square. -/
lemma affineOverlapRightRingHom_comp :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    r.comp f = algebraMap A C := by
  letI : Algebra A B := f.toAlgebra
  change Algebra.TensorProduct.includeRight.toRingHom.comp f =
    Algebra.TensorProduct.includeLeftRingHom.comp f
  simpa only [show f = algebraMap A B from rfl] using
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm

/-- The composite of two extension-of-scalars compositors associated to two
factorizations of the same ring map. -/
noncomputable def mapCompOverlap
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h₁ h₂ : S →+* T) (k : R →+* T)
    (e₁ : h₁.comp g = k) (e₂ : h₂.comp g = k)
    (M : ModuleCat R) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h₁.toAlgebra
    letI : Algebra R T := k.toAlgebra
    (extendScalars h₁).obj ((extendScalars g).obj M) ⟶
      (extendScalars h₂).obj ((extendScalars g).obj M) :=
  (extendScalarsPseudofunctorOpOp.mapComp'
    (CommRingCat.ofHom g).op.op.toLoc
    (CommRingCat.ofHom h₁).op.op.toLoc
    (CommRingCat.ofHom k).op.op.toLoc
    (doubleOpCompEq g h₁ k e₁)).inv.toNatTrans.app M ≫
  (extendScalarsPseudofunctorOpOp.mapComp'
    (CommRingCat.ofHom g).op.op.toLoc
    (CommRingCat.ofHom h₂).op.op.toLoc
    (CommRingCat.ofHom k).op.op.toLoc
    (doubleOpCompEq g h₂ k e₂)).hom.toNatTrans.app M

set_option maxHeartbeats 300000 in
-- Elaborating the pseudofunctor compositor naturality needs additional heartbeats.
/-- The composite of the two extension-of-scalars compositors is natural in
the module over the base ring. -/
lemma mapCompOverlap_naturality
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h₁ h₂ : S →+* T) (k : R →+* T)
    (e₁ : h₁.comp g = k) (e₂ : h₂.comp g = k)
    {M N : ModuleCat R} (a : M ⟶ N) :
    (extendScalars h₁).map ((extendScalars g).map a) ≫
        mapCompOverlap g h₁ h₂ k e₁ e₂ N =
      mapCompOverlap g h₁ h₂ k e₁ e₂ M ≫
        (extendScalars h₂).map ((extendScalars g).map a) := by
  unfold mapCompOverlap
  let fg := (CommRingCat.ofHom g).op.op.toLoc
  let fh₁ := (CommRingCat.ofHom h₁).op.op.toLoc
  let fh₂ := (CommRingCat.ofHom h₂).op.op.toLoc
  let fk := (CommRingCat.ofHom k).op.op.toLoc
  let p₁ := doubleOpCompEq g h₁ k e₁
  let p₂ := doubleOpCompEq g h₂ k e₂
  let β := (extendScalarsPseudofunctorOpOp.mapComp'
    fg fh₂ fk p₂).hom.toNatTrans.app N
  change (extendScalarsPseudofunctorOpOp.map fh₁).toFunctor.map
        ((extendScalarsPseudofunctorOpOp.map fg).toFunctor.map a) ≫
      (extendScalarsPseudofunctorOpOp.mapComp' fg fh₁ fk p₁).inv.toNatTrans.app N ≫ β =
    ((extendScalarsPseudofunctorOpOp.mapComp' fg fh₁ fk p₁).inv.toNatTrans.app M ≫
      (extendScalarsPseudofunctorOpOp.mapComp' fg fh₂ fk p₂).hom.toNatTrans.app M) ≫
      (extendScalarsPseudofunctorOpOp.map fh₂).toFunctor.map
        ((extendScalarsPseudofunctorOpOp.map fg).toFunctor.map a)
  rw [extendScalarsPseudofunctorOpOp.mapComp'_inv_naturality_assoc,
    extendScalarsPseudofunctorOpOp.mapComp'_hom_naturality,
    Category.assoc]

/-- Elementwise formula for `mapCompOverlap`. -/
lemma mapCompOverlap_apply
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (g : R →+* S) (h₁ h₂ : S →+* T) (k : R →+* T)
    (e₁ : h₁.comp g = k) (e₂ : h₂.comp g = k)
    (M : ModuleCat R) (t : T) (s : S) (m : M) :
    letI : Algebra R S := g.toAlgebra
    letI : Algebra S T := h₁.toAlgebra
    letI : Algebra R T := k.toAlgebra
    (mapCompOverlap g h₁ h₂ k e₁ e₂ M).hom
        (t ⊗ₜ[S,h₁] (s ⊗ₜ[R,g] m)) =
      (t * h₁ s) ⊗ₜ[S,h₂] ((1 : S) ⊗ₜ[R,g] m) := by
  exact mapComp'_inv_hom_app_tmul_tmul g h₁ h₂ k e₁ e₂ M t s m

/-- The explicit overlap morphism underlying the canonical affine descent
datum of a module. Keeping this morphism separate avoids dependent carrier
normalization through `DescentData.ofObj` in elementwise calculations. -/
noncomputable def AffineStandardDescentData.ofModuleOverlapHom
    (M : ModuleCat A) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (extendScalars l).obj ((extendScalars f).obj M) ⟶
      (extendScalars r).obj ((extendScalars f).obj M) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let q : A →+* C := algebraMap A C
  exact mapCompOverlap f l r q (affineOverlapLeftRingHom_comp f)
    (affineOverlapRightRingHom_comp f) M

/-- On the canonical affine descent datum, the explicit overlap morphism
moves the middle scalar to the left tensor factor. -/
lemma AffineStandardDescentData.ofModuleOverlapHom_apply
    (M : ModuleCat A) (b : B) (m : M) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (AffineStandardDescentData.ofModuleOverlapHom f M).hom
        ((1 : C) ⊗ₜ[B,l] (b ⊗ₜ[A,f] m)) =
      l b ⊗ₜ[B,r] ((1 : B) ⊗ₜ[A,f] m) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let q : A →+* C := algebraMap A C
  unfold AffineStandardDescentData.ofModuleOverlapHom
  simpa only [one_mul] using mapCompOverlap_apply f l r q
    (affineOverlapLeftRingHom_comp f) (affineOverlapRightRingHom_comp f) M 1 b m

/-- The explicit overlap morphism of the canonical affine descent datum gives
the Beck comparison coaction. -/
lemma AffineStandardDescentData.ofModuleOverlapCoaction
    (M : ModuleCat A) :
    overlapHomEquiv f ((extendScalars f).obj M)
        (AffineStandardDescentData.ofModuleOverlapHom f M) =
      ((Comonad.comparison (extendRestrictScalarsAdj f)).obj M).a := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B ⊗[A] M at x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (.+.) hx hy
  | tmul b m =>
      rw [overlapHomEquiv_apply]
      rw [AffineStandardDescentData.ofModuleOverlapHom_apply]
      change (overlapCancel f ((extendScalars f).obj M)).hom
          (((b ⊗ₜ[A] (1 : B) : B ⊗[A] B)) ⊗ₜ[B,r]
            ((1 : B) ⊗ₜ[A,f] m)) = _
      have h := overlapCancel_tmul_tmul f ((extendScalars f).obj M)
        b 1 ((1 : B) ⊗ₜ[A,f] m)
      rw [one_smul] at h
      rw [h]
      change b ⊗ₜ[A,f] ((1 : B) ⊗ₜ[A,f] m) = _
      exact (ExtendScalars.map_tmul f
        ((extendRestrictScalarsAdj f).unit.app M) b m).symm

end ModuleCat
