module

public import StacksAndModuli.API.CommAlgebraDescent
public import StacksAndModuli.Util.FpqcCover
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine schemes from commutative-algebra descent data

This file realizes a multiplicative algebra descent coaction geometrically.  The
invariant algebra defines an affine scheme over the base, and the algebraic base-change
equivalence identifies its pullback with the original affine scheme.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Algebra.CommAlgebraDescentData

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (D : CommAlgebraDescentData A B)

/-- The affine scheme of the invariant algebra. -/
noncomputable def descendedScheme : Scheme.{u} :=
  Spec (.of D.invariants)

/-- The descended affine scheme's structure morphism to `Spec A`. -/
noncomputable def descendedHom : D.descendedScheme ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A D.invariants))

/-- The affine covering morphism associated to `A → B`. -/
noncomputable def coverHom (_D : CommAlgebraDescentData A B) :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The affine scheme before descent. -/
noncomputable def originalScheme : Scheme.{u} :=
  Spec (.of D.carrier)

/-- The original affine scheme's structure morphism to `Spec B`. -/
noncomputable def originalHom : D.originalScheme ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B D.carrier))

/-- The underlying ring equivalence used to compare the original scheme with the
pullback of the descended scheme. -/
noncomputable def descentRingEquiv [Module.Flat A B] :
    RingEquiv (TensorProduct A D.invariants B) D.carrier :=
  ((Algebra.TensorProduct.comm A D.invariants B).trans
    (D.baseChangeIso.restrictScalars A)).toRingEquiv

/-- The original affine scheme is the pullback of the descended affine scheme along
`Spec B → Spec A`. -/
noncomputable def comparisonIso [Module.Flat A B] :
    D.originalScheme ≅ pullback D.descendedHom D.coverHom :=
  Scheme.Spec.mapIso D.descentRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso A D.invariants B).symm

@[reassoc]
lemma comparisonIso_hom_snd [Module.Flat A B] :
    D.comparisonIso.hom ≫ pullback.snd D.descendedHom D.coverHom = D.originalHom := by
  dsimp [comparisonIso, originalScheme, descendedScheme, descendedHom, coverHom, originalHom]
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp]
  congr 1
  ext b
  change D.baseChangeIso (b ⊗ₜ[A] (1 : D.invariants)) = (algebraMap B D.carrier) b
  rw [D.baseChangeIso_tmul]
  simp [Algebra.smul_def]

/-- The faithfully-flat base change from the original affine scheme to the descended
affine scheme. -/
noncomputable def descentCoverHom [Module.Flat A B] :
    D.originalScheme ⟶ D.descendedScheme :=
  D.comparisonIso.hom ≫ pullback.fst D.descendedHom D.coverHom

@[reassoc]
lemma descentCoverHom_comp [Module.Flat A B] :
    D.descentCoverHom ≫ D.descendedHom = D.originalHom ≫ D.coverHom := by
  rw [descentCoverHom, Category.assoc, pullback.condition]
  rw [← D.comparisonIso_hom_snd_assoc]

lemma descentCoverHom_flat [Module.Flat A B]
    (hff : (algebraMap A B).FaithfullyFlat) : Flat D.descentCoverHom := by
  letI : Flat D.coverHom :=
    (flat_and_surjective_SpecMap_iff _).mpr hff |>.1
  dsimp [descentCoverHom]
  infer_instance

lemma descentCoverHom_surjective [Module.Flat A B]
    (hff : (algebraMap A B).FaithfullyFlat) : Surjective D.descentCoverHom := by
  letI : Surjective D.coverHom :=
    (flat_and_surjective_SpecMap_iff _).mpr hff |>.2
  dsimp [descentCoverHom]
  infer_instance

lemma descentCoverHom_quasiCompact [Module.Flat A B] : QuasiCompact D.descentCoverHom := by
  dsimp [descentCoverHom]
  infer_instance

/-- The map from the original affine scheme to the descended affine scheme is an fpqc
cover whenever `A → B` is faithfully flat. -/
lemma descentCoverHom_isFpqcCover [Module.Flat A B]
    (hff : (algebraMap A B).FaithfullyFlat) : Scheme.IsFpqcCover D.descentCoverHom := by
  letI : Flat D.descentCoverHom := D.descentCoverHom_flat hff
  letI : Surjective D.descentCoverHom := D.descentCoverHom_surjective hff
  letI : QuasiCompact D.descentCoverHom := D.descentCoverHom_quasiCompact
  exact Scheme.IsFpqcCover.of_flat_of_surjective_of_quasiCompact D.descentCoverHom

end Algebra.CommAlgebraDescentData
