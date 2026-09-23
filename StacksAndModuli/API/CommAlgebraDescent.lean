module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Effective descent for commutative algebras

This file gives the equalizer construction for a commutative algebra equipped with a
multiplicative descent coaction.  It is the affine algebraic core of fpqc descent for
schemes: the descended algebra is the equalizer of the coaction and the unit map, and
flat base change reconstructs the original algebra.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u

namespace Algebra

/-- A commutative `B`-algebra with a counital, coassociative multiplicative descent
coaction relative to `A → B`.

The `A`-algebra structure on `carrier` is required to be the one induced through `B`.
The coaction takes values in `B ⊗[A] carrier`; its two identities are the algebraic
unit and cocycle conditions for singleton descent. -/
structure CommAlgebraDescentData (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] where
  carrier : Type u
  commRingD : CommRing carrier
  algebraBD : Algebra B carrier
  algebraAD : Algebra A carrier
  towerABD : IsScalarTower A B carrier
  coaction : carrier →ₐ[B] B ⊗[A] carrier
  counit : ∀ d, (Algebra.TensorProduct.lift (Algebra.ofId B carrier)
      (AlgHom.id A carrier) (fun _ _ ↦ Commute.all _ _)) (coaction d) = d
  coassoc : ∀ d,
    Algebra.TensorProduct.map (AlgHom.id B B) (coaction.restrictScalars A) (coaction d) =
      Algebra.TensorProduct.map (AlgHom.id B B)
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := carrier)) (coaction d)

attribute [instance] CommAlgebraDescentData.commRingD
  CommAlgebraDescentData.algebraBD CommAlgebraDescentData.algebraAD
  CommAlgebraDescentData.towerABD

namespace CommAlgebraDescentData

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (D : CommAlgebraDescentData A B)

/-- The unit map against which the coaction is equalized. -/
noncomputable def unitMap : D.carrier →ₐ[A] B ⊗[A] D.carrier :=
  Algebra.TensorProduct.includeRight

/-- The descended `A`-algebra: elements fixed by the descent coaction. -/
noncomputable def invariants : Subalgebra A D.carrier :=
  AlgHom.equalizer (D.coaction.restrictScalars A) D.unitMap

/-- The equalizer obtained after extending the invariant algebra from `A` to `B`. -/
noncomputable def baseChangeEqualizer : Subalgebra B (B ⊗[A] D.carrier) :=
  AlgHom.equalizer
    (Algebra.TensorProduct.map (R := A) (S := B)
      (AlgHom.id B B) (D.coaction.restrictScalars A))
    (Algebra.TensorProduct.map (R := A) (S := B)
      (AlgHom.id B B) D.unitMap)

/-- Contract the leading `B` tensor factor using the `B`-algebra structure. -/
noncomputable def counitMap : B ⊗[A] D.carrier →ₐ[B] D.carrier :=
  Algebra.TensorProduct.lift (Algebra.ofId B D.carrier) (AlgHom.id A D.carrier)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
lemma counitMap_tmul (b : B) (d : D.carrier) :
    D.counitMap (b ⊗ₜ[A] d) = b • d := by
  simp [counitMap, Algebra.smul_def]

/-- Contract the first two factors of `B ⊗[A] (B ⊗[A] D)`. -/
noncomputable def flattenMap :
    B ⊗[A] (B ⊗[A] D.carrier) →ₐ[B] B ⊗[A] D.carrier :=
  Algebra.TensorProduct.lift (Algebra.ofId B (B ⊗[A] D.carrier))
    (AlgHom.id A (B ⊗[A] D.carrier)) (fun _ _ ↦ Commute.all _ _)

lemma flattenMap_map_coaction (x : B ⊗[A] D.carrier) :
    D.flattenMap (Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
      (D.coaction.restrictScalars A) x) = D.coaction (D.counitMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b d => simp [flattenMap, counitMap]
  | add x y hx hy => simp [hx, hy]

lemma flattenMap_map_unitMap (x : B ⊗[A] D.carrier) :
    D.flattenMap (Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
      D.unitMap x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b d => simp [flattenMap, unitMap]
  | add x y hx hy => simp [hx, hy]

/-- The coaction lands in the equalizer obtained after base change. -/
noncomputable def coactionToBaseChangeEqualizer :
    D.carrier →ₐ[B] D.baseChangeEqualizer :=
  D.coaction.codRestrict D.baseChangeEqualizer (fun d ↦ by
    change
      Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
          (D.coaction.restrictScalars A) (D.coaction d) =
        Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
          D.unitMap (D.coaction d)
    exact D.coassoc d)

/-- The counit restricted to the equalizer after base change. -/
noncomputable def baseChangeEqualizerToD : D.baseChangeEqualizer →ₐ[B] D.carrier :=
  D.counitMap.comp D.baseChangeEqualizer.val

@[simp]
lemma baseChangeEqualizerToD_coactionToBaseChangeEqualizer (d : D.carrier) :
    D.baseChangeEqualizerToD (D.coactionToBaseChangeEqualizer d) = d := by
  exact D.counit d

lemma coaction_counitMap_eq_of_mem_baseChangeEqualizer
    (x : B ⊗[A] D.carrier) (hx : x ∈ D.baseChangeEqualizer) :
    D.coaction (D.counitMap x) = x := by
  have hx' :
      Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
          (D.coaction.restrictScalars A) x =
        Algebra.TensorProduct.map (R := A) (S := B) (AlgHom.id B B)
          D.unitMap x := hx
  rw [← D.flattenMap_map_coaction x, hx', D.flattenMap_map_unitMap]

/-- The coaction identifies the original algebra with the equalizer after base change. -/
noncomputable def baseChangeEqualizerIsoD :
    CommAlgCat.of B D.baseChangeEqualizer ≅ CommAlgCat.of B D.carrier := by
  refine CommAlgCat.isoMk (AlgEquiv.ofAlgHom D.baseChangeEqualizerToD
    D.coactionToBaseChangeEqualizer ?_ ?_)
  · ext d
    exact D.baseChangeEqualizerToD_coactionToBaseChangeEqualizer d
  · ext x
    exact D.coaction_counitMap_eq_of_mem_baseChangeEqualizer x.1 x.2

/-- Effective flat descent for a multiplicative coaction: extending the invariant
`A`-algebra to `B` recovers the original `B`-algebra. -/
noncomputable def baseChangeIso [Module.Flat A B] :
    B ⊗[A] D.invariants ≃ₐ[B] D.carrier :=
  (AlgHom.tensorEqualizerEquiv B B (D.coaction.restrictScalars A) D.unitMap).trans
    (CommAlgCat.algEquivOfIso D.baseChangeEqualizerIsoD)

@[simp]
lemma baseChangeIso_tmul [Module.Flat A B] (b : B) (c : D.invariants) :
    D.baseChangeIso (b ⊗ₜ[A] c) = b • (c : D.carrier) := by
  change D.counitMap
      (((AlgHom.tensorEqualizerEquiv B B (D.coaction.restrictScalars A) D.unitMap)
        (b ⊗ₜ[A] c) : D.baseChangeEqualizer) : B ⊗[A] D.carrier) = _
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
  rw [Algebra.TensorProduct.map_tmul]
  simp [counitMap, Algebra.smul_def]

end CommAlgebraDescentData

end Algebra
