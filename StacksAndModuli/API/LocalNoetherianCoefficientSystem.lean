module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# A local ring as a limit of local Noetherian rings

For a local ring `R`, consider the finitely generated `ℤ`-subalgebras `A ⊆ R`.  Localizing
each `A` at the inverse image of the maximal ideal of `R` gives a directed system of local
Noetherian rings.  Its direct limit is canonically isomorphic to `R`.

This is the coefficient-ring layer in the approximation system used in the proof of Stacks
Project tag 00QX.  The rest of that system must also descend an algebra and a finite module,
with transition maps given by localization.
-/

@[expose] public section

open IsLocalRing

universe u

namespace LocalNoetherianApproximation

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Finitely generated `ℤ`-subalgebras of a local ring, ordered by inclusion. -/
abbrev Index := { A : Subalgebra ℤ R // A.FG }

instance : Nonempty (Index R) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance : IsDirectedOrder (Index R) where
  directed a b := by
    let c : Index R := ⟨a.1 ⊔ b.1, a.2.sup b.2⟩
    exact ⟨c,
      show a.1 ≤ c.1 from le_sup_left,
      show b.1 ≤ c.1 from le_sup_right⟩

/-- The local Noetherian coefficient ring associated to a finitely generated subalgebra. -/
noncomputable def coefficient (i : Index R) : Type u :=
  Localization.AtPrime ((maximalIdeal R).comap i.1.val)

instance (i : Index R) : CommRing (coefficient R i) := by
  dsimp [coefficient]
  infer_instance

instance (i : Index R) : Algebra i.1 (coefficient R i) := by
  dsimp [coefficient]
  infer_instance

instance (i : Index R) :
    IsLocalization ((maximalIdeal R).comap i.1.val).primeCompl (coefficient R i) := by
  change IsLocalization ((maximalIdeal R).comap i.1.val).primeCompl
    (Localization ((maximalIdeal R).comap i.1.val).primeCompl)
  exact Localization.isLocalization

instance (i : Index R) : IsLocalRing (coefficient R i) := by
  dsimp [coefficient]
  infer_instance

instance (i : Index R) : IsNoetherianRing (coefficient R i) := by
  dsimp [coefficient]
  let _ : Algebra.FiniteType ℤ i.1 := (Subalgebra.fg_iff_finiteType i.1).mp i.2
  let _ : IsNoetherianRing i.1 := Algebra.FiniteType.isNoetherianRing ℤ i.1
  infer_instance

/-- Inclusion of coefficient subalgebras induces a local homomorphism between their
localizations. -/
noncomputable def transition (i j : Index R) (h : i ≤ j) :
    coefficient R i →+* coefficient R j := by
  let f : i.1 →+* j.1 := (Subalgebra.inclusion h).toRingHom
  let p := (maximalIdeal R).comap i.1.val
  let q := (maximalIdeal R).comap j.1.val
  have hpq : p = q.comap f := by
    ext x
    rfl
  exact Localization.localRingHom p q f hpq

@[simp]
theorem transition_algebraMap (i j : Index R) (h : i ≤ j) (x : i.1) :
    transition R i j h (algebraMap i.1 (coefficient R i) x) =
      algebraMap j.1 (coefficient R j) ((Subalgebra.inclusion h) x) := by
  unfold transition
  exact Localization.localRingHom_to_map _ _ _ _ _

instance (i j : Index R) (h : i ≤ j) :
    IsLocalHom (transition R i j h) := by
  dsimp only [transition]
  apply Localization.isLocalHom_localRingHom

instance : DirectedSystem (coefficient R) (transition R · · · ·) where
  map_self {i} x := by
    have heq : transition R i i le_rfl = RingHom.id _ := by
      apply IsLocalization.ringHom_ext
        ((maximalIdeal R).comap i.1.val).primeCompl
      ext y
      change transition R i i le_rfl (algebraMap i.1 (coefficient R i) y) =
        algebraMap i.1 (coefficient R i) y
      simp
    exact DFunLike.congr_fun heq x
  map_map {k j i} hij hjk x := by
    have heq : (transition R j k hjk).comp (transition R i j hij) =
        transition R i k (hij.trans hjk) := by
      apply IsLocalization.ringHom_ext
        ((maximalIdeal R).comap i.1.val).primeCompl
      ext y
      change transition R j k hjk
          (transition R i j hij (algebraMap i.1 (coefficient R i) y)) =
        transition R i k (hij.trans hjk) (algebraMap i.1 (coefficient R i) y)
      simp
    exact DFunLike.congr_fun heq x

/-- The compatible map from a coefficient stage to the original local ring. -/
noncomputable def toLimit (i : Index R) : coefficient R i →+* R := by
  refine IsLocalization.lift
    (M := ((maximalIdeal R).comap i.1.val).primeCompl)
    (S := coefficient R i) (P := R) (g := i.1.val) ?_
  rintro ⟨x, hx⟩
  exact IsLocalRing.notMem_maximalIdeal.mp hx

@[simp]
theorem toLimit_algebraMap (i : Index R) (x : i.1) :
    toLimit R i (algebraMap i.1 (coefficient R i) x) = (x : R) := by
  simp [toLimit, IsLocalization.lift_eq]

/-- The canonical inclusion of the coefficient subalgebra into its localization. -/
noncomputable def ofBase (i : Index R) : i.1 →+* coefficient R i :=
  algebraMap i.1 (coefficient R i)

@[simp]
theorem toLimit_ofBase (i : Index R) (x : i.1) :
    toLimit R i (ofBase R i x) = (x : R) :=
  toLimit_algebraMap R i x

theorem toLimit_injective (i : Index R) : Function.Injective (toLimit R i) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    ((maximalIdeal R).comap i.1.val).primeCompl (toLimit R i)]
  intro x y
  constructor
  · intro h
    simpa only [toLimit_algebraMap] using congrArg (toLimit R i) h
  · intro h
    have hxy : (x : R) = (y : R) := by
      simpa only [toLimit_algebraMap] using h
    exact congrArg (algebraMap i.1 (coefficient R i)) (Subtype.ext hxy)

theorem toLimit_transition (i j : Index R) (h : i ≤ j) (x : coefficient R i) :
    toLimit R j (transition R i j h x) = toLimit R i x := by
  have heq : (toLimit R j).comp (transition R i j h) = toLimit R i := by
    apply IsLocalization.ringHom_ext
      ((maximalIdeal R).comap i.1.val).primeCompl
    ext y
    change toLimit R j
        (transition R i j h (algebraMap i.1 (coefficient R i) y)) =
      toLimit R i (algebraMap i.1 (coefficient R i) y)
    simp
  exact DFunLike.congr_fun heq x

/-- The map from the direct limit of the coefficient system to the original local ring. -/
noncomputable def limitMap :
    Ring.DirectLimit (coefficient R) (fun i j h => transition R i j h) →+* R :=
  Ring.DirectLimit.lift _ _ _ (toLimit R) (toLimit_transition R)

theorem limitMap_injective : Function.Injective (limitMap R) :=
  Ring.DirectLimit.lift_injective R (toLimit R) (toLimit_transition R)
    (fun i ↦ toLimit_injective R i)

theorem limitMap_surjective : Function.Surjective (limitMap R) := by
  intro x
  let s : Finset R := {x}
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ (s : Set R)
  let i : Index R := ⟨A, Subalgebra.fg_adjoin_finset s⟩
  have hxA : x ∈ A := Algebra.subset_adjoin (by simp [s])
  let y : i.1 := ⟨x, hxA⟩
  refine ⟨Ring.DirectLimit.of (coefficient R)
    (fun i j h ↦ transition R i j h) i
      (ofBase R i y), ?_⟩
  rw [show limitMap R (Ring.DirectLimit.of (coefficient R)
      (fun i j h ↦ transition R i j h) i (ofBase R i y)) =
        toLimit R i (ofBase R i y) by
    apply Ring.DirectLimit.lift_of]
  rw [toLimit_ofBase]

/-- A local ring is the direct limit of its local Noetherian coefficient rings. -/
noncomputable def limitEquiv :
    Ring.DirectLimit (coefficient R) (fun i j h ↦ transition R i j h) ≃+* R :=
  RingEquiv.ofBijective (limitMap R) ⟨limitMap_injective R, limitMap_surjective R⟩

end LocalNoetherianApproximation
