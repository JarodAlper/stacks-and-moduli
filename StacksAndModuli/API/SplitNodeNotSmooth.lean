module

public import StacksAndModuli.API.NodalBranches
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Split nodes are not smooth

This file proves the local-algebra bridge from the completed local model
`k[[x,y]]/(xy)` to nonsmoothness. In dimension at most one, equality of maximal-ideal
span ranks under completion is enough: a reduced completion of a regular local ring is
again regular, hence a domain, whereas the standard node has two minimal primes.

## Main results

* `AdicCompletion.isRegularLocalRing_of_isRegularLocalRing_of_isReduced_of_ringKrullDim_le_one`:
  a dimension-one regularity result for reduced maximal-adic completions.
* `AlgebraicGeometry.Scheme.nodeRing_not_isDomain`: the standard split-node ring is not a
  domain.
* `AlgebraicGeometry.Scheme.not_formallySmooth_of_adicCompletion_algEquiv_nodeRing`:
  a local algebra with node completion is not formally smooth in dimension at most one.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.not_formallySmooth_stalkMap_of_ringKrullDim_le_one`:
  the scheme-point specialization.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open IsLocalRing

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- A reduced maximal-adic completion of a regular local ring of dimension at most one is
regular. This avoids requiring a general theorem that completion preserves Krull dimension. -/
theorem isRegularLocalRing_of_isRegularLocalRing_of_isReduced_of_ringKrullDim_le_one
    [IsRegularLocalRing R]
    [IsNoetherianRing (AdicCompletion (maximalIdeal R) R)]
    [IsReduced (AdicCompletion (maximalIdeal R) R)]
    (hdim : ringKrullDim R ≤ 1) :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  by_cases hzero : ringKrullDim (AdicCompletion (maximalIdeal R) R) ≤ 0
  · let _ : Ring.KrullDimLE 0 (AdicCompletion (maximalIdeal R) R) :=
      Ring.krullDimLE_iff.mpr hzero
    let _ : Field (AdicCompletion (maximalIdeal R) R) :=
      Ring.KrullDimLE.isField_of_isReduced.toField
    simp [IsLocalRing.maximalIdeal_eq_bot]
  · have hone : (1 : WithBot ℕ∞) ≤
        ringKrullDim (AdicCompletion (maximalIdeal R) R) := by
      simpa using
        (ENat.WithBot.add_one_le_iff (n := 0)).mpr (lt_of_not_ge hzero)
    calc
      ((maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank : WithBot ℕ∞) =
          ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
            rw [AdicCompletion.spanFinrank_maximalIdeal_eq]
      _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
      _ ≤ 1 := hdim
      _ ≤ ringKrullDim (AdicCompletion (maximalIdeal R) R) := hone

end AdicCompletion

namespace AlgebraicGeometry.Scheme

/-- The standard split-node ring has two minimal primes and therefore is not a domain. -/
theorem nodeRing_not_isDomain (k : Type u) [Field k] :
    ¬ IsDomain (nodeRing k) := by
  intro h
  let _ : IsDomain (nodeRing k) := h
  let e := nodeFormalBranchesEquivFinTwo k
  have hbranches (p q : nodeFormalBranches k) : p = q := by
    apply Subtype.ext
    have hp : p.1 = (⊥ : Ideal (nodeRing k)) := by
      simpa only [IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff] using p.2
    have hq : q.1 = (⊥ : Ideal (nodeRing k)) := by
      simpa only [IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff] using q.2
    exact hp.trans hq.symm
  have h01 : (0 : Fin 2) = 1 :=
    e.symm.injective (hbranches (e.symm 0) (e.symm 1))
  exact Fin.zero_ne_one h01

/-- A Noetherian local finitely presented algebra of dimension at most one whose
maximal-adic completion is a split-node ring is not formally smooth. -/
theorem not_formallySmooth_of_adicCompletion_algEquiv_nodeRing
    (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra.FinitePresentation k R]
    (hdim : ringKrullDim R ≤ 1)
    (e : AdicCompletion (maximalIdeal R) R ≃ₐ[k] nodeRing k) :
    ¬ Algebra.FormallySmooth k R := by
  intro hsmooth
  let _ : Algebra.FormallySmooth k R := hsmooth
  let _ : Algebra.Smooth k R := ⟨hsmooth, inferInstance⟩
  let _ : IsRegularLocalRing (Localization.AtPrime (maximalIdeal R)) :=
    regularAtPrime_of_smooth k R (maximalIdeal R)
  let elocal : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  let _ : IsRegularLocalRing R :=
    IsRegularLocalRing.of_ringEquiv elocal.toRingEquiv.symm
  let _ : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    isNoetherianRing_of_ringEquiv (nodeRing k) e.toRingEquiv.symm
  let _ : _root_.IsReduced (AdicCompletion (maximalIdeal R) R) :=
    _root_.isReduced_of_injective e e.injective
  let _ : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isRegularLocalRing_of_isRegularLocalRing_of_isReduced_of_ringKrullDim_le_one
      hdim
  let _ : IsDomain (AdicCompletion (maximalIdeal R) R) := IsRegularLocalRing.isDomain
  let _ : IsDomain (nodeRing k) := e.symm.injective.isDomain
  exact nodeRing_not_isDomain k inferInstance

/-- A split node on a locally Noetherian, locally finitely presented field-scheme is not
formally smooth whenever its local ring has dimension at most one. -/
theorem IsSplitNodeAt.not_formallySmooth_stalkMap_of_ringKrullDim_le_one
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    [LocallyOfFinitePresentation (C ↘ Spec (CommRingCat.of k))] {x : C}
    (hnode : C.IsSplitNodeAt k x)
    (hdim : ringKrullDim (C.presheaf.stalk x) ≤ 1) :
    ¬ ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth := by
  intro hsmooth
  let _ : IsRegularLocalRing (C.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field
      (C ↘ Spec (CommRingCat.of k)) x hsmooth
  let _ := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
  rcases hnode with ⟨e⟩
  let _ : IsNoetherianRing (C.completedLocalRing x) :=
    isNoetherianRing_of_ringEquiv (nodeRing k) e.toRingEquiv.symm
  let _ : _root_.IsReduced (C.completedLocalRing x) :=
    _root_.isReduced_of_injective e e.injective
  let _ : IsRegularLocalRing (C.completedLocalRing x) :=
    AdicCompletion.isRegularLocalRing_of_isRegularLocalRing_of_isReduced_of_ringKrullDim_le_one
      hdim
  let _ : IsDomain (C.completedLocalRing x) := IsRegularLocalRing.isDomain
  let _ : IsDomain (nodeRing k) := e.symm.injective.isDomain
  exact nodeRing_not_isDomain k inferInstance

end AlgebraicGeometry.Scheme
