module

public import StacksAndModuli.API.PowerSeriesCompletionRegular
public import StacksAndModuli.API.SmoothStalkReduced

/-!
# Regular stalks are smooth over an algebraically closed field

For a scheme locally of finite presentation over an algebraically closed field, regularity
of one local ring implies formal smoothness at that point.  This is the pointwise converse
to `Scheme.isRegularLocalRing_stalk_of_formallySmooth_toSpec_field`.

The proof passes to an affine neighbourhood, transfers regularity to the localization of
its section ring, and applies the regular-local direction of Stacks Project tag `00TV`.

## Main result

* `AlgebraicGeometry.Scheme.formallySmooth_stalk_of_isRegularLocalRing_toSpec_isAlgClosed`:
  a regular stalk of a locally finitely presented scheme over an algebraically closed field
  is formally smooth.
* `Scheme.formallySmooth_stalk_of_adicCompletion_equiv_powerSeries_toSpec_isAlgClosed`:
  a stalk whose completion is `k[[t]]` is formally smooth.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A regular stalk of a scheme locally of finite presentation over an algebraically closed
field is formally smooth over that field. -/
theorem formallySmooth_stalk_of_isRegularLocalRing_toSpec_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    (p.stalkMap x).hom.FormallySmooth := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : (Spec (.of K)).Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top _
  have hVU : V ≤ p ⁻¹ᵁ U := le_top
  have hpfin := p.finitePresentation_appLE hU hV hVU
  let e : K ≃+* Γ(Spec (.of K), U) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let _ : Field Γ(Spec (.of K), U) :=
    (e.symm.isField (Field.toIsField K)).toField
  let _ : IsAlgClosed Γ(Spec (.of K), U) :=
    IsAlgClosed.of_ringEquiv (k := K) Γ(Spec (.of K), U) e
  let φ := p.appLE U V hVU
  algebraize [φ.hom]
  let _ : Algebra.FinitePresentation Γ(Spec (.of K), U) Γ(X, V) := hpfin
  rw [formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let _ : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).toRingEquiv.symm
  let _ : Algebra.EssFiniteType Γ(Spec (.of K), U) q.ResidueField :=
    Algebra.EssFiniteType.comp Γ(Spec (.of K), U) Γ(X, V) q.ResidueField
  let _ : Algebra.FormallySmooth Γ(Spec (.of K), U) q.ResidueField := inferInstance
  exact Algebra.FormallySmooth.of_isRegularLocalRing_localization_atPrime
    Γ(Spec (.of K), U) Γ(X, V) q

/-- A Noetherian domain stalk whose completion is a one-variable power-series ring is
formally smooth over an algebraically closed base field. -/
theorem formallySmooth_stalk_of_adicCompletion_equiv_powerSeries_toSpec_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    [IsDomain (X.presheaf.stalk x)]
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* PowerSeries K) :
    (p.stalkMap x).hom.FormallySmooth := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_of_adicCompletion_equiv_powerSeries K
      (X.presheaf.stalk x) e
  exact formallySmooth_stalk_of_isRegularLocalRing_toSpec_isAlgClosed p x

end AlgebraicGeometry.Scheme
