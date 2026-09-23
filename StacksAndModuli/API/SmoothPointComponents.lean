module

public import StacksAndModuli.API.FormalBranchComponents
public import StacksAndModuli.API.SmoothStalkReduced

/-!
# Irreducible components through smooth points

This file assigns a point whose local ring is a domain to its unique irreducible component.
For a smooth point of a locally finitely presented scheme over a field, the domain hypothesis
comes from regularity of the local ring.  The construction uses the unique minimal prime of the
stalk and `Scheme.stalkBranchComponent`, so it is compatible with the component assignment for
formal branches.

The indexed wrappers give the component map needed for marked dual graphs.  In particular,
`smoothSectionComponent` accepts sections bundled in the relevant over-category, without
depending on the Chapter 6 stable-curve definitions.

## Main definitions

* `AlgebraicGeometry.Scheme.componentAtOfIsDomainStalk`: the unique component through a point
  whose stalk is a domain.
* `AlgebraicGeometry.Scheme.smoothPointComponent`: the unique component through a smooth point
  over a field.
* `AlgebraicGeometry.Scheme.smoothPointsComponent`: the component map for an indexed family of
  smooth points.
* `AlgebraicGeometry.Scheme.smoothSectionComponent`: the component map for an indexed family of
  smooth sections over a field.

## Main results

* `AlgebraicGeometry.Scheme.eq_of_mem_irreducibleComponents_of_isDomain_stalk`: two components
  through a point with domain stalk coincide.
* `AlgebraicGeometry.Scheme.eq_smoothPointComponent_iff_mem`: a component is the component of a
  smooth point exactly when it contains that point.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- Two irreducible components through a point coincide when the local ring at that point is a
domain. -/
theorem eq_of_mem_irreducibleComponents_of_isDomain_stalk
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)]
    (Z W : irreducibleComponents X) (hxZ : x ∈ Z.1) (hxW : x ∈ W.1) :
    Z = W := by
  let U := X.branchAffineOpen x
  let hU : IsAffineOpen U :=
    isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let hxU : x ∈ U := X.affineCover.covers x
  let xU : U := ⟨x, hxU⟩
  let e : U ≃ₜ Spec Γ(X, U) := hU.isoSpec.hom.homeomorph
  let ZU : Set U := U.ι ⁻¹' Z.1
  let WU : Set U := U.ι ⁻¹' W.1
  have hZU_nonempty : ZU.Nonempty := ⟨xU, hxZ⟩
  have hWU_nonempty : WU.Nonempty := ⟨xU, hxW⟩
  have hZU : ZU ∈ irreducibleComponents U := by
    apply preimage_mem_irreducibleComponents Z.2 U.ι.isOpenEmbedding
    exact ⟨x, hxZ, xU, rfl⟩
  have hWU : WU ∈ irreducibleComponents U := by
    apply preimage_mem_irreducibleComponents W.2 U.ι.isOpenEmbedding
    exact ⟨x, hxW, xU, rfl⟩
  let SZ : Set (Spec Γ(X, U)) := e '' ZU
  let SW : Set (Spec Γ(X, U)) := e '' WU
  have he_fiber : ∀ y, IsPreirreducible (e ⁻¹' ({y} : Set (Spec Γ(X, U)))) :=
    fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible
  have hSZ : SZ ∈ irreducibleComponents (Spec Γ(X, U)) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
      e.isOpenMap he_fiber e.surjective hZU
  have hSW : SW ∈ irreducibleComponents (Spec Γ(X, U)) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
      e.isOpenMap he_fiber e.surjective hWU
  let qZ : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal SZ
  let qW : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal SW
  have hqZ : qZ ∈ minimalPrimes Γ(X, U) := by
    rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
    exact ⟨SZ, hSZ, rfl⟩
  have hqW : qW ∈ minimalPrimes Γ(X, U) := by
    rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
    exact ⟨SW, hSW, rfl⟩
  let _ : qZ.IsPrime := hqZ.isPrime
  let _ : qW.IsPrime := hqW.isPrime
  let p : Ideal Γ(X, U) := (hU.primeIdealOf xU).asIdeal
  have hqZp : qZ ≤ p := by
    intro a ha
    exact (PrimeSpectrum.mem_vanishingIdeal SZ a).mp ha (e xU) ⟨xU, hxZ, rfl⟩
  have hqWp : qW ≤ p := by
    intro a ha
    exact (PrimeSpectrum.mem_vanishingIdeal SW a).mp ha (e xU) ⟨xU, hxW, rfl⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk xU
  have hqZ_map : qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
      minimalPrimes (X.presheaf.stalk x) := by
    have hmem : qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
        ((⊥ : Ideal Γ(X, U)).map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map p.primeCompl (X.presheaf.stalk x)]
      change (qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) ∈
        minimalPrimes Γ(X, U)
      rw [Ideal.under_map_of_isLocalizationAtPrime p hqZp]
      exact hqZ
    simpa only [Ideal.map_bot] using hmem
  have hqW_map : qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
      minimalPrimes (X.presheaf.stalk x) := by
    have hmem : qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
        ((⊥ : Ideal Γ(X, U)).map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map p.primeCompl (X.presheaf.stalk x)]
      change (qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) ∈
        minimalPrimes Γ(X, U)
      rw [Ideal.under_map_of_isLocalizationAtPrime p hqWp]
      exact hqW
    simpa only [Ideal.map_bot] using hmem
  have hqZ_map_bot :
      qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) = ⊥ := by
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using hqZ_map
  have hqW_map_bot :
      qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) = ⊥ := by
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using hqW_map
  have hunderZ :
      (qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) = qZ :=
    Ideal.under_map_of_isLocalizationAtPrime (S := X.presheaf.stalk x) p hqZp
  have hunderW :
      (qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) = qW :=
    Ideal.under_map_of_isLocalizationAtPrime (S := X.presheaf.stalk x) p hqWp
  have hq : qZ = qW := by
    calc
      qZ = (qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) :=
        hunderZ.symm
      _ = (⊥ : Ideal (X.presheaf.stalk x)).under Γ(X, U) :=
        congrArg (fun J : Ideal (X.presheaf.stalk x) ↦ J.under Γ(X, U)) hqZ_map_bot
      _ = (qW.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) :=
        congrArg (fun J : Ideal (X.presheaf.stalk x) ↦ J.under Γ(X, U)) hqW_map_bot.symm
      _ = qW := hunderW
  have hSZ_closed : IsClosed SZ := isClosed_of_mem_irreducibleComponents SZ hSZ
  have hSW_closed : IsClosed SW := isClosed_of_mem_irreducibleComponents SW hSW
  have hSZW : SZ = SW := by
    calc
      SZ = closure SZ := hSZ_closed.closure_eq.symm
      _ = PrimeSpectrum.zeroLocus qZ :=
        (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure SZ).symm
      _ = PrimeSpectrum.zeroLocus qW :=
        congrArg (fun q : Ideal Γ(X, U) ↦ PrimeSpectrum.zeroLocus (q : Set Γ(X, U))) hq
      _ = closure SW := PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure SW
      _ = SW := hSW_closed.closure_eq
  have hZUWU : ZU = WU := Set.image_injective.mpr e.injective hSZW
  have hrecoverZ : closure (U.ι '' ZU) = Z.1 :=
    closure_image_preimage_of_isPreirreducible U.ι U.ι.isOpenEmbedding.isOpenMap Z.1
      hZU_nonempty Z.2.1.2 (isClosed_of_mem_irreducibleComponents Z.1 Z.2)
  have hrecoverW : closure (U.ι '' WU) = W.1 :=
    closure_image_preimage_of_isPreirreducible U.ι U.ι.isOpenEmbedding.isOpenMap W.1
      hWU_nonempty W.2.1.2 (isClosed_of_mem_irreducibleComponents W.1 W.2)
  apply Subtype.ext
  exact hrecoverZ.symm.trans ((congrArg (fun T : Set U ↦ closure (U.ι '' T)) hZUWU).trans
    hrecoverW)

/-- The unique irreducible component through a point whose local ring is a domain. It is
constructed from the unique minimal prime of the stalk. -/
noncomputable def componentAtOfIsDomainStalk
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)] :
    irreducibleComponents X :=
  X.stalkBranchComponent x ⟨⊥, by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton ⊥⟩

/-- A point with domain stalk lies on its canonical irreducible component. -/
theorem mem_componentAtOfIsDomainStalk
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)] :
    x ∈ (X.componentAtOfIsDomainStalk x).1 :=
  X.stalkBranchComponent_mem x _

/-- A component is the canonical component through a point with domain stalk exactly when it
contains that point. -/
@[simp]
theorem eq_componentAtOfIsDomainStalk_iff_mem
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)]
    (Z : irreducibleComponents X) :
    Z = X.componentAtOfIsDomainStalk x ↔ x ∈ Z.1 := by
  constructor
  · rintro rfl
    exact X.mem_componentAtOfIsDomainStalk x
  · intro hxZ
    exact X.eq_of_mem_irreducibleComponents_of_isDomain_stalk x Z
      (X.componentAtOfIsDomainStalk x) hxZ (X.mem_componentAtOfIsDomainStalk x)

/-- The irreducible component containing a point with domain stalk exists uniquely. -/
theorem existsUnique_irreducibleComponent_of_isDomain_stalk
    (X : Scheme.{u}) (x : X) [IsDomain (X.presheaf.stalk x)] :
    ∃! Z : irreducibleComponents X, x ∈ Z.1 := by
  refine ⟨X.componentAtOfIsDomainStalk x, X.mem_componentAtOfIsDomainStalk x, ?_⟩
  intro Z hxZ
  exact X.eq_of_mem_irreducibleComponents_of_isDomain_stalk x Z
    (X.componentAtOfIsDomainStalk x) hxZ (X.mem_componentAtOfIsDomainStalk x)

/-- The unique irreducible component through a formally smooth point of a locally finitely
presented scheme over a field. -/
noncomputable def smoothPointComponent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : X) (hx : (f.stalkMap x).hom.FormallySmooth) :
    irreducibleComponents X := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field f x hx
  let _ : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain
  exact X.componentAtOfIsDomainStalk x

/-- A formally smooth point lies on its smooth-point component. -/
theorem mem_smoothPointComponent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : X) (hx : (f.stalkMap x).hom.FormallySmooth) :
    x ∈ (X.smoothPointComponent f x hx).1 := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field f x hx
  let _ : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain
  exact X.mem_componentAtOfIsDomainStalk x

/-- A component is the smooth-point component exactly when it contains the smooth point. -/
@[simp]
theorem eq_smoothPointComponent_iff_mem
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : X) (hx : (f.stalkMap x).hom.FormallySmooth)
    (Z : irreducibleComponents X) :
    Z = X.smoothPointComponent f x hx ↔ x ∈ Z.1 := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field f x hx
  let _ : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain
  exact X.eq_componentAtOfIsDomainStalk_iff_mem x Z

/-- The component map of an indexed family of formally smooth points over a field. -/
noncomputable def smoothPointsComponent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v} (p : I → X)
    (hp : ∀ i, (f.stalkMap (p i)).hom.FormallySmooth) :
    I → irreducibleComponents X :=
  fun i ↦ X.smoothPointComponent f (p i) (hp i)

/-- The component map of a smooth point family is computed pointwise. -/
@[simp]
theorem smoothPointsComponent_apply
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v} (p : I → X)
    (hp : ∀ i, (f.stalkMap (p i)).hom.FormallySmooth) (i : I) :
    X.smoothPointsComponent f p hp i = X.smoothPointComponent f (p i) (hp i) :=
  rfl

/-- Each point in a smooth point family lies on the component assigned to its index. -/
theorem smoothPointsComponent_mem
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v} (p : I → X)
    (hp : ∀ i, (f.stalkMap (p i)).hom.FormallySmooth) (i : I) :
    p i ∈ (X.smoothPointsComponent f p hp i).1 :=
  X.mem_smoothPointComponent f (p i) (hp i)

/-- The component map of smooth sections of a locally finitely presented scheme over a
field. The sections are bundled in the over-category, so the source triangle records their
section equations. -/
noncomputable def smoothSectionComponent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v}
    (p : I → ((Over.mk (𝟙 (Spec (.of K))) : Over (Spec (.of K))) ⟶
      (Over.mk f : Over (Spec (.of K)))))
    (hp : ∀ i, (f.stalkMap ((p i).left (IsLocalRing.closedPoint K))).hom.FormallySmooth) :
    I → irreducibleComponents X :=
  X.smoothPointsComponent f (fun i ↦ (p i).left (IsLocalRing.closedPoint K)) hp

/-- The component map of smooth sections is the smooth-point component of the value of each
section at the unique point of the field spectrum. -/
@[simp]
theorem smoothSectionComponent_apply
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v}
    (p : I → ((Over.mk (𝟙 (Spec (.of K))) : Over (Spec (.of K))) ⟶
      (Over.mk f : Over (Spec (.of K)))))
    (hp : ∀ i, (f.stalkMap ((p i).left (IsLocalRing.closedPoint K))).hom.FormallySmooth)
    (i : I) :
    X.smoothSectionComponent f p hp i =
      X.smoothPointComponent f ((p i).left (IsLocalRing.closedPoint K)) (hp i) :=
  rfl

/-- The value of every smooth section lies on the component assigned to that section. -/
theorem smoothSectionComponent_mem
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {I : Type v}
    (p : I → ((Over.mk (𝟙 (Spec (.of K))) : Over (Spec (.of K))) ⟶
      (Over.mk f : Over (Spec (.of K)))))
    (hp : ∀ i, (f.stalkMap ((p i).left (IsLocalRing.closedPoint K))).hom.FormallySmooth)
    (i : I) :
    (p i).left (IsLocalRing.closedPoint K) ∈ (X.smoothSectionComponent f p hp i).1 :=
  X.smoothPointsComponent_mem f _ hp i

end AlgebraicGeometry.Scheme
