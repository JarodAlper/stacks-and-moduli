module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianImmersionPackage
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackageFromGeometry
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualVeryAmple

/-!
# Eventual intrinsic Quot-to-Grassmannian immersion packages

This is the presentation-independent eventual interface for the Quot construction.
For every sufficiently large twist it retains the canonical transformation and its
relative immersion, but does not remember whether the latter was proved using a finite
intersection or a directly represented projective flattening locus.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eventual availability of the minimal canonical Quot-to-Grassmannian immersion
package. -/
def HasEventualTwistedFreeQuotGrassmannianImmersionPackages
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
    ∃ e : ℕ, ∃ he : (d : ℤ) - l = (e : ℤ), ∃ m : ℕ,
      ∃ σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n),
        Nonempty (TwistedFreeQuotGrassmannianImmersionPackage
          n S l r P d e he m (P.hilbertNatValue d) σ)

namespace HasEventualTwistedFreeQuotGrassmannianImmersionPackages

/-- The finite-intersection eventual package canonically forgets to the intrinsic
immersion package. -/
theorem ofCanonicalPackages
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    (H : HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  obtain ⟨D, hD⟩ := H
  refine ⟨D, fun d hd ↦ ?_⟩
  obtain ⟨e, he, m, σ, ⟨C⟩⟩ := hD d hd
  exact ⟨e, he, m, σ, ⟨
    TwistedFreeQuotGrassmannianImmersionPackage.ofCanonicalPackage C⟩⟩

/-- One sufficiently large degree supplies W6. -/
theorem w6
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    (H : HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P := by
  obtain ⟨D, hD⟩ := H
  obtain ⟨e, he, m, σ, ⟨C⟩⟩ := hD D le_rfl
  exact C.w6

end HasEventualTwistedFreeQuotGrassmannianImmersionPackages

/-- Uniform canonical inputs and kernel generation, together with one flattening locus
on each sufficiently large universal Grassmannian reconstruction, produce the eventual
intrinsic immersion packages. -/
theorem hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalGeometry
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n) (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d)
    (hflattening : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := P.hilbertNatValue d) (l := l)
              (d := d) (e := e) (he := he)
              (σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n))
              (grassmannianOverRepresentation S (P.hilbertNatValue d)
                (r * (n + e).choose n))
              (freeGrassmannianUniversalPoint S (P.hilbertNatValue d)
                (r * (n + e).choose n))) P)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  obtain ⟨DI, hI⟩ := hinputs
  obtain ⟨DK, hK⟩ := hkernel
  obtain ⟨DF, hF⟩ := hflattening
  obtain ⟨DT, hT⟩ := exists_bound_twistedFree_twistDifference l
  refine ⟨max DI (max DK (max DF DT)), ?_⟩
  intro d hd
  have hdI : DI ≤ d := by omega
  have hdK : DK ≤ d := by omega
  have hdF : DF ≤ d := by omega
  have hdT : DT ≤ d := by omega
  obtain ⟨e, he⟩ := hT d hdT
  let m := r * (n + e).choose n
  let σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n)
  obtain ⟨I⟩ := hI d hdI e he
  obtain ⟨H⟩ := hF d hdF e he
  refine ⟨e, he, m, σ, ⟨?_⟩⟩
  apply TwistedFreeQuotGrassmannianImmersionPackage.ofUniversalFlatteningLocus
    I H (fun X ↦ twistedFreeAmbientReconstructionCompatibility n X l r d e he)
  intro T a hP
  exact quotGrassmannianTwistedKernelMap_epi_of_isGloballyGenerated
    n T.left l r
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
      d e he (hK d hdK T a hP)

/-- Eventual intrinsic immersion packages make the determinant of the universal
fixed-degree pushforward relatively very ample. -/
theorem exists_eventually_isRelativelyVeryAmple_exteriorPower_of_immersionPackages
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (H : HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          (twistedFreeQuotientTwistPushforward n S l r
            (h.homEquiv (CategoryStruct.id Q)).1.out d)
          (P.hilbertNatValue d)) := by
  obtain ⟨D, hD⟩ := H
  refine ⟨D, fun d hd ↦ ?_⟩
  obtain ⟨e, he, m, σ, ⟨C⟩⟩ := hD d hd
  exact C.determinant_isRelativelyVeryAmple h

/-- Integer-indexed form of eventual determinant very ampleness from intrinsic
immersion packages. -/
theorem exists_eventually_isRelativelyVeryAmple_universalQuot_int_of_immersionPackages
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (H : HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          ((Modules.pushforward (projectiveSpaceOverπ n Q.left)).obj
            (projectiveSpaceOverTwistModule
              (quotDataOnProjectiveSpace
                (Modules.QuotientPullbackData.twistedFreeAmbient
                  (n := n) (r := r) (l := l))
                (h.homEquiv (CategoryStruct.id Q)).1.out) d)) N) := by
  obtain ⟨D, hD⟩ :=
    exists_eventually_isRelativelyVeryAmple_exteriorPower_of_immersionPackages
      n S l r P H Q h
  refine ⟨(D : ℤ), fun d hd N hN ↦ ?_⟩
  have hd0 : 0 ≤ d := le_trans (Int.natCast_nonneg D) hd
  have hdn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
  have hDdn : D ≤ d.toNat := by
    exact_mod_cast (show (D : ℤ) ≤ (d.toNat : ℤ) by simpa [hdn] using hd)
  have hv := hD d.toNat hDdn
  have hq : P.hilbertNatValue d.toNat = N := by
    apply Polynomial.hilbertNatValue_eq
    rw [show ((d.toNat : ℕ) : ℚ) = ((d.toNat : ℤ) : ℚ) by push_cast; ring, hdn]
    exact hN
  rw [hq] at hv
  simpa [twistedFreeQuotientTwistPushforward, twistedFreeQuotientSheaf, hdn] using hv

/-- Empty representatives make every line bundle relatively very ample; otherwise an
eventual intrinsic immersion package gives the result. -/
theorem
    exists_eventually_isRelativelyVeryAmple_universalQuot_int_of_nonempty_immersionPackages
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q)
    (H : Nonempty Q.left →
      HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          ((Modules.pushforward (projectiveSpaceOverπ n Q.left)).obj
            (projectiveSpaceOverTwistModule
              (quotDataOnProjectiveSpace
                (Modules.QuotientPullbackData.twistedFreeAmbient
                  (n := n) (r := r) (l := l))
                (h.homEquiv (CategoryStruct.id Q)).1.out) d)) N) := by
  by_cases hQ : Nonempty Q.left
  · exact exists_eventually_isRelativelyVeryAmple_universalQuot_int_of_immersionPackages
      n S l r P (H hQ) Q h
  · letI : IsEmpty Q.left := not_nonempty_iff.mp hQ
    exact ⟨0, fun d _ N _ ↦ isRelativelyVeryAmple_of_isEmpty Q.hom _⟩

end AlgebraicGeometry.Scheme

end

end
