module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianProjectivity
public import StacksAndModuli.API.QuotientKernelFiniteModelZeroLocus
public import StacksAndModuli.API.QuotientKernelProjectiveTwistedModels
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianImmersion

/-!
# Projectivity of general Quot from a twisted-free Grassmannian presentation

This file combines two sorry-free categorical reductions for fixed-polynomial Quot.
First, a twisted-free Quot-to-Grassmannian immersion, together with the required DVR
input, constructs a projective representative of the twisted-free Quot functor.  Second,
universal closed zero loci for the kernel of an epimorphic presentation cut out the Quot
functor of the target sheaf as a projective closed subfunctor.

The resulting theorems apply to a finitely presented quasicoherent ambient sheaf `F`
equipped with an epimorphism `O(-l)^⊕r ⟶ F`.  In arbitrary relative projective
dimension, their only further input is uniform scheme-level Serre vanishing over DVRs.
In relative dimension zero, the Grassmannian immersion and the kernel zero loci alone
suffice.  Compatible affine finite-free kernel models are also accepted directly through
their canonical universal-zero-locus construction.

None of these endpoints uses the existing sorry-backed projectivity or quasi-projectivity
theorems from §2.4.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Compatible affine finite-free vanishing models for the single universal
twisted-free quotient on a chosen representing scheme.

This is the universal-family form of the remaining Exercise 1.3.23 input: it
does not ask for zero-locus data independently on every test scheme and every
Quot point. -/
abbrev UniversalQuotientKernelFiniteFreeModels
    {n : ℕ} {S : Scheme.{u}}
    {F G : (projectiveSpaceOver n S).Modules}
    (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
    (Q₀ : Over S) (eG : (quotFunctorP G P).RepresentableBy Q₀) :=
  CompatibleAffineFiniteFreeKernelModels p P
    (T := Q₀) (z := eG.homEquiv (𝟙 Q₀))

/-- Universal-family finite-free models produce the single kernel zero locus
needed to cut the target Quot functor out of its represented twisted-free
ambient Quot functor. -/
noncomputable def UniversalQuotientKernelFiniteFreeModels.toZeroLocusData
    {n : ℕ} {S : Scheme.{u}}
    {F G : (projectiveSpaceOver n S).Modules}
    {p : G ⟶ F} [Epi p] {P : Polynomial ℚ}
    {Q₀ : Over S} {eG : (quotFunctorP G P).RepresentableBy Q₀}
    (D : UniversalQuotientKernelFiniteFreeModels p P Q₀ eG) :
    QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀)) :=
  CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData p P D

/-- A finite-free vanishing model for the universal quotient alone suffices to
descend projective representability along an epimorphism of ambient sheaves. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_finiteFreeModels
    {n : ℕ} {S : Scheme.{u}}
    {F G : (projectiveSpaceOver n S).Modules}
    (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
    (Q₀ : Over S) (eG : (quotFunctorP G P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom)
    (D : UniversalQuotientKernelFiniteFreeModels p P Q₀ eG) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
    p P Q₀ eG hQ₀ D.toZeroLocusData

/-- A twisted-free presentation with universal closed kernel zero loci descends the
Grassmannian/DVR projectivity endpoint to a finitely presented quasicoherent ambient
sheaf. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_zeroLoci_grassmannian_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).obj (op T)),
      Nonempty (QuotientKernelZeroLocusData p P T z))
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_precomp_zeroLoci
    p P H
    (exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion_of_serre
      n S l r P himm hserre)

/-- On relative `P⁰`, a twisted-free presentation with universal closed kernel zero
loci and a Quot-to-Grassmannian immersion gives projective representability of the
general ambient fixed-polynomial Quot functor. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_zero_of_zeroLoci_grassmannian
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver 0 S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree 0 S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)),
      Nonempty (QuotientKernelZeroLocusData p P T z))
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion 0 S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_precomp_zeroLoci
    p P H
    (exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion
      S l r P himm)

/-- Compatible affine finite-free models for the presentation kernel construct the
universal zero loci needed to descend the general Grassmannian/Serre projectivity
endpoint. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_finiteFreeModels_grassmannian_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).obj (op T)),
      Nonempty (CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)))
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_zeroLoci_grassmannian_serre
    n S F l r p P
      (fun T z ↦
        ⟨CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData
          p P (Classical.choice (H T z))⟩)
      himm hserre

/-- In relative dimension zero, compatible affine finite-free kernel models and the
twisted-free Quot-to-Grassmannian immersion alone give a projective representative for
the general ambient Quot functor. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_zero_of_finiteFreeModels_grassmannian
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver 0 S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree 0 S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)),
      Nonempty (CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)))
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion 0 S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_zero_of_zeroLoci_grassmannian
    S F l r p P
      (fun T z ↦
        ⟨CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData
          p P (Classical.choice (H T z))⟩)
      himm

/-- In positive relative dimension, a twisted-free presentation and the canonical
Quot-to-Grassmannian immersion produce a projective representative for the general
ambient fixed-polynomial Quot functor.  The canonical base-change models and universal
kernel zero locus are constructed internally. -/
theorem
    exists_generalQuotFunctorP_representableBy_isHProjective_of_grassmannianImmersion
    (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver n S).Modules) [F.IsQuasicoherent]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q₀, ⟨eG⟩, hQ₀⟩ :=
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion
      n S l r P himm
  have hp : Epi p := inferInstance
  change Modules.QuotientPullbackData.twistedFreeAmbient
    (S := S) (n := n) (r := r) (l := l) ⟶ F at p
  letI : Epi p := hp
  change (quotFunctorP
    (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l)) P).RepresentableBy Q₀ at eG
  letI : LocallyOfFiniteType Q₀.hom :=
    hQ₀.isHQuasiProjective.locallyOfFiniteType
  letI : IsLocallyNoetherian Q₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q₀.hom
  exact exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree
    n r hn l p P Q₀ eG hQ₀

/-- In positive relative dimension, the printed twisted-free presentation hypothesis
reduces projective representability of a general fixed-polynomial Quot functor solely to
the canonical Quot-to-Grassmannian immersion for finite twisted-free sources. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_twistedFreeGrassmannianImmersions
    (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF : F.IsQuotientOfTwistedFree) (P : Polynomial ℚ)
    (himm : ∀ (l : ℤ) (r : ℕ),
      TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨l, r, p, hp⟩ := hF
  letI : Epi p := hp
  exact
    exists_generalQuotFunctorP_representableBy_isHProjective_of_grassmannianImmersion
      n hn S F l r p P (himm l r)

/-- On relative projective zero-space, the printed twisted-free presentation
hypothesis alone gives projective representability of the general fixed-polynomial
Quot functor.  Both the twisted-free Grassmannian immersion and the canonical kernel
zero locus are unconditional in this dimension. -/
theorem
    exists_quotFunctorP_zero_representableBy_isHProjective_of_twistedFreePresentation
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver 0 S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF : F.IsQuotientOfTwistedFree) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨l, r, p, hp⟩ := hF
  letI : Epi p := hp
  obtain ⟨Q₀, ⟨eG⟩, hQ₀⟩ :=
    exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion
      S l r P (twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)
  have hp' : Epi p := inferInstance
  change Modules.QuotientPullbackData.twistedFreeAmbient
    (S := S) (n := 0) (r := r) (l := l) ⟶ F at p
  letI : Epi p := hp'
  change (quotFunctorP
    (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := 0) (r := r) (l := l)) P).RepresentableBy Q₀ at eG
  letI : LocallyOfFiniteType Q₀.hom :=
    hQ₀.isHQuasiProjective.locallyOfFiniteType
  letI : IsLocallyNoetherian Q₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q₀.hom
  exact
    exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree_zero
      r l p P Q₀ eG hQ₀

/-- In every relative projective dimension, the printed twisted-free presentation
hypothesis reduces projective representability of the general fixed-polynomial Quot
functor to the canonical twisted-free Quot-to-Grassmannian immersions.  Dimension zero
is discharged by the unconditional projective-zero construction. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_twistedFreeGrassmannianImmersions_all_dimensions
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF : F.IsQuotientOfTwistedFree) (P : Polynomial ℚ)
    (himm : ∀ (l : ℤ) (r : ℕ),
      TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  cases n with
  | zero =>
      exact
        exists_quotFunctorP_zero_representableBy_isHProjective_of_twistedFreePresentation
          S F hF P
  | succ n =>
      exact
        exists_quotFunctorP_representableBy_isHProjective_of_twistedFreeGrassmannianImmersions
          (n + 1) (Nat.zero_lt_succ n) S F hF P himm

end AlgebraicGeometry.Scheme

end
