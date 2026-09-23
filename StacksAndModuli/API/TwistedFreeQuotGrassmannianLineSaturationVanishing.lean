module

public import StacksAndModuli.API.ProjectiveLineFiniteLocallyFreeTwistOneCohomology
public import StacksAndModuli.API.ProjectiveLineQuasicoherentHigherCohomology
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSaturationVanishing

/-!
# The higher-cohomology input to projective-line saturation

For reconstructed quotients on the projective line over a noetherian affine base,
the relation-kernel sheaf is quasicoherent.  Its second cohomology therefore vanishes
automatically by the two-chart Mayer--Vietoris calculation.  Consequently the
next-degree pushforward and full saturation criteria need no separate `H²` hypothesis.
When the coefficient quotient is finite locally free, its relation kernel is finite
locally free too, so the pullback-coefficient `H¹` input is also automatic.  In that
case only the first cohomology of the reconstructed relation kernel and the
source-comparison coherence remain.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The twisted kernel of the reconstructed relation-to-image map on a projective
line has vanishing second cohomology over a noetherian affine base. -/
theorem subsingleton_H_two_reconstructedNextDegreeRelationKernel_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 2) := by
  let T := Spec (.of R)
  let f := reconstructedRelation' 1 T l r d e he u
  let O := projectiveSpaceOverTwist 1 T ((d + 1 : ℕ) : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  haveI hkeruqc : (kernel u).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent u
  haveI hpullKqc : ((Modules.pullback
      (projectiveSpaceOverπ 1 T)).obj (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ 1 T) _
  haveI hAqc : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
      (projectiveSpaceOverTwist 1 T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  haveI hFqc : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ 1 T _
  haveI hIQC : (Abelian.image f).IsQuasicoherent := by
    dsimp only [Abelian.image]
    letI : (cokernel f).IsQuasicoherent :=
      Modules.isQuasicoherent_cokernel f
    exact Modules.kernel_isQuasicoherent (cokernel.π f)
  haveI hAOqc : (Modules.tensor
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
        (projectiveSpaceOverTwist 1 T (-(d : ℤ)))) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
        (projectiveSpaceOverTwist 1 T (-(d : ℤ))))
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI hIOqc : (Modules.tensor (Abelian.image f) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule (Abelian.image f)
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI hgqc : (kernel g).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent g
  exact ProjectiveSpace.subsingleton_H_projectiveSpaceOver_one_of_two_le
    R (kernel g) 2 le_rfl

/-- For a finite locally free quotient of the monomial free coefficient sheaf,
the relation coefficient is finite locally free.  Consequently its pullback to
the projective line, tensored with `O(1)`, has vanishing first cohomology. -/
theorem subsingleton_H_one_reconstructedRelationCoefficient_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (r e : ℕ) {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback
            (projectiveSpaceOverπ 1 (Spec (.of R)))).obj (kernel u)) 1)).H 1) := by
  let m := r * (1 + e).choose 1
  let σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((1 + e).choose 1) :=
    twistedFreeMonomialIndexEquiv r ((1 + e).choose 1)
  let f := SheafOfModules.freeMap
    (R := (Spec (.of R)).ringCatSheaf) σ.symm
  letI : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  have hSource : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))) :=
    (Modules.free_isFiniteLocallyFree (Spec (.of R)) m).of_iso
      (asIso f).symm
  have hKernel : Modules.IsFiniteLocallyFree (kernel u) :=
    Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
      hSource hE u
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  exact
    subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
      R hKernel

/-- On the projective line over a noetherian affine base, first-cohomology
vanishing for the pullback relation coefficient already implies epimorphy of the
reconstructed next-degree pushforward map; the usual `H²` input is automatic. -/
theorem reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback
            (projectiveSpaceOverπ 1 (Spec (.of R)))).obj (kernel u)) 1)).H 1)) :
    Epi (quotGrassmannianFreeMap 1 (Spec (.of R)) l r
      (reconstructedQuotientMap' 1 (Spec (.of R)) l r d e he u)
      (d + 1) (e + 1) (by omega)) := by
  exact reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing
    1 (Spec (.of R)) l r d e he u hpullback1
      (subsingleton_H_two_reconstructedNextDegreeRelationKernel_line
        R l r d e he u)

/-- For a finite locally free coefficient quotient on a noetherian affine base,
the reconstructed next-degree pushforward map on the projective line is an epimorphism;
the pullback-coefficient `H¹` and relation-kernel `H²` inputs are automatic. -/
theorem reconstructedNextDegreePushforwardMap_epi_of_finiteLocallyFree_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    Epi (quotGrassmannianFreeMap 1 (Spec (.of R)) l r
      (reconstructedQuotientMap' 1 (Spec (.of R)) l r d e he u)
      (d + 1) (e + 1) (by omega)) := by
  exact reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing_line
    R l r d e he u
      (subsingleton_H_one_reconstructedRelationCoefficient_line R r e u hE)

/-- On the projective line over a noetherian affine base, full reconstructed
next-degree saturation follows from the two first-cohomology vanishings and the
canonical relation-source comparison. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_line_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback
            (projectiveSpaceOverπ 1 (Spec (.of R)))).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1))
    (hcomparison : TwistedFreeNextDegreeRelationSourcePushforwardComparison
      1 (Spec (.of R)) l r d e he u) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  exact twistedFreeNextDegreeReconstructionSaturation_of_pullback_one_vanishing
    1 (Spec (.of R)) l r d e he u hpullback1 hrelationKernel1
      (subsingleton_H_two_reconstructedNextDegreeRelationKernel_line
        R l r d e he u) hcomparison

/-- For a finite locally free coefficient quotient on the projective line over a
noetherian affine base, full reconstructed next-degree saturation requires only
vanishing of `H¹` of the reconstructed relation kernel and the canonical
relation-source comparison. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_line_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E)
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1))
    (hcomparison : TwistedFreeNextDegreeRelationSourcePushforwardComparison
      1 (Spec (.of R)) l r d e he u) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  exact twistedFreeNextDegreeReconstructionSaturation_of_line_vanishing
    R l r d e he u
      (subsingleton_H_one_reconstructedRelationCoefficient_line R r e u hE)
      hrelationKernel1 hcomparison

end AlgebraicGeometry.Scheme

end

end
