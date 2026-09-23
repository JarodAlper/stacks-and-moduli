module

public import StacksProject.Topologies.Fpqc.«lemma-fpqc-affine»
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Descent of morphism properties from fpqc covering sieves

Mathlib's `MorphismProperty.DescendsAlong` packages descent along one
quasi-compact faithfully flat morphism.  This file upgrades that result to an
arbitrary fpqc covering sieve.  Over an affine target, Stacks Project Tag 022E
gives a finite affine refinement; its disjoint union is one affine fpqc cover.
The general case follows by restricting to an affine open cover of the target.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (P : MorphismProperty Scheme.{u})

/-- Flatness descends along a quasi-compact faithfully flat morphism.  This is
the ring-theoretic input needed to apply the family descent theorem below to
`Flat` itself. -/
lemma flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  apply HasRingHomProperty.descendsAlong_flat (Q := RingHom.Flat)
  apply RingHom.CodescendsAlong.mk (P := RingHom.Flat)
    (Q := RingHom.FaithfullyFlat) RingHom.Flat.respectsIso
  intro R S T _ _ _ _ _ hff hflat
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI := hff
  rw [RingHom.flat_algebraMap_iff] at hflat ⊢
  exact (Module.Flat.iff_flat_tensorProduct R T S).mp hflat

/-- A target-local morphism property satisfying singleton fpqc descent descends
from an fpqc covering sieve when the target is affine. -/
lemma MorphismProperty.of_fpqc_sieve_of_isAffine
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (R : Sieve Y) (hR : R ∈ Scheme.fpqcTopology Y)
    (hP : ∀ {U : Scheme.{u}} (g : U ⟶ Y), R.arrows g →
      P (pullback.snd f g)) : P f := by
  obtain ⟨Q, hQ, hQR⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨n, U, p, hU, hp, hpQ, hcover⟩ :=
    Scheme.exists_finite_affine_refinement_of_mem_fpqcPrecoverage hQ
  let _ (i : Fin n) : IsAffine (U i) := hU i
  have hcoverFlat : Presieve.ofArrows U p ∈ Scheme.precoverage (@Flat) Y :=
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat)) Y hcover
  let C : Scheme.Cover.{0, u} (Scheme.precoverage (@Flat)) Y :=
    { I₀ := Fin n
      X := U
      f := p
      mem₀ := hcoverFlat }
  let V : Scheme.{u} := ∐ U
  let q : V ⟶ Y := Sigma.desc p
  let _ : IsAffine V := by
    dsimp [V]
    infer_instance
  have hqflat : Flat q := IsZariskiLocalAtSource.sigmaDesc hp
  have hqsurj : Surjective q :=
    Surjective.sigmaDesc_of_union_range_eq_univ (by
      simpa [C, q] using C.iUnion_range)
  have hqqc : QuasiCompact q := by infer_instance
  have hqP : P (pullback.snd f q) := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover
      (P := P) (sigmaOpenCover U)]
    intro i
    change Fin n at i
    unfold Scheme.Cover.pullbackHom
    rw [← pullbackLeftPullbackSndIso_hom_snd,
      P.cancel_left_of_respectsIso]
    have hpR : R.arrows (p i) :=
      ((Sieve.generate_le_iff Q R).mpr hQR) _ (hpQ i)
    apply hP ((sigmaOpenCover U).f i ≫ q)
    have hi : (sigmaOpenCover U).f i ≫ q = p i := by
      rw [sigmaOpenCover_f, show q = Sigma.desc p from rfl, Sigma.ι_desc]
    exact hi.symm ▸ hpR
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := P) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hqsurj, hqflat⟩, hqqc⟩ hqP

/-- A target-local morphism property satisfying singleton fpqc descent descends
from an arbitrary fpqc covering sieve. -/
lemma MorphismProperty.of_fpqc_sieve
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sieve Y) (hR : R ∈ Scheme.fpqcTopology Y)
    (hP : ∀ {U : Scheme.{u}} (g : U ⟶ Y), R.arrows g →
      P (pullback.snd f g)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) Y.affineCover]
  intro i
  let j := Y.affineCover.f i
  apply MorphismProperty.of_fpqc_sieve_of_isAffine (P := P)
    (pullback.snd f j)
    (R.pullback j) (Scheme.fpqcTopology.pullback_stable j hR)
  intro U g hg
  rw [← pullbackLeftPullbackSndIso_hom_snd,
    P.cancel_left_of_respectsIso]
  exact hP (g ≫ j) hg

/-- The family form of `MorphismProperty.of_fpqc_sieve`. -/
lemma MorphismProperty.of_fpqc_family
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {I : Type u} {U : I → Scheme.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : ∀ i, U i ⟶ Y)
    (hp : Presieve.ofArrows U p ∈ Scheme.fpqcPrecoverage Y)
    (hP : ∀ i, P (pullback.snd f (p i))) : P f := by
  let R : Sieve Y := Sieve.generate (Presieve.ofArrows U p)
  apply MorphismProperty.of_fpqc_sieve (P := P) f R
    (Precoverage.generate_mem_toGrothendieck hp)
  intro V g hg
  obtain ⟨W, h, k, ⟨i⟩, rfl⟩ := hg
  rw [← P.cancel_left_of_respectsIso
    (pullbackLeftPullbackSndIso f (p i) h).hom,
    pullbackLeftPullbackSndIso_hom_snd]
  exact P.pullback_snd _ _ (hP i)

end AlgebraicGeometry
