module

public import StacksProject.Algebra.AscendingProperties.Normality
public import StacksProject.Algebra.SmoothOverField.«lemma-characterize-smooth-over-field»

/-!
# Regularity ascends along smooth ring maps

This file formalizes Stacks Project tag **07NF**
(`algebra-lemma-smooth-regular`) from §`0336` (Ascending properties) of
`algebra.tex`.

The proof is local at a prime of the target.  The resulting local map is flat;
its closed fiber is a localization of a smooth algebra over the residue field,
hence regular.  Stacks **031E** then ascends regularity from the base localization
and the closed fiber.
-/

@[expose] public section

universe u

open IsLocalRing

/-- A localization at a prime of a smooth algebra is regular when the corresponding
localization of the base is regular. -/
theorem isRegularLocalRing_localization_of_smooth
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S))
    [IsRegularLocalRing (Localization.AtPrime p)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  letI : q.LiesOver p := ⟨hpq⟩
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.Flat.atPrime p q hpq
  letI : Algebra.EssFiniteType R S := inferInstance
  letI : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  letI : IsNoetherianRing (Localization.AtPrime q) :=
    Algebra.EssFiniteType.isNoetherianRing (Localization.AtPrime p) (Localization.AtPrime q)
  let F := p.Fiber S
  letI : Algebra.Smooth p.ResidueField F := inferInstance
  obtain ⟨qf, hqf, ⟨e⟩⟩ :=
    Ideal.Fiber.exists_localizationRingEquivQuotient p q hpq
  letI : qf.IsPrime := hqf
  letI : IsRegularLocalRing (Localization.AtPrime qf) :=
    isRegularLocalRing_of_smooth_of_isLocalization_atPrime
      p.ResidueField F qf (Localization.AtPrime qf)
  have hclosed : IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime qf) e
  have hI : Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (maximalIdeal (Localization.AtPrime p)) =
      p.map (algebraMap R (Localization.AtPrime q)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
      Ideal.map_map, IsScalarTower.algebraMap_eq R (Localization.AtPrime p)
        (Localization.AtPrime q)]
  letI : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
          (maximalIdeal (Localization.AtPrime p))) := by
    rw [hI]
    exact hclosed
  exact IsRegularLocalRing.of_flat_of_isRegularLocalRing_quotient
    (R := Localization.AtPrime p) (S := Localization.AtPrime q)

/-- **Stacks 07NF** (`algebra-lemma-smooth-regular`): regularity ascends along
smooth maps of rings. -/
@[stacks 07NF]
theorem isRegularRing_of_smooth (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] [IsRegularRing R] : IsRegularRing S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  rw [isRegularRing_iff]
  intro q hq
  letI : q.IsPrime := hq
  exact isRegularLocalRing_localization_of_smooth R S
    (q.comap (algebraMap R S)) q rfl
