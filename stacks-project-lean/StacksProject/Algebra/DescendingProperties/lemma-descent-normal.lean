module

public import StacksProject.Algebra.NormalRings.«definition-ring-normal»
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Descending normality along a faithfully flat ring map

Stacks Project tag **033G**, label `algebra-lemma-descent-normal`, in `algebra.tex`,
§`033D` (Descending properties).

> Let `R → S` be a ring map. Assume that (1) `R → S` is faithfully flat, and (2) `S` is a
> normal ring. Then `R` is a normal ring.

Normality here is `IsNormalRing` (Stacks 00GV), defined in
`StacksProject.Algebra.NormalRings.definition-ring-normal`, since Mathlib has no notion of a
normal ring outside the domain case.

**Proof route (Stacks Project, ~15 lines of prose).** Normality is a condition on localizations
at primes, so the statement reduces to the local case: given a prime `p ⊆ R`, choose a prime
`q ⊆ S` lying over it — possible because `Spec S → Spec R` is surjective for a faithfully flat
map — and observe that `R_p → S_q` is again faithfully flat (a flat local homomorphism of local
rings is faithfully flat, `Module.FaithfullyFlat.of_flat_of_isLocalHom`, which Mathlib has). So
assume `R`, `S` local with `R → S` faithfully flat and `S` a normal domain. Then `R` is a domain
by injectivity, and reduced by Stacks 033F. For integral closedness, take `x` in the fraction
field of `R` integral over `R`; write `x = a / b`. The point is that `R/bR → S/bS` is again
faithfully flat, which lets one transfer the divisibility `a ∈ bR` from `a ∈ bS`.

Mathlib's `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` supplies the Zariski-local
API for `IsIntegrallyClosed` needed to assemble the reduction step.
-/

@[expose] public section

universe u v

open scoped nonZeroDivisors

/-- Being an integrally closed domain descends along a faithfully flat algebra: an integral
element `x = a/b` of the fraction field of `A` lands in the integrally closed `B`, so
`a ∈ bB ∩ A = bA` by faithful flatness. -/
theorem IsIntegrallyClosed.of_faithfullyFlat {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A _
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr ?_
  rintro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective A⁰ x
  -- the image of `x` in the fraction field of `B` is integral over `B`
  have hxL : IsIntegral B (algebraMap (FractionRing A) (FractionRing B)
      (IsLocalization.mk' (FractionRing A) a b)) :=
    IsIntegral.tower_top (R := A)
      (hx.map (IsScalarTower.toAlgHom A (FractionRing A) (FractionRing B)))
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxL
  -- clear denominators: `s * b = a` in `B`
  have hspec : IsLocalization.mk' (FractionRing A) a b * algebraMap A (FractionRing A) b =
      algebraMap A (FractionRing A) a := IsLocalization.mk'_spec _ a b
  have hL := congrArg (algebraMap (FractionRing A) (FractionRing B)) hspec
  rw [map_mul, ← hs, ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B),
    ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B),
    IsScalarTower.algebraMap_apply A B (FractionRing B),
    IsScalarTower.algebraMap_apply A B (FractionRing B) a,
    ← map_mul] at hL
  have hsb : s * algebraMap A B b = algebraMap A B a :=
    IsFractionRing.injective B (FractionRing B) hL
  -- contract along the faithfully flat map
  have hmem : (a : A) ∈ Ideal.span {(b : A)} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {(b : A)})]
    refine Ideal.mem_comap.mpr ?_
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, by rw [← hsb, mul_comm]⟩
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨a', ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
  exact congrArg (algebraMap A (FractionRing A)) (by rw [ha']; ring)

/-- **Stacks 033G** (`algebra-lemma-descent-normal`). If `R → S` is faithfully flat and `S` is a
normal ring, then `R` is a normal ring. -/
@[stacks 033G]
theorem isNormalRing_of_faithfullyFlat (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsNormalRing S] : IsNormalRing R := by
  -- for each prime `p ⊆ R` choose a prime of `S` lying over it and localize
  have hlocal : ∀ (p : Ideal R) (_ : p.IsPrime),
      ∃ (q : Ideal S) (_ : q.IsPrime) (hpq : p = q.comap (algebraMap R S)), True := by
    intro p hp
    obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := R) (B := S) ⟨p, hp⟩
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal hq.symm, trivial⟩
  have main : ∀ (p : Ideal R) (_ : p.IsPrime),
      IsDomain (Localization.AtPrime p) ∧
      (∀ (_ : IsDomain (Localization.AtPrime p)),
        IsIntegrallyClosed (Localization.AtPrime p)) := by
    intro p hp
    obtain ⟨q, hq, hpq, -⟩ := hlocal p hp
    have hflat : (Localization.localRingHom p q (algebraMap R S) hpq).Flat :=
      RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) q p hpq
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      (Localization.localRingHom p q (algebraMap R S) hpq).toAlgebra
    haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hflat
    haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
      Localization.isLocalHom_localRingHom (I := p) q (algebraMap R S) hpq
    haveI : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    haveI hdomq : IsDomain (Localization.AtPrime q) :=
      IsNormalRing.isDomain_localization q
    haveI hicq : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsNormalRing.isIntegrallyClosed_localization q
    haveI hdomp : IsDomain (Localization.AtPrime p) :=
      IsDomain.of_faithfulSMul (Localization.AtPrime p) (Localization.AtPrime q)
    exact ⟨hdomp, fun _ ↦ IsIntegrallyClosed.of_faithfullyFlat
      (B := Localization.AtPrime q)⟩
  refine ⟨fun p hp ↦ (main p hp).1, fun p hp ↦ ?_⟩
  exact (main p hp).2 (main p hp).1
