module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Normal rings

Stacks Project tag **00GV**, label `algebra-definition-ring-normal`, in `algebra.tex`,
§`037B` (Normal rings).

> A ring `R` is called *normal* if for every prime `p ⊆ R` the localization `R_p` is a normal
> domain.

and tag **0309**, `algebra-definition-domain-normal`:

> A domain `R` is called *normal* if it is integrally closed in its field of fractions.

Mathlib has the domain notion as `IsIntegrallyClosed` but has **no** notion of a normal ring in
the non-domain sense — `grep` for `NormalRing` over all of Mathlib comes up empty. Note that
this is genuinely more general than "integrally closed domain": the Stacks Project remarks that
a normal ring need not be a domain (a finite product of normal domains is normal), and that
every normal ring is reduced.

`Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` has Zariski-local statements about
`IsIntegrallyClosed` which should make the basic API of this definition routine.
-/

@[expose] public section

universe u

/-- **Stacks 00GV** (`algebra-definition-ring-normal`). A commutative ring is *normal* when all
of its localizations at primes are normal domains, i.e. integrally closed domains. -/
@[stacks 00GV]
class IsNormalRing (R : Type u) [CommRing R] : Prop where
  /-- Every localization at a prime is a domain. -/
  isDomain_localization (p : Ideal R) [p.IsPrime] : IsDomain (Localization.AtPrime p)
  /-- Every localization at a prime is integrally closed in its fraction field. -/
  isIntegrallyClosed_localization (p : Ideal R) [p.IsPrime] :
    letI := isDomain_localization p
    IsIntegrallyClosed (Localization.AtPrime p)
