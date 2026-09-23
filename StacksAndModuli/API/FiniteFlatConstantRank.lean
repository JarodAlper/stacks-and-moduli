module

public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite flat modules of constant rank

Supporting API with no Stacks Project counterpart.

A finite flat module need not be finitely presented over an arbitrary ring.  Constant
stalkwise rank supplies the missing uniformity: Mathlib's local-freeness theorem gives a
free localization away from an element through every prime.  Those elements generate the
unit ideal, so locality of finite presentation makes the module finitely presented and
hence finite projective.

Main declarations:

* `Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_eq`;
* `Module.Projective.of_finite_of_flat_of_rankAtStalk_eq`.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

namespace Module

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M]

/-- A finite flat module whose rank at every stalk is the same natural number is finitely
presented.  The rank hypothesis turns pointwise freeness into freeness on basic
neighbourhoods; finite presentation is then patched over the resulting basic cover. -/
theorem FinitePresentation.of_finite_of_flat_of_rankAtStalk_eq (q : ℕ)
    (hrank : ∀ p : PrimeSpectrum R, rankAtStalk M p = q) :
    Module.FinitePresentation R M := by
  let s : Set R := {a | Module.Free (Localization.Away a) (LocalizedModule.Away a M)}
  have hs : Ideal.span s = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rw [PrimeSpectrum.mem_zeroLocus] at hp
    obtain ⟨a, ha, hfree⟩ :=
      Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p.asIdeal (by
        intro m hm
        rw [hrank ⟨m, hm.isPrime⟩, hrank p])
    exact ha (hp hfree)
  apply Module.FinitePresentation.of_localizationSpan s hs
  intro a
  letI : Module.Free (Localization.Away a.1) (LocalizedModule.Away a.1 M) := a.2
  letI : Module.Finite (Localization.Away a.1) (LocalizedModule.Away a.1 M) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers a.1)
      (LocalizedModule.mkLinearMap (Submonoid.powers a.1) M)
  exact Module.finitePresentation_of_projective _ _

/-- A finite flat module of constant stalkwise rank is projective. -/
theorem Projective.of_finite_of_flat_of_rankAtStalk_eq (q : ℕ)
    (hrank : ∀ p : PrimeSpectrum R, rankAtStalk M p = q) : Module.Projective R M := by
  letI : Module.FinitePresentation R M :=
    FinitePresentation.of_finite_of_flat_of_rankAtStalk_eq q hrank
  exact Module.Flat.projective_of_finitePresentation

end Module

end
