module

public import StacksAndModuli.API.NoetherianLocalFlatnessCriterion

/-!
# The Noetherian local criterion for flatness

Stacks Project tag **00MK**, label `algebra-lemma-local-criterion-flatness`, in
`algebra.tex`, §`00MD` (`section-criteria-flatness`, Criteria for flatness).

The Stacks Project states the hypothesis as `Tor₁ʳ(κ, M) = 0`.  The exact sequence
`0 → maximalIdeal R → R → κ → 0` identifies this with injectivity of the maximal-ideal
tensor map used below.
-/

@[expose] public section

universe u

section Tag00MK

/-- **Stacks 00MK** (`algebra-lemma-local-criterion-flatness`). Let `R → S` be a local
homomorphism of Noetherian local rings and let `M` be a finite `S`-module. If
`maximalIdeal R ⊗[R] M → M` is injective, then `M` is flat over `R`. -/
@[stacks 00MK]
theorem Module.Flat.of_maximalIdeal_rTensor_injective_of_finite_noetherian
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (hmax : Function.Injective
      ((IsLocalRing.maximalIdeal R).subtype.rTensor M)) :
    Module.Flat R M :=
  Module.Flat.of_maximalIdeal_rTensor_injective_of_finite S hmax

end Tag00MK
