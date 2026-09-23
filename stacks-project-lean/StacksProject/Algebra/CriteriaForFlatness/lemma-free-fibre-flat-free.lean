module

public import StacksAndModuli.API.NoetherianLocalFlatCokernelFiberCriterion

/-!
# Lifting a free closed fibre

Stacks Project tag **00MH**, label `algebra-lemma-free-fibre-flat-free`, in
`algebra.tex`, §`00MD` (`section-criteria-flatness`, Criteria for flatness).

The quotient by the extension of the maximal ideal is the Lean rendering of
`M / 𝔪M` over `S / 𝔪S`.
-/

@[expose] public section

universe u

section Tag00MH

/-- **Stacks 00MH** (`algebra-lemma-free-fibre-flat-free`). Let `R → S` be a local
homomorphism of Noetherian local rings and let `M` be a nonzero finite `S`-module. If
`M / 𝔪M` is free over `S / 𝔪S` and `M` is flat over `R`, then `M` is free over
`S` and `S` is flat over `R`. -/
@[stacks 00MH]
theorem Module.free_and_source_flat_of_free_closedFiber_noetherian
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M]
    [Module.Free
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) •
        (⊤ : Submodule S M))]
    [Nontrivial M] :
    Module.Free S M ∧ Module.Flat R S :=
  Module.Flat.free_and_source_flat_of_free_closedFiber

end Tag00MH
