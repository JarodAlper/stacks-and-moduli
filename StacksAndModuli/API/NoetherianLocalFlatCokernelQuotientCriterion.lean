module

public import StacksAndModuli.API.IdealQuotientExact
public import StacksAndModuli.API.NoetherianLocalFlatCokernelFiberCriterion

/-!
# Relative flat cokernels from exact coefficient quotients

This file restates the local Noetherian flatness criterion in the quotient-module
language used by finite complexes on coefficient closed fibres.  For an exact
presentation `K → F → M → 0`, injectivity of the induced map
`K / 𝔪K → F / 𝔪F` implies that `M` is flat over the coefficient local ring.

Main declaration:

* `Module.Flat.of_exact_of_surjective_of_quotientByMappedIdeal_injective`.
-/

@[expose] public section

universe u

namespace Module.Flat

set_option linter.style.haveILetI false

/-- In an exact presentation over a local Noetherian algebra, injectivity after
quotienting by the extended coefficient maximal ideal implies coefficient flatness
of the presented module. -/
theorem of_exact_of_surjective_of_quotientByMappedIdeal_injective
    {R S K F M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R F]
    (i : K →ₗ[S] F) (p : F →ₗ[S] M)
    (hexact : Function.Exact i p) (hp : Function.Surjective p)
    (hfibre : Function.Injective
      (LinearMap.quotientByIdeal
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) i)) :
    Module.Flat R M := by
  have hquot : Function.Injective
      (LinearMap.quotientByIdeal (IsLocalRing.maximalIdeal R)
        (i.restrictScalars R)) :=
    LinearMap.quotientByIdeal_restrictScalars_injective_of_mappedIdeal_injective
      (IsLocalRing.maximalIdeal R) i hfibre
  have htensor : Function.Injective
      ((i.restrictScalars R).lTensor
        (R ⧸ IsLocalRing.maximalIdeal R)) :=
    (LinearMap.lTensor_injective_iff_quotientByIdeal_injective
      (IsLocalRing.maximalIdeal R) (i.restrictScalars R)).mpr hquot
  apply Module.Flat.of_exact_of_surjective_of_lTensor_residueField_injective
    i p hexact hp
  change Function.Injective
    ((i.restrictScalars R).lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))
  exact htensor

end Module.Flat

end
