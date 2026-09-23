module

public import StacksAndModuli.API.NoetherianLocalFlatnessCriterion

/-!
# Tor vanishing for finite-length modules

Stacks Project tag **00MJ**, label `algebra-lemma-prepare-local-criterion-flatness`, in
`algebra.tex`, §`00MD` (`section-criteria-flatness`, Criteria for flatness).

The Stacks Project states this result using `Tor₁`.  Since the current library does not
provide that interface, the theorem below uses its standard flat-presentation formulation:
for a map into a flat module, injectivity after tensoring with the residue field propagates
to every finite-length module.
-/

@[expose] public section

universe u

section Tag00MJ

/-- **Stacks 00MJ** (`algebra-lemma-prepare-local-criterion-flatness`). Over a local ring,
if a map into a flat module remains injective after tensoring with the residue field, then
it remains injective after tensoring with every finite-length module. -/
@[stacks 00MJ]
theorem LinearMap.rTensor_injective_of_isFiniteLength_of_residueField
    {R K F N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [AddCommGroup N] [Module R N] (f : K →ₗ[R] F) [Module.Flat R F]
    (hk : Function.Injective (f.rTensor (IsLocalRing.ResidueField R)))
    (hN : IsFiniteLength R N) : Function.Injective (f.rTensor N) :=
  LinearMap.rTensor_injective_of_isFiniteLength f hk hN

end Tag00MJ
