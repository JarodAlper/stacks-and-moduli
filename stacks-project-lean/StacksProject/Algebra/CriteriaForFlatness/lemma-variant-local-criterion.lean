module

public import StacksAndModuli.API.KernelFlatnessCriterion
public import StacksAndModuli.API.NoetherianLocalFlatnessCriterion

/-!
# A variant of the Noetherian local criterion for flatness

Stacks Project tag **00ML**, label `algebra-lemma-criterion-flatness`, in `algebra.tex`,
§`00MD` (`section-criteria-flatness`, Criteria for flatness).

The Stacks Project expresses one hypothesis using `Tor₁`.  The exact sequence
`0 → I → R → R/I → 0` identifies it with injectivity of `I ⊗[R] M → M`, which is the
form used below.
-/

@[expose] public section

universe u

section Tag00ML

/-- **Stacks 00ML** (`algebra-lemma-criterion-flatness`). Let `R → S` be a local
homomorphism of Noetherian local rings, let `I` be a proper ideal of `R`, and let `M` be a
finite `S`-module. If `I ⊗[R] M → M` is injective and `M / IM` is flat over `R / I`,
then `M` is flat over `R`. -/
@[stacks 00ML]
theorem Module.Flat.of_ideal_rTensor_injective_of_quotient_flat_noetherian
    (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (I : Ideal R) (hIproper : I ≠ ⊤)
    (hI : Function.Injective (I.subtype.rTensor M))
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Flat R M := by
  apply Module.Flat.of_maximalIdeal_rTensor_injective_of_finite S
  exact LinearMap.maximalIdeal_rTensor_injective_of_ideal_of_flat_quotient
    I hIproper hI

end Tag00ML
