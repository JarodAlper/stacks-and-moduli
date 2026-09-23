module

public import StacksAndModuli.API.FlatLocal
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Relative flatness from source-localizations at maximal ideals

Let `R → S` and let `M` be an `S`-module.  Flatness of `M` over the external coefficient
ring `R` can be checked after localizing `M` at every maximal ideal of `S`.  This is the
pointwise source-local counterpart of the basic-open gluing lemmas in `FlatLocal`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

open TensorProduct

namespace Module.Flat

/-- An `S`-module is flat over an external coefficient ring `R` if its localization at
every maximal ideal of `S` is flat over `R`. -/
theorem of_forall_maximal_localization_over_source
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hflat : ∀ (J : Ideal S) [J.IsMaximal],
      Module.Flat R (LocalizedModule J.primeCompl M)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  change Function.Injective
    (TensorProduct.AlgebraTensorModule.lTensor S M f)
  apply injective_of_localized_maximal
  intro J _
  letI : Module S (LocalizedModule J.primeCompl M) :=
    OreLocalization.instModuleOfIsScalarTower
  let g : M →ₗ[S] LocalizedModule J.primeCompl M :=
    LocalizedModule.mkLinearMap J.primeCompl M
  let gP := TensorProduct.AlgebraTensorModule.rTensor R P g
  let gQ := TensorProduct.AlgebraTensorModule.rTensor R Q g
  apply (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
    gP gQ).mp
  rw [IsLocalizedModule.map_lTensor]
  let _ : Module.Flat R (LocalizedModule J.primeCompl M) := hflat J
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (M := LocalizedModule J.primeCompl M) f hf

end Module.Flat

end

end
