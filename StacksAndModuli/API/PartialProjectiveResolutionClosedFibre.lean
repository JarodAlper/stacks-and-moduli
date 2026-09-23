module

public import StacksAndModuli.API.IdealQuotientExact
public import StacksAndModuli.API.PartialProjectiveResolutionFlat

/-!
# Closed fibres of coefficient-flat partial projective resolutions

Let `R → S` be flat, and let a partial projective resolution over `S` resolve an
`R`-flat module.  Quotienting every term by the extension of an ideal `I ⊆ R`
gives a partial projective resolution over `S / IS`.

The proof combines coefficient-flatness of every successive syzygy with exactness
of quotienting a short exact sequence whose cokernel is flat over `R`.  This is the
closed-fibre resolution step in the Noetherian proof of openness of the relative
flat locus.

Main declaration:

* `Module.IsPartialProjectiveResolution.quotientByMappedIdeal_of_flat`.
-/

@[expose] public section

universe u

noncomputable section

namespace Module.IsPartialProjectiveResolution

set_option linter.style.haveILetI false

/-- A coefficient-flat partial projective resolution remains a partial projective
resolution after passage to a closed fibre. -/
theorem quotientByMappedIdeal_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module S M]
    [AddCommGroup K] [Module S K]
    (hres : Module.IsPartialProjectiveResolution S e M K)
    (hM : @Module.Flat R M _ _ (Module.compHom M (algebraMap R S)))
    (I : Ideal R) :
    let J := I.map (algebraMap R S)
    letI : SMul (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
      Ideal.Quotient.smulModuleQuotient J
    letI : Module (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
      Ideal.Quotient.moduleQuotient J
    letI : SMul (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
      Ideal.Quotient.smulModuleQuotient J
    letI : Module (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
      Ideal.Quotient.moduleQuotient J
    Module.IsPartialProjectiveResolution (S ⧸ J) e
      (M ⧸ J • (⊤ : Submodule S M))
      (K ⧸ J • (⊤ : Submodule S K)) := by
  induction hres with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      let J := I.map (algebraMap R S)
      letI : Module R M := Module.compHom M (algebraMap R S)
      letI : Module R K := Module.compHom K (algebraMap R S)
      letI : Module R F := Module.compHom F (algebraMap R S)
      letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
      letI : IsScalarTower R S K := IsScalarTower.of_compHom R S K
      letI : IsScalarTower R S F := IsScalarTower.of_compHom R S F
      letI : Module.Flat R M := hM
      have hshort := LinearMap.quotientByMappedIdeal_shortExact_of_flat
        I i f hi (LinearMap.exact_iff.mpr hexact.symm) hf
      letI : SMul (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : SMul (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : SMul (S ⧸ J) (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : Module.Projective (S ⧸ J)
          (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.projective_moduleQuotient J
      let iq := LinearMap.quotientByIdealOverQuotient J i
      let fq := LinearMap.quotientByIdealOverQuotient J f
      have hexq : Function.Exact iq fq := by
        change Function.Exact (LinearMap.quotientByIdeal J i)
          (LinearMap.quotientByIdeal J f)
        exact hshort.2.1
      exact Module.IsPartialProjectiveResolution.zero fq hshort.2.2 iq
        hshort.1 (LinearMap.exact_iff.mp hexq).symm
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact ih =>
      let J := I.map (algebraMap R S)
      letI : Module R M := Module.compHom M (algebraMap R S)
      letI : Module R K' := Module.compHom K' (algebraMap R S)
      letI : Module R K := Module.compHom K (algebraMap R S)
      letI : Module R F := Module.compHom F (algebraMap R S)
      letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
      letI : IsScalarTower R S K' := IsScalarTower.of_compHom R S K'
      letI : IsScalarTower R S K := IsScalarTower.of_compHom R S K
      letI : IsScalarTower R S F := IsScalarTower.of_compHom R S F
      have hK' : Module.Flat R K' := hres.flat_final_of_flat hM
      letI : Module.Flat R K' := hK'
      have hshort := LinearMap.quotientByMappedIdeal_shortExact_of_flat
        I i f hi (LinearMap.exact_iff.mpr hexact.symm) hf
      letI : SMul (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (M ⧸ J • (⊤ : Submodule S M)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : SMul (S ⧸ J) (K' ⧸ J • (⊤ : Submodule S K')) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (K' ⧸ J • (⊤ : Submodule S K')) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (K' ⧸ J • (⊤ : Submodule S K')) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : SMul (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (K ⧸ J • (⊤ : Submodule S K)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : SMul (S ⧸ J) (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.smulModuleQuotient J
      letI : Module (S ⧸ J) (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.moduleQuotient J
      letI : IsScalarTower S (S ⧸ J)
          (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.isScalarTower_moduleQuotient J
      letI : Module.Projective (S ⧸ J)
          (F ⧸ J • (⊤ : Submodule S F)) :=
        Ideal.Quotient.projective_moduleQuotient J
      have ih' := ih hM
      let iq := LinearMap.quotientByIdealOverQuotient J i
      let fq := LinearMap.quotientByIdealOverQuotient J f
      have hexq : Function.Exact iq fq := by
        change Function.Exact (LinearMap.quotientByIdeal J i)
          (LinearMap.quotientByIdeal J f)
        exact hshort.2.1
      exact Module.IsPartialProjectiveResolution.succ ih' fq hshort.2.2 iq
        hshort.1 (LinearMap.exact_iff.mp hexq).symm

end Module.IsPartialProjectiveResolution

end

end
