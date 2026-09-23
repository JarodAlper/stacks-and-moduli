module

public import StacksAndModuli.API.SheafCohomologyModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# When is `Γ(X, 𝒪_X) = k`?

For a scheme `X` over a field `k`, the ring of global functions is a `k`-algebra
(`AlgebraicGeometry.Scheme.instAlgebraGlobalSections`). Numerical invariants such as
`h⁰(X, 𝒪_X)` and the genus are dimensions over `k`, and they take the values one expects
exactly when the structure map `k → Γ(X, 𝒪_X)` is *bijective* — the classical
`Γ(X, 𝒪_X) = k`.

This file collects the conditions under which that happens and the linear-algebra
consequences. Mathlib already supplies the two hard inputs, for a scheme universally closed
over a field: its global sections are integral over the field, and for an integral scheme
they form a field. We also prove the more flexible connected-reduced version: an integral
algebra over a field is zero-dimensional, a connected reduced zero-dimensional ring is a
domain, and hence over an algebraically closed field it is the base field.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_baseRingHom`: `k → Γ(X, 𝒪_X)` is an integral ring
  map for `X` universally closed over `Spec k`.
* `AlgebraicGeometry.Scheme.bijective_baseRingHom_of_isAlgClosed`: `Γ(X, 𝒪_X) = k` for an
  integral scheme universally closed over an algebraically closed field.
* `AlgebraicGeometry.Scheme.bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected`:
  the corresponding result for a connected reduced scheme.
* `AlgebraicGeometry.Scheme.bijective_baseRingHom_spec`: `Γ(Spec R, 𝒪) = R`.
* `AlgebraicGeometry.Scheme.h_structureModule_zero_eq_one`: `h⁰(X, 𝒪_X) = 1` in that
  situation.
* `AlgebraicGeometry.Scheme.finrank_globalSections_eq_one` and
  `…free_globalSections`: the linear algebra that `Γ(X, 𝒪_X) = k` provides, namely that
  `Γ(X, 𝒪_X)` is free of rank one over `k`. This is what collapses the tower law
  `dim_k = dim_k Γ · dim_Γ` used to compare the several readings of the genus.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Limits

universe u

/-- An integral algebra over a field has Krull dimension at most zero. -/
lemma RingHom.krullDimLE_zero_of_isIntegral_of_field {k R : Type*} [Field k] [CommRing R]
    (f : k →+* R) (hf : f.IsIntegral) : Ring.KrullDimLE 0 R := by
  apply Ring.KrullDimLE.mk₀
  intro P hP
  let _ : P.IsPrime := hP
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf P
  let _ : (P.comap f).IsPrime := hP.comap f
  infer_instance

/-- The localization of a reduced zero-dimensional ring at a maximal ideal is a field. -/
lemma Ring.KrullDimLE.isField_localizationAtPrime_of_isReduced
    {R : Type*} [CommRing R] [IsReduced R] [Ring.KrullDimLE 0 R]
    (P : Ideal R) (hP : P.IsMaximal) : IsField (Localization.AtPrime P) := by
  let _ : P.IsPrime := hP.isPrime
  have hpmin : P ∈ minimalPrimes R := Ideal.mem_minimalPrimes_of_krullDimLE_zero P
  let _ : Ring.KrullDimLE 0 (Localization.AtPrime P) :=
    Ring.KrullDimLE.of_isLocalization P hpmin _
  exact Ring.KrullDimLE.isField_of_isReduced

/-- Every principal ideal of a reduced zero-dimensional ring is idempotent. -/
lemma Ring.KrullDimLE.isIdempotentElem_span_singleton_of_isReduced
    {R : Type*} [CommRing R] [IsReduced R] [Ring.KrullDimLE 0 R] (a : R) :
    IsIdempotentElem (Ideal.span {a}) := by
  rw [IsIdempotentElem]
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let _ : Field (Localization.AtPrime P) :=
    (Ring.KrullDimLE.isField_localizationAtPrime_of_isReduced P hP).toField
  rcases (Ideal.eq_bot_or_top
    (Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span {a}))) with h | h
  · rw [Ideal.map_mul, h]
    simp
  · rw [Ideal.map_mul, h]
    simp

/-- If the prime spectrum is connected, every idempotent is zero or one. -/
lemma IsIdempotentElem.eq_zero_or_one_of_connected_primeSpectrum
    {R : Type*} [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  let c := E ⟨e, he⟩
  rcases (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace (PrimeSpectrum R))).2
      (c : Set (PrimeSpectrum R)) c.2 with hc | hc
  · left
    have hc' : c = ⊥ := by
      ext x
      simpa using Set.ext_iff.mp hc x
    have h' : (⟨e, he⟩ : {e : R // IsIdempotentElem e}) = ⟨0, .zero⟩ :=
      (E.symm_apply_apply ⟨e, he⟩).symm.trans <|
        (congrArg E.symm hc').trans <| by
          simpa [E] using
            (PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot (R := R))
    exact congrArg Subtype.val h'
  · right
    have hc' : c = ⊤ := by
      ext x
      simpa using Set.ext_iff.mp hc x
    have h' : (⟨e, he⟩ : {e : R // IsIdempotentElem e}) = ⟨1, .one⟩ :=
      (E.symm_apply_apply ⟨e, he⟩).symm.trans <|
        (congrArg E.symm hc').trans <| by
          simpa [E] using
            (PrimeSpectrum.isIdempotentElemEquivClopens_symm_top (R := R))
    exact congrArg Subtype.val h'

/-- A reduced zero-dimensional ring with connected prime spectrum is a domain. -/
lemma isDomain_of_isReduced_of_krullDimLE_zero_of_connected_primeSpectrum
    {R : Type*} [CommRing R] [IsReduced R] [Ring.KrullDimLE 0 R]
    [ConnectedSpace (PrimeSpectrum R)] : IsDomain R := by
  let _ : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let _ : NoZeroDivisors R := ⟨by
    intro a b hab
    obtain ⟨e, he, hae⟩ :=
      (Ideal.isIdempotentElem_iff_of_fg (Ideal.span {a})
        (Submodule.fg_span_singleton a)).mp
          (Ring.KrullDimLE.isIdempotentElem_span_singleton_of_isReduced a)
    rcases he.eq_zero_or_one_of_connected_primeSpectrum with rfl | rfl
    · left
      have ha : a ∈ Ideal.span {a} := Ideal.subset_span (Set.mem_singleton a)
      rw [hae] at ha
      simpa using ha
    · right
      have ha : IsUnit a := Ideal.span_singleton_eq_top.mp (by simpa using hae)
      obtain ⟨u, rfl⟩ := ha
      simpa using hab⟩
  exact NoZeroDivisors.to_isDomain R

namespace AlgebraicGeometry.Scheme

/-- For an integral scheme universally closed over a field, the ring of global sections is
a field. This is Mathlib's `isField_of_universallyClosed`, stated for the structure
morphism of a `k`-scheme. -/
lemma isField_globalSections (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] : IsField Γ(X, ⊤) :=
  isField_of_universallyClosed k (X ↘ Spec (CommRingCat.of k))

/-- For a scheme universally closed over `Spec k`, the structure map `k → Γ(X, 𝒪_X)` is an
integral ring homomorphism.

This is `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`, transported across the
`Γ`–`Spec` isomorphism so that it speaks about `Scheme.baseRingHom`. -/
lemma isIntegral_baseRingHom (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    (X.baseRingHom (CommRingCat.of k)).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed (X ↘ Spec (CommRingCat.of k))

/-- If `X` is connected and universally closed over a field, then the prime spectrum of
its global-sections ring is connected.

Indeed, universal closedness makes `X.toSpecΓ` closed, while quasi-compactness makes it
dominant. It is therefore surjective, and connectedness descends along that map. -/
lemma connectedSpace_primeSpectrum_globalSections (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    [ConnectedSpace X] : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) := by
  let _ : CompactSpace X :=
    (quasiCompact_iff_compactSpace (X ↘ Spec (CommRingCat.of k))).mp inferInstance
  have hcomp : UniversallyClosed
      (X.toSpecΓ ≫ Spec.map (X ↘ Spec (CommRingCat.of k)).appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  let _ : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated X.toSpecΓ
      (Spec.map (X ↘ Spec (CommRingCat.of k)).appTop)
  exact X.toSpecΓ.surjective.connectedSpace X.toSpecΓ.continuous

/-- The global-sections ring of a connected reduced scheme universally closed over a field
is a domain. -/
lemma isDomain_globalSections_of_isReduced_of_connected (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
    [ConnectedSpace X] [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    IsDomain Γ(X, ⊤) := by
  let _ : Ring.KrullDimLE 0 Γ(X, ⊤) :=
    (X.baseRingHom (CommRingCat.of k)).krullDimLE_zero_of_isIntegral_of_field
      (isIntegral_baseRingHom k X)
  let _ : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    connectedSpace_primeSpectrum_globalSections k X
  exact isDomain_of_isReduced_of_krullDimLE_zero_of_connected_primeSpectrum

/-- `Γ(X, 𝒪_X) = k` for a connected reduced scheme universally closed over an
algebraically closed field. -/
theorem bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [ConnectedSpace X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Function.Bijective (X.baseRingHom (CommRingCat.of k)) := by
  let _ : IsDomain Γ(X, ⊤) := isDomain_globalSections_of_isReduced_of_connected k X
  exact IsAlgClosed.ringHom_bijective_of_isIntegral _ (isIntegral_baseRingHom k X)

/-- **`Γ(X, 𝒪_X) = k` for an integral scheme universally closed over an algebraically
closed field.**

The ring of global sections is a domain (`X` is integral) and integral over `k` (`X` is
universally closed over `Spec k`), so over an algebraically closed field the structure map
is bijective. Every geometric fibre of a proper geometrically integral family is such a
scheme, which is what makes fibrewise `h⁰` and the genus behave. -/
theorem bijective_baseRingHom_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Function.Bijective (X.baseRingHom (CommRingCat.of k)) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (isIntegral_baseRingHom k X)

/-- `Γ(Spec R, 𝒪) = R`: the structure map of an affine scheme over itself is bijective.

This is the sanity check that the chain
`baseRingHom → Algebra k Γ(X, ⊤) → Module k (Hⁿ(X, F)) → h` computes the expected
values on the simplest example. -/
lemma bijective_baseRingHom_spec (R : CommRingCat.{u}) :
    Function.Bijective ((Spec R).baseRingHom R) := by
  have h : (Spec R).baseRingHom R = ((Scheme.ΓSpecIso R).inv).hom := by
    rw [baseRingHom_eq]
    congr 1
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

/-- If the structure map `k → Γ(X, 𝒪_X)` is bijective, then `Γ(X, 𝒪_X)` is free of
rank one over `k`. Recorded separately from the `finrank` statement because the tower law for
`finrank` takes freeness as a hypothesis. -/
lemma free_globalSections (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (hb : Function.Bijective (X.baseRingHom (CommRingCat.of k))) :
    Module.Free k Γ(X, ⊤) :=
  Module.Free.of_equiv (LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) hb)

/-- If the structure map `k → Γ(X, 𝒪_X)` is bijective — the classical `Γ(X, 𝒪_X) = k`
— then `Γ(X, 𝒪_X)` is one-dimensional over `k`. -/
lemma finrank_globalSections_eq_one (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (hb : Function.Bijective (X.baseRingHom (CommRingCat.of k))) :
    Module.finrank k Γ(X, ⊤) = 1 := by
  have e : k ≃ₗ[k] Γ(X, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) hb
  rw [← e.finrank_eq, Module.finrank_self]

/-- **`h⁰(X, 𝒪_X) = 1`** for an integral scheme proper over an algebraically closed field.
This is the book's `H⁰(C, 𝒪_C) = k`, in the form the Euler characteristic uses. -/
lemma h_structureModule_zero_eq_one (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Modules.h k (structureModule X) 0 = 1 := by
  rw [Modules.h_structureModule_zero,
    finrank_globalSections_eq_one k X (bijective_baseRingHom_of_isAlgClosed k X)]

/-- `h⁰(X, 𝒪_X) = 1` for a connected reduced scheme universally closed over an
algebraically closed field. -/
lemma h_structureModule_zero_eq_one_of_isReduced_of_connected
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [ConnectedSpace X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Modules.h k (structureModule X) 0 = 1 := by
  rw [Modules.h_structureModule_zero,
    finrank_globalSections_eq_one k X
      (bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected k X)]

/-- `h⁰(Spec k, 𝒪) = 1`. -/
lemma h_structureModule_spec_zero (k : Type u) [Field k] :
    Modules.h k (structureModule (Spec (CommRingCat.of k))) 0 = 1 := by
  rw [Modules.h_structureModule_zero,
    finrank_globalSections_eq_one k _ (bijective_baseRingHom_spec (CommRingCat.of k))]

end AlgebraicGeometry.Scheme
