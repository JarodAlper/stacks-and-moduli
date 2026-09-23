module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Permanence of finiteness properties along a faithfully flat ring map

Stacks Project §`02KJ` (`descent-section-descent-finiteness-smoothness`) of `descent.tex`,
tags **02KK** and **0367**, plus the quasi-finite codescent used alongside them.

- **02KK** `descent-lemma-flat-finitely-presented-permanence-algebra`:
  > Let `R → A → B` be ring maps. Assume `R → B` is of finite presentation and `A → B` is
  > faithfully flat and of finite presentation. Then `R → A` is of finite presentation.

  This is **the hardest lemma of that section** (~90 lines in the Stacks Project), going through
  `algebra-lemma-characterize-finite-presentation` and the colimit/limit machinery of
  `algebra-lemma-flat-finite-presentation-limit-flat`.

- **0367** `descent-lemma-finite-type-local-source-fppf-algebra`: the same statement with
  "finite type" in place of "finite presentation" for `R → B`, proved via `034Y`
  (`algebra-lemma-descend-faithfully-flat-finite-presentation`).

Mathlib has faithfully flat **codescent** for these properties
(`RingHom.{Finite,FiniteType,FinitePresentation}.codescendsAlong_faithfullyFlat` in
`Mathlib/RingTheory/Finiteness/Descent.lean`), which is the statement about a *base change*
`R → A` versus `T → T ⊗_R A`. What is missing is this *permanence* form, about a factorisation
`R → A → B` — the two are genuinely different statements, and the permanence form is what
locality on the source needs.

Mathlib likewise has `RingHom.QuasiFinite` with `isStableUnderBaseChange`, `propertyIsLocal`
and `ofLocalizationSpanTarget` (`Mathlib/RingTheory/RingHom/QuasiFinite.lean`) but no
`codescendsAlong_faithfullyFlat`.
-/

@[expose] public section

namespace RingHom

/-- **Stacks 02KK** (`descent-lemma-flat-finitely-presented-permanence-algebra`). Given
`R → A → B` with `R → B` of finite presentation and `A → B` faithfully flat of finite
presentation, `R → A` is of finite presentation. -/
@[stacks 02KK]
theorem FinitePresentation.of_comp_of_faithfullyFlat_permanence {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).FinitePresentation) (hψ : ψ.FinitePresentation)
    (hff : ψ.FaithfullyFlat) : φ.FinitePresentation := by
  sorry

/-- **Stacks 0367** (`descent-lemma-finite-type-local-source-fppf-algebra`). Given `R → A → B`
with `R → B` of finite type and `A → B` faithfully flat of finite presentation, `R → A` is of
finite type. -/
@[stacks 0367]
theorem FiniteType.of_comp_of_faithfullyFlat_finitePresentation_permanence {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).FiniteType) (hψ : ψ.FinitePresentation) (hff : ψ.FaithfullyFlat) :
    φ.FiniteType := by
  sorry

/-- Faithfully flat codescent for quasi-finiteness, the missing companion to Mathlib's
`RingHom.{Finite,FiniteType,FinitePresentation}.codescendsAlong_faithfullyFlat`.

Corresponds to Stacks **02VI** (`descent-lemma-descending-property-quasi-finite`), "the property
`P(f) = f is quasi-finite` is fpqc local on the base", in its affine/ring-theoretic form.

Proof route: quasi-finiteness is a fibrewise finiteness condition
(`Algebra.QuasiFinite`, `Mathlib/RingTheory/QuasiFinite/Basic.lean`: `κ(p) ⊗_R S` is
finite-dimensional over `κ(p)`), and a faithfully flat base change is surjective on `Spec`, so
every fibre of `R → A` is a fibre of the base change. Mathlib's
`RingHom.QuasiFinite.isStableUnderBaseChange` gives the easy direction. -/
@[stacks 02VI]
theorem QuasiFinite.codescendsAlong_faithfullyFlat_of_ringHom :
    RingHom.CodescendsAlong @RingHom.QuasiFinite @RingHom.FaithfullyFlat := by
  refine RingHom.CodescendsAlong.mk (Q := @RingHom.FaithfullyFlat)
    RingHom.QuasiFinite.respectsIso ?_
  introv hQ H
  rw [RingHom.quasiFinite_algebraMap] at H ⊢
  haveI : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.mp hQ
  constructor
  intro p hp
  obtain ⟨P', hP'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := S) ⟨p, hp⟩
  haveI hfin1 : Module.Finite P'.asIdeal.ResidueField
      (P'.asIdeal.Fiber (TensorProduct R S T)) :=
    H.finite_fiber P'.asIdeal
  have hcomap : p = P'.asIdeal.comap (algebraMap R S) :=
    congrArg PrimeSpectrum.asIdeal hP'.symm
  letI : Algebra p.ResidueField P'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p P'.asIdeal (algebraMap R S) hcomap).toAlgebra
  haveI : IsScalarTower R p.ResidueField P'.asIdeal.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    show algebraMap R P'.asIdeal.ResidueField r =
      Ideal.ResidueField.map p P'.asIdeal (algebraMap R S) hcomap
        (algebraMap R p.ResidueField r)
    rw [Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply R S P'.asIdeal.ResidueField]
  -- the residue-field extension is faithfully flat
  haveI : IsLocalHom (algebraMap p.ResidueField P'.asIdeal.ResidueField) := by
    refine ⟨fun a ha ↦ isUnit_iff_ne_zero.mpr fun h ↦ ?_⟩
    rw [h, map_zero] at ha
    exact not_isUnit_zero ha
  haveI : Module.FaithfullyFlat p.ResidueField P'.asIdeal.ResidueField :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- the extended fibre is finite, via the two cancellation isomorphisms
  haveI hfin2 : Module.Finite P'.asIdeal.ResidueField
      (TensorProduct p.ResidueField P'.asIdeal.ResidueField (p.Fiber T)) := by
    have e1 : TensorProduct p.ResidueField P'.asIdeal.ResidueField (p.Fiber T) ≃ₗ[P'.asIdeal.ResidueField]
        TensorProduct R P'.asIdeal.ResidueField T :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R p.ResidueField
        P'.asIdeal.ResidueField P'.asIdeal.ResidueField T
    have e2 : P'.asIdeal.Fiber (TensorProduct R S T) ≃ₗ[P'.asIdeal.ResidueField]
        TensorProduct R P'.asIdeal.ResidueField T :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S
        P'.asIdeal.ResidueField P'.asIdeal.ResidueField T
    exact Module.Finite.equiv (e2.trans e1.symm)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
    P'.asIdeal.ResidueField

end RingHom

namespace RingHom

/-- **Stacks 08XE** (`descent-theorem-descend-algebra-properties`), the formally-unramified
clause, in permanence form. Given `R → A → B` with `R → B` formally unramified and `A → B`
étale and faithfully flat, `R → A` is formally unramified.

Proof route: `Ω_{B/A} = 0` for `A → B` étale, so the conormal sequence for `R → A → B` gives
`Ω_{A/R} ⊗_A B ≅ Ω_{B/R} = 0`; faithful flatness of `A → B` then forces `Ω_{A/R} = 0`. Mathlib
has the Kähler differential machinery (`Mathlib/RingTheory/Kaehler/`) and
`Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential`. -/
@[stacks 08XE]
theorem FormallyUnramified.of_comp_of_etale_faithfullyFlat_permanence {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).FormallyUnramified) (hψ : ψ.Etale) (hff : ψ.FaithfullyFlat) :
    φ.FormallyUnramified := by
  algebraize [φ, ψ, ψ.comp φ]
  haveI : Algebra.FormallyEtale A B := Algebra.Etale.formallyEtale
  show Algebra.FormallyUnramified R A
  rw [Algebra.formallyUnramified_iff]
  -- the Kähler differentials of `R → B` vanish, and pull back to `B ⊗ Ω[A⁄R]`
  haveI hB : Subsingleton (Ω[B⁄R]) :=
    (Algebra.formallyUnramified_iff R B).mp inferInstance
  haveI htensor : Subsingleton (TensorProduct A B (Ω[A⁄R])) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      R A B).toEquiv.injective.subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A B (Ω[A⁄R])

/-- **Stacks 03X4** (`descent-lemma-descending-property-quasi-finite` along étale surjections),
permanence form. Given `R → A → B` with `R → B` quasi-finite and `A → B` faithfully flat,
`R → A` is quasi-finite.

Proof route: quasi-finiteness is fibrewise finite-dimensionality of `κ(p) ⊗_R A`. Faithful
flatness makes `Spec B → Spec A` surjective, so each fibre of `R → A` embeds in a fibre of
`R → B` after a faithfully flat base change, and finite-dimensionality descends. -/
@[stacks 03X4]
theorem QuasiFinite.of_comp_of_faithfullyFlat_permanence {R A B : Type*} [CommRing R]
    [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).QuasiFinite) (hff : ψ.FaithfullyFlat) : φ.QuasiFinite := by
  algebraize [φ, ψ, ψ.comp φ]
  constructor
  intro P hP
  haveI : Module.Finite P.ResidueField (P.Fiber B) :=
    Algebra.QuasiFinite.finite_fiber P
  -- the fibre of `A` embeds `κ(P)`-linearly into the fibre of `B`
  set F : P.Fiber A →ₐ[P.ResidueField] P.Fiber B :=
    Algebra.TensorProduct.map (AlgHom.id P.ResidueField P.ResidueField)
      (IsScalarTower.toAlgHom R A B) with hF
  -- injectivity: through the cancellation isomorphism, `F` is the faithfully flat unit
  have hunit : Function.Injective
      (TensorProduct.mk A B (TensorProduct R A P.ResidueField) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) _
  have hsq : ∀ x : TensorProduct R A P.ResidueField,
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B P.ResidueField)
        (TensorProduct.mk A B (TensorProduct R A P.ResidueField) 1 x) =
      (LinearMap.rTensor P.ResidueField
        (IsScalarTower.toAlgHom R A B).toLinearMap) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrinj : Function.Injective
      (LinearMap.rTensor P.ResidueField (IsScalarTower.toAlgHom R A B).toLinearMap) := by
    intro x y hxy
    apply hunit
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R A B B P.ResidueField).injective
    rw [hsq, hsq, hxy]
  have hFinj : Function.Injective F := by
    intro x y hxy
    -- transport along the commutation with `rTensor`
    have hcomm : ∀ z : P.Fiber A,
        (TensorProduct.comm R A P.ResidueField)
          ((TensorProduct.comm R P.ResidueField A) z) = z := fun z ↦ by simp
    apply (TensorProduct.comm R P.ResidueField A).injective
    apply hrinj
    have hnat : ∀ z : P.Fiber A,
        (LinearMap.rTensor P.ResidueField (IsScalarTower.toAlgHom R A B).toLinearMap)
          ((TensorProduct.comm R P.ResidueField A) z) =
        (TensorProduct.comm R P.ResidueField B) (F z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp [hF]
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [hnat, hnat, hxy]
  exact Module.Finite.of_injective F.toLinearMap hFinj

end RingHom
