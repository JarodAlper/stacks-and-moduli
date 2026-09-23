module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.QuasiFinite.Polynomial

/-!
# A smooth quasi-finite ring map is étale

Stacks Project tag **02GK**, label `morphisms-lemma-etale-smooth-unramified`, in
`morphisms.tex`.

> A morphism is étale if and only if it is smooth and unramified — equivalently, smooth of
> relative dimension zero.

The form needed by §3.1 is the ring-level statement: a smooth quasi-finite ring map is étale.

**Proof route.** Smooth implies flat (Mathlib: `Algebra.Smooth.flat`,
`Mathlib/RingTheory/Smooth/Flat.lean`). Quasi-finiteness makes the fibres finite over the
residue fields, and a smooth algebra over a field with finite-dimensional fibre is unramified
— this is where relative dimension zero enters. Mathlib then closes the argument with
`Algebra.Etale.of_formallyUnramified_of_flat`
(`Mathlib/RingTheory/Smooth/Fiber.lean:247`), which turns formally unramified plus flat into
étale. The missing step is therefore "smooth + quasi-finite ⇒ formally unramified", i.e. the
vanishing of `Ω` in relative dimension zero.

Note Mathlib does have `Algebra.QuasiFinite` and the full `RingHom.QuasiFinite` API
(`Mathlib/RingTheory/QuasiFinite/Basic.lean`, `Mathlib/RingTheory/RingHom/QuasiFinite.lean`),
so only this comparison is absent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Polynomial

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}

set_option backward.isDefEq.respectTransparency false in
/-- If the composite is quasi-finite at a point and the first map is universally
open, then the second map is quasi-finite at the image point. -/
lemma Scheme.Hom.QuasiFiniteAt.cancel_right_of_isOpenMap
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [UniversallyOpen f]
    (hfg : (f ≫ g).QuasiFiniteAt x) : g.QuasiFiniteAt (f x) := by
  let e : (f ≫ g) x = g (f x) := Scheme.Hom.comp_apply f g x
  let ρ : Spec (Z.residueField ((f ≫ g) x)) ⟶
      Spec (Z.residueField (g (f x))) :=
    Spec.map (Z.residueFieldCongr e.symm).hom
  let a : (f ≫ g).fiber ((f ≫ g) x) ⟶ g.fiber (g (f x)) :=
    pullback.lift ((f ≫ g).fiberι _ ≫ f)
      ((f ≫ g).fiberToSpecResidueField _ ≫ ρ) (by
        rw [Category.assoc]
        simpa [ρ] using (f ≫ g).fiber_fac ((f ≫ g) x))
  have ha_fiberι : a ≫ g.fiberι _ = (f ≫ g).fiberι _ ≫ f := by
    simp [a, Scheme.Hom.fiberι]
  have ha_residue : a ≫ g.fiberToSpecResidueField _ =
      (f ≫ g).fiberToSpecResidueField _ ≫ ρ := by
    simp [a, Scheme.Hom.fiberToSpecResidueField]
  have hρ : IsPullback (Z.fromSpecResidueField ((f ≫ g) x)) ρ (𝟙 Z)
      (Z.fromSpecResidueField (g (f x))) := by
    apply IsPullback.of_vert_isIso
    constructor
    simp [ρ]
  have houter : IsPullback ((f ≫ g).fiberι _)
      ((f ≫ g).fiberToSpecResidueField _ ≫ ρ) (f ≫ g)
      (Z.fromSpecResidueField (g (f x))) := by
    simpa [Scheme.Hom.fiber, Scheme.Hom.fiberι,
      Scheme.Hom.fiberToSpecResidueField] using
      (IsPullback.of_hasPullback (f ≫ g)
        (Z.fromSpecResidueField ((f ≫ g) x))).paste_vert hρ
  have ha_pb : IsPullback ((f ≫ g).fiberι _) a f (g.fiberι _) := by
    have hs : IsPullback ((f ≫ g).fiberι _)
        (a ≫ g.fiberToSpecResidueField _) (f ≫ g)
        (Z.fromSpecResidueField (g (f x))) := by
      simpa only [ha_residue] using houter
    exact IsPullback.of_bot hs ha_fiberι.symm
      (IsPullback.of_hasPullback g (Z.fromSpecResidueField (g (f x))))
  haveI : UniversallyOpen a :=
    MorphismProperty.of_isPullback ha_pb inferInstance
  have ha_point : a ((f ≫ g).asFiber x) = g.asFiber (f x) := by
    apply (g.fiberι _).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ha_fiberι, Scheme.Hom.comp_apply,
      Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hopen := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hfg
  rw [← ha_point]
  simpa only [Set.image_singleton] using a.isOpenMap _ hopen

set_option backward.isDefEq.respectTransparency false in
lemma RingHom.QuasiFiniteAt.of_specMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum S)
    (h : (Spec.map (CommRingCat.ofHom f)).QuasiFiniteAt p) :
    f.QuasiFiniteAt p.asIdeal := by
  algebraize [f]
  change Algebra.QuasiFinite R (Localization.AtPrime p.asIdeal)
  let q := p.asIdeal.under R
  letI := Localization.AtPrime.algebraOfLiesOver q p.asIdeal
  rw [← RingHom.quasiFinite_algebraMap]
  have hbase : (algebraMap R (Localization.AtPrime q)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.mpr (.of_isLocalization q.primeCompl)
  have hloc : (Localization.localRingHom q p.asIdeal f rfl).QuasiFinite := by
    apply (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p)).mp
    exact h
  convert hloc.comp hbase
  ext r
  simpa [RingHom.algebraMap_toAlgebra] using
    (IsScalarTower.algebraMap_apply R S (Localization.AtPrime p.asIdeal) r)

/-- The affine-line projection is nowhere quasi-finite. -/
lemma polynomial_spec_not_quasiFiniteAt {R : Type u} [CommRing R]
    (p : PrimeSpectrum R[X]) :
    ¬ (Spec.map (CommRingCat.ofHom
      (Polynomial.C : R →+* R[X]))).QuasiFiniteAt p := by
  intro h
  have h' : (Spec.map (CommRingCat.ofHom
      (algebraMap R R[X]))).QuasiFiniteAt p := by
    simpa [Polynomial.algebraMap_eq] using h
  have hf := RingHom.QuasiFiniteAt.of_specMap (algebraMap R R[X]) p h'
  have halg : (algebraMap R R[X]).toAlgebra =
      (inferInstance : Algebra R R[X]) := toAlgebra_algebraMap
  rw [RingHom.QuasiFiniteAt, halg] at hf
  apply Polynomial.not_quasiFiniteAt p.asIdeal
  exact hf

/-- A positive-dimensional affine-space projection is nowhere quasi-finite. -/
lemma mvPolynomial_spec_not_quasiFiniteAt {R : Type u} [CommRing R]
    (n : ℕ) (hn : n ≠ 0)
    (p : PrimeSpectrum (MvPolynomial (Fin n) R)) :
    ¬ (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))).QuasiFiniteAt p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let A := MvPolynomial (Fin m) R
  let e : MvPolynomial (Fin (m + 1)) R ≃ₐ[R] A[X] :=
    MvPolynomial.finSuccEquiv R m
  let c₀ : R[X] →+* A[X] :=
    Polynomial.mapRingHom (algebraMap R A)
  let c : R[X] →+* MvPolynomial (Fin (m + 1)) R :=
    e.symm.toRingEquiv.toRingHom.comp c₀
  have hc_comp : c.comp Polynomial.C =
      (MvPolynomial.C : R →+* MvPolynomial (Fin (m + 1)) R) := by
    apply DFunLike.ext _ _
    intro r
    dsimp only [RingHom.comp_apply]
    dsimp [c]
    change e.symm.toRingEquiv (c₀ (Polynomial.C r)) = MvPolynomial.C r
    calc
      _ = e.symm.toRingEquiv (algebraMap R A[X] r) := by
        congr 1
        simp [c₀]
      _ = algebraMap R (MvPolynomial (Fin (m + 1)) R) r :=
        e.symm.commutes r
      _ = MvPolynomial.C r := rfl
  have hc₀ : c₀.Smooth := by
    letI := c₀.toAlgebra
    letI : IsScalarTower R R[X] A[X] :=
      .of_algebraMap_eq (by
        intro r
        simp [c₀, RingHom.algebraMap_toAlgebra])
    change c₀.Smooth
    apply RingHom.Smooth.isStableUnderBaseChange R A R[X] A[X]
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  have hc : c.Smooth :=
    hc₀.comp (RingHom.Smooth.of_bijective e.symm.bijective)
  let a : Spec (.of (MvPolynomial (Fin (m + 1)) R)) ⟶ Spec (.of R[X]) :=
    Spec.map (CommRingCat.ofHom c)
  let b : Spec (.of R[X]) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
  have hab : a ≫ b = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (Fin (m + 1)) R)) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hc_comp)
  haveI : Smooth a := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact hc
  have hbsm : (Polynomial.C : R →+* R[X]).Smooth := by
    rw [← Polynomial.algebraMap_eq, RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  haveI : Smooth b := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact hbsm
  intro h
  have hcomp : (a ≫ b).QuasiFiniteAt p := hab ▸ h
  have hbq : b.QuasiFiniteAt (a p) :=
    Scheme.Hom.QuasiFiniteAt.cancel_right_of_isOpenMap hcomp
  exact polynomial_spec_not_quasiFiniteAt (a p) hbq

end AlgebraicGeometry

namespace RingHom

universe u v w

open AlgebraicGeometry

/-- Composition preserves étaleness, with all three ring universes explicit. -/
private lemma Etale.comp' {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale := by
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hf hg ⊢
  exact ⟨hf.1.comp hg.1, hf.2.comp hg.2⟩

/-- A standard-smooth quasi-finite ring map between rings in one universe is
étale. -/
private lemma IsStandardSmooth.etale_of_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hstd : f.IsStandardSmooth) (hqf : f.QuasiFinite) :
    f.Etale := by
  by_cases hS : Nontrivial S
  · letI : Nontrivial S := hS
    obtain ⟨n, g, hgf, hge⟩ := hstd.exists_etale_mvPolynomial
    have hn : n = 0 := by
      by_contra hn
      let a := Spec.map (CommRingCat.ofHom g)
      let b := Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
      have hab : a ≫ b = Spec.map (CommRingCat.ofHom f) := by
        rw [← Spec.map_comp]
        exact congrArg Spec.map (CommRingCat.hom_ext hgf)
      haveI : AlgebraicGeometry.Etale a := by
        rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
        exact hge
      have hbsm : (MvPolynomial.C :
          R →+* MvPolynomial (Fin n) R).Smooth := by
        rw [← MvPolynomial.algebraMap_eq, RingHom.smooth_algebraMap]
        exact ⟨inferInstance, inferInstance⟩
      haveI : AlgebraicGeometry.Smooth b := by
        rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
        exact hbsm
      haveI : AlgebraicGeometry.LocallyQuasiFinite (a ≫ b) := by
        rw [hab, HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.LocallyQuasiFinite)]
        exact hqf
      let p : PrimeSpectrum S := Classical.choice inferInstance
      have hcomp : (a ≫ b).QuasiFiniteAt p :=
        (a ≫ b).quasiFiniteAt p
      have hbq : b.QuasiFiniteAt (a p) :=
        Scheme.Hom.QuasiFiniteAt.cancel_right_of_isOpenMap hcomp
      exact mvPolynomial_spec_not_quasiFiniteAt n hn (a p) hbq
    subst n
    have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R).Etale := by
      apply RingHom.Etale.of_bijective
      rw [← MvPolynomial.isEmptyAlgEquiv_symm_toRingHom]
      exact (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.bijective
    rw [← hgf]
    exact RingHom.Etale.stableUnderComposition _ _ hC hge
  · haveI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    rw [RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero]
    algebraize [f]
    rw [← f.algebraMap_toAlgebra,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    infer_instance

/-- A smooth quasi-finite ring map between rings in one universe is étale. -/
private theorem Etale.of_smooth_of_quasiFinite_sameUniverse
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsm : f.Smooth) (hqf : f.QuasiFinite) : f.Etale := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth] at hsm
  obtain ⟨s, hs, hstd⟩ := hsm
  apply (RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
    RingHom.Etale.ofLocalizationSpanTarget f).mp
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hloc : (algebraMap S (Localization.Away t)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.mpr
      (.of_isLocalization (.powers t))
  exact IsStandardSmooth.etale_of_quasiFinite _ (hstd t ht)
    (hloc.comp hqf)

/-- **Stacks 02GK** (`morphisms-lemma-etale-smooth-unramified`), ring-level form: a smooth
quasi-finite ring map is étale. -/
@[stacks 02GK]
theorem Etale.of_smooth_of_quasiFinite_of_ringHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hsm : φ.Smooth) (hqf : φ.QuasiFinite) : φ.Etale := by
  let φ' : ULift.{max u v} R →+* ULift.{max u v} S :=
    RingHom.ulift.{max u v, max u v} φ
  have hsm' : φ'.Smooth := by
    dsimp [φ', RingHom.ulift]
    exact (RingHom.Smooth.of_bijective ULift.ringEquiv.bijective).comp hsm |>.comp
      (RingHom.Smooth.of_bijective ULift.ringEquiv.symm.bijective)
  have hqf' : φ'.QuasiFinite := by
    dsimp [φ', RingHom.ulift]
    exact (RingHom.QuasiFinite.of_finite
      (RingHom.Finite.of_surjective _ ULift.ringEquiv.symm.surjective)).comp
        (hqf.comp (RingHom.QuasiFinite.of_finite
          (RingHom.Finite.of_surjective _ ULift.ringEquiv.surjective)))
  have het' : φ'.Etale :=
    Etale.of_smooth_of_quasiFinite_sameUniverse φ' hsm' hqf'
  have hback : (ULift.ringEquiv.toRingHom.comp
      (φ'.comp ULift.ringEquiv.symm.toRingHom)).Etale :=
    (RingHom.Etale.of_bijective ULift.ringEquiv.symm.bijective).comp' het' |>.comp'
      (RingHom.Etale.of_bijective ULift.ringEquiv.bijective)
  rw [show ULift.ringEquiv.toRingHom.comp
      (φ'.comp ULift.ringEquiv.symm.toRingHom) = φ by
    exact RingHom.comp_ulift_eq φ] at hback
  exact hback

end RingHom

namespace RingHom

/-- **Stacks 02GK** companion: an étale ring map is quasi-finite.

OBLIGATION. Mathlib has `RingHom.QuasiFinite` with a full API
(`Mathlib/RingTheory/RingHom/QuasiFinite.lean`: `.comp`, `.of_comp`, `.of_finite`,
`.isStableUnderBaseChange`, `.of_isIntegral_of_finiteType`, …) but no route from étale.

Proof route: étale implies unramified, so each fibre `κ(p) ⊗_R S` is a finite product of finite
separable extensions of `κ(p)` — this is the structure theorem for unramified algebras over a
field. In particular each fibre is finite-dimensional over `κ(p)`, which is precisely
`Algebra.QuasiFinite` as Mathlib defines it (`Mathlib/RingTheory/QuasiFinite/Basic.lean`). The
missing input is the fibrewise structure of unramified algebras; `Mathlib/RingTheory/Etale/Field.lean`
and `Mathlib/RingTheory/Unramified/LocalStructure.lean` are the relevant neighbourhoods. -/
theorem QuasiFinite.of_etale_of_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (h : φ.Etale) : φ.QuasiFinite := by
  algebraize [φ]
  constructor
  intro P hP
  -- the fibre is an unramified, essentially-of-finite-type, free algebra over the
  -- residue field, hence finite
  haveI : Algebra.FormallyUnramified R S := inferInstance
  haveI : Algebra.FormallyUnramified P.ResidueField (P.Fiber S) :=
    Algebra.FormallyUnramified.base_change P.ResidueField
  haveI : Algebra.FiniteType R S := inferInstance
  haveI : Algebra.FiniteType P.ResidueField (P.Fiber S) :=
    Algebra.FiniteType.baseChange P.ResidueField
  haveI : Algebra.EssFiniteType P.ResidueField (P.Fiber S) :=
    Algebra.EssFiniteType.of_finiteType _ _
  exact Algebra.FormallyUnramified.finite_of_free _ _

end RingHom
