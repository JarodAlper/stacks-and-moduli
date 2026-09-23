module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Integral

/-!
# Ingredients for étale neighborhoods

This file collects reusable ingredients for spreading finite separable point data to a standard
étale algebra and applying that construction to smooth morphisms with affine target. They support
the formalization of Stacks Project tag 055U, but are independent of that tag's global statement.

The key construction clears the finitely many denominators in a primitive polynomial by scaling
its roots.  The resulting monic polynomial is defined over the original ring and its standard
étale algebra has a residue field containing the prescribed finite family.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial

namespace StacksProject

noncomputable section

universe u v

/-- A separably closed field is infinite.  In positive characteristic this uses that a finite
field is perfect, hence a finite separably closed field would be algebraically closed. -/
lemma infinite_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K] : Infinite K := by
  rcases finite_or_infinite K with hK | hK
  · letI : Finite K := hK
    letI : PerfectField K := PerfectField.ofFinite
    letI : IsAlgClosed K := IsSepClosed.isAlgClosed_of_perfectField K
    infer_instance
  · exact hK

/-- Separably closedness transports across a ring equivalence of fields. -/
lemma isSepClosed_of_ringEquiv {K R : Type*} [Field K] [Field R] [IsSepClosed K]
    (e : R ≃+* K) : IsSepClosed R where
  splits_of_separable p hp := by
    apply Polynomial.Splits.of_splits_map e.toRingHom
      (IsSepClosed.splits_of_separable (p.map e.toRingHom) (Polynomial.Separable.map hp))
    exact fun a _ ↦ e.surjective a

/-- A nonzero multivariable polynomial over a separably closed field is nonzero at some rational
point. -/
lemma exists_eval_ne_zero_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    {n : Type*} {g : MvPolynomial n K} (hg : g ≠ 0) :
    ∃ r : n → K, MvPolynomial.eval r g ≠ 0 := by
  letI : Infinite K := infinite_of_isSepClosed K
  contrapose! hg
  apply MvPolynomial.funext
  simpa using hg

/-- Every nonempty open subset of affine space over a separably closed field contains a rational
point. -/
lemma exists_rationalPoint_mem_open_affineSpace_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] {n : Type v}
    {U : Set (PrimeSpectrum (MvPolynomial n K))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r : n → K,
      PrimeSpectrum.comap (MvPolynomial.eval r) default ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, ⟨_, ⟨g, rfl⟩, rfl⟩, hxV, hVU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx hU
  have hg : g ≠ 0 := by
    intro e
    subst e
    simpa using hxV
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_isSepClosed K hg
  refine ⟨r, hVU ?_⟩
  apply (PrimeSpectrum.mem_basicOpen _ _).2
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum K).asIdeal]
  simpa using hr

/-- A finite family in the separable closure of a residue field spreads to the residue field of
a standard étale algebra over the original ring.

The output includes the standard étale presentation, its point in the separable closure, the
corresponding prime, and the induced embedding of its residue field. -/
lemma exists_standardEtalePair_spreading_finite_family
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {n : Type v} [Finite n]
    (a : n → SeparableClosure p.ResidueField) :
    ∃ (P : StandardEtalePair A) (h : P.Ring →ₐ[A] SeparableClosure p.ResidueField)
      (Q : Ideal P.Ring) (_ : Q.IsPrime)
      (ℓ : Q.ResidueField →+* SeparableClosure p.ResidueField),
      Q = RingHom.ker h.toRingHom ∧ p = Q.comap (algebraMap A P.Ring) ∧
        (∀ x, ℓ (algebraMap P.Ring Q.ResidueField x) = h x) ∧
          ∀ i, a i ∈ ℓ.fieldRange := by
  let k := p.ResidueField
  let Ω := SeparableClosure k
  let E := IntermediateField.adjoin k (Set.range a)
  letI : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  letI : Algebra.IsSeparable k E := by infer_instance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k E
  let L := Localization.AtPrime p
  let m : k[X] := minpoly k α
  have hm : m.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  have hm_lifts : m ∈ Polynomial.lifts (IsLocalRing.residue L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i ↦ Set.mem_range.mpr (IsLocalRing.residue_surjective (m.coeff i))
  obtain ⟨q, hq, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hm_lifts hm
  let d : p.primeCompl := IsLocalization.commonDenom p.primeCompl q.support q.coeff
  have hqscale_lifts :
      q.scaleRoots (algebraMap A L d.1) ∈ Polynomial.lifts (algebraMap A L) := by
    apply IsLocalization.scaleRoots_commonDenom_mem_lifts p.primeCompl q
    rw [hqmonic.leadingCoeff]
    exact ⟨1, map_one _⟩
  obtain ⟨f, hf, -, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hqscale_lifts
      ((Polynomial.monic_scaleRoots_iff _).mpr hqmonic)
  let P : StandardEtalePair A :=
    ⟨f, hfmonic, f.derivative, 1, 0, 1, by simp⟩
  letI : IsScalarTower A k Ω := IsScalarTower.of_algebraMap_eq' rfl
  let δ : k := IsLocalRing.residue L (algebraMap A L d.1)
  let β : Ω := algebraMap k Ω δ * (α : Ω)
  have hmroot : Polynomial.eval₂ (algebraMap k Ω) (α : Ω) m = 0 := by
    rw [← Polynomial.aeval_def]
    change aeval (α : Ω) (minpoly k α) = 0
    have hcoe : (α : Ω) = E.val α := rfl
    rw [hcoe]
    calc
      _ = E.val (aeval α (minpoly k α)) := by
        exact Polynomial.aeval_algHom_apply E.val α (minpoly k α)
      _ = 0 := by rw [minpoly.aeval, map_zero]
  have hf_k : f.map (algebraMap A k) = m.scaleRoots δ := by
    calc
      f.map (algebraMap A k) =
          (f.map (algebraMap A L)).map (IsLocalRing.residue L) := by
            rw [Polynomial.map_map]
            congr 2
      _ = (q.scaleRoots (algebraMap A L d.1)).map (IsLocalRing.residue L) := by rw [hf]
      _ = (q.map (IsLocalRing.residue L)).scaleRoots δ := by
        apply Polynomial.map_scaleRoots
        rw [hqmonic.leadingCoeff, map_one]
        exact one_ne_zero
      _ = m.scaleRoots δ := by rw [hq]
  have hroot : aeval β f = 0 := by
    rw [← Polynomial.eval_map_algebraMap f β,
      IsScalarTower.algebraMap_eq A k Ω, ← Polynomial.map_map,
      hf_k, Polynomial.map_scaleRoots]
    · dsimp [β]
      rw [Polynomial.scaleRoots_eval_mul]
      exact mul_eq_zero_of_right _ (by simpa [Polynomial.eval_map] using hmroot)
    · rw [hm.leadingCoeff, map_one]
      exact one_ne_zero
  have hderiv : aeval β f.derivative ≠ 0 := by
    let F : Polynomial Ω := f.map (algebraMap A Ω)
    let M : Polynomial Ω := m.map (algebraMap k Ω)
    let e : Ω := algebraMap k Ω δ
    have hF : F = M.scaleRoots e := by
      dsimp [F, M, e]
      rw [IsScalarTower.algebraMap_eq A k Ω, ← Polynomial.map_map, hf_k,
        Polynomial.map_scaleRoots]
      rw [hm.leadingCoeff, map_one]
      exact one_ne_zero
    have hδ : δ ≠ 0 := by
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr
        (IsLocalization.map_units L d)
    have he : e ≠ 0 := by
      simpa [e] using (algebraMap k Ω).injective.ne hδ
    have hmsep : m.Separable := Algebra.IsSeparable.isSeparable k α
    have hMsep : M.Separable := hmsep.map
    have hMroot : M.IsRoot (α : Ω) := by
      simpa [Polynomial.IsRoot.def, M, Polynomial.eval_map] using hmroot
    have hMmult : M.rootMultiplicity (α : Ω) = 1 := by
      apply le_antisymm (Polynomial.rootMultiplicity_le_one_of_separable hMsep _)
      exact (Nat.succ_le_iff.mpr ((Polynomial.rootMultiplicity_pos hMsep.ne_zero).mpr hMroot))
    have hFmult : F.rootMultiplicity β = 1 := by
      rw [hF]
      change (M.scaleRoots e).rootMultiplicity (e * (α : Ω)) = 1
      rw [Polynomial.rootMultiplicity_scaleRoots M
        (isUnit_iff_ne_zero.mpr he).isRegular.left, hMmult]
    intro hzero
    have hFroot : F.IsRoot β := by
      rw [Polynomial.IsRoot.def]
      dsimp [F]
      rw [Polynomial.eval_map_algebraMap]
      exact hroot
    have hFderiv : F.derivative.IsRoot β := by
      rw [Polynomial.IsRoot.def]
      dsimp [F]
      rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
      exact hzero
    have hFne : F ≠ 0 := by
      rw [hF]
      exact M.scaleRoots_ne_zero hMsep.ne_zero e
    have := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hFne).mpr ⟨hFroot, hFderiv⟩
    omega
  have hP : P.HasMap β := ⟨hroot, isUnit_iff_ne_zero.mpr hderiv⟩
  let h : P.Ring →ₐ[A] Ω := P.lift β hP
  let Q : Ideal P.Ring := RingHom.ker h.toRingHom
  letI : Q.IsPrime := by
    dsimp [Q]
    exact RingHom.ker_isPrime h.toRingHom
  let hker : Q ≤ RingHom.ker h.toRingHom := by rfl
  let hunit : Q.primeCompl ≤ (IsUnit.submonoid Ω).comap h.toRingHom :=
    fun x hx ↦ isUnit_iff_ne_zero.mpr (by simpa [Q, RingHom.mem_ker] using hx)
  let ℓ : Q.ResidueField →+* Ω :=
    Ideal.ResidueField.lift Q h.toRingHom hker hunit
  have hcontraction : p = Q.comap (algebraMap A P.Ring) := by
    ext x
    change x ∈ p ↔ h (algebraMap A P.Ring x) = 0
    rw [h.commutes]
    simp [IsScalarTower.algebraMap_apply A k Ω]
    exact Ideal.algebraMap_residueField_eq_zero.symm
  refine ⟨P, h, Q, inferInstance, ℓ, rfl, hcontraction, ?_, ?_⟩
  · intro x
    exact Ideal.ResidueField.lift_algebraMap Q h.toRingHom hker hunit x
  · intro i
    let φ : k →+* Q.ResidueField :=
      Ideal.ResidueField.map p Q (algebraMap A P.Ring) hcontraction
    letI : Algebra k Q.ResidueField := φ.toAlgebra
    have hℓφ : ℓ.comp φ = algebraMap k Ω := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp only [RingHom.comp_apply]
      rw [show φ (algebraMap A k x) =
          algebraMap P.Ring Q.ResidueField (algebraMap A P.Ring x) by
        exact Ideal.ResidueField.map_algebraMap p Q (algebraMap A P.Ring) hcontraction x]
      rw [show ℓ (algebraMap P.Ring Q.ResidueField (algebraMap A P.Ring x)) =
          h (algebraMap A P.Ring x) from
        Ideal.ResidueField.lift_algebraMap Q h.toRingHom hker hunit _]
      rw [h.commutes, IsScalarTower.algebraMap_apply A k Ω]
    let ℓk : Q.ResidueField →ₐ[k] Ω :=
      { __ := ℓ
        commutes' := fun x ↦ DFunLike.congr_fun hℓφ x }
    have hβrange : β ∈ ℓk.fieldRange := by
      rw [AlgHom.mem_fieldRange]
      refine ⟨algebraMap P.Ring Q.ResidueField P.X, ?_⟩
      change ℓ (algebraMap P.Ring Q.ResidueField P.X) = β
      calc
        _ = h P.X := Ideal.ResidueField.lift_algebraMap Q h.toRingHom hker hunit P.X
        _ = β := P.lift_X β hP
    have herange : algebraMap k Ω δ ∈ ℓk.fieldRange :=
      ℓk.fieldRange.algebraMap_mem δ
    have hαrange : (α : Ω) ∈ ℓk.fieldRange := by
      have hδ' : δ ≠ 0 := by
        exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr
          (IsLocalization.map_units L d)
      have heq : (algebraMap k Ω δ)⁻¹ * β = (α : Ω) := by
        dsimp [β]
        rw [← mul_assoc, inv_mul_cancel₀ (by
          simpa using (algebraMap k Ω).injective.ne hδ'), one_mul]
      rw [← heq]
      exact ℓk.fieldRange.mul_mem (ℓk.fieldRange.inv_mem herange) hβrange
    have hE : E ≤ ℓk.fieldRange := by
      calc
        (E : IntermediateField k Ω) = E.val.fieldRange :=
          (IntermediateField.fieldRange_val E).symm
        _ = (IntermediateField.adjoin k {α}).map E.val := by
          rw [AlgHom.fieldRange_eq_map, hα]
        _ = IntermediateField.adjoin k {(α : Ω)} := by
          rw [IntermediateField.adjoin_map]
          rw [Set.image_singleton]
          congr 2
        _ ≤ ℓk.fieldRange :=
          IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαrange)
    have haiE : a i ∈ E := by
      dsimp [E]
      exact (IntermediateField.subset_adjoin k (Set.range a)) (Set.mem_range_self i)
    have hai : a i ∈ ℓk.fieldRange := hE haiE
    rw [RingHom.mem_fieldRange]
    rw [AlgHom.mem_fieldRange] at hai
    exact hai

/-- A finite family in the residue field at a prime lifts after localizing away from a single
element outside that prime.

Besides the lifts, the result returns the induced residue-field map and its kernel prime; this
makes the statement directly usable to construct a point of the principal open. -/
lemma exists_away_lifting_residueField
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    {n : Type v} [Finite n] (a : n → q.ResidueField) :
    ∃ (t : R) (_ : t ∉ q) (b : n → Localization.Away t)
      (g : Localization.Away t →+* q.ResidueField)
      (Q : Ideal (Localization.Away t)) (_ : Q.IsPrime),
      Q = RingHom.ker g ∧ q = Q.comap (algebraMap R (Localization.Away t)) ∧
        (∀ x, g (algebraMap R (Localization.Away t) x) =
          algebraMap R q.ResidueField x) ∧ ∀ i, g (b i) = a i := by
  letI := Fintype.ofFinite n
  choose z hz using fun i ↦ IsLocalRing.residue_surjective (R := Localization.AtPrime q) (a i)
  let d : q.primeCompl :=
    IsLocalization.commonDenom q.primeCompl Finset.univ z
  let r : n → R := fun i ↦
    IsLocalization.integerMultiple q.primeCompl Finset.univ z ⟨i, Finset.mem_univ i⟩
  have hdr (i : n) : algebraMap R (Localization.AtPrime q) (r i) =
      algebraMap R (Localization.AtPrime q) d.1 * z i := by
    dsimp [r, d]
    rw [IsLocalization.map_integerMultiple, Submonoid.smul_def, Algebra.smul_def]
  have hdt : d.1 ∉ q := d.2
  have hdunit : IsUnit (algebraMap R q.ResidueField d.1) :=
    isUnit_iff_ne_zero.mpr (Ideal.algebraMap_residueField_eq_zero.not.mpr hdt)
  let g : Localization.Away d.1 →+* q.ResidueField :=
    IsLocalization.Away.lift d.1 hdunit
  let den : Submonoid.powers d.1 := ⟨d.1, Submonoid.mem_powers d.1⟩
  let b : n → Localization.Away d.1 := fun i ↦
    IsLocalization.mk' (Localization.Away d.1) (r i) den
  have hgb (i : n) : g (b i) = a i := by
    dsimp [g, b, den, IsLocalization.Away.lift]
    rw [IsLocalization.lift_mk'_spec]
    change IsLocalRing.residue (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime q) (r i)) =
      IsLocalRing.residue (Localization.AtPrime q)
          (algebraMap R (Localization.AtPrime q) d.1) * a i
    rw [hdr, map_mul, hz]
  let Q : Ideal (Localization.Away d.1) := RingHom.ker g
  letI : Q.IsPrime := by dsimp [Q]; exact RingHom.ker_isPrime g
  refine ⟨d.1, hdt, b, g, Q, inferInstance, rfl, ?_, ?_, hgb⟩
  · ext x
    change x ∈ q ↔ g (algebraMap R (Localization.Away d.1) x) = 0
    dsimp [g]
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.algebraMap_residueField_eq_zero.symm
  · intro x
    dsimp [g]
    rw [IsLocalization.Away.lift_eq]

/-- A nonempty smooth scheme over a separably closed field has a rational point, expressed as a
section of its structure morphism. -/
lemma exists_section_of_smooth_toSpec_of_isSepClosed
    {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [Nonempty X] :
    ∃ s : Spec (.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hxU : f x ∈ U := e hxV
  have hUtop : U = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext y
    constructor
    · intro _
      trivial
    · intro _
      rw [Subsingleton.elim y (f x)]
      exact hxU
  subst U
  obtain ⟨n, g, hg, hg'⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hf
  let A := Γ(Spec (.of K), ⊤)
  let B := Γ(X, V)
  let e' : Spec (.of B) ⟶ Spec (.of (MvPolynomial (Fin n) A)) :=
    Spec.map (CommRingCat.ofHom g)
  letI : RingHom.Etale g := hg'
  letI : Etale e' := by
    dsimp [e']
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg'
  let eK : A ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI : Field A :=
    (eK.toMulEquiv.isField (Field.toIsField K)).toField
  letI : IsSepClosed A := isSepClosed_of_ringEquiv eK
  have hopen : IsOpen (Set.range e') := e'.isOpenMap.isOpen_range
  have hne : (Set.range e').Nonempty := by
    have hxr : x ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact hxV
    obtain ⟨x', -⟩ := hxr
    exact ⟨e' x', x', rfl⟩
  obtain ⟨r, hr⟩ :=
    exists_rationalPoint_mem_open_affineSpace_of_isSepClosed A
      (n := Fin n) (U := Set.range e') hopen hne
  let q : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin n) A)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval r))
  have hqapply : q default = PrimeSpectrum.comap (MvPolynomial.eval r) default := by
    dsimp only [q, Spec.map_apply, CommRingCat.hom_ofHom]
    exact congrArg (PrimeSpectrum.comap (MvPolynomial.eval r))
      (Subsingleton.elim _ _)
  rw [← hqapply] at hr
  obtain ⟨x', hx'⟩ := hr
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e' q x' hx'
  let i : Spec (.of K) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom eK.toRingHom)
  refine ⟨i ≫ l ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
  have happ : Spec.map (f.appLE ⊤ V e) =
      e' ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    dsimp [e']
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, CommRingCat.ofHom_hom]
  rw [happ, Category.assoc e', ← Category.assoc l e', hl]
  have hq : q ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _ := by
    dsimp [q]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_comp_C,
      CommRingCat.ofHom_id, Spec.map_id]
  rw [← Category.assoc q, hq, Category.id_comp]
  dsimp [i, eK]
  rw [Iso.commRingCatIsoToRingEquiv_toRingHom, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp, CommRingCat.ofHom_hom,
    Iso.inv_hom_id, Spec.map_id]

/-- Given a smooth morphism to an affine scheme and a target point in its image, construct an
étale neighborhood of that point equipped with a lift to the source. -/
lemma exists_etaleNeighborhood_of_smooth_toSpec
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Smooth f] (y : Spec (.of A))
    (hy : y ∈ Set.range f) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ Spec (.of A)) (_ : Etale p)
      (_ : y ∈ Set.range p) (s : Y' ⟶ X), s ≫ f = p := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hyU : y ∈ U := by
    rw [← hx]
    exact e hxV
  have hyrange : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hyU
  obtain ⟨p₀, hp₀⟩ := hyrange
  let A₀ := Γ(Spec (.of A), U)
  letI : p₀.asIdeal.IsPrime := p₀.isPrime
  let Ω := SeparableClosure p₀.asIdeal.ResidueField
  let φ : A₀ →+* Ω :=
    (algebraMap p₀.asIdeal.ResidueField Ω).comp
      (algebraMap A₀ p₀.asIdeal.ResidueField)
  let yΩ : Spec (.of Ω) ⟶ Spec (.of A₀) := Spec.map (CommRingCat.ofHom φ)
  have hyΩp₀ : yΩ default = p₀ := by
    have hyΩapply : yΩ default = PrimeSpectrum.comap φ default := by
      dsimp only [yΩ, Spec.map_apply, CommRingCat.hom_ofHom]
      exact congrArg (PrimeSpectrum.comap φ) (Subsingleton.elim _ _)
    rw [hyΩapply]
    apply PrimeSpectrum.ext
    ext a
    change φ a ∈ (default : PrimeSpectrum Ω).asIdeal ↔ a ∈ p₀.asIdeal
    rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum Ω).asIdeal]
    simp only [Ideal.mem_bot]
    simpa [φ] using (Ideal.algebraMap_residueField_eq_zero (I := p₀.asIdeal) (x := a))
  let yΩY : Spec (.of Ω) ⟶ Spec (.of A) := yΩ ≫ hU.fromSpec
  have hyΩY : yΩY default = y := by
    change (yΩ ≫ hU.fromSpec) default = y
    rw [Scheme.Hom.comp_apply, hyΩp₀]
    exact hp₀
  let b : Spec Γ(X, V) ⟶ Spec (.of A₀) := Spec.map (f.appLE U V e)
  have hb_smooth : Smooth b := by
    dsimp [b]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hf.smooth
  letI : Smooth b := hb_smooth
  have hxrange : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hxV
  obtain ⟨x₀, hx₀⟩ := hxrange
  have hbx₀ : b x₀ = p₀ := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e,
      Scheme.Hom.comp_apply, hx₀, hx, hp₀]
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback x₀ default (hbx₀.trans hyΩp₀.symm)
  letI : Nonempty (↑(pullback b yΩ : Scheme)) := ⟨z⟩
  obtain ⟨sec, hsec⟩ :=
    exists_section_of_smooth_toSpec_of_isSepClosed (pullback.snd b yΩ)
  let zB : Spec (.of Ω) ⟶ Spec Γ(X, V) := sec ≫ pullback.fst b yΩ
  have hzB : zB ≫ b = yΩ := by
    dsimp [zB]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsec,
      Category.id_comp]
  let B := Γ(X, V)
  let h : B →+* Ω := (Spec.preimage zB).hom
  have hzBmap : Spec.map (CommRingCat.ofHom h) = zB := by
    dsimp [h]
    exact Spec.map_preimage zB
  have hbase : h.comp (f.appLE U V e).hom = φ := by
    have hcat : f.appLE U V e ≫ CommRingCat.ofHom h = CommRingCat.ofHom φ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hzBmap]
      simpa only [b, yΩ] using hzB
    exact congrArg CommRingCat.Hom.hom hcat
  obtain ⟨n, g, hg, hgEtale⟩ :=
    RingHom.IsStandardSmooth.exists_etale_mvPolynomial hf
  let a : Fin n → Ω := fun i ↦ h (g (MvPolynomial.X i))
  have hφ : algebraMap A₀ Ω = φ := by
    ext r
    simp [φ, IsScalarTower.algebraMap_apply A₀ p₀.asIdeal.ResidueField Ω]
  obtain ⟨P, hC, Q, hQprime, ℓ, hQker, hQcon, hℓC, ha⟩ :=
    exists_standardEtalePair_spreading_finite_family p₀.asIdeal a
  choose c hc using fun i ↦ (RingHom.mem_fieldRange.mp (ha i))
  obtain ⟨t, htQ, d, gd, QD, hQDprime, hQDker, hQDcon, hgdC, hgdd⟩ :=
    exists_away_lifting_residueField Q c
  let D := Localization.Away t
  let ψ : MvPolynomial (Fin n) A₀ →+* D :=
    MvPolynomial.eval₂Hom (algebraMap A₀ D) d
  have hψ : ℓ.comp (gd.comp ψ) = h.comp g := by
    apply MvPolynomial.ringHom_ext
    · intro r
      dsimp [ψ]
      rw [MvPolynomial.eval₂_C]
      change ℓ (gd (algebraMap A₀ D r)) = h (g (MvPolynomial.C r))
      rw [IsScalarTower.algebraMap_apply A₀ P.Ring D, hgdC, hℓC, hC.commutes]
      rw [DFunLike.congr_fun hφ r]
      change φ r = h (g (MvPolynomial.C r))
      calc
        φ r = (h.comp (f.appLE U V e).hom) r := (DFunLike.congr_fun hbase r).symm
        _ = h ((f.appLE U V e).hom r) := rfl
        _ = h ((g.comp MvPolynomial.C) r) :=
          congrArg h (DFunLike.congr_fun hg r).symm
        _ = h (g (MvPolynomial.C r)) := rfl
    · intro i
      dsimp [ψ]
      rw [MvPolynomial.eval₂_X]
      change ℓ (gd (d i)) = h (g (MvPolynomial.X i))
      rw [hgdd, hc]
  let qB : PrimeSpectrum B := ⟨RingHom.ker h, RingHom.ker_isPrime h⟩
  let qD : PrimeSpectrum D := ⟨QD, hQDprime⟩
  let eG : Spec (.of B) ⟶ Spec (.of (MvPolynomial (Fin n) A₀)) :=
    Spec.map (CommRingCat.ofHom g)
  let uD : Spec (.of D) ⟶ Spec (.of (MvPolynomial (Fin n) A₀)) :=
    Spec.map (CommRingCat.ofHom ψ)
  letI : Etale eG := by
    dsimp [eG]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hgEtale
  have heqPoint : eG qB = uD qD := by
    apply PrimeSpectrum.ext
    ext F
    change h (g F) = 0 ↔ ψ F ∈ QD
    rw [hQDker, RingHom.mem_ker]
    have hF := DFunLike.congr_fun hψ F
    change ℓ (gd (ψ F)) = h (g F) at hF
    constructor
    · intro hzero
      apply ℓ.injective
      rw [map_zero, hF, hzero]
    · intro hzero
      rw [← hF, hzero, map_zero]
  obtain ⟨w, hwfst, hwsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := eG) (g := uD) qB qD heqPoint
  let rD : Spec (.of D) ⟶ Spec (.of A₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ D))
  letI : Etale rD := by
    dsimp [rD]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A₀ D))
  have hrDpoint : rD qD = p₀ := by
    apply PrimeSpectrum.ext
    ext r
    change algebraMap A₀ D r ∈ QD ↔ r ∈ p₀.asIdeal
    rw [IsScalarTower.algebraMap_apply A₀ P.Ring D,
      ← Ideal.mem_comap, ← hQDcon, ← Ideal.mem_comap, ← hQcon]
  have heGb : eG ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = b := by
    dsimp [eG, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg,
      CommRingCat.ofHom_hom]
  have huDrD : uD ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = rD := by
    dsimp [uD, rD, ψ]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      MvPolynomial.eval₂Hom_comp_C]
  let p : pullback eG uD ⟶ Spec (.of A) :=
    pullback.snd eG uD ≫ rD ≫ hU.fromSpec
  let s : pullback eG uD ⟶ X := pullback.fst eG uD ≫ hV.fromSpec
  refine ⟨pullback eG uD, p, inferInstance, ?_, s, ?_⟩
  · refine ⟨w, ?_⟩
    dsimp [p]
    change hU.fromSpec (rD (pullback.snd eG uD w)) = y
    rw [hwsnd, hrDpoint, hp₀]
  · dsimp [s, p]
    simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    change pullback.fst eG uD ≫ b ≫ hU.fromSpec =
      pullback.snd eG uD ≫ rD ≫ hU.fromSpec
    rw [← heGb, ← huDrD]
    simp only [Category.assoc]
    rw [← Category.assoc (pullback.fst eG uD) eG, pullback.condition]
    simp only [Category.assoc]

end

end StacksProject
