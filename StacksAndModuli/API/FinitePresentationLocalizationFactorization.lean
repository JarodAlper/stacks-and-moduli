module

public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Factoring finitely presented algebras through a finite localization stage

Let `A` be an `R`-algebra and `p ⊆ A` a prime ideal.  A map from a finitely presented
`R`-algebra `C` to `Aₚ` involves only finitely many numerators and denominators.  After
adjoining them to any prescribed finitely generated `R`-subalgebra `B₀ ⊆ A`, the
relations of a finite presentation may still vanish only after mapping to `Aₚ`.  Adjoining
one further denominator for every relation makes them vanish already in the localization of
the enlarged coefficient ring.

The main theorem packages this denominator-clearing argument as an exact factorization
through `Bₚ`.  It is useful for spreading finite-presentation data from a local ring back to
a finite coefficient stage.

Main declarations:
- `Algebra.Presentation.liftOfRelations`: maps out of a presented algebra from images of its
  generators satisfying the chosen relations;
- `Algebra.FinitePresentation.exists_fg_subalgebra_lift_family_atPrime`: lift a finite
  family of fractions to a finite coefficient stage;
- `Algebra.FinitePresentation.exists_fg_subalgebra_killing_relations_atPrime`: enlarge a
  coefficient stage until finitely many relations vanish there;
- `Algebra.FinitePresentation.exists_fg_subalgebra_factorization_atPrime`: factorization of a
  finitely presented algebra map through the localization of a finite coefficient stage;
- `Algebra.FinitePresentation.exists_localized_source_lift_of_factorization_atPrime`: extend
  such a factorization after localizing its source at the closed-point contraction;
- `Algebra.FinitePresentation.exists_fg_subalgebra_over_factorization_atPrime`: the relative
  coefficient-subalgebra specialization, retaining exact linearity over the starting stage.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open MvPolynomial

universe u v w t

namespace Algebra.Presentation

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- A family of values which kills the distinguished relations of a presentation kills its
whole relation ideal. -/
theorem aeval_eq_zero_of_relations
    (P : Presentation R S ι σ)
    {T : Type*} [CommRing T] [Algebra R T]
    (x : ι → T)
    (h : ∀ j, aeval x (P.relation j) = 0)
    (p : P.Ring) (hp : p ∈ P.ker) :
    aeval x p = 0 := by
  rw [← RingHom.mem_ker]
  apply (Ideal.span_le.mpr (fun r hr ↦ ?_))
  · simpa only [← P.span_range_relation_eq_ker] using hp
  · obtain ⟨j, rfl⟩ := hr
    change aeval x (P.relation j) = 0
    exact h j

/-- Construct an algebra homomorphism out of a presented algebra by specifying values of
the generators which satisfy the distinguished relations. -/
noncomputable def liftOfRelations
    (P : Presentation R S ι σ)
    {T : Type*} [CommRing T] [Algebra R T]
    (x : ι → T)
    (h : ∀ j, aeval x (P.relation j) = 0) :
    S →ₐ[R] T :=
  (Ideal.Quotient.liftₐ P.ker (aeval x)
    (P.aeval_eq_zero_of_relations x h)).comp
      (P.quotientEquiv.restrictScalars R).symm.toAlgHom

@[simp]
theorem liftOfRelations_val
    (P : Presentation R S ι σ)
    {T : Type*} [CommRing T] [Algebra R T]
    (x : ι → T)
    (h : ∀ j, aeval x (P.relation j) = 0)
    (i : ι) :
    P.liftOfRelations x h (P.val i) = x i := by
  have hv : P.val i = P.quotientEquiv (Ideal.Quotient.mk P.ker (X i)) := by
    rw [P.quotientEquiv_mk, P.algebraMap_apply, aeval_X]
  rw [hv]
  unfold liftOfRelations
  rw [AlgHom.comp_apply]
  change Ideal.Quotient.liftₐ P.ker (aeval x) _
      ((P.quotientEquiv.restrictScalars R).symm
        ((P.quotientEquiv.restrictScalars R)
          (Ideal.Quotient.mk P.ker (X i)))) = x i
  rw [AlgEquiv.symm_apply_apply]
  change ((Ideal.Quotient.liftₐ P.ker (aeval x)
      (P.aeval_eq_zero_of_relations x h)).comp
        (Ideal.Quotient.mkₐ R P.ker)) (X i) = x i
  rw [Ideal.Quotient.liftₐ_comp, aeval_X]

end Algebra.Presentation

namespace Algebra.FinitePresentation

variable {R : Type u} {A : Type v} {C : Type w}
variable [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C]

/-- A finite family of elements of `Aₚ` is defined over the localization of a finitely
generated coefficient subalgebra.  The coefficient subalgebra may be required to contain a
prescribed finite starting stage. -/
theorem exists_fg_subalgebra_lift_family_atPrime
    (p : Ideal A) [p.IsPrime]
    (B₀ : Subalgebra R A) (hB₀ : B₀.FG)
    {ι : Type t} [Finite ι]
    (z : ι → Localization.AtPrime p) :
    ∃ (B : Subalgebra R A) (_hB : B.FG) (_hB₀B : B₀ ≤ B)
      (x : ι → Localization.AtPrime (p.comap B.val)),
      ∀ i, Localization.localAlgHom (p.comap B.val) p B.val rfl (x i) = z i := by
  classical
  letI := Fintype.ofFinite ι
  choose rep rep_spec using fun i : ι ↦ IsLocalization.surj p.primeCompl (z i)
  let num (i : ι) : A := (rep i).1
  let den (i : ι) : p.primeCompl := (rep i).2
  let coeffs : Finset A :=
    (Finset.univ.image num) ∪ (Finset.univ.image fun i ↦ (den i : A))
  let B : Subalgebra R A := B₀ ⊔ Algebra.adjoin R (coeffs : Set A)
  have hB : B.FG := hB₀.sup (Subalgebra.fg_adjoin_finset coeffs)
  have hB₀B : B₀ ≤ B := le_sup_left
  have num_mem (i : ι) : num i ∈ B := by
    exact (show Algebra.adjoin R (coeffs : Set A) ≤ B from le_sup_right)
      (Algebra.subset_adjoin
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  have den_mem (i : ι) : (den i : A) ∈ B := by
    exact (show Algebra.adjoin R (coeffs : Set A) ≤ B from le_sup_right)
      (Algebra.subset_adjoin
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  let q : Ideal B := p.comap B.val
  let L := Localization.AtPrime q
  let numB (i : ι) : B := ⟨num i, num_mem i⟩
  let denB (i : ι) : q.primeCompl := ⟨⟨den i, den_mem i⟩, (den i).2⟩
  let x (i : ι) : L := IsLocalization.mk' L (numB i) (denB i)
  refine ⟨B, hB, hB₀B, x, fun i ↦ ?_⟩
  have hmap : Localization.localAlgHom q p B.val rfl (x i) =
      IsLocalization.mk' (Localization.AtPrime p) (num i) (den i) := by
    change (Localization.localRingHom q p B.val rfl)
        (IsLocalization.mk' L (numB i) (denB i)) = _
    rw [Localization.localRingHom_mk']
    rfl
  rw [hmap]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  exact (rep_spec i).symm

/-- Enlarge a finite coefficient subalgebra until a finite family of polynomial relations
which vanishes in `Aₚ` already vanishes at the coefficient localization. -/
theorem exists_fg_subalgebra_killing_relations_atPrime
    (p : Ideal A) [p.IsPrime]
    (B₁ : Subalgebra R A) (hB₁ : B₁.FG)
    {ι σ : Type t} [Finite σ]
    (x₁ : ι → Localization.AtPrime (p.comap B₁.val))
    (relation : σ → MvPolynomial ι R)
    (hzero : ∀ j,
      Localization.localAlgHom (p.comap B₁.val) p B₁.val rfl
        (aeval x₁ (relation j)) = 0) :
    ∃ (B : Subalgebra R A) (_hB : B.FG) (_hB₁B : B₁ ≤ B)
      (x : ι → Localization.AtPrime (p.comap B.val)),
      (∀ i, Localization.localAlgHom (p.comap B.val) p B.val rfl (x i) =
        Localization.localAlgHom (p.comap B₁.val) p B₁.val rfl (x₁ i)) ∧
      ∀ j, aeval x (relation j) = 0 := by
  classical
  letI := Fintype.ofFinite σ
  let q₁ : Ideal B₁ := p.comap B₁.val
  let L₁ := Localization.AtPrime q₁
  let φ₁ : L₁ →ₐ[R] Localization.AtPrime p :=
    Localization.localAlgHom q₁ p B₁.val rfl
  let relVal (j : σ) : L₁ := aeval x₁ (relation j)
  choose relNum relDen relRep_spec using
    fun j : σ ↦ IsLocalization.exists_mk'_eq (M := q₁.primeCompl) (relVal j)
  have hrelNum_map (j : σ) :
      algebraMap A (Localization.AtPrime p) ((relNum j : B₁) : A) = 0 := by
    have h := congrArg φ₁ (relRep_spec j)
    rw [hzero j] at h
    change (Localization.localRingHom q₁ p B₁.val rfl)
        (IsLocalization.mk' L₁ (relNum j) (relDen j)) = 0 at h
    rw [Localization.localRingHom_mk'] at h
    rw [IsLocalization.mk'_eq_zero_iff] at h
    exact (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) _).mpr h
  choose relKill relKill_spec using fun j : σ ↦
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p)
      (((relNum j : B₁) : A))).mp (hrelNum_map j)
  let relationDenominators : Finset A :=
    Finset.univ.image fun j ↦ (relKill j : A)
  let B : Subalgebra R A := B₁ ⊔ Algebra.adjoin R (relationDenominators : Set A)
  have hB : B.FG := hB₁.sup (Subalgebra.fg_adjoin_finset relationDenominators)
  have hB₁B : B₁ ≤ B := le_sup_left
  let q : Ideal B := p.comap B.val
  let L := Localization.AtPrime q
  let inc₁ : B₁ →ₐ[R] B := Subalgebra.inclusion hB₁B
  have hq₁q : q₁ = q.comap inc₁ := by
    ext z
    rfl
  let ψ : L₁ →ₐ[R] L := Localization.localAlgHom q₁ q inc₁ hq₁q
  let φ : L →ₐ[R] Localization.AtPrime p := Localization.localAlgHom q p B.val rfl
  let x (i : ι) : L := ψ (x₁ i)
  have relKill_mem (j : σ) : (relKill j : A) ∈ B := by
    exact (show Algebra.adjoin R (relationDenominators : Set A) ≤ B from le_sup_right)
      (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  have hψrelVal (j : σ) : ψ (relVal j) = 0 := by
    rw [← relRep_spec j]
    have hmap : ψ (IsLocalization.mk' L₁ (relNum j) (relDen j)) =
        IsLocalization.mk' L
          (⟨((relNum j : B₁) : A), hB₁B (relNum j).2⟩ : B)
          (⟨⟨((relDen j : q₁.primeCompl).1 : B₁),
              hB₁B (relDen j).1.2⟩,
            (relDen j).2⟩ : q.primeCompl) := by
      change (Localization.localRingHom q₁ q inc₁ hq₁q)
          (IsLocalization.mk' L₁ (relNum j) (relDen j)) = _
      rw [Localization.localRingHom_mk']
      rfl
    rw [hmap, IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨⟨relKill j, relKill_mem j⟩, (relKill j).2⟩, ?_⟩
    apply Subtype.ext
    exact relKill_spec j
  have hφψ (z : L₁) : φ (ψ z) = φ₁ z := by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := q₁.primeCompl) z
    change (Localization.localRingHom q p B.val rfl)
        ((Localization.localRingHom q₁ q inc₁ hq₁q)
          (IsLocalization.mk' L₁ a s)) =
        (Localization.localRingHom q₁ p B₁.val rfl) (IsLocalization.mk' L₁ a s)
    rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
      Localization.localRingHom_mk']
    rfl
  have hrelations (j : σ) : aeval x (relation j) = 0 := by
    rw [← hψrelVal j]
    change aeval (fun i ↦ ψ (x₁ i)) (relation j) =
      ψ (aeval x₁ (relation j))
    exact (MvPolynomial.comp_aeval_apply x₁ ψ (relation j)).symm
  exact ⟨B, hB, hB₁B, x, ⟨fun i ↦ hφψ (x₁ i), hrelations⟩⟩

/-- A map from a finitely presented `R`-algebra to the localization `Aₚ` factors through
the localization of a finitely generated `R`-subalgebra of `A`.  The finite subalgebra may
be required to contain any prescribed finitely generated starting subalgebra.

Besides lifting the finitely many generator fractions, the proof clears one annihilating
denominator for each relation.  This last step is necessary because the natural map from a
smaller coefficient localization to `Aₚ` need not be injective. -/
theorem exists_fg_subalgebra_factorization_atPrime
    [Algebra.FinitePresentation R C]
    (p : Ideal A) [p.IsPrime]
    (B₀ : Subalgebra R A) (hB₀ : B₀.FG)
    (g : C →ₐ[R] Localization.AtPrime p) :
    ∃ (B : Subalgebra R A) (_hB : B.FG) (_hB₀B : B₀ ≤ B)
      (f : C →ₐ[R] Localization.AtPrime (p.comap B.val)),
      (Localization.localAlgHom (p.comap B.val) p B.val rfl).comp f = g := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R C
  obtain ⟨B₁, hB₁, hB₀B₁, x₁, hx₁⟩ :=
    exists_fg_subalgebra_lift_family_atPrime p B₀ hB₀ (fun i ↦ g (P.val i))
  have hzero (j : Fin (Algebra.Presentation.ofFinitePresentationRels R C)) :
      Localization.localAlgHom (p.comap B₁.val) p B₁.val rfl
        (aeval x₁ (P.relation j)) = 0 := by
    calc
      Localization.localAlgHom (p.comap B₁.val) p B₁.val rfl
          (aeval x₁ (P.relation j)) =
          aeval (fun i ↦ Localization.localAlgHom
            (p.comap B₁.val) p B₁.val rfl (x₁ i)) (P.relation j) := by
        exact MvPolynomial.comp_aeval_apply x₁
          (Localization.localAlgHom (p.comap B₁.val) p B₁.val rfl) (P.relation j)
      _ = aeval (fun i ↦ g (P.val i)) (P.relation j) := by
        rw [show (fun i ↦ Localization.localAlgHom
          (p.comap B₁.val) p B₁.val rfl (x₁ i)) =
          (fun i ↦ g (P.val i)) from funext hx₁]
      _ = g (aeval P.val (P.relation j)) := by
        exact (MvPolynomial.comp_aeval_apply P.val g (P.relation j)).symm
      _ = 0 := by rw [P.aeval_val_relation, map_zero]
  obtain ⟨B, hB, hB₁B, x, hx, hrelations⟩ :=
    exists_fg_subalgebra_killing_relations_atPrime p B₁ hB₁ x₁ P.relation hzero
  have hB₀B : B₀ ≤ B := hB₀B₁.trans hB₁B
  let f : C →ₐ[R] Localization.AtPrime (p.comap B.val) :=
    P.liftOfRelations x hrelations
  refine ⟨B, hB, hB₀B, f, ?_⟩
  apply AlgHom.ext
  intro c
  rw [← P.aeval_val_σ c]
  calc
    (((Localization.localAlgHom (p.comap B.val) p B.val rfl).comp f)
        (aeval P.val (P.σ c))) =
        aeval (fun i ↦ Localization.localAlgHom (p.comap B.val) p B.val rfl
          (f (P.val i))) (P.σ c) := by
      exact MvPolynomial.comp_aeval_apply P.val
        ((Localization.localAlgHom (p.comap B.val) p B.val rfl).comp f) (P.σ c)
    _ = aeval (fun i ↦ g (P.val i)) (P.σ c) := by
      rw [show (fun i ↦ Localization.localAlgHom (p.comap B.val) p B.val rfl
          (f (P.val i))) = (fun i ↦ g (P.val i)) from funext fun i ↦ by
        change Localization.localAlgHom (p.comap B.val) p B.val rfl
          (P.liftOfRelations x hrelations (P.val i)) = g (P.val i)
        rw [Algebra.Presentation.liftOfRelations_val]
        exact (hx i).trans (hx₁ i)]
    _ = g (aeval P.val (P.σ c)) := by
      exact (MvPolynomial.comp_aeval_apply P.val g (P.σ c)).symm

/-- A factorization `C → Bₚ → Aₚ` extends across localization of `C` at the
contraction of the maximal ideal of `Aₚ`.

Indeed the canonical map `Bₚ → Aₚ` is local, so whenever the image of an element of
`C` is a unit in `Aₚ`, its image is already a unit in `Bₚ`.  This is the localized-source
form needed when `C` is the unlocalized finite coefficient algebra and its localization is
the local Noetherian coefficient ring. -/
theorem exists_localized_source_lift_of_factorization_atPrime
    (p : Ideal A) [p.IsPrime]
    (B : Subalgebra R A)
    (g : C →ₐ[R] Localization.AtPrime p)
    (f : C →ₐ[R] Localization.AtPrime (p.comap B.val))
    (hgf : (Localization.localAlgHom (p.comap B.val) p B.val rfl).comp f = g) :
    ∃ fₗ : Localization.AtPrime
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap g) →ₐ[R]
          Localization.AtPrime (p.comap B.val),
      ∀ c, fₗ (algebraMap C
        (Localization.AtPrime
          ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap g)) c) = f c := by
  let q : Ideal B := p.comap B.val
  let φ : Localization.AtPrime q →ₐ[R] Localization.AtPrime p :=
    Localization.localAlgHom q p B.val rfl
  letI : IsLocalHom φ.toRingHom := by
    dsimp only [φ, Localization.localAlgHom]
    exact Localization.isLocalHom_localRingHom q p B.val rfl
  let r : Ideal C := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap g
  have hfUnits (y : r.primeCompl) : IsUnit (f y) := by
    have hgy : IsUnit (g y) := IsLocalRing.notMem_maximalIdeal.mp (by
      exact y.2)
    have heq : φ (f y) = g y := by
      exact congrArg (fun k : C →ₐ[R] Localization.AtPrime p ↦ k (y : C)) hgf
    rw [← heq] at hgy
    exact isUnit_of_map_unit φ.toRingHom (f y) hgy
  let fₗ : Localization.AtPrime r →ₐ[R] Localization.AtPrime q :=
    IsLocalization.liftAlgHom hfUnits
  refine ⟨fₗ, fun c ↦ ?_⟩
  exact IsLocalization.lift_eq hfUnits c

/-- Relative form of
`Algebra.FinitePresentation.exists_fg_subalgebra_factorization_atPrime` for a prescribed
coefficient subalgebra `B₀ ⊆ A`.

Here `C` is finitely presented over `B₀`, so the factor map is exactly `B₀`-linear.
The resulting `B₀`-subalgebra `D ⊆ A` is finite type over `B₀`; after restricting
scalars it is also a finitely generated `ℤ`-subalgebra containing `B₀`.  Thus
`D.restrictScalars ℤ` is a valid later coefficient stage, while retaining `D.val` gives
the canonical `B₀`-algebra map used in the factorization. -/
theorem exists_fg_subalgebra_over_factorization_atPrime
    (p : Ideal A) [p.IsPrime]
    (B₀ : Subalgebra ℤ A) (hB₀ : B₀.FG)
    [Algebra B₀ C] [Algebra.FinitePresentation B₀ C]
    (g : C →ₐ[B₀] Localization.AtPrime p) :
    ∃ (D : Subalgebra B₀ A), D.FG ∧ (D.restrictScalars ℤ).FG ∧
      B₀ ≤ D.restrictScalars ℤ ∧
      ∃ f : C →ₐ[B₀] Localization.AtPrime (p.comap D.val),
        ∀ c, Localization.localRingHom (p.comap D.val) p D.val.toRingHom rfl (f c) = g c := by
  let gr : C →+* Localization.AtPrime p := g.toRingHom
  have gr_commutes (b : B₀) :
      gr (algebraMap B₀ C b) =
        @algebraMap B₀ (Localization.AtPrime p) _ _ B₀.toAlgebra b :=
    g.commutes b
  letI : Algebra B₀ (Localization.AtPrime p) := OreLocalization.instAlgebra
  let g' : C →ₐ[B₀] Localization.AtPrime p :=
    { __ := gr
      commutes' b := gr_commutes b }
  obtain ⟨D, hD, _hbotD, f, hf⟩ :=
    exists_fg_subalgebra_factorization_atPrime
      (R := B₀) p (⊥ : Subalgebra B₀ A) Subalgebra.fg_bot g'
  have hB₀D : B₀ ≤ D.restrictScalars ℤ := by
    intro a ha
    have ha' : (algebraMap B₀ A ⟨a, ha⟩) ∈ D := D.algebraMap_mem ⟨a, ha⟩
    simpa [Subalgebra.mem_restrictScalars, Subalgebra.algebraMap_eq] using ha'
  have hDℤ : (D.restrictScalars ℤ).FG := by
    have hft : Algebra.FiniteType ℤ D :=
      Algebra.FiniteType.trans (R := ℤ) (S := B₀) (A := D)
        ((Subalgebra.fg_iff_finiteType B₀).mp hB₀)
        ((Subalgebra.fg_iff_finiteType D).mp hD)
    exact (Subalgebra.fg_iff_finiteType (D.restrictScalars ℤ)).mpr hft
  refine ⟨D, hD, hDℤ, hB₀D, f, fun c ↦ ?_⟩
  have hc := congrArg (fun k : C →ₐ[B₀] Localization.AtPrime p ↦ k c) hf
  change Localization.localRingHom (p.comap D.val) p D.val.toRingHom rfl (f c) = gr c at hc
  change Localization.localRingHom (p.comap D.val) p D.val.toRingHom rfl (f c) = gr c
  exact hc

end Algebra.FinitePresentation
