module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily

/-!
# Finite affine refinements of étale covers

An étale covering family of an affine scheme admits a finite affine refinement whose
members are still étale.  The proof uses openness of étale morphisms to obtain the
quasi-compact-cover structure, then Mathlib's affine refinement of quasi-compact covers.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- An étale covering presieve of an affine scheme is refined by a finite jointly
surjective family of affine schemes which are étale over the base. -/
theorem exists_finite_affine_refinement_of_mem_etalePrecoverage
    {S : Scheme.{u}} [IsAffine S] {R : Presieve S}
    (hR : R ∈ Scheme.etalePrecoverage S) :
    ∃ (n : ℕ) (X : Fin n → Scheme.{u}) (p : ∀ i, X i ⟶ S),
      (∀ i, IsAffine (X i)) ∧ (∀ i, Etale (p i)) ∧
        (∀ i, (Sieve.generate R).arrows (p i)) ∧
        Presieve.ofArrows X p ∈ Scheme.etalePrecoverage S := by
  classical
  change R ∈ Scheme.precoverage (@Etale) S at hR
  obtain ⟨𝒰, h𝒰eq⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (𝒰.f i).isOpenMap)
  obtain ⟨𝒱, φ, hfin, -⟩ := QuasiCompactCover.exists_hom (P := @Etale) 𝒰
  letI : Finite 𝒱.I₀ := hfin
  letI : Fintype 𝒱.I₀ := Fintype.ofFinite _
  let e : Fin (Fintype.card 𝒱.I₀) ≃ 𝒱.I₀ := (Fintype.equivFin 𝒱.I₀).symm
  refine ⟨Fintype.card 𝒱.I₀, fun i ↦ Spec (𝒱.X (e i)),
    fun i ↦ 𝒱.f (e i), fun _ ↦ inferInstance,
    fun i ↦ 𝒱.map_prop (e i), ?_, ?_⟩
  · intro i
    refine ⟨_, φ.h₀ (e i), 𝒰.f (φ.s₀ (e i)), ?_, φ.w₀ (e i)⟩
    rw [h𝒰eq]
    exact ⟨φ.s₀ (e i)⟩
  · have hofeq :
        Presieve.ofArrows (fun i ↦ Spec (𝒱.X (e i))) (fun i ↦ 𝒱.f (e i)) =
          Presieve.ofArrows (fun j ↦ Spec (𝒱.X j)) 𝒱.f := by
      funext T
      ext g
      constructor
      · rintro ⟨i⟩
        exact ⟨e i⟩
      · rintro ⟨j⟩
        have hj : e (e.symm j) = j := e.apply_symm_apply j
        exact hj ▸ ⟨e.symm j⟩
    change Presieve.ofArrows (fun i ↦ Spec (𝒱.X (e i)))
      (fun i ↦ 𝒱.f (e i)) ∈ Scheme.precoverage (@Etale) S
    rw [hofeq]
    exact 𝒱.cover.mem₀

/-- A surjective étale morphism to an affine scheme admits a surjective étale
refinement by a single affine scheme.  The refinement still factors through the
original morphism. -/
theorem exists_affine_etale_surjective_refinement
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [Etale f] [Surjective f] :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (q : Z ⟶ S),
      Etale q ∧ Surjective q ∧ ∃ e : Z ⟶ X, e ≫ f = q := by
  classical
  have hsingleton : Presieve.singleton f ∈ Scheme.etalePrecoverage S := by
    change Presieve.singleton f ∈ Scheme.precoverage (@Etale) S
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨Surjective.surj, inferInstance⟩
  obtain ⟨n, Y, p, hY, hpEt, hpGen, hpCover⟩ :=
    exists_finite_affine_refinement_of_mem_etalePrecoverage hsingleton
  let Z := ∐ Y
  let q : Z ⟶ S := Limits.Sigma.desc p
  letI (i : Fin n) : IsAffine (Y i) := hY i
  letI : IsAffine Z := inferInstance
  have hqEt : Etale q :=
    IsZariskiLocalAtSource.sigmaDesc hpEt
  have hfamilySurj : ∀ x : S, ∃ i, x ∈ Set.range (p i) :=
    (Scheme.ofArrows_mem_precoverage_iff (@Etale) |>.mp hpCover).1
  have hqSurj : Surjective q := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, y, rfl⟩ := hfamilySurj x
    exact Set.mem_iUnion_of_mem i ⟨y, rfl⟩
  have hfactor (i : Fin n) : ∃ e : Y i ⟶ X, e ≫ f = p i := by
    rw [Sieve.generateSingleton_eq] at hpGen
    exact hpGen i
  choose e he using hfactor
  let eSigma : Z ⟶ X := Limits.Sigma.desc e
  have heSigma : eSigma ≫ f = q := by
    apply Limits.Sigma.hom_ext
    intro i
    simpa [eSigma, q, Category.assoc] using he i
  exact ⟨Z, inferInstance, q, hqEt, hqSurj, eSigma, heSigma⟩

end AlgebraicGeometry.Scheme
