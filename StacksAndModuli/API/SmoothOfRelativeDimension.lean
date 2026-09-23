module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smooth morphisms of a fixed relative dimension

Supporting material for §4.3 of *Stacks and Moduli*, corresponding to no result of the book
and to no Stacks Project tag.

Mathlib's `AlgebraicGeometry.SmoothOfRelativeDimension n` is defined through
`Algebra.IsStandardSmoothOfRelativeDimension`, but Mathlib provides no examples of positive
relative dimension and no way to *rule out* a relative dimension. This file supplies both.

## Main declarations

- `Algebra.SubmersivePresentation.mvPolynomial`: the submersive presentation of
  `MvPolynomial ι R` over `R` given by the variables and no relations; hence the instance
  `Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)`.
- `Algebra.IsStandardSmoothOfRelativeDimension.eq_of_locally`: relative dimension is well
  defined — a ring map to a nontrivial ring that is locally standard smooth of relative
  dimension `n` and standard smooth of relative dimension `m` has `n = m`.
- `AlgebraicGeometry.specMvPolynomialHom`: the structure morphism
  `Spec R[x₁,…,x_k] ⟶ Spec R` of affine `k`-space, a smooth surjection of relative
  dimension `k`.
- `AlgebraicGeometry.eq_of_smoothOfRelativeDimension_SpecMap` and its two specializations
  `eq_of_smoothOfRelativeDimension_specMvPolynomialHom`,
  `eq_zero_of_smoothOfRelativeDimension_id`: the relative dimension of a `Spec` of a standard
  smooth algebra map is uniquely determined.
-/

@[expose] public section

open TensorProduct MvPolynomial CategoryTheory Limits

universe t w u v

namespace Algebra

variable (R : Type u) [CommRing R] (ι : Type w)

/-- The presentation of `MvPolynomial ι R` over `R` by the variables, with no relations. -/
noncomputable def Presentation.mvPolynomial :
    Presentation R (MvPolynomial ι R) ι PEmpty.{t + 1} where
  __ := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    have h : (Generators.mvPolynomial R ι).ker = ⊥ := by
      rw [Generators.ker_eq_ker_aeval_val]
      simp only [Generators.mvPolynomial, aeval_X_left]
      exact RingHom.ker_coe_equiv (RingEquiv.refl _)
    simp [h, Set.range_eq_empty]

/-- The pre-submersive presentation of `MvPolynomial ι R` with no relations. -/
noncomputable def PreSubmersivePresentation.mvPolynomial :
    PreSubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{t + 1} where
  __ := Presentation.mvPolynomial.{t} R ι
  map := PEmpty.elim
  map_inj := fun a _ _ => a.elim

/-- The submersive presentation of `MvPolynomial ι R` with no relations; its Jacobian is the
determinant of the empty matrix, hence `1`. -/
noncomputable def SubmersivePresentation.mvPolynomial :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{t + 1} where
  __ := PreSubmersivePresentation.mvPolynomial.{t} R ι
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

/-- The presentation of `MvPolynomial ι R` by the variables and no relations has dimension
the number of variables. -/
@[simp]
lemma Presentation.mvPolynomial_dimension [Finite ι] :
    (Presentation.mvPolynomial.{t} R ι).dimension = Nat.card ι := by
  simp [Presentation.dimension]

/-- Affine `n`-space: `MvPolynomial (Fin n) R` is standard smooth of relative dimension `n`. -/
instance IsStandardSmoothOfRelativeDimension.mvPolynomial_fin (n : ℕ) :
    IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) :=
  (SubmersivePresentation.mvPolynomial.{0} R (Fin n)).isStandardSmoothOfRelativeDimension
    (by simp [Presentation.dimension])

/-- Relative dimension is well defined: if `A → C` is *locally* standard smooth of relative
dimension `n` and *globally* standard smooth of relative dimension `m`, and `C` is nontrivial,
then `n = m`.  Both numbers compute the rank of `Ω[C'⁄A]` over a suitable nontrivial
localization `C'` of `C`. -/
theorem IsStandardSmoothOfRelativeDimension.eq_of_locally
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Nontrivial C] {n m : ℕ}
    (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap A C))
    [IsStandardSmoothOfRelativeDimension m A C] : n = m := by
  obtain ⟨s, hs, hsp⟩ := hn
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, ¬ IsNilpotent t := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ nilradical C := Ideal.span_le.mpr fun x hx => h x hx
    rw [hs] at hle
    obtain ⟨k, hk⟩ : IsNilpotent (1 : C) := hle Submodule.mem_top
    simp at hk
  have hL : ¬ Subsingleton (Localization.Away t) := fun hsub =>
    ht ((IsLocalization.subsingleton_iff (M := Submonoid.powers t)
      (S := Localization.Away t)).mp hsub)
  have : Nontrivial (Localization.Away t) := not_subsingleton_iff_nontrivial.mp hL
  have : IsScalarTower A C (Localization.Away t) := inferInstance
  have hnL : IsStandardSmoothOfRelativeDimension n A (Localization.Away t) := by
    have h := hsp t hts
    rwa [← IsScalarTower.algebraMap_eq,
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at h
  have : IsStandardSmoothOfRelativeDimension 0 C (Localization.Away t) :=
    IsStandardSmoothOfRelativeDimension.localization_away (R := C)
      (S := Localization.Away t) t
  have hmL : IsStandardSmoothOfRelativeDimension (0 + m) A (Localization.Away t) :=
    IsStandardSmoothOfRelativeDimension.trans (n := m) (m := 0) A C (Localization.Away t)
  have h1 : Module.rank (Localization.Away t) (Ω[Localization.Away t⁄A]) = n :=
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have h2 : Module.rank (Localization.Away t) (Ω[Localization.Away t⁄A])
      = ((0 + m : ℕ) : Cardinal) :=
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (0 + m)
  simpa using h1.symm.trans h2

end Algebra

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- The structure morphism `Spec A[x₁,…,x_k] ⟶ Spec A` of affine `k`-space over `Spec A`.
(This is the affine incarnation of `AlgebraicGeometry.AffineSpace`; see
`AlgebraicGeometry.AffineSpace.SpecIso`.) -/
noncomputable def specMvPolynomialHom (k : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin k) A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin k) A)))

instance (k : ℕ) : SmoothOfRelativeDimension k (specMvPolynomialHom A k) := by
  rw [specMvPolynomialHom, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension k)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap k).mpr inferInstance)

instance (k : ℕ) : Smooth (specMvPolynomialHom A k) :=
  SmoothOfRelativeDimension.smooth k _

instance (k : ℕ) : Surjective (specMvPolynomialHom A k) := by
  have h : Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ : Fin k => (0 : A)))) ≫
      specMvPolynomialHom A k = 𝟙 _ := by
    rw [specMvPolynomialHom, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  refine ⟨fun y => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, (Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval (fun _ : Fin k => (0 : A)))) ≫ specMvPolynomialHom A k).base x = y := by
    rw [h]; exact ⟨y, rfl⟩
  exact ⟨_, hx⟩

/-- Relative dimension is well defined on affines: the `Spec` of an algebra map which is
standard smooth of relative dimension `m` is smooth of relative dimension `n` only for
`n = m`. -/
theorem eq_of_smoothOfRelativeDimension_SpecMap {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] [Nontrivial C] {n m : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension m A C]
    (h : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) : n = m := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)] at h
  exact Algebra.IsStandardSmoothOfRelativeDimension.eq_of_locally (A := A) (C := C) h

/-- Affine `k`-space over a nonzero ring is smooth of relative dimension `n` only for
`n = k`. -/
theorem eq_of_smoothOfRelativeDimension_specMvPolynomialHom [Nontrivial A] {n k : ℕ}
    (h : SmoothOfRelativeDimension n (specMvPolynomialHom A k)) : n = k :=
  eq_of_smoothOfRelativeDimension_SpecMap (A := A) (C := MvPolynomial (Fin k) A) h

/-- The identity of a nonempty affine scheme is smooth of relative dimension `n` only for
`n = 0`. -/
theorem eq_zero_of_smoothOfRelativeDimension_id [Nontrivial A] {n : ℕ}
    (h : SmoothOfRelativeDimension n (𝟙 (Spec (CommRingCat.of A)))) : n = 0 := by
  rw [← Spec.map_id, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)] at h
  have h' : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap A A) := by simpa using h
  exact Algebra.IsStandardSmoothOfRelativeDimension.eq_of_locally (A := A) (C := A) h'

end AlgebraicGeometry
