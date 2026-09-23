module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.2-projectivity-of-the-grassmannian»
public import StacksAndModuli.API.DualNumberGrassmannian

/-!
# The tangent space of the Grassmannian

This module formalizes **Exercise 2.2.10** (`exer:grassmannian-tangent-space`) of §2.2
(Projectivity of the Grassmannian) of Chapter 2 of *Stacks and Moduli*,
label `sec:grassmannian`: for a field `k` and a
`k`-point `p` of `Gr(q, n)` corresponding to a quotient `Q = k^n/K`, the tangent space
`T_p Gr(q, n)_k` is naturally in bijection with `Hom_k(K, Q)`.

Tangent vectors are rendered as the book later defines them for stacks
(**Definition 4.5.7**, `def:tangent-space`): morphisms `Spec k[ε] → Gr(q, n)`
restricting to `p` along the closed embedding `Spec k → Spec k[ε ]`; see the
`[decision]` entry in this folder's COMMENTARY.md. The module-theoretic heart — lifts
of the subspace `K ⊆ k^n` to `k[ε]^n` with locally free quotient are classified by
`Hom_k(K, k^n/K)` — is `StacksAndModuli/API/DualNumberGrassmannian.lean`; this module supplies
the scheme-level translation through the functor of points.

Main book result:
- `AlgebraicGeometry.Scheme.grassmannianTangentSpaceEquiv` (**Exercise 2.2.10**,
  `exer:grassmannian-tangent-space`): the tangent-space bijection
  `T_p Gr(q, n) ≃ Hom_k(K, k^n/K)`.
-/

@[expose] public section

section ExerGrassmannianTangentSpace

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {n : ℕ}

/-- Background definition for Exercise 2.2.10 (the implicit description
of the point): the subspace `K ⊆ A^n` attached to an `A`-valued point of the
Grassmannian functor, obtained from the kernel datum's global sections along the
global-sections isomorphism `Γ(Spec A, O) ≅ A`. The corresponding quotient of the
point is `A^n/K`. -/
noncomputable def grassmannianPointSubmodule {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {A : Type u} [CommRing A] (p : Spec (CommRingCat.of A) ⟶ P) :
    Submodule A (Fin n → A) :=
  ((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv

/-- Over a field, the quotient by the subspace attached to a `k`-point of `Gr(q, n)`
has dimension `q`. -/
lemma finrank_quotient_grassmannianPointSubmodule {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P) :
    Module.finrank k ((Fin n → k) ⧸ grassmannianPointSubmodule h p) = q := by
  obtain ⟨-, hrank⟩ := quotient_projective_rank_of_mapPiRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    ((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩)
    ((h.homEquiv p).2.projective_affine ⟨⊤, isAffineOpen_top _⟩)
    (fun p' ↦ (h.homEquiv p).2.rankAtStalk_affine ⟨⊤, isAffineOpen_top _⟩ p')
  have h0 := hrank ⟨⊥, Ideal.isPrime_bot⟩
  change Module.finrank k ((Fin n → k) ⧸
    (((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv)) = q
  rwa [congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := k) (M := (Fin n → k) ⧸
      (((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv))) _] at h0

/-- The augmentation `Spec k → Spec k[ε]` (inclusion of the closed point). -/
noncomputable def specAugmentation (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

set_option maxSynthPendingDepth 10 in
/-- The projectivity-and-rank package of the lift attached to a homomorphism,
transported to the global sections of the spectrum of the dual numbers. -/
lemma grassmannianDualLift_package {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    Module.Projective Γ(Spec (CommRingCat.of (DualNumber k)), ⊤)
        ((Fin n → Γ(Spec (CommRingCat.of (DualNumber k)), ⊤)) ⧸
          (Submodule.dualNumberLift φ).mapPiRingEquiv
            (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm) ∧
      ∀ p' : PrimeSpectrum Γ(Spec (CommRingCat.of (DualNumber k)), ⊤),
        Module.rankAtStalk
          ((Fin n → Γ(Spec (CommRingCat.of (DualNumber k)), ⊤)) ⧸
            (Submodule.dualNumberLift φ).mapPiRingEquiv
              (Scheme.ΓSpecIso
                (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm) p'
          = q := by
  have hq : Module.finrank k ((Fin n → k) ⧸ grassmannianPointSubmodule h p) = q :=
    finrank_quotient_grassmannianPointSubmodule h p
  have hprojN : Module.Projective (DualNumber k)
      ((Fin n → DualNumber k) ⧸ Submodule.dualNumberLift φ) := by
    have hfree := Submodule.dualNumberLift_free φ
    exact Module.Projective.of_free
  have hrankN : ∀ p' : PrimeSpectrum (DualNumber k),
      Module.rankAtStalk
        ((Fin n → DualNumber k) ⧸ Submodule.dualNumberLift φ) p' = q := by
    intro p'
    rw [Submodule.rankAtStalk_dualNumberLift φ p', hq]
  exact quotient_projective_rank_of_mapPiRingEquiv _ _ hprojN hrankN

/-- The point of the Grassmannian functor over the dual numbers attached to a
homomorphism `φ : K → k^n/K` at a `k`-point with kernel `K`. -/
noncomputable def grassmannianDualPoint {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    (grassmannianFunctor.{u} q n).obj (op (Spec (CommRingCat.of (DualNumber k)))) :=
  ⟨SubmoduleSheafData.ofAffineSubmodule
      ((Submodule.dualNumberLift φ).mapPiRingEquiv
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm),
    SubmoduleSheafData.quotientProjectiveOfRank_ofAffineSubmodule _
      (grassmannianDualLift_package h p φ).1 (grassmannianDualLift_package h p φ).2⟩

@[simp] lemma grassmannianDualPoint_val {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    (grassmannianDualPoint h p φ).1 =
      SubmoduleSheafData.ofAffineSubmodule
        ((Submodule.dualNumberLift φ).mapPiRingEquiv
          (Scheme.ΓSpecIso
            (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm) :=
  rfl

/-- The tangent vector of the Grassmannian at `p` attached to a homomorphism. -/
noncomputable def grassmannianTangentVector {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ P :=
  h.homEquiv.symm (grassmannianDualPoint h p φ)

lemma homEquiv_grassmannianTangentVector {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    h.homEquiv (grassmannianTangentVector h p φ) = grassmannianDualPoint h p φ :=
  Equiv.apply_symm_apply _ _

/-- Auxiliary identifications for the tangent-space computation. -/
lemma grassmannianPointSubmodule_eq_mapPiRingEquiv {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {A : Type u} [CommRing A] (p : Spec (CommRingCat.of A) ⟶ P) :
    ((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv =
      grassmannianPointSubmodule h p :=
  rfl

set_option maxSynthPendingDepth 10 in
/-- The tangent vector attached to `φ` restricts to `p` at the closed point. -/
lemma specAugmentation_comp_grassmannianTangentVector {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P)
    (φ : grassmannianPointSubmodule h p →ₗ[k]
      ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) :
    specAugmentation k ≫ grassmannianTangentVector h p φ = p := by
  set σ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom with hσdef
  set eA := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv
    with heA
  have hle : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤
      (Spec.map σ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of (DualNumber k))).Opens) := by
    intro x _
    trivial
  have hcancel :
      ((Submodule.dualNumberLift φ).mapPiRingEquiv eA.symm).mapPiRingEquiv eA =
        Submodule.dualNumberLift φ := by
    rw [show eA = eA.symm.symm from (RingEquiv.symm_symm eA).symm]
    exact Submodule.mapPiRingEquiv_symm_mapPiRingEquiv eA.symm _
  have hσfst : ((fun (v : Fin n → DualNumber k) i ↦ σ.hom (v i)) ''
        ((Submodule.dualNumberLift φ) : Set (Fin n → DualNumber k))) =
      Submodule.dualFstPi ''
        ((Submodule.dualNumberLift φ) : Set (Fin n → DualNumber k)) := by
    apply Set.image_congr
    intro v _
    rfl
  apply h.homEquiv.injective
  rw [show specAugmentation k = Spec.map σ from rfl, h.homEquiv_comp,
    homEquiv_grassmannianTangentVector, grassmannianFunctor_map_apply]
  apply Subtype.ext
  change SubmoduleSheafData.comap (Spec.map σ) (grassmannianDualPoint h p φ).1 =
    (h.homEquiv p).1
  rw [grassmannianDualPoint_val,
    SubmoduleSheafData.eq_iff_submodule_top,
    SubmoduleSheafData.comap_submodule_eq_span _ (Spec.map σ)
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩) hle,
    SubmoduleSheafData.ofAffineSubmodule_submodule_top,
    span_specMap_appPi_image_eq_iff σ _ ((h.homEquiv p).1.submodule
      ⟨⊤, isAffineOpen_top _⟩),
    hcancel, hσfst, grassmannianPointSubmodule_eq_mapPiRingEquiv]
  exact Submodule.span_fst_image_dualNumberLift φ

set_option maxSynthPendingDepth 10 in
/-- **Exercise 2.2.10** (`exer:grassmannian-tangent-space`): let `k` be a field and
`p` a `k`-point of a scheme `P` representing `Gr(q, n)`, corresponding to a quotient
`Q = k^n/K`. The tangent space of the Grassmannian at `p` — morphisms
`Spec k[ε] → P` restricting to `p` at the closed point — is naturally in bijection
with the `k`-vector space `Hom_k(K, Q)`.

Faithfulness caveat: the book's tangent space `T_p (Gr(q,n) ×_ℤ k)` is rendered as
dual-number lifts of the absolute point (the book's own definition of tangent spaces,
Definition 4.5.7, applied through the identification of `S`-morphisms
`Spec k[ε] → Gr ×_ℤ k` with absolute morphisms `Spec k[ε] → Gr`); see the
`[decision]` COMMENTARY entry. -/
noncomputable def grassmannianTangentSpaceEquiv {q : ℕ} {P : Scheme.{u}}
    (h : (grassmannianFunctor.{u} q n).RepresentableBy P)
    {k : Type u} [Field k] (p : Spec (CommRingCat.of k) ⟶ P) :
    {f : Spec (CommRingCat.of (DualNumber k)) ⟶ P // specAugmentation k ≫ f = p} ≃
      (grassmannianPointSubmodule h p →ₗ[k]
        ((Fin n → k) ⧸ grassmannianPointSubmodule h p)) := by
  classical
  set σ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom with hσdef
  have hle : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤
      (Spec.map σ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of (DualNumber k))).Opens) := by
    intro x _
    trivial
  have hcancel : ∀ (N : Submodule (DualNumber k) (Fin n → DualNumber k)),
      (N.mapPiRingEquiv
          (Scheme.ΓSpecIso
            (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm).mapPiRingEquiv
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv
        = N := by
    intro N
    rw [show (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv
        = (Scheme.ΓSpecIso
            (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm.symm from
      (RingEquiv.symm_symm _).symm]
    exact Submodule.mapPiRingEquiv_symm_mapPiRingEquiv _ N
  refine (Equiv.ofBijective
    (fun φ ↦ ⟨grassmannianTangentVector h p φ,
      specAugmentation_comp_grassmannianTangentVector h p φ⟩) ⟨?_, ?_⟩).symm
  · -- injectivity
    intro φ ψ hfψ
    have h1 : grassmannianDualPoint h p φ = grassmannianDualPoint h p ψ := by
      rw [← homEquiv_grassmannianTangentVector h p φ,
        ← homEquiv_grassmannianTangentVector h p ψ]
      exact congrArg h.homEquiv (congrArg Subtype.val hfψ)
    have h2 := congrArg Subtype.val h1
    rw [grassmannianDualPoint_val, grassmannianDualPoint_val,
      SubmoduleSheafData.eq_iff_submodule_top,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top] at h2
    have h3 := congrArg (fun U ↦ Submodule.mapPiRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv U) h2
    simp only [hcancel] at h3
    exact Submodule.dualNumberLift_injective h3
  · -- surjectivity
    rintro ⟨f, hf⟩
    have hproj : Module.Projective (DualNumber k)
        ((Fin n → DualNumber k) ⧸
          ((h.homEquiv f).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
            (Scheme.ΓSpecIso
              (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv) :=
      (quotient_projective_rank_of_mapPiRingEquiv _ _
        ((h.homEquiv f).2.projective_affine ⟨⊤, isAffineOpen_top _⟩)
        (fun p' ↦ (h.homEquiv f).2.rankAtStalk_affine ⟨⊤, isAffineOpen_top _⟩ p')).1
    have hspan : Submodule.span k
        (Submodule.dualFstPi ''
          ((((h.homEquiv f).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
            (Scheme.ΓSpecIso
              (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv) :
            Set (Fin n → DualNumber k))) = grassmannianPointSubmodule h p := by
      have hcomap : (h.homEquiv f).1.comap (Spec.map σ) = (h.homEquiv p).1 := by
        have h1 : h.homEquiv (specAugmentation k ≫ f) = h.homEquiv p := by
          rw [hf]
        rw [show specAugmentation k = Spec.map σ from rfl] at h1
        rw [h.homEquiv_comp, grassmannianFunctor_map_apply] at h1
        exact congrArg Subtype.val h1
      have htop := (SubmoduleSheafData.eq_iff_submodule_top _ _).mp hcomap
      rw [SubmoduleSheafData.comap_submodule_eq_span _ (Spec.map σ)
        (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩) hle] at htop
      have hiff := (span_specMap_appPi_image_eq_iff σ
        ((h.homEquiv f).1.submodule ⟨⊤, isAffineOpen_top _⟩)
        ((h.homEquiv p).1.submodule ⟨⊤, isAffineOpen_top _⟩)).mp htop
      rw [grassmannianPointSubmodule_eq_mapPiRingEquiv h p] at hiff
      have hσfst : ((fun (v : Fin n → DualNumber k) i ↦ σ.hom (v i)) ''
            ((((h.homEquiv f).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
              (Scheme.ΓSpecIso
                (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv) :
              Set (Fin n → DualNumber k))) =
          Submodule.dualFstPi ''
            ((((h.homEquiv f).1.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
              (Scheme.ΓSpecIso
                (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv) :
              Set (Fin n → DualNumber k)) := by
        apply Set.image_congr
        intro v _
        rfl
      rw [hσfst] at hiff
      exact hiff
    obtain ⟨φ, hφ⟩ := Submodule.exists_dualNumberLift_eq hproj hspan
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    change grassmannianTangentVector h p φ = f
    apply h.homEquiv.injective
    rw [homEquiv_grassmannianTangentVector]
    apply Subtype.ext
    rw [grassmannianDualPoint_val,
      SubmoduleSheafData.eq_iff_submodule_top,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top, hφ,
      Submodule.mapPiRingEquiv_symm_mapPiRingEquiv]

end AlgebraicGeometry.Scheme

end ExerGrassmannianTangentSpace

section ExerGrassmannianProjectiveAlternativeProof

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- **Exercise 2.2.11** (`exer:grassmannian-projective-alternative-proof`): the
Grassmannian `Gr(q, n)` is projective over `ℤ`.

The book asks for an *alternative* proof of this — via the valuative criterion for
properness of Exercise 2.2.7, together with a criterion for a
proper morphism that is injective on points and tangent spaces (equivalently, a proper
monomorphism) to be a closed immersion.  The statement is recorded here and derived from
the Plücker embedding of Proposition 2.2.8
(`grassmannianOverRepresentation_isStronglyProjective`); the alternative argument itself is
not formalized, since neither "proper + monomorphism ⟹ closed immersion" nor the
properness of `Gr(q, n)` deduced from the valuative criterion is available.  See the
`[deviation]` entry in this folder's COMMENTARY.md.

Here `Gr(q, n)` is presented as its base change to `Spec ℤ`, the terminal scheme, which is
the same scheme up to the canonical isomorphism `Gr ×_ℤ Spec ℤ ≅ Gr`. -/
theorem isStronglyProjective_grassmannianOverRepresentation_specZ (q n : ℕ) :
    IsStronglyProjective
      (grassmannianOverRepresentation
        (Spec (CommRingCat.of (ULift.{u} ℤ))) q n).hom :=
  grassmannianOverRepresentation_isStronglyProjective _ q n

end AlgebraicGeometry.Scheme

end ExerGrassmannianProjectiveAlternativeProof
