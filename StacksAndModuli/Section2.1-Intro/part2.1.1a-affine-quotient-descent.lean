module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.1-quasi-coherent-subsheaves»
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Affine descent for locally free quotients

Supporting infrastructure for §2.1 (The Grassmannian, Hilbert, and Quot functors) of
Chapter 2 of *Stacks and Moduli* (the section
heading carries no `sec:` label).

This module supplies the affine local-to-global algebra needed to pass from the
local definition of a finite locally free quotient in §2.1 to a finite projective
constant-rank quotient on every affine open. It contains no declaration corresponding to
a labelled book result; everything here is glue for Theorem 2.1.1
(`thm:grassmannian-projective-relative`).

Main declarations:
- `AlgebraicGeometry.Scheme.SubmoduleSheafData.QuotientProjectiveOfRank.projective_affine`
  and `QuotientProjectiveOfRank.rankAtStalk_affine`: the pointwise local definition of a
  rank-`q` locally free quotient yields finite projectivity and constant rank `q` of the
  quotient module on *every* affine open.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmGrassmannianProjectiveRelative

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace SubmoduleSheafData

variable {X : Scheme.{u}} {n : ℕ}

/-- Finite projectivity and constant rank of a quotient pass from an affine open to
each of its basic opens.  This is the module-theoretic localization step underlying
the affine globalization of the Plücker construction. -/
lemma quotient_projective_rank_affineBasicOpen (K : X.SubmoduleSheafData n)
    (U : X.affineOpens) (f : Γ(X, U.1)) {q : ℕ}
    (hproj : Module.Projective Γ(X, U.1)
      ((Fin n → Γ(X, U.1)) ⧸ K.submodule U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U.1),
      Module.rankAtStalk ((Fin n → Γ(X, U.1)) ⧸ K.submodule U) p = q) :
    Module.Projective Γ(X, (X.affineBasicOpen f).1)
        ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
          K.submodule (X.affineBasicOpen f)) ∧
      ∀ p : PrimeSpectrum Γ(X, (X.affineBasicOpen f).1),
        Module.rankAtStalk
          ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
            K.submodule (X.affineBasicOpen f)) p = q := by
  let R := Γ(X, U.1)
  let S := Γ(X, (X.affineBasicOpen f).1)
  let φ : R →+* S :=
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le f)).op).hom
  letI : Algebra R S := φ.toAlgebra
  let N := K.submodule U
  haveI : Module.Finite R ((Fin n → R) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective _)
  haveI : Module.Projective R ((Fin n → R) ⧸ N) := hproj
  let ψ := LinearMap.baseChangePi S N.mkQ
  have hsurj : Function.Surjective ψ :=
    LinearMap.baseChangePi_surjective S (Submodule.mkQ_surjective N)
  have hker : LinearMap.ker ψ = K.submodule (X.affineBasicOpen f) := by
    rw [← K.span_resPi_basicOpen U f]
    apply le_antisymm
    · have h := LinearMap.ker_baseChangePi_le_span S
        (Submodule.mkQ_surjective N)
      rwa [Submodule.ker_mkQ] at h
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change ψ (fun i ↦ algebraMap R S (w i)) = 0
      rw [LinearMap.baseChangePi_comp_algebraMap,
        show N.mkQ w = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hw,
        TensorProduct.tmul_zero]
  let e := Submodule.quotEquivOfEq _ _ hker.symm
  have hbase := LinearMap.quotKer_baseChangePi_finite_projective_rank
    (S := S) N.mkQ (Submodule.mkQ_surjective N) hrank
  constructor
  · letI : Module.Projective S ((Fin n → S) ⧸ LinearMap.ker ψ) := hbase.2.1
    exact Module.Projective.of_equiv e.symm
  · intro p
    have he := Module.rankAtStalk_eq_of_equiv e
    calc
      Module.rankAtStalk ((Fin n → S) ⧸ K.submodule (X.affineBasicOpen f)) p =
          Module.rankAtStalk ((Fin n → S) ⧸ LinearMap.ker ψ) p := congrFun he p
      _ = q := hbase.2.2 p

/-- A locally free quotient of fixed rank admits, around every point of every affine
open, a basic neighborhood on which the corresponding module of sections is finite
projective of that rank. -/
lemma QuotientProjectiveOfRank.exists_affineBasicOpen_projective_rank
    {q : ℕ} {K : X.SubmoduleSheafData n} (hK : K.QuotientProjectiveOfRank q)
    (U : X.affineOpens) (x : ↑U.1) :
    ∃ f : Γ(X, U.1), x.1 ∈ X.basicOpen f ∧
      Module.Projective Γ(X, (X.affineBasicOpen f).1)
        ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
          K.submodule (X.affineBasicOpen f)) ∧
      ∀ p : PrimeSpectrum Γ(X, (X.affineBasicOpen f).1),
        Module.rankAtStalk
          ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
            K.submodule (X.affineBasicOpen f)) p = q := by
  obtain ⟨V, hxV, hproj, hrank⟩ := hK x.1
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 x.1 ⟨x.2, hxV⟩
  have hlocal := K.quotient_projective_rank_affineBasicOpen V g hproj hrank
  have hW : X.affineBasicOpen f = X.affineBasicOpen g := Subtype.ext hfg
  refine ⟨f, hxf, ?_⟩
  exact hW.symm ▸ hlocal

/-- The basic opens on which a locally free quotient has a projective module of
sections of the prescribed rank form a spanning family in every affine open. -/
lemma QuotientProjectiveOfRank.span_affineBasicOpen_projective_rank
    {q : ℕ} {K : X.SubmoduleSheafData n} (hK : K.QuotientProjectiveOfRank q)
    (U : X.affineOpens) :
    Ideal.span {f : Γ(X, U.1) |
      Module.Projective Γ(X, (X.affineBasicOpen f).1)
          ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
            K.submodule (X.affineBasicOpen f)) ∧
        ∀ p : PrimeSpectrum Γ(X, (X.affineBasicOpen f).1),
          Module.rankAtStalk
            ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
              K.submodule (X.affineBasicOpen f)) p = q} = ⊤ := by
  apply U.2.iSup_basicOpen_eq_self_iff.mp
  apply le_antisymm
  · exact iSup_le fun f ↦ X.basicOpen_le f.1
  · intro x hx
    obtain ⟨f, hxf, hf⟩ :=
      hK.exists_affineBasicOpen_projective_rank U ⟨x, hx⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨f, hf⟩, hxf⟩

/-- On an affine open, the module of sections of a locally free quotient is
projective.  The proof identifies its restriction to every good basic open with a
localized module, uses the spanning family above to descend finite presentation and
flatness, and then applies the finite-presentation criterion for projectivity. -/
lemma QuotientProjectiveOfRank.projective_affine
    {q : ℕ} {K : X.SubmoduleSheafData n} (hK : K.QuotientProjectiveOfRank q)
    (U : X.affineOpens) :
    Module.Projective Γ(X, U.1)
      ((Fin n → Γ(X, U.1)) ⧸ K.submodule U) := by
  let R := Γ(X, U.1)
  let M := (Fin n → R) ⧸ K.submodule U
  let s : Set R := {f |
    Module.Projective Γ(X, (X.affineBasicOpen f).1)
        ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
          K.submodule (X.affineBasicOpen f)) ∧
      ∀ p : PrimeSpectrum Γ(X, (X.affineBasicOpen f).1),
        Module.rankAtStalk
          ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
            K.submodule (X.affineBasicOpen f)) p = q}
  have hs : Ideal.span s = ⊤ := hK.span_affineBasicOpen_projective_rank U
  let S (g : s) := Γ(X, (X.affineBasicOpen g.1).1)
  let α (g : s) : R →+* S g :=
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le g.1)).op).hom
  letI (g : s) : Algebra R (S g) := (α g).toAlgebra
  let Mloc (g : s) :=
    (Fin n → S g) ⧸ K.submodule (X.affineBasicOpen g.1)
  let equiv (g : s) : Mloc g ≃ₗ[S g] TensorProduct R (S g) M := by
    let N := K.submodule U
    let ψ := LinearMap.baseChangePi (S g) N.mkQ
    have hker : LinearMap.ker ψ = K.submodule (X.affineBasicOpen g.1) := by
      rw [← K.span_resPi_basicOpen U g.1]
      apply le_antisymm
      · have h := LinearMap.ker_baseChangePi_le_span (S g)
          (Submodule.mkQ_surjective N)
        rwa [Submodule.ker_mkQ] at h
      · apply Submodule.span_le.mpr
        rintro _ ⟨w, hw, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        change ψ (fun i ↦ algebraMap R (S g) (w i)) = 0
        rw [LinearMap.baseChangePi_comp_algebraMap,
          show N.mkQ w = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hw,
          TensorProduct.tmul_zero]
    exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (ψ.quotKerEquivOfSurjective
        (LinearMap.baseChangePi_surjective (S g) (Submodule.mkQ_surjective N)))
  let locMap (g : s) : M →ₗ[R] Mloc g :=
    (equiv g).symm.toLinearMap.restrictScalars R ∘ₗ
      TensorProduct.mk R (S g) M 1
  letI (g : s) : IsLocalization.Away g.1 (S g) :=
    U.2.isLocalization_basicOpen g.1
  letI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (locMap g) := by
    exact IsLocalizedModule.of_linearEquiv (Submonoid.powers g.1)
      (TensorProduct.mk R (S g) M 1) ((equiv g).symm.restrictScalars R)
  have hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs locMap fun g ↦ by
      letI : Module.Projective (S g) (Mloc g) := g.2.1
      exact Module.finitePresentation_of_projective (S g) (Mloc g)
  have hflat : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs Mloc locMap fun g ↦ by
      letI : Module.Projective (S g) (Mloc g) := g.2.1
      haveI : Module.Flat (S g) (Mloc g) := Module.Flat.of_projective
      haveI : Module.Flat R (S g) := IsLocalization.flat (S g) (Submonoid.powers g.1)
      exact Module.Flat.trans R (S g) (Mloc g)
  letI : Module.FinitePresentation R M := hfp
  letI : Module.Flat R M := hflat
  exact Module.Flat.projective_of_finitePresentation

/-- On an affine open, the module of sections of a locally free quotient has the
prescribed rank at every prime. -/
lemma QuotientProjectiveOfRank.rankAtStalk_affine
    {q : ℕ} {K : X.SubmoduleSheafData n} (hK : K.QuotientProjectiveOfRank q)
    (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk
      ((Fin n → Γ(X, U.1)) ⧸ K.submodule U) p = q := by
  let R := Γ(X, U.1)
  let M := (Fin n → R) ⧸ K.submodule U
  let s : Set R := {f |
    Module.Projective Γ(X, (X.affineBasicOpen f).1)
        ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
          K.submodule (X.affineBasicOpen f)) ∧
      ∀ p : PrimeSpectrum Γ(X, (X.affineBasicOpen f).1),
        Module.rankAtStalk
          ((Fin n → Γ(X, (X.affineBasicOpen f).1)) ⧸
            K.submodule (X.affineBasicOpen f)) p = q}
  have hs : Ideal.span s = ⊤ := hK.span_affineBasicOpen_projective_rank U
  have hnsub : ¬ s ⊆ p.asIdeal := by
    intro hle
    have : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr hle
    rw [hs] at this
    exact p.2.ne_top (top_unique this)
  obtain ⟨f, hfs, hfp⟩ := Set.not_subset.mp hnsub
  let S := Γ(X, (X.affineBasicOpen f).1)
  let α : R →+* S :=
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le f)).op).hom
  letI : Algebra R S := α.toAlgebra
  letI : IsLocalization.Away f S := U.2.isLocalization_basicOpen f
  have hpBasic : p ∈ PrimeSpectrum.basicOpen f := by
    simpa [PrimeSpectrum.mem_basicOpen] using hfp
  have hpRange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S f]
    exact hpBasic
  obtain ⟨P, hP⟩ := hpRange
  let N := K.submodule U
  let ψ := LinearMap.baseChangePi S N.mkQ
  have hker : LinearMap.ker ψ = K.submodule (X.affineBasicOpen f) := by
    rw [← K.span_resPi_basicOpen U f]
    apply le_antisymm
    · have h := LinearMap.ker_baseChangePi_le_span S
        (Submodule.mkQ_surjective N)
      rwa [Submodule.ker_mkQ] at h
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change ψ (fun i ↦ algebraMap R S (w i)) = 0
      rw [LinearMap.baseChangePi_comp_algebraMap,
        show N.mkQ w = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hw,
        TensorProduct.tmul_zero]
  let e : ((Fin n → S) ⧸ K.submodule (X.affineBasicOpen f)) ≃ₗ[S]
      TensorProduct R S M :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (ψ.quotKerEquivOfSurjective
        (LinearMap.baseChangePi_surjective S (Submodule.mkQ_surjective N)))
  have he := Module.rankAtStalk_eq_of_equiv e
  letI : Module.Finite R M :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  letI : Module.Projective R M := hK.projective_affine U
  letI : Module.Flat R M := Module.Flat.of_projective
  calc
    Module.rankAtStalk M p = Module.rankAtStalk M
        (PrimeSpectrum.comap (algebraMap R S) P) := by rw [hP]
    _ = Module.rankAtStalk (TensorProduct R S M) P :=
      (Module.rankAtStalk_baseChange P).symm
    _ = Module.rankAtStalk
        ((Fin n → S) ⧸ K.submodule (X.affineBasicOpen f)) P :=
      (congrFun he P).symm
    _ = q := hfs.2 P
end SubmoduleSheafData

end AlgebraicGeometry.Scheme

end ThmGrassmannianProjectiveRelative

#min_imports
