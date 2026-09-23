module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»
public import StacksAndModuli.API.BaseChangePi
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Quasi-coherent submodule sheaves of a trivial bundle

This module provides supporting infrastructure for §2.1 (The Grassmannian, Hilbert, and Quot
functors) of Chapter 2 of *Stacks and Moduli* (the
section heading carries no `sec:` label). It contains no declaration corresponding to a
labelled book result; everything here is glue for Theorem 2.1.1
(`thm:grassmannian-projective-relative`).

A point of the Grassmannian functor `Gr(q, n)` over a scheme `X` is a rank-`q` locally free
quotient `O_X^{⊕n} ↠ Q`, and two quotients are identified when they have equal kernels
(`rem:quot-remarks`(2)). We therefore encode such a point by its kernel: a quasi-coherent
submodule sheaf `K ⊆ O_X^{⊕n}`. Mirroring `AlgebraicGeometry.Scheme.IdealSheafData`, the
sheaf `K` is recorded by its values on affine opens together with the localization property
on basic opens; this keeps the data in `Type u` and strictly functorial, which is essential
for building set-valued moduli functors on `Scheme.{u}`.

Main declarations:
- `AlgebraicGeometry.Scheme.resPi`: componentwise restriction of sections of `O_X^{⊕n}`.
- `AlgebraicGeometry.Scheme.Hom.appPi`: componentwise pullback of sections of `O_Y^{⊕n}`
  along a morphism `X ⟶ Y`, restricted to an open of `X`.
- `AlgebraicGeometry.Scheme.SubmoduleSheafData`: a quasi-coherent submodule sheaf of
  `O_X^{⊕n}`, given by submodules on affine opens with the localization property.
- `AlgebraicGeometry.Scheme.SubmoduleSheafData.QuotientProjectiveOfRank`: the quotient
  `O_X^{⊕n}/K` is finite locally free of rank `q`.
- `AlgebraicGeometry.Scheme.SubmoduleSheafData.comap`: pullback of a quasi-coherent
  submodule sheaf along a morphism of schemes, with functoriality
  (`comap_id`, `comap_comp`).
- `AlgebraicGeometry.Scheme.SubmoduleSheafData.ofSubmodules`: the largest
  quasi-coherent datum below an arbitrary family of affine-local submodules; it induces
  the complete lattice on `SubmoduleSheafData`.
- `AlgebraicGeometry.Scheme.SubmoduleSheafData.map`: the order-theoretic direct image,
  right adjoint to pullback (`map_gc`).
-/

@[expose] public section


section ThmGrassmannianProjectiveRelative

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} {n : ℕ}

/-- A presheaf restriction along an endomorphism of an open is the identity, since the
category of opens is thin. -/
lemma presheaf_map_end_apply (U : X.Opens) (i : Opposite.op U ⟶ Opposite.op U)
    (x : Γ(X, U)) : (X.presheaf.map i).hom x = x := by
  rw [show i = 𝟙 _ from Subsingleton.elim _ _]
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (Opposite.op U)) x

/-- Fusion of two consecutive presheaf restrictions: the category of opens is thin, so any
two restrictions with the same endpoints agree. Stated for arbitrary homs so that use
sites whose opens are only definitionally equal still elaborate. -/
lemma presheaf_map_map_apply {A B C : (X.Opens)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (x : X.presheaf.obj A) :
    (X.presheaf.map b).hom ((X.presheaf.map a).hom x) = (X.presheaf.map c).hom x := by
  have h : a ≫ b = c := Subsingleton.elim _ _
  rw [← h, X.presheaf.map_comp]
  rfl

/-- Fusion of three consecutive presheaf restrictions; see `presheaf_map_map_apply`. -/
lemma presheaf_map_map_map_apply {A B C D : (X.Opens)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (d : A ⟶ D) (x : X.presheaf.obj A) :
    (X.presheaf.map c).hom ((X.presheaf.map b).hom ((X.presheaf.map a).hom x)) =
      (X.presheaf.map d).hom x := by
  have h : a ≫ b ≫ c = d := Subsingleton.elim _ _
  rw [← h, X.presheaf.map_comp, X.presheaf.map_comp]
  rfl

/-- Every Zariski open cover of an affine scheme admits a finite refinement by
canonical basic opens.  In addition to the covering functions, this records a member
of the original cover containing each chosen basic open; the resulting factorization
through that member is obtained with `IsOpenImmersion.lift`.

This is the topological refinement step used to pass from arbitrary Zariski descent to
finite affine basic-open descent. -/
lemma exists_finite_basicOpen_refinement [IsAffine X] (𝒰 : X.OpenCover) :
    ∃ (κ : Type u) (_ : Finite κ) (f : κ → Γ(X, ⊤)) (j : κ → 𝒰.I₀),
      (∀ i, X.basicOpen (f i) ≤ (𝒰.f (j i)).opensRange) ∧
        ⨆ i, X.basicOpen (f i) = ⊤ := by
  classical
  choose V hVbasis hVmem hVsub using fun x : X ↦
    (Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X)
      (U := (𝒰.f (𝒰.idx x)).opensRange) (x := x)) (by simpa using 𝒰.covers x)
  let f : X → Γ(X, ⊤) := fun x ↦ (hVbasis x).choose
  have hf (x : X) : X.basicOpen (f x) = V x := (hVbasis x).choose_spec
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (X.basicOpen (f x) : Set X))
    (fun x ↦ (X.basicOpen (f x)).2) (fun x _ ↦ Set.mem_iUnion.mpr
      ⟨x, by rw [hf x]; exact hVmem x⟩)
  refine ⟨s, s.finite_toSet, fun x ↦ f x.1, fun x ↦ 𝒰.idx x.1,
    fun x ↦ by simpa [hf x.1] using hVsub x.1, ?_⟩
  apply le_antisymm
  · exact le_top
  · intro x _
    have hx : x ∈ ⋃ i : s, (X.basicOpen (f i.1) : Set X) := by
      simpa [Set.iUnion_subtype] using hs (Set.mem_univ x)
    rw [Opens.mem_iSup]
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, hi⟩

/-- Morphism-valued form of `exists_finite_basicOpen_refinement`: every basic open in
the finite refinement comes with its canonical factorization through the selected member
of the original cover. -/
lemma exists_finite_basicOpen_refinement_lift [IsAffine X] (𝒰 : X.OpenCover) :
    ∃ (κ : Type u) (_ : Finite κ) (f : κ → Γ(X, ⊤)) (j : κ → 𝒰.I₀)
      (k : ∀ i, (X.basicOpen (f i)).toScheme ⟶ 𝒰.X (j i)),
      (∀ i, k i ≫ 𝒰.f (j i) = (X.basicOpen (f i)).ι) ∧
        ⨆ i, X.basicOpen (f i) = ⊤ := by
  obtain ⟨κ, hκ, f, j, hsub, hcover⟩ := exists_finite_basicOpen_refinement 𝒰
  letI : Finite κ := hκ
  let k (i : κ) : (X.basicOpen (f i)).toScheme ⟶ 𝒰.X (j i) :=
    IsOpenImmersion.lift (𝒰.f (j i)) (X.basicOpen (f i)).ι (by
      rw [Opens.range_ι]
      simpa only [Scheme.Hom.coe_opensRange] using SetLike.coe_mono (hsub i))
  exact ⟨κ, hκ, f, j, k, fun i ↦ IsOpenImmersion.lift_fac _ _ _, hcover⟩

/-- Let `X` be a scheme and `V ≤ U` opens of `X`. The componentwise restriction of sections
of the trivial rank-`n` module `O_X^{⊕n}`, as a plain function
`(Fin n → Γ(X, U)) → Fin n → Γ(X, V)`. -/
def resPi (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U) (n : ℕ) (v : Fin n → Γ(X, U)) :
    Fin n → Γ(X, V) :=
  fun i ↦ (X.presheaf.map (homOfLE h).op).hom (v i)

@[simp]
lemma resPi_apply {U V : X.Opens} (h : V ≤ U) (v : Fin n → Γ(X, U)) (i : Fin n) :
    X.resPi h n v i = (X.presheaf.map (homOfLE h).op).hom (v i) :=
  rfl

/-- Restriction of sections of `O_X^{⊕n}` along `U ≤ U` is the identity. -/
lemma resPi_refl {U : X.Opens} (v : Fin n → Γ(X, U)) : X.resPi le_rfl n v = v := by
  funext i
  simp [resPi]

/-- Restriction of sections of `O_X^{⊕n}` is compatible with composition of inclusions. -/
lemma resPi_resPi {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (v : Fin n → Γ(X, U)) :
    X.resPi hWV n (X.resPi hVU n v) = X.resPi (hWV.trans hVU) n v := by
  funext i
  simp only [resPi_apply]
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Restriction of sections of `O_X^{⊕n}` is additive. -/
lemma resPi_add {U V : X.Opens} (h : V ≤ U) (v w : Fin n → Γ(X, U)) :
    X.resPi h n (v + w) = X.resPi h n v + X.resPi h n w := by
  funext i
  simp [resPi]

/-- Restriction of sections of `O_X^{⊕n}` is semilinear over the restriction of functions:
scalars restrict along the structure sheaf. -/
lemma resPi_smul {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (v : Fin n → Γ(X, U)) :
    X.resPi h n (a • v) = (X.presheaf.map (homOfLE h).op).hom a • X.resPi h n v := by
  funext i
  simp [resPi]

/-- Restriction of sections of `O_X^{⊕n}` kills zero. -/
lemma resPi_zero {U V : X.Opens} (h : V ≤ U) : X.resPi h n (0 : Fin n → Γ(X, U)) = 0 := by
  funext i
  simp [resPi]

/-- Let `f : X ⟶ Y` be a morphism of schemes, `U` an open of `Y` and `V ≤ f⁻¹(U)` an open
of `X`. The componentwise pullback of sections of `O_Y^{⊕n}` over `U` to sections of
`O_X^{⊕n}` over `V`. -/
def Hom.appPi (f : X.Hom Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (v : Fin n → Γ(Y, U)) : Fin n → Γ(X, V) :=
  fun i ↦ (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom (v i))

@[simp]
lemma Hom.appPi_apply (f : X.Hom Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (v : Fin n → Γ(Y, U)) (i : Fin n) :
    f.appPi U h n v i = (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom (v i)) :=
  rfl

/-- Pullback of a vector of global sections is componentwise application of `appTop`. -/
lemma Hom.appPi_top (f : X.Hom Y) (v : Fin n → Γ(Y, ⊤)) :
    f.appPi (⊤ : Y.Opens) (by intro x _; trivial) n v =
      fun i ↦ f.appTop.hom (v i) := by
  funext i
  show (X.presheaf.map (𝟙 (⊤ : X.Opens)).op).hom ((f.app ⊤).hom (v i)) = _
  simp [Scheme.Hom.appTop]
  rfl
lemma Hom.appPi_add (f : X.Hom Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (v w : Fin n → Γ(Y, U)) : f.appPi U h n (v + w) = f.appPi U h n v + f.appPi U h n w := by
  funext i
  simp [Hom.appPi]

/-- Pullback of sections of `O_Y^{⊕n}` is semilinear over the pullback of functions. -/
lemma Hom.appPi_smul (f : X.Hom Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(Y, U)) (v : Fin n → Γ(Y, U)) :
    f.appPi U h n (a • v) =
      (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom a) • f.appPi U h n v := by
  funext i
  simp [Hom.appPi]

/-- Restricting a pulled-back section pulls it back along the composed inclusion. -/
lemma resPi_appPi (f : X.Hom Y) (U : Y.Opens) {V W : X.Opens} (hV : V ≤ f ⁻¹ᵁ U)
    (hWV : W ≤ V) (v : Fin n → Γ(Y, U)) :
    X.resPi hWV n (f.appPi U hV n v) = f.appPi U (hWV.trans hV) n v := by
  funext i
  simp only [resPi_apply, Hom.appPi_apply]
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Restriction carries a span into the span of the restricted generators. -/
lemma resPi_mem_span_image {U V : X.Opens} (hVU : V ≤ U) {S : Set (Fin n → Γ(X, U))}
    {z : Fin n → Γ(X, U)} (hz : z ∈ Submodule.span Γ(X, U) S) :
    X.resPi hVU n z ∈ Submodule.span Γ(X, V) (X.resPi hVU n '' S) := by
  induction hz using Submodule.span_induction with
  | mem z hm => exact Submodule.subset_span ⟨z, hm, rfl⟩
  | zero =>
    rw [resPi_zero]
    exact Submodule.zero_mem _
  | add z₁ z₂ _ _ ih₁ ih₂ =>
    rw [resPi_add]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul b z _ ih =>
    rw [resPi_smul]
    exact Submodule.smul_mem _ _ ih

/-- Pullback of sections along a composition of scheme morphisms is the composition of
the pullbacks. -/
lemma Hom.appPi_comp (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) (v : Fin n → Γ(Z, U)) :
    f.appPi V hW n (g.appPi U hV n v) =
      Hom.appPi (f ≫ g) U (hW.trans (f.preimage_mono hV)) n v := by
  funext i
  change (f.appLE V W hW).hom ((g.appLE U V hV).hom (v i)) =
    ((f ≫ g).appLE U W _).hom (v i)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- Pullback of sections absorbs a restriction on the source: pulling back the
restriction of a section equals pulling back the section itself. -/
lemma Hom.appPi_resPi (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ V) (v : Fin n → Γ(Y, U)) :
    f.appPi V hW n (Y.resPi hVU n v) =
      f.appPi U (hW.trans (f.preimage_mono hVU)) n v := by
  funext i
  change (f.appLE V W hW).hom ((Y.presheaf.map (homOfLE hVU).op).hom (v i)) =
    (f.appLE U W _).hom (v i)
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- Pullback of sections kills zero. -/
lemma Hom.appPi_zero (f : X ⟶ Y) (U : Y.Opens) {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    f.appPi U h n (0 : Fin n → Γ(Y, U)) = 0 := by
  funext i
  simp [Hom.appPi]

/-- Pullback of sections carries a span into the span of the pulled-back generators. -/
lemma Hom.appPi_mem_span_appPi (f : X ⟶ Y) {V : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ V) {S : Set (Fin n → Γ(Y, V))} {z : Fin n → Γ(Y, V)}
    (hz : z ∈ Submodule.span Γ(Y, V) S) :
    f.appPi V hW n z ∈ Submodule.span Γ(X, W) (f.appPi V hW n '' S) := by
  induction hz using Submodule.span_induction with
  | mem z hm => exact Submodule.subset_span ⟨z, hm, rfl⟩
  | zero =>
    rw [Hom.appPi_zero]
    exact Submodule.zero_mem _
  | add z₁ z₂ _ _ ih₁ ih₂ =>
    rw [Hom.appPi_add]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul c z _ ih =>
    rw [Hom.appPi_smul]
    exact Submodule.smul_mem _ _ ih

/-- Membership in the span of restrictions is preserved by further restriction. -/
lemma resPi_mem_span_resPi {U V V' : X.Opens} (hVU : V ≤ U) (hV'V : V' ≤ V)
    {W : Submodule Γ(X, U) (Fin n → Γ(X, U))} {z : Fin n → Γ(X, V)}
    (hz : z ∈ Submodule.span Γ(X, V) (X.resPi hVU n '' (W : Set (Fin n → Γ(X, U))))) :
    X.resPi hV'V n z ∈ Submodule.span Γ(X, V')
      (X.resPi (hV'V.trans hVU) n '' (W : Set (Fin n → Γ(X, U)))) := by
  induction hz using Submodule.span_induction with
  | mem z hm =>
    obtain ⟨w, hw, rfl⟩ := hm
    rw [resPi_resPi]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero =>
    rw [resPi_zero]
    exact Submodule.zero_mem _
  | add z₁ z₂ _ _ ih₁ ih₂ =>
    rw [resPi_add]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul b z _ ih =>
    rw [resPi_smul]
    exact Submodule.smul_mem _ _ ih

/-- A local–global principle for membership in a submodule: if for every maximal ideal
there is an element outside it carrying `v` into `W`, then `v ∈ W` (the ideal of
denominators is contained in no maximal ideal). -/
lemma _root_.Submodule.mem_of_forall_isMaximal_exists_smul_mem {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {W : Submodule A M} {v : M}
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ u : A, u ∉ P ∧ u • v ∈ W) : v ∈ W := by
  have hI : W.comap (LinearMap.toSpanSingleton A M v) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨u, hu, huv⟩ := h P hP
    exact hu (hle huv)
  simpa using (Ideal.eq_top_iff_one _).mp hI

/-- Clearing denominators: an element of the `B`-span of the image of a submodule
`W ≤ A^{⊕n}` in a localization `B` of `A` away from `g` is, after scaling by a power of
`g`, the image of an element of `W`. -/
lemma _root_.Submodule.exists_pow_smul_eq_algebraMap_of_mem_span {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] {g : A} [IsLocalization.Away g B] {n : ℕ}
    {W : Submodule A (Fin n → A)} {z : Fin n → B}
    (hz : z ∈ Submodule.span B
      ((fun v (i : Fin n) ↦ algebraMap A B (v i)) '' (W : Set (Fin n → A)))) :
    ∃ (k : ℕ) (w : Fin n → A), w ∈ W ∧
      algebraMap A B (g ^ k) • z = fun i ↦ algebraMap A B (w i) := by
  induction hz using Submodule.span_induction with
  | mem z hzmem =>
    obtain ⟨w, hw, rfl⟩ := hzmem
    refine ⟨0, w, hw, ?_⟩
    funext i
    simp
  | zero =>
    refine ⟨0, 0, Submodule.zero_mem _, ?_⟩
    funext i
    simp
  | add z₁ z₂ _ _ ih₁ ih₂ =>
    obtain ⟨k₁, w₁, hw₁, e₁⟩ := ih₁
    obtain ⟨k₂, w₂, hw₂, e₂⟩ := ih₂
    refine ⟨k₁ + k₂, g ^ k₂ • w₁ + g ^ k₁ • w₂,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw₁) (Submodule.smul_mem _ _ hw₂), ?_⟩
    funext i
    have h₁ := congrFun e₁ i
    have h₂ := congrFun e₂ i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_add, map_mul, map_pow]
      at h₁ h₂ ⊢
    rw [← h₁, ← h₂]
    ring
  | smul b z _ ih =>
    obtain ⟨k, w, hw, e⟩ := ih
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := Submonoid.powers g) b
    obtain ⟨m, hm⟩ := s.2
    refine ⟨k + m, a • w, Submodule.smul_mem _ _ hw, ?_⟩
    funext i
    have h₀ := congrFun e i
    have hb : algebraMap A B g ^ m * b = algebraMap A B a := by
      rw [← map_pow, show g ^ m = (s : A) from hm, mul_comm]
      exact hs
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at h₀ ⊢
    rw [pow_add, ← h₀, ← hb]
    ring

/-- Let `B` be the localization of a ring `A` away from one element. For submodules
`K, L ≤ Aⁿ`, the `B`-span of the componentwise image of `K ⊓ L` is the intersection of
the spans of the componentwise images of `K` and `L`. -/
lemma _root_.Submodule.span_image_inf_of_isLocalization_away
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {g : A}
    [IsLocalization.Away g B] {n : ℕ} (K L : Submodule A (Fin n → A)) :
    Submodule.span B ((fun v i ↦ algebraMap A B (v i)) ''
        ((K ⊓ L : Submodule A (Fin n → A)) : Set (Fin n → A))) =
      Submodule.span B ((fun v i ↦ algebraMap A B (v i)) ''
        (K : Set (Fin n → A))) ⊓
      Submodule.span B ((fun v i ↦ algebraMap A B (v i)) ''
        (L : Set (Fin n → A))) := by
  classical
  let φ : (Fin n → A) → (Fin n → B) := fun v i ↦ algebraMap A B (v i)
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨Submodule.subset_span ⟨w, hw.1, rfl⟩,
      Submodule.subset_span ⟨w, hw.2, rfl⟩⟩
  · intro z hz
    obtain ⟨k, wK, hwK, hK⟩ :=
      Submodule.exists_pow_smul_eq_algebraMap_of_mem_span (g := g) hz.1
    obtain ⟨l, wL, hwL, hL⟩ :=
      Submodule.exists_pow_smul_eq_algebraMap_of_mem_span (g := g) hz.2
    have heq : φ (g ^ l • wK) = φ (g ^ k • wL) := by
      funext i
      have hKi := congrFun hK i
      have hLi := congrFun hL i
      simp only [φ, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hKi hLi ⊢
      rw [← hKi, ← hLi]
      ring
    have heqComp : ∀ i, algebraMap A B ((g ^ l • wK) i) =
        algebraMap A B ((g ^ k • wL) i) :=
      fun i ↦ congrFun heq i
    choose s hs using fun i ↦
      (IsLocalization.exists_of_eq (M := Submonoid.powers g) (heqComp i))
    choose m hm using fun i ↦ (s i).2
    let d : ℕ := ∑ i, m i
    have hsource : g ^ d • (g ^ l • wK) = g ^ d • (g ^ k • wL) := by
      funext i
      have hi := hs i
      rw [← hm i] at hi
      simp only [Pi.smul_apply, smul_eq_mul]
      dsimp [d]
      let e : ℕ := ∑ x ∈ Finset.univ.erase i, m x
      calc
        g ^ (∑ x, m x) * (g ^ l * wK i) =
            g ^ e * (g ^ m i * (g ^ l * wK i)) := by
          dsimp [e]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), pow_add]
          ring
        _ = g ^ e * (g ^ m i * (g ^ k * wL i)) := congrArg (g ^ e * ·) hi
        _ = g ^ (∑ x, m x) * (g ^ k * wL i) := by
          dsimp [e]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), pow_add]
          ring
    let w : Fin n → A := g ^ d • (g ^ l • wK)
    have hwKi : w ∈ K :=
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hwK)
    have hwLi : w ∈ L := by
      rw [show w = g ^ d • (g ^ k • wL) from hsource]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hwL)
    have hscale : algebraMap A B (g ^ (d + l + k)) • z = φ w := by
      funext i
      have hKi := congrFun hK i
      simp only [φ, w, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hKi ⊢
      rw [pow_add, pow_add, ← hKi]
      ring
    have hwSpan : φ w ∈ Submodule.span B
        (φ '' (((K ⊓ L : Submodule A (Fin n → A))) : Set (Fin n → A))) :=
      Submodule.subset_span ⟨w, ⟨hwKi, hwLi⟩, rfl⟩
    have hscaled : algebraMap A B (g ^ (d + l + k)) • z ∈ Submodule.span B
        (φ '' (((K ⊓ L : Submodule A (Fin n → A))) : Set (Fin n → A))) := by
      rwa [hscale]
    obtain ⟨u, hu⟩ := IsLocalization.map_units (M := Submonoid.powers g) B
      ⟨g ^ (d + l + k), d + l + k, rfl⟩
    have hinv := Submodule.smul_mem
      (Submodule.span B
        (φ '' (((K ⊓ L : Submodule A (Fin n → A))) : Set (Fin n → A))))
      (↑(u⁻¹) : B) hscaled
    rw [← hu, smul_smul, Units.inv_mul, one_smul] at hinv
    exact hinv

/-- The componentwise map `Aⁿ → Bⁿ` induced by an algebra structure. -/
def _root_.Submodule.algebraMapPi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (w : Fin n → A) : Fin n → B :=
  fun i ↦ algebraMap A B (w i)

/-- A ring equivalence applied componentwise to a finite free module, as a semilinear
equivalence. -/
def _root_.RingEquiv.piSemilinearEquiv {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (n : ℕ) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
    (Fin n → R) ≃ₛₗ[(↑e : R →+* S)] (Fin n → S) :=
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  { toFun := fun w i ↦ e (w i)
    invFun := fun w i ↦ e.symm (w i)
    left_inv := fun w ↦ by ext i; simp
    right_inv := fun w ↦ by ext i; simp
    map_add' := fun x y ↦ by ext i; simp
    map_smul' := fun r x ↦ by ext i; simp [smul_eq_mul] }

@[simp]
lemma _root_.RingEquiv.piSemilinearEquiv_apply
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (n : ℕ)
    (w : Fin n → R) (i : Fin n) :
    e.piSemilinearEquiv n w i = e (w i) :=
  rfl

@[simp]
lemma _root_.RingEquiv.piSemilinearEquiv_symm_apply
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (n : ℕ)
    (w : Fin n → S) (i : Fin n) :
    (e.piSemilinearEquiv n).symm w i = e.symm (w i) :=
  rfl

/-- Transport a submodule of a finite free module componentwise across a ring
equivalence. -/
def _root_.Submodule.mapPiRingEquiv
    {R S : Type*} [Semiring R] [Semiring S] {n : ℕ}
    (e : R ≃+* S) (K : Submodule R (Fin n → R)) : Submodule S (Fin n → S) :=
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  K.map (e.piSemilinearEquiv n).toLinearMap

@[simp]
lemma _root_.Submodule.mem_mapPiRingEquiv
    {R S : Type*} [Semiring R] [Semiring S] {n : ℕ}
    (e : R ≃+* S) (K : Submodule R (Fin n → R)) (w : Fin n → S) :
    w ∈ K.mapPiRingEquiv e ↔ (fun i ↦ e.symm (w i)) ∈ K := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  rw [Submodule.mapPiRingEquiv, Submodule.mem_map_equiv]
  rfl

@[simp]
lemma _root_.Submodule.mapPiRingEquiv_symm_mapPiRingEquiv
    {R S : Type*} [Semiring R] [Semiring S] {n : ℕ}
    (e : R ≃+* S) (K : Submodule R (Fin n → R)) :
    (K.mapPiRingEquiv e).mapPiRingEquiv e.symm = K := by
  ext w
  simp

@[simp]
lemma _root_.Submodule.mapPiRingEquiv_refl
    {R : Type*} [CommRing R] {n : ℕ} (K : Submodule R (Fin n → R)) :
    K.mapPiRingEquiv (RingEquiv.refl R) = K := by
  ext w
  simp

/-- Componentwise transport across a ring equivalence commutes with span. -/
lemma _root_.Submodule.mapPiRingEquiv_span
    {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (e : R ≃+* S) (s : Set (Fin n → R)) :
    (Submodule.span R s).mapPiRingEquiv e =
      Submodule.span S ((fun w i ↦ e (w i)) '' s) := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  rw [Submodule.mapPiRingEquiv, Submodule.map_span]
  congr 1

/-- The contraction of a submodule of `Bⁿ` along a ring map `A → B`. -/
def _root_.Submodule.comapPi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (N : Submodule B (Fin n → B)) : Submodule A (Fin n → A) :=
  (N.restrictScalars A).comap
    ({ toFun := fun w => Submodule.algebraMapPi w
       map_add' := by intros; funext; simp [Submodule.algebraMapPi]
       map_smul' := by
         intros
         funext
         simp [Submodule.algebraMapPi, smul_eq_mul, Algebra.smul_def] } :
      (Fin n → A) →ₗ[A] (Fin n → B))

@[simp]
lemma _root_.Submodule.mem_comapPi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (N : Submodule B (Fin n → B)) (w : Fin n → A) :
    w ∈ N.comapPi ↔ (fun i ↦ algebraMap A B (w i)) ∈ N := by
  change Submodule.algebraMapPi w ∈ N ↔ _
  rfl

/-- Contraction of finite-free submodules is natural under a commutative square of ring
equivalences. -/
lemma _root_.Submodule.mapPiRingEquiv_comapPi
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] {n : ℕ}
    (eA : A ≃+* A') (eB : B ≃+* B')
    (h : ∀ x : A, eB (algebraMap A B x) = algebraMap A' B' (eA x))
    (N : Submodule B (Fin n → B)) :
    (N.comapPi (A := A)).mapPiRingEquiv eA =
      (N.mapPiRingEquiv eB).comapPi (A := A') := by
  ext w
  rw [Submodule.mem_mapPiRingEquiv, Submodule.mem_comapPi]
  change (fun i ↦ algebraMap A B (eA.symm (w i))) ∈ N ↔
    (fun i ↦ algebraMap A' B' (w i)) ∈ N.mapPiRingEquiv eB
  rw [Submodule.mem_mapPiRingEquiv]
  have heq : (fun i ↦ algebraMap A B (eA.symm (w i))) =
      fun i ↦ eB.symm (algebraMap A' B' (w i)) := by
    funext i
    apply eB.injective
    rw [eB.apply_symm_apply, h]
    simp
  rw [heq]

/-- A submodule of a finite free module over a localization is generated by the
localization of its contraction to the original ring. -/
lemma _root_.Submodule.span_image_comapPi_of_isLocalization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] {n : ℕ}
    (N : Submodule B (Fin n → B)) :
    Submodule.span B ((fun w i ↦ algebraMap A B (w i)) ''
      (N.comapPi (A := A) : Set (Fin n → A))) = N := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ ⟨w, hw, hweq⟩ ↦ hweq ▸ (N.mem_comapPi w).mp hw
  · intro z hz
    choose x hx using fun i ↦ IsLocalization.surj M (z i)
    let a : Fin n → A := fun i ↦ (x i).1
    let s : Fin n → M := fun i ↦ (x i).2
    have hs : ∀ i, z i * algebraMap A B (s i : A) = algebraMap A B (a i) :=
      fun i ↦ hx i
    let t : A := ∏ i, (s i : A)
    let w : Fin n → A := fun i ↦
      (∏ j ∈ Finset.univ.erase i, (s j : A)) * a i
    have htM : t ∈ M := by
      dsimp [t]
      exact Submonoid.prod_mem M fun i _ ↦ (s i).2
    have hscale : algebraMap A B t • z = fun i ↦ algebraMap A B (w i) := by
      funext i
      have hi := hs i
      simp only [Pi.smul_apply, smul_eq_mul]
      dsimp [t, w]
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), map_mul,
        map_mul]
      rw [show Finset.univ \ {i} = Finset.univ.erase i by ext; simp]
      calc
        algebraMap A B (s i : A) *
            algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) * z i =
            algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) *
              (z i * algebraMap A B (s i : A)) := by ring
        _ = algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) *
              algebraMap A B (a i) := congrArg
                (algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) * ·) hi
    have hwN : (fun i ↦ algebraMap A B (w i)) ∈ N := by
      rw [← hscale]
      exact N.smul_mem _ hz
    let P := Submodule.span B ((fun w i ↦ algebraMap A B (w i)) ''
      (N.comapPi (A := A) : Set (Fin n → A)))
    have hwSpan : (fun i ↦ algebraMap A B (w i)) ∈ P :=
      Submodule.subset_span ⟨w, (N.mem_comapPi w).mpr hwN, rfl⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B ⟨t, htM⟩
    have hinv : (↑(u⁻¹) : B) • (fun i ↦ algebraMap A B (w i)) ∈ P :=
      P.smul_mem _ hwSpan
    rw [← hscale, ← hu, smul_smul, Units.inv_mul, one_smul] at hinv
    exact hinv

/-- The easy inclusion in base change for localization--contraction: after changing
scalars from `A` to `C`, vectors whose image in `B` lies in `N` still lie in the
contraction from any common `A`-algebra `D` of the `D`-span of `N`. -/
lemma _root_.Submodule.span_image_comapPi_le_comapPi_span_image
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] {n : ℕ}
    (N : Submodule B (Fin n → B)) :
    Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
        (N.comapPi (A := A) : Set (Fin n → A))) ≤
      (Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
        (N : Set (Fin n → B)))).comapPi (A := C) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change (fun i ↦ algebraMap C D (algebraMap A C (w i))) ∈
    Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
      (N : Set (Fin n → B)))
  apply Submodule.subset_span
  refine ⟨fun i ↦ algebraMap A B (w i), (N.mem_comapPi w).mp hw, ?_⟩
  funext i
  change algebraMap B D (algebraMap A B (w i)) =
    algebraMap C D (algebraMap A C (w i))
  rw [← IsScalarTower.algebraMap_apply A B D,
    ← IsScalarTower.algebraMap_apply A C D]

/-- Contraction from a localization away from `g` is saturated under powers of `g`. -/
lemma _root_.Submodule.pow_smul_mem_comapPi_iff_of_isLocalization_away
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {g : A} [IsLocalization.Away g B] {n : ℕ}
    (N : Submodule B (Fin n → B)) (k : ℕ) (w : Fin n → A) :
    g ^ k • w ∈ N.comapPi ↔ w ∈ N.comapPi := by
  rw [N.mem_comapPi, N.mem_comapPi]
  have hu : IsUnit (algebraMap A B (g ^ k)) := by
    rw [map_pow]
    exact IsLocalization.Away.algebraMap_pow_isUnit (R := A) (S := B) (x := g) k
  let v : Fin n → B := fun i ↦ algebraMap A B (w i)
  have heq : (fun i ↦ algebraMap A B ((g ^ k • w) i)) =
      algebraMap A B (g ^ k) • v := by
    funext i
    simp [v, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact N.smul_mem_iff_of_isUnit hu

/-- A finite vector over a localization can be written with one common denominator. -/
lemma _root_.Submodule.exists_s_smul_eq_algebraMapPi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] {n : ℕ} (z : Fin n → B) :
    ∃ (s : M) (w : Fin n → A),
      algebraMap A B (s : A) • z = fun i ↦ algebraMap A B (w i) := by
  classical
  choose x hx using fun i ↦ IsLocalization.surj M (z i)
  let a : Fin n → A := fun i ↦ (x i).1
  let s : Fin n → M := fun i ↦ (x i).2
  let t : M := ∏ i, s i
  let w : Fin n → A := fun i ↦
    (∏ j ∈ Finset.univ.erase i, (s j : A)) * a i
  refine ⟨t, w, ?_⟩
  funext i
  have hi : z i * algebraMap A B (s i : A) = algebraMap A B (a i) := hx i
  simp only [Pi.smul_apply, smul_eq_mul]
  dsimp [t, w]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd, map_mul]
  rw [show Finset.univ \ {i} = Finset.univ.erase i by ext; simp]
  calc
    algebraMap A B (s i : A) *
        algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) * z i =
        algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) *
          (z i * algebraMap A B (s i : A)) := by ring
    _ = algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) *
          algebraMap A B (a i) := congrArg
            (algebraMap A B (∏ j ∈ Finset.univ.erase i, (s j : A)) * ·) hi

/-- Equality of two finite vectors after localization can be cleared by one common
denominator. -/
lemma _root_.Submodule.exists_s_smul_eq_of_algebraMapPi_eq
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] {n : ℕ} {v w : Fin n → A}
    (h : (fun i ↦ algebraMap A B (v i)) = fun i ↦ algebraMap A B (w i)) :
    ∃ s : M, (s : A) • v = (s : A) • w := by
  classical
  choose s hs using fun i ↦ IsLocalization.exists_of_eq (M := M) (congrFun h i)
  let t : M := ∏ i, s i
  refine ⟨t, ?_⟩
  funext i
  have hi := hs i
  let e : A := ∏ j ∈ Finset.univ.erase i, (s j : A)
  have ht : (t : A) = (s i : A) * e := by
    dsimp [t, e]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [Submonoid.coe_mul, Submonoid.coe_finsetProd]
    congr 1
    rw [show Finset.univ \ {i} = Finset.univ.erase i by ext; simp]
  simp only [Pi.smul_apply, smul_eq_mul, ht]
  calc
    ((s i : A) * e) * v i = e * ((s i : A) * v i) := by ring
    _ = e * ((s i : A) * w i) := congrArg (e * ·) hi
    _ = ((s i : A) * e) * w i := by ring

/-- Power-saturation of a submodule is preserved when it is extended to a localization
away from a second element. -/
lemma _root_.Submodule.pow_smul_mem_span_image_iff_of_saturated
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {f g : A} [IsLocalization.Away f C] {n : ℕ}
    (W : Submodule A (Fin n → A))
    (hsat : ∀ (k : ℕ) (w : Fin n → A), g ^ k • w ∈ W ↔ w ∈ W)
    (k : ℕ) (z : Fin n → C) :
    algebraMap A C (g ^ k) • z ∈
        Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
          (W : Set (Fin n → A))) ↔
      z ∈ Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
        (W : Set (Fin n → A))) := by
  classical
  let P := Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
    (W : Set (Fin n → A)))
  constructor
  · intro hz
    obtain ⟨l, w, hw, he⟩ :=
      Submodule.exists_pow_smul_eq_algebraMap_of_mem_span (g := f) hz
    obtain ⟨s, a, ha⟩ :=
      Submodule.exists_s_smul_eq_algebraMapPi (Submonoid.powers f) z
    obtain ⟨r, hr⟩ := s.2
    have heq : (fun i ↦ algebraMap A C (((f ^ l * g ^ k) • a) i)) =
        fun i ↦ algebraMap A C ((f ^ r • w) i) := by
      funext i
      have hei := congrFun he i
      have hai := congrFun ha i
      rw [← hr] at hai
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hei hai ⊢
      calc
        algebraMap A C f ^ l * algebraMap A C g ^ k * algebraMap A C (a i) =
            algebraMap A C f ^ r *
              (algebraMap A C f ^ l * (algebraMap A C g ^ k * z i)) := by
                rw [← hai]
                ring
        _ = algebraMap A C f ^ r * algebraMap A C (w i) :=
          congrArg (algebraMap A C f ^ r * ·) hei
    obtain ⟨t, ht⟩ := Submodule.exists_s_smul_eq_of_algebraMapPi_eq
      (Submonoid.powers f) heq
    let b : Fin n → A := ((t : A) * f ^ l) • a
    have hvec : g ^ k • b = ((t : A) * f ^ r) • w := by
      funext i
      have hti := congrFun ht i
      simp only [Pi.smul_apply, smul_eq_mul] at hti ⊢
      dsimp [b]
      calc
        g ^ k * ((t : A) * f ^ l * a i) =
            (t : A) * ((f ^ l * g ^ k) * a i) := by ring
        _ = (t : A) * (f ^ r * w i) := hti
        _ = ((t : A) * f ^ r) * w i := by ring
    have hgb : g ^ k • b ∈ W := by
      rw [hvec]
      exact W.smul_mem _ hw
    have hb : b ∈ W := (hsat k b).mp hgb
    have hbP : (fun i ↦ algebraMap A C (b i)) ∈ P :=
      Submodule.subset_span ⟨b, hb, rfl⟩
    have hu : IsUnit (algebraMap A C ((t : A) * f ^ l)) := by
      rw [map_mul, map_pow]
      exact (IsLocalization.map_units C t).mul
        (IsLocalization.Away.algebraMap_pow_isUnit (R := A) (S := C) (x := f) l)
    have hscaled : algebraMap A C ((t : A) * f ^ l) •
        (fun i ↦ algebraMap A C (a i)) ∈ P := by
      convert hbP using 1
      funext i
      simp [b, Pi.smul_apply, smul_eq_mul]
    have haP : (fun i ↦ algebraMap A C (a i)) ∈ P :=
      (P.smul_mem_iff_of_isUnit hu).mp hscaled
    have hsunit : IsUnit (algebraMap A C (s : A)) := IsLocalization.map_units C s
    apply (P.smul_mem_iff_of_isUnit hsunit).mp
    rw [ha]
    exact haP
  · exact fun hz ↦ P.smul_mem _ hz

/-- The denominator-clearing inclusion in base change for localization--contraction. -/
lemma _root_.Submodule.comapPi_span_image_le_span_image_comapPi_of_isLocalization_away
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    (f g : A) [IsLocalization.Away g B] [IsLocalization.Away f C]
    [IsLocalization.Away (algebraMap A B f) D]
    [IsLocalization.Away (algebraMap A C g) D] {n : ℕ}
    (N : Submodule B (Fin n → B)) :
    (Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
        (N : Set (Fin n → B)))).comapPi (A := C) ≤
      Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
        (N.comapPi (A := A) : Set (Fin n → A))) := by
  classical
  let W := N.comapPi (A := A)
  let P := Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
    (W : Set (Fin n → A)))
  intro z hz
  change (fun i ↦ algebraMap C D (z i)) ∈
    Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
      (N : Set (Fin n → B))) at hz
  obtain ⟨k, w, hw, he⟩ :=
    Submodule.exists_pow_smul_eq_algebraMap_of_mem_span
      (g := algebraMap A B f) hz
  obtain ⟨s, a, ha⟩ :=
    Submodule.exists_s_smul_eq_algebraMapPi (Submonoid.powers g) w
  obtain ⟨l, hl⟩ := s.2
  have haW : a ∈ W := by
    change a ∈ N.comapPi
    rw [N.mem_comapPi]
    rw [← ha]
    exact N.smul_mem _ hw
  have heqD :
      (fun i ↦ algebraMap C D
        ((algebraMap A C (g ^ l * f ^ k) • z) i)) =
        fun i ↦ algebraMap C D (algebraMap A C (a i)) := by
    funext i
    have hei := congrFun he i
    have hai := congrFun ha i
    rw [← hl] at hai
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hei hai ⊢
    have hC (x : A) : algebraMap C D (algebraMap A C x) = algebraMap A D x :=
      (IsScalarTower.algebraMap_apply A C D x).symm
    have hB (x : A) : algebraMap B D (algebraMap A B x) = algebraMap A D x :=
      (IsScalarTower.algebraMap_apply A B D x).symm
    simp_rw [hC, hB] at hei hai ⊢
    calc
      algebraMap A D g ^ l * algebraMap A D f ^ k * algebraMap C D (z i) =
          algebraMap A D g ^ l * algebraMap B D (w i) := by
            rw [← hei]
            ring
      _ = algebraMap A D (a i) := by
        have haiD := congrArg (algebraMap B D) hai
        simpa only [map_mul, map_pow, hB] using haiD
  obtain ⟨t, ht⟩ := Submodule.exists_s_smul_eq_of_algebraMapPi_eq
    (Submonoid.powers (algebraMap A C g)) heqD
  obtain ⟨m, hm⟩ := t.2
  have hright : (t : C) • (fun i ↦ algebraMap A C (a i)) ∈ P := by
    apply P.smul_mem
    exact Submodule.subset_span ⟨a, haW, rfl⟩
  have hleft : (t : C) • (algebraMap A C (g ^ l * f ^ k) • z) ∈ P := by
    rw [ht]
    exact hright
  have hgf : algebraMap A C (g ^ (m + l)) •
      (algebraMap A C (f ^ k) • z) ∈ P := by
    convert hleft using 1
    rw [← hm]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, pow_add]
    ring
  have hg : algebraMap A C (g ^ (m + l)) • z ∈ P := by
    have hu : IsUnit (algebraMap A C (f ^ k)) := by
      rw [map_pow]
      exact IsLocalization.Away.algebraMap_pow_isUnit (R := A) (S := C) (x := f) k
    apply (P.smul_mem_iff_of_isUnit hu).mp
    convert hgf using 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact (Submodule.pow_smul_mem_span_image_iff_of_saturated
    (f := f) (g := g) W
    (fun r v ↦ Submodule.pow_smul_mem_comapPi_iff_of_isLocalization_away N r v)
    (m + l) z).mp hg

/-- Localization--contraction commutes with localization in the transverse element.
This is the algebraic Beck--Chevalley identity for two affine basic opens. -/
lemma _root_.Submodule.span_image_comapPi_eq_comapPi_span_image_of_isLocalization_away
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    (f g : A) [IsLocalization.Away g B] [IsLocalization.Away f C]
    [IsLocalization.Away (algebraMap A B f) D]
    [IsLocalization.Away (algebraMap A C g) D] {n : ℕ}
    (N : Submodule B (Fin n → B)) :
    Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
        (N.comapPi (A := A) : Set (Fin n → A))) =
      (Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
        (N : Set (Fin n → B)))).comapPi (A := C) := by
  apply le_antisymm
  · exact Submodule.span_image_comapPi_le_comapPi_span_image N
  · exact Submodule.comapPi_span_image_le_span_image_comapPi_of_isLocalization_away
      f g N

/-- Ambient-section form of the algebraic Beck--Chevalley identity on the intersection
`D(fg) = D(f) ∩ D(g)` of two basic opens of an affine scheme. -/
lemma span_resPi_comapPi_eq_comapPi_span_resPi_basicOpen [IsAffine X]
    (f g : Γ(X, ⊤)) (N : Submodule Γ(X, X.basicOpen g)
      (Fin n → Γ(X, X.basicOpen g))) :
    let A := Γ(X, ⊤)
    let B := Γ(X, X.basicOpen g)
    let C := Γ(X, X.basicOpen f)
    let D := Γ(X, X.basicOpen (f * g))
    letI : Algebra A B :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI : Algebra A C :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    letI : Algebra A D :=
      (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom.toAlgebra
    letI : Algebra B D :=
      (X.presheaf.map (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom.toAlgebra
    letI : Algebra C D :=
      (X.presheaf.map (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom.toAlgebra
    Submodule.span C ((fun w i ↦ algebraMap A C (w i)) ''
        (N.comapPi (A := A) : Set (Fin n → A))) =
      (Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
      (N : Set (Fin n → B)))).comapPi (A := C) := by
  dsimp only
  letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen (f * g)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom.toAlgebra
  letI : Algebra Γ(X, X.basicOpen g) Γ(X, X.basicOpen (f * g)) :=
    (X.presheaf.map
      (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom.toAlgebra
  letI : Algebra Γ(X, X.basicOpen f) Γ(X, X.basicOpen (f * g)) :=
    (X.presheaf.map
      (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen g)
      Γ(X, X.basicOpen (f * g)) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom x =
      (X.presheaf.map
        (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom x)
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  letI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen f)
      Γ(X, X.basicOpen (f * g)) := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom x =
      (X.presheaf.map
        (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x)
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
    (isAffineOpen_top X).isLocalization_basicOpen g
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    (isAffineOpen_top X).isLocalization_basicOpen f
  haveI : IsLocalization.Away
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) f)
      Γ(X, X.basicOpen (f * g)) := by
    have hle : X.basicOpen (f * g) ≤ X.basicOpen g :=
      (X.basicOpen_mul f g).le.trans inf_le_right
    have heq : X.basicOpen (f * g) = X.basicOpen
        (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) f) := by
      rw [show algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) f =
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f from rfl,
      X.basicOpen_res, X.basicOpen_mul, inf_comm]
    exact ((isAffineOpen_top X).basicOpen g).isLocalization_of_eq_basicOpen
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g) f) (homOfLE hle) heq
  haveI : IsLocalization.Away
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) g)
      Γ(X, X.basicOpen (f * g)) := by
    have hle : X.basicOpen (f * g) ≤ X.basicOpen f :=
      (X.basicOpen_mul f g).le.trans inf_le_left
    have heq : X.basicOpen (f * g) = X.basicOpen
        (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) g) := by
      rw [show algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) g =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom g from rfl,
      X.basicOpen_res, X.basicOpen_mul]
    exact ((isAffineOpen_top X).basicOpen f).isLocalization_of_eq_basicOpen
      (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) g) (homOfLE hle) heq
  exact Submodule.span_image_comapPi_eq_comapPi_span_image_of_isLocalization_away
    f g N

/-- **Local–global principle over an affine open**: membership of a section of
`O_X^{⊕n}` over an affine open `U` in a submodule `W` of the sections can be checked on
a basic-open cover, where it becomes membership in the span of the restrictions of `W`.
This is the quasi-coherence engine behind the pullback of submodule sheaves. -/
lemma mem_of_forall_exists_basicOpen_resPi_mem_span {U : X.affineOpens}
    {W : Submodule Γ(X, U.1) (Fin n → Γ(X, U.1))} {v : Fin n → Γ(X, U.1)}
    (h : ∀ x ∈ U.1, ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧
      X.resPi (X.basicOpen_le g) n v ∈ Submodule.span Γ(X, X.basicOpen g)
        (X.resPi (X.basicOpen_le g) n '' (W : Set (Fin n → Γ(X, U.1))))) :
    v ∈ W := by
  refine Submodule.mem_of_forall_isMaximal_exists_smul_mem fun P hP ↦ ?_
  have hxU : U.2.fromSpec ⟨P, hP.isPrime⟩ ∈ U.1 := by
    rw [← SetLike.mem_coe, ← U.2.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨g, hxg, hspan⟩ := h (U.2.fromSpec ⟨P, hP.isPrime⟩) hxU
  haveI := U.2.isLocalization_basicOpen g
  have hgP : g ∉ P := by
    have h2 : (⟨P, hP.isPrime⟩ : PrimeSpectrum Γ(X, U.1)) ∈
        U.2.fromSpec ⁻¹ᵁ X.basicOpen g := hxg
    rw [U.2.fromSpec_preimage_basicOpen] at h2
    exact (PrimeSpectrum.mem_basicOpen g _).mp h2
  have hz : (fun i ↦ algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) (v i)) ∈
      Submodule.span Γ(X, X.basicOpen g)
        ((fun w (i : Fin n) ↦ algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) (w i)) ''
          (W : Set (Fin n → Γ(X, U.1)))) := hspan
  obtain ⟨k, w, hw, he⟩ := Submodule.exists_pow_smul_eq_algebraMap_of_mem_span (g := g) hz
  have hzero : ∀ i, algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) (g ^ k * v i - w i) = 0 := by
    intro i
    have hei := congrFun he i
    simp only [Pi.smul_apply, smul_eq_mul] at hei
    rw [map_sub, map_mul, hei, sub_self]
  choose s hs using fun i ↦
    (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp (hzero i)
  choose m hm using fun i ↦ (s i).2
  refine ⟨g ^ (k + ∑ j, m j), fun hmem ↦ hgP (hP.isPrime.mem_of_pow_mem _ hmem), ?_⟩
  have hvw : g ^ (k + ∑ j, m j) • v = g ^ (∑ j, m j) • w := by
    funext i
    have h0 := hs i
    rw [← hm i] at h0
    have h1 : g ^ (∑ j, m j) * (g ^ k * v i - w i) = 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), pow_add, mul_assoc, h0, mul_zero]
    have h2 : g ^ (k + ∑ j, m j) * v i - g ^ (∑ j, m j) * w i =
        g ^ (∑ j, m j) * (g ^ k * v i - w i) := by ring
    have h3 : g ^ (k + ∑ j, m j) * v i - g ^ (∑ j, m j) * w i = 0 := by rw [h2, h1]
    simpa [sub_eq_zero] using h3
  rw [hvw]
  exact W.smul_mem _ hw

/-- Let `X` be a scheme. A structure containing the data of a quasi-coherent submodule sheaf
`K ⊆ O_X^{⊕n}` of the trivial rank-`n` module, consisting of

1. a submodule `K(U) ≤ Γ(X, U)^{⊕n}` for every affine open `U`, and
2. a proof that `K(D(f))` is the localization of `K(U)`, i.e. spanned by the restriction of
   `K(U)`, for every affine open `U` and section `f : Γ(X, U)`.

This mirrors `AlgebraicGeometry.Scheme.IdealSheafData` (the case of a submodule sheaf of
`O_X` itself) and is the strict, universe-small encoding of "a quasi-coherent subsheaf of
`O_X^{⊕n}`" used to define the Grassmannian and Quot functors of Chapter 2 of *Stacks and
Moduli*. -/
structure SubmoduleSheafData (X : Scheme.{u}) (n : ℕ) : Type u where
  /-- The component of the submodule sheaf at an affine open. -/
  submodule : ∀ U : X.affineOpens, Submodule Γ(X, U.1) (Fin n → Γ(X, U.1))
  /-- Compatibility: on a basic open `D(f) ⊆ U`, the submodule is the localization of the
  one on `U`, i.e. the span of its componentwise restriction. -/
  span_resPi_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
    Submodule.span Γ(X, (X.affineBasicOpen f).1)
      (X.resPi (show (X.affineBasicOpen f).1 ≤ U.1 from X.basicOpen_le f) n ''
        (submodule U : Set (Fin n → Γ(X, U.1)))) =
      submodule (X.affineBasicOpen f)

namespace SubmoduleSheafData

/-- On an affine scheme, a submodule of the finite free module of global sections
defines quasi-coherent submodule data by localization to every affine open. -/
def ofAffineSubmodule [IsAffine X]
    (W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤))) : X.SubmoduleSheafData n where
  submodule U := Submodule.span Γ(X, U.1)
    (X.resPi (show U.1 ≤ (⊤ : X.Opens) from le_top) n ''
      (W : Set (Fin n → Γ(X, ⊤))))
  span_resPi_basicOpen := by
    intro U f
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact resPi_mem_span_resPi le_top (X.basicOpen_le f) hz
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      apply Submodule.subset_span
      refine ⟨X.resPi le_top n w, Submodule.subset_span ⟨w, hw, rfl⟩, ?_⟩
      rw [resPi_resPi]

/-- The global component of the affine submodule datum generated by `W` is `W` itself. -/
@[simp]
lemma ofAffineSubmodule_submodule_top [IsAffine X]
    (W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤))) :
    (ofAffineSubmodule W).submodule ⟨⊤, isAffineOpen_top X⟩ = W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    simpa only [resPi_refl] using hw
  · intro w hw
    exact Submodule.subset_span ⟨w, hw, by rw [resPi_refl]⟩

@[ext]
protected lemma ext {K L : X.SubmoduleSheafData n} (h : K.submodule = L.submodule) :
    K = L := by
  cases K
  cases L
  congr

/-- On an empty scheme there is only one quasi-coherent submodule datum. -/
instance [IsEmpty X] : Subsingleton (X.SubmoduleSheafData n) := by
  constructor
  intro K L
  apply SubmoduleSheafData.ext
  funext U
  exact Subsingleton.elim _ _

instance : PartialOrder (X.SubmoduleSheafData n) :=
  PartialOrder.lift SubmoduleSheafData.submodule fun _ _ ↦ SubmoduleSheafData.ext

/-- Inclusion of quasi-coherent submodule data can be checked on every affine open. -/
lemma le_def {K L : X.SubmoduleSheafData n} :
    K ≤ L ↔ ∀ U, K.submodule U ≤ L.submodule U :=
  Iff.rfl

/-- The span over the target ring of the additive image of a supremum of submodules
is the supremum of the spans of the images. -/
private lemma _root_.Submodule.span_image_iSup_of_addMonoidHom
    {ι : Sort*} {A B M N : Type*} [Semiring A] [Semiring B]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module B N]
    (p : ι → Submodule A M) (g : M →+ N) :
    Submodule.span B (g '' ↑(⨆ i, p i)) = ⨆ i, Submodule.span B (g '' ↑(p i)) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (iSup_le fun i ↦ Submodule.span_mono (Set.image_mono
      (SetLike.coe_subset_coe.mpr (le_iSup p i))))
  rintro _ ⟨x, hx, rfl⟩
  refine Submodule.iSup_induction p
    (motive := fun y ↦ g y ∈ ⨆ i, Submodule.span B (g '' ↑(p i))) hx ?_ ?_ ?_
  · intro i y hy
    exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨y, hy, rfl⟩)
  · simp
  · intro y z hy hz
    rw [map_add]; exact Submodule.add_mem _ hy hz

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherent submodule data of a fixed finite free module admit arbitrary
suprema, computed affine-locally. -/
instance : CompleteSemilatticeSup (X.SubmoduleSheafData n) where
  sSup s :=
    { submodule := sSup (SubmoduleSheafData.submodule '' s)
      span_resPi_basicOpen := by
        have hsubmodule : sSup (SubmoduleSheafData.submodule '' s) =
            ⨆ K : s, K.1.submodule := by
          conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
          rfl
        intro U f
        simp only [hsubmodule, iSup_apply]
        let g : (Fin n → Γ(X, U.1)) →+ (Fin n → Γ(X, (X.affineBasicOpen f).1)) :=
          { toFun := X.resPi (X.basicOpen_le f) n
            map_zero' := X.resPi_zero (X.basicOpen_le f)
            map_add' := X.resPi_add (X.basicOpen_le f) }
        change Submodule.span _ (g '' (⨆ K : s, K.1.submodule U :
          Submodule Γ(X, U.1) (Fin n → Γ(X, U.1)))) = _
        rw [Submodule.span_image_iSup_of_addMonoidHom]
        exact iSup_congr fun K ↦ K.1.span_resPi_basicOpen U f }
  isLUB_sSup _ := .of_image (f := SubmoduleSheafData.submodule) le_def (isLUB_sSup _)

/-- Suprema of quasi-coherent submodule data are computed componentwise on affine
opens. -/
lemma submodule_iSup {ι : Sort*} (K : ι → X.SubmoduleSheafData n)
    (U : X.affineOpens) :
    (⨆ i, K i).submodule U = ⨆ i, (K i).submodule U := by
  change (sSup (SubmoduleSheafData.submodule '' Set.range K)) U = _
  have h : sSup (SubmoduleSheafData.submodule '' Set.range K) =
      ⨆ i, (K i).submodule := by
    conv_lhs => rw [← Set.range_comp]
    rfl
  rw [h, iSup_apply]

/-- The largest quasi-coherent submodule datum contained in an arbitrary family of
submodules on the affine opens. -/
def ofSubmodules
    (K : ∀ U : X.affineOpens, Submodule Γ(X, U.1) (Fin n → Γ(X, U.1))) :
    X.SubmoduleSheafData n :=
  sSup {L : X.SubmoduleSheafData n | L.submodule ≤ K}

/-- Every affine component of `ofSubmodules K` is contained in the corresponding
candidate submodule `K U`. -/
lemma submodule_ofSubmodules_le
    (K : ∀ U : X.affineOpens, Submodule Γ(X, U.1) (Fin n → Γ(X, U.1))) :
    (ofSubmodules K).submodule ≤ K :=
  sSup_le (Set.forall_mem_image.mpr fun _ ↦ id)

/-- A quasi-coherent submodule datum lies below `ofSubmodules K` exactly when all of
its affine components lie below the candidate family `K`. -/
lemma le_ofSubmodules_iff {L : X.SubmoduleSheafData n}
    {K : ∀ U : X.affineOpens, Submodule Γ(X, U.1) (Fin n → Γ(X, U.1))} :
    L ≤ ofSubmodules K ↔ L.submodule ≤ K := by
  constructor
  · intro h U
    exact (SubmoduleSheafData.le_def.mp h U).trans (submodule_ofSubmodules_le K U)
  · intro h
    exact le_sSup h

/-- Applying `ofSubmodules` to the affine components of a quasi-coherent submodule
datum recovers that datum. -/
@[simp]
lemma ofSubmodules_submodule (K : X.SubmoduleSheafData n) :
    ofSubmodules K.submodule = K := by
  apply le_antisymm
  · exact le_def.mpr (submodule_ofSubmodules_le K.submodule)
  · exact le_ofSubmodules_iff.mpr le_rfl

/-- Taking affine components and taking the largest quasi-coherent subdatum form a
Galois coinsertion. -/
protected def gci : GaloisCoinsertion
    (SubmoduleSheafData.submodule (X := X) (n := n)) ofSubmodules where
  choice K hK :=
    { submodule := K
      span_resPi_basicOpen U f :=
        (submodule_ofSubmodules_le K).antisymm hK ▸
          (ofSubmodules K).span_resPi_basicOpen U f }
  gc _ _ := le_ofSubmodules_iff.symm
  u_l_le _ := submodule_ofSubmodules_le _
  choice_eq K hK := SubmoduleSheafData.ext (hK.antisymm (submodule_ofSubmodules_le K))

instance : OrderTop (X.SubmoduleSheafData n) where
  top := ofSubmodules fun _ ↦ ⊤
  le_top _ := le_ofSubmodules_iff.mpr fun _ ↦ le_top

instance : OrderBot (X.SubmoduleSheafData n) where
  bot := ofSubmodules fun _ ↦ ⊥
  bot_le K := le_def.mpr fun U ↦
    (submodule_ofSubmodules_le (fun _ ↦ ⊥) U).trans (bot_le : ⊥ ≤ K.submodule U)

instance : SemilatticeInf (X.SubmoduleSheafData n) where
  inf K L := ofSubmodules fun U ↦ K.submodule U ⊓ L.submodule U
  inf_le_left K L := le_def.mpr fun U ↦
    (submodule_ofSubmodules_le (fun U ↦ K.submodule U ⊓ L.submodule U) U).trans inf_le_left
  inf_le_right K L := le_def.mpr fun U ↦
    (submodule_ofSubmodules_le (fun U ↦ K.submodule U ⊓ L.submodule U) U).trans inf_le_right
  le_inf _ _ _ hKL hKM := le_ofSubmodules_iff.mpr fun U ↦
    le_inf (le_def.mp hKL U) (le_def.mp hKM U)

instance : CompleteLattice (X.SubmoduleSheafData n) where
  __ := (inferInstance : OrderTop (X.SubmoduleSheafData n))
  __ := (inferInstance : OrderBot (X.SubmoduleSheafData n))
  __ := (inferInstance : SemilatticeInf (X.SubmoduleSheafData n))
  __ := (inferInstance : CompleteSemilatticeSup (X.SubmoduleSheafData n))
  __ := SubmoduleSheafData.gci.liftCompleteLattice

/-- Binary intersections of quasi-coherent submodule data are computed on every
affine open. -/
@[simp]
lemma submodule_inf (K L : X.SubmoduleSheafData n) (U : X.affineOpens) :
    (K ⊓ L).submodule U = K.submodule U ⊓ L.submodule U := by
  apply le_antisymm
  · exact le_inf (le_def.mp inf_le_left U) (le_def.mp inf_le_right U)
  · let M : X.SubmoduleSheafData n :=
      { submodule := fun V ↦ K.submodule V ⊓ L.submodule V
        span_resPi_basicOpen := by
          intro V f
          letI : Algebra Γ(X, V.1) Γ(X, (X.affineBasicOpen f).1) :=
            (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
          haveI : IsLocalization.Away f Γ(X, (X.affineBasicOpen f).1) :=
            V.2.isLocalization_basicOpen f
          have hres : X.resPi (show (X.affineBasicOpen f).1 ≤ V.1 from X.basicOpen_le f) n =
              fun v i ↦ algebraMap Γ(X, V.1) Γ(X, (X.affineBasicOpen f).1) (v i) := rfl
          rw [hres, Submodule.span_image_inf_of_isLocalization_away (g := f)]
          rw [← hres, K.span_resPi_basicOpen, L.span_resPi_basicOpen] }
    have hM : M ≤ K ⊓ L := le_inf
      (le_def.mpr fun _ ↦ inf_le_left) (le_def.mpr fun _ ↦ inf_le_right)
    exact le_def.mp hM U

/-- The localization axiom of a submodule sheaf datum, stated for an arbitrary
presentation of the target as a basic open (transport of `span_resPi_basicOpen` across an
equality of affine opens). -/
lemma span_resPi_of_eq (K : X.SubmoduleSheafData n) {U V : X.affineOpens}
    (f : Γ(X, U.1)) (hV : V = X.affineBasicOpen f) :
    Submodule.span Γ(X, V.1)
      (X.resPi ((congrArg (fun W : X.affineOpens ↦ W.1) hV).trans_le
        (Subtype.coe_le_coe.mpr (X.affineBasicOpen_le f))) n ''
        (K.submodule U : Set (Fin n → Γ(X, U.1)))) = K.submodule V := by
  subst hV
  exact K.span_resPi_basicOpen U f

/-- Sections of quasi-coherent submodule data restrict along inclusions of affine
opens. -/
lemma resPi_mem_submodule_of_le (K : X.SubmoduleSheafData n)
    {U V : X.affineOpens} (hVU : V.1 ≤ U.1)
    {v : Fin n → Γ(X, U.1)} (hv : v ∈ K.submodule U) :
    X.resPi hVU n v ∈ K.submodule V := by
  apply mem_of_forall_exists_basicOpen_resPi_mem_span
  intro x hxV
  obtain ⟨c₁, c₂, hc, hxc⟩ := exists_basicOpen_le_affine_inter
    U.2 V.2 x ⟨hVU hxV, hxV⟩
  refine ⟨c₂, hc ▸ hxc, ?_⟩
  have hspan := K.span_resPi_basicOpen V c₂
  change Submodule.span Γ(X, X.basicOpen c₂)
      (X.resPi (X.basicOpen_le c₂) n ''
        (K.submodule V : Set (Fin n → Γ(X, V.1)))) =
      K.submodule (X.affineBasicOpen c₂) at hspan
  rw [hspan]
  have htarget : X.affineBasicOpen c₂ = X.affineBasicOpen c₁ :=
    Subtype.ext hc.symm
  have hspanU := K.span_resPi_of_eq c₁ htarget
  change Submodule.span Γ(X, X.basicOpen c₂)
      (X.resPi (show X.basicOpen c₂ ≤ U.1 from hc ▸ X.basicOpen_le c₁) n ''
        (K.submodule U : Set (Fin n → Γ(X, U.1)))) =
      K.submodule (X.affineBasicOpen c₂) at hspanU
  rw [← hspanU]
  apply Submodule.subset_span
  refine ⟨v, hv, ?_⟩
  rw [resPi_resPi]

/-- Quasi-coherent submodule data on an affine scheme are generated by their module
of global sections. -/
lemma submodule_eq_span_top [IsAffine X] (K : X.SubmoduleSheafData n)
    (U : X.affineOpens) :
    K.submodule U = Submodule.span Γ(X, U.1)
      (X.resPi (show U.1 ≤ (⊤ : X.Opens) from le_top) n ''
        (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) := by
  let W := Submodule.span Γ(X, U.1)
    (X.resPi (show U.1 ≤ (⊤ : X.Opens) from le_top) n ''
      (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤))))
  have local_eq (x : X) (hx : x ∈ U.1) :
      ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧
        Submodule.span Γ(X, X.basicOpen g)
          (X.resPi (X.basicOpen_le g) n '' (W : Set (Fin n → Γ(X, U.1)))) =
            K.submodule (X.affineBasicOpen g) := by
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter
      (isAffineOpen_top X) U.2 x ⟨trivial, hx⟩
    refine ⟨g, hfg ▸ hxf, ?_⟩
    have htop : Submodule.span Γ(X, X.basicOpen g)
        (X.resPi (show X.basicOpen g ≤ (⊤ : X.Opens) from le_top) n ''
          (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) =
        K.submodule (X.affineBasicOpen g) :=
      K.span_resPi_of_eq (U := ⟨⊤, isAffineOpen_top X⟩)
        (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
    rw [← htop]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      change z ∈ Submodule.span Γ(X, U.1)
        (X.resPi le_top n ''
          (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) at hz
      exact resPi_mem_span_resPi le_top (X.basicOpen_le g) hz
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, hw, rfl⟩
      apply Submodule.subset_span
      refine ⟨X.resPi le_top n w, Submodule.subset_span ⟨w, hw, rfl⟩, ?_⟩
      rw [resPi_resPi]
  apply le_antisymm
  · intro v hv
    apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    obtain ⟨g, hxg, heq⟩ := local_eq x hx
    refine ⟨g, hxg, ?_⟩
    have hvD : X.resPi (X.basicOpen_le g) n v ∈
        K.submodule (X.affineBasicOpen g) := by
      rw [← K.span_resPi_basicOpen U g]
      exact Submodule.subset_span ⟨v, hv, rfl⟩
    rw [← heq] at hvD
    exact hvD
  · intro v hv
    change v ∈ W at hv
    apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    obtain ⟨g, hxg, heq⟩ := local_eq x hx
    refine ⟨g, hxg, ?_⟩
    have hres : X.resPi (X.basicOpen_le g) n v ∈
        Submodule.span Γ(X, X.basicOpen g)
          (X.resPi (X.basicOpen_le g) n '' (W : Set (Fin n → Γ(X, U.1)))) :=
      Submodule.subset_span ⟨v, hv, rfl⟩
    rw [heq, ← K.span_resPi_basicOpen U g] at hres
    exact hres

/-- On an affine scheme, quasi-coherent submodule data are recovered from their
global component. -/
@[simp]
lemma ofAffineSubmodule_submodule [IsAffine X] (K : X.SubmoduleSheafData n) :
    ofAffineSubmodule (K.submodule ⟨⊤, isAffineOpen_top X⟩) = K := by
  apply SubmoduleSheafData.ext
  funext U
  exact (submodule_eq_span_top K U).symm

/-- Inclusion of quasi-coherent submodule data on an affine scheme can be checked on
global sections. -/
lemma le_iff_submodule_top_le [IsAffine X] {K L : X.SubmoduleSheafData n} :
    K ≤ L ↔ K.submodule ⟨⊤, isAffineOpen_top X⟩ ≤
      L.submodule ⟨⊤, isAffineOpen_top X⟩ := by
  constructor
  · intro h
    exact le_def.mp h _
  · intro h
    apply le_def.mpr
    intro U
    rw [submodule_eq_span_top K U, submodule_eq_span_top L U]
    exact Submodule.span_mono (Set.image_mono h)

/-- Quasi-coherent submodule data on an affine scheme are determined by their
restrictions to any basic-open cover. -/
lemma eq_of_span_resPi_eq_of_iSup_basicOpen_eq_top [IsAffine X]
    {ι : Type*} (f : ι → Γ(X, ⊤)) (K L : X.SubmoduleSheafData n)
    (hcover : ⨆ i, X.basicOpen (f i) = ⊤)
    (hlocal : ∀ i,
      Submodule.span Γ(X, X.basicOpen (f i))
          (X.resPi (X.basicOpen_le (f i)) n ''
            (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) =
        Submodule.span Γ(X, X.basicOpen (f i))
          (X.resPi (X.basicOpen_le (f i)) n ''
            (L.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤))))) :
    K = L := by
  apply le_antisymm
  · apply le_iff_submodule_top_le.mpr
    intro v hv
    apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    have hxcover : x ∈ ⨆ i, X.basicOpen (f i) := by
      rw [hcover]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hxcover
    obtain ⟨i, hxi⟩ := hxcover
    refine ⟨f i, hxi, ?_⟩
    rw [← hlocal i]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  · apply le_iff_submodule_top_le.mpr
    intro v hv
    apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    have hxcover : x ∈ ⨆ i, X.basicOpen (f i) := by
      rw [hcover]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hxcover
    obtain ⟨i, hxi⟩ := hxcover
    refine ⟨f i, hxi, ?_⟩
    rw [hlocal i]
    exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- Let `K ⊆ O_X^{⊕n}` be a quasi-coherent submodule sheaf and `q` a natural number. The
quotient `O_X^{⊕n}/K` is a vector bundle (finite locally free module) of rank `q`: every
point of `X` has an affine open neighborhood `U` on which the quotient module
`Γ(X, U)^{⊕n}/K(U)` is (finite and) projective with rank `q` at every prime. This is the
sheaf-level analogue of the conditions in Mathlib's `Module.Grassmannian`. -/
def QuotientProjectiveOfRank (q : ℕ) (K : X.SubmoduleSheafData n) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    Module.Projective Γ(X, U.1) ((Fin n → Γ(X, U.1)) ⧸ K.submodule U) ∧
    ∀ p : PrimeSpectrum Γ(X, U.1),
      Module.rankAtStalk ((Fin n → Γ(X, U.1)) ⧸ K.submodule U) p = q

variable (f : X ⟶ Y) (K : Y.SubmoduleSheafData n)

/-- Let `f : X ⟶ Y` be a morphism of schemes, `K ⊆ O_Y^{⊕n}` a quasi-coherent submodule
sheaf, `U'` an affine open of `X` and `g : Γ(X, U')`. The submodule of sections of
`O_X^{⊕n}` over the basic open `D(g)` spanned by all pullbacks of sections of `K` along
`f`, over all affine opens `U ⊆ Y` with `D(g) ⊆ f⁻¹(U)`. -/
def pullSpan (V : X.Opens) :
    Submodule Γ(X, V) (Fin n → Γ(X, V)) :=
  Submodule.span Γ(X, V)
    (⋃ (U : Y.affineOpens) (h : V ≤ f ⁻¹ᵁ U.1),
      f.appPi U.1 h n '' (K.submodule U : Set (Fin n → Γ(Y, U.1))))

/-- Formation of the span of local pullbacks commutes with arbitrary suprema of
quasi-coherent submodule data. -/
lemma pullSpan_iSup {ι : Sort*} (K : ι → Y.SubmoduleSheafData n) (f : X ⟶ Y)
    (V : X.Opens) :
    (⨆ i, K i).pullSpan f V = ⨆ i, (K i).pullSpan f V := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨U, h, w, hw, rfl⟩ := hz
    rw [submodule_iSup] at hw
    refine Submodule.iSup_induction (fun i ↦ (K i).submodule U)
      (motive := fun w ↦ f.appPi U.1 h n w ∈ ⨆ i, (K i).pullSpan f V) hw ?_ ?_ ?_
    · intro i w hw
      exact Submodule.mem_iSup_of_mem i (Submodule.subset_span
        (Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨h, ⟨w, hw, rfl⟩⟩⟩))
    · rw [Hom.appPi_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [Hom.appPi_add]
      exact Submodule.add_mem _ hv hw
  · refine iSup_le fun i ↦ Submodule.span_le.mpr ?_
    rintro _ hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨U, h, w, hw, rfl⟩ := hz
    have hwi : w ∈ (⨆ i, K i).submodule U := by
      rw [submodule_iSup]
      exact Submodule.mem_iSup_of_mem i hw
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨U,
      Set.mem_iUnion.mpr ⟨h, ⟨w, hwi, rfl⟩⟩⟩)

/-- Inclusion of quasi-coherent submodule data is preserved by taking the span of
local pullbacks. -/
lemma pullSpan_mono {K L : Y.SubmoduleSheafData n} (hKL : K ≤ L) (f : X ⟶ Y)
    (V : X.Opens) :
    K.pullSpan f V ≤ L.pullSpan f V := by
  refine Submodule.span_mono ?_
  rintro _ hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨U, h, w, hw, rfl⟩ := hz
  exact Set.mem_iUnion.mpr ⟨U,
    Set.mem_iUnion.mpr ⟨h, ⟨w, (le_def.mp hKL U) hw, rfl⟩⟩⟩

/-- Sections of the pulled-back span restrict into the pulled-back span over a smaller
basic open. -/
lemma resPi_mem_pullSpan_of_mem_pullSpan {V V' : X.Opens}
    (hle : V' ≤ V) {v : Fin n → Γ(X, V)}
    (hv : v ∈ K.pullSpan f V) : X.resPi hle n v ∈ K.pullSpan f V' := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨s, ⟨U, rfl⟩, hs⟩ := hv
    simp only [Set.mem_iUnion] at hs
    obtain ⟨h, w, hw, rfl⟩ := hs
    rw [resPi_appPi]
    exact Submodule.subset_span (Set.mem_iUnion.mpr
      ⟨U, Set.mem_iUnion.mpr ⟨hle.trans h, Set.mem_image_of_mem _ hw⟩⟩)
  | zero =>
    have : X.resPi hle n 0 = 0 := by
      funext i
      simp [resPi]
    rw [this]
    exact Submodule.zero_mem _
  | add v w _ _ hv hw =>
    rw [resPi_add]
    exact Submodule.add_mem _ hv hw
  | smul a v _ hv =>
    rw [resPi_smul]
    exact Submodule.smul_mem _ _ hv

/-- The underlying submodule family of the pullback of a quasi-coherent submodule sheaf:
over an affine open `U' ⊆ X`, a section lies in the pullback exactly when, locally on
basic opens of `U'`, it lies in the span of pullbacks of sections of `K`. The
localization axiom is proved in `SubmoduleSheafData.comap`. -/
def comapSubmodule (U' : X.affineOpens) :
    Submodule Γ(X, U'.1) (Fin n → Γ(X, U'.1)) :=
    { carrier := {v | ∀ x ∈ U'.1, ∃ g : Γ(X, U'.1), x ∈ X.basicOpen g ∧
        X.resPi (X.basicOpen_le g) n v ∈ K.pullSpan f (X.basicOpen g)}
      zero_mem' := by
        intro x hx
        refine ⟨1, by simpa using hx, ?_⟩
        have : X.resPi (X.basicOpen_le (1 : Γ(X, U'.1))) n 0 = 0 := by
          funext i
          simp [resPi]
        rw [this]
        exact Submodule.zero_mem _
      add_mem' := by
        intro v w hv hw x hx
        obtain ⟨g₁, hxg₁, hv₁⟩ := hv x hx
        obtain ⟨g₂, hxg₂, hw₂⟩ := hw x hx
        refine ⟨g₁ * g₂, ?_, ?_⟩
        · rw [X.basicOpen_mul]
          exact ⟨hxg₁, hxg₂⟩
        · have h₁ : X.basicOpen (g₁ * g₂) ≤ X.basicOpen g₁ := by
            rw [X.basicOpen_mul]; exact inf_le_left
          have h₂ : X.basicOpen (g₁ * g₂) ≤ X.basicOpen g₂ := by
            rw [X.basicOpen_mul]; exact inf_le_right
          rw [resPi_add]
          refine Submodule.add_mem _ ?_ ?_
          · have := K.resPi_mem_pullSpan_of_mem_pullSpan f h₁ hv₁
            rwa [resPi_resPi] at this
          · have := K.resPi_mem_pullSpan_of_mem_pullSpan f h₂ hw₂
            rwa [resPi_resPi] at this
      smul_mem' := by
        intro a v hv x hx
        obtain ⟨g, hxg, hvg⟩ := hv x hx
        refine ⟨g, hxg, ?_⟩
        rw [resPi_smul]
        exact Submodule.smul_mem _ _ hvg }

/-- On an affine open, every section in the span of local pullbacks belongs to the
affine-local submodule defining the pullback datum. -/
lemma pullSpan_le_comapSubmodule (U : X.affineOpens) :
    K.pullSpan f U.1 ≤ K.comapSubmodule f U := by
  intro v hv x hx
  refine ⟨1, by simpa using hx, ?_⟩
  have hres := K.resPi_mem_pullSpan_of_mem_pullSpan f
    (X.basicOpen_le (1 : Γ(X, U.1))) hv
  simpa only [Scheme.basicOpen_one, resPi_refl] using hres

/-- Inclusion of quasi-coherent submodule data is preserved by the affine-local
submodules underlying pullback. -/
lemma comapSubmodule_mono {K L : Y.SubmoduleSheafData n} (hKL : K ≤ L)
    (f : X ⟶ Y) (U : X.affineOpens) :
    K.comapSubmodule f U ≤ L.comapSubmodule f U := by
  intro v hv x hx
  obtain ⟨g, hxg, hvg⟩ := hv x hx
  exact ⟨g, hxg, K.pullSpan_mono hKL f (X.basicOpen g) hvg⟩

/-- Restriction of the pullback family along an inclusion of affine opens. -/
lemma resPi_mem_comapSubmodule_of_le {U₀ W : X.affineOpens} (hle : W.1 ≤ U₀.1)
    {v : Fin n → Γ(X, U₀.1)} (hv : v ∈ K.comapSubmodule f U₀) :
    X.resPi hle n v ∈ K.comapSubmodule f W := by
  intro x hx
  obtain ⟨g, hxg, hvg⟩ := hv x (hle hx)
  obtain ⟨c₁, c₂, hc, hxc⟩ := exists_basicOpen_le_affine_inter W.2
    (X.affineBasicOpen g).2 x ⟨hx, hxg⟩
  refine ⟨c₁, hxc, ?_⟩
  have hcg : X.basicOpen c₁ ≤ X.basicOpen g := hc.trans_le (X.basicOpen_le c₂)
  have h1 := K.resPi_mem_pullSpan_of_mem_pullSpan f hcg hvg
  rw [resPi_resPi] at h1
  rw [resPi_resPi]
  exact h1

/-- **The pullback is chart-computable**: over an affine open `U'` mapped into an affine
chart `V`, the pullback submodule sheaf is exactly the span of the pulled-back sections
of `K` over the chart. This is the quasi-coherence of the pullback in its computational
form. -/
theorem comapSubmodule_eq_span (K : Y.SubmoduleSheafData n) (f : X ⟶ Y)
    {U' : X.affineOpens} {V : Y.affineOpens} (hle : U'.1 ≤ f ⁻¹ᵁ V.1) :
    K.comapSubmodule f U' = Submodule.span Γ(X, U'.1)
      (f.appPi V.1 hle n '' (K.submodule V : Set (Fin n → Γ(Y, V.1)))) := by
  refine le_antisymm (fun v hv ↦ ?_) (fun v hv x hx ↦ ?_)
  · refine mem_of_forall_exists_basicOpen_resPi_mem_span fun x hx ↦ ?_
    obtain ⟨g, hxg, hvg⟩ := hv x hx
    have key : ∀ z ∈ K.pullSpan f (X.basicOpen g),
        ∃ (g₂ : Γ(X, U'.1)) (hle₂ : X.basicOpen g₂ ≤ X.basicOpen g), x ∈ X.basicOpen g₂ ∧
          X.resPi hle₂ n z ∈ Submodule.span Γ(X, X.basicOpen g₂)
            (X.resPi (X.basicOpen_le g₂) n ''
              ((Submodule.span Γ(X, U'.1)
                (f.appPi V.1 hle n '' (K.submodule V : Set (Fin n → Γ(Y, V.1)))) :
                  Submodule Γ(X, U'.1) (Fin n → Γ(X, U'.1))) :
                Set (Fin n → Γ(X, U'.1)))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hzmem =>
        obtain ⟨s, ⟨U, rfl⟩, hs⟩ := hzmem
        simp only [Set.mem_iUnion] at hs
        obtain ⟨hUle, w, hw, rfl⟩ := hs
        obtain ⟨c₁, c₂, hc, hyc⟩ := exists_basicOpen_le_affine_inter U.2 V.2
          (f.base x) ⟨hUle hxg, hle hx⟩
        obtain ⟨c, hcle, hxc⟩ := (X.affineBasicOpen g).2.exists_basicOpen_le
          (V := X.basicOpen g ⊓ f ⁻¹ᵁ Y.basicOpen c₁) ⟨x, ⟨hxg, hyc⟩⟩ hxg
        rw [le_inf_iff] at hcle
        obtain ⟨g₂, hg₂⟩ := U'.2.basicOpen_basicOpen_is_basicOpen g c
        refine ⟨g₂, hg₂.trans_le hcle.1, hg₂ ▸ hxc, ?_⟩
        have hW₁ : X.basicOpen g₂ ≤ f ⁻¹ᵁ Y.basicOpen c₁ := hg₂.trans_le hcle.2
        rw [resPi_appPi]
        rw [show f.appPi U.1 ((hg₂.trans_le hcle.1).trans hUle) n w =
            f.appPi (Y.basicOpen c₁) hW₁ n (Y.resPi (Y.basicOpen_le c₁) n w) from
          (Hom.appPi_resPi f (Y.basicOpen_le c₁) hW₁ w).symm.trans (by rfl)]
        have hwmem : Y.resPi (Y.basicOpen_le c₁) n w ∈
            K.submodule (Y.affineBasicOpen c₁) := by
          rw [← K.span_resPi_basicOpen U c₁]
          exact Submodule.subset_span ⟨w, hw, rfl⟩
        rw [← K.span_resPi_of_eq (U := V) c₂ (V := Y.affineBasicOpen c₁)
          (Subtype.ext (by simpa using hc))] at hwmem
        have hpush := Hom.appPi_mem_span_appPi f hW₁ hwmem
        refine Submodule.span_le.mpr ?_ hpush
        rintro _ ⟨t, ⟨k, hk, rfl⟩, rfl⟩
        exact Set.mem_of_eq_of_mem
          ((Hom.appPi_resPi f _ hW₁ k).trans ((resPi_appPi f V.1 hle
            (X.basicOpen_le g₂) k).symm.trans (by rfl)))
          (Submodule.subset_span ⟨f.appPi V.1 hle n k,
            Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩)
      | zero =>
        exact ⟨g, le_rfl, hxg, by rw [resPi_zero]; exact Submodule.zero_mem _⟩
      | add z₁ z₂ _ _ ih₁ ih₂ =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih₁
        obtain ⟨b, hleb, hxb, hb⟩ := ih₂
        have hab₁ : X.basicOpen (a * b) ≤ X.basicOpen a := by
          rw [X.basicOpen_mul]; exact inf_le_left
        have hab₂ : X.basicOpen (a * b) ≤ X.basicOpen b := by
          rw [X.basicOpen_mul]; exact inf_le_right
        refine ⟨a * b, hab₁.trans hlea,
          by rw [X.basicOpen_mul]; exact ⟨hxa, hxb⟩, ?_⟩
        rw [resPi_add]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 := resPi_mem_span_resPi (X.basicOpen_le a) hab₁ ha
          rwa [resPi_resPi] at h1
        · have h2 := resPi_mem_span_resPi (X.basicOpen_le b) hab₂ hb
          rwa [resPi_resPi] at h2
      | smul c z _ ih =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih
        refine ⟨a, hlea, hxa, ?_⟩
        rw [resPi_smul]
        exact Submodule.smul_mem _ _ ha
    obtain ⟨g₂, hle₂, hxg₂, hmem⟩ := key _ hvg
    exact ⟨g₂, hxg₂, by rwa [resPi_resPi] at hmem⟩
  · refine ⟨1, by simpa using hx, ?_⟩
    have h1 := resPi_mem_span_image (X.basicOpen_le (1 : Γ(X, U'.1))) hv
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨t, ⟨k, hk, rfl⟩, rfl⟩
    rw [resPi_appPi]
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨V,
      Set.mem_iUnion.mpr ⟨(X.basicOpen_le _).trans hle, ⟨k, hk, rfl⟩⟩⟩)

/-- Ring-level composition of restrictions of sections. -/
lemma res_res_section {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE hWV).op) ((X.presheaf.map (homOfLE hVU).op) a) =
      (X.presheaf.map (homOfLE (hWV.trans hVU)).op) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Membership in the pullback family is local on basic-open covers. -/
lemma mem_comapSubmodule_of_forall_res (K : Y.SubmoduleSheafData n) (f : X ⟶ Y)
    {U₀ : X.affineOpens} {v : Fin n → Γ(X, U₀.1)}
    {ι : Type*} (g : ι → Γ(X, U₀.1))
    (hcov : ∀ x ∈ U₀.1, ∃ i, x ∈ X.basicOpen (g i))
    (h : ∀ i, X.resPi (X.basicOpen_le (g i)) n v ∈
      K.comapSubmodule f (X.affineBasicOpen (g i))) :
    v ∈ K.comapSubmodule f U₀ := by
  intro x hx
  obtain ⟨i, hxi⟩ := hcov x hx
  obtain ⟨g', hxg', hg'⟩ := h i x hxi
  obtain ⟨g₂, hg₂⟩ := U₀.2.basicOpen_basicOpen_is_basicOpen (g i) g'
  refine ⟨g₂, hg₂ ▸ hxg', ?_⟩
  have h1 := K.resPi_mem_pullSpan_of_mem_pullSpan f
    (V' := X.basicOpen g₂) (le_of_eq hg₂) hg'
  convert h1 using 2
  funext ℓ
  exact (presheaf_map_map_map_apply _ _ _ _ (v ℓ)).symm

/-- Sections of the pullback over a basic open are power-of-`h₀` quotients of sections
over the ambient chart-subordinate affine: denominator clearing for the pullback
family. -/
lemma exists_pow_smul_resPi_eq_of_mem_comapSubmodule (K : Y.SubmoduleSheafData n)
    (f : X ⟶ Y) {U₀ : X.affineOpens} {V : Y.affineOpens} (hle : U₀.1 ≤ f ⁻¹ᵁ V.1)
    (h₀ : Γ(X, U₀.1)) {z : Fin n → Γ(X, X.basicOpen h₀)}
    (hz : z ∈ K.comapSubmodule f (X.affineBasicOpen h₀)) :
    ∃ (k : ℕ) (w : Fin n → Γ(X, U₀.1)), w ∈ K.comapSubmodule f U₀ ∧
      algebraMap Γ(X, U₀.1) Γ(X, X.basicOpen h₀) (h₀ ^ k) • z =
        X.resPi (X.basicOpen_le h₀) n w := by
  haveI := U₀.2.isLocalization_basicOpen h₀
  have hz1 : z ∈ Submodule.span Γ(X, X.basicOpen h₀)
      (f.appPi V.1 ((X.basicOpen_le h₀).trans hle) n ''
        (K.submodule V : Set (Fin n → Γ(Y, V.1)))) := by
    have h2 := hz
    rw [K.comapSubmodule_eq_span f (U' := X.affineBasicOpen h₀)
      ((X.basicOpen_le h₀).trans hle)] at h2
    exact h2
  have hz' : z ∈ Submodule.span Γ(X, X.basicOpen h₀)
      ((fun w (i : Fin n) ↦ algebraMap Γ(X, U₀.1) Γ(X, X.basicOpen h₀) (w i)) ''
        (K.comapSubmodule f U₀ : Set (Fin n → Γ(X, U₀.1)))) := by
    refine Submodule.span_le.mpr ?_ hz1
    rintro _ ⟨kk, hkk, rfl⟩
    refine Submodule.subset_span ⟨f.appPi V.1 hle n kk, ?_, ?_⟩
    · rw [K.comapSubmodule_eq_span f (U' := U₀) hle]
      exact Submodule.subset_span ⟨kk, hkk, rfl⟩
    · exact resPi_appPi f V.1 hle (X.basicOpen_le h₀) kk
  obtain ⟨k, w, hw, he⟩ :=
    Submodule.exists_pow_smul_eq_algebraMap_of_mem_span (g := h₀) hz'
  refine ⟨k, w, hw, ?_⟩
  rw [he]
  rfl

/-- Two sections of `O_X^{⊕n}` over an affine open that agree on a basic open agree
after multiplication by a power of the defining section. -/
lemma exists_pow_smul_eq_of_resPi_eq {U₀ : X.affineOpens} (h₀ : Γ(X, U₀.1))
    {w₁ w₂ : Fin n → Γ(X, U₀.1)}
    (h : X.resPi (X.basicOpen_le h₀) n w₁ = X.resPi (X.basicOpen_le h₀) n w₂) :
    ∃ m : ℕ, h₀ ^ m • w₁ = h₀ ^ m • w₂ := by
  haveI := U₀.2.isLocalization_basicOpen h₀
  have hcomp : ∀ j, algebraMap Γ(X, U₀.1) Γ(X, X.basicOpen h₀) (w₁ j) =
      algebraMap Γ(X, U₀.1) Γ(X, X.basicOpen h₀) (w₂ j) :=
    fun j ↦ congrFun h j
  choose s hs using fun j ↦
    (IsLocalization.exists_of_eq (M := Submonoid.powers h₀) (hcomp j))
  choose m hm using fun j ↦ (s j).2
  refine ⟨∑ j, m j, ?_⟩
  funext j
  have h0 := hs j
  rw [← hm j] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), pow_add, mul_assoc, h0, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : X ⟶ Y` be a morphism of schemes and `K ⊆ O_Y^{⊕n}` a quasi-coherent submodule
sheaf. The pullback `f⁻¹K·O_X^{⊕n} ⊆ O_X^{⊕n}`: over an affine open `U' ⊆ X`, a section
lies in the pullback exactly when, locally on basic opens of `U'`, it lies in the span of
pullbacks of sections of `K`. -/
def comap : X.SubmoduleSheafData n where
  submodule := K.comapSubmodule f
  span_resPi_basicOpen := by
    intro U' f₀
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact K.resPi_mem_comapSubmodule_of_le f (X.basicOpen_le f₀) hv
    · intro v' hv'
      classical
      -- chart-subordinate basic opens covering U'
      have hcov : ∀ x : ↥U'.1, ∃ (g : Γ(X, U'.1)) (V : Y.affineOpens),
          x.1 ∈ X.basicOpen g ∧ X.basicOpen g ≤ f ⁻¹ᵁ V.1 := by
        rintro ⟨x, hx⟩
        obtain ⟨V, hVmem, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
          Y.isBasis_affineOpens (U := ⊤) (show f.base x ∈ (⊤ : Y.Opens) from trivial)
        obtain ⟨g, hgle, hxg⟩ := U'.2.exists_basicOpen_le
          (V := U'.1 ⊓ f ⁻¹ᵁ V) ⟨x, ⟨hx, hyV⟩⟩ hx
        rw [le_inf_iff] at hgle
        exact ⟨g, ⟨V, hVmem⟩, hxg, hgle.2⟩
      choose gg VV hxg hgV using hcov
      obtain ⟨t, ht⟩ := U'.2.isCompact.elim_finite_subcover
        (fun x : ↥U'.1 ↦ (X.basicOpen (gg x) : Set X))
        (fun _ ↦ (X.basicOpen _).2) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxg _⟩)
      -- notation: restrictions of f₀ to the chart pieces (typed over the affine opens)
      set F : (i : ↥t) → Γ(X, (X.affineBasicOpen (gg i.1)).1) := fun i ↦
        (X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) f₀ with hF
      have hFopen : ∀ i, X.basicOpen (F i) = X.basicOpen (gg i.1) ⊓ X.basicOpen f₀ := by
        intro i
        rw [show X.basicOpen (F i) = X.basicOpen
          ((X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) f₀) from rfl,
          Scheme.basicOpen_res]
      have hOle : ∀ i : ↥t, X.basicOpen (F i) ≤ X.basicOpen f₀ := fun i ↦
        (hFopen i).trans_le inf_le_right
      -- denominator clearing on each chart piece
      have hclear := fun i : ↥t ↦
        K.exists_pow_smul_resPi_eq_of_mem_comapSubmodule f
          (U₀ := X.affineBasicOpen (gg i.1)) (hgV i.1) (F i)
          (K.resPi_mem_comapSubmodule_of_le f (U₀ := X.affineBasicOpen f₀)
            (W := X.affineBasicOpen (F i)) (hOle i) hv')
      choose kk ww hww hkeq using hclear
      set k : ℕ := Finset.univ.sup kk with hkdef
      -- first boost, to the common exponent k
      obtain ⟨w1, hw1def⟩ : ∃ w1 : (i : ↥t) →
            Fin n → Γ(X, (X.affineBasicOpen (gg i.1)).1),
          ∀ i, w1 i = F i ^ (k - kk i) • ww i := ⟨_, fun _ ↦ rfl⟩
      have hw1mem : ∀ i, w1 i ∈ K.comapSubmodule f (X.affineBasicOpen (gg i.1)) := by
        intro i
        rw [hw1def i]
        exact Submodule.smul_mem _ _ (hww i)
      have hkeq1 : ∀ i : ↥t,
          algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1) Γ(X, X.basicOpen (F i))
              (F i ^ k) • X.resPi (hOle i) n v' =
            X.resPi (X.basicOpen_le (F i)) n (w1 i) := by
        intro i
        have hle' : kk i ≤ k := Finset.le_sup (Finset.mem_univ i)
        have hsplit : F i ^ k = F i ^ (k - kk i) * F i ^ kk i := by
          rw [← pow_add]
          congr 1
          omega
        have hres : X.resPi (X.basicOpen_le (F i)) n (F i ^ (k - kk i) • ww i) =
            algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1) Γ(X, X.basicOpen (F i))
              (F i ^ (k - kk i)) • X.resPi (X.basicOpen_le (F i)) n (ww i) :=
          resPi_smul _ _ _
        rw [hw1def i, hres, hsplit, map_mul, mul_smul, hkeq i]
      -- the overlaps, presented as basic opens of the chart pieces
      set c : (i j : ↥t) → Γ(X, (X.affineBasicOpen (gg i.1)).1) := fun i j ↦
        (X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) (gg j.1) with hc
      have hcopen : ∀ i j, X.basicOpen (c i j) =
          X.basicOpen (gg i.1) ⊓ X.basicOpen (gg j.1) := by
        intro i j
        rw [show X.basicOpen (c i j) = X.basicOpen
          ((X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) (gg j.1)) from rfl,
          Scheme.basicOpen_res]
      have hcle₁ : ∀ i j, X.basicOpen (c i j) ≤ X.basicOpen (gg i.1) := fun i j ↦
        (hcopen i j).trans_le inf_le_left
      have hcle₂ : ∀ i j, X.basicOpen (c i j) ≤ X.basicOpen (gg j.1) := fun i j ↦
        (hcopen i j).trans_le inf_le_right
      -- the restriction of f₀ to an overlap, from either side
      have hFres : ∀ i j, (X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i) =
          (X.presheaf.map (homOfLE (hcle₂ i j)).op).hom (F j) := by
        intro i j
        rw [show (X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i) =
            (X.presheaf.map (homOfLE (hcle₁ i j)).op)
              ((X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) f₀) from rfl,
          show (X.presheaf.map (homOfLE (hcle₂ i j)).op).hom (F j) =
            (X.presheaf.map (homOfLE (hcle₂ i j)).op)
              ((X.presheaf.map (homOfLE (X.basicOpen_le (gg j.1))).op) f₀) from rfl,
          res_res_section, res_res_section]
      -- the boosted sections agree on the overlaps after inverting f₀
      have hagree : ∀ i j : ↥t,
          X.resPi (X.basicOpen_le ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)))
              n (X.resPi (hcle₁ i j) n (w1 i)) =
          X.resPi (X.basicOpen_le ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)))
              n (X.resPi (hcle₂ i j) n (w1 j)) := by
        intro i j
        have hD₀ : X.basicOpen ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)) =
            X.basicOpen (c i j) ⊓ X.basicOpen (F i) := by
          rw [show (X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i) =
              (X.presheaf.map (homOfLE (hcle₁ i j)).op) (F i) from rfl,
            Scheme.basicOpen_res]
        have hD₁ : X.basicOpen ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)) ≤
            X.basicOpen (F i) := hD₀.trans_le inf_le_right
        have hD₂ : X.basicOpen ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)) ≤
            X.basicOpen (F j) := by
          rw [hD₀, hFopen i, hFopen j]
          exact le_inf (inf_le_left.trans (hcle₂ i j))
            (inf_le_right.trans inf_le_right)
        have hi := congrArg (X.resPi hD₁ n) (hkeq1 i).symm
        rw [resPi_resPi, resPi_smul, resPi_resPi] at hi
        have hj := congrArg (X.resPi hD₂ n) (hkeq1 j).symm
        rw [resPi_resPi, resPi_smul, resPi_resPi] at hj
        have hs : (X.presheaf.map (homOfLE hD₁).op).hom
            (algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1) Γ(X, X.basicOpen (F i))
              (F i ^ k)) =
            (X.presheaf.map (homOfLE hD₂).op).hom
              (algebraMap Γ(X, (X.affineBasicOpen (gg j.1)).1) Γ(X, X.basicOpen (F j))
                (F j ^ k)) := by
          rw [map_pow, map_pow, map_pow, map_pow]
          congr 1
          have hi2 := (res_res_section (X := X) (X.basicOpen_le (F i)) hD₁
            ((X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) f₀)).trans
            (res_res_section (X.basicOpen_le (gg i.1))
              (hD₁.trans (X.basicOpen_le (F i))) f₀)
          have hj2 := (res_res_section (X := X) (X.basicOpen_le (F j)) hD₂
            ((X.presheaf.map (homOfLE (X.basicOpen_le (gg j.1))).op) f₀)).trans
            (res_res_section (X.basicOpen_le (gg j.1))
              (hD₂.trans (X.basicOpen_le (F j))) f₀)
          exact hi2.trans hj2.symm
        rw [resPi_resPi, resPi_resPi, hi, hj, hs]
      -- second boost, killing the overlap discrepancies
      have hpair : ∀ p : ↥t × ↥t, ∃ mp : ℕ,
          ((X.presheaf.map (homOfLE (hcle₁ p.1 p.2)).op).hom (F p.1)) ^ mp •
            X.resPi (hcle₁ p.1 p.2) n (w1 p.1) =
          ((X.presheaf.map (homOfLE (hcle₁ p.1 p.2)).op).hom (F p.1)) ^ mp •
            X.resPi (hcle₂ p.1 p.2) n (w1 p.2) := fun p ↦
        exists_pow_smul_eq_of_resPi_eq (X := X)
          (U₀ := X.affineBasicOpen (c p.1 p.2))
          ((X.presheaf.map (homOfLE (hcle₁ p.1 p.2)).op).hom (F p.1))
          (hagree p.1 p.2)
      choose mm hmm using hpair
      set m : ℕ := Finset.univ.sup mm with hmdef
      obtain ⟨w2, hw2def⟩ : ∃ w2 : (i : ↥t) →
            Fin n → Γ(X, (X.affineBasicOpen (gg i.1)).1),
          ∀ i, w2 i = F i ^ m • w1 i := ⟨_, fun _ ↦ rfl⟩
      have hw2mem : ∀ i, w2 i ∈ K.comapSubmodule f (X.affineBasicOpen (gg i.1)) := by
        intro i
        rw [hw2def i]
        exact Submodule.smul_mem _ _ (hw1mem i)
      have hkeq2 : ∀ i : ↥t,
          algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1) Γ(X, X.basicOpen (F i))
              (F i ^ (m + k)) • X.resPi (hOle i) n v' =
            X.resPi (X.basicOpen_le (F i)) n (w2 i) := by
        intro i
        have hres : X.resPi (X.basicOpen_le (F i)) n (F i ^ m • w1 i) =
            algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1) Γ(X, X.basicOpen (F i))
              (F i ^ m) • X.resPi (X.basicOpen_le (F i)) n (w1 i) :=
          resPi_smul _ _ _
        rw [hw2def i, hres, pow_add, map_mul, mul_smul, hkeq1 i]
      -- exact agreement of the twice-boosted sections on the overlaps
      have hagree2 : ∀ i j : ↥t,
          X.resPi (hcle₁ i j) n (w2 i) = X.resPi (hcle₂ i j) n (w2 j) := by
        intro i j
        have hle' : mm (i, j) ≤ m := Finset.le_sup (Finset.mem_univ _)
        have h1 := congrArg
          ((((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)) ^ (m - mm (i, j))) • ·)
          (hmm (i, j))
        simp only [smul_smul, ← pow_add] at h1
        rw [show m - mm (i, j) + mm (i, j) = m from by omega] at h1
        have hres₁ : X.resPi (hcle₁ i j) n (F i ^ m • w1 i) =
            ((X.presheaf.map (homOfLE (hcle₁ i j)).op).hom (F i)) ^ m •
              X.resPi (hcle₁ i j) n (w1 i) := by
          have := resPi_smul (X := X) (hcle₁ i j) (F i ^ m) (w1 i)
          rw [map_pow] at this
          exact this
        have hres₂ : X.resPi (hcle₂ i j) n (F j ^ m • w1 j) =
            ((X.presheaf.map (homOfLE (hcle₂ i j)).op).hom (F j)) ^ m •
              X.resPi (hcle₂ i j) n (w1 j) := by
          have := resPi_smul (X := X) (hcle₂ i j) (F j ^ m) (w1 j)
          rw [map_pow] at this
          exact this
        rw [hw2def i, hw2def j, hres₁, hres₂, ← hFres i j]
        exact h1
      -- glue the twice-boosted sections to a section over U'
      have hcoverop : U'.1 ≤ iSup (fun i : ↥t ↦ X.basicOpen (gg i.1)) := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hxi⟩
      have hglue : ∀ ℓ : Fin n, ∃ s : Γ(X, U'.1), ∀ i : ↥t,
          (X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op).hom s = w2 i ℓ := by
        intro ℓ
        have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1
            (fun i : ↥t ↦ X.basicOpen (gg i.1)) (fun i ↦ w2 i ℓ) := by
          intro i j
          have hle₀ : X.basicOpen (gg i.1) ⊓ X.basicOpen (gg j.1) ≤
              X.basicOpen (c i j) := le_of_eq (hcopen i j).symm
          have h2 := congrFun (congrArg (X.resPi hle₀ n) (hagree2 i j)) ℓ
          rw [resPi_resPi, resPi_resPi] at h2
          exact h2
        obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing'
          (fun i : ↥t ↦ X.basicOpen (gg i.1)) U'.1
          (fun i ↦ homOfLE (X.basicOpen_le (gg i.1))) hcoverop
          (fun i ↦ w2 i ℓ) hcompat
        exact ⟨s, fun i ↦ hs i⟩
      choose s hs using hglue
      -- the glued vector restricts to the boosted local sections
      have hresw : ∀ i : ↥t,
          X.resPi (X.basicOpen_le (gg i.1)) n (fun ℓ ↦ s ℓ) = w2 i := by
        intro i
        funext ℓ
        exact hs ℓ i
      -- the glued vector lies in the pullback over U'
      have hwmem : (fun ℓ ↦ s ℓ) ∈ K.comapSubmodule f U' := by
        refine K.mem_comapSubmodule_of_forall_res f (fun i : ↥t ↦ gg i.1) ?_ ?_
        · intro x hx
          obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
          exact ⟨⟨i, hit⟩, hxi⟩
        · intro i
          rw [hresw i]
          exact hw2mem i
      -- the covering basics of D(f₀) and the comparison opens
      have hGopen : ∀ i : ↥t, X.basicOpen
          ((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
            X.basicOpen_le f₀)).op) (gg i.1)) =
          X.basicOpen f₀ ⊓ X.basicOpen (gg i.1) := fun i ↦ by
        rw [Scheme.basicOpen_res]
        rfl
      have hGle : ∀ i : ↥t, X.basicOpen
          ((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
            X.basicOpen_le f₀)).op) (gg i.1)) ≤ (X.affineBasicOpen f₀).1 := fun i ↦
        (hGopen i).trans_le inf_le_left
      have hGF : ∀ i : ↥t, X.basicOpen
          ((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
            X.basicOpen_le f₀)).op) (gg i.1)) ≤ X.basicOpen (F i) := fun i ↦ by
        rw [hGopen i, hFopen i]
        exact le_inf inf_le_right inf_le_left
      have hGcover : (X.affineBasicOpen f₀).1 ≤ iSup (fun i : ↥t ↦ X.basicOpen
          ((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
            X.basicOpen_le f₀)).op) (gg i.1))) := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (X.basicOpen_le f₀ hx))
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hit⟩, ?_⟩
        rw [hGopen ⟨i, hit⟩]
        exact ⟨hx, hxi⟩
      -- the key equation over D(f₀)
      have hfinal : (X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
            X.basicOpen_le f₀)).op).hom (f₀ ^ (m + k)) • v' =
          X.resPi (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀) n
            (fun ℓ ↦ s ℓ) := by
        funext ℓ
        refine X.sheaf.eq_of_locally_eq' _ (X.affineBasicOpen f₀).1
          (fun i : ↥t ↦ homOfLE (hGle i)) hGcover _ _ fun i ↦ ?_
        -- compare through the boosted equation on the chart piece
        have hGgi : X.basicOpen ((X.presheaf.map (homOfLE
            (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀)).op)
              (gg i.1)) ≤ X.basicOpen (gg i.1) := (hGopen i).trans_le inf_le_right
        have h3v := congrArg (X.resPi (hGF i) n) (hkeq2 i)
        rw [resPi_smul, resPi_resPi, resPi_resPi] at h3v
        have h3 := congrFun h3v ℓ
        simp only [Pi.smul_apply, smul_eq_mul] at h3
        have hbase : (X.sheaf.1.map (homOfLE (hGle i)).op)
            ((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
              X.basicOpen_le f₀)).op).hom f₀) =
            (X.presheaf.map (homOfLE (hGF i)).op).hom
              (algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1)
                Γ(X, X.basicOpen (F i)) (F i)) :=
          (res_res_section (X := X) _ (hGle i) f₀).trans
            (((res_res_section (X.basicOpen_le (F i)) (hGF i)
              ((X.presheaf.map (homOfLE (X.basicOpen_le (gg i.1))).op) f₀)).trans
              (res_res_section (X.basicOpen_le (gg i.1))
                ((hGF i).trans (X.basicOpen_le (F i))) f₀)).symm)
        have e₁ : (X.sheaf.1.map (homOfLE (hGle i)).op)
            ((((X.presheaf.map (homOfLE (show (X.affineBasicOpen f₀).1 ≤ U'.1 from
              X.basicOpen_le f₀)).op).hom (f₀ ^ (m + k))) • v') ℓ) =
            (X.presheaf.map (homOfLE (hGF i)).op).hom
              (algebraMap Γ(X, (X.affineBasicOpen (gg i.1)).1)
                Γ(X, X.basicOpen (F i)) (F i ^ (m + k))) *
              (X.presheaf.map (homOfLE ((hGF i).trans (hOle i))).op).hom (v' ℓ) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul]
          congr 1
          rw [map_pow, map_pow, map_pow, map_pow]
          exact congrArg (· ^ (m + k)) hbase
        have e₂ : (X.sheaf.1.map (homOfLE (hGle i)).op)
            ((X.resPi (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀) n
              (fun ℓ ↦ s ℓ)) ℓ) =
            (X.presheaf.map (homOfLE hGgi).op).hom (w2 i ℓ) :=
          (res_res_section (X := X) _ (hGle i) (s ℓ)).trans
            (((res_res_section (X.basicOpen_le (gg i.1)) hGgi (s ℓ)).symm).trans
              (congrArg _ (hs ℓ i)))
        rw [e₁, e₂]
        exact h3
      -- conclude: v' is a unit multiple of the restriction of the glued section
      haveI := U'.2.isLocalization_basicOpen f₀
      obtain ⟨u, hu⟩ := IsLocalization.map_units (M := Submonoid.powers f₀)
        Γ(X, X.basicOpen f₀) ⟨f₀ ^ (m + k), m + k, rfl⟩
      obtain ⟨uv, ui, hui, huv⟩ : ∃ uv ui : Γ(X, (X.affineBasicOpen f₀).1),
          ui * uv = 1 ∧ uv = (X.presheaf.map (homOfLE
            (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀)).op).hom
              (f₀ ^ (m + k)) :=
        ⟨u.val, u⁻¹.val, u.inv_mul, hu⟩
      have hv'eq : v' = ui • X.resPi
          (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀) n
            (fun ℓ ↦ s ℓ) := by
        have h4 : uv • v' = X.resPi
            (show (X.affineBasicOpen f₀).1 ≤ U'.1 from X.basicOpen_le f₀) n
              (fun ℓ ↦ s ℓ) := by
          rw [huv]
          exact hfinal
        rw [← h4, smul_smul, hui, one_smul]
      rw [hv'eq]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨fun ℓ ↦ s ℓ, hwmem, rfl⟩)
/-- Pullback of quasi-coherent submodule data is monotone. -/
lemma comap_mono {K L : Y.SubmoduleSheafData n} (hKL : K ≤ L) (f : X ⟶ Y) :
    K.comap f ≤ L.comap f :=
  le_def.mpr fun U ↦ K.comapSubmodule_mono hKL f U

/-- Pullback of quasi-coherent submodule data commutes with arbitrary suprema. -/
lemma comap_iSup {ι : Sort*} (K : ι → Y.SubmoduleSheafData n) (f : X ⟶ Y) :
    (⨆ i, K i).comap f = ⨆ i, (K i).comap f := by
  let L : X.SubmoduleSheafData n := ⨆ i, (K i).comap f
  refine le_antisymm (le_def.mpr fun U v hv ↦ ?_) ?_
  · apply mem_of_forall_exists_basicOpen_resPi_mem_span
    intro x hx
    obtain ⟨g, hxg, hvg⟩ := hv x hx
    refine ⟨g, hxg, ?_⟩
    have hvg' : X.resPi (X.basicOpen_le g) n v ∈
        ⨆ i, (K i).pullSpan f (X.basicOpen g) := by
      rwa [← pullSpan_iSup]
    have hvg'' : X.resPi (X.basicOpen_le g) n v ∈
        ⨆ i, (K i).comapSubmodule f (X.affineBasicOpen g) := by
      exact (iSup_mono fun i ↦ (K i).pullSpan_le_comapSubmodule f
        (X.affineBasicOpen g)) hvg'
    have hvgL : X.resPi (X.basicOpen_le g) n v ∈
        L.submodule (X.affineBasicOpen g) := by
      rw [show L.submodule (X.affineBasicOpen g) =
        ⨆ i, ((K i).comap f).submodule (X.affineBasicOpen g) from
          submodule_iSup (fun i ↦ (K i).comap f) (X.affineBasicOpen g)]
      exact hvg''
    change X.resPi (X.basicOpen_le g) n v ∈ Submodule.span
      Γ(X, X.basicOpen g) (X.resPi (X.basicOpen_le g) n ''
        (L.submodule U : Set (Fin n → Γ(X, U.1))))
    have heq := L.span_resPi_basicOpen U g
    rw [← heq] at hvgL
    exact hvgL
  · change sSup (Set.range fun i ↦ (K i).comap f) ≤ _
    refine sSup_le ?_
    rintro _ ⟨i, rfl⟩
    apply comap_mono
    change K i ≤ sSup (Set.range K)
    exact le_sSup (Set.mem_range_self i)

/-- The direct image of quasi-coherent submodule data along a scheme morphism, defined
as the largest datum whose pullback is contained in the given datum. -/
def map (K : X.SubmoduleSheafData n) (f : X ⟶ Y) : Y.SubmoduleSheafData n :=
  ⨆ L : {L : Y.SubmoduleSheafData n // L.comap f ≤ K}, L.1

/-- Pulling back the direct image of quasi-coherent submodule data is contained in the
original datum. -/
lemma comap_map_le (K : X.SubmoduleSheafData n) (f : X ⟶ Y) :
    (K.map f).comap f ≤ K := by
  rw [map, comap_iSup]
  change sSup (Set.range fun L : {L : Y.SubmoduleSheafData n // L.comap f ≤ K} ↦
    L.1.comap f) ≤ K
  refine sSup_le ?_
  rintro _ ⟨L, rfl⟩
  exact L.2

/-- Pullback and direct image form a Galois connection on quasi-coherent submodule
data. -/
lemma le_map_iff_comap_le {K : X.SubmoduleSheafData n}
    {L : Y.SubmoduleSheafData n} {f : X ⟶ Y} :
    L ≤ K.map f ↔ L.comap f ≤ K := by
  constructor
  · intro h
    exact (comap_mono h f).trans (comap_map_le K f)
  · intro h
    change L ≤ sSup (Set.range fun L :
      {L : Y.SubmoduleSheafData n // L.comap f ≤ K} ↦ L.1)
    exact le_sSup ⟨⟨L, h⟩, rfl⟩

/-- The Galois connection between pullback and direct image of quasi-coherent
submodule data. -/
lemma map_gc (f : X ⟶ Y) :
    GaloisConnection (fun L : Y.SubmoduleSheafData n ↦ L.comap f) (fun K ↦ K.map f) :=
  fun _ _ ↦ le_map_iff_comap_le.symm

/-- Direct image of quasi-coherent submodule data is monotone. -/
lemma map_mono (f : X ⟶ Y) :
    Monotone (fun K : X.SubmoduleSheafData n ↦ K.map f) :=
  (map_gc f).monotone_u

/-- Every quasi-coherent submodule datum is contained in the direct image of its
pullback. -/
lemma le_map_comap (L : Y.SubmoduleSheafData n) (f : X ⟶ Y) :
    L ≤ (L.comap f).map f :=
  (map_gc f).le_u_l L

/-- Direct image, as a right adjoint, preserves binary intersections. -/
@[simp]
lemma map_inf (K L : X.SubmoduleSheafData n) (f : X ⟶ Y) :
    (K ⊓ L).map f = K.map f ⊓ L.map f :=
  (map_gc f).u_inf

/-- Direct image, as a right adjoint, preserves the largest submodule datum. -/
@[simp]
lemma map_top (f : X ⟶ Y) :
    (⊤ : X.SubmoduleSheafData n).map f = ⊤ :=
  (map_gc f).u_top

/-- Pulling back a quasi-coherent submodule sheaf along the identity does not change it. -/
lemma comap_id (K : X.SubmoduleSheafData n) : K.comap (𝟙 X) = K := by
  refine SubmoduleSheafData.ext (funext fun U' ↦ ?_)
  refine le_antisymm (fun v hv ↦ ?_) (fun v hv x hx ↦ ?_)
  · refine mem_of_forall_exists_basicOpen_resPi_mem_span fun x hx ↦ ?_
    obtain ⟨g, hxg, hvg⟩ := hv x hx
    have key : ∀ z ∈ K.pullSpan (𝟙 X) (X.basicOpen g),
        ∃ (g₂ : Γ(X, U'.1)) (hle : X.basicOpen g₂ ≤ X.basicOpen g), x ∈ X.basicOpen g₂ ∧
          X.resPi hle n z ∈ Submodule.span Γ(X, X.basicOpen g₂)
            (X.resPi (X.basicOpen_le g₂) n ''
              (K.submodule U' : Set (Fin n → Γ(X, U'.1)))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hzmem =>
        obtain ⟨s, ⟨U, rfl⟩, hs⟩ := hzmem
        simp only [Set.mem_iUnion] at hs
        obtain ⟨hUle, w, hw, rfl⟩ := hs
        obtain ⟨c₁, c₂, hc, hxc⟩ := exists_basicOpen_le_affine_inter
          (X.affineBasicOpen g).2 U.2 x ⟨hxg, hUle hxg⟩
        obtain ⟨g₂, hg₂⟩ := U'.2.basicOpen_basicOpen_is_basicOpen g c₁
        have hleg : X.basicOpen g₂ ≤ X.basicOpen g := hg₂.trans_le (X.basicOpen_le c₁)
        refine ⟨g₂, hleg, hg₂ ▸ hxc, ?_⟩
        suffices hmem : X.resPi hleg n (Hom.appPi (𝟙 X) U.1 hUle n w) ∈
            K.submodule (X.affineBasicOpen g₂) by
          rw [← K.span_resPi_basicOpen U' g₂] at hmem
          exact hmem
        rw [← K.span_resPi_of_eq (U := U) c₂ (V := X.affineBasicOpen g₂)
          (Subtype.ext (by simpa using hg₂.trans hc))]
        refine Submodule.subset_span ⟨w, hw, ?_⟩
        rw [show Hom.appPi (𝟙 X) U.1 hUle n w =
            X.resPi (show X.basicOpen g ≤ U.1 from hUle) n w from rfl, resPi_resPi]
        rfl
      | zero =>
        exact ⟨g, le_rfl, hxg, by rw [resPi_zero]; exact Submodule.zero_mem _⟩
      | add z₁ z₂ _ _ ih₁ ih₂ =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih₁
        obtain ⟨b, hleb, hxb, hb⟩ := ih₂
        have hab₁ : X.basicOpen (a * b) ≤ X.basicOpen a := by
          rw [X.basicOpen_mul]; exact inf_le_left
        have hab₂ : X.basicOpen (a * b) ≤ X.basicOpen b := by
          rw [X.basicOpen_mul]; exact inf_le_right
        refine ⟨a * b, hab₁.trans hlea,
          by rw [X.basicOpen_mul]; exact ⟨hxa, hxb⟩, ?_⟩
        rw [resPi_add]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 := resPi_mem_span_resPi (X.basicOpen_le a) hab₁ ha
          rwa [resPi_resPi] at h1
        · have h2 := resPi_mem_span_resPi (X.basicOpen_le b) hab₂ hb
          rwa [resPi_resPi] at h2
      | smul c z _ ih =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih
        refine ⟨a, hlea, hxa, ?_⟩
        rw [resPi_smul]
        exact Submodule.smul_mem _ _ ha
    obtain ⟨g₂, hle, hxg₂, hmem⟩ := key _ hvg
    refine ⟨g₂, hxg₂, ?_⟩
    rwa [resPi_resPi] at hmem
  · refine ⟨1, by simpa using hx, ?_⟩
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨U', Set.mem_iUnion.mpr
      ⟨by simp, ⟨v, hv, rfl⟩⟩⟩)

/-- Pulling back a quasi-coherent submodule sheaf along a composition is the composition of
the pullbacks. -/
lemma comap_comp (K : Z.SubmoduleSheafData n) (f : X ⟶ Y) (g : Y ⟶ Z) :
    K.comap (f ≫ g) = (K.comap g).comap f := by
  refine SubmoduleSheafData.ext (funext fun U' ↦ ?_)
  refine le_antisymm (fun v hv x hx ↦ ?_) (fun v hv x hx ↦ ?_)
  · obtain ⟨h, hxh, hvh⟩ := hv x hx
    have key : ∀ z ∈ K.pullSpan (f ≫ g) (X.basicOpen h),
        ∃ (h₂ : Γ(X, U'.1)) (hle : X.basicOpen h₂ ≤ X.basicOpen h), x ∈ X.basicOpen h₂ ∧
          X.resPi hle n z ∈ (K.comap g).pullSpan f (X.basicOpen h₂) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hzmem =>
        obtain ⟨s, ⟨U, rfl⟩, hs⟩ := hzmem
        simp only [Set.mem_iUnion] at hs
        obtain ⟨hUle, w, hw, rfl⟩ := hs
        have hyU : f.base x ∈ g ⁻¹ᵁ U.1 := hUle hxh
        obtain ⟨V, hVmem, hyV, hVle⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyU
        obtain ⟨c, hcle, hxc⟩ := (X.affineBasicOpen h).2.exists_basicOpen_le
          (V := X.basicOpen h ⊓ f ⁻¹ᵁ V) ⟨x, ⟨hxh, hyV⟩⟩ hxh
        rw [le_inf_iff] at hcle
        obtain ⟨h₂, hh₂⟩ := U'.2.basicOpen_basicOpen_is_basicOpen h c
        refine ⟨h₂, hh₂.trans_le hcle.1, hh₂ ▸ hxc, ?_⟩
        have hW : X.basicOpen h₂ ≤ f ⁻¹ᵁ V := hh₂.trans_le hcle.2
        rw [resPi_appPi]
        rw [show Hom.appPi (f ≫ g) U.1
              ((hh₂.trans_le hcle.1).trans hUle) n w =
            f.appPi V hW n (g.appPi U.1 hVle n w) from
          (Hom.appPi_comp f g hVle hW w).symm.trans (by rfl)]
        refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨V, hVmem⟩,
          Set.mem_iUnion.mpr ⟨hW, ?_⟩⟩)
        refine ⟨g.appPi U.1 hVle n w, ?_, rfl⟩
        intro y hy
        refine ⟨1, by simpa using hy, ?_⟩
        rw [resPi_appPi]
        exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨U,
          Set.mem_iUnion.mpr ⟨(Y.basicOpen_le _).trans hVle,
            ⟨w, hw, rfl⟩⟩⟩)
      | zero =>
        exact ⟨h, le_rfl, hxh, by rw [resPi_zero]; exact Submodule.zero_mem _⟩
      | add z₁ z₂ _ _ ih₁ ih₂ =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih₁
        obtain ⟨b, hleb, hxb, hb⟩ := ih₂
        have hab₁ : X.basicOpen (a * b) ≤ X.basicOpen a := by
          rw [X.basicOpen_mul]; exact inf_le_left
        have hab₂ : X.basicOpen (a * b) ≤ X.basicOpen b := by
          rw [X.basicOpen_mul]; exact inf_le_right
        refine ⟨a * b, hab₁.trans hlea,
          by rw [X.basicOpen_mul]; exact ⟨hxa, hxb⟩, ?_⟩
        rw [resPi_add]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 := (K.comap g).resPi_mem_pullSpan_of_mem_pullSpan f hab₁ ha
          rwa [resPi_resPi] at h1
        · have h2 := (K.comap g).resPi_mem_pullSpan_of_mem_pullSpan f hab₂ hb
          rwa [resPi_resPi] at h2
      | smul c z _ ih =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih
        refine ⟨a, hlea, hxa, ?_⟩
        rw [resPi_smul]
        exact Submodule.smul_mem _ _ ha
    obtain ⟨h₂, hle, hxh₂, hmem⟩ := key _ hvh
    refine ⟨h₂, hxh₂, ?_⟩
    rwa [resPi_resPi] at hmem
  · obtain ⟨h, hxh, hvh⟩ := hv x hx
    have key : ∀ z ∈ (K.comap g).pullSpan f (X.basicOpen h),
        ∃ (h₂ : Γ(X, U'.1)) (hle : X.basicOpen h₂ ≤ X.basicOpen h), x ∈ X.basicOpen h₂ ∧
          X.resPi hle n z ∈ K.pullSpan (f ≫ g) (X.basicOpen h₂) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hzmem =>
        obtain ⟨s', ⟨V, rfl⟩, hs⟩ := hzmem
        simp only [Set.mem_iUnion] at hs
        obtain ⟨hVle, s, hsK, rfl⟩ := hs
        have hyV : f.base x ∈ V.1 := hVle hxh
        obtain ⟨b, hyb, hsb⟩ := hsK (f.base x) hyV
        obtain ⟨c, hcle, hxc⟩ := (X.affineBasicOpen h).2.exists_basicOpen_le
          (V := X.basicOpen h ⊓ f ⁻¹ᵁ Y.basicOpen b) ⟨x, ⟨hxh, hyb⟩⟩ hxh
        rw [le_inf_iff] at hcle
        obtain ⟨h₂, hh₂⟩ := U'.2.basicOpen_basicOpen_is_basicOpen h c
        refine ⟨h₂, hh₂.trans_le hcle.1, hh₂ ▸ hxc, ?_⟩
        have hW : X.basicOpen h₂ ≤ f ⁻¹ᵁ Y.basicOpen b := hh₂.trans_le hcle.2
        rw [resPi_appPi]
        rw [show f.appPi V.1 ((hh₂.trans_le hcle.1).trans hVle) n s =
            f.appPi (Y.basicOpen b) hW n (Y.resPi (Y.basicOpen_le b) n s) from
          (Hom.appPi_resPi f (Y.basicOpen_le b) hW s).symm.trans (by rfl)]
        have hpush := Hom.appPi_mem_span_appPi f hW hsb
        refine Submodule.span_le.mpr ?_ hpush
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t', ⟨U, rfl⟩, ht'⟩ := ht
        simp only [Set.mem_iUnion] at ht'
        obtain ⟨hUle, w, hw, rfl⟩ := ht'
        rw [Hom.appPi_comp f g hUle hW]
        exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨U,
          Set.mem_iUnion.mpr ⟨hW.trans (f.preimage_mono hUle), ⟨w, hw, rfl⟩⟩⟩)
      | zero =>
        exact ⟨h, le_rfl, hxh, by rw [resPi_zero]; exact Submodule.zero_mem _⟩
      | add z₁ z₂ _ _ ih₁ ih₂ =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih₁
        obtain ⟨b, hleb, hxb, hb⟩ := ih₂
        have hab₁ : X.basicOpen (a * b) ≤ X.basicOpen a := by
          rw [X.basicOpen_mul]; exact inf_le_left
        have hab₂ : X.basicOpen (a * b) ≤ X.basicOpen b := by
          rw [X.basicOpen_mul]; exact inf_le_right
        refine ⟨a * b, hab₁.trans hlea,
          by rw [X.basicOpen_mul]; exact ⟨hxa, hxb⟩, ?_⟩
        rw [resPi_add]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 := K.resPi_mem_pullSpan_of_mem_pullSpan (f ≫ g) hab₁ ha
          rwa [resPi_resPi] at h1
        · have h2 := K.resPi_mem_pullSpan_of_mem_pullSpan (f ≫ g) hab₂ hb
          rwa [resPi_resPi] at h2
      | smul c z _ ih =>
        obtain ⟨a, hlea, hxa, ha⟩ := ih
        refine ⟨a, hlea, hxa, ?_⟩
        rw [resPi_smul]
        exact Submodule.smul_mem _ _ ha
    obtain ⟨h₂, hle, hxh₂, hmem⟩ := key _ hvh
    refine ⟨h₂, hxh₂, ?_⟩
    rwa [resPi_resPi] at hmem

/-- Along an isomorphism, restricting the direct image of quasi-coherent submodule
data recovers the original datum. -/
lemma comap_map_eq_of_isIso (K : X.SubmoduleSheafData n) (f : X ⟶ Y) [IsIso f] :
    (K.map f).comap f = K := by
  apply le_antisymm (comap_map_le K f)
  let L : Y.SubmoduleSheafData n := K.comap (inv f)
  have hLf : L.comap f = K := by
    rw [show L.comap f = K.comap (f ≫ inv f) from (K.comap_comp f (inv f)).symm,
      IsIso.hom_inv_id, K.comap_id]
  have hLmap : L ≤ K.map f := le_map_iff_comap_le.mpr hLf.le
  exact hLf.ge.trans (comap_mono hLmap f)

/-- Direct image of quasi-coherent submodule data along the identity is the identity. -/
@[simp]
lemma map_id (K : X.SubmoduleSheafData n) : K.map (𝟙 X) = K := by
  have h := comap_map_eq_of_isIso K (𝟙 X)
  rwa [comap_id] at h

/-- Direct image of quasi-coherent submodule data is compatible with composition. -/
lemma map_comp (K : X.SubmoduleSheafData n) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (K.map f).map g = K.map (f ≫ g) := by
  apply le_antisymm
  · rw [le_map_iff_comap_le, comap_comp]
    exact (comap_mono (comap_map_le (K.map f) g) f).trans (comap_map_le K f)
  · rw [le_map_iff_comap_le, le_map_iff_comap_le, ← comap_comp]
    exact comap_map_le K (f ≫ g)

/-- Chart-computation of the pullback, phrased for `comap` (an alias of
`comapSubmodule_eq_span`). -/
theorem comap_submodule_eq_span (K : Y.SubmoduleSheafData n) (f : X ⟶ Y)
    {U' : X.affineOpens} {V : Y.affineOpens} (hle : U'.1 ≤ f ⁻¹ᵁ V.1) :
    (K.comap f).submodule U' = Submodule.span Γ(X, U'.1)
      (f.appPi V.1 hle n '' (K.submodule V : Set (Fin n → Γ(Y, V.1)))) :=
  K.comapSubmodule_eq_span f hle

/-- Pullback of sections from an affine scheme to a basic open is the componentwise
algebra map on global sections. -/
lemma basicOpenι_appPi_top [IsAffine X] (f : Γ(X, ⊤)) :
    (X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n =
      fun w i ↦ algebraMap Γ(X, ⊤) Γ((X.basicOpen f).toScheme, ⊤) (w i) := by
  funext w i
  change ((X.basicOpen f).ι.appLE (⊤ : X.Opens) (⊤ : (X.basicOpen f).toScheme.Opens)
    _).hom (w i) = ((X.basicOpen f).ι.appTop).hom (w i)
  rw [show (X.basicOpen f).ι.appLE (⊤ : X.Opens)
      (⊤ : (X.basicOpen f).toScheme.Opens) _ = (X.basicOpen f).ι.app (⊤ : X.Opens) by
    rw [(X.basicOpen f).ι.app_eq_appLE]
    congr 1]

/-- The canonical top-sections isomorphism identifies pullback to the restricted
scheme with restriction to the underlying basic open. -/
lemma basicOpenι_appTop_topIso_hom [IsAffine X] (f : Γ(X, ⊤)) :
    (X.basicOpen f).ι.appTop ≫ (X.basicOpen f).topIso.hom =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
  simp only [Opens.ι_appTop, Opens.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

/-- Componentwise form of `basicOpenι_appTop_topIso_hom`. -/
lemma topIso_hom_basicOpenι_appPi_top [IsAffine X] (f : Γ(X, ⊤))
    (w : Fin n → Γ(X, ⊤)) :
    (fun i ↦ (X.basicOpen f).topIso.hom.hom
      ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n w i)) =
      X.resPi (X.basicOpen_le f) n w := by
  funext i
  change (X.basicOpen f).topIso.hom.hom
      (((X.basicOpen f).ι.appLE (⊤ : X.Opens)
        (⊤ : (X.basicOpen f).toScheme.Opens) _).hom (w i)) = _
  rw [show (X.basicOpen f).ι.appLE (⊤ : X.Opens)
      (⊤ : (X.basicOpen f).toScheme.Opens) _ = (X.basicOpen f).ι.appTop by
    rw [Hom.appTop, (X.basicOpen f).ι.app_eq_appLE]
    congr 1]
  rw [← CommRingCat.comp_apply, basicOpenι_appTop_topIso_hom]
  rfl

/-- The global submodule of data on the restricted scheme `D(f)`, transported through
the canonical top-sections isomorphism to the ambient section ring `Γ(D(f), 𝒪_X)`. -/
noncomputable def ambientBasicOpenSubmodule [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    Submodule Γ(X, X.basicOpen f) (Fin n → Γ(X, X.basicOpen f)) :=
  (K.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
    (X.basicOpen f).topIso.commRingCatIsoToRingEquiv

/-- The global component of data on the restricted scheme of an affine open,
transported back to sections on that open in the ambient scheme. -/
noncomputable def ambientAffineOpenSubmodule (U : X.affineOpens)
    (K : U.1.toScheme.SubmoduleSheafData n) :
    Submodule Γ(X, U.1) (Fin n → Γ(X, U.1)) :=
  (K.submodule ⟨⊤, isAffineOpen_top _⟩).mapPiRingEquiv
    U.1.topIso.commRingCatIsoToRingEquiv

/-- Restricting global submodule data to an affine open and transporting its top
component back through `topIso` recovers the original affine component. -/
@[simp]
lemma ambientAffineOpenSubmodule_comap (U : X.affineOpens)
    (K : X.SubmoduleSheafData n) :
    ambientAffineOpenSubmodule U (K.comap U.1.ι) = K.submodule U := by
  rw [ambientAffineOpenSubmodule,
    K.comap_submodule_eq_span U.1.ι
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := U)
      (by simp),
    Submodule.mapPiRingEquiv_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    convert hw using 1
    funext i
    change U.1.topIso.hom.hom
        ((U.1.ι.appLE U.1 (⊤ : U.1.toScheme.Opens) _).hom (w i)) = w i
    simp only [Opens.topIso_hom, Functor.op_obj, eqToHom_op, Opens.ι_appLE,
      homOfLE_leOfHom]
    exact ConcreteCategory.congr_hom ((X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _))) (w i)
  · intro z hz
    apply Submodule.subset_span
    refine ⟨U.1.ι.appPi U.1 (by simp) n z, ⟨z, hz, rfl⟩, ?_⟩
    · funext i
      change U.1.topIso.hom.hom
          ((U.1.ι.appLE U.1 (⊤ : U.1.toScheme.Opens) _).hom (z i)) = z i
      simp only [Opens.topIso_hom, Functor.op_obj, eqToHom_op, Opens.ι_appLE,
        homOfLE_leOfHom]
      exact ConcreteCategory.congr_hom ((X.presheaf.map_comp _ _).symm.trans
        ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _))) (z i)

/-- Pullback between restricted schemes of affine opens, transported to ambient
sections, is the span of ordinary restriction from the larger affine open. -/
lemma ambientAffineOpenSubmodule_comap_homOfLE
    (U V : X.affineOpens) (hVU : V.1 ≤ U.1)
    (K : U.1.toScheme.SubmoduleSheafData n) :
    ambientAffineOpenSubmodule V (K.comap (X.homOfLE hVU)) =
      Submodule.span Γ(X, V.1)
        (X.resPi hVU n '' (ambientAffineOpenSubmodule U K :
          Set (Fin n → Γ(X, U.1)))) := by
  let h : V.1.toScheme ⟶ U.1.toScheme := X.homOfLE hVU
  have hcomm : h.appTop ≫ V.1.topIso.hom =
      U.1.topIso.hom ≫ X.presheaf.map (homOfLE hVU).op := by
    simp only [h, Scheme.homOfLE_appTop, Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  rw [ambientAffineOpenSubmodule,
    K.comap_submodule_eq_span h
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩)
      (by intro x _; trivial),
    Submodule.mapPiRingEquiv_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i ↦ U.1.topIso.hom.hom (v i), ⟨v, hv, rfl⟩, ?_⟩
    rw [h.appPi_top]
    funext i
    change (X.presheaf.map (homOfLE hVU).op).hom
        (U.1.topIso.hom.hom (v i)) =
      V.1.topIso.hom.hom (h.appTop.hom (v i))
    have hi := congrArg (fun φ : Γ(U.1.toScheme, ⊤) ⟶ Γ(X, V.1) ↦
      φ.hom (v i)) hcomm
    simpa only [CommRingCat.comp_apply] using hi.symm
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨h.appPi (⊤ : U.1.toScheme.Opens)
      (by intro x _; trivial) n v, ⟨v, hv, rfl⟩, ?_⟩
    rw [h.appPi_top]
    funext i
    change V.1.topIso.hom.hom (h.appTop.hom (v i)) =
      (X.presheaf.map (homOfLE hVU).op).hom
        (U.1.topIso.hom.hom (v i))
    have hi := congrArg (fun φ : Γ(U.1.toScheme, ⊤) ⟶ Γ(X, V.1) ↦
      φ.hom (v i)) hcomm
    simpa only [CommRingCat.comp_apply] using hi

/-- Inclusion of data on a restricted affine open can be checked after transporting
its global module to ambient sections. -/
lemma le_iff_ambientAffineOpenSubmodule_le (U : X.affineOpens)
    {K L : U.1.toScheme.SubmoduleSheafData n} :
    K ≤ L ↔ ambientAffineOpenSubmodule U K ≤ ambientAffineOpenSubmodule U L := by
  rw [le_iff_submodule_top_le]
  constructor
  · exact fun h ↦ Submodule.map_mono h
  · intro h w hw
    let e := U.1.topIso.commRingCatIsoToRingEquiv
    have hw' : (fun i ↦ e (w i)) ∈ ambientAffineOpenSubmodule U K := by
      rw [ambientAffineOpenSubmodule, Submodule.mem_mapPiRingEquiv]
      change (fun i ↦ e.symm (e (w i))) ∈
        K.submodule ⟨⊤, isAffineOpen_top _⟩
      simpa only [e.symm_apply_apply] using hw
    have hwL := h hw'
    rw [ambientAffineOpenSubmodule, Submodule.mem_mapPiRingEquiv] at hwL
    change (fun i ↦ e.symm (e (w i))) ∈
      L.submodule ⟨⊤, isAffineOpen_top _⟩ at hwL
    simpa only [e.symm_apply_apply] using hwL

/-- In ambient sections, pullback to `D(f)` is the span of restrictions of global
sections. -/
lemma ambientBasicOpenSubmodule_comap [IsAffine X] (f : Γ(X, ⊤))
    (K : X.SubmoduleSheafData n) :
    ambientBasicOpenSubmodule f (K.comap (X.basicOpen f).ι) =
      Submodule.span Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) n ''
          (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) := by
  rw [ambientBasicOpenSubmodule,
    K.comap_submodule_eq_span (X.basicOpen f).ι
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top X⟩)
      (by intro x _; trivial),
    Submodule.mapPiRingEquiv_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    change X.resPi (X.basicOpen_le f) n w =
      fun i ↦ (X.basicOpen f).topIso.hom.hom
        ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n w i)
    exact (topIso_hom_basicOpenι_appPi_top f w).symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(X.basicOpen f).ι.appPi (⊤ : X.Opens)
      (by intro x _; trivial) n w, ⟨w, hw, rfl⟩, ?_⟩
    change (fun i ↦ (X.basicOpen f).topIso.hom.hom
      ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n w i)) =
        X.resPi (X.basicOpen_le f) n w
    exact topIso_hom_basicOpenι_appPi_top f w

/-- Inclusion of data on a restricted affine basic open can be checked after transporting
its global module to ambient sections. -/
lemma le_iff_ambientBasicOpenSubmodule_le [IsAffine X] (f : Γ(X, ⊤))
    {K L : (X.basicOpen f).toScheme.SubmoduleSheafData n} :
    K ≤ L ↔ ambientBasicOpenSubmodule f K ≤ ambientBasicOpenSubmodule f L := by
  rw [le_iff_submodule_top_le]
  constructor
  · intro h
    exact Submodule.map_mono h
  · intro h w hw
    let e := (X.basicOpen f).topIso.commRingCatIsoToRingEquiv
    have hw' : (fun i ↦ e (w i)) ∈
        ambientBasicOpenSubmodule f K := by
      rw [ambientBasicOpenSubmodule, Submodule.mem_mapPiRingEquiv]
      change (fun i ↦ e.symm (e (w i))) ∈ K.submodule ⟨⊤, isAffineOpen_top _⟩
      simpa only [e.symm_apply_apply] using hw
    have hwL := h hw'
    rw [ambientBasicOpenSubmodule, Submodule.mem_mapPiRingEquiv] at hwL
    change (fun i ↦ e.symm (e (w i))) ∈ L.submodule ⟨⊤, isAffineOpen_top _⟩ at hwL
    simpa only [e.symm_apply_apply] using hwL

/-- Applying the canonical top-sections isomorphism carries the span of pulled-back
vectors to the span of their ordinary restrictions. -/
lemma topIso_homPi_mem_span_basicOpenι [IsAffine X] (f : Γ(X, ⊤))
    {W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤))}
    {z : Fin n → Γ((X.basicOpen f).toScheme, ⊤)}
    (hz : z ∈ Submodule.span Γ((X.basicOpen f).toScheme, ⊤)
      ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n ''
        (W : Set (Fin n → Γ(X, ⊤))))) :
    (fun i ↦ (X.basicOpen f).topIso.hom.hom (z i)) ∈
      Submodule.span Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) n '' (W : Set (Fin n → Γ(X, ⊤)))) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      rw [topIso_hom_basicOpenι_appPi_top]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero =>
      have hzero : (fun i ↦ (X.basicOpen f).topIso.hom.hom ((0 :
          Fin n → Γ((X.basicOpen f).toScheme, ⊤)) i)) = 0 := by
        funext i
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add z₁ z₂ _ _ ih₁ ih₂ =>
      convert Submodule.add_mem _ ih₁ ih₂ using 1
      funext i
      simp
  | smul c z _ ih =>
      have h := Submodule.smul_mem
        (Submodule.span Γ(X, X.basicOpen f)
          (X.resPi (X.basicOpen_le f) n '' (W : Set (Fin n → Γ(X, ⊤)))))
        ((X.basicOpen f).topIso.hom.hom c) ih
      convert h using 1
      funext i
      simp [smul_eq_mul]

/-- Applying the inverse top-sections isomorphism carries the span of ordinary
restrictions back to the span of pullbacks to the restricted scheme. -/
lemma topIso_invPi_mem_span_basicOpenι [IsAffine X] (f : Γ(X, ⊤))
    {W : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤))}
    {z : Fin n → Γ(X, X.basicOpen f)}
    (hz : z ∈ Submodule.span Γ(X, X.basicOpen f)
      (X.resPi (X.basicOpen_le f) n '' (W : Set (Fin n → Γ(X, ⊤))))) :
    (fun i ↦ (X.basicOpen f).topIso.inv.hom (z i)) ∈
      Submodule.span Γ((X.basicOpen f).toScheme, ⊤)
        ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n ''
          (W : Set (Fin n → Γ(X, ⊤)))) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨w, hw, ?_⟩
      funext i
      have hi := congrFun (topIso_hom_basicOpenι_appPi_top f w) i
      rw [← hi]
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  | zero =>
      have hzero : (fun i ↦ (X.basicOpen f).topIso.inv.hom ((0 :
          Fin n → Γ(X, X.basicOpen f)) i)) = 0 := by
        funext i
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add z₁ z₂ _ _ ih₁ ih₂ =>
      convert Submodule.add_mem _ ih₁ ih₂ using 1
      funext i
      simp
  | smul c z _ ih =>
      have h := Submodule.smul_mem
        (Submodule.span Γ((X.basicOpen f).toScheme, ⊤)
          ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n ''
            (W : Set (Fin n → Γ(X, ⊤)))))
        ((X.basicOpen f).topIso.inv.hom c) ih
      convert h using 1
      funext i
      simp [smul_eq_mul]

/-- Pullback from `D(f)` to the canonical overlap `D(fg)`, transported to ambient
sections, is the span of the ordinary restrictions from `D(f)`. -/
lemma ambientBasicOpenSubmodule_comap_mul_left [IsAffine X] (f g : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    ambientBasicOpenSubmodule (f * g)
        (K.comap (X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left))) =
      Submodule.span Γ(X, X.basicOpen (f * g))
        (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n ''
          (ambientBasicOpenSubmodule f K : Set (Fin n → Γ(X, X.basicOpen f)))) := by
  let h : (X.basicOpen (f * g)).toScheme ⟶ (X.basicOpen f).toScheme :=
    X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)
  have hcomm : h.appTop ≫ (X.basicOpen (f * g)).topIso.hom =
      (X.basicOpen f).topIso.hom ≫
        X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op := by
    simp only [h, Scheme.homOfLE_appTop, Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  rw [ambientBasicOpenSubmodule,
    K.comap_submodule_eq_span h
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩)
      (by intro x _; trivial),
    Submodule.mapPiRingEquiv_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i ↦ (X.basicOpen f).topIso.hom.hom (v i), ?_, ?_⟩
    · exact ⟨v, hv, rfl⟩
    · rw [h.appPi_top]
      funext i
      change (X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom
            ((X.basicOpen f).topIso.hom.hom (v i)) =
        (X.basicOpen (f * g)).topIso.hom.hom (h.appTop.hom (v i))
      have hi := congrArg (fun φ : Γ((X.basicOpen f).toScheme, ⊤) ⟶
          Γ(X, X.basicOpen (f * g)) ↦ φ.hom (v i)) hcomm
      simpa only [CommRingCat.comp_apply] using hi.symm
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨h.appPi (⊤ : (X.basicOpen f).toScheme.Opens)
      (by intro x _; trivial) n v, ⟨v, hv, rfl⟩, ?_⟩
    · rw [h.appPi_top]
      funext i
      change (X.basicOpen (f * g)).topIso.hom.hom (h.appTop.hom (v i)) =
        (X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom
            ((X.basicOpen f).topIso.hom.hom (v i))
      have hi := congrArg (fun φ : Γ((X.basicOpen f).toScheme, ⊤) ⟶
          Γ(X, X.basicOpen (f * g)) ↦ φ.hom (v i)) hcomm
      simpa only [CommRingCat.comp_apply] using hi

/-- Right-hand counterpart of `ambientBasicOpenSubmodule_comap_mul_left`. -/
lemma ambientBasicOpenSubmodule_comap_mul_right [IsAffine X] (f g : Γ(X, ⊤))
    (K : (X.basicOpen g).toScheme.SubmoduleSheafData n) :
    ambientBasicOpenSubmodule (f * g)
        (K.comap (X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right))) =
      Submodule.span Γ(X, X.basicOpen (f * g))
        (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_right) n ''
          (ambientBasicOpenSubmodule g K : Set (Fin n → Γ(X, X.basicOpen g)))) := by
  let h : (X.basicOpen (f * g)).toScheme ⟶ (X.basicOpen g).toScheme :=
    X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)
  have hcomm : h.appTop ≫ (X.basicOpen (f * g)).topIso.hom =
      (X.basicOpen g).topIso.hom ≫
        X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op := by
    simp only [h, Scheme.homOfLE_appTop, Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  rw [ambientBasicOpenSubmodule,
    K.comap_submodule_eq_span h
      (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩)
      (by intro x _; trivial),
    Submodule.mapPiRingEquiv_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i ↦ (X.basicOpen g).topIso.hom.hom (v i), ?_, ?_⟩
    · exact ⟨v, hv, rfl⟩
    · rw [h.appPi_top]
      funext i
      change (X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom
            ((X.basicOpen g).topIso.hom.hom (v i)) =
        (X.basicOpen (f * g)).topIso.hom.hom (h.appTop.hom (v i))
      have hi := congrArg (fun φ : Γ((X.basicOpen g).toScheme, ⊤) ⟶
          Γ(X, X.basicOpen (f * g)) ↦ φ.hom (v i)) hcomm
      simpa only [CommRingCat.comp_apply] using hi.symm
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨h.appPi (⊤ : (X.basicOpen g).toScheme.Opens)
      (by intro x _; trivial) n v, ⟨v, hv, rfl⟩, ?_⟩
    · rw [h.appPi_top]
      funext i
      change (X.basicOpen (f * g)).topIso.hom.hom (h.appTop.hom (v i)) =
        (X.presheaf.map
          (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom
            ((X.basicOpen g).topIso.hom.hom (v i))
      have hi := congrArg (fun φ : Γ((X.basicOpen g).toScheme, ⊤) ⟶
          Γ(X, X.basicOpen (f * g)) ↦ φ.hom (v i)) hcomm
      simpa only [CommRingCat.comp_apply] using hi

/-- Equality of local data on the canonical overlap `D(fg)` is exactly equality of
the two ambient localized spans used by finite affine basic-open descent. -/
lemma span_overlap_eq_of_comap_eq_mul [IsAffine X] (f g : Γ(X, ⊤))
    (Kf : (X.basicOpen f).toScheme.SubmoduleSheafData n)
    (Kg : (X.basicOpen g).toScheme.SubmoduleSheafData n)
    (h : Kf.comap (X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)) =
      Kg.comap (X.homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right))) :
    Submodule.span Γ(X, X.basicOpen (f * g))
        (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n ''
          (ambientBasicOpenSubmodule f Kf : Set (Fin n → Γ(X, X.basicOpen f)))) =
      Submodule.span Γ(X, X.basicOpen (f * g))
        (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_right) n ''
          (ambientBasicOpenSubmodule g Kg : Set (Fin n → Γ(X, X.basicOpen g)))) := by
  rw [← ambientBasicOpenSubmodule_comap_mul_left,
    ← ambientBasicOpenSubmodule_comap_mul_right, h]

/-- Equality after pullback to a restricted basic-open scheme implies equality of the
corresponding localized global submodules in the ambient scheme's section ring. -/
lemma span_resPi_eq_of_comap_eq_basicOpen [IsAffine X] (f : Γ(X, ⊤))
    (K L : X.SubmoduleSheafData n)
    (h : K.comap (X.basicOpen f).ι = L.comap (X.basicOpen f).ι) :
    Submodule.span Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) n ''
          (K.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) =
      Submodule.span Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) n ''
          (L.submodule ⟨⊤, isAffineOpen_top X⟩ : Set (Fin n → Γ(X, ⊤)))) := by
  let D := (X.basicOpen f).toScheme
  let Dtop : D.affineOpens := ⟨⊤, isAffineOpen_top D⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have htop := congrArg (fun M : D.SubmoduleSheafData n ↦ M.submodule Dtop) h
  rw [K.comap_submodule_eq_span (X.basicOpen f).ι
      (U' := Dtop) (V := Xtop) (by intro x _; trivial),
    L.comap_submodule_eq_span (X.basicOpen f).ι
      (U' := Dtop) (V := Xtop) (by intro x _; trivial)] at htop
  dsimp [Dtop, Xtop, D] at htop
  apply le_antisymm
  · intro z hz
    have hz' := topIso_invPi_mem_span_basicOpenι f hz
    rw [htop] at hz'
    have hz'' := topIso_homPi_mem_span_basicOpenι f hz'
    have hround : (fun i ↦ (X.basicOpen f).topIso.hom.hom
        ((X.basicOpen f).topIso.inv.hom (z i))) = z := by
      funext i
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    rwa [hround] at hz''
  · intro z hz
    have hz' := topIso_invPi_mem_span_basicOpenι f hz
    rw [← htop] at hz'
    have hz'' := topIso_homPi_mem_span_basicOpenι f hz'
    have hround : (fun i ↦ (X.basicOpen f).topIso.hom.hom
        ((X.basicOpen f).topIso.inv.hom (z i))) = z := by
      funext i
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    rwa [hround] at hz''

/-- Quasi-coherent submodule data on an affine scheme satisfy uniqueness of descent
for a basic-open cover. -/
lemma eq_of_comap_eq_of_iSup_basicOpen_eq_top [IsAffine X]
    {ι : Type*} (f : ι → Γ(X, ⊤)) (K L : X.SubmoduleSheafData n)
    (hcover : ⨆ i, X.basicOpen (f i) = ⊤)
    (hlocal : ∀ i, K.comap (X.basicOpen (f i)).ι =
      L.comap (X.basicOpen (f i)).ι) :
    K = L :=
  eq_of_span_resPi_eq_of_iSup_basicOpen_eq_top f K L hcover fun i ↦
    span_resPi_eq_of_comap_eq_basicOpen (f i) K L (hlocal i)

/-- The affine extension of a quasi-coherent submodule datum on `D(f)`, obtained by
contracting its module of global sections and sheafifying on the ambient affine scheme. -/
def affineBasicOpenExtension [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    X.SubmoduleSheafData n :=
  ofAffineSubmodule ((K.submodule ⟨⊤, isAffineOpen_top _⟩).comapPi)

/-- Restricting the explicit affine extension to `D(f)` recovers the original datum. -/
@[simp]
lemma affineBasicOpenExtension_comap [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    (affineBasicOpenExtension f K).comap (X.basicOpen f).ι = K := by
  let D := (X.basicOpen f).toScheme
  let Dtop : D.affineOpens := ⟨⊤, isAffineOpen_top D⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let C : Submodule Γ(X, ⊤) (Fin n → Γ(X, ⊤)) :=
    (K.submodule Dtop).comapPi
  have htop : ((affineBasicOpenExtension f K).comap (X.basicOpen f).ι).submodule Dtop =
      K.submodule Dtop := by
    rw [(affineBasicOpenExtension f K).comap_submodule_eq_span (X.basicOpen f).ι
      (U' := Dtop) (V := Xtop) (by intro x _; trivial)]
    change Submodule.span Γ(D, Dtop.1)
      ((X.basicOpen f).ι.appPi Xtop.1 (by intro x _; trivial) n ''
        ((ofAffineSubmodule C).submodule Xtop : Set (Fin n → Γ(X, Xtop.1)))) =
      K.submodule Dtop
    rw [ofAffineSubmodule_submodule_top]
    dsimp [affineBasicOpenExtension, Dtop, Xtop, C, D]
    change Submodule.span Γ((X.basicOpen f).toScheme, ⊤)
      ((X.basicOpen f).ι.appPi (⊤ : X.Opens) (by intro x _; trivial) n ''
        ((K.submodule ⟨⊤, isAffineOpen_top _⟩).comapPi (A := Γ(X, ⊤)) :
          Set (Fin n → Γ(X, ⊤)))) = K.submodule ⟨⊤, isAffineOpen_top _⟩
    rw [basicOpenι_appPi_top f]
    exact Submodule.span_image_comapPi_of_isLocalization (Submonoid.powers f)
      (K.submodule Dtop)
  apply SubmoduleSheafData.ext
  funext U
  rw [submodule_eq_span_top
      ((affineBasicOpenExtension f K).comap (X.basicOpen f).ι) U,
    submodule_eq_span_top K U, htop]

/-- Extension followed by restriction is the identity for a quasi-coherent submodule
datum on an affine basic open. This is the extension--restriction input for Zariski
descent. -/
lemma comap_map_eq_affineBasicOpen [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    (K.map (X.basicOpen f).ι).comap (X.basicOpen f).ι = K := by
  apply le_antisymm (comap_map_le K (X.basicOpen f).ι)
  have hLmap : affineBasicOpenExtension f K ≤ K.map (X.basicOpen f).ι :=
    le_map_iff_comap_le.mpr (affineBasicOpenExtension_comap f K).le
  exact (affineBasicOpenExtension_comap f K).ge.trans
    (comap_mono hLmap (X.basicOpen f).ι)

/-- The order-theoretic direct image from an affine basic open is the explicit affine
extension obtained by contracting global sections. -/
lemma map_eq_affineBasicOpenExtension [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    K.map (X.basicOpen f).ι = affineBasicOpenExtension f K := by
  let D := (X.basicOpen f).toScheme
  let Dtop : D.affineOpens := ⟨⊤, isAffineOpen_top D⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  apply le_antisymm
  · apply le_iff_submodule_top_le.mpr
    intro w hw
    rw [affineBasicOpenExtension, ofAffineSubmodule_submodule_top]
    apply (Submodule.mem_comapPi (K.submodule Dtop) w).mpr
    have hres : (X.basicOpen f).ι.appPi Xtop.1 (by intro x _; trivial) n w ∈
        ((K.map (X.basicOpen f).ι).comap (X.basicOpen f).ι).submodule Dtop := by
      rw [(K.map (X.basicOpen f).ι).comap_submodule_eq_span (X.basicOpen f).ι
        (U' := Dtop) (V := Xtop) (by intro x _; trivial)]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    have hk := le_def.mp (comap_map_le K (X.basicOpen f).ι) Dtop hres
    dsimp [Dtop, Xtop, D] at hk ⊢
    rw [basicOpenι_appPi_top f] at hk
    exact hk
  · exact le_map_iff_comap_le.mpr (affineBasicOpenExtension_comap f K).le

/-- On global sections, direct image from `D(f)` is contraction along the localization
map. -/
@[simp]
lemma map_submodule_top_affineBasicOpen [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    (K.map (X.basicOpen f).ι).submodule ⟨⊤, isAffineOpen_top X⟩ =
      (K.submodule ⟨⊤, isAffineOpen_top _⟩).comapPi := by
  rw [map_eq_affineBasicOpenExtension, affineBasicOpenExtension,
    ofAffineSubmodule_submodule_top]

/-- Transporting contraction along the restricted-scheme inclusion through `topIso`
gives ordinary contraction along restriction of ambient sections. -/
lemma map_submodule_top_eq_ambient_comapPi [IsAffine X] (f : Γ(X, ⊤))
    (K : (X.basicOpen f).toScheme.SubmoduleSheafData n) :
    (K.map (X.basicOpen f).ι).submodule ⟨⊤, isAffineOpen_top X⟩ =
      (ambientBasicOpenSubmodule f K).comapPi := by
  rw [map_submodule_top_affineBasicOpen]
  let eB := (X.basicOpen f).topIso.commRingCatIsoToRingEquiv
  letI : Algebra Γ(X, ⊤) Γ((X.basicOpen f).toScheme, ⊤) :=
    (X.basicOpen f).ι.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have h := Submodule.mapPiRingEquiv_comapPi
    (RingEquiv.refl Γ(X, ⊤)) eB (fun x ↦ by
      change (X.basicOpen f).topIso.hom.hom ((X.basicOpen f).ι.appTop.hom x) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x
      rw [← CommRingCat.comp_apply, basicOpenι_appTop_topIso_hom])
    (K.submodule ⟨⊤, isAffineOpen_top _⟩)
  simpa [ambientBasicOpenSubmodule] using h

/-- Ambient global sections of restriction to `D(f)` after maximal extension from
`D(g)`, computed as localization of the contraction of the original ambient module. -/
lemma ambientBasicOpenSubmodule_comap_map [IsAffine X] (f g : Γ(X, ⊤))
    (K : (X.basicOpen g).toScheme.SubmoduleSheafData n) :
    ambientBasicOpenSubmodule f
        ((K.map (X.basicOpen g).ι).comap (X.basicOpen f).ι) =
      Submodule.span Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) n ''
          ((K.map (X.basicOpen g).ι).submodule ⟨⊤, isAffineOpen_top X⟩ :
            Set (Fin n → Γ(X, ⊤)))) := by
  rw [ambientBasicOpenSubmodule_comap]

/-- Beck--Chevalley for a pair of affine basic opens, expressed entirely in ambient
section rings: restriction to `D(f)` of maximal extension from `D(g)` is contraction
from the overlap `D(fg)`. -/
lemma ambientBasicOpenSubmodule_comap_map_eq_overlap_comapPi [IsAffine X]
    (f g : Γ(X, ⊤)) (K : (X.basicOpen g).toScheme.SubmoduleSheafData n) :
    let A := Γ(X, ⊤)
    let B := Γ(X, X.basicOpen g)
    let C := Γ(X, X.basicOpen f)
    let D := Γ(X, X.basicOpen (f * g))
    letI : Algebra A B :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI : Algebra A C :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    letI : Algebra A D :=
      (X.presheaf.map (homOfLE (X.basicOpen_le (f * g))).op).hom.toAlgebra
    letI : Algebra B D :=
      (X.presheaf.map (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_right)).op).hom.toAlgebra
    letI : Algebra C D :=
      (X.presheaf.map (homOfLE ((X.basicOpen_mul f g).le.trans inf_le_left)).op).hom.toAlgebra
    ambientBasicOpenSubmodule f
        ((K.map (X.basicOpen g).ι).comap (X.basicOpen f).ι) =
      (Submodule.span D ((fun w i ↦ algebraMap B D (w i)) ''
        (ambientBasicOpenSubmodule g K : Set (Fin n → B)))).comapPi (A := C) := by
  dsimp only
  rw [ambientBasicOpenSubmodule_comap_map,
    map_submodule_top_eq_ambient_comapPi]
  exact span_resPi_comapPi_eq_comapPi_span_resPi_basicOpen f g
    (ambientBasicOpenSubmodule g K)

/-- Equality of two local data after restriction to the canonical overlap `D(fg)`
implies the extension--restriction containment needed for finite basic-open gluing. -/
lemma le_comap_map_of_span_overlap_eq [IsAffine X] (f g : Γ(X, ⊤))
    (Kf : (X.basicOpen f).toScheme.SubmoduleSheafData n)
    (Kg : (X.basicOpen g).toScheme.SubmoduleSheafData n)
    (h : Submodule.span Γ(X, X.basicOpen (f * g))
          (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n ''
            (ambientBasicOpenSubmodule f Kf :
              Set (Fin n → Γ(X, X.basicOpen f)))) =
        Submodule.span Γ(X, X.basicOpen (f * g))
          (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_right) n ''
            (ambientBasicOpenSubmodule g Kg :
              Set (Fin n → Γ(X, X.basicOpen g))))) :
    Kf ≤ (Kg.map (X.basicOpen g).ι).comap (X.basicOpen f).ι := by
  apply (le_iff_ambientBasicOpenSubmodule_le f).mpr
  rw [ambientBasicOpenSubmodule_comap_map_eq_overlap_comapPi]
  intro z hz
  change X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n z ∈
    Submodule.span Γ(X, X.basicOpen (f * g))
      (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_right) n ''
        (ambientBasicOpenSubmodule g Kg :
          Set (Fin n → Γ(X, X.basicOpen g))))
  have hz' : X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n z ∈
      Submodule.span Γ(X, X.basicOpen (f * g))
        (X.resPi ((X.basicOpen_mul f g).le.trans inf_le_left) n ''
          (ambientBasicOpenSubmodule f Kf :
            Set (Fin n → Γ(X, X.basicOpen f)))) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  rw [h] at hz'
  exact hz'

/-- Restriction to an affine basic open preserves binary intersections of
quasi-coherent submodule data. -/
lemma comap_inf_affineBasicOpen [IsAffine X] (f : Γ(X, ⊤))
    (K L : X.SubmoduleSheafData n) :
    (K ⊓ L).comap (X.basicOpen f).ι =
      K.comap (X.basicOpen f).ι ⊓ L.comap (X.basicOpen f).ι := by
  let D := (X.basicOpen f).toScheme
  let Dtop : D.affineOpens := ⟨⊤, isAffineOpen_top D⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have htop : ((K ⊓ L).comap (X.basicOpen f).ι).submodule Dtop =
      (K.comap (X.basicOpen f).ι ⊓ L.comap (X.basicOpen f).ι).submodule Dtop := by
    rw [submodule_inf,
      (K ⊓ L).comap_submodule_eq_span (X.basicOpen f).ι
        (U' := Dtop) (V := Xtop) (by intro x _; trivial),
      K.comap_submodule_eq_span (X.basicOpen f).ι
        (U' := Dtop) (V := Xtop) (by intro x _; trivial),
      L.comap_submodule_eq_span (X.basicOpen f).ι
        (U' := Dtop) (V := Xtop) (by intro x _; trivial)]
    dsimp [Dtop, Xtop, D]
    rw [submodule_inf, basicOpenι_appPi_top f,
      Submodule.span_image_inf_of_isLocalization_away (g := f)]
  rw [← ofAffineSubmodule_submodule ((K ⊓ L).comap (X.basicOpen f).ι),
    ← ofAffineSubmodule_submodule
      (K.comap (X.basicOpen f).ι ⊓ L.comap (X.basicOpen f).ι), htop]

/-- Restriction to an affine basic open preserves nonempty finite intersections. -/
lemma comap_inf'_affineBasicOpen [IsAffine X] (f : Γ(X, ⊤))
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (K : ι → X.SubmoduleSheafData n) :
    (s.inf' hs K).comap (X.basicOpen f).ι =
      s.inf' hs (fun i ↦ (K i).comap (X.basicOpen f).ι) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
      simp only [Finset.inf'_cons hs, comap_inf_affineBasicOpen, ih]

/-- A finite family of submodule data on affine basic opens extends to the ambient affine
scheme by intersecting its direct images. -/
noncomputable def glueAffineBasicOpen [IsAffine X] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Γ(X, ⊤))
    (K : ∀ i, (X.basicOpen (f i)).toScheme.SubmoduleSheafData n) :
    X.SubmoduleSheafData n :=
  s.inf' hs fun i ↦ (K i).map (X.basicOpen (f i)).ι

/-- The finite affine-basic-open gluing construction restricts to the prescribed datum whenever
every prescribed local datum is contained in every other datum after extension and restriction.
This is the order-theoretic effectivity step in Zariski descent for submodule sheaves. -/
lemma glueAffineBasicOpen_comap [IsAffine X] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Γ(X, ⊤))
    (K : ∀ i, (X.basicOpen (f i)).toScheme.SubmoduleSheafData n)
    (hcompat : ∀ i, i ∈ s → ∀ j, j ∈ s →
      K i ≤ ((K j).map (X.basicOpen (f j)).ι).comap (X.basicOpen (f i)).ι)
    {i : ι} (hi : i ∈ s) :
    (glueAffineBasicOpen s hs f K).comap (X.basicOpen (f i)).ι = K i := by
  rw [glueAffineBasicOpen, comap_inf'_affineBasicOpen]
  apply le_antisymm
  · exact Finset.inf'_le_of_le _ hi (comap_map_le (K i) (X.basicOpen (f i)).ι)
  · exact Finset.le_inf' _ _ fun j hj ↦ hcompat i hi j hj

/-- Finite affine-basic-open descent from equality of the ambient localized submodules
on every canonical overlap `D(f_i f_j)`. -/
lemma glueAffineBasicOpen_comap_of_span_overlap_eq [IsAffine X] {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Γ(X, ⊤))
    (K : ∀ i, (X.basicOpen (f i)).toScheme.SubmoduleSheafData n)
    (hcompat : ∀ i, i ∈ s → ∀ j, j ∈ s →
      Submodule.span Γ(X, X.basicOpen (f i * f j))
          (X.resPi ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_left) n ''
            (ambientBasicOpenSubmodule (f i) (K i) :
              Set (Fin n → Γ(X, X.basicOpen (f i))))) =
        Submodule.span Γ(X, X.basicOpen (f i * f j))
          (X.resPi ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_right) n ''
            (ambientBasicOpenSubmodule (f j) (K j) :
              Set (Fin n → Γ(X, X.basicOpen (f j))))))
    {i : ι} (hi : i ∈ s) :
    (glueAffineBasicOpen s hs f K).comap (X.basicOpen (f i)).ι = K i := by
  apply glueAffineBasicOpen_comap s hs f K _ hi
  intro a ha b hb
  exact le_comap_map_of_span_overlap_eq (f a) (f b) (K a) (K b)
    (hcompat a ha b hb)

/-- Finite affine basic-open descent in its geometric form: equality of the two
pullbacks to every canonical overlap `D(f_i f_j)` implies that the glued datum
restricts to the prescribed datum on each member of the cover. -/
lemma glueAffineBasicOpen_comap_of_comap_eq_mul [IsAffine X] {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Γ(X, ⊤))
    (K : ∀ i, (X.basicOpen (f i)).toScheme.SubmoduleSheafData n)
    (hcompat : ∀ i, i ∈ s → ∀ j, j ∈ s →
      (K i).comap
          (X.homOfLE ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_left)) =
        (K j).comap
          (X.homOfLE ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_right)))
    {i : ι} (hi : i ∈ s) :
    (glueAffineBasicOpen s hs f K).comap (X.basicOpen (f i)).ι = K i := by
  apply glueAffineBasicOpen_comap_of_span_overlap_eq s hs f K _ hi
  intro a ha b hb
  exact span_overlap_eq_of_comap_eq_mul (f a) (f b) (K a) (K b)
    (hcompat a ha b hb)

/-- Effectivity of compatible submodule data after choosing a finite basic-open
refinement of an open cover.  Compatibility is stated on arbitrary common sources,
which is the form supplied by a compatible family of elements of a presheaf. -/
lemma exists_submoduleSheafData_of_finite_basicOpen_refinement [IsAffine X]
    {κ : Type*} [Finite κ] [Nonempty κ] (f : κ → Γ(X, ⊤))
    (𝒰 : X.OpenCover) (j : κ → 𝒰.I₀)
    (k : ∀ i, (X.basicOpen (f i)).toScheme ⟶ 𝒰.X (j i))
    (hfac : ∀ i, k i ≫ 𝒰.f (j i) = (X.basicOpen (f i)).ι)
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b) :
    ∃ L : X.SubmoduleSheafData n, ∀ i,
      L.comap (X.basicOpen (f i)).ι = (K (j i)).comap (k i) := by
  letI := Fintype.ofFinite κ
  let K' (i : κ) : (X.basicOpen (f i)).toScheme.SubmoduleSheafData n :=
    (K (j i)).comap (k i)
  have hcompat' : ∀ i, i ∈ Finset.univ → ∀ j, j ∈ Finset.univ →
      (K' i).comap
          (X.homOfLE ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_left)) =
        (K' j).comap
          (X.homOfLE ((X.basicOpen_mul (f i) (f j)).le.trans inf_le_right)) := by
    intro a _ b _
    let ha := X.homOfLE ((X.basicOpen_mul (f a) (f b)).le.trans inf_le_left)
    let hb := X.homOfLE ((X.basicOpen_mul (f a) (f b)).le.trans inf_le_right)
    have hab : ha ≫ k a ≫ 𝒰.f (j a) = hb ≫ k b ≫ 𝒰.f (j b) := by
      simp only [hfac, ha, hb, Scheme.homOfLE_ι]
    calc
      (K' a).comap ha = (K (j a)).comap (ha ≫ k a) :=
        ((K (j a)).comap_comp ha (k a)).symm
      _ = (K (j b)).comap (hb ≫ k b) := hcompat (j a) (j b) _ _ _ hab
      _ = (K' b).comap hb := (K (j b)).comap_comp hb (k b)
  let L := glueAffineBasicOpen Finset.univ Finset.univ_nonempty f K'
  refine ⟨L, fun i ↦ ?_⟩
  exact glueAffineBasicOpen_comap_of_comap_eq_mul Finset.univ
    Finset.univ_nonempty f K' hcompat' (Finset.mem_univ i)

/-- Zariski-local uniqueness for quasi-coherent submodule data on an affine scheme:
two data are equal if their pullbacks agree on every member of an arbitrary open cover. -/
lemma eq_of_comap_eq_openCover_of_isAffine [IsAffine X] (𝒰 : X.OpenCover)
    (K L : X.SubmoduleSheafData n)
    (hlocal : ∀ i, K.comap (𝒰.f i) = L.comap (𝒰.f i)) : K = L := by
  obtain ⟨κ, _, f, j, k, hfac, hcover⟩ := exists_finite_basicOpen_refinement_lift 𝒰
  apply eq_of_comap_eq_of_iSup_basicOpen_eq_top f K L hcover
  intro i
  calc
    K.comap (X.basicOpen (f i)).ι = K.comap (k i ≫ 𝒰.f (j i)) := by rw [hfac]
    _ = (K.comap (𝒰.f (j i))).comap (k i) := K.comap_comp _ _
    _ = (L.comap (𝒰.f (j i))).comap (k i) := by rw [hlocal]
    _ = L.comap (k i ≫ 𝒰.f (j i)) := (L.comap_comp _ _).symm
    _ = L.comap (X.basicOpen (f i)).ι := by rw [hfac]

/-- Equality after pullback to the restricted scheme of an affine open detects the
corresponding affine component of quasi-coherent submodule data. -/
lemma submodule_eq_of_comap_eq_affineOpen (U : X.affineOpens)
    (K L : X.SubmoduleSheafData n) (h : K.comap U.1.ι = L.comap U.1.ι) :
    K.submodule U = L.submodule U := by
  rw [← ambientAffineOpenSubmodule_comap U K,
    ← ambientAffineOpenSubmodule_comap U L, h]

/-- Quasi-coherent submodule data are determined by their restrictions to all affine
open subschemes. -/
lemma eq_of_forall_affineOpen_comap_eq (K L : X.SubmoduleSheafData n)
    (h : ∀ U : X.affineOpens, K.comap U.1.ι = L.comap U.1.ι) : K = L := by
  apply SubmoduleSheafData.ext
  funext U
  exact submodule_eq_of_comap_eq_affineOpen U K L (h U)

set_option backward.isDefEq.respectTransparency false in
/-- Zariski-local uniqueness for quasi-coherent submodule data on an arbitrary scheme. -/
lemma eq_of_comap_eq_openCover (𝒰 : X.OpenCover) (K L : X.SubmoduleSheafData n)
    (hlocal : ∀ i, K.comap (𝒰.f i) = L.comap (𝒰.f i)) : K = L := by
  apply eq_of_forall_affineOpen_comap_eq K L
  intro U
  let 𝒱 : U.1.toScheme.OpenCover := 𝒰.pullback₁ U.1.ι
  apply eq_of_comap_eq_openCover_of_isAffine 𝒱
  intro i
  let p : 𝒱.X i ⟶ 𝒰.X i := 𝒰.pullbackHom U.1.ι i
  calc
    (K.comap U.1.ι).comap (𝒱.f i) = K.comap (𝒱.f i ≫ U.1.ι) :=
      (K.comap_comp _ _).symm
    _ = K.comap (p ≫ 𝒰.f i) := by rw [𝒰.pullbackHom_map]
    _ = (K.comap (𝒰.f i)).comap p := K.comap_comp _ _
    _ = (L.comap (𝒰.f i)).comap p := by rw [hlocal]
    _ = L.comap (p ≫ 𝒰.f i) := (L.comap_comp _ _).symm
    _ = L.comap (𝒱.f i ≫ U.1.ι) := by rw [𝒰.pullbackHom_map]
    _ = (L.comap U.1.ι).comap (𝒱.f i) := L.comap_comp _ _
set_option backward.isDefEq.respectTransparency false in
lemma exists_submoduleSheafData_of_affine_openCover_of_nonempty [IsAffine X] [Nonempty X]
    (𝒰 : X.OpenCover)
    [∀ i, IsAffine (𝒰.X i)] (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b) :
    ∃ L : X.SubmoduleSheafData n, ∀ i, L.comap (𝒰.f i) = K i := by
  obtain ⟨κ, hκ, f, j, k, hfac, hcover⟩ :=
    exists_finite_basicOpen_refinement_lift 𝒰
  letI : Finite κ := hκ
  letI : Nonempty κ := by
    let x : X := Classical.choice inferInstance
    have hx : x ∈ ⨆ i, X.basicOpen (f i) := by rw [hcover]; trivial
    rw [Opens.mem_iSup] at hx
    exact ⟨hx.choose⟩
  obtain ⟨L, hL⟩ := exists_submoduleSheafData_of_finite_basicOpen_refinement
    f 𝒰 j k hfac K hcompat
  refine ⟨L, fun a ↦ ?_⟩
  let 𝒱 : X.OpenCover :=
    X.openCoverOfIsOpenCover (fun i ↦ X.basicOpen (f i)) hcover
  let 𝒲 : (𝒰.X a).OpenCover := 𝒱.pullback₁ (𝒰.f a)
  apply eq_of_comap_eq_openCover_of_isAffine 𝒲
  intro i
  let b : 𝒱.I₀ := i
  let c : κ := b
  let p : 𝒲.X i ⟶ 𝒱.X b := 𝒱.pullbackHom (𝒰.f a) i
  let q : 𝒱.X b ⟶ 𝒰.X (j c) := k c
  have hq : q ≫ 𝒰.f (j c) = 𝒱.f b := hfac c
  have hL' : L.comap (𝒱.f b) = (K (j c)).comap q := hL c
  have hp : p ≫ q ≫ 𝒰.f (j c) = 𝒲.f i ≫ 𝒰.f a := by
    rw [hq]
    exact 𝒱.pullbackHom_map (𝒰.f a) i
  calc
    (L.comap (𝒰.f a)).comap (𝒲.f i) = L.comap (𝒲.f i ≫ 𝒰.f a) :=
      (L.comap_comp _ _).symm
    _ = L.comap (p ≫ 𝒱.f b) := by rw [𝒱.pullbackHom_map]
    _ = (L.comap (𝒱.f b)).comap p := L.comap_comp _ _
    _ = ((K (j c)).comap q).comap p := by rw [hL']
    _ = (K (j c)).comap (p ≫ q) := (K (j c)).comap_comp _ _ |>.symm
    _ = (K a).comap (𝒲.f i) := hcompat (j c) a _ _ _ hp
lemma exists_submoduleSheafData_of_affine_openCover [IsAffine X]
    (𝒰 : X.OpenCover)
    [∀ i, IsAffine (𝒰.X i)] (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b) :
    ∃ L : X.SubmoduleSheafData n, ∀ i, L.comap (𝒰.f i) = K i := by
  cases isEmpty_or_nonempty X with
  | inl h =>
      letI := h
      letI (i : 𝒰.I₀) : IsEmpty (𝒰.X i) :=
        ⟨fun x ↦ isEmptyElim ((𝒰.f i).base x)⟩
      exact ⟨⊥, fun _ ↦ Subsingleton.elim _ _⟩
  | inr h =>
      letI := h
      exact exists_submoduleSheafData_of_affine_openCover_of_nonempty 𝒰 K hcompat

set_option backward.isDefEq.respectTransparency false in
/-- Compatible data on a Zariski cover admit an amalgamation after pullback to any
affine scheme.  No affineness hypothesis is imposed on the members of the original
cover: they are first replaced by their canonical affine refinements. -/
lemma exists_submoduleSheafData_of_isAffine
    (𝒰 : X.OpenCover.{u + 1}) (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ X) :
    ∃ L : Y.SubmoduleSheafData n, ∀ i,
      L.comap ((𝒰.pullback₁ g).f i) =
        (K i).comap (𝒰.pullbackHom g i) := by
  let P : Y.OpenCover.{u + 1} := 𝒰.pullback₁ g
  let A : Y.OpenCover.{u + 1} := P.affineRefinement.openCover
  let r := P.fromAffineRefinement.{u, u + 1}
  let t : P.I₀ → 𝒰.I₀ := fun i ↦ i
  have hP (i) :
      𝒰.pullbackHom g (t i) ≫ 𝒰.f (t i) = P.f i ≫ g :=
    𝒰.pullbackHom_map g i
  let s : A.I₀ → 𝒰.I₀ := fun j ↦ t (r.s₀ j)
  let q : ∀ j, A.X j ⟶ 𝒰.X (s j) :=
    fun j ↦ r.h₀ j ≫ 𝒰.pullbackHom g (s j)
  have hq (j) : q j ≫ 𝒰.f (s j) = A.f j ≫ g := by
    dsimp only [q]
    rw [Category.assoc, hP]
    rw [← Category.assoc, r.w₀]
  let K' : ∀ j, (A.X j).SubmoduleSheafData n :=
    fun j ↦ (K (s j)).comap (q j)
  have hcompat' : ∀ (i j : A.I₀) (Z : Scheme.{u})
      (a : Z ⟶ A.X i) (b : Z ⟶ A.X j),
      a ≫ A.f i = b ≫ A.f j → (K' i).comap a = (K' j).comap b := by
    intro i j Z a b hab
    have hab' :
        (a ≫ q i) ≫ 𝒰.f (s i) = (b ≫ q j) ≫ 𝒰.f (s j) := by
      calc
        (a ≫ q i) ≫ 𝒰.f (s i) = a ≫ (q i ≫ 𝒰.f (s i)) :=
          Category.assoc _ _ _
        _ = a ≫ (A.f i ≫ g) := by rw [hq]
        _ = (a ≫ A.f i) ≫ g := (Category.assoc _ _ _).symm
        _ = (b ≫ A.f j) ≫ g := by rw [hab]
        _ = b ≫ (A.f j ≫ g) := Category.assoc _ _ _
        _ = b ≫ (q j ≫ 𝒰.f (s j)) := by rw [hq]
        _ = (b ≫ q j) ≫ 𝒰.f (s j) := (Category.assoc _ _ _).symm
    calc
      (K' i).comap a = (K (s i)).comap (a ≫ q i) := by
        dsimp only [K']
        exact ((K (s i)).comap_comp a (q i)).symm
      _ = (K (s j)).comap (b ≫ q j) :=
        hcompat (s i) (s j) _ _ _ hab'
      _ = (K' j).comap b := by
        dsimp only [K']
        exact (K (s j)).comap_comp b (q j)
  letI (j : A.I₀) : IsAffine (A.X j) := inferInstance
  obtain ⟨L, hL⟩ :=
    exists_submoduleSheafData_of_affine_openCover A K' hcompat'
  refine ⟨L, fun i ↦ ?_⟩
  let B : (P.X i).OpenCover := A.pullback₁ (P.f i)
  apply eq_of_comap_eq_openCover B
  intro j
  let d : A.I₀ := j
  let p : B.X j ⟶ A.X d := A.pullbackHom (P.f i) j
  have hp : (p ≫ q d) ≫ 𝒰.f (s d) =
      (B.f j ≫ 𝒰.pullbackHom g (t i)) ≫ 𝒰.f (t i) := by
    calc
      (p ≫ q d) ≫ 𝒰.f (s d) = p ≫ (q d ≫ 𝒰.f (s d)) :=
        Category.assoc _ _ _
      _ = p ≫ (A.f d ≫ g) := by rw [hq]
      _ = (p ≫ A.f d) ≫ g := (Category.assoc _ _ _).symm
      _ = (B.f j ≫ P.f i) ≫ g := by rw [A.pullbackHom_map]
      _ = B.f j ≫ (P.f i ≫ g) := Category.assoc _ _ _
      _ = B.f j ≫
          (𝒰.pullbackHom g (t i) ≫ 𝒰.f (t i)) := by rw [hP]
      _ = (B.f j ≫ 𝒰.pullbackHom g (t i)) ≫ 𝒰.f (t i) :=
        (Category.assoc _ _ _).symm
  calc
    (L.comap (P.f i)).comap (B.f j) =
        L.comap (B.f j ≫ P.f i) :=
      (L.comap_comp _ _).symm
    _ = L.comap (p ≫ A.f d) := by rw [A.pullbackHom_map]
    _ = (L.comap (A.f d)).comap p := L.comap_comp _ _
    _ = (K' d).comap p := by rw [hL]
    _ = (K (s d)).comap (p ≫ q d) := by
      dsimp only [K']
      exact ((K (s d)).comap_comp p (q d)).symm
    _ = (K (t i)).comap (B.f j ≫ 𝒰.pullbackHom g (t i)) :=
      hcompat (s d) (t i) _ _ _ hp
    _ = ((K (t i)).comap (𝒰.pullbackHom g (t i))).comap (B.f j) := by
      rw [SubmoduleSheafData.comap_comp]
def IsAmalgamationAlong (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    {Y : Scheme.{u}} (g : Y ⟶ X) (L : Y.SubmoduleSheafData n) : Prop :=
  ∀ i, L.comap ((𝒰.pullback₁ g).f i) =
    (K i).comap (𝒰.pullbackHom g i)

set_option backward.isDefEq.respectTransparency false in
/-- An amalgamation remains an amalgamation after any further base change.  The proof
uses the canonical associativity isomorphism between an iterated pullback and the
pullback along the composite. -/
lemma IsAmalgamationAlong.comap (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    {Y Z : Scheme.{u}} {g : Y ⟶ X} {L : Y.SubmoduleSheafData n}
    (hL : IsAmalgamationAlong 𝒰 K g L) (f : Z ⟶ Y) :
    IsAmalgamationAlong 𝒰 K (f ≫ g) (L.comap f) := by
  intro i
  let j : 𝒰.I₀ := i
  have hc_f : (𝒰.pullback₁ (f ≫ g)).f i =
      Limits.pullback.fst (f ≫ g) (𝒰.f j) := rfl
  have hg_f : (𝒰.pullback₁ g).f j =
      Limits.pullback.fst g (𝒰.f j) := rfl
  have hc_snd : 𝒰.pullbackHom (f ≫ g) i =
      Limits.pullback.snd (f ≫ g) (𝒰.f j) := rfl
  have hg_snd : 𝒰.pullbackHom g j =
      Limits.pullback.snd g (𝒰.f j) := rfl
  let e := Limits.pullbackRightPullbackFstIso g (𝒰.f j) f
  let a := e.inv ≫ Limits.pullback.snd f (Limits.pullback.fst g (𝒰.f j))
  have ha_fst :
      a ≫ Limits.pullback.fst g (𝒰.f j) =
        Limits.pullback.fst (f ≫ g) (𝒰.f j) ≫ f := by
    exact Limits.pullbackRightPullbackFstIso_inv_snd_fst g (𝒰.f j) f
  have ha_snd :
      a ≫ Limits.pullback.snd g (𝒰.f j) =
        Limits.pullback.snd (f ≫ g) (𝒰.f j) := by
    exact Limits.pullbackRightPullbackFstIso_inv_snd_snd g (𝒰.f j) f
  calc
    (L.comap f).comap ((𝒰.pullback₁ (f ≫ g)).f i) =
        L.comap ((𝒰.pullback₁ (f ≫ g)).f i ≫ f) :=
      (L.comap_comp _ _).symm
    _ = L.comap (a ≫ (𝒰.pullback₁ g).f j) := by
      rw [hc_f, hg_f, ha_fst]
    _ = (L.comap ((𝒰.pullback₁ g).f j)).comap a := L.comap_comp _ _
    _ = ((K j).comap (𝒰.pullbackHom g j)).comap a := by rw [hL]
    _ = (K j).comap (a ≫ 𝒰.pullbackHom g j) :=
      ((K j).comap_comp _ _).symm
    _ = (K j).comap (𝒰.pullbackHom (f ≫ g) i) := by
      rw [hg_snd, hc_snd, ha_snd]
noncomputable def affineAmalgamation (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ X) :
    Y.SubmoduleSheafData n :=
  (exists_submoduleSheafData_of_isAffine 𝒰 K hcompat g).choose

/-- The chosen affine amalgamation has the prescribed restrictions. -/
lemma affineAmalgamation_isAmalgamationAlong (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u})
      (a : Z ⟶ 𝒰.X i) (b : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ X) :
    IsAmalgamationAlong 𝒰 K g (affineAmalgamation 𝒰 K hcompat g) :=
  (exists_submoduleSheafData_of_isAffine 𝒰 K hcompat g).choose_spec

/-- An amalgamation over an affine source is uniquely the chosen affine
amalgamation. -/
lemma eq_affineAmalgamation_of_isAmalgamationAlong
    (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y : Scheme.{u}} [IsAffine Y] {g : Y ⟶ X}
    {L : Y.SubmoduleSheafData n} (hL : IsAmalgamationAlong 𝒰 K g L) :
    L = affineAmalgamation 𝒰 K hcompat g := by
  apply eq_of_comap_eq_openCover (𝒰.pullback₁ g)
  intro i
  rw [hL, affineAmalgamation_isAmalgamationAlong 𝒰 K hcompat g]

/-- Pulling prescribed data back from one member of the cover gives an amalgamation
along every morphism factoring through that member. -/
lemma isAmalgamationAlong_comap_coverMember
    (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    (i : 𝒰.I₀) {Y : Scheme.{u}} (f : Y ⟶ 𝒰.X i) :
    IsAmalgamationAlong 𝒰 K (f ≫ 𝒰.f i) ((K i).comap f) := by
  intro j
  let a : (𝒰.pullback₁ (f ≫ 𝒰.f i)).X j ⟶ 𝒰.X i :=
    (𝒰.pullback₁ (f ≫ 𝒰.f i)).f j ≫ f
  let b : (𝒰.pullback₁ (f ≫ 𝒰.f i)).X j ⟶ 𝒰.X j :=
    𝒰.pullbackHom (f ≫ 𝒰.f i) j
  have hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j := by
    exact (𝒰.pullbackHom_map (f ≫ 𝒰.f i) j).symm
  calc
    ((K i).comap f).comap ((𝒰.pullback₁ (f ≫ 𝒰.f i)).f j) =
        (K i).comap a := ((K i).comap_comp _ _).symm
    _ = (K j).comap b := hcompat i j _ _ _ hab

/-- Chosen affine amalgamations are natural under pullback between affine schemes. -/
lemma affineAmalgamation_comap (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    (affineAmalgamation 𝒰 K hcompat g).comap f =
      affineAmalgamation 𝒰 K hcompat (f ≫ g) := by
  let P : Z.OpenCover := 𝒰.pullback₁ (f ≫ g)
  apply eq_of_comap_eq_openCover P
  intro i
  rw [(affineAmalgamation_isAmalgamationAlong 𝒰 K hcompat g).comap 𝒰 K f,
    affineAmalgamation_isAmalgamationAlong 𝒰 K hcompat (f ≫ g)]

/-- The global quasi-coherent submodule datum obtained by assembling the canonical
amalgamations on all affine opens. -/
noncomputable def glueOpenCover (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b) :
    X.SubmoduleSheafData n where
  submodule U :=
    ambientAffineOpenSubmodule U
      (affineAmalgamation 𝒰 K hcompat U.1.ι)
  span_resPi_basicOpen U f := by
    let V : X.affineOpens := X.affineBasicOpen f
    let h : V.1.toScheme ⟶ U.1.toScheme :=
      X.homOfLE (X.basicOpen_le f)
    let L := affineAmalgamation 𝒰 K hcompat U.1.ι
    have hh : h ≫ U.1.ι = V.1.ι := X.homOfLE_ι _
    have hnatural :
        L.comap h = affineAmalgamation 𝒰 K hcompat V.1.ι := by
      calc
        L.comap h = affineAmalgamation 𝒰 K hcompat (h ≫ U.1.ι) :=
          affineAmalgamation_comap 𝒰 K hcompat h U.1.ι
        _ = affineAmalgamation 𝒰 K hcompat V.1.ι := by rw [hh]
    rw [← hnatural]
    exact (ambientAffineOpenSubmodule_comap_homOfLE
      U V (X.basicOpen_le f) L).symm

/-- The assembled datum restricts to the chosen amalgamation on every affine open. -/
lemma glueOpenCover_comap_affineOpen (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    (U : X.affineOpens) :
    (glueOpenCover 𝒰 K hcompat).comap U.1.ι =
      affineAmalgamation 𝒰 K hcompat U.1.ι := by
  apply le_antisymm
  · rw [le_iff_ambientAffineOpenSubmodule_le,
      ambientAffineOpenSubmodule_comap]
    exact le_rfl
  · rw [le_iff_ambientAffineOpenSubmodule_le,
      ambientAffineOpenSubmodule_comap]
    exact le_rfl

/-- The assembled datum pulls back to the chosen amalgamation along every open
immersion with affine source. -/
lemma glueOpenCover_comap_of_isAffine (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ X) [IsOpenImmersion g] :
    (glueOpenCover 𝒰 K hcompat).comap g =
      affineAmalgamation 𝒰 K hcompat g := by
  let V : X.affineOpens :=
    ⟨g ''ᵁ (⊤ : Y.Opens), (isAffineOpen_top Y).image_of_isOpenImmersion g⟩
  letI : IsAffine V.1.toScheme := V.2
  have hrange : Set.range g = Set.range V.1.ι := by
    simp only [V, Scheme.Opens.range_ι]
    exact Set.image_univ.symm
  let e : Y ≅ V.1.toScheme :=
    IsOpenImmersion.isoOfRangeEq g V.1.ι hrange
  have he : e.hom ≫ V.1.ι = g :=
    IsOpenImmersion.isoOfRangeEq_hom_fac g V.1.ι hrange
  calc
    (glueOpenCover 𝒰 K hcompat).comap g =
        (glueOpenCover 𝒰 K hcompat).comap (e.hom ≫ V.1.ι) := by rw [he]
    _ = ((glueOpenCover 𝒰 K hcompat).comap V.1.ι).comap e.hom :=
      (glueOpenCover 𝒰 K hcompat).comap_comp _ _
    _ = (affineAmalgamation 𝒰 K hcompat V.1.ι).comap e.hom := by
      rw [glueOpenCover_comap_affineOpen]
    _ = affineAmalgamation 𝒰 K hcompat (e.hom ≫ V.1.ι) :=
      affineAmalgamation_comap 𝒰 K hcompat e.hom V.1.ι
    _ = affineAmalgamation 𝒰 K hcompat g := by rw [he]

/-- The assembled global datum has the prescribed restriction on every member of the
original open cover. -/
lemma glueOpenCover_comap (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b)
    (i : 𝒰.I₀) :
    (glueOpenCover 𝒰 K hcompat).comap (𝒰.f i) = K i := by
  apply eq_of_comap_eq_openCover (𝒰.X i).affineCover
  intro j
  let f := (𝒰.X i).affineCover.f j
  calc
    ((glueOpenCover 𝒰 K hcompat).comap (𝒰.f i)).comap f =
        (glueOpenCover 𝒰 K hcompat).comap (f ≫ 𝒰.f i) :=
      ((glueOpenCover 𝒰 K hcompat).comap_comp _ _).symm
    _ = affineAmalgamation 𝒰 K hcompat (f ≫ 𝒰.f i) :=
      glueOpenCover_comap_of_isAffine 𝒰 K hcompat _
    _ = (K i).comap f :=
      (eq_affineAmalgamation_of_isAmalgamationAlong 𝒰 K hcompat
        (isAmalgamationAlong_comap_coverMember 𝒰 K hcompat i f)).symm

/-- Compatible quasi-coherent submodule data on an arbitrary Zariski open cover are
effective. -/
lemma exists_submoduleSheafData_of_openCover (𝒰 : X.OpenCover.{u + 1})
    (K : ∀ i, (𝒰.X i).SubmoduleSheafData n)
    (hcompat : ∀ (i j : 𝒰.I₀) (W : Scheme.{u})
      (a : W ⟶ 𝒰.X i) (b : W ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (K i).comap a = (K j).comap b) :
    ∃ L : X.SubmoduleSheafData n, ∀ i, L.comap (𝒰.f i) = K i :=
  ⟨glueOpenCover 𝒰 K hcompat, glueOpenCover_comap 𝒰 K hcompat⟩

/-- Finite affine-basic-open gluing reduced to Beck--Chevalley for the pairwise
pullback squares.  Thus ordinary equality of the two restrictions on every overlap
implies effectivity as soon as restriction of a direct image agrees with direct image
of the restriction across that square. -/
lemma glueAffineBasicOpen_comap_of_overlap [IsAffine X] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Γ(X, ⊤))
    (K : ∀ i, (X.basicOpen (f i)).toScheme.SubmoduleSheafData n)
    (hcompat : ∀ i, i ∈ s → ∀ j, j ∈ s →
      (K i).comap (Limits.pullback.fst (X.basicOpen (f i)).ι (X.basicOpen (f j)).ι) =
        (K j).comap (Limits.pullback.snd (X.basicOpen (f i)).ι (X.basicOpen (f j)).ι))
    (hbaseChange : ∀ i, i ∈ s → ∀ j, j ∈ s →
      ((K j).map (X.basicOpen (f j)).ι).comap (X.basicOpen (f i)).ι =
        ((K j).comap
          (Limits.pullback.snd (X.basicOpen (f i)).ι (X.basicOpen (f j)).ι)).map
          (Limits.pullback.fst (X.basicOpen (f i)).ι (X.basicOpen (f j)).ι))
    {i : ι} (hi : i ∈ s) :
    (glueAffineBasicOpen s hs f K).comap (X.basicOpen (f i)).ι = K i := by
  apply glueAffineBasicOpen_comap s hs f K _ hi
  intro a ha b hb
  rw [hbaseChange a ha b hb, ← hcompat a ha b hb]
  exact le_map_comap (K a)
    (Limits.pullback.fst (X.basicOpen (f a)).ι (X.basicOpen (f b)).ι)

/-- If the quotient by `K` is a vector bundle of rank `q`, so is the quotient by any
pullback of `K`: the pullback of a rank-`q` locally free quotient of `O_Y^{⊕n}` is a
rank-`q` locally free quotient of `O_X^{⊕n}`. -/
lemma QuotientProjectiveOfRank.comap {q : ℕ} {K : Y.SubmoduleSheafData n}
    (hK : K.QuotientProjectiveOfRank q) (f : X ⟶ Y) :
    (K.comap f).QuotientProjectiveOfRank q := by
  intro x
  obtain ⟨V, hyV, hproj, hrank⟩ := hK (f.base x)
  obtain ⟨U₀, hU₀mem, hxU₀, hU₀le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ V.1 from hyV)
  letI : Algebra ↑Γ(Y, V.1) ↑Γ(X, U₀) := (f.appLE V.1 U₀ hU₀le).hom.toAlgebra
  haveI : Module.Finite ↑Γ(Y, V.1) ((Fin n → ↑Γ(Y, V.1)) ⧸ K.submodule V) :=
    Module.Finite.of_surjective (K.submodule V).mkQ (Submodule.mkQ_surjective _)
  haveI hMproj : Module.Projective ↑Γ(Y, V.1)
      ((Fin n → ↑Γ(Y, V.1)) ⧸ K.submodule V) := hproj
  have hsurj : Function.Surjective
      (LinearMap.baseChangePi ↑Γ(X, U₀) (K.submodule V).mkQ) :=
    LinearMap.baseChangePi_surjective _ (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker (LinearMap.baseChangePi ↑Γ(X, U₀) (K.submodule V).mkQ) =
      Submodule.span ↑Γ(X, U₀)
        ((fun w i ↦ algebraMap ↑Γ(Y, V.1) ↑Γ(X, U₀) (w i)) ''
          (K.submodule V : Set (Fin n → ↑Γ(Y, V.1)))) := by
    simpa only [Submodule.ker_mkQ] using
      LinearMap.ker_baseChangePi_eq_span ↑Γ(X, U₀)
        (Submodule.mkQ_surjective (K.submodule V))
  have heq : (K.comap f).submodule ⟨U₀, hU₀mem⟩ =
      LinearMap.ker (LinearMap.baseChangePi ↑Γ(X, U₀) (K.submodule V).mkQ) := by
    rw [K.comap_submodule_eq_span f (U' := ⟨U₀, hU₀mem⟩) (V := V) hU₀le, hker]
    rfl
  let e := Submodule.quotEquivOfEq _ _ heq
  have hbase := LinearMap.quotKer_baseChangePi_finite_projective_rank
    (S := ↑Γ(X, U₀)) (K.submodule V).mkQ (Submodule.mkQ_surjective _) hrank
  refine ⟨⟨U₀, hU₀mem⟩, hxU₀, ?_, ?_⟩
  · letI : Module.Projective ↑Γ(X, U₀)
        ((Fin n → ↑Γ(X, U₀)) ⧸
          LinearMap.ker (LinearMap.baseChangePi ↑Γ(X, U₀) (K.submodule V).mkQ)) :=
      hbase.2.1
    exact Module.Projective.of_equiv e.symm
  · intro p
    have h1 := Module.rankAtStalk_eq_of_equiv e
    calc Module.rankAtStalk ((Fin n → ↑Γ(X, U₀)) ⧸ (K.comap f).submodule ⟨U₀, hU₀mem⟩) p
        = Module.rankAtStalk ((Fin n → ↑Γ(X, U₀)) ⧸
            LinearMap.ker (LinearMap.baseChangePi ↑Γ(X, U₀)
              (K.submodule V).mkQ)) p := congrFun h1 p
      _ = q := hbase.2.2 p

/-- Pullback along an open immersion transports the affine component over an affine
open through the induced ring isomorphism on sections. -/
lemma submodule_comap_of_isOpenImmersion (K : Y.SubmoduleSheafData n)
    (f : X ⟶ Y) [IsOpenImmersion f] (U : X.affineOpens) :
    (K.comap f).submodule U =
      (K.submodule
        ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩).mapPiRingEquiv
          (f.appIso U.1).commRingCatIsoToRingEquiv := by
  let V : Y.affineOpens :=
    ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  let e := (f.appIso U.1).commRingCatIsoToRingEquiv
  rw [K.comap_submodule_eq_span f (U' := U)
    (V := V) (by
      dsimp only [V]
      exact (f.preimage_image_eq U.1).ge)]
  change Submodule.span Γ(X, U.1)
      (f.appPi V.1 (by simp [V]) n '' (K.submodule V : Set _)) =
    (K.submodule V).mapPiRingEquiv e
  conv_rhs =>
    rw [← Submodule.span_eq (K.submodule V), Submodule.mapPiRingEquiv_span]
  have happ (z : Fin n → Γ(Y, V.1)) :
      f.appPi V.1 (by simp [V]) n z = fun i ↦ e (z i) := by
    funext i
    change (f.appLE V.1 U.1 _).hom (z i) = _
    dsimp only [V, e]
    rw [← f.appIso_hom']
    rfl
  congr 1
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (happ z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, happ z⟩

/-- Finite projectivity and constant rank of the quotient transport from an affine
open in the source of an open immersion to its affine image. -/
lemma quotient_finite_projective_rank_image_of_isOpenImmersion
    (K : Y.SubmoduleSheafData n) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.affineOpens) {q : ℕ}
    (hproj : Module.Projective Γ(X, U.1)
      ((Fin n → Γ(X, U.1)) ⧸ (K.comap f).submodule U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U.1),
      Module.rankAtStalk
        ((Fin n → Γ(X, U.1)) ⧸ (K.comap f).submodule U) p = q) :
    Module.Projective Γ(Y, f ''ᵁ U.1)
        ((Fin n → Γ(Y, f ''ᵁ U.1)) ⧸
          K.submodule ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩) ∧
      ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ U.1),
        Module.rankAtStalk
          ((Fin n → Γ(Y, f ''ᵁ U.1)) ⧸
            K.submodule ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩) p = q := by
  let V : Y.affineOpens :=
    ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  let eR := (f.appIso U.1).commRingCatIsoToRingEquiv
  letI := RingHomInvPair.of_ringEquiv eR
  letI := RingHomInvPair.symm (eR : Γ(Y, V.1) →+* Γ(X, U.1))
    (eR.symm : Γ(X, U.1) →+* Γ(Y, V.1))
  letI := RingHomInvPair.of_ringEquiv eR.symm
  letI := RingHomInvPair.symm
    (eR.symm : Γ(X, U.1) →+* Γ(Y, V.1))
    (eR.symm.symm : Γ(Y, V.1) →+* Γ(X, U.1))
  let ePi := eR.piSemilinearEquiv n
  have hsub :
      (K.submodule V).map (ePi : (Fin n → Γ(Y, V.1)) →ₛₗ[eR] _) =
        (K.comap f).submodule U := by
    change (K.submodule V).mapPiRingEquiv eR = (K.comap f).submodule U
    exact (submodule_comap_of_isOpenImmersion K f U).symm
  let eQ :
      ((Fin n → Γ(Y, V.1)) ⧸ K.submodule V) ≃ₛₗ[eR]
        ((Fin n → Γ(X, U.1)) ⧸ (K.comap f).submodule U) :=
    Submodule.Quotient.equiv _ _ ePi hsub
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := eR.symm.toRingHom.toAlgebra
  have hfin : Module.Finite Γ(X, U.1)
      ((Fin n → Γ(X, U.1)) ⧸ (K.comap f).submodule U) :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have htransport := Module.finite_projective_rankAtStalk_of_semilinearEquiv
    eR.symm rfl eQ.symm hfin hproj hrank
  exact ⟨htransport.2.1, htransport.2.2⟩

/-- The finite-locally-free quotient condition of fixed rank is local for arbitrary
Zariski open covers. -/
lemma QuotientProjectiveOfRank.of_comap_openCover
    (K : X.SubmoduleSheafData n) {q : ℕ} (𝒰 : X.OpenCover)
    (hlocal : ∀ i, (K.comap (𝒰.f i)).QuotientProjectiveOfRank q) :
    K.QuotientProjectiveOfRank q := by
  intro x
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  obtain ⟨U, hyU, hproj, hrank⟩ := hlocal i y
  let V : X.affineOpens :=
    ⟨𝒰.f i ''ᵁ U.1, U.2.image_of_isOpenImmersion (𝒰.f i)⟩
  have hxV : x ∈ V.1 := by
    change x ∈ 𝒰.f i ''ᵁ U.1
    exact ⟨y, hyU, hy⟩
  have htransport :=
    quotient_finite_projective_rank_image_of_isOpenImmersion K (𝒰.f i) U hproj hrank
  exact ⟨V, hxV, htransport.1, htransport.2⟩
end SubmoduleSheafData

end AlgebraicGeometry.Scheme

end ThmGrassmannianProjectiveRelative
