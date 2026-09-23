module

public import StacksAndModuli.«Section4.7-Smoothness».«part4.7.1-liftings»
public import StacksAndModuli.API.FormallySmoothLiftNilpotent
public import StacksAndModuli.«Section4.3-Properties».«part4.3.6-etale-and-unramified»
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The Infinitesimal Lifting Criteria

This module formalizes Theorem 4.7.1 (`thm:infinitesimal-lifting-criterion-stacks`) and
Exercise 4.7.5 (`exer:infinitisemal-lifting-criterion`) of §4.7 (Smoothness and the
Infinitesimal Lifting Criterion) of *Stacks and Moduli*
(the section and its subsections carry no `sec:`
labels).

A *small extension* is a surjection `π : A → A₀` of (artinian local) rings whose kernel is
a simple `A`-module; for a local ring this says `ker π ≅ κ(A)` and forces the kernel to be
square-zero. The Infinitesimal Lifting Criteria characterize a locally of finite type
morphism `F : 𝒳 → 𝒴` of locally noetherian algebraic stacks as smooth (resp. étale,
unramified, with unramified diagonal) in terms of existence (resp. existence and
uniqueness, uniqueness, rigidity) of liftings (`rmk:lifting`, part 4.7.1) of
2-commutative squares along `Spec` of small extensions.

Main declarations:
- the characterization of étale morphisms as smooth and unramified (Appendix A.3);
- `AlgebraicGeometry.BasedFunctor.smooth_iff_nonempty_lifting_of_isSmallExtension`,
  `etale_iff_nonempty_and_unique_hom_lifting_of_isSmallExtension`,
  `unramified_iff_unique_hom_lifting_of_isSmallExtension`, and
  `relativelyDeligneMumford_iff_subsingleton_end_lifting_of_isSmallExtension`: the four
  criteria (proofs deferred, see the ledger comment at the end of the theorem's section
  block and this folder's STATUS.md).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmInfinitesimalLiftingCriterionStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  CategoryTheory.BasedFunctor

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

/-- Background definition used in Theorem 4.7.1: let $\pi \colon A \to A_0$ be a
morphism of commutative
rings. Then $\pi$ is a *small extension* if it is surjective and its kernel is a simple
$A$-module. For $A$ local with residue field $\kappa$ this says exactly that
$\ker(A \to A_0) \cong \kappa$, and it forces the kernel to be square-zero. The
Infinitesimal Lifting Criteria quantify over small extensions of artinian local rings. -/
structure IsSmallExtension {A A₀ : CommRingCat.{u}} (π : A ⟶ A₀) : Prop where
  /-- A small extension is surjective. -/
  surjective : Function.Surjective π.hom
  /-- The kernel of a small extension is a simple module. -/
  isSimpleModule_ker : IsSimpleModule A (RingHom.ker π.hom)

namespace IsSmallExtension

variable {A A₀ : CommRingCat.{u}} {π : A ⟶ A₀}

/-- Let $\pi \colon A \to A_0$ be a small extension with $A$ local. Then the kernel of
$\pi$ is isomorphic to the residue field of $A$ as an $A$-module: the only simple module
over a local ring is its residue field. This is the form in which the book introduces
small extensions. -/
theorem nonempty_linearEquiv_ker_residueField [IsLocalRing A] (h : IsSmallExtension π) :
    Nonempty (RingHom.ker π.hom ≃ₗ[A] IsLocalRing.ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h.isSimpleModule_ker
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- Let $\pi \colon A \to A_0$ be a small extension with $A$ local and $A_0$ nontrivial.
Then the kernel of $\pi$ is square-zero: it is annihilated by the maximal ideal and
contained in it. -/
theorem ker_pow_two_eq_bot [IsLocalRing A] [Nontrivial A₀] (h : IsSmallExtension π) :
    RingHom.ker π.hom ^ 2 = ⊥ := by
  haveI := h.isSimpleModule_ker
  -- the maximal ideal annihilates the simple module `ker π`, which is a proper ideal
  have hann : Module.annihilator A (RingHom.ker π.hom) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  have hle : RingHom.ker π.hom ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π.hom)
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.mpr fun x hx y hy ↦ ?_
  have hx' : x ∈ Module.annihilator A (RingHom.ker π.hom) := by
    rw [hann]
    exact hle hx
  have h0 := congrArg Subtype.val (Module.mem_annihilator.mp hx' ⟨y, hy⟩)
  simpa using h0

/-- Let $\pi \colon A \to A_0$ be a small extension. Then the induced morphism of affine
schemes $\Spec A_0 \to \Spec A$ is a closed immersion. -/
theorem isClosedImmersion_spec_map (h : IsSmallExtension π) :
    IsClosedImmersion (Spec.map π) :=
  IsClosedImmersion.spec_of_surjective π h.surjective

/-- Let $\pi \colon A \to A_0$ be a small extension with $A$ local and $A_0$ nontrivial.
Then the kernel ideal sheaf of the closed immersion $\Spec A_0 \to \Spec A$ is nilpotent
(it is even square-zero, cf. `AlgebraicGeometry.IsSmallExtension.ker_pow_two_eq_bot`);
thus $\Spec A_0 \to \Spec A$ is an infinitesimal thickening, as required by the
uniqueness part of the lifting criteria
(`AlgebraicGeometry.FormallyUnramified.hom_ext`). -/
theorem isNilpotent_ker_spec_map [IsLocalRing A] [Nontrivial A₀] (h : IsSmallExtension π) :
    IsNilpotent (Spec.map π).ker := by
  refine ⟨2, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Scheme.ker_of_isAffine,
    Pi.pow_apply, Scheme.IdealSheafData.ofIdealTop_ideal,
    Scheme.IdealSheafData.zero_eq_bot, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤)) (𝟙 _)]
  simp only [op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  have hnat : (Spec.map π).appTop ≫ (Scheme.ΓSpecIso A₀).hom
      = (Scheme.ΓSpecIso A).hom ≫ π := Scheme.ΓSpecIso_naturality π
  have hker : RingHom.ker (Scheme.Hom.appTop (Spec.map π)).hom
      = Ideal.comap (Scheme.ΓSpecIso A).hom.hom (RingHom.ker π.hom) := by
    rw [RingHom.comap_ker, ← CommRingCat.hom_comp, ← hnat, CommRingCat.hom_comp]
    exact (RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso A₀).commRingCatIsoToRingEquiv).symm
  rw [hker, pow_two, eq_bot_iff]
  have h2 := h.ker_pow_two_eq_bot
  have hinj : Function.Injective (Scheme.ΓSpecIso A).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
  refine Ideal.mul_le.mpr fun x hx y hy ↦ ?_
  have hmul : (Scheme.ΓSpecIso A).hom.hom (x * y) = 0 := by
    rw [map_mul]
    have : (Scheme.ΓSpecIso A).hom.hom x * (Scheme.ΓSpecIso A).hom.hom y
        ∈ RingHom.ker π.hom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (Ideal.mem_comap.mp hx) (Ideal.mem_comap.mp hy)
    rw [h2] at this
    simpa using this
  have hxy : x * y = 0 := hinj (by rw [hmul, map_zero])
  simp [hxy]

end IsSmallExtension

/-- Supporting factorization used in the proof of Theorem 4.7.1: let $A \to A_0$ be a
surjection of artinian local
rings. Then it factors into finitely many small extensions: there is a chain of ideals
$\bot = J_0 \le J_1 \le \dots \le J_n = \ker(A \to A_0)$ such that each successive
quotient map $A/J_i \to A/J_{i+1}$ is a small extension (a composition series of the
kernel, which has finite length over the artinian ring $A$). This factorization drives
the induction over $A_0/\mathfrak{m}^{k+1} \to A_0/\mathfrak{m}^k$ in the proof of the
smoothness criterion. -/
theorem exists_ideal_chain_factor_isSmallExtension {A A₀ : CommRingCat.{u}}
    [IsArtinianRing A] [IsLocalRing A] (π : A ⟶ A₀)
    (hπ : Function.Surjective π.hom) :
    ∃ (n : ℕ) (J : Fin (n + 1) → Ideal A) (hJ : Monotone J), J 0 = ⊥ ∧
      J (Fin.last n) = RingHom.ker π.hom ∧
      ∀ i : Fin n, IsSmallExtension
        (CommRingCat.ofHom (Ideal.Quotient.factor (hJ (Fin.castSucc_le_succ i)))) := by
  set K : Ideal A := RingHom.ker π.hom with hKdef
  have : _root_.IsNoetherian A A := inferInstanceAs (_root_.IsNoetherianRing A)
  have : _root_.IsArtinian A ↥K := inferInstance
  have : _root_.IsNoetherian A ↥K := inferInstance
  obtain ⟨s, shead, slast⟩ :=
    exists_compositionSeries_of_isNoetherian_isArtinian ↥A ↥K
  refine ⟨s.length, fun i => Submodule.map K.subtype (s i), ?_, ?_, ?_, ?_⟩
  · exact fun i j h => Submodule.map_mono (s.strictMono.monotone h)
  · change Submodule.map K.subtype s.head = ⊥
    rw [shead, Submodule.map_bot]
  · change Submodule.map K.subtype s.last = K
    rw [slast, Submodule.map_subtype_top]
  · intro i
    constructor
    · simpa using Ideal.Quotient.factor_surjective _
    · set J₁ : Ideal ↥A := Submodule.map K.subtype (s i.castSucc) with hJ₁
      set J₂ : Ideal ↥A := Submodule.map K.subtype (s i.succ) with hJ₂
      rw [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker]
      have hsurj : Function.Surjective (algebraMap ↥A (↥A ⧸ J₁)) := by
        rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
      rw [← isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj]
      have hrange : Set.range (Submodule.MapSubtype.orderEmbedding K) = Set.Iic K := by
        ext q
        constructor
        · rintro ⟨q', rfl⟩
          exact Submodule.map_subtype_le _ _
        · intro hq
          exact ⟨Submodule.comap K.subtype q, by
            simpa [Submodule.map_comap_subtype] using inf_of_le_right hq⟩
      have hcov : J₁ ⋖ J₂ :=
        CovBy.image (Submodule.MapSubtype.orderEmbedding K)
          (show s i.castSucc ⋖ s i.succ from s.step i)
          (by rw [hrange]; exact Set.ordConnected_Iic)
      have hle : J₁ ≤ J₂ := hcov.le
      have hsimp := (covBy_iff_quot_is_simple hle).mp hcov
      have hker : LinearMap.ker (J₁.mkQ ∘ₗ J₂.subtype) = Submodule.comap J₂.subtype J₁ := by
        rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      have key : LinearMap.range (J₁.mkQ ∘ₗ J₂.subtype) =
          Submodule.restrictScalars ↥A (Ideal.map (Ideal.Quotient.mk J₁) J₂) := by
        ext x
        simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.restrictScalars_mem,
          Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
        constructor
        · rintro ⟨⟨y, hy⟩, rfl⟩
          exact ⟨y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
      haveI := hsimp
      exact IsSimpleModule.congr
        (((Submodule.quotEquivOfEq _ _ hker.symm).trans
          ((LinearMap.quotKerEquivRange (J₁.mkQ ∘ₗ J₂.subtype)).trans
            (LinearEquiv.ofEq _ _ key))).symm)

/-- Supporting scheme-level lifting lemma for Theorem A.3.1: let $f \colon X \to Y$ be a
smooth
morphism of schemes, let $\pi \colon A \to A_0$ be a small extension of artinian local
rings, and consider a commutative square $\Spec A_0 \to X$, $\Spec A \to Y$ over $f$ and
$\Spec \pi$. Then a lifting $\Spec A \to X$ exists. This is the existence half of the
Infinitesimal Lifting Criterion for Smoothness for schemes, specialized to small
extensions.

The proof runs through stalks rather than through the book's affine-open argument:
`Scheme.SpecMap_stalkMap_fromSpecStalk` turns the square of schemes into a square of local
rings, injectivity of `(SpecToEquivOfLocalRing Y A₀).symm` identifies the two, and the
diagonal filler comes from `Algebra.FormallySmooth.exists_lift` packaged for `CommRingCat`
arrows as `CommRingCat.exists_lift_of_formallySmooth_of_isNilpotent_ker`
(`StacksAndModuli/API/FormallySmoothLiftNilpotent.lean`). See COMMENTARY.md. -/
theorem Smooth.exists_lift_spec_map_of_isSmallExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] {A A₀ : CommRingCat.{u}} [IsArtinianRing A] [IsLocalRing A] [Nontrivial A₀]
    {π : A ⟶ A₀} (hπ : IsSmallExtension π) (a : Spec A₀ ⟶ X) (b : Spec A ⟶ Y)
    (h : a ≫ f = Spec.map π ≫ b) :
    ∃ l : Spec A ⟶ X, Spec.map π ≫ l = a ∧ l ≫ f = b := by
  haveI : IsLocalRing A₀ := IsLocalRing.of_surjective' π.hom hπ.surjective
  haveI : IsLocalHom π.hom := IsLocalHom.of_surjective π.hom hπ.surjective
  set x : X := a (IsLocalRing.closedPoint A₀) with hxdef
  have hsm : (f.stalkMap x).hom.FormallySmooth :=
    (Scheme.Hom.mem_smoothLocus (f := f) (x := x)).mp (f.smoothLocus_eq_top ▸ trivial)
  set ψ : X.presheaf.stalk x ⟶ A₀ := Scheme.stalkClosedPointTo a with hψ
  have ha : Spec.map ψ ≫ X.fromSpecStalk x = a := Scheme.Spec_stalkClosedPointTo_fromSpecStalk a
  have hpt : f x = b (IsLocalRing.closedPoint A) := by
    have := congrArg (fun g : Spec A₀ ⟶ Y => g.base (IsLocalRing.closedPoint A₀)) h
    simpa using this
  set χ : Y.presheaf.stalk (f x) ⟶ A :=
    (Y.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo b with hχ
  have hb : Spec.map χ ≫ Y.fromSpecStalk (f x) = b := by
    rw [hχ, Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e1 : Spec.map (f.stalkMap x ≫ ψ) ≫ Y.fromSpecStalk (f x) = a ≫ f := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ha]
  have e2 : Spec.map (χ ≫ π) ≫ Y.fromSpecStalk (f x) = Spec.map π ≫ b := by
    rw [Spec.map_comp, Category.assoc, hb]
  have hsq : f.stalkMap x ≫ ψ = χ ≫ π := by
    have key : (SpecToEquivOfLocalRing Y A₀).symm ⟨f x, ⟨f.stalkMap x ≫ ψ, inferInstance⟩⟩ =
        (SpecToEquivOfLocalRing Y A₀).symm ⟨f x, ⟨χ ≫ π, inferInstance⟩⟩ := by
      simpa using e1.trans (h.trans e2.symm)
    simpa using (SpecToEquivOfLocalRing Y A₀).symm.injective key
  obtain ⟨w, hw1, hw2⟩ := CommRingCat.exists_lift_of_formallySmooth_of_isNilpotent_ker (f.stalkMap x) hsm π hπ.surjective
    ⟨2, hπ.ker_pow_two_eq_bot⟩ χ ψ hsq
  refine ⟨Spec.map w ≫ X.fromSpecStalk x, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hw1, ha]
  · rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
      ← Spec.map_comp, hw2, hb]

/-- Supporting scheme-level uniqueness lemma for Theorem A.3.3: let $f \colon X \to Y$
be a formally
unramified morphism of schemes and let $\pi \colon A \to A_0$ be a small extension with
$A$ local and $A_0$ nontrivial. Two morphisms $\Spec A \to X$ over $Y$ agreeing on
$\Spec A_0$ are equal. This is the uniqueness half of the Infinitesimal Lifting Criterion
for Unramifiedness for schemes, specialized to small extensions. -/
theorem FormallyUnramified.hom_ext_spec_map_of_isSmallExtension {X Y : Scheme.{u}}
    (f : X ⟶ Y) [FormallyUnramified f] {A A₀ : CommRingCat.{u}} [IsLocalRing A]
    [Nontrivial A₀] {π : A ⟶ A₀} (hπ : IsSmallExtension π) {g₁ g₂ : Spec A ⟶ X}
    (h : Spec.map π ≫ g₁ = Spec.map π ≫ g₂) (hf : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  have := hπ.isClosedImmersion_spec_map
  exact FormallyUnramified.hom_ext (Spec.map π) hπ.isNilpotent_ker_spec_map f h hf

section ThmEtaleEquivalences

/-- **Theorem A.3.2** (`thm:etale-equivalences`) (étale = smooth and unramified): a
morphism of schemes is étale if and only if it is smooth, locally of finite type,
and formally unramified (i.e. smooth and unramified). This identifies the étale case of
the Infinitesimal Lifting Criteria as the conjunction of the smooth and unramified
cases; Mathlib defines all four classes through ring-homomorphism properties, and the
comparison is deferred to the formalization of Appendix A.3. -/
theorem etale_iff_smooth_and_locallyOfFiniteType_and_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    Etale f ↔ (Smooth f ∧ LocallyOfFiniteType f ∧ FormallyUnramified f) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, fun ⟨_, _, _⟩ ↦ ?_⟩
  exact Etale.of_formallyUnramified_of_flat f

end ThmEtaleEquivalences

end AlgebraicGeometry

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

/-- **Theorem 4.7.1** (`thm:infinitesimal-lifting-criterion-stacks`) (part (1)):
the Infinitesimal Lifting
Criterion for Smoothness. Let $f \colon \cX \to \cY$ be a locally of finite type
morphism of locally noetherian algebraic stacks. Then $f$ is smooth if and only if for
every small extension $\pi \colon A \to A_0$ of artinian local rings, every
2-commutative square $\Spec A_0 \to \cX$, $\Spec A \to \cY$ over $f$ and $\Spec \pi$
admits a lifting $\Spec A \to \cX$. (The book also assumes that $\cX$ and $\cY$ have
quasi-compact and separated diagonals; these hypotheses await the §4.2 diagonal — see
the ledger below and the `[decision]` entry in this folder's COMMENTARY.md.) -/
theorem smooth_iff_nonempty_lifting_of_isSmallExtension (F : 𝒳 ⥤ᵇ 𝒴)
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳)
    (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴) (hF : LocallyOfFiniteType F) :
    Smooth F ↔
      ∀ (A A₀ : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [IsArtinianRing A₀]
        [IsLocalRing A₀] (π : A ⟶ A₀), IsSmallExtension π →
        ∀ σ : F.LiftingSq (Spec.map π), Nonempty σ.Lifting := by
  sorry

/-- **Theorem 4.7.1** (`thm:infinitesimal-lifting-criterion-stacks`) (part (2)):
the Infinitesimal Lifting Criterion
for Étaleness. Let $f \colon \cX \to \cY$ be a locally of finite type morphism of
locally noetherian algebraic stacks. Then $f$ is étale if and only if for every small
extension $\pi \colon A \to A_0$ of artinian local rings, every 2-commutative square
over $f$ and $\Spec \pi$ admits a lifting which is unique up to unique isomorphism. (On
the omitted diagonal hypotheses see the ledger below.) -/
theorem etale_iff_nonempty_and_unique_hom_lifting_of_isSmallExtension (F : 𝒳 ⥤ᵇ 𝒴)
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳)
    (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴) (hF : LocallyOfFiniteType F) :
    Etale F ↔
      ∀ (A A₀ : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [IsArtinianRing A₀]
        [IsLocalRing A₀] (π : A ⟶ A₀), IsSmallExtension π →
        ∀ σ : F.LiftingSq (Spec.map π),
          Nonempty σ.Lifting ∧ ∀ l l' : σ.Lifting, Nonempty (Unique (l ⟶ l')) := by
  sorry

/-- **Theorem 4.7.1** (`thm:infinitesimal-lifting-criterion-stacks`) (part (3)):
the Infinitesimal Lifting
Criterion for Unramifiedness. Let $f \colon \cX \to \cY$ be a locally of finite type
morphism of locally noetherian algebraic stacks. Then $f$ is unramified if and only if
for every small extension $\pi \colon A \to A_0$ of artinian local rings and every
2-commutative square over $f$ and $\Spec \pi$, any two liftings are uniquely isomorphic.
(On the omitted diagonal hypotheses see the ledger below.) -/
theorem unramified_iff_unique_hom_lifting_of_isSmallExtension (F : 𝒳 ⥤ᵇ 𝒴)
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳)
    (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴) (hF : LocallyOfFiniteType F) :
    Unramified F ↔
      ∀ (A A₀ : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [IsArtinianRing A₀]
        [IsLocalRing A₀] (π : A ⟶ A₀), IsSmallExtension π →
        ∀ (σ : F.LiftingSq (Spec.map π)) (l l' : σ.Lifting),
          Nonempty (Unique (l ⟶ l')) := by
  sorry

/-- **Theorem 4.7.1** (`thm:infinitesimal-lifting-criterion-stacks`) (part (4)):
the Infinitesimal
Lifting Criterion for Unramifiedness of the Diagonal. Let $f \colon \cX \to \cY$ be a
locally of finite type morphism of locally noetherian algebraic stacks. Then $f$ has
unramified diagonal — equivalently, $f$ is relatively Deligne–Mumford (Corollary 4.6.5,
through which the statement is phrased here)
— if and only if for every small extension $\pi \colon A \to A_0$ of artinian local
rings and every 2-commutative square over $f$ and $\Spec \pi$, every automorphism of a
lifting is trivial. (On the omitted diagonal hypotheses see the ledger below.) -/
theorem relativelyDeligneMumford_iff_subsingleton_end_lifting_of_isSmallExtension
    (F : 𝒳 ⥤ᵇ 𝒴) (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳)
    (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴) (hF : LocallyOfFiniteType F) :
    RelativelyDeligneMumford F ↔
      ∀ (A A₀ : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [IsArtinianRing A₀]
        [IsLocalRing A₀] (π : A ⟶ A₀), IsSmallExtension π →
        ∀ (σ : F.LiftingSq (Spec.map π)) (l : σ.Lifting),
          Subsingleton (l ⟶ l) := by
  sorry

/- LEDGER (`thm:infinitesimal-lifting-criterion-stacks`, hypotheses and proofs):

- The book assumes in addition that the diagonals of `𝒳` and `𝒴` (equivalently, of `F`)
  are quasi-compact and separated. These hypotheses require the §4.2 diagonal
  `Δ_F : 𝒳 ⥤ᵇ fiberProduct F F` (Section4.2-Representability, verified in parallel) and
  the separation predicates of §4.3.3 built on it; they are omitted from the four
  statements above and must be added once §4.2 lands. They enter the proofs through
  `prop:presentations-lifting-points` (§5.3), which needs them to produce presentations
  through a prescribed field-valued point.
- Part (4) is stated with `RelativelyDeligneMumford F` in place of the book's "`f` has
  unramified diagonal": the two are identified by `cor:characterization-of-relatively-DM`
  (§4.6, forward dependency), and the diagonal itself is §4.2 infrastructure.
- Proofs (all four sorried; cf. Stacks 0DP0 and Laumon–Moret-Bailly, Prop. 4.15): the
  smooth forward direction base-changes to `𝒴 = Spec A`, then bootstraps scheme →
  algebraic space → stack via smooth presentations, `prop:presentations-lifting-points`
  (§5.3, proven there independently of this section), the factorization
  `AlgebraicGeometry.exists_ideal_chain_factor_isSmallExtension`, and the scheme-level
  stepping stone `AlgebraicGeometry.Smooth.exists_lift_spec_map_of_isSmallExtension`; the
  converse tests `U → 𝒳_V → V` for presentations and uses that smoothness is smooth
  local on source and target (§4.3.1). The étale case reduces to smooth + unramified via
  `AlgebraicGeometry.etale_iff_smooth_and_locallyOfFiniteType_and_formallyUnramified` and
  `AlgebraicGeometry.BasedFunctor.etale_iff_smooth_and_unramified` (§4.3.6). The
  unramified case reduces via `cor:characterization-of-relatively-DM` (§4.6) and
  `AlgebraicGeometry.FormallyUnramified.hom_ext_spec_map_of_isSmallExtension`. The
  diagonal case identifies automorphisms of liftings for `F` with liftings for the double
  diagonal `𝒳 → I_{𝒳/𝒴}` (§4.2 relative inertia) and uses
  `exer:diagonal-characterizations` (§4.3.6, itself §4.2-blocked); the book's
  commented-out solutions give complete arguments. -/

end AlgebraicGeometry.BasedFunctor

end ThmInfinitesimalLiftingCriterionStacks

section ExerInfinitisemalLiftingCriterion

/- Coverage note for Exercise 4.7.5 (whose label is misspelled in the book): prove the
étale, unramified, and unramified-diagonal parts of the
Infinitesimal Lifting Criteria. The content of this exercise is exactly parts (2)–(4) of
`thm:infinitesimal-lifting-criterion-stacks`, formalized above (in the namespace
`AlgebraicGeometry.BasedFunctor`) as
`etale_iff_nonempty_and_unique_hom_lifting_of_isSmallExtension`,
`unramified_iff_unique_hom_lifting_of_isSmallExtension`, and
`relativelyDeligneMumford_iff_subsingleton_end_lifting_of_isSmallExtension`; no separate
statement is introduced. The book's commented-out solutions (relating an
automorphism of a lifting for `f` to a lifting for the double diagonal
`𝒳 → I_{𝒳/𝒴}`, reducing étaleness to smoothness plus unramifiedness, and reducing
unramifiedness to the relatively Deligne–Mumford case via
`cor:characterization-of-relatively-DM`) are recorded in the ledger of the theorem's
section. -/

end ExerInfinitisemalLiftingCriterion
