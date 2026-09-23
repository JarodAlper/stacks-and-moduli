module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# The finite-length boundary in Krull--Akizuki

This file isolates the part of the Krull--Akizuki theorem which is not already
available in Mathlib.  For an algebraic extension of domains, Mathlib's polynomial
and ideal API proves that every nonzero ideal has nonzero contraction.  It then
suffices to know that the quotients by nonzero elements of the base have finite
length as modules over the base.

The latter statement is Stacks Project tag 00PF: if `R` is a noetherian
one-dimensional domain with fraction field `K`, and `M` is an arbitrary
`R`-submodule of a finite-dimensional `K`-vector space, then `M / xM` has finite
length for every nonzero `x : R`.  Mathlib proves the special case `M = R` as
`isFiniteLength_quotient_span_singleton`, but not the arbitrary-submodule result.

Main declarations:

* `Ideal.comap_ne_bot_of_isAlgebraic` is the algebraic ideal-contraction lemma
  (Stacks tag 0H7L);
* `IsNoetherianRing.of_finiteLength_quotients_of_isAlgebraic` is the formal final
  step of Krull--Akizuki, reducing it exactly to the finite-length assertion above.
-/

@[expose] public section

universe u v

open scoped Pointwise

/-- A nonzero ideal in an algebraic extension domain has nonzero contraction.

This is the algebraic part of Stacks Project tag 0H7L.  For a nonzero element of
the ideal, choose a nonzero polynomial relation over the base.  Mathlib's
`Ideal.comap_ne_bot_of_root_mem` then finds a nonzero coefficient in the
contraction. -/
theorem Ideal.comap_ne_bot_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsAlgebraic R A] (I : Ideal A) (hI : I ≠ ⊥) :
    I.comap (algebraMap R A) ≠ ⊥ := by
  obtain ⟨⟨a, haI⟩, ha0⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  obtain ⟨p, hp0, hpa⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) a
  have ha0' : a ≠ 0 := fun ha ↦ ha0 (Subtype.ext ha)
  exact Ideal.comap_ne_bot_of_root_mem ha0' haI hp0 (by
    simpa only [Polynomial.aeval_def] using hpa)

/-- Every nonzero ideal in an algebraic extension domain contains the image of a
nonzero element of the base ring. -/
theorem Ideal.exists_ne_zero_mem_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsAlgebraic R A] (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x : R, x ≠ 0 ∧ algebraMap R A x ∈ I := by
  have hcomap := I.comap_ne_bot_of_isAlgebraic (R := R) hI
  obtain ⟨⟨x, hxI⟩, hx0⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hcomap)
  have hx0' : x ≠ 0 := fun hx ↦ hx0 (Subtype.ext hx)
  exact ⟨x, hx0', hxI⟩

/-- Clear denominators in the span of a submodule inside a vector space over
the fraction field.  Every vector in the fraction-field span of `N` has a
non-zero-divisor multiple lying in `N`. -/
theorem Submodule.exists_nonZeroDivisor_smul_mem_of_mem_span_fractionField
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V]
    (N : Submodule R V) {z : V}
    (hz : z ∈ Submodule.span K (N : Set V)) :
    ∃ d : nonZeroDivisors R, d.val • z ∈ N := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      exact ⟨1, by simpa using hz⟩
  | zero =>
      exact ⟨1, by simpa using N.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      change (a * b : R) • (x + y) ∈ N
      rw [smul_add]
      exact N.add_mem
        (by simpa only [smul_smul, mul_comm] using N.smul_mem b.val ha)
        (by simpa only [smul_smul] using N.smul_mem a.val hb)
  | smul c z _ hz =>
      obtain ⟨d, hd⟩ := hz
      obtain ⟨e, he⟩ :=
        IsLocalization.exists_integer_multiple (nonZeroDivisors R) c
      obtain ⟨a, ha⟩ := he
      refine ⟨e * d, ?_⟩
      have had := N.smul_mem a hd
      have had' : algebraMap R K (a * d.val) • z ∈ N := by
        rw [IsScalarTower.algebraMap_smul K]
        simpa only [smul_smul] using had
      have heq : ((e * d : nonZeroDivisors R).val : R) • (c • z) =
          algebraMap R K (a * d.val) • z := by
        calc
          ((e * d : nonZeroDivisors R).val : R) • (c • z) =
              (((e * d : nonZeroDivisors R).val : R) • c) • z :=
            (IsScalarTower.smul_assoc _ _ _).symm
          _ = algebraMap R K (a * d.val) • z := by
            congr 1
            rw [Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul,
              ha, Algebra.smul_def]
            ac_rfl
      rw [heq]
      exact had'

/-- The copy of an `R`-submodule inside its fraction-field span still spans
the whole space over the fraction field. -/
theorem Submodule.span_comap_span_fractionField_eq_top
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (N : Submodule R V) :
    let W := Submodule.span K (N : Set V)
    Submodule.span K
      ((N.comap (W.subtype.restrictScalars R) : Submodule R W) : Set W) = ⊤ := by
  let W := Submodule.span K (N : Set V)
  let N' : Submodule R W := N.comap (W.subtype.restrictScalars R)
  have himage : W.subtype '' (N' : Set W) = (N : Set V) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      refine ⟨⟨z, Submodule.subset_span hz⟩, hz, rfl⟩
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span, himage, Submodule.map_top,
    Submodule.range_subtype]

/-- The module quotient `A / xA` is linearly equivalent to the quotient by the
principal ideal generated by the image of `x`. -/
def QuotSMulTop.equivIdealQuotientSpanAlgebraMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (x : R) :
    QuotSMulTop x A ≃ₗ[R] A ⧸ Ideal.span {algebraMap R A x} := by
  let J : Ideal A := Ideal.span {algebraMap R A x}
  have hsubmodule :
      x • (⊤ : Submodule R A) = J.restrictScalars R := by
    ext y
    rw [Submodule.mem_smul_pointwise_iff_exists,
      Submodule.restrictScalars_mem]
    change (∃ z ∈ (⊤ : Submodule R A), x • z = y) ↔
      y ∈ Ideal.span {algebraMap R A x}
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, by simpa only [Algebra.smul_def, mul_comm] using hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Submodule.mem_top, by
        simpa only [Algebra.smul_def, mul_comm] using hz⟩
  exact Submodule.quotEquivOfEq _ _ hsubmodule ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R J

/-- Transfer finite generation of `A / xA` from the module-theoretic
`QuotSMulTop` spelling to the ideal-quotient spelling. -/
theorem Module.Finite.idealQuotient_span_algebraMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (x : R) (h : Module.Finite R (QuotSMulTop x A)) :
    Module.Finite R (A ⧸ Ideal.span {algebraMap R A x}) := by
  letI := h
  exact Module.Finite.equiv
    (QuotSMulTop.equivIdealQuotientSpanAlgebraMap x)

/-- Transfer the ACC on submodules of `A / xA` from the module-theoretic
`QuotSMulTop` spelling to the ideal-quotient spelling. -/
theorem IsNoetherian.idealQuotient_span_algebraMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (x : R) (h : IsNoetherian R (QuotSMulTop x A)) :
    IsNoetherian R (A ⧸ Ideal.span {algebraMap R A x}) :=
  (QuotSMulTop.equivIdealQuotientSpanAlgebraMap x).isNoetherian_iff.mp h

/-- Transfer finite length of `A / xA` from the module-theoretic
`QuotSMulTop` spelling to the ideal-quotient spelling. -/
theorem IsFiniteLength.idealQuotient_span_algebraMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (x : R) (h : IsFiniteLength R (QuotSMulTop x A)) :
    IsFiniteLength R (A ⧸ Ideal.span {algebraMap R A x}) :=
  (QuotSMulTop.equivIdealQuotientSpanAlgebraMap x).isFiniteLength h

/-- For an endomorphism of a finite-length module, the kernel and cokernel
have the same length. -/
theorem LinearMap.length_ker_eq_length_quotient_range_of_finiteLength
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) (hM : IsFiniteLength R M) :
    Module.length R (LinearMap.ker f) =
      Module.length R (M ⧸ LinearMap.range f) := by
  letI : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  letI : IsArtinian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  have hexactRange : Function.Exact
      (LinearMap.ker f).subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      Submodule.range_subtype]
  have hkernel := Module.length_eq_add_of_exact
    (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict hexactRange
  have hcokernel := Module.length_eq_add_of_exact
    (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ (LinearMap.range f))
  apply ENat.add_right_injective_of_ne_top
    (Module.length_ne_top (R := R) (M := LinearMap.range f))
  calc
    Module.length R (LinearMap.range f) +
          Module.length R (LinearMap.ker f) =
        Module.length R (LinearMap.ker f) +
          Module.length R (LinearMap.range f) := add_comm _ _
    _ = Module.length R M := hkernel.symm
    _ = Module.length R (LinearMap.range f) +
          Module.length R (M ⧸ LinearMap.range f) := hcokernel

/-- A full lattice and its ambient torsion-free module have reductions modulo
a regular scalar of the same length, provided the quotient lattice has finite
length.

This is the snake-lemma core of the finite-module part of Stacks Project tag
00PE.  The kernel of `N / xN → F / xF` is the `x`-torsion in `F / N`; its
length equals the length of `(F / N) / x(F / N)`, which is the cokernel on the
right. -/
theorem Module.length_quotSMulTop_eq_of_quotient_finiteLength
    {R : Type u} [CommRing R]
    {F : Type v} [AddCommGroup F] [Module R F]
    (N : Submodule R F) (x : R) (hx : IsSMulRegular F x)
    (hC : IsFiniteLength R (F ⧸ N)) :
    Module.length R (QuotSMulTop x N) =
      Module.length R (QuotSMulTop x F) := by
  classical
  let C := F ⧸ N
  let iN : N →ₗ[R] N := LinearMap.lsmul R N x
  let iF : F →ₗ[R] F := LinearMap.lsmul R F x
  let iC : C →ₗ[R] C := LinearMap.lsmul R C x
  let f₁ : N →ₗ[R] F := N.subtype
  let f₂ : F →ₗ[R] C := N.mkQ
  have hrow : Function.Exact f₁ f₂ :=
    LinearMap.exact_subtype_mkQ N
  have hcomm₁ : f₁.comp iN = iF.comp f₁ := by
    ext z
    rfl
  have hcomm₂ : f₂.comp iF = iC.comp f₂ := by
    ext z
    rfl
  let ιC : LinearMap.ker iC →ₗ[R] C := (LinearMap.ker iC).subtype
  have hιC : Function.Exact ιC iC :=
    LinearMap.exact_subtype_ker_map iC
  let πN : N →ₗ[R] QuotSMulTop x N :=
    (x • (⊤ : Submodule R N)).mkQ
  let πF : F →ₗ[R] QuotSMulTop x F :=
    (x • (⊤ : Submodule R F)).mkQ
  have hπN : Function.Exact iN πN := by
    intro z
    simp [iN, πN, Submodule.mem_smul_pointwise_iff_exists]
  have hπF : Function.Exact iF πF := by
    intro z
    simp [iF, πF, Submodule.mem_smul_pointwise_iff_exists]
  let δ : LinearMap.ker iC →ₗ[R] QuotSMulTop x N :=
    SnakeLemma.δ' iN iF iC f₁ f₂ hrow f₁ f₂ hrow hcomm₁ hcomm₂
      ιC hιC πN hπN (Submodule.mkQ_surjective N)
        (Submodule.subtype_injective N)
  let qNF : QuotSMulTop x N →ₗ[R] QuotSMulTop x F :=
    QuotSMulTop.map x f₁
  let qFC : QuotSMulTop x F →ₗ[R] QuotSMulTop x C :=
    QuotSMulTop.map x f₂
  have hπcomm : qNF.comp πN = πF.comp f₁ := by
    simpa only [qNF, πN, πF] using
      (QuotSMulTop.map_comp_mkQ (r := x) f₁)
  have hδqNF : Function.Exact δ qNF := by
    exact SnakeLemma.exact_δ'_left iN iF iC f₁ f₂ hrow f₁ f₂ hrow
      hcomm₁ hcomm₂ ιC hιC πN hπN πF hπF
        (Submodule.mkQ_surjective N) (Submodule.subtype_injective N)
          qNF hπcomm (Submodule.mkQ_surjective _)
  let ιF : LinearMap.ker iF →ₗ[R] F := (LinearMap.ker iF).subtype
  have hιF : Function.Exact ιF iF :=
    LinearMap.exact_subtype_ker_map iF
  let kmap : LinearMap.ker iF →ₗ[R] LinearMap.ker iC :=
    (f₂.domRestrict (LinearMap.ker iF)).codRestrict (LinearMap.ker iC)
      fun z ↦ by
        change iC (f₂ z) = 0
        rw [← LinearMap.comp_apply, ← hcomm₂, LinearMap.comp_apply]
        simpa only [map_zero] using congrArg f₂ z.property
  have hkcomm : f₂.comp ιF = ιC.comp kmap := by
    ext z
    rfl
  have hkδ : Function.Exact kmap δ := by
    exact SnakeLemma.exact_δ'_right iN iF iC f₁ f₂ hrow f₁ f₂ hrow
      hcomm₁ hcomm₂ ιF hιF ιC hιC πN hπN
        (Submodule.mkQ_surjective N) (Submodule.subtype_injective N)
          kmap hkcomm (Submodule.subtype_injective _)
  have hkerF : LinearMap.ker iF = ⊥ := by
    simpa only [iF] using
      (isSMulRegular_iff_ker_lsmul_eq_bot F x).mp hx
  letI : Subsingleton (LinearMap.ker iF) :=
    Submodule.subsingleton_iff_eq_bot.mpr hkerF
  have hkmap : kmap = 0 := by
    apply LinearMap.ext
    intro z
    rw [Subsingleton.elim z 0, map_zero, LinearMap.zero_apply]
  have hδinj : Function.Injective δ := by
    rw [hkmap, LinearMap.exact_zero_iff_injective] at hkδ
    exact hkδ
  have hqExact : Function.Exact qNF qFC :=
    QuotSMulTop.map_exact x hrow (Submodule.mkQ_surjective N)
  have hqFC : Function.Surjective qFC :=
    QuotSMulTop.map_surjective x (Submodule.mkQ_surjective N)
  have hδrange : Function.Exact δ qNF.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp hδqNF
  have hrangeq : Function.Exact qNF.range.subtype qFC := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact LinearMap.exact_iff.mp hqExact
  have hleft := Module.length_eq_add_of_exact δ qNF.rangeRestrict
    hδinj qNF.surjective_rangeRestrict hδrange
  have hright := Module.length_eq_add_of_exact qNF.range.subtype qFC
    (Submodule.subtype_injective _) hqFC hrangeq
  have hrangeC : LinearMap.range iC = x • (⊤ : Submodule R C) := by
    have hexactC : Function.Exact iC
        ((x • (⊤ : Submodule R C)).mkQ) := by
      intro z
      simp [iC, Submodule.mem_smul_pointwise_iff_exists]
    calc
      LinearMap.range iC =
          LinearMap.ker ((x • (⊤ : Submodule R C)).mkQ) :=
        (LinearMap.exact_iff.mp hexactC).symm
      _ = x • (⊤ : Submodule R C) := Submodule.ker_mkQ _
  let eC : (C ⧸ LinearMap.range iC) ≃ₗ[R] QuotSMulTop x C :=
    Submodule.quotEquivOfEq _ _ hrangeC
  have hkernelC : Module.length R (LinearMap.ker iC) =
      Module.length R (QuotSMulTop x C) :=
    (LinearMap.length_ker_eq_length_quotient_range_of_finiteLength iC hC).trans
      eC.length_eq
  calc
    Module.length R (QuotSMulTop x N) =
        Module.length R (LinearMap.ker iC) +
          Module.length R qNF.range := hleft
    _ = Module.length R qNF.range +
          Module.length R (QuotSMulTop x C) := by rw [hkernelC, add_comm]
    _ = Module.length R (QuotSMulTop x F) := hright.symm

/-- Nested-submodule form of
`Module.length_quotSMulTop_eq_of_quotient_finiteLength`. -/
theorem Module.length_quotSMulTop_eq_of_le_of_quotient_finiteLength
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (N F : Submodule R M) (hNF : N ≤ F) (x : R)
    (hx : IsSMulRegular F x)
    (hC : IsFiniteLength R (F ⧸ N.comap F.subtype)) :
    Module.length R (QuotSMulTop x N) =
      Module.length R (QuotSMulTop x F) := by
  let e : N.comap F.subtype ≃ₗ[R] N :=
    Submodule.comapSubtypeEquivOfLe hNF
  calc
    Module.length R (QuotSMulTop x N) =
        Module.length R (QuotSMulTop x (N.comap F.subtype)) :=
      (QuotSMulTop.congr x e).length_eq.symm
    _ = Module.length R (QuotSMulTop x F) :=
      Module.length_quotSMulTop_eq_of_quotient_finiteLength
        (N.comap F.subtype) x hx hC

/-- A uniform finite bound on the lengths of finitely generated submodules
forces the ambient module to have finite length.

This is the formal infinite-module step in Stacks Project tag 00PE.  Given a
strict chain in the ambient module, choose one witness from each strict
inclusion.  Their span is finitely generated and contains a strict chain of
the same length, so the uniform bound controls every finite chain. -/
theorem isFiniteLength_of_bounded_fg_submodule_lengths
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ∞) (hn : n ≠ ⊤)
    (hbound : ∀ N : Submodule R M, N.FG → Module.length R N ≤ n) :
    IsFiniteLength R M := by
  have hlength : Module.length R M ≤ n := by
    rw [Module.length_eq_height]
    apply Order.height_le
    intro p _
    classical
    choose m hm_mem hm_not using fun i : Fin p.length ↦
      SetLike.exists_of_lt
        (show p i.castSucc < p i.succ from p.step i)
    let N : Submodule R M := Submodule.span R (Set.range m)
    have hN : N.FG := Submodule.fg_span (Set.finite_range m)
    let q : LTSeries (Submodule R N) :=
      { length := p.length
        toFun := fun i ↦ (p i).comap N.subtype
        step := fun i ↦ by
          apply lt_of_le_of_ne (Submodule.comap_mono (p.step i).le)
          intro heq
          let mi : N :=
            ⟨m i, Submodule.subset_span (Set.mem_range_self i)⟩
          have hi : mi ∈ (p i.castSucc).comap N.subtype := by
            rw [heq]
            exact hm_mem i
          exact hm_not i hi }
    have hchain : (p.length : ℕ∞) ≤ Module.length R N := by
      rw [Module.length_eq_height]
      simpa only [q] using
        (Order.length_le_height (p := q) (show q.last ≤ ⊤ from le_top))
    exact hchain.trans (hbound N hN)
  apply Module.length_ne_top_iff.mp
  intro htop
  apply hn
  exact top_unique (htop ▸ hlength)

/-- To prove `M / xM` has finite length, it is enough to bound uniformly the
lengths of `N / xN` for finitely generated submodules `N` of `M`.

Every finitely generated submodule of `M / xM` has finitely many chosen lifts
to `M`; their span is a finitely generated `N`, and the original submodule is
contained in the image of `N / xN`.  Together with
`isFiniteLength_of_bounded_fg_submodule_lengths`, this packages the second
paragraph of the proof of Stacks Project tag 00PE. -/
theorem isFiniteLength_quotSMulTop_of_bounded_fg_submodule_quotient_lengths
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (x : R) (n : ℕ∞) (hn : n ≠ ⊤)
    (hbound : ∀ N : Submodule R M, N.FG →
      Module.length R (QuotSMulTop x N) ≤ n) :
    IsFiniteLength R (QuotSMulTop x M) := by
  apply isFiniteLength_of_bounded_fg_submodule_lengths n hn
  intro P hP
  classical
  obtain ⟨k, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hP
  choose m hm using fun i : Fin k ↦
    Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) (s i : QuotSMulTop x M)
  let N : Submodule R M := Submodule.span R (Set.range m)
  have hN : N.FG := Submodule.fg_span (Set.finite_range m)
  let f : QuotSMulTop x N →ₗ[R] QuotSMulTop x M :=
    QuotSMulTop.map x N.subtype
  have hP_range : P ≤ LinearMap.range f := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Submodule.Quotient.mk
      ⟨m i, Submodule.subset_span (Set.mem_range_self i)⟩, ?_⟩
    change (x • (⊤ : Submodule R M)).mkQ (m i) = s i
    exact hm i
  let inclusion : P →ₗ[R] LinearMap.range f :=
    Submodule.inclusion hP_range
  have h₁ : Module.length R P ≤ Module.length R (LinearMap.range f) :=
    Module.length_le_of_injective inclusion
      (Submodule.inclusion_injective hP_range)
  have h₂ : Module.length R (LinearMap.range f) ≤
      Module.length R (QuotSMulTop x N) :=
    Module.length_le_of_surjective f.rangeRestrict
      f.surjective_rangeRestrict
  exact h₁.trans (h₂.trans (hbound N hN))

/-- A uniform system of finite-length over-lattices proves that `M / xM` has
finite length.  This combines the lattice comparison with the reduction from
an arbitrary module to its finitely generated submodules. -/
theorem isFiniteLength_quotSMulTop_of_bounded_overlattices
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (x : R) (n : ℕ∞) (hn : n ≠ ⊤)
    (hlattice : ∀ N : Submodule R M, N.FG →
      ∃ F : Submodule R M, ∃ hNF : N ≤ F,
        IsSMulRegular F x ∧
        IsFiniteLength R (F ⧸ N.comap F.subtype) ∧
        Module.length R (QuotSMulTop x F) ≤ n) :
    IsFiniteLength R (QuotSMulTop x M) := by
  apply isFiniteLength_quotSMulTop_of_bounded_fg_submodule_quotient_lengths
    x n hn
  intro N hN
  obtain ⟨F, hNF, hxF, hquotient, hF⟩ := hlattice N hN
  rw [Module.length_quotSMulTop_eq_of_le_of_quotient_finiteLength
    N F hNF x hxF hquotient]
  exact hF

/-- A generating family gives an explicit length bound after reduction by a
non-zero-divisor.  The coefficients of the resulting presentation live in
`R / (x)`, so a family indexed by `ι` contributes at most `|ι|` copies of the
length of that quotient. -/
theorem Module.length_quotSMulTop_le_of_span_eq_top
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (s : ι → M)
    (hs : Submodule.span R (Set.range s) = ⊤)
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    Module.length R (QuotSMulTop x M) ≤
      Fintype.card ι * Module.length R (R ⧸ Ideal.span {x}) := by
  classical
  let Q := R ⧸ Ideal.span {x}
  have hbase : IsFiniteLength R Q :=
    isFiniteLength_quotient_span_singleton R hx
  let t : ι → QuotSMulTop x M := fun i ↦
    Submodule.Quotient.mk (s i)
  have ht : Submodule.span Q (Set.range t) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨m, rfl⟩ :=
      Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) z
    have hm : m ∈ Submodule.span R (Set.range s) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => exact (Submodule.span Q (Set.range t)).zero_mem
    | add y z _ _ hy hz => exact (Submodule.span Q (Set.range t)).add_mem hy hz
    | smul a y _ hy =>
        have hsmul := (Submodule.span Q (Set.range t)).smul_mem
          (Ideal.Quotient.mk (Ideal.span {x}) a) hy
        change (algebraMap R Q a) • Submodule.Quotient.mk y ∈
          Submodule.span Q (Set.range t) at hsmul
        rw [IsScalarTower.algebraMap_smul Q] at hsmul
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
        exact hsmul
  let f : (ι → Q) →ₗ[R] QuotSMulTop x M :=
    (Fintype.linearCombination Q t).restrictScalars R
  have hf : Function.Surjective f :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination Q t).mp ht
  calc
    Module.length R (QuotSMulTop x M) ≤ Module.length R (ι → Q) :=
      Module.length_le_of_surjective f hf
    _ = Fintype.card ι * Module.length R Q := by
      simp [Module.length_pi_of_fintype]

/-- The finite-module case of the finite-length lemma used in Krull--Akizuki.
For a finite module, reduction modulo a non-zero-divisor is finite over the
zero-dimensional noetherian quotient of the base, hence has finite length.

The substantive content of Stacks Project tag 00PF is that the same conclusion
holds for an *arbitrary* submodule of a finite-dimensional fraction-field vector
space, without assuming `Module.Finite R M`. -/
theorem isFiniteLength_quotSMulTop_of_module_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    IsFiniteLength R (QuotSMulTop x M) := by
  let Q := R ⧸ Ideal.span {x}
  have hbase : IsFiniteLength R Q :=
    isFiniteLength_quotient_span_singleton R hx
  letI : IsNoetherian R Q :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hbase).1
  letI : IsArtinian R Q :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hbase).2
  letI : Module.Finite R (QuotSMulTop x M) := inferInstance
  letI : Module.Finite Q (QuotSMulTop x M) :=
    Module.Finite.of_restrictScalars_finite R Q (QuotSMulTop x M)
  obtain ⟨n, s, hs⟩ :=
    Module.Finite.exists_fin (R := Q) (M := QuotSMulTop x M)
  let f : (Fin n → Q) →ₗ[R] QuotSMulTop x M :=
    (Fintype.linearCombination Q s).restrictScalars R
  have hf : Function.Surjective f :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination Q s).mp hs
  have hsource : IsFiniteLength R (Fin n → Q) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  exact hsource.of_surjective hf

/-- A finite torsion module over a one-dimensional noetherian domain has
finite length. -/
theorem Module.IsTorsion.isFiniteLength_of_finite
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.IsTorsion R M) : IsFiniteLength R M := by
  obtain ⟨x, hxann, hx⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hquot : IsFiniteLength R (QuotSMulTop x M) :=
    isFiniteLength_quotSMulTop_of_module_finite hx
  have hzero : x • (⊤ : Submodule R M) = ⊥ := by
    apply le_antisymm _ bot_le
    rintro y hy
    obtain ⟨z, -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact (Submodule.mem_annihilator.mp hxann) z Submodule.mem_top
  exact ((x • (⊤ : Submodule R M)).quotEquivOfEqBot hzero).isFiniteLength hquot

/-- A finitely generated full lattice in a finite-dimensional fraction-field
vector space has uniformly bounded reduction modulo a non-zero-divisor.

The proof clears all basis-coordinate denominators at once, sending the given
lattice into the standard free lattice.  The intervening quotient is finite
torsion, so the snake-lemma lattice comparison identifies the two reduction
lengths. -/
theorem Module.length_quotSMulTop_le_of_fg_spanning_fractionField
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (N : Submodule R V) (hN : N.FG)
    (hspan : Submodule.span K (N : Set V) = ⊤)
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    Module.length R (QuotSMulTop x N) ≤
      Module.finrank K V * Module.length R (R ⧸ Ideal.span {x}) := by
  classical
  let ι := Module.Free.ChooseBasisIndex K V
  let b : Basis ι K V := Module.Free.chooseBasis K V
  letI : Fintype ι := Fintype.ofFinite ι
  let B : Submodule R V := Submodule.span R (Set.range b)
  let bR : Basis ι R B := b.restrictScalars R
  letI : Module.Finite R B := Module.Finite.of_basis bR
  obtain ⟨k, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hN
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors R)
      (fun ij : Fin k × ι ↦ b.repr (s ij.1) ij.2)
  have hclear (i : Fin k) : d.val • s i ∈ B := by
    rw [b.mem_span_iff_repr_mem R]
    intro j
    obtain ⟨a, ha⟩ := hd (i, j)
    refine ⟨a, ?_⟩
    rw [← IsScalarTower.algebraMap_smul K d.val (s i), map_smul]
    simpa only [IsScalarTower.algebraMap_smul K, Finsupp.smul_apply] using ha
  have hd0 : d.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hdK : algebraMap R K d.val ≠ 0 :=
    fun h ↦ hd0 (IsFractionRing.injective R K (by simpa using h))
  let eK : V ≃ₗ[K] V :=
    LinearEquiv.smulOfNeZero K V (algebraMap R K d.val) hdK
  let e : V ≃ₗ[R] V := eK.restrictScalars R
  let P : Submodule R V := N.map e.toLinearMap
  have hPB : P ≤ B := by
    rw [Submodule.map_le_iff_le_comap, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change e (s i) ∈ B
    change algebraMap R K d.val • s i ∈ B
    rw [IsScalarTower.algebraMap_smul K]
    exact hclear i
  let C := B ⧸ P.comap B.subtype
  letI : Module.Finite R C := inferInstance
  have hCtorsion : Module.IsTorsion R C := by
    intro q
    obtain ⟨z, rfl⟩ :=
      Submodule.mkQ_surjective (P.comap B.subtype) q
    obtain ⟨c, hc⟩ :=
      N.exists_nonZeroDivisor_smul_mem_of_mem_span_fractionField
        (by rw [hspan]; trivial : (z : V) ∈ Submodule.span K (N : Set V))
    refine ⟨d * c, ?_⟩
    change (P.comap B.subtype).mkQ
      (((d * c : nonZeroDivisors R).val : R) • z) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change ((d * c : nonZeroDivisors R).val : R) • (z : V) ∈ P
    refine ⟨c.val • (z : V), hc, ?_⟩
    change e (c.val • (z : V)) =
      ((d * c : nonZeroDivisors R).val : R) • (z : V)
    simp only [e, eK, LinearEquiv.restrictScalars_apply,
      LinearEquiv.smulOfNeZero_apply, Submonoid.coe_mul,
      IsScalarTower.algebraMap_smul, smul_smul, map_mul]
  have hC : IsFiniteLength R C :=
    hCtorsion.isFiniteLength_of_finite
  have hx0 : x ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hx
  have hxK : algebraMap R K x ≠ 0 :=
    fun h ↦ hx0 (IsFractionRing.injective R K (by simpa using h))
  have hxV : IsSMulRegular V x := by
    intro y z hyz
    apply smul_right_injective V hxK
    simpa only [IsScalarTower.algebraMap_smul K] using hyz
  have hxB : IsSMulRegular B x := hxV.submodule B x
  have hcompare : Module.length R (QuotSMulTop x P) =
      Module.length R (QuotSMulTop x B) :=
    Module.length_quotSMulTop_eq_of_le_of_quotient_finiteLength
      P B hPB x hxB hC
  have hBbound : Module.length R (QuotSMulTop x B) ≤
      Fintype.card ι * Module.length R (R ⧸ Ideal.span {x}) :=
    Module.length_quotSMulTop_le_of_span_eq_top bR bR.span_eq hx
  calc
    Module.length R (QuotSMulTop x N) =
        Module.length R (QuotSMulTop x P) :=
      (QuotSMulTop.congr x (e.submoduleMap N)).length_eq
    _ = Module.length R (QuotSMulTop x B) := hcompare
    _ ≤ Fintype.card ι * Module.length R (R ⧸ Ideal.span {x}) := hBbound
    _ = Module.finrank K V * Module.length R (R ⧸ Ideal.span {x}) := by
      rw [Module.finrank_eq_card_basis b]

/-- The same uniform bound for an arbitrary finitely generated submodule of a
finite-dimensional fraction-field vector space.  Passing to its
fraction-field span reduces to the full-lattice case. -/
theorem Module.length_quotSMulTop_le_of_fg_submodule_fractionField
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (N : Submodule R V) (hN : N.FG)
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    Module.length R (QuotSMulTop x N) ≤
      Module.finrank K V * Module.length R (R ⧸ Ideal.span {x}) := by
  let W := Submodule.span K (N : Set V)
  let N' : Submodule R W :=
    N.comap (W.subtype.restrictScalars R)
  have hNW : N ≤ W.restrictScalars R := by
    intro z hz
    exact Submodule.subset_span hz
  have hN' : N'.FG := by
    apply Submodule.fg_of_fg_map_injective
      (W.subtype.restrictScalars R) W.injective_subtype
    have hmap : N'.map (W.subtype.restrictScalars R) = N := by
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap]
      · intro z hz
        refine ⟨⟨z, hNW hz⟩, hz, rfl⟩
    rw [hmap]
    exact hN
  have hspan : Submodule.span K (N' : Set W) = ⊤ := by
    simpa only [W, N'] using
      N.span_comap_span_fractionField_eq_top (K := K)
  have hbound :=
    Module.length_quotSMulTop_le_of_fg_spanning_fractionField
      N' hN' hspan hx
  let e : N' ≃ₗ[R] N :=
    Submodule.comapSubtypeEquivOfLe hNW
  calc
    Module.length R (QuotSMulTop x N) =
        Module.length R (QuotSMulTop x N') :=
      (QuotSMulTop.congr x e).length_eq.symm
    _ ≤ Module.finrank K W *
        Module.length R (R ⧸ Ideal.span {x}) := hbound
    _ ≤ Module.finrank K V *
        Module.length R (R ⧸ Ideal.span {x}) := by
      gcongr
      exact W.finrank_le

/-- **Stacks 00PE.** Reduction modulo a non-zero-divisor of an arbitrary
`R`-submodule of a finite-dimensional vector space over the fraction field of
a one-dimensional noetherian domain has finite length.

The uniform bound is the ambient vector-space dimension times the length of
`R / (x)`. -/
theorem isFiniteLength_quotSMulTop_of_submodule_fractionField
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (M : Submodule R V) {x : R} (hx : x ∈ nonZeroDivisors R) :
    IsFiniteLength R (QuotSMulTop x M) := by
  let n : ℕ∞ := Module.finrank K V *
    Module.length R (R ⧸ Ideal.span {x})
  have hbase : IsFiniteLength R (R ⧸ Ideal.span {x}) :=
    isFiniteLength_quotient_span_singleton R hx
  letI : IsFiniteLength R (R ⧸ Ideal.span {x}) := hbase
  have hn : n ≠ ⊤ := by
    exact WithTop.mul_ne_top (α := ℕ) (ENat.natCast_ne_top _)
      (Module.length_ne_top_iff.mpr hbase)
  apply isFiniteLength_quotSMulTop_of_bounded_fg_submodule_quotient_lengths
    x n hn
  intro N hN
  let P : Submodule R V := N.map M.subtype
  have hP : P.FG := hN.map M.subtype
  have hbound :=
    Module.length_quotSMulTop_le_of_fg_submodule_fractionField
      (R := R) (K := K) (V := V) P hP hx
  calc
    Module.length R (QuotSMulTop x N) =
        Module.length R (QuotSMulTop x P) :=
      (QuotSMulTop.congr x (M.equivSubtypeMap N)).length_eq
    _ ≤ n := by simpa only [n] using hbound

/-- The weakest quotient-ring form of the final step of Krull--Akizuki.

If `A` is algebraic over `R` and every quotient `A / xA` by a nonzero element
of `R` is a noetherian ring, then `A` is noetherian.  Indeed, every nonzero
ideal contains such an `x`, and its image modulo `xA` is finitely generated. -/
theorem IsNoetherianRing.of_noetherian_principal_quotients_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsAlgebraic R A]
    (hquotient : ∀ (x : R), x ≠ 0 →
      IsNoetherianRing (A ⧸ Ideal.span {algebraMap R A x})) :
    IsNoetherianRing A := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact ⟨∅, by simp⟩
  obtain ⟨x, hx0, hxI⟩ := I.exists_ne_zero_mem_of_isAlgebraic (R := R) hI
  let J : Ideal A := Ideal.span {algebraMap R A x}
  let q : A →+* A ⧸ J := Ideal.Quotient.mk J
  have hJI : J ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
  letI : IsNoetherianRing (A ⧸ J) := hquotient x hx0
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective (f := q)
  · exact Ideal.fg_of_isNoetherianRing (I.map q)
  · rw [Ideal.mk_ker, inf_eq_right.mpr hJI]
    exact ⟨{algebraMap R A x}, by simp only [Finset.coe_singleton, J]⟩
  · exact Ideal.Quotient.mk_surjective

/-- The ACC-on-submodules form of the final step of Krull--Akizuki.

It is enough that `A / xA`, written as `QuotSMulTop x A`, be a noetherian
`R`-module for every nonzero `x`. -/
theorem IsNoetherianRing.of_isNoetherian_quotients_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsAlgebraic R A]
    (hnoetherian : ∀ (x : R), x ≠ 0 →
      IsNoetherian R (QuotSMulTop x A)) :
    IsNoetherianRing A := by
  apply IsNoetherianRing.of_noetherian_principal_quotients_of_isAlgebraic
    (R := R) (A := A)
  intro x hx
  have hquotient :
      IsNoetherian R (A ⧸ Ideal.span {algebraMap R A x}) :=
    IsNoetherian.idealQuotient_span_algebraMap x (hnoetherian x hx)
  exact isNoetherian_of_tower R hquotient

/-- The finite-generation form of the final step of Krull--Akizuki.

Over a noetherian base, it is enough that every `A / xA` be finitely generated
as an `R`-module.  This isolates a strictly weaker sufficient input than the
finite-length conclusion of Stacks Project tag 00PF. -/
theorem IsNoetherianRing.of_finite_quotients_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsAlgebraic R A]
    (hfinite : ∀ (x : R), x ≠ 0 → Module.Finite R (QuotSMulTop x A)) :
    IsNoetherianRing A := by
  apply IsNoetherianRing.of_isNoetherian_quotients_of_isAlgebraic
    (R := R) (A := A)
  intro x hx
  letI : Module.Finite R (QuotSMulTop x A) := hfinite x hx
  exact inferInstance

/-- The finite-length form of the final, purely formal step of
Krull--Akizuki.  In the usual one-dimensional fraction-field setting, Stacks
Project tag 00PF supplies precisely this input. -/
theorem IsNoetherianRing.of_finiteLength_quotients_of_isAlgebraic
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsAlgebraic R A]
    (hfiniteLength : ∀ (x : R), x ≠ 0 →
      IsFiniteLength R (A ⧸ Ideal.span {algebraMap R A x})) :
    IsNoetherianRing A := by
  apply IsNoetherianRing.of_noetherian_principal_quotients_of_isAlgebraic
    (R := R) (A := A)
  intro x hx
  have hnoetherian :
      IsNoetherian R (A ⧸ Ideal.span {algebraMap R A x}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (hfiniteLength x hx)).1
  exact isNoetherian_of_tower R hnoetherian
