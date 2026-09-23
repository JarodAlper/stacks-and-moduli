module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Flat finite graded modules over a local base

Stacks Project tag **053C**, label
`more-algebra-lemma-flat-graded-finite-type-finite-presentation-module`, in
`more-algebra.tex`, §`054A` (`section-flat-finite-presentation`, Flatness and finiteness
conditions).

The Stacks proof presents the graded module by finitely many homogeneous generators, proves that
each homogeneous piece of the relation module is finite free over the local base, chooses finitely
many homogeneous relations after passage to the residue field, and then applies Nakayama degree by
degree.  This file first records the last step in a form independent of the chosen presentation.
-/

@[expose] public section

open DirectSum
open scoped TensorProduct

universe uR uS uM uF

section Tag053C

variable {ιA ιM : Type*} {R : Type uR} {S : Type uS} {M : Type uM}
  [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
  (𝒜 : ιA → Submodule R S) (ℳ : ιM → Submodule R M)
  [DecidableEq ιA] [DecidableEq ιM] [AddMonoid ιA] [AddAction ιA ιM]
  [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

include 𝒜 in
/-- The homogeneous component of a scalar multiple of a homogeneous element remains in every
submodule containing that element. -/
theorem Submodule.decompose_smul_mem_of_isHomogeneousElem
    (W : Submodule S M) (r : S) (x : M) (hxhom : SetLike.IsHomogeneousElem ℳ x)
    (hxW : x ∈ W) (j : ιM) : (DirectSum.decompose ℳ (r • x) j : M) ∈ W := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Submodule.sum_mem
  intro k hk
  obtain ⟨i, hi⟩ := hxhom
  have hmem : (DirectSum.decompose 𝒜 r k : S) • x ∈ ℳ (k +ᵥ i) :=
    SetLike.GradedSMul.smul_mem (DirectSum.decompose 𝒜 r k).2 hi
  rw [DirectSum.decompose_of_mem ℳ hmem, DirectSum.coe_of_apply]
  split_ifs
  · exact W.smul_mem _ hxW
  · exact W.zero_mem

set_option backward.isDefEq.respectTransparency false in
include 𝒜 in
/-- The span of homogeneous elements in a graded module is a homogeneous submodule. -/
theorem Submodule.isHomogeneous_span_of_isHomogeneousElem
    (s : Set M) (hs : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) :
    (Submodule.span S s).IsHomogeneous ℳ := by
  rintro j r hr
  rw [Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨c, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply, Finsupp.sum, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ ?_
  rintro z hz
  refine Submodule.decompose_smul_mem_of_isHomogeneousElem 𝒜 ℳ _ (c z) z ?_ ?_ j
  · rcases z with ⟨z, hz'⟩
    exact hs z hz'
  · exact Submodule.subset_span z.2

omit [Algebra R S] in
/-- A finite module with an additive decomposition admits a finite homogeneous generating set. -/
theorem Module.Finite.exists_finset_isHomogeneousElem_span_eq_top
    [Module.Finite S M] :
    ∃ t : Finset M, (∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span S (t : Set M) = ⊤ := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  let t : Finset M := Finset.univ.biUnion fun i : Fin n =>
    (DirectSum.decompose ℳ (g i)).support.image fun d =>
      (DirectSum.decompose ℳ (g i) d : M)
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hx
    obtain ⟨i, d, hd, rfl⟩ := hx
    exact ⟨d, (DirectSum.decompose ℳ (g i) d).2⟩
  · apply top_unique
    rw [← hg, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← DirectSum.sum_support_decompose ℳ (g i)]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.subset_span
    change (DirectSum.decompose ℳ (g i) d : M) ∈ t
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨i, d, hd, rfl⟩

/-- If the pieces of a graded ring are finite over the coefficient ring and only finitely many
ring degrees can carry a fixed module degree to another fixed degree, then every component of a
finite graded module is finite over the coefficient ring. -/
theorem Module.Finite.finite_decomposition_component
    [IsScalarTower R S M] [Module.Finite S M]
    (hA : ∀ a, Module.Finite R (𝒜 a))
    (hsol : ∀ (e d : ιM), Set.Finite {a : ιA | a +ᵥ e = d}) (d : ιM) :
    Module.Finite R (ℳ d) := by
  classical
  obtain ⟨t, htHom, htSpan⟩ :=
    Module.Finite.exists_finset_isHomogeneousElem_span_eq_top (S := S) ℳ
  let e : t → ιM := fun x => (htHom x x.2).choose
  have he (x : t) : (x : M) ∈ ℳ (e x) := (htHom x x.2).choose_spec
  let sol (x : t) : Finset ιA := (hsol (e x) d).toFinset
  let L (x : t) (a : {a : ιA // a ∈ sol x}) : 𝒜 a.1 →ₗ[R] M :=
    { toFun := fun p => (p : S) • (x : M)
      map_add' := fun p q => add_smul (p : S) (q : S) (x : M)
      map_smul' := fun r p => by
        change (r • (p : S)) • (x : M) = r • ((p : S) • (x : M))
        exact smul_assoc r (p : S) (x : M) }
  let N : Submodule R M :=
    ⨆ x : t, ⨆ a : {a : ιA // a ∈ sol x}, LinearMap.range (L x a)
  have hNfg : N.FG := by
    apply Submodule.fg_iSup
    intro x
    apply Submodule.fg_iSup
    intro a
    exact Submodule.fg_range (L x a)
  have hNle : N ≤ ℳ d := by
    refine iSup_le fun x => iSup_le fun a => ?_
    rintro _ ⟨p, rfl⟩
    change (p : S) • (x : M) ∈ ℳ d
    have hmem : (p : S) • (x : M) ∈ ℳ (a.1 +ᵥ e x) :=
      SetLike.GradedSMul.smul_mem p.2 (he x)
    have ha : a.1 +ᵥ e x = d := by
      simpa only [sol, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.2
    exact ha ▸ hmem
  have hle : (ℳ d : Submodule R M) ≤ N := by
    intro y hy
    have hyspan : y ∈ Submodule.span S (t : Set M) := by rw [htSpan]; trivial
    rw [Finsupp.span_eq_range_linearCombination, LinearMap.mem_range] at hyspan
    obtain ⟨c, hc⟩ := hyspan
    rw [← DirectSum.decompose_of_mem_same ℳ hy, ← hc, Finsupp.linearCombination_apply,
      Finsupp.sum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
      AddSubmonoidClass.coe_finsetSum]
    apply Submodule.sum_mem
    intro x hx
    rw [← DirectSum.sum_support_decompose 𝒜 (c x), Finset.sum_smul,
      DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    apply Submodule.sum_mem
    intro a ha
    have hmem : (DirectSum.decompose 𝒜 (c x) a : S) • (x : M) ∈
        ℳ (a +ᵥ e x) := SetLike.GradedSMul.smul_mem
          (DirectSum.decompose 𝒜 (c x) a).2 (he x)
    rw [DirectSum.decompose_of_mem ℳ hmem, DirectSum.coe_of_apply]
    split_ifs with had
    · change (DirectSum.decompose 𝒜 (c x) a : S) • (x : M) ∈ N
      let a' : {a : ιA // a ∈ sol x} := ⟨a, by
        simp only [sol, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact had⟩
      exact (le_iSup (fun x : t => ⨆ a : {a : ιA // a ∈ sol x},
        LinearMap.range (L x a)) x) ((le_iSup (fun a : {a : ιA // a ∈ sol x} =>
          LinearMap.range (L x a)) a') ⟨DirectSum.decompose 𝒜 (c x) a, rfl⟩)
    · exact N.zero_mem
  have heq : (ℳ d : Submodule R M) = N := le_antisymm hle hNle
  rw [Module.Finite.iff_fg, heq]
  exact hNfg

/-- Every component of a flat module with an internal direct-sum decomposition is flat. -/
theorem Module.Flat.decomposition_component [Module.Flat R M] (i : ιM) :
    Module.Flat R (ℳ i) := by
  let p : M →ₗ[R] ℳ i :=
    DirectSum.component R ιM (fun i => ↥(ℳ i)) i ∘ₗ
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap
  refine Module.Flat.of_retract (ℳ i).subtype p ?_
  ext x
  change (DirectSum.decompose ℳ (x : M) i : M) = x
  exact DirectSum.decompose_of_mem_same ℳ x.2

/-- Under the degree-finiteness hypotheses, every homogeneous component of a finite graded module
that is flat over a local coefficient ring is finite free over that ring. -/
theorem Module.Finite.free_decomposition_component_of_flat_of_isLocalRing
    [IsScalarTower R S M] [Module.Finite S M] [Module.Flat R M] [IsLocalRing R]
    (hA : ∀ a, Module.Finite R (𝒜 a))
    (hsol : ∀ (e d : ιM), Set.Finite {a : ιA | a +ᵥ e = d}) (d : ιM) :
    Module.Free R (ℳ d) := by
  let _ : Module.Finite R (ℳ d) :=
    Module.Finite.finite_decomposition_component 𝒜 ℳ hA hsol d
  let _ : Module.Flat R (ℳ d) := Module.Flat.decomposition_component ℳ d
  exact Module.free_of_flat_of_isLocalRing

variable {R : Type uR} {S : Type uS} {K : Type uM} [CommRing R] [CommRing S]
  [Algebra R S] [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]

/-- A degreewise form of Nakayama's lemma.  If an `S`-submodule contains every graded piece
modulo the maximal ideal of a local base ring, and every piece is finite over the base, then it is
the whole module. -/
theorem Submodule.eq_top_of_degreewise_le_sup_maximalIdeal_smul
    {ι : Type*} [DecidableEq ι] (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (W : Submodule S K)
    (hfinite : ∀ i, Module.Finite R (𝒦 i)) [IsLocalRing R]
    (hmod : ∀ i, (𝒦 i : Submodule R K) ≤
      W.restrictScalars R ⊔ IsLocalRing.maximalIdeal R • (𝒦 i : Submodule R K)) :
    W = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  rw [← DirectSum.sum_support_decompose 𝒦 x]
  apply Submodule.sum_mem
  intro i hi
  have hpiece : (𝒦 i : Submodule R K) ≤ W.restrictScalars R :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.Finite.iff_fg.mp (hfinite i))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) (hmod i)
  exact hpiece (DirectSum.decompose 𝒦 x i).2

/-- Taking a homogeneous component preserves membership in the product of an ideal with the
whole module, and lands in the product with the corresponding homogeneous piece. -/
theorem DirectSum.decompose_mem_ideal_smul_piece
    {ι : Type*} [DecidableEq ι] (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (I : Ideal R) (x : K)
    (hx : x ∈ I • (⊤ : Submodule R K)) (i : ι) :
    (DirectSum.decompose 𝒦 x i : K) ∈ I • (𝒦 i : Submodule R K) := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun x y hx hy => ?_)
  · have hdec : DirectSum.decompose 𝒦 (r • y) i =
        r • DirectSum.decompose 𝒦 y i :=
      DFunLike.congr_fun (DirectSum.decompose_smul 𝒦 r y) i
    rw [hdec]
    exact Submodule.smul_mem_smul hr (DirectSum.decompose 𝒦 y i).2
  · have hdec := DFunLike.congr_fun (DirectSum.decompose_add 𝒦 x y) i
    rw [hdec]
    exact Submodule.add_mem _ hx hy

/-- The `S`-submodule whose underlying `R`-submodule is an ideal of `R` times the whole module. -/
def Submodule.algebraIdealSMulTop (I : Ideal R) : Submodule S K where
  carrier := {x | x ∈ I • (⊤ : Submodule R K)}
  zero_mem' := (I • (⊤ : Submodule R K)).zero_mem
  add_mem' := fun hx hy => (I • (⊤ : Submodule R K)).add_mem hx hy
  smul_mem' := by
    intro s x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun x y hx hy => ?_)
    · rw [smul_comm s r y]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    · rw [smul_add]
      exact (I • (⊤ : Submodule R K)).add_mem hx hy

@[simp]
theorem Submodule.mem_algebraIdealSMulTop_iff (I : Ideal R) (x : K) :
    x ∈ Submodule.algebraIdealSMulTop (S := S) (K := K) I ↔
      x ∈ I • (⊤ : Submodule R K) := by
  rfl

@[simp]
theorem Submodule.algebraIdealSMulTop_restrictScalars (I : Ideal R) :
    (Submodule.algebraIdealSMulTop (S := S) (K := K) I).restrictScalars R =
      I • (⊤ : Submodule R K) := by
  ext x
  rfl

variable {F : Type uF} {M : Type uM} [AddCommGroup F] [Module R F] [Module S F]
  [IsScalarTower R S F] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- Restricting the scalars of a linear map does not change its kernel. -/
noncomputable def LinearMap.kerRestrictScalarsEquiv (f : F →ₗ[S] M) :
    f.ker ≃ₗ[R] (f.restrictScalars R).ker where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The quotient of an `S`-module by the extension of an ideal of the coefficient ring. -/
abbrev Submodule.AlgebraIdealQuotient (I : Ideal R) :=
  K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I

/-- The inclusion of a submodule carries its coefficient-ideal multiple into the corresponding
coefficient-ideal multiple of the ambient module. -/
theorem Submodule.algebraIdealSMulTop_subtype_mem (f : F →ₗ[S] M) (I : Ideal R)
    (x : f.ker) (hx : x ∈ Submodule.algebraIdealSMulTop (S := S) (K := f.ker) I) :
    (x : F) ∈ Submodule.algebraIdealSMulTop (S := S) (K := F) I := by
  change (x : F) ∈ I • (⊤ : Submodule R F)
  change x ∈ I • (⊤ : Submodule R f.ker) at hx
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun x y hx hy => ?_)
  · exact Submodule.smul_mem_smul hr Submodule.mem_top
  · exact (I • (⊤ : Submodule R F)).add_mem hx hy

/-- Multiplication by an ideal of the coefficient ring agrees with multiplication by the
extended ideal. -/
theorem Submodule.algebraIdealSMulTop_eq_map_smul_top (I : Ideal R) :
    Submodule.algebraIdealSMulTop (S := S) (K := K) I =
      I.map (algebraMap R S) • (⊤ : Submodule S K) := by
  apply le_antisymm
  · intro x hx
    change x ∈ I • (⊤ : Submodule R K) at hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
    · have hmem := Submodule.smul_mem_smul
        (Ideal.mem_map_of_mem (algebraMap R S) hr) (Submodule.mem_top : y ∈ (⊤ : Submodule S K))
      simpa only [IsScalarTower.algebraMap_smul S] using hmem
    · exact (I.map (algebraMap R S) • (⊤ : Submodule S K)).add_mem ha hb
  · let A : Ideal S :=
      { carrier := {s | ∀ x : K, s • x ∈ I • (⊤ : Submodule R K)}
        zero_mem' := fun x => by rw [zero_smul]; exact Submodule.zero_mem _
        add_mem' := fun hs ht x => by
          rw [add_smul]
          exact (I • (⊤ : Submodule R K)).add_mem (hs x) (ht x)
        smul_mem' := fun s t ht x => by
          rw [smul_eq_mul, mul_smul]
          exact (Submodule.algebraIdealSMulTop (S := S) (K := K) I).smul_mem s (ht x) }
    have hmap : I.map (algebraMap R S) ≤ A := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change ∀ x : K, algebraMap R S r • x ∈ I • (⊤ : Submodule R K)
      intro x
      rw [IsScalarTower.algebraMap_smul S]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    intro x hx
    change x ∈ I.map (algebraMap R S) • (⊤ : Submodule S K) at hx
    change x ∈ I • (⊤ : Submodule R K)
    refine Submodule.smul_induction_on hx (fun s hs y hy => ?_) (fun a b ha hb => ?_)
    · exact hmap hs y
    · exact (I • (⊤ : Submodule R K)).add_mem ha hb

/-- A quotient by a coefficient-ideal multiple is naturally a module over the quotient of the
polynomial ring by the extended ideal. -/
theorem Submodule.algebraIdealQuotient_isTorsionBySet (I : Ideal R) :
    Module.IsTorsionBySet S
      (Submodule.AlgebraIdealQuotient (S := S) (K := K) I)
      (I.map (algebraMap R S) : Set S) := by
  change Module.IsTorsionBySet S
    (K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I)
    (I.map (algebraMap R S) : Set S)
  rw [Submodule.algebraIdealSMulTop_eq_map_smul_top]
  exact Module.isTorsionBySet_quotient_ideal_smul K (I.map (algebraMap R S))

/-- The map from the coefficient-ideal quotient of a relation module to the corresponding
quotient of the source module. -/
noncomputable def LinearMap.relationQuotientToSourceQuotient (f : F →ₗ[S] M) (I : Ideal R) :
    Submodule.AlgebraIdealQuotient (R := R) (S := S) (K := f.ker) I →ₗ[S]
      Submodule.AlgebraIdealQuotient (R := R) (S := S) (K := F) I :=
  (Submodule.algebraIdealSMulTop (S := S) (K := f.ker) I).mapQ
    (τ₁₂ := RingHom.id S)
    (Submodule.algebraIdealSMulTop (S := S) (K := F) I)
    f.ker.subtype (fun x hx => Submodule.algebraIdealSMulTop_subtype_mem (R := R) f I x hx)

@[simp]
theorem LinearMap.relationQuotientToSourceQuotient_mk (f : F →ₗ[S] M) (I : Ideal R)
    (x : f.ker) :
    f.relationQuotientToSourceQuotient (R := R) I
      ((Submodule.algebraIdealSMulTop (S := S) (K := f.ker) I).mkQ x) =
      (Submodule.algebraIdealSMulTop (S := S) (K := F) I).mkQ x.1 := rfl

/-- If the target is flat over the coefficient ring, passage to a coefficient-ideal quotient
preserves the inclusion of the relation module into the source. -/
theorem LinearMap.injective_relationQuotientToSourceQuotient
    (f : F →ₗ[S] M) (hf : Function.Surjective f) [Module.Flat R M]
    (I : Ideal R) : Function.Injective (f.relationQuotientToSourceQuotient (R := R) I) := by
  let g := f.restrictScalars R
  have hg : Function.Surjective g := hf
  let e := f.kerRestrictScalarsEquiv (R := R)
  let JK := Submodule.algebraIdealSMulTop (S := S) (K := f.ker) I
  let JF := Submodule.algebraIdealSMulTop (S := S) (K := F) I
  let qmap : (f.ker ⧸ JK) →ₗ[S] (F ⧸ JF) :=
    f.relationQuotientToSourceQuotient (R := R) I
  intro x y hxy
  obtain ⟨x, rfl⟩ := JK.mkQ_surjective x
  obtain ⟨y, rfl⟩ := JK.mkQ_surjective y
  apply (Submodule.Quotient.eq JK).mpr
  change x - y ∈ JK
  have hsource : (x - y : f.ker).1 ∈ I • (⊤ : Submodule R F) := by
    have hzero : qmap (JK.mkQ (x - y)) = 0 := by
      rw [map_sub, map_sub, hxy, sub_self]
    have hzero' : JF.mkQ ((x - y : f.ker).1) = 0 := by
      change qmap (JK.mkQ (x - y)) = 0
      exact hzero
    have hmem : (x - y : f.ker).1 ∈ JF :=
      (Submodule.Quotient.mk_eq_zero _).mp hzero'
    exact hmem
  let z : g.ker := e (x - y)
  have htensorF : (1 : R ⧸ I) ⊗ₜ[R] (z : F) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul F I).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    have hzval : (z : F) = (x - y : f.ker).1 := rfl
    rw [map_zero, Submodule.Quotient.mk_eq_zero, hzval]
    exact hsource
  have htensorK : (1 : R ⧸ I) ⊗ₜ[R] z = 0 := by
    let E := g.kerLTensorEquivOfSurjective hg (R ⧸ I)
    have hz : E.symm ((1 : R ⧸ I) ⊗ₜ[R] z) = 0 := by
      apply Subtype.ext
      change ((g.kerLTensorEquivOfSurjective hg (R ⧸ I)).symm
        ((1 : R ⧸ I) ⊗ₜ[R] z)).1 = 0
      rw [LinearMap.tensorKerEquivOfSurjective_symm_tmul]
      exact htensorF
    apply E.symm.injective
    simpa using hz
  have hzmod : z ∈ I • (⊤ : Submodule R g.ker) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact congrArg (TensorProduct.quotTensorEquivQuotSMul g.ker I) htensorK
  have hxmod : e.symm z ∈ I • (⊤ : Submodule R f.ker) := by
    refine Submodule.smul_induction_on hzmod (fun r hr w hw => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact (I • (⊤ : Submodule R f.ker)).add_mem ha hb
  change x - y ∈ I • (⊤ : Submodule R f.ker)
  have he : e.symm z = x - y := by simp only [z, e, LinearEquiv.symm_apply_apply]
  rwa [← he]

/-- The relation module modulo a coefficient ideal is finite when the target is coefficient-flat
and the corresponding quotient of the source ring is noetherian. -/
theorem Module.Finite.relationQuotient_of_flat
    (f : F →ₗ[S] M) (hf : Function.Surjective f) [Module.Flat R M]
    [Module.Finite S F] (I : Ideal R)
    [IsNoetherianRing (S ⧸ I.map (algebraMap R S))] :
    Module.Finite S
      (Submodule.AlgebraIdealQuotient (R := R) (S := S) (K := f.ker) I) := by
  let Sbar := S ⧸ I.map (algebraMap R S)
  let QK := Submodule.AlgebraIdealQuotient (R := R) (S := S) (K := f.ker) I
  let QF := Submodule.AlgebraIdealQuotient (R := R) (S := S) (K := F) I
  let hK := Submodule.algebraIdealQuotient_isTorsionBySet
    (R := R) (S := S) (K := f.ker) I
  let hF := Submodule.algebraIdealQuotient_isTorsionBySet
    (R := R) (S := S) (K := F) I
  letI : Module Sbar QK := hK.module
  letI : Module Sbar QF := hF.module
  letI : IsScalarTower S Sbar QK := hK.isScalarTower
  letI : IsScalarTower S Sbar QF := hF.isScalarTower
  letI : Module.Finite S QF := inferInstance
  letI : Module.Finite Sbar QF := Module.Finite.of_restrictScalars_finite S Sbar QF
  letI : IsNoetherian Sbar QF := inferInstance
  let qmap : QK →ₗ[S] QF := f.relationQuotientToSourceQuotient (R := R) I
  let qmapBar : QK →ₗ[Sbar] QF :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective qmap
  have hqmap : Function.Injective qmapBar :=
    f.injective_relationQuotientToSourceQuotient (R := R) hf I
  letI : Module.Finite Sbar QK := Module.Finite.of_injective qmapBar hqmap
  exact Module.Finite.trans Sbar QK

/-- The submodule obtained by multiplying by an ideal of the coefficient ring is homogeneous. -/
theorem Submodule.isHomogeneous_algebraIdealSMulTop
    {ι : Type*} [DecidableEq ι] (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (I : Ideal R) :
    (Submodule.algebraIdealSMulTop (S := S) (K := K) I).IsHomogeneous 𝒦 := by
  intro d x hx
  have hd := DirectSum.decompose_mem_ideal_smul_piece 𝒦 I x hx d
  change (DirectSum.decompose 𝒦 x d : K) ∈ I • (⊤ : Submodule R K)
  refine Submodule.smul_induction_on hd (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · exact Submodule.smul_mem_smul hr Submodule.mem_top
  · exact (I • (⊤ : Submodule R K)).add_mem ha hb

namespace Submodule.QuotientGrading

variable {ι : Type*} [DecidableEq ι]

/-- The image of a homogeneous piece in a quotient by a homogeneous submodule. -/
def piece (𝒦 : ι → Submodule R K) (J : Submodule S K) (d : ι) :
    Submodule R (K ⧸ J) :=
  LinearMap.range ((J.mkQ.restrictScalars R).comp (𝒦 d).subtype)

/-- The quotient map restricted to a homogeneous piece. -/
def pieceMap (𝒦 : ι → Submodule R K) (J : Submodule S K) (d : ι) :
    𝒦 d →ₗ[R] piece 𝒦 J d :=
  ((J.mkQ.restrictScalars R).comp (𝒦 d).subtype).rangeRestrict

@[simp]
theorem pieceMap_coe (𝒦 : ι → Submodule R K) (J : Submodule S K)
    (d : ι) (x : 𝒦 d) :
    (pieceMap 𝒦 J d x : K ⧸ J) = J.mkQ x.1 := rfl

/-- Decompose in the source and then map every component to the quotient. -/
def preDecompose (𝒦 : ι → Submodule R K) [DirectSum.Decomposition 𝒦]
    (J : Submodule S K) :
    K →ₗ[R] ⨁ d : ι, piece 𝒦 J d :=
  DirectSum.lmap (pieceMap 𝒦 J) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒦).toLinearMap

theorem preDecompose_mem_ker (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) (x : K) (hx : x ∈ J) :
    preDecompose 𝒦 J x = 0 := by
  apply DFinsupp.ext
  intro d
  change pieceMap 𝒦 J d (DirectSum.decompose 𝒦 x d) = 0
  apply Subtype.ext
  change J.mkQ (DirectSum.decompose 𝒦 x d : K) = 0
  exact (Submodule.Quotient.mk_eq_zero J).mpr (hJ d hx)

/-- The decomposition map on the quotient viewed first as a quotient of `R`-modules. -/
noncomputable def decomposeRestricted (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) :
    (K ⧸ J.restrictScalars R) →ₗ[R] ⨁ d : ι, piece 𝒦 J d :=
  (J.restrictScalars R).liftQ (R₂ := R)
    (M₂ := ⨁ d : ι, piece 𝒦 J d) (τ₁₂ := RingHom.id R)
    (preDecompose 𝒦 J : K →ₗ[R] ⨁ d : ι, piece 𝒦 J d)
    (fun x hx => LinearMap.mem_ker.mpr (preDecompose_mem_ker 𝒦 J hJ x hx))

/-- The decomposition map on the quotient by a homogeneous submodule. -/
noncomputable def decompose (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) :
    (K ⧸ J) →ₗ[R] ⨁ d : ι, piece 𝒦 J d :=
  decomposeRestricted 𝒦 J hJ ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R J).symm.toLinearMap

/-- Recompose the images of homogeneous pieces in the quotient. -/
def recompose (𝒦 : ι → Submodule R K) (J : Submodule S K) :
    (⨁ d : ι, piece 𝒦 J d) →ₗ[R] (K ⧸ J) :=
  DirectSum.coeLinearMap (piece 𝒦 J)

@[simp]
theorem decompose_mk (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) (x : K) :
    decompose 𝒦 J hJ (J.mkQ x) = preDecompose 𝒦 J x := rfl

theorem recompose_comp_preDecompose (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K) :
    recompose 𝒦 J ∘ₗ preDecompose 𝒦 J = J.mkQ.restrictScalars R := by
  apply DirectSum.decompose_lhom_ext 𝒦
  intro d
  apply LinearMap.ext
  intro x
  change DirectSum.coeLinearMap (piece 𝒦 J)
    (DirectSum.lmap (pieceMap 𝒦 J)
      (DirectSum.decomposeLinearEquiv 𝒦 x)) = J.mkQ x.1
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof,
    DirectSum.coeLinearMap_lof]
  rfl

theorem recompose_comp_decompose (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) :
    recompose 𝒦 J ∘ₗ decompose 𝒦 J hJ = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := J.mkQ_surjective q
  rw [LinearMap.comp_apply, decompose_mk]
  exact DFunLike.congr_fun (recompose_comp_preDecompose 𝒦 J) x

theorem decompose_comp_recompose (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K)
    (hJ : J.IsHomogeneous 𝒦) :
    decompose 𝒦 J hJ ∘ₗ recompose 𝒦 J = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro d
  apply LinearMap.ext
  intro q
  obtain ⟨x, hx⟩ := q.2
  apply DFinsupp.ext
  intro e
  simp only [LinearMap.comp_apply, recompose, DirectSum.coeLinearMap_lof,
    LinearMap.id_apply]
  change (decompose 𝒦 J hJ q.1) e =
    (DirectSum.lof R ι (fun d => piece 𝒦 J d) d q) e
  have hqx : q = pieceMap 𝒦 J d x := by
    apply Subtype.ext
    exact hx.symm
  rw [hqx, pieceMap_coe, decompose_mk]
  change (DirectSum.lmap (pieceMap 𝒦 J)
    (DirectSum.decomposeLinearEquiv 𝒦 (x : K))) e = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

/-- The quotient by a homogeneous submodule decomposes as the direct sum of the images of the
homogeneous pieces. -/
@[instance_reducible]
noncomputable def decomposition (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (J : Submodule S K) (hJ : J.IsHomogeneous 𝒦) :
    DirectSum.Decomposition (piece 𝒦 J) :=
  DirectSum.Decomposition.ofLinearMap (piece 𝒦 J)
    (decompose 𝒦 J hJ)
    (recompose_comp_decompose 𝒦 J hJ)
    (decompose_comp_recompose 𝒦 J hJ)

/-- Every element of a quotient piece has a lift in the corresponding source piece. -/
theorem exists_lift (𝒦 : ι → Submodule R K)
    (J : Submodule S K) (d : ι) (y : piece 𝒦 J d) :
    ∃ x : 𝒦 d, J.mkQ x.1 = y.1 := by
  exact y.2

variable {ιA : Type*} [DecidableEq ιA] [AddMonoid ιA] [AddAction ιA ι]

/-- The quotient-piece decomposition inherits the graded scalar action of the source. -/
theorem gradedSMul (𝒜 : ιA → Submodule R S)
    [GradedRing 𝒜] (𝒦 : ι → Submodule R K) [DirectSum.Decomposition 𝒦]
    [SetLike.GradedSMul 𝒜 𝒦] (J : Submodule S K) :
    SetLike.GradedSMul 𝒜 (piece 𝒦 J) where
  smul_mem := by
    intro a d p y hp hy
    obtain ⟨x, hx⟩ := hy
    let z : 𝒦 (a +ᵥ d) :=
      ⟨(p : S) • (x : K), SetLike.GradedSMul.smul_mem hp x.2⟩
    refine ⟨z, ?_⟩
    change J.mkQ ((p : S) • (x : K)) = (p : S) • y
    change J.mkQ x.1 = y at hx
    rw [map_smul, hx]

end Submodule.QuotientGrading

/-- If the quotient of a module by an extended coefficient ideal is finite, finitely many lifts
of quotient generators generate the original module modulo that ideal. -/
theorem Module.Finite.exists_fin_global_mod_ideal
    (I : Ideal R)
    [Module.Finite S (K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I)] :
    ∃ (n : ℕ) (k : Fin n → K),
      (⊤ : Submodule R K) ≤
        (Submodule.span S (Set.range k)).restrictScalars R ⊔
          I • (⊤ : Submodule R K) := by
  classical
  let J := Submodule.algebraIdealSMulTop (S := S) (K := K) I
  obtain ⟨n, y, hy⟩ := Module.Finite.exists_fin (R := S) (M := K ⧸ J)
  choose k hk using fun i => J.mkQ_surjective (y i)
  refine ⟨n, k, ?_⟩
  intro x hx
  have hxy : J.mkQ x ∈ Submodule.span S (Set.range y) := by rw [hy]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hxy
  let w : K := ∑ i, c i • k i
  have hw : w ∈ Submodule.span S (Set.range k) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hqw : J.mkQ w = J.mkQ x := by
    rw [map_sum]
    simp_rw [map_smul, hk]
    exact hc
  have hz : x - w ∈ I • (⊤ : Submodule R K) := by
    have hzJ : x - w ∈ J := by
      rw [← Submodule.ker_mkQ J, LinearMap.mem_ker]
      rw [map_sub, hqw, sub_self]
    simpa only [J, Submodule.mem_algebraIdealSMulTop_iff] using hzJ
  exact Submodule.mem_sup.mpr ⟨w, hw, x - w, hz, by abel⟩

/-- A graded refinement of `Module.Finite.exists_fin_global_mod_ideal`.  If homogeneous elements
of the quotient lift to homogeneous elements of the original module, one may choose all the
generators modulo the ideal to be homogeneous. -/
theorem Module.Finite.exists_finset_isHomogeneousElem_global_mod_ideal
    {ιA' ι' : Type*} [DecidableEq ιA'] [DecidableEq ι']
    [AddMonoid ιA'] [AddAction ιA' ι']
    (𝒜' : ιA' → Submodule R S) [GradedRing 𝒜']
    (𝒦 : ι' → Submodule R K) [DirectSum.Decomposition 𝒦]
    [SetLike.GradedSMul 𝒜' 𝒦] (I : Ideal R)
    (𝒬 : ι' → Submodule R
      (K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I))
    [DirectSum.Decomposition 𝒬] [SetLike.GradedSMul 𝒜' 𝒬]
    [Module.Finite S (K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I)]
    (hlift : ∀ d (y : 𝒬 d), ∃ x : 𝒦 d,
      (Submodule.algebraIdealSMulTop (S := S) (K := K) I).mkQ x.1 = y.1) :
    ∃ (t : Finset
      (K ⧸ Submodule.algebraIdealSMulTop (S := S) (K := K) I)) (k : t → K),
      (∀ j, SetLike.IsHomogeneousElem 𝒦 (k j)) ∧
        (⊤ : Submodule R K) ≤
          (Submodule.span S (Set.range k)).restrictScalars R ⊔
            I • (⊤ : Submodule R K) := by
  let J := Submodule.algebraIdealSMulTop (S := S) (K := K) I
  let Q := K ⧸ J
  classical
  obtain ⟨t, htHom, htSpan⟩ :=
    Module.Finite.exists_finset_isHomogeneousElem_span_eq_top (S := S) 𝒬
  let deg : t → ι' := fun y => (htHom y y.2).choose
  have hydeg (y : t) : (y : Q) ∈ 𝒬 (deg y) := (htHom y y.2).choose_spec
  choose k hk using fun y : t => hlift (deg y) ⟨y, hydeg y⟩
  refine ⟨t, fun y => (k y : K), ?_, ?_⟩
  · intro y
    exact ⟨deg y, (k y).2⟩
  · intro x hx
    have hxy : J.mkQ x ∈ Submodule.span S (Set.range fun y : t => (y : Q)) := by
      rw [show Set.range (fun y : t => (y : Q)) = (t : Set Q) by ext; simp, htSpan]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hxy
    let w : K := ∑ y, c y • (k y : K)
    have hw : w ∈ Submodule.span S (Set.range fun y : t => (k y : K)) := by
      apply Submodule.sum_mem
      intro y hy
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self y))
    have hqw : J.mkQ w = J.mkQ x := by
      rw [map_sum]
      simp_rw [map_smul]
      rw [Finset.sum_congr rfl (fun y _ => congrArg (c y • ·) (hk y))]
      exact hc
    have hz : x - w ∈ I • (⊤ : Submodule R K) := by
      have hzJ : x - w ∈ J := by
        rw [← Submodule.ker_mkQ J, LinearMap.mem_ker]
        rw [map_sub, hqw, sub_self]
      simpa only [J, Submodule.mem_algebraIdealSMulTop_iff] using hzJ
    exact Submodule.mem_sup.mpr ⟨w, hw, x - w, hz, by abel⟩

/-- If finitely many homogeneous elements generate a graded module modulo the maximal ideal
globally, then they generate every homogeneous piece modulo the maximal ideal of that piece. -/
theorem Submodule.degreewise_mod_of_global_mod
    {ιA' ι' : Type*} [DecidableEq ιA'] [DecidableEq ι']
    [AddMonoid ιA'] [AddAction ιA' ι'] [IsLocalRing R]
    (𝒜' : ιA' → Submodule R S) [GradedRing 𝒜']
    (𝒦 : ι' → Submodule R K)
    [DirectSum.Decomposition 𝒦] [SetLike.GradedSMul 𝒜' 𝒦]
    {κ : Type*} [Finite κ] (k : κ → K)
    (hk : ∀ j, SetLike.IsHomogeneousElem 𝒦 (k j))
    (hglobal : (⊤ : Submodule R K) ≤
      (Submodule.span S (Set.range k)).restrictScalars R ⊔
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R K)) (i : ι') :
    (𝒦 i : Submodule R K) ≤
      (Submodule.span S (Set.range k)).restrictScalars R ⊔
        IsLocalRing.maximalIdeal R • (𝒦 i : Submodule R K) := by
  intro x hx
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp (hglobal (Submodule.mem_top))
  have hW : (Submodule.span S (Set.range k)).IsHomogeneous 𝒦 :=
    Submodule.isHomogeneous_span_of_isHomogeneousElem 𝒜' 𝒦 _ (by
      rintro _ ⟨j, rfl⟩
      exact hk j)
  have hw' : (DirectSum.decompose 𝒦 w i : K) ∈
      (Submodule.span S (Set.range k)).restrictScalars R := hW i hw
  have hz' : (DirectSum.decompose 𝒦 z i : K) ∈
      IsLocalRing.maximalIdeal R • (𝒦 i : Submodule R K) :=
    DirectSum.decompose_mem_ideal_smul_piece 𝒦 _ z hz i
  have hx' : (DirectSum.decompose 𝒦 x i : K) = x :=
    DirectSum.decompose_of_mem_same 𝒦 hx
  have hsum : x = (DirectSum.decompose 𝒦 w i : K) +
      (DirectSum.decompose 𝒦 z i : K) := by
    calc
      x = (DirectSum.decompose 𝒦 x i : K) := hx'.symm
      _ = (DirectSum.decompose 𝒦 (w + z) i : K) := by rw [hwz]
      _ = _ := congrArg Subtype.val
        (DFunLike.congr_fun (DirectSum.decompose_add 𝒦 w z) i)
  rw [hsum]
  exact Submodule.mem_sup.mpr ⟨_, hw', _, hz', rfl⟩

variable {F : Type uF} {M : Type uM} [AddCommGroup F] [Module R F] [Module S F]
  [IsScalarTower R S F] [AddCommGroup M] [Module S M]

/-- A finite-presentation criterion implementing the relation-module step of the graded local
argument.  It suffices to exhibit finitely many relations whose span contains every finite graded
piece modulo the maximal ideal. -/
theorem Module.finitePresentation_of_degreewise_relations_mod_maximalIdeal
    [IsLocalRing R] [Module.FinitePresentation S F]
    {ι κ : Type*} [DecidableEq ι] [Finite κ] (f : F →ₗ[S] M)
    (hf : Function.Surjective f) (𝒦 : ι → Submodule R f.ker)
    [DirectSum.Decomposition 𝒦] (hfinite : ∀ i, Module.Finite R (𝒦 i))
    (k : κ → f.ker)
    (hmod : ∀ i, (𝒦 i : Submodule R f.ker) ≤
      (Submodule.span S (Set.range k)).restrictScalars R ⊔
        IsLocalRing.maximalIdeal R • (𝒦 i : Submodule R f.ker)) :
    Module.FinitePresentation S M := by
  have hspan : Submodule.span S (Set.range k) = ⊤ :=
    Submodule.eq_top_of_degreewise_le_sup_maximalIdeal_smul 𝒦 _ hfinite hmod
  have htop : (⊤ : Submodule S f.ker).FG := by
    rw [← hspan]
    exact Submodule.fg_span (Set.finite_range k)
  have hfin : Module.Finite S f.ker := Module.finite_def.mpr htop
  exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp hfin)

/-- A global homogeneous-relation version of the graded local finite-presentation criterion.
It suffices that finitely many homogeneous relations generate the entire relation module modulo
the maximal ideal; degreewise Nakayama then makes them genuine generators. -/
theorem Module.finitePresentation_of_homogeneous_relations_mod_maximalIdeal
    [IsLocalRing R] [Module.FinitePresentation S F]
    {ιA' ι' κ : Type*} [DecidableEq ιA'] [DecidableEq ι']
    [AddMonoid ιA'] [AddAction ιA' ι'] [Finite κ]
    (𝒜' : ιA' → Submodule R S) [GradedRing 𝒜'] (f : F →ₗ[S] M)
    (hf : Function.Surjective f) (𝒦 : ι' → Submodule R f.ker)
    [DirectSum.Decomposition 𝒦] [SetLike.GradedSMul 𝒜' 𝒦]
    (hfinite : ∀ i, Module.Finite R (𝒦 i))
    (k : κ → f.ker) (hk : ∀ j, SetLike.IsHomogeneousElem 𝒦 (k j))
    (hmod : (⊤ : Submodule R f.ker) ≤
      (Submodule.span S (Set.range k)).restrictScalars R ⊔
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R f.ker)) :
    Module.FinitePresentation S M := by
  apply Module.finitePresentation_of_degreewise_relations_mod_maximalIdeal
    f hf 𝒦 hfinite k
  exact fun i => Submodule.degreewise_mod_of_global_mod 𝒜' 𝒦 k hk hmod i

/-- Finite presentation from a finite graded relation module on the closed fibre.  This packages
the homogeneous-generator choice in the quotient, homogeneous lifting, and degreewise Nakayama. -/
theorem Module.finitePresentation_of_finite_graded_relation_quotient
    [IsLocalRing R] [Module.FinitePresentation S F]
    {ιA' ι' : Type*} [DecidableEq ιA'] [DecidableEq ι']
    [AddMonoid ιA'] [AddAction ιA' ι']
    (𝒜' : ιA' → Submodule R S) [GradedRing 𝒜'] (f : F →ₗ[S] M)
    (hf : Function.Surjective f) (𝒦 : ι' → Submodule R f.ker)
    [DirectSum.Decomposition 𝒦] [SetLike.GradedSMul 𝒜' 𝒦]
    (hfinite : ∀ i, Module.Finite R (𝒦 i))
    (𝒬 : ι' → Submodule R
      (f.ker ⧸ Submodule.algebraIdealSMulTop (S := S) (K := f.ker)
        (IsLocalRing.maximalIdeal R)))
    [DirectSum.Decomposition 𝒬] [SetLike.GradedSMul 𝒜' 𝒬]
    [Module.Finite S
      (f.ker ⧸ Submodule.algebraIdealSMulTop (S := S) (K := f.ker)
        (IsLocalRing.maximalIdeal R))]
    (hlift : ∀ d (y : 𝒬 d), ∃ x : 𝒦 d,
      (Submodule.algebraIdealSMulTop (S := S) (K := f.ker)
        (IsLocalRing.maximalIdeal R)).mkQ x.1 = y.1) :
    Module.FinitePresentation S M := by
  obtain ⟨t, k, hk, hmod⟩ :=
    Module.Finite.exists_finset_isHomogeneousElem_global_mod_ideal
      𝒜' 𝒦 (IsLocalRing.maximalIdeal R) 𝒬 hlift
  exact Module.finitePresentation_of_homogeneous_relations_mod_maximalIdeal
    𝒜' f hf 𝒦 hfinite k hk hmod

/-- A graded local finite-presentation criterion.  A flat quotient of a finitely presented
graded source is finitely presented when its relation pieces are finite over the local base and
the closed-fibre scalar ring is noetherian. -/
theorem Module.finitePresentation_of_flat_of_noetherian_closedFiber
    [Module R M] [IsScalarTower R S M] [IsLocalRing R]
    [Module.FinitePresentation S F] [Module.Flat R M]
    [IsNoetherianRing
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))]
    {ιA' ι' : Type*} [DecidableEq ιA'] [DecidableEq ι']
    [AddMonoid ιA'] [AddAction ιA' ι']
    (𝒜' : ιA' → Submodule R S) [GradedRing 𝒜'] (f : F →ₗ[S] M)
    (hf : Function.Surjective f) (𝒦 : ι' → Submodule R f.ker)
    [DirectSum.Decomposition 𝒦] [SetLike.GradedSMul 𝒜' 𝒦]
    (hfinite : ∀ i, Module.Finite R (𝒦 i)) :
    Module.FinitePresentation S M := by
  let I := IsLocalRing.maximalIdeal R
  let J := Submodule.algebraIdealSMulTop (S := S) (K := f.ker) I
  have hJ : J.IsHomogeneous 𝒦 :=
    Submodule.isHomogeneous_algebraIdealSMulTop 𝒦 I
  let 𝒬 : ι' → Submodule R (f.ker ⧸ J) :=
    Submodule.QuotientGrading.piece 𝒦 J
  letI : DirectSum.Decomposition 𝒬 :=
    Submodule.QuotientGrading.decomposition 𝒦 J hJ
  letI : SetLike.GradedSMul 𝒜' 𝒬 :=
    Submodule.QuotientGrading.gradedSMul 𝒜' 𝒦 J
  letI : Module.Finite S (f.ker ⧸ J) :=
    Module.Finite.relationQuotient_of_flat f hf I
  apply Module.finitePresentation_of_finite_graded_relation_quotient
    𝒜' f hf 𝒦 hfinite 𝒬
  intro d y
  exact Submodule.QuotientGrading.exists_lift 𝒦 J d y

end Tag053C
