module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Descent of finite-typeness along a smooth faithfully flat ring map

If `A → B` is smooth and faithfully flat and `R → B` is of finite type, then `R → A` is of
finite type. This is the smooth case of Stacks Project tag
[0367](https://stacks.math.columbia.edu/tag/0367); Mathlib has neither it nor the fppf case.

It is the missing input for source-locality of "locally of finite type" along smooth
surjections — the `isLocalOnSourceAlong` field of
`AlgebraicGeometry.isSmoothLocal_locallyOfFiniteType` in
`StacksAndModuli/Section4.3-Properties/part4.3.1-properties-of-morphisms.lean` — which is in turn
one of the hypotheses under which Definition 4.3.2 of *Stacks and Moduli* extends a property
of morphisms of schemes to morphisms of algebraic stacks.

The argument descends a finite generating set through a finitely generated subalgebra
`A₀ ⊆ A` over which `B` is already defined (`Algebra.Smooth.exists_subalgebra_fg`), and uses
faithful flatness twice: to see that `Spec A → Spec A₀` is surjective on primes, and to
descend surjectivity of `A₀ ⊗ B₀ → B` to surjectivity of `A₀ → A`.

## Main results

* `Algebra.FiniteType.of_smooth_of_faithfullyFlat`: the algebra form.
* `RingHom.FiniteType.of_comp_of_smooth_of_faithfullyFlat`: the ring-homomorphism form.
-/

@[expose] public section

universe u

open TensorProduct

/-- If a prime `q` of `S` contracts into the image of `Spec T → Spec R`, then `q` is in the
image of `Spec (S ⊗[R] T) → Spec S`. -/
lemma mem_range_comap_tensorProduct {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (q : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) q ∈
      Set.range (PrimeSpectrum.comap (algebraMap R T))) :
    q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T))) := by
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap] at h ⊢
  set p : Ideal R := q.asIdeal.comap (algebraMap R S) with hp
  letI : Algebra p.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p q.asIdeal (algebraMap R S) rfl).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (Ideal.ResidueField.map_algebraMap p q.asIdeal (algebraMap R S) rfl r).symm
  haveI : IsLocalHom (algebraMap p.ResidueField q.asIdeal.ResidueField) := by
    refine ⟨fun a ha ↦ ?_⟩
    rw [isUnit_iff_ne_zero]
    rintro rfl
    simp at ha
  haveI : Module.FaithfullyFlat p.ResidueField q.asIdeal.ResidueField :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h2 : Nontrivial (q.asIdeal.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] T)) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField
      q.asIdeal.ResidueField).mpr h
  have e1 : (q.asIdeal.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] T))
      ≃ₗ[q.asIdeal.ResidueField] q.asIdeal.ResidueField ⊗[R] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R p.ResidueField q.asIdeal.ResidueField
      q.asIdeal.ResidueField T
  have e2 : (q.asIdeal.ResidueField ⊗[S] (S ⊗[R] T)) ≃ₗ[q.asIdeal.ResidueField]
      q.asIdeal.ResidueField ⊗[R] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S q.asIdeal.ResidueField
      q.asIdeal.ResidueField T
  exact (e2.toEquiv.nontrivial_congr).mpr ((e1.toEquiv.nontrivial_congr).mp h2)

lemma surjective_algebraMap_of_baseChange
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T]
    (B₀ : Type u) [CommRing B₀] [Algebra R B₀]
    [Module.FaithfullyFlat S (S ⊗[R] B₀)]
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R B₀))) :
    Function.Surjective (algebraMap S T) := by
  set e1 : (S ⊗[R] B₀) ⊗[S] S ≃ₗ[S] (S ⊗[R] B₀) := TensorProduct.rid S (S ⊗[R] B₀) with he1
  set e2 : (S ⊗[R] B₀) ⊗[S] T ≃ₗ[S] T ⊗[S] (S ⊗[R] B₀) := TensorProduct.comm S _ T with he2
  set e3 : T ⊗[S] (S ⊗[R] B₀) ≃ₗ[T] T ⊗[R] B₀ :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T B₀ with he3
  have key : ∀ x : S ⊗[R] B₀,
      e3 (e2 (LinearMap.lTensor (S ⊗[R] B₀) (Algebra.linearMap S T) (e1.symm x))) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R B₀) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [he1, he2, he3, Algebra.smul_def]
    | add y z hy hz => simp only [map_add, hy, hz]
  have h1 : Function.Surjective (LinearMap.lTensor (S ⊗[R] B₀) (Algebra.linearMap S T)) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (e3 (e2 y))
    exact ⟨e1.symm x, e2.injective (e3.injective (by rw [key, hx]))⟩
  simpa [Algebra.coe_linearMap] using
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective S (S ⊗[R] B₀)
      (Algebra.linearMap S T)).mp h1


section Core

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Core spreading-out argument. -/
theorem core (A₀ : Subalgebra R A) (hA₀ : A₀.FG) (B₀ : Type u) [CommRing B₀] [Algebra ↥A₀ B₀]
    [Algebra.Smooth ↥A₀ B₀] [Module.FaithfullyFlat A (A ⊗[↥A₀] B₀)]
    [Algebra.FiniteType R (A ⊗[↥A₀] B₀)] :
    Algebra.FiniteType R A := by
  classical
  -- the finite set of `A`-coefficients of a generating set of `A ⊗[A₀] B₀` over `R`
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R (A ⊗[↥A₀] B₀)).FG := Algebra.FiniteType.out
  choose k m n hmn using fun x : A ⊗[↥A₀] B₀ ↦ TensorProduct.exists_sum_tmul_eq x
  -- the ideal cutting out the complement of the image of `Spec B₀ → Spec A₀`
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap ↥A₀ B₀))) := by
    simpa using PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := ↥A₀) (S := B₀) _ isOpen_univ
  obtain ⟨sI, hsI⟩ := (PrimeSpectrum.isOpen_iff _).mp hopen
  have hzero : (Set.range (PrimeSpectrum.comap (algebraMap ↥A₀ B₀)))ᶜ =
      PrimeSpectrum.zeroLocus ((Ideal.span sI : Ideal ↥A₀) : Set ↥A₀) := by
    rw [hsI, PrimeSpectrum.zeroLocus_span]
  -- `I` generates the unit ideal in `A`
  have hIA : Ideal.span (algebraMap ↥A₀ A '' sI) = ⊤ := by
    rw [← Ideal.map_span]
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI : 𝔪.IsPrime := h𝔪.isPrime
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := A) (B := A ⊗[↥A₀] B₀) ⟨𝔪, inferInstance⟩
    have hcomp : (algebraMap A (A ⊗[↥A₀] B₀)).comp (algebraMap ↥A₀ A) =
        (Algebra.TensorProduct.includeRight (R := ↥A₀) (A := A) (B := B₀)).toRingHom.comp
          (algebraMap ↥A₀ B₀) := by
      ext a
      simp
    have hmem : PrimeSpectrum.comap (algebraMap ↥A₀ A) (⟨𝔪, inferInstance⟩ : PrimeSpectrum A) ∈
        Set.range (PrimeSpectrum.comap (algebraMap ↥A₀ B₀)) := by
      refine ⟨PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight (R := ↥A₀) (A := A) (B := B₀)).toRingHom Q, ?_⟩
      rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hcomp]
    have hnotin : PrimeSpectrum.comap (algebraMap ↥A₀ A) (⟨𝔪, inferInstance⟩ : PrimeSpectrum A) ∉
        PrimeSpectrum.zeroLocus ((Ideal.span sI : Ideal ↥A₀) : Set ↥A₀) := by
      rw [← hzero]
      simpa using hmem
    rw [PrimeSpectrum.mem_zeroLocus] at hnotin
    exact hnotin (Ideal.map_le_iff_le_comap.mp hle)
  -- the resulting partition of unity
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp
    (show (1 : A) ∈ Ideal.span (algebraMap ↥A₀ A '' sI) from hIA ▸ Submodule.mem_top)
  choose b hb hb' using fun i : Fin N ↦ (g i).2
  -- the finite set of coefficients we adjoin to `A₀`
  set S : Set A := (⋃ x ∈ (s : Set (A ⊗[↥A₀] B₀)), Set.range (m x)) ∪ Set.range f with hS
  have hSfin : S.Finite :=
    (s.finite_toSet.biUnion fun x _ ↦ Set.finite_range (m x)).union (Set.finite_range f)
  set A₁ : Subalgebra ↥A₀ A := Algebra.adjoin ↥A₀ S with hA₁
  have hmmem : ∀ x ∈ s, ∀ j, m x j ∈ A₁ := fun x hx j ↦
    Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_biUnion hx ⟨j, rfl⟩))
  have hfmem : ∀ i, f i ∈ A₁ := fun i ↦
    Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
  -- `A₁` is of finite type over `R`
  haveI : Algebra.FiniteType R ↥A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  haveI : Algebra.FiniteType ↥A₀ ↥A₁ :=
    (Subalgebra.fg_iff_finiteType A₁).mp (Subalgebra.fg_def.mpr ⟨S, hSfin, rfl⟩)
  haveI : Algebra.FiniteType R ↥A₁ := Algebra.FiniteType.trans ‹_› ‹_›
  -- `A₁ → A₁ ⊗[A₀] B₀` is faithfully flat
  haveI : Module.Flat ↥A₁ (↥A₁ ⊗[↥A₀] B₀) := Module.Flat.baseChange ↥A₀ ↥A₁ B₀
  haveI : Module.FaithfullyFlat ↥A₁ (↥A₁ ⊗[↥A₀] B₀) := by
    refine Module.FaithfullyFlat.of_comap_surjective fun q₁ ↦ mem_range_comap_tensorProduct q₁ ?_
    by_contra hcon
    have hsub : ((Ideal.span sI : Ideal ↥A₀) : Set ↥A₀) ⊆
        (PrimeSpectrum.comap (algebraMap ↥A₀ ↥A₁) q₁).asIdeal := by
      rw [← PrimeSpectrum.mem_zeroLocus, ← hzero]
      exact hcon
    refine q₁.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
    have hy : (∑ i, (⟨f i, hfmem i⟩ : ↥A₁) * algebraMap ↥A₀ ↥A₁ (b i)) = 1 := by
      apply Subtype.val_injective
      push_cast
      simpa [← hb', Algebra.smul_def, mul_comm] using hfg
    rw [← hy]
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ ?_
    exact hsub (Ideal.subset_span (hb i))
  -- the base change of `B₀` to `A₁` surjects onto `A ⊗[A₀] B₀`
  have hφ : Function.Surjective (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom ↥A₀ ↥A₁ A) (AlgHom.id ↥A₀ B₀)) := by
    have hle : Algebra.adjoin R (s : Set (A ⊗[↥A₀] B₀)) ≤
        AlgHom.range ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥A₀ ↥A₁ A)
          (AlgHom.id ↥A₀ B₀)).restrictScalars R) := by
      rw [Algebra.adjoin_le_iff]
      rintro x hx
      refine ⟨∑ j, (⟨m x j, hmmem x hx j⟩ : ↥A₁) ⊗ₜ n x j, ?_⟩
      rw [map_sum]
      conv_rhs => rw [hmn x]
      exact Finset.sum_congr rfl fun j _ ↦ rfl
    have h2 : Function.Surjective ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom ↥A₀ ↥A₁ A) (AlgHom.id ↥A₀ B₀)).restrictScalars R) := by
      rw [← AlgHom.range_eq_top]
      rw [hs] at hle
      exact top_le_iff.mp hle
    exact h2
  exact Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom R ↥A₁ A)
    (surjective_algebraMap_of_baseChange B₀ hφ)

end Core


/-- **Stacks 0367** in the smooth case: if `A → B` is smooth and faithfully flat and `R → B`
is of finite type, then `R → A` is of finite type. -/
theorem Algebra.FiniteType.of_smooth_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.Smooth A B] [Module.FaithfullyFlat A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A := by
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg R A B
  haveI : Module.FaithfullyFlat A (A ⊗[↥A₀] B₀) :=
    Module.FaithfullyFlat.of_linearEquiv A B e.symm.toLinearEquiv
  haveI : Algebra.FiniteType R (A ⊗[↥A₀] B₀) :=
    Algebra.FiniteType.equiv (R := R) (A := B) (B := A ⊗[↥A₀] B₀) inferInstance
      (e.restrictScalars R)
  exact core A₀ hA₀ B₀

/-- Ring-homomorphism form of `Algebra.FiniteType.of_smooth_of_faithfullyFlat`. -/
theorem RingHom.FiniteType.of_comp_of_smooth_of_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B) (hcomp : (ψ.comp φ).FiniteType)
    (hsm : ψ.Smooth) (hff : ψ.FaithfullyFlat) : φ.FiniteType := by
  algebraize [φ, ψ, ψ.comp φ]
  exact Algebra.FiniteType.of_smooth_of_faithfullyFlat (B := B)
