module

public import StacksProject.Algebra.CriteriaForFlatness.«lemma-local-criterion-flatness»
public import StacksAndModuli.API.FlatColimit
public import StacksAndModuli.API.FlatLocal
public import Mathlib.RingTheory.Ideal.Finsupp
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Relative flat cokernels from residue-fibre injectivity

For a local homomorphism of Noetherian local rings, consider an exact presentation
`K → F → M → 0` whose middle term is flat over the coefficient ring.  If the first map
remains injective after tensoring with the coefficient residue field, then `M` is flat over
the coefficient ring.

This is the one-step induction used in Stacks Project tag 00MI.  The proof turns fibre
injectivity into injectivity of `maximalIdeal R ⊗ M → M` by the tensor diagram lemma, then
applies the already formalized Noetherian local flatness criterion (tag 00MK).

The second theorem adds the injectivity conclusion of the Noetherian form of Stacks Project
tag 00ME.  After the cokernel is known to be flat, its kernel inclusion has flat quotient;
closed-fibre injectivity and Nakayama then kill the kernel of the original map.
-/

@[expose] public section

open Function TensorProduct

universe u v w

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Module.Flat

/-- In an exact presentation over a local Noetherian algebra, residue-fibre injectivity of
the relation map implies coefficient-ring flatness of the presented module.

This is the length-one case and induction step of Stacks Project tag 00MI. -/
theorem of_exact_of_surjective_of_lTensor_residueField_injective
    {R : Type u} {S : Type v} {K F M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R F]
    (i : K →ₗ[S] F) (p : F →ₗ[S] M)
    (hexact : Function.Exact i p) (hp : Function.Surjective p)
    (hfibre : Function.Injective
      ((i.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R M := by
  apply Module.Flat.of_maximalIdeal_rTensor_injective_of_finite S
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := i.restrictScalars R) (f₂ := p.restrictScalars R)
    (g₁ := (IsLocalRing.maximalIdeal R).subtype)
    (g₂ := Submodule.mkQ (IsLocalRing.maximalIdeal R))
  · exact hexact
  · exact hp
  · exact LinearMap.exact_subtype_mkQ _
  · exact Submodule.mkQ_surjective _
  · exact (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hfibre
  · exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- For a local homomorphism of Noetherian local rings, a map from a finite module into an
`R`-flat finite module which is injective on the closed fibre is injective, and its cokernel
is `R`-flat.

This is the Noetherian form of Stacks Project tag 00ME. -/
theorem injective_and_flat_coker_of_lTensor_residueField_injective
    {R : Type u} {S : Type v} {N F : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S N] [Module.Finite S F] [Module.Flat R F]
    (u : N →ₗ[S] F)
    (hfibre : Function.Injective
      ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (F ⧸ LinearMap.range u) := by
  let p : F →ₗ[S] F ⧸ LinearMap.range u := (LinearMap.range u).mkQ
  letI : Module.Finite S (F ⧸ LinearMap.range u) :=
    Module.Finite.of_surjective p (Submodule.mkQ_surjective _)
  have hflatC : Module.Flat R (F ⧸ LinearMap.range u) :=
    Module.Flat.of_exact_of_surjective_of_lTensor_residueField_injective
      u p (LinearMap.exact_map_mkQ_range u) (Submodule.mkQ_surjective _) hfibre
  letI : Module.Flat R (F ⧸ LinearMap.range u) := hflatC
  have hflatRange : Module.Flat R (LinearMap.range u) := by
    apply Module.Flat.of_shortExact_general
      ((LinearMap.range u).subtype.restrictScalars R) (p.restrictScalars R)
    · exact Subtype.val_injective
    · exact LinearMap.exact_subtype_mkQ _
    · intro z
      exact Submodule.mkQ_surjective (LinearMap.range u) z
  letI : Module.Flat R (LinearMap.range u) := hflatRange
  let v : N →ₗ[S] LinearMap.range u := u.rangeRestrict
  have hvSurj : Function.Surjective v :=
    LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict u)
  have hvFibre : Function.Injective
      ((v.restrictScalars R).lTensor (IsLocalRing.ResidueField R)) := by
    have huv :
        ((LinearMap.range u).subtype.restrictScalars R).comp
          (v.restrictScalars R) = u.restrictScalars R := by
      ext z
      rfl
    intro x y hxy
    apply hfibre
    have h := congrArg
      ((LinearMap.range u).subtype.restrictScalars R |>.lTensor
        (IsLocalRing.ResidueField R)) hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, huv] using h
  have hkerTensorInj : Function.Injective
      (((LinearMap.ker v).subtype.restrictScalars R).lTensor
        (IsLocalRing.ResidueField R)) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (v.restrictScalars R) hvSurj
      ((LinearMap.ker v).subtype.restrictScalars R) Subtype.val_injective
      (LinearMap.exact_subtype_ker_map v) (IsLocalRing.ResidueField R)
  have hkerTensor : Subsingleton
      ((IsLocalRing.ResidueField R) ⊗[R] LinearMap.ker v) := by
    constructor
    intro x y
    apply hkerTensorInj
    apply hvFibre
    have hzero :
        (v.restrictScalars R).comp
          ((LinearMap.ker v).subtype.restrictScalars R) = 0 := by
      ext z
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      exact_mod_cast z.property
    simp only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  let K := LinearMap.ker v
  let m := IsLocalRing.maximalIdeal R
  have hbase : Subsingleton ((R ⧸ m) ⊗[R] K) := by
    simpa only [K, m, IsLocalRing.ResidueField] using hkerTensor
  letI : Subsingleton ((R ⧸ m) ⊗[R] K) := hbase
  have hquot : Subsingleton (K ⧸ m • (⊤ : Submodule R K)) :=
    (TensorProduct.quotTensorEquivQuotSMul K m).symm.injective.subsingleton
  have htopR : (⊤ : Submodule R K) = m • (⊤ : Submodule R K) := by
    apply le_antisymm
    · intro x _
      rw [← Submodule.Quotient.mk_eq_zero]
      exact Subsingleton.elim _ 0
    · exact le_top
  let mS := m.map (algebraMap R S)
  have htopS : (⊤ : Submodule S K) ≤ mS • (⊤ : Submodule S K) := by
    intro x _
    have hxR : x ∈ m • (⊤ : Submodule R K) := by
      rw [← htopR]
      exact Submodule.mem_top
    refine Submodule.smul_induction_on hxR ?_ ?_
    · intro r hr y _
      have hrS : algebraMap R S r ∈ mS := Ideal.mem_map_of_mem _ hr
      have hyS : (y : K) ∈ (⊤ : Submodule S K) := Submodule.mem_top
      have hmem := Submodule.smul_mem_smul hrS hyS
      simpa only [IsScalarTower.algebraMap_smul S r (y : K)] using hmem
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  have htopBot : (⊤ : Submodule S K) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot mS ⊤ Module.Finite.fg_top htopS
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
        (IsLocalRing.maximalIdeal_le_jacobson ⊥))
  have hKsub : Subsingleton K := by
    constructor
    intro x y
    have hxy : x - y ∈ (⊤ : Submodule S K) := Submodule.mem_top
    rw [htopBot] at hxy
    exact sub_eq_zero.mp (by simpa using hxy)
  have hvInj : Function.Injective v := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    let z : K := ⟨x, hx⟩
    exact congrArg Subtype.val (Subsingleton.elim z 0)
  refine ⟨?_, hflatC⟩
  intro x y hxy
  apply hvInj
  apply Subtype.ext
  exact hxy

/-- A surjection from a finite free `S`-module to an `R`-flat finite `S`-module is an
isomorphism, hence has free target, when it is injective on the closed `R`-fibre.

This is the map-level lifting step in Stacks Project tag 00MH. -/
theorem free_of_surjective_of_lTensor_residueField_injective
    {R S M ι : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M] [Finite ι]
    (u : (ι →₀ S) →ₗ[S] M) (hu : Function.Surjective u)
    (hfibre : Function.Injective
      ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Module.Free S M := by
  have hinj :=
    (Module.Flat.injective_and_flat_coker_of_lTensor_residueField_injective
      u hfibre).1
  exact Module.Free.of_equiv (LinearEquiv.ofBijective u ⟨hinj, hu⟩)

/-- In the preceding finite-free lifting situation, a nonempty free source also detects
flatness of `S` over `R`: `S` is a retract of the source and the source is isomorphic to the
given `R`-flat target.

This is the coefficient-ring flatness conclusion used in Stacks Project tag 00MH. -/
theorem source_flat_of_surjective_of_lTensor_residueField_injective
    {R S M ι : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M] [Finite ι] [Nonempty ι]
    (u : (ι →₀ S) →ₗ[S] M) (hu : Function.Surjective u)
    (hfibre : Function.Injective
      ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R S := by
  have hinj :=
    (Module.Flat.injective_and_flat_coker_of_lTensor_residueField_injective
      u hfibre).1
  let e : (ι →₀ S) ≃ₗ[S] M := LinearEquiv.ofBijective u ⟨hinj, hu⟩
  letI : Module.Flat R (ι →₀ S) :=
    Module.Flat.of_linearEquiv (e.restrictScalars R)
  let i : ι := Classical.arbitrary ι
  apply Module.Flat.of_retract
    ((Finsupp.lsingle i : S →ₗ[S] (ι →₀ S)).restrictScalars R)
    ((Finsupp.lapply i : (ι →₀ S) →ₗ[S] S).restrictScalars R)
  ext x
  simp

/-- A nonzero finite module over a local Noetherian algebra which is flat over the
coefficient ring and free on the closed coefficient fibre is free over the algebra;
the algebra is flat over the coefficient ring as well.

This is the full lifting statement of Stacks Project tag 00MH. -/
theorem free_and_source_flat_of_free_closedFiber
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M]
    [Module.Free
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) •
        (⊤ : Submodule S M))]
    [Nontrivial M] :
    Module.Free S M ∧ Module.Flat R S := by
  let mR := IsLocalRing.maximalIdeal R
  let mS := mR.map (algebraMap R S)
  have hmSne : mS ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  letI : Nontrivial (S ⧸ mS) :=
    Ideal.Quotient.nontrivial_iff.mpr hmSne
  let Q := M ⧸ mS • (⊤ : Submodule S M)
  let I := Module.Free.ChooseBasisIndex (S ⧸ mS) Q
  let b := Module.Free.chooseBasis (S ⧸ mS) Q
  have hQfinite : Module.Finite (S ⧸ mS) Q := by
    letI : Module.Finite S Q :=
      Module.Finite.of_surjective
        (Submodule.mkQ (mS • (⊤ : Submodule S M)))
        (Submodule.mkQ_surjective _)
    exact Module.Finite.of_restrictScalars_finite S (S ⧸ mS) Q
  haveI : Finite I := Module.Finite.finite_basis b
  let b' : Q ≃ₗ[S] I →₀ S ⧸ mS := b.repr.restrictScalars S
  let f : (I →₀ S) →ₗ[S] Q :=
    b'.symm.toLinearMap.comp
      (Finsupp.mapRange.linearMap (Submodule.mkQ mS))
  let q : M →ₗ[S] Q := Submodule.mkQ (mS • (⊤ : Submodule S M))
  rcases Module.projective_lifting_property q f (Submodule.mkQ_surjective _) with
    ⟨g, hg⟩
  have hfsurj : Function.Surjective f := by
    simpa [f] using!
      Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective mS)
  have hkerf : LinearMap.ker f = mS • (⊤ : Submodule S (I →₀ S)) := by
    simp only [LinearEquiv.ker_comp, f]
    rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, ← mS.mul_top,
      ← smul_eq_mul, Finsupp.submodule_smul]
    simp
  have hmSjac : mS ≤ (⊥ : Ideal S).jacobson :=
    (IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hgsurj : Function.Surjective g := by
    apply g.surjective_of_surjective_comp_mkQ mS hmSjac
    simpa [q, hg] using hfsurj
  have hgfibre : Function.Injective
      ((g.restrictScalars R).lTensor (IsLocalRing.ResidueField R)) := by
    change Function.Injective ((g.restrictScalars R).lTensor (R ⧸ mR))
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective R (I →₀ S)
      (R ⧸ mR) Ideal.Quotient.mk_surjective x
    have huyR : g y ∈ mR • (⊤ : Submodule R M) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply (TensorProduct.quotTensorEquivQuotSMul M mR).symm.injective
      simpa [IsLocalRing.ResidueField] using hx
    have huyS : g y ∈ mS • (⊤ : Submodule S M) := by
      have hsmul :
          (mS • (⊤ : Submodule S M)).restrictScalars R =
            mR • (⊤ : Submodule R M) := by
        simpa [mR, mS] using
          (Ideal.smul_restrictScalars mR (⊤ : Submodule S M))
      change g y ∈ (mS • (⊤ : Submodule S M)).restrictScalars R
      rw [hsmul]
      exact huyR
    have hfy : f y = 0 := by
      rw [← hg]
      exact (Submodule.Quotient.mk_eq_zero _).mpr huyS
    have hyS : y ∈ mS • (⊤ : Submodule S (I →₀ S)) := by
      rw [← hkerf]
      exact hfy
    have hyR : y ∈ mR • (⊤ : Submodule R (I →₀ S)) := by
      have hsmul :
          (mS • (⊤ : Submodule S (I →₀ S))).restrictScalars R =
            mR • (⊤ : Submodule R (I →₀ S)) := by
        simpa [mR, mS] using
          (Ideal.smul_restrictScalars mR (⊤ : Submodule S (I →₀ S)))
      rw [← hsmul]
      exact hyS
    change (1 ⊗ₜ[R] y : (R ⧸ mR) ⊗[R] (I →₀ S)) = 0
    apply (TensorProduct.quotTensorEquivQuotSMul (I →₀ S) mR).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
      map_zero, Submodule.Quotient.mk_eq_zero]
    exact hyR
  have hInonempty : Nonempty I := by
    by_contra hI
    haveI : IsEmpty I := not_nonempty_iff.mp hI
    have hz : ∀ z : I →₀ S, z = 0 := by
      intro z
      ext i
      exact isEmptyElim i
    have hMsub : Subsingleton M := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := hgsurj x
      obtain ⟨y', rfl⟩ := hgsurj y
      rw [hz x', hz y']
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M
    exact hxy (hMsub.elim x y)
  letI : Nonempty I := hInonempty
  exact ⟨
    Module.Flat.free_of_surjective_of_lTensor_residueField_injective
      g hgsurj hgfibre,
    Module.Flat.source_flat_of_surjective_of_lTensor_residueField_injective
      g hgsurj hgfibre⟩

end Module.Flat

end
