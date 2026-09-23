module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalRing.Module
public import StacksAndModuli.API.KernelBaseChange

/-!
# Open loci defined by maps of finite projective modules

Stacks Project tag **00O0**, label `algebra-lemma-cokernel-flat`, in `algebra.tex`,
§`05GD` (`section-loci-maps`, Open loci defined by module maps).

> Let `φ : P₁ → P₂` be a map of finite projective modules. Then
> (1) the set `U` of primes `p` with `φ ⊗ κ(p)` injective is open, and for `D(f) ⊆ U`:
>     (a) `P₁_f → P₂_f` is injective, (b) `coker(φ)_f` is finite projective over `R_f`;
> (2) the same for surjectivity, with `ker(φ)_f` finite projective;
> (3) the same for bijectivity.

Only clause (1) is needed by §A.6, so that is what is stated here.

Neighbouring tags in the same Stacks section, also absent from Mathlib and likely needed later:
**05GE** (`algebra-lemma-map-between-finite`, the surjectivity locus is open) and **05GF**
(`algebra-lemma-map-between-finitely-presented`, the isomorphism locus is open).

Mathlib has closely related machinery — `Module.freeLocus`, `Module.rankAtStalk` and
`Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean` — but not this statement: those describe the
locus where a *module* is free, not the locus where a *map* has constant rank.

**Proof route (Stacks Project).** Openness reduces, via `00NX` (the eight-way characterisation
of finite projective modules, which Mathlib essentially has through
`Module.Flat.projective_of_finitePresentation` and `Module.freeLocus`), to the free case, where
injectivity of `φ ⊗ κ(p)` says some maximal minor of a matrix for `φ` is nonzero at `p` — an
open condition. On such a `D(f)` the map splits, so the cokernel is a direct summand of `P₂_f`
and hence finite projective. This is a moderate, self-contained argument: `05GE` is shallow
(Nakayama, `algebra-lemma-NAK` (3)), `05GF` is about 30 lines, and `00O0` reduces to the free
case via `00NX`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The locus of primes at which the fibre of `f` is injective. Clause (1) of Stacks 00O0
asserts that this set is open. -/
def tensorInjectiveLocus (f : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Injective (LinearMap.lTensor p.residueField f)}

@[simp]
theorem mem_tensorInjectiveLocus {f : M →ₗ[R] N} {p : PrimeSpectrum R} :
    p ∈ f.tensorInjectiveLocus ↔ Function.Injective (LinearMap.lTensor p.residueField f) :=
  Iff.rfl

/-- Transfer of fibre injectivity through a base change: if `f ⊗_R L` is injective for an
`A`-algebra `L`, then `(f ⊗_R A) ⊗_A L` is injective. -/
theorem lTensor_baseChange_injective_of_lTensor_injective
    (f : M →ₗ[R] N) (A : Type*) [CommRing A] [Algebra R A]
    (L : Type*) [CommRing L] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    (hp : Function.Injective (LinearMap.lTensor L f)) :
    Function.Injective (LinearMap.lTensor L (f.baseChange A)) := by
  have key : ((f.baseChange A).baseChange L) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A L L N).symm.toLinearMap ∘ₗ
        ((f.baseChange L) ∘ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R A L L M).toLinearMap) := by
    ext x
    simp
  have : Function.Injective ((f.baseChange A).baseChange L) := by
    rw [key]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
    refine (TensorProduct.AlgebraTensorModule.cancelBaseChange R A L L N).symm.injective.comp
      (Function.Injective.comp ?_
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A L L M).injective)
    rw [LinearMap.baseChange_eq_ltensor]
    exact hp
  rwa [LinearMap.baseChange_eq_ltensor] at this

/-- Fibre injectivity ascends along a field extension of the fibre. -/
theorem lTensor_injective_of_lTensor_injective_of_field
    (f : M →ₗ[R] N) (K L : Type*) [Field K] [CommRing L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (hK : Function.Injective (LinearMap.lTensor K f)) :
    Function.Injective (LinearMap.lTensor L f) := by
  have key : ((f.baseChange K).baseChange L) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L N).symm.toLinearMap ∘ₗ
        ((f.baseChange L) ∘ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M).toLinearMap) := by
    ext x
    simp
  have hup : Function.Injective ((f.baseChange K).baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    refine Module.Flat.lTensor_preserves_injective_linearMap (M := L) _ ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact hK
  rw [key] at hup
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at hup
  intro x y hxy
  obtain ⟨x', rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M).surjective x
  obtain ⟨y', rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M).surjective y
  have h1 : (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L N).symm
      ((f.baseChange L)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M) x')) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L N).symm
      ((f.baseChange L)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L M) y')) := by
    rw [LinearMap.baseChange_eq_ltensor, hxy]
  exact congrArg _ (hup h1)

/-- A residue-fibre injection spreads out to a scaled left inverse: if `f ⊗ κ(p)` is
injective, then near `p` the map `f` admits `h` with `h ∘ f = a • id` for some `a ∉ p`. -/
theorem exists_scaled_leftInverse_of_lTensor_injective
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) (p : PrimeSpectrum R)
    (hp : Function.Injective (LinearMap.lTensor p.residueField f)) :
    ∃ (a : R) (_ : a ∉ p.asIdeal) (h : N →ₗ[R] M),
      h.comp f = a • (LinearMap.id : M →ₗ[R] M) := by
  classical
  set A := Localization.AtPrime p.asIdeal with hA
  -- the base change of `f` to the localization splits
  haveI : Module.Free A (A ⊗[R] N) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨σ, hσ⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (f.baseChange A)).mpr
    (lTensor_baseChange_injective_of_lTensor_injective f (Localization.AtPrime p.asIdeal)
      p.asIdeal.ResidueField hp)
  -- localized-module structures
  set mkM : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1 with hmkM
  set mkN : N →ₗ[R] A ⊗[R] N := TensorProduct.mk R A N 1 with hmkN
  haveI hlM : IsLocalizedModule p.asIdeal.primeCompl mkM :=
    (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl A mkM).mpr
      (TensorProduct.isBaseChange R M A)
  haveI hlN : IsLocalizedModule p.asIdeal.primeCompl mkN :=
    (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl A mkN).mpr
      (TensorProduct.isBaseChange R N A)
  haveI : Module.FinitePresentation R N :=
    Module.finitePresentation_of_projective R N
  -- clear the denominators of the retraction
  haveI := Module.FinitePresentation.isLocalizedModule_mapExtendScalars
    p.asIdeal.primeCompl mkN mkM A
  obtain ⟨⟨h₀, s⟩, hs⟩ := IsLocalizedModule.surj p.asIdeal.primeCompl
    (IsLocalizedModule.mapExtendScalars p.asIdeal.primeCompl mkN mkM A) σ
  have himg : ∀ m : M, mkM ((h₀.comp f) m) = mkM (((s : R) • m)) := by
    intro m
    have hfm : (f.baseChange A) (mkM m) = mkN (f m) := by simp [hmkM, hmkN]
    have hsg := LinearMap.congr_fun hs (mkN (f m))
    rw [Submonoid.smul_def] at hsg
    have hext : (IsLocalizedModule.mapExtendScalars p.asIdeal.primeCompl mkN mkM A)
        h₀ (mkN (f m)) = mkM (h₀ (f m)) := by simp
    rw [hext] at hsg
    have hsg2 : (s : R) • σ (mkN (f m)) = mkM (h₀ (f m)) := hsg
    -- `σ (mkN (f m)) = mkM m` by the left-inverse property
    have hσm := LinearMap.congr_fun hσ (mkM m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hσm
    rw [hfm] at hσm
    rw [hσm] at hsg2
    simp only [LinearMap.comp_apply]
    rw [← hsg2, map_smul]
  -- multiply out over a finite generating family
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose c hc using fun i ↦ IsLocalizedModule.exists_of_eq
    (S := p.asIdeal.primeCompl) (f := mkM) (himg (v i))
  set ctot : p.asIdeal.primeCompl := ∏ i, c i with hctot
  refine ⟨(ctot : R) * (s : R), fun hmem ↦ (ctot * s).2 hmem, (ctot : R) • h₀, ?_⟩
  apply LinearMap.ext_on hv
  rintro x ⟨i, rfl⟩
  have hcc : ∃ d : p.asIdeal.primeCompl, (d : R) * (c i : R) = (ctot : R) := by
    refine ⟨∏ j ∈ Finset.univ.erase i, c j, ?_⟩
    rw [hctot]
    push_cast
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  obtain ⟨d, hd⟩ := hcc
  have hci' : (c i : R) • ((h₀.comp f) (v i)) = (c i : R) • ((s : R) • (v i)) := by
    have := hc i
    rwa [Submonoid.smul_def, Submonoid.smul_def] at this
  have hmul := congrArg (fun z ↦ (d : R) • z) hci'
  simp only [smul_smul, ← mul_assoc, hd] at hmul
  show (((ctot : R) • h₀).comp f) (v i) = (((ctot : R) * (s : R)) • LinearMap.id) (v i)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  simpa only [LinearMap.comp_apply] using hmul

/-- **Stacks 00O0** (`algebra-lemma-cokernel-flat`), clause (1), openness. -/
@[stacks 00O0]
theorem isOpen_tensorInjectiveLocus [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) :
    IsOpen f.tensorInjectiveLocus := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨a, ha, h, hh⟩ := exists_scaled_leftInverse_of_lTensor_injective f p hp
  refine ⟨PrimeSpectrum.basicOpen a, ?_, (PrimeSpectrum.basicOpen a).2, ha⟩
  intro q hq
  rw [mem_tensorInjectiveLocus]
  -- from `h ∘ f = a • id` with `a` invertible in `κ(q)`
  have hres : (LinearMap.lTensor q.residueField h) ∘ₗ
      (LinearMap.lTensor q.residueField f) =
      algebraMap R q.residueField a • LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hh]
    ext x
    simp [algebraMap_smul]
  intro x y hxy
  have h1 := congrArg (LinearMap.lTensor q.residueField h) hxy
  have h2 := LinearMap.congr_fun hres x
  have h3 := LinearMap.congr_fun hres y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2 h3
  rw [h2, h3] at h1
  have hunit : algebraMap R q.residueField a ≠ 0 := by
    simpa [Ideal.algebraMap_residueField_eq_zero] using hq
  exact smul_right_injective _ hunit h1

/-- The cokernel of a linear map with a left inverse is projective (it is a direct
summand of the target). -/
theorem projective_coker_of_leftInverse {A : Type*} [CommRing A] {P Q : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] [Module.Projective A Q]
    (g : P →ₗ[A] Q) (σ : Q →ₗ[A] P) (hσ : σ.comp g = LinearMap.id) :
    Module.Projective A (Q ⧸ LinearMap.range g) := by
  set π : Q →ₗ[A] Q := LinearMap.id - g ∘ₗ σ with hπdef
  have hπ : LinearMap.range g ≤ LinearMap.ker π := by
    rintro _ ⟨x, rfl⟩
    have hσx : σ (g x) = x := LinearMap.congr_fun hσ x
    simp [hπdef, hσx]
  set w := (LinearMap.range g).liftQ π hπ with hw
  refine Module.Projective.of_split w (LinearMap.range g).mkQ ?_
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    have hwmk : w (Submodule.Quotient.mk y) = π y := rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hwmk]
    have : (LinearMap.range g).mkQ (π y) =
        (LinearMap.range g).mkQ y - (LinearMap.range g).mkQ (g (σ y)) := by
      simp [hπdef]
    rw [this]
    have hzero : (LinearMap.range g).mkQ (g (σ y)) = 0 := by
      simp [Submodule.Quotient.mk_eq_zero]
    rw [hzero, sub_zero]
    rfl

/-- Transport of projectivity between two models of the same localized module. -/
theorem _root_.Module.Projective.of_isLocalizedModule_pair
    {R : Type*} [CommRing R] (S : Submonoid R) {Rₛ : Type*} [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ]
    {X C D : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup C] [Module R C] [Module Rₛ C] [IsScalarTower R Rₛ C]
    [AddCommGroup D] [Module R D] [Module Rₛ D] [IsScalarTower R Rₛ D]
    (g₁ : X →ₗ[R] C) (g₂ : X →ₗ[R] D)
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂]
    [Module.Projective Rₛ D] : Module.Projective Rₛ C := by
  refine Module.Projective.of_equiv (R := Rₛ) (M := D)
    (show D ≃ₗ[Rₛ] C from
      { __ := IsLocalizedModule.linearEquiv S g₂ g₁
        map_smul' := ?_ })
  intro r m
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g₁ s)).1
  dsimp
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

/-- The localized image submodule is the range of the base change. -/
theorem localized'_range_eq_range_baseChange
    (f : M →ₗ[R] N) (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ]
    [IsLocalizedModule S (TensorProduct.mk R Rₛ N 1)]
    [IsLocalizedModule S (TensorProduct.mk R Rₛ M 1)] :
    Submodule.localized' Rₛ S (TensorProduct.mk R Rₛ N 1) (LinearMap.range f) =
      LinearMap.range (f.baseChange Rₛ) := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨n, ⟨m, rfl⟩, t, rfl⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    refine ⟨IsLocalizedModule.mk' (TensorProduct.mk R Rₛ M 1) m t, ?_⟩
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (TensorProduct.mk R Rₛ N 1) t)).1
    dsimp
    rw [← Submonoid.smul_def, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      Submonoid.smul_def, ← LinearMap.map_smul_of_tower, ← Submonoid.smul_def,
      IsLocalizedModule.mk'_cancel']
    simp
  · rintro _ ⟨y, rfl⟩
    obtain ⟨⟨m, t⟩, hmt⟩ := IsLocalizedModule.surj S (TensorProduct.mk R Rₛ M 1) y
    have hy : y = IsLocalizedModule.mk' (TensorProduct.mk R Rₛ M 1) m t := by
      apply ((Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (TensorProduct.mk R Rₛ M 1) t)).1
      dsimp
      rw [← Submonoid.smul_def, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
      exact hmt
    subst hy
    refine (Submodule.mem_localized' _ _ _ _ _).mpr
      ⟨f m, LinearMap.mem_range_self f m, t, ?_⟩
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (TensorProduct.mk R Rₛ N 1) t)).1
    dsimp
    rw [← Submonoid.smul_def, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      Submonoid.smul_def, ← LinearMap.map_smul_of_tower, ← Submonoid.smul_def,
      IsLocalizedModule.mk'_cancel']
    simp

/-- **Stacks 00O0** (`algebra-lemma-cokernel-flat`), clause (1)(b): on a basic open contained
in the fibrewise-injective locus, the cokernel is projective. -/
@[stacks 00O0]
theorem projective_coker_of_mem_tensorInjectiveLocus [Module.Finite R M]
    [Module.Projective R M] [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N)
    (a : R) (hU : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ⊆ f.tensorInjectiveLocus) :
    Module.Projective (Localization.Away a)
      (LocalizedModule.Away a (N ⧸ LinearMap.range f)) := by
  classical
  set R' := Localization.Away a with hR'
  -- every residue fibre of the base change to `R'` is injective
  have hall : ∀ p' : PrimeSpectrum R',
      Function.Injective (LinearMap.lTensor p'.residueField (f.baseChange R')) := by
    intro p'
    set q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p' with hq
    have hmem : q ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) := by
      show a ∉ q.asIdeal
      intro hcontra
      have : algebraMap R R' a ∈ p'.asIdeal := hcontra
      exact p'.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this
        (IsLocalization.Away.algebraMap_isUnit a))
    have hbase := hU hmem
    rw [mem_tensorInjectiveLocus] at hbase
    -- ascend along the residue-field embedding `κ(q) ↪ κ(p')`
    letI : Algebra q.residueField p'.residueField :=
      (Ideal.ResidueField.map q.asIdeal p'.asIdeal (algebraMap R R') rfl).toAlgebra
    haveI : IsScalarTower R q.residueField p'.residueField := by
      refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
      show algebraMap R p'.residueField r =
        Ideal.ResidueField.map q.asIdeal p'.asIdeal (algebraMap R R') rfl
          (algebraMap R q.residueField r)
      rw [Ideal.ResidueField.map_algebraMap]
      rw [IsScalarTower.algebraMap_apply R R' p'.residueField]
    have hmid : Function.Injective
        (LinearMap.lTensor p'.residueField f) :=
      lTensor_injective_of_lTensor_injective_of_field f q.residueField
        p'.residueField hbase
    exact lTensor_baseChange_injective_of_lTensor_injective f R' p'.residueField hmid
  -- the base-changed cokernel is projective over `R'`
  set f' := f.baseChange R' with hf'
  haveI : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  haveI hfpN' : Module.FinitePresentation R' (R' ⊗[R] N) := by
    haveI : Module.Projective R' (R' ⊗[R] N) := Module.Projective.tensorProduct
    exact Module.finitePresentation_of_projective R' _
  haveI hfpC : Module.FinitePresentation R' ((R' ⊗[R] N) ⧸ LinearMap.range f') := by
    refine Module.finitePresentation_of_surjective (LinearMap.range f').mkQ
      (Submodule.mkQ_surjective _) ?_
    rw [Submodule.ker_mkQ]
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ (Module.Finite.fg_top)
  haveI hproj' : Module.Projective R' ((R' ⊗[R] N) ⧸ LinearMap.range f') := by
    apply Module.projective_of_localization_maximal
    intro I hI
    set A := Localization.AtPrime I with hA
    -- split the further base change at the local ring `A`
    haveI : Module.Finite R' (R' ⊗[R] M) := inferInstance
    haveI : Module.Projective R' (R' ⊗[R] M) := Module.Projective.tensorProduct
    haveI : Module.Projective R' (R' ⊗[R] N) := Module.Projective.tensorProduct
    haveI : Module.Free A (A ⊗[R'] (R' ⊗[R] N)) :=
      Module.free_of_flat_of_isLocalRing
    obtain ⟨σ, hσ⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
      (f'.baseChange A)).mpr
      (lTensor_baseChange_injective_of_lTensor_injective f' A I.ResidueField
        (hall ⟨I, hI.isPrime⟩))
    haveI hcoker : Module.Projective A ((A ⊗[R'] (R' ⊗[R] N)) ⧸
        LinearMap.range (f'.baseChange A)) :=
      projective_coker_of_leftInverse (f'.baseChange A) σ hσ
    -- identify the localized cokernel with the cokernel of the base change
    set mkN' : (R' ⊗[R] N) →ₗ[R'] A ⊗[R'] (R' ⊗[R] N) :=
      TensorProduct.mk R' A (R' ⊗[R] N) 1 with hmkN'
    haveI hlN' : IsLocalizedModule I.primeCompl mkN' :=
      (isLocalizedModule_iff_isBaseChange I.primeCompl A mkN').mpr
        (TensorProduct.isBaseChange R' (R' ⊗[R] N) A)
    haveI hlM' : IsLocalizedModule I.primeCompl
        (TensorProduct.mk R' A (R' ⊗[R] M) 1) :=
      (isLocalizedModule_iff_isBaseChange I.primeCompl A _).mpr
        (TensorProduct.isBaseChange R' (R' ⊗[R] M) A)
    haveI hqproj : Module.Projective A ((A ⊗[R'] (R' ⊗[R] N)) ⧸
        Submodule.localized' A I.primeCompl mkN' (LinearMap.range f')) := by
      have heq := localized'_range_eq_range_baseChange f' I.primeCompl A
      exact Module.Projective.of_equiv (Submodule.quotEquivOfEq _ _ heq).symm
    exact Module.Projective.of_isLocalizedModule_pair I.primeCompl
      (LocalizedModule.mkLinearMap I.primeCompl ((R' ⊗[R] N) ⧸ LinearMap.range f'))
      ((LinearMap.range f').toLocalizedQuotient' A I.primeCompl mkN')
  -- finally, identify the localized cokernel over `R'` with the base-changed cokernel
  set mkN₀ : N →ₗ[R] R' ⊗[R] N := TensorProduct.mk R R' N 1 with hmkN₀
  haveI hlN₀ : IsLocalizedModule (Submonoid.powers a) mkN₀ :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) R' mkN₀).mpr
      (TensorProduct.isBaseChange R N R')
  haveI hlM₀ : IsLocalizedModule (Submonoid.powers a)
      (TensorProduct.mk R R' M 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) R' _).mpr
      (TensorProduct.isBaseChange R M R')
  haveI hq₀ : Module.Projective R' ((R' ⊗[R] N) ⧸
      Submodule.localized' R' (Submonoid.powers a) mkN₀ (LinearMap.range f)) := by
    have heq := localized'_range_eq_range_baseChange f (Submonoid.powers a) R'
    exact Module.Projective.of_equiv (Submodule.quotEquivOfEq _ _ heq).symm
  exact Module.Projective.of_isLocalizedModule_pair (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) (N ⧸ LinearMap.range f))
    ((LinearMap.range f).toLocalizedQuotient' R' (Submonoid.powers a) mkN₀)

end LinearMap
