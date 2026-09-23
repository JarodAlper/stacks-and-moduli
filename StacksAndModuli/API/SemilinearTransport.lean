module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Transport of module properties along a semilinear equivalence

Supporting API with no Stacks Project counterpart.

§2.1 repeatedly compares an `R`-module with the sections `Γ(M, ⊤)` of the corresponding sheaf on
`Spec R`, which are a module over `Γ(Spec R, ⊤)` rather than over `R`. The two coefficient rings
are identified by `Scheme.ΓSpecIso`, so the comparison is a *semilinear* equivalence over a ring
equivalence, not a linear one. Mathlib's transport lemmas (`Module.Finite.equiv`,
`Module.Projective.of_equiv`, `Module.rankAtStalk_eq_of_equiv`) are all stated for `≃ₗ`, i.e. for
a fixed coefficient ring, so they do not apply.

These lemmas package the semilinear versions. Each is a transport of structure along a ring
equivalence and carries no mathematical content beyond that, but the bookkeeping is what makes
the §2.1 comparisons go through.

Main declarations:
- `Module.Flat.of_ringEquiv`, `Module.Flat.baseChange_of_semilinearEquiv`;
- `Module.finite_projective_of_semilinearEquiv`;
- `Module.finite_projective_rankAtStalk_of_semilinearEquiv`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Module

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w}
variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The base-change structure induced by a semilinear equivalence over a ring isomorphism
that agrees with the algebra map: `N` is the base change of `M` along `R → S`. Stated with
`N` regarded as an `R`-module through `e`. -/
theorem isBaseChange_of_semilinearEquiv [Algebra R S] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
    (h : algebraMap R S = (e : R →+* S)) (eM : M ≃ₛₗ[(e : R →+* S)] N) :
    letI : Module R N := Module.compHom N (e : R →+* S)
    haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
      show (r • s) • n = (e : R →+* S) r • (s • n)
      rw [Algebra.smul_def, h, mul_smul]⟩
    IsBaseChange S
      ({ toFun := eM
         map_add' := fun a b ↦ map_add eM a b
         map_smul' := fun r m ↦ eM.map_smulₛₗ r m } : M →ₗ[R] N) := by
  letI : Module R N := Module.compHom N (e : R →+* S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    show (r • s) • n = (e : R →+* S) r • (s • n)
    rw [Algebra.smul_def, h, mul_smul]⟩
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  refine ⟨{ toFun := fun n ↦ g (eM.symm n)
            map_add' := fun a b ↦ by simp
            map_smul' := fun s n ↦ by
              show g (eM.symm (s • n)) = s • g (eM.symm n)
              rw [show eM.symm (s • n) = e.symm s • eM.symm n from eM.symm.map_smulₛₗ s n,
                map_smul, ← algebraMap_smul S (e.symm s) (g (eM.symm n)), h]
              simp }, ?_, ?_⟩
  · ext m
    simp
  · rintro g' hg'
    ext n
    have hh := LinearMap.congr_fun hg' (eM.symm n)
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk] at hh ⊢
    rw [← hh]
    congr 1
    exact (eM.apply_symm_apply n).symm

/-- Flatness transports along a semilinear equivalence whose ring equivalence is the algebra
map. This is the form used at the `Γ(Spec R, ⊤)` comparisons. -/
theorem Flat.baseChange_of_semilinearEquiv [Algebra R S] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
    (h : algebraMap R S = (e : R →+* S)) (eM : M ≃ₛₗ[(e : R →+* S)] N) [Module.Flat R M] :
    Module.Flat S N := by
  letI : Module R N := Module.compHom N (e : R →+* S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    show (r • s) • n = (e : R →+* S) r • (s • n)
    rw [Algebra.smul_def, h, mul_smul]⟩
  exact Module.Flat.isBaseChange (R := R) (S := S) (M := M) N
    (isBaseChange_of_semilinearEquiv e h eM)

/-- Flatness transports along a semilinear equivalence over a ring equivalence. -/
theorem Flat.of_ringEquiv (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (eM : M ≃ₛₗ[(e : R →+* S)] N) [Module.Flat R M] :
    Module.Flat S N := by
  letI : Algebra R S := (e : R →+* S).toAlgebra
  exact Flat.baseChange_of_semilinearEquiv e rfl eM

/-- Finiteness and projectivity transport along a semilinear equivalence. -/
theorem finite_projective_of_semilinearEquiv [Algebra R S] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
    (h : algebraMap R S = (e : R →+* S)) (eM : M ≃ₛₗ[(e : R →+* S)] N)
    (hfin : Module.Finite R M) (hproj : Module.Projective R M) :
    Module.Finite S N ∧ Module.Projective S N := by
  haveI : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  exact ⟨Module.Finite.of_surjective (eM : M →ₛₗ[(e : R →+* S)] N) eM.surjective,
    Module.Projective.of_ringEquiv eM⟩

/-- Finiteness, projectivity and constant stalk rank transport along a semilinear
equivalence. The rank statement additionally uses that `e` induces a homeomorphism
`Spec S ≃ Spec R` under which the stalk ranks correspond. -/
theorem finite_projective_rankAtStalk_of_semilinearEquiv [Algebra R S] {q : ℕ} (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
    (h : algebraMap R S = (e : R →+* S)) (eM : M ≃ₛₗ[(e : R →+* S)] N)
    (hfin : Module.Finite R M) (hproj : Module.Projective R M)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = q) :
    Module.Finite S N ∧ Module.Projective S N ∧
      ∀ p : PrimeSpectrum S, Module.rankAtStalk N p = q := by
  obtain ⟨h1, h2⟩ := finite_projective_of_semilinearEquiv e h eM hfin hproj
  refine ⟨h1, h2, fun p ↦ ?_⟩
  letI : Module R N := Module.compHom N (e : R →+* S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    show (r • s) • n = (e : R →+* S) r • (s • n)
    rw [Algebra.smul_def, h, mul_smul]⟩
  rw [Module.rankAtStalk_isBaseChange (isBaseChange_of_semilinearEquiv e h eM) p]
  exact hrank _

end Module

section BaseChange

open TensorProduct

/-- Finiteness, projectivity and constant stalk rank all ascend along a base change.

Mathlib supplies each piece: `Module.Finite.base_change` and `Module.Projective.tensorProduct`
are instances, and `Module.rankAtStalk_baseChange` identifies the rank of `S ⊗[R] M` at `p` with
the rank of `M` at the contracted prime. -/
theorem Module.finite_projective_rankAtStalk_baseChange (R S M : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (hfin : Module.Finite R M) (hproj : Module.Projective R M) (q : ℕ)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = q) :
    Module.Finite S (S ⊗[R] M) ∧ Module.Projective S (S ⊗[R] M) ∧
      ∀ p : PrimeSpectrum S, Module.rankAtStalk (S ⊗[R] M) p = q := by
  refine ⟨inferInstance, inferInstance, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_baseChange]
  exact hrank _

/-- Flatness over the base ascends across a pushout square of rings: if `B` is the pushout of
`A ← R → S` and `M` is an `A`-module flat over `R`, then `B ⊗[A] M` is flat over `S`.

Proof route: the pushout gives `B ≅ S ⊗[R] A` as an `A`-algebra, whence
`B ⊗[A] M ≅ S ⊗[R] M` as `S`-modules by associativity of the tensor product; flatness of `M`
over `R` then gives flatness of `S ⊗[R] M` over `S` by base change. -/
theorem Module.Flat.baseChange_of_isPushout (R S A B : Type*) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B]
    [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    (M : Type*) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.Flat R M] : Module.Flat S (TensorProduct A B M) :=
  Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R S A B M)

end BaseChange
