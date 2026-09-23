module

public import StacksAndModuli.API.NoetherianLocalTensorFlatness
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.Module

/-!
# The Noetherian local flatness criterion

This file proves the tensor-kernel forms of the finite-length propagation lemma and the
Noetherian local flatness criterion used in Stacks Project tags 00MJ and 00MK.

For a map into a flat module, injectivity after tensoring with the residue field propagates
to every finite-length module.  Applied to a free presentation, this converts injectivity of
`maximalIdeal R ⊗ M → M` into injectivity for every ideal with finite-length quotient.
The Artin--Rees and Krull-intersection API in `NoetherianLocalTensorFlatness` then handles an
arbitrary ideal.
-/

@[expose] public section

open TensorProduct

universe u v w x y z

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {K : Type v} {F : Type w} {A : Type x} {B : Type y} {C : Type z}
variable [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]

/-- Tensor-injectivity for the ends of a short exact sequence propagates to its middle
term, provided the target of the fixed map is flat. -/
theorem rTensor_injective_of_extension (f : K →ₗ[R] F)
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hex : Function.Exact i p) (hi : Function.Injective i)
    (hp : Function.Surjective p) [Module.Flat R F]
    (hA : Function.Injective (f.rTensor A))
    (hC : Function.Injective (f.rTensor C)) :
    Function.Injective (f.rTensor B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxC : p.lTensor K x = 0 := by
    apply hC
    calc
      f.rTensor C (p.lTensor K x) = p.lTensor F (f.rTensor B x) := by
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
      _ = 0 := by rw [hx]; simp
  obtain ⟨y, hy⟩ := (lTensor_exact K hex hp x).mp hxC
  have hyF : i.lTensor F (f.rTensor A y) = 0 := by
    calc
      i.lTensor F (f.rTensor A y) = f.rTensor B (i.lTensor K y) := by
        rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
          ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
      _ = 0 := by rw [hy, hx]
  have hiy : f.rTensor A y = 0 :=
    (Module.Flat.lTensor_preserves_injective_linearMap i hi) hyF
  rw [(injective_iff_map_eq_zero _).mp hA y hiy] at hy
  simpa using hy.symm

/-- Tensor-injectivity transports across a linear equivalence in the tensor factor. -/
theorem rTensor_injective_of_linearEquiv (f : K →ₗ[R] F)
    (e : A ≃ₗ[R] B) (hB : Function.Injective (f.rTensor B)) :
    Function.Injective (f.rTensor A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (e.lTensor K).injective
  apply (injective_iff_map_eq_zero _).mp hB
  calc
    f.rTensor B (e.lTensor K x) = e.lTensor F (f.rTensor A x) := by
      change f.rTensor B (e.toLinearMap.lTensor K x) =
        e.toLinearMap.lTensor F (f.rTensor A x)
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]
    _ = 0 := by rw [hx]; simp

/-- Over a local ring, residue-field tensor-injectivity propagates to every simple
module. -/
theorem rTensor_injective_of_isSimpleModule [IsLocalRing R]
    (f : K →ₗ[R] F) [IsSimpleModule R A]
    (hk : Function.Injective (f.rTensor (IsLocalRing.ResidueField R))) :
    Function.Injective (f.rTensor A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance :
    IsSimpleModule R A)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact rTensor_injective_of_linearEquiv f e hk

/-- Over a local ring, residue-field tensor-injectivity propagates to every
finite-length module when the target of the fixed map is flat. -/
theorem rTensor_injective_of_isFiniteLength [IsLocalRing R]
    (f : K →ₗ[R] F) [Module.Flat R F]
    (hk : Function.Injective (f.rTensor (IsLocalRing.ResidueField R)))
    {Q : Type x} [AddCommGroup Q] [Module R Q] (hQ : IsFiniteLength R Q) :
    Function.Injective (f.rTensor Q) := by
  induction hQ with
  | of_subsingleton => exact fun _ _ _ => Subsingleton.elim _ _
  | @of_simple_quotient Q _ _ N _ hN ih =>
    exact rTensor_injective_of_extension f N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N) Subtype.val_injective
      (Submodule.mkQ_surjective N) ih
      (rTensor_injective_of_isSimpleModule f hk)

/-- For a short exact presentation with flat middle term, injectivity of the maximal-ideal
tensor map on the cokernel implies residue-field tensor-injectivity of its kernel map. -/
theorem lTensor_residueField_injective_of_maximalIdeal_rTensor_injective
    [IsLocalRing R] (f : K →ₗ[R] F) (g : F →ₗ[R] C)
    (hex : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g)
    (hmax : Function.Injective
      ((IsLocalRing.maximalIdeal R).subtype.rTensor C)) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) := by
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := (IsLocalRing.maximalIdeal R).subtype)
    (f₂ := Submodule.mkQ (IsLocalRing.maximalIdeal R))
    (g₁ := f) (g₂ := g)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
    hex hg hmax (Module.Flat.lTensor_preserves_injective_linearMap f hf)

/-- In a short exact presentation with flat middle term, injectivity of the maximal-ideal
tensor map on the cokernel propagates to ideals with finite-length quotient. -/
theorem ideal_rTensor_injective_of_finiteLength_quotient_of_presentation
    [IsLocalRing R] (f : K →ₗ[R] F) (g : F →ₗ[R] C)
    (hex : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) [Module.Flat R F]
    (hmax : Function.Injective
      ((IsLocalRing.maximalIdeal R).subtype.rTensor C))
    (J : Ideal R) (hJ : IsFiniteLength R (R ⧸ J)) :
    Function.Injective (J.subtype.rTensor C) := by
  have hkL : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) :=
    lTensor_residueField_injective_of_maximalIdeal_rTensor_injective
      f g hex hf hg hmax
  have hkR : Function.Injective (f.rTensor (IsLocalRing.ResidueField R)) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj _ f).mp hkL
  have hQ : Function.Injective (f.rTensor (R ⧸ J)) :=
    rTensor_injective_of_isFiniteLength f hkR hJ
  apply (LinearMap.lTensor_inj_iff_rTensor_inj C J.subtype).mp
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    hex hg (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J)
    hQ (Module.Flat.lTensor_preserves_injective_linearMap J.subtype
      Subtype.val_injective)

end LinearMap

namespace Ideal

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A quotient of a Noetherian local ring by an ideal containing a power of the maximal
ideal has finite length. -/
theorem isFiniteLength_quotient_of_maximalIdeal_pow_le [IsNoetherianRing R]
    (J : Ideal R) (hJ : ∃ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n ≤ J) :
    IsFiniteLength R (R ⧸ J) := by
  by_cases htop : J = ⊤
  · subst J
    exact IsFiniteLength.of_subsingleton
  let q := Ideal.Quotient.mk J
  let _ : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr htop
  let _ : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (R ⧸ J)) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have hm : (IsLocalRing.maximalIdeal R).map q =
        IsLocalRing.maximalIdeal (R ⧸ J) :=
      IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
    rw [← hm, ← Ideal.map_pow, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hn
  have hArt : IsArtinianRing (R ⧸ J) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ J)).mpr hnil
  let e : (R ⧸ J) →ₛₗ[Ideal.Quotient.mk J] (R ⧸ J) :=
    ⟨.id _, fun _ _ ↦ rfl⟩
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  exact (e.isArtinian_iff_of_bijective Function.bijective_id).mpr hArt

/-- Injectivity of the maximal-ideal tensor map on a module over a local ring propagates
to every ideal whose quotient has finite length. -/
theorem rTensor_injective_of_finiteLength_quotient
    (hmax : Function.Injective
      ((IsLocalRing.maximalIdeal R).subtype.rTensor M))
    (J : Ideal R) (hJ : IsFiniteLength R (R ⧸ J)) :
    Function.Injective (J.subtype.rTensor M) := by
  let g : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hg : Function.Surjective g := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    simp [g]
  let f : LinearMap.ker g →ₗ[R] (M →₀ R) := (LinearMap.ker g).subtype
  have hf : Function.Injective f := Subtype.val_injective
  have hex : Function.Exact f g := by
    simpa [f] using LinearMap.exact_subtype_ker_map g
  exact LinearMap.ideal_rTensor_injective_of_finiteLength_quotient_of_presentation
    (K := LinearMap.ker g) (F := M →₀ R) (C := M) (f := f) (g := g)
    hex hf hg hmax J hJ

end Ideal

namespace Module.Flat

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/-- The Noetherian local flatness criterion in tensor-kernel form: for a local map of
Noetherian local rings `R → S` and an `S`-finite module `M`, injectivity of
`maximalIdeal R ⊗[R] M → M` implies that `M` is flat over `R`. -/
theorem of_maximalIdeal_rTensor_injective_of_finite
    (S : Type w) [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hmax : Function.Injective
      ((IsLocalRing.maximalIdeal R).subtype.rTensor M)) :
    Module.Flat R M := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply Ideal.injective_rTensor_of_injective_sup_maximalIdeal_pow (S := S)
  intro n
  apply Ideal.rTensor_injective_of_finiteLength_quotient hmax
  apply Ideal.isFiniteLength_quotient_of_maximalIdeal_pow_le
  exact ⟨n, le_sup_right⟩

end Module.Flat
