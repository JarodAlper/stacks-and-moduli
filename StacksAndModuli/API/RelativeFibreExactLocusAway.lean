module

public import StacksAndModuli.API.RelativeFibreFlatCokernel
public import StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Relative-fibre exactness under principal localization

For a finite matrix over an algebra `S`, this file compares the canonical kernel
presentation of its cokernel with the corresponding presentation after localizing `S` away
from one element.  At a prime of the principal localization, the two relative-fibre
exactness predicates agree after contraction to `Spec S`.

The comparison is made through localized cokernels rather than through kernels.  Scalar
extension commutes with the matrix cokernel, localization at a prime of an away localization
is the localization at the contracted prime, and relative-fibre exactness of a canonical
kernel presentation is equivalent to flatness of that localized cokernel.  In particular,
no freeness or base-change theorem for the kernel is required.

Topologically, the prime spectrum of `Localization.Away a` is the basic open `D(a)`.
Consequently an open relative-fibre exactness locus after principal localization gives an
open intersection of the original locus with `D(a)`.  If such a localization is available
around every point of the original locus, the original locus is open.

Main declarations:

* `Matrix.toLinCokerBaseChangeEquiv`;
* `Matrix.awayLocalizedToLinCokerEquiv`;
* `Matrix.isRelativeFibreExactAt_kernel_toLin_map_away_iff`;
* `Matrix.image_relativeFibreExactLocus_kernel_toLin_map_away`;
* `Matrix.isOpen_relativeFibreExactLocus_inter_basicOpen_of_away`;
* `Matrix.hasOpenRelativeFibreExactLocus_kernel_toLin_of_away_local`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Matrix

/-- Scalar extension commutes with the concrete cokernel of the linear map associated to a
finite matrix, after identifying the scalar extension of a standard finite free module with
the corresponding standard finite free module. -/
noncomputable def toLinCokerBaseChangeEquiv
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S) :
    ((Fin n → T) ⧸ LinearMap.range
        (Matrix.toLin' (G.map (algebraMap S T)))) ≃ₗ[T]
      T ⊗[S] ((Fin n → S) ⧸ LinearMap.range (Matrix.toLin' G)) := by
  let e := TensorProduct.piScalarRight S T T (Fin n)
  let eQuot :
      ((T ⊗[S] (Fin n → S)) ⧸
          LinearMap.range ((Matrix.toLin' G).baseChange T)) ≃ₗ[T]
        ((Fin n → T) ⧸ LinearMap.range
          (Matrix.toLin' (G.map (algebraMap S T)))) :=
    Submodule.Quotient.equiv _ _ e (by
      simpa only [LinearMap.range_baseChange] using
        (Matrix.map_baseChange_range (A := T) G))
  exact eQuot.symm.trans
    (LinearMap.baseChangeCokerEquiv (Matrix.toLin' G))

/-- At corresponding primes of a ring and one of its principal localizations, the localized
cokernel of the coefficientwise localized matrix is linearly equivalent to the localization
of the original matrix cokernel. -/
noncomputable def awayLocalizedToLinCokerEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S) (a : S)
    (q : PrimeSpectrum (Localization.Away a)) :
    let T := Localization.Away a
    (Localization.AtPrime q.asIdeal ⊗[T]
        ((Fin n → T) ⧸ LinearMap.range
          (Matrix.toLin' (G.map (algebraMap S T))))) ≃ₗ[S]
      Localization.AtPrime
          (q.comap (algebraMap S T)).asIdeal ⊗[S]
        ((Fin n → S) ⧸ LinearMap.range (Matrix.toLin' G)) := by
  let T := Localization.Away a
  let U := Localization.AtPrime
    (q.comap (algebraMap S T)).asIdeal
  let V := Localization.AtPrime q.asIdeal
  let M := (Fin n → S) ⧸ LinearMap.range (Matrix.toLin' G)
  let Gₐ := G.map (algebraMap S T)
  let eCoker :
      ((Fin n → T) ⧸ LinearMap.range (Matrix.toLin' Gₐ)) ≃ₗ[T]
        T ⊗[S] M :=
    Matrix.toLinCokerBaseChangeEquiv G
  let eTensor :
      (V ⊗[T] ((Fin n → T) ⧸
          LinearMap.range (Matrix.toLin' Gₐ))) ≃ₗ[V]
        V ⊗[T] (T ⊗[S] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl V V) eCoker
  let eCancel : V ⊗[T] (T ⊗[S] M) ≃ₗ[V] V ⊗[S] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S T V V M
  let eRing : U ≃ₐ[S] V :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers a) q.asIdeal
  let ePrime : U ⊗[S] M ≃ₗ[S] V ⊗[S] M :=
    TensorProduct.congr eRing.toLinearEquiv (LinearEquiv.refl S M)
  exact ((eTensor.trans eCancel).restrictScalars S).trans ePrime.symm

/-- Relative-fibre exactness of the canonical kernel presentation of a localized matrix at
a prime is equivalent to relative-fibre exactness of the original canonical presentation at
the contracted prime. -/
theorem isRelativeFibreExactAt_kernel_toLin_map_away_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S) (a : S)
    (q : PrimeSpectrum (Localization.Away a)) :
    let T := Localization.Away a
    let Gₐ := G.map (algebraMap S T)
    LinearMap.IsRelativeFibreExactAt (R := R)
        (LinearMap.ker (Matrix.toLin' Gₐ)).subtype
        (Matrix.toLin' Gₐ) q ↔
      LinearMap.IsRelativeFibreExactAt (R := R)
        (LinearMap.ker (Matrix.toLin' G)).subtype
        (Matrix.toLin' G)
        (q.comap (algebraMap S T)) := by
  let T := Localization.Away a
  let Gₐ := G.map (algebraMap S T)
  let g := Matrix.toLin' G
  let gₐ := Matrix.toLin' Gₐ
  letI : Module.Free S S := Module.Free.self S
  letI : Module.Free S (Fin n → S) :=
    Module.Free.function (Fin n) S S
  letI : Module.Projective S (Fin n → S) :=
    Module.Projective.of_free
  letI : Module.Free T T := Module.Free.self T
  letI : Module.Free T (Fin n → T) :=
    Module.Free.function (Fin n) T T
  letI : Module.Projective T (Fin n → T) :=
    Module.Projective.of_free
  change LinearMap.IsRelativeFibreExactAt (R := R)
      (LinearMap.ker gₐ).subtype gₐ q ↔
    LinearMap.IsRelativeFibreExactAt (R := R)
      (LinearMap.ker g).subtype g (q.comap (algebraMap S T))
  rw [Module.Flat.isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact
        q (LinearMap.ker gₐ).subtype gₐ
        (LinearMap.exact_subtype_ker_map gₐ),
    Module.Flat.isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact
      (q.comap (algebraMap S T)) (LinearMap.ker g).subtype g
      (LinearMap.exact_subtype_ker_map g)]
  exact Module.Flat.equiv_iff
    ((Matrix.awayLocalizedToLinCokerEquiv (R := R) G a q).restrictScalars R)

/-- Under contraction from a principal localization, the image of the localized canonical
relative-fibre exactness locus is the intersection of the original locus with the
corresponding basic open. -/
theorem image_relativeFibreExactLocus_kernel_toLin_map_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S) (a : S) :
    let T := Localization.Away a
    let Gₐ := G.map (algebraMap S T)
    PrimeSpectrum.comap (algebraMap S T) ''
        LinearMap.relativeFibreExactLocus (R := R)
          (LinearMap.ker (Matrix.toLin' Gₐ)).subtype
          (Matrix.toLin' Gₐ) =
      LinearMap.relativeFibreExactLocus (R := R)
          (LinearMap.ker (Matrix.toLin' G)).subtype
          (Matrix.toLin' G) ∩
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) := by
  let T := Localization.Away a
  let Gₐ := G.map (algebraMap S T)
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, ?_⟩
    · exact
        (Matrix.isRelativeFibreExactAt_kernel_toLin_map_away_iff
          (R := R) G a q).mp hq
    · rw [← PrimeSpectrum.localization_away_comap_range T a]
      exact ⟨q, rfl⟩
  · rintro ⟨hp, hpa⟩
    rw [← PrimeSpectrum.localization_away_comap_range T a] at hpa
    obtain ⟨q, rfl⟩ := hpa
    exact ⟨q,
      (Matrix.isRelativeFibreExactAt_kernel_toLin_map_away_iff
        (R := R) G a q).mpr hp, rfl⟩

/-- Openness of the canonical relative-fibre exactness locus after principal localization
makes the intersection of the original locus with that principal open subset open. -/
theorem isOpen_relativeFibreExactLocus_inter_basicOpen_of_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S) (a : S)
    (hopen : LinearMap.HasOpenRelativeFibreExactLocus (R := R)
      (LinearMap.ker (Matrix.toLin'
        (G.map (algebraMap S (Localization.Away a))))).subtype
      (Matrix.toLin'
        (G.map (algebraMap S (Localization.Away a))))) :
    IsOpen (LinearMap.relativeFibreExactLocus (R := R)
        (LinearMap.ker (Matrix.toLin' G)).subtype
        (Matrix.toLin' G) ∩
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S))) := by
  rw [← Matrix.image_relativeFibreExactLocus_kernel_toLin_map_away
    (R := R) G a]
  exact (PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization.Away a) a).isOpenMap _ hopen

/-- If every point of the canonical relative-fibre exactness locus has a principal
localization on which the corresponding localized canonical locus is open, then the
original canonical locus is open. -/
theorem hasOpenRelativeFibreExactLocus_kernel_toLin_of_away_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) S)
    (hlocal : ∀ q : PrimeSpectrum S,
      LinearMap.IsRelativeFibreExactAt (R := R)
          (LinearMap.ker (Matrix.toLin' G)).subtype
          (Matrix.toLin' G) q →
        ∃ a : S, a ∉ q.asIdeal ∧
          LinearMap.HasOpenRelativeFibreExactLocus (R := R)
            (LinearMap.ker (Matrix.toLin'
              (G.map (algebraMap S (Localization.Away a))))).subtype
            (Matrix.toLin'
              (G.map (algebraMap S (Localization.Away a))))) :
    LinearMap.HasOpenRelativeFibreExactLocus (R := R)
      (LinearMap.ker (Matrix.toLin' G)).subtype
      (Matrix.toLin' G) := by
  change IsOpen (LinearMap.relativeFibreExactLocus (R := R)
    (LinearMap.ker (Matrix.toLin' G)).subtype (Matrix.toLin' G))
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨a, ha, hopen⟩ := hlocal q hq
  refine ⟨LinearMap.relativeFibreExactLocus (R := R)
      (LinearMap.ker (Matrix.toLin' G)).subtype (Matrix.toLin' G) ∩
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)),
    Set.inter_subset_left, ?_, ⟨hq, ha⟩⟩
  exact Matrix.isOpen_relativeFibreExactLocus_inter_basicOpen_of_away
    (R := R) G a hopen

end Matrix

end

end
