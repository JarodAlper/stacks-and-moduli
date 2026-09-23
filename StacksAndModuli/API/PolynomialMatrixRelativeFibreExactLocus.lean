module

public import StacksAndModuli.API.FiniteFreeComplexExpectedRanksExistence
public import StacksAndModuli.API.FiniteFreeComplexRelativeFibreResolution
public import StacksAndModuli.API.FreeBasicOpen
public import StacksAndModuli.API.PartialProjectiveResolutionFiniteFreeComplex
public import StacksAndModuli.API.PolynomialPartialResolutionArbitraryPrimeFreeNeighborhood
public import StacksAndModuli.API.RelativeFibreExactLocusAway

/-!
# Relative-fibre exact loci of polynomial matrices

Let `A` be Noetherian, let `S = A[x_i]` have finitely many variables, and let `G` be a
finite matrix over `S`.  This file reduces openness of the relative-fibre exactness locus
of the canonical presentation

`ker(toLin G) → Sⁿ → coker(toLin G)`

to relative regular-sequence openness after principal localization of `S`.

At a point of the exactness locus, the localized matrix cokernel is flat over `A`.  An
anchored finite-free partial resolution of that cokernel can therefore be localized on a
principal neighbourhood so that its terminal syzygy is free.  Compiling this anchored
resolution gives a bounded exact finite-free complex whose first differential is literally
the localized matrix.  Expected ranks exist automatically, so the relative
Buchsbaum--Eisenbud theorem proves openness on that principal neighbourhood.  The Away
comparison then glues these neighbourhoods into the desired open locus.

The sole remaining hypothesis is the varying-fibre regular-sequence theorem (Stacks
Project tag 00RA) for principal localizations of the polynomial algebra.

Main declarations:

* `MvPolynomial.HasOpenRelativeFibreRegularSequenceLociAfterAway`;
* `Matrix.hasOpenRelativeFibreExactLocus_kernel_toLin_mvPolynomial_of_regularSequence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace MvPolynomial

/-- Relative regularity of every finite sequence is open on its zero locus after every
principal localization of a polynomial algebra.  This is the exact 00RA input consumed by
the polynomial-matrix 00RB theorem. -/
def HasOpenRelativeFibreRegularSequenceLociAfterAway
    (A : Type u) (sigma : Type v) [CommRing A] : Prop :=
  ∀ (a : MvPolynomial sigma A) (d : ℕ)
    (f : Fin d → Localization.Away a),
    IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
      Matrix.FiniteFreeComplex.IsRelativeFibreRegularSequenceAt
        (R := A) q.1 f}

end MvPolynomial

namespace Matrix

/-- Relative regular-sequence openness after principal localization implies openness of
the canonical relative-fibre exactness locus of every finite polynomial matrix.  This is
the finite-presentation exactness-locus theorem 00RB in the form used by coefficient
spreading. -/
theorem hasOpenRelativeFibreExactLocus_kernel_toLin_mvPolynomial_of_regularSequence
    {A : Type u} {sigma : Type v}
    [CommRing A] [IsNoetherianRing A] [Finite sigma]
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial sigma A))
    (hregular :
      MvPolynomial.HasOpenRelativeFibreRegularSequenceLociAfterAway A sigma) :
    LinearMap.HasOpenRelativeFibreExactLocus (R := A)
      (LinearMap.ker (Matrix.toLin' G)).subtype (Matrix.toLin' G) := by
  let S := MvPolynomial sigma A
  let g : (Fin m → S) →ₗ[S] (Fin n → S) := Matrix.toLin' G
  letI : Module.Free S S := Module.Free.self S
  letI : Module.Free S (Fin n → S) :=
    Module.Free.function (Fin n) S S
  letI : Module.Projective S (Fin n → S) :=
    Module.Projective.of_free
  apply Matrix.hasOpenRelativeFibreExactLocus_kernel_toLin_of_away_local
    (R := A) G
  intro q hq
  have hcomp : g.comp (LinearMap.ker g).subtype = 0 :=
    (LinearMap.exact_subtype_ker_map g).linearMap_comp_eq_zero
  have hflat : Module.Flat A
      (Localization.AtPrime q.asIdeal ⊗[S]
        ((Fin n → S) ⧸ LinearMap.range g)) :=
    Module.Flat.localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
      q (LinearMap.ker g).subtype g hcomp hq
  let d := Nat.card sigma
  obtain ⟨K, addK, moduleK, finiteK, hanchor⟩ :=
    Module.exists_anchoredMatrixCokernel_finiteFree S G d
  letI : AddCommGroup K := addK
  letI : Module S K := moduleK
  letI : Module.Finite S K := finiteK
  let hresolution := hanchor.toResolution
  obtain ⟨a, ha, hfree⟩ :=
    Module.IsPartialProjectiveResolution.exists_away_free_final_of_flat_localizationAtPrime
      q hresolution hflat (by dsimp only [d]; omega)
  letI : Nontrivial (Localization.Away a) :=
    IsLocalization.Away.nontrivial_of_notMem ha (Localization.Away a)
  letI : Module.Flat A (Localization.Away a) :=
    Module.Flat.trans A S (Localization.Away a)
  obtain ⟨C, hbounded, hexact⟩ :=
    hanchor.exists_finiteFreeComplex_away a hfree
  let D := C.toFiniteFreeComplex
  obtain ⟨r⟩ :=
    D.nonempty_expectedRanks_of_exact (d + 3) hbounded hexact
  have hopenD :=
    D.hasOpenRelativeFibreKernelExactLocus_of_buchsbaumEisenbudGrade
      (R := A) (d + 3) hbounded hexact r
      (fun i _ f _ ↦ hregular a (i + 1) f)
  change LinearMap.HasOpenRelativeFibreExactLocus (R := A)
      (LinearMap.ker (Matrix.toLin'
        (G.map (algebraMap S (Localization.Away a))))).subtype
      (Matrix.toLin' (G.map (algebraMap S (Localization.Away a)))) at hopenD
  have hopen := hopenD
  exact ⟨a, ha, hopen⟩

end Matrix

end
