module

public import StacksProject.Algebra.SmoothOverField.«lemma-separable-smooth»
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Local rings of a smooth algebra over a field are regular

Stacks Project tag **00TT**, label `algebra-lemma-characterize-smooth-over-field`, in
`algebra.tex`, §`00TQ` (Smooth algebras over fields).

> Let `k` be a field, `S` a finite type `k`-algebra, `X = Spec S`, and `q ⊆ S` a prime
> corresponding to `x ∈ X`. The following are equivalent: (1) `S` is smooth at `q` over `k`;
> (2) `dim_{κ(q)} Ω_{S/k} ⊗_S κ(q) ≤ dim_x X`; (3) equality holds. **Moreover, in this case the
> local ring `S_q` is regular.**

Only the final clause is needed by §3.1, so that is what is stated here.

Mathlib has `Algebra.Smooth`, `Algebra.IsSmoothAt`, `Algebra.smoothLocus` and the standard
smooth machinery, and it has `IsRegularLocalRing`. What it does **not** have is any link
between smoothness and regularity — `grep IsReduced Mathlib/RingTheory/Smooth/` and the
corresponding search for `IsRegularLocalRing` both come up empty.

**Proof route (Stacks Project).** Via `00TS`
(`algebra-lemma-characterize-smooth-kbar`, the algebraically closed case) and the Jacobian
criterion: smoothness gives, Zariski-locally, a standard smooth presentation
(`Algebra.IsStandardSmooth`, which Mathlib has as
`Mathlib/RingTheory/Smooth/StandardSmooth.lean`), whose relative dimension computes both
`dim_x X` and the rank of the module of differentials; regularity of `S_q` then follows from
the corresponding statement for a polynomial ring together with the regular-sequence
description of the presentation ideal. Descending from `k̄` to `k` uses that regularity is
insensitive to a separable (indeed any faithfully flat) base field extension.
-/

@[expose] public section

universe u

open IsLocalRing

/-- Regularity ascends along a flat, formally unramified, essentially finite type local
homomorphism of Noetherian local rings. -/
lemma regularLocal_of_formallyUnramified_flat (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    [IsRegularLocalRing A] : IsRegularLocalRing B := by
  have hmap : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
    Algebra.FormallyUnramified.map_maximalIdeal
  haveI : (maximalIdeal B).LiesOver (maximalIdeal A) := by
    constructor
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  have hheight : (maximalIdeal B).height = (maximalIdeal A).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A), hmap]
    simp
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  show ((maximalIdeal B).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim B
  calc
    ((maximalIdeal B).spanFinrank : WithBot ℕ∞) =
        (((maximalIdeal A).map (algebraMap A B)).spanFinrank : WithBot ℕ∞) := by rw [hmap]
    _ ≤ ((maximalIdeal A).spanFinrank : WithBot ℕ∞) := by
      norm_cast
      exact Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing
    _ = ringKrullDim A := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ = ringKrullDim B := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
        ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight]

/-- A localization at a prime of a smooth algebra over a field is regular. -/
lemma regularAtPrime_of_smooth (K S : Type u) [Field K] [CommRing S] [Algebra K S]
    [Algebra.Smooth K S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨f, hfq, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := q)
  let Sf := Localization.Away f
  let Q := q.map (algebraMap S Sf)
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid S) : Set S) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfq
  haveI : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) Sf q inferInstance hdisj
  let p := Q.under (MvPolynomial (Fin n) K)
  haveI : p.IsPrime := Ideal.IsPrime.under _ Q
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  haveI : IsNoetherianRing Sf :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin n) K) Sf
  haveI : IsNoetherianRing (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallyUnramified (Localization.AtPrime p)
      (Localization.AtPrime Q) := by
    exact Algebra.FormallyUnramified.localization_base p.primeCompl
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin n) K)
      (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp (MvPolynomial (Fin n) K) Sf
      (Localization.AtPrime Q)
  haveI : Algebra.EssFiniteType (Localization.AtPrime p)
      (Localization.AtPrime Q) := Algebra.EssFiniteType.of_comp
        (MvPolynomial (Fin n) K) (Localization.AtPrime p)
        (Localization.AtPrime Q)
  haveI : IsRegularLocalRing (Localization.AtPrime Q) := by
    apply regularLocal_of_formallyUnramified_flat
      (Localization.AtPrime p) (Localization.AtPrime Q)
  have hunder : Q.under S = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) Sf inferInstance hdisj
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (.powers f) (Localization.AtPrime Q) Q
    exact hunder.symm
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime q)).toRingEquiv

/-- **Stacks 00TT** (`algebra-lemma-characterize-smooth-over-field`), final clause. If `S` is a
smooth algebra over a field `K` and `A` is a localization of `S` at a prime `q`, then `A` is a
regular local ring. -/
@[stacks 00TT]
theorem isRegularLocalRing_of_smooth_of_isLocalization_atPrime (K : Type u) (S : Type u)
    [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization.AtPrime A q] : IsRegularLocalRing A := by
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    regularAtPrime_of_smooth K S q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) A).toRingEquiv

/-- **Stacks 00TS** (`algebra-lemma-characterize-smooth-kbar`), the direction used by §3.1.
Over an algebraically closed field, a finitely presented algebra all of whose localizations at
primes are regular local rings is smooth.

This is the converse direction to `isRegularLocalRing_of_smooth_of_isLocalization_atPrime`
above. The proof identifies formal smoothness with the entire smooth locus, then applies the
regular-local direction of Stacks 00TV at every prime. Algebraic closedness makes the base
field perfect, so each essentially finite type residue-field extension is formally smooth. -/
@[stacks 00TS]
theorem smooth_of_isAlgClosed_of_forall_isRegularLocalRing (K : Type u) (S : Type u)
    [Field K] [IsAlgClosed K] [CommRing S] [Algebra K S] [Algebra.FinitePresentation K S]
    (h : ∀ (q : Ideal S) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.Smooth K S := by
  haveI : Algebra.FiniteType K S := inferInstance
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]
  ext q
  simp only [Set.mem_univ, iff_true]
  letI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := h q.asIdeal
  letI : Algebra.EssFiniteType K q.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K S q.asIdeal.ResidueField
  letI : Algebra.FormallySmooth K q.asIdeal.ResidueField := inferInstance
  exact Algebra.FormallySmooth.of_isRegularLocalRing_localization_atPrime K S q.asIdeal
