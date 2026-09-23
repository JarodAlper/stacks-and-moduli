module

public import Mathlib.Algebra.Colimit.Ring
public import StacksAndModuli.API.FlatLocusLocal
public import StacksAndModuli.API.TwistedFreeQuotKernelBaseChange

/-!
# Interface for relative flat spreading

This file gives a precise interface for the missing inputs in the relative flat-spreading
argument of Stacks Project tags 00RC and 02JO without asserting that they exist.

At the ring level, `HasFlatBasicNeighborhoods` is the basic-open-neighbourhood consequence
of openness of the relative flat locus.  Once it is available at every prime,
`HasFlatBasicNeighborhoods.flat_of_flat_localizationAtPrime` is exactly the already-proved
source-local gluing theorem.  `FiniteUnitIdealRelationsEventuallyDescend` isolates the final
finite relation in the quasi-compactness argument: a finite family whose images generate the
unit ideal in the limit already generates the unit ideal at a later stage.  This last step is
proved here for Mathlib's concrete ring direct limit, so it is not an additional blocker.

At the scheme level, `NoetherianTwistedFreeQuotSpreading` records a descended flat,
finitely-presented, fixed-Hilbert-polynomial quotient presentation together with its
base-change comparison.  The final theorem shows that affine-local witnesses of this form
supply the arbitrary-test-scheme kernel-generation premise used by the Quot-to-Grassmannian
construction.  In particular, the theorem does not hide an existence or approximation
claim: that claim is precisely its `H` hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Module.FinitePresentation

/-- The locus of primes of the source algebra at which the localized module is flat over
the coefficient ring. -/
def flatOverLocus
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    Set (PrimeSpectrum S) :=
  {q | Module.Flat R (Localization.AtPrime q.asIdeal ⊗[S] M)}

/-- The relative flat locus is open.  Under the usual finite-presentation hypotheses this
is the exact openness assertion needed in the spreading argument; this definition makes no
claim that the assertion holds. -/
def HasOpenFlatOverLocus
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] : Prop :=
  IsOpen (flatOverLocus (R := R) (S := S) (M := M))

/-- Every relatively flat localization at a prime of the source algebra has a basic-open
neighbourhood on which the original module is flat over the coefficient ring.  This is the
exact basic-neighbourhood interface supplied by openness of the relative flat locus. -/
def HasFlatBasicNeighborhoods
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] : Prop :=
  ∀ q : PrimeSpectrum S, q ∈ flatOverLocus (R := R) (S := S) (M := M) →
      ∃ f : S, f ∉ q.asIdeal ∧ Module.Flat R (LocalizedModule.Away f M)

/-- Openness of the relative flat locus supplies a flat basic-open neighbourhood at every
point of that locus. -/
theorem HasOpenFlatOverLocus.hasFlatBasicNeighborhoods
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hopen : HasOpenFlatOverLocus (R := R) (S := S) (M := M)) :
    HasFlatBasicNeighborhoods (R := R) (S := S) (M := M) := by
  intro q hq
  obtain ⟨V, hVsub, hVopen, hqV⟩ :=
    (isOpen_iff_forall_mem_open.mp hopen) q hq
  obtain ⟨W, ⟨f, rfl⟩, hqW, hWsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hVopen
  refine ⟨f, hqW, ?_⟩
  exact Module.Flat.away_of_forall_mem_basicOpen_flat_localizationAtPrime f
    fun q' hq' ↦ hWsub hq' |> hVsub

/-- A finite basic-open cover on each member of which the module is flat over the
coefficient ring. -/
def HasFiniteFlatBasicCover
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] : Prop :=
  ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
    ∀ f ∈ s, Module.Flat R (LocalizedModule.Away f M)

/-- Basic flat neighbourhoods turn flatness at every source prime into global relative
flatness. -/
theorem HasFlatBasicNeighborhoods.flat_of_flat_localizationAtPrime
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hnbhd : HasFlatBasicNeighborhoods (R := R) (S := S) (M := M))
    (hlocal : ∀ q : PrimeSpectrum S,
      Module.Flat R (Localization.AtPrime q.asIdeal ⊗[S] M)) :
    Module.Flat R M :=
  Module.Flat.of_forall_prime_exists_away fun q ↦ hnbhd q (hlocal q)

/-- A finite flat basic cover glues to global relative flatness. -/
theorem HasFiniteFlatBasicCover.flat
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hcover : HasFiniteFlatBasicCover (R := R) (S := S) (M := M)) :
    Module.Flat R M := by
  obtain ⟨s, hs, hflat⟩ := hcover
  apply Module.Flat.of_forall_prime_exists_away (R := R) (S := S) (M := M)
  intro q
  have hnot : ¬ (s : Set S) ⊆ q.asIdeal := by
    intro hsub
    have htop : (⊤ : Ideal S) ≤ q.asIdeal := by
      rw [← hs]
      exact Ideal.span_le.mpr hsub
    exact q.2.ne_top (top_unique htop)
  obtain ⟨f, hfs, hfq⟩ := Set.not_subset.mp hnot
  exact ⟨f, hfq, hflat f hfs⟩

end Module.FinitePresentation

namespace Ring.DirectLimit

/-- Finite unit-ideal relations in a proposed limit ring already hold at a later stage.

This is the finite-denominator-clearing endpoint used after quasi-compactness in the
relative flat-spreading argument.  Compatibility and the universal property of the maps
are deliberately not bundled here: this predicate states only the exact eventual relation
needed by that endpoint. -/
def FiniteUnitIdealRelationsEventuallyDescend
    {ι : Type u} [Preorder ι]
    (S : ι → Type v) [∀ i, CommRing (S i)]
    (transition : ∀ i j, i ≤ j → S i →+* S j)
    {A : Type w} [CommRing A] (toLimit : ∀ i, S i →+* A) : Prop :=
  ∀ (i : ι) (s : Finset (S i)),
    Ideal.span (toLimit i '' (s : Set (S i))) = ⊤ →
      ∃ (j : ι) (hij : i ≤ j),
        Ideal.span (transition i j hij '' (s : Set (S i))) = ⊤

open scoped Classical in
/-- Finite unit-ideal relations eventually descend in Mathlib's concrete direct limit of a
directed system of rings. -/
theorem finiteUnitIdealRelationsEventuallyDescend
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type v) [∀ i, CommRing (S i)]
    (transition : ∀ i j, i ≤ j → S i →+* S j)
    [DirectedSystem S fun i j h ↦ transition i j h] :
    FiniteUnitIdealRelationsEventuallyDescend S transition
      (fun i ↦ Ring.DirectLimit.of S (fun i j h ↦ transition i j h) i) := by
  intro i s hspan
  let L := Ring.DirectLimit S (fun i j h ↦ transition i j h)
  let toLimit : ∀ i, S i →+* L :=
    fun i ↦ Ring.DirectLimit.of S (fun i j h ↦ transition i j h) i
  let t : Finset L := s.image (toLimit i)
  have hspan' : Ideal.span (t : Set L) = ⊤ := by
    simpa only [t, Finset.coe_image] using hspan
  have hone : (1 : L) ∈ Ideal.span (t : Set L) :=
    (Ideal.eq_top_iff_one _).mp hspan'
  obtain ⟨c, _hcSupport, hc⟩ := Submodule.mem_span_finset.mp hone
  let pre (a : t) : S i := Classical.choose (Finset.mem_image.mp a.2)
  have pre_mem (a : t) : pre a ∈ s :=
    (Classical.choose_spec (Finset.mem_image.mp a.2)).1
  have pre_eq (a : t) : toLimit i (pre a) = a.1 :=
    (Classical.choose_spec (Finset.mem_image.mp a.2)).2
  let coeffStage (a : t) : ι := Classical.choose
    (Ring.DirectLimit.exists_of (G := S)
      (f := fun i j h ↦ transition i j h) (c a.1))
  let coeff (a : t) : S (coeffStage a) := Classical.choose (Classical.choose_spec
    (Ring.DirectLimit.exists_of (G := S)
      (f := fun i j h ↦ transition i j h) (c a.1)))
  have coeff_eq (a : t) : toLimit (coeffStage a) (coeff a) = c a.1 :=
    Classical.choose_spec (Classical.choose_spec
      (Ring.DirectLimit.exists_of (G := S)
        (f := fun i j h ↦ transition i j h) (c a.1)))
  let stages : Finset ι := {i} ∪ Finset.univ.image coeffStage
  obtain ⟨j, hj⟩ := Finset.exists_le stages
  have hij : i ≤ j := hj i (by simp [stages])
  have hcoeff (a : t) : coeffStage a ≤ j := by
    apply hj (coeffStage a)
    simp [stages]
  have coeff_later_eq (a : t) :
      toLimit j (transition (coeffStage a) j (hcoeff a) (coeff a)) = c a.1 := by
    rw [show toLimit j (transition (coeffStage a) j (hcoeff a) (coeff a)) =
      toLimit (coeffStage a) (coeff a) from
        Ring.DirectLimit.of_f (hcoeff a) (coeff a)]
    exact coeff_eq a
  have pre_later_eq (a : t) :
      toLimit j (transition i j hij (pre a)) = a.1 := by
    rw [show toLimit j (transition i j hij (pre a)) = toLimit i (pre a) from
      Ring.DirectLimit.of_f hij (pre a)]
    exact pre_eq a
  let y : S j := ∑ a : t,
    transition (coeffStage a) j (hcoeff a) (coeff a) *
      transition i j hij (pre a)
  have hy : toLimit j y = 1 := by
    calc
      toLimit j y = ∑ a : t, c a.1 * a.1 := by
        simp only [y, map_sum, map_mul, coeff_later_eq, pre_later_eq]
      _ = ∑ a ∈ t, c a * a := Finset.sum_coe_sort t (fun a ↦ c a * a)
      _ = 1 := by simpa only [smul_eq_mul] using hc
  have hyzero : toLimit j (y - 1) = 0 := by
    rw [map_sub, hy, map_one, sub_self]
  obtain ⟨k, hjk, hkzero⟩ := Ring.DirectLimit.of.zero_exact hyzero
  have hyk : transition j k hjk y = 1 := by
    exact sub_eq_zero.mp (by simpa only [map_sub, map_one] using hkzero)
  refine ⟨k, hij.trans hjk, ?_⟩
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hyk]
  dsimp only [y]
  rw [map_sum]
  apply Ideal.sum_mem
  intro a _ha
  rw [map_mul]
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  refine ⟨pre a, pre_mem a, ?_⟩
  exact (DirectedSystem.map_map' transition hij hjk (pre a)).symm

end Ring.DirectLimit

namespace AlgebraicGeometry.Scheme

/-- A noetherian model of one twisted-free Quot presentation, retaining precisely the
properties used by the uniform kernel-generation theorem and an identification after
base change.  This is witness data, not an assertion that such a model exists. -/
structure NoetherianTwistedFreeQuotSpreading
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ)
    {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) where
  /-- The locally noetherian coefficient scheme carrying the descended quotient. -/
  stage : Scheme.{u}
  /-- The descended stage is locally noetherian. -/
  stageLocallyNoetherian : IsLocallyNoetherian stage
  /-- The map from the original test scheme to the noetherian stage. -/
  map : T ⟶ stage
  /-- The descended quotient sheaf. -/
  model : (projectiveSpaceOver n stage).Modules
  /-- The descended quotient is finitely presented. -/
  modelFinitePresentation : model.IsFinitePresentation
  /-- The descended twisted-free quotient presentation. -/
  quotient : (∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n stage (-l)) ⟶ model
  /-- The descended presentation is a quotient. -/
  quotientEpi : Epi quotient
  /-- The descended quotient is flat over its coefficient scheme. -/
  modelFlat : model.FlatOver (projectiveSpaceOverπ n stage)
  /-- The descended quotient has the prescribed fibrewise Hilbert polynomial. -/
  modelHilbert : HasFiberwiseHilbertPolynomial model P
  /-- Pulling the descended quotient back recovers the original quotient. -/
  modelPullbackIso :
    (Modules.pullback (projectiveSpaceOverMap n map)).obj model ≅ Q
  /-- The quotient maps agree under the pullback identification. -/
  quotient_comp :
    projectiveSpaceTwistedFreeQuotientPullback n r map l quotient ≫
      modelPullbackIso.hom = q

/-- Kernel generation for a descended noetherian presentation propagates through the
base-change comparison recorded by a spreading witness. -/
theorem NoetherianTwistedFreeQuotSpreading.kernelIsGloballyGenerated
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ)
    {T : Scheme.{u}}
    {Q : (projectiveSpaceOver n T).Modules}
    {q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    (E : NoetherianTwistedFreeQuotSpreading n r l P Q q) (d : ℕ)
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated
      n E.stage l r E.quotient d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T l r q d := by
  letI : Epi E.quotient := E.quotientEpi
  have hbase : TwistedFreeQuotKernelIsGloballyGenerated n T l r
      (projectiveSpaceTwistedFreeQuotientPullback n r E.map l E.quotient) d :=
    TwistedFreeQuotKernelIsGloballyGenerated.pullback
      n r E.map l E.quotient d hgen
  have htransport : TwistedFreeQuotKernelIsGloballyGenerated n T l r
      (projectiveSpaceTwistedFreeQuotientPullback n r E.map l E.quotient ≫
        E.modelPullbackIso.hom) d :=
    TwistedFreeQuotKernelIsGloballyGenerated.comp_iso n r T l
      (projectiveSpaceTwistedFreeQuotientPullback n r E.map l E.quotient)
      E.modelPullbackIso d hbase
  rw [E.quotient_comp] at htransport
  exact htransport

/-- Every affine open of a test scheme carries a noetherian spreading witness for the
restricted twisted-free quotient.  Affineness and openness are explicit premises so that
the predicate also applies to covers other than the canonical affine cover. -/
def HasAffineLocalNoetherianTwistedFreeQuotSpreading
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ)
    {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) : Prop :=
  ∀ (U : Scheme.{u}) (g : U ⟶ T), IsAffine U → IsOpenImmersion g →
    Nonempty (NoetherianTwistedFreeQuotSpreading n r l P
      ((Modules.pullback (projectiveSpaceOverMap n g)).obj Q)
      (projectiveSpaceTwistedFreeQuotientPullback n r g l q))

/-- Family-level form of affine-local noetherian spreading for every fixed-polynomial Quot
datum over an arbitrary test scheme. -/
def HasUniversalAffineLocalNoetherianTwistedFreeQuotSpreading
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) (S : Scheme.{u}) : Prop :=
  ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      HasAffineLocalNoetherianTwistedFreeQuotSpreading n r l P
        (twistedFreeQuotientSheaf n S l r a)
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)

/-- Affine-local noetherian spreading supplies the arbitrary-test-scheme kernel-generation
premise with the same uniform bound as the locally noetherian theorem. -/
theorem
    exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_of_noetherianSpreading
    (n r : ℕ) (hn : 0 < n) (S : Scheme.{u}) (l : ℤ) (P : Polynomial ℚ)
    (H : HasUniversalAffineLocalNoetherianTwistedFreeQuotSpreading n r l P S) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d := by
  obtain ⟨D, hD⟩ :=
    exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_locallyNoetherian
      n r hn l P
  refine ⟨D, ?_⟩
  intro d hd T a hP
  let Q := twistedFreeQuotientSheaf n S l r a
  let q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  letI : Q.IsFinitePresentation :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over T a
  letI : Epi q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  apply TwistedFreeQuotKernelIsGloballyGenerated.of_openCover
    n r T.left.affineCover l q d
  intro i
  let U := T.left.affineCover.X i
  let g := T.left.affineCover.f i
  have hU : IsAffine U := inferInstance
  have hg : IsOpenImmersion g := inferInstance
  obtain ⟨E⟩ := H T a hP U g hU hg
  letI : IsLocallyNoetherian E.stage := E.stageLocallyNoetherian
  letI : E.model.IsFinitePresentation := E.modelFinitePresentation
  letI : Epi E.quotient := E.quotientEpi
  have hgen : TwistedFreeQuotKernelIsGloballyGenerated
      n E.stage l r E.quotient d :=
    hD d hd E.stage E.model E.quotient E.modelFlat E.modelHilbert
  exact E.kernelIsGloballyGenerated n r l P d hgen

end AlgebraicGeometry.Scheme

end

end
