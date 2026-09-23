module

public import StacksAndModuli.API.RelativeFlatSpreadingInterface
public import
  StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Assembly of a flat coefficient model from persistent basic stages

This file isolates the remaining relative flat-spreading input in Stacks Project tag 02JO
for a module presented over a polynomial ring.  The predicate
`HasPrimewisePersistentFlatBasicStages` says exactly that every prime of the limit polynomial
ring has a basic neighbourhood which is flat at every later coefficient stage.  No existence
claim for these neighbourhoods is made here; obtaining them is the unresolved 00RC/02JO
openness-and-spreading step.

The theorem
`exists_flatCoefficientModel_of_primewise_persistent_flatBasicStages` proves all subsequent
assembly.  It extracts finitely many basic neighbourhoods, moves them to one common stage,
descends their unit-ideal relation to a later stage, glues flatness there, and constructs the
`FlatCoefficientModel` required by the existing polynomial-presentation API.

For the canonical coefficient stages of one `PolynomialModel`, flat basic localizations
automatically persist under stage extension.  Thus the residual geometric input is only the
existence of one flat basic neighbourhood at some canonical stage over each limit prime.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe uR u v

namespace Module.FinitePresentation.PolynomialModel

open TensorProduct

variable {R : Type uR} {A M : Type u} {σ : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module (MvPolynomial σ A) M]

/-- Flatness over the coefficient ring on one basic open of a polynomial coefficient model.

The localized module carries the canonical coefficient action induced from the polynomial
cokernel.  This is the action used by the source-local flatness theorem. -/
def IsFlatOnBasicCoefficientModel
    {B : Type u} [CommRing B] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ B))
    (f : MvPolynomial σ B) : Prop :=
  let N := polynomialMatrixCokernel G
  let L := LocalizedModule.Away f N
  Module.Flat B L

/-- The explicit restriction-of-scalars action on a polynomial matrix cokernel agrees with
its canonical coefficient-module action. -/
theorem compHom_polynomialMatrixCokernel_eq
    {B : Type u} [CommRing B] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ B)) :
    Module.compHom (polynomialMatrixCokernel G)
        (algebraMap B (MvPolynomial σ B)) =
      (inferInstance : Module B (polynomialMatrixCokernel G)) := by
  apply Module.ext'
  intro b x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (algebraMap B (MvPolynomial σ B) b) •
        (Submodule.Quotient.mk x : polynomialMatrixCokernel G) =
      b • (Submodule.Quotient.mk x : polynomialMatrixCokernel G)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    apply congrArg (fun y : Fin n → MvPolynomial σ B =>
      (Submodule.Quotient.mk y : polynomialMatrixCokernel G))
    exact IsScalarTower.algebraMap_smul (MvPolynomial σ B) b x

/-- Primewise persistent flat basic stages for a directed system of polynomial coefficient
models.

For every prime of the limit polynomial ring, an element occurs at some stage, avoids that
prime in the limit, and gives a flat basic localization after every later transition.  This is
the precise local callback left by the 00RC/02JO argument.  Persistence is included because
the quasi-compactness assembly must move finitely many independently chosen neighbourhoods to
one common stage. -/
def HasPrimewisePersistentFlatBasicStages
    {ι : Type u} [Preorder ι]
    (B : ι → Subalgebra R A)
    {m n : ℕ}
    (G : ∀ i, Matrix (Fin n) (Fin m) (MvPolynomial σ (B i)))
    (transition : ∀ i j, i ≤ j →
      MvPolynomial σ (B i) →+* MvPolynomial σ (B j))
    (toLimit : ∀ i, MvPolynomial σ (B i) →+* MvPolynomial σ A) : Prop :=
  ∀ q : PrimeSpectrum (MvPolynomial σ A),
    ∃ (i : ι) (f : MvPolynomial σ (B i)),
      toLimit i f ∉ q.asIdeal ∧
        ∀ j (hij : i ≤ j),
          IsFlatOnBasicCoefficientModel (G j) (transition i j hij f)

/-- Persistent primewise flat basic stages assemble to one globally flat coefficient model.

The other hypotheses are structural data of the directed presentation system.  In
particular, `hunit` is not a flatness assumption: it is the finite unit-ideal relation supplied
for Mathlib's concrete ring direct limit by
`Ring.DirectLimit.finiteUnitIdealRelationsEventuallyDescend`. -/
theorem exists_flatCoefficientModel_of_primewise_persistent_flatBasicStages
    (D : PolynomialModel A σ M)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (B : ι → Subalgebra R A) (hBfg : ∀ i, (B i).FG)
    (G : ∀ i, Matrix (Fin D.generators) (Fin D.relations)
      (MvPolynomial σ (B i)))
    (hGmap : ∀ i, (G i).map
      (MvPolynomial.map (algebraMap (B i) A)) = LinearMap.toMatrix' D.relation)
    (transition : ∀ i j, i ≤ j →
      MvPolynomial σ (B i) →+* MvPolynomial σ (B j))
    (toLimit : ∀ i, MvPolynomial σ (B i) →+* MvPolynomial σ A)
    (hcompat : ∀ i j (hij : i ≤ j) f,
      toLimit j (transition i j hij f) = toLimit i f)
    (htransition_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) f,
      transition j k hjk (transition i j hij f) =
        transition i k (hij.trans hjk) f)
    (hunit : Ring.DirectLimit.FiniteUnitIdealRelationsEventuallyDescend
      (fun i ↦ MvPolynomial σ (B i)) transition toLimit)
    (hprime : HasPrimewisePersistentFlatBasicStages B G transition toLimit) :
    Nonempty (FlatCoefficientModel (R := R) D) := by
  classical
  let good : Set (MvPolynomial σ A) :=
    {a | ∃ (i : ι) (f : MvPolynomial σ (B i)),
      toLimit i f = a ∧ ∀ j (hij : i ≤ j),
        IsFlatOnBasicCoefficientModel (G j) (transition i j hij f)}
  have hgoodSpan : Ideal.span good = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span good) hne
    let q : PrimeSpectrum (MvPolynomial σ A) := ⟨m, hm.isPrime⟩
    obtain ⟨i, f, hfq, hlater⟩ := hprime q
    exact hfq (hle (Ideal.subset_span ⟨i, f, rfl, hlater⟩))
  obtain ⟨t, htgood, htspan⟩ :=
    (Ideal.span_eq_top_iff_finite good).mp hgoodSpan
  let stage (a : t) : ι := Classical.choose (htgood a.2)
  let element (a : t) : MvPolynomial σ (B (stage a)) :=
    Classical.choose (Classical.choose_spec (htgood a.2))
  have element_eq (a : t) : toLimit (stage a) (element a) = a.1 :=
    (Classical.choose_spec (Classical.choose_spec (htgood a.2))).1
  have element_later (a : t) (j : ι) (haj : stage a ≤ j) :
      IsFlatOnBasicCoefficientModel (G j)
        (transition (stage a) j haj (element a)) :=
    (Classical.choose_spec (Classical.choose_spec (htgood a.2))).2 j haj
  let stages : Finset ι := Finset.univ.image stage
  obtain ⟨j, hj⟩ := Finset.exists_le stages
  have hstage (a : t) : stage a ≤ j := by
    apply hj (stage a)
    simp [stages]
  let s : Finset (MvPolynomial σ (B j)) :=
    Finset.univ.image fun a : t ↦ transition (stage a) j (hstage a) (element a)
  have hspanLimit :
      Ideal.span (toLimit j '' (s : Set (MvPolynomial σ (B j)))) = ⊤ := by
    apply top_unique
    rw [← htspan]
    apply Ideal.span_mono
    intro a ha
    let a' : t := ⟨a, ha⟩
    refine ⟨transition (stage a') j (hstage a') (element a'), ?_, ?_⟩
    · simp [s]
    · rw [hcompat, element_eq]
  obtain ⟨k, hjk, hkspan⟩ := hunit j s hspanLimit
  let sK : Finset (MvPolynomial σ (B k)) := s.image (transition j k hjk)
  have hsKspan : Ideal.span (sK : Set (MvPolynomial σ (B k))) = ⊤ := by
    simpa only [sK, Finset.coe_image] using hkspan
  have hsKflat : ∀ f ∈ sK, IsFlatOnBasicCoefficientModel (G k) f := by
    intro f hfsK
    obtain ⟨g, hgs, rfl⟩ := Finset.mem_image.mp hfsK
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hgs
    rw [htransition_comp]
    exact element_later a k ((hstage a).trans hjk)
  have hkflatDefault : Module.Flat (B k) (polynomialMatrixCokernel (G k)) := by
    apply Module.Flat.of_forall_prime_exists_away
      (R := B k) (S := MvPolynomial σ (B k))
      (M := polynomialMatrixCokernel (G k))
    intro q
    have hnot : ¬ (sK : Set (MvPolynomial σ (B k))) ⊆ q.asIdeal := by
      intro hsub
      have htop : (⊤ : Ideal (MvPolynomial σ (B k))) ≤ q.asIdeal := by
        rw [← hsKspan]
        exact Ideal.span_le.mpr hsub
      exact q.2.ne_top (top_unique htop)
    obtain ⟨f, hfs, hfq⟩ := Set.not_subset.mp hnot
    exact ⟨f, hfq, hsKflat f hfs⟩
  have hkflat :
      let Nk := polynomialMatrixCokernel (G k)
      letI : Module (B k) Nk :=
        Module.compHom Nk (algebraMap (B k) (MvPolynomial σ (B k)))
      Module.Flat (B k) Nk := by
    dsimp only
    rw [compHom_polynomialMatrixCokernel_eq]
    exact hkflatDefault
  exact ⟨{
    coefficientRing := B k
    coefficientRing_fg := hBfg k
    relation := G k
    relation_map := hGmap k
    flat := hkflat
  }⟩

/-! ## The canonical finitely generated coefficient-stage system -/

/-- Finitely generated coefficient subalgebras which contain all coefficients of a fixed
polynomial presentation. -/
abbrev CoefficientStage (D : PolynomialModel A σ M) :=
  {B : Subalgebra R A // B.FG ∧ D.coefficientRing (R := R) ≤ B}

instance (D : PolynomialModel A σ M) :
    Nonempty (CoefficientStage (R := R) D) :=
  ⟨⟨D.coefficientRing (R := R), D.coefficientRing_fg, le_rfl⟩⟩

instance (D : PolynomialModel A σ M) :
    IsDirectedOrder (CoefficientStage (R := R) D) where
  directed i j := by
    let k : CoefficientStage (R := R) D :=
      ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, i.2.2.trans le_sup_left⟩
    exact ⟨k,
      show i.1 ≤ k.1 from le_sup_left,
      show j.1 ≤ k.1 from le_sup_right⟩

/-- The polynomial-ring map induced by inclusion of two canonical coefficient stages. -/
noncomputable def coefficientStageTransition (D : PolynomialModel A σ M)
    (i j : CoefficientStage (R := R) D) (h : i ≤ j) :
    MvPolynomial σ i.1 →+* MvPolynomial σ j.1 :=
  MvPolynomial.map (Subalgebra.inclusion h)

/-- The polynomial-ring map from a canonical coefficient stage to the original coefficient
ring. -/
noncomputable def coefficientStageToLimit (D : PolynomialModel A σ M)
    (i : CoefficientStage (R := R) D) :
    MvPolynomial σ i.1 →+* MvPolynomial σ A :=
  MvPolynomial.map (algebraMap i.1 A)

/-- The relation matrix of a polynomial presentation at a canonical coefficient stage. -/
noncomputable def coefficientStageRelation (D : PolynomialModel A σ M)
    (i : CoefficientStage (R := R) D) :
    Matrix (Fin D.generators) (Fin D.relations) (MvPolynomial σ i.1) :=
  (D.modelRelation (R := R)).map
    (MvPolynomial.map (Subalgebra.inclusion i.2.2))

/-- Polynomial transition maps commute with the maps to the original coefficient ring. -/
theorem coefficientStageToLimit_transition (D : PolynomialModel A σ M)
    (i j : CoefficientStage (R := R) D) (h : i ≤ j)
    (f : MvPolynomial σ i.1) :
    coefficientStageToLimit D j (coefficientStageTransition D i j h f) =
      coefficientStageToLimit D i f := by
  change MvPolynomial.map (algebraMap j.1 A)
      (MvPolynomial.map (Subalgebra.inclusion h) f) =
    MvPolynomial.map (algebraMap i.1 A) f
  rw [MvPolynomial.map_map]
  congr 1

/-- Polynomial transition maps compose. -/
theorem coefficientStageTransition_comp (D : PolynomialModel A σ M)
    (i j k : CoefficientStage (R := R) D) (hij : i ≤ j) (hjk : j ≤ k)
    (f : MvPolynomial σ i.1) :
    coefficientStageTransition D j k hjk
        (coefficientStageTransition D i j hij f) =
      coefficientStageTransition D i k (hij.trans hjk) f := by
  rw [coefficientStageTransition, coefficientStageTransition,
    coefficientStageTransition, MvPolynomial.map_map]
  congr 1

/-- Canonical relation matrices commute with coefficient-stage transition maps. -/
theorem coefficientStageRelation_transition (D : PolynomialModel A σ M)
    (i j : CoefficientStage (R := R) D) (hij : i ≤ j) :
    (coefficientStageRelation D i).map (coefficientStageTransition D i j hij) =
      coefficientStageRelation D j := by
  rw [coefficientStageRelation, coefficientStageRelation]
  ext a b
  simp only [Matrix.map_apply, coefficientStageTransition, MvPolynomial.map_map]
  congr 1

/-- The polynomial matrix cokernel at a later canonical coefficient stage is the scalar
extension of the cokernel at an earlier stage. -/
noncomputable def coefficientStageModelBaseChangeEquiv
    (D : PolynomialModel A σ M)
    (i j : CoefficientStage (R := R) D) (hij : i ≤ j) :
    letI : Algebra i.1 j.1 := (Subalgebra.inclusion hij).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial σ i.1) (MvPolynomial σ j.1) :=
      MvPolynomial.algebraMvPolynomial
    (MvPolynomial σ j.1) ⊗[MvPolynomial σ i.1]
        polynomialMatrixCokernel (coefficientStageRelation D i) ≃ₗ[
      MvPolynomial σ j.1]
        polynomialMatrixCokernel (coefficientStageRelation D j) := by
  let Sj := MvPolynomial σ j.1
  let Gj := coefficientStageRelation D j
  let gj : (Fin D.relations → Sj) →ₗ[Sj] (Fin D.generators → Sj) :=
    Matrix.toLin' Gj
  let fj : (Fin D.generators → Sj) →ₗ[Sj] polynomialMatrixCokernel Gj :=
    (LinearMap.range gj).mkQ
  letI : Algebra i.1 j.1 := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial σ i.1) Sj :=
    MvPolynomial.algebraMvPolynomial
  apply polynomialPresentationBaseChangeEquivOfMap fj gj
    (coefficientStageRelation D i)
  · rw [show algebraMap i.1 j.1 = (Subalgebra.inclusion hij).toRingHom from rfl]
    change (coefficientStageRelation D i).map
        (coefficientStageTransition D i j hij) = LinearMap.toMatrix' gj
    rw [coefficientStageRelation_transition]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix']
  · exact Submodule.mkQ_surjective _
  · rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _

/-- The map between away localizations induced by a canonical coefficient-stage
transition. -/
noncomputable def coefficientStageAwayTransition
    (D : PolynomialModel A σ M)
    (i j : CoefficientStage (R := R) D) (hij : i ≤ j)
    (f : MvPolynomial σ i.1) :
    Localization.Away f →+*
      Localization.Away (coefficientStageTransition D i j hij f) :=
  Localization.awayMap (coefficientStageTransition D i j hij) f

/-- Every canonical stage relation matrix maps to the original relation matrix. -/
theorem coefficientStageRelation_map (D : PolynomialModel A σ M)
    (i : CoefficientStage (R := R) D) :
    (coefficientStageRelation D i).map
        (MvPolynomial.map (algebraMap i.1 A)) =
      LinearMap.toMatrix' D.relation := by
  have hmap : (algebraMap i.1 A).comp (Subalgebra.inclusion i.2.2) =
      algebraMap (D.coefficientRing (R := R)) A := by
    apply RingHom.ext
    intro x
    rfl
  rw [coefficientStageRelation]
  calc
    ((D.modelRelation (R := R)).map
          (MvPolynomial.map (Subalgebra.inclusion i.2.2))).map
        (MvPolynomial.map (algebraMap i.1 A)) =
        (D.modelRelation (R := R)).map
          (MvPolynomial.map
            ((algebraMap i.1 A).comp (Subalgebra.inclusion i.2.2))) := by
      ext a b
      simp only [Matrix.map_apply, MvPolynomial.map_map]
    _ = LinearMap.toMatrix' D.relation := by
      rw [hmap]
      exact D.modelRelation_map

/-- Finite unit-ideal relations descend in the canonical coefficient-stage system.

The proof adjoins the finitely many coefficients of one unit-ideal relation to the current
stage.  Since every stage embeds into `A`, the lifted relation already equals one at that
stage; unlike an abstract direct-limit proof, no further equality-detection stage is needed. -/
theorem coefficientStages_finiteUnitIdealRelationsEventuallyDescend
    (D : PolynomialModel A σ M) :
    Ring.DirectLimit.FiniteUnitIdealRelationsEventuallyDescend
      (fun i : CoefficientStage (R := R) D ↦ MvPolynomial σ i.1)
      (coefficientStageTransition D) (coefficientStageToLimit D) := by
  classical
  intro i s hspan
  let image : Finset (MvPolynomial σ A) :=
    s.image (coefficientStageToLimit D i)
  have hspan' : Ideal.span (image : Set (MvPolynomial σ A)) = ⊤ := by
    simpa only [image, Finset.coe_image] using hspan
  have hone : (1 : MvPolynomial σ A) ∈
      Ideal.span (image : Set (MvPolynomial σ A)) :=
    (Ideal.eq_top_iff_one _).mp hspan'
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hone
  let coeffs : Set A := ⋃ a : image, (c a).coeffs
  let C : Subalgebra R A := Algebra.adjoin R coeffs
  have hCfg : C.FG := by
    apply Subalgebra.fg_def.mpr
    refine ⟨coeffs, ?_, rfl⟩
    exact Set.finite_iUnion fun a : image ↦ Finset.finite_toSet (c a).coeffs
  let j : CoefficientStage (R := R) D :=
    ⟨i.1 ⊔ C, i.2.1.sup hCfg, i.2.2.trans le_sup_left⟩
  have hij : i ≤ j := show i.1 ≤ j.1 from le_sup_left
  have hcoeffs (a : image) : ((c a).coeffs : Set A) ⊆
      Set.range (algebraMap j.1 A) := by
    rw [Subalgebra.setRange_algebraMap]
    intro x hx
    exact (show C ≤ j.1 from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_iUnion_of_mem a hx))
  let coeff (a : image) : MvPolynomial σ j.1 :=
    Classical.choose
      (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (hcoeffs a))
  have coeff_eq (a : image) : coefficientStageToLimit D j (coeff a) = c a :=
    Classical.choose_spec
      (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (hcoeffs a))
  let pre (a : image) : MvPolynomial σ i.1 :=
    Classical.choose (Finset.mem_image.mp a.2)
  have pre_mem (a : image) : pre a ∈ s :=
    (Classical.choose_spec (Finset.mem_image.mp a.2)).1
  have pre_eq (a : image) : coefficientStageToLimit D i (pre a) = a.1 :=
    (Classical.choose_spec (Finset.mem_image.mp a.2)).2
  let y : MvPolynomial σ j.1 := ∑ a : image,
    coeff a * coefficientStageTransition D i j hij (pre a)
  have hyMap : coefficientStageToLimit D j y = 1 := by
    calc
      coefficientStageToLimit D j y = ∑ a : image, c a * a.1 := by
        simp only [y, map_sum, map_mul, coeff_eq,
          coefficientStageToLimit_transition, pre_eq]
      _ = 1 := by simpa only [smul_eq_mul] using hc
  have hmapInjective : Function.Injective (coefficientStageToLimit D j) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  have hy : y = 1 := hmapInjective (by simpa only [map_one] using hyMap)
  refine ⟨j, hij, ?_⟩
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hy]
  dsimp only [y]
  apply Ideal.sum_mem
  intro a _ha
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  exact ⟨pre a, pre_mem a, rfl⟩

/-- The sole flatness callback for the canonical coefficient-stage system.

This specializes `HasPrimewisePersistentFlatBasicStages` to the stages, transition maps, and
compatible relation matrices canonically determined by `D`. -/
def HasPersistentFlatCoefficientNeighborhoods
    (D : PolynomialModel A σ M) : Prop :=
  HasPrimewisePersistentFlatBasicStages
    (fun i : CoefficientStage (R := R) D ↦ i.1)
    (coefficientStageRelation D)
    (coefficientStageTransition D)
    (coefficientStageToLimit D)

/-- Every flat basic localization at one canonical coefficient stage stays flat after
passing to a later stage.

This is the purely algebraic base-change compatibility needed to turn a one-stage
primewise witness into the persistent witness used by quasi-compactness. -/
def FlatBasicCoefficientNeighborhoodsPersist
    (D : PolynomialModel A σ M) : Prop :=
  ∀ (i j : CoefficientStage (R := R) D) (hij : i ≤ j)
    (f : MvPolynomial σ i.1),
    IsFlatOnBasicCoefficientModel (coefficientStageRelation D i) f →
      IsFlatOnBasicCoefficientModel (coefficientStageRelation D j)
        (coefficientStageTransition D i j hij f)

set_option maxHeartbeats 800000 in
-- The proof explicitly assembles two nested pushout squares and their module base changes.
set_option synthInstance.maxHeartbeats 100000 in
/-- Flat basic localizations persist under extension between canonical coefficient stages. -/
theorem flatBasicCoefficientNeighborhoodsPersist
    (D : PolynomialModel A σ M) :
    FlatBasicCoefficientNeighborhoodsPersist (R := R) D := by
  intro i j hij f hflat
  unfold IsFlatOnBasicCoefficientModel at hflat
  let Ni₀ := polynomialMatrixCokernel (coefficientStageRelation D i)
  let Nj₀ := polynomialMatrixCokernel (coefficientStageRelation D j)
  let Li₀ := LocalizedModule.Away f Ni₀
  let Lj₀ := LocalizedModule.Away (coefficientStageTransition D i j hij f) Nj₀
  let modBiLi₀ : Module i.1 Li₀ := inferInstance
  let modBjLj₀ : Module j.1 Lj₀ := inferInstance
  change @Module.Flat i.1 Li₀ _ _ modBiLi₀ at hflat
  letI : Algebra i.1 j.1 := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  let Si := MvPolynomial σ i.1
  let Sj := MvPolynomial σ j.1
  let Ai := Localization.Away f
  let fj := coefficientStageTransition D i j hij f
  let Aj := Localization.Away fj
  let algSiSj : Algebra Si Sj := MvPolynomial.algebraMvPolynomial
  letI : Algebra Si Sj := algSiSj
  letI : SMul Si Sj := algSiSj.toSMul
  let algSiAi : Algebra Si Ai := inferInstance
  letI : Algebra Si Ai := algSiAi
  letI : SMul Si Ai := algSiAi.toSMul
  let algSjAj : Algebra Sj Aj := inferInstance
  letI : Algebra Sj Aj := algSjAj
  letI : SMul Sj Aj := algSjAj.toSMul
  let algSiAj : Algebra Si Aj := Algebra.compHom Aj (algebraMap Si Sj)
  letI : Algebra Si Aj := algSiAj
  letI : SMul Si Aj := algSiAj.toSMul
  let algAiAj : Algebra Ai Aj :=
    (coefficientStageAwayTransition D i j hij f).toAlgebra
  letI : Algebra Ai Aj := algAiAj
  letI : SMul Ai Aj := algAiAj.toSMul
  have hpolyMap : algebraMap Si Sj = coefficientStageTransition D i j hij := rfl
  letI : IsScalarTower Si Sj Aj :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Si Ai Aj :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ by
      change algebraMap Sj Aj (algebraMap Si Sj x) =
        coefficientStageAwayTransition D i j hij f (algebraMap Si Ai x)
      symm
      change coefficientStageAwayTransition D i j hij f (algebraMap Si Ai x) =
        algebraMap Sj Aj (coefficientStageTransition D i j hij x)
      rw [coefficientStageAwayTransition, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq])
  have hsub : Algebra.algebraMapSubmonoid Sj (Submonoid.powers f) =
      Submonoid.powers fj := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, hpolyMap]
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid Sj (Submonoid.powers f)) Aj :=
    hsub.symm ▸ inferInstance
  haveI : Algebra.IsPushout Si Sj Ai Aj :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers f) Ai Sj Aj
  -- The coefficient rings form the outer pushout square.
  let Bi := i.1
  let Bj := j.1
  let algBiBj : Algebra Bi Bj := (Subalgebra.inclusion hij).toRingHom.toAlgebra
  letI : Algebra Bi Bj := algBiBj
  letI : SMul Bi Bj := algBiBj.toSMul
  let algBiSi : Algebra Bi Si := inferInstance
  letI : Algebra Bi Si := algBiSi
  letI : SMul Bi Si := algBiSi.toSMul
  let algBjSj : Algebra Bj Sj := inferInstance
  letI : Algebra Bj Sj := algBjSj
  letI : SMul Bj Sj := algBjSj.toSMul
  let algBiAi : Algebra Bi Ai := Algebra.compHom Ai (algebraMap Bi Si)
  letI : Algebra Bi Ai := algBiAi
  letI : SMul Bi Ai := algBiAi.toSMul
  let algBjAj : Algebra Bj Aj := Algebra.compHom Aj (algebraMap Bj Sj)
  letI : Algebra Bj Aj := algBjAj
  letI : SMul Bj Aj := algBjAj.toSMul
  let algBiSj : Algebra Bi Sj := Algebra.compHom Sj (algebraMap Bi Bj)
  letI : Algebra Bi Sj := algBiSj
  letI : SMul Bi Sj := algBiSj.toSMul
  let algBiAj : Algebra Bi Aj := Algebra.compHom Aj (algebraMap Bi Bj)
  letI : Algebra Bi Aj := algBiAj
  letI : SMul Bi Aj := algBiAj.toSMul
  letI : IsScalarTower Bi Bj Sj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Bi Si Sj := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change MvPolynomial.C (algebraMap Bi Bj x) =
      MvPolynomial.map (algebraMap Bi Bj) (MvPolynomial.C x)
    exact (MvPolynomial.map_C _ x).symm)
  letI : IsScalarTower Bi Si Ai := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Bj Sj Aj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Bi Bj Aj := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Bi Sj Aj := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change algebraMap Bj Aj (algebraMap Bi Bj x) =
      algebraMap Sj Aj (algebraMap Bj Sj (algebraMap Bi Bj x))
    rw [← IsScalarTower.algebraMap_apply Bj Sj Aj])
  letI : IsScalarTower Bi Si Aj := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    rw [IsScalarTower.algebraMap_apply Bi Sj Aj,
      IsScalarTower.algebraMap_apply Bi Si Sj,
      IsScalarTower.algebraMap_apply Si Sj Aj])
  letI : IsScalarTower Bi Ai Aj := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    rw [IsScalarTower.algebraMap_apply Bi Si Aj,
      IsScalarTower.algebraMap_apply Bi Si Ai,
      IsScalarTower.algebraMap_apply Si Ai Aj])
  haveI : Algebra.IsPushout Bi Si Bj Sj := inferInstance
  have houter : Algebra.IsPushout Bi Ai Bj Aj :=
    (Algebra.IsPushout.comp_iff Bi Si Bj Sj).mpr
      (Algebra.IsPushout.symm
        (show Algebra.IsPushout Si Sj Ai Aj from inferInstance))
  haveI : Algebra.IsPushout Bi Bj Ai Aj :=
    Algebra.IsPushout.symm houter
  -- The stage cokernels and their localizations are successive base changes.
  let Ni := polynomialMatrixCokernel (coefficientStageRelation D i)
  let Nj := polynomialMatrixCokernel (coefficientStageRelation D j)
  let Li := LocalizedModule.Away f Ni
  let Lj := LocalizedModule.Away fj Nj
  letI : Module Si Nj := Module.compHom Nj (algebraMap Si Sj)
  letI : IsScalarTower Si Sj Nj := IsScalarTower.of_compHom Si Sj Nj
  let eN : Sj ⊗[Si] Ni ≃ₗ[Sj] Nj :=
    coefficientStageModelBaseChangeEquiv D i j hij
  let u : Ni →ₗ[Si] Nj :=
    (eN.toLinearMap.restrictScalars Si).comp (TensorProduct.mk Si Sj Ni 1)
  have hu : IsBaseChange Sj u := by
    apply IsBaseChange.of_equiv eN
    intro x
    simp [u, eN]
  let mi : Ni →ₗ[Si] Li :=
    LocalizedModule.mkLinearMap (Submonoid.powers f) Ni
  have hmi : IsBaseChange Ai mi := by
    exact LocalizedModule.isBaseChange (Submonoid.powers f) Ni
  let mj : Nj →ₗ[Sj] Lj :=
    LocalizedModule.mkLinearMap (Submonoid.powers fj) Nj
  have hmj : IsBaseChange Aj mj := by
    exact LocalizedModule.isBaseChange (Submonoid.powers fj) Nj
  -- The composite base-change map factors through the first localization.
  let modSiLj : Module Si Lj := Module.compHom Lj (algebraMap Si Sj)
  letI : Module Si Lj := modSiLj
  letI : SMul Si Lj := modSiLj.toSMul
  letI : IsScalarTower Si Sj Lj := IsScalarTower.of_compHom Si Sj Lj
  let modAiLj : Module Ai Lj := Module.compHom Lj (algebraMap Ai Aj)
  letI : Module Ai Lj := modAiLj
  letI : SMul Ai Lj := modAiLj.toSMul
  letI : IsScalarTower Ai Aj Lj := IsScalarTower.of_compHom Ai Aj Lj
  letI : IsScalarTower Si Aj Lj := IsScalarTower.to₁₃₄ Si Sj Aj Lj
  letI : IsScalarTower Si Ai Lj := IsScalarTower.to₁₂₄ Si Ai Aj Lj
  let g : Ni →ₗ[Si] Lj := (mj.restrictScalars Si).comp u
  have hg : IsBaseChange Aj g := hu.comp hmj
  let h : Li →ₗ[Ai] Lj := hmi.lift g
  have hh : IsBaseChange Aj h := by
    apply IsBaseChange.of_comp hmi
    simpa only [h, hmi.lift_comp] using hg
  let eL : Aj ⊗[Ai] Li ≃ₗ[Aj] Lj := hh.equiv
  let modBiLi : Module Bi Li := modBiLi₀
  letI : Module Bi Li := modBiLi
  letI : SMul Bi Li := modBiLi.toSMul
  letI : IsScalarTower Bi Si Li := inferInstance
  letI : IsScalarTower Bi Ai Li := IsScalarTower.to₁₃₄ Bi Si Ai Li
  haveI : Module.Flat Bi Li := hflat
  let modAiAj : Module Ai Aj := algAiAj.toModule
  letI : Module Ai Aj := modAiAj
  letI : SMul Ai Aj := modAiAj.toSMul
  letI : DistribMulAction Ai Aj := modAiAj.toDistribMulAction
  let modBjAj : Module Bj Aj := algBjAj.toModule
  letI : Module Bj Aj := modBjAj
  letI : SMul Bj Aj := modBjAj.toSMul
  letI : DistribMulAction Bj Aj := modBjAj.toDistribMulAction
  letI : SMulCommClass Ai Bj Aj :=
    ⟨fun a b x ↦ by
      simp only [Algebra.smul_def]
      ac_rfl⟩
  let modBjTensor : Module Bj (Aj ⊗[Ai] Li) := TensorProduct.leftModule
  letI : Module Bj (Aj ⊗[Ai] Li) := modBjTensor
  letI : SMul Bj (Aj ⊗[Ai] Li) := modBjTensor.toSMul
  letI : IsScalarTower Bj Aj (Aj ⊗[Ai] Li) :=
    TensorProduct.isScalarTower_left
  have hbase : Module.Flat Bj (Aj ⊗[Ai] Li) :=
    Module.Flat.baseChange_of_isPushout Bi Bj Ai Aj Li
  let modBjLj : Module Bj Lj := modBjLj₀
  letI : Module Bj Lj := modBjLj
  letI : SMul Bj Lj := modBjLj.toSMul
  letI : IsScalarTower Bj Sj Lj := inferInstance
  letI : IsScalarTower Bj Aj Lj := IsScalarTower.to₁₃₄ Bj Sj Aj Lj
  exact Module.Flat.of_linearEquiv (eL.symm.restrictScalars Bj)

/-- A flat basic-neighbourhood witness at one canonical coefficient stage for every prime
of the limit polynomial ring.  Unlike `HasPersistentFlatCoefficientNeighborhoods`, this
predicate does not build base-change persistence into the witness. -/
def HasPrimewiseFlatCoefficientNeighborhoods
    (D : PolynomialModel A σ M) : Prop :=
  ∀ q : PrimeSpectrum (MvPolynomial σ A),
    ∃ (i : CoefficientStage (R := R) D) (f : MvPolynomial σ i.1),
      coefficientStageToLimit D i f ∉ q.asIdeal ∧
        IsFlatOnBasicCoefficientModel (coefficientStageRelation D i) f

/-- One-stage primewise flat neighbourhoods become persistent when flat basic localizations
are compatible with coefficient-stage base change. -/
theorem HasPrimewiseFlatCoefficientNeighborhoods.persistent
    (D : PolynomialModel A σ M)
    (hpersist : FlatBasicCoefficientNeighborhoodsPersist (R := R) D)
    (hprime : HasPrimewiseFlatCoefficientNeighborhoods (R := R) D) :
    HasPersistentFlatCoefficientNeighborhoods (R := R) D := by
  intro q
  obtain ⟨i, f, hfq, hflat⟩ := hprime q
  exact ⟨i, f, hfq, fun j hij ↦ hpersist i j hij f hflat⟩

/-- Persistent flat basic neighbourhoods in the canonical coefficient system produce a flat
coefficient model.  This is the one-callback form of the remaining 00RC/02JO bridge. -/
theorem exists_flatCoefficientModel_of_persistent_flatCoefficientNeighborhoods
    (D : PolynomialModel A σ M)
    (hflat : HasPersistentFlatCoefficientNeighborhoods (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) := by
  apply exists_flatCoefficientModel_of_primewise_persistent_flatBasicStages
    D (fun i : CoefficientStage (R := R) D ↦ i.1)
      (fun i ↦ i.2.1) (coefficientStageRelation D)
      (coefficientStageRelation_map D) (coefficientStageTransition D)
      (coefficientStageToLimit D) (coefficientStageToLimit_transition D)
      (coefficientStageTransition_comp D)
      (coefficientStages_finiteUnitIdealRelationsEventuallyDescend D)
      hflat

/-- One-stage primewise flat neighbourhoods and their algebraic persistence under
coefficient extension produce a flat coefficient model. -/
theorem exists_flatCoefficientModel_of_primewise_flatCoefficientNeighborhoods
    (D : PolynomialModel A σ M)
    (hpersist : FlatBasicCoefficientNeighborhoodsPersist (R := R) D)
    (hprime : HasPrimewiseFlatCoefficientNeighborhoods (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  D.exists_flatCoefficientModel_of_persistent_flatCoefficientNeighborhoods
    (hprime.persistent D hpersist)

/-- One-stage primewise flat basic neighbourhoods produce a flat coefficient model; their
persistence under canonical coefficient extension is automatic. -/
theorem HasPrimewiseFlatCoefficientNeighborhoods.exists_flatCoefficientModel
    (D : PolynomialModel A σ M)
    (hprime : HasPrimewiseFlatCoefficientNeighborhoods (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  D.exists_flatCoefficientModel_of_primewise_flatCoefficientNeighborhoods
    (flatBasicCoefficientNeighborhoodsPersist D) hprime

end Module.FinitePresentation.PolynomialModel

end

end
