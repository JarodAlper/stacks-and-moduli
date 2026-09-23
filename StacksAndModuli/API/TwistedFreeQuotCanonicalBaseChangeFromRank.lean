module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianArbitrarySurjectivity
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# Canonical base change from universal fixed-rank projectivity

The monomial map attached to a twisted-free Quot presentation is compatible with the
canonical pushforward base-change morphism without any cohomological hypothesis.  This
file uses that square in the converse direction: once every fixed-degree pushforward is a
vector bundle of one fixed rank, surjectivity of the monomial map over residue fields
forces the canonical base-change map over those fields to be bijective.  Affine Nakayama
then descends monomial generation to an arbitrary base.

This isolates the part of canonical Cohomology and Base Change that follows formally from
the uniform rank theorem and the field-valued regularity theorem.  The remaining input is
the arbitrary-base uniform rank theorem itself.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open _root_.AlgebraicGeometry.ProjectiveSpace

set_option synthInstance.maxHeartbeats 1000000 in
-- Residue-field normalization creates nested pullback and twist instances.
set_option maxHeartbeats 3000000 in
-- The rank comparison transports two vector bundles through a canonical base-change square.
/-- A universal fixed-rank theorem removes the arbitrary-base hypothesis from monomial
generation.  Over a closed residue fibre the classical noetherian generation theorem makes
the monomial map surjective.  Its factorization through the canonical base-change map makes
that map surjective; equality of the two fixed ranks makes it bijective, so the original
residue pullback of the monomial map is surjective as well. -/
theorem
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_universalRank
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m q : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      (∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          Scheme.Modules.IsProjectiveOfRank q
            (Scheme.twistedFreeQuotientTwistPushforward n S l r a d)) →
      ∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          ∀ U : T.left.affineOpens,
            Function.Surjective (Scheme.Modules.finFreeSectionsMap'
              (Scheme.twistedFreeQuotGrassmannianFreeMap
                n S l r a d e he σ) U.1) := by
  obtain ⟨d₁, hd₁0, hfield⟩ :=
    Scheme.ProjectiveSpace.exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap.{u}
      n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro S d e he hd m q σ hRank T a hP U
  let p := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  let M := Scheme.twistedFreeQuotientTwistPushforward n S l r a d
  letI : M.IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  apply Scheme.Modules.finFreeSectionsMap'_surjective_of_geometric_residue_pullbacks_of_rank
    p (hRank T a hP) U
  intro I hI
  let κ := Γ(T.left, U.1) ⧸ I
  letI : Field κ := @Ideal.Quotient.field _ _ I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f := k ≫ (j ≫ i)
  let Tκ : Over S := Over.mk (f ≫ T.hom)
  let g : Tκ ⟶ T := Over.homMk f rfl
  let aκ := a.pullback g
  let pκ := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r aκ d e he σ
  let β := Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d
  let freeIso := Scheme.Modules.pullbackFreeIso f (ULift.{u} (Fin m))
  have hPκ : aκ.HasFiberwiseHilbertPolynomial P :=
    a.hasFiberwiseHilbertPolynomial_pullback g hP
  haveI : IsAffine Tκ.left := by
    change IsAffine (Spec (.of κ))
    infer_instance
  haveI : IsLocallyNoetherian Tκ.left := by
    change IsLocallyNoetherian (Spec (.of κ))
    infer_instance
  have hpκ' : ∀ V : Tκ.left.affineOpens, Function.Surjective
      (Scheme.Modules.finFreeSectionsMap' pκ V.1) :=
    hfield S Tκ aκ hPκ d e he hd σ
  have hpκ : Function.Surjective (Scheme.Modules.Hom.app pκ ⊤) := by
    let V : Tκ.left.affineOpens := ⟨⊤, isAffineOpen_top Tκ.left⟩
    exact Scheme.Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective
      pκ hpκ' V
  have hsq :
      (Scheme.Modules.pullback f).map p ≫ β = freeIso.hom ≫ pκ := by
    rw [← cancel_epi freeIso.inv]
    simp only [Iso.inv_hom_id_assoc]
    change (Scheme.Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Scheme.Modules.pullback g.left).map
          (Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      Scheme.twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ
    exact Scheme.twistedFreeQuotGrassmannianFreeMap_baseChange
      n S l r g a d e he σ
  let source := (Scheme.Modules.pullback f).obj M
  let target := Scheme.twistedFreeQuotientTwistPushforward n S l r aκ d
  have hsource : Scheme.Modules.IsProjectiveOfRank q source := by
    exact (hRank T a hP).pullback f
  have htarget : Scheme.Modules.IsProjectiveOfRank q target := hRank Tκ aκ hPκ
  letI : Inhabited Tκ.left := by
    change Inhabited (Spec (.of κ))
    infer_instance
  letI : Subsingleton Tκ.left := by
    change Subsingleton (Spec (.of κ))
    infer_instance
  let t : Tκ.left := default
  obtain ⟨Us, hts, hfins, hprojs, hranks⟩ := hsource t
  obtain ⟨Ut, htt, hfint, hprojt, hrankt⟩ := htarget t
  have hUs : Us.1 = ⊤ := by
    apply top_unique
    intro x _
    rw [show x = t from Subsingleton.elim _ _]
    exact hts
  have hUt : Ut.1 = ⊤ := by
    apply top_unique
    intro x _
    rw [show x = t from Subsingleton.elim _ _]
    exact htt
  rw [hUs] at hfins hprojs hranks
  rw [hUt] at hfint hprojt hrankt
  have hright : Function.Surjective
      (Scheme.Modules.Hom.app (freeIso.hom ≫ pκ) ⊤) := by
    change Function.Surjective
      ((Scheme.Modules.Hom.app pκ ⊤) ∘ (Scheme.Modules.Hom.app freeIso.hom ⊤))
    exact hpκ.comp (ConcreteCategory.bijective_of_isIso
      (Scheme.Modules.Hom.app freeIso.hom ⊤)).2
  have hleft : Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map p ≫ β) ⊤) := by
    rw [hsq]
    exact hright
  have hcomp : Function.Surjective
      ((Scheme.Modules.Hom.app β ⊤) ∘
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map p) ⊤)) := by
    change Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map p ≫ β) ⊤)
    exact hleft
  have hβsurj : Function.Surjective (Scheme.Modules.Hom.app β ⊤) :=
    Function.Surjective.of_comp hcomp
  letI : Module.Finite Γ(Tκ.left, ⊤) Γ(source, ⊤) := hfins
  letI : Module.Projective Γ(Tκ.left, ⊤) Γ(source, ⊤) := hprojs
  letI : Module.Flat Γ(Tκ.left, ⊤) Γ(source, ⊤) := Module.Flat.of_projective
  letI : Module.Finite Γ(Tκ.left, ⊤) Γ(target, ⊤) := hfint
  letI : Module.Projective Γ(Tκ.left, ⊤) Γ(target, ⊤) := hprojt
  letI : Module.Flat Γ(Tκ.left, ⊤) Γ(target, ⊤) := Module.Flat.of_projective
  let ψ : Γ(source, ⊤) →ₗ[Γ(Tκ.left, ⊤)] Γ(target, ⊤) :=
    { toFun := Scheme.Modules.Hom.app β ⊤
      map_add' := map_add _
      map_smul' := fun c x ↦ Scheme.Modules.Hom.app_smul β c x }
  have hψsurj : Function.Surjective ψ := hβsurj
  have hψbij : Function.Bijective ψ :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hψsurj fun J _ ↦
      (hranks ⟨J, inferInstance⟩).trans (hrankt ⟨J, inferInstance⟩).symm
  exact Function.Surjective.of_comp_left hcomp hψbij.1

set_option synthInstance.maxHeartbeats 1000000 in
-- Pullback coherence creates deeply nested quasicoherent-sheaf instances.
set_option maxHeartbeats 3000000 in
/-- A universal fixed-rank theorem forces the canonical pushforward base-change map to
be an isomorphism.  Arbitrary-base monomial generation makes the monomial map after base
change an epimorphism.  Its compatibility square factors this epimorphism through the
canonical base-change map, which is therefore itself epi; the two sides are vector bundles
of the same rank, so the epi is an isomorphism. -/
theorem
    exists_bound_twistedFreeQuotientTwistPushforwardBaseChange_isIso_of_universalRank
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (_he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m q : ℕ}
        (_σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      (∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          Scheme.Modules.IsProjectiveOfRank q
            (Scheme.twistedFreeQuotientTwistPushforward n S l r a d)) →
      ∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          ∀ (T' : Over S) (g : T' ⟶ T),
            IsIso (Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom
              n S l r g a d) := by
  obtain ⟨d₁, hd₁0, hgen⟩ :=
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_universalRank
      n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro S d e he hd m q σ hRank T a hP T' g
  let a' := a.pullback g
  let p := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  let p' := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a' d e he σ
  let β := Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d
  let freeIso := Scheme.Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))
  letI : (Scheme.twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  letI : (Scheme.twistedFreeQuotientTwistPushforward n S l r a' d).IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a' d
  letI : ((Scheme.Modules.pullback g.left).obj
      (Scheme.twistedFreeQuotientTwistPushforward n S l r a d)).IsQuasicoherent := by
    infer_instance
  have hP' : a'.HasFiberwiseHilbertPolynomial P :=
    a.hasFiberwiseHilbertPolynomial_pullback g hP
  have hp'fin : ∀ U : T'.left.affineOpens,
      Function.Surjective (Scheme.Modules.finFreeSectionsMap' p' U.1) :=
    hgen S d e he hd σ hRank T' a' hP'
  have hp' : ∀ U : T'.left.affineOpens,
      Function.Surjective (Scheme.Modules.Hom.app p' U.1) :=
    Scheme.Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective p' hp'fin
  letI : Epi p' := Scheme.Modules.epi_of_surjective_on_affineOpens p' hp'
  have hsq :
      (Scheme.Modules.pullback g.left).map p ≫ β = freeIso.hom ≫ p' := by
    rw [← cancel_epi freeIso.inv]
    simp only [Iso.inv_hom_id_assoc]
    change (Scheme.Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Scheme.Modules.pullback g.left).map
          (Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      Scheme.twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ
    exact Scheme.twistedFreeQuotGrassmannianFreeMap_baseChange
      n S l r g a d e he σ
  have hcomp : Epi ((Scheme.Modules.pullback g.left).map p ≫ β) := by
    rw [hsq]
    infer_instance
  letI : Epi ((Scheme.Modules.pullback g.left).map p ≫ β) := hcomp
  letI : Epi β := epi_of_epi ((Scheme.Modules.pullback g.left).map p) β
  have hsource : Scheme.Modules.IsProjectiveOfRank q
      ((Scheme.Modules.pullback g.left).obj
        (Scheme.twistedFreeQuotientTwistPushforward n S l r a d)) :=
    (hRank T a hP).pullback g.left
  have htarget : Scheme.Modules.IsProjectiveOfRank q
      (Scheme.twistedFreeQuotientTwistPushforward n S l r a' d) :=
    hRank T' a' hP'
  exact Scheme.Modules.isIso_of_epi_of_isProjectiveOfRank hsource htarget β

set_option synthInstance.maxHeartbeats 1000000 in
-- The free-map sheaf and fixed-rank pushforward carry nested normalized-Quot instances.
set_option maxHeartbeats 2000000 in
/-- Under the same universal fixed-rank input, the Hilbert rank cannot exceed the number
of monomial generators whenever the chosen test scheme is nonempty. -/
theorem
    exists_bound_twistedFreeQuot_pushforward_rank_le_monomial_count_of_universalRank
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (_he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m q : ℕ}
        (_σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      (∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          Scheme.Modules.IsProjectiveOfRank q
            (Scheme.twistedFreeQuotientTwistPushforward n S l r a d)) →
      ∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P → Nonempty T.left → q ≤ m := by
  obtain ⟨d₁, hd₁0, hgen⟩ :=
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_universalRank
      n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro S d e he hd m q σ hRank T a hP hT
  let p := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  let M := Scheme.twistedFreeQuotientTwistPushforward n S l r a d
  letI : M.IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  have hsurj : ∀ U : T.left.affineOpens,
      Function.Surjective (Scheme.Modules.finFreeSectionsMap' p U.1) :=
    hgen S d e he hd σ hRank T a hP
  letI : Epi p := Scheme.Modules.epi_of_surjective_on_affineOpens p
    (Scheme.Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective p hsurj)
  exact (hRank T a hP).rank_le_of_epi_finFree p hT

/-- The uniform relative-perfectness input specialized to normalized twisted-free Quot
families over one base scheme.  It asks for the affine strictly-perfect replacements used
by `exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_of_strictlyPerfectReplacement`
for every point of the fixed-Hilbert-polynomial Quot functor. -/
def HasUniversallyAffineStrictlyPerfectTwistedFreeQuotCechReplacement
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) (S : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ (T : Over S)
    (a : Scheme.Modules.QuotientPullbackData
      (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (Scheme.projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      HasAffineStrictlyPerfectTwistedFreeQuotCechReplacement n r l
        (Scheme.twistedFreeQuotientSheaf n S l r a)
        (Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) d

set_option synthInstance.maxHeartbeats 1000000 in
-- This combines three independent uniform bounds and normalizes every raw Quot datum.
set_option maxHeartbeats 4000000 in
/-- A universal affine strictly-perfect replacement theorem supplies all intrinsic
fixed-degree natural-transformation data: rank, arbitrary-base monomial generation, and
canonical pushforward base change.  The rank is the value prescribed by the Hilbert
polynomial. -/
theorem
    exists_bound_twistedFreeQuotGrassmannianQuotientNatTransData_of_strictlyPerfectReplacement
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₀ ≤ (d : ℤ) →
      ∀ {m : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      HasUniversallyAffineStrictlyPerfectTwistedFreeQuotCechReplacement
          n r l P S d →
        Nonempty (Scheme.TwistedFreeQuotGrassmannianQuotientNatTransData
          n S l r P d e he m (P.hilbertNatValue d) σ) := by
  obtain ⟨dRank, hdRank0, hRank⟩ :=
    exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_of_strictlyPerfectReplacement
      n r hn l P
  obtain ⟨dGen, hdGen0, hGen⟩ :=
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_universalRank
      n r l P
  obtain ⟨dBC, hdBC0, hBC⟩ :=
    exists_bound_twistedFreeQuotientTwistPushforwardBaseChange_isIso_of_universalRank
      n r l P
  refine ⟨max dRank (max dGen dBC), by omega, ?_⟩
  intro S d e he hd m σ hperfect
  have hdRank : dRank ≤ (d : ℤ) := le_trans (le_max_left _ _) hd
  have hdGen : dGen ≤ (d : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hdBC : dBC ≤ (d : ℤ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hM : ∀ (T : Over S)
      (a : Scheme.Modules.QuotientPullbackData
        (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (Scheme.projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
          (Scheme.twistedFreeQuotientTwistPushforward n S l r a d) := by
    intro T a hP
    let Q := Scheme.twistedFreeQuotientSheaf n S l r a
    let q :=
      Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
    haveI : Q.IsFinitePresentation :=
      Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over
        T a
    haveI : Epi q :=
      Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
    have hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n T.left) :=
      Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over T a
    exact hRank T.left Q (by infer_instance) q (by infer_instance)
      hflat hP d hdRank (hperfect T a hP)
  have hsurj := hGen S d e he hdGen σ hM
  have hbaseChange := hBC S d e he hdBC σ hM
  exact ⟨Scheme.TwistedFreeQuotGrassmannianQuotientNatTransData.ofCanonicalBaseChange
    hM hsurj
    (Scheme.TwistedFreeQuotGrassmannianCanonicalBaseChangeData.ofBaseChange
      (fun {T T'} g a hP ↦ hbaseChange T a hP T' g))⟩

end AlgebraicGeometry.ProjectiveSpace

end

end
