module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFibre
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianVeryAmple
public import StacksAndModuli.API.FreeQuotientRankBound

/-!
# Conditional endpoint package for the Quot-to-Grassmannian construction

This file gathers the independent geometric inputs to the canonical fixed-degree
Quot-to-Grassmannian construction into one interface.  Fixed-rank projectivity, canonical
pushforward base change, and affine surjectivity construct the intrinsic natural
transformation.  Reconstruction reflection and finite immersed fibre loci then make it a
relative immersion.  The resulting package simultaneously supplies the twisted-free W6
predicate and relative very ampleness of the determinant of the fixed-degree universal
pushforward on every representative of the Quot functor.

The numerical field `rank_le` is explicit: without a point of the Quot functor, the rank
inequality cannot in general be recovered from the other universally quantified fields.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A single fixed-polynomial family over a nonempty test scheme forces the target rank
of the intrinsic monomial quotient to lie in the finite-free source rank.  Keeping this
deduction separate is essential for arbitrary polynomials: if the Quot functor is empty,
the corresponding numerical inequality need not hold. -/
theorem TwistedFreeQuotGrassmannianQuotientNatTransData.rank_le_of_nonempty_family
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
    {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hP : a.HasFiberwiseHilbertPolynomial P) (hT : Nonempty T.left) :
    q ≤ m := by
  let x : Modules.FreeQuotient q (ULift.{u} (Fin m)) T.left :=
    twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ
      (D.isProjectiveOfRank T a hP) (D.surjective T a hP)
  let y : Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) T :=
    Modules.PullbackQuotient.ofFreeQuotient x
  exact y.rank_le_of_nonempty hT

/-- The rank, canonical base-change, affine-generation, and numerical inputs which
construct the intrinsic fixed-degree Quot-to-Grassmannian natural transformation. -/
structure TwistedFreeQuotGrassmannianCanonicalInputs
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m q : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Type (u + 1) where
  /-- Every fixed-polynomial family has the prescribed rank in degree `d`. -/
  isProjectiveOfRank : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      Modules.IsProjectiveOfRank q
        (twistedFreeQuotientTwistPushforward n S l r a d)
  /-- The canonical fixed-degree pushforward base-change morphism is invertible. -/
  baseChange_isIso : ∀ {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      IsIso (twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d)
  /-- The normalized monomial map is surjective on every affine open. -/
  surjective : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      ∀ U : T.left.affineOpens, Function.Surjective
        (Modules.finFreeSectionsMap'
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)
  /-- The quotient rank lies in the nonempty range of the free Grassmannian. -/
  rank_le : q ≤ m

namespace TwistedFreeQuotGrassmannianCanonicalInputs

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The canonical base-change data.  Its monomial compatibility field is supplied by
formal naturality, so the only input retained here is invertibility of canonical CBC. -/
noncomputable def baseChangeData
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ) :
    TwistedFreeQuotGrassmannianCanonicalBaseChangeData
      n S l r P d e he m σ :=
  .ofBaseChange I.baseChange_isIso

/-- The intrinsic strict-quotient natural-transformation data constructed from the
canonical inputs. -/
noncomputable def natTransData
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ) :
    TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ :=
  .ofCanonicalBaseChange I.isProjectiveOfRank I.surjective I.baseChangeData

end TwistedFreeQuotGrassmannianCanonicalInputs

/-- All independent hypotheses needed to close the canonical twisted-free
Quot-to-Grassmannian immersion and determinant-very-ampleness argument. -/
structure TwistedFreeQuotGrassmannianCanonicalPackage
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m q : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    : Type (u + 1)
    extends TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ where
  /-- The degree-`d` free quotient detects equivalence of the original Quot data. -/
  reflectsQuotientEquivalence :
    toTwistedFreeQuotGrassmannianCanonicalInputs.natTransData.ReflectsQuotientEquivalence
  /-- Every fibre of the canonical natural transformation has a finite immersed-locus
  presentation. -/
  finiteFibreLoci : HasFiniteImmersionFibreLoci
    toTwistedFreeQuotGrassmannianCanonicalInputs.natTransData.natTrans

namespace TwistedFreeQuotGrassmannianCanonicalPackage

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The canonical intrinsic natural-transformation data carried by the package. -/
noncomputable def natTransData
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ) :
    TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ :=
  C.toTwistedFreeQuotGrassmannianCanonicalInputs.natTransData

/-- The packaged canonical natural transformation is relatively representable by
immersions. -/
theorem relative_isImmersion
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) C.natTransData.natTrans := by
  exact C.natTransData.relative_isImmersion_of_reflection_finiteFibreLoci
    C.reflectsQuotientEquivalence C.finiteFibreLoci

/-- The package closes the exact twisted-free free-Grassmannian immersion predicate. -/
theorem w6
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P := by
  exact
    twistedFreeQuotHasFreeGrassmannianImmersion_of_quotientNatTrans_reflection_finiteFibreLoci
      C.rank_le C.natTransData C.reflectsQuotientEquivalence C.finiteFibreLoci

/-- On any representative of the Quot functor, the determinant of the normalized
fixed-degree universal pushforward is relatively very ample. -/
theorem determinant_isRelativelyVeryAmple
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ)
    {Q : Over S}
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower
        (twistedFreeQuotientTwistPushforward n S l r
          (h.homEquiv (CategoryStruct.id Q)).1.out d) q) := by
  exact
    C.natTransData.isRelativelyVeryAmple_exteriorPower_twistedFreeUniversalPushforward
      C.relative_isImmersion h

/-- The combined endpoint: the same canonical package supplies both the twisted-free W6
predicate and determinant relative very ampleness on every representative. -/
theorem w6_and_determinant_isRelativelyVeryAmple
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ)
    {Q : Over S}
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P ∧
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          (twistedFreeQuotientTwistPushforward n S l r
            (h.homEquiv (CategoryStruct.id Q)).1.out d) q) :=
  ⟨C.w6, C.determinant_isRelativelyVeryAmple h⟩

end TwistedFreeQuotGrassmannianCanonicalPackage

end AlgebraicGeometry.Scheme

end

end
