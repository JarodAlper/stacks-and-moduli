module

public import StacksAndModuli.API.ProjectiveFlatteningOneStepBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Canonical base change for one-step projective multiplication

The base-change comparison for the two adjacent twisted pushforwards in a one-step
projective flattening problem is canonical: it is the mate of the pullback--pushforward
counit, followed by the canonical comparison between pullback and twisting.  This file
shows that these canonical maps automatically intertwine multiplication by the degree-one
monomials.  Consequently, once the two adjacent canonical maps are isomorphisms, they
assemble into `ProjectiveOneStepMultiplicationBaseChangeComparison`; no separate
multiplication-coherence hypothesis is needed.

This isolates the substantive Cohomology-and-Base-Change input for a reconstructed
Grassmannian family: invertibility of the canonical maps in degrees `d` and `d + 1`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {W X Y : Scheme.{u}}

/-- Naturality of the canonical comparison between an iterated pullback and pullback
along an equal composite. -/
lemma pullbackCompCongrIso_hom_naturality
    (f : W ⟶ X) (ρ : X ⟶ Y) (g : W ⟶ Y) (h : f ≫ ρ = g)
    {M N : Y.Modules} (m : M ⟶ N) :
    (pullback f).map ((pullback ρ).map m) ≫
        ((pullbackComp f ρ).hom.app N ≫ (pullbackCongr h).hom.app N) =
      ((pullbackComp f ρ).hom.app M ≫ (pullbackCongr h).hom.app M) ≫
        (pullback g).map m := by
  let cM := (pullbackComp f ρ).hom.app M
  let cN := (pullbackComp f ρ).hom.app N
  let kM := (pullbackCongr h).hom.app M
  let kN := (pullbackCongr h).hom.app N
  have hc :
      (pullback f).map ((pullback ρ).map m) ≫ cN =
        cM ≫ (pullback (f ≫ ρ)).map m :=
    (pullbackComp f ρ).hom.naturality m
  have hk :
      (pullback (f ≫ ρ)).map m ≫ kN =
        kM ≫ (pullback g).map m :=
    (pullbackCongr h).hom.naturality m
  calc
    (pullback f).map ((pullback ρ).map m) ≫ (cN ≫ kN) =
        ((pullback f).map ((pullback ρ).map m) ≫ cN) ≫ kN :=
      (Category.assoc _ _ _).symm
    _ = (cM ≫ (pullback (f ≫ ρ)).map m) ≫ kN :=
      congrArg (fun q ↦ q ≫ kN) hc
    _ = cM ≫ ((pullback (f ≫ ρ)).map m ≫ kN) :=
      Category.assoc _ _ _
    _ = cM ≫ (kM ≫ (pullback g).map m) :=
      congrArg (fun q ↦ cM ≫ q) hk
    _ = (cM ≫ kM) ≫ (pullback g).map m :=
      (Category.assoc _ _ _).symm

/-- The canonical pushforward base-change mate is natural in the sheaf. -/
lemma pushforwardBaseChangeHomOfComm_naturality
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) {M N : X.Modules} (m : M ⟶ N) :
    (pullback g).map ((pushforward p).map m) ≫
        pushforwardBaseChangeHomOfComm p p' g G h N =
      pushforwardBaseChangeHomOfComm p p' g G h M ≫
        (pushforward p').map ((pullback G).map m) := by
  let adj := pullbackPushforwardAdjunction p'
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_naturality_right_symm]
  dsimp only [pushforwardBaseChangeHomOfComm]
  dsimp only [adj]
  simp only [Equiv.symm_apply_apply]
  let q := (pushforward p).map m
  let cM := (pullbackComp p' g).hom.app ((pushforward p).obj M)
  let cN := (pullbackComp p' g).hom.app ((pushforward p).obj N)
  let kM := (pullbackCongr h.symm).hom.app ((pushforward p).obj M)
  let kN := (pullbackCongr h.symm).hom.app ((pushforward p).obj N)
  let aM := (pullbackComp G p).inv.app ((pushforward p).obj M)
  let aN := (pullbackComp G p).inv.app ((pushforward p).obj N)
  let εM := (pullbackPushforwardAdjunction p).counit.app M
  let εN := (pullbackPushforwardAdjunction p).counit.app N
  have hc : (pullback p').map ((pullback g).map q) ≫ cN =
      cM ≫ (pullback (p' ≫ g)).map q := by
    simpa only [cM, cN, q, Functor.comp_map] using
      (pullbackComp p' g).hom.naturality q
  have hk : (pullback (p' ≫ g)).map q ≫ kN =
      kM ≫ (pullback (G ≫ p)).map q :=
    (pullbackCongr h.symm).hom.naturality q
  have ha : (pullback (G ≫ p)).map q ≫ aN =
      aM ≫ (pullback G).map ((pullback p).map q) := by
    simpa only [aM, aN, q, Functor.comp_map] using
      (pullbackComp G p).inv.naturality q
  have hε : (pullback p).map q ≫ εN = εM ≫ m := by
    simpa only [q, εM, εN, Functor.comp_map, Functor.id_map] using
      (pullbackPushforwardAdjunction p).counit.naturality m
  change (pullback p').map ((pullback g).map q) ≫ cN ≫ kN ≫ aN ≫
      (pullback G).map εN =
    cM ≫ kM ≫ aM ≫ (pullback G).map εM ≫ (pullback G).map m
  slice_lhs 1 2 => rw [hc]
  slice_lhs 2 3 => rw [hk]
  slice_lhs 3 4 => rw [ha]
  slice_lhs 4 5 => rw [← (pullback G).map_comp, hε,
    (pullback G).map_comp]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pullback of a relative monomial multiplication is the corresponding monomial
multiplication on the base-changed relative projective space. -/
lemma twistMonomialMulHom_pullback
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) (a b : ℤ) (e : ℕ)
    (hb : b = a + (e : ℤ)) (i : Fin ((n + e).choose n)) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (twistMonomialMulHom n S a b e hb i) ≫
        (projectiveSpaceOverTwist_pullbackIso n g b).hom =
      (projectiveSpaceOverTwist_pullbackIso n g a).hom ≫
        twistMonomialMulHom n T a b e hb i := by
  let ρS : projectiveSpaceOver n S ⟶ projectiveSpace n := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let ρT : projectiveSpaceOver n T ⟶ projectiveSpace n := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let m : ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) a ⟶
      ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) b :=
    ProjectiveSpectrum.Twist.mulHom
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i)
      a b hb
  have h := Modules.pullbackCompCongrIso_hom_naturality
    (projectiveSpaceOverMap n g) ρS ρT
    (projectiveSpaceOverMap_absolute_snd n g) m
  simpa only [twistMonomialMulHom, projectiveSpaceOverTwist_pullbackIso,
    Iso.trans_hom, Iso.app_hom, ρS, ρT, m] using h

namespace Modules

/-- The canonical twist-module pullback comparison intertwines multiplication by a
degree-one monomial. -/
lemma projectiveTwistMulOne_pullback
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S)
    (Q : (projectiveSpaceOver n S).Modules) (d : ℕ)
    (i : Fin ((n + 1).choose n)) :
    (pullback (projectiveSpaceOverMap n g)).map
          (projectiveTwistMulOne n Q d i) ≫
        (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q (d + 1)).hom =
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d).hom ≫
        projectiveTwistMulOne n
          ((pullback (projectiveSpaceOverMap n g)).obj Q) d i := by
  unfold projectiveTwistMulOne
  dsimp only [projectiveSpaceOverTwistModule_pullbackIso_nat, Iso.trans_hom,
    tensorRightIso, projectiveSpaceOverTwistModule]
  simp only [asIso_hom]
  rw [← Category.assoc, pullbackTensorComparison_naturality_right,
    Category.assoc, Category.assoc, ← tensorMapRight_comp,
    ← tensorMapRight_comp]
  exact congrArg
    (fun ψ ↦ pullbackTensorComparison (projectiveSpaceOverMap n g) Q
          (projectiveSpaceOverTwist n S (d : ℤ)) ≫
        tensorMapRight
          ((pullback (projectiveSpaceOverMap n g)).obj Q) ψ)
    (twistMonomialMulHom_pullback n g (d : ℤ)
      ((d + 1 : ℕ) : ℤ) 1 (by omega) i)

/-- The canonical base-change morphism for a twisted projective pushforward.  It is
the pushforward base-change mate followed by the natural-degree twist comparison. -/
noncomputable def projectiveTwistedPushforwardBaseChangeHom
    (n : ℕ) {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ⟶
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d :=
  pushforwardBaseChangeHomOfComm
      (projectiveSpaceOverπ n T)
      (projectiveSpaceOverπ n A.left) A.hom
      (projectiveSpaceOverMap n A.hom)
      (projectiveSpaceOverMap_π n A.hom)
      (projectiveSpaceOverTwistModule Q (d : ℤ)) ≫
    (pushforward (projectiveSpaceOverπ n A.left)).map
      (projectiveSpaceOverTwistModule_pullbackIso_nat n A.hom Q d).hom

/-- The canonical twisted-pushforward base-change maps intertwine each individual
degree-one monomial multiplication map. -/
lemma projectiveTwistedPushforwardBaseChangeHom_mulOne
    (n : ℕ) {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) (A : Over T)
    (i : Fin ((n + 1).choose n)) :
    (pullback A.hom).map
          ((pushforward (projectiveSpaceOverπ n T)).map
            (projectiveTwistMulOne n Q d i)) ≫
        projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A =
      projectiveTwistedPushforwardBaseChangeHom n Q d A ≫
        (pushforward (projectiveSpaceOverπ n A.left)).map
          (projectiveTwistMulOne n (projectiveFamilyAt n Q A) d i) := by
  unfold projectiveTwistedPushforwardBaseChangeHom
  rw [← Category.assoc, pushforwardBaseChangeHomOfComm_naturality]
  simp only [Category.assoc]
  rw [← (pushforward (projectiveSpaceOverπ n A.left)).map_comp,
    projectiveTwistMulOne_pullback,
    (pushforward (projectiveSpaceOverπ n A.left)).map_comp]

/-- The canonical twisted-pushforward base-change maps intertwine the full degree-one
multiplication map.  Invertibility is needed only in degree `d`, to package the
termwise comparison as the canonical coproduct isomorphism. -/
lemma projectiveTwistedPushforwardBaseChangeHom_mul
    (n : ℕ) {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) (A : Over T)
    [IsIso (projectiveTwistedPushforwardBaseChangeHom n Q d A)] :
    (pullback A.hom).map (projectiveTwistedPushforwardMul n Q d) ≫
        projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A =
      (projectiveOneStepMultiplicationSourceBaseChangeIso n Q d A
        (asIso (projectiveTwistedPushforwardBaseChangeHom n Q d A))).hom ≫
        projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d := by
  let e := asIso (projectiveTwistedPushforwardBaseChangeHom n Q d A)
  let E := projectiveOneStepMultiplicationSourceBaseChangeIso n Q d A e
  change (pullback A.hom).map (projectiveTwistedPushforwardMul n Q d) ≫
      projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A =
    E.hom ≫
      projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d
  rw [← cancel_epi E.inv]
  simp only [Iso.inv_hom_id_assoc]
  apply Sigma.hom_ext
  intro i
  have hι : Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) i ≫
        E.inv =
      e.inv ≫ (pullback A.hom).map
        (Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n Q d) i) := by
    dsimp only [E, projectiveOneStepMultiplicationSourceBaseChangeIso,
      Iso.trans_inv]
    rw [Sigma.ι_mapIso_inv_assoc, PreservesCoproduct.inv_hom,
      ι_comp_sigmaComparison]
  change Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) i ≫
        E.inv ≫ (pullback A.hom).map
          (projectiveTwistedPushforwardMul n Q d) ≫
        projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A =
      Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) i ≫
        projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d
  slice_lhs 1 2 => rw [hι]
  unfold projectiveTwistedPushforwardMul
  rw [Category.assoc]
  slice_lhs 2 3 => rw [← (pullback A.hom).map_comp, Sigma.ι_desc]
  slice_lhs 2 3 =>
    rw [projectiveTwistedPushforwardBaseChangeHom_mulOne]
  rw [Sigma.ι_desc]
  change e.inv ≫ e.hom ≫
      (pushforward (projectiveSpaceOverπ n A.left)).map
        (projectiveTwistMulOne n (projectiveFamilyAt n Q A) d i) = _
  simp

/-- Canonical Cohomology-and-Base-Change in one twist degree, uniformly over all test
schemes over the base. -/
def ProjectiveTwistedPushforwardCanonicalBaseChange
    (n : ℕ) {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) : Prop :=
  ∀ A : Over T, IsIso (projectiveTwistedPushforwardBaseChangeHom n Q d A)

namespace ProjectiveOneStepMultiplicationBaseChangeComparison

/-- Two adjacent canonical Cohomology-and-Base-Change isomorphisms automatically form
the multiplication-compatible base-change package used by one-step flattening. -/
noncomputable def ofCanonical
    (n : ℕ) {T : Scheme.{u}}
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ)
    (hdegree : ProjectiveTwistedPushforwardCanonicalBaseChange n Q d)
    (hdegreeSucc : ProjectiveTwistedPushforwardCanonicalBaseChange n Q (d + 1)) :
    ProjectiveOneStepMultiplicationBaseChangeComparison n Q d where
  degree A := by
    letI := hdegree A
    exact asIso (projectiveTwistedPushforwardBaseChangeHom n Q d A)
  degreeSucc A := by
    letI := hdegreeSucc A
    exact asIso (projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A)
  multiplication_comm A := by
    letI := hdegree A
    exact projectiveTwistedPushforwardBaseChangeHom_mul n Q d A

end ProjectiveOneStepMultiplicationBaseChangeComparison

end Modules

end AlgebraicGeometry.Scheme

end

end
