module

public import StacksAndModuli.API.TwistedFreeQuotDenormalization
public import StacksAndModuli.API.QuotGrassmannianReconstructionIso
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFibre
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection

/-!
# Reconstruction reflection for the canonical Quot-to-Grassmannian map

An isomorphism between the strict degree-`d` monomial quotients induces an isomorphism
between their reconstructed twisted-free quotients.  If reconstruction presents the
kernel of each original quotient, those reconstructed quotients recover the originals.
This file assembles the two facts and transports the resulting compatible isomorphism
from the standard model `P^n_T` back to the raw fibre-product model used by the Quot
functor.  The endpoint is exactly `ReflectsQuotientEquivalence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Modules.QuotientPullbackData

variable {n r : ℕ} {l : ℤ} {S : Scheme.{u}}

/-- A compatible isomorphism after normalizing two twisted-free quotient presentations
reflects to an equivalence of the original raw quotient presentations. -/
lemma r_of_twistedFreeQuotientOnProjectiveSpaceOver_iso
    (T : Over S)
    {a b : QuotientPullbackData
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T}
    (e : quotDataOnProjectiveSpace
          (twistedFreeAmbient (n := n) (r := r) (l := l)) a ≅
        quotDataOnProjectiveSpace
          (twistedFreeAmbient (n := n) (r := r) (l := l)) b)
    (h : twistedFreeQuotientOnProjectiveSpaceOver T a ≫ e.hom =
      twistedFreeQuotientOnProjectiveSpaceOver T b) :
    (QuotientPullbackData.setoid
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r a b := by
  let E := projectiveSpaceOverBaseChangeIso n T.hom
  let η := Modules.pullbackInverseUnit E.hom_inv_id
  change (Modules.pullback E.inv).obj a.Q ≅
    (Modules.pullback E.inv).obj b.Q at e
  let e' : a.Q ≅ b.Q :=
    η.app a.Q ≪≫
      (Modules.pullback E.hom).mapIso e ≪≫
      (η.app b.Q).symm
  refine ⟨e', ?_⟩
  let A := (Modules.pullback
    ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
      (twistedFreeAmbient (n := n) (r := r) (l := l))
  let ν := twistedFreeQuotientToProjectiveSpaceAmbientIso
    (n := n) (r := r) (l := l) T
  change ν.hom ≫ (Modules.pullback E.inv).map a.π ≫ e.hom =
    ν.hom ≫ (Modules.pullback E.inv).map b.π at h
  have h' :
      (Modules.pullback E.inv).map a.π ≫ e.hom =
        (Modules.pullback E.inv).map b.π := by
    apply (cancel_epi ν.hom).1
    simpa only [Category.assoc] using h
  have hmap := congrArg (fun k ↦ (Modules.pullback E.hom).map k) h'
  simp only [Functor.map_comp] at hmap
  have hηa := η.hom.naturality a.π
  have hηb := η.hom.naturality b.π
  change a.π ≫ (η.app a.Q).hom =
    (η.app A).hom ≫
      (Modules.pullback E.hom).map ((Modules.pullback E.inv).map a.π) at hηa
  change b.π ≫ (η.app b.Q).hom =
    (η.app A).hom ≫
      (Modules.pullback E.hom).map ((Modules.pullback E.inv).map b.π) at hηb
  dsimp only [e', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, hηa]
  slice_lhs 2 3 => rw [hmap]
  rw [← Category.assoc, ← hηb]
  simp

end Modules.QuotientPullbackData

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- Reindexing the strict quotient of an arbitrary twisted-free Quot presentation back
to the product monomial basis recovers the unreindexed monomial quotient map. -/
lemma twistedFreeQuotGrassmannianFreeQuotient_reindex_π
    (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)) :
    SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
        (twistedFreeQuotGrassmannianFreeQuotient
          n S l r a d e he σ hM hsurj).π =
      quotGrassmannianFreeMap n T.left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
        d e he := by
  dsimp only [twistedFreeQuotGrassmannianFreeQuotient,
    twistedFreeQuotGrassmannianFreeMap, quotGrassmannianFreeMap]
  rw [Modules.freeMap_comp_freeHomOfSections]
  congr 1
  funext i
  simp only [Equiv.apply_symm_apply]

namespace TwistedFreeQuotGrassmannianQuotientNatTransData

/-- Kernel presentation for every fixed-polynomial quotient makes the fixed-degree
Grassmannian quotient reflect equivalence of the original twisted-free Quot data. -/
theorem reflectsQuotientEquivalence_of_reconstructedRelationPresentsKernel
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (R : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        ReconstructedRelationPresentsKernel n T.left l r d e he
          (quotGrassmannianFreeMap n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d e he)
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)) :
    D.ReflectsQuotientEquivalence := by
  intro T a b hPa hPb hfree
  let xa := twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ
    (D.isProjectiveOfRank T a hPa) (D.surjective T a hPa)
  let xb := twistedFreeQuotGrassmannianFreeQuotient n S l r b d e he σ
    (D.isProjectiveOfRank T b hPb) (D.surjective T b hPb)
  obtain ⟨ε, hε⟩ := hfree
  let pa := Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  let pb := Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T b
  letI : Epi pa :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  letI : Epi pb :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T b
  let ua := quotGrassmannianFreeMap n T.left l r pa d e he
  let ub := quotGrassmannianFreeMap n T.left l r pb d e he
  have hxa : SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫ xa.π = ua :=
    twistedFreeQuotGrassmannianFreeQuotient_reindex_π T a
      (D.isProjectiveOfRank T a hPa) (D.surjective T a hPa)
  have hxb : SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫ xb.π = ub :=
    twistedFreeQuotGrassmannianFreeQuotient_reindex_π T b
      (D.isProjectiveOfRank T b hPb) (D.surjective T b hPb)
  have hε' : ua ≫ ε.hom = ub := by
    calc
      ua ≫ ε.hom =
          (SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫ xa.π) ≫
            ε.hom := congrArg (fun k ↦ k ≫ ε.hom) hxa.symm
      _ = SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
            (xa.π ≫ ε.hom) := Category.assoc _ _ _
      _ = SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫ xb.π :=
        congrArg (fun k ↦ SheafOfModules.freeMap
          (R := T.left.ringCatSheaf) σ.symm ≫ k) hε
      _ = ub := hxb
  let Ra := R T a hPa
  let Rb := R T b hPb
  change ReconstructedRelationPresentsKernel n T.left l r d e he ua pa at Ra
  change ReconstructedRelationPresentsKernel n T.left l r d e he ub pb at Rb
  let δ := reconstructedQuotientIsoOfTargetIso
    n T.left l r d e he ua ub ε hε'
  let θ : (quotDataOnProjectiveSpace
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) a) ≅
      (quotDataOnProjectiveSpace
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) b) :=
    Ra.quotientIso.symm ≪≫ δ ≪≫ Rb.quotientIso
  have hRa : pa ≫ Ra.quotientIso.inv =
      reconstructedQuotientMap' n T.left l r d e he ua := by
    calc
      pa ≫ Ra.quotientIso.inv =
          (reconstructedQuotientMap' n T.left l r d e he ua ≫
            Ra.quotientIso.hom) ≫ Ra.quotientIso.inv :=
        congrArg (fun k ↦ k ≫ Ra.quotientIso.inv)
          Ra.reconstructedQuotientMap'_comp_quotientIso_hom.symm
      _ = reconstructedQuotientMap' n T.left l r d e he ua := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hδ : reconstructedQuotientMap' n T.left l r d e he ua ≫ δ.hom =
      reconstructedQuotientMap' n T.left l r d e he ub :=
    reconstructedQuotientMap'_comp_reconstructedQuotientIsoOfTargetIso_hom
      n T.left l r d e he ua ub ε hε'
  have hθ : pa ≫ θ.hom = pb := by
    dsimp only [θ, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, hRa]
    rw [hδ]
    exact Rb.reconstructedQuotientMap'_comp_quotientIso_hom
  exact Modules.QuotientPullbackData.r_of_twistedFreeQuotientOnProjectiveSpaceOver_iso
    T θ hθ

end TwistedFreeQuotGrassmannianQuotientNatTransData

end AlgebraicGeometry.Scheme

end

end
