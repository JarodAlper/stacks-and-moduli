module

public import StacksAndModuli.API.ProjectiveDVRTwistedFreeCohomologyReduction
public import StacksAndModuli.API.ProjectiveSheafGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveSpaceGlobalSectionsBaseChange
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Serre specialization for projective Quot pullback data over a DVR

This file normalizes a `Scheme.Modules.QuotientPullbackData` object whose ambient
module is a finite twisted-free sheaf.  After identifying the pullback
`T ×ₛ ℙⁿₛ` with `ℙⁿ_T`, its quotient map becomes an epimorphism from the standard
twisted-free module on `ℙⁿ_T`.  Over a discrete valuation ring, scheme-level Serre
vanishing then transfers the generic Hilbert polynomial to the residue-field fibre.

Main declarations:
- `AlgebraicGeometry.Scheme.projectiveSpaceOverTwistedFree_pullbackIso`;
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.
    twistedFreeQuotientOnProjectiveSpace`;
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.
    closedPullback_hasFiberwiseHilbertPolynomial_of_twistedFree_of_serre`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The inverse projective-space base-change comparison followed by the first
pullback projection is the relative projective-space projection. -/
lemma projectiveSpaceOverBaseChangeIso_inv_fst
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (projectiveSpaceOverBaseChangeIso n g).inv ≫
        pullback.fst g (projectiveSpaceOverπ n S) =
      projectiveSpaceOverπ n T := by
  rw [← cancel_epi (projectiveSpaceOverBaseChangeIso n g).hom]
  simp

/-- The inverse projective-space base-change comparison followed by the second
pullback projection is the projective-space map induced by the base morphism. -/
lemma projectiveSpaceOverBaseChangeIso_inv_snd
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (projectiveSpaceOverBaseChangeIso n g).inv ≫
        pullback.snd g (projectiveSpaceOverπ n S) =
      projectiveSpaceOverMap n g := by
  rw [← cancel_epi (projectiveSpaceOverBaseChangeIso n g).hom]
  rw [Iso.hom_inv_id_assoc]
  exact (projectiveSpaceOverBaseChangeIso_hom_map n g).symm

/-- Pulling back a finite coproduct of copies of `O(-l)` along a base morphism
gives the corresponding finite twisted-free module on the new projective space. -/
noncomputable def projectiveSpaceOverTwistedFree_pullbackIso
    (n r : ℕ) (l : ℤ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (Modules.pullback (projectiveSpaceOverMap n g)).obj
        (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)) ≅
      ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l) :=
  PreservesCoproduct.iso
      (Modules.pullback (projectiveSpaceOverMap n g))
      (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)) ≪≫
    Sigma.mapIso (fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist_pullbackIso n g (-l))

namespace Modules.QuotientPullbackData

variable {n r : ℕ} {l : ℤ} {S : Scheme.{u}} {R : CommRingCat.{u}}

abbrev twistedFreeAmbient :
    (projectiveSpaceOver n S).Modules :=
  ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)

/-- The pullback of the ambient module in a Quot datum, normalized from
`Spec R ×ₛ ℙⁿₛ` to `ℙⁿ_R`, agrees with direct pullback along
`ℙⁿ_R ⟶ ℙⁿₛ`. -/
noncomputable def quotDataOnProjectiveSpaceAmbientIso
    (σ : Spec R ⟶ S) :
    (Modules.pullback (projectiveSpaceOverMap n σ)).obj
        (twistedFreeAmbient (n := n) (r := r) (l := l)) ≅
      (Modules.pullback (projectiveSpaceOverBaseChangeIso n σ).inv).obj
        ((Modules.pullback
          ((Over.pullback (projectiveSpaceOverπ n S)).obj (Over.mk σ)).hom).obj
            (twistedFreeAmbient (n := n) (r := r) (l := l))) :=
  (Modules.pullbackPullbackIsoOfEq
    (projectiveSpaceOverBaseChangeIso n σ).inv
    ((Over.pullback (projectiveSpaceOverπ n S)).obj (Over.mk σ)).hom
    (projectiveSpaceOverMap n σ)
    (projectiveSpaceOverBaseChangeIso_inv_snd n σ)
    (twistedFreeAmbient (n := n) (r := r) (l := l))).symm

/-- Normalize the quotient map of twisted-free Quot pullback data to the
standard finite twisted-free source on `ℙⁿ_R`. -/
noncomputable def twistedFreeQuotientOnProjectiveSpace
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ)) :
    (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n (Spec R) (-l)) ⟶
      quotDataOnProjectiveSpace
        (n := n) (S := S) (T := Over.mk σ)
        (twistedFreeAmbient (n := n) (r := r) (l := l)) a :=
  (projectiveSpaceOverTwistedFree_pullbackIso n r l σ).inv ≫
    (quotDataOnProjectiveSpaceAmbientIso σ).hom ≫
    (Modules.pullback (projectiveSpaceOverBaseChangeIso n σ).inv).map a.π

/-- The normalized twisted-free quotient map remains an epimorphism. -/
lemma twistedFreeQuotientOnProjectiveSpace_epi
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ)) :
    Epi (twistedFreeQuotientOnProjectiveSpace σ a) := by
  have : Epi a.π := a.epi
  dsimp only [twistedFreeQuotientOnProjectiveSpace]
  infer_instance

/-- The normalized quotient sheaf of a Quot datum is quasicoherent. -/
lemma quotDataOnProjectiveSpace_isQuasicoherent
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ)) :
    (quotDataOnProjectiveSpace
      (n := n) (S := S) (T := Over.mk σ)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a).IsQuasicoherent := by
  let : a.Q.IsQuasicoherent := a.isQuasicoherent
  change ((Modules.pullback
    (projectiveSpaceOverBaseChangeIso n σ).inv).obj a.Q).IsQuasicoherent
  infer_instance

/-- Normalizing a Quot datum along the projective-space base-change isomorphism
preserves its flatness over the parameter scheme. -/
lemma quotDataOnProjectiveSpace_flatOver
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ)) :
    (quotDataOnProjectiveSpace
      (n := n) (S := S) (T := Over.mk σ)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a).FlatOver
        (projectiveSpaceOverπ n (Spec R)) := by
  exact FlatOver.pullback_isIso
    (projectiveSpaceOverBaseChangeIso n σ).inv a.Q
    (projectiveSpaceOverBaseChangeIso_inv_fst n σ) a.flatOver

/-- A fibrewise Hilbert polynomial on any field-valued pullback of a Quot datum
gives the ordinary Hilbert polynomial of the corresponding pullback of its
normalized projective-space sheaf. -/
theorem hasHilbertPolynomialOver_projectiveSpacePullback
    {F : (projectiveSpaceOver n S).Modules} {T : Over S}
    (a : QuotientPullbackData F (projectiveSpaceOverπ n S) T)
    {K : CommRingCat.{u}} (hK : IsField K) (s : Spec K ⟶ S)
    (g : Over.mk s ⟶ T) (P : Polynomial ℚ)
    (h : AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
      (quotDataOnProjectiveSpace (n := n) (S := S) F (a.pullback g)) P) :
    HasHilbertPolynomialOver
      ((Modules.pullback (projectiveSpaceOverMap n g.left)).obj
        (quotDataOnProjectiveSpace (n := n) (S := S) F a)) P := by
  let Qg := quotDataOnProjectiveSpace (n := n) (S := S) F (a.pullback g)
  change AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial Qg P at h
  have hbase : HasHilbertPolynomialOver Qg P :=
    AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial.hasHilbertPolynomialOver hK h
  exact HasHilbertPolynomialOver.iso
    (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g) hbase

/-- For a twisted-free Quot datum over a DVR, scheme-level Serre vanishing
transfers the generic fixed Hilbert polynomial to the canonical residue-field
pullback of its normalized quotient sheaf. -/
theorem hasHilbertPolynomialOver_closedFiber_of_twistedFree_of_serre
    [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ))
    (hserre : ProjectiveSpaceHasSerreVanishing n (Spec R))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let g : Over.mk (j₀ ≫ σ) ⟶ Over.mk σ := Over.homMk j₀ rfl
      AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
        (quotDataOnProjectiveSpace (n := n) (S := S)
          (twistedFreeAmbient (n := n) (r := r) (l := l))
          (a.pullback g)) P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Q := quotDataOnProjectiveSpace
      (n := n) (S := S) (T := Over.mk σ)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a
    HasHilbertPolynomialOver
      ((Modules.pullback (projectiveSpaceOverMap n c)).obj Q) P := by
  let Q := quotDataOnProjectiveSpace
    (n := n) (S := S) (T := Over.mk σ)
    (twistedFreeAmbient (n := n) (r := r) (l := l)) a
  let q := twistedFreeQuotientOnProjectiveSpace σ a
  have : Epi q := twistedFreeQuotientOnProjectiveSpace_epi σ a
  have : Q.IsQuasicoherent := quotDataOnProjectiveSpace_isQuasicoherent σ a
  have hflat : Q.FlatOver (projectiveSpaceOverπ n (Spec R)) :=
    quotDataOnProjectiveSpace_flatOver σ a
  let j₀ := Spec.map
    (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let g : Over.mk (j₀ ≫ σ) ⟶ Over.mk σ := Over.homMk j₀ rfl
  have hgeneric' : AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
      (quotDataOnProjectiveSpace (n := n) (S := S)
        (twistedFreeAmbient (n := n) (r := r) (l := l))
        (a.pullback g)) P := by
    simpa [j₀, g] using hgeneric
  have hgenericQ : HasHilbertPolynomialOver
      ((Modules.pullback (projectiveSpaceOverMap n j₀)).obj Q) P := by
    simpa [Q, g] using hasHilbertPolynomialOver_projectiveSpacePullback
      a (Field.toIsField (FractionRing R)) (j₀ ≫ σ) g P hgeneric'
  exact hflat.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistedFree_epi_of_serre
    n r l R q hserre ϖ hϖ P hgenericQ

/-- For a twisted-free Quot datum over a DVR, scheme-level Serre vanishing
makes the generic fixed Hilbert polynomial valid at every field-valued point
of the canonical residue-field fibre. -/
theorem hasFiberwiseHilbertPolynomial_closedFiber_of_twistedFree_of_serre
    [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ))
    (hserre : ProjectiveSpaceHasSerreVanishing n (Spec R))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let g : Over.mk (j₀ ≫ σ) ⟶ Over.mk σ := Over.homMk j₀ rfl
      AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
        (quotDataOnProjectiveSpace (n := n) (S := S)
          (twistedFreeAmbient (n := n) (r := r) (l := l))
          (a.pullback g)) P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Q := quotDataOnProjectiveSpace
      (n := n) (S := S) (T := Over.mk σ)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a
    AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
      ((Modules.pullback (projectiveSpaceOverMap n c)).obj Q) P := by
  let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
  let Q := quotDataOnProjectiveSpace
    (n := n) (S := S) (T := Over.mk σ)
    (twistedFreeAmbient (n := n) (r := r) (l := l)) a
  let Qκ := (Modules.pullback (projectiveSpaceOverMap n c)).obj Q
  have hclosed : HasHilbertPolynomialOver Qκ P := by
    simpa [c, Q, Qκ] using
      hasHilbertPolynomialOver_closedFiber_of_twistedFree_of_serre
        σ a hserre ϖ hϖ P hgeneric
  have hQqc : Q.IsQuasicoherent := quotDataOnProjectiveSpace_isQuasicoherent σ a
  have : Qκ.IsQuasicoherent := by
    let : Q.IsQuasicoherent := hQqc
    dsimp only [Qκ]
    infer_instance
  exact hclosed.hasFiberwise_over_field n Qκ P

/-- The canonical closed pullback of twisted-free Quot data itself has the
generic fixed Hilbert polynomial, not merely its normalized projective-space
model. -/
theorem closedPullback_hasFiberwiseHilbertPolynomial_of_twistedFree_of_serre
    [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec R ⟶ S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk σ))
    (hserre : ProjectiveSpaceHasSerreVanishing n (Spec R))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let g : Over.mk (j₀ ≫ σ) ⟶ Over.mk σ := Over.homMk j₀ rfl
      AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
        (quotDataOnProjectiveSpace (n := n) (S := S)
          (twistedFreeAmbient (n := n) (r := r) (l := l))
          (a.pullback g)) P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
    Modules.QuotientPullbackData.HasFiberwiseHilbertPolynomial
      (n := n) (S := S)
      (F := twistedFreeAmbient (n := n) (r := r) (l := l))
      (a.pullback gc) P := by
  let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
  let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
  let Q := quotDataOnProjectiveSpace
    (n := n) (S := S) (T := Over.mk σ)
    (twistedFreeAmbient (n := n) (r := r) (l := l)) a
  have hclosed : AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
      ((Modules.pullback (projectiveSpaceOverMap n c)).obj Q) P := by
    simpa [c, Q] using
      hasFiberwiseHilbertPolynomial_closedFiber_of_twistedFree_of_serre
        σ a hserre ϖ hϖ P hgeneric
  change AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial
    (quotDataOnProjectiveSpace (n := n) (S := S)
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (a.pullback gc)) P
  exact AlgebraicGeometry.Scheme.HasFiberwiseHilbertPolynomial.of_iso
    (a.quotDataOnProjectiveSpace_pullbackIso
      (n := n) (S := S) gc).symm hclosed

end Modules.QuotientPullbackData

end AlgebraicGeometry.Scheme

end
