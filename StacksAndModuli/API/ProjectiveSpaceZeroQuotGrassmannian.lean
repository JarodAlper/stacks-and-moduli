module

public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre

/-!
# Quotients on projective zero-space as Grassmannian quotients

This file transports a Quot presentation on relative projective zero-space across
the canonical isomorphisms
`T ×ₛ ℙ⁰ₛ ≅ ℙ⁰_T ≅ T`.  The transported quotient sheaf is
quasicoherent, finitely presented, and flat over the identity of the parameter
scheme.  For a twisted-free ambient sheaf, its quotient map is transported to a
quotient map from the pullback of the corresponding free sheaf on the base.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.zeroNormalizedSheaf`;
* `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.zeroNormalizedMap`;
* `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.toPullbackQuotientZero`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

variable {S : Scheme.{u}} {F : (Scheme.projectiveSpaceOver 0 S).Modules}
  {T : Over S}

/-- Inverse naturality for the canonical identification `ℙ⁰_T ≅ T`. -/
lemma projectiveSpaceOverZeroIso_inv_naturality
    {T' : Over S} (g : T' ⟶ T) :
    (Scheme.projectiveSpaceOverZeroIso T'.left).inv ≫
        Scheme.projectiveSpaceOverMap 0 g.left =
      g.left ≫ (Scheme.projectiveSpaceOverZeroIso T.left).inv := by
  rw [← cancel_mono (Scheme.projectiveSpaceOverZeroIso T.left).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.projectiveSpaceOverZeroIso_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The quotient sheaf on the parameter scheme obtained by successively
normalizing the base-changed projective zero-space and then identifying
`ℙ⁰_T` with `T`. -/
noncomputable def zeroNormalizedSheaf
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    T.left.Modules :=
  (Modules.pullback (Scheme.projectiveSpaceOverZeroIso T.left).inv).obj
    (quotDataOnProjectiveSpace (n := 0) (S := S) F x)

/-- Normalization from projective zero-space to the parameter scheme commutes
with pullback, up to the canonical pullback-composition isomorphisms. -/
noncomputable def zeroNormalizedSheaf_pullbackIso
    {T' : Over S} (g : T' ⟶ T)
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    (x.pullback g).zeroNormalizedSheaf ≅
      (Modules.pullback g.left).obj x.zeroNormalizedSheaf :=
  (Modules.pullback
    (Scheme.projectiveSpaceOverZeroIso T'.left).inv).mapIso
      (x.quotDataOnProjectiveSpace_pullbackIso (n := 0) (S := S) g) ≪≫
    (Modules.pullbackComp
      (Scheme.projectiveSpaceOverZeroIso T'.left).inv
      (Scheme.projectiveSpaceOverMap 0 g.left)).app
        (quotDataOnProjectiveSpace (n := 0) (S := S) F x) ≪≫
    (Modules.pullbackCongr
      (projectiveSpaceOverZeroIso_inv_naturality g)).app
        (quotDataOnProjectiveSpace (n := 0) (S := S) F x) ≪≫
    ((Modules.pullbackComp g.left
      (Scheme.projectiveSpaceOverZeroIso T.left).inv).app
        (quotDataOnProjectiveSpace (n := 0) (S := S) F x)).symm

/-- The quotient sheaf normalized from projective zero-space to the parameter
scheme remains quasicoherent. -/
lemma zeroNormalizedSheaf_isQuasicoherent
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    x.zeroNormalizedSheaf.IsQuasicoherent := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  dsimp only [zeroNormalizedSheaf, quotDataOnProjectiveSpace]
  infer_instance

/-- The quotient sheaf normalized from projective zero-space to the parameter
scheme remains finitely presented. -/
lemma zeroNormalizedSheaf_isFinitePresentation
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    x.zeroNormalizedSheaf.IsFinitePresentation := by
  letI : x.Q.IsFinitePresentation := x.isFinitePresentation
  dsimp only [zeroNormalizedSheaf, quotDataOnProjectiveSpace]
  infer_instance

/-- The quotient sheaf normalized from projective zero-space to the parameter
scheme is flat over the identity. -/
lemma zeroNormalizedSheaf_flatOver_id
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    x.zeroNormalizedSheaf.FlatOver (𝟙 T.left) := by
  have hprojective :
      (quotDataOnProjectiveSpace (n := 0) (S := S) F x).FlatOver
        (Scheme.projectiveSpaceOverπ 0 T.left) :=
    FlatOver.pullback_isIso
      (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv x.Q
      (Scheme.projectiveSpaceOverBaseChangeIso_inv_fst 0 T.hom) x.flatOver
  exact FlatOver.pullback_isIso
    (Scheme.projectiveSpaceOverZeroIso T.left).inv
    (quotDataOnProjectiveSpace (n := 0) (S := S) F x)
    (by simpa only [Scheme.projectiveSpaceOverZeroIso_hom] using
      (Scheme.projectiveSpaceOverZeroIso T.left).inv_hom_id) hprojective

/-- The source of a Quot presentation, after normalizing the fibre product to
projective space over the parameter scheme, agrees with direct pullback along
the induced map of projective spaces. -/
noncomputable def zeroNormalizedProjectiveAmbientIso
    (F : (Scheme.projectiveSpaceOver 0 S).Modules) :
    (Modules.pullback (Scheme.projectiveSpaceOverMap 0 T.hom)).obj F ≅
      (Modules.pullback
        (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv).obj
        ((Modules.pullback
          ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).obj T).hom).obj F) :=
  (Modules.pullbackPullbackIsoOfEq
    (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv
    ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).obj T).hom
    (Scheme.projectiveSpaceOverMap 0 T.hom)
    (Scheme.projectiveSpaceOverBaseChangeIso_inv_snd 0 T.hom) F).symm

variable {l : ℤ} {r : ℕ}

/-- Normalize the quotient map of a twisted-free Quot presentation to the
standard twisted-free source on `ℙ⁰_T`. -/
noncomputable def zeroTwistedFreeMapOnProjectiveSpace
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T) :
    Scheme.projectiveSpaceOverTwistedFree 0 T.left l r ⟶
      quotDataOnProjectiveSpace (n := 0) (S := S)
        (Scheme.projectiveSpaceOverTwistedFree 0 S l r) x :=
  (Scheme.projectiveSpaceOverTwistedFree_pullbackIso 0 r l T.hom).inv ≫
    (zeroNormalizedProjectiveAmbientIso
      (T := T) (Scheme.projectiveSpaceOverTwistedFree 0 S l r)).hom ≫
    (Modules.pullback
      (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv).map x.π

/-- The quotient map remains epic after normalizing the fibre product to
projective zero-space over the parameter scheme. -/
lemma zeroTwistedFreeMapOnProjectiveSpace_epi
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T) :
    Epi x.zeroTwistedFreeMapOnProjectiveSpace := by
  haveI : Epi x.π := x.epi
  dsimp only [zeroTwistedFreeMapOnProjectiveSpace]
  infer_instance

/-- The pullback of the free ambient sheaf on `S` agrees with the pullback to
`T` of the twisted-free ambient sheaf on `ℙ⁰_T`. -/
noncomputable def zeroTwistedFreeAmbientIso :
    (Modules.pullback T.hom).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      (Modules.pullback (Scheme.projectiveSpaceOverZeroIso T.left).inv).obj
        (Scheme.projectiveSpaceOverTwistedFree 0 T.left l r) :=
  Modules.pullbackFreeIso T.hom (ULift.{u} (Fin r)) ≪≫
    (Modules.pullbackFreeIso
      (Scheme.projectiveSpaceOverZeroIso T.left).inv
      (ULift.{u} (Fin r))).symm ≪≫
    (Modules.pullback
      (Scheme.projectiveSpaceOverZeroIso T.left).inv).mapIso
        (Scheme.projectiveSpaceOverZeroTwistedFreeIsoFree T.left l r).symm

/-- The normalized quotient map on the parameter scheme, with source the
pullback of the canonical rank-`r` free sheaf on the base. -/
noncomputable def zeroNormalizedMap
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T) :
    (Modules.pullback T.hom).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      x.zeroNormalizedSheaf :=
  (zeroTwistedFreeAmbientIso (T := T) (l := l) (r := r)).hom ≫
    (Modules.pullback
      (Scheme.projectiveSpaceOverZeroIso T.left).inv).map
        x.zeroTwistedFreeMapOnProjectiveSpace

/-- The normalized quotient map on the parameter scheme is epic. -/
lemma zeroNormalizedMap_epi
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T) :
    Epi x.zeroNormalizedMap := by
  haveI : Epi x.zeroTwistedFreeMapOnProjectiveSpace :=
    zeroTwistedFreeMapOnProjectiveSpace_epi x
  dsimp only [zeroNormalizedMap]
  infer_instance

/-- Without any fixed-rank hypothesis, the quotient sheaf normalized to the
parameter scheme is already finite locally free. -/
theorem zeroNormalizedSheaf_isFiniteLocallyFree
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) :
    IsFiniteLocallyFree x.zeroNormalizedSheaf := by
  letI : x.zeroNormalizedSheaf.IsQuasicoherent :=
    zeroNormalizedSheaf_isQuasicoherent x
  exact Modules.isFiniteLocallyFree_of_isFinitePresentation_flatOver_id
    x.zeroNormalizedSheaf x.zeroNormalizedSheaf_isFinitePresentation
      x.zeroNormalizedSheaf_flatOver_id

/-- A twisted-free Quot presentation on projective zero-space determines a
relative Grassmannian quotient as soon as the residue fibres of its normalized
quotient sheaf have dimension `q`. -/
noncomputable def toPullbackQuotientZero (q : ℕ)
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T)
    (hrank : ∀ (U : T.left.affineOpens)
      (p : PrimeSpectrum Γ(T.left, U.1)),
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(x.zeroNormalizedSheaf, U.1)) = q) :
    Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T where
  Q := x.zeroNormalizedSheaf
  isQuasicoherent := x.zeroNormalizedSheaf_isQuasicoherent
  isProjectiveOfRank := by
    letI : x.zeroNormalizedSheaf.IsQuasicoherent :=
      x.zeroNormalizedSheaf_isQuasicoherent
    exact Modules.isProjectiveOfRank_of_isFinitePresentation_flatOver_id
      x.zeroNormalizedSheaf q x.zeroNormalizedSheaf_isFinitePresentation
        x.zeroNormalizedSheaf_flatOver_id hrank
  π := x.zeroNormalizedMap
  epi := x.zeroNormalizedMap_epi

/-- An isomorphism between Quot targets transports to an isomorphism between
their quotient sheaves normalized onto the parameter scheme. -/
noncomputable def zeroNormalizedSheafIso
    {x y : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T}
    (e : x.Q ≅ y.Q) : x.zeroNormalizedSheaf ≅ y.zeroNormalizedSheaf :=
  (Modules.pullback (Scheme.projectiveSpaceOverZeroIso T.left).inv).mapIso
    ((Modules.pullback
      (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv).mapIso e)

/-- Compatibility of Quot projections survives both normalizations and the
identification of the twisted-free source with the pulled-back free sheaf. -/
lemma zeroNormalizedMap_comp_zeroNormalizedSheafIso_hom
    {x y : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T}
    (e : x.Q ≅ y.Q) (he : x.π ≫ e.hom = y.π) :
    x.zeroNormalizedMap ≫ (zeroNormalizedSheafIso e).hom =
      y.zeroNormalizedMap := by
  simp only [zeroNormalizedMap, zeroTwistedFreeMapOnProjectiveSpace,
    zeroNormalizedSheafIso, Functor.mapIso_hom, Category.assoc,
    ← Functor.map_comp, he]

/-- The pointwise Quot-to-Grassmannian constructor respects the equivalence
relations on quotient presentations. -/
theorem toPullbackQuotientZero_r (q : ℕ)
    {x y : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T}
    (hxy : (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r x y)
    (hrankx : ∀ (U : T.left.affineOpens)
      (p : PrimeSpectrum Γ(T.left, U.1)),
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(x.zeroNormalizedSheaf, U.1)) = q)
    (hranky : ∀ (U : T.left.affineOpens)
      (p : PrimeSpectrum Γ(T.left, U.1)),
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(y.zeroNormalizedSheaf, U.1)) = q) :
    (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T).r
        (x.toPullbackQuotientZero q hrankx)
        (y.toPullbackQuotientZero q hranky) := by
  obtain ⟨e, he⟩ := hxy
  exact ⟨zeroNormalizedSheafIso e,
    zeroNormalizedMap_comp_zeroNormalizedSheafIso_hom e he⟩

/-- The field-valued point of the parameter scheme associated to a prime of an
affine open. -/
noncomputable def zeroResiduePoint (U : T.left.affineOpens)
    (p : PrimeSpectrum Γ(T.left, U.1)) :
    Spec (CommRingCat.of p.asIdeal.ResidueField) ⟶ T.left :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(T.left, U.1) p.asIdeal.ResidueField)) ≫ U.2.fromSpec

/-- The precise local comparison datum needed to extract the rank of the
normalized quotient from its Hilbert polynomial: the algebraic residue fibre
of sections on an affine open has the same linear realization as the global
sections of the corresponding field-valued projective-zero fibre. -/
def HasZeroResidueFiberComparison
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T) : Prop :=
  ∀ (U : T.left.affineOpens) (p : PrimeSpectrum Γ(T.left, U.1)),
    let K := p.asIdeal.ResidueField
    let s := zeroResiduePoint U p
    let Qs := (Modules.pullback
      (Scheme.projectiveSpaceOverMap 0 s)).obj
        (quotDataOnProjectiveSpace (n := 0) (S := S) F x)
    letI := Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of K))) Qs
    Nonempty
      (p.asIdeal.Fiber Γ(x.zeroNormalizedSheaf, U.1) ≃ₗ[K] Γ(Qs, ⊤))

/-- The constant Hilbert-polynomial condition gives the residue-rank hypothesis
for the normalized quotient once the local residue-fibre comparison is known. -/
theorem zeroNormalizedSheaf_residueRank_of_hilbert
    (q : ℕ)
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)))
    (hcompare : HasZeroResidueFiberComparison x) :
    ∀ (U : T.left.affineOpens) (p : PrimeSpectrum Γ(T.left, U.1)),
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(x.zeroNormalizedSheaf, U.1)) = q := by
  intro U p
  let K := p.asIdeal.ResidueField
  let s := zeroResiduePoint U p
  let Qs := (Modules.pullback
    (Scheme.projectiveSpaceOverMap 0 s)).obj
      (quotDataOnProjectiveSpace (n := 0) (S := S) F x)
  letI := Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of K))) Qs
  obtain ⟨e⟩ := hcompare U p
  calc
    Module.finrank K
        (p.asIdeal.Fiber Γ(x.zeroNormalizedSheaf, U.1)) =
        Module.finrank K Γ(Qs, ⊤) := e.finrank_eq
    _ = q := by
      exact (Scheme.hasFiberwiseHilbertPolynomial_zero_C_iff
        (quotDataOnProjectiveSpace (n := 0) (S := S) F x) q).mp hP
          (CommRingCat.of K) (Field.toIsField K) s

/-- Conditional pointwise comparison from the fixed-polynomial Quot functor to
the relative Grassmannian.  Its only extra input is the explicit local
residue-fibre/global-sections comparison isolated above. -/
noncomputable def toPullbackQuotientZeroOfHilbert (q : ℕ)
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)))
    (hcompare : HasZeroResidueFiberComparison x) :
    Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T :=
  x.toPullbackQuotientZero q
    (x.zeroNormalizedSheaf_residueRank_of_hilbert q hP hcompare)

/-- The Hilbert-polynomial version of the pointwise comparison respects the
quotient-presentation setoids whenever the local comparison data are supplied
for both representatives. -/
theorem toPullbackQuotientZeroOfHilbert_r (q : ℕ)
    {x y : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T}
    (hxy : (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r x y)
    (hPx : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)))
    (hcomparex : HasZeroResidueFiberComparison x)
    (hPy : y.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)))
    (hcomparey : HasZeroResidueFiberComparison y) :
    (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T).r
        (x.toPullbackQuotientZeroOfHilbert q hPx hcomparex)
        (y.toPullbackQuotientZeroOfHilbert q hPy hcomparey) :=
  toPullbackQuotientZero_r q hxy
    (x.zeroNormalizedSheaf_residueRank_of_hilbert q hPx hcomparex)
    (y.zeroNormalizedSheaf_residueRank_of_hilbert q hPy hcomparey)

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

end
