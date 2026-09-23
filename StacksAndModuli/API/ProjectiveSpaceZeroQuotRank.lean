module

public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSpaceZeroQuotGrassmannian

/-!
# Fixed-polynomial Quot data on projective zero-space have fixed-rank quotients

Supporting API with no Stacks Project counterpart.

`API/ProjectiveSpaceZeroQuotGrassmannian.lean` transports a Quot presentation on
relative projective zero-space to a quotient sheaf on the parameter scheme
(`zeroNormalizedSheaf`) and packages it as a relative Grassmannian point under a
residue-fibre rank hypothesis (`toPullbackQuotientZero`).  This file removes that
hypothesis: a constant fibrewise Hilbert polynomial `C q` already forces the
normalized sheaf to be a vector bundle of rank `q`
(`isProjectiveOfRank_zeroNormalizedSheaf`), so the pointwise Quot-to-Grassmannian
comparison `toPullbackQuotientZeroOfPolynomial` needs only the Hilbert-polynomial
condition carried by the fixed-polynomial Quot functor itself.

Main declarations:
- `Modules.QuotientPullbackData.isProjectiveOfRank_zeroNormalizedSheaf`;
- `Modules.QuotientPullbackData.toPullbackQuotientZeroOfPolynomial` and its
  setoid-compatibility `toPullbackQuotientZeroOfPolynomial_r`.
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


set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

variable {S : Scheme.{u}} {F : (Scheme.projectiveSpaceOver 0 S).Modules}
  {T : Over S}

/-- A twisted-free Quot presentation on relative projective zero-space whose fibrewise
Hilbert polynomial is the constant `q` has normalized quotient sheaf a vector bundle of
rank `q`.  This discharges the residue-fibre rank hypothesis of the pointwise
Quot-to-Grassmannian comparison unconditionally: on an affine chart the global sections
of the transported family are finite projective of rank `q` by
`projectiveSpaceZero_globalSections_rankAtStalk_eq`, and the rank transports along the
normalization isomorphisms back to the affine open. -/
theorem isProjectiveOfRank_zeroNormalizedSheaf (q : ℕ)
    (x : QuotientPullbackData F (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ))) :
    IsProjectiveOfRank q x.zeroNormalizedSheaf := by
  intro t
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, -⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ t) isOpen_univ
  let A : T.left.affineOpens := ⟨U, hU⟩
  let R := Γ(T.left, A.1)
  let j := A.2.fromSpec
  let TA : Over S := Over.mk (j ≫ T.hom)
  let g : TA ⟶ T := Over.homMk j rfl
  let xA := x.pullback g
  let QA := quotDataOnProjectiveSpace (n := 0) (S := S) F xA
  let pA := Scheme.projectiveSpaceOverπ 0 (Spec (.of R))
  let zA := Scheme.projectiveSpaceOverZeroIso (Spec (.of R))
  let MA := xA.zeroNormalizedSheaf
  letI : xA.Q.IsQuasicoherent := xA.isQuasicoherent
  letI : xA.Q.IsFinitePresentation := xA.isFinitePresentation
  letI : QA.IsQuasicoherent := by
    dsimp only [QA, quotDataOnProjectiveSpace]
    infer_instance
  have hfpQA : QA.IsFinitePresentation := by
    dsimp only [QA, quotDataOnProjectiveSpace]
    infer_instance
  have hflatQA : QA.FlatOver pA := by
    exact FlatOver.pullback_isIso
      (Scheme.projectiveSpaceOverBaseChangeIso 0 TA.hom).inv xA.Q
      (Scheme.projectiveSpaceOverBaseChangeIso_inv_fst 0 TA.hom) xA.flatOver
  have hPA : xA.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)) :=
    x.hasFiberwiseHilbertPolynomial_pullback g hP
  have hfinQA := Scheme.projectiveSpaceZero_globalSections_finite_projective
    QA hfpQA hflatQA
  have hrankQA := Scheme.projectiveSpaceZero_globalSections_rankAtStalk_eq
    QA q hfinQA.1 hfinQA.2 hPA
  letI : Module R Γ(QA, ⊤) := globalSectionsModule pA QA
  letI : Module.Finite R Γ(QA, ⊤) := hfinQA.1
  letI : Module.Projective R Γ(QA, ⊤) := hfinQA.2
  let MA' := (Modules.pullback zA.inv).obj QA
  have hMA : MA = MA' := rfl
  letI : Module R Γ(MA', ⊤) := globalSectionsModule (zA.inv ≫ pA) MA'
  let eΓ := pullbackGlobalSectionsViaIsoLinearEquiv zA.inv pA QA (Iso.refl MA')
  have hfinMA' : Module.Finite R Γ(MA', ⊤) := Module.Finite.equiv eΓ
  have hprojMA' : Module.Projective R Γ(MA', ⊤) :=
    Module.Projective.of_equiv' eΓ
  have hrankMA' : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk Γ(MA', ⊤) p = q := fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).symm.trans (hrankQA p)
  have hcomp : zA.inv ≫ pA = 𝟙 (Spec (.of R)) := by
    simpa only [zA, pA, Scheme.projectiveSpaceOverZeroIso_hom] using zA.inv_hom_id
  have hcoord : Module.Finite R (moduleSpecΓFunctor.obj MA') ∧
      Module.Projective R (moduleSpecΓFunctor.obj MA') ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (moduleSpecΓFunctor.obj MA') p = q := by
    let moduleId : Module R Γ(MA', ⊤) :=
      globalSectionsModule (𝟙 (Spec (.of R))) MA'
    change @Module.Finite R Γ(MA', ⊤) _ _ moduleId ∧
      @Module.Projective R _ Γ(MA', ⊤) _ moduleId ∧
      ∀ p : PrimeSpectrum R,
        @Module.rankAtStalk R Γ(MA', ⊤) _ _ moduleId p = q
    have hmodule : (globalSectionsModule (zA.inv ≫ pA) MA') = moduleId := by
      dsimp only [moduleId]
      rw [hcomp]
    rw [← hmodule]
    exact ⟨hfinMA', hprojMA', hrankMA'⟩
  have htop := moduleSpecΓFunctor_finite_projective_rank_top MA'
    hcoord.1 hcoord.2.1 hcoord.2.2
  let e := x.zeroNormalizedSheaf_pullbackIso g
  have htopMA : Module.Finite Γ(Spec (.of R), ⊤) Γ(MA, ⊤) ∧
      Module.Projective Γ(Spec (.of R), ⊤) Γ(MA, ⊤) ∧
      ∀ p : PrimeSpectrum Γ(Spec (.of R), ⊤),
        Module.rankAtStalk Γ(MA, ⊤) p = q := hMA.symm ▸ htop
  obtain ⟨hfinPull, hprojPull, hrankPull⟩ :=
    sections_finite_projective_rank_of_iso e ⊤
      htopMA.1 htopMA.2.1 htopMA.2.2
  obtain ⟨hfin, hproj, hrank⟩ :=
    sections_finite_projective_rank_of_pullback_openImmersion
      j x.zeroNormalizedSheaf ⊤ hfinPull hprojPull hrankPull
  have himage : j ''ᵁ (⊤ : (Spec (.of R)).Opens) = A.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, A.2.opensRange_fromSpec]
  rw [himage] at hfin hproj hrank
  exact ⟨A, htU, hfin, hproj, hrank⟩

variable {l : ℤ} {r : ℕ}

/-- The unconditional pointwise comparison from the constant-polynomial Quot functor on
relative projective zero-space to the relative Grassmannian of the free rank-`r` sheaf:
the fixed Hilbert polynomial supplies the rank condition, so no residue-fibre input is
needed. -/
noncomputable def toPullbackQuotientZeroOfPolynomial (q : ℕ)
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ))) :
    Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T where
  Q := x.zeroNormalizedSheaf
  isQuasicoherent := x.zeroNormalizedSheaf_isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank_zeroNormalizedSheaf q hP
  π := x.zeroNormalizedMap
  epi := x.zeroNormalizedMap_epi

/-- The unconditional pointwise comparison respects the equivalence relations on
quotient presentations. -/
theorem toPullbackQuotientZeroOfPolynomial_r (q : ℕ)
    {x y : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T}
    (hxy : (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r x y)
    (hPx : x.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)))
    (hPy : y.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ))) :
    (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T).r
        (x.toPullbackQuotientZeroOfPolynomial q hPx)
        (y.toPullbackQuotientZeroOfPolynomial q hPy) := by
  obtain ⟨e, he⟩ := hxy
  exact ⟨zeroNormalizedSheafIso e,
    zeroNormalizedMap_comp_zeroNormalizedSheafIso_hom e he⟩

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

end
