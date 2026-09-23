module

public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsBaseChange
public import StacksAndModuli.API.QuasicoherentVectorBundles

/-!
# Rank of global sections on projective zero-space

For a quasicoherent finitely presented sheaf on relative projective zero-space,
flatness over the affine base makes its global sections a finite projective module.
If the family has constant fiberwise Hilbert polynomial `q`, arbitrary affine
base change identifies every residue fiber of this module with the corresponding
sheaf fiber, and hence its rank at every prime is `q`.

This is the module-theoretic endpoint consumed by the affine charts of the
relative Grassmannian.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- A quasicoherent finitely presented sheaf which is flat over the base on
projective zero-space has finite projective global sections over the base ring. -/
theorem projectiveSpaceZero_globalSections_finite_projective
    {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent]
    (hfp : Q.IsFinitePresentation)
    (hflat : Q.FlatOver (projectiveSpaceOverπ 0 (Spec (.of R)))) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ 0 (Spec (.of R))) Q
    Module.Finite R Γ(Q, ⊤) ∧ Module.Projective R Γ(Q, ⊤) := by
  let p := projectiveSpaceOverπ 0 (Spec (.of R))
  let e := projectiveSpaceOverZeroIso (Spec (.of R))
  let N := (Modules.pullback e.inv).obj Q
  letI : N.IsQuasicoherent := by
    dsimp only [N]
    infer_instance
  have hfpN : N.IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation e.inv hfp
  have hflatN : N.FlatOver (𝟙 (Spec (.of R))) :=
    Modules.FlatOver.pullback_isIso e.inv Q (by
      simpa only [e, p, projectiveSpaceOverZeroIso_hom] using e.inv_hom_id) hflat
  have hloc : Modules.IsFiniteLocallyFree N :=
    Modules.isFiniteLocallyFree_of_isFinitePresentation_flatOver_id N hfpN hflatN
  have hcoord :=
    Modules.moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree N hloc
  have hcomp : e.inv ≫ p = 𝟙 (Spec (.of R)) := by
    simpa only [e, p, projectiveSpaceOverZeroIso_hom] using e.inv_hom_id
  have hNfin :
      letI := Modules.globalSectionsModule (e.inv ≫ p) N
      Module.Finite R Γ(N, ⊤) := by
    rw [hcomp]
    change Module.Finite R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N)
    exact hcoord.1
  have hNproj :
      letI := Modules.globalSectionsModule (e.inv ≫ p) N
      Module.Projective R Γ(N, ⊤) := by
    rw [hcomp]
    change Module.Projective R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N)
    exact hcoord.2
  letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule p Q
  letI : Module R Γ(N, ⊤) := Modules.globalSectionsModule (e.inv ≫ p) N
  letI : Module.Finite R Γ(N, ⊤) := hNfin
  letI : Module.Projective R Γ(N, ⊤) := hNproj
  let eΓ := Modules.pullbackGlobalSectionsViaIsoLinearEquiv
    e.inv p Q (Iso.refl N)
  exact ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv' eΓ.symm⟩

/-- The fiberwise constant Hilbert-polynomial condition on projective zero-space
computes the rank at every prime of the module of global sections. -/
theorem projectiveSpaceZero_globalSections_rankAtStalk_eq
    {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] (q : ℕ)
    (hfinite :
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ 0 (Spec (.of R))) Q
      Module.Finite R Γ(Q, ⊤))
    (hprojective :
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ 0 (Spec (.of R))) Q
      Module.Projective R Γ(Q, ⊤))
    (hP : HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ))) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ 0 (Spec (.of R))) Q
    ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(Q, ⊤) p = q := by
  let pR := projectiveSpaceOverπ 0 (Spec (.of R))
  letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
  letI : Module.Finite R Γ(Q, ⊤) := hfinite
  letI : Module.Projective R Γ(Q, ⊤) := hprojective
  intro p
  let K := p.asIdeal.ResidueField
  let f : R →+* K := algebraMap R K
  let newAlgebra : Algebra R K := f.toAlgebra
  letI : Algebra R K := newAlgebra
  letI : Module R K := newAlgebra.toModule
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom f)
  let g := projectiveSpaceOverMap 0 s
  let QK := (Modules.pullback g).obj Q
  let pK := projectiveSpaceOverπ 0 (Spec (.of K))
  letI : Module K Γ(QK, ⊤) := Modules.globalSectionsModule pK QK
  have hdim : Module.finrank K Γ(QK, ⊤) = q :=
    (hasFiberwiseHilbertPolynomial_zero_C_iff Q q).mp hP
      (CommRingCat.of K) (Field.toIsField K) s
  let e := projectiveSpaceZeroGlobalSectionsBaseChangeLinearEquiv f Q
  have hbase : Module.finrank K (TensorProduct R K Γ(Q, ⊤)) = q :=
    e.finrank_eq.trans hdim
  let η : PrimeSpectrum K := ⊥
  have hη : η.comap (algebraMap R K) = p := by
    ext r
    change f r = 0 ↔ r ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  calc
    Module.rankAtStalk Γ(Q, ⊤) p =
        Module.rankAtStalk Γ(Q, ⊤) (η.comap (algebraMap R K)) := by
      rw [hη]
    _ = Module.rankAtStalk (TensorProduct R K Γ(Q, ⊤)) η :=
      (Module.rankAtStalk_baseChange η).symm
    _ = Module.finrank K (TensorProduct R K Γ(Q, ⊤)) := by
      simp
    _ = q := hbase

/-- The residue fiber of global sections of a finite projective family on
projective zero-space has the dimension prescribed by its constant fiberwise
Hilbert polynomial. -/
theorem projectiveSpaceZero_globalSections_residue_finrank_eq
    {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] (q : ℕ)
    (hfinite :
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ 0 (Spec (.of R))) Q
      Module.Finite R Γ(Q, ⊤))
    (hprojective :
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ 0 (Spec (.of R))) Q
      Module.Projective R Γ(Q, ⊤))
    (hP : HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ))) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ 0 (Spec (.of R))) Q
    ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(Q, ⊤)) = q := by
  let pR := projectiveSpaceOverπ 0 (Spec (.of R))
  letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
  letI : Module.Finite R Γ(Q, ⊤) := hfinite
  letI : Module.Projective R Γ(Q, ⊤) := hprojective
  intro p
  rw [p.asIdeal.finrank_fiber_eq_rankAtStalk]
  exact projectiveSpaceZero_globalSections_rankAtStalk_eq
    Q q hfinite hprojective hP p

/-- A quasicoherent finitely presented family on projective zero-space which is
flat over the base has finite projective global sections; if its fiberwise
Hilbert polynomial is the constant `q`, all residue fibers have dimension `q`. -/
theorem projectiveSpaceZero_globalSections_finite_projective_residue_finrank
    {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] (q : ℕ)
    (hfp : Q.IsFinitePresentation)
    (hflat : Q.FlatOver (projectiveSpaceOverπ 0 (Spec (.of R))))
    (hP : HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ))) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ 0 (Spec (.of R))) Q
    Module.Finite R Γ(Q, ⊤) ∧
      Module.Projective R Γ(Q, ⊤) ∧
      ∀ p : PrimeSpectrum R,
        Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.Fiber Γ(Q, ⊤)) = q := by
  let pR := projectiveSpaceOverπ 0 (Spec (.of R))
  letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
  obtain ⟨hfinite, hprojective⟩ :=
    projectiveSpaceZero_globalSections_finite_projective Q hfp hflat
  exact ⟨hfinite, hprojective,
    projectiveSpaceZero_globalSections_residue_finrank_eq
      Q q hfinite hprojective hP⟩

end AlgebraicGeometry.Scheme

end
