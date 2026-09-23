module

public import StacksAndModuli.API.SemilinearTransport
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# Fixed graded pieces in the twisted-free Quot construction

This file records the strongest direct statement presently available for the fixed-degree
piece of the kernel-quotient graded model over an arbitrary commutative base ring.

The finite twisted-free presentation makes every graded piece finite, but not visibly
finitely presented: the model is the cokernel of a map into a finite free graded module,
and finite presentation of its degree-`d` cokernel requires finite generation of the image
in that degree.  Over a noncoherent ring, a submodule of a finite free module need not be
finite.  Fibrewise regularity controls the Cech cohomology of the associated sheaf, but does
not by itself control this global relation module.

There is a second independent issue.  Constant fibre dimension of a finite, or even
finitely presented, module does not imply flatness over an arbitrary ring.  Accordingly the
endpoint below assumes fixed-degree flatness and that, on every field-valued fibre, the
graded Cech augmentation is bijective.  Under precisely those inputs the Hilbert polynomial
computes the fibre rank, finite flat constant-rank algebra upgrades the piece to finite
projective, and these properties persist under every coefficient change.  The last base
change assertion concerns the algebraic graded model, whose degree pieces are tensor
products by definition; identifying it with geometric pushforward is the missing
cohomology-and-base-change input.

Main declarations:

* `GradedModule.finitePresentation_coker_obj_of_range_fg`;
* `finitePresentation_kernelQuotientModule_twistedFree_obj_of_range_fg`;
* `GradedModule.CechSchemeGlobalSectionsComparison.finrank_cechHgr_zero_baseChange_eq`;
* `GradedModule.CechSchemeGlobalSectionsComparison.finrank_obj_baseChange_eq_of_cechAug`;
* `GradedModule.CechSchemeGlobalSectionsComparison.finitePresentation_projective_obj`;
* `exists_bound_kernelQuotientModule_obj_finite_projective_rank_of_flat_of_cechAug`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The finite-presentation obstruction -/

namespace GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Every homogeneous piece of the polynomial structure module is finitely presented over
the coefficient ring.  In nonnegative degree this follows from its finite monomial basis;
in negative degree the piece is zero. -/
lemma finitePresentation_polySubmodule (d : ℤ) :
    Module.FinitePresentation R (polySubmodule R n d) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [polySubmodule_of_neg R n hd]
    exact Module.FinitePresentation.of_subsingleton _
  · rw [polySubmodule_of_nonneg R n hd]
    let b := MvPolynomial.homogeneousSubmoduleFinBasis n R d.toNat
    letI : Module.Finite R
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat) :=
      Module.Finite.of_basis b
    letI : Module.Projective R
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat) :=
      Module.Projective.of_basis b
    exact Module.finitePresentation_of_projective _ _

/-- Every degree of a finite direct sum of twists of the polynomial structure module is
finitely presented over the coefficient ring. -/
lemma finitePresentation_free_obj (a : ℤ) (r : ℕ) (d : ℤ) :
    Module.FinitePresentation R (((((structureModule R n).twist a).pow r).obj d)) := by
  have hpiece : Module.FinitePresentation R (((structureModule R n).twist a).obj d) :=
    finitePresentation_polySubmodule (d + a)
  letI : ∀ _ : Fin r,
      Module.FinitePresentation R (((structureModule R n).twist a).obj d) := fun _ ↦ hpiece
  exact Module.FinitePresentation.pi _

/-- A degree of a diagrammatic cokernel is finitely presented as soon as the target degree
is finitely presented and the degreewise relation image is finitely generated.  This is the
precise algebraic condition missing for the kernel-quotient model over a noncoherent ring. -/
lemma finitePresentation_coker_obj_of_range_fg {A B : GradedModule R n}
    (f : A ⟶ B) (d : ℤ) (hB : Module.FinitePresentation R (B.obj d))
    (hfg : (LinearMap.range (f.app d).hom).FG) :
    Module.FinitePresentation R ((coker f).obj d) := by
  rw [coker_obj]
  letI : Module.FinitePresentation R (B.obj d) := hB
  apply Module.finitePresentation_of_surjective
    (LinearMap.range (f.app d).hom).mkQ (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ]
  exact hfg

end GradedModule

/-- Every degree of `Gamma_*` of the finite twisted-free ambient sheaf is finitely
presented over the coefficient ring. -/
theorem finitePresentation_gammaStarPullTwistedFree_obj
    (n r : ℕ) (hn : 0 < n) (l d : ℤ) (R : Type u) [CommRing R] :
    Module.FinitePresentation R
      ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (∐ fun _ : ULift.{u} (Fin r) ↦
            Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)))
        (stdVars n R)).obj d) := by
  let e := GradedModule.isoApp (gammaStarPullTwistedFreeIso n R hn (-l) r) d
  letI : Module.FinitePresentation R
      (((((GradedModule.structureModule R n).twist (-l)).pow r).obj d)) :=
    GradedModule.finitePresentation_free_obj (-l) r d
  exact Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

/-- For the kernel-quotient model of a twisted-free presentation, finite generation of the
degreewise relation image is enough for finite presentation of that degree.  The ambient
finite-presentation premise is discharged unconditionally by its monomial basis. -/
theorem finitePresentation_kernelQuotientModule_twistedFree_obj_of_range_fg
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q) (d : ℤ)
    (hrelations :
      let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
      (LinearMap.range ((Proj.gammaStarMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (kernel.ι p) (stdVars n R)).app d).hom).FG) :
    let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
    Module.FinitePresentation R ((Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) (stdVars n R) p).obj d) := by
  dsimp only
  apply GradedModule.finitePresentation_coker_obj_of_range_fg _ d
    (finitePresentation_gammaStarPullTwistedFree_obj n r hn l d R)
  exact hrelations

/-! ## Fibre rank and the flat constant-rank endpoint -/

namespace GradedModule.CechSchemeGlobalSectionsComparison

variable {R : Type u} [CommRing R] {n : ℕ}
variable {M : GradedModule R n}
variable {Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules}

/-- On every field-valued coefficient change, fibrewise positive Cech vanishing makes the
Hilbert polynomial compute fixed-degree Cech `H⁰`.  No finiteness, flatness, or base-change
hypothesis on Cech `H⁰` over the source ring is used. -/
theorem finrank_cechHgr_zero_baseChange_eq
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ)
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ)))
    (κ : Type u) [Field κ] [Algebra R κ] :
    Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) =
      P.hilbertNatValue d := by
  let f : R →+* κ := algebraMap R κ
  have halg : f.toAlgebra = (‹Algebra R κ›) :=
    Algebra.algebra_ext _ _ (fun x ↦ rfl)
  let Qκ := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
    (Scheme.projectiveSpaceOverTwistModule Qκ (d : ℤ))
  have hPκ : Scheme.HasHilbertPolynomialOver Qκ P := by
    simpa [Qκ, Scheme.Modules.projectiveSpaceBaseChangeOfRingHom] using
      hP (CommRingCat.of κ) (Field.toIsField κ)
        (Spec.map (CommRingCat.ofHom f))
  have heventual : ∀ᶠ e : ℕ in Filter.atTop,
      (((Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) : ℕ) : ℚ) =
        P.eval (e : ℚ) := by
    filter_upwards [hPκ, Filter.eventually_ge_atTop E.bound] with e he heE
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
      (Scheme.projectiveSpaceOverTwistModule Qκ (e : ℤ))
    have heiso := E.fibreGlobalSectionsIso κ f e heE
    rw [halg] at heiso
    have heq : (Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) =
        Scheme.hilbertFunctionOver Qκ (e : ℤ) := by
      change Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (e : ℤ)) =
        Module.finrank κ
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Qκ (e : ℤ))
      simpa only [Qκ] using heiso.finrank_eq
    rw [heq]
    exact he
  have hpoly : (Cohomology.cech κ).HasHilbertPolynomial (M.baseChange κ) P :=
    (Cohomology.cech κ).hasHilbertPolynomial_of_eventually_h_zero_eq
      (Cohomology.hasInfiniteBaseChange_cech κ) (M.baseChange κ)
      (hM.baseChange κ) P heventual
  have hdim : (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) := by
    have hp := hpoly (d : ℤ)
    rw [(Cohomology.cech κ).chi_eq_h_zero_of_subsingleton
      (M.baseChange κ) (d : ℤ) (hfib κ)] at hp
    change (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) at hp
    exact hp
  exact (Polynomial.hilbertNatValue_eq hdim).symm

/-- If the graded Cech augmentation is bijective on every field-valued fibre, the actual
degree-`d` piece of the base-changed graded model has the dimension prescribed by the
Hilbert polynomial. -/
theorem finrank_obj_baseChange_eq_of_cechAug
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ)
    (haug : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      Function.Bijective (((M.baseChange κ).cechAug (d : ℤ)).hom))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ)))
    (κ : Type u) [Field κ] [Algebra R κ] :
    Module.finrank κ ((M.baseChange κ).obj (d : ℤ)) =
      P.hilbertNatValue d := by
  let e := LinearEquiv.ofBijective
    (((M.baseChange κ).cechAug (d : ℤ)).hom) (haug κ)
  exact e.finrank_eq.trans
    (finrank_cechHgr_zero_baseChange_eq E hM P hP d hfib κ)

/-- A finite graded piece which is flat over the source ring and agrees with Cech `H⁰` on
all field-valued fibres is finitely presented and projective of the Hilbert-polynomial
rank.  Every coefficient change of the algebraic graded model remains finite projective of
that rank. -/
theorem finitePresentation_projective_obj
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ)
    (hflat : Module.Flat R (M.obj (d : ℤ)))
    (haug : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      Function.Bijective (((M.baseChange κ).cechAug (d : ℤ)).hom))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    Module.FinitePresentation R (M.obj (d : ℤ)) ∧
      Module.Projective R (M.obj (d : ℤ)) ∧
      (∀ p : PrimeSpectrum R,
        Module.rankAtStalk (M.obj (d : ℤ)) p = P.hilbertNatValue d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Module.Finite A ((M.baseChange A).obj (d : ℤ)) ∧
          Module.Projective A ((M.baseChange A).obj (d : ℤ)) ∧
          ∀ p : PrimeSpectrum A,
            Module.rankAtStalk ((M.baseChange A).obj (d : ℤ)) p =
              P.hilbertNatValue d := by
  have hfinite : Module.Finite R (M.obj (d : ℤ)) := hM.1 (d : ℤ)
  letI : Module.Finite R (M.obj (d : ℤ)) := hfinite
  letI : Module.Flat R (M.obj (d : ℤ)) := hflat
  have hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (M.obj (d : ℤ)) p = P.hilbertNatValue d := by
    intro p
    rw [Module.rankAtStalk_eq p]
    exact finrank_obj_baseChange_eq_of_cechAug E hM P hP d haug hfib
      p.asIdeal.ResidueField
  have hfp : Module.FinitePresentation R (M.obj (d : ℤ)) :=
    Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_eq
      (P.hilbertNatValue d) hrank
  have hprojective : Module.Projective R (M.obj (d : ℤ)) :=
    Module.Projective.of_finite_of_flat_of_rankAtStalk_eq
      (P.hilbertNatValue d) hrank
  refine ⟨hfp, hprojective, hrank, ?_⟩
  intro A _ _
  simpa only [GradedModule.baseChange_obj] using
    Module.finite_projective_rankAtStalk_baseChange R A (M.obj (d : ℤ))
      hfinite hprojective (P.hilbertNatValue d) hrank

end GradedModule.CechSchemeGlobalSectionsComparison

open GradedModule.CechSchemeGlobalSectionsComparison

-- The polynomial `Proj` comparison and its fibrewise rank calculation are elaboration-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The kernel-route model carries several quantified twist instances.
set_option maxHeartbeats 2000000 in
/-- Uniform finite projectivity of the fixed graded piece of the canonical kernel-quotient
model, conditional on the two direct-module inputs not supplied by fibrewise regularity:
flatness of that piece and bijectivity of its Cech augmentation after every field-valued
coefficient change.  The uniform degree bound supplies all positive fibrewise vanishing. -/
theorem exists_bound_kernelQuotientModule_obj_finite_projective_rank_of_flat_of_cechAug
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
      let M := Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p
      Module.Flat R (M.obj (d : ℤ)) →
        (∀ (κ : Type u) [Field κ] [Algebra R κ],
          Function.Bijective (((M.baseChange κ).cechAug (d : ℤ)).hom)) →
        Module.FinitePresentation R (M.obj (d : ℤ)) ∧
          Module.Projective R (M.obj (d : ℤ)) ∧
          (∀ x : PrimeSpectrum R,
            Module.rankAtStalk (M.obj (d : ℤ)) x = P.hilbertNatValue d) ∧
          ∀ (A : Type u) [CommRing A] [Algebra R A],
            Module.Finite A ((M.baseChange A).obj (d : ℤ)) ∧
              Module.Projective A ((M.baseChange A).obj (d : ℤ)) ∧
              ∀ x : PrimeSpectrum A,
                Module.rankAtStalk ((M.baseChange A).obj (d : ℤ)) x =
                  P.hilbertNatValue d := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange_arbitrary
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro R _ Q hQfp q hq hQflat hHP d hd
  dsimp only
  intro hMflat haug
  haveI := hQfp
  haveI := hq
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  have hKqc₀ : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  letI hKqc₀' : (kernel p).IsQuasicoherent := hKqc₀
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent := fun e ↦
    twistModule_std_isQuasicoherent_of_isQuasicoherent n _ e
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  let C := cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary n R Q p
  have hMfg : GradedModule.IsFG M :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  exact C.finitePresentation_projective_obj hMfg P hHP d hMflat haug
    (hd₀ R Q hQfp q hq hQflat hHP d hd)

end AlgebraicGeometry.ProjectiveSpace

end

end
