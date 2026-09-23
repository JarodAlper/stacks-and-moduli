module

public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.API.FlatColimit
public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.TwistMonomialSections

/-!
# Surjectivity of an affine quasicoherent map from its residue fibres

Supporting API with no Stacks Project counterpart.

For a morphism of quasicoherent modules on `Spec R` whose target has finite global
sections, surjectivity on global sections can be checked after pullback to every closed
residue fibre.  The proof combines canonical affine global-sections base change with
Nakayama's lemma for a map into a finite module.

Main declaration:
- `AlgebraicGeometry.Scheme.Modules.appTop_surjective_of_pullback_quotient_maximal`.
- `Scheme.Modules.app_affineOpen_surjective_of_coordinate_residue_pullbacks`.
- `Scheme.Modules.app_affineOpen_surjective_of_coordinate_residue_pullbacks_of_rank`.
- `Scheme.Modules.epi_of_coordinate_residue_pullbacks_of_rank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory TensorProduct
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- On affine spectra, surjectivity of a scalar-extended map on global sections is
equivalent to surjectivity of the global-sections map of the pulled-back sheaf morphism.
The statement is recorded in the direction used by residue-field Nakayama. -/
lemma baseChange_specSectionsLinearMap_surjective_of_pullback
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N)
    (h : Function.Surjective
      (specSectionsLinearMap ((pullback (Spec.map f)).map p))) :
    letI : Algebra R A := f.hom.toAlgebra
    Function.Surjective (LinearMap.baseChange A (specSectionsLinearMap p)) := by
  letI : Algebra R A := f.hom.toAlgebra
  let PM := (pullback (Spec.map f)).obj M
  let PN := (pullback (Spec.map f)).obj N
  letI : Module R Γ(PM, ⊤) := Module.compHom _ f.hom
  letI : Module R Γ(PN, ⊤) := Module.compHom _ f.hom
  letI : IsScalarTower R A Γ(PM, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R A Γ(PN, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let cM := specPullbackSectionsBaseChangeLinearMap f M
  let cN := specPullbackSectionsBaseChangeLinearMap f N
  have hcM : Function.Bijective cM :=
    specPullbackSectionsBaseChangeLinearMap_bijective f M
  have hcN : Function.Bijective cN :=
    specPullbackSectionsBaseChangeLinearMap_bijective f N
  intro y
  obtain ⟨z, hz⟩ := h (cN y)
  obtain ⟨x, rfl⟩ := hcM.2 z
  refine ⟨x, hcN.1 ?_⟩
  have hnat := DFunLike.congr_fun
    (specPullbackSectionsBaseChangeLinearMap_naturality f p) x
  change specSectionsLinearMap ((pullback (Spec.map f)).map p) (cM x) =
      cN ((LinearMap.lTensor A (specSectionsLinearMap p)) x) at hnat
  rw [hz] at hnat
  simpa only [LinearMap.baseChange_eq_ltensor] using hnat.symm

/-- **Residue-fibre Nakayama for an affine quasicoherent morphism.**  If the target has
finite global sections and the pullback of `p` to `Spec (R / m)` is surjective on global
sections for every maximal ideal `m`, then `p` is surjective on global sections over
`Spec R` itself. -/
theorem appTop_surjective_of_pullback_quotient_maximal
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N) [Module.Finite R Γ(N, ⊤)]
    (h : ∀ m : Ideal R, m.IsMaximal →
      Function.Surjective
        (specSectionsLinearMap ((pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))).map p))) :
    Function.Surjective (p.app ⊤).hom := by
  change Function.Surjective (specSectionsLinearMap p)
  apply Module.surjective_of_forall_quotient_maximal (specSectionsLinearMap p)
  intro m hm
  exact baseChange_specSectionsLinearMap_surjective_of_pullback
    (CommRingCat.ofHom (Ideal.Quotient.mk m)) p (h m hm)

/-- Residue-fibre Nakayama on an affine open of an arbitrary scheme.  The morphism is
first restricted to the affine open and transported across its canonical spectrum
isomorphism.  Thus the fibre hypothesis is stated on a literal `Spec R`, where the
coefficient map to `R / m` is definitionally the quotient map. -/
theorem app_affineOpen_surjective_of_coordinate_residue_pullbacks
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N) (U : X.affineOpens)
    (hfinite :
      let NU := (restrictFunctor U.1.ι).obj N
      let QN := (restrictFunctor U.2.isoSpec.inv).obj NU
      Module.Finite Γ(X, U.1) (moduleSpecΓFunctor.obj QN))
    (h : ∀ m : Ideal Γ(X, U.1), m.IsMaximal →
      let q := (restrictFunctor U.2.isoSpec.inv).map
        ((restrictFunctor U.1.ι).map p)
      Function.Surjective
        (specSectionsLinearMap ((pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))).map q))) :
    Function.Surjective (p.app U.1).hom := by
  let q := (restrictFunctor U.2.isoSpec.inv).map
    ((restrictFunctor U.1.ι).map p)
  let NU := (restrictFunctor U.1.ι).obj N
  let QN := (restrictFunctor U.2.isoSpec.inv).obj NU
  have hsource : U.2.isoSpec.inv ''ᵁ
      (⊤ : (Spec (.of Γ(X, U.1))).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hopen : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  letI : Module.Finite Γ(X, U.1) Γ(QN, ⊤) := hfinite
  have hq : Function.Surjective (q.app ⊤).hom :=
    appTop_surjective_of_pullback_quotient_maximal q (fun m hm ↦ h m hm)
  change Function.Surjective
    (p.app (U.1.ι ''ᵁ (U.2.isoSpec.inv ''ᵁ ⊤))).hom at hq
  rw [hsource, hopen] at hq
  exact hq

/-- The finite-target hypothesis in
`app_affineOpen_surjective_of_coordinate_residue_pullbacks` is automatic when the target
is a quasicoherent vector bundle of fixed rank. -/
theorem app_affineOpen_surjective_of_coordinate_residue_pullbacks_of_rank
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {q : ℕ}
    (p : M ⟶ N) (hN : IsProjectiveOfRank q N) (U : X.affineOpens)
    (h : ∀ m : Ideal Γ(X, U.1), m.IsMaximal →
      let pU := (restrictFunctor U.2.isoSpec.inv).map
        ((restrictFunctor U.1.ι).map p)
      Function.Surjective
        (specSectionsLinearMap ((pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))).map pU))) :
    Function.Surjective (p.app U.1).hom := by
  let NU := (restrictFunctor U.1.ι).obj N
  let QN := (restrictFunctor U.2.isoSpec.inv).obj NU
  have hPullU : IsFiniteLocallyFree ((pullback U.1.ι).obj N) :=
    hN.isFiniteLocallyFree.pullback U.1.ι
  have hNU : IsFiniteLocallyFree NU :=
    hPullU.of_iso ((restrictFunctorIsoPullback U.1.ι).app N).symm
  have hPullSpec : IsFiniteLocallyFree ((pullback U.2.isoSpec.inv).obj NU) :=
    hNU.pullback_of_isIso U.2.isoSpec.inv
  have hQN : IsFiniteLocallyFree QN :=
    hPullSpec.of_iso ((restrictFunctorIsoPullback U.2.isoSpec.inv).app NU).symm
  have hfinite : Module.Finite Γ(X, U.1) (moduleSpecΓFunctor.obj QN) :=
    (moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree QN hQN).1
  exact app_affineOpen_surjective_of_coordinate_residue_pullbacks
    p U hfinite h

/-- A quasicoherent morphism with finite-locally-free target is an epimorphism if, on every
affine coordinate chart, its pullback to every closed residue fibre is surjective on global
sections.  This is the scheme-wide form of residue-fibre Nakayama used for multiplication
maps between projective pushforwards. -/
theorem epi_of_coordinate_residue_pullbacks_of_rank
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {q : ℕ}
    (p : M ⟶ N) (hN : IsProjectiveOfRank q N)
    (h : ∀ (U : X.affineOpens) (m : Ideal Γ(X, U.1)), m.IsMaximal →
      let pU := (restrictFunctor U.2.isoSpec.inv).map
        ((restrictFunctor U.1.ι).map p)
      Function.Surjective
        (specSectionsLinearMap ((pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))).map pU))) :
    Epi p := by
  apply epi_of_surjective_on_affineOpens p
  intro U
  exact app_affineOpen_surjective_of_coordinate_residue_pullbacks_of_rank
    p hN U (h U)

end AlgebraicGeometry.Scheme.Modules

end

end
