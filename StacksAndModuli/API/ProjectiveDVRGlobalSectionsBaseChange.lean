module

public import StacksAndModuli.API.ProjectiveDVRGlobalSectionsLocalization
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso

/-!
# Generic-fibre base change for projective-space global sections over a DVR

This file transports the localization calculation on the raw scheme-theoretic generic
fibre across its canonical isomorphism with projective space over the fraction field.
The resulting equivalence lands in the standard projective-space base change used by
Hilbert functions and Hilbert polynomials.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical generic-fibre isomorphism preserves the projection to the fraction
field. -/
@[reassoc (attr := simp)]
theorem projectiveSpaceGenericFiberIso_inv_π
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R] :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let φ : R ⟶ CommRingCat.of (FractionRing R) :=
      CommRingCat.ofHom (algebraMap R (FractionRing R))
    let j₀ := Spec.map φ
    (projectiveSpaceGenericFiberIso n R).inv ≫
        Limits.pullback.snd p j₀ =
      Scheme.projectiveSpaceOverπ n
        (Spec (CommRingCat.of (FractionRing R))) := by
  dsimp only
  unfold projectiveSpaceGenericFiberIso
  rw [Iso.trans_inv, Category.assoc,
    Limits.pullbackSymmetry_inv_comp_snd]
  let φ : R ⟶ CommRingCat.of (FractionRing R) :=
    CommRingCat.ofHom (algebraMap R (FractionRing R))
  let g : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec R := Spec.map φ
  change (Scheme.projectiveSpaceOverBaseChangeIso n g).inv ≫
      Limits.pullback.fst g (Scheme.projectiveSpaceOverπ n (Spec R)) = _
  rw [← cancel_epi (Scheme.projectiveSpaceOverBaseChangeIso n g).hom]
  simp

/-- For a quasicoherent module on projective space over a DVR, global sections commute
with passage to the fraction field.  The target is the standard pullback sheaf on
`ℙⁿ_{Frac(R)}`, rather than a raw categorical pullback model of the generic fibre. -/
noncomputable def fractionRingTensorGlobalSectionsLinearEquiv_projectiveSpaceBaseChange
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let φ : R ⟶ CommRingCat.of (FractionRing R) :=
      CommRingCat.ofHom (algebraMap R (FractionRing R))
    let j₀ := Spec.map φ
    let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Module (FractionRing R) Γ(NK, ⊤) :=
      globalSectionsModule
        (Scheme.projectiveSpaceOverπ n
          (Spec (CommRingCat.of (FractionRing R)))) NK
    (FractionRing R ⊗[R] Γ(N, ⊤)) ≃ₗ[FractionRing R] Γ(NK, ⊤) := by
  dsimp only
  let K := FractionRing R
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let φ : R ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap R K)
  let j₀ : Spec (CommRingCat.of K) ⟶ Spec R := Spec.map φ
  let XK := Limits.pullback p j₀
  let j := Limits.pullback.fst p j₀
  let q := Limits.pullback.snd p j₀
  let PK := Scheme.projectiveSpaceOver n (Spec (CommRingCat.of K))
  let pK := Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of K))
  let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
  let Nraw := (pullback j).obj N
  let e := projectiveSpaceGenericFiberIso n R
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing K
  letI : IsOpenImmersion j := inferInstance
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Module K Γ(Nraw, ⊤) := globalSectionsModule q Nraw
  letI : Module K Γ(NK, ⊤) := globalSectionsModule pK NK
  let e₁aux := fractionRingTensorGlobalSectionsLinearEquiv_genericFiber
    n R N ϖ hϖ
  let e₁ : (K ⊗[R] Γ(N, ⊤)) ≃ₗ[K] Γ(Nraw, ⊤) :=
    { toEquiv := e₁aux.toEquiv
      map_add' := e₁aux.map_add
      map_smul' := fun k m ↦ by
        change e₁aux (k • m) = (baseRingHom q).hom k • e₁aux m
        calc
          e₁aux (k • m) =
              projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ k •
                e₁aux m := e₁aux.map_smul k m
          _ = (baseRingHom q).hom k • e₁aux m := by
            exact congrArg (fun a : Γ(XK, ⊤) ↦ a • e₁aux m)
              (RingHom.congr_fun
                (projectiveSpaceFractionRingToGenericFiber_eq_baseRingHom
                  n R ϖ hϖ) k) }
  let eraw : (pullback e.inv).obj Nraw ≅ NK :=
    pullbackProjectiveSpaceGenericFiberIso n R N
  let e₂aux := pullbackGlobalSectionsViaIsoLinearEquiv e.inv q Nraw eraw
  let e₂ : Γ(Nraw, ⊤) ≃ₗ[K] Γ(NK, ⊤) :=
    { toEquiv := e₂aux.toEquiv
      map_add' := e₂aux.map_add
      map_smul' := fun k m ↦ by
        have hm := e₂aux.map_smul k m
        change e₂aux (k • m) = (baseRingHom pK).hom k • e₂aux m
        change e₂aux (k • m) =
          (baseRingHom (e.inv ≫ q)).hom k • e₂aux m at hm
        have hbase : e.inv ≫ q = pK :=
          projectiveSpaceGenericFiberIso_inv_π n R
        have hmap : (baseRingHom (e.inv ≫ q)).hom k =
            (baseRingHom pK).hom k := by
          rw [hbase]
        exact hm.trans
          (congrArg (fun a : Γ(PK, ⊤) ↦ a • e₂aux m) hmap) }
  exact e₁.trans e₂

/-- The rank of a finite projective global-section module over the DVR is the
dimension of global sections after the standard projective-space base change to the
fraction field. -/
theorem finrank_projectiveSpaceBaseChange_globalSections_eq
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Finite R Γ(N, ⊤))
    (hprojective :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Projective R Γ(N, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let φ : R ⟶ CommRingCat.of (FractionRing R) :=
      CommRingCat.ofHom (algebraMap R (FractionRing R))
    let j₀ := Spec.map φ
    let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Module (FractionRing R) Γ(NK, ⊤) :=
      globalSectionsModule
        (Scheme.projectiveSpaceOverπ n
          (Spec (CommRingCat.of (FractionRing R)))) NK
    Module.finrank (FractionRing R) Γ(NK, ⊤) =
      Module.finrank R Γ(N, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let φ : R ⟶ CommRingCat.of (FractionRing R) :=
    CommRingCat.ofHom (algebraMap R (FractionRing R))
  let j₀ := Spec.map φ
  let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Module.Finite R Γ(N, ⊤) := hfinite
  letI : Module.Projective R Γ(N, ⊤) := hprojective
  letI : Module (FractionRing R) Γ(NK, ⊤) :=
    globalSectionsModule
      (Scheme.projectiveSpaceOverπ n
        (Spec (CommRingCat.of (FractionRing R)))) NK
  rw [← (fractionRingTensorGlobalSectionsLinearEquiv_projectiveSpaceBaseChange
    n R N ϖ hϖ).finrank_eq]
  exact Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing

end AlgebraicGeometry.Scheme.Modules

end
