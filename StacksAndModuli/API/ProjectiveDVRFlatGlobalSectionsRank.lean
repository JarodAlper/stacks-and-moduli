module

public import StacksAndModuli.API.FlatOverGlobalSectionsDVR
public import StacksAndModuli.API.ProjectiveDVRGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveTwistFlatOver

/-!
# Global-section rank for flat families on projective space over a DVR

This file combines two ingredients used in the DVR step of the projectivity proof:
finite global sections of a flat family are projective, and their rank is detected by
global sections on the scheme-theoretic generic fibre.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasicoherent module on projective space over a DVR that is flat over the
base, finiteness of global sections suffices to identify their rank with the dimension
of global sections on the scheme-theoretic generic fibre. -/
theorem FlatOver.finrank_genericFiber_globalSections_eq_of_finite
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (hflat : N.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Finite R Γ(N, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let XK := Limits.pullback p j₀
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Algebra (FractionRing R) Γ(XK, ⊤) :=
      (projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ).toAlgebra
    letI : Module (FractionRing R) Γ((Scheme.Modules.pullback j).obj N, ⊤) :=
      Module.compHom _ (algebraMap (FractionRing R) Γ(XK, ⊤))
    Module.finrank (FractionRing R) Γ((Scheme.Modules.pullback j).obj N, ⊤) =
      Module.finrank R Γ(N, ⊤) := by
  have hprojective := hflat.projective_globalSections_of_finite ϖ hϖ hfinite
  exact finrank_genericFiber_globalSections_eq n R N ϖ hϖ hfinite hprojective

/-- In the standard projective-space model of the generic fibre, flatness and
finiteness of global sections identify their relative rank with the dimension after
base change to the fraction field. -/
theorem FlatOver.finrank_projectiveSpaceBaseChange_globalSections_eq_of_finite
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (hflat : N.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Finite R Γ(N, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let φ : R ⟶ CommRingCat.of (FractionRing R) :=
      CommRingCat.ofHom (algebraMap R (FractionRing R))
    let j₀ := Spec.map φ
    let NK := (Scheme.Modules.pullback
      (Scheme.projectiveSpaceOverMap n j₀)).obj N
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Module (FractionRing R) Γ(NK, ⊤) :=
      globalSectionsModule
        (Scheme.projectiveSpaceOverπ n
          (Spec (CommRingCat.of (FractionRing R)))) NK
    Module.finrank (FractionRing R) Γ(NK, ⊤) =
      Module.finrank R Γ(N, ⊤) := by
  have hprojective := hflat.projective_globalSections_of_finite ϖ hϖ hfinite
  exact finrank_projectiveSpaceBaseChange_globalSections_eq
    n R N ϖ hϖ hfinite hprojective

/-- For a flat quasicoherent `Q` with finite global sections after twisting on
projective space over a DVR, the rank of `H⁰(Q(d))` is the Hilbert function of the
pullback of `Q` to projective space over the fraction field. -/
theorem FlatOver.finrank_twistedGlobalSections_eq_hilbertFunctionOver_fractionRing_of_finite
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [Q.IsQuasicoherent]
    (d : ℤ)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite :
      let Qd := Scheme.projectiveSpaceOverTwistModule Q d
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤)) :
    let Qd := Scheme.projectiveSpaceOverTwistModule Q d
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    letI : Module R Γ(Qd, ⊤) := globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
    Module.finrank R Γ(Qd, ⊤) = Scheme.hilbertFunctionOver QK d := by
  dsimp only
  let K := FractionRing R
  let φ : R ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap R K)
  let j₀ : Spec (CommRingCat.of K) ⟶ Spec R := Spec.map φ
  let f := Scheme.projectiveSpaceOverMap n j₀
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let pK := Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of K))
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  let QK := (pullback f).obj Q
  let QKd := Scheme.projectiveSpaceOverTwistModule QK d
  let NK := (pullback f).obj Qd
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing K
  letI : Module R Γ(Qd, ⊤) := globalSectionsModule p Qd
  letI : Module K Γ(NK, ⊤) := globalSectionsModule pK NK
  letI : Module K Γ(QKd, ⊤) := globalSectionsModule pK QKd
  have hflatQd := hflat.projectiveSpaceOverTwistModule n (Spec R) Q d
  have hrank := hflatQd.finrank_projectiveSpaceBaseChange_globalSections_eq_of_finite
    n R Qd ϖ hϖ hfinite
  let e : NK ≅ QKd :=
    Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
      n j₀ Q d
  let eΓ := globalSectionsLinearEquivOfIso pK e
  change Module.finrank R Γ(Qd, ⊤) = Module.finrank K Γ(QKd, ⊤)
  exact hrank.symm.trans eΓ.finrank_eq

end AlgebraicGeometry.Scheme.Modules

end
