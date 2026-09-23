module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.RingTheory.Flat.Basic

/-!
# Relative flatness and twisting on projective space

Tensoring a quasicoherent module on relative projective space with a twisting sheaf
preserves flatness over the base.  The proof uses the standard coordinate cover, on
which every twisting sheaf is trivial.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If two module sheaves become isomorphic after pullback along an open immersion,
then flatness of their sections on the corresponding image open is equivalent. -/
lemma sections_flat_of_pullback_iso_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    (e : (pullback f).obj M ≅ (pullback f).obj N)
    (U : X.Opens) (a : R₀ →+* Γ(Y, f ''ᵁ U))
    (hflat :
      letI := Module.compHom Γ(M, f ''ᵁ U) a
      Module.Flat R₀ Γ(M, f ''ᵁ U)) :
    letI := Module.compHom Γ(N, f ''ᵁ U) a
    Module.Flat R₀ Γ(N, f ''ᵁ U) := by
  let b : R₀ →+* Γ(X, U) := (f.appIso U).hom.hom.comp a
  have hMpull :
      letI := Module.compHom Γ((pullback f).obj M, U) b
      Module.Flat R₀ Γ((pullback f).obj M, U) :=
    pullback_openImmersion_sections_flat_restrictScalars f M U a hflat
  have hNpull :
      letI := Module.compHom Γ((pullback f).obj N, U) b
      Module.Flat R₀ Γ((pullback f).obj N, U) :=
    sections_flat_of_iso_restrictScalars e U b hMpull
  have hpush := sections_flat_of_pullback_openImmersion f N U b hNpull
  apply Module.Flat.compHom_congr
      ((f.appIso U).inv.hom.comp b) a
  · ext r
    simp [b]
  · exact hpush

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Twisting a quasicoherent module on relative projective space preserves its
flatness over the base. -/
theorem FlatOver.projectiveSpaceOverTwistModule
    (n : ℕ) (S : Scheme.{u})
    (Q : (Scheme.projectiveSpaceOver n S).Modules) [Q.IsQuasicoherent]
    (hQ : Q.FlatOver (Scheme.projectiveSpaceOverπ n S)) (d : ℤ) :
    (Scheme.projectiveSpaceOverTwistModule Q d).FlatOver
      (Scheme.projectiveSpaceOverπ n S) := by
  let X := Scheme.projectiveSpaceOver n S
  let p := Scheme.projectiveSpaceOverπ n S
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let f : X ⟶ Proj 𝒜 := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
  let W (j : ULift.{u} (Fin (n + 1))) : X.Opens :=
    f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  have hW : ⨆ j, W j = ⊤ := by
    dsimp [W]
    rw [← Scheme.Hom.preimage_iSup, iSup_ulift]
    rw [ProjectiveSpectrum.Twist.polynomialCoordinateCover_iSup_eq_top,
      Scheme.Hom.preimage_top]
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  intro U V hUV
  apply FlatOver.flat_sections_affine_of_pointwise_basicOpen p Qd U V hUV
  intro x hxU
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  rw [Opens.mem_iSup] at hxW
  obtain ⟨j, hxj⟩ := hxW
  obtain ⟨r, hrW, hxr⟩ := U.2.exists_basicOpen_le
    (show W j from ⟨x, hxj⟩) hxU
  refine ⟨r, hxr, ?_⟩
  let jW := (W j).ι
  let D : (W j).toScheme.Opens := jW ⁻¹ᵁ X.basicOpen r
  have himage : jW ''ᵁ D = X.basicOpen r := by
    dsimp only [D, jW]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hrW
  let hrV : X.basicOpen r ≤ p ⁻¹ᵁ V.1 :=
    (X.basicOpen_le r).trans hUV
  let a : Γ(S, V.1) →+* Γ(X, X.basicOpen r) :=
    (p.appLE V.1 (X.basicOpen r) hrV).hom
  have hflatB :
      letI := Module.compHom Γ(Q, X.basicOpen r) a
      Module.Flat Γ(S, V.1) Γ(Q, X.basicOpen r) := by
    have h := hQ (X.affineBasicOpen r) V hrV
    change
      letI := Module.compHom Γ(Q, X.basicOpen r) a
      Module.Flat Γ(S, V.1) Γ(Q, X.basicOpen r) at h
    exact h
  have hflatImage :
      let a' : Γ(S, V.1) →+* Γ(X, jW ''ᵁ D) := himage.symm ▸ a
      letI := Module.compHom Γ(Q, jW ''ᵁ D) a'
      Module.Flat Γ(S, V.1) Γ(Q, jW ''ᵁ D) :=
    sections_flat_of_eq Q (X.basicOpen r) (jW ''ᵁ D)
      himage.symm a hflatB
  let Qj := (restrictFunctor jW).obj Q
  let Lj := (restrictFunctor jW).obj
    (Scheme.projectiveSpaceOverTwist n S d)
  let hX : MvPolynomial.X j.down ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j.down)
  let eL : Lj ≅ SheafOfModules.unit (W j).toScheme.ringCatSheaf := by
    dsimp [Lj, Scheme.projectiveSpaceOverTwist, W, f, X, 𝒜]
    exact ProjectiveSpectrum.Twist.restrictPullbackTwistIsoUnitOfHom
      (Limits.pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) d hX
  let eRestrict : (restrictFunctor jW).obj Qd ≅ Qj :=
    restrictTensorIso jW Q
        (Scheme.projectiveSpaceOverTwist n S d) ≪≫
      tensorRightIso Qj eL ≪≫ tensorUnitIso Qj
  let ePull : (pullback jW).obj Qd ≅ (pullback jW).obj Q :=
    (restrictFunctorIsoPullback jW).symm.app Qd ≪≫ eRestrict ≪≫
      (restrictFunctorIsoPullback jW).app Q
  have hflatImageQd :
      let a' : Γ(S, V.1) →+* Γ(X, jW ''ᵁ D) := himage.symm ▸ a
      letI := Module.compHom Γ(Qd, jW ''ᵁ D) a'
      Module.Flat Γ(S, V.1) Γ(Qd, jW ''ᵁ D) :=
    sections_flat_of_pullback_iso_restrictScalars jW Q Qd ePull.symm D
      (himage.symm ▸ a) hflatImage
  have hflatB' := sections_flat_of_eq Qd (jW ''ᵁ D)
    (X.basicOpen r) himage (himage.symm ▸ a) hflatImageQd
  apply Module.Flat.compHom_congr
      (himage ▸ (himage.symm ▸ a))
      (p.appLE V.1 (X.basicOpen r) hrV).hom
  · have hcancel : himage ▸ (himage.symm ▸ a) = a := by
      apply eq_of_heq
      exact (@eqRec_heq X.Opens
        (fun E ↦ Γ(S, V.1) →+* Γ(X, E))
        (jW ''ᵁ D) (X.basicOpen r) himage
        (himage.symm ▸ a)).trans
          (@eqRec_heq X.Opens
            (fun E ↦ Γ(S, V.1) →+* Γ(X, E))
            (X.basicOpen r) (jW ''ᵁ D) himage.symm a)
    exact hcancel.trans rfl
  · exact hflatB'

end AlgebraicGeometry.Scheme.Modules

end
