module

public import StacksAndModuli.API.AffineOpenGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveStandardCoverBaseChange

/-!
# Global sections on polynomial projective space after field extension

This file applies the finite affine-cover base-change theorem to the standard
opens of polynomial projective space.  It identifies the canonical
scalar-extension map on global sections with a linear equivalence.

The chart and overlap inputs need **no flatness and no field hypothesis** — only that the
charts and their preimages are affine and the coefficient-change square is cartesian — so they
are also recorded separately, for an arbitrary ring map.  They are the "bottom map" of the
chart comparison that `HasGammaStarBaseChangeCechHgrZero` needs: `Hgr⁰` sees only the
localizations at the coordinates, where base change is unconditionally bijective, even though
global sections themselves do not commute with a non-flat coefficient change.

Main declarations:

* `Proj.ProjectiveCoverPullback.bijective_pullbackOpenSectionsBaseChange_chart` and
  `bijective_pullbackOpenSectionsBaseChange_overlap`;
* `Proj.polynomialProjectiveGlobalSectionsBaseChangeLinearEquiv`;
* `Proj.ProjectiveCoverPullback.polynomialProjectiveGlobalSectionsBaseChangeLinearEquivOfFlat`,
  the same for any flat coefficient change.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Global sections of a quasicoherent module on polynomial projective space
commute with extension of the coefficient field.  The underlying map is the
canonical scalar-extension map induced by the pullback adjunction unit. -/
noncomputable def Proj.polynomialProjectiveGlobalSectionsBaseChangeLinearEquiv
    (n : ℕ) {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (M : (Proj.ProjectiveCoverPullback.XR (R := K) n).Modules)
    [M.IsQuasicoherent] :
    let g := Proj.ProjectiveCoverPullback.g n f
    let N := (Scheme.Modules.pullback g).obj M
    let pK := Proj.ProjectiveCoverPullback.pR (R := K) n
    let pL := Proj.ProjectiveCoverPullback.pS (S := L) n
    letI : Algebra K L := f.toAlgebra
    letI : Module K Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pK M
    letI : Module L Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pL N
    L ⊗[K] Γ(M, ⊤) ≃ₗ[L] Γ(N, ⊤) := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of L := CommRingCat.ofHom f
  let g := Proj.ProjectiveCoverPullback.g n f
  let pK := Proj.ProjectiveCoverPullback.pR (R := K) n
  let pL := Proj.ProjectiveCoverPullback.pS (S := L) n
  let H := Proj.polynomialMap_isPullback (Fin (n + 1)) K f
  let I := ULift.{u} (Fin (n + 1))
  let U : I → (Proj.ProjectiveCoverPullback.XR (R := K) n).Opens :=
    fun i ↦ Proj.ProjectiveCoverPullback.UR (R := K) n i.down
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra K L := f.toAlgebra
  let hflat : Module.Flat K L := inferInstance
  letI : Module K Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pK M
  letI : Module L Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pL N
  have hchart (i : I) : Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pK pL H.w M (U i)) := by
    apply Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback
      φ g pK pL H.w M (U i)
      (Proj.ProjectiveCoverPullback.UR_isAffineOpen n i.down)
      (Proj.ProjectiveCoverPullback.US_isAffineOpen n f i.down)
    simpa only [Scheme.Modules.restrictToPreimage,
      Scheme.Hom.resLE_eq_morphismRestrict,
      Proj.ProjectiveCoverPullback.chartMap, U] using
        (Proj.ProjectiveCoverPullback.isPullback_chart n f i.down)
  have hover (ij : I × I) : Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pK pL H.w M (U ij.1 ⊓ U ij.2)) := by
    apply Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback
      φ g pK pL H.w M (U ij.1 ⊓ U ij.2)
      (Proj.ProjectiveCoverPullback.UR2_isAffineOpen n (ij.1.down, ij.2.down))
      (Proj.ProjectiveCoverPullback.US2_isAffineOpen n f (ij.1.down, ij.2.down))
    simpa only [Scheme.Modules.restrictToPreimage,
      Scheme.Hom.resLE_eq_morphismRestrict,
      Proj.ProjectiveCoverPullback.overlapMap, U] using
        (Proj.ProjectiveCoverPullback.isPullback_overlap n f
          (ij.1.down, ij.2.down))
  have hU : ⨆ i : I, U i = ⊤ := by
    apply le_antisymm le_top
    rw [← Proj.iSup_polynomialStandardOpen_eq_top n K]
    exact iSup_le fun i ↦ le_iSup (fun j : I ↦ U j) (ULift.up i)
  exact Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearEquiv_of_finiteCover
    φ hflat g pK pL H.w M U hU hchart hover

namespace Proj.ProjectiveCoverPullback

variable (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **Chart-level base change for an arbitrary coefficient change.**  On a standard chart of
polynomial projective space, extension of scalars on sections is bijective — no flatness
hypothesis, because the chart and its preimage are affine and the square is cartesian. -/
theorem bijective_pullbackOpenSectionsBaseChange_chart
    (M : (XR (R := R) n).Modules) [M.IsQuasicoherent] (i : Fin (n + 1)) :
    Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom f) (g n f)
        (pR (R := R) n) (pS (S := S) n)
        (Proj.polynomialMap_isPullback (Fin (n + 1)) R f).w M (UR (R := R) n i)) := by
  apply Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback
    (CommRingCat.ofHom f) (g n f) (pR (R := R) n) (pS (S := S) n) _ M (UR (R := R) n i)
    (UR_isAffineOpen n i) (US_isAffineOpen n f i)
  simpa only [Scheme.Modules.restrictToPreimage, Scheme.Hom.resLE_eq_morphismRestrict,
    chartMap] using isPullback_chart n f i

/-- **Overlap-level base change for an arbitrary coefficient change.** -/
theorem bijective_pullbackOpenSectionsBaseChange_overlap
    (M : (XR (R := R) n).Modules) [M.IsQuasicoherent] (ij : Fin (n + 1) × Fin (n + 1)) :
    Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom f) (g n f)
        (pR (R := R) n) (pS (S := S) n)
        (Proj.polynomialMap_isPullback (Fin (n + 1)) R f).w M
        (UR (R := R) n ij.1 ⊓ UR (R := R) n ij.2)) := by
  apply Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback
    (CommRingCat.ofHom f) (g n f) (pR (R := R) n) (pS (S := S) n) _ M
    (UR (R := R) n ij.1 ⊓ UR (R := R) n ij.2)
    (UR2_isAffineOpen n ij) (US2_isAffineOpen n f ij)
  simpa only [Scheme.Modules.restrictToPreimage, Scheme.Hom.resLE_eq_morphismRestrict,
    overlapMap] using isPullback_overlap n f ij

/-- **Global sections on polynomial projective space commute with any *flat* coefficient
change.**  This is `Proj.polynomialProjectiveGlobalSectionsBaseChangeLinearEquiv` with the
field hypothesis replaced by flatness — the chart and overlap inputs never used it. -/
noncomputable def polynomialProjectiveGlobalSectionsBaseChangeLinearEquivOfFlat
    (M : (XR (R := R) n).Modules) [M.IsQuasicoherent]
    (hflat : letI : Algebra R S := f.toAlgebra; Module.Flat R S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule (pR (R := R) n) M
    letI : Module S Γ((Scheme.Modules.pullback (g n f)).obj M, ⊤) :=
      Scheme.Modules.globalSectionsModule (pS (S := S) n)
        ((Scheme.Modules.pullback (g n f)).obj M)
    S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ((Scheme.Modules.pullback (g n f)).obj M, ⊤) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule (pR (R := R) n) M
  letI : Module S Γ((Scheme.Modules.pullback (g n f)).obj M, ⊤) :=
    Scheme.Modules.globalSectionsModule (pS (S := S) n)
      ((Scheme.Modules.pullback (g n f)).obj M)
  let I := ULift.{u} (Fin (n + 1))
  let U : I → (XR (R := R) n).Opens := fun i ↦ UR (R := R) n i.down
  have hU : ⨆ i : I, U i = ⊤ := by
    apply le_antisymm le_top
    rw [← Proj.iSup_polynomialStandardOpen_eq_top n R]
    exact iSup_le fun i ↦ le_iSup (fun j : I ↦ U j) (ULift.up i)
  exact Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearEquiv_of_finiteCover
    (CommRingCat.ofHom f) hflat (g n f) (pR (R := R) n) (pS (S := S) n)
    (Proj.polynomialMap_isPullback (Fin (n + 1)) R f).w M U hU
    (fun i ↦ bijective_pullbackOpenSectionsBaseChange_chart n f M i.down)
    (fun ij ↦ bijective_pullbackOpenSectionsBaseChange_overlap n f M (ij.1.down, ij.2.down))

end Proj.ProjectiveCoverPullback

end AlgebraicGeometry
