module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.ProjTwistMulHom

/-!
# Coefficient change intertwines multiplication by homogeneous elements

`ProjectiveSpectrum.Twist.twistToPushforwardComparison` sends a section of `𝒪_{Proj 𝒜}(d)`,
locally a homogeneous fraction, to the fraction obtained by applying a graded ring
homomorphism `f : 𝒜 →+*ᵍ ℬ` to numerator and denominator.  Multiplication by a homogeneous
`p : 𝒜 m` multiplies that fraction by `p / 1`.  The two therefore commute, with `p` replaced
by `f p` on the target:

`mulHom 𝒜 p d dc ≫ comparison = comparison ≫ pushforward (mulHom ℬ (f p) d dc)`.

This is the compatibility that makes `Γ_*` — whose degree-raising maps are exactly these
multiplications — functorial for coefficient change, and hence the `comm` field of the
comparison morphism `Γ_*(F).baseChange S ⟶ Γ_*(F_S)`.

Main declarations:

* `ProjectiveSpectrum.Twist.comapTwistAddHom_mulSectionHom`;
* `ProjectiveSpectrum.Twist.mulHom_comp_twistToPushforwardComparison`;
* `ProjectiveSpectrum.Twist.pullback_map_mulHom_comp_pullbackComparison`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal HomogeneousLocalization
open TopologicalSpace Opposite TopCat
open ProjectiveSpectrum

universe u

namespace ProjectiveSpectrum.Twist

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The image of a homogeneous element under a graded ring homomorphism, as an element of
the corresponding graded piece. -/
def gradedImage (f : 𝒜 →+*ᵍ ℬ) {m : ℕ} (p : 𝒜 m) : ℬ m :=
  ⟨f (p : A), (f.gradedAddHom m p).2⟩

omit [GradedRing 𝒜] [GradedRing ℬ] in
@[simp]
theorem gradedImage_coe (f : 𝒜 →+*ᵍ ℬ) {m : ℕ} (p : 𝒜 m) :
    ((gradedImage f p : ℬ m) : B) = f (p : A) := rfl

/-- **Coefficient change intertwines multiplication by `p` with multiplication by `f p`**, at
the level of sections. -/
theorem comapTwistAddHom_mulSectionHom
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {m : ℕ} (p : 𝒜 m) (d dc : ℤ)
    (hdc : dc = d + (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : (sheafInType 𝒜 d).1.obj (.op U)) :
    comapTwistAddHom f hf dc U V hUV (mulSectionHom 𝒜 p d dc hdc (.op U) s)
      = mulSectionHom ℬ (gradedImage f p) d dc hdc (.op V)
        (comapTwistAddHom f hf d U V hUV s) := by
  refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
  set x : U := ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩ with hx
  set φ := Localization.localRingHom
    (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal f.toRingHom rfl with hφ
  have hleft : (((comapTwistAddHom f hf dc U V hUV)
      (mulSectionHom 𝒜 p d dc hdc (.op U) s)).1 y :
        Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl)
      = φ ((s.1 x).1 * Localization.mk (p : A) 1) :=
    comapTwistAddHom_apply_val f hf dc U V hUV _ y
  have hright : ((mulSectionHom ℬ (gradedImage f p) d dc hdc (.op V)
      ((comapTwistAddHom f hf d U V hUV) s)).1 y :
        Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl)
      = φ ((s.1 x).1) * Localization.mk (f (p : A)) 1 := by
    change (((comapTwistAddHom f hf d U V hUV) s).1 y).1 * _ = _
    rw [comapTwistAddHom_apply_val f hf d U V hUV s y, homogeneousSection_apply]
    rfl
  rw [hleft, hright, map_mul]
  congr 1
  rw [hφ, Localization.localRingHom_mk]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, by simp⟩)

/-- **Coefficient change intertwines multiplication by `p` with multiplication by `f p`.** -/
theorem mulHom_comp_twistToPushforwardComparison
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {m : ℕ} (p : 𝒜 m) (d dc : ℤ)
    (hdc : dc = d + (m : ℤ)) :
    mulHom 𝒜 p d dc hdc ≫ twistToPushforwardComparison f hf dc
      = twistToPushforwardComparison f hf d ≫
        (Scheme.Modules.pushforward (Proj.map f hf)).map
          (mulHom ℬ (gradedImage f p) d dc hdc) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact comapTwistAddHom_mulSectionHom f hf p d dc hdc U.unop
    ((Proj.map f hf) ⁻¹ᵁ U.unop) (by rfl) s

/-- **The adjoint form: the pullback comparison intertwines multiplication by `p` with
multiplication by `f p`.**

This is the shape the twist of a general sheaf needs, since
`ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom` is built from
`pullbackComparison`. -/
theorem pullback_map_mulHom_comp_pullbackComparison
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {m : ℕ} (p : 𝒜 m) (d dc : ℤ)
    (hdc : dc = d + (m : ℤ)) :
    (Scheme.Modules.pullback (Proj.map f hf)).map (mulHom 𝒜 p d dc hdc) ≫
        pullbackComparison f hf dc
      = pullbackComparison f hf d ≫ mulHom ℬ (gradedImage f p) d dc hdc := by
  have hadj := mulHom_comp_twistToPushforwardComparison f hf p d dc hdc
  have hL := congrArg
    (fun u : twist 𝒜 d ⟶ (Scheme.Modules.pushforward (Proj.map f hf)).obj (twist ℬ dc) ↦
      ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv
        (twist 𝒜 d) (twist ℬ dc)).symm u) hadj
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm] at hL
  exact hL

end ProjectiveSpectrum.Twist

end

end
