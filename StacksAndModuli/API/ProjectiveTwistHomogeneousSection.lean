module

public import StacksAndModuli.API.ProjectiveTwistGlobalSections
public import StacksAndModuli.API.ProjTwistMulHom

/-!
# Sections of `𝒪(e)` from homogeneous forms, with the degree as a parameter

`ProjectiveSpectrum.Twist.homogeneousSection` sends a homogeneous `p` of degree `m : ℕ` to a
section of `𝒪(m)`.  The comparison of a *graded module* with `Γ_*` needs it in degree
`e : ℤ` presented together with an equation `e = m`, so that no `eqToHom` transport of a
section ever appears: transports across a degree equality are the standard source of
`motive is not type correct` in this development (see the root INSIGHTS).

Main declarations:

* `ProjectiveSpectrum.Twist.homogeneousFractionAt'` and
  `ProjectiveSpectrum.Twist.homogeneousSection'`;
* `ProjectiveSpectrum.Twist.homogeneousSection'_apply`, the defining value `p / 1`;
* `ProjectiveSpectrum.Twist.mulSectionHom_homogeneousSection'`, multiplicativity, which is
  the degree-raising compatibility of the comparison with `Γ_*`;
* `ProjectiveSpectrum.Twist.homogeneousToGlobalSections'` and
  `ProjectiveSpectrum.Twist.degreeZeroSection_smul_homogeneousSection'`, the degreewise
  component of that comparison and its scalar compatibility.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open HomogeneousLocalization

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

/-- The fraction `p / 1` at a point, in a degree presented as equal to the degree of `p`. -/
def homogeneousFractionAt' {m : ℕ} (p : R m) (e : ℤ) (he : e = (m : ℤ))
    (x : ProjectiveSpectrum.top R) : atDeg R e x := by
  refine ⟨Localization.mk (p : A) 1, ?_⟩
  let q : NumDenShift R x.asHomogeneousIdeal.toIdeal.primeCompl e :=
    { degDen := 0
      degNum := m
      num := p
      den := ⟨1, SetLike.one_mem_graded _⟩
      den_mem := one_mem _
      deg_eq := by omega }
  exact ⟨q, rfl⟩

@[simp]
theorem homogeneousFractionAt'_val {m : ℕ} (p : R m) (e : ℤ) (he : e = (m : ℤ))
    (x : ProjectiveSpectrum.top R) :
    (homogeneousFractionAt' R p e he x :
      Localization x.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.mk (p : A) 1 := rfl

theorem homogeneousFraction'_pred {m : ℕ} (p : R m) (e : ℤ) (he : e = (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) :
    (isLocallyFraction R e).pred
      (fun x : U ↦ homogeneousFractionAt' R p e he x.1) := by
  intro x
  refine ⟨U, x.2, 𝟙 U, 0, m, by omega, p, ⟨1, SetLike.one_mem_graded _⟩,
    fun _ ↦ one_mem _, fun _ ↦ rfl⟩

/-- **A homogeneous form as a section of `𝒪(e)`**, for any degree `e` presented as equal to
the degree of the form. -/
def homogeneousSection' {m : ℕ} (p : R m) (e : ℤ) (he : e = (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) : Γ(twist R e, U) :=
  ⟨fun x ↦ homogeneousFractionAt' R p e he x.1, homogeneousFraction'_pred R p e he U⟩

@[simp]
theorem homogeneousSection'_apply {m : ℕ} (p : R m) (e : ℤ) (he : e = (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) (x : U) :
    ((homogeneousSection' R p e he U).1 x :
      Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.mk (p : A) 1 := rfl

/-- In the degree of the form itself this is `homogeneousSection`. -/
theorem homogeneousSection'_self {m : ℕ} (p : R m)
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection' R p (m : ℤ) rfl U = homogeneousSection R p U := rfl

@[simp]
theorem homogeneousSection'_zero {m : ℕ} (e : ℤ) (he : e = (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection' R (0 : R m) e he U = 0 := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact Localization.mk_zero _

@[simp]
theorem homogeneousSection'_add {m : ℕ} (p q : R m) (e : ℤ) (he : e = (m : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection' R (p + q) e he U
      = homogeneousSection' R p e he U + homogeneousSection' R q e he U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk ((p : A) + (q : A)) 1 =
    Localization.mk (p : A) 1 + Localization.mk (q : A) 1
  rw [Localization.add_mk_self]

/-- **Multiplying the form multiplies the section.**  This is the degree-raising
compatibility that makes a form-to-section map a morphism of graded modules into `Γ_*`. -/
theorem mulSectionHom_homogeneousSection' {m k : ℕ} (p : R m) (c : R k)
    (e ec : ℤ) (he : e = (m : ℤ)) (hec : ec = e + (k : ℤ))
    (hprod : ec = ((m + k : ℕ) : ℤ))
    (U : (Opens (ProjectiveSpectrum.top R))ᵒᵖ) :
    mulSectionHom R c e ec hec U (homogeneousSection' R p e he U.unop)
      = homogeneousSection' R
          (⟨(p : A) * (c : A), SetLike.mul_mem_graded p.2 c.2⟩ : R (m + k))
          ec hprod U.unop := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) 1 * Localization.mk (c : A) 1
    = Localization.mk ((p : A) * (c : A)) 1
  rw [Localization.mk_mul, one_mul]

/-- **The section depends only on the underlying form**, not on the degree index it is
presented in.  This is what replaces an `eqToHom` transport when two constructions land in
`R m` and `R m'` for provably equal but syntactically different `m`, `m'`. -/
theorem homogeneousSection'_congr {m m' : ℕ} (p : R m) (p' : R m')
    (hp : (p : A) = (p' : A)) (e : ℤ) (he : e = (m : ℤ)) (he' : e = (m' : ℤ))
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection' R p e he U = homogeneousSection' R p' e he' U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) 1 = Localization.mk (p' : A) 1
  rw [hp]

/-- **The degreewise component of the comparison `S ⟶ Γ_*(𝒪)`**: the additive map from the
degree-`m` forms to the global sections of `𝒪(e)`, for `e` presented as equal to `m`. -/
def homogeneousToGlobalSections' {m : ℕ} (e : ℤ) (he : e = (m : ℤ)) :
    R m →+ Γ(twist R e, ⊤) where
  toFun p := homogeneousSection' R p e he ⊤
  map_zero' := homogeneousSection'_zero R e he ⊤
  map_add' p q := homogeneousSection'_add R p q e he ⊤

@[simp]
theorem homogeneousToGlobalSections'_apply {m : ℕ} (e : ℤ) (he : e = (m : ℤ)) (p : R m) :
    homogeneousToGlobalSections' R e he p = homogeneousSection' R p e he ⊤ := rfl

/-- **Scalar compatibility.**  Multiplying the form by a degree-zero form before taking the
section is the structure-sheaf action afterwards.  This is what makes the degreewise
component `R`-linear, once the base ring is identified with `R 0`. -/
theorem degreeZeroSection_smul_homogeneousSection' {m : ℕ} (r : R 0) (p : R m)
    (e : ℤ) (he : e = (m : ℤ)) (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R r U • homogeneousSection' R p e he U =
      homogeneousSection' R
        (⟨(r : A) * (p : A), by simpa using SetLike.mul_mem_graded r.2 p.2⟩ : R m) e he U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (r : A) 1 * Localization.mk (p : A) 1 =
    Localization.mk ((r : A) * (p : A)) 1
  rw [Localization.mk_mul]
  congr 1
  all_goals simp

end ProjectiveSpectrum.Twist

end

end
