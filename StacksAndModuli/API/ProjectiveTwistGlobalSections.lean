module

public import «StacksProject».«Constructions».«InvertibleSheavesOnProj».«definition-twist»
public import StacksAndModuli.API.HomogeneousDimension
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Homogeneous forms as sections of twisting sheaves on `Proj`

Every degree-`d` form defines a section of `𝒪_{Proj A}(d)`, locally represented by `p / 1`.
For polynomial rings the standard cover proves that all global sections arise uniquely this
way.  The finite-free description includes coefficient and tensor base change and underlies
`π_* 𝒪_{ℙⁿ_S}(d) ≅ 𝒪_S^{⊕ binom(n+d,n)}` for `d ≥ 0`.

* `MvPolynomial.homogeneousToGlobalSections_bijective`: the standard-cover gluing theorem.
* `Scheme.Modules.pullbackGlobalSections`: the adjunction-unit geometric pullback map.
* `MvPolynomial.projectiveTwistGlobalSectionsBaseChangeEquiv`: tensor base change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open HomogeneousLocalization
open TensorProduct
open scoped AlgebraicGeometry

namespace ProjectiveSpectrum.Twist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

/-- A homogeneous element `p` of degree `d`, viewed at a point of `Proj R` as the
degree-`d` fraction `p / 1`. -/
def homogeneousFractionAt {d : ℕ} (p : R d) (x : ProjectiveSpectrum.top R) :
    atDeg R (d : ℤ) x := by
  refine ⟨Localization.mk (p : A) 1, ?_⟩
  let q : NumDenShift R x.asHomogeneousIdeal.toIdeal.primeCompl (d : ℤ) :=
    { degDen := 0
      degNum := d
      num := p
      den := ⟨1, SetLike.one_mem_graded _⟩
      den_mem := one_mem _
      deg_eq := by omega }
  exact ⟨q, rfl⟩

@[simp]
theorem homogeneousFractionAt_val {d : ℕ} (p : R d)
    (x : ProjectiveSpectrum.top R) :
    (homogeneousFractionAt R p x : Localization
      x.asHomogeneousIdeal.toIdeal.primeCompl) = Localization.mk (p : A) 1 := rfl

/-- The pointwise fractions `p / 1` satisfy the local-fraction condition defining
`𝒪(d)` on every open subset of `Proj R`. -/
theorem homogeneousFraction_pred {d : ℕ} (p : R d)
    (U : Opens (ProjectiveSpectrum.top R)) :
    (isLocallyFraction R (d : ℤ)).pred
      (fun x : U ↦ homogeneousFractionAt R p x.1) := by
  intro x
  refine ⟨U, x.2, 𝟙 U, 0, d, by omega, p, ⟨1, SetLike.one_mem_graded _⟩,
    fun _ ↦ one_mem _, fun _ ↦ rfl⟩

/-- A homogeneous element of degree `d` defines a section of `𝒪(d)` over every open
subset of `Proj R`, represented everywhere by `p / 1`. -/
def homogeneousSection {d : ℕ} (p : R d) (U : Opens (ProjectiveSpectrum.top R)) :
    Γ(twist R (d : ℤ), U) :=
  ⟨fun x ↦ homogeneousFractionAt R p x.1, homogeneousFraction_pred R p U⟩

@[simp]
theorem homogeneousSection_apply {d : ℕ} (p : R d)
    (U : Opens (ProjectiveSpectrum.top R)) (x : U) :
    ((homogeneousSection R p U).1 x : Localization
      x.1.asHomogeneousIdeal.toIdeal.primeCompl) = Localization.mk (p : A) 1 := rfl

@[simp]
theorem homogeneousSection_zero (d : ℕ) (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection R (0 : R d) U = 0 := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact Localization.mk_zero _

@[simp]
theorem homogeneousSection_add {d : ℕ} (p q : R d)
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection R (p + q) U = homogeneousSection R p U + homogeneousSection R q U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk ((p : A) + (q : A)) 1 =
    Localization.mk (p : A) 1 + Localization.mk (q : A) 1
  simp only [Localization.add_mk]
  congr 1 <;> simp [add_comm]

@[simp]
theorem homogeneousSection_neg {d : ℕ} (p : R d)
    (U : Opens (ProjectiveSpectrum.top R)) :
    homogeneousSection R (-p) U = -homogeneousSection R p U := by
  refine Subtype.ext (funext fun x ↦ ?_)
  refine Subtype.ext ?_
  change Localization.mk (-(p : A)) 1 = -Localization.mk (p : A) 1
  rw [Localization.neg_mk]

/-- A degree-zero homogeneous element, viewed at a point of `Proj R` as a section of the
structure sheaf represented by `p / 1`. -/
def degreeZeroFractionAt (p : R 0) (x : ProjectiveSpectrum.top R) :
    HomogeneousLocalization.AtPrime R x.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    { deg := 0
      num := p
      den := ⟨1, SetLike.one_mem_graded _⟩
      den_mem := one_mem _ }

@[simp]
theorem degreeZeroFractionAt_val (p : R 0) (x : ProjectiveSpectrum.top R) :
    (degreeZeroFractionAt R p x).val = Localization.mk (p : A) 1 := rfl

/-- The pointwise degree-zero fractions `p / 1` satisfy the local-fraction condition
defining the structure sheaf of `Proj R`. -/
theorem degreeZeroFraction_pred (p : R 0) (U : Opens (ProjectiveSpectrum.top R)) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction R).pred
      (fun x : U ↦ degreeZeroFractionAt R p x.1) := by
  intro x
  exact ⟨U, x.2, 𝟙 U,
    ⟨0, p, ⟨1, SetLike.one_mem_graded _⟩,
      fun y ↦ y.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ ↦ rfl⟩⟩

/-- The structure-sheaf section induced by a degree-zero homogeneous element. -/
def degreeZeroSection (p : R 0) (U : Opens (ProjectiveSpectrum.top R)) : Γ(Proj R, U) :=
  ⟨fun x ↦ degreeZeroFractionAt R p x.1, degreeZeroFraction_pred R p U⟩

@[simp]
theorem degreeZeroSection_apply (p : R 0) (U : Opens (ProjectiveSpectrum.top R)) (x : U) :
    (degreeZeroSection R p U).1 x = degreeZeroFractionAt R p x.1 := rfl

@[simp]
theorem degreeZeroSection_zero (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R (0 : R 0) U = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  calc
    ((degreeZeroSection R (0 : R 0) U).1 x).val =
        Localization.mk (0 : A) 1 := degreeZeroFractionAt_val R (0 : R 0) x.1
    _ = 0 := Localization.mk_zero _
    _ = (0 : HomogeneousLocalization.AtPrime R x.1.asHomogeneousIdeal.toIdeal).val :=
      (HomogeneousLocalization.val_zero (𝒜 := R)).symm
    _ = ((0 : Γ(Proj R, U)).1 x).val := congrArg HomogeneousLocalization.val
      (Proj.zero_apply (𝒜 := R) (x := x)).symm

@[simp]
theorem degreeZeroSection_one (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R (1 : R 0) U = 1 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  calc
    ((degreeZeroSection R (1 : R 0) U).1 x).val =
        Localization.mk (1 : A) 1 := degreeZeroFractionAt_val R (1 : R 0) x.1
    _ = 1 := Localization.mk_one
    _ = (1 : HomogeneousLocalization.AtPrime R x.1.asHomogeneousIdeal.toIdeal).val :=
      (HomogeneousLocalization.val_one (𝒜 := R)).symm
    _ = ((1 : Γ(Proj R, U)).1 x).val := congrArg HomogeneousLocalization.val
      (Proj.one_apply (𝒜 := R) (x := x)).symm

@[simp]
theorem degreeZeroSection_add (p q : R 0) (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R (p + q) U = degreeZeroSection R p U + degreeZeroSection R q U := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  let W : Submonoid A := x.1.asHomogeneousIdeal.toIdeal.primeCompl
  have hadd : Localization.mk (S := W) ((p : A) + (q : A)) 1 =
      Localization.mk (S := W) (p : A) 1 + Localization.mk (S := W) (q : A) 1 := by
    simp only [Localization.add_mk]
    congr 1
    all_goals simp [add_comm]
  exact (degreeZeroFractionAt_val R (p + q) x.1).trans <|
    hadd.trans <| congrArg₂ (fun a b ↦ a + b)
      (degreeZeroFractionAt_val R p x.1).symm (degreeZeroFractionAt_val R q x.1).symm |>.trans <|
        (HomogeneousLocalization.val_add _ _).symm |>.trans <|
          congrArg HomogeneousLocalization.val
            (Proj.add_apply (𝒜 := R) (s := degreeZeroSection R p U)
              (t := degreeZeroSection R q U) x).symm

@[simp]
theorem degreeZeroSection_mul (p q : R 0) (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R (p * q) U = degreeZeroSection R p U * degreeZeroSection R q U := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  let W : Submonoid A := x.1.asHomogeneousIdeal.toIdeal.primeCompl
  have hmul : Localization.mk (S := W) ((p : A) * (q : A)) 1 =
      Localization.mk (S := W) (p : A) 1 * Localization.mk (S := W) (q : A) 1 := by
    rw [Localization.mk_mul]
    congr 1
    all_goals simp
  exact (degreeZeroFractionAt_val R (p * q) x.1).trans <|
    hmul.trans <| congrArg₂ (fun a b ↦ a * b)
      (degreeZeroFractionAt_val R p x.1).symm (degreeZeroFractionAt_val R q x.1).symm |>.trans <|
        (HomogeneousLocalization.val_mul _ _).symm |>.trans <|
          congrArg HomogeneousLocalization.val
            (Proj.mul_apply (𝒜 := R) (s := degreeZeroSection R p U)
              (t := degreeZeroSection R q U) x).symm

/-- Degree-zero homogeneous elements act as structure-sheaf sections, bundled as a
ring homomorphism on any open subset of `Proj`. -/
def degreeZeroToSectionsRingHom (U : Opens (ProjectiveSpectrum.top R)) :
    R 0 →+* Γ(Proj R, U) where
  toFun p := degreeZeroSection R p U
  map_zero' := degreeZeroSection_zero R U
  map_one' := degreeZeroSection_one R U
  map_add' p q := degreeZeroSection_add R p q U
  map_mul' p q := degreeZeroSection_mul R p q U

/-- Degree-zero homogeneous elements map canonically to structure-sheaf sections on every
open subset of `Proj R`. -/
noncomputable def degreeZeroToSections (U : Opens (ProjectiveSpectrum.top R)) :
    R 0 →+* Γ(Proj R, U) where
  toFun p := degreeZeroSection R p U
  map_zero' := degreeZeroSection_zero R U
  map_one' := degreeZeroSection_one R U
  map_add' p q := degreeZeroSection_add R p q U
  map_mul' p q := degreeZeroSection_mul R p q U

/-- On `D₊(f)`, a form `p` of degree `d` can be dehomogenized to the degree-zero
fraction `p / f^d` at every point. -/
def dehomogenizedFractionAt {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1)
    (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    HomogeneousLocalization.AtPrime R x.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    { deg := d
      num := p
      den := ⟨f ^ d, by
        simpa [smul_eq_mul] using SetLike.pow_mem_graded d hf⟩
      den_mem := Submonoid.pow_mem _ hfx d }

@[simp]
theorem dehomogenizedFractionAt_val {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1)
    (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (dehomogenizedFractionAt R p hf x hfx).val =
      Localization.mk (p : A) ⟨f ^ d, Submonoid.pow_mem _ hfx d⟩ := rfl

/-- The pointwise fractions `p / f^d` satisfy the structure sheaf's local-fraction
condition on every open contained in `D₊(f)`. -/
theorem dehomogenizedFraction_pred {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1)
    (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction R).pred
      (fun x : U ↦ dehomogenizedFractionAt R p hf x.1 (hU x.2)) := by
  intro x
  refine ⟨U, x.2, 𝟙 U, d, p,
    ⟨f ^ d, by simpa [smul_eq_mul] using SetLike.pow_mem_graded d hf⟩,
    fun y ↦ by
      change f ^ d ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl
      exact Submonoid.pow_mem _ (hU y.2) d,
    fun _ ↦ rfl⟩

/-- The regular function `p / f^d` on an open contained in `D₊(f)`. -/
def dehomogenizedSection {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1)
    (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) : Γ(Proj R, U) :=
  ⟨fun x ↦ dehomogenizedFractionAt R p hf x.1 (hU x.2),
    dehomogenizedFraction_pred R p hf U hU⟩

/-- If `p` has degree `N ≥ d`, then `p / f^(N-d)` is a degree-`d` fraction at
every point of `D₊(f)`. -/
def localizedHomogeneousFractionAt {d N : ℕ} (p : R N) {f : A} (hf : f ∈ R 1)
    (hdN : d ≤ N) (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) : atDeg R (d : ℤ) x := by
  refine ⟨Localization.mk (p : A)
    ⟨f ^ (N - d), Submonoid.pow_mem _ hfx (N - d)⟩, ?_⟩
  let q : NumDenShift R x.asHomogeneousIdeal.toIdeal.primeCompl (d : ℤ) :=
    { degDen := N - d
      degNum := N
      num := p
      den := ⟨f ^ (N - d), by
        simpa [smul_eq_mul] using SetLike.pow_mem_graded (N - d) hf⟩
      den_mem := Submonoid.pow_mem _ hfx (N - d)
      deg_eq := by omega }
  exact ⟨q, rfl⟩

@[simp]
theorem localizedHomogeneousFractionAt_val {d N : ℕ} (p : R N) {f : A}
    (hf : f ∈ R 1) (hdN : d ≤ N) (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (localizedHomogeneousFractionAt R p hf hdN x hfx).1 =
      Localization.mk (p : A) ⟨f ^ (N - d), Submonoid.pow_mem _ hfx (N - d)⟩ := rfl

/-- The fractions `p / f^(N-d)` satisfy the local-fraction condition on every open
contained in `D₊(f)`. -/
theorem localizedHomogeneousFraction_pred {d N : ℕ} (p : R N) {f : A}
    (hf : f ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R)) (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    (isLocallyFraction R (d : ℤ)).pred
      (fun x : U ↦ localizedHomogeneousFractionAt R p hf hdN x.1 (hU x.2)) := by
  intro x
  refine ⟨U, x.2, 𝟙 U, N - d, N, by omega, p,
    ⟨f ^ (N - d), by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded (N - d) hf⟩,
    fun y ↦ Submonoid.pow_mem _ (hU y.2) (N - d), fun _ ↦ rfl⟩

/-- The local section of `𝒫(d)` represented by `p / f^(N-d)`, for a form `p` of
degree `N ≥ d`. -/
def localizedHomogeneousSection {d N : ℕ} (p : R N) {f : A} (hf : f ∈ R 1)
    (hdN : d ≤ N) (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) : Γ(twist R (d : ℤ), U) :=
  ⟨fun x ↦ localizedHomogeneousFractionAt R p hf hdN x.1 (hU x.2),
    localizedHomogeneousFraction_pred R p hf hdN U hU⟩

@[simp]
theorem localizedHomogeneousSection_apply {d N : ℕ} (p : R N) {f : A}
    (hf : f ∈ R 1) (hdN : d ≤ N) (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) (x : U) :
    ((localizedHomogeneousSection R p hf hdN U hU).1 x).1 =
      Localization.mk (p : A)
        ⟨f ^ (N - d), Submonoid.pow_mem _ (hU x.2) (N - d)⟩ := rfl

/-- On an open where two degree-one elements `f` and `g` are invertible, the
degree-zero fraction `p / (g^(N-d) f^d)`.  It is the coordinate, in the `f^d`
trivialization, of the twist fraction `p / g^(N-d)`. -/
def mixedDehomogenizedFractionAt {d N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hgx : g ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    HomogeneousLocalization.AtPrime R x.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk
    { deg := N
      num := p
      den := ⟨g ^ (N - d) * f ^ d, by
        convert SetLike.mul_mem_graded (SetLike.pow_mem_graded (N - d) hg)
          (SetLike.pow_mem_graded d hf) using 1
        simp [smul_eq_mul, Nat.sub_add_cancel hdN]⟩
      den_mem := mul_mem (Submonoid.pow_mem _ hgx (N - d))
        (Submonoid.pow_mem _ hfx d) }

@[simp]
theorem mixedDehomogenizedFractionAt_val {d N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (x : ProjectiveSpectrum.top R)
    (hfx : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hgx : g ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (mixedDehomogenizedFractionAt R p hf hg hdN x hfx hgx).val =
      Localization.mk (p : A)
        ⟨g ^ (N - d) * f ^ d,
          mul_mem (Submonoid.pow_mem _ hgx (N - d)) (Submonoid.pow_mem _ hfx d)⟩ := rfl

/-- The mixed fractions `p / (g^(N-d) f^d)` satisfy the structure sheaf's
local-fraction condition wherever both `f` and `g` are invertible. -/
theorem mixedDehomogenizedFraction_pred {d N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R))
    (hUf : U ≤ ProjectiveSpectrum.basicOpen R f)
    (hUg : U ≤ ProjectiveSpectrum.basicOpen R g) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction R).pred
      (fun x : U ↦ mixedDehomogenizedFractionAt R p hf hg hdN x.1
        (hUf x.2) (hUg x.2)) := by
  intro x
  refine ⟨U, x.2, 𝟙 U, N, p,
    ⟨g ^ (N - d) * f ^ d, by
      convert SetLike.mul_mem_graded (SetLike.pow_mem_graded (N - d) hg)
        (SetLike.pow_mem_graded d hf) using 1
      simp [smul_eq_mul, Nat.sub_add_cancel hdN]⟩,
    fun y ↦ by
      change g ^ (N - d) * f ^ d ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl
      exact mul_mem (Submonoid.pow_mem _ (hUg y.2) (N - d))
        (Submonoid.pow_mem _ (hUf y.2) d), fun _ ↦ rfl⟩

/-- The regular function `p / (g^(N-d) f^d)` on an open where both degree-one
forms are invertible. -/
def mixedDehomogenizedSection {d N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R))
    (hUf : U ≤ ProjectiveSpectrum.basicOpen R f)
    (hUg : U ≤ ProjectiveSpectrum.basicOpen R g) : Γ(Proj R, U) :=
  ⟨fun x ↦ mixedDehomogenizedFractionAt R p hf hg hdN x.1
      (hUf x.2) (hUg x.2),
    mixedDehomogenizedFraction_pred R p hf hg hdN U hUf hUg⟩

/-- Multiplying the mixed coordinate `p / (g^(N-d) f^d)` by the basis `f^d`
recovers the twist fraction `p / g^(N-d)`. -/
theorem mixedDehomogenizedSection_smul_unitSection {d N : ℕ} (p : R N)
    {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R))
    (hUf : U ≤ ProjectiveSpectrum.basicOpen R f)
    (hUg : U ≤ ProjectiveSpectrum.basicOpen R g) :
    mixedDehomogenizedSection R p hf hg hdN U hUf hUg •
        unitSection R hf (d : ℤ) (op U) hUf =
      localizedHomogeneousSection R p hg hdN U hUg := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) ⟨g ^ (N - d) * f ^ d, _⟩ *
      (unitPow hf (hUf x.2) (d : ℤ)).embed =
    Localization.mk (p : A) ⟨g ^ (N - d), _⟩
  simp only [NumDenShift.embed_def, unitPow, Int.toNat_natCast]
  simp only [show (-(d : ℤ)).toNat = 0 by omega, pow_zero]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Thus the coordinate of `p / g^(N-d)` in the `f^d` basis is the mixed
degree-zero fraction `p / (g^(N-d) f^d)`. -/
theorem unitSectionEquiv_symm_localizedHomogeneousSection_mixed {d N : ℕ}
    (p : R N) {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R))
    (hUf : U ≤ ProjectiveSpectrum.basicOpen R f)
    (hUg : U ≤ ProjectiveSpectrum.basicOpen R g) :
    (unitSectionEquiv R hf (d : ℤ) (op U) hUf).symm
        (localizedHomogeneousSection R p hg hdN U hUg) =
      mixedDehomogenizedSection R p hf hg hdN U hUf hUg := by
  apply (unitSectionEquiv R hf (d : ℤ) (op U) hUf).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (mixedDehomogenizedSection_smul_unitSection
    R p hf hg hdN U hUf hUg).symm

/-- In the standard trivialization by `f^d`, the twist fraction `p / f^(N-d)` has
degree-zero coordinate `p / f^N`. -/
theorem dehomogenizedSection_smul_unitSection_eq_localized {d N : ℕ} (p : R N)
    {f : A} (hf : f ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R)) (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    dehomogenizedSection R p hf U hU •
        unitSection R hf (d : ℤ) (op U) hU =
      localizedHomogeneousSection R p hf hdN U hU := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) ⟨f ^ N, _⟩ *
      (unitPow hf (hU x.2) (d : ℤ)).embed =
    Localization.mk (p : A) ⟨f ^ (N - d), _⟩
  simp only [NumDenShift.embed_def, unitPow, Int.toNat_natCast]
  simp only [show (-(d : ℤ)).toNat = 0 by omega, pow_zero]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  calc
    f ^ (N - d) * ((p : A) * f ^ d) = (p : A) * f ^ ((N - d) + d) := by
      rw [pow_add]
      ring
    _ = (p : A) * f ^ N := by rw [Nat.sub_add_cancel hdN]
    _ = f ^ N * 1 * (p : A) := by ring

/-- Dividing a local twist fraction `p / f^(N-d)` by the standard basis `f^d`
produces the regular function `p / f^N`. -/
theorem unitSectionEquiv_symm_localizedHomogeneousSection {d N : ℕ} (p : R N)
    {f : A} (hf : f ∈ R 1) (hdN : d ≤ N)
    (U : Opens (ProjectiveSpectrum.top R)) (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    (unitSectionEquiv R hf (d : ℤ) (op U) hU).symm
        (localizedHomogeneousSection R p hf hdN U hU) =
      dehomogenizedSection R p hf U hU := by
  apply (unitSectionEquiv R hf (d : ℤ) (op U) hU).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (dehomogenizedSection_smul_unitSection_eq_localized
    R p hf hdN U hU).symm

/-- The standard local coordinate of a twist section commutes with restriction to a
smaller open on which the same degree-one element is invertible. -/
theorem unitSectionEquiv_symm_restrict {f : A} (hf : f ∈ R 1) (d : ℤ)
    {U V : Opens (ProjectiveSpectrum.top R)} (hU : U ≤ ProjectiveSpectrum.basicOpen R f)
    (hVU : V ≤ U) (s : Γ(twist R d, U)) :
    (unitSectionEquiv R hf d (op V) (hVU.trans hU)).symm
        ((sheafInType R d).1.map (homOfLE hVU).op s) =
      (Proj R).presheaf.map (homOfLE hVU).op
        ((unitSectionEquiv R hf d (op U) hU).symm s) := by
  apply (unitSectionEquiv R hf d (op V) (hVU.trans hU)).injective
  rw [LinearEquiv.apply_symm_apply]
  have hs := congrArg (fun t : Γ(twist R d, U) ↦
    (sheafInType R d).1.map (homOfLE hVU).op t)
      ((unitSectionEquiv R hf d (op U) hU).apply_symm_apply s)
  exact hs.symm

/-- After restricting `p / f^(N-d)` from its standard chart, its coordinate in the
same `f^d` basis is still `p / f^N`. -/
theorem unitSectionEquiv_symm_restrict_localizedHomogeneousSection
    {d N : ℕ} (p : R N) {f : A} (hf : f ∈ R 1) (hdN : d ≤ N)
    (V : Opens (ProjectiveSpectrum.top R)) (hV : V ≤ ProjectiveSpectrum.basicOpen R f) :
    (unitSectionEquiv R hf (d : ℤ) (op V) hV).symm
        ((sheafInType R (d : ℤ)).1.map (homOfLE hV).op
          (localizedHomogeneousSection R p hf hdN
            (ProjectiveSpectrum.basicOpen R f) le_rfl)) =
      dehomogenizedSection R p hf V hV := by
  rw [unitSectionEquiv_symm_restrict R hf (d : ℤ) le_rfl hV]
  rw [unitSectionEquiv_symm_localizedHomogeneousSection]
  rfl

/-- On an overlap with `D₊(f)`, the restriction of `p / g^(N-d)` from `D₊(g)`
has `f^d`-coordinate `p / (g^(N-d) f^d)`. -/
theorem unitSectionEquiv_symm_restrict_localizedHomogeneousSection_mixed
    {d N : ℕ} (p : R N) {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1)
    (hdN : d ≤ N) (V : Opens (ProjectiveSpectrum.top R))
    (hVf : V ≤ ProjectiveSpectrum.basicOpen R f)
    (hVg : V ≤ ProjectiveSpectrum.basicOpen R g) :
    (unitSectionEquiv R hf (d : ℤ) (op V) hVf).symm
        ((sheafInType R (d : ℤ)).1.map (homOfLE hVg).op
          (localizedHomogeneousSection R p hg hdN
            (ProjectiveSpectrum.basicOpen R g) le_rfl)) =
      mixedDehomogenizedSection R p hf hg hdN V hVf hVg := by
  change (unitSectionEquiv R hf (d : ℤ) (op V) hVf).symm
      (localizedHomogeneousSection R p hg hdN V hVg) = _
  exact unitSectionEquiv_symm_localizedHomogeneousSection_mixed
    R p hf hg hdN V hVf hVg

/-- Compatibility of two denominator-cleared twist fractions on `D₊(f) ∩ D₊(g)`,
written in the common `f^d` trivialization. -/
theorem localizedHomogeneousSection_overlap_coordinates_eq {d N : ℕ}
    (p q : R N) {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (hcompat :
      (sheafInType R (d : ℤ)).1.map
          (Opens.infLELeft (ProjectiveSpectrum.basicOpen R f)
            (ProjectiveSpectrum.basicOpen R g)).op
          (localizedHomogeneousSection R p hf hdN
            (ProjectiveSpectrum.basicOpen R f) le_rfl) =
        (sheafInType R (d : ℤ)).1.map
          (Opens.infLERight (ProjectiveSpectrum.basicOpen R f)
            (ProjectiveSpectrum.basicOpen R g)).op
          (localizedHomogeneousSection R q hg hdN
            (ProjectiveSpectrum.basicOpen R g) le_rfl)) :
    dehomogenizedSection R p hf
        (ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g) inf_le_left =
      mixedDehomogenizedSection R q hf hg hdN
        (ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g)
          inf_le_left inf_le_right := by
  have h := congrArg
    (unitSectionEquiv R hf (d : ℤ)
      (op (ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g))
        inf_le_left).symm hcompat
  dsimp only [Opens.infLELeft, Opens.infLERight] at h
  rw [unitSectionEquiv_symm_restrict_localizedHomogeneousSection,
    unitSectionEquiv_symm_restrict_localizedHomogeneousSection_mixed] at h
  exact h

/-- The element of `(R_(fg))₀` representing `p / f^N` on the overlap:
`p g^N / (fg)^N`. -/
def dehomogenizedOverlapAway {N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) : HomogeneousLocalization.Away R (f * g) :=
  HomogeneousLocalization.Away.mk (d := 2) R
    (SetLike.mul_mem_graded hf hg) N ((p : A) * g ^ N) (by
        convert SetLike.mul_mem_graded p.2 (SetLike.pow_mem_graded N hg) using 1
        congr 1
        simp [smul_eq_mul, Nat.mul_two])

@[simp]
theorem dehomogenizedOverlapAway_val {N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) :
    (dehomogenizedOverlapAway R p hf hg).val =
      Localization.mk ((p : A) * g ^ N) ⟨(f * g) ^ N, by exact ⟨N, rfl⟩⟩ :=
  HomogeneousLocalization.Away.val_mk R N _ _ _

/-- The element of `(R_(fg))₀` representing the mixed fraction
`q / (g^(N-d) f^d)` on the overlap, with common denominator `(fg)^N`. -/
def mixedDehomogenizedOverlapAway {d N : ℕ} (q : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N) :
    HomogeneousLocalization.Away R (f * g) :=
  HomogeneousLocalization.Away.mk (d := 2) R
    (SetLike.mul_mem_graded hf hg) N
    ((q : A) * f ^ (N - d) * g ^ d) (by
      have hqf := SetLike.mul_mem_graded q.2 (SetLike.pow_mem_graded (N - d) hf)
      have hqfg := SetLike.mul_mem_graded hqf (SetLike.pow_mem_graded d hg)
      convert hqfg using 1
      simp only [smul_eq_mul]
      congr 1
      omega)

@[simp]
theorem mixedDehomogenizedOverlapAway_val {d N : ℕ} (q : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N) :
    (mixedDehomogenizedOverlapAway R q hf hg hdN).val =
      Localization.mk ((q : A) * f ^ (N - d) * g ^ d)
        ⟨(f * g) ^ N, by exact ⟨N, rfl⟩⟩ :=
  HomogeneousLocalization.Away.val_mk R N _ _ _

/-- The overlap localization element `p g^N / (fg)^N` realizes the regular
function `p / f^N` on `D₊(fg)`. -/
theorem awayToSection_dehomogenizedOverlapAway {N : ℕ} (p : R N) {f g : A}
    (hf : f ∈ R 1) (hg : g ∈ R 1) :
    Proj.awayToSection R (f * g) (dehomogenizedOverlapAway R p hf hg) =
      dehomogenizedSection R p hf (ProjectiveSpectrum.basicOpen R (f * g))
        (ProjectiveSpectrum.basicOpen_mul_le_left R f g) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [dehomogenizedOverlapAway_val]
  change _ = Localization.mk (p : A) ⟨f ^ N, _⟩
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  rw [← Localization.mk_eq_mk']
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  push_cast
  rw [mul_pow]
  ring

/-- The overlap localization element
`q f^(N-d) g^d / (fg)^N` realizes `q / (g^(N-d) f^d)` on `D₊(fg)`. -/
theorem awayToSection_mixedDehomogenizedOverlapAway {d N : ℕ}
    (q : R N) {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N) :
    Proj.awayToSection R (f * g) (mixedDehomogenizedOverlapAway R q hf hg hdN) =
      mixedDehomogenizedSection R q hf hg hdN
        (ProjectiveSpectrum.basicOpen R (f * g))
          (ProjectiveSpectrum.basicOpen_mul_le_left R f g)
          (ProjectiveSpectrum.basicOpen_mul_le_right R f g) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [mixedDehomogenizedOverlapAway_val]
  change _ = Localization.mk (q : A) ⟨g ^ (N - d) * f ^ d, _⟩
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  rw [← Localization.mk_eq_mk']
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  push_cast
  rw [mul_pow]
  calc
    g ^ (N - d) * f ^ d * ((q : A) * f ^ (N - d) * g ^ d) =
        (g ^ (N - d) * g ^ d) * (f ^ (N - d) * f ^ d) * (q : A) := by ring
    _ = g ^ N * f ^ N * (q : A) := by
      rw [← pow_add, Nat.sub_add_cancel hdN, ← pow_add, Nat.sub_add_cancel hdN]
    _ = f ^ N * g ^ N * (q : A) := by ring

/-- Equality of the two explicit regular functions on the overlap is faithfully
detected in the homogeneous localization `(R_(fg))₀`. -/
theorem dehomogenizedOverlapAway_eq_mixed_of_sections_eq {d N : ℕ}
    (p q : R N) {f g : A} (hf : f ∈ R 1) (hg : g ∈ R 1) (hdN : d ≤ N)
    (hsec :
      dehomogenizedSection R p hf
          (ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g) inf_le_left =
        mixedDehomogenizedSection R q hf hg hdN
          (ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g)
            inf_le_left inf_le_right) :
    dehomogenizedOverlapAway R p hf hg = mixedDehomogenizedOverlapAway R q hf hg hdN := by
  apply (Proj.basicOpenIsoAway R (f * g) (SetLike.mul_mem_graded hf hg)
    (by omega)).commRingCatIsoToRingEquiv.injective
  change Proj.awayToSection R (f * g) (dehomogenizedOverlapAway R p hf hg) =
    Proj.awayToSection R (f * g) (mixedDehomogenizedOverlapAway R q hf hg hdN)
  rw [awayToSection_dehomogenizedOverlapAway,
    awayToSection_mixedDehomogenizedOverlapAway]
  refine Subtype.ext (funext fun x ↦ ?_)
  let W : Opens (ProjectiveSpectrum.top R) :=
    ProjectiveSpectrum.basicOpen R f ⊓ ProjectiveSpectrum.basicOpen R g
  let y : W :=
    ⟨x.1, by
      change x.1 ∈ ProjectiveSpectrum.basicOpen R f ⊓
        ProjectiveSpectrum.basicOpen R g
      rw [← ProjectiveSpectrum.basicOpen_mul R f g]
      exact x.2⟩
  have hy := congrArg (fun s ↦ s.1 y) hsec
  apply HomogeneousLocalization.val_injective
  have hyval := congrArg HomogeneousLocalization.val hy
  simpa only [dehomogenizedSection, mixedDehomogenizedSection,
    dehomogenizedFractionAt_val, mixedDehomogenizedFractionAt_val] using hyval

/-- On `D₊(f)`, the section of `𝒪(d)` defined by `p` is `(p / f^d) · f^d` under the
standard local trivialization of the twisting sheaf. -/
theorem dehomogenizedSection_smul_unitSection {d : ℕ} (p : R d) {f : A}
    (hf : f ∈ R 1) (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    dehomogenizedSection R p hf U hU •
        unitSection R hf (d : ℤ) (op U) hU = homogeneousSection R p U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) ⟨f ^ d, _⟩ *
      (unitPow hf (hU x.2) (d : ℤ)).embed = Localization.mk (p : A) 1
  simp only [NumDenShift.embed_def, unitPow, Int.toNat_natCast]
  simp only [show (-(d : ℤ)).toNat = 0 by omega, pow_zero]
  rw [Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

/-- In the standard trivialization of `𝒪(d)` on `D₊(f)`, the local coordinate of the
section defined by `p` is the regular function `p / f^d`. -/
theorem unitSectionEquiv_symm_homogeneousSection {d : ℕ} (p : R d) {f : A}
    (hf : f ∈ R 1) (U : Opens (ProjectiveSpectrum.top R))
    (hU : U ≤ ProjectiveSpectrum.basicOpen R f) :
    (unitSectionEquiv R hf (d : ℤ) (op U) hU).symm (homogeneousSection R p U) =
      dehomogenizedSection R p hf U hU := by
  apply (unitSectionEquiv R hf (d : ℤ) (op U) hU).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (dehomogenizedSection_smul_unitSection R p hf U hU).symm

/-- Restricting the section induced by a homogeneous form gives the section induced by
the same form on the smaller open. -/
theorem homogeneousSection_restrict {d : ℕ} (p : R d)
    {U V : Opens (ProjectiveSpectrum.top R)} (hVU : V ≤ U) :
    (Scheme.Modules.presheaf (twist R (d : ℤ))).map
      (Quiver.Hom.op (homOfLE hVU)) (homogeneousSection R p U) =
        homogeneousSection R p V := rfl

/-- A compatible family of sections of `𝒪(d)` on a family of open subsets.  This is the
explicit type-theoretic equalizer of the two restriction maps to pairwise intersections. -/
def CompatibleSectionFamily {ι : Type*} (d : ℤ)
    (U : ι → Opens (ProjectiveSpectrum.top R)) : Type _ :=
  {s : ∀ i, Γ(twist R d, U i) //
    TopCat.Presheaf.IsCompatible (sheafInType R d).1 U s}

/-- Restrict a section of `𝒪(d)` to a compatible family on a collection of smaller opens. -/
def restrictToCompatibleSectionFamily {ι : Type*} (d : ℤ)
    (U : ι → Opens (ProjectiveSpectrum.top R))
    (V : Opens (ProjectiveSpectrum.top R)) (hUV : ∀ i, U i ≤ V) :
    Γ(twist R d, V) → CompatibleSectionFamily R d U := fun s ↦
  ⟨fun i ↦ (sheafInType R d).1.map (homOfLE (hUV i)).op s, by
    intro i j
    rfl⟩

/-- The restriction map from sections on `V` to compatible local families is bijective
whenever the chosen opens cover `V`. -/
theorem restrictToCompatibleSectionFamily_bijective {ι : Type*} (d : ℤ)
    (U : ι → Opens (ProjectiveSpectrum.top R))
    (V : Opens (ProjectiveSpectrum.top R)) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U) :
    Function.Bijective (restrictToCompatibleSectionFamily R d U V hUV) := by
  constructor
  · intro s t hst
    apply (sheafInType R d).eq_of_locally_eq' U V
      (fun i ↦ homOfLE (hUV i)) hcover
    intro i
    exact congrArg (fun q : CompatibleSectionFamily R d U ↦ q.1 i) hst
  · intro sf
    obtain ⟨s, hs, -⟩ := (sheafInType R d).existsUnique_gluing' U V
      (fun i ↦ homOfLE (hUV i)) hcover sf.1 sf.2
    exact ⟨s, Subtype.ext (funext hs)⟩

/-- The Čech equalizer equivalence: sections of `𝒪(d)` on an open are exactly compatible
families of sections on any open cover. -/
noncomputable def sectionsEquivCompatibleSectionFamily {ι : Type*} (d : ℤ)
    (U : ι → Opens (ProjectiveSpectrum.top R))
    (V : Opens (ProjectiveSpectrum.top R)) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U) :
    Γ(twist R d, V) ≃ CompatibleSectionFamily R d U :=
  Equiv.ofBijective (restrictToCompatibleSectionFamily R d U V hUV)
    (restrictToCompatibleSectionFamily_bijective R d U V hUV hcover)

@[simp]
theorem sectionsEquivCompatibleSectionFamily_apply {ι : Type*} (d : ℤ)
    (U : ι → Opens (ProjectiveSpectrum.top R))
    (V : Opens (ProjectiveSpectrum.top R)) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ iSup U) (s : Γ(twist R d, V)) :
    sectionsEquivCompatibleSectionFamily R d U V hUV hcover s =
      restrictToCompatibleSectionFamily R d U V hUV s := rfl

/-- On a degree-one basic open `D₊(f)`, sections of `𝒪(d)` are identified with the
degree-zero homogeneous localization `(R_f)₀`: first divide by the basis `f^d`, then use
the standard affine-chart computation for the structure sheaf. -/
noncomputable def sectionsBasicOpenEquivAway {f : A} (hf : f ∈ R 1) (d : ℤ) :
    Γ(twist R d, Proj.basicOpen R f) ≃ HomogeneousLocalization.Away R f :=
  (unitSectionEquiv R hf d (op (Proj.basicOpen R f)) le_rfl).symm.toEquiv.trans
    (Proj.basicOpenIsoAway R f hf Nat.zero_lt_one).commRingCatIsoToRingEquiv.symm.toEquiv

/-- A degree-`d` homogeneous element represented as the degree-zero fraction `p / f^d`
in the homogeneous localization away from a degree-one element `f`. -/
def homogeneousAway {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1) :
    HomogeneousLocalization.Away R f :=
  HomogeneousLocalization.Away.mk R hf d p
    (by
      convert p.2 using 1
      simp [smul_eq_mul])

@[simp]
theorem homogeneousAway_val {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1) :
    (homogeneousAway R p hf).val =
      Localization.mk (p : A) ⟨f ^ d, by exact ⟨d, rfl⟩⟩ :=
  HomogeneousLocalization.Away.val_mk R d hf p _

/-- A fraction `p / f^m` may be rewritten with any larger denominator exponent `N`
by multiplying its numerator by `f^(N-m)`. -/
theorem homogeneousAway_raiseDenominator {m N : ℕ} (p : R m) {f : A}
    (hf : f ∈ R 1) (hmN : m ≤ N) :
    homogeneousAway R
        (⟨(p : A) * f ^ (N - m), by
          convert SetLike.mul_mem_graded p.2
            (SetLike.pow_mem_graded (N - m) hf) using 1
          simp [smul_eq_mul, Nat.add_sub_of_le hmN]⟩ : R N) hf =
      homogeneousAway R p hf := by
  apply HomogeneousLocalization.val_injective
  rw [homogeneousAway_val, homogeneousAway_val, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  push_cast
  calc
    f ^ m * ((p : A) * f ^ (N - m)) = (p : A) * (f ^ m * f ^ (N - m)) := by ring
    _ = (p : A) * f ^ N := by rw [← pow_add, Nat.add_sub_of_le hmN]
    _ = f ^ N * (p : A) := by ring

/-- Under the affine-chart isomorphism for the structure sheaf, the homogeneous
localization element `p / f^d` is the pointwise section constructed above. -/
theorem awayToSection_homogeneousAway {d : ℕ} (p : R d) {f : A} (hf : f ∈ R 1) :
    Proj.awayToSection R f (homogeneousAway R p hf) =
      dehomogenizedSection R p hf (Proj.basicOpen R f) le_rfl := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]

/-- The affine-coordinate image of the twist section defined by `p` is the homogeneous
localization fraction `p / f^d`. -/
theorem sectionsBasicOpenEquivAway_homogeneousSection {d : ℕ} (p : R d)
    {f : A} (hf : f ∈ R 1) :
    sectionsBasicOpenEquivAway R hf (d : ℤ)
        (homogeneousSection R p (Proj.basicOpen R f)) = homogeneousAway R p hf := by
  apply (Proj.basicOpenIsoAway R f hf Nat.zero_lt_one).commRingCatIsoToRingEquiv.injective
  rw [sectionsBasicOpenEquivAway, Equiv.trans_apply, Equiv.coe_fn_mk]
  erw [RingEquiv.apply_symm_apply]
  erw [unitSectionEquiv_symm_homogeneousSection]
  exact (awayToSection_homogeneousAway R p hf).symm

/-- More generally, on `D₊(f)` the twist fraction `p / f^(N-d)` has affine
coordinate `p / f^N`. -/
theorem sectionsBasicOpenEquivAway_localizedHomogeneousSection {d N : ℕ}
    (p : R N) {f : A} (hf : f ∈ R 1) (hdN : d ≤ N) :
    sectionsBasicOpenEquivAway R hf (d : ℤ)
        (localizedHomogeneousSection R p hf hdN (Proj.basicOpen R f) le_rfl) =
      homogeneousAway R p hf := by
  apply (Proj.basicOpenIsoAway R f hf Nat.zero_lt_one).commRingCatIsoToRingEquiv.injective
  rw [sectionsBasicOpenEquivAway, Equiv.trans_apply, Equiv.coe_fn_mk]
  erw [RingEquiv.apply_symm_apply]
  erw [unitSectionEquiv_symm_localizedHomogeneousSection]
  exact (awayToSection_homogeneousAway R p hf).symm

/-- Inverse form of `sectionsBasicOpenEquivAway_localizedHomogeneousSection`, useful
when a chart fraction has first been put over a uniform denominator. -/
theorem sectionsBasicOpenEquivAway_symm_homogeneousAway {d N : ℕ}
    (p : R N) {f : A} (hf : f ∈ R 1) (hdN : d ≤ N) :
    (sectionsBasicOpenEquivAway R hf (d : ℤ)).symm (homogeneousAway R p hf) =
      localizedHomogeneousSection R p hf hdN (Proj.basicOpen R f) le_rfl := by
  apply (sectionsBasicOpenEquivAway R hf (d : ℤ)).injective
  rw [Equiv.apply_symm_apply]
  exact (sectionsBasicOpenEquivAway_localizedHomogeneousSection R p hf hdN).symm

/-- Multiplication of homogeneous forms agrees with multiplication of the corresponding
sections of twisting sheaves. -/
theorem mulSections_homogeneousSection {d e : ℕ} (p : R d) (q : R e)
    (U : Opens (ProjectiveSpectrum.top R)) :
    mulSections R (d : ℤ) (e : ℤ) (op U)
      (homogeneousSection R p U) (homogeneousSection R q U) =
        homogeneousSection R
          (⟨(p : A) * (q : A), SetLike.mul_mem_graded p.2 q.2⟩ : R (d + e)) U := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) 1 * Localization.mk (q : A) 1 =
    Localization.mk ((p : A) * (q : A)) 1
  rw [Localization.mk_mul]
  congr 1
  all_goals simp

/-- The additive map from the degree-`d` piece of a graded ring to the global sections
of `𝒪(d)` on its projective spectrum. -/
def homogeneousToGlobalSections (d : ℕ) :
    R d →+ Γ(twist R (d : ℤ), ⊤) where
  toFun p := homogeneousSection R p ⊤
  map_zero' := homogeneousSection_zero R d ⊤
  map_add' p q := homogeneousSection_add R p q ⊤

@[simp]
theorem homogeneousToGlobalSections_apply (d : ℕ) (p : R d) :
    homogeneousToGlobalSections R d p = homogeneousSection R p ⊤ := rfl

/-- Multiplication by a degree-zero form before taking the associated section agrees with
the structure-sheaf scalar action afterwards.  This is the scalar-compatibility statement
for `homogeneousToGlobalSections`, without choosing a global `Module (R 0) (R d)` instance. -/
theorem degreeZeroSection_smul_homogeneousSection {d : ℕ} (r : R 0) (p : R d)
    (U : Opens (ProjectiveSpectrum.top R)) :
    degreeZeroSection R r U • homogeneousSection R p U =
      homogeneousSection R
        (⟨(r : A) * (p : A), by simpa using SetLike.mul_mem_graded r.2 p.2⟩ : R d) U := by
  refine Subtype.ext (funext fun x ↦ ?_)
  refine Subtype.ext ?_
  change Localization.mk (r : A) 1 * Localization.mk (p : A) 1 =
    Localization.mk ((r : A) * (p : A)) 1
  rw [Localization.mk_mul]
  congr 1
  all_goals simp

end ProjectiveSpectrum.Twist

namespace Scheme.Modules

variable {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)

/-- The actual pullback map on global sections: apply the unit of the
pullback--pushforward adjunction on the top open. -/
public noncomputable def pullbackGlobalSections : Γ(M, ⊤) →+
    Γ((Scheme.Modules.pullback f).obj M, ⊤) where
  toFun s := by
    simpa using ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ s
  map_zero' := by
    simpa using
      map_zero (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom
  map_add' s t := by
    simpa using
      map_add (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom s t

/-- Pull global sections back and then transport them across a chosen identification of
the pulled-back sheaf. -/
public noncomputable def pullbackGlobalSectionsViaIso {N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) : Γ(M, ⊤) →+ Γ(N, ⊤) where
  toFun s := e.hom.app ⊤ (pullbackGlobalSections f M s)
  map_zero' := by
    change e.hom.val.app (op ⊤) (pullbackGlobalSections f M 0) = 0
    rw [(pullbackGlobalSections f M).map_zero]
    exact (e.hom.val.app (op ⊤)).hom.map_zero
  map_add' s t := by
    change e.hom.val.app (op ⊤) (pullbackGlobalSections f M (s + t)) =
      e.hom.val.app (op ⊤) (pullbackGlobalSections f M s) +
        e.hom.val.app (op ⊤) (pullbackGlobalSections f M t)
    rw [(pullbackGlobalSections f M).map_add]
    exact (e.hom.val.app (op ⊤)).hom.map_add _ _

@[simp]
public theorem pullbackGlobalSectionsViaIso_apply {N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (s : Γ(M, ⊤)) :
    pullbackGlobalSectionsViaIso f M e s =
      e.hom.app ⊤ (pullbackGlobalSections f M s) := rfl

end Scheme.Modules

namespace MvPolynomial

variable (ι R : Type*) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine open `D₊(Xᵢ)` in projective `n`-space over a ring. -/
noncomputable def projectiveStandardOpen (n : ℕ) (R : Type*) [CommRing R]
    (i : Fin (n + 1)) :
    Opens (ProjectiveSpectrum.top (homogeneousSubmodule (Fin (n + 1)) R)) :=
  ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) (X i)

/-- Every polynomial variable has degree one in the standard grading. -/
theorem X_mem_homogeneousSubmodule_one (n : ℕ) (R : Type*) [CommRing R]
    (i : Fin (n + 1)) :
    X i ∈ homogeneousSubmodule (Fin (n + 1)) R 1 :=
  MvPolynomial.isWeightedHomogeneous_X (R := R) (1 : Fin (n + 1) → ℕ) i

/-- Constants identify the coefficient ring with the degree-zero homogeneous
subring of a polynomial ring. -/
noncomputable def coefficientToDegreeZeroRingHom (n : ℕ) (R : Type*) [CommRing R] :
    R →+* homogeneousSubmodule (Fin (n + 1)) R 0 where
  toFun r := ⟨C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' r s := by ext; simp
  map_mul' r s := by ext; simp

/-- The coefficient ring acts on projective-space twist sections through its constant
degree-zero structure-sheaf sections. -/
noncomputable def projectiveSpaceScalarRingHom (n : ℕ) (R : Type*) [CommRing R] :
    R →+* Γ(Proj (homogeneousSubmodule (Fin (n + 1)) R), ⊤) :=
  (ProjectiveSpectrum.Twist.degreeZeroToSectionsRingHom
    (homogeneousSubmodule (Fin (n + 1)) R) ⊤).comp
      (coefficientToDegreeZeroRingHom n R)

@[simp]
theorem projectiveSpaceScalarRingHom_apply (n : ℕ) (R : Type*) [CommRing R] (r : R) :
    projectiveSpaceScalarRingHom n R r =
      ProjectiveSpectrum.Twist.degreeZeroSection
        (homogeneousSubmodule (Fin (n + 1)) R)
          (coefficientToDegreeZeroRingHom n R r) ⊤ := rfl

/-- The natural `R`-module structure on global sections of `𝒪(d)` on `ℙⁿ_R`, obtained
by restricting the structure-sheaf action along constant functions. -/
@[instance_reducible]
noncomputable def projectiveTwistGlobalSectionsModule (n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ) :
    Module R Γ(ProjectiveSpectrum.Twist.twist
      (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) :=
  Module.compHom _ (projectiveSpaceScalarRingHom n R)

attribute [local instance] projectiveTwistGlobalSectionsModule

/-- Every degree-zero homogeneous fraction on a standard projective chart has a
homogeneous numerator and a power of the chart variable as denominator. -/
theorem exists_homogeneousAway_eq (n : ℕ) (R : Type*) [CommRing R]
    (i : Fin (n + 1))
    (z : HomogeneousLocalization.Away
      (homogeneousSubmodule (Fin (n + 1)) R) (X i)) :
    ∃ m : ℕ, ∃ p : homogeneousSubmodule (Fin (n + 1)) R m,
      ProjectiveSpectrum.Twist.homogeneousAway
        (homogeneousSubmodule (Fin (n + 1)) R) p
          (X_mem_homogeneousSubmodule_one n R i) = z := by
  obtain ⟨m, a, ha, hza⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule (Fin (n + 1)) R)
      (X_mem_homogeneousSubmodule_one n R i) z
  have ha' : a ∈ homogeneousSubmodule (Fin (n + 1)) R m := by
    simpa [smul_eq_mul] using ha
  refine ⟨m, ⟨a, ha'⟩, ?_⟩
  simpa only [ProjectiveSpectrum.Twist.homogeneousAway] using hza

/-- A finite family of standard-chart fractions can be presented using one common
denominator exponent `N`, chosen at least as large as a prescribed bound `d`. -/
theorem exists_uniform_homogeneousAway_eq (n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ)
    (z : ∀ i : Fin (n + 1), HomogeneousLocalization.Away
      (homogeneousSubmodule (Fin (n + 1)) R) (X i)) :
    ∃ N : ℕ, d ≤ N ∧
      ∃ p : ∀ _ : Fin (n + 1), homogeneousSubmodule (Fin (n + 1)) R N,
        ∀ i, ProjectiveSpectrum.Twist.homogeneousAway
          (homogeneousSubmodule (Fin (n + 1)) R) (p i)
            (X_mem_homogeneousSubmodule_one n R i) = z i := by
  classical
  choose m p hp using fun i ↦ exists_homogeneousAway_eq n R i (z i)
  let N := max d (Finset.univ.sup m)
  have hdN : d ≤ N := Nat.le_max_left _ _
  have hmN (i : Fin (n + 1)) : m i ≤ N :=
    (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  let q : ∀ i : Fin (n + 1), homogeneousSubmodule (Fin (n + 1)) R N := fun i ↦
    ⟨(p i : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - m i), by
      convert SetLike.mul_mem_graded (p i).2
        (SetLike.pow_mem_graded (N - m i)
          (X_mem_homogeneousSubmodule_one n R i)) using 1
      simp [smul_eq_mul, Nat.add_sub_of_le (hmN i)]⟩
  refine ⟨N, hdN, q, fun i ↦ ?_⟩
  exact (ProjectiveSpectrum.Twist.homogeneousAway_raiseDenominator
    (homogeneousSubmodule (Fin (n + 1)) R) (p i)
      (X_mem_homogeneousSubmodule_one n R i) (hmN i)).trans (hp i)

/-- The variables generate the polynomial ring as an algebra over its degree-zero
homogeneous subring. -/
theorem adjoin_range_X_over_degreeZero_eq_top (n : ℕ) (R : Type*) [CommRing R] :
    Algebra.adjoin (homogeneousSubmodule (Fin (n + 1)) R 0)
      (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) = ⊤ := by
  let S := Algebra.adjoin (homogeneousSubmodule (Fin (n + 1)) R 0)
    (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R))
  refine top_unique fun p hp ↦ ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact S.algebraMap_mem
        ⟨C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- The standard affine opens `D₊(Xᵢ)` cover projective `n`-space. -/
theorem iSup_projectiveStandardOpen_eq_top (n : ℕ) (R : Type*) [CommRing R] :
    ⨆ i : Fin (n + 1), projectiveStandardOpen n R i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, X_mem_homogeneousSubmodule_one n R i⟩
  · exact adjoin_range_X_over_degreeZero_eq_top n R

/-- The explicit Čech equalizer for `𝒪(d)` on the standard affine cover of projective
`n`-space. -/
noncomputable def projectiveStandardSectionsEquiv (n : ℕ) (R : Type*) [CommRing R]
    (d : ℤ) :
    Γ(ProjectiveSpectrum.Twist.twist (homogeneousSubmodule (Fin (n + 1)) R) d, ⊤) ≃
      ProjectiveSpectrum.Twist.CompatibleSectionFamily
        (homogeneousSubmodule (Fin (n + 1)) R) d (projectiveStandardOpen n R) :=
  ProjectiveSpectrum.Twist.sectionsEquivCompatibleSectionFamily
    (homogeneousSubmodule (Fin (n + 1)) R) d (projectiveStandardOpen n R) ⊤
      (fun _ ↦ le_top) (by rw [iSup_projectiveStandardOpen_eq_top])

/-- Read a compatible family on the standard projective cover in affine coordinates.
The `i`-th coordinate is the degree-zero homogeneous fraction obtained after dividing
the twist section by the standard basis `Xᵢ^d` on `D₊(Xᵢ)`. -/
noncomputable def standardCompatibleSectionAway (n : ℕ) (R : Type*) [CommRing R]
    (d : ℤ)
    (s : ProjectiveSpectrum.Twist.CompatibleSectionFamily
      (homogeneousSubmodule (Fin (n + 1)) R) d (projectiveStandardOpen n R))
    (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) R) (X i) :=
  ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
    (homogeneousSubmodule (Fin (n + 1)) R)
      (X_mem_homogeneousSubmodule_one n R i) d (s.1 i)

/-- The standard-cover Čech equalizer written entirely in affine chart coordinates.
An element is a family `zᵢ ∈ (R[X]_{Xᵢ})₀` whose corresponding twist sections agree
after restriction to every pairwise intersection. -/
def StandardCompatibleAwayFamily (n : ℕ) (R : Type*) [CommRing R] (d : ℤ) : Type _ :=
  {z : ∀ i : Fin (n + 1),
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) R) (X i) //
    TopCat.Presheaf.IsCompatible
      (ProjectiveSpectrum.Twist.sheafInType
        (homogeneousSubmodule (Fin (n + 1)) R) d).1
      (projectiveStandardOpen n R)
      (fun i ↦ (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
        (homogeneousSubmodule (Fin (n + 1)) R)
          (X_mem_homogeneousSubmodule_one n R i) d).symm (z i))}

/-- Passing through the standard affine-chart isomorphisms identifies compatible twist
sections with compatible degree-zero localization elements. -/
noncomputable def standardCompatibleSectionFamilyAwayEquiv
    (n : ℕ) (R : Type*) [CommRing R] (d : ℤ) :
    ProjectiveSpectrum.Twist.CompatibleSectionFamily
        (homogeneousSubmodule (Fin (n + 1)) R) d (projectiveStandardOpen n R) ≃
      StandardCompatibleAwayFamily n R d where
  toFun s := ⟨fun i ↦ standardCompatibleSectionAway n R d s i, by
    intro i j
    simpa only [standardCompatibleSectionAway, Equiv.symm_apply_apply] using s.2 i j⟩
  invFun z := ⟨fun i ↦ (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
      (homogeneousSubmodule (Fin (n + 1)) R)
        (X_mem_homogeneousSubmodule_one n R i) d).symm (z.1 i), z.2⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    exact (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
      (homogeneousSubmodule (Fin (n + 1)) R)
        (X_mem_homogeneousSubmodule_one n R i) d).symm_apply_apply (s.1 i)
  right_inv z := by
    apply Subtype.ext
    funext i
    exact (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
      (homogeneousSubmodule (Fin (n + 1)) R)
        (X_mem_homogeneousSubmodule_one n R i) d).apply_symm_apply (z.1 i)

/-- Global sections of `𝒫(d)` are the standard-cover Čech equalizer expressed in the
degree-zero homogeneous localizations at the variables. -/
noncomputable def projectiveStandardSectionsAwayEquiv
    (n : ℕ) (R : Type*) [CommRing R] (d : ℤ) :
    Γ(ProjectiveSpectrum.Twist.twist (homogeneousSubmodule (Fin (n + 1)) R) d, ⊤) ≃
      StandardCompatibleAwayFamily n R d :=
  (projectiveStandardSectionsEquiv n R d).trans
    (standardCompatibleSectionFamilyAwayEquiv n R d)

/-- Every compatible standard-chart family for `𝒫(d)` admits one denominator exponent
`N ≥ d`.  In those coordinates its local sections are the explicit fractions
`pᵢ / Xᵢ^(N-d)`, and the displayed final equality is precisely their Čech compatibility
on each pairwise intersection. -/
theorem StandardCompatibleAwayFamily.exists_uniform_localizedPresentation
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ)
    (s : StandardCompatibleAwayFamily n R (d : ℤ)) :
    ∃ N : ℕ, ∃ hdN : d ≤ N,
      ∃ p : ∀ _ : Fin (n + 1), homogeneousSubmodule (Fin (n + 1)) R N,
        (∀ i, (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
            (homogeneousSubmodule (Fin (n + 1)) R)
              (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)).symm (s.1 i) =
          ProjectiveSpectrum.Twist.localizedHomogeneousSection
            (homogeneousSubmodule (Fin (n + 1)) R) (p i)
              (X_mem_homogeneousSubmodule_one n R i) hdN
                (projectiveStandardOpen n R i) le_rfl) ∧
        ∀ i j,
          (ProjectiveSpectrum.Twist.sheafInType
            (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)).1.map
              (Opens.infLELeft (projectiveStandardOpen n R i)
                (projectiveStandardOpen n R j)).op
              (ProjectiveSpectrum.Twist.localizedHomogeneousSection
                (homogeneousSubmodule (Fin (n + 1)) R) (p i)
                  (X_mem_homogeneousSubmodule_one n R i) hdN
                    (projectiveStandardOpen n R i) le_rfl) =
            (ProjectiveSpectrum.Twist.sheafInType
              (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)).1.map
                (Opens.infLERight (projectiveStandardOpen n R i)
                  (projectiveStandardOpen n R j)).op
                (ProjectiveSpectrum.Twist.localizedHomogeneousSection
                  (homogeneousSubmodule (Fin (n + 1)) R) (p j)
                    (X_mem_homogeneousSubmodule_one n R j) hdN
                      (projectiveStandardOpen n R j) le_rfl) := by
  obtain ⟨N, hdN, p, hp⟩ := exists_uniform_homogeneousAway_eq n R d s.1
  have hlocal (i : Fin (n + 1)) :
      (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
        (homogeneousSubmodule (Fin (n + 1)) R)
          (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)).symm (s.1 i) =
        ProjectiveSpectrum.Twist.localizedHomogeneousSection
          (homogeneousSubmodule (Fin (n + 1)) R) (p i)
            (X_mem_homogeneousSubmodule_one n R i) hdN
              (projectiveStandardOpen n R i) le_rfl := by
    rw [← hp i]
    exact ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway_symm_homogeneousAway
      (homogeneousSubmodule (Fin (n + 1)) R) (p i)
        (X_mem_homogeneousSubmodule_one n R i) hdN
  refine ⟨N, hdN, p, hlocal, fun i j ↦ ?_⟩
  rw [← hlocal i, ← hlocal j]
  exact s.2 i j

/-- Denominator-cleared compatibility on two standard projective charts is the
polynomial cross-product identity
`pᵢ Xⱼ^(N-d) = pⱼ Xᵢ^(N-d)`.  No domain hypothesis on the coefficient ring is
needed: polynomial variables and their products are regular. -/
theorem localizedHomogeneousSection_overlap_cross_eq
    (n : ℕ) (R : Type*) [CommRing R] {d N : ℕ} (hdN : d ≤ N)
    (p q : homogeneousSubmodule (Fin (n + 1)) R N) (i j : Fin (n + 1))
    (hcompat :
      (ProjectiveSpectrum.Twist.sheafInType
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)).1.map
          (Opens.infLELeft (projectiveStandardOpen n R i)
            (projectiveStandardOpen n R j)).op
          (ProjectiveSpectrum.Twist.localizedHomogeneousSection
            (homogeneousSubmodule (Fin (n + 1)) R) p
              (X_mem_homogeneousSubmodule_one n R i) hdN
                (projectiveStandardOpen n R i) le_rfl) =
        (ProjectiveSpectrum.Twist.sheafInType
          (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)).1.map
            (Opens.infLERight (projectiveStandardOpen n R i)
              (projectiveStandardOpen n R j)).op
            (ProjectiveSpectrum.Twist.localizedHomogeneousSection
              (homogeneousSubmodule (Fin (n + 1)) R) q
                (X_mem_homogeneousSubmodule_one n R j) hdN
                  (projectiveStandardOpen n R j) le_rfl)) :
    (p : MvPolynomial (Fin (n + 1)) R) * X j ^ (N - d) =
      (q : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d) := by
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let P := MvPolynomial (Fin (n + 1)) R
  have hcoord := ProjectiveSpectrum.Twist.localizedHomogeneousSection_overlap_coordinates_eq
    G p q (X_mem_homogeneousSubmodule_one n R i)
      (X_mem_homogeneousSubmodule_one n R j) hdN (by
        simpa only [projectiveStandardOpen] using hcompat)
  have haway := ProjectiveSpectrum.Twist.dehomogenizedOverlapAway_eq_mixed_of_sections_eq
    G p q (X_mem_homogeneousSubmodule_one n R i)
      (X_mem_homogeneousSubmodule_one n R j) hdN hcoord
  have hval := congrArg HomogeneousLocalization.val haway
  rw [ProjectiveSpectrum.Twist.dehomogenizedOverlapAway_val,
    ProjectiveSpectrum.Twist.mixedDehomogenizedOverlapAway_val] at hval
  let L := Localization (Submonoid.powers (X i * X j : P))
  have hmap : algebraMap P L ((p : P) * X j ^ N) =
      algebraMap P L ((q : P) * X i ^ (N - d) * X j ^ d) := by
    let t : Submonoid.powers (X i * X j : P) :=
      ⟨(X i * X j) ^ N, ⟨N, rfl⟩⟩
    change Localization.mk ((p : P) * X j ^ N) t =
      Localization.mk ((q : P) * X i ^ (N - d) * X j ^ d) t at hval
    rw [Localization.mk_eq_mk'] at hval
    have hmul := congrArg (fun z : L ↦ z * algebraMap P L (t : P)) hval
    rw [IsLocalization.mk'_spec L ((p : P) * X j ^ N) t,
      IsLocalization.mk'_spec L ((q : P) * X i ^ (N - d) * X j ^ d) t] at hmul
    exact hmul
  have hnum : (p : P) * X j ^ N =
      (q : P) * X i ^ (N - d) * X j ^ d := by
    apply IsLocalization.injectiveₛ L
      (fun z hz ↦ by
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff z (X i * X j : P)).mp hz
        rw [← hk]
        exact ((MvPolynomial.isRegular_X (R := R) (n := i)).mul
          (MvPolynomial.isRegular_X (R := R) (n := j))).pow k)
    exact hmap
  apply (MvPolynomial.isRegular_X_pow (R := R) (n := j) d).right
  calc
    (p : P) * X j ^ (N - d) * X j ^ d = (p : P) * X j ^ N := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hdN]
    _ = (q : P) * X i ^ (N - d) * X j ^ d := hnum

/-- If multiplication by a power of a different variable makes a polynomial divisible
by `X i ^ k`, then the original polynomial was already divisible by that power.  This
coefficientwise form avoids any domain hypothesis on the coefficient ring. -/
theorem X_pow_dvd_of_mul_X_pow_eq_mul_X_pow
    {σ : Type*} {R : Type*} [CommRing R]
    {a b : MvPolynomial σ R} {i j : σ} (hij : i ≠ j) (k : ℕ)
    (h : a * X j ^ k = b * X i ^ k) :
    X i ^ k ∣ a := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  ext m
  by_cases hle : Finsupp.single i k ≤ m
  · rw [coeff_modMonomial_of_le _ hle, coeff_zero]
  · rw [coeff_modMonomial_of_not_le _ hle, coeff_zero]
    have hnot : ¬ Finsupp.single i k ≤ m + Finsupp.single j k := by
      intro hh
      apply hle
      rw [Finsupp.single_le_iff] at hh ⊢
      simpa [Finsupp.single_apply, hij] using hh
    calc
      coeff m a = coeff (m + Finsupp.single j k) (a * X j ^ k) := by
        symm
        rw [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
      _ = coeff (m + Finsupp.single j k) (b * X i ^ k) :=
        congrArg (coeff (m + Finsupp.single j k)) h
      _ = 0 := by
        simp only [X_pow_eq_monomial, coeff_mul_monomial', hnot, ↓reduceIte]

/-- Dividing a degree-`N` homogeneous polynomial by one monomial of degree `k ≤ N`
and discarding nondivisible terms produces a homogeneous polynomial of degree `N - k`. -/
theorem divMonomial_single_mem_homogeneousSubmodule
    {σ : Type*} {R : Type*} [CommRing R] {N k : ℕ}
    (p : homogeneousSubmodule σ R N) (i : σ) (hkN : k ≤ N) :
    divMonomial (p : MvPolynomial σ R) (Finsupp.single i k) ∈
      homogeneousSubmodule σ R (N - k) := by
  rw [mem_homogeneousSubmodule]
  intro m hm
  rw [show (1 : σ → ℕ) = (fun _ ↦ 1) by ext; simp,
    ← Finsupp.degree_eq_weight_one]
  have hm' : coeff (Finsupp.single i k + m) (p : MvPolynomial σ R) ≠ 0 := by
    simpa only [coeff_divMonomial] using hm
  have hdegree := p.2 hm'
  rw [show (1 : σ → ℕ) = (fun _ ↦ 1) by ext; simp,
    ← Finsupp.degree_eq_weight_one] at hdegree
  simp only [map_add, Finsupp.degree_single] at hdegree
  omega

/-- The homogeneous quotient obtained by deleting `k` copies of one variable from
every divisible monomial of a degree-`N` form. -/
noncomputable def homogeneousDivXPower
    {σ : Type*} {R : Type*} [CommRing R] {N k : ℕ}
    (p : homogeneousSubmodule σ R N) (i : σ) (hkN : k ≤ N) :
    homogeneousSubmodule σ R (N - k) :=
  ⟨divMonomial (p : MvPolynomial σ R) (Finsupp.single i k),
    divMonomial_single_mem_homogeneousSubmodule p i hkN⟩

/-- If `X i ^ k` divides a homogeneous form, multiplying its homogeneous quotient
back by that power recovers the original form. -/
theorem X_pow_mul_homogeneousDivXPower_eq
    {σ : Type*} {R : Type*} [CommRing R] {N k : ℕ}
    (p : homogeneousSubmodule σ R N) (i : σ) (hkN : k ≤ N)
    (hdiv : X i ^ k ∣ (p : MvPolynomial σ R)) :
    (X i : MvPolynomial σ R) ^ k *
      (homogeneousDivXPower p i hkN : MvPolynomial σ R) = p := by
  have hmod : modMonomial (p : MvPolynomial σ R) (Finsupp.single i k) = 0 := by
    rw [← monomial_one_dvd_iff_modMonomial_eq_zero, ← X_pow_eq_monomial]
    exact hdiv
  simpa only [homogeneousDivXPower, X_pow_eq_monomial, hmod, add_zero] using
    divMonomial_add_modMonomial (p : MvPolynomial σ R) (Finsupp.single i k)

/-- For at least two variables, a family of degree-`N` forms satisfying the projective
cross-product identities is obtained from one degree-`d` form by multiplying its `i`-th
member by `X i ^ (N - d)`. -/
theorem exists_homogeneous_eq_of_cross_eq_of_pos
    (n : ℕ) (R : Type*) [CommRing R] {d N : ℕ} (hdN : d ≤ N)
    (p : ∀ _ : Fin (n + 1), homogeneousSubmodule (Fin (n + 1)) R N)
    (hn : 0 < n)
    (hcross : ∀ i j,
      (p i : MvPolynomial (Fin (n + 1)) R) * X j ^ (N - d) =
        (p j : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d)) :
    ∃ q : homogeneousSubmodule (Fin (n + 1)) R d, ∀ i,
      (p i : MvPolynomial (Fin (n + 1)) R) =
        (q : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d) := by
  classical
  let i₀ : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let j₀ : Fin (n + 1) := ⟨1, by omega⟩
  have hij : i₀ ≠ j₀ := by simp [i₀, j₀]
  have hdiv : X i₀ ^ (N - d) ∣
      (p i₀ : MvPolynomial (Fin (n + 1)) R) :=
    X_pow_dvd_of_mul_X_pow_eq_mul_X_pow hij (N - d) (hcross i₀ j₀)
  have hkN : N - d ≤ N := Nat.sub_le N d
  let q₀ := homogeneousDivXPower (p i₀) i₀ hkN
  have hq₀ : (X i₀ : MvPolynomial (Fin (n + 1)) R) ^ (N - d) * q₀ = p i₀ :=
    X_pow_mul_homogeneousDivXPower_eq (p i₀) i₀ hkN hdiv
  let q : homogeneousSubmodule (Fin (n + 1)) R d :=
    ⟨(q₀ : MvPolynomial (Fin (n + 1)) R), by
      simpa only [Nat.sub_sub_self hdN] using q₀.2⟩
  refine ⟨q, fun i ↦ ?_⟩
  apply (MvPolynomial.isRegular_X_pow (R := R) (n := i₀) (N - d)).right
  calc
    (p i : MvPolynomial (Fin (n + 1)) R) * X i₀ ^ (N - d) =
        (p i₀ : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d) :=
      (hcross i₀ i).symm
    _ = (X i₀ ^ (N - d) * (q : MvPolynomial (Fin (n + 1)) R)) *
        X i ^ (N - d) := by rw [hq₀]
    _ = ((q : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d)) *
        X i₀ ^ (N - d) := by ring

/-- A homogeneous polynomial in one variable is the single monomial of its degree. -/
theorem homogeneous_fin_one_eq_monomial
    (R : Type*) [CommRing R] (N : ℕ)
    (p : homogeneousSubmodule (Fin 1) R N) :
    (p : MvPolynomial (Fin 1) R) =
      monomial (Finsupp.single (0 : Fin 1) N)
        (coeff (Finsupp.single (0 : Fin 1) N) (p : MvPolynomial (Fin 1) R)) := by
  apply p.2.eq_monomial_of_unique_weight
  intro m hm
  have hone : (1 : Fin 1 → ℕ) = (fun _ ↦ 1) := by ext; simp
  rw [hone] at hm
  have hmdegree : m.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hm
  have hmzero : m (0 : Fin 1) = N := by
    rw [Finsupp.degree_eq_sum] at hmdegree
    simpa using hmdegree
  apply Finsupp.ext
  intro i
  fin_cases i
  simp [hmzero]

/-- For any number of variables, a projectively compatible family of homogeneous
numerators has one common homogeneous quotient.  The one-variable case follows from
the uniqueness of its degree-`N` monomial; the remaining cases use a distinct variable
to establish divisibility without assumptions on the coefficient ring. -/
theorem exists_homogeneous_eq_of_cross_eq
    (n : ℕ) (R : Type*) [CommRing R] {d N : ℕ} (hdN : d ≤ N)
    (p : ∀ _ : Fin (n + 1), homogeneousSubmodule (Fin (n + 1)) R N)
    (hcross : ∀ i j,
      (p i : MvPolynomial (Fin (n + 1)) R) * X j ^ (N - d) =
        (p j : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d)) :
    ∃ q : homogeneousSubmodule (Fin (n + 1)) R d, ∀ i,
      (p i : MvPolynomial (Fin (n + 1)) R) =
        (q : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d) := by
  classical
  by_cases hn : n = 0
  · subst n
    let i₀ : Fin (0 + 1) := 0
    let c := coeff (Finsupp.single i₀ N)
      (p i₀ : MvPolynomial (Fin (0 + 1)) R)
    let q : homogeneousSubmodule (Fin (0 + 1)) R d :=
      ⟨monomial (Finsupp.single i₀ d) c,
        isHomogeneous_monomial c (by simp [i₀])⟩
    refine ⟨q, fun i ↦ ?_⟩
    have hi : i = i₀ := by
      apply Fin.eq_zero
    subst i
    calc
      (p i₀ : MvPolynomial (Fin (0 + 1)) R) =
          monomial (Finsupp.single i₀ N) c := by
        simpa only [i₀, c] using homogeneous_fin_one_eq_monomial R N (p i₀)
      _ = (q : MvPolynomial (Fin (0 + 1)) R) * X i₀ ^ (N - d) := by
        simp only [q, X_pow_eq_monomial, monomial_mul, mul_one,
          ← Finsupp.single_add, Nat.add_sub_of_le hdN]
  · exact exists_homogeneous_eq_of_cross_eq_of_pos n R hdN p (Nat.pos_of_ne_zero hn) hcross

/-- On every standard chart, the fraction map `p ↦ p / Xᵢ^d` is injective on
degree-`d` homogeneous polynomials. -/
theorem homogeneousAway_X_injective (n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ) (i : Fin (n + 1)) :
    Function.Injective (fun p : homogeneousSubmodule (Fin (n + 1)) R d ↦
      ProjectiveSpectrum.Twist.homogeneousAway
        (homogeneousSubmodule (Fin (n + 1)) R) p
          (X_mem_homogeneousSubmodule_one n R i)) := by
  intro p q hpq
  have hval := congrArg HomogeneousLocalization.val hpq
  rw [ProjectiveSpectrum.Twist.homogeneousAway_val,
    ProjectiveSpectrum.Twist.homogeneousAway_val] at hval
  let P := MvPolynomial (Fin (n + 1)) R
  let L := Localization (Submonoid.powers (X i : P))
  have hmap : algebraMap P L (p : P) = algebraMap P L (q : P) := by
    let s : Submonoid.powers (X i : P) := ⟨X i ^ d, ⟨d, rfl⟩⟩
    change Localization.mk (p : P) s = Localization.mk (q : P) s at hval
    rw [Localization.mk_eq_mk'] at hval
    have hmul := congrArg (fun z : L ↦ z * algebraMap P L (s : P)) hval
    rw [IsLocalization.mk'_spec L (p : P) s,
      IsLocalization.mk'_spec L (q : P) s] at hmul
    exact hmul
  apply Subtype.ext
  apply IsLocalization.injectiveₛ L
    (fun z hz ↦ by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff z (X i : P)).mp hz
      rw [← hk]
      exact MvPolynomial.isRegular_X_pow k)
  exact hmap

/-- A homogeneous polynomial is determined by the global section of `𝒪(d)` that it
defines on projective space. -/
theorem homogeneousToGlobalSections_injective (n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ) :
    Function.Injective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) := by
  intro p q hpq
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let U := projectiveStandardOpen n R i
  have hlocal := congrArg (fun s : Γ(ProjectiveSpectrum.Twist.twist G (d : ℤ), ⊤) ↦
    (ProjectiveSpectrum.Twist.sheafInType G (d : ℤ)).1.map
      (homOfLE (le_top : U ≤ ⊤)).op s) hpq
  change ProjectiveSpectrum.Twist.homogeneousSection G p U =
    ProjectiveSpectrum.Twist.homogeneousSection G q U at hlocal
  have haway := congrArg
    (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway G
      (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)) hlocal
  dsimp only [U, projectiveStandardOpen] at haway
  erw [ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway_homogeneousSection,
    ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway_homogeneousSection] at haway
  exact homogeneousAway_X_injective n R d i haway

/-- Send a homogeneous form to its compatible family of sections on the standard
projective cover.  This is the Čech-coordinate form of the global section map. -/
noncomputable def homogeneousToStandardCompatibleSectionFamily
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) R d →
      ProjectiveSpectrum.Twist.CompatibleSectionFamily
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ) (projectiveStandardOpen n R) :=
  fun p ↦ projectiveStandardSectionsEquiv n R (d : ℤ)
    (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d p)

/-- In affine coordinates on the `i`-th standard chart, the compatible family attached
to a homogeneous form `p` is the fraction `p / Xᵢ^d`. -/
@[simp]
theorem standardCompatibleSectionAway_homogeneous
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d) (i : Fin (n + 1)) :
    standardCompatibleSectionAway n R (d : ℤ)
        (homogeneousToStandardCompatibleSectionFamily n R d p) i =
      ProjectiveSpectrum.Twist.homogeneousAway
        (homogeneousSubmodule (Fin (n + 1)) R) p
          (X_mem_homogeneousSubmodule_one n R i) := by
  change ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
      (homogeneousSubmodule (Fin (n + 1)) R)
        (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)
        (ProjectiveSpectrum.Twist.homogeneousSection
          (homogeneousSubmodule (Fin (n + 1)) R) p (projectiveStandardOpen n R i)) = _
  exact ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway_homogeneousSection
    (homogeneousSubmodule (Fin (n + 1)) R) p
      (X_mem_homogeneousSubmodule_one n R i)

/-- The global homogeneous-form map in pure affine Čech coordinates.  Its value on
`p` has `i`-th component exactly `p / Xᵢ^d`. -/
noncomputable def homogeneousToStandardAwayFamily
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) R d → StandardCompatibleAwayFamily n R (d : ℤ) :=
  fun p ↦ standardCompatibleSectionFamilyAwayEquiv n R (d : ℤ)
    (homogeneousToStandardCompatibleSectionFamily n R d p)

@[simp]
theorem homogeneousToStandardAwayFamily_apply
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d) (i : Fin (n + 1)) :
    (homogeneousToStandardAwayFamily n R d p).1 i =
      ProjectiveSpectrum.Twist.homogeneousAway
        (homogeneousSubmodule (Fin (n + 1)) R) p
          (X_mem_homogeneousSubmodule_one n R i) :=
  standardCompatibleSectionAway_homogeneous n R d p i

/-- Effectivity of compatible twist sections and effectivity of their affine localization
coordinates are the same statement. -/
theorem surjective_homogeneousToStandardCompatible_iff_away
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Surjective (homogeneousToStandardCompatibleSectionFamily n R d) ↔
      Function.Surjective (homogeneousToStandardAwayFamily n R d) := by
  let e := standardCompatibleSectionFamilyAwayEquiv n R (d : ℤ)
  constructor
  · intro hf z
    obtain ⟨s, rfl⟩ := e.surjective z
    obtain ⟨p, rfl⟩ := hf s
    exact ⟨p, rfl⟩
  · intro hef s
    obtain ⟨p, hp⟩ := hef (e s)
    exact ⟨p, e.injective hp⟩

/-- Surjectivity of the global homogeneous-form map is exactly effectivity of compatible
standard-chart families. -/
theorem surjective_homogeneousToGlobalSections_iff_standardCompatible
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Surjective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) ↔
    Function.Surjective (homogeneousToStandardCompatibleSectionFamily n R d) := by
  let e := projectiveStandardSectionsEquiv n R (d : ℤ)
  let f := ProjectiveSpectrum.Twist.homogeneousToGlobalSections
    (homogeneousSubmodule (Fin (n + 1)) R) d
  constructor
  · intro hf s
    obtain ⟨t, rfl⟩ := e.surjective s
    obtain ⟨p, rfl⟩ := hf t
    exact ⟨p, rfl⟩
  · intro hef s
    obtain ⟨p, hp⟩ := hef (e s)
    refine ⟨p, e.injective ?_⟩
    exact hp

/-- The computation `Γ(ℙⁿ_R, 𝒪(d)) = R[x₀, …, xₙ]_d` is reduced to one explicit
Čech-effectivity statement: every compatible standard-chart family comes from a form.
Injectivity is already unconditional. -/
theorem bijective_homogeneousToGlobalSections_iff_standardCompatible
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Bijective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) ↔
    Function.Surjective (homogeneousToStandardCompatibleSectionFamily n R d) := by
  change (Function.Injective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) ∧
    Function.Surjective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d)) ↔ _
  rw [and_iff_right (homogeneousToGlobalSections_injective n R d),
    surjective_homogeneousToGlobalSections_iff_standardCompatible]

/-- Final affine Čech reduction of the global-sections computation: bijectivity is
equivalent to the purely algebraic assertion that every compatible family of degree-zero
fractions on the standard localizations is `p / Xᵢ^d` for one homogeneous form `p`. -/
theorem bijective_homogeneousToGlobalSections_iff_standardAway
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Bijective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) ↔
    Function.Surjective (homogeneousToStandardAwayFamily n R d) := by
  rw [bijective_homogeneousToGlobalSections_iff_standardCompatible,
    surjective_homogeneousToStandardCompatible_iff_away]

/-- Every compatible family of standard-chart fractions for `𝒪(d)` is induced by one
degree-`d` homogeneous polynomial. -/
theorem homogeneousToStandardAwayFamily_surjective
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Surjective (homogeneousToStandardAwayFamily n R d) := by
  classical
  intro s
  obtain ⟨N, hdN, p, hlocal, hcompat⟩ :=
    s.exists_uniform_localizedPresentation n R d
  have hcross (i j : Fin (n + 1)) :
      (p i : MvPolynomial (Fin (n + 1)) R) * X j ^ (N - d) =
        (p j : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d) :=
    localizedHomogeneousSection_overlap_cross_eq n R hdN (p i) (p j) i j (hcompat i j)
  obtain ⟨q, hq⟩ := exists_homogeneous_eq_of_cross_eq n R hdN p hcross
  refine ⟨q, ?_⟩
  apply Subtype.ext
  funext i
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let hXi := X_mem_homogeneousSubmodule_one n R i
  have hs : s.1 i = ProjectiveSpectrum.Twist.homogeneousAway G (p i) hXi := by
    have hi := congrArg
      (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway
        (homogeneousSubmodule (Fin (n + 1)) R)
          (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)) (hlocal i)
    rw [Equiv.apply_symm_apply] at hi
    exact hi.trans
      (ProjectiveSpectrum.Twist.sectionsBasicOpenEquivAway_localizedHomogeneousSection
        (homogeneousSubmodule (Fin (n + 1)) R) (p i)
          (X_mem_homogeneousSubmodule_one n R i) hdN)
  let qi : homogeneousSubmodule (Fin (n + 1)) R N :=
    ⟨(q : MvPolynomial (Fin (n + 1)) R) * X i ^ (N - d), by
      convert SetLike.mul_mem_graded q.2
        (SetLike.pow_mem_graded (N - d) hXi) using 1
      simp [smul_eq_mul, Nat.add_sub_of_le hdN]⟩
  have hpqi : p i = qi := Subtype.ext (hq i)
  calc
    (homogeneousToStandardAwayFamily n R d q).1 i =
        ProjectiveSpectrum.Twist.homogeneousAway G q hXi :=
      homogeneousToStandardAwayFamily_apply n R d q i
    _ = ProjectiveSpectrum.Twist.homogeneousAway G qi hXi := by
      simpa only [qi] using
        (ProjectiveSpectrum.Twist.homogeneousAway_raiseDenominator G q hXi hdN).symm
    _ = ProjectiveSpectrum.Twist.homogeneousAway G (p i) hXi := by rw [hpqi]
    _ = s.1 i := hs.symm

/-- The degree-`d` homogeneous forms are in bijection with global sections of `𝒪(d)`
on projective `n`-space over an arbitrary commutative ring. -/
theorem homogeneousToGlobalSections_bijective
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Function.Bijective (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d) := by
  rw [bijective_homogeneousToGlobalSections_iff_standardAway]
  exact homogeneousToStandardAwayFamily_surjective n R d

/-- The additive equivalence between degree-`d` forms and global sections of `𝒪(d)`
on projective space. -/
noncomputable def homogeneousSubmoduleGlobalSectionsAddEquiv
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) R d ≃+
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) :=
  AddEquiv.ofBijective
    (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d)
    (homogeneousToGlobalSections_bijective n R d)

@[simp]
theorem homogeneousSubmoduleGlobalSectionsAddEquiv_apply
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d) :
    homogeneousSubmoduleGlobalSectionsAddEquiv n R d p =
      ProjectiveSpectrum.Twist.homogeneousToGlobalSections
        (homogeneousSubmodule (Fin (n + 1)) R) d p := rfl

/-- The homogeneous-form map as an `R`-linear map, for the natural coefficient-ring
module structure on global twist sections. -/
noncomputable def homogeneousToGlobalSectionsLinearMap
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    letI := projectiveTwistGlobalSectionsModule n R d
    homogeneousSubmodule (Fin (n + 1)) R d →ₗ[R]
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) := by
  letI := projectiveTwistGlobalSectionsModule n R d
  let G := homogeneousSubmodule (Fin (n + 1)) R
  refine
    { ProjectiveSpectrum.Twist.homogeneousToGlobalSections G d with
      map_smul' := fun r p ↦ ?_ }
  change ProjectiveSpectrum.Twist.homogeneousSection G (r • p) ⊤ =
    ProjectiveSpectrum.Twist.degreeZeroSection G
        (coefficientToDegreeZeroRingHom n R r) ⊤ •
      ProjectiveSpectrum.Twist.homogeneousSection G p ⊤
  rw [ProjectiveSpectrum.Twist.degreeZeroSection_smul_homogeneousSection]
  congr 2
  apply Subtype.ext
  exact MvPolynomial.smul_eq_C_mul (p : MvPolynomial (Fin (n + 1)) R) r

/-- The `R`-linear equivalence
`R[x₀, …, xₙ]_d ≃ Γ(ℙⁿ_R, 𝒪(d))`. -/
noncomputable def homogeneousSubmoduleGlobalSectionsLinearEquiv
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    letI := projectiveTwistGlobalSectionsModule n R d
    homogeneousSubmodule (Fin (n + 1)) R d ≃ₗ[R]
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) := by
  letI := projectiveTwistGlobalSectionsModule n R d
  exact LinearEquiv.ofBijective (homogeneousToGlobalSectionsLinearMap n R d)
    (homogeneousToGlobalSections_bijective n R d)

@[simp]
theorem homogeneousSubmoduleGlobalSectionsLinearEquiv_apply
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d) :
    letI := projectiveTwistGlobalSectionsModule n R d
    homogeneousSubmoduleGlobalSectionsLinearEquiv n R d p =
      ProjectiveSpectrum.Twist.homogeneousToGlobalSections
        (homogeneousSubmodule (Fin (n + 1)) R) d p := rfl

/-- Homogeneous polynomials of degree `d` are the free `R`-module of coefficient
families indexed by monomials of total degree `d`. -/
noncomputable def homogeneousSubmoduleFinsuppEquiv (d : ℕ) :
    homogeneousSubmodule ι R d ≃ₗ[R] {m : ι →₀ ℕ // m.degree = d} →₀ R :=
  (LinearEquiv.ofEq (homogeneousSubmodule ι R d)
      (restrictSupport R {m : ι →₀ ℕ | m.degree = d})
      (homogeneousSubmodule_eq_finsupp_supported ι R d)).trans
    (basisRestrictSupport R {m : ι →₀ ℕ | m.degree = d}).repr

@[simp]
theorem homogeneousSubmoduleFinsuppEquiv_apply (d : ℕ)
    (p : homogeneousSubmodule ι R d) (m : {m : ι →₀ ℕ // m.degree = d}) :
    homogeneousSubmoduleFinsuppEquiv ι R d p m = coeff m.1 p.1 := by
  simp only [homogeneousSubmoduleFinsuppEquiv, LinearEquiv.trans_apply]
  change p.1.coeff m.1 = _
  rfl

/-- The degree-`d` monomials in `n + 1` variables, noncomputably enumerated by
`Fin ((n + d).choose n)`. -/
noncomputable def degreeMonomialEquivFin (n d : ℕ) :
    {m : Fin (n + 1) →₀ ℕ // m.degree = d} ≃ Fin ((n + d).choose n) := by
  letI : Fintype {m : Fin (n + 1) →₀ ℕ // m.degree = d} :=
    Finsupp.fintypeDegree (Fin (n + 1)) d
  exact Fintype.equivFinOfCardEq <| by
    calc
      Fintype.card {m : Fin (n + 1) →₀ ℕ // m.degree = d} =
          (Fintype.card (Fin (n + 1)) + d - 1).choose d :=
        Finsupp.card_degree (Fin (n + 1)) d
      _ = (n + d).choose d := by
        rw [Fintype.card_fin]
        congr 1
        omega
      _ = (n + d).choose n := (Nat.choose_symm_add (a := n) (b := d)).symm

/-- The degree-`d` homogeneous polynomials in `n + 1` variables form a free module of
rank `binom(n + d, n)`.  This is the module that occurs as `π_* 𝒪(d)` after the
global-sections comparison is proved. -/
noncomputable def homogeneousSubmoduleFinFinsuppEquiv (n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) R d ≃ₗ[R] Fin ((n + d).choose n) →₀ R :=
  (homogeneousSubmoduleFinsuppEquiv (Fin (n + 1)) R d).trans
    (Finsupp.domLCongr (degreeMonomialEquivFin n d))

/-- A basis of degree-`d` forms in `n + 1` variables indexed by exactly
`binom(n + d, n)` elements. -/
noncomputable def homogeneousSubmoduleFinBasis (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Fin ((n + d).choose n)) R (homogeneousSubmodule (Fin (n + 1)) R d) :=
  Module.Basis.ofRepr (homogeneousSubmoduleFinFinsuppEquiv n R d)

/-- Global sections of `𝒪(d)` on `ℙⁿ_R` are finite free of rank
`binom(n + d, n)` over every commutative coefficient ring. -/
noncomputable def projectiveTwistGlobalSectionsBasis
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    letI := projectiveTwistGlobalSectionsModule n R d
    Module.Basis (Fin ((n + d).choose n)) R
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) := by
  letI := projectiveTwistGlobalSectionsModule n R d
  exact (homogeneousSubmoduleFinBasis n R d).map
    (homogeneousSubmoduleGlobalSectionsLinearEquiv n R d)

/-- Global sections of `𝒪(d)` on projective space form a finite projective module over
the coefficient ring (in fact the displayed basis makes them finite free). -/
theorem projectiveTwistGlobalSections_finite_projective
    (n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Module.Finite R
        Γ(ProjectiveSpectrum.Twist.twist
          (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) ∧
      Module.Projective R
        Γ(ProjectiveSpectrum.Twist.twist
          (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) :=
  ⟨Module.Finite.of_basis (projectiveTwistGlobalSectionsBasis n R d),
    Module.Projective.of_basis (projectiveTwistGlobalSectionsBasis n R d)⟩

/-- Over a field, the dimension of the global sections of `𝒪(d)` on projective
`n`-space is `binom(n + d, n)`. -/
theorem finrank_projectiveTwistGlobalSections
    (n : ℕ) (K : Type*) [Field K] (d : ℕ) :
    Module.finrank K
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) K) (d : ℤ), ⊤) =
      (n + d).choose n := by
  rw [Module.finrank_eq_card_basis (projectiveTwistGlobalSectionsBasis n K d),
    Fintype.card_fin]

/-- A finite family of homogeneous pieces in `n + 1` variables is free, with one basis
vector for each pair consisting of a summand and a monomial of the requested degree.
This is the algebraic module underlying global sections of a finite direct sum of twists. -/
noncomputable def homogeneousSubmoduleFinFamilyBasis (r n : ℕ) (R : Type*) [CommRing R]
    (degree : Fin r → ℕ) :
    Module.Basis (Σ j : Fin r, Fin ((n + degree j).choose n)) R
      (∀ j : Fin r, homogeneousSubmodule (Fin (n + 1)) R (degree j)) :=
  Pi.basis fun j : Fin r ↦ homogeneousSubmoduleFinBasis n R (degree j)

/-- For a constant degree `d`, a finite family of degree-`d` homogeneous pieces has the
product-indexed basis expected for a finite direct sum of equal twists. -/
noncomputable def homogeneousSubmoduleFinSumBasis (r n : ℕ) (R : Type*) [CommRing R]
    (d : ℕ) :
    Module.Basis (Fin r × Fin ((n + d).choose n)) R
      (Fin r → homogeneousSubmodule (Fin (n + 1)) R d) :=
  (homogeneousSubmoduleFinFamilyBasis r n R fun _ ↦ d).reindex
    (Equiv.sigmaEquivProd _ _)

/-- Global sections of a finite family of nonnegative twists are finite free, with a
basis indexed by the summand and its degree monomials.  This is the global-sections
module of the corresponding finite direct sum, written as a finite product. -/
noncomputable def projectiveTwistGlobalSectionsFinFamilyBasis
    (r n : ℕ) (R : Type*) [CommRing R] (degree : Fin r → ℕ) :
    Module.Basis (Σ j : Fin r, Fin ((n + degree j).choose n)) R
      (∀ j : Fin r,
        Γ(ProjectiveSpectrum.Twist.twist
          (homogeneousSubmodule (Fin (n + 1)) R) (degree j : ℤ), ⊤)) :=
  Pi.basis fun j : Fin r ↦ projectiveTwistGlobalSectionsBasis n R (degree j)

/-- For `r` equal twists, the finite-free basis of global sections is indexed by
`Fin r × Fin (binom(n + d, n))`. -/
noncomputable def projectiveTwistGlobalSectionsFinSumBasis
    (r n : ℕ) (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Fin r × Fin ((n + d).choose n)) R
      (Fin r → Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤)) :=
  (projectiveTwistGlobalSectionsFinFamilyBasis r n R fun _ ↦ d).reindex
    (Equiv.sigmaEquivProd _ _)

/-- A finite family of global sections of nonnegative twists is a finite projective
module over the coefficient ring. -/
theorem projectiveTwistGlobalSectionsFinFamily_finite_projective
    (r n : ℕ) (R : Type*) [CommRing R] (degree : Fin r → ℕ) :
    Module.Finite R
        (∀ j : Fin r,
          Γ(ProjectiveSpectrum.Twist.twist
            (homogeneousSubmodule (Fin (n + 1)) R) (degree j : ℤ), ⊤)) ∧
      Module.Projective R
        (∀ j : Fin r,
          Γ(ProjectiveSpectrum.Twist.twist
            (homogeneousSubmodule (Fin (n + 1)) R) (degree j : ℤ), ⊤)) :=
  ⟨Module.Finite.of_basis
      (projectiveTwistGlobalSectionsFinFamilyBasis r n R degree),
    Module.Projective.of_basis
      (projectiveTwistGlobalSectionsFinFamilyBasis r n R degree)⟩

variable {ι R} {S : Type*} [CommRing S]

/-- Change of coefficients preserves the homogeneous piece of every degree. -/
noncomputable def homogeneousSubmoduleMap (f : R →+* S) (d : ℕ) :
    homogeneousSubmodule ι R d →ₛₗ[f] homogeneousSubmodule ι S d where
  toFun p := ⟨map f p.1, p.2.map f⟩
  map_add' p q := by ext m; simp
  map_smul' r p := by
    ext m
    calc
      coeff m (map f (r • p.1)) = f (coeff m (r • p.1)) :=
        MvPolynomial.coeff_map (f := f) (r • p.1) m
      _ = f r * f (coeff m p.1) := by simp
      _ = coeff m (f r • map f p.1) := by
        symm
        calc
          coeff m (f r • map f p.1) = f r * coeff m (map f p.1) := by simp
          _ = f r * f (coeff m p.1) := by
            rw [MvPolynomial.coeff_map]

@[simp]
theorem homogeneousSubmoduleMap_coe (f : R →+* S) (d : ℕ)
    (p : homogeneousSubmodule ι R d) :
    (homogeneousSubmoduleMap f d p : MvPolynomial ι S) = map f p.1 := rfl

@[simp]
theorem coeff_homogeneousSubmoduleMap (f : R →+* S) (d : ℕ)
    (p : homogeneousSubmodule ι R d) (m : ι →₀ ℕ) :
    coeff m (homogeneousSubmoduleMap f d p).1 = f (coeff m p.1) := by
  exact MvPolynomial.coeff_map (f := f) p.1 m

/-- Under the monomial-coordinate equivalences, changing coefficients acts coefficientwise. -/
theorem homogeneousSubmoduleFinsuppEquiv_map (f : R →+* S) (d : ℕ)
    (p : homogeneousSubmodule ι R d)
    (m : {m : ι →₀ ℕ // m.degree = d}) :
    homogeneousSubmoduleFinsuppEquiv ι S d (homogeneousSubmoduleMap f d p) m =
      f (homogeneousSubmoduleFinsuppEquiv ι R d p m) := by
  rw [homogeneousSubmoduleFinsuppEquiv_apply, homogeneousSubmoduleFinsuppEquiv_apply]
  exact MvPolynomial.coeff_map (f := f) p.1 m.1

/-- The finite monomial coordinates for homogeneous forms in `n + 1` variables commute
with change of coefficients. -/
theorem homogeneousSubmoduleFinFinsuppEquiv_map (f : R →+* S) (n d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d)
    (m : Fin ((n + d).choose n)) :
    homogeneousSubmoduleFinFinsuppEquiv n S d (homogeneousSubmoduleMap f d p) m =
      f (homogeneousSubmoduleFinFinsuppEquiv n R d p m) := by
  change homogeneousSubmoduleFinsuppEquiv (Fin (n + 1)) S d
      (homogeneousSubmoduleMap f d p) ((degreeMonomialEquivFin n d).symm m) =
    f (homogeneousSubmoduleFinsuppEquiv (Fin (n + 1)) R d p
      ((degreeMonomialEquivFin n d).symm m))
  exact homogeneousSubmoduleFinsuppEquiv_map f d p _

/-- Homogeneous forms commute with arbitrary extension of scalars.  In monomial
coordinates this is the standard base-change equivalence for a finite free module. -/
noncomputable def homogeneousSubmoduleBaseChangeEquiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n d : ℕ) :
    S ⊗[R] (homogeneousSubmodule (Fin (n + 1)) R d) ≃ₗ[S]
      homogeneousSubmodule (Fin (n + 1)) S d :=
  Algebra.TensorProduct.equivFinsuppOfBasis S
      (homogeneousSubmoduleFinBasis n R d) ≪≫ₗ
    (homogeneousSubmoduleFinFinsuppEquiv n S d).symm

@[simp]
theorem homogeneousSubmoduleBaseChangeEquiv_tmul
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n d : ℕ) (s : S) (p : homogeneousSubmodule (Fin (n + 1)) R d) :
    homogeneousSubmoduleBaseChangeEquiv R S n d (s ⊗ₜ[R] p) =
      s • homogeneousSubmoduleMap (algebraMap R S) d p := by
  apply (homogeneousSubmoduleFinFinsuppEquiv n S d).injective
  ext m
  simp [homogeneousSubmoduleBaseChangeEquiv,
    homogeneousSubmoduleFinBasis, homogeneousSubmoduleFinFinsuppEquiv_map]
  rw [Algebra.smul_def, mul_comm]

/-- The global sections of `𝒪(d)` commute with arbitrary extension of coefficient
scalars.  This is the tensor-product base-change equivalence obtained from the
homogeneous-form computation. -/
noncomputable def projectiveTwistGlobalSectionsBaseChangeEquiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n d : ℕ) :
    S ⊗[R] Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) ≃ₗ[S]
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) S) (d : ℤ), ⊤) :=
  (homogeneousSubmoduleGlobalSectionsLinearEquiv n R d).symm.baseChange R S _ _ ≪≫ₗ
    homogeneousSubmoduleBaseChangeEquiv R S n d ≪≫ₗ
      homogeneousSubmoduleGlobalSectionsLinearEquiv n S d

@[simp]
theorem projectiveTwistGlobalSectionsBaseChangeEquiv_tmul_homogeneous
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n d : ℕ) (s : S) (p : homogeneousSubmodule (Fin (n + 1)) R d) :
    projectiveTwistGlobalSectionsBaseChangeEquiv R S n d
        (s ⊗ₜ[R] ProjectiveSpectrum.Twist.homogeneousToGlobalSections
          (homogeneousSubmodule (Fin (n + 1)) R) d p) =
      s • ProjectiveSpectrum.Twist.homogeneousToGlobalSections
        (homogeneousSubmodule (Fin (n + 1)) S) d
          (homogeneousSubmoduleMap (algebraMap R S) d p) := by
  rw [show ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d p =
        homogeneousSubmoduleGlobalSectionsLinearEquiv n R d p by rfl]
  simp [projectiveTwistGlobalSectionsBaseChangeEquiv]
  rw [show (homogeneousSubmoduleGlobalSectionsLinearEquiv n R d).symm
      (ProjectiveSpectrum.Twist.homogeneousSection
        (homogeneousSubmodule (Fin (n + 1)) R) p ⊤) = p by
    exact (homogeneousSubmoduleGlobalSectionsLinearEquiv n R d).symm_apply_apply p]

/-- Coefficient change on global sections of `𝒪(d)`, defined through the canonical
homogeneous-form equivalences.  On a section represented by a form, it applies the
coefficient homomorphism to that form. -/
noncomputable def projectiveTwistGlobalSectionsMap
    (f : R →+* S) (n d : ℕ) :
    Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) →+
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) S) (d : ℤ), ⊤) :=
  (homogeneousSubmoduleGlobalSectionsAddEquiv n S d).toAddMonoidHom.comp
    ((homogeneousSubmoduleMap (ι := Fin (n + 1)) f d).toAddMonoidHom.comp
      (homogeneousSubmoduleGlobalSectionsAddEquiv n R d).symm.toAddMonoidHom)

@[simp]
theorem projectiveTwistGlobalSectionsMap_homogeneous
    (f : R →+* S) (n d : ℕ)
    (p : homogeneousSubmodule (Fin (n + 1)) R d) :
    projectiveTwistGlobalSectionsMap f n d
        (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
          (homogeneousSubmodule (Fin (n + 1)) R) d p) =
      ProjectiveSpectrum.Twist.homogeneousToGlobalSections
        (homogeneousSubmodule (Fin (n + 1)) S) d
          (homogeneousSubmoduleMap f d p) := by
  unfold projectiveTwistGlobalSectionsMap
  dsimp only [AddMonoidHom.comp_apply]
  rw [show ProjectiveSpectrum.Twist.homogeneousToGlobalSections
      (homogeneousSubmodule (Fin (n + 1)) R) d p =
        homogeneousSubmoduleGlobalSectionsAddEquiv n R d p by rfl,
    show (homogeneousSubmoduleGlobalSectionsAddEquiv n R d).symm.toAddMonoidHom
        (homogeneousSubmoduleGlobalSectionsAddEquiv n R d p) = p by
      exact (homogeneousSubmoduleGlobalSectionsAddEquiv n R d).symm_apply_apply p]
  rfl

/-- Two maps on global twists agreeing on homogeneous forms agree everywhere; thus geometric
pullback comparisons reduce to their formula on homogeneous generators. -/
theorem projectiveTwistGlobalSectionsMap_eq_of_homogeneous
    (f : R →+* S) (n d : ℕ)
    (g : Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) →+
      Γ(ProjectiveSpectrum.Twist.twist (homogeneousSubmodule (Fin (n + 1)) S)
        (d : ℤ), ⊤))
    (h : ∀ p : homogeneousSubmodule (Fin (n + 1)) R d,
      g (ProjectiveSpectrum.Twist.homogeneousToGlobalSections
          (homogeneousSubmodule (Fin (n + 1)) R) d p) =
        ProjectiveSpectrum.Twist.homogeneousToGlobalSections
          (homogeneousSubmodule (Fin (n + 1)) S) d
            (homogeneousSubmoduleMap f d p)) :
    g = projectiveTwistGlobalSectionsMap f n d := by
  ext s
  obtain ⟨p, rfl⟩ := (homogeneousToGlobalSections_bijective n R d).2 s
  simpa only [projectiveTwistGlobalSectionsMap_homogeneous] using h p

/-- Tensor base change sends `1 ⊗ s` to coefficient change on the section `s`. -/
@[simp]
theorem projectiveTwistGlobalSectionsBaseChangeEquiv_one_tmul
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n d : ℕ) (s : Γ(ProjectiveSpectrum.Twist.twist
      (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤)) :
    projectiveTwistGlobalSectionsBaseChangeEquiv R S n d (1 ⊗ₜ[R] s) =
      projectiveTwistGlobalSectionsMap (algebraMap R S) n d s := by
  obtain ⟨p, rfl⟩ := (homogeneousToGlobalSections_bijective n R d).2 s
  rw [projectiveTwistGlobalSectionsBaseChangeEquiv_tmul_homogeneous, one_smul,
      projectiveTwistGlobalSectionsMap_homogeneous]

/-- After arbitrary coefficient change, global sections of `𝒪(d)` remain finite free. -/
noncomputable def projectiveTwistGlobalSectionsBaseChangeBasis
    {R S : Type*} [CommRing R] [CommRing S] (_f : R →+* S) (n d : ℕ) :
    Module.Basis (Fin ((n + d).choose n)) S
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) S) (d : ℤ), ⊤) :=
  projectiveTwistGlobalSectionsBasis n S d

/-- After arbitrary base change to a field, the fiber dimension is `binom(n + d, n)`. -/
theorem finrank_projectiveTwistGlobalSections_baseChange
    {R K : Type*} [CommRing R] [Field K] (_f : R →+* K) (n d : ℕ) :
    Module.finrank K
      Γ(ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) K) (d : ℤ), ⊤) =
      (n + d).choose n :=
  finrank_projectiveTwistGlobalSections n K d

end MvPolynomial
