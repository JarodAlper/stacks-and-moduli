module

public import StacksAndModuli.API.ProjectiveTwistGlobalSections

/-!
# Multiplication by a homogeneous element as a map of twisting sheaves

For `p` homogeneous of degree `m`, multiplying sections by `p / 1` is a morphism of sheaves of
`𝒪_{Proj 𝒜}`-modules `𝒪(d) ⟶ 𝒪(d + m)`.  This is the sheaf-level shape of the `mulX` field of
`GradedModule`, and is what turns global sections of the twists of a sheaf into a graded module:
`Γ_*(F)_d := Γ(Proj 𝒜, F(d))` with `mulX i` induced by multiplication by the variable `xᵢ`.

Everything is assembled from `ProjectiveSpectrum.Twist.mulSections` and its algebraic laws in
`definition-twist.lean`, together with the constant section `homogeneousSection`.

## Main definitions

* `ProjectiveSpectrum.Twist.mulSectionHom`: multiplication on sections.
* `ProjectiveSpectrum.Twist.mulHom`: the induced morphism `𝒪(d) ⟶ 𝒪(d + m)` in
  `(Proj 𝒜).Modules`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open HomogeneousLocalization

namespace ProjectiveSpectrum.Twist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Multiplication of a section of `𝒪(d)` by the constant section `p / 1` of `𝒪(m)`, with the
output degree supplied by an equation so that no cast is needed downstream (the same device as
`ProjectiveSpectrum.Twist.mul_mem'`). -/
theorem mul_homogeneousSection_mem {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U)
    (x : U.unop) :
    (s.1 x).1 * ((homogeneousSection 𝒜 p U.unop).1 x).1
      ∈ HomogeneousLocalization.degSet 𝒜
        (x.1).asHomogeneousIdeal.toIdeal.primeCompl dc := by
  rw [hdc]
  exact HomogeneousLocalization.mul_mem_degSet (s.1 x).2
    ((homogeneousSection 𝒜 p U.unop).1 x).2

def mulSectionHom {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (s : (sheafInType 𝒜 d).1.obj U) : (sheafInType 𝒜 dc).1.obj U :=
  ⟨fun x ↦ ⟨(s.1 x).1 * ((homogeneousSection 𝒜 p U.unop).1 x).1,
      mul_homogeneousSection_mem 𝒜 p d dc hdc U s x⟩,
    mul_mem' 𝒜 d (m : ℤ) hdc U s.1 _ s.2 (homogeneousSection 𝒜 p U.unop).2 _⟩

theorem mulSectionHom_add {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s s' : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 p d dc hdc U (s + s')
      = mulSectionHom 𝒜 p d dc hdc U s + mulSectionHom 𝒜 p d dc hdc U s' := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((s.1 x).1 + (s'.1 x).1) * _ = _
  exact add_mul _ _ _

theorem mulSectionHom_smul {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (r : (Proj 𝒜).presheaf.obj U)
    (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 p d dc hdc U (r • s) = r • mulSectionHom 𝒜 p d dc hdc U s := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((r.1 x).val * (s.1 x).1) * _ = (r.1 x).val * ((s.1 x).1 * _)
  exact mul_assoc _ _ _

theorem mulSectionHom_naturality {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : U ⟶ V)
    (s : (sheafInType 𝒜 d).1.obj U) :
    (sheafInType 𝒜 dc).1.map i (mulSectionHom 𝒜 p d dc hdc U s)
      = mulSectionHom 𝒜 p d dc hdc V ((sheafInType 𝒜 d).1.map i s) := rfl

/-- Multiplication by `p`, as a morphism of presheaves of abelian groups. -/
noncomputable def mulPresheafHom {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ)) :
    presheafInAddCommGrp 𝒜 d ⟶ presheafInAddCommGrp 𝒜 dc where
  app U := AddCommGrpCat.ofHom
    { toFun := mulSectionHom 𝒜 p d dc hdc U
      map_zero' := by
        have h := mulSectionHom_add 𝒜 p d dc hdc U 0 0
        simpa using (add_right_cancel (a := mulSectionHom 𝒜 p d dc hdc U 0)
          (b := mulSectionHom 𝒜 p d dc hdc U 0) (by simpa using h.symm))
      map_add' := mulSectionHom_add 𝒜 p d dc hdc U }
  naturality _ _ i := by
    ext s
    exact (mulSectionHom_naturality 𝒜 p d dc hdc i s).symm

/-- **Multiplication by a homogeneous element of degree `m`**, as a morphism
`𝒪(d) ⟶ 𝒪(dc)` of sheaves of `𝒪_{Proj 𝒜}`-modules, for any `dc = d + m`. -/
noncomputable def mulHom {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ)) :
    twist 𝒜 d ⟶ twist 𝒜 dc :=
  ⟨PresheafOfModules.homMk (M₁ := presheafOfModules 𝒜 d) (M₂ := presheafOfModules 𝒜 dc)
    (mulPresheafHom 𝒜 p d dc hdc) (fun U r s ↦ mulSectionHom_smul 𝒜 p d dc hdc U r s)⟩

theorem mulHom_val_app_apply {m : ℕ} (p : 𝒜 m) (d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U) :
    (PresheafOfModules.Hom.app (mulHom 𝒜 p d dc hdc).val U).hom s
      = mulSectionHom 𝒜 p d dc hdc U s := rfl

/-- Multiplications by two homogeneous elements of the *same* degree commute. -/
theorem mulSectionHom_comm {m : ℕ} (p q : 𝒜 m) (d dc dcc : ℤ) (hdc : dc = d + (m : ℤ))
    (hdcc : dcc = dc + (m : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 q dc dcc hdcc U (mulSectionHom 𝒜 p d dc hdc U s)
      = mulSectionHom 𝒜 p dc dcc hdcc U (mulSectionHom 𝒜 q d dc hdc U s) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((s.1 x).1 * Localization.mk (p : A) 1) * Localization.mk (q : A) 1
      = ((s.1 x).1 * Localization.mk (q : A) 1) * Localization.mk (p : A) 1
  ring

/-- The morphism form of `mulSectionHom_comm`: the `mulX` maps of the graded model commute. -/
theorem mulHom_comm {m : ℕ} (p q : 𝒜 m) (d dc dcc : ℤ) (hdc : dc = d + (m : ℤ))
    (hdcc : dcc = dc + (m : ℤ)) :
    mulHom 𝒜 p d dc hdc ≫ mulHom 𝒜 q dc dcc hdcc
      = mulHom 𝒜 q d dc hdc ≫ mulHom 𝒜 p dc dcc hdcc := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U ↦ ?_))
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact mulSectionHom_comm 𝒜 p q d dc dcc hdc hdcc U s

/-- **Multiplication by `p` on the twist of an arbitrary sheaf of modules**, `F(d) ⟶ F(dc)`.
This is the `mulX` map of the graded module `Γ_*(F)`. -/
noncomputable def twistModuleMulHom (F : (Proj 𝒜).Modules) {m : ℕ} (p : 𝒜 m)
    (d dc : ℤ) (hdc : dc = d + (m : ℤ)) :
    twistModule 𝒜 F d ⟶ twistModule 𝒜 F dc :=
  Scheme.Modules.tensorMapRight F (mulHom 𝒜 p d dc hdc)

/-- The `mulX` maps of `Γ_*(F)` commute. -/
theorem twistModuleMulHom_comm (F : (Proj 𝒜).Modules) {m : ℕ} (p q : 𝒜 m)
    (d dc dcc : ℤ) (hdc : dc = d + (m : ℤ)) (hdcc : dcc = dc + (m : ℤ)) :
    twistModuleMulHom 𝒜 F p d dc hdc ≫ twistModuleMulHom 𝒜 F q dc dcc hdcc
      = twistModuleMulHom 𝒜 F q d dc hdc ≫ twistModuleMulHom 𝒜 F p dc dcc hdcc := by
  simp only [twistModuleMulHom, ← Scheme.Modules.tensorMapRight_comp, mulHom_comm]

/-- Multiplication by a degree-one `f` is the twist file's `mulUnitPowSection` with exponent one:
`f / 1` and `f^1 / f^0` are the same fraction. -/
theorem mulSectionHom_eq_mulUnitPowSection {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 (⟨f, hf⟩ : 𝒜 1) d (d + 1) (by norm_num) U s
      = mulUnitPowSection 𝒜 hf 1 d U hU s := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x).1 * Localization.mk f 1
      = (s.1 x).1 * (HomogeneousLocalization.unitPow hf (hU x.2) 1).embed
  congr 1
  rw [HomogeneousLocalization.NumDenShift.embed_def, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [HomogeneousLocalization.unitPow]

/-- **On `D₊(f)`, multiplication by a degree-one `f` is bijective on sections.**  This is the
local triviality of the twisting sheaves, restated for `mulSectionHom`. -/
theorem bijective_mulSectionHom {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Bijective (mulSectionHom 𝒜 (⟨f, hf⟩ : 𝒜 1) d (d + 1) (by norm_num) U) := by
  have h : mulSectionHom 𝒜 (⟨f, hf⟩ : 𝒜 1) d (d + 1) (by norm_num) U
      = mulUnitPowSection 𝒜 hf 1 d U hU :=
    funext fun s ↦ mulSectionHom_eq_mulUnitPowSection 𝒜 hf d U hU s
  rw [h]
  exact ⟨mulUnitPowSection_injective 𝒜 hf 1 d U hU,
    mulUnitPowSection_surjective 𝒜 hf 1 d U hU⟩

/-- Multiplication by `1 : 𝒜 0` is the identity on sections. -/
theorem mulSectionHom_one (d : ℤ) (hdc : d = d + ((0 : ℕ) : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) d d hdc U s = s := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x).1 * Localization.mk (1 : A) 1 = (s.1 x).1
  rw [Localization.mk_one, mul_one]

/-- Multiplication by `1 : 𝒜 0` is the identity morphism of `𝒪(d)`. -/
theorem mulHom_one (d : ℤ) (hdc : d = d + ((0 : ℕ) : ℤ)) :
    mulHom 𝒜 (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) d d hdc = 𝟙 (twist 𝒜 d) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact mulSectionHom_one 𝒜 d hdc U s

/-- Multiplication by `1 : 𝒜 0` is the identity on the twist of an arbitrary sheaf. -/
theorem twistModuleMulHom_one (F : (Proj 𝒜).Modules) (d : ℤ) (hdc : d = d + ((0 : ℕ) : ℤ)) :
    twistModuleMulHom 𝒜 F (⟨1, SetLike.one_mem_graded 𝒜⟩ : 𝒜 0) d d hdc
      = 𝟙 (twistModule 𝒜 F d) := by
  simp only [twistModuleMulHom, mulHom_one]
  exact Scheme.Modules.tensorMapRight_id F (twist 𝒜 d)

/-- Multiplication only sees the underlying element of `A`, not the degree it is recorded in.
This is what lets `a ^ n * a ^ k : 𝒜 (n + k)` be traded for `a ^ N : 𝒜 N` without transporting
any section along `n + k = N`. -/
theorem mulSectionHom_congr {m m' : ℕ} (p : 𝒜 m) (p' : 𝒜 m') (hpp : (p : A) = (p' : A))
    (d dc : ℤ) (hdc : dc = d + (m : ℤ)) (hdc' : dc = d + (m' : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 p d dc hdc U s = mulSectionHom 𝒜 p' d dc hdc' U s := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x).1 * Localization.mk (p : A) 1 = (s.1 x).1 * Localization.mk (p' : A) 1
  rw [hpp]

/-- The morphism form of `mulSectionHom_congr`. -/
theorem mulHom_congr {m m' : ℕ} (p : 𝒜 m) (p' : 𝒜 m') (hpp : (p : A) = (p' : A))
    (d dc : ℤ) (hdc : dc = d + (m : ℤ)) (hdc' : dc = d + (m' : ℤ)) :
    mulHom 𝒜 p d dc hdc = mulHom 𝒜 p' d dc hdc' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact mulSectionHom_congr 𝒜 p p' hpp d dc hdc hdc' U s

/-- The degree index of the multiplier is irrelevant for the twist of an arbitrary sheaf. -/
theorem twistModuleMulHom_congr (F : (Proj 𝒜).Modules) {m m' : ℕ} (p : 𝒜 m) (p' : 𝒜 m')
    (hpp : (p : A) = (p' : A)) (d dc : ℤ) (hdc : dc = d + (m : ℤ)) (hdc' : dc = d + (m' : ℤ)) :
    twistModuleMulHom 𝒜 F p d dc hdc = twistModuleMulHom 𝒜 F p' d dc hdc' := by
  simp only [twistModuleMulHom]
  exact congrArg _ (mulHom_congr 𝒜 p p' hpp d dc hdc hdc')

/-- Multiplying by `p` and then by `q` is multiplying by `p * q`. -/
theorem mulSectionHom_comp {m m' : ℕ} (p : 𝒜 m) (q : 𝒜 m') (d dc dcc : ℤ)
    (hdc : dc = d + (m : ℤ)) (hdcc : dcc = dc + (m' : ℤ))
    (hd' : dcc = d + ((m + m' : ℕ) : ℤ))
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (s : (sheafInType 𝒜 d).1.obj U) :
    mulSectionHom 𝒜 q dc dcc hdcc U (mulSectionHom 𝒜 p d dc hdc U s)
      = mulSectionHom 𝒜
          (⟨(p : A) * (q : A), SetLike.mul_mem_graded p.2 q.2⟩ : 𝒜 (m + m')) d dcc hd' U s := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((s.1 x).1 * Localization.mk (p : A) 1) * Localization.mk (q : A) 1
      = (s.1 x).1 * Localization.mk ((p : A) * (q : A)) 1
  rw [mul_assoc, Localization.mk_mul, one_mul]

/-- The morphism form of `mulSectionHom_comp`. -/
theorem mulHom_comp {m m' : ℕ} (p : 𝒜 m) (q : 𝒜 m') (d dc dcc : ℤ)
    (hdc : dc = d + (m : ℤ)) (hdcc : dcc = dc + (m' : ℤ))
    (hd' : dcc = d + ((m + m' : ℕ) : ℤ)) :
    mulHom 𝒜 p d dc hdc ≫ mulHom 𝒜 q dc dcc hdcc
      = mulHom 𝒜 (⟨(p : A) * (q : A), SetLike.mul_mem_graded p.2 q.2⟩ : 𝒜 (m + m'))
          d dcc hd' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact mulSectionHom_comp 𝒜 p q d dc dcc hdc hdcc hd' U s

/-- The composition law for multiplication on the twist of an arbitrary sheaf. -/
theorem twistModuleMulHom_comp (F : (Proj 𝒜).Modules) {m m' : ℕ} (p : 𝒜 m) (q : 𝒜 m')
    (d dc dcc : ℤ) (hdc : dc = d + (m : ℤ)) (hdcc : dcc = dc + (m' : ℤ))
    (hd' : dcc = d + ((m + m' : ℕ) : ℤ)) :
    twistModuleMulHom 𝒜 F p d dc hdc ≫ twistModuleMulHom 𝒜 F q dc dcc hdcc
      = twistModuleMulHom 𝒜 F
          (⟨(p : A) * (q : A), SetLike.mul_mem_graded p.2 q.2⟩ : 𝒜 (m + m')) d dcc hd' := by
  simp only [twistModuleMulHom, ← Scheme.Modules.tensorMapRight_comp]
  exact congrArg _ (mulHom_comp 𝒜 p q d dc dcc hdc hdcc hd')

end ProjectiveSpectrum.Twist
