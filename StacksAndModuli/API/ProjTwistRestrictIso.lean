module

public import StacksAndModuli.API.ModulesRestrictIso
public import StacksAndModuli.API.ProjTwistMulHom
public import StacksAndModuli.API.SchemeModulesPullbackPolynomialTwist
public import StacksAndModuli.API.ModulesSmulHom
public import StacksAndModuli.API.ProjRatioSectionMul

/-!
# `𝒪(d) ≅ 𝒪(d+1)` on `D₊(f)`

For `f` homogeneous of degree one, multiplication by `f` becomes an isomorphism of sheaves of
modules after restriction to `D₊(f)`: over every open of `D₊(f)` it is bijective on sections
(`ProjectiveSpectrum.Twist.bijective_mulSectionHom`), and a morphism of sheaves of modules whose
section maps are all bijective is an isomorphism
(`AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_bijective`).

This is the local triviality of the twisting sheaves in the form needed to twist an *arbitrary*
sheaf: once `restrict (mulHom …)` is invertible, tensoring with `F` and transporting along
`Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion` makes multiplication by `f` invertible on
`F(d)|_{D₊(f)}` too.  See `PLAN-hilbert-quot.md`, "Dependency audit of the five sorries".
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **On `D₊(f)`, multiplication by a degree-one `f` trivializes the twisting sheaves.** -/
theorem isIso_restrict_mulHom {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (hdc : d + 1 = d + ((1 : ℕ) : ℤ)) :
    IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
      (mulHom 𝒜 (⟨f, hf⟩ : 𝒜 1) d (d + 1) hdc)) := by
  refine Scheme.Modules.isIso_restrictFunctor_map_of_bijective _ _ fun U ↦ ?_
  have hle : (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ U
      ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f := Scheme.Opens.ι_image_le _ _
  exact bijective_mulSectionHom 𝒜 hf d
    (op ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ U)) hle

/-- **The trivialization for an arbitrary sheaf.**  Multiplication by a degree-one `f` becomes an
isomorphism `F(d) ≅ F(d+1)` after restriction to `D₊(f)`, for every sheaf of modules `F`. -/
theorem isIso_restrict_twistModuleMulHom {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (hdc : d + 1 = d + ((1 : ℕ) : ℤ)) (F : (Proj 𝒜).Modules) :
    IsIso ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
      (twistModuleMulHom 𝒜 F (⟨f, hf⟩ : 𝒜 1) d (d + 1) hdc)) := by
  haveI := isIso_restrict_mulHom 𝒜 hf d hdc
  exact Scheme.Modules.restrict_tensorMapRight_isIso _ F _

/-- **On `D₊(f)`, multiplication by a degree-one `f` is bijective on sections of `F(d)`**, for
every sheaf of modules `F`.  This is the statement the `Γ_*` comparison needs. -/
theorem bijective_twistModuleMulHom_app {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (hdc : d + 1 = d + ((1 : ℕ) : ℤ)) (F : (Proj 𝒜).Modules)
    (W : (AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens) :
    Function.Bijective
      (((twistModuleMulHom 𝒜 F (⟨f, hf⟩ : 𝒜 1) d (d + 1) hdc).val.app
        (op ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W))).hom) := by
  haveI := isIso_restrict_twistModuleMulHom 𝒜 hf d hdc F
  have key := Scheme.Modules.isIso_app_of_isIso
    ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
      (twistModuleMulHom 𝒜 F (⟨f, hf⟩ : 𝒜 1) d (d + 1) hdc)) (op W)
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 key
  exact hb

/-- **The bridge identity.**  Over `D₊(f)`, multiplication by `g^N` is multiplication by `f^N`
followed by multiplication by the function `(g/f)^N`.

The hypothesis `hr` is exactly what `ratio_pow_mul_homogeneous` supplies: at each point of
`D₊(f)`, the value of `r` is `(g/f)^N`, and `(g/f)^N · (f^N/1) = g^N/1`. -/
theorem restrict_mulHom_pow_eq {f g : A} (_hf : f ∈ 𝒜 1) (_hg : g ∈ 𝒜 1) (N : ℕ)
    (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (r : Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤))
    (hr : ∀ (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
        (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
        (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl),
      (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
            (Scheme.Modules.resTop r W)).1 x).val) * (z * Localization.mk (f ^ N) 1)
        = z * Localization.mk (g ^ N) 1) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (mulHom 𝒜 (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (mulHom 𝒜 (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom r _ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact (hr W x (s.1 x).1).symm

/-- Naturality of the open-immersion tensor isomorphism in the right factor, extracted from the
argument of `Scheme.Modules.restrict_tensorMapRight_isIso`. -/
theorem restrict_tensorMapRight_naturality {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Y.Modules) {G G' : Y.Modules} (ψ : G ⟶ G') :
    (Scheme.Modules.restrictFunctor j).map (Scheme.Modules.tensorMapRight F ψ)
        ≫ (Scheme.Modules.restrictTensorIso j F G').hom
      = (Scheme.Modules.restrictTensorIso j F G).hom
        ≫ Scheme.Modules.tensorMapRight ((Scheme.Modules.restrictFunctor j).obj F)
            ((Scheme.Modules.restrictFunctor j).map ψ) := by
  have h0 := Scheme.Modules.restrictTensorIso_naturality j (𝟙 F) ψ
  have hid : (Scheme.Modules.restrictFunctor j).map (𝟙 F)
      = 𝟙 ((Scheme.Modules.restrictFunctor j).obj F) := (Scheme.Modules.restrictFunctor j).map_id F
  have ht : Scheme.Modules.tensorMapLeft (𝟙 ((Scheme.Modules.restrictFunctor j).obj F))
      ((Scheme.Modules.restrictFunctor j).obj G) = 𝟙 _ := Scheme.Modules.tensorMapLeft_id _ _
  have hs : Scheme.Modules.tensorMapLeft (𝟙 F) G ≫ Scheme.Modules.tensorMapRight F ψ
      = Scheme.Modules.tensorMapRight F ψ := by
    rw [Scheme.Modules.tensorMapLeft_id, Category.id_comp]
  rw [hid, ht, Category.id_comp, hs] at h0
  exact h0

/-- **The bridge identity for an arbitrary sheaf.**  Over `D₊(f)`, multiplication by `g^N` on
`F(e)` is multiplication by `f^N` followed by multiplication by the function `(g/f)^N`. -/
theorem restrict_twistModuleMulHom_pow_eq (F : (Proj 𝒜).Modules) {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (r : Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤))
    (hr : ∀ (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
        (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
        (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl),
      (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
            (Scheme.Modules.resTop r W)).1 x).val) * (z * Localization.mk (f ^ N) 1)
        = z * Localization.mk (g ^ N) 1) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom r _ := by
  rw [← cancel_mono (Scheme.Modules.restrictTensorIso
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι F (twist 𝒜 ec)).hom]
  rw [twistModuleMulHom, twistModuleMulHom, restrict_tensorMapRight_naturality,
    restrict_mulHom_pow_eq 𝒜 hf hg N e ec hec hfN hgN r hr,
    Scheme.Modules.tensorMapRight_comp, Scheme.Modules.tensorMapRight_smulHom,
    ← Category.assoc, ← restrict_tensorMapRight_naturality, Category.assoc,
    Scheme.Modules.smulHom_naturality, ← Category.assoc]
  rfl

/-- The concrete scalar for the bridge: the `N`-th power of the ratio, transported to a global
function on `D₊(f)`. -/
noncomputable def ratioTop {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ) :
    Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤) :=
  (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv
    (AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg ^ N)

/-- `ratioTop` satisfies the hypothesis of the bridge identity: at every point its value is
`(g/f)^N`, and `(g/f)^N · (f^N/1) = g^N/1`. -/
theorem hr_ratioTop {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ)
    (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
    (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
    (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl) :
    (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
        (Scheme.Modules.resTop (ratioTop 𝒜 hf hg N) W)).1 x).val)
      * (z * Localization.mk (f ^ N) 1) = z * Localization.mk (g ^ N) 1 := by
  have hx : f ∈ (x.1).asHomogeneousIdeal.toIdeal.primeCompl :=
    Scheme.Opens.ι_image_le _ _ x.2
  have hval0 : (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
      (Scheme.Modules.resTop (ratioTop 𝒜 hf hg N) W)).1 x))
      = ((AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg).1 ⟨x.1, hx⟩) ^ N := by
    simp only [ratioTop, Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Modules.resTop,
      Scheme.Opens.topIso_inv]
    rfl
  have hval : (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
      (Scheme.Modules.resTop (ratioTop 𝒜 hf hg N) W)).1 x).val)
      = ((AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg).1 ⟨x.1, hx⟩).val ^ N := by
    rw [hval0, HomogeneousLocalization.val_pow]
  rw [hval, ← ratio_pow_mul_homogeneous 𝒜 hf hg N x.1 hx]
  ring

/-- **The bridge identity with the concrete scalar.**  Over `D₊(f)`, multiplication by `g^N` on
`F(e)` is multiplication by `f^N` followed by multiplication by the function `(g/f)^N`. -/
theorem restrict_twistModuleMulHom_pow_eq_ratio (F : (Proj 𝒜).Modules) {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N) :
    (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom (ratioTop 𝒜 hf hg N) _ :=
  restrict_twistModuleMulHom_pow_eq 𝒜 F hf hg N e ec hec hfN hgN _ (hr_ratioTop 𝒜 hf hg N)

end ProjectiveSpectrum.Twist
