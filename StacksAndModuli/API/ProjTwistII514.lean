module

public import StacksAndModuli.API.ProjTwistRestrictIso
public import StacksAndModuli.API.ModulesLocalVanishing

/-!
# Hartshorne II.5.14, chart step

On the chart `D₊(f)`, a section that dies on `D₊(f) ⊓ D₊(g)` is killed by a power of the ratio
`g/f`: this is `AlgebraicGeometry.Proj.isLocalizedModule_res_ratioSection` read through
`IsLocalizedModule.eq_zero_iff`.

Together with the bridge identity `restrict_twistModuleMulHom_pow_eq_ratio` this is the chart-wise
half of the injectivity statement of Hartshorne II.5.14: a global section of `F(e)` vanishing on
`D₊(g)` is killed by `g^N` on every chart, hence — by
`Scheme.Modules.app_top_eq_zero_of_app_restrict` — globally.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false
set_option linter.style.show false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A section over `D₊(f)` that vanishes on `D₊(f) ⊓ D₊(g)` is killed by a power of the ratio
`g/f`. -/
theorem exists_pow_ratioSection_smul_eq_zero {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent]
    (t : Γ(F, basicOpen 𝒜 f))
    (ht : (F.presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op) t = 0) :
    ∃ N : ℕ, (ratioSection 𝒜 hf hg) ^ N • t = 0 := by
  letI : Algebra Γ(Proj 𝒜, basicOpen 𝒜 f)
      Γ(Proj 𝒜, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
    (((Proj 𝒜).presheaf.map
      (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom).toAlgebra
  letI : Module Γ(Proj 𝒜, basicOpen 𝒜 f)
      Γ(F, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
    Module.compHom _ (((Proj 𝒜).presheaf.map
      (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom)
  haveI := isLocalizedModule_res_ratioSection 𝒜 hf hg Nat.one_pos F
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers (ratioSection 𝒜 hf hg))
      (Scheme.Modules.resBasicOpenLinearMap F (ratioSection 𝒜 hf hg))).1 ht
  exact ⟨N, hN⟩

/-- **Chart step of II.5.14.**  If a section of `F(e)` over `D₊(f)` is killed by `(g/f)^N`, then
multiplication by `g^N` kills it. -/
theorem app_twistModuleMulHom_eq_zero_of_smul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (σ : ((Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).obj
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F e)).val.obj (op ⊤))
    (hσ : (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) (op ⊤)) • σ = 0) :
    (PresheafOfModules.Hom.app
      ((Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).map
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)).val
      (op ⊤)).hom σ = 0 := by
  have hb := ProjectiveSpectrum.Twist.restrict_twistModuleMulHom_pow_eq_ratio
    𝒜 F hf hg N e ec hec hfN hgN
  have happ := congrArg
    (fun ψ : (Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).obj
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F e) ⟶
      (Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).obj
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec) ↦
      (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom σ) hb
  refine happ.trans ?_
  have hlin := (PresheafOfModules.Hom.app
      ((Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).map
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)).val
      (op ⊤)).hom.map_smul
    (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) (op ⊤)) σ
  rw [hσ, map_zero] at hlin
  exact hlin.symm

/-- `resTop` of `ratioTop` at the top open is the restriction of `(g/f)^N` to `ι ''ᵁ ⊤`. -/
theorem resTop_ratioTop_top {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ) :
    Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) (op ⊤)
      = ((Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) ⊤)).op).hom
        (ratioSection 𝒜 hf hg ^ N) := by
  simp only [Scheme.Modules.resTop, ProjectiveSpectrum.Twist.ratioTop,
    Scheme.Opens.topIso_inv]
  rfl

/-- The same, with the `appIso` transport that the restricted module structure inserts. -/
theorem appIso_inv_resTop_ratioTop_top {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ) :
    ((((basicOpen 𝒜 f).ι.appIso ⊤).inv)
        (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) (op ⊤)))
      = ((Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) ⊤)).op).hom
        (ratioSection 𝒜 hf hg ^ N) := by
  rw [Scheme.Opens.ι_appIso]
  exact resTop_ratioTop_top 𝒜 hf hg N

/-- **Chart-level injectivity.**  On `D₊(f)`, if `(g/f)^N` kills `t` then so does `g^N`. -/
theorem app_twistModuleMulHom_eq_zero_of_pow_smul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 f))
    (ht : (ratioSection 𝒜 hf hg) ^ N • t = 0) :
    (PresheafOfModules.Hom.app
      ((Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).map
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)).val
      (op ⊤)).hom
      (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) ⊤)).op) t) = 0 := by
  refine app_twistModuleMulHom_eq_zero_of_smul 𝒜 hf hg F N e ec hec hfN hgN _ ?_
  show ((((basicOpen 𝒜 f).ι.appIso ⊤).inv)
      (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) (op ⊤))) •
      (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) ⊤)).op) t) = 0
  rw [appIso_inv_resTop_ratioTop_top]
  have hms := Scheme.Modules.map_smul (ProjectiveSpectrum.Twist.twistModule 𝒜 F e)
    (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) ⊤))
    (ratioSection 𝒜 hf hg ^ N) t
  rw [ht, map_zero] at hms
  exact hms.symm

/-- **Hartshorne II.5.14, injectivity.**  If a global section of `F(e)` vanishes on `D₊(x i₀)`,
then some power of `x i₀` kills it. -/
theorem exists_pow_app_top_eq_zero {ι : Type*} [Finite ι] (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ i, basicOpen 𝒜 (x i))
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [(ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (i₀ : ι) (t : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, ⊤))
    (ht : ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op) t = 0) :
    ∃ N : ℕ, ∀ (hgN : (x i₀) ^ N ∈ 𝒜 N) (ec : ℤ) (hec : ec = e + (N : ℤ)),
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
          (⟨(x i₀) ^ N, hgN⟩ : 𝒜 N) e ec hec) ⊤ t = 0 := by
  classical
  haveI := Fintype.ofFinite ι
  have hchart : ∀ j : ι, ∃ Nj : ℕ,
      (ratioSection 𝒜 (hx j) (hx i₀)) ^ Nj •
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x j) ≤ ⊤)).op) t) = 0 := by
    intro j
    refine exists_pow_ratioSection_smul_eq_zero 𝒜 (hx j) (hx i₀) _ _ ?_
    have hle : (Proj 𝒜).basicOpen (ratioSection 𝒜 (hx j) (hx i₀)) ≤ basicOpen 𝒜 (x i₀) := by
      rw [basicOpen_ratioSection 𝒜 (hx j) (hx i₀) Nat.one_pos]
      exact inf_le_right
    have h1 : ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 (hx j) (hx i₀)))).op)
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x j) ≤ ⊤)).op) t)
        = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hle).op)
          (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜 (x i₀) ≤ ⊤)).op) t) := by
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp]
      congr 1
    rw [h1, ht, map_zero]
  choose Nj hNj using hchart
  refine ⟨Finset.univ.sup Nj, fun hgN ec hec ↦ ?_⟩
  refine Scheme.Modules.app_top_eq_zero_of_app_restrict _
    (fun j ↦ (basicOpen 𝒜 (x j)).ι ''ᵁ ⊤) ?_ t ?_
  · simpa only [Scheme.Opens.ι_image_top] using hcover
  · intro j
    have hN : Nj j ≤ Finset.univ.sup Nj := Finset.le_sup (Finset.mem_univ j)
    have hraise : (ratioSection 𝒜 (hx j) (hx i₀)) ^ (Finset.univ.sup Nj) •
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x j) ≤ ⊤)).op) t) = 0 := by
      rw [← tsub_add_cancel_of_le hN, pow_add, mul_smul, hNj j, smul_zero]
    have hfN : (x j) ^ (Finset.univ.sup Nj) ∈ 𝒜 (Finset.univ.sup Nj) := by
      simpa using SetLike.pow_mem_graded _ (hx j)
    have hkey := app_twistModuleMulHom_eq_zero_of_pow_smul 𝒜 (hx j) (hx i₀) F
      (Finset.univ.sup Nj) e ec hec hfN hgN _ hraise
    have hres : (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 (x j)) ⊤)).op)
        (((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x j) ≤ ⊤)).op) t))
        = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
          (homOfLE (le_top : (basicOpen 𝒜 (x j)).ι ''ᵁ ⊤ ≤ ⊤)).op) t := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      congr 1
    rw [hres] at hkey
    exact hkey

/-- **Chart-level surjectivity.**  Every section over `D₊(f) ⊓ D₊(g)` becomes, after multiplying
by a power of the ratio `g/f`, the restriction of a section over `D₊(f)`. -/
theorem exists_pow_ratioSection_smul_eq_res {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent]
    (y : Γ(F, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg))) :
    ∃ (N : ℕ) (m : Γ(F, basicOpen 𝒜 f)),
      letI : Algebra Γ(Proj 𝒜, basicOpen 𝒜 f)
          Γ(Proj 𝒜, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
        (((Proj 𝒜).presheaf.map
          (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom).toAlgebra
      letI : Module Γ(Proj 𝒜, basicOpen 𝒜 f)
          Γ(F, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
        Module.compHom _ (((Proj 𝒜).presheaf.map
          (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom)
      (ratioSection 𝒜 hf hg) ^ N • y
        = (F.presheaf.map
            (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op) m := by
  letI : Algebra Γ(Proj 𝒜, basicOpen 𝒜 f)
      Γ(Proj 𝒜, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
    (((Proj 𝒜).presheaf.map
      (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom).toAlgebra
  letI : Module Γ(Proj 𝒜, basicOpen 𝒜 f)
      Γ(F, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
    Module.compHom _ (((Proj 𝒜).presheaf.map
      (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom)
  haveI := isLocalizedModule_res_ratioSection 𝒜 hf hg Nat.one_pos F
  obtain ⟨⟨m, ⟨_, N, rfl⟩⟩, hm⟩ :=
    IsLocalizedModule.surj (Submonoid.powers (ratioSection 𝒜 hf hg))
      (Scheme.Modules.resBasicOpenLinearMap F (ratioSection 𝒜 hf hg)) y
  exact ⟨N, m, hm⟩

/-- `resTop` of `ratioTop` over an arbitrary open, generalizing `resTop_ratioTop_top`. -/
theorem resTop_ratioTop {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ)
    (W : ((basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ) :
    Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) W
      = ((Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op).hom
        (ratioSection 𝒜 hf hg ^ N) := by
  simp only [Scheme.Modules.resTop, ProjectiveSpectrum.Twist.ratioTop,
    Scheme.Opens.topIso_inv]
  rfl

/-- The same, with the `appIso` transport the restricted module structure inserts. -/
theorem appIso_inv_resTop_ratioTop {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (N : ℕ)
    (W : ((basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ) :
    ((((basicOpen 𝒜 f).ι.appIso W.unop).inv)
        (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) W))
      = ((Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op).hom
        (ratioSection 𝒜 hf hg ^ N) := by
  rw [Scheme.Opens.ι_appIso]
  exact resTop_ratioTop 𝒜 hf hg N W

/-- **Section-level bridge.**  Over any open of the chart `D₊(f)`, applying multiplication by
`g^N` is multiplication by the function `(g/f)^N` after applying multiplication by `f^N`. -/
theorem app_twistModuleMulHom_eq_smul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (W : ((basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e,
      (basicOpen 𝒜 f).ι ''ᵁ W.unop)) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
      ((basicOpen 𝒜 f).ι ''ᵁ W.unop) σ
      = (((Proj 𝒜).presheaf.map
            (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op).hom
          (ratioSection 𝒜 hf hg ^ N)) •
        Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
          ((basicOpen 𝒜 f).ι ''ᵁ W.unop) σ := by
  have hb := ProjectiveSpectrum.Twist.restrict_twistModuleMulHom_pow_eq_ratio
    𝒜 F hf hg N e ec hec hfN hgN
  have happ := congrArg
    (fun ψ : (Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).obj
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F e) ⟶
      (Scheme.Modules.restrictFunctor (basicOpen 𝒜 f).ι).obj
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F ec) ↦
      (PresheafOfModules.Hom.app ψ.val W).hom σ) hb
  refine happ.trans ?_
  show ((((basicOpen 𝒜 f).ι.appIso W.unop).inv)
      (Scheme.Modules.resTop (ProjectiveSpectrum.Twist.ratioTop 𝒜 hf hg N) W)) •
      (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ((basicOpen 𝒜 f).ι ''ᵁ W.unop) σ) = _
  rw [appIso_inv_resTop_ratioTop]

/-- **Chart-level lift.**  If `(g/f)^N` carries `y` into the image of the restriction from
`D₊(f)`, then multiplication by `g^N` carries `y` to the restriction of a section over
`D₊(f)`. -/
theorem app_twistModuleMulHom_eq_res {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (W : ((basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
    (y : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e,
      (basicOpen 𝒜 f).ι ''ᵁ W.unop))
    (m : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 f))
    (hm : (((Proj 𝒜).presheaf.map
            (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op).hom
          (ratioSection 𝒜 hf hg ^ N)) • y
        = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map
            (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op) m) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
      ((basicOpen 𝒜 f).ι ''ᵁ W.unop) y
      = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F ec).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le (basicOpen 𝒜 f) W.unop)).op)
        (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
          (basicOpen 𝒜 f) m) := by
  rw [app_twistModuleMulHom_eq_smul 𝒜 hf hg F N e ec hec hfN hgN W y,
    ← Scheme.Modules.Hom.app_smul, hm, Scheme.Modules.app_restrict]

/-- Every open contained in `U` is the `ι`-image of its preimage.  This is what lets the
chart-level lemmas, which are stated with the open written `U.ι ''ᵁ W`, be applied to an arbitrary
open of `U` without transporting any section. -/
theorem eq_image_preimage_of_le {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    V = U.ι ''ᵁ (U.ι ⁻¹ᵁ V) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr h).symm

/-- **Chart-level lift, for an arbitrary open of the chart.** -/
theorem app_twistModuleMulHom_eq_res_of_le {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (V : (Proj 𝒜).Opens) (hV : ∃ W : (basicOpen 𝒜 f).toScheme.Opens,
      V = (basicOpen 𝒜 f).ι ''ᵁ W)
    (hVf : V ≤ basicOpen 𝒜 f)
    (y : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V))
    (m : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 f))
    (hm : (((Proj 𝒜).presheaf.map (homOfLE hVf).op).hom
          (ratioSection 𝒜 hf hg ^ N)) • y
        = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F e).presheaf.map (homOfLE hVf).op) m) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec) V y
      = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F ec).presheaf.map (homOfLE hVf).op)
        (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
          (basicOpen 𝒜 f) m) := by
  obtain ⟨W, rfl⟩ := hV
  exact app_twistModuleMulHom_eq_res 𝒜 hf hg F N e ec hec hfN hgN (op W) y m hm

/-- **Hartshorne II.5.14, surjectivity on a chart.**  A section of `F(e)` over `D₊(f) ⊓ D₊(g)`
becomes, after multiplying by a power of `g`, the restriction of a section over `D₊(f)`. -/
theorem exists_app_twistModuleMulHom_eq_res {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (e : ℤ)
    [(ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (y : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e,
      (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg))) :
    ∃ (N : ℕ) (m : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, basicOpen 𝒜 f)),
      ∀ (ec : ℤ) (hec : ec = e + (N : ℤ)) (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N),
        Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec)
          ((Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) y
        = ((ProjectiveSpectrum.Twist.twistModule 𝒜 F ec).presheaf.map
            (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op)
          (Scheme.Modules.Hom.app
            (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
            (basicOpen 𝒜 f) m) := by
  obtain ⟨N, m, hm⟩ := exists_pow_ratioSection_smul_eq_res 𝒜 hf hg
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F e) y
  refine ⟨N, m, fun ec hec hfN hgN ↦ ?_⟩
  exact app_twistModuleMulHom_eq_res_of_le 𝒜 hf hg F N e ec hec hfN hgN
    ((Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg))
    ⟨_, eq_image_preimage_of_le ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))⟩
    ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg)) y m hm

/-- The bridge `app_twistModuleMulHom_eq_smul`, stated for an arbitrary open `V ≤ D₊(f)`. -/
theorem app_twistModuleMulHom_eq_smul_of_le {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f)
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V)) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec) V σ
      = (((Proj 𝒜).presheaf.map (homOfLE hV).op).hom (ratioSection 𝒜 hf hg ^ N)) •
        Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec) V σ := by
  obtain ⟨W, hW⟩ : ∃ W : (basicOpen 𝒜 f).toScheme.Opens, V = (basicOpen 𝒜 f).ι ''ᵁ W :=
    ⟨_, eq_image_preimage_of_le hV⟩
  subst hW
  exact app_twistModuleMulHom_eq_smul 𝒜 hf hg F N e ec hec hfN hgN (op W) σ

/-- **Chart-level injectivity over an arbitrary open of the chart.**  If `(g/f)^N` kills a section
over `V ≤ D₊(f)`, then multiplication by `g^N` kills it. -/
theorem app_twistModuleMulHom_eq_zero_of_le {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (F : (Proj 𝒜).Modules) (N : ℕ) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (hgN : g ^ N ∈ 𝒜 N)
    (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f)
    (σ : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V))
    (hσ : (((Proj 𝒜).presheaf.map (homOfLE hV).op).hom (ratioSection 𝒜 hf hg ^ N)) • σ = 0) :
    Scheme.Modules.Hom.app
      (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (⟨g ^ N, hgN⟩ : 𝒜 N) e ec hec) V σ = 0 := by
  rw [app_twistModuleMulHom_eq_smul_of_le 𝒜 hf hg F N e ec hec hfN hgN V hV σ,
    ← Scheme.Modules.Hom.app_smul, hσ]
  exact map_zero _

end AlgebraicGeometry.Proj
