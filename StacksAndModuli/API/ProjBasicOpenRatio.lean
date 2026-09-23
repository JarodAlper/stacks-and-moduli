module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import StacksAndModuli.API.QuasicoherentSectionsQcqs

/-!
# The basic open cut out by a ratio of homogeneous elements

For homogeneous `f, g` of positive degrees `d, e`, the element
`HomogeneousLocalization.Away.isLocalizationElem hf hg = g^d / f^e` of `A⁰_f` gives, through
`AlgebraicGeometry.Proj.awayToSection`, a section of `𝒪_{Proj 𝒜}` over `D₊(f)`.  Its basic open is
`D₊(f) ⊓ D₊(g)`.

This is the geometric input for Hartshorne II.5.14: it exhibits `D₊(f) ⊓ D₊(g)` as a *basic open
of a function on the affine open `D₊(f)`*, so the qcqs localization lemma
`Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap_of_qcqs` applies and sections of a
quasicoherent sheaf over `D₊(f) ⊓ D₊(g)` are a localization of its sections over `D₊(f)`.

Mathlib proves the corresponding statement one level down, on `Spec (A⁰_f)`
(`AlgebraicGeometry.Proj.awayι_preimage_basicOpen`); the point here is to say it about a section
of the structure sheaf of `Proj 𝒜` itself, which is what the module-localization interface wants.

## Main results

* `AlgebraicGeometry.Proj.ratioSection`: the section `g^d / f^e` of `𝒪_{Proj 𝒜}` on `D₊(f)`.
* `AlgebraicGeometry.Proj.basicOpen_ratioSection`: its basic open is `D₊(f) ⊓ D₊(g)`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The section `g^{deg f} / f^{deg g}` of the structure sheaf of `Proj 𝒜` over `D₊(f)`. -/
noncomputable def ratioSection {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  (awayToSection 𝒜 f).hom (HomogeneousLocalization.Away.isLocalizationElem hf hg)

/-- The value of the ratio section at a point of `D₊(f)` is the fraction `g^{deg f} / f^{deg g}`
in the homogeneous localization there. -/
theorem ratioSection_apply_val {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (x : ProjectiveSpectrum 𝒜) (hxf : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    ((ratioSection 𝒜 hf hg).1 ⟨x, hxf⟩).val
      = Localization.mk (g ^ d)
        (⟨f ^ e, pow_mem hxf e⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) := rfl

/-- The germ of the ratio section at a point of `D₊(f)` is a unit exactly when `g` does not
vanish there. -/
theorem isUnit_germ_ratioSection {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hd : 0 < d)
    (x : ProjectiveSpectrum 𝒜) (hxf : x ∈ basicOpen 𝒜 f) :
    IsUnit ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 f) x hxf (ratioSection 𝒜 hf hg))
      ↔ x ∈ basicOpen 𝒜 g := by
  have hxf' : f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxf
  have hstalk : IsUnit ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 f) x hxf (ratioSection 𝒜 hf hg))
      ↔ IsUnit (stalkIso' 𝒜 x
          ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 f) x hxf (ratioSection 𝒜 hf hg))) := by
    refine ⟨fun h ↦ h.map (stalkIso' 𝒜 x).toRingHom, fun h ↦ ?_⟩
    simpa using h.map (stalkIso' 𝒜 x).symm.toRingHom
  have hgerm : stalkIso' 𝒜 x
      ((Proj 𝒜).presheaf.germ (basicOpen 𝒜 f) x hxf (ratioSection 𝒜 hf hg))
      = (ratioSection 𝒜 hf hg).1 ⟨x, hxf⟩ :=
    stalkIso'_germ 𝒜 (basicOpen 𝒜 f) x hxf (ratioSection 𝒜 hf hg)
  have hval := ratioSection_apply_val 𝒜 hf hg x hxf'
  rw [hstalk, hgerm, ← HomogeneousLocalization.isUnit_iff_isUnit_val, hval,
    Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff, mem_basicOpen]
  refine ⟨fun h hgx ↦ h (Ideal.pow_mem_of_mem _ hgx d hd),
    fun h hpow ↦ h (x.isPrime.mem_of_pow_mem d hpow)⟩

/-- **The basic open of the ratio section is the intersection of the two basic opens.** -/
theorem basicOpen_ratioSection {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hd : 0 < d) :
    (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g := by
  refine SetLike.ext fun x ↦ ?_
  rw [Scheme.mem_basicOpen'']
  constructor
  · rintro ⟨hxf, hu⟩
    exact ⟨hxf, (isUnit_germ_ratioSection 𝒜 hf hg hd x hxf).1 hu⟩
  · rintro ⟨hxf, hxg⟩
    exact ⟨hxf, (isUnit_germ_ratioSection 𝒜 hf hg hd x hxf).2 hxg⟩

/-- **Hartshorne II.5.14, local form.**  For a quasicoherent sheaf on `Proj 𝒜` and homogeneous
`f, g` with `deg f > 0`, sections over `D₊(f) ⊓ D₊(g)` are the localization of sections over
`D₊(f)` away from the ratio `g^{deg f} / f^{deg g}`.

`D₊(f)` is affine (`isAffineOpen_basicOpen`), hence quasi-compact and quasi-separated, so the
qcqs module-localization lemma applies; `basicOpen_ratioSection` identifies the basic open of the
ratio with `D₊(f) ⊓ D₊(g)`. -/
theorem isLocalizedModule_res_ratioSection {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hd : 0 < d) (N : (Proj 𝒜).Modules) [N.IsQuasicoherent] :
    letI : Algebra Γ(Proj 𝒜, basicOpen 𝒜 f)
        Γ(Proj 𝒜, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
      (((Proj 𝒜).presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom).toAlgebra
    letI : Module Γ(Proj 𝒜, basicOpen 𝒜 f)
        Γ(N, (Proj 𝒜).basicOpen (ratioSection 𝒜 hf hg)) :=
      Module.compHom _ (((Proj 𝒜).presheaf.map
        (homOfLE ((Proj 𝒜).basicOpen_le (ratioSection 𝒜 hf hg))).op).hom)
    IsLocalizedModule (Submonoid.powers (ratioSection 𝒜 hf hg))
      (Scheme.Modules.resBasicOpenLinearMap N (ratioSection 𝒜 hf hg)) :=
  Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap_of_qcqs N
    (isAffineOpen_basicOpen 𝒜 f hf hd).isCompact
    (isAffineOpen_basicOpen 𝒜 f hf hd).isQuasiSeparated (ratioSection 𝒜 hf hg)

end AlgebraicGeometry.Proj
