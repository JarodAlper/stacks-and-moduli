module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»

/-!
# Recognizing quasicoherence from section-level localization

Mathlib recognizes a quasicoherent sheaf through `IsIso M.fromTildeΓ`, or equivalently
through `IsLocalizing`.  Both are statements about the `Spec` model of an affine open, so
using them means transporting every section along `AffineOpen.fromSpec` by hand.

`Scheme.Modules.isQuasicoherent_of_sections_localization` packages that transport once and
for all, leaving a criterion phrased entirely in the ambient scheme: sections over an
affine open `U` localize onto each basic open `D(r)`, in the elementwise form

* a section over `U` restricting to `0` on `D(r)` is killed by a power of `r`, and
* a section over `D(r)` becomes the restriction of a section over `U` after multiplying by
  a power of `r`.

Those two conditions are exactly what `API/QuasicoherentSectionsQcqs.lean` *proves* for a
quasicoherent sheaf on a qcqs open, which is what makes the criterion the converse half of
a usable equivalence; `API/QcqsPushforwardQuasicoherent.lean` runs the pair in sequence to
push a quasicoherent sheaf forward along a qcqs morphism.

This lemma used to live in `Section2.4-Projectivity/part2.4.1-valuative-criteria.lean`,
where it recognized the saturated kernel of `prop:quot-proper` as quasicoherent.  It moved
here unchanged so that §2.4 can also consume the qcqs pushforward theorem built on top of
it, which would otherwise be circular.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_sections_localization`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- **Quasicoherence criterion by section-level localization.**  A sheaf of modules
whose sections over every affine open localize onto every basic open — in the concrete
form of the two conditions: a section vanishing on `D(r)` is killed by a power of `r`,
and a section over `D(r)` extends after multiplication by a power of `r` — is
quasicoherent.  This is the converse of
`exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero` and
`exists_pow_smul_res_of_basicOpen`, and is an API lemma used to recognize the saturated
kernel in Proposition 2.4.2 as quasicoherent. -/
theorem Modules.isQuasicoherent_of_sections_localization {P : Scheme.{u}} (M : P.Modules)
    (hex : ∀ (U : P.affineOpens) (r : Γ(P, U.1)) (z : Γ(M, U.1)),
      (M.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom z = 0 → ∃ n : ℕ, r ^ n • z = 0)
    (hsurj : ∀ (U : P.affineOpens) (r : Γ(P, U.1)) (z : Γ(M, P.basicOpen r)),
      ∃ (z₀ : Γ(M, U.1)) (n : ℕ),
        (M.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom z₀ =
          (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r ^ n • z) :
    M.IsQuasicoherent := by
  classical
  -- the canonical cover of `P` by the spectra of its affine opens
  let 𝒰 : P.OpenCover :=
    { I₀ := P.affineOpens
      X := fun U ↦ Spec Γ(P, U.1)
      f := fun U ↦ U.2.fromSpec
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, inferInstance⟩
        obtain ⟨V, hVaff, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
          P.isBasis_affineOpens) (show x ∈ (⊤ : P.Opens) from trivial)
        obtain ⟨y, hy⟩ := (Set.ext_iff.mp hVaff.range_fromSpec x).mpr hxV
        exact ⟨⟨V, hVaff⟩, ⟨y, hy⟩⟩ }
  haveI hqc : ∀ U : P.affineOpens,
      ((Modules.restrictFunctor U.2.fromSpec).obj M).IsQuasicoherent := by
    intro U
    set j : Spec Γ(P, U.1) ⟶ P := U.2.fromSpec with hj
    set Ms : (Spec Γ(P, U.1)).Modules := M.restrict j with hMs
    have him : j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens) = U.1 := by
      rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
    rw [AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ,
      AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing]
    intro r
    have himD : j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U.1)).Opens) =
        P.basicOpen r := U.2.fromSpec_image_basicOpen (f := r)
    have key : IsLocalizedModule (Submonoid.powers r)
        (Scheme.Modules.sectionsToBasicOpenLinearMap Ms r) := by
      -- the two transport squares between the ambient and the Spec model
      have hsq : ∀ y : Γ(M, U.1),
          Scheme.Modules.sectionsToBasicOpenLinearMap Ms r
              ((M.presheaf.map (eqToHom him).op).hom y) =
            (M.presheaf.map (eqToHom himD).op).hom
              ((M.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom y) := by
        intro y
        have hmor : M.presheaf.map (eqToHom him).op ≫
            Ms.presheaf.map (homOfLE (le_top : (PrimeSpectrum.basicOpen r :
              (Spec Γ(P, U.1)).Opens) ≤ ⊤)).op =
            M.presheaf.map (homOfLE (P.basicOpen_le r)).op ≫
              M.presheaf.map (eqToHom himD).op := by
          rw [Scheme.Modules.restrict_map, ← Functor.map_comp, ← Functor.map_comp]
          congr 1
        exact CategoryTheory.congr_fun hmor y
      -- the scalar comparison over the basic open
      have hscal : (P.presheaf.map (eqToHom himD).op).hom
          ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r) =
          (j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
            (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) r) := by
        have hpre : (PrimeSpectrum.basicOpen r : (Spec Γ(P, U.1)).Opens) ≤ j ⁻¹ᵁ U.1 := by
          rw [hj, U.2.fromSpec_preimage_self]
          exact le_top
        have happ : (j.appLE U.1 (PrimeSpectrum.basicOpen r) hpre).hom =
            algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) :=
          U.2.fromSpec_appLE_eq_algebraMap (PrimeSpectrum.basicOpen r)
        have hsplit : P.presheaf.map (homOfLE (P.basicOpen_le r)).op ≫
            P.presheaf.map (eqToHom himD).op ≫
            j.appLE (j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U.1)).Opens))
              (PrimeSpectrum.basicOpen r) (j.preimage_image_eq _).ge =
              j.appLE U.1 (PrimeSpectrum.basicOpen r) hpre := by
          rw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
        have happiso : (j.appIso (PrimeSpectrum.basicOpen r)).hom =
            (j.appLE (j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U.1)).Opens))
              (PrimeSpectrum.basicOpen r) (j.preimage_image_eq _).ge) :=
          Scheme.Hom.appIso_hom' j _
        apply (ConcreteCategory.bijective_of_isIso
          (j.appIso (PrimeSpectrum.basicOpen r)).hom).injective
        have h1 : (j.appIso (PrimeSpectrum.basicOpen r)).hom.hom
            ((P.presheaf.map (eqToHom himD).op).hom
              ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r)) =
            algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) r := by
          have hc := CategoryTheory.congr_fun hsplit r
          rw [← happ]
          refine Eq.trans ?_ hc
          rw [happiso]
          rfl
        have h2 : (j.appIso (PrimeSpectrum.basicOpen r)).hom.hom
            ((j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
              (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) r)) =
            algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) r := by
          change ((j.appIso (PrimeSpectrum.basicOpen r)).inv ≫
            (j.appIso (PrimeSpectrum.basicOpen r)).hom).hom _ = _
          rw [Iso.inv_hom_id]
          rfl
        exact h1.trans h2.symm
      -- the action of powers of `r` on the Spec-model sections over the basic open
      have hact : ∀ (k : ℕ) (y : Γ(Ms, PrimeSpectrum.basicOpen r)),
          (r ^ k : Γ(P, U.1)) • y =
            ((P.presheaf.map (eqToHom himD).op).hom
              ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r)) ^ k •
            (show ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen r :
              (Spec Γ(P, U.1)).Opens)) from y) := by
        intro k y
        rw [← algebraMap_smul Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) (r ^ k) y]
        have hpow : ((P.presheaf.map (eqToHom himD).op).hom
            ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r)) ^ k =
            (j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
              (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)
                (r ^ k)) := by
          rw [hscal, ← map_pow, ← map_pow]
        rw [hpow]
        exact Scheme.Modules.smul_restrictAppIso_hom_apply j M
          (PrimeSpectrum.basicOpen r)
          (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) (r ^ k)) y
      refine ⟨?_, ?_, ?_⟩
      · -- powers of `r` act invertibly on the sections over the basic open
        rintro ⟨x, k, rfl⟩
        rw [Module.End.isUnit_iff]
        have hunit : IsUnit (algebraMap Γ(P, U.1)
            Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r) (r ^ k)) := by
          rw [map_pow]
          exact (IsLocalization.map_units (M := Submonoid.powers r)
            Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)
            ⟨r, Submonoid.mem_powers r⟩).pow k
        obtain ⟨u, hu⟩ := hunit
        have huy : ∀ y : Γ(Ms, PrimeSpectrum.basicOpen r),
            (algebraMap Γ(P, U.1) (Module.End Γ(P, U.1)
              Γ(Ms, PrimeSpectrum.basicOpen r)) (r ^ k)) y =
            (u : Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)) • y := by
          intro y
          change (r ^ k : Γ(P, U.1)) • y = _
          rw [hu]
          exact (algebraMap_smul Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)
            (r ^ k) y).symm
        constructor
        · intro y₁ y₂ h12
          rw [huy y₁, huy y₂] at h12
          have h3 := congrArg (fun w ↦
            ((u⁻¹ : (Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r))ˣ) :
              Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)) • w) h12
          beta_reduce at h3
          rwa [smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at h3
        · intro y
          refine ⟨((u⁻¹ : (Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r))ˣ) :
            Γ(Spec Γ(P, U.1), PrimeSpectrum.basicOpen r)) • y, ?_⟩
          rw [huy, smul_smul, Units.mul_inv, one_smul]
      · -- surjectivity up to powers of `r`
        intro y
        obtain ⟨z₀, n, hz₀⟩ := hsurj U r ((M.presheaf.map (eqToHom himD.symm).op).hom y)
        refine ⟨⟨(M.presheaf.map (eqToHom him).op).hom z₀, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
        change (r ^ n : Γ(P, U.1)) • y =
          Scheme.Modules.sectionsToBasicOpenLinearMap Ms r
            ((M.presheaf.map (eqToHom him).op).hom z₀)
        rw [hsq z₀, hz₀, Scheme.Modules.map_smul M (eqToHom himD)]
        have hcollapse : (M.presheaf.map (eqToHom himD).op).hom
            ((M.presheaf.map (eqToHom himD.symm).op).hom y) = y := by
          rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
            eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
          rfl
        rw [hcollapse, map_pow]
        exact hact n y
      · -- separation up to powers of `r`
        intro x₁ x₂ h12
        have hρU : (M.presheaf.map (eqToHom him).op).hom
            ((M.presheaf.map (eqToHom him.symm).op).hom (x₁ - x₂)) = x₁ - x₂ := by
          rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
            eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
          rfl
        have hres0 : (M.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom
            ((M.presheaf.map (eqToHom him.symm).op).hom (x₁ - x₂)) = 0 := by
          apply (ConcreteCategory.bijective_of_isIso
            (M.presheaf.map (eqToHom himD).op)).injective
          rw [map_zero]
          have hkey := hsq ((M.presheaf.map (eqToHom him.symm).op).hom (x₁ - x₂))
          rw [hρU] at hkey
          rw [← hkey, map_sub, h12, sub_self]
        obtain ⟨n, hn⟩ := hex U r _ hres0
        refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
        -- the scalar comparison over the top open
        have hscalTop : (P.presheaf.map (eqToHom him).op).hom (r ^ n) =
            (j.appIso ⊤).inv.hom
              (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) (r ^ n)) := by
          have hpre : (⊤ : (Spec Γ(P, U.1)).Opens) ≤ j ⁻¹ᵁ U.1 := by
            rw [hj, U.2.fromSpec_preimage_self]
          have happ : (j.appLE U.1 ⊤ hpre).hom =
              algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) :=
            U.2.fromSpec_appLE_eq_algebraMap ⊤
          have hsplit : P.presheaf.map (eqToHom him).op ≫
              j.appLE (j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) ⊤ (j.preimage_image_eq ⊤).ge =
                j.appLE U.1 ⊤ hpre := by
            rw [Scheme.Hom.map_appLE]
          have happiso : (j.appIso ⊤).hom =
              (j.appLE (j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) ⊤
                (j.preimage_image_eq ⊤).ge) :=
            Scheme.Hom.appIso_hom' j ⊤
          apply (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).hom).injective
          have h1 : (j.appIso ⊤).hom.hom
              ((P.presheaf.map (eqToHom him).op).hom (r ^ n)) =
              algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) (r ^ n) := by
            have hc := CategoryTheory.congr_fun hsplit (r ^ n)
            rw [← happ]
            refine Eq.trans ?_ hc
            rw [happiso]
            rfl
          have h2 : (j.appIso ⊤).hom.hom ((j.appIso ⊤).inv.hom
              (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) (r ^ n))) =
              algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) (r ^ n) := by
            change ((j.appIso ⊤).inv ≫ (j.appIso ⊤).hom).hom _ = _
            rw [Iso.inv_hom_id]
            rfl
          exact h1.trans h2.symm
        have hzero : (r ^ n : Γ(P, U.1)) • (x₁ - x₂) = 0 := by
          have h1 : (r ^ n : Γ(P, U.1)) • (x₁ - x₂) =
              (P.presheaf.map (eqToHom him).op).hom (r ^ n) •
              (show ToType Γ(M, j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) from x₁ - x₂) := by
            rw [← algebraMap_smul Γ(Spec Γ(P, U.1), ⊤) (r ^ n) (x₁ - x₂), hscalTop]
            exact (Scheme.Modules.smul_restrictAppIso_hom_apply j M ⊤
              (algebraMap Γ(P, U.1) Γ(Spec Γ(P, U.1), ⊤) (r ^ n)) (x₁ - x₂)).symm
          rw [h1, ← hρU, ← Scheme.Modules.map_smul M (eqToHom him), hn, map_zero]
        have hsub : (⟨r ^ n, n, rfl⟩ : Submonoid.powers r) • x₁ -
            (⟨r ^ n, n, rfl⟩ : Submonoid.powers r) • x₂ = 0 := by
          rw [Submonoid.smul_def, Submonoid.smul_def, ← smul_sub]
          exact hzero
        exact sub_eq_zero.mp hsub
    change IsLocalizedModule (Submonoid.powers r)
      (Scheme.Modules.sectionsToBasicOpenLinearMap Ms r)
    exact key
  haveI : ∀ i, ((Modules.restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent := fun U ↦ hqc U
  exact Modules.isQuasicoherent_of_openCover_restrict M 𝒰

end AlgebraicGeometry.Scheme
