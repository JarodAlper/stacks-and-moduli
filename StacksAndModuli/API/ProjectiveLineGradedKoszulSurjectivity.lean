module

public import StacksAndModuli.API.ProjectiveLineGradedCechHgrKoszul
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient

/-!
# Surjectivity in the projective-line Koszul recurrence

The projective-line Koszul recurrence on Cech complexes is short exact.  Its long exact
cohomology sequence therefore shows that the last map on `H^0` is surjective whenever the
preceding `H^1` group vanishes.  This file also records that graded Cech cohomology
vanishing descends to retracts, both abstractly and for `Proj.gammaStar`.

These are the formal bridges used to obtain the right-exact recurrence for a relation
sheaf which is a summand of a finite twisted-free sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R]

/-- Cech cohomology vanishing descends from a graded module to any of its retracts. -/
theorem subsingleton_cechHgr_of_retract {n q : ℕ} {M N : GradedModule R n}
    (i : M ⟶ N) (p : N ⟶ M) (h : i ≫ p = 𝟙 M) (d : ℤ)
    [Subsingleton ((N.cechHgr q).obj d)] :
    Subsingleton ((M.cechHgr q).obj d) := by
  have hip : cechHgrMap i q ≫ cechHgrMap p q = 𝟙 (M.cechHgr q) := by
    rw [← cechHgrMap_comp, h, cechHgrMap_id]
  have hipd : (cechHgrMap i q).app d ≫ (cechHgrMap p q).app d = 𝟙 _ := by
    simpa only [comp_app, id_app] using congrArg (fun f ↦ f.app d) hip
  letI : IsSplitMono ((cechHgrMap i q).app d) :=
    IsSplitMono.mk' { retraction := (cechHgrMap p q).app d, id := hipd }
  exact (ModuleCat.mono_iff_injective ((cechHgrMap i q).app d)).mp inferInstance |>.subsingleton

/-- Vanishing of the degree-`d` first Cech cohomology makes the final map in the
projective-line Koszul recurrence on zeroth Cech cohomology surjective. -/
theorem lineKoszulG_cechHgr_zero_surjective_of_subsingleton_one
    (M : GradedModule R 1) (d : ℤ)
    [Subsingleton ((M.cechHgr 1).obj d)] :
    Function.Surjective (lineKoszulG (M.cechHgr 0) d) := by
  let e := cechHgrPowIso M 2 0 (d + 1)
  let g := HomologicalComplex.homologyMap (lineCechKoszulG M d) 0
  have hg : e.inv ≫ g = ModuleCat.ofHom (lineKoszulG (M.cechHgr 0) d) :=
    cechHgrPowIso_inv_comp_homologyMap_lineCechKoszulG M 0 d
  have hsurj : Function.Surjective g.hom := by
    have hex : Function.Exact g.hom
        ((lineCechKoszulShortComplex_shortExact M d).δ 0 1 rfl).hom := by
      have h := (lineCechKoszulShortComplex_shortExact M d).homology_exact₃ 0 1 rfl
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
      exact h
    letI : Subsingleton
        ((lineCechKoszulShortComplex M d).X₁.homology 1) := by
      change Subsingleton ((M.cechHgr 1).obj d)
      infer_instance
    intro z
    exact (hex z).mp (Subsingleton.elim _ _)
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨e.hom.hom y, ?_⟩
  have happ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hg) (e.hom.hom y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at happ
  rw [e.hom_inv_id_apply] at happ
  exact happ.symm.trans hy

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝓐 : ℕ → σ) [GradedRing 𝓐]
variable {n : ℕ} {R : CommRingCat.{u}}
variable (f : Proj 𝓐 ⟶ Spec R) (x : Fin (n + 1) → 𝓐 1)

/-- Cech cohomology of `Proj.gammaStar` vanishes on a sheaf retract whenever it vanishes
on the containing sheaf. -/
theorem subsingleton_cechHgr_gammaStar_of_retract
    {F G : (Proj 𝓐).Modules} (i : F ⟶ G) (p : G ⟶ F)
    (h : i ≫ p = 𝟙 F) (q : ℕ) (d : ℤ)
    [Subsingleton (((gammaStar 𝓐 f G x).cechHgr q).obj d)] :
    Subsingleton (((gammaStar 𝓐 f F x).cechHgr q).obj d) := by
  apply ProjectiveSpace.GradedModule.subsingleton_cechHgr_of_retract
    (gammaStarMap 𝓐 f i x) (gammaStarMap 𝓐 f p x)
  rw [← gammaStarMap_comp, h, gammaStarMap_id]

end AlgebraicGeometry.Proj

end

end
