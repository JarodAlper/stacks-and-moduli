module

public import StacksAndModuli.API.ProjectiveGradedAffineAcyclic
public import StacksAndModuli.API.ProjectiveGradedFreeAug

/-!
# `M_d ≅ H⁰(ℙⁿ, M~(d))` in large degrees

Supporting API with no Stacks Project counterpart.

For a finitely generated graded module the augmentation `cechAug : M_d ⟶ H⁰(M~(d))` is an
isomorphism once `d` is large.  Its kernel is the irrelevant torsion, which vanishes in
large degrees; surjectivity comes from the free presentation together with Serre vanishing
for the kernel of that presentation.

Main declarations:
- `GradedModule.cechAug_naturality`;
- `GradedModule.ker_cechAug₀_le_irrTorsSub`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k] {n : ℕ}

/-! ## The kernel of the augmentation is the irrelevant torsion -/

lemma ker_cechAug₀_le_irrTorsSub (M : GradedModule k n) (d : ℤ) (x : M.obj d)
    (hx : (M.cechAug₀ d).hom x = 0) : x ∈ M.irrTorsSub d := by
  intro i
  have hcomp : ((M.locOf [i]).app d).hom x = 0 :=
    congrFun hx (CechIdx.zeroIdx i)
  rw [locOf_app] at hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  obtain ⟨t, hle, ht⟩ := M.locIncl_eq_zero [i] d 0 _ hcomp
  have hEq : ∀ h : 0 ≤ t, M.locTr [i] d 0 t h
      = eqToHom (congrArg M.obj (show locDeg [i] d 0 = d by simp [locDeg_def]))
        ≫ M.mulPow i t d (d + (t : ℤ)) rfl
        ≫ eqToHom (congrArg M.obj (show d + (t : ℤ) = locDeg [i] d t by simp [locDeg_def])) := by
    intro h
    show M.mulList (listPow [i] (t - 0)) (locDeg [i] d 0) (locDeg [i] d t) _ = _
    rw [M.mulList_congr_list (show listPow [i] (t - 0) = listPow [i] t by rw [Nat.sub_zero])
      (locDeg [i] d 0) (locDeg [i] d t) _ (by simp [locDeg_def])]
    exact M.mulList_congr_degree (listPow [i] t) (by simp [locDeg_def])
      (by simp [locDeg_def]) _ (by simp)
  rw [hEq] at ht
  refine ⟨t, ?_⟩
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
  have hz : ((eqToHom (congrArg M.obj (show locDeg [i] d 0 = d by simp [locDeg_def]))).hom
      ((eqToHom (congrArg M.obj (show d = locDeg [i] d 0 by
        rw [locDeg_def]; push_cast; ring))).hom x)) = x := by
    rw [← ModuleCat.comp_apply, eqToHom_trans, eqToHom_refl, ModuleCat.id_apply]
  rw [hz] at ht
  have hinj : Function.Injective
      ((eqToHom (congrArg M.obj (show d + (t : ℤ) = locDeg [i] d t by simp [locDeg_def]))).hom) := by
    intro a b hab
    have hb := congrArg (fun w => (eqToHom (congrArg M.obj
      (show locDeg [i] d t = d + (t : ℤ) by simp [locDeg_def]))).hom w) hab
    simpa [← ModuleCat.comp_apply, eqToHom_trans] using hb
  refine hinj ?_
  rw [ht, map_zero]

/-! ## Injectivity of the augmentation in large degrees -/

/-- The augmentation is injective in every degree where the irrelevant torsion
vanishes. -/
theorem injective_cechAug_of_subsingleton_irrTors (M : GradedModule k n) {d : ℤ}
    (h : Subsingleton (M.irrTors.obj d)) :
    Function.Injective ((M.cechAug d).hom) := by
  refine injective_cechAug_of_aug₀ M d fun a b hab => ?_
  have h0 : (M.cechAug₀ d).hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem := ker_cechAug₀_le_irrTorsSub M d (a - b) h0
  haveI : Subsingleton (M.irrTorsSub d) := h
  have hz : (⟨a - b, hmem⟩ : M.irrTorsSub d) = 0 := Subsingleton.elim _ _
  have := congrArg Subtype.val hz
  simpa [sub_eq_zero] using this

/-- **The augmentation is injective in all large degrees** on a finitely generated
module. -/
theorem exists_injective_cechAug (M : GradedModule k n) (hM : IsFG M) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → Function.Injective ((M.cechAug d).hom) := by
  obtain ⟨d₁, hd₁⟩ := exists_subsingleton_irrTors M hM
  exact ⟨d₁, fun d hd => injective_cechAug_of_subsingleton_irrTors M (hd₁ d hd)⟩

/-! ## Surjectivity of the augmentation in large degrees -/

/-- **The augmentation is surjective in all large degrees** on a finitely generated
module.  The free presentation `0 → R → S(-d₀)^r → M' → 0` is surjective on `H⁰` once
`H¹(R)` vanishes, and the augmentation of a free module is surjective as soon as the twist
is nonnegative. -/
theorem exists_surjective_cechAug (M : GradedModule k n) (hM : IsFG M) :
    ∃ d₂ : ℤ, ∀ d : ℤ, d₂ ≤ d → Function.Surjective ((M.cechAug d).hom) := by
  classical
  obtain ⟨hfd, hlow, d₀, hgen⟩ := hM
  haveI : FiniteDimensional k (M.obj d₀) := hfd d₀
  set r := Module.finrank k (M.obj d₀) with hr
  set y : Fin r → M.obj d₀ := fun t => (Module.finBasis k (M.obj d₀)) t with hy
  have hyspan : Submodule.span k (Set.range y) = ⊤ :=
    (Module.finBasis k (M.obj d₀)).span_eq
  have hK : IsFG (ker (freeGenHom M d₀ y)) :=
    IsFG.of_injective (kerι (freeGenHom M d₀ y))
      (fun _ _ _ h => Subtype.val_injective h) (isFG_free (-d₀) r)
  obtain ⟨d₃, hd₃⟩ := exists_subsingleton_cechHgr_of_isFG _ hK 1 le_rfl
  refine ⟨max d₀ d₃, fun d hd => ?_⟩
  have hd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd3 : d₃ ≤ d := le_trans (le_max_right _ _) hd
  -- surjectivity for the image of the free presentation
  have himg : Function.Surjective (((imgMod M d₀ y).cechAug d).hom) := by
    intro z
    haveI := hd₃ d hd3
    obtain ⟨w, hw⟩ := (cech_exact_map_δ (shortExact_freeGenToImg M d₀ y) 0 d z).mp
      (Subsingleton.elim _ _)
    obtain ⟨u, hu⟩ := bijective_cechAug_free (-d₀) r d (by omega) |>.2 w
    refine ⟨((freeGenToImg M d₀ y).app d).hom u, ?_⟩
    have hnat := congrArg ModuleCat.Hom.hom
      (cechAug_naturality (freeGenToImg M d₀ y) d)
    simp only [ModuleCat.hom_comp] at hnat
    have := LinearMap.congr_fun hnat u
    simp only [LinearMap.comp_apply] at this
    rw [← this, hu, hw]
  -- transfer along the comparison with `M`
  intro z
  obtain ⟨z', hz'⟩ :=
    (bijective_cechHgrMap_imgIota M d₀ y hyspan hgen 0 d).2 z
  obtain ⟨v, hv⟩ := himg z'
  refine ⟨((imgIota M d₀ y).app d).hom v, ?_⟩
  have hnat := congrArg ModuleCat.Hom.hom (cechAug_naturality (imgIota M d₀ y) d)
  simp only [ModuleCat.hom_comp] at hnat
  have hval := LinearMap.congr_fun hnat v
  simp only [LinearMap.comp_apply] at hval
  rw [← hval, hv, hz']

/-- **`M_d ≅ H⁰(ℙⁿ, M~(d))` in large degrees.** -/
theorem exists_bijective_cechAug (M : GradedModule k n) (hM : IsFG M) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d → Function.Bijective ((M.cechAug d).hom) := by
  obtain ⟨d₁, hd₁⟩ := exists_injective_cechAug M hM
  obtain ⟨d₂, hd₂⟩ := exists_surjective_cechAug M hM
  exact ⟨max d₁ d₂, fun d hd =>
    ⟨hd₁ d (le_trans (le_max_left _ _) hd), hd₂ d (le_trans (le_max_right _ _) hd)⟩⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
