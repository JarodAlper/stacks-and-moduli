module

public import StacksAndModuli.API.ProjGammaStarChart

/-!
# Multiplicativity of the Čech augmentation

The canonical augmentation from a graded module to the zeroth cohomology of its
standard Čech complex commutes with multiplication by variables and hence by
arbitrary monomials.  Consequently, a multiplication-span statement in Čech
`H⁰` transfers back across degreewise bijective augmentations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k : Type u} [CommRing k] {n : ℕ} (M : GradedModule k n)

/-- Multiplication spans reflect across a graded morphism that is bijective in
the two degrees involved.  Unlike `mulSpan_eq_top_iff_of_bijective`, this only
requires the degreewise comparisons actually used. -/
theorem mulSpan_eq_top_of_bijective_at {M N : GradedModule k n}
    (f : M ⟶ N) (d e : ℤ)
    (hd : Function.Bijective (f.app d).hom)
    (he : Function.Bijective (f.app e).hom)
    (hspan : N.mulSpan d e = ⊤) :
    M.mulSpan d e = ⊤ := by
  let fd : M.obj d ≃ₗ[k] N.obj d := LinearEquiv.ofBijective (f.app d).hom hd
  let fe : M.obj e ≃ₗ[k] N.obj e := LinearEquiv.ofBijective (f.app e).hom he
  apply top_unique
  intro y _
  have hy : fe y ∈ N.mulSpan d e := hspan.symm ▸ Submodule.mem_top
  have hmain : fe.symm (fe y) ∈ M.mulSpan d e := by
    refine Submodule.iSup_induction
      (fun l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e} ↦
        LinearMap.range ((N.mulList l.1 d e l.2).hom))
      (motive := fun z ↦ fe.symm z ∈ M.mulSpan d e)
      hy ?_ ?_ ?_
    · rintro ⟨l, hl⟩ _ ⟨z, rfl⟩
      let w := fd.symm z
      have hcompat := congrArg (fun g : M.obj d ⟶ N.obj e ↦ g.hom w)
        (comm_mulList f l d e hl)
      have hfd : (f.app d).hom w = z := fd.apply_symm_apply z
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, hfd] at hcompat
      have hpre : fe.symm ((N.mulList l d e hl).hom z) =
          (M.mulList l d e hl).hom w := by
        apply fe.injective
        rw [fe.apply_symm_apply]
        change (N.mulList l d e hl).hom z =
          (f.app e).hom ((M.mulList l d e hl).hom w)
        exact hcompat
      rw [hpre]
      exact le_mulSpan M d e l hl (LinearMap.mem_range_self _ w)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add]
      exact Submodule.add_mem _ hz₁ hz₂
  rwa [LinearEquiv.symm_apply_apply] at hmain

/-- The degree-zero Čech augmentation commutes with multiplication by a variable. -/
lemma cechAug₀_comp_cechMulX' (i : Fin (n + 1)) (d e : ℤ)
    (h : d + 1 = e) :
    M.cechAug₀ d ≫ (M.cechMulX' i d e h).f 0 =
      M.mulX' i d e h ≫ M.cechAug₀ e := by
  subst e
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ funext fun τ ↦ ?_)
  have hc := congrArg ModuleCat.Hom.hom ((M.locOf τ.toList).comm i d)
  exact LinearMap.congr_fun hc s

/-- The augmentation into Čech `H⁰` commutes with multiplication by a variable. -/
lemma cechAug_comp_mulX' (i : Fin (n + 1)) (d e : ℤ)
    (h : d + 1 = e) :
    M.cechAug d ≫ (M.cechHgr 0).mulX' i d e h =
      M.mulX' i d e h ≫ M.cechAug e := by
  rw [← homologyMap_cechMulX' M i d e h 0]
  show (M.cechComplex d).liftCycles (M.cechAug₀ d) 1 (by simp)
        (by rw [M.cechComplex_d_zero_one d]; exact M.cechAug₀_comp_cechD d) ≫
      (M.cechComplex d).homologyπ 0 ≫
      HomologicalComplex.homologyMap (M.cechMulX' i d e h) 0
    = M.mulX' i d e h ≫
      (M.cechComplex e).liftCycles (M.cechAug₀ e) 1 (by simp)
        (by rw [M.cechComplex_d_zero_one e]; exact M.cechAug₀_comp_cechD e) ≫
      (M.cechComplex e).homologyπ 0
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap, ← Category.assoc]
  congr 1
  refine (cancel_mono ((M.cechComplex e).iCycles 0)).mp ?_
  rw [HomologicalComplex.liftCycles_i, Category.assoc,
    HomologicalComplex.liftCycles_i]
  exact cechAug₀_comp_cechMulX' M i d e h

/-- The augmentation into Čech `H⁰` commutes with an iterated monomial
multiplication. -/
lemma cechAug_comp_mulList :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ)
      (h : d + (l.length : ℤ) = e),
      M.cechAug d ≫ (M.cechHgr 0).mulList l d e h =
        M.mulList l d e h ≫ M.cechAug e
  | [], d, e, h => by
      have hde : d = e := by simpa using h
      subst e
      simp [mulList]
  | i :: l, d, e, h => by
      have hl : d + 1 + (l.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega
      have hx := cechAug_comp_mulX' M i d (d + 1) rfl
      simp only [mulX', eqToHom_refl, Category.comp_id] at hx
      simp only [mulList, Category.assoc]
      rw [← Category.assoc, hx, Category.assoc,
        cechAug_comp_mulList l (d + 1) e hl]

/-- Generation in Čech `H⁰` transfers back to the original graded module whenever
the augmentations in the source and target degrees are bijective. -/
theorem mulSpan_eq_top_of_cechHgrZero_of_bijective_cechAug
    (d e : ℤ) (hd : Function.Bijective ((M.cechAug d).hom))
    (he : Function.Bijective ((M.cechAug e).hom))
    (hspan : (M.cechHgr 0).mulSpan d e = ⊤) :
    M.mulSpan d e = ⊤ := by
  let Ad : M.obj d ≃ₗ[k] (M.cechHgr 0).obj d :=
    LinearEquiv.ofBijective (M.cechAug d).hom hd
  let Ae : M.obj e ≃ₗ[k] (M.cechHgr 0).obj e :=
    LinearEquiv.ofBijective (M.cechAug e).hom he
  apply top_unique
  intro y _
  have hy : Ae y ∈ (M.cechHgr 0).mulSpan d e :=
    hspan.symm ▸ Submodule.mem_top
  have hmain : Ae.symm (Ae y) ∈ M.mulSpan d e := by
    refine Submodule.iSup_induction
      (fun l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e} ↦
        LinearMap.range (((M.cechHgr 0).mulList l.1 d e l.2).hom))
      (motive := fun z ↦ Ae.symm z ∈ M.mulSpan d e)
      hy ?_ ?_ ?_
    · rintro ⟨l, hl⟩ _ ⟨z, rfl⟩
      let w := Ad.symm z
      have hcompat := congrArg
        (fun f : M.obj d ⟶ (M.cechHgr 0).obj e ↦ f.hom w)
        (cechAug_comp_mulList M l d e hl)
      have hAd : (M.cechAug d).hom w = z := by
        exact Ad.apply_symm_apply z
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, hAd] at hcompat
      have hpre : Ae.symm
          (((M.cechHgr 0).mulList l d e hl).hom z) =
          (M.mulList l d e hl).hom w := by
        apply Ae.injective
        rw [Ae.apply_symm_apply]
        change ((M.cechHgr 0).mulList l d e hl).hom z =
          (M.cechAug e).hom ((M.mulList l d e hl).hom w)
        exact hcompat
      rw [hpre]
      exact le_mulSpan M d e l hl (LinearMap.mem_range_self _ w)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add]
      exact Submodule.add_mem _ hz₁ hz₂
  rwa [LinearEquiv.symm_apply_apply] at hmain

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
