module

public import StacksAndModuli.API.ProjectiveGradedFinitePi
public import StacksAndModuli.API.ProjectiveGradedFlatFinitePresentation

/-!
# The standard-graded local finite-presentation theorem

This file completes the standard-graded specialization of Stacks Project tag 053C used by
the projective-space Cech arguments.  Over a local coefficient ring, a finitely generated
diagrammatic graded module which is flat in every degree has finitely presented total module
over the standard polynomial ring.

The proof replaces a single eventual free presentation by a finite product of shifted-free
presentations, one for each degree between a lower vanishing bound and an eventual generation
bound.  The resulting graded map is surjective in every degree, so the graded relation criterion
applies directly.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The standard free-generator map is already surjective in the degree containing its chosen
generators; no eventual-generation hypothesis is needed in that degree. -/
lemma surjective_freeGenHom_app_self {M : GradedModule R n} (d₀ : ℤ) {r : ℕ}
    (y : Fin r → M.obj d₀) (hy : Submodule.span R (Set.range y) = ⊤) :
    Function.Surjective (((freeGenHom M d₀ y).app d₀).hom) := by
  classical
  intro z
  obtain ⟨c, hc⟩ : ∃ c : Fin r → R, ∑ t, c t • y t = z :=
    (Submodule.mem_span_range_iff_exists_fun R).mp (by rw [hy]; trivial)
  have hmem (t : Fin r) :
      (MvPolynomial.monomial 0 (c t) : MvPolynomial (Fin (n + 1)) R) ∈
        polySubmodule R n (d₀ + -d₀) := by
    rw [polySubmodule_of_nonneg R n (by omega), MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial _ (by simp)
  let p : (((structureModule R n).twist (-d₀)).pow r).obj d₀ :=
    fun t => ⟨MvPolynomial.monomial 0 (c t), hmem t⟩
  refine ⟨p, ?_⟩
  rw [freeGenHom_app_apply]
  have hterm (t : Fin r) :
      mulFormZ M (d₀ + -d₀) d₀ d₀ (by ring) (p t) (y t) = c t • y t := by
    rw [show p t =
      ⟨MvPolynomial.monomial 0 (c t), hmem t⟩ from rfl,
      mulFormZ_monomial M (d₀ + -d₀) d₀ d₀ (by ring)
        0 (by simp) (c t) (hmem t) (y t),
      mulMono_zero]
    rfl
  rw [Finset.sum_congr rfl (fun t _ => hterm t), hc]

namespace Total

/-- The standard-graded specialization of the local graded finite-presentation theorem:
a finitely generated, degreewise-flat graded module over a local ring has finitely presented
total module over the standard polynomial ring. -/
theorem finitePresentation_of_isFG_of_isFlat_of_isLocalRing [IsLocalRing R]
    (M : GradedModule R n) (hM : IsFG M) (hflat : IsFlat M) :
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total M) := by
  classical
  obtain ⟨lo, hlow⟩ := hM.2.1
  obtain ⟨hi, hgen⟩ := hM.2.2
  letI finite_obj (d : ℤ) : Module.Finite R (M.obj d) := hM.1 d
  let lo' : ℤ := min lo hi
  let I := ULift.{u} (↑(Finset.Icc lo' hi))
  let r : I → ℕ := fun i => Classical.choose
    (Module.Finite.exists_fin (R := R) (M := (M.obj i.down.1 : Type u)))
  let y : ∀ i : I, Fin (r i) → M.obj i.down.1 := fun i => Classical.choose
    (Classical.choose_spec
      (Module.Finite.exists_fin (R := R) (M := (M.obj i.down.1 : Type u))))
  have hy : ∀ i : I, Submodule.span R (Set.range (y i)) = ⊤ := fun i =>
    Classical.choose_spec (Classical.choose_spec
      (Module.Finite.exists_fin (R := R) (M := (M.obj i.down.1 : Type u))))
  let F : I → GradedModule R n := fun i =>
    ((structureModule R n).twist (-i.down.1)).pow (r i)
  let g : ∀ i : I, F i ⟶ M := fun i => freeGenHom M i.down.1 (y i)
  let f : pi F ⟶ M := piDesc F g
  have hFfp (i : I) : Module.FinitePresentation
      (MvPolynomial (Fin (n + 1)) R) (Total (F i)) := by
    dsimp only [F]
    exact finitePresentation_shiftedFree R n (r i) i.down.1
  letI : Module.FinitePresentation
      (MvPolynomial (Fin (n + 1)) R) (Total (pi F)) :=
    finitePresentation_pi F hFfp
  have hFfg : IsFG (pi F) := IsFG.pi F fun i =>
    ((isFG_structureModule (k := R) (n := n)).twist (-i.down.1)).pow (r i)
  have hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom) := by
    intro d z
    rcases lt_or_ge d lo' with hdlo | hdlo
    · haveI : Subsingleton (M.obj d) :=
        hlow d (lt_of_lt_of_le hdlo (min_le_left lo hi))
      refine ⟨0, ?_⟩
      simpa using (Subsingleton.elim (0 : M.obj d) z)
    · rcases le_or_gt d hi with hdhi | hdhi
      · let i : I := ⟨⟨d, Finset.mem_Icc.mpr ⟨hdlo, hdhi⟩⟩⟩
        obtain ⟨q, hq⟩ := surjective_freeGenHom_app_self
          (M := M) d (y i) (hy i) z
        refine ⟨((piIncl F i).app d).hom q, ?_⟩
        dsimp only [f]
        rw [piDesc_piIncl_app]
        exact hq
      · let i : I :=
          ⟨⟨hi, Finset.mem_Icc.mpr ⟨min_le_right lo hi, le_rfl⟩⟩⟩
        obtain ⟨q, hq⟩ := surjective_freeGenHom_app M hi
          (y i) (hy i) hgen d (le_of_lt hdhi) z
        refine ⟨((piIncl F i).app d).hom q, ?_⟩
        dsimp only [f]
        rw [piDesc_piIncl_app]
        exact hq
  exact finitePresentation_of_surjective_of_isFG_of_isFlat
    hFfg hM hflat f hf

end Total

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
