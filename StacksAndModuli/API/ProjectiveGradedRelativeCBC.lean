module

public import StacksAndModuli.API.ProjectiveGradedFlatComplex
public import StacksAndModuli.API.ProjectiveGradedSerre

/-!
# Cohomology and Base Change for the graded Čech complex

Supporting API with no Stacks Project counterpart: **Theorem A.6.4** (`thm:cbc`) in the
graded-module model, for a coherent family flat over a noetherian base.

The Čech complex of a coherent flat family `M` on `ℙⁿ_R` is a complex of flat `R`-modules
(`GradedModule.IsFlat.flat_cechCochain`) concentrated in degrees `0 … n`, whose base change
along **any** ring map computes the Čech complex of the base-changed family
(`GradedModule.cechComplexBaseChangeIso`), and whose cohomology is finite over `R` (Serre
finiteness). Those are exactly the hypotheses of `API/ProjectiveGradedFlatComplex.lean`.

Main declarations:
- `GradedModule.subsingleton_cechHgr_of_fibrewise`: fibrewise vanishing implies vanishing over
  the base;
- `GradedModule.projective_cechHgr_zero`: `π_* M(d)` is a vector bundle;
- `GradedModule.cechHgrZeroBaseChangeEquiv`: its formation commutes with base change.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct CochainComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
  (M : GradedModule R n) (d : ℤ)

/-- The Čech complex of a flat family consists of flat `R`-modules. -/
lemma flat_cechComplex_X (hflat : IsFlat M) (p : ℕ) :
    Module.Flat R ((M.cechComplex d).X p) :=
  hflat.flat_cechCochain p d

/-- The Čech complex is concentrated in degrees `0 … n`. -/
lemma subsingleton_cechComplex_X {p : ℕ} (hp : n < p) :
    Subsingleton ((M.cechComplex d).X p) := by
  have h := isZero_cechCochain M hp d
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h

/-- The homology of the Čech complex of a base-changed family agrees with the homology of the
base-changed Čech complex. -/
noncomputable def cechHgrBaseChangeHomologyIso (A : Type u) [CommRing A] [Algebra R A]
    (q : ℕ) :
    ((M.baseChange A).cechComplex d).homology q
      ≅ (cochainBaseChange A (M.cechComplex d)).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℕ) q).mapIso
    (cechComplexBaseChangeIso A M d)

/-- Exactness of all positive-degree terms of a flat Čech complex survives arbitrary
base change.  This fixed-degree form is useful when a uniform vanishing bound comes from
geometry rather than from finite generation. -/
theorem subsingleton_cechHgr_baseChange_of_flatCochain
    (A : Type u) [CommRing A] [Algebra R A]
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hvan : ∀ i : ℕ, 1 ≤ i → Subsingleton ((M.cechHgr i).obj d))
    (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (((M.baseChange A).cechHgr i).obj d) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  have hex : ∀ j' : ℕ, ExactAtSucc (M.cechComplex d) j' := by
    intro j'
    rw [← subsingleton_homology_succ_iff]
    exact hvan (j' + 1) (by omega)
  have hbc : ExactAtSucc (cochainBaseChange A (M.cechComplex d)) j := by
    rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom, cochainBaseChange_d_hom]
    exact range_baseChange_d_eq_ker A hflat
      (N := n) (fun p hp ↦ subsingleton_cechComplex_X M d hp)
      (t := 0) (fun j' _ ↦ hex j') (Nat.zero_le j)
  rw [← subsingleton_homology_succ_iff] at hbc
  exact (cechHgrBaseChangeHomologyIso M d A (j + 1)).toLinearEquiv.toEquiv.subsingleton

/-- Fibrewise vanishing, translated into exactness of the base-changed Čech complex. -/
lemma exactAtSucc_cochainBaseChange_of_subsingleton
    (A : Type u) [CommRing A] [Algebra R A] (j : ℕ)
    (h : Subsingleton (((M.baseChange A).cechHgr (j + 1)).obj d)) :
    ExactAtSucc (cochainBaseChange A (M.cechComplex d)) j := by
  rw [← subsingleton_homology_succ_iff]
  haveI : Subsingleton (((M.baseChange A).cechComplex d).homology (j + 1)) := h
  exact (cechHgrBaseChangeHomologyIso M d A (j + 1)).toLinearEquiv.toEquiv.symm.subsingleton

/-- **Cohomology and Base Change, vanishing half**, with the flatness hypothesis weakened to
what the proof uses: flatness of the Čech cochain groups in the one degree `d`.

`IsFlat M` enters the whole Cohomology-and-Base-Change package *only* through
`flat_cechComplex_X`, and `(M.cechComplex d).X p` is a finite product of the localizations
`M[1/x_I]_d`.  Those can be flat for reasons that have nothing to do with flatness of the
graded pieces — on `Proj` they are sections on an affine chart, so they are flat as soon as the
sheaf is flat over the base.  Keeping the hypothesis in this form is what lets the package
apply to a graded module that is *not* degreewise flat. -/
theorem exactAtSucc_cechComplex_of_fibrewise' (hM : IsFG M)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d)) :
    ∀ j : ℕ, ExactAtSucc (M.cechComplex d) j := by
  refine exactAtSucc_of_fibrewise (M.cechComplex d) hflatC
    (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) (fun j => ?_) (fun κ _ _ j => ?_)
  · haveI : Module.Finite R ((M.cechComplex d).homology (j + 1)) :=
      finiteDimensional_cechHgr_of_isFG M hM (j + 1) d
    exact finite_cohomologySucc (M.cechComplex d) j
  · exact exactAtSucc_cochainBaseChange_of_subsingleton M d κ j (hfib κ (j + 1) (by omega))

/-- **Cohomology and Base Change, vanishing half.** For a coherent family flat over a
noetherian base, vanishing of the higher cohomology on every field fibre forces vanishing over
the base. -/
theorem exactAtSucc_cechComplex_of_fibrewise (hM : IsFG M) (hflat : IsFlat M)
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d)) :
    ∀ j : ℕ, ExactAtSucc (M.cechComplex d) j := by
  refine exactAtSucc_of_fibrewise (M.cechComplex d) (flat_cechComplex_X M d hflat)
    (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) (fun j => ?_) (fun κ _ _ j => ?_)
  · haveI : Module.Finite R ((M.cechComplex d).homology (j + 1)) :=
      finiteDimensional_cechHgr_of_isFG M hM (j + 1) d
    exact finite_cohomologySucc (M.cechComplex d) j
  · exact exactAtSucc_cochainBaseChange_of_subsingleton M d κ j (hfib κ (j + 1) (by omega))

/-- **Cohomology and Base Change, vanishing half**, in the form the interface uses. -/
theorem subsingleton_cechHgr_of_fibrewise (hM : IsFG M) (hflat : IsFlat M)
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (i : ℕ) (hi : 1 ≤ i) : Subsingleton ((M.cechHgr i).obj d) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  rw [show ((M.cechHgr (j + 1)).obj d) = ((M.cechComplex d).homology (j + 1)) from rfl,
    subsingleton_homology_succ_iff]
  exact exactAtSucc_cechComplex_of_fibrewise M d hM hflat hfib j

/-! ## The pushforward is a vector bundle, and its formation commutes with base change -/

variable {M d}

/-- **Cohomology and Base Change, finiteness half**, with cochain flatness in place of
degreewise flatness. -/
theorem projective_cechHgr_zero' (hM : IsFG M)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d)) :
    Module.Projective R ((M.cechHgr 0).obj d) := by
  have hex := exactAtSucc_cechComplex_of_fibrewise' (M := M) (d := d) hM hflatC hfib
  haveI : Module.Finite R ((M.cechComplex d).homology 0) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 d
  haveI : Module.Finite R (cocyclesSub (M.cechComplex d) 0) :=
    finite_cocyclesSub_zero (M.cechComplex d)
  haveI := projective_cocyclesSub (M.cechComplex d) hflatC
    (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) hex 0
  exact Module.Projective.of_equiv (homologyZeroEquiv (M.cechComplex d)).symm

/-- **Cohomology and Base Change, comparison half**, with cochain flatness in place of
degreewise flatness. -/
noncomputable def cechHgrZeroBaseChangeEquiv' (hM : IsFG M)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (A : Type u) [CommRing A] [Algebra R A] :
    (A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A] (((M.baseChange A).cechHgr 0).obj d) :=
  have hex := exactAtSucc_cechComplex_of_fibrewise' (M := M) (d := d) hM hflatC hfib
  (LinearEquiv.baseChange R A _ _ (homologyZeroEquiv (M.cechComplex d))).trans
    ((cocyclesBaseChangeEquiv (M.cechComplex d) hflatC
        (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) hex A 0).trans
      ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm.trans
        (cechHgrBaseChangeHomologyIso M d A 0).symm.toLinearEquiv))

/-- **Cohomology and Base Change, vanishing half**, in the `Hᵍʳ` form, with cochain
flatness. -/
theorem subsingleton_cechHgr_of_fibrewise' (hM : IsFG M)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (i : ℕ) (hi : 1 ≤ i) : Subsingleton ((M.cechHgr i).obj d) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  rw [show ((M.cechHgr (j + 1)).obj d) = ((M.cechComplex d).homology (j + 1)) from rfl,
    subsingleton_homology_succ_iff]
  exact exactAtSucc_cechComplex_of_fibrewise' (M := M) (d := d) hM hflatC hfib j

/-- **Cohomology and Base Change, finiteness half.** Under fibrewise vanishing of the higher
cohomology, `π_* M(d)` is a finite projective `R`-module — a vector bundle on the base. -/
theorem projective_cechHgr_zero (hM : IsFG M) (hflat : IsFlat M)
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d)) :
    Module.Projective R ((M.cechHgr 0).obj d) := by
  have hex := exactAtSucc_cechComplex_of_fibrewise M d hM hflat hfib
  haveI : Module.Finite R ((M.cechComplex d).homology 0) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 d
  haveI : Module.Finite R (cocyclesSub (M.cechComplex d) 0) :=
    finite_cocyclesSub_zero (M.cechComplex d)
  haveI := projective_cocyclesSub (M.cechComplex d) (flat_cechComplex_X M d hflat)
    (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) hex 0
  exact Module.Projective.of_equiv (homologyZeroEquiv (M.cechComplex d)).symm

/-- **Cohomology and Base Change, comparison half.** Under fibrewise vanishing of the higher
cohomology, the formation of `π_* M(d)` commutes with an arbitrary base change `R → A`. -/
noncomputable def cechHgrZeroBaseChangeEquiv (hM : IsFG M) (hflat : IsFlat M)
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (A : Type u) [CommRing A] [Algebra R A] :
    (A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A] (((M.baseChange A).cechHgr 0).obj d) :=
  have hex := exactAtSucc_cechComplex_of_fibrewise M d hM hflat hfib
  (LinearEquiv.baseChange R A _ _ (homologyZeroEquiv (M.cechComplex d))).trans
    ((cocyclesBaseChangeEquiv (M.cechComplex d) (flat_cechComplex_X M d hflat)
        (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) hex A 0).trans
      ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm.trans
        (cechHgrBaseChangeHomologyIso M d A 0).symm.toLinearEquiv))

/-! ## Uniform relative Serre vanishing -/

variable (M)

/-- **Serre vanishing over the base, uniformly in the cohomological degree.** Above the
dimension the cohomology vanishes for free, so only finitely many degrees need a bound. -/
theorem exists_uniform_subsingleton_cechHgr (hM : IsFG M) :
    ∃ d₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ d : ℤ, d₀ ≤ d → Subsingleton ((M.cechHgr i).obj d) := by
  classical
  choose f hf using fun (i : ℕ) (hi : 1 ≤ i) => exists_subsingleton_cechHgr_of_isFG M hM i hi
  set g : ℕ → ℤ := fun i => if h : 1 ≤ i then f i h else 0 with hg
  refine ⟨((Finset.range (n + 1)).sup fun i => (g i).toNat : ℕ), fun i hi d hd => ?_⟩
  rcases lt_or_ge n i with hni | hni
  · exact subsingleton_cechHgr M i hni d
  · refine hf i hi d (le_trans ?_ hd)
    have h1 : f i hi ≤ ((g i).toNat : ℤ) := by
      have : g i = f i hi := by rw [hg]; simp [hi]
      rw [← this]
      exact Int.self_le_toNat _
    refine le_trans h1 ?_
    exact_mod_cast Finset.le_sup (f := fun i => (g i).toNat)
      (Finset.mem_range.mpr (by omega))

variable {M}

/-- **Uniform relative Serre vanishing.** For a coherent family flat over a noetherian base
there is a single twist `d₀` beyond which the higher cohomology vanishes on *every* base
change — in particular on every field fibre, uniformly.

This is the statement that makes `RelativeCohomology.uniform_serre_vanishing` available: no
semicontinuity is needed, because the Čech complex of a flat family is a bounded complex of
flat modules, so once it is exact over `R` it stays exact after any base change. -/
theorem exists_uniform_subsingleton_cechHgr_baseChange' (hM : IsFG M)
    (hflatC : ∀ (d : ℤ) (p : ℕ), Module.Flat R ((M.cechComplex d).X p)) :
    ∃ d₀ : ℤ, ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ), 1 ≤ i →
      ∀ d : ℤ, d₀ ≤ d → Subsingleton (((M.baseChange A).cechHgr i).obj d) := by
  obtain ⟨d₀, hd₀⟩ := exists_uniform_subsingleton_cechHgr M hM
  refine ⟨d₀, fun A _ _ i hi d hd => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  have hex : ∀ j' : ℕ, ExactAtSucc (M.cechComplex d) j' := by
    intro j'
    rw [← subsingleton_homology_succ_iff]
    exact hd₀ (j' + 1) (by omega) d hd
  have hbc : ExactAtSucc (cochainBaseChange A (M.cechComplex d)) j := by
    rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom, cochainBaseChange_d_hom]
    exact range_baseChange_d_eq_ker A (hflatC d)
      (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) (t := 0)
      (fun i' _ => hex i') (Nat.zero_le j)
  rw [← subsingleton_homology_succ_iff] at hbc
  exact (cechHgrBaseChangeHomologyIso M d A (j + 1)).toLinearEquiv.toEquiv.subsingleton

/-- **Uniform relative Serre vanishing.** -/
theorem exists_uniform_subsingleton_cechHgr_baseChange (hM : IsFG M) (hflat : IsFlat M) :
    ∃ d₀ : ℤ, ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ), 1 ≤ i →
      ∀ d : ℤ, d₀ ≤ d → Subsingleton (((M.baseChange A).cechHgr i).obj d) := by
  obtain ⟨d₀, hd₀⟩ := exists_uniform_subsingleton_cechHgr M hM
  refine ⟨d₀, fun A _ _ i hi d hd => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  have hex : ∀ j' : ℕ, ExactAtSucc (M.cechComplex d) j' := by
    intro j'
    rw [← subsingleton_homology_succ_iff]
    exact hd₀ (j' + 1) (by omega) d hd
  have hbc : ExactAtSucc (cochainBaseChange A (M.cechComplex d)) j := by
    rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom, cochainBaseChange_d_hom]
    exact range_baseChange_d_eq_ker A (flat_cechComplex_X M d hflat)
      (N := n) (fun p hp => subsingleton_cechComplex_X M d hp) (t := 0)
      (fun i' _ => hex i') (Nat.zero_le j)
  rw [← subsingleton_homology_succ_iff] at hbc
  exact (cechHgrBaseChangeHomologyIso M d A (j + 1)).toLinearEquiv.toEquiv.subsingleton

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
