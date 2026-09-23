module

public import StacksAndModuli.API.ProjectiveGradedSnapper

/-!
# Uniform regularity of kernels of twisted-free presentations

Supporting API for Step 1 of Proposition 2.4.1 (§2.4 of *Stacks and Moduli*): there is an
integer `m₀`, depending only on `(n, l, r, P)`, such that over
**every** field the kernel of **every** presentation `𝒪(-l)^{⊕r} ↠ Q` on `ℙⁿ` whose
quotient has Hilbert polynomial `P` is `m₀`-regular.

This combines three inputs.  Theorem 2.3.8 (`exists_boundsRegularity_of_field`) bounds
the regularity of subsheaves of the **untwisted** `𝒪^{⊕r}` in terms of their
`χ`-Hilbert polynomial; Snapper's theorem (`Cohomology.exists_hasHilbertPolynomial`)
provides the kernel's `χ`-polynomial; and its identification with `P_F - P`, where
`P_F(z) = r·C(z - l + n, n)` is the Hilbert polynomial of the ambient sheaf, is by
additivity of `χ` together with eventual agreement of `χ` with `h⁰` (Serre vanishing) and
uniqueness of polynomials.  The twist `l` is removed degreewise: `F(l) ⊆ 𝒪^{⊕r}`, and
`m`-regularity of `F(l)` is `(m + l)`-regularity of `F`.

Main declarations:

* `Polynomial.twistedFreeHilbertPolynomial`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.h_pow`, `h_twist`,
  `exists_uniform_serre_vanishing`, `eventually_chi_eq_h_zero`;
* `AlgebraicGeometry.ProjectiveSpace.GradedModule.untwistInto`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.exists_boundsRegularity_twistedFree_kernel`
  — the endpoint.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open Polynomial

/-- **The Hilbert polynomial of the twisted-free ambient sheaf** `𝒪(-l)^{⊕r}` on `ℙⁿ`:
`P_F(z) = r · C(z - l + n, n)`. -/
noncomputable def Polynomial.twistedFreeHilbertPolynomial (n r : ℕ) (l : ℤ) : Polynomial ℚ :=
  (r : ℚ) • (binomialPoly n).comp (X + C ((n : ℚ) - (l : ℚ)))

/-- The value of the ambient Hilbert polynomial in degrees `d ≥ l` is the rank of the
degree-`d` part, `r · C(n + d - l, n)`. -/
lemma Polynomial.twistedFreeHilbertPolynomial_eval (n r : ℕ) (l d : ℤ) (hd : l ≤ d) :
    (twistedFreeHilbertPolynomial n r l).eval (d : ℚ)
      = (r : ℚ) * (((n : ℤ) + (d - l)).toNat.choose n : ℚ) := by
  have hnn : (0 : ℤ) ≤ (n : ℤ) + (d - l) := by omega
  have hcast : ((((n : ℤ) + (d - l)).toNat : ℕ) : ℚ) = (n : ℚ) + ((d : ℚ) - (l : ℚ)) := by
    have h1 : (((n : ℤ) + (d - l)).toNat : ℤ) = (n : ℤ) + (d - l) := Int.toNat_of_nonneg hnn
    have h2 : ((((n : ℤ) + (d - l)).toNat : ℕ) : ℚ)
        = ((((n : ℤ) + (d - l)).toNat : ℤ) : ℚ) := by push_cast; ring
    rw [h2, h1]
    push_cast
    ring
  rw [twistedFreeHilbertPolynomial, eval_smul, smul_eq_mul, eval_comp, eval_add, eval_X,
    eval_C]
  congr 1
  rw [show (d : ℚ) + ((n : ℚ) - (l : ℚ)) = ((((n : ℤ) + (d - l)).toNat : ℕ) : ℚ) by
    rw [hcast]; ring]
  exact binomialPoly_eval_natCast n _

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open AlgebraicGeometry.ProjectiveSpace GradedModule

variable {k : Type u} [Field k] (C : Cohomology k)

/-- Cohomological dimensions of a finite direct sum of a coherent module. -/
lemma h_pow {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M) (r : ℕ) (i : ℕ) (d : ℤ) :
    C.h (M.pow r) i d = r * C.h M i d := by
  haveI := C.finiteDimensional hM i d
  rw [show C.h (M.pow r) i d = Module.finrank k ((C.Hgr (M.pow r) i).obj d) from rfl,
    (C.HgrPowIso M r i d).toLinearEquiv.finrank_eq]
  change Module.finrank k (Fin r → ((C.Hgr M i).obj d)) = _
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rfl

/-- Cohomological dimensions of a twist. -/
lemma h_twist {n : ℕ} (M : GradedModule k n) (a : ℤ) (i : ℕ) (d : ℤ) :
    C.h (M.twist a) i d = C.h M i (d + a) :=
  (C.twistIso M a i d).toLinearEquiv.finrank_eq

/-- **Uniform Serre vanishing**: for a coherent module there is a single degree beyond which
all higher cohomology vanishes.  Above the dimension the vanishing is Grothendieck's. -/
lemma exists_uniform_serre_vanishing {n : ℕ} {M : GradedModule k n}
    (hM : C.IsCoherent M) :
    ∃ d₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ d : ℤ, d₀ ≤ d → Subsingleton ((C.Hgr M i).obj d) := by
  classical
  choose f hf using fun (i : ℕ) (hi : 1 ≤ i) => C.serre_vanishing hM i hi
  set g : ℕ → ℤ := fun i => if h : 1 ≤ i then f i h else 0 with hg
  refine ⟨((Finset.range (n + 1)).sup fun i => (g i).toNat : ℕ), fun i hi d hd => ?_⟩
  rcases lt_or_ge n i with hni | hni
  · exact C.subsingleton_of_lt M i d hni
  · refine hf i hi d (le_trans ?_ hd)
    have h1 : f i hi ≤ ((g i).toNat : ℤ) := by
      have : g i = f i hi := by rw [hg]; simp [hi]
      rw [← this]
      exact Int.self_le_toNat _
    refine le_trans h1 ?_
    exact_mod_cast Finset.le_sup (f := fun i => (g i).toNat)
      (Finset.mem_range.mpr (by omega))

/-- **`χ` is eventually `h⁰`**, by Serre vanishing. -/
lemma eventually_chi_eq_h_zero {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → C.chi M d = (C.h M 0 d : ℤ) := by
  obtain ⟨d₀, hd₀⟩ := C.exists_uniform_serre_vanishing hM
  refine ⟨d₀, fun d hd => ?_⟩
  rw [chi]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi0
    rw [C.h_eq_zero_of_subsingleton (hd₀ i (by omega) d hd)]
    ring
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0




end AlgebraicGeometry.ProjectiveSpace.Cohomology

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory

variable (k : Type u) [Field k] (n : ℕ)

/-- Multiplication on a twist of the structure module is multiplication of the underlying
polynomials, in any pair of degrees. -/
lemma structureModule_twist_mulX'_val (a b c : ℤ) (h : b + 1 = c) (i : Fin (n + 1))
    (y : ((structureModule k n).twist a).obj b) :
    ((((structureModule k n).twist a).mulX' i b c h).hom y).1
      = MvPolynomial.X i * y.1 := by
  subst h
  rw [mulX'_rfl, twist_mulX]
  exact structureModule_mulX'_val i (b + a) (b + 1 + a) (by ring) y

/-- Untwisting the ambient free module degreewise: the degree-`(d+l)` part of
`𝒪(-l)^{⊕r}` is the degree-`d` part of `𝒪^{⊕r}`. -/
noncomputable def untwistAmbientEquiv (l : ℤ) (r : ℕ) (d : ℤ) :
    ((((structureModule k n).twist (-l)).pow r).obj (d + l)) ≃ₗ[k]
      (((structureModule k n).pow r).obj d) :=
  LinearEquiv.piCongrRight fun _ : Fin r => LinearEquiv.ofEq _ _
    (congrArg (polySubmodule k n) (show d + l + -l = d by ring))

/-- The untwisting equivalence does not change the underlying polynomials. -/
lemma untwistAmbientEquiv_apply_val (l : ℤ) (r : ℕ) (d : ℤ)
    (y : (((structureModule k n).twist (-l)).pow r).obj (d + l)) (t : Fin r) :
    (((untwistAmbientEquiv k n l r d) y) t).1 = (y t).1 := rfl

/-- **Removing the twist from a subsheaf of the twisted-free ambient sheaf**: an injection
`F ⟶ 𝒪(-l)^{⊕r}` yields an injection `F(l) ⟶ 𝒪^{⊕r}`. -/
noncomputable def untwistInto {F : GradedModule k n} (l : ℤ) (r : ℕ)
    (f : F ⟶ ((structureModule k n).twist (-l)).pow r) :
    F.twist l ⟶ (structureModule k n).pow r where
  app d := ModuleCat.ofHom
    ((untwistAmbientEquiv k n l r d).toLinearMap.comp (f.app (d + l)).hom)
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun t => Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearEquiv.coe_coe]
    have hL : ((((structureModule k n).pow r).mulX i d).hom
        ((untwistAmbientEquiv k n l r d) ((f.app (d + l)).hom x)) t).1
        = MvPolynomial.X i * ((((f.app (d + l)).hom x) t).1) := by
      rw [pow_mulX_apply]
      rfl
    have h2 : (f.app (d + 1 + l)).hom ((F.mulX' i (d + l) (d + 1 + l) (by ring)).hom x)
        = ((((structureModule k n).twist (-l)).pow r).mulX' i (d + l) (d + 1 + l)
            (by ring)).hom ((f.app (d + l)).hom x) := by
      have h3 := congrArg (fun ψ : F.obj (d + l) ⟶
          (((structureModule k n).twist (-l)).pow r).obj (d + 1 + l) => ψ.hom x)
        (Hom.comm' f i (d + l) (d + 1 + l) (by ring))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
      exact h3.symm
    have hR : (((untwistAmbientEquiv k n l r (d + 1))
        ((f.app (d + 1 + l)).hom ((((F.twist l).mulX i d).hom x)))) t).1
        = MvPolynomial.X i * ((((f.app (d + l)).hom x) t).1) := by
      have h1 : ((F.twist l).mulX i d).hom x = (F.mulX' i (d + l) (d + 1 + l)
          (by ring)).hom x := rfl
      rw [untwistAmbientEquiv_apply_val, h1, h2]
      have h4 := pow_mulX'_apply ((structureModule k n).twist (-l)) r i (d + l) (d + 1 + l)
        (by ring) ((f.app (d + l)).hom x) t
      rw [show (((((structureModule k n).twist (-l)).pow r).mulX' i (d + l) (d + 1 + l)
          (by ring)).hom ((f.app (d + l)).hom x)) t
        = ((((structureModule k n).twist (-l)).mulX' i (d + l) (d + 1 + l)
          (by ring)).hom (((f.app (d + l)).hom x) t)) from h4]
      exact structureModule_twist_mulX'_val k n (-l) (d + l) (d + 1 + l) (by ring) i _
    exact hL.trans hR.symm

/-- The untwisted comparison is degreewise injective when the original one is. -/
lemma injective_untwistInto_app {F : GradedModule k n} (l : ℤ) (r : ℕ)
    (f : F ⟶ ((structureModule k n).twist (-l)).pow r)
    (hf : ∀ d, Function.Injective (f.app d).hom) (d : ℤ) :
    Function.Injective ((untwistInto k n l r f).app d).hom := by
  intro x y hxy
  exact hf (d + l) ((untwistAmbientEquiv k n l r d).injective hxy)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open AlgebraicGeometry.ProjectiveSpace GradedModule Polynomial

/-- Two rational polynomials agreeing at every large integer are equal. -/
lemma _root_.Polynomial.eq_of_eventually_intCast_eval_eq {P Q : Polynomial ℚ} (D : ℤ)
    (h : ∀ d : ℤ, D ≤ d → P.eval (d : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  refine Polynomial.eq_of_infinite_eval_eq P Q ?_
  have hinj : Function.Injective (fun m : ℕ => ((D + m : ℤ) : ℚ)) := by
    intro a b hab
    have hab' : ((D + a : ℤ) : ℚ) = ((D + b : ℤ) : ℚ) := hab
    have : (D + a : ℤ) = (D + b : ℤ) := by exact_mod_cast hab'
    omega
  exact Set.infinite_of_injective_forall_mem hinj (fun m => h (D + m) (by omega))

/-- Supporting uniform-regularity theorem for Step 1 of Proposition 2.4.1: there is an
integer `m₀ = m₀(n, l, r, P)` such that over every
field, the kernel of every presentation `𝒪(-l)^{⊕r} ↠ Q` on `ℙⁿ` whose quotient has
eventual Hilbert function `P` is `m₀`-regular.

The kernel has `χ`-Hilbert polynomial `P_F - P` by Snapper's theorem, additivity of `χ`,
and uniqueness of polynomials, so Theorem 2.3.8 applies to its untwist `F(l) ⊆ 𝒪^{⊕r}`. -/
theorem exists_boundsRegularity_twistedFree_kernel (r n : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ m₀ : ℤ, ∀ (K : Type u) [Field K] (C : Cohomology K), C.HasInfiniteBaseChange →
      ∀ (F Q' : GradedModule K n)
        (f : F ⟶ ((structureModule K n).twist (-l)).pow r)
        (g : ((structureModule K n).twist (-l)).pow r ⟶ Q'),
        GradedModule.ShortExact f g → C.IsCoherent Q' →
        (∃ dP : ℤ, ∀ d : ℤ, dP ≤ d → (C.h Q' 0 d : ℚ) = P.eval (d : ℚ)) →
        C.IsMRegular F m₀ := by
  obtain ⟨m₁, hm₁⟩ := exists_boundsRegularity_of_field.{u} r n
    ((twistedFreeHilbertPolynomial n r l - P).comp (X + C (l : ℚ)))
  refine ⟨m₁ + l, ?_⟩
  intro K _ C hC F Q' f g hfg hQcoh hP
  obtain ⟨dP, hdP⟩ := hP
  have hAmbcoh : C.IsCoherent (((structureModule K n).twist (-l)).pow r) :=
    C.isCoherent_pow (C.isCoherent_twist C.isCoherent_structureModule (-l)) r
  have hFcoh : C.IsCoherent F := C.isCoherent_of_injective f hfg.injective hAmbcoh
  -- Snapper's polynomial for the kernel
  obtain ⟨P'', hP''⟩ := C.exists_hasHilbertPolynomial hC F hFcoh
  -- identify it with `P_F - P`
  have hPeq : P'' = twistedFreeHilbertPolynomial n r l - P := by
    obtain ⟨dA, hdA⟩ := C.eventually_chi_eq_h_zero hAmbcoh
    obtain ⟨dQ, hdQ⟩ := C.eventually_chi_eq_h_zero hQcoh
    refine Polynomial.eq_of_eventually_intCast_eval_eq (max (max dA dQ) (max l dP))
      (fun d hd => ?_)
    have hdA' : dA ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hdQ' : dQ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hdl : l ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
    have hdP' : dP ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
    have hadd := C.chi_add hfg hFcoh hAmbcoh hQcoh d
    -- ambient value
    have hAmb : (C.chi (((structureModule K n).twist (-l)).pow r) d : ℚ)
        = (twistedFreeHilbertPolynomial n r l).eval (d : ℚ) := by
      rw [hdA d hdA']
      rw [twistedFreeHilbertPolynomial_eval n r l d hdl]
      rw [show C.h (((structureModule K n).twist (-l)).pow r) 0 d
          = r * C.h ((structureModule K n).twist (-l)) 0 d from
        C.h_pow (C.isCoherent_twist C.isCoherent_structureModule (-l)) r 0 d]
      rw [show C.h ((structureModule K n).twist (-l)) 0 d
          = C.h (structureModule K n) 0 (d + -l) from C.h_twist _ (-l) 0 d]
      have hfin : C.h (structureModule K n) 0 (d + -l)
          = ((n : ℤ) + (d + -l)).toNat.choose n :=
        C.finrank_HgrZero_structureModule (d + -l) (by omega)
      rw [hfin]
      rw [show ((n : ℤ) + (d + -l)).toNat = ((n : ℤ) + (d - l)).toNat by omega]
      push_cast
      ring
    -- quotient value
    have hQ : (C.chi Q' d : ℚ) = P.eval (d : ℚ) := by
      rw [hdQ d hdQ']
      exact hdP d hdP'
    have hF := hP'' d
    have haddQ : (C.chi (((structureModule K n).twist (-l)).pow r) d : ℚ)
        = (C.chi F d : ℚ) + (C.chi Q' d : ℚ) := by exact_mod_cast hadd
    rw [Polynomial.eval_sub, ← hAmb, ← hQ, ← hF]
    linarith
  -- untwist and apply the regularity bound
  have hFl : C.HasHilbertPolynomial (F.twist l)
      (((twistedFreeHilbertPolynomial n r l - P)).comp (X + Polynomial.C (l : ℚ))) := by
    intro d
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [C.chi_twist F l d]
    have := hP'' (d + l)
    rw [hPeq] at this
    rw [show ((d : ℚ) + (l : ℚ)) = ((d + l : ℤ) : ℚ) by push_cast; ring]
    exact this
  have hreg := hm₁ K C hC (F.twist l) (untwistInto K n l r f)
    (injective_untwistInto_app K n l r f hfg.injective) hFl
  intro i hi
  have hs := hreg i hi
  rw [C.subsingleton_Hgr_twist_iff] at hs
  rwa [show m₁ - (i : ℤ) + l = m₁ + l - i by ring] at hs

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
