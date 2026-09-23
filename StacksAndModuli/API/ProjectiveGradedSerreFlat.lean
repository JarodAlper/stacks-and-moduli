module

public import StacksAndModuli.API.ProjectiveGradedImagePresentation

/-!
# Relative Serre finiteness and vanishing for flat graded modules

This file generalizes the graded Čech vanishing dévissage of
`StacksAndModuli/API/ProjectiveGradedSerre.lean` from noetherian coefficient rings to arbitrary
commutative rings for finitely generated graded modules that are degreewise flat over the
coefficient ring.  The corresponding finiteness dévissage is recorded with its additional
exact-middle finiteness input made explicit.

The sole additional input is the finite-presentation conclusion of the graded flat
finite-presentation theorem: the total polynomial module of every finitely generated flat
graded module is finitely presented.  At each stage of the dévissage, the image of the
eventual free presentation is again finitely generated and flat.  Its finitely presented
total module therefore makes the diagrammatic relation kernel finitely generated, while
short exactness makes that kernel flat.  The original Čech exactness and free vanishing
arguments then apply without change.

Over an arbitrary noncoherent ring, exactness `A → B → C` and finiteness of `A` and `C`
do not imply finiteness of `B`: the image in `C` is a submodule of a finite module and need
not be finite.  Thus the finite-presentation input alone does **not** imply arbitrary-base
Serre finiteness.  `ExactFiniteMiddleInput` names precisely this further closure property;
the noetherian specialization is supplied by `exactFiniteMiddleInput_of_isNoetherianRing`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The finite-presentation input for relative Serre dévissage: every finitely generated
degreewise-flat graded module has finitely presented total module over the polynomial ring. -/
def FlatFinitePresentationInput (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ (N : GradedModule R n), IsFG N → IsFlat N →
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total N)

/-- The exact-middle closure used by the classical Serre finiteness dévissage.  It is kept
as an explicit hypothesis because it fails over arbitrary noncoherent coefficient rings. -/
def ExactFiniteMiddleInput (R : Type u) [CommRing R] : Prop :=
  ∀ {A B C : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C],
    ∀ (f : A →ₗ[R] B) (g : B →ₗ[R] C), Function.Exact f g →
      Module.Finite R A → Module.Finite R C → Module.Finite R B

/-- Noetherian rings satisfy exact-middle finiteness. -/
theorem exactFiniteMiddleInput_of_isNoetherianRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] : ExactFiniteMiddleInput R := by
  intro A B C _ _ _ _ _ _ f g hfg hA hC
  letI : Module.Finite R A := hA
  letI : Module.Finite R C := hC
  exact finiteDimensional_of_exact f g hfg

/-! ## Serre finiteness -/

/-- The descending induction behind relative Serre finiteness for finitely generated flat
graded modules. -/
theorem finite_cechHgr_of_isFG_of_isFlat_aux
    (hfp : FlatFinitePresentationInput R n) (hfiniteExact : ExactFiniteMiddleInput R)
    (j : ℕ) :
    ∀ (M : GradedModule R n), IsFG M → IsFlat M →
      ∀ i : ℕ, n + 1 ≤ i + j → ∀ d : ℤ,
        Module.Finite R ((M.cechHgr i).obj d) := by
  classical
  induction j with
  | zero =>
      intro M _ _ i hij d
      haveI := subsingleton_cechHgr M i (by omega) d
      exact finiteDimensional_of_subsingleton
  | succ j ih =>
      intro M hM hMflat i hij d
      rcases lt_or_ge n i with hni | hni
      · haveI := subsingleton_cechHgr M i hni d
        exact finiteDimensional_of_subsingleton
      obtain ⟨hfd, hlow, d₀, hgen⟩ := hM
      haveI : Module.Finite R (M.obj d₀) := hfd d₀
      obtain ⟨r, y, hyspan⟩ := Module.Finite.exists_fin (R := R) (M := (M.obj d₀ : Type u))
      have himgFG : IsFG (imgMod M d₀ y) := isFG_imgMod M d₀ y
      have himgFlat : IsFlat (imgMod M d₀ y) :=
        hMflat.freeGenImage d₀ y hyspan hgen
      letI : Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
          (Total (imgMod M d₀ y)) := hfp _ himgFG himgFlat
      have hK : IsFG (ker (freeGenHom M d₀ y)) :=
        isFG_kernel_freeGenHom_of_finitePresentation_image M d₀ y
      have hfreeFlat : IsFlat (((structureModule R n).twist (-d₀)).pow r) :=
        (isFlat_structureModule.twist (-d₀)).pow r
      have hKflat : IsFlat (ker (freeGenHom M d₀ y)) :=
        IsFlat.of_shortExact (shortExact_freeGenToImg M d₀ y) hfreeFlat himgFlat
      haveI : Module.Finite R
          (((ker (freeGenHom M d₀ y)).cechHgr (i + 1)).obj d) :=
        ih _ hK hKflat (i + 1) (by omega) d
      haveI : Module.Finite R
          (((((structureModule R n).twist (-d₀)).pow r).cechHgr i).obj d) :=
        finiteDimensional_cechHgr_free (-d₀) r i d
      haveI : Module.Finite R (((imgMod M d₀ y).cechHgr i).obj d) :=
        hfiniteExact
          ((cechHgrMap (freeGenToImg M d₀ y) i).app d).hom
          (cechδ (shortExact_freeGenToImg M d₀ y) i d).hom
          (cech_exact_map_δ (shortExact_freeGenToImg M d₀ y) i d)
          inferInstance inferInstance
      exact Module.Finite.of_surjective ((cechHgrMap (imgIota M d₀ y) i).app d).hom
        (bijective_cechHgrMap_imgIota M d₀ y hyspan hgen i d).2

/-- Relative Serre finiteness for finitely generated degreewise-flat graded modules, assuming
finite presentation of total modules for all such graded modules. -/
theorem finite_cechHgr_of_isFG_of_isFlat
    (hfp : FlatFinitePresentationInput R n) (hfiniteExact : ExactFiniteMiddleInput R)
    (M : GradedModule R n)
    (hM : IsFG M) (hMflat : IsFlat M) (i : ℕ) (d : ℤ) :
    Module.Finite R ((M.cechHgr i).obj d) :=
  finite_cechHgr_of_isFG_of_isFlat_aux
    hfp hfiniteExact (n + 1) M hM hMflat i (by omega) d

/-! ## Serre vanishing -/

/-- The descending induction behind relative Serre vanishing for finitely generated flat
graded modules. -/
theorem exists_subsingleton_cechHgr_of_isFG_of_isFlat_aux
    (hfp : FlatFinitePresentationInput R n) (j : ℕ) :
    ∀ (M : GradedModule R n), IsFG M → IsFlat M →
      ∀ i : ℕ, 1 ≤ i → n + 1 ≤ i + j →
        ∃ e₀ : ℤ, ∀ d : ℤ, e₀ ≤ d → Subsingleton ((M.cechHgr i).obj d) := by
  classical
  induction j with
  | zero =>
      intro M _ _ i _ hij
      exact ⟨0, fun d _ => subsingleton_cechHgr M i (by omega) d⟩
  | succ j ih =>
      intro M hM hMflat i hi hij
      rcases lt_or_ge n i with hni | hni
      · exact ⟨0, fun d _ => subsingleton_cechHgr M i hni d⟩
      obtain ⟨hfd, hlow, d₀, hgen⟩ := hM
      haveI : Module.Finite R (M.obj d₀) := hfd d₀
      obtain ⟨r, y, hyspan⟩ := Module.Finite.exists_fin (R := R) (M := (M.obj d₀ : Type u))
      have himgFG : IsFG (imgMod M d₀ y) := isFG_imgMod M d₀ y
      have himgFlat : IsFlat (imgMod M d₀ y) :=
        hMflat.freeGenImage d₀ y hyspan hgen
      letI : Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
          (Total (imgMod M d₀ y)) := hfp _ himgFG himgFlat
      have hK : IsFG (ker (freeGenHom M d₀ y)) :=
        isFG_kernel_freeGenHom_of_finitePresentation_image M d₀ y
      have hfreeFlat : IsFlat (((structureModule R n).twist (-d₀)).pow r) :=
        (isFlat_structureModule.twist (-d₀)).pow r
      have hKflat : IsFlat (ker (freeGenHom M d₀ y)) :=
        IsFlat.of_shortExact (shortExact_freeGenToImg M d₀ y) hfreeFlat himgFlat
      obtain ⟨eK, heK⟩ := ih _ hK hKflat (i + 1) (by omega) (by omega)
      refine ⟨max eK (-(n : ℤ) + d₀), fun d hd => ?_⟩
      haveI : Subsingleton (((ker (freeGenHom M d₀ y)).cechHgr (i + 1)).obj d) :=
        heK d (le_trans (le_max_left _ _) hd)
      haveI : Subsingleton
          (((((structureModule R n).twist (-d₀)).pow r).cechHgr i).obj d) := by
        refine subsingleton_cechHgr_free (-d₀) r i hi d ?_
        have := le_trans (le_max_right _ _) hd
        omega
      haveI : Subsingleton (((imgMod M d₀ y).cechHgr i).obj d) :=
        subsingleton_of_exact
          ((cechHgrMap (freeGenToImg M d₀ y) i).app d).hom
          (cechδ (shortExact_freeGenToImg M d₀ y) i d).hom
          (cech_exact_map_δ (shortExact_freeGenToImg M d₀ y) i d)
      exact ((bijective_cechHgrMap_imgIota M d₀ y hyspan hgen i d).2).subsingleton

/-- Relative Serre vanishing for finitely generated degreewise-flat graded modules, assuming
finite presentation of total modules for all such graded modules. -/
theorem exists_subsingleton_cechHgr_of_isFG_of_isFlat
    (hfp : FlatFinitePresentationInput R n) (M : GradedModule R n)
    (hM : IsFG M) (hMflat : IsFlat M) (i : ℕ) (hi : 1 ≤ i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Subsingleton ((M.cechHgr i).obj d) :=
  exists_subsingleton_cechHgr_of_isFG_of_isFlat_aux
    hfp (n + 1) M hM hMflat i hi (by omega)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
