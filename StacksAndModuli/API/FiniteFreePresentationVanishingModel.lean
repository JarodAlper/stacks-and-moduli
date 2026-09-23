module

public import StacksAndModuli.API.FiniteProjectiveSheafMorphismZeroLocus
public import StacksAndModuli.API.FlatGlobalSectionsBaseChange
public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# Vanishing models from finite free presentations and global sections

Let `p : E ⟶ F` be a morphism on a scheme over an affine base.  If finitely many global
sections generate `E`, then `p` vanishes after a base change precisely when their images in
`F` vanish.  When global sections of `F` form a finite projective module and the canonical
global-sections comparison is bijective after every base change, those finitely many images
give a universal finite-projective coefficient model.  The finite-free retract construction
then cuts out their zero locus.

This is the reusable algebraic-geometric core of the finite twisted-free presentation
argument used for Quot schemes.  Twisting and the eventual Cohomology-and-Base-Change input
are kept outside this file.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling the defining sections of a free-sheaf morphism through a target morphism
gives the corresponding composite after pullback.  This lightweight form is kept here
to avoid importing the full Quot-to-Grassmannian naturality construction. -/
lemma pullback_freeHomOfSections_comp_of_sections
    {X Y : Scheme.{u}} (g : X ⟶ Y) {I : Type u} {M : Y.Modules}
    {N : X.Modules} (s : I → Γ(M, ⊤)) (s' : I → Γ(N, ⊤))
    (β : (pullback g).obj M ⟶ N)
    (h : ∀ i, Hom.app β ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections g M (s i)) = s' i) :
    (pullbackFreeIso g I).inv ≫ (pullback g).map (freeHomOfSections s) ≫ β =
      freeHomOfSections s' := by
  apply Scheme.free_hom_ext
  intro i
  have hs : Hom.app (freeHomOfSections s) ⊤
      (Scheme.freeGenSection Y i) = s i := by
    simp only [Scheme.freeGenSection, freeHomOfSections]
    change ((SheafOfModules.freeHomEquiv M) (freeHomOfSections s) i).val (op ⊤) = s i
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
    exact (sectionsTopEquiv M).apply_symm_apply (s i)
  have hs' : Hom.app (freeHomOfSections s') ⊤
      (Scheme.freeGenSection X i) = s' i := by
    simp only [Scheme.freeGenSection, freeHomOfSections]
    change ((SheafOfModules.freeHomEquiv N) (freeHomOfSections s') i).val (op ⊤) = s' i
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
    exact (sectionsTopEquiv N).apply_symm_apply (s' i)
  change Hom.app β ⊤
      (Hom.app ((pullback g).map (freeHomOfSections s)) ⊤
        (Hom.app (pullbackFreeIso g I).inv ⊤
          (Scheme.freeGenSection X i))) =
    Hom.app (freeHomOfSections s') ⊤ (Scheme.freeGenSection X i)
  rw [Scheme.pullbackFreeIso_inv_freeGenSection]
  have hnat := Scheme.unit_app_naturality_top g
    (freeHomOfSections s) (Scheme.freeGenSection Y i)
  calc
    _ = Hom.app β ⊤
        ((((pullbackPushforwardAdjunction g).unit.app M).app ⊤)
          (Hom.app (freeHomOfSections s) ⊤ (Scheme.freeGenSection Y i))) :=
      congrArg (fun z ↦ Hom.app β ⊤ z) hnat
    _ = Hom.app β ⊤ (_root_.Scheme.Modules.pullbackGlobalSections g M (s i)) := by
      rw [hs]
      rfl
    _ = s' i := h i
    _ = _ := hs'.symm

/-- A map from a free sheaf defined by global sections is zero exactly when every defining
section is zero. -/
lemma freeHomOfSections_eq_zero_iff
    {X : Scheme.{u}} {I : Type u} {M : X.Modules} (s : I → Γ(M, ⊤)) :
    freeHomOfSections s = 0 ↔ ∀ i, s i = 0 := by
  have hs (i : I) :
      Hom.app (freeHomOfSections s) ⊤ (Scheme.freeGenSection X i) = s i := by
    simp only [Scheme.freeGenSection, freeHomOfSections]
    change ((SheafOfModules.freeHomEquiv M) (freeHomOfSections s) i).val (op ⊤) = s i
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
    exact (sectionsTopEquiv M).apply_symm_apply (s i)
  constructor
  · intro h i
    have hi := hs i
    rw [h] at hi
    simpa using hi.symm
  · intro h
    apply Scheme.free_hom_ext
    intro i
    rw [hs i, h i]
    simp

/-- Fixed-degree finite projectivity and arbitrary-base compatibility for global sections.

The comparison is required to be the canonical map, rather than merely an unspecified
equivalence, so its value on a pure tensor is definitionally the pulled-back section. -/
structure HasFiniteProjectiveGlobalSectionsBaseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of R)) (F : X.Modules) : Type (u + 1) where
  /-- Global sections are finite over the affine base. -/
  finite :
    letI := globalSectionsModule pX F
    Module.Finite R Γ(F, ⊤)
  /-- Global sections are projective over the affine base. -/
  projective :
    letI := globalSectionsModule pX F
    Module.Projective R Γ(F, ⊤)
  /-- The canonical global-sections comparison is bijective after every affine base
  change. -/
  baseChange_bijective : ∀ (A : Type u) [CommRing A] (f : R →+* A),
    let φ := CommRingCat.ofHom f
    let Y := Limits.pullback (Spec.map φ) pX
    let g : Y ⟶ X := Limits.pullback.snd (Spec.map φ) pX
    let pY : Y ⟶ Spec (.of A) := Limits.pullback.fst (Spec.map φ) pX
    letI : Algebra R A := f.toAlgebra
    letI : Module R Γ(F, ⊤) := globalSectionsModule pX F
    letI : Module A Γ((pullback g).obj F, ⊤) := globalSectionsModule pY ((pullback g).obj F)
    Function.Bijective
      (pullbackGlobalSectionsBaseChangeLinearMap
        φ g pX pY Limits.pullback.condition.symm F)

namespace HasFiniteProjectiveGlobalSectionsBaseChange

/-- A finite generating family for the source and arbitrary-base finite-projective global
sections for the target produce a universal finite-projective vanishing model. -/
noncomputable def toFiniteProjectiveVanishingModel
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    {pX : X ⟶ Spec (.of R)} {E F : X.Modules} {p : E ⟶ F}
    {I : Type u} [Fintype I] (s : I → Γ(E, ⊤)) [Epi (freeHomOfSections s)]
    (H : HasFiniteProjectiveGlobalSectionsBaseChange pX F) :
    HasFiniteProjectiveVanishingModel pX p := by
  classical
  letI : Module R Γ(F, ⊤) := globalSectionsModule pX F
  letI : Module.Finite R Γ(F, ⊤) := H.finite
  letI : Module.Projective R Γ(F, ⊤) := H.projective
  let t : I → Γ(F, ⊤) := fun i ↦ Hom.app p ⊤ (s i)
  refine
    { M := I → R
      N := Γ(F, ⊤)
      coordinates := Fintype.linearCombination R t
      pullback_zero_iff := fun A _ f ↦ ?_ }
  let φ := CommRingCat.ofHom f
  let Y := Limits.pullback (Spec.map φ) pX
  let g : Y ⟶ X := Limits.pullback.snd (Spec.map φ) pX
  let pY : Y ⟶ Spec (.of A) := Limits.pullback.fst (Spec.map φ) pX
  letI : Algebra R A := f.toAlgebra
  letI : Module A Γ((pullback g).obj F, ⊤) :=
    globalSectionsModule pY ((pullback g).obj F)
  let c := pullbackGlobalSectionsBaseChangeLinearMap
    φ g pX pY Limits.pullback.condition.symm F
  let tA : I → Γ((pullback g).obj F, ⊤) :=
    fun i ↦ _root_.Scheme.Modules.pullbackGlobalSections g F (t i)
  have hc : Function.Bijective c := H.baseChange_bijective A f
  have hfree :
      (pullbackFreeIso g I).inv ≫
          (pullback g).map (freeHomOfSections s) ≫ (pullback g).map p =
        freeHomOfSections tA := by
    apply pullback_freeHomOfSections_comp_of_sections
    intro i
    simpa only [tA, t] using pullbackGlobalSections_naturality g p (s i)
  let eA := (pullbackFreeIso g I).inv ≫
    (pullback g).map (freeHomOfSections s)
  haveI : Epi ((pullback g).map (freeHomOfSections s)) :=
    Functor.map_epi (pullback g) (freeHomOfSections s)
  haveI : Epi eA := inferInstance
  have hp_iff : (pullback g).map p = 0 ↔ freeHomOfSections tA = 0 := by
    constructor
    · intro hp
      calc
        freeHomOfSections tA = eA ≫ (pullback g).map p := hfree.symm
        _ = 0 := by rw [hp, comp_zero]
    · intro ht
      apply zero_of_epi_comp eA
      exact hfree.trans ht
  rw [hp_iff, freeHomOfSections_eq_zero_iff]
  change (
    ∀ i, tA i = 0) ↔
      (Fintype.linearCombination R t).baseChange A = 0
  constructor
  · intro htA
    apply LinearMap.ext
    intro x
    change (Fintype.linearCombination R t).baseChange A x = 0
    apply hc.injective
    rw [map_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul a v =>
        rw [LinearMap.baseChange_tmul, Fintype.linearCombination_apply,
          TensorProduct.tmul_sum, map_sum, Finset.sum_eq_zero]
        intro i _
        rw [TensorProduct.tmul_smul]
        change (pullbackGlobalSectionsBaseChangeLinearMap
          φ g pX pY Limits.pullback.condition.symm F)
            (v i • a ⊗ₜ[R] t i) = 0
        refine (pullbackGlobalSectionsBaseChangeLinearMap_tmul
          φ g pX pY Limits.pullback.condition.symm F (v i • a) (t i)).trans ?_
        change (v i • a) • tA i = 0
        rw [htA i, smul_zero]
  · intro h i
    have hi := LinearMap.congr_fun h
      (1 ⊗ₜ[R] (Pi.single i (1 : R)))
    change (Fintype.linearCombination R t).baseChange A
      (1 ⊗ₜ[R] (Pi.single i (1 : R))) = 0 at hi
    rw [LinearMap.baseChange_tmul,
      Fintype.linearCombination_apply_single, one_smul] at hi
    have hi' := congrArg c hi
    have hi'' : c (1 ⊗ₜ[R] t i) = 0 := by
      simpa only [map_zero] using hi'
    have hc_tmul : c (1 ⊗ₜ[R] t i) = tA i := by
      dsimp only [c, tA]
      rw [pullbackGlobalSectionsBaseChangeLinearMap_tmul, one_smul]
    exact hc_tmul.symm.trans hi''

/-- The preceding construction, followed by a finite-free retract of the target, gives
the exact finite-free vanishing model consumed by the affine zero-locus API. -/
noncomputable def toFiniteFreeVanishingModel
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    {pX : X ⟶ Spec (.of R)} {E F : X.Modules} {p : E ⟶ F}
    {I : Type u} [Fintype I] (s : I → Γ(E, ⊤)) [Epi (freeHomOfSections s)]
    (H : HasFiniteProjectiveGlobalSectionsBaseChange pX F) :
    HasFiniteFreeVanishingModel pX p :=
  (H.toFiniteProjectiveVanishingModel s).toFiniteFreeVanishingModel

end HasFiniteProjectiveGlobalSectionsBaseChange

end AlgebraicGeometry.Scheme.Modules
