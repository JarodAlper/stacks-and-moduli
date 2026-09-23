module

public import StacksAndModuli.API.PushforwardProjectiveRank
public import StacksAndModuli.API.ProjectiveTwistGlobalSections
public import StacksAndModuli.API.SheafifyComparison

/-!
# Monomial global sections of `𝒪(e)` on relative projective space

The Grassmannian step of §2.4 needs, for `d ≫ 0`, an epimorphism `𝒪_T^m ↠ π_*(Q(d))` where
`Q` is a quotient of `F = 𝒪(-l)^{⊕r}` on `ℙⁿ_T`.  Its `m` components are the images of the
degree-`(d-l)` **monomial** sections of `F(d)`; those exist on every base because
`Scheme.projectiveSpaceOverTwist` is *defined* as the pullback of the absolute twist on
`ℙⁿ_ℤ`, so global sections pull back from there.

This file records those sections.  The absolute monomial basis is
`MvPolynomial.projectiveTwistGlobalSectionsBasis` (in `API/ProjectiveTwistGlobalSections.lean`),
and `Scheme.Modules.pullbackGlobalSections` carries it along
`ℙⁿ_S → ℙⁿ_ℤ`.

**Note** the local instance: `MvPolynomial.gradedAlgebra` does not export, so it must be
re-declared in every file that mentions the polynomial `Proj`.

`Scheme.Modules.sectionsTopEquiv` is the missing comparison for the second half: Mathlib's
`SheafOfModules.freeHomEquiv` builds a map `𝒪^I ⟶ M` out of a family `I → M.sections`, and
`M.sections` — the sections of the presheaf over the *whole* site — is **not** definitionally
`Γ(M, ⊤)`.  On a scheme `⊤` is terminal, so evaluation at `⊤` is a bijection; that is the
equivalence recorded here, and `Scheme.Modules.freeHomOfSections` is the resulting
"map out of a free sheaf from global sections".

Main declarations:

* `AlgebraicGeometry.Scheme.twistMonomialSection`;
* `AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv` and
  `AlgebraicGeometry.Scheme.Modules.freeHomOfSections`, with its naturality
  `…freeHomOfSections_comp` (the handle for every later property of the
  Quot-to-Grassmannian map);
* `AlgebraicGeometry.Scheme.Modules.epi_of_surjective_on_affineOpens` — a morphism of sheaves
  of modules surjective on sections over every affine open is an epimorphism (affine opens are
  a basis, so local surjectivity is immediate);
* `AlgebraicGeometry.Scheme.Modules.restrict_mem_range_freeHomOfSections` and
  `…epi_freeHomOfSections_of_span` — **a map out of a free sheaf is an epimorphism as soon as,
  over every affine open, the restrictions of its defining sections generate the target**.
  This is what reduces the epimorphism half of the Quot-to-Grassmannian map to the affine
  statements "the monomials are a basis of `H⁰(F(d))`" and "`H⁰(F(d)) ↠ H⁰(Q(d))`".
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The `i`-th monomial global section of `𝒪(e)` on relative projective space**, pulled
back from `ℙⁿ_ℤ`, where `i` ranges over the `binom(n+e, n)` monomials of degree `e`. -/
def twistMonomialSection (n : ℕ) (S : Scheme.{u}) (e : ℕ)
    (i : Fin ((n + e).choose n)) :
    Γ(Scheme.projectiveSpaceOverTwist n S (e : ℤ), ⊤) :=
  Scheme.Modules.pullbackGlobalSections
    (Limits.pullback.snd (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))
    (ProjectiveSpectrum.Twist.twist
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ))
    (MvPolynomial.projectiveTwistGlobalSectionsBasis n (ULift.{u} ℤ) e i)

namespace Modules

/-- Sections of a sheaf of modules on a scheme are its global sections: `⊤` is terminal. -/
def sectionsTopEquiv {X : Scheme.{u}} (M : X.Modules) : M.sections ≃ ↥Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun m := PresheafOfModules.sectionsMk (M := M.val)
    (fun U => M.val.map ((homOfLE (le_top (a := U.unop))).op :
      (op (⊤ : X.Opens)) ⟶ U) m)
    (fun {U V} f => by
      have h : ((homOfLE (le_top (a := U.unop))).op : (op (⊤ : X.Opens)) ⟶ U) ≫ f =
          ((homOfLE (le_top (a := V.unop))).op : (op (⊤ : X.Opens)) ⟶ V) := rfl
      rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property ((homOfLE (le_top (a := U.unop))).op)
  right_inv m := by
    show M.val.map ((homOfLE (le_top (a := (⊤ : X.Opens)))).op :
      (op (⊤ : X.Opens)) ⟶ (op (⊤ : X.Opens))) m = m
    rw [show ((homOfLE (le_top (a := (⊤ : X.Opens)))).op :
      (op (⊤ : X.Opens)) ⟶ (op (⊤ : X.Opens))) = 𝟙 _ from rfl]
    simp

/-- **A map out of a free sheaf of modules, from a family of global sections.** -/
def freeHomOfSections {X : Scheme.{u}} {I : Type u} {M : X.Modules} (s : I → ↥Γ(M, ⊤)) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm (fun i => (sectionsTopEquiv M).symm (s i))

/-- `sectionsTopEquiv` is natural in the module. -/
lemma sectionsMap_sectionsTopEquiv_symm {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (m : ↥Γ(M, ⊤)) :
    SheafOfModules.sectionsMap φ ((sectionsTopEquiv M).symm m) =
      (sectionsTopEquiv N).symm (Scheme.Modules.Hom.app φ ⊤ m) := by
  apply Subtype.ext
  funext U
  change φ.val.app U (M.val.map ((homOfLE (le_top (a := U.unop))).op :
      (op (⊤ : X.Opens)) ⟶ U) m) =
    N.val.map ((homOfLE (le_top (a := U.unop))).op : (op (⊤ : X.Opens)) ⟶ U)
      (φ.val.app (op ⊤) m)
  exact (ConcreteCategory.congr_hom (φ.val.naturality
    ((homOfLE (le_top (a := U.unop))).op :
      (op (⊤ : X.Opens)) ⟶ U)) m)

/-- **`freeHomOfSections` is natural.** -/
lemma freeHomOfSections_comp {X : Scheme.{u}} {I : Type u} {M N : X.Modules}
    (s : I → ↥Γ(M, ⊤)) (φ : M ⟶ N) :
    freeHomOfSections s ≫ φ =
      freeHomOfSections (fun i => Scheme.Modules.Hom.app φ ⊤ (s i)) := by
  apply (SheafOfModules.freeHomEquiv N).injective
  funext i
  change N.unitHomEquiv (SheafOfModules.ιFree i ≫ freeHomOfSections s ≫ φ) = _
  rw [← Category.assoc, SheafOfModules.unitHomEquiv_comp_apply]
  change SheafOfModules.sectionsMap φ
    ((SheafOfModules.freeHomEquiv M) (freeHomOfSections s) i) = _
  simp only [freeHomOfSections, Equiv.apply_symm_apply]
  rw [sectionsMap_sectionsTopEquiv_symm]

/-- **A morphism of sheaves of modules that is surjective on sections over every affine open
is an epimorphism.** -/
lemma epi_of_surjective_on_affineOpens {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Surjective (Scheme.Modules.Hom.app φ U.1)) :
    Epi φ := by
  apply SheafOfModules.epi_of_isLocallySurjective
  constructor
  intro U s
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V', hV'mem, hxV, hVU⟩ :=
    (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open hx U.isOpen
  obtain ⟨V, hVmem, rfl⟩ := hV'mem
  refine ⟨V, homOfLE hVU, ?_, hxV⟩
  obtain ⟨t, ht⟩ := h ⟨V, hVmem⟩ (N.val.map (homOfLE hVU).op s)
  exact ⟨t, ht⟩

/-- The restriction of a defining section is in the image of `freeHomOfSections`. -/
lemma restrict_mem_range_freeHomOfSections {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (s : I → ↥Γ(M, ⊤)) (U : X.Opens) (i : I) :
    M.val.map ((homOfLE (le_top (a := U))).op : (op (⊤ : X.Opens)) ⟶ op U) (s i) ∈
      Set.range (Scheme.Modules.Hom.app (freeHomOfSections s) U) := by
  refine ⟨Scheme.Modules.Hom.app (SheafOfModules.ιFree i) U (1 : ↥Γ(X, U)), ?_⟩
  have hkey : (SheafOfModules.freeHomEquiv M) (freeHomOfSections s) i =
      (sectionsTopEquiv M).symm (s i) := by
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
  have h2 := congrArg (fun t : M.sections => t.1 (op U)) hkey
  change (SheafOfModules.ιFree i ≫ freeHomOfSections s).val.app (op U) (1 : ↥Γ(X, U)) =
    M.val.map ((homOfLE (le_top (a := U))).op : (op (⊤ : X.Opens)) ⟶ op U) (s i)
  exact h2

/-- The section map associated to a family of global sections is surjective on an open
whenever the restrictions of that family span the target sections there. -/
lemma surjective_app_freeHomOfSections_of_span {X : Scheme.{u}} {I : Type u}
    {M : X.Modules} (s : I → ↥Γ(M, ⊤)) (U : X.Opens)
    (h : Submodule.span ↥Γ(X, U)
      (Set.range (fun i =>
        M.val.map ((homOfLE (le_top (a := U))).op :
          (op (⊤ : X.Opens)) ⟶ op U) (s i))) = ⊤) :
    Function.Surjective (Scheme.Modules.Hom.app (freeHomOfSections s) U) := by
  intro y
  have hspan : Submodule.span ↥Γ(X, U) (Set.range (fun i =>
      M.val.map ((homOfLE (le_top (a := U))).op :
        (op (⊤ : X.Opens)) ⟶ op U) (s i))) ≤
      LinearMap.range
        (PresheafOfModules.Hom.app (freeHomOfSections s).val (op U)).hom := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact restrict_mem_range_freeHomOfSections s U i
  exact hspan (by rw [h]; exact Submodule.mem_top)

/-- Surjectivity of a section map transports across an equality of open subsets.  Keeping
the open equality as an explicit parameter avoids dependent rewriting inside `Γ(-, U)`. -/
lemma surjective_app_of_eq {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (hUV : U = V)
    (h : Function.Surjective (Scheme.Modules.Hom.app φ V)) :
    Function.Surjective (Scheme.Modules.Hom.app φ U) := by
  subst U
  exact h

/-- **Epimorphism criterion for a map out of a free sheaf**: it suffices that, over every
affine open of the base, the restrictions of the defining sections generate. -/
lemma epi_freeHomOfSections_of_span {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (s : I → ↥Γ(M, ⊤))
    (h : ∀ U : X.affineOpens,
      (⊤ : Submodule ↥Γ(X, U.1) ↥Γ(M, U.1)) ≤
        Submodule.span ↥Γ(X, U.1) (Set.range (fun i =>
          M.val.map ((homOfLE (le_top (a := U.1))).op : (op (⊤ : X.Opens)) ⟶ op U.1)
            (s i)))) :
    Epi (freeHomOfSections s) := by
  apply epi_of_surjective_on_affineOpens
  intro U y
  have hspan : Submodule.span ↥Γ(X, U.1) (Set.range (fun i =>
      M.val.map ((homOfLE (le_top (a := U.1))).op : (op (⊤ : X.Opens)) ⟶ op U.1) (s i))) ≤
      LinearMap.range
        (PresheafOfModules.Hom.app (freeHomOfSections s).val (op U.1)).hom := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact restrict_mem_range_freeHomOfSections s U.1 i
  exact hspan (h U Submodule.mem_top)

end Modules

end AlgebraicGeometry.Scheme
