module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksAndModuli.API.GlobalSectionsOverBase
public import StacksAndModuli.API.SheafOfModulesColimits

/-!
# The cohomology long exact sequence, and vanishing transfer along it

`Mathlib/CategoryTheory/Sites/SheafCohomology/` offers only the definition of
`CategoryTheory.Sheaf.H` and its functoriality — no long exact sequence for a short exact
sequence of coefficient sheaves. It is easy to conclude that no such sequence exists and
that every cohomological argument is therefore out of reach. That conclusion is wrong.

`Sheaf.H F n` is *by definition* `Ext ((constantSheaf J AddCommGrpCat).obj (ULift ℤ)) F n`,
and Mathlib has the covariant long exact sequence of `Ext` in the second variable
(`CategoryTheory.Abelian.Ext.covariantSequence` and the pointwise
`covariant_sequence_exact₁'/₂'/₃'`). It applies to `TopCat.Sheaf AddCommGrpCat X` for a
scheme `X` with no extra instances.

Cohomological arguments in the book use that sequence in one shape almost exclusively: two
of three consecutive terms vanish, hence so does the third. This file packages that as three
lemmas, one per position, and derives the corresponding statements for sheaves of *modules*
on a scheme.

## The bridge

Transporting a short exact sequence from `X.Modules` to abelian sheaves needs
`SheafOfModules.toSheaf` to be exact. Mathlib registers `PreservesFiniteLimits` for it but
not `PreservesFiniteColimits`, so `ShortComplex.ShortExact.map_of_exact` does not apply on
its own. The missing colimit instance is supplied by
`StacksAndModuli/API/SheafOfModulesColimits.lean`: sheaves of modules are reflective in presheaves
of modules, and module sheafification followed by forgetting is ordinary abelian
sheafification. Everything here is therefore unconditional.

## Main results

* `AlgebraicGeometry.subsingleton_H_of_shortExact_left`, `…_middle`, `…_right`: vanishing
  transfer along the long exact sequence, at each of the three positions. All proved.
* `AlgebraicGeometry.subsingleton_H_of_iso`: vanishing transfers along an isomorphism of
  sheaves. Proved.
* `AlgebraicGeometry.subsingleton_H_of_retract`: vanishing descends from a sheaf to any
  retract of it. Proved.
* `AlgebraicGeometry.surjective_H_map_of_shortExact_of_subsingleton`: the map on
  cohomology is surjective when the next cohomology group of the kernel vanishes. Proved.
* `AlgebraicGeometry.Scheme.Modules.shortExact_map_toSheaf`: the exactness of
  `SheafOfModules.toSheaf`, in the scheme case. Proved.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_iso`: vanishing transfers along
  an isomorphism of module sheaves. Proved.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_retract`: the corresponding
  retract statement for module sheaves. Proved.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_shortExact_middle`,
  `…_right`: the module-sheaf forms, proved from the two above.
* `AlgebraicGeometry.Scheme.Modules.
  surjective_appTop_of_shortExact_of_subsingleton_H_one`: eventual `H¹` vanishing makes
  the quotient map surjective on global sections.
* `AlgebraicGeometry.Scheme.Modules.
  finite_globalSections_of_shortExact_of_subsingleton_H_one`: finite generation of the
  middle global sections then descends to the quotient.
* `AlgebraicGeometry.Scheme.Modules.
  finite_globalSections_of_epi_of_subsingleton_H_kernel_one`: the same consequence for
  the canonical kernel sequence of an epimorphism.
* `AlgebraicGeometry.Scheme.Modules.exact_appTop_of_shortExact`: global sections preserve
  exactness at the middle term.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Abelian Limits

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- The constant sheaf `ℤ`, the first argument of the `Ext` group that `Sheaf.H` unfolds
to. -/
noncomputable abbrev constantIntSheaf (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf _ AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))

/-- Vanishing of cohomology transfers along an isomorphism of sheaves. -/
theorem subsingleton_H_of_iso {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) (n : ℕ)
    (hF : Subsingleton (F.H n)) : Subsingleton (G.H n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : Sheaf.H.map e.hom n (Sheaf.H.map e.inv n x) = x := by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  rw [← hx, Subsingleton.elim (Sheaf.H.map e.inv n x) 0, map_zero]

/-- Vanishing of sheaf cohomology descends to a retract: if `F ⟶ G ⟶ F`
is the identity and `Hⁿ(G)` vanishes, then `Hⁿ(F)` vanishes. -/
theorem subsingleton_H_of_retract
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (i : F ⟶ G) (p : G ⟶ F) (hip : i ≫ p = 𝟙 F) (n : ℕ)
    (hG : Subsingleton (G.H n)) : Subsingleton (F.H n) := by
  have hi : Function.Injective (Sheaf.H.map i n) := by
    intro x y hxy
    have hxy' := congrArg (fun z ↦ Sheaf.H.map p n z) hxy
    rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      hip, Sheaf.H.map_id_apply, Sheaf.H.map_id_apply] at hxy'
    exact hxy'
  let _ : Subsingleton (G.H n) := hG
  exact hi.subsingleton

/-- Vanishing transfer at the **right** position of the long exact sequence
`H^n(X₁) → H^n(X₂) → H^n(X₃) → H^{n+1}(X₁)`: if `H^n(X₂)` and
`H^{n+1}(X₁)` vanish, so does `H^n(X₃)`.

This is an API lemma used to prove Exercise 2.3.4, that a quotient inherits regularity. -/
theorem subsingleton_H_of_shortExact_right
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₁.H n₁)) :
    Subsingleton (S.X₃.H n₀) := by
  have hex := Abelian.Ext.covariant_sequence_exact₃' (constantIntSheaf X) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      (hS.extClass.postcomp (constantIntSheaf X) h)).hom x = 0 := Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

/-- Vanishing transfer at the **middle** position of the long exact sequence
`H^n(X₁) → H^n(X₂) → H^n(X₃)`: if `H^n(X₁)` and `H^n(X₃)` vanish, so does `H^n(X₂)`.

This is an API lemma used in the induction for Proposition 2.3.5. -/
theorem subsingleton_H_of_shortExact_middle
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) {n : ℕ}
    (h₁ : Subsingleton (S.X₁.H n)) (h₃ : Subsingleton (S.X₃.H n)) :
    Subsingleton (S.X₂.H n) := by
  have hex := Abelian.Ext.covariant_sequence_exact₂' (constantIntSheaf X) hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.g).postcomp (constantIntSheaf X) (add_zero n))).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

/-- Vanishing transfer at the **left** position of the long exact sequence
`H^n(X₃) → H^{n+1}(X₁) → H^{n+1}(X₂)`: if `H^n(X₃)` and `H^{n+1}(X₂)` vanish, so does
`H^{n+1}(X₁)`. -/
theorem subsingleton_H_of_shortExact_left
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₃ : Subsingleton (S.X₃.H n₀)) (h₂ : Subsingleton (S.X₂.H n₁)) :
    Subsingleton (S.X₁.H n₁) := by
  have hex := Abelian.Ext.covariant_sequence_exact₁' (constantIntSheaf X) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.f).postcomp (constantIntSheaf X) (add_zero n₁))).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

/-- In the long exact sequence of a short exact sequence, the map
`H^n(X₂) → H^n(X₃)` is surjective when `H^{n+1}(X₁)` vanishes. -/
theorem surjective_H_map_of_shortExact_of_subsingleton
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (S.X₁.H n₁)) :
    Function.Surjective (Sheaf.H.map S.g n₀) := by
  have hex := Abelian.Ext.covariant_sequence_exact₃' (constantIntSheaf X) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  intro x
  have hx : (AddCommGrpCat.ofHom
      (hS.extClass.postcomp (constantIntSheaf X) h)).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (hex x).mp hx
  exact ⟨y, hy⟩

/-- **`H¹` of the sub vanishes when `H⁰` of the quotient is hit and `H¹` of the middle
vanishes.**  This is the converse direction of
`surjective_H_map_of_shortExact_of_subsingleton` in the same four-term stretch
`H⁰(X₂) → H⁰(X₃) → H¹(X₁) → H¹(X₂)` of the long exact sequence, and it is what turns a
resolution by acyclic sheaves into a vanishing theorem. -/
theorem subsingleton_H_one_of_shortExact_of_surjective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hsurj : Function.Surjective (Sheaf.H.map S.g 0))
    (h₂ : Subsingleton (S.X₂.H 1)) :
    Subsingleton (S.X₁.H 1) := by
  have hex₁ := Abelian.Ext.covariant_sequence_exact₁' (constantIntSheaf X) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hex₁
  have hex₃ := Abelian.Ext.covariant_sequence_exact₃' (constantIntSheaf X) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hex₃
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.f).postcomp (constantIntSheaf X) (add_zero 1))).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex₁ x).mp hgx
  obtain ⟨z, rfl⟩ := hsurj y
  exact (hex₃ _).mpr ⟨z, rfl⟩

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The forgetful functor from sheaves of modules to abelian sheaves is exact, so it
carries short exact sequences to short exact sequences.

Mathlib has `PreservesFiniteLimits` for `SheafOfModules.toSheaf` but not
`PreservesFiniteColimits`, which is what `ShortComplex.ShortExact.map_of_exact` needs; the
missing half is supplied by `StacksAndModuli/API/SheafOfModulesColimits.lean`. -/
theorem shortExact_map_toSheaf
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact :=
  hS.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

/-- Vanishing of sheaf cohomology transfers along an isomorphism of module sheaves. -/
theorem subsingleton_H_of_iso {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    (hM : Subsingleton (((SheafOfModules.toSheaf _).obj M).H n)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj N).H n) :=
  AlgebraicGeometry.subsingleton_H_of_iso
    ((SheafOfModules.toSheaf _).mapIso e) n hM

/-- Vanishing of module-sheaf cohomology descends to a retract. -/
theorem subsingleton_H_of_retract
    {M N : X.Modules} (i : M ⟶ N) (p : N ⟶ M)
    (hip : i ≫ p = 𝟙 M) (n : ℕ)
    (hN : Subsingleton (((SheafOfModules.toSheaf _).obj N).H n)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj M).H n) := by
  apply AlgebraicGeometry.subsingleton_H_of_retract
    ((SheafOfModules.toSheaf _).map i)
    ((SheafOfModules.toSheaf _).map p) _ n hN
  rw [← CategoryTheory.Functor.map_comp, hip,
    CategoryTheory.Functor.map_id]

/-- Vanishing transfer at the right position, for a short exact sequence of sheaves of
modules on a scheme. -/
theorem subsingleton_H_of_shortExact_right
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₂).H n₀))
    (h₁ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H n₁)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj S.X₃).H n₀) :=
  AlgebraicGeometry.subsingleton_H_of_shortExact_right (shortExact_map_toSheaf hS) h h₂ h₁

/-- Vanishing transfer at the middle position, for a short exact sequence of sheaves of
modules on a scheme. -/
theorem subsingleton_H_of_shortExact_middle
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    {n : ℕ}
    (h₁ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H n))
    (h₃ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₃).H n)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj S.X₂).H n) :=
  AlgebraicGeometry.subsingleton_H_of_shortExact_middle (shortExact_map_toSheaf hS) h₁ h₃

/-- The map on module-sheaf cohomology induced by the quotient in a short exact
sequence is surjective when the next cohomology group of the kernel vanishes. -/
theorem surjective_H_map_of_shortExact_of_subsingleton
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H n₁)) :
    Function.Surjective
      (Sheaf.H.map ((SheafOfModules.toSheaf _).map S.g) n₀) :=
  AlgebraicGeometry.surjective_H_map_of_shortExact_of_subsingleton
    (shortExact_map_toSheaf hS) h h₁

/-- In a short exact sequence of module sheaves, the map on global sections is
surjective when `H¹` of the kernel vanishes. -/
theorem surjective_appTop_of_shortExact_of_subsingleton_H_one
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h₁ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H 1)) :
    Function.Surjective (S.g.val.app (Opposite.op ⊤)).hom := by
  have hsurj := surjective_H_map_of_shortExact_of_subsingleton hS rfl h₁
  intro x
  obtain ⟨y, hy⟩ := hsurj
    ((Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₃)
      Limits.isTerminalTop).symm x)
  refine ⟨Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₂)
    Limits.isTerminalTop y, ?_⟩
  have hn := Sheaf.H.equiv₀_naturality
    (f := (SheafOfModules.toSheaf _).map S.g) (hT := Limits.isTerminalTop) y
  rw [hy] at hn
  exact hn.trans (AddEquiv.apply_symm_apply _ x)

/-- In a short exact sequence of module sheaves, finite generation of the middle
global sections descends to the quotient when `H¹` of the kernel vanishes. -/
theorem finite_globalSections_of_shortExact_of_subsingleton_H_one
    {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}
    (hS : S.ShortExact)
    (hfinite :
      letI := globalSectionsModule p S.X₂
      Module.Finite R Γ(S.X₂, ⊤))
    (h₁ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H 1)) :
    letI := globalSectionsModule p S.X₃
    Module.Finite R Γ(S.X₃, ⊤) := by
  let _ := globalSectionsModule p S.X₂
  let _ := globalSectionsModule p S.X₃
  let _ : Module.Finite R Γ(S.X₂, ⊤) := hfinite
  exact Module.Finite.of_surjective (globalSectionsLinearMap p S.g)
    (surjective_appTop_of_shortExact_of_subsingleton_H_one hS h₁)

/-- Finite generation of global sections descends along an epimorphism when
`H¹` of its kernel vanishes. -/
theorem finite_globalSections_of_epi_of_subsingleton_H_kernel_one
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) {M Q : X.Modules}
    (q : M ⟶ Q) [Epi q]
    (hfinite :
      letI := globalSectionsModule p M
      Module.Finite R Γ(M, ⊤))
    (h₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj (kernel q)).H 1)) :
    letI := globalSectionsModule p Q
    Module.Finite R Γ(Q, ⊤) := by
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  apply finite_globalSections_of_shortExact_of_subsingleton_H_one p
    (S := S) { exact := ShortComplex.exact_kernel q } hfinite h₁

/-- **`H¹` of the sub vanishes when the global sections surject and `H¹` of the middle
vanishes**, for a short exact sequence of module sheaves.  This is the exact input the
dimension shift along a resolution by acyclic sheaves needs. -/
theorem subsingleton_H_one_of_shortExact_of_surjective_appTop
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (hsurj : Function.Surjective (S.g.val.app (Opposite.op ⊤)).hom)
    (h₂ : Subsingleton (((SheafOfModules.toSheaf _).obj S.X₂).H 1)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj S.X₁).H 1) := by
  refine AlgebraicGeometry.subsingleton_H_one_of_shortExact_of_surjective
    (shortExact_map_toSheaf hS) (fun x ↦ ?_) h₂
  obtain ⟨u, hu⟩ := hsurj (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₃)
    Limits.isTerminalTop x)
  refine ⟨(Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₂)
    Limits.isTerminalTop).symm u, ?_⟩
  apply (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₃) Limits.isTerminalTop).injective
  have hn := Sheaf.H.equiv₀_naturality (f := (SheafOfModules.toSheaf _).map S.g)
    (hT := Limits.isTerminalTop)
    ((Sheaf.H.equiv₀ ((SheafOfModules.toSheaf _).obj S.X₂) Limits.isTerminalTop).symm u)
  rw [AddEquiv.apply_symm_apply] at hn
  exact hn.symm.trans hu

/-- Global sections are left exact: a short exact sequence of module sheaves remains
exact at its middle term after evaluating on the top open. -/
theorem exact_appTop_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact) :
    Function.Exact (S.f.val.app (Opposite.op ⊤)).hom
      (S.g.val.app (Opposite.op ⊤)).hom := by
  let S' := S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  have hS' : S'.ShortExact := shortExact_map_toSheaf hS
  have hex := Abelian.Ext.covariant_sequence_exact₂'
    (constantIntSheaf X) hS' 0
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  change Function.Exact (S'.f.hom.app (Opposite.op ⊤)).hom
    (S'.g.hom.app (Opposite.op ⊤)).hom
  apply Function.Exact.of_ladder_addEquiv_of_exact
    (Sheaf.H.equiv₀ S'.X₁ Limits.isTerminalTop)
    (Sheaf.H.equiv₀ S'.X₂ Limits.isTerminalTop)
    (Sheaf.H.equiv₀ S'.X₃ Limits.isTerminalTop)
  · ext x
    exact Sheaf.H.equiv₀_naturality
      (f := S'.f) (hT := Limits.isTerminalTop) x
  · ext x
    exact Sheaf.H.equiv₀_naturality
      (f := S'.g) (hT := Limits.isTerminalTop) x
  · exact hex

end Scheme.Modules

end AlgebraicGeometry
