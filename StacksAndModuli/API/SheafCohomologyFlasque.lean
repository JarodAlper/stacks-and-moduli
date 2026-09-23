module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksAndModuli.API.SheafCohomologyTerminal
public import StacksAndModuli.API.InjectiveSheafFlasque

/-!
# Cohomology of a flasque sheaf, on every open

A flasque sheaf of abelian groups has vanishing cohomology in every positive degree **on
every open**, not merely globally. The degree-one case uses the canonical injective
presentation: flasqueness makes the map on sections over `U` onto, and the first part of the
long exact `Ext` sequence kills every degree-one class. The higher degrees follow by
dimension shifting.

The *global* statement `Hⁿ⁺¹(X, F) = 0` is `TopCat.Sheaf.subsingleton_H_of_isFlasque` in
`StacksAndModuli/API/FlasqueVanishing.lean`, proved there from the long exact sequence of global
cohomology; this file's `subsingleton_HPrime_succ_of_isFlasque` is the refinement to an
arbitrary open, which is what a Mayer–Vietoris or Čech computation needs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}}

/-- Degree-zero site-local sheaf cohomology is equivalent, as a type, to evaluation of
the coefficient sheaf on the given open. -/
noncomputable def HPrimeEquivZero
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    F.H' 0 U ≃ F.obj.obj (op U) :=
  Ext.addEquiv₀.toEquiv.trans
    (freeAbelianYonedaCorepresentableBy (Opens.grothendieckTopology X) U).homEquiv

/-- The degree-zero site-local cohomology equivalence is natural in the coefficient
sheaf. -/
theorem HPrimeEquivZero_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (U : Opens X) (x : F.H' 0 U) :
    f.hom.app (op U) (HPrimeEquivZero F U x) =
      HPrimeEquivZero G U (x.comp (Ext.mk₀ f) (add_zero 0)) := by
  simp only [HPrimeEquivZero, Equiv.trans_apply]
  have h₀ : Ext.addEquiv₀
      (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
    apply (Ext.mk₀_bijective _ G).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀,
      Ext.mk₀_addEquiv₀_apply]
  calc
    _ = (freeAbelianYonedaCorepresentableBy
        (Opens.grothendieckTopology X) U).homEquiv (Ext.addEquiv₀ x ≫ f) :=
      ((freeAbelianYonedaCorepresentableBy
        (Opens.grothendieckTopology X) U).homEquiv_comp f _).symm
    _ = (freeAbelianYonedaCorepresentableBy
        (Opens.grothendieckTopology X) U).homEquiv
          (Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0))) :=
      congrArg ((freeAbelianYonedaCorepresentableBy
        (Opens.grothendieckTopology X) U).homEquiv (Y := G)) h₀.symm

/-- The degree-one cohomology presheaf of a flasque sheaf vanishes on every open. -/
theorem subsingleton_HPrime_one_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : Opens X) : Subsingleton (F.H' 1 U) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let K := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  let i := Injective.ι F
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  have hxI : x.comp (Ext.mk₀ i) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ K hS x hxI rfl
  have hg : Function.Surjective (S.g.hom.app (op U)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS)
  obtain ⟨t, ht⟩ := hg (HPrimeEquivZero S.X₃ U x₃)
  let y : S.X₂.H' 0 U := (HPrimeEquivZero S.X₂ U).symm t
  have hy : y.comp (Ext.mk₀ S.g) (add_zero 0) = x₃ := by
    apply (HPrimeEquivZero S.X₃ U).injective
    rw [← HPrimeEquivZero_naturality (f := S.g) (U := U)]
    simpa [y] using ht
  have hz : (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp
      hS.extClass rfl = 0 := by
    calc
      (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl =
          y.comp ((Ext.mk₀ S.g).comp hS.extClass rfl) rfl := by
            apply Ext.comp_assoc
            all_goals omega
      _ = 0 := by rw [hS.comp_extClass]; simp
  rw [← hx₃, ← hy]
  exact hz

/-- **A flasque sheaf of abelian groups has vanishing higher cohomology on every open.**

Dimension shifting: embed `F` in an injective sheaf `I`, which is flasque
(`isFlasque_of_injective`); the quotient `Q` is then flasque
(`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`), and the covariant `Ext` long exact
sequence identifies `H'^{i+2}(F, U)` with a quotient of `H'^{i+1}(Q, U)`, which vanishes by
induction. The base case is `subsingleton_HPrime_one_of_isFlasque`. -/
theorem subsingleton_HPrime_succ_of_isFlasque :
    ∀ (i : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (U : Opens X),
      Subsingleton (F.H' (i + 1) U) := by
  intro i
  induction i with
  | zero => intro F _ U; exact subsingleton_HPrime_one_of_isFlasque F U
  | succ i ih =>
      intro F _ U
      apply subsingleton_of_forall_eq 0
      intro x
      let K := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)
      let ι := Injective.ι F
      let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
      haveI : S.X₂.IsFlasque := TopCat.Sheaf.isFlasque_of_injective _
      haveI : S.X₃.IsFlasque := TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
      have hxI : x.comp (Ext.mk₀ S.f) (add_zero (i + 1 + 1)) = 0 :=
        Ext.eq_zero_of_injective _
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ K hS x hxI rfl
      have hz : x₃ = 0 := @Subsingleton.elim _ (ih S.X₃ U) x₃ 0
      rw [← hx₃, hz, Ext.zero_comp]

/-- A flasque sheaf of abelian groups has vanishing first sheaf cohomology. -/
theorem subsingleton_H_one_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    Subsingleton (F.H 1) :=
  (subsingleton_HPrime_terminal_iff (Opens.grothendieckTopology X) F 1
    Limits.isTerminalTop).1 (subsingleton_HPrime_one_of_isFlasque F ⊤)

/-- The degree-one cohomology presheaf of a flasque sheaf vanishes on the top open. -/
theorem subsingleton_HPrime_one_top_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    Subsingleton (F.H' 1 (⊤ : Opens X)) :=
  subsingleton_HPrime_one_of_isFlasque F ⊤

end CategoryTheory.Sheaf
