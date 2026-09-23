module

public import StacksAndModuli.API.SheafCohomologyFlasque

/-!
# The long exact sequence of site-local sheaf cohomology

`StacksAndModuli/API/SheafCohomologyLES.lean` records the vanishing transfers along the long exact
sequence of *global* cohomology `Hⁿ(X, -)`.  This file records the two transfers along the
same sequence for the cohomology `H'ⁿ(U, -)` of a **fixed open** `U`, which is what a
Mayer–Vietoris or Čech computation over an affine cover consumes.

Both are the arguments already used for a flasque sheaf in
`StacksAndModuli/API/SheafCohomologyFlasque.lean`, with the flasqueness replaced by the hypotheses
it was there used to supply.

* `subsingleton_HPrime_one_of_shortExact_of_surjective`: `H'¹(U, X₁) = 0` when `X₂(U) ↠ X₃(U)`
  and `H'¹(U, X₂) = 0`.
* `subsingleton_HPrime_succ_of_shortExact`: `H'ⁱ⁺²(U, X₁) = 0` when `H'ⁱ⁺¹(U, X₃) = 0` and
  `H'ⁱ⁺²(U, X₂) = 0` — the dimension shift.
* `surjective_app_of_shortExact_of_subsingleton_HPrime_one`: the converse of the first —
  `X₂(U) ↠ X₃(U)` when `H'¹(U, X₁) = 0`.  This is what makes sections over an *affine* open
  exact, and hence what a graded model of a quotient sheaf needs on each chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

/-- **`H'¹(U, X₁)` vanishes when sections over `U` surject and `H'¹(U, X₂)` vanishes.** -/
theorem subsingleton_HPrime_one_of_shortExact_of_surjective
    (hS : S.ShortExact) (U : Opens X)
    (hsurj : Function.Surjective (S.g.hom.app (op U)))
    (h₂ : Subsingleton (S.X₂.H' 1 U)) :
    Subsingleton (S.X₁.H' 1 U) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let K := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  have hxI : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    @Subsingleton.elim _ h₂ _ 0
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ K hS x hxI rfl
  obtain ⟨t, ht⟩ := hsurj (HPrimeEquivZero S.X₃ U x₃)
  let y : S.X₂.H' 0 U := (HPrimeEquivZero S.X₂ U).symm t
  have hy : y.comp (Ext.mk₀ S.g) (add_zero 0) = x₃ := by
    apply (HPrimeEquivZero S.X₃ U).injective
    rw [← HPrimeEquivZero_naturality (f := S.g) (U := U)]
    simpa [y] using ht
  have hz : (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0 := by
    calc
      (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl =
          y.comp ((Ext.mk₀ S.g).comp hS.extClass rfl) rfl := by
            apply Ext.comp_assoc
            all_goals omega
      _ = 0 := by rw [hS.comp_extClass]; simp
  rw [← hx₃, ← hy]
  exact hz

/-- **Sections over `U` surject when `H'¹(U, X₁)` vanishes.**  The converse of
`subsingleton_HPrime_one_of_shortExact_of_surjective`, and the direction that matters on an
affine open, where the vanishing is a theorem. -/
theorem surjective_app_of_shortExact_of_subsingleton_HPrime_one
    (hS : S.ShortExact) (U : Opens X)
    (h₁ : Subsingleton (S.X₁.H' 1 U)) :
    Function.Surjective (S.g.hom.app (op U)) := by
  let K := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  have hex := Ext.covariant_sequence_exact₃' K hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  intro t
  set x₃ : S.X₃.H' 0 U := (HPrimeEquivZero S.X₃ U).symm t with hx₃
  have hzero : (AddCommGrpCat.ofHom (hS.extClass.postcomp K rfl)).hom x₃ = 0 :=
    @Subsingleton.elim _ h₁ _ 0
  obtain ⟨y, hy⟩ := (hex x₃).mp hzero
  refine ⟨HPrimeEquivZero S.X₂ U y, ?_⟩
  rw [HPrimeEquivZero_naturality]
  rw [show Ext.comp y (Ext.mk₀ S.g) (add_zero 0) = x₃ from hy, hx₃, Equiv.apply_symm_apply]

/-- **The dimension shift for the cohomology of a fixed open.** -/
theorem subsingleton_HPrime_succ_of_shortExact
    (hS : S.ShortExact) (U : Opens X) (i : ℕ)
    (h₃ : Subsingleton (S.X₃.H' (i + 1) U))
    (h₂ : Subsingleton (S.X₂.H' (i + 2) U)) :
    Subsingleton (S.X₁.H' (i + 2) U) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let K := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  have hxI : x.comp (Ext.mk₀ S.f) (add_zero (i + 2)) = 0 :=
    @Subsingleton.elim _ h₂ _ 0
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ K hS x hxI rfl
  rw [← hx₃, @Subsingleton.elim _ h₃ x₃ 0, Ext.zero_comp]

/-- Vanishing of site-local cohomology transfers along an isomorphism of sheaves. -/
theorem subsingleton_HPrime_of_iso {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G)
    (n : ℕ) (U : Opens X) (hF : Subsingleton (F.H' n U)) :
    Subsingleton (G.H' n U) := by
  let φ := ((cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).mapIso e).app (op U)
  have hsurj : Function.Surjective φ.hom := by
    intro y
    exact ⟨φ.inv y, by rw [← ConcreteCategory.comp_apply, φ.inv_hom_id,
      ConcreteCategory.id_apply]⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  rw [@Subsingleton.elim _ hF a' b']

end CategoryTheory.Sheaf
