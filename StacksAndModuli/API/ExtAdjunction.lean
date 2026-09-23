module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Ext and exact adjunctions

An adjunction `L ⊣ R` induces an additive equivalence
`Ext (L.obj X) Y n ≃+ Ext X (R.obj Y) n` when the left adjoint preserves
monomorphisms, the right adjoint is exact, and the target of the left adjoint
has enough injectives.

The comparison first applies the exact functor `R` to an Ext class and then
precomposes with the adjunction unit.  Bijectivity follows by dimension shifting
along a canonical injective presentation.

When the left adjoint is exact as well, the opposite comparison applies `L` and
postcomposes with the counit.  This map is also bijective.  Its explicit formula is
the form needed for canonical cohomology maps from a pushforward.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe wC wD vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D] [HasExt.{wC} C] [HasExt.{wD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The canonical map on `Ext` associated to an exact right adjoint: apply the
right adjoint to the Ext class, then precompose with the adjunction unit. -/
noncomputable def extAddHom (X : C) (Y : D) (n : ℕ) :
    Ext (L.obj X) Y n →+ Ext X (R.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (R.obj Y) (zero_add n)).comp
    (R.mapExtAddHom (L.obj X) Y n)

@[simp]
lemma extAddHom_apply (X : C) (Y : D) (n : ℕ) (x : Ext (L.obj X) Y n) :
    adj.extAddHom X Y n x =
      (Ext.mk₀ (adj.unit.app X)).comp (x.mapExactFunctor R) (zero_add n) := rfl

section AdditiveLeft

variable [L.Additive]

/-- In degree zero, the Ext comparison is the ordinary additive hom-set
adjunction transported across `Ext.addEquiv₀`. -/
noncomputable def extAddEquivZero (X : C) (Y : D) :
    Ext (L.obj X) Y 0 ≃+ Ext X (R.obj Y) 0 :=
  Ext.addEquiv₀.trans (adj.homAddEquiv X Y) |>.trans Ext.addEquiv₀.symm

/-- The canonical Ext comparison agrees with the ordinary adjunction in degree
zero. -/
lemma extAddHom_zero_eq (X : C) (Y : D) :
    adj.extAddHom X Y 0 = (adj.extAddEquivZero X Y).toAddMonoidHom := by
  ext x
  apply Ext.addEquiv₀.injective
  simp only [extAddHom_apply, extAddEquivZero]
  rw [Ext.mapExactFunctor₀]
  simp only [Function.comp_apply]
  rw [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀]
  change Ext.addEquiv₀ (Ext.mk₀
      (adj.unit.app X ≫ R.map (Ext.addEquiv₀ x))) =
    Ext.addEquiv₀ (Ext.addEquiv₀.symm
      (adj.homAddEquiv X Y (Ext.addEquiv₀ x)))
  rw [← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact (adj.homEquiv_unit X Y (Ext.addEquiv₀ x)).symm

end AdditiveLeft

/-- The Ext comparison commutes with postcomposition by a degree-zero class. -/
lemma extAddHom_postcomp_mk₀ (X : C) {Y Z : D} (f : Y ⟶ Z)
    (n : ℕ) (x : Ext (L.obj X) Y n) :
    adj.extAddHom X Z n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (adj.extAddHom X Y n x).comp (Ext.mk₀ (R.map f)) (add_zero n) := by
  simp only [extAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc (Ext.mk₀ (adj.unit.app X))
    (x.mapExactFunctor R) (Ext.mk₀ (R.map f))
    (zero_add n) (add_zero n) (by omega)).symm

/-- The Ext comparison commutes with the connecting morphism of a short exact
sequence. -/
lemma extAddHom_postcomp_extClass (X : C) {S : ShortComplex D}
    (hS : S.ShortExact) (n : ℕ) (x : Ext (L.obj X) S.X₃ n) :
    adj.extAddHom X S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (adj.extAddHom X S.X₃ n x).comp
        (hS.map_of_exact R).extClass rfl := by
  simp only [extAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ (adj.unit.app X))
    (x.mapExactFunctor R) (hS.map_of_exact R).extClass
    (zero_add n) rfl (by omega)).symm

section Bijective

variable [L.Additive] [L.PreservesMonomorphisms] [EnoughInjectives D]

attribute [local instance] Ext.subsingleton_of_injective in
/-- The canonical Ext comparison associated to an exact adjunction is
bijective in every degree. -/
theorem extAddHom_bijective (X : C) (Y : D) (n : ℕ) :
    Function.Bijective (adj.extAddHom X Y n) := by
  let _ : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing Y with
  | zero =>
      rw [adj.extAddHom_zero_eq X Y]
      exact (adj.extAddEquivZero X Y).bijective
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have : Injective (S.map R).X₂ :=
        Functor.PreservesInjectiveObjects.injective_obj I.injective
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
        (adj.extAddHom X S.X₂ n) (adj.extAddHom X S.X₃ n)
        (adj.extAddHom X S.X₁ (n + 1))
        (by
          ext x
          exact (adj.extAddHom_postcomp_mk₀ X S.g n x).symm)
        (by
          ext x
          exact (adj.extAddHom_postcomp_extClass X hS n x).symm)
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X (hS.map_of_exact R) n (n + 1) rfl))
        (hn _).surjective (hn _)
        (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
        (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁
          (by subsingleton) rfl)

/-- The additive Ext adjunction for a monomorphism-preserving left adjoint and
an exact right adjoint. -/
noncomputable def extAddEquiv (X : C) (Y : D) (n : ℕ) :
    Ext (L.obj X) Y n ≃+ Ext X (R.obj Y) n :=
  AddEquiv.ofBijective (adj.extAddHom X Y n)
    (adj.extAddHom_bijective X Y n)

@[simp]
lemma extAddEquiv_apply (X : C) (Y : D) (n : ℕ)
    (x : Ext (L.obj X) Y n) :
    adj.extAddEquiv X Y n x = adj.extAddHom X Y n x := rfl

/-- The additive Ext adjunction is natural in the covariant coefficient
object. -/
lemma extAddEquiv_postcomp_mk₀ (X : C) {Y Z : D} (f : Y ⟶ Z)
    (n : ℕ) (x : Ext (L.obj X) Y n) :
    adj.extAddEquiv X Z n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (adj.extAddEquiv X Y n x).comp (Ext.mk₀ (R.map f)) (add_zero n) :=
  adj.extAddHom_postcomp_mk₀ X f n x

end Bijective

section CounitComparison

variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- The opposite-direction Ext comparison associated to the counit of an exact
adjunction: apply the exact left adjoint to the Ext class, then postcompose with
the adjunction counit. -/
noncomputable def extAddHomInv (X : C) (Y : D) (n : ℕ) :
    Ext X (R.obj Y) n →+ Ext (L.obj X) Y n :=
  ((Ext.mk₀ (adj.counit.app Y)).postcomp (L.obj X) (add_zero n)).comp
    (L.mapExtAddHom X (R.obj Y) n)

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
@[simp]
lemma extAddHomInv_apply (X : C) (Y : D) (n : ℕ)
    (x : Ext X (R.obj Y) n) :
    adj.extAddHomInv X Y n x =
      (x.mapExactFunctor L).comp
        (Ext.mk₀ (adj.counit.app Y)) (add_zero n) := rfl

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- In degree zero, the counit comparison is the inverse of the ordinary
additive hom-set adjunction. -/
lemma extAddHomInv_zero_eq (X : C) (Y : D) :
    adj.extAddHomInv X Y 0 =
      (adj.extAddEquivZero X Y).symm.toAddMonoidHom := by
  ext x
  apply Ext.addEquiv₀.injective
  simp only [extAddHomInv_apply]
  rw [Ext.mapExactFunctor₀]
  simp only [Function.comp_apply]
  rw [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀]
  have hleft : Ext.addEquiv₀
      (Ext.mk₀ (L.map (Ext.homEquiv₀ x) ≫ adj.counit.app Y)) =
      L.map (Ext.homEquiv₀ x) ≫ adj.counit.app Y :=
    Ext.homEquiv₀.apply_symm_apply _
  have hright : Ext.addEquiv₀
      ((adj.extAddEquivZero X Y).symm.toAddMonoidHom x) =
      (adj.homAddEquiv X Y).symm (Ext.homEquiv₀ x) := by
    simp only [extAddEquivZero, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, homAddEquiv_symm_apply]
    exact Ext.homEquiv₀.apply_symm_apply _
  refine hleft.trans ?_
  exact (adj.homEquiv_counit X Y (Ext.homEquiv₀ x)).symm.trans
    hright.symm

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- The counit comparison commutes with postcomposition by a degree-zero
class. -/
lemma extAddHomInv_postcomp_mk₀ (X : C) {Y Z : D} (f : Y ⟶ Z)
    (n : ℕ) (x : Ext X (R.obj Y) n) :
    adj.extAddHomInv X Z n
        (x.comp (Ext.mk₀ (R.map f)) (add_zero n)) =
      (adj.extAddHomInv X Y n x).comp
        (Ext.mk₀ f) (add_zero n) := by
  simp only [extAddHomInv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  have hc : L.map (R.map f) ≫ adj.counit.app Z =
      adj.counit.app Y ≫ f := by
    exact adj.counit.naturality f
  calc
    ((x.mapExactFunctor L).comp (Ext.mk₀ (L.map (R.map f)))
        (add_zero n)).comp (Ext.mk₀ (adj.counit.app Z)) (add_zero n) =
      (x.mapExactFunctor L).comp
        ((Ext.mk₀ (L.map (R.map f))).comp
          (Ext.mk₀ (adj.counit.app Z)) (zero_add 0)) (add_zero n) :=
      Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = (x.mapExactFunctor L).comp
        (Ext.mk₀ (L.map (R.map f) ≫ adj.counit.app Z)) (add_zero n) := by
      rw [Ext.mk₀_comp_mk₀]
    _ = (x.mapExactFunctor L).comp
        (Ext.mk₀ (adj.counit.app Y ≫ f)) (add_zero n) := by
      rw [hc]
    _ = ((x.mapExactFunctor L).comp
          (Ext.mk₀ (adj.counit.app Y)) (add_zero n)).comp
        (Ext.mk₀ f) (add_zero n) := by
      rw [← Ext.mk₀_comp_mk₀]
      exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

/-- The counit comparison commutes with the connecting morphism of a short
exact sequence. -/
lemma extAddHomInv_postcomp_extClass (X : C) {S : ShortComplex D}
    (hS : S.ShortExact) (n : ℕ) (x : Ext X (R.obj S.X₃) n) :
    adj.extAddHomInv X S.X₁ (n + 1)
        (x.comp (hS.map_of_exact R).extClass rfl) =
      (adj.extAddHomInv X S.X₃ n x).comp hS.extClass rfl := by
  simp only [extAddHomInv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  rw [Ext.comp_assoc_of_second_deg_zero]
  let τ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := by exact (adj.counit.naturality S.f).symm
      comm₂₃ := by exact (adj.counit.naturality S.g).symm }
  have hn := ShortComplex.ShortExact.extClass_naturality
    ((hS.map_of_exact R).map_of_exact L) hS τ
  calc
    ((x.mapExactFunctor L).comp
        ((hS.map_of_exact R).map_of_exact L).extClass rfl).comp
          (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero (n + 1)) =
      (x.mapExactFunctor L).comp
        (((hS.map_of_exact R).map_of_exact L).extClass.comp
          (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero 1)) rfl :=
      Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = (x.mapExactFunctor L).comp
        ((Ext.mk₀ (adj.counit.app S.X₃)).comp hS.extClass
          (zero_add 1)) rfl :=
      congrArg (fun q ↦ (x.mapExactFunctor L).comp q rfl) hn

variable [L.PreservesMonomorphisms] [EnoughInjectives D]

attribute [local instance] Ext.subsingleton_of_injective in
/-- The counit Ext comparison of an exact adjunction is bijective in every
degree. -/
theorem extAddHomInv_bijective (X : C) (Y : D) (n : ℕ) :
    Function.Bijective (adj.extAddHomInv X Y n) := by
  let _ : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing Y with
  | zero =>
      rw [adj.extAddHomInv_zero_eq X Y]
      exact (adj.extAddEquivZero X Y).symm.bijective
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have : Injective (S.map R).X₂ :=
        Functor.PreservesInjectiveObjects.injective_obj I.injective
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
        (adj.extAddHomInv X S.X₂ n) (adj.extAddHomInv X S.X₃ n)
        (adj.extAddHomInv X S.X₁ (n + 1))
        (by
          ext x
          exact (adj.extAddHomInv_postcomp_mk₀ X S.g n x).symm)
        (by
          ext x
          exact (adj.extAddHomInv_postcomp_extClass X hS n x).symm)
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X
            (hS.map_of_exact R) n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
        (hn _).surjective (hn _)
        (fun x₁ ↦ Ext.covariant_sequence_exact₁ _
          (hS.map_of_exact R) x₁ (by subsingleton) rfl)
        (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS y₁
          (by subsingleton) rfl)

/-- The additive equivalence obtained from the counit comparison of an exact
adjunction. -/
noncomputable def extAddEquivInv (X : C) (Y : D) (n : ℕ) :
    Ext X (R.obj Y) n ≃+ Ext (L.obj X) Y n :=
  AddEquiv.ofBijective (adj.extAddHomInv X Y n)
    (adj.extAddHomInv_bijective X Y n)

@[simp]
lemma extAddEquivInv_apply (X : C) (Y : D) (n : ℕ)
    (x : Ext X (R.obj Y) n) :
    adj.extAddEquivInv X Y n x = adj.extAddHomInv X Y n x := rfl

end CounitComparison

end CategoryTheory.Adjunction
