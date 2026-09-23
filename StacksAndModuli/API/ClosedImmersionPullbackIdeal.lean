module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The ideal of a pullback of closed immersions

The scheme-theoretic pullback of two closed subschemes is the closed subscheme
cut out by the sum of their ideal sheaves.  This file records the statement
directly for arbitrary closed immersions, without first replacing them by their
canonical subscheme presentations.

## Main result

* `AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_comp_eq_sup`: the ideal sheaf
  of the intersection is the sum of the two ideal sheaves.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

/-- The composite from the pullback of two closed immersions to their common
target is cut out by the sum of the two kernel ideal sheaves. -/
theorem Hom.ker_pullback_fst_comp_eq_sup (i : X ⟶ S) (j : Y ⟶ S)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (pullback.fst i j ≫ i).ker = i.ker ⊔ j.ker := by
  let K : S.IdealSheafData := i.ker ⊔ j.ker
  let p : pullback i j ⟶ S := pullback.fst i j ≫ i
  have hiK : i.ker ≤ K := le_sup_left
  have hjK : j.ker ≤ K := le_sup_right
  let a : K.subscheme ⟶ X :=
    IsClosedImmersion.lift i K.subschemeι (by simpa using hiK)
  let b : K.subscheme ⟶ Y :=
    IsClosedImmersion.lift j K.subschemeι (by simpa using hjK)
  have hab : a ≫ i = b ≫ j := by
    rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac]
  let e : K.subscheme ⟶ pullback i j := pullback.lift a b hab
  have hKp : K ≤ p.ker := by
    apply sup_le
    · exact (pullback.fst i j).le_ker_comp i
    · change j.ker ≤ (pullback.fst i j ≫ i).ker
      rw [pullback.condition]
      exact (pullback.snd i j).le_ker_comp j
  let eInv : pullback i j ⟶ K.subscheme :=
    IsClosedImmersion.lift K.subschemeι p (by simpa using hKp)
  have he : e ≫ p = K.subschemeι := by
    change (pullback.lift a b hab ≫ pullback.fst i j) ≫ i = K.subschemeι
    rw [pullback.lift_fst, IsClosedImmersion.lift_fac]
  have heInv : eInv ≫ K.subschemeι = p := by
    exact IsClosedImmersion.lift_fac K.subschemeι p (by simpa using hKp)
  have h_e_eInv : e ≫ eInv = 𝟙 _ := by
    apply (cancel_mono K.subschemeι).1
    rw [Category.assoc, heInv, he, Category.id_comp]
  have h_eInv_e : eInv ≫ e = 𝟙 _ := by
    apply (cancel_mono p).1
    rw [Category.assoc, he, heInv, Category.id_comp]
  let _ : IsIso e := ⟨⟨eInv, h_e_eInv, h_eInv_e⟩⟩
  change p.ker = K
  rw [← Hom.ker_comp_of_isIso e p, he, K.ker_subschemeι]

end AlgebraicGeometry.Scheme

end
