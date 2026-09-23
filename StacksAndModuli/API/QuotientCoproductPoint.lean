module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.3-quotient-stacks-of-groupoids»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»

/-!
# Quotient-prestack points over coproducts

A quotient-prestack object is a point of the groupoid's object presheaf.  If that
presheaf is a Zariski sheaf, points over an arbitrary family of schemes glue uniquely
to a point over their coproduct.  The identity relations give the corresponding
cartesian coproduct cocone in the quotient prestack.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}}

/-- Points of a quotient prestack over a family of schemes extend to their
coproduct when the object presheaf is a Zariski sheaf. -/
theorem exists_quotientCoproductCocone
    (hU : Presieve.IsSheaf Scheme.zariskiTopology 𝒢.U)
    {ι : Type u} (U : ι → Scheme.{u})
    (x : ι → 𝒢.quotientPrestack.obj)
    (hx : ∀ j, (x j).base = U j) :
    ∃ (a : 𝒢.quotientPrestack.obj), a.base = ∐ U ∧
      ∀ j, ∃ r : x j ⟶ a,
        IsHomLift 𝒢.quotientProj (Sigma.ι U j) r := by
  let localPoint : ∀ j, 𝒢.U.obj (op (U j)) := fun j ↦
    𝒢.U.map (eqToHom (hx j).symm).op (x j).pt
  have hbij := bijective_sigma_of_isSheaf_zariskiTopology 𝒢.U hU U
  obtain ⟨pt, hpt⟩ := hbij.2 localPoint
  let a : 𝒢.quotientPrestack.obj := ⟨∐ U, pt⟩
  refine ⟨a, rfl, fun j ↦ ?_⟩
  let f : (x j).base ⟶ ∐ U := eqToHom (hx j) ≫ Sigma.ι U j
  let r : x j ⟶ a :=
    { hom := f
      rel := 𝒢.e.app (op (x j).base) (x j).pt
      s_rel := 𝒢.s_app_e_app _
      t_rel := by
        rw [𝒢.t_app_e_app]
        dsimp only [f, a]
        rw [op_comp, Functor.map_comp_apply]
        have hj : 𝒢.U.map (Sigma.ι U j).op pt = localPoint j :=
          congrFun hpt j
        rw [hj]
        dsimp only [localPoint]
        simp }
  refine ⟨r, ?_⟩
  apply IsHomLift.of_fac' 𝒢.quotientProj (Sigma.ι U j) r (hx j) rfl
  dsimp only [r, f, quotientProj]
  simp

end AlgebraicGeometry.PresheafGroupoid
