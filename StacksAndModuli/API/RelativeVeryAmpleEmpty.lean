module

public import StacksAndModuli.API.RelativeVeryAmplePullback

/-!
# Relative very ampleness on an empty scheme

Every sheaf of modules on an empty scheme is the zero object.  Pulling the universal
rank-one quotient of the free projective bundle back along the unique map from an empty
scheme therefore identifies it with any prescribed sheaf.  This supplies the empty branch
needed when a fixed-Hilbert-polynomial Quot functor has no points on nonempty test schemes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private lemma modules_isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (M : X.Modules) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply Modules.hom_ext _ _ fun U ↦ ?_
  have hU : U = ⊥ := Subsingleton.elim _ _
  subst U
  let N : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  letI : Subsingleton Γ(M, ⊥) := by
    refine ⟨fun a b ↦ ?_⟩
    exact N.eq_of_locally_eq' (fun i : PEmpty.{u + 1} ↦ ⊥) ⊥
      (fun _ ↦ homOfLE le_rfl) (by simp) a b (fun i ↦ i.elim)
  ext x
  exact Subsingleton.elim _ _

/-- Every sheaf of modules on an empty scheme is relatively very ample over every base.
The classifying immersion is the unique map to the free rank-one projective bundle. -/
theorem isRelativelyVeryAmple_of_isEmpty
    {X S : Scheme.{u}} [IsEmpty X] (f : X ⟶ S) (L : X.Modules) :
    IsRelativelyVeryAmple f L := by
  letI : IsEmpty (Over.mk f).left := by
    change IsEmpty X
    infer_instance
  let E : S.Modules :=
    SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin 1))
  let P : Over S := grassmannianOverRepresentation S 1 1
  let repr : (Modules.grassmannianOverFunctor 1 E).RepresentableBy P :=
    freeGrassmannianRepresentableBy S 1 1
  let hX : IsInitial X := isInitialOfIsEmpty
  let t : Over.mk f ⟶ P :=
    Over.homMk (hX.to P.left) (hX.hom_ext _ _)
  have ht : IsImmersion t.left := by
    dsimp only [t]
    infer_instance
  let x : Modules.PullbackQuotient 1 E (Over.mk f) :=
    (repr.homEquiv t).out
  have hx : Quotient.mk (Modules.PullbackQuotient.setoid 1 E (Over.mk f)) x =
      repr.homEquiv t :=
    Quotient.out_eq _
  have hx0 : IsZero x.Q := modules_isZero_of_isEmpty x.Q
  have hL0 : IsZero L := modules_isZero_of_isEmpty L
  exact ⟨E, inferInstance, Modules.free_isFiniteLocallyFree S 1,
    P, repr, t, ht, x, hx, ⟨hx0.isoZero ≪≫ hL0.isoZero.symm⟩⟩

end AlgebraicGeometry.Scheme

end

end
