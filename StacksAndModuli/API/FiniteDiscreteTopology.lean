module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Finite discrete spaces in scheme and sheaf theory

This file packages two elementary consequences of discreteness used by the
component-generic resolution.  A morphism whose source is a finite discrete
scheme is affine, and an additive sheaf on a discrete space is flasque.

## Main results

* `AlgebraicGeometry.isAffineHom_of_finite_of_discreteTopology`: every morphism
  from a finite discrete scheme is affine.
* `TopCat.Sheaf.isFlasque_of_discreteTopology`: every sheaf of abelian groups on
  a discrete space is flasque.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Every morphism from a finite discrete scheme is affine. -/
theorem isAffineHom_of_finite_of_discreteTopology
    [Finite X] [DiscreteTopology X] (f : X ⟶ Y) : IsAffineHom f := by
  constructor
  intro U _
  change IsAffine (f ⁻¹ᵁ U).toScheme
  let _ : Finite (f ⁻¹ᵁ U).toScheme :=
    Finite.of_injective (f ⁻¹ᵁ U).ι (by
      intro x y h
      exact Subtype.ext h)
  let _ : DiscreteTopology (f ⁻¹ᵁ U).toScheme :=
    DiscreteTopology.of_continuous_injective (f ⁻¹ᵁ U).ι.continuous (by
      intro x y h
      exact Subtype.ext h)
  infer_instance

end AlgebraicGeometry

namespace TopCat.Sheaf

variable {T : TopCat.{u}}

/-- A sheaf of abelian groups on a discrete space is flasque.

To extend a section from `V` to `U`, glue it with the zero section on the open
complement `U \ V`. -/
theorem isFlasque_of_discreteTopology
    [DiscreteTopology T] (F : Sheaf AddCommGrpCat.{u} T) : F.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    let C : Opens T :=
      ⟨(U.unop : Set T) \ V.unop, isOpen_discrete _⟩
    have hCU : C ≤ U.unop := fun _ hx ↦ hx.1
    have hcover : U.unop ≤ V.unop ⊔ C := by
      intro x hx
      by_cases hxV : x ∈ V.unop
      · exact Or.inl hxV
      · exact Or.inr ⟨hx, hxV⟩
    let W : Fin 2 → Opens T := ![V.unop, C]
    let sf : (j : Fin 2) → F.obj.obj (Opposite.op (W j))
      | 0 => s
      | 1 => 0
    have hBC : V.unop ⊓ C = ⊥ := by
      ext x
      simp [C]
    have hCB : C ⊓ V.unop = ⊥ := by
      rw [inf_comm, hBC]
    have hsub (P : Opens T) (hP : P = ⊥) :
        Subsingleton (F.obj.obj (Opposite.op P)) := by
      exact AddCommGrpCat.subsingleton_of_isZero
        (Limits.IsZero.of_iso (Limits.isZero_zero _)
          ((TopCat.Sheaf.isTerminalOfEqEmpty F hP).uniqueUpToIso
            Limits.HasZeroObject.zeroIsTerminal))
    have hW01 : W 0 ⊓ W 1 = ⊥ := by
      simpa [W] using hBC
    have hW10 : W 1 ⊓ W 0 = ⊥ := by
      simpa [W] using hCB
    have hcompat : TopCat.Presheaf.IsCompatible F.obj W sf := by
      simp only [TopCat.Presheaf.IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, ?_⟩, Eq.symm ?_, rfl⟩
      · exact @Subsingleton.elim _ (hsub _ hW01) _ _
      · exact @Subsingleton.elim _ (hsub _ hW10) _ _
    let iUV : (j : Fin 2) → W j ⟶ U.unop
      | 0 => i.unop
      | 1 => homOfLE hCU
    have hiSup : (⨆ j, W j) = V.unop ⊔ C := by
      apply le_antisymm
      · rw [iSup_le_iff, Fin.forall_fin_two]
        exact ⟨le_sup_left, le_sup_right⟩
      · exact sup_le (le_iSup W 0) (le_iSup W 1)
    have hcover' : U.unop ≤ ⨆ j, W j := by
      simpa [hiSup] using hcover
    obtain ⟨t, ht, _⟩ :=
      F.existsUnique_gluing' W U.unop iUV hcover' sf hcompat
    refine ⟨t, ?_⟩
    have ht₀ := ht (0 : Fin 2)
    dsimp [iUV, W, sf] at ht₀
    exact ht₀

end TopCat.Sheaf

end
