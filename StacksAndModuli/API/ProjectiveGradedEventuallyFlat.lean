module

public import StacksAndModuli.API.FlatSequentialColimitTail
public import StacksAndModuli.API.ProjectiveGradedFlat

/-!
# Eventual flatness and projective localization

Supporting API with no Stacks Project counterpart.

The degree-`d` part of the localization of a graded module at one variable is the sequential
colimit of the pieces in degrees `d, d + 1, d + 2, ...`.  Consequently, flatness of all
sufficiently high graded pieces is enough to make every degree of this localization flat.

Main declarations:
- `GradedModule.IsFlatAbove`;
- `GradedModule.IsFlatAbove.flat_loc_singleton`.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A graded module is flat above `D` if every piece of degree at least `D` is flat over the
base ring. -/
def IsFlatAbove (M : GradedModule R n) (D : ℤ) : Prop :=
  ∀ d : ℤ, D ≤ d → Module.Flat R (M.obj d)

variable {M : GradedModule R n}

/-- Eventual flatness of the graded pieces makes every degree of a single-variable
localization flat. -/
lemma IsFlatAbove.flat_loc_singleton_degree {D : ℤ} (hM : IsFlatAbove M D)
    (a : Fin (n + 1)) (d : ℤ) : Module.Flat R ((M.loc [a]).obj d) := by
  let N : ℕ := (D - d).toNat
  refine @Module.Flat.directLimit_of_eventually R _
    (fun j : ℕ ↦ M.obj (locDeg [a] d j)) _ _
    (fun j j' h ↦ (M.locTr [a] d j j' h).hom) _ N (fun i ↦ hM _ ?_)
  have hN : D - d ≤ (N : ℤ) := by
    exact Int.self_le_toNat (D - d)
  simp only [locDeg_def, List.length_singleton, Int.natCast_add]
  omega

/-- Eventual flatness of the graded pieces makes the localization at any one variable a
degreewise flat graded module. -/
lemma IsFlatAbove.flat_loc_singleton {D : ℤ} (hM : IsFlatAbove M D)
    (a : Fin (n + 1)) : IsFlat (M.loc [a]) :=
  fun d ↦ hM.flat_loc_singleton_degree a d

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
