module

public import StacksAndModuli.API.FlatColimit

/-!
# Cofinal tails of sequential module colimits

A sequential direct limit is unchanged after discarding finitely many initial terms.  This
file records the corresponding linear equivalence and the consequence used by projective
graded localization: a sequential colimit is flat as soon as a cofinal tail of its terms is
flat.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.DirectLimit

variable {R : Type u} [CommRing R]
variable {G : ℕ → Type v} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j : ℕ, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G fun i j h ↦ f i j h]

/-- The family obtained by discarding the terms before `N`. -/
abbrev tailFamily (N : ℕ) : ℕ → Type v := fun i ↦ G (N + i)

/-- The transition maps on the cofinal tail beginning at `N`. -/
def tailMap (N : ℕ) (i j : ℕ) (h : i ≤ j) :
    tailFamily (G := G) N i →ₗ[R] tailFamily (G := G) N j :=
  f (N + i) (N + j) (Nat.add_le_add_left h N)

instance tailDirectedSystem (N : ℕ) :
    DirectedSystem (tailFamily (G := G) N) (fun i j h ↦ tailMap f N i j h) where
  map_self i x := by
    simpa only [tailMap] using
      (DirectedSystem.map_self' (F := G) f x)
  map_map {k j i} hij hjk x := by
    simpa only [tailMap] using
      (DirectedSystem.map_map' (F := G) f
        (Nat.add_le_add_left hij N) (Nat.add_le_add_left hjk N) x)

/-- Discarding finitely many initial objects does not change a sequential direct limit. -/
noncomputable def tailLinearEquiv (N : ℕ) :
    Module.DirectLimit (tailFamily (G := G) N) (fun i j h ↦ tailMap f N i j h) ≃ₗ[R]
      Module.DirectLimit G f := by
  let toLimit :
      Module.DirectLimit (tailFamily (G := G) N) (fun i j h ↦ tailMap f N i j h) →ₗ[R]
        Module.DirectLimit G f :=
    Module.DirectLimit.lift R ℕ (tailFamily (G := G) N)
      (fun i j h ↦ tailMap f N i j h)
      (fun i ↦ Module.DirectLimit.of R ℕ G f (N + i))
      (fun i j hij x ↦ by
        simpa only [tailMap] using
          (Module.DirectLimit.of_f (R := R) (G := G) (f := f)
            (hij := Nat.add_le_add_left hij N) (x := x)))
  let fromLimit : Module.DirectLimit G f →ₗ[R]
      Module.DirectLimit (tailFamily (G := G) N) (fun i j h ↦ tailMap f N i j h) :=
    Module.DirectLimit.lift R ℕ G f
      (fun i ↦
        Module.DirectLimit.of R ℕ (tailFamily (G := G) N)
          (fun i j h ↦ tailMap f N i j h) i ∘ₗ
            f i (N + i) (Nat.le_add_left i N))
      (fun i j hij x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        rw [← Module.DirectLimit.of_f
          (R := R) (G := tailFamily (G := G) N)
          (f := fun i j h ↦ tailMap f N i j h) (hij := hij)]
        congr 1
        simp only [tailMap]
        calc
          f j (N + j) (Nat.le_add_left j N) (f i j hij x) =
              f i (N + j) (hij.trans (Nat.le_add_left j N)) x :=
            DirectedSystem.map_map' (F := G) f hij (Nat.le_add_left j N) x
          _ = f i (N + j)
              ((Nat.le_add_left i N).trans (Nat.add_le_add_left hij N)) x := by
            congr
          _ = f (N + i) (N + j) (Nat.add_le_add_left hij N)
              (f i (N + i) (Nat.le_add_left i N) x) :=
            (DirectedSystem.map_map' (F := G) f
              (Nat.le_add_left i N) (Nat.add_le_add_left hij N) x).symm)
  refine LinearEquiv.ofLinearMap toLimit fromLimit ?_ ?_
  · apply Module.DirectLimit.hom_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    dsimp only [fromLimit]
    rw [Module.DirectLimit.lift_of]
    rw [LinearMap.comp_apply]
    dsimp only [toLimit]
    rw [Module.DirectLimit.lift_of]
    exact Module.DirectLimit.of_f (R := R) (G := G) (f := f)
      (hij := Nat.le_add_left i N)
  · apply Module.DirectLimit.hom_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    dsimp only [toLimit]
    rw [Module.DirectLimit.lift_of]
    dsimp only [fromLimit]
    rw [Module.DirectLimit.lift_of]
    exact Module.DirectLimit.of_f
      (R := R) (G := tailFamily (G := G) N)
      (f := fun i j h ↦ tailMap f N i j h)
      (hij := Nat.le_add_left i N)

end Module.DirectLimit

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {G : ℕ → Type v} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j : ℕ, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G fun i j h ↦ f i j h]

/-- A sequential direct limit is flat if all terms in some cofinal tail are flat. -/
theorem directLimit_of_eventually (N : ℕ) [∀ i, Module.Flat R (G (N + i))] :
    Module.Flat R (Module.DirectLimit G f) := by
  let htail : Module.Flat R
      (Module.DirectLimit (Module.DirectLimit.tailFamily (G := G) N)
        (fun i j h ↦ Module.DirectLimit.tailMap f N i j h)) :=
    Module.Flat.directLimit
      (fun i j h ↦ Module.DirectLimit.tailMap f N i j h)
  exact (Module.Flat.equiv_iff (Module.DirectLimit.tailLinearEquiv f N)).mp htail

end Module.Flat

end

end
