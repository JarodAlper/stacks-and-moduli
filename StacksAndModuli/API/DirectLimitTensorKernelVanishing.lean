module

public import StacksAndModuli.API.DirectLimitFiniteVanishing
public import StacksAndModuli.API.NoetherianTorKernelFinite

/-!
# Killing ideal-tensor kernels at a finite stage

A finite obstruction which vanishes in a directed colimit vanishes after one transition.  If
a compatible comparison from that obstruction spans a later ideal-multiplication kernel, the
later multiplication map is injective.  This is the purely finite-obstruction part of Stacks
Project tag 00R6, separated from the Noetherian local flatness criterion.

The separation is useful for polynomial approximation: one first kills the kernel on a
global polynomial-stage module, then uses flat base change to localize that injectivity at a
chosen prime.
-/

@[expose] public section

universe u

namespace Module.DirectLimit

variable {ι : Type u} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι]

/-- A zero-compatible spanning comparison from a finite colimit obstruction eventually
makes ideal multiplication injective. -/
theorem exists_later_tensorMul_injective_of_zero_compatible_comparison
    (R S M : ι → Type u)
    [∀ j, CommRing (R j)] [∀ j, CommRing (S j)]
    [∀ j, Algebra (R j) (S j)]
    [∀ j, AddCommGroup (M j)] [∀ j, Module (R j) (M j)]
    [∀ j, Module (S j) (M j)]
    [∀ j, IsScalarTower (R j) (S j) (M j)]
    (I : ∀ j, Ideal (R j))
    (i : ι) (G : ι → Type u)
    [∀ j, AddCommGroup (G j)] [∀ j, Module (S i) (G j)]
    (f : ∀ a b, a ≤ b → G a →ₗ[S i] G b)
    [DirectedSystem G fun a b h => f a b h]
    (K : Type u) [AddCommGroup K] [Module (S i) K]
    [Module.Finite (S i) K] (g : K →ₗ[S i] G i)
    (compare : ∀ j (_hij : i ≤ j), K →+
      LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))
    (compare_zero : ∀ j (hij : i ≤ j),
      (f i j hij).comp g = 0 → compare j hij = 0)
    (hlim : (Module.DirectLimit.of (S i) ι G f i).comp g = 0)
    (hspan : ∀ j (hij : i ≤ j),
      Submodule.span (S j) (Set.range (compare j hij)) = ⊤) :
    ∃ j, ∃ _ : i ≤ j, Function.Injective
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)) := by
  obtain ⟨j, hij, hj⟩ :=
    exists_later_comp_eq_zero_of_finite (f := f) g hlim
  refine ⟨j, hij, ?_⟩
  have hcompare : compare j hij = 0 := compare_zero j hij hj
  have hK : ∀ x : LinearMap.ker
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)), x = 0 := by
    intro x
    have hx : x ∈ (⊤ : Submodule (S j) (LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))) :=
      Submodule.mem_top
    rw [← hspan j hij, hcompare] at hx
    have hle : Submodule.span (S j) (Set.range
        (0 : K →+ LinearMap.ker
          (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))) ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro y ⟨z, rfl⟩
      simp
    simpa using hle hx
  rw [injective_iff_map_eq_zero]
  intro x hx
  let z : LinearMap.ker
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)) := ⟨x, hx⟩
  exact congrArg Subtype.val (hK z)

/-- Factored form of
`exists_later_tensorMul_injective_of_zero_compatible_comparison`.  If each spanning
comparison literally factors through the transitioned finite obstruction, zero-compatibility
is automatic. -/
theorem exists_later_tensorMul_injective_of_factored_spanning_comparison
    (R S M : ι → Type u)
    [∀ j, CommRing (R j)] [∀ j, CommRing (S j)]
    [∀ j, Algebra (R j) (S j)]
    [∀ j, AddCommGroup (M j)] [∀ j, Module (R j) (M j)]
    [∀ j, Module (S j) (M j)]
    [∀ j, IsScalarTower (R j) (S j) (M j)]
    (I : ∀ j, Ideal (R j))
    (i : ι) (G : ι → Type u)
    [∀ j, AddCommGroup (G j)] [∀ j, Module (S i) (G j)]
    (f : ∀ a b, a ≤ b → G a →ₗ[S i] G b)
    [DirectedSystem G fun a b h => f a b h]
    (K : Type u) [AddCommGroup K] [Module (S i) K]
    [Module.Finite (S i) K] (g : K →ₗ[S i] G i)
    (lift : ∀ j (_hij : i ≤ j), G j →+
      LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))
    (hlim : (Module.DirectLimit.of (S i) ι G f i).comp g = 0)
    (hspan : ∀ j (hij : i ≤ j),
      Submodule.span (S j) (Set.range
        ((lift j hij).comp ((f i j hij).comp g).toAddMonoidHom)) = ⊤) :
    ∃ j, ∃ _ : i ≤ j, Function.Injective
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)) := by
  apply exists_later_tensorMul_injective_of_zero_compatible_comparison
    R S M I i G f K g
    (compare := fun j hij =>
      (lift j hij).comp ((f i j hij).comp g).toAddMonoidHom)
    (hlim := hlim) (hspan := hspan)
  intro j hij hzero
  ext x
  simp only [AddMonoidHom.comp_apply]
  have hx : ((f i j hij).comp g).toAddMonoidHom x = 0 :=
    LinearMap.congr_fun hzero x
  rw [hx]
  simp

end Module.DirectLimit
