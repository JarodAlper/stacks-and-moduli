module

public import StacksAndModuli.API.NoetherianLocalFlatApproximation

/-!
# Local flat approximation from a zero-compatible spanning comparison

This file packages the finite-obstruction conclusion of Stacks Project tag 00R6 in the form
adapted to the presentation comparison of tag 00MO.  A finite initial obstruction maps into a
directed system.  At every later stage it also maps to the kernel of ideal multiplication.
It suffices that:

* the directed-limit image of the obstruction is zero;
* whenever its directed transition is zero, the corresponding kernel comparison is zero;
* the comparison spans the later ideal-multiplication kernel.

The second condition is strictly weaker than identifying the comparison with the canonical
tensor transition element by element.  The first two bullets make the comparison zero at one
finite stage; the third makes the entire tensor kernel zero, and the Noetherian local
flatness criterion finishes the proof.
-/

@[expose] public section

universe u

namespace Module.DirectLimit

variable {ι : Type u} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι]

/-- A finite obstruction which dies in a directed limit forces eventual flatness whenever
its stagewise spanning comparisons vanish with the corresponding transition. -/
theorem exists_later_flat_of_zero_compatible_comparison
    (R S M : ι → Type u)
    [∀ j, CommRing (R j)] [∀ j, CommRing (S j)]
    [∀ j, Algebra (R j) (S j)]
    [∀ j, IsNoetherianRing (R j)] [∀ j, IsLocalRing (R j)]
    [∀ j, IsNoetherianRing (S j)] [∀ j, IsLocalRing (S j)]
    [∀ j, IsLocalHom (algebraMap (R j) (S j))]
    [∀ j, AddCommGroup (M j)] [∀ j, Module (R j) (M j)]
    [∀ j, Module (S j) (M j)]
    [∀ j, IsScalarTower (R j) (S j) (M j)]
    [∀ j, Module.Finite (S j) (M j)]
    (I : ∀ j, Ideal (R j)) (hI : ∀ j, I j ≠ ⊤)
    (hquot : ∀ j, Module.Flat (R j ⧸ I j)
      (M j ⧸ I j • (⊤ : Submodule (R j) (M j))))
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
    ∃ j, ∃ _ : i ≤ j, Module.Flat (R j) (M j) := by
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
  have hker : Function.Injective
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    let z : LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)) := ⟨x, hx⟩
    exact congrArg Subtype.val (hK z)
  let _ : Module.Flat (R j ⧸ I j)
      (M j ⧸ I j • (⊤ : Submodule (R j) (M j))) := hquot j
  exact Module.Flat.of_tensorMul_injective_of_quotient_flat
    (S := S j) (I j) (hI j) hker

/-- A finite obstruction which dies in a directed limit forces eventual flatness if its
transitioned image has stagewise maps whose ranges span the ideal-multiplication kernels.

This is the factored form of `exists_later_flat_of_zero_compatible_comparison`: because the
comparison factors through the transitioned obstruction, its required zero-compatibility is
automatic. -/
theorem exists_later_flat_of_factored_spanning_comparison
    (R S M : ι → Type u)
    [∀ j, CommRing (R j)] [∀ j, CommRing (S j)]
    [∀ j, Algebra (R j) (S j)]
    [∀ j, IsNoetherianRing (R j)] [∀ j, IsLocalRing (R j)]
    [∀ j, IsNoetherianRing (S j)] [∀ j, IsLocalRing (S j)]
    [∀ j, IsLocalHom (algebraMap (R j) (S j))]
    [∀ j, AddCommGroup (M j)] [∀ j, Module (R j) (M j)]
    [∀ j, Module (S j) (M j)]
    [∀ j, IsScalarTower (R j) (S j) (M j)]
    [∀ j, Module.Finite (S j) (M j)]
    (I : ∀ j, Ideal (R j)) (hI : ∀ j, I j ≠ ⊤)
    (hquot : ∀ j, Module.Flat (R j ⧸ I j)
      (M j ⧸ I j • (⊤ : Submodule (R j) (M j))))
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
    ∃ j, ∃ _ : i ≤ j, Module.Flat (R j) (M j) := by
  apply exists_later_flat_of_zero_compatible_comparison R S M I hI hquot i G f K g
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
