module

public import StacksAndModuli.API.DirectLimitFiniteVanishing
public import StacksAndModuli.API.NoetherianTorKernelFinite

/-!
# The finite-obstruction core of local flat approximation

This file packages the complete formal part of the eventual-flatness argument in Stacks
Project tag 00R6 after the approximation system and its tensor-kernel comparisons have been
constructed.

At an initial stage `i`, let `G i` be a finite obstruction module.  If its map to the direct
limit is zero, finite generation kills the whole obstruction at one later stage `j`.  Suppose
the induced image spans the kernel of ideal multiplication at `j`.  That kernel is then zero,
and the Noetherian variant local flatness criterion makes the stage module flat.

Thus the two approximation-system inputs left explicit by the theorem are precisely:

* `hlim`: the initial obstruction dies in the limit;
* `hspan`: the comparison from the transitioned obstruction spans the later ideal-tensor
  kernel.

For the systems of tag 00R6, the initial finiteness instance is supplied by
`Ideal.finite_ker_tensorMul`; tensor/direct-limit compatibility gives `hlim`; and the Tor
comparison lemmas 00MM, 00MN together with localization give `hspan`.
-/

@[expose] public section

universe u

namespace Module.DirectLimit

variable {ι : Type u} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι]

/-- A finite obstruction which dies in a directed limit and spans every later ideal-tensor
kernel dies at one finite stage; the corresponding stage module is flat.

This is the finite-generation and local-flatness core of Stacks Project tag 00R6. -/
theorem exists_later_flat_of_tensorMulKernel
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
    [Module.Finite (S i) (G i)]
    (compare : ∀ j (_hij : i ≤ j), G j →+
      LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))
    (hlim : Module.DirectLimit.of (S i) ι G f i = 0)
    (hspan : ∀ j (hij : i ≤ j),
      Submodule.span (S j) (Set.range
        ((compare j hij).comp (f i j hij).toAddMonoidHom)) = ⊤) :
    ∃ j, ∃ _ : i ≤ j, Module.Flat (R j) (M j) := by
  have hmap : (Module.DirectLimit.of (S i) ι G f i).comp
      (LinearMap.id : G i →ₗ[S i] G i) = 0 := by
    rw [hlim, LinearMap.zero_comp]
  obtain ⟨j, hij, hj⟩ :=
    exists_later_comp_eq_zero_of_finite (f := f)
      (LinearMap.id : G i →ₗ[S i] G i) hmap
  refine ⟨j, hij, ?_⟩
  have hfzero : f i j hij = 0 := by
    simpa using hj
  have hK : ∀ x : LinearMap.ker
      (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)), x = 0 := by
    intro x
    have hx : x ∈ (⊤ : Submodule (S j) (LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))) :=
      Submodule.mem_top
    rw [← hspan j hij, hfzero] at hx
    have hle : Submodule.span (S j) (Set.range
        ((compare j hij).comp (0 : G i →ₗ[S i] G j).toAddMonoidHom)) ≤ ⊥ := by
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

/-- A version of `exists_later_flat_of_tensorMulKernel` adapted to the actual proof of
Stacks 00R6.  Here `G` is a directed system of ambient tensor modules, `K` is the finite
initial tensor kernel, and `g` includes that kernel into the initial ambient term.

The maps `compare` land in the later ideal-tensor kernels.  The equation `compare_val`
identifies their underlying ambient vectors with the transitioned elements of `K`, while
`hspan` records the surjectivity-up-to-scalar-extension supplied by the Tor comparison
lemmas. -/
theorem exists_later_flat_of_transitioned_tensorMulKernel
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
    (ambient : ∀ j, (G j →+ TensorProduct (R j) (M j) (I j)))
    (compare : ∀ j (_hij : i ≤ j), K →+
      LinearMap.ker
        (Ideal.tensorMul (R := R j) (S := S j) (M := M j) (I j)))
    (compare_val : ∀ j (hij : i ≤ j) (x : K),
      ((compare j hij) x : TensorProduct (R j) (M j) (I j)) =
        ambient j (f i j hij (g x)))
    (hlim : (Module.DirectLimit.of (S i) ι G f i).comp g = 0)
    (hspan : ∀ j (hij : i ≤ j),
      Submodule.span (S j) (Set.range (compare j hij)) = ⊤) :
    ∃ j, ∃ _ : i ≤ j, Module.Flat (R j) (M j) := by
  obtain ⟨j, hij, hj⟩ :=
    exists_later_comp_eq_zero_of_finite (f := f) g hlim
  refine ⟨j, hij, ?_⟩
  have hcompare : compare j hij = 0 := by
    ext x
    change ((compare j hij) x : TensorProduct (R j) (M j) (I j)) = 0
    rw [compare_val, ← LinearMap.comp_apply, hj, LinearMap.zero_apply, map_zero]
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

end Module.DirectLimit
