module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent of formal unramifiedness along a smooth faithfully flat algebra

If `R → A → B` are ring maps with `A → B` formally smooth and faithfully flat, and `R → B`
is formally unramified, then `R → A` is formally unramified.

The proof is the Jacobi–Zariski sequence (Stacks 00S2, Mathlib's
`Algebra.H1Cotangent.exact_δ_mapBaseChange`): the sequence
`H₁(L_{B/A}) →ᵟ B ⊗_A Ω[A⁄R] → Ω[B⁄R]` is exact, and `H₁(L_{B/A}) = 0` because `A → B` is
formally smooth, so `B ⊗_A Ω[A⁄R] → Ω[B⁄R]` is injective. As `Ω[B⁄R] = 0`, the tensor
product `B ⊗_A Ω[A⁄R]` vanishes, and faithful flatness of `B` over `A` forces
`Ω[A⁄R] = 0`.

This is the unramified analogue of the finite-type descent of
`StacksAndModuli/API/FiniteTypeSmoothDescent.lean` (Stacks 0367 in the smooth case); together
they give étale-local-on-the-source-ness of "locally of finite type and formally
unramified" in
`StacksAndModuli/Section4.3-Properties/part4.3.1-properties-of-morphisms.lean`.

## Main results

* `Algebra.FormallyUnramified.of_formallySmooth_of_faithfullyFlat`: the algebra form.
* `RingHom.FormallyUnramified.of_comp_of_smooth_of_faithfullyFlat`: the
  ring-homomorphism form.
-/

@[expose] public section

universe u₁ u₂ u₃ u

open TensorProduct

/-- **Descent of formal unramifiedness along a formally smooth faithfully flat algebra.**
Let `R → A → B` with `A → B` formally smooth and faithfully flat. If `B` is formally
unramified over `R`, then so is `A`. -/
theorem Algebra.FormallyUnramified.of_formallySmooth_of_faithfullyFlat
    {R : Type u₁} {A : Type u₂} {B : Type u₃} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified R A := by
  have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R A B
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (hex x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  have h2 : Subsingleton (B ⊗[A] Ω[A⁄R]) := hinj.subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp h2⟩

/-- Ring-homomorphism form of
`Algebra.FormallyUnramified.of_formallySmooth_of_faithfullyFlat`. -/
theorem RingHom.FormallyUnramified.of_comp_of_smooth_of_faithfullyFlat {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B)
    (hcomp : (ψ.comp φ).FormallyUnramified) (hsm : ψ.Smooth) (hff : ψ.FaithfullyFlat) :
    φ.FormallyUnramified := by
  algebraize [φ, ψ, ψ.comp φ]
  exact Algebra.FormallyUnramified.of_formallySmooth_of_faithfullyFlat (B := B)
