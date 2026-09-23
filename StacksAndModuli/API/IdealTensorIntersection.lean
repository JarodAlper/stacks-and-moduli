module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor kernels and intersections of ideals

For ideals `I` and `J`, right exactness of tensor product applied to
`I ∩ J → I × J → I + J` gives a useful diagram-chase lemma.  If
`(I + J) ⊗ M → M` is injective, then every element of the kernel of
`I ⊗ M → M` lifts from `(I ∩ J) ⊗ M`.

This is the tensor-intersection step in the Artin--Rees proof of the Noetherian local
flatness criterion (Stacks Project tag 00MK).
-/

@[expose] public section

open TensorProduct

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] {M : Type v}
variable [AddCommGroup M] [Module R M]

/-- The signed diagonal map `I ∩ J → I × J`, sending `z` to `(z, -z)`. -/
def intersectionToProduct (I J : Ideal R) : (I ⊓ J : Ideal R) →ₗ[R] I × J where
  toFun z := (⟨z, z.property.1⟩, ⟨-z, J.neg_mem z.property.2⟩)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [add_comm]
  map_smul' r x := by ext <;> simp

/-- The addition map `I × J → I + J`. -/
def productToSup (I J : Ideal R) : I × J →ₗ[R] (I ⊔ J : Ideal R) where
  toFun z := ⟨z.1 + z.2, Submodule.add_mem_sup z.1.property z.2.property⟩
  map_add' x y := by
    apply Subtype.ext
    change (x.1 : R) + y.1 + (x.2 + y.2) = (x.1 + x.2) + (y.1 + y.2)
    ac_rfl
  map_smul' r x := by
    apply Subtype.ext
    exact (mul_add r x.1 x.2).symm

/-- The inclusion of `I` as the first factor of `I × J`. -/
def inclusionToProduct (I J : Ideal R) : I →ₗ[R] I × J where
  toFun x := (x, 0)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- The first projection `I × J → I`. -/
def productFst (I J : Ideal R) : I × J →ₗ[R] I where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The addition map `I × J → I + J` is surjective. -/
theorem productToSup_surjective (I J : Ideal R) :
    Function.Surjective (productToSup I J) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  intro z hz
  let q : Submodule R R := (LinearMap.range (productToSup I J)).map (I ⊔ J).subtype
  have hq : I ⊔ J ≤ q := by
    apply sup_le
    · intro x hx
      refine ⟨⟨x, Submodule.mem_sup_left hx⟩, ?_, rfl⟩
      exact ⟨(⟨x, hx⟩, 0), by apply Subtype.ext; simp [productToSup]⟩
    · intro x hx
      refine ⟨⟨x, Submodule.mem_sup_right hx⟩, ?_, rfl⟩
      exact ⟨(0, ⟨x, hx⟩), by apply Subtype.ext; simp [productToSup]⟩
  obtain ⟨y, hy, hyz⟩ := hq z.property
  obtain ⟨w, hw⟩ := hy
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw ▸ hyz

/-- The signed diagonal and addition maps form an exact pair. -/
theorem exact_intersectionToProduct_productToSup (I J : Ideal R) :
    Function.Exact (intersectionToProduct I J) (productToSup I J) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    have hzval : (z.1 : R) + z.2 = 0 := congrArg Subtype.val hz
    have hz2 : (z.1 : R) ∈ J := by
      rw [eq_neg_of_add_eq_zero_left hzval]
      exact J.neg_mem z.2.property
    refine ⟨⟨z.1, z.1.property, hz2⟩, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact neg_eq_iff_add_eq_zero.mpr hzval
  · rintro z ⟨x, hx⟩
    rw [LinearMap.mem_ker]
    calc
      productToSup I J z =
          productToSup I J (intersectionToProduct I J x) := congrArg _ hx.symm
      _ = 0 := by apply Subtype.ext; simp [intersectionToProduct, productToSup]

/-- If `(I + J) ⊗ M → M` is injective, the kernel of `I ⊗ M → M` is contained in
the image of `(I ∩ J) ⊗ M → I ⊗ M`. -/
theorem ker_rTensor_subtype_le_range_inf_inclusion
    (I J : Ideal R)
    (hSup : Function.Injective ((I ⊔ J : Ideal R).subtype.rTensor M)) :
    LinearMap.ker (I.subtype.rTensor M) ≤
      LinearMap.range ((Submodule.inclusion
        (show (I ⊓ J : Ideal R) ≤ I from inf_le_left)).rTensor M) := by
  intro z hz
  let i := intersectionToProduct I J
  let p := productToSup I J
  let l := inclusionToProduct I J
  let fst := productFst I J
  have hex : Function.Exact i p := exact_intersectionToProduct_productToSup I J
  have hp : Function.Surjective p := productToSup_surjective I J
  have hexT : Function.Exact (i.rTensor M) (p.rTensor M) :=
    rTensor_exact M hex hp
  let z' := l.rTensor M z
  have hz' : (p.rTensor M) z' = 0 := by
    apply hSup
    rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    change (((I ⊔ J : Ideal R).subtype.comp p).comp l).rTensor M z = 0
    have hcomp : ((I ⊔ J : Ideal R).subtype.comp p).comp l = I.subtype := by
      ext x
      simp [p, l, productToSup, inclusionToProduct]
    rw [hcomp]
    exact LinearMap.mem_ker.mp hz
  have hzker : z' ∈ LinearMap.ker (p.rTensor M) := LinearMap.mem_ker.mpr hz'
  rw [hexT.linearMap_ker_eq] at hzker
  obtain ⟨w, hw⟩ := hzker
  refine ⟨w, ?_⟩
  have h := congrArg (fst.rTensor M) hw
  rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply] at h
  have hleft : fst.comp i = Submodule.inclusion
      (show (I ⊓ J : Ideal R) ≤ I from inf_le_left) := by ext x; rfl
  have hright : fst.comp l = LinearMap.id := by ext x; rfl
  simpa [hleft, hright] using h

end Ideal

end
