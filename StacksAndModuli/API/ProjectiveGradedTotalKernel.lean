module

public import StacksAndModuli.API.ProjectiveGradedTotalMap

/-!
# Total modules commute with degreewise kernels

The total polynomial-linear map of a graded morphism has kernel equal to the total module of
the degreewise kernel.  This is the relation-module comparison needed to transport finite
presentation of a total module back to finite generation of a graded syzygy.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open CategoryTheory DirectSum MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}
variable {M N : GradedModule R n}

/-- The total inclusion of the degreewise kernel lands in the kernel of the total map. -/
def kernelMap (f : M ⟶ N) :
    Total (ker f) →ₗ[MvPolynomial (Fin (n + 1)) R] LinearMap.ker (map f) :=
  LinearMap.codRestrict (LinearMap.ker (map f)) (map (kerι f)) fun x => by
    rw [LinearMap.mem_ker]
    apply DFinsupp.ext
    intro d
    change tcomp N d (map f (map (kerι f) x)) = tcomp N d 0
    rw [tcomp_map, tcomp_map]
    exact (tcomp (ker f) d x).2

@[simp]
lemma kernelMap_coe (f : M ⟶ N) (x : Total (ker f)) :
    ((kernelMap f x : LinearMap.ker (map f)) : Total M) = map (kerι f) x := rfl

/-- The total inclusion of a degreewise kernel is injective. -/
lemma injective_map_kerι (f : M ⟶ N) : Function.Injective (map (kerι f)) := by
  intro x y hxy
  apply DFinsupp.ext
  intro d
  change tcomp (ker f) d x = tcomp (ker f) d y
  apply Subtype.ext
  have h := congrArg (tcomp M d) hxy
  simp only [tcomp_map] at h
  have hval (w : (ker f).obj d) : ((kerι f).app d).hom w = w.1 := rfl
  simpa only [hval] using h

/-- The component of an element killed by the total map lies in the corresponding degreewise
kernel. -/
lemma kernelComponent_mem (f : M ⟶ N) (z : LinearMap.ker (map f)) (d : ℤ) :
    (f.app d).hom (tcomp M d z.1) = 0 := by
  have h := congrArg (tcomp N d) z.2
  simpa only [tcomp_map, map_zero] using h

/-- The degreewise preimage of an element in the kernel of the total map. -/
def kernelPreimage (f : M ⟶ N) (z : LinearMap.ker (map f)) : Total (ker f) := by
  classical
  let z' : Π₀ d : ℤ, (M.obj d : Type u) := z.1
  exact DFinsupp.mk z'.support fun d =>
    ⟨z' d, LinearMap.mem_ker.mpr (kernelComponent_mem f z d)⟩

/-- The degreewise preimage maps back to the original total-kernel element. -/
lemma kernelMap_preimage (f : M ⟶ N) (z : LinearMap.ker (map f)) :
    kernelMap f (kernelPreimage f z) = z := by
  apply Subtype.ext
  apply DFinsupp.ext
  intro d
  change tcomp M d (map (kerι f) (kernelPreimage f z)) = tcomp M d z.1
  rw [tcomp_map]
  change (tcomp (ker f) d (kernelPreimage f z)).1 =
    tcomp M d z.1
  classical
  simp only [kernelPreimage, tcomp, DirectSum.component]
  let z' : Π₀ e : ℤ, (M.obj e : Type u) := z.1
  change ((DFinsupp.mk z'.support (fun e =>
    (⟨z' e, LinearMap.mem_ker.mpr (kernelComponent_mem f z e)⟩ :
      LinearMap.ker (f.app e).hom)) :
        Π₀ e : ℤ, LinearMap.ker (f.app e).hom) d).1 = z' d
  by_cases hd : d ∈ z'.support
  · rw [DFinsupp.mk_of_mem hd]
  · rw [DFinsupp.mk_of_notMem hd]
    exact (DFinsupp.notMem_support_iff.mp hd).symm

/-- The total module of the degreewise kernel is polynomial-linearly equivalent to the kernel
of the total polynomial-linear map. -/
def kernelLinearEquiv (f : M ⟶ N) :
    Total (ker f) ≃ₗ[MvPolynomial (Fin (n + 1)) R] LinearMap.ker (map f) :=
  LinearEquiv.ofBijective (kernelMap f)
    ⟨fun _ _ h => injective_map_kerι f (congrArg Subtype.val h),
      fun z => ⟨kernelPreimage f z, kernelMap_preimage f z⟩⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end
