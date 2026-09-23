module

public import StacksAndModuli.API.ProjectiveGradedImagePresentation

/-!
# Total modules commute with degreewise cokernels

For a morphism of diagrammatic graded modules, quotienting its target total module by the
range of the induced polynomial-linear map agrees with totalizing its degreewise cokernel.
This is the cokernel counterpart of `GradedModule.Total.kernelLinearEquiv`.

The comparison is useful for homogeneous polynomial presentations: a presentation obtained
from a graded morphism has an ordinary matrix cokernel whose compatible grading is the
degreewise cokernel grading.

Main declaration:

* `GradedModule.Total.cokerLinearEquiv`.
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

/-- Every homogeneous component of a total element killed by the total cokernel map lies in
the corresponding degreewise relation range. -/
lemma component_mem_range_of_mem_cokerKernel (f : M ⟶ N)
    (z : LinearMap.ker (map (toCoker f))) (d : ℤ) :
    tcomp N d z.1 ∈ LinearMap.range ((f.app d).hom) := by
  have hz := congrArg (tcomp (coker f) d) z.2
  simp only [tcomp_map, map_zero, toCoker_app, ModuleCat.hom_ofHom] at hz
  change (LinearMap.range ((f.app d).hom)).mkQ (tcomp N d z.1) =
    (0 : (N.obj d) ⧸ LinearMap.range ((f.app d).hom)) at hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  exact hz

/-- Choose degreewise preimages of all components of an element killed by the total cokernel
map and assemble them into one total element. -/
def cokerPreimage (f : M ⟶ N)
    (z : LinearMap.ker (map (toCoker f))) : Total M := by
  classical
  let pre (d : ℤ) : M.obj d :=
    Classical.choose (component_mem_range_of_mem_cokerKernel f z d)
  exact DFinsupp.mk z.1.support fun d ↦ pre d.1

/-- The assembled degreewise preimage maps to the original total-kernel element. -/
lemma map_cokerPreimage (f : M ⟶ N)
    (z : LinearMap.ker (map (toCoker f))) :
    map f (cokerPreimage f z) = z.1 := by
  apply DFinsupp.ext
  intro d
  classical
  let pre (e : ℤ) : M.obj e :=
    Classical.choose (component_mem_range_of_mem_cokerKernel f z e)
  change (f.app d).hom
    ((DFinsupp.mk z.1.support (fun e ↦ pre e.1) : Π₀ e : ℤ, M.obj e) d) =
      tcomp N d z.1
  by_cases hd : d ∈ z.1.support
  · rw [DFinsupp.mk_of_mem hd]
    exact Classical.choose_spec (component_mem_range_of_mem_cokerKernel f z d)
  · rw [DFinsupp.mk_of_notMem hd, map_zero]
    exact (DFinsupp.notMem_support_iff.mp hd).symm

/-- The range of the total relation map is the kernel of the total degreewise-cokernel map. -/
theorem range_map_eq_kernel_map_toCoker (f : M ⟶ N) :
    LinearMap.range (map f) = LinearMap.ker (map (toCoker f)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply DFinsupp.ext
    intro d
    change ((toCoker f).app d).hom ((f.app d).hom (tcomp M d x)) = 0
    simp only [toCoker_app, ModuleCat.hom_ofHom]
    change (LinearMap.range ((f.app d).hom)).mkQ
      ((f.app d).hom (tcomp M d x)) =
        (0 : (N.obj d) ⧸ LinearMap.range ((f.app d).hom))
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _
  · intro z hz
    let z' : LinearMap.ker (map (toCoker f)) := ⟨z, hz⟩
    exact ⟨cokerPreimage f z', map_cokerPreimage f z'⟩

/-- Totalization of the degreewise cokernel is the cokernel of the total polynomial-linear
map. -/
noncomputable def cokerLinearEquiv (f : M ⟶ N) :
    (Total N ⧸ LinearMap.range (map f))
      ≃ₗ[MvPolynomial (Fin (n + 1)) R] Total (coker f) := by
  let eKer :
      (Total N ⧸ LinearMap.range (map f)) ≃ₗ[MvPolynomial (Fin (n + 1)) R]
        (Total N ⧸ LinearMap.ker (map (toCoker f))) :=
    Submodule.Quotient.equiv _ _
      (LinearEquiv.refl (MvPolynomial (Fin (n + 1)) R) (Total N))
      (by simpa using range_map_eq_kernel_map_toCoker f)
  exact eKer.trans <|
    (map (toCoker f)).quotKerEquivOfSurjective
      (surjective_map_of_surjective (toCoker f) (surjective_toCoker_app f))

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end

end
