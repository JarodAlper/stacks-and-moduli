module

public import StacksAndModuli.API.FlatColimit
public import StacksAndModuli.API.ProjectiveGradedCechBaseChange
public import StacksAndModuli.API.ProjectiveGradedStructureCohomology

/-!
# Flat families of graded modules

Supporting API with no Stacks Project counterpart.

A family of quasi-coherent sheaves on `ℙⁿ_R` is modelled by a graded `R[x₀,…,xₙ]`-module `M`;
it is **flat over the base** when every graded piece `M_d` is a flat `R`-module
(`GradedModule.IsFlat`). This is the right rendering for the library, because
`GradedModule.ShortExact` is degreewise: a short exact sequence of families with flat quotient
must stay exact after base change *in every degree*.

The point of the file is that flatness propagates to the Čech complex:

```
theorem IsFlat.flat_cechCochain : Module.Flat R (M.cechCochain p d)
```

Each `M[1/x_I]_d` is a *sequential colimit* of the pieces `M_{d+t·|I|}` and a filtered colimit
of flat modules is flat (`Module.Flat.directLimit`); the cochain group is a finite product of
those. So the Čech complex of a coherent flat family is a bounded complex of flat `R`-modules,
which is what makes Cohomology and Base Change an elementary argument — see
`API/ProjectiveGradedFlatComplex.lean`.

Main declarations:
- `GradedModule.IsFlat`, and its closure properties;
- `GradedModule.IsFlat.flat_cechCochain`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial TensorProduct

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A family of quasi-coherent sheaves on `ℙⁿ_R` is **flat over the base** when each of its
graded pieces is a flat `R`-module. -/
def IsFlat (M : GradedModule R n) : Prop := ∀ d : ℤ, Module.Flat R (M.obj d)

variable {M : GradedModule R n}

/-- Every localization of a flat family is degreewise flat: it is a sequential colimit of the
graded pieces. -/
lemma IsFlat.flat_loc (hM : IsFlat M) (l : List (Fin (n + 1))) (d : ℤ) :
    Module.Flat R ((M.loc l).obj d) := by
  haveI : ∀ j : ℕ, Module.Flat R (M.obj (locDeg l d j)) := fun j => hM _
  exact Module.Flat.directLimit (fun j j' h => (M.locTr l d j j' h).hom)

/-- The Čech cochain groups of a flat family are flat: a finite product of localizations. -/
lemma IsFlat.flat_cechCochain (hM : IsFlat M) (p : ℕ) (d : ℤ) :
    Module.Flat R (M.cechCochain p d) := by
  classical
  haveI : ∀ τ : CechIdx n p, Module.Flat R ((M.loc τ.toList).obj d) :=
    fun τ => hM.flat_loc τ.toList d
  exact Module.Flat.pi (fun τ : CechIdx n p => (((M.loc τ.toList).obj d : Type u)))

/-- The structure sheaf is flat over the base: each graded piece is a direct summand of the
polynomial ring, cut out by the homogeneous component projection. -/
lemma flat_polySubmodule (d : ℤ) : Module.Flat R (polySubmodule R n d) := by
  rcases lt_or_ge d 0 with h | h
  · haveI : Subsingleton (polySubmodule R n d) :=
      subsingleton_polySubmodule_lt_zero (k := R) (n := n) h
    exact Module.Flat.of_shrink.{u, u, u}
  · refine Module.Flat.of_retract
      ((polySubmodule R n d).subtype)
      (LinearMap.codRestrict (polySubmodule R n d)
        (MvPolynomial.homogeneousComponent d.toNat) (fun p => by
          rw [polySubmodule_of_nonneg R n h]
          exact MvPolynomial.homogeneousComponent_isHomogeneous d.toNat p)) ?_
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hd : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg h
    have hx : (x : MvPolynomial (Fin (n + 1)) R).IsHomogeneous d.toNat :=
      isHomogeneous_of_mem_polySubmodule (by rw [hd]; exact x.2)
    simpa using MvPolynomial.homogeneousComponent_eq_self hx

lemma isFlat_structureModule : IsFlat (structureModule R n) := fun d => flat_polySubmodule d

/-- Twists of flat families are flat. -/
lemma IsFlat.twist (hM : IsFlat M) (a : ℤ) : IsFlat (M.twist a) := fun d => hM (d + a)

/-- Finite direct sums of flat families are flat. -/
lemma IsFlat.pow (hM : IsFlat M) (r : ℕ) : IsFlat (M.pow r) := by
  classical
  intro d
  haveI := hM d
  exact Module.Flat.pi (fun _ : Fin r => ((M.obj d : Type u)))

/-- The kernel of a surjection of flat families with flat quotient is flat. -/
lemma IsFlat.of_shortExact {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (hN : IsFlat N) (hP : IsFlat P) : IsFlat M := by
  intro d
  haveI := hN d
  haveI := hP d
  exact Module.Flat.of_shortExact (f.app d).hom (g.app d).hom (hfg.injective d)
    (LinearMap.exact_iff.mpr (hfg.exact d).symm) (hfg.surjective d)

/-- **Fibres of a short exact sequence with flat quotient stay short exact.** The `Tor₁` term
vanishes because the quotient is degreewise flat, so no flatness of the base change is
needed. -/
lemma shortExact_baseChangeMap {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (hP : IsFlat P) (A : Type u) [CommRing A] [Algebra R A] :
    ShortExact (GradedModule.baseChangeMap f A) (GradedModule.baseChangeMap g A) where
  injective d := by
    haveI := hP d
    have h := LinearMap.lTensor_injective_of_exact_of_flat (g.app d).hom (hfg.surjective d)
      (f.app d).hom (hfg.injective d)
      (LinearMap.exact_iff.mpr (hfg.exact d).symm) A
    intro x y hxy
    refine h ?_
    have hxy' : (LinearMap.baseChange A (f.app d).hom) x
        = (LinearMap.baseChange A (f.app d).hom) y := hxy
    simpa only [LinearMap.baseChange_eq_ltensor] using hxy'
  exact d := by
    have h := lTensor_exact A (f := (f.app d).hom) (g := (g.app d).hom)
      (LinearMap.exact_iff.mpr (hfg.exact d).symm) (hfg.surjective d)
    have h' : Function.Exact (LinearMap.baseChange A (f.app d).hom)
        (LinearMap.baseChange A (g.app d).hom) := by
      intro x
      simpa only [LinearMap.baseChange_eq_ltensor] using h x
    exact ((LinearMap.exact_iff.mp h').symm : _)
  surjective d := LinearMap.baseChange_surjective A (hfg.surjective d)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
