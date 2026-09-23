module

public import StacksAndModuli.API.NoetherianLocalFlatCokernelFiberCriterion
public import StacksAndModuli.API.NoetherianLocalFlatCokernelQuotientCriterion
public import StacksAndModuli.API.IdealQuotientExact

/-!
# Relative flatness from an exact two-step residue-fibre complex

Let `R → S` be a local homomorphism of noetherian local rings and let
`L → K → F` be two consecutive maps of finite `S`-modules, with `F` flat over `R`.
If the two maps become exact after tensoring with the residue field of `R`, then the
original pair is exact and the cokernel of `K → F` is flat over `R`.

The proof factors the second map through `K / range(f)`.  Fibre exactness makes the
induced map injective on the closed coefficient fibre, so
`Module.Flat.injective_and_flat_coker_of_lTensor_residueField_injective` applies.  This is
the two-differential form of the local homological step in Stacks Project tag 00MI.

Main declaration:

* `Module.Flat.exact_and_flat_coker_of_lTensor_residueField_exact`;
* `Module.Flat.coker_of_lTensor_residueField_exact`;
* `Module.Flat.coker_of_quotientByMappedIdeal_exact`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

open Function TensorProduct

namespace Module.Flat

/-- For two consecutive maps of finite modules over a noetherian local algebra, exactness
on the closed coefficient fibre makes the original pair exact and the cokernel of the
second map coefficient-flat.

This retains the ordinary exactness conclusion of the local criterion.  It is the
pointwise bridge used before spreading relative-fibre exactness in Stacks Project tag
00RB. -/
theorem exact_and_flat_coker_of_lTensor_residueField_exact
    {R : Type u} {S : Type v} {L K F : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S K] [Module.Finite S F] [Module.Flat R F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : Function.Exact
      ((f.restrictScalars R).lTensor (IsLocalRing.ResidueField R))
      ((g.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Function.Exact f g ∧ Module.Flat R (F ⧸ LinearMap.range g) := by
  let Q := K ⧸ LinearMap.range f
  let u : Q →ₗ[S] F :=
    (LinearMap.range f).liftQ g (LinearMap.range_le_ker_iff.mpr hcomp)
  have hucomp : (u.restrictScalars R).comp
      ((LinearMap.range f).mkQ.restrictScalars R) = g.restrictScalars R := by
    ext x
    rfl
  have hzero : ((LinearMap.range f).mkQ.restrictScalars R).comp
      (f.restrictScalars R) = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f x)
  have hufibre : Function.Injective
      ((u.restrictScalars R).lTensor (IsLocalRing.ResidueField R)) := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hxyzero : ((u.restrictScalars R).lTensor
        (IsLocalRing.ResidueField R)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    suffices x - y = 0 by exact this
    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective
      (IsLocalRing.ResidueField R)
      (g := (LinearMap.range f).mkQ.restrictScalars R)
      (Submodule.mkQ_surjective (LinearMap.range f)) (x - y)
    rw [← hz]
    have hgz : ((g.restrictScalars R).lTensor
        (IsLocalRing.ResidueField R)) z = 0 := by
      rw [← hucomp, LinearMap.lTensor_comp, LinearMap.comp_apply]
      rw [hz]
      exact hxyzero
    obtain ⟨w, rfl⟩ := (hfibre z).mp hgz
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  letI : Module.Finite S Q :=
    Module.Finite.of_surjective (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _)
  have hu :
      Function.Injective u ∧ Module.Flat R (F ⧸ LinearMap.range u) :=
    (Module.Flat.injective_and_flat_coker_of_lTensor_residueField_injective
      u hufibre)
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    apply (LinearMap.ker_eq_bot_range_liftQ_iff
      (LinearMap.range_le_ker_iff.mpr hcomp)).mp
    exact LinearMap.ker_eq_bot.mpr hu.1
  refine ⟨hexact, ?_⟩
  rw [Submodule.range_liftQ] at hu
  exact hu.2

/-- For two consecutive maps of finite modules over a noetherian local algebra, exactness
on the closed coefficient fibre makes the cokernel of the second map coefficient-flat. -/
theorem coker_of_lTensor_residueField_exact
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S K] [Module.Finite S F] [Module.Flat R F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : Function.Exact
      ((f.restrictScalars R).lTensor (IsLocalRing.ResidueField R))
      ((g.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Module.Flat R (F ⧸ LinearMap.range g) :=
  (exact_and_flat_coker_of_lTensor_residueField_exact
    f g hcomp hfibre).2

/-- For two consecutive maps of finite modules over a noetherian local algebra,
exactness after quotienting by the extension of the coefficient maximal ideal makes the
cokernel of the second map coefficient-flat.

This is the quotient-module form of `coker_of_lTensor_residueField_exact`.  It is useful
for relative fibres presented concretely as a quotient of the localized source ring. -/
theorem coker_of_quotientByMappedIdeal_exact
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
    [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
    [Module.Finite S K] [Module.Finite S F] [Module.Flat R F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : Function.Exact
      (LinearMap.quotientByIdeal
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) f)
      (LinearMap.quotientByIdeal
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) g)) :
    Module.Flat R (F ⧸ LinearMap.range g) := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let Q := K ⧸ LinearMap.range f
  let u : Q →ₗ[S] F :=
    (LinearMap.range f).liftQ g (LinearMap.range_le_ker_iff.mpr hcomp)
  have hucomp : u.comp (LinearMap.range f).mkQ = g := by
    ext x
    rfl
  have hzero : (LinearMap.range f).mkQ.comp f = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (LinearMap.mem_range_self f x)
  have hufibre : Function.Injective (LinearMap.quotientByIdeal J u) := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hxyzero : LinearMap.quotientByIdeal J u (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    suffices x - y = 0 by exact this
    obtain ⟨z, hz⟩ := LinearMap.quotientByIdeal_surjective J
      (LinearMap.range f).mkQ (Submodule.mkQ_surjective _) (x - y)
    rw [← hz]
    have hgz : LinearMap.quotientByIdeal J g z = 0 := by
      rw [← hucomp, LinearMap.quotientByIdeal_comp, LinearMap.comp_apply,
        hz]
      exact hxyzero
    obtain ⟨w, rfl⟩ := (hfibre z).mp hgz
    rw [← LinearMap.comp_apply, ← LinearMap.quotientByIdeal_comp, hzero,
      LinearMap.quotientByIdeal_zero, LinearMap.zero_apply]
  have hflat : Module.Flat R (F ⧸ LinearMap.range u) :=
    Module.Flat.of_exact_of_surjective_of_quotientByMappedIdeal_injective
      u (LinearMap.range u).mkQ (LinearMap.exact_map_mkQ_range u)
      (Submodule.mkQ_surjective _) hufibre
  rw [Submodule.range_liftQ] at hflat
  exact hflat

end Module.Flat

end
