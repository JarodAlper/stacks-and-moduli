module

public import StacksAndModuli.API.PointSupportCohomology
public import StacksAndModuli.API.SchemeModuleStalkwiseIso

/-!
# Stalk support of residue-point modules

The canonical residue-field module at a closed point is supported only at that point.
Consequently, a finite coproduct of such modules is supported in the range of its family
of points.

For one point, restrict the pushforward to the open complement of the point.  Every
section there is a section on the empty open of the source and hence is zero.  For a
finite family, stalks commute with the finite coproduct.

## Main results

* `AlgebraicGeometry.Scheme.stalkSupport_residuePointSupportModule_subset_singleton`:
  the residue-point module of a closed point is supported at that point.
* `AlgebraicGeometry.Scheme.stalkSupport_finiteResiduePointSupportModule_subset_range`:
  a finite coproduct of closed residue-point modules is supported in the range of the
  indexing family.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The underlying additive-group sheaf of a scheme module, used to invoke the sheaf
condition without changing the module itself. -/
noncomputable abbrev Modules.toAddCommGrpSheaf
    {X : Scheme.{u}} (M : X.Modules) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨M.presheaf, M.isSheaf⟩

/-- Sections of a scheme module on the empty open form a subsingleton. -/
theorem Modules.subsingleton_sections_empty_open {X : Scheme.{u}}
    (M : X.Modules) : Subsingleton Γ(M, ⊥) := by
  refine ⟨fun a b ↦ ?_⟩
  apply (Modules.toAddCommGrpSheaf M).eq_of_locally_eq'
    (fun i : PEmpty.{u + 1} ↦ ⊥) ⊥
    (fun _ ↦ homOfLE le_rfl) ?_ a b (fun i ↦ i.elim)
  intro z hz
  exact absurd hz (by simp)

/-- The restriction of a residue-point module to an open not containing its point is a
zero module. -/
theorem isZero_restrict_residuePointSupportModule_of_not_mem
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∉ U) :
    IsZero ((Modules.restrictFunctor U.ι).obj
      (residuePointSupportModule X x)) := by
  let f := X.fromSpecResidueField x
  let M := structureModule (Spec (X.residueField x))
  rw [IsZero.iff_id_eq_zero]
  apply Modules.hom_ext _ _ fun W ↦ ?_
  have hopen : f ⁻¹ᵁ (U.ι ''ᵁ W) = ⊥ := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hzw⟩ := hz
      have hfx : f z = x := Scheme.fromSpecResidueField_apply x z
      have hwU : U.ι w ∈ U := by
        change w.1 ∈ U
        exact w.2
      have hfU : f z ∈ U := hzw ▸ hwU
      have hxmem : x ∈ U := hfx ▸ hfU
      exact (hxU hxmem).elim
    · exact False.elim
  let _ : Subsingleton
      Γ((Modules.restrictFunctor U.ι).obj
        (residuePointSupportModule X x), W) := by
    change Subsingleton Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ W))
    exact hopen.symm ▸ Modules.subsingleton_sections_empty_open M
  ext a
  exact Subsingleton.elim _ _

/-- The restriction of the residue-point module of a closed point to its open complement
is a zero module. -/
theorem isZero_restrict_residuePointSupportModule_compl_singleton
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    let U : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩
    IsZero ((Modules.restrictFunctor U.ι).obj
      (residuePointSupportModule X x)) :=
  isZero_restrict_residuePointSupportModule_of_not_mem
    X x ⟨{x}ᶜ, hx.isOpen_compl⟩ (by simp)

/-- The residue-point module of a closed point has no nonzero stalk away from that
point. -/
theorem stalkSupport_residuePointSupportModule_subset_singleton
    (X : Scheme.{u}) (x : X) (hx : IsClosed ({x} : Set X)) :
    Modules.stalkSupport (residuePointSupportModule X x) ⊆ {x} := by
  intro y hy
  by_contra hyx
  have hyU : y ∈ (⟨{x}ᶜ, hx.isOpen_compl⟩ : X.Opens) := hyx
  exact hy (Modules.isZero_stalk_of_isZero_restrict
    (residuePointSupportModule X x) ⟨{x}ᶜ, hx.isOpen_compl⟩
    (isZero_restrict_residuePointSupportModule_compl_singleton X x hx)
    ⟨y, hyU⟩)

/-- A finite coproduct of closed residue-point modules has no nonzero stalk away from
the range of its indexing family. -/
theorem stalkSupport_finiteResiduePointSupportModule_subset_range
    (X : Scheme.{u}) {J : Type u} [Finite J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    Modules.stalkSupport (finiteResiduePointSupportModule X x) ⊆
      Set.range x := by
  intro y hy
  by_contra hyrange
  let S : Set X := Set.range x
  have hSclosed : IsClosed S := by
    dsimp only [S]
    rw [Set.range_eq_iUnion]
    exact isClosed_iUnion_of_finite hx
  let U : X.Opens := ⟨Sᶜ, hSclosed.isOpen_compl⟩
  let R := Modules.restrictFunctor U.ι
  have hzero : IsZero
      (Discrete.functor (fun j ↦ residuePointSupportModule X (x j)) ⋙ R) := by
    apply Functor.isZero
    rintro ⟨j⟩
    apply isZero_restrict_residuePointSupportModule_of_not_mem
    intro hxj
    exact hxj ⟨j, rfl⟩
  have hcolim : IsZero
      (colimit (Discrete.functor
        (fun j ↦ residuePointSupportModule X (x j)) ⋙ R)) :=
    (colimit.isColimit _).isZero_pt hzero
  have hrestrict : IsZero
      (R.obj (finiteResiduePointSupportModule X x)) :=
    hcolim.of_iso (preservesColimitIso R
      (Discrete.functor (fun j ↦ residuePointSupportModule X (x j))))
  have hyU : y ∈ U := hyrange
  exact hy (Modules.isZero_stalk_of_isZero_restrict
    (finiteResiduePointSupportModule X x) U hrestrict ⟨y, hyU⟩)

end AlgebraicGeometry.Scheme

end
