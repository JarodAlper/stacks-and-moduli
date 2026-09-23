module

public import StacksAndModuli.API.SheafCohomologySubsingletonSpace
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaf cohomology in the presence of a global point

A point is called global here when every point of the space specializes to it.
Equivalently, its only open neighbourhood is the whole space.  At such a point,
the germ from global sections to the stalk is an isomorphism.  Since the stalk
functor is a left adjoint, global sections preserve epimorphisms, and every
positive cohomology group of every abelian sheaf vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace TopologicalSpace

/-- A point is global if every point of the space specializes to it. -/
def IsGlobalPoint {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∀ y : X, Specializes y x

namespace IsGlobalPoint

/-- A global point belongs only to the top open. -/
theorem open_eq_top {X : Type u} [TopologicalSpace X] {x : X} (hx : IsGlobalPoint x)
    (U : Opens X) (hxU : x ∈ U) : U = ⊤ := by
  apply top_unique
  intro y _
  exact (hx y).mem_open U.2 hxU

/-- Having no proper open neighbourhood characterizes global points. -/
theorem iff_open_eq_top {X : Type u} [TopologicalSpace X] {x : X} :
    IsGlobalPoint x ↔ ∀ (U : Opens X), x ∈ U → U = ⊤ := by
  constructor
  · exact fun hx U hxU ↦ hx.open_eq_top U hxU
  · intro hx y
    rw [specializes_iff_forall_open]
    intro s hs hxs
    let U : Opens X := ⟨s, hs⟩
    have hU : U = ⊤ := hx U hxs
    change y ∈ U
    rw [hU]
    trivial

/-- Homeomorphisms carry global points to global points. -/
theorem homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (hx : IsGlobalPoint x)
    (e : X ≃ₜ Y) : IsGlobalPoint (e x) := by
  intro y
  simpa using (hx (e.symm y)).map e.continuous

end IsGlobalPoint

end TopologicalSpace

namespace TopCat.Presheaf

/-- At a global point, the germ from global sections to the stalk is an
isomorphism for every abelian-group-valued presheaf. -/
theorem isIso_Γgerm_of_isGlobalPoint {X : TopCat.{u}} (x : X)
    (hx : TopologicalSpace.IsGlobalPoint x) (F : X.Presheaf AddCommGrpCat.{u}) :
    IsIso (F.Γgerm x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro s t hst
    obtain ⟨W, hxW, iWs, iWt, hW⟩ :=
      F.germ_eq x (U := ⊤) (V := ⊤) (by simp) (by simp) s t hst
    have hWtop : W = ⊤ := hx.open_eq_top W hxW
    subst W
    simpa only [Subsingleton.elim iWs (𝟙 _), Subsingleton.elim iWt (𝟙 _),
      op_id, Functor.map_id_apply] using hW
  · intro t
    obtain ⟨U, hxU, s, hs⟩ := F.exists_germ_eq t
    have hUtop : U = ⊤ := hx.open_eq_top U hxU
    subst U
    exact ⟨s, by simpa [Γgerm] using hs⟩

end TopCat.Presheaf

namespace TopCat.Sheaf

/-- At a global point, evaluation of sheaves on the top open is naturally
isomorphic to the stalk functor. -/
noncomputable def sheafSectionsTopIsoStalkOfIsGlobalPoint
    {X : TopCat.{u}} (x : X) (hx : TopologicalSpace.IsGlobalPoint x) :
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X)) ≅
      Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  NatIso.ofComponents
    (fun F ↦ by
      letI : IsIso (Presheaf.Γgerm F.obj x) :=
        Presheaf.isIso_Γgerm_of_isGlobalPoint x hx F.obj
      exact asIso (Presheaf.Γgerm F.obj x))
    (fun f ↦ by
      exact (Presheaf.stalkFunctor_map_germ
        (⊤ : Opens X) x (by simp) f.hom).symm)

/-- Evaluation on the top open preserves epimorphisms when the space has a
global point. -/
theorem sheafSectionsTop_preservesEpimorphisms_of_isGlobalPoint
    {X : TopCat.{u}} (x : X) (hx : TopologicalSpace.IsGlobalPoint x) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).PreservesEpimorphisms := by
  let e := sheafSectionsTopIsoStalkOfIsGlobalPoint x hx
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ ↦ Classical.dec _
  letI : (Sheaf.forget AddCommGrpCat.{u} X ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} x).IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction x).isLeftAdjoint
  exact Functor.PreservesEpimorphisms.iso_iff e |>.mpr inferInstance

end TopCat.Sheaf

namespace CategoryTheory.Sheaf

/-- Every positive sheaf-cohomology group vanishes on a space with a global
point. -/
theorem subsingleton_H_succ_of_isGlobalPoint
    {X : TopCat.{u}} (x : X) (hx : TopologicalSpace.IsGlobalPoint x)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (F.H (n + 1)) := by
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).PreservesEpimorphisms :=
    TopCat.Sheaf.sheafSectionsTop_preservesEpimorphisms_of_isGlobalPoint x hx
  let P := AddCommGrpCat.of (ULift.{u} ℤ)
  letI : Projective P := by
    let M := ModuleCat.of ℤ (ULift.{u} ℤ)
    letI : Projective M := inferInstance
    change Projective ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj M)
    infer_instance
  let J := Opens.grothendieckTopology X
  let adj := constantSheafAdj J AddCommGrpCat Limits.isTerminalTop
  letI : Projective ((constantSheaf J AddCommGrpCat).obj P) :=
    adj.map_projective P (by infer_instance)
  change Subsingleton
    (Abelian.Ext ((constantSheaf J AddCommGrpCat).obj P) F (n + 1))
  exact Abelian.Ext.subsingleton_of_projective _ F n

/-- Every positive sheaf-cohomology group vanishes on a space with a global
point, with the degree supplied as an inequality. -/
theorem subsingleton_H_of_isGlobalPoint
    {X : TopCat.{u}} (x : X) (hx : TopologicalSpace.IsGlobalPoint x)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (F.H i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [Nat.add_comm] using subsingleton_H_succ_of_isGlobalPoint x hx F n

end CategoryTheory.Sheaf
