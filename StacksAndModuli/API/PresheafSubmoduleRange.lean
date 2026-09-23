module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Ranges of morphisms of presheaves of modules

Supporting API with no Stacks Project counterpart.

Mathlib's `PresheafOfModules.Submodule` provides the lattice of restriction-stable
sectionwise submodules of a presheaf of modules. This file adds the operations the
relative Grassmannian development (§2.1–§2.2) consumes: the sectionwise **range** of a
morphism, transport of a submodule along an isomorphism of ambients, and the two
comparison lemmas — the range of a composite with an isomorphism is the transported
range, and precomposition with an isomorphism does not change the range. Together these
let the kernel of a quotient of sheaves of modules be tracked as a sectionwise
submodule datum, invariantly under the ambient identifications produced by pullback
functors.

Main declarations:
- `PresheafOfModules.Submodule.range`;
- `PresheafOfModules.Submodule.mapIso`;
- `PresheafOfModules.Submodule.range_comp_iso`;
- `PresheafOfModules.Submodule.range_eq_of_iso`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The sectionwise range of a morphism of presheaves of modules, as a submodule of
the target. Stability under restriction is naturality of the morphism. -/
noncomputable def range {K M : PresheafOfModules.{v} R} (f : K ⟶ M) : M.Submodule where
  obj X := LinearMap.range (f.app X).hom
  map {X Y} g := by
    intro x hx
    obtain ⟨n, rfl⟩ := LinearMap.mem_range.mp hx
    exact Submodule.mem_comap.mpr
      (LinearMap.mem_range.mpr ⟨K.map g n, naturality_apply f g n⟩)

@[simp]
lemma range_obj {K M : PresheafOfModules.{v} R} (f : K ⟶ M) (X : Cᵒᵖ) :
    (range f).obj X = LinearMap.range (f.app X).hom := rfl

/-- Transport of a submodule along an isomorphism of ambient presheaves of modules. -/
noncomputable def mapIso {M M' : PresheafOfModules.{v} R} (N : M.Submodule)
    (e : M ≅ M') : M'.Submodule where
  obj X := (N.obj X).map (e.hom.app X).hom
  map {X Y} g := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_comap.mpr
      (Submodule.mem_map.mpr ⟨M.map g m, N.map_mem g hm, naturality_apply e.hom g m⟩)

@[simp]
lemma mapIso_obj {M M' : PresheafOfModules.{v} R} (N : M.Submodule) (e : M ≅ M')
    (X : Cᵒᵖ) : (N.mapIso e).obj X = (N.obj X).map (e.hom.app X).hom := rfl

/-- Transport along a composite isomorphism is iterated transport. -/
lemma mapIso_trans {M M' M'' : PresheafOfModules.{v} R} (N : M.Submodule)
    (e : M ≅ M') (e' : M' ≅ M'') :
    (N.mapIso e).mapIso e' = N.mapIso (e ≪≫ e') := by
  refine (PresheafOfModules.Submodule.ext fun X ↦ ?_).symm
  change (N.obj X).map (((e ≪≫ e').hom.app X)).hom = _
  rw [show ((e ≪≫ e').hom.app X) = e.hom.app X ≫ e'.hom.app X from rfl,
    ModuleCat.hom_comp]
  exact Submodule.map_comp _ _ (N.obj X)

lemma hom_mem_mapIso {M M' : PresheafOfModules.{v} R} (N : M.Submodule) (e : M ≅ M')
    (X : Cᵒᵖ) (x : M.obj X) (hx : x ∈ N.obj X) :
    e.hom.app X x ∈ (N.mapIso e).obj X :=
  ⟨x, hx, rfl⟩

lemma mem_of_eq {M : PresheafOfModules.{v} R} {N N' : M.Submodule} (h : N = N')
    {X : Cᵒᵖ} {x : M.obj X} (hx : x ∈ N.obj X) : x ∈ N'.obj X := h ▸ hx

lemma mem_range_iff {K M : PresheafOfModules.{v} R} (f : K ⟶ M) (X : Cᵒᵖ)
    (x : M.obj X) : x ∈ (range f).obj X ↔ ∃ t, f.app X t = x :=
  LinearMap.mem_range

/-- The range of a composite with an isomorphism is the transported range. -/
lemma range_comp_iso {K M M' : PresheafOfModules.{v} R} (f : K ⟶ M) (e : M ≅ M') :
    range (f ≫ e.hom) = (range f).mapIso e := by
  refine PresheafOfModules.Submodule.ext fun X ↦ ?_
  change LinearMap.range ((f.app X ≫ e.hom.app X)).hom = _
  rw [ModuleCat.hom_comp]
  exact LinearMap.range_comp _ _

/-- Precomposition with an isomorphism does not change the sectionwise range. -/
lemma range_eq_of_iso {K K' M : PresheafOfModules.{v} R} (f : K ⟶ M) (g : K' ⟶ M)
    (e : K ≅ K') (h : e.hom ≫ g = f) : range f = range g := by
  subst h
  refine PresheafOfModules.Submodule.ext fun X ↦ ?_
  change LinearMap.range ((e.hom.app X ≫ g.app X)).hom = LinearMap.range (g.app X).hom
  rw [ModuleCat.hom_comp, LinearMap.range_comp]
  have hiso : IsIso (e.hom.app X) := by
    change IsIso ((evaluation R X).map e.hom)
    infer_instance
  rw [LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso (e.hom.app X)).2,
    Submodule.map_top]

section RangeLE

variable {K K' M : PresheafOfModules.{v} R}

/-- Sectionwise lift of `f` through a monomorphism `g` whose sectionwise range
contains that of `f`. -/
noncomputable def rangeLELift (f : K ⟶ M) (g : K' ⟶ M) [Mono g]
    (h : range f ≤ range g) (X : Cᵒᵖ) :
    K.obj X →ₗ[R.obj X] K'.obj X :=
  ((LinearEquiv.ofInjective (g.app X).hom
      (PresheafOfModules.injective_of_mono g X)).symm.toLinearMap.comp
    ((Submodule.inclusion (h X)).comp (f.app X).hom.rangeRestrict))

lemma app_rangeLELift (f : K ⟶ M) (g : K' ⟶ M) [Mono g]
    (h : range f ≤ range g) (X : Cᵒᵖ) (m : K.obj X) :
    g.app X (rangeLELift f g h X m) = f.app X m := by
  dsimp [rangeLELift]
  simp

/-- Lift of a morphism through a monomorphism with larger sectionwise range. -/
noncomputable def homOfRangeLE (f : K ⟶ M) (g : K' ⟶ M) [Mono g]
    (h : range f ≤ range g) : K ⟶ K' :=
  homMk
    { app := fun X ↦ AddCommGrpCat.ofHom (rangeLELift f g h X).toAddMonoidHom
      naturality := fun {X Y} ρ ↦ by
        ext m
        apply PresheafOfModules.injective_of_mono g Y
        change g.app Y (rangeLELift f g h Y (K.map ρ m)) =
          g.app Y (K'.map ρ (rangeLELift f g h X m))
        calc g.app Y (rangeLELift f g h Y (K.map ρ m))
            = f.app Y (K.map ρ m) := app_rangeLELift f g h Y _
          _ = M.map ρ (f.app X m) := naturality_apply f ρ m
          _ = M.map ρ (g.app X (rangeLELift f g h X m)) := by
              rw [app_rangeLELift]
          _ = g.app Y (K'.map ρ (rangeLELift f g h X m)) :=
              (naturality_apply g ρ _).symm }
    (fun X r m ↦ (rangeLELift f g h X).map_smul r m)

@[reassoc (attr := simp)]
lemma homOfRangeLE_comp (f : K ⟶ M) (g : K' ⟶ M) [Mono g]
    (h : range f ≤ range g) :
    homOfRangeLE f g h ≫ g = f := by
  ext X m
  exact app_rangeLELift f g h X m

/-- Two monomorphisms into a presheaf of modules with equal sectionwise ranges have
isomorphic sources. -/
noncomputable def isoOfRangeEq (f : K ⟶ M) (g : K' ⟶ M) [Mono f] [Mono g]
    (h : range f = range g) : K ≅ K' :=
  Subobject.isoOfMkEqMk f g (le_antisymm
    (Subobject.mk_le_mk_of_comm (homOfRangeLE f g h.le)
      (homOfRangeLE_comp f g h.le))
    (Subobject.mk_le_mk_of_comm (homOfRangeLE g f h.ge)
      (homOfRangeLE_comp g f h.ge)))

@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_comp (f : K ⟶ M) (g : K' ⟶ M) [Mono f] [Mono g]
    (h : range f = range g) :
    (isoOfRangeEq f g h).hom ≫ g = f :=
  Subobject.ofMkLEMk_comp _

end RangeLE

end PresheafOfModules.Submodule

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : CategoryTheory.GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{u}}

/-- Two monomorphisms of sheaves of modules into a common ambient sheaf with equal
sectionwise ranges of their underlying presheaf morphisms have isomorphic sources.
Stated with the ambient sheaf explicit for dot-notation at call sites. -/
noncomputable def isoOfRangeEq (M : SheafOfModules.{v} R) {K K' : SheafOfModules.{v} R}
    (f : K ⟶ M) (g : K' ⟶ M) [Mono f.val] [Mono g.val]
    (h : Submodule.range f.val = Submodule.range g.val) : K ≅ K' :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (Submodule.isoOfRangeEq f.val g.val h)

@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_comp (M : SheafOfModules.{v} R) {K K' : SheafOfModules.{v} R}
    (f : K ⟶ M) (g : K' ⟶ M) [Mono f.val] [Mono g.val]
    (h : Submodule.range f.val = Submodule.range g.val) :
    (M.isoOfRangeEq f g h).hom ≫ g = f := by
  apply (SheafOfModules.fullyFaithfulForget R).map_injective
  rw [Functor.map_comp,
    show (SheafOfModules.forget R).map (M.isoOfRangeEq f g h).hom =
        (Submodule.isoOfRangeEq f.val g.val h).hom from
      (SheafOfModules.fullyFaithfulForget R).map_preimage _]
  exact Submodule.isoOfRangeEq_hom_comp f.val g.val h

open CategoryTheory.Limits in
/-- Postcomposing with an isomorphism does not change the sectionwise range of the
kernel inclusion. -/
lemma kernelRange_comp_isIso [HasZeroMorphisms (SheafOfModules.{v} R)]
    {M Q Q' : SheafOfModules.{v} R} (π : M ⟶ Q) (u : Q ≅ Q')
    [HasKernel π] [HasKernel (π ≫ u.hom)] :
    PresheafOfModules.Submodule.range (kernel.ι (π ≫ u.hom)).val =
      PresheafOfModules.Submodule.range (kernel.ι π).val := by
  let eK : kernel (π ≫ u.hom) ≅ kernel π :=
    kernel.mapIso (π ≫ u.hom) π (Iso.refl _) u.symm (by simp)
  have he : eK.hom ≫ kernel.ι π = kernel.ι (π ≫ u.hom) := by
    have h0 : eK.hom ≫ kernel.ι π = kernel.ι (π ≫ u.hom) ≫ (Iso.refl M).hom := by
      dsimp [eK, kernel.mapIso, kernel.map]
      exact kernel.lift_ι _ _ _
    rw [Iso.refl_hom, Category.comp_id] at h0
    exact h0
  exact PresheafOfModules.Submodule.range_eq_of_iso _ _
    ((SheafOfModules.forget R).mapIso eK) (congrArg SheafOfModules.Hom.val he)

/-- Transport of submodules along the identity isomorphism is trivial. -/
lemma _root_.PresheafOfModules.Submodule.mapIso_refl
    {C₀ : Type u₁} [CategoryTheory.Category.{v₁} C₀] {R₀ : C₀ᵒᵖ ⥤ RingCat.{u}}
    {M : PresheafOfModules.{v} R₀} (N : M.Submodule) :
    N.mapIso (Iso.refl M) = N := by
  refine PresheafOfModules.Submodule.ext fun X ↦ ?_
  rw [PresheafOfModules.Submodule.mapIso_obj]
  exact Submodule.map_id _

/-- Transport of submodules along an isomorphism is injective. -/
lemma _root_.PresheafOfModules.Submodule.mapIso_injective
    {C₀ : Type u₁} [CategoryTheory.Category.{v₁} C₀] {R₀ : C₀ᵒᵖ ⥤ RingCat.{u}}
    {M M' : PresheafOfModules.{v} R₀} (e : M ≅ M')
    {N N' : M.Submodule} (h : N.mapIso e = N'.mapIso e) : N = N' := by
  have h2 := congrArg (fun A ↦ PresheafOfModules.Submodule.mapIso A e.symm) h
  beta_reduce at h2
  rw [PresheafOfModules.Submodule.mapIso_trans, PresheafOfModules.Submodule.mapIso_trans,
    Iso.self_symm_id, PresheafOfModules.Submodule.mapIso_refl,
    PresheafOfModules.Submodule.mapIso_refl] at h2
  exact h2

open CategoryTheory.Limits in
/-- Precomposing a quotient of sheaves of modules with an ambient isomorphism transports
the sectionwise range of its kernel inclusion through that isomorphism. -/
lemma kernelRange_comp_iso [HasZeroMorphisms (SheafOfModules.{v} R)]
    {M' M Q : SheafOfModules.{v} R} (π : M ⟶ Q) (e : M' ≅ M)
    [HasKernel π] [HasKernel (e.hom ≫ π)] :
    (PresheafOfModules.Submodule.range
        (kernel.ι (e.hom ≫ π)).val).mapIso
      ((SheafOfModules.forget R).mapIso e) =
    PresheafOfModules.Submodule.range (kernel.ι π).val := by
  let eK : kernel (e.hom ≫ π) ≅ kernel π :=
    kernel.mapIso (e.hom ≫ π) π e (Iso.refl _) (by simp)
  have he : eK.hom ≫ kernel.ι π = kernel.ι (e.hom ≫ π) ≫ e.hom := by
    dsimp [eK, kernel.mapIso, kernel.map]
    exact kernel.lift_ι _ _ _
  refine Eq.trans
    (PresheafOfModules.Submodule.range_comp_iso (kernel.ι (e.hom ≫ π)).val
      ((SheafOfModules.forget R).mapIso e)).symm
    (PresheafOfModules.Submodule.range_eq_of_iso _ (kernel.ι π).val
      ((SheafOfModules.forget R).mapIso eK)
      (congrArg SheafOfModules.Hom.val he))

open CategoryTheory.Limits in
/-- The sectionwise range of a kernel inclusion depends only on the morphism.  Use this instead
of `rw` on the morphism: the `HasKernel` instance mentions the morphism structurally, so
rewriting under `kernel.ι` reports `motive is not type correct` as soon as the instance is
found through `Functor.map` rather than generically. -/
lemma kernelRange_congr [HasZeroMorphisms (SheafOfModules.{v} R)]
    {M Q : SheafOfModules.{v} R} {f g : M ⟶ Q} [HasKernel f] [HasKernel g] (h : f = g) :
    PresheafOfModules.Submodule.range (kernel.ι f).val =
      PresheafOfModules.Submodule.range (kernel.ι g).val := by
  subst h; rfl

open CategoryTheory.Limits in
/-- Conjugating two quotients of a common source by an ambient isomorphism preserves
the comparison of their kernel ranges. -/
lemma kernelRange_precomp_iso_eq_of_eq [HasZeroMorphisms (SheafOfModules.{v} R)]
    {M' M Qa Qb : SheafOfModules.{v} R} (e : M' ≅ M) (πa : M ⟶ Qa) (πb : M ⟶ Qb)
    [HasKernel πa] [HasKernel πb] [HasKernel (e.hom ≫ πa)] [HasKernel (e.hom ≫ πb)]
    (h : PresheafOfModules.Submodule.range (kernel.ι πa).val =
      PresheafOfModules.Submodule.range (kernel.ι πb).val) :
    PresheafOfModules.Submodule.range (kernel.ι (e.hom ≫ πa)).val =
      PresheafOfModules.Submodule.range (kernel.ι (e.hom ≫ πb)).val := by
  refine PresheafOfModules.Submodule.mapIso_injective
    ((SheafOfModules.forget R).mapIso e) ?_
  rw [kernelRange_comp_iso πa e, kernelRange_comp_iso πb e]
  exact h

end SheafOfModules
