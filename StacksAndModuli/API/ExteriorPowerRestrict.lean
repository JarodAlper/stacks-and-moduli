module

public import StacksAndModuli.API.ExteriorPowerQcoh

/-!
# Restriction of the exterior-power sheaf along open immersions

Supporting API with no Stacks Project counterpart of its own, consumed by the relative
Plücker embedding of **Theorem 2.1.1**: for an open immersion `f : X ⟶ Y` and a sheaf of
modules `M` on `Y`, the canonical identification

`Modules.exteriorPower (M.restrict f) n ≅ (Modules.exteriorPower M n).restrict f`.

The comparison presheaf morphism sends a wedge of sections over `U ⊆ X` to the
sheafification unit of `Y` applied over `f ''ᵁ U`; it is locally bijective because the
sieve conditions transfer along the open immersion, so the master lemma
`PresheafOfModules.sheafifyIsoOfLocallyBijective` applies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (n : ℕ)

/-- The ring transport of exterior powers along the section isomorphism of an open
immersion: `⋀[Γ(X,U)]^n Γ(M.restrict f, U) → ⋀[Γ(Y, f''U)]^n Γ(M, f''U)`. -/
noncomputable def restrictWedgeTransport (U : X.Opens) :
    letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
    letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
    haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
      ⟨fun r s m ↦ by
        show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
        rw [mul_smul]⟩
    (⋀[Γ(X, U)]^n Γ(M.restrict f, U) :
        Submodule Γ(X, U) (ExteriorAlgebra Γ(X, U) Γ(M.restrict f, U))) →ₗ[Γ(X, U)]
      (⋀[Γ(Y, f ''ᵁ U)]^n Γ(M, f ''ᵁ U) :
        Submodule Γ(Y, f ''ᵁ U) (ExteriorAlgebra Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))) :=
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
  letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
      rw [mul_smul]⟩
  let ι : Γ(M.restrict f, U) →ₗ[Γ(X, U)] Γ(M, f ''ᵁ U) :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exteriorPower.mapSemilinear Γ(X, U) Γ(Y, f ''ᵁ U) n Γ(M.restrict f, U) ι

@[simp]
lemma restrictWedgeTransport_ιMulti (U : X.Opens) (m : Fin n → Γ(M.restrict f, U)) :
    restrictWedgeTransport f M n U (exteriorPower.ιMulti Γ(X, U) n m) =
      exteriorPower.ιMulti Γ(Y, f ''ᵁ U) n
        (fun i ↦ show Γ(M, f ''ᵁ U) from m i) := by
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
  letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
      rw [mul_smul]⟩
  let ι : Γ(M.restrict f, U) →ₗ[Γ(X, U)] Γ(M, f ''ᵁ U) :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact exteriorPower.mapSemilinear_ιMulti Γ(X, U) Γ(Y, f ''ᵁ U) n Γ(M.restrict f, U) ι m

lemma appIso_inv_hom_apply (U : X.Opens) (s : Γ(Y, f ''ᵁ U)) :
    (f.appIso U).inv.hom ((f.appIso U).hom.hom s) = s := by
  have := (f.appIso U).hom_inv_id
  calc (f.appIso U).inv.hom ((f.appIso U).hom.hom s)
      = ((f.appIso U).hom ≫ (f.appIso U).inv).hom s := rfl
    _ = s := by rw [this]; rfl

lemma appIso_hom_inv_apply (U : X.Opens) (r : Γ(X, U)) :
    (f.appIso U).hom.hom ((f.appIso U).inv.hom r) = r := by
  have := (f.appIso U).inv_hom_id
  calc (f.appIso U).hom.hom ((f.appIso U).inv.hom r)
      = ((f.appIso U).inv ≫ (f.appIso U).hom).hom r := rfl
    _ = r := by rw [this]; rfl

set_option maxHeartbeats 1600000 in
/-- The ring transport of exterior powers along an open immersion is bijective. -/
lemma restrictWedgeTransport_bijective (U : X.Opens) :
    Function.Bijective (restrictWedgeTransport f M n U) := by
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
  letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
      rw [mul_smul]⟩
  letI : Algebra Γ(Y, f ''ᵁ U) Γ(X, U) := ((f.appIso U).hom.hom).toAlgebra
  letI : Module Γ(Y, f ''ᵁ U) Γ(M.restrict f, U) :=
    Module.compHom _ ((f.appIso U).hom.hom)
  haveI : IsScalarTower Γ(Y, f ''ᵁ U) Γ(X, U) Γ(M.restrict f, U) :=
    ⟨fun s r m ↦ by
      show (((f.appIso U).hom.hom s) * r) • m = ((f.appIso U).hom.hom s) • r • m
      rw [mul_smul]⟩
  let ι' : Γ(M, f ''ᵁ U) →ₗ[Γ(Y, f ''ᵁ U)] Γ(M.restrict f, U) :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun s m ↦ by
        show (s : Γ(Y, f ''ᵁ U)) • m =
          ((f.appIso U).inv.hom ((f.appIso U).hom.hom s)) • m
        rw [appIso_inv_hom_apply] }
  let σ := exteriorPower.mapSemilinear Γ(Y, f ''ᵁ U) Γ(X, U) n Γ(M, f ''ᵁ U) ι'
  constructor
  · -- injectivity: `σ` is a left inverse on the span of the generators
    have hleft : ∀ w, σ (restrictWedgeTransport f M n U w) = w := by
      intro w
      have hw : w ∈ Submodule.span Γ(X, U)
          (Set.range (exteriorPower.ιMulti Γ(X, U) n (M := Γ(M.restrict f, U)))) := by
        rw [exteriorPower.ιMulti_span]
        trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨m, rfl⟩ := hw
        rw [restrictWedgeTransport_ιMulti]
        exact exteriorPower.mapSemilinear_ιMulti Γ(Y, f ''ᵁ U) Γ(X, U) n
          Γ(M, f ''ᵁ U) ι' _
      | zero => rw [map_zero, map_zero]
      | add u v hu hv h1 h2 => rw [map_add, map_add, h1, h2]
      | smul r w hw h1 =>
        have hstep : restrictWedgeTransport f M n U (r • w) =
            ((f.appIso U).inv.hom r) • restrictWedgeTransport f M n U w := by
          rw [LinearMap.map_smul]
          rfl
        rw [hstep]
        have hstep2 : σ (((f.appIso U).inv.hom r) •
            restrictWedgeTransport f M n U w) =
            ((f.appIso U).hom.hom ((f.appIso U).inv.hom r)) •
              σ (restrictWedgeTransport f M n U w) := by
          rw [LinearMap.map_smul]
          rfl
        rw [hstep2, appIso_hom_inv_apply, h1]
    exact Function.LeftInverse.injective hleft
  · -- surjectivity: the image is stable under the target scalars via the ring iso
    intro w
    have hw : w ∈ Submodule.span Γ(Y, f ''ᵁ U)
        (Set.range (exteriorPower.ιMulti Γ(Y, f ''ᵁ U) n (M := Γ(M, f ''ᵁ U)))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      exact ⟨exteriorPower.ιMulti Γ(X, U) n
        (fun i ↦ show Γ(M.restrict f, U) from m i),
        restrictWedgeTransport_ιMulti f M n U _⟩
    | zero => exact ⟨0, map_zero _⟩
    | add u v hu hv h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | smul s w hw h1 =>
      obtain ⟨a, ha⟩ := h1
      refine ⟨((f.appIso U).hom.hom s) • a, ?_⟩
      have hstep : restrictWedgeTransport f M n U
          (((f.appIso U).hom.hom s) • a) =
          ((f.appIso U).inv.hom ((f.appIso U).hom.hom s)) •
            restrictWedgeTransport f M n U a := by
        rw [LinearMap.map_smul]
        rfl
      rw [hstep, appIso_inv_hom_apply, ha]

/-- The section-level component of the restriction comparison: the `Γ(X, U)`-linear map
from the exterior power of the restricted sections into the sections of the restricted
exterior-power sheaf, via the sheafification unit of `Y` over `f ''ᵁ U`. -/
noncomputable def restrictWedgeApp (U : X.Opens) :
    (⋀[Γ(X, U)]^n Γ(M.restrict f, U) :
        Submodule Γ(X, U) (ExteriorAlgebra Γ(X, U) Γ(M.restrict f, U))) →ₗ[Γ(X, U)]
      Γ((Scheme.Modules.exteriorPower M n).restrict f, U) :=
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
  letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
      rw [mul_smul]⟩
  { toFun := fun w ↦
      show Γ((Scheme.Modules.exteriorPower M n).restrict f, U) from
        ((Scheme.Modules.toExteriorPower M n).app (.op (f ''ᵁ U))).hom
          (restrictWedgeTransport f M n U w)
    map_add' := fun u v ↦ by
      dsimp only
      rw [map_add, map_add]
    map_smul' := fun r w ↦ by
      dsimp only [RingHom.id_apply]
      rw [LinearMap.map_smul,
        ← algebraMap_smul (R := Γ(X, U)) Γ(Y, f ''ᵁ U) r
          (restrictWedgeTransport f M n U w),
        LinearMap.map_smul]
      rfl }

lemma restrictWedgeApp_ιMulti (U : X.Opens) (m : Fin n → Γ(M.restrict f, U)) :
    restrictWedgeApp f M n U (exteriorPower.ιMulti Γ(X, U) n m) =
      ((Scheme.Modules.toExteriorPower M n).app (.op (f ''ᵁ U))).hom
        (exteriorPower.ιMulti Γ(Y, f ''ᵁ U) n
          (fun i ↦ show Γ(M, f ''ᵁ U) from m i)) := by
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
  letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
      rw [mul_smul]⟩
  let ι : Γ(M.restrict f, U) →ₗ[Γ(X, U)] Γ(M, f ''ᵁ U) :=
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact congrArg (((Scheme.Modules.toExteriorPower M n).app (.op (f ''ᵁ U))).hom)
    (exteriorPower.mapSemilinear_ιMulti Γ(X, U) Γ(Y, f ''ᵁ U) n Γ(M.restrict f, U) ι m)

set_option maxHeartbeats 3200000 in
/-- The restriction comparison of exterior-power presheaves: over `U ⊆ X`, apply the
sheafification unit of `Y` over `f ''ᵁ U`. -/
noncomputable def restrictWedge :
    Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n ⟶
      (_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        ((Scheme.Modules.exteriorPower M n).restrict f).val where
  app U := ModuleCat.ofHom (restrictWedgeApp f M n U.unop)
  naturality {U V} g := by
    letI : Module ((X.sheaf.val).obj V)
        Γ((Scheme.Modules.exteriorPower M n).restrict f, V.unop) :=
      inferInstanceAs (Module Γ(X, V.unop)
        Γ((Scheme.Modules.exteriorPower M n).restrict f, V.unop))
    letI : Module ((X.sheaf.val).obj U)
        Γ((Scheme.Modules.exteriorPower M n).restrict f, U.unop) :=
      inferInstanceAs (Module Γ(X, U.unop)
        Γ((Scheme.Modules.exteriorPower M n).restrict f, U.unop))
    change _root_.PresheafOfModules.exteriorPowerObjMap (R := X.sheaf.val)
        (M := ((M.restrict f).val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n g ≫
        (ModuleCat.restrictScalars
          ((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map g).hom).map
            (ModuleCat.ofHom (restrictWedgeApp f M n V.unop)) =
      ModuleCat.ofHom (restrictWedgeApp f M n U.unop) ≫
        (((_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
          ((Scheme.Modules.exteriorPower M n).restrict f).val).map g)
    ext m
    have a1 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := X.sheaf.val)
      (M := ((M.restrict f).val : _root_.PresheafOfModules.{u}
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n g m
    have b1 := congrArg (restrictWedgeApp f M n V.unop) a1
    have b2 := restrictWedgeApp_ιMulti f M n V.unop
      (fun i ↦ show Γ(M.restrict f, V.unop) from (M.restrict f).val.map g (m i))
    have b3 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := Y.sheaf.val)
      (M := (M.val : _root_.PresheafOfModules.{u}
        (Y.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n
      (f.opensFunctor.map g.unop).op
      (fun i ↦ show Γ(M, f ''ᵁ U.unop) from m i)
    have b4 := _root_.PresheafOfModules.naturality_apply
      (Scheme.Modules.toExteriorPower M n) (f.opensFunctor.map g.unop).op
      (exteriorPower.ιMulti Γ(Y, f ''ᵁ U.unop) n
        (fun i ↦ show Γ(M, f ''ᵁ U.unop) from m i))
    have b5 := restrictWedgeApp_ιMulti f M n U.unop m
    exact b1.trans (b2.trans ((congrArg (((Scheme.Modules.toExteriorPower M n).app
      (.op (f ''ᵁ V.unop))).hom) b3.symm).trans (b4.trans
        (congrArg (ConcreteCategory.hom
          (((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
            (Scheme.Modules.exteriorPower M n).val).map
              (f.opensFunctor.map g.unop).op)) b5.symm))))

/-- **Local surjectivity of the restriction comparison**. -/
theorem isLocallySurjective_restrictWedge :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      ((_root_.PresheafOfModules.toPresheaf _).map (restrictWedge f M n)) := by
  constructor
  intro U t x hx
  obtain ⟨W, fW, hf, hfx⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥Y)
    ((_root_.PresheafOfModules.toPresheaf _).map
      (Scheme.Modules.toExteriorPower M n))
    (U := Opposite.op (f ''ᵁ U))
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
        (Scheme.Modules.exteriorPower M n).val)).obj (Opposite.op (f ''ᵁ U))) from t)
    (f.base x) ⟨x, hx, rfl⟩
  obtain ⟨w, hw⟩ := hf
  have hfVW : f ''ᵁ (U ⊓ f ⁻¹ᵁ W) ≤ W :=
    le_trans (f.image_mono inf_le_right) (f.image_preimage_le W)
  obtain ⟨v, hv⟩ := (restrictWedgeTransport_bijective f M n (U ⊓ f ⁻¹ᵁ W)).2
    (show (⋀[Γ(Y, f ''ᵁ (U ⊓ f ⁻¹ᵁ W))]^n Γ(M, f ''ᵁ (U ⊓ f ⁻¹ᵁ W)) :
        Submodule Γ(Y, f ''ᵁ (U ⊓ f ⁻¹ᵁ W))
          (ExteriorAlgebra Γ(Y, f ''ᵁ (U ⊓ f ⁻¹ᵁ W)) Γ(M, f ''ᵁ (U ⊓ f ⁻¹ᵁ W)))) from
      (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).obj
          (Scheme.Modules.exteriorPowerPresheaf M n)).map (homOfLE hfVW).op)) w)
  refine ⟨U ⊓ f ⁻¹ᵁ W, homOfLE inf_le_left, ⟨v, ?_⟩,
    ⟨hx, show f.base x ∈ W from hfx⟩⟩
  have c2 := congrArg (((Scheme.Modules.toExteriorPower M n).app
    (.op (f ''ᵁ (U ⊓ f ⁻¹ᵁ W)))).hom) hv
  have c3 := _root_.PresheafOfModules.naturality_apply
    (Scheme.Modules.toExteriorPower M n) (homOfLE hfVW).op w
  have c4 := congrArg (ConcreteCategory.hom
    (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
        (Scheme.Modules.exteriorPower M n).val)).map (homOfLE hfVW).op)) hw
  have c5 : (ConcreteCategory.hom
      (((_root_.PresheafOfModules.toPresheaf _).obj
        ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
          (Scheme.Modules.exteriorPower M n).val)).map (homOfLE hfVW).op))
      ((ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).obj
          ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
            (Scheme.Modules.exteriorPower M n).val)).map fW.op))
        (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
          ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
            (Scheme.Modules.exteriorPower M n).val)).obj
              (Opposite.op (f ''ᵁ U))) from t)) =
      (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).obj
          ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
            (Scheme.Modules.exteriorPower M n).val)).map
              ((homOfLE hfVW ≫ fW)).op))
        (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
          ((_root_.PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
            (Scheme.Modules.exteriorPower M n).val)).obj
              (Opposite.op (f ''ᵁ U))) from t) := by
    rw [show ((homOfLE hfVW ≫ fW)).op = fW.op ≫ (homOfLE hfVW).op from rfl,
      Functor.map_comp]
    rfl
  exact c2.trans (c3.trans (c4.trans c5))

set_option maxHeartbeats 3200000 in
/-- The ring transport commutes with restriction: the exterior-power presheaf square
along an open immersion. -/
lemma restrictWedgeTransport_naturality {U V : X.Opens} (h : V ≤ U)
    (w : (⋀[Γ(X, U)]^n Γ(M.restrict f, U) :
      Submodule Γ(X, U) (ExteriorAlgebra Γ(X, U) Γ(M.restrict f, U)))) :
    restrictWedgeTransport f M n V
        (((Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).map
          (homOfLE h).op).hom w) =
      ((Scheme.Modules.exteriorPowerPresheaf M n).map
        (homOfLE (f.image_mono h)).op).hom (restrictWedgeTransport f M n U w) := by
  have hw : w ∈ Submodule.span Γ(X, U)
      (Set.range (exteriorPower.ιMulti Γ(X, U) n (M := Γ(M.restrict f, U)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, rfl⟩ := hw
    have a1 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := X.sheaf.val)
      (M := ((M.restrict f).val : _root_.PresheafOfModules.{u}
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n (homOfLE h).op m
    have b1 := congrArg (restrictWedgeTransport f M n V) a1
    have b2 := restrictWedgeTransport_ιMulti f M n V
      (fun i ↦ show Γ(M.restrict f, V) from (M.restrict f).val.map (homOfLE h).op (m i))
    have b3 := restrictWedgeTransport_ιMulti f M n U m
    have b4 := congrArg (((Scheme.Modules.exteriorPowerPresheaf M n).map
      (homOfLE (f.image_mono h)).op).hom) b3
    have b5 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := Y.sheaf.val)
      (M := (M.val : _root_.PresheafOfModules.{u}
        (Y.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n
      (homOfLE (f.image_mono h)).op
      (fun i ↦ show Γ(M, f ''ᵁ U) from m i)
    exact b1.trans (b2.trans ((b4.trans b5).symm))
  | zero =>
    rw [map_zero, map_zero, map_zero, map_zero]
  | add u v hu hv h1 h2 =>
    rw [map_add, map_add, map_add, map_add, h1, h2]
  | smul r w hw h1 =>
    letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := ((f.appIso U).inv.hom).toAlgebra
    letI : Module Γ(X, U) Γ(M, f ''ᵁ U) := Module.compHom _ ((f.appIso U).inv.hom)
    haveI : IsScalarTower Γ(X, U) Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) :=
      ⟨fun r s m ↦ by
        show (((f.appIso U).inv.hom r) * s) • m = ((f.appIso U).inv.hom r) • s • m
        rw [mul_smul]⟩
    letI : Algebra Γ(X, V) Γ(Y, f ''ᵁ V) := ((f.appIso V).inv.hom).toAlgebra
    letI : Module Γ(X, V) Γ(M, f ''ᵁ V) := Module.compHom _ ((f.appIso V).inv.hom)
    haveI : IsScalarTower Γ(X, V) Γ(Y, f ''ᵁ V) Γ(M, f ''ᵁ V) :=
      ⟨fun r s m ↦ by
        show (((f.appIso V).inv.hom r) * s) • m = ((f.appIso V).inv.hom r) • s • m
        rw [mul_smul]⟩
    have hring : ((f.appIso V).inv.hom) (((X.presheaf.map (homOfLE h).op)).hom r) =
        ((Y.presheaf.map (homOfLE (f.image_mono h)).op)).hom
          (((f.appIso U).inv.hom) r) := by
      have hnat := f.appIso_inv_naturality (U := U) (V := V) (homOfLE h).op
      exact CategoryTheory.congr_fun hnat r
    have hXmap : ((Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).map
        (homOfLE h).op).hom (r • w) =
        ((X.presheaf.map (homOfLE h).op)).hom r •
          ((Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).map
            (homOfLE h).op).hom w := by
      exact _root_.PresheafOfModules.map_smul _ _ _ _
    have htrV : ∀ (s : Γ(X, V)) (v : (⋀[Γ(X, V)]^n Γ(M.restrict f, V) :
        Submodule Γ(X, V) (ExteriorAlgebra Γ(X, V) Γ(M.restrict f, V)))),
        restrictWedgeTransport f M n V (s • v) =
          ((f.appIso V).inv.hom s) • restrictWedgeTransport f M n V v := by
      intro s v
      rw [LinearMap.map_smul]
      rfl
    have htrU : restrictWedgeTransport f M n U (r • w) =
        ((f.appIso U).inv.hom r) • restrictWedgeTransport f M n U w := by
      rw [LinearMap.map_smul]
      rfl
    have hYmap : ((Scheme.Modules.exteriorPowerPresheaf M n).map
        (homOfLE (f.image_mono h)).op).hom
          (((f.appIso U).inv.hom r) • restrictWedgeTransport f M n U w) =
        ((Y.presheaf.map (homOfLE (f.image_mono h)).op)).hom
            (((f.appIso U).inv.hom) r) •
          ((Scheme.Modules.exteriorPowerPresheaf M n).map
            (homOfLE (f.image_mono h)).op).hom
              (restrictWedgeTransport f M n U w) := by
      exact _root_.PresheafOfModules.map_smul _ _ _ _
    rw [hXmap, htrV, h1, htrU, hYmap, hring]

set_option maxHeartbeats 6400000 in
/-- **Local injectivity of the restriction comparison**. -/
theorem isLocallyInjective_restrictWedge :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      ((_root_.PresheafOfModules.toPresheaf _).map (restrictWedge f M n)) := by
  constructor
  intro U w w' h x hx
  have hunit := Presheaf.IsLocallyInjective.equalizerSieve_mem
    (J := Opens.grothendieckTopology ↥Y)
    (φ := (_root_.PresheafOfModules.toPresheaf _).map
      (Scheme.Modules.toExteriorPower M n))
    (X := Opposite.op (f ''ᵁ U.unop))
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf M n)).obj
          (Opposite.op (f ''ᵁ U.unop))) from
      restrictWedgeTransport f M n U.unop w)
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf M n)).obj
          (Opposite.op (f ''ᵁ U.unop))) from
      restrictWedgeTransport f M n U.unop w') h
  obtain ⟨W, fW, hfW, hfx⟩ := hunit (f.base x) ⟨x, hx, rfl⟩
  have hfVW : f ''ᵁ (U.unop ⊓ f ⁻¹ᵁ W) ≤ W :=
    le_trans (f.image_mono inf_le_right) (f.image_preimage_le W)
  refine ⟨U.unop ⊓ f ⁻¹ᵁ W, homOfLE inf_le_left, ?_,
    ⟨hx, show f.base x ∈ W from hfx⟩⟩
  show ((Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).map
      (homOfLE (inf_le_left : U.unop ⊓ f ⁻¹ᵁ W ≤ U.unop)).op).hom w =
    ((Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).map
      (homOfLE (inf_le_left : U.unop ⊓ f ⁻¹ᵁ W ≤ U.unop)).op).hom w'
  refine (restrictWedgeTransport_bijective f M n (U.unop ⊓ f ⁻¹ᵁ W)).1 ?_
  rw [restrictWedgeTransport_naturality f M n inf_le_left w,
    restrictWedgeTransport_naturality f M n inf_le_left w']
  -- the equalizer condition on `W`, restricted to `f ''ᵁ V`
  have hstep := congrArg (ConcreteCategory.hom
    (((_root_.PresheafOfModules.toPresheaf _).obj
      (Scheme.Modules.exteriorPowerPresheaf M n)).map (homOfLE hfVW).op)) hfW
  have hsplit : ∀ (a : ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      (Scheme.Modules.exteriorPowerPresheaf M n)).obj
        (Opposite.op (f ''ᵁ U.unop)))),
      ((Scheme.Modules.exteriorPowerPresheaf M n).map
        (homOfLE (f.image_mono (inf_le_left : U.unop ⊓ f ⁻¹ᵁ W ≤ U.unop))).op).hom a =
      (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).obj
          (Scheme.Modules.exteriorPowerPresheaf M n)).map (homOfLE hfVW).op))
        ((ConcreteCategory.hom
          (((_root_.PresheafOfModules.toPresheaf _).obj
            (Scheme.Modules.exteriorPowerPresheaf M n)).map fW.op)) a) := by
    intro a
    exact _root_.PresheafOfModules.map_comp_apply
      (M := Scheme.Modules.exteriorPowerPresheaf M n) fW.op (homOfLE hfVW).op a
  exact (hsplit _).trans (hstep.trans (hsplit _).symm)

/-- **Restriction compatibility of the exterior-power sheaf**: along an open immersion,
the exterior power of the restriction is the restriction of the exterior power. -/
noncomputable def restrictExteriorPowerIso :
    Scheme.Modules.exteriorPower (M.restrict f) n ≅
      (Scheme.Modules.exteriorPower M n).restrict f :=
  _root_.PresheafOfModules.sheafifyIsoOfLocallyBijective (𝟙 X.ringCatSheaf.val)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (Scheme.Modules.exteriorPowerPresheaf (M.restrict f) n).presheaf)
    (restrictWedge f M n)
    (isLocallyInjective_restrictWedge f M n)
    (isLocallySurjective_restrictWedge f M n)

end AlgebraicGeometry

end
