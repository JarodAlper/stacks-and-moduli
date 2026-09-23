module

public import StacksAndModuli.API.ExteriorPowerRestrict

/-!
# The pullback comparison for exterior-power sheaves

Supporting API with no Stacks Project counterpart of its own, consumed by the relative
Plücker embedding of **Theorem 2.1.1**: for a morphism of schemes `f : T ⟶ S` and a sheaf
of modules `V` on `S`, the canonical comparison morphism

`(Modules.pullback f).obj (Modules.exteriorPower V q) ⟶
  Modules.exteriorPower ((Modules.pullback f).obj V) q`,

the adjoint transpose of the wedge of the pullback-adjunction unit followed by the
sheafification unit.  (It is an isomorphism for quasi-coherent `V`; only the morphism and
its compatibilities are needed for the Plücker transformation, whose quotient targets are
epimorphic images.)
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

variable {T S : Scheme.{u}} (f : T ⟶ S) (V : S.Modules) (q : ℕ)

/-- The section-level component of the pullback comparison: the wedge of the
pullback-adjunction unit followed by the sheafification unit of `T` over `f ⁻¹ᵁ U`. -/
noncomputable def pullbackWedgeApp (U : S.Opens) :
    (⋀[Γ(S, U)]^q Γ(V, U) :
        Submodule Γ(S, U) (ExteriorAlgebra Γ(S, U) Γ(V, U))) →ₗ[Γ(S, U)]
      Γ((Scheme.Modules.pushforward f).obj
        (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q), U) :=
  letI : Algebra Γ(S, U) Γ(T, f ⁻¹ᵁ U) := ((f.app U).hom).toAlgebra
  letI : Module Γ(S, U) Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    Module.compHom _ ((f.app U).hom)
  haveI : IsScalarTower Γ(S, U) Γ(T, f ⁻¹ᵁ U)
      Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.app U).hom r) * s) • m = ((f.app U).hom r) • s • m
      rw [mul_smul]⟩
  let ι : Γ(V, U) →ₗ[Γ(S, U)] Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    { toFun := fun m ↦
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U).hom m
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r m ↦
        Scheme.Modules.Hom.app_smul
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V) r m }
  { toFun := fun w ↦
      show Γ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q), U) from
        ((Scheme.Modules.toExteriorPower ((Scheme.Modules.pullback f).obj V) q).app
          (.op (f ⁻¹ᵁ U))).hom
          (exteriorPower.mapSemilinear Γ(S, U) Γ(T, f ⁻¹ᵁ U) q Γ(V, U) ι w)
    map_add' := fun u v ↦ by
      dsimp only
      rw [map_add, map_add]
    map_smul' := fun r w ↦ by
      dsimp only [RingHom.id_apply]
      rw [LinearMap.map_smul,
        ← algebraMap_smul (R := Γ(S, U)) Γ(T, f ⁻¹ᵁ U) r
          (exteriorPower.mapSemilinear Γ(S, U) Γ(T, f ⁻¹ᵁ U) q Γ(V, U) ι w),
        LinearMap.map_smul]
      rfl }

lemma pullbackWedgeApp_ιMulti (U : S.Opens) (m : Fin q → Γ(V, U)) :
    pullbackWedgeApp f V q U (exteriorPower.ιMulti Γ(S, U) q m) =
      ((Scheme.Modules.toExteriorPower ((Scheme.Modules.pullback f).obj V) q).app
        (.op (f ⁻¹ᵁ U))).hom
        (exteriorPower.ιMulti Γ(T, f ⁻¹ᵁ U) q
          (fun i ↦ show Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) from
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U)
              (m i))) := by
  letI : Algebra Γ(S, U) Γ(T, f ⁻¹ᵁ U) := ((f.app U).hom).toAlgebra
  letI : Module Γ(S, U) Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    Module.compHom _ ((f.app U).hom)
  haveI : IsScalarTower Γ(S, U) Γ(T, f ⁻¹ᵁ U)
      Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    ⟨fun r s m ↦ by
      show (((f.app U).hom r) * s) • m = ((f.app U).hom r) • s • m
      rw [mul_smul]⟩
  let ι : Γ(V, U) →ₗ[Γ(S, U)] Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U) :=
    { toFun := fun m ↦
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U).hom m
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r m ↦
        Scheme.Modules.Hom.app_smul
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V) r m }
  exact congrArg (((Scheme.Modules.toExteriorPower
      ((Scheme.Modules.pullback f).obj V) q).app (.op (f ⁻¹ᵁ U))).hom)
    (exteriorPower.mapSemilinear_ιMulti Γ(S, U) Γ(T, f ⁻¹ᵁ U) q Γ(V, U) ι m)

set_option maxHeartbeats 3200000 in
/-- The pullback comparison of exterior-power presheaves: over `U ⊆ S`, the wedge of the
pullback-adjunction unit followed by the sheafification unit of `T` over `f ⁻¹ᵁ U`. -/
noncomputable def pullbackWedge :
    Scheme.Modules.exteriorPowerPresheaf V q ⟶
      (_root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.val)).obj
        ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q)).val where
  app U := ModuleCat.ofHom (pullbackWedgeApp f V q U.unop)
  naturality {U W} g := by
    letI : Module ((S.sheaf.val).obj W)
        Γ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q),
            W.unop) :=
      inferInstanceAs (Module Γ(S, W.unop)
        Γ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q),
            W.unop))
    letI : Module ((S.sheaf.val).obj U)
        Γ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q),
            U.unop) :=
      inferInstanceAs (Module Γ(S, U.unop)
        Γ((Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q),
            U.unop))
    change _root_.PresheafOfModules.exteriorPowerObjMap (R := S.sheaf.val)
        (M := (V.val : _root_.PresheafOfModules.{u}
          (S.sheaf.val ⋙ forget₂ CommRingCat RingCat))) q g ≫
        (ModuleCat.restrictScalars
          ((S.sheaf.val ⋙ forget₂ CommRingCat RingCat).map g).hom).map
            (ModuleCat.ofHom (pullbackWedgeApp f V q W.unop)) =
      ModuleCat.ofHom (pullbackWedgeApp f V q U.unop) ≫
        (((_root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.val)).obj
          ((Scheme.Modules.pushforward f).obj
            (Scheme.Modules.exteriorPower
              ((Scheme.Modules.pullback f).obj V) q)).val).map g)
    ext m
    have a1 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := S.sheaf.val)
      (M := (V.val : _root_.PresheafOfModules.{u}
        (S.sheaf.val ⋙ forget₂ CommRingCat RingCat))) q g m
    have b1 := congrArg (pullbackWedgeApp f V q W.unop) a1
    have b2 := pullbackWedgeApp_ιMulti f V q W.unop
      (fun i ↦ show Γ(V, W.unop) from V.val.map g (m i))
    have b3 := _root_.PresheafOfModules.exteriorPowerObjMap_ιMulti (R := T.sheaf.val)
      (M := (((Scheme.Modules.pullback f).obj V).val : _root_.PresheafOfModules.{u}
        (T.sheaf.val ⋙ forget₂ CommRingCat RingCat))) q
      ((Opens.map f.base).map g.unop).op
      (fun i ↦ show Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U.unop) from
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U.unop)
          (m i))
    have b4 := _root_.PresheafOfModules.naturality_apply
      (Scheme.Modules.toExteriorPower ((Scheme.Modules.pullback f).obj V) q)
      ((Opens.map f.base).map g.unop).op
      (exteriorPower.ιMulti Γ(T, f ⁻¹ᵁ U.unop) q
        (fun i ↦ show Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ U.unop) from
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U.unop)
            (m i)))
    have b5 := pullbackWedgeApp_ιMulti f V q U.unop m
    have hunitnat : ∀ i, (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          V).app W.unop) (V.val.map g (m i)) =
        (((Scheme.Modules.pullback f).obj V).val.map ((Opens.map f.base).map g.unop).op)
          ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app U.unop)
            (m i)) := by
      intro i
      exact _root_.PresheafOfModules.naturality_apply
        ((SheafOfModules.forget _).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V)) g (m i)
    have b2' : pullbackWedgeApp f V q W.unop
        (exteriorPower.ιMulti Γ(S, W.unop) q
          (fun i ↦ show Γ(V, W.unop) from V.val.map g (m i))) =
        ((Scheme.Modules.toExteriorPower ((Scheme.Modules.pullback f).obj V) q).app
          (.op (f ⁻¹ᵁ W.unop))).hom
          (exteriorPower.ιMulti Γ(T, f ⁻¹ᵁ W.unop) q
            (fun i ↦ show Γ((Scheme.Modules.pullback f).obj V, f ⁻¹ᵁ W.unop) from
              (((Scheme.Modules.pullback f).obj V).val.map
                ((Opens.map f.base).map g.unop).op)
                ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app V).app
                  U.unop) (m i)))) := by
      refine b2.trans ?_
      exact congrArg _ (congrArg (exteriorPower.ιMulti Γ(T, f ⁻¹ᵁ W.unop) q)
        (funext fun i ↦ hunitnat i))
    exact b1.trans (b2'.trans ((congrArg (((Scheme.Modules.toExteriorPower
      ((Scheme.Modules.pullback f).obj V) q).app
        (.op (f ⁻¹ᵁ W.unop))).hom) b3.symm).trans (b4.trans
          (congrArg (ConcreteCategory.hom
            (((_root_.PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.val)).obj
              (Scheme.Modules.exteriorPower
                ((Scheme.Modules.pullback f).obj V) q).val).map
                  ((Opens.map f.base).map g.unop).op)) b5.symm))))

/-- The comparison `⋀^q V ⟶ f_* (⋀^q f^* V)` of sheaves on `S`, induced by the
locally bijective presheaf comparison through the sheafification universal property. -/
noncomputable def exteriorPowerPushforwardComparison :
    Scheme.Modules.exteriorPower V q ⟶
      (Scheme.Modules.pushforward f).obj
        (Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q) :=
  (_root_.PresheafOfModules.sheafifyHomEquiv (𝟙 S.ringCatSheaf.val)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology S)
      (Scheme.Modules.exteriorPowerPresheaf V q).presheaf)).symm
    (pullbackWedge f V q)

/-- **The pullback comparison for exterior powers**: the canonical morphism
`f^* (⋀^q V) ⟶ ⋀^q (f^* V)`, the adjoint transpose of
`exteriorPowerPushforwardComparison`. -/
noncomputable def pullbackExteriorPower :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.exteriorPower V q) ⟶
      Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj V) q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (exteriorPowerPushforwardComparison f V q)

end AlgebraicGeometry

end
