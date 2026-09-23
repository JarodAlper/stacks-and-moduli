module

public import StacksAndModuli.API.SchemeModulesPullbackTensorCoherence
public import StacksAndModuli.API.SchemeModulesTensorFiniteCoproduct
public import StacksAndModuli.API.SchemeModulesTensorUnitNaturality

/-!
# The canonical projection-formula morphism for scheme modules

For a scheme morphism `f : X ⟶ Y`, a module `K` on `Y`, and a module `F` on `X`,
the canonical projection-formula morphism is

`K ⊗ f_*F ⟶ f_*(f^*K ⊗ F)`.

It is defined as the adjoint mate of the oplax tensor comparison for pullback followed by
the pullback--pushforward counit.  The naturality lemmas make the precise canonical map
available to later relative-cohomology calculations; invertibility is intentionally a
separate geometric assertion.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The canonical projection-formula morphism
`K ⊗ f_*F ⟶ f_*(f^*K ⊗ F)`. -/
noncomputable def projectionFormulaHom
    (f : X ⟶ Y) (K : Y.Modules) (F : X.Modules) :
    tensor K ((pushforward f).obj F) ⟶
      (pushforward f).obj (tensor ((pullback f).obj K) F) :=
  (pullbackPushforwardAdjunction f).homEquiv _ _
    (pullbackTensorComparison f K ((pushforward f).obj F) ≫
      tensorMapRight ((pullback f).obj K)
        ((pullbackPushforwardAdjunction f).counit.app F))

/-- Invertibility of the canonical projection-formula morphism for one pair of
module sheaves. -/
abbrev ProjectionFormula
    (f : X ⟶ Y) (K : Y.Modules) (F : X.Modules) : Prop :=
  IsIso (projectionFormulaHom f K F)

/-- The canonical projection-formula morphism is natural in the module on the base. -/
theorem projectionFormulaHom_naturality_left
    (f : X ⟶ Y) {K K' : Y.Modules} (k : K ⟶ K') (F : X.Modules) :
    tensorMapLeft k ((pushforward f).obj F) ≫
        projectionFormulaHom f K' F =
      projectionFormulaHom f K F ≫
        (pushforward f).map (tensorMapLeft ((pullback f).map k) F) := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_naturality_right_symm]
  dsimp only [projectionFormulaHom]
  dsimp only [adj]
  simp only [Equiv.symm_apply_apply]
  rw [← Category.assoc]
  rw [pullbackTensorComparison_naturality_left]
  simp only [Category.assoc]
  rw [tensorMap_exchange]

/-- For fixed `F`, the projection-formula morphisms form a natural transformation in
the module on the base. -/
noncomputable def projectionFormulaNatTrans
    (f : X ⟶ Y) (F : X.Modules) :
    tensorRightFunctor ((pushforward f).obj F) ⟶
      pullback f ⋙ tensorRightFunctor F ⋙ pushforward f where
  app K := projectionFormulaHom f K F
  naturality {K K'} k := by
    exact projectionFormulaHom_naturality_left f k F

/-- The canonical projection-formula morphism is natural in the module on the source. -/
theorem projectionFormulaHom_naturality_right
    (f : X ⟶ Y) (K : Y.Modules) {F F' : X.Modules} (k : F ⟶ F') :
    tensorMapRight K ((pushforward f).map k) ≫
        projectionFormulaHom f K F' =
      projectionFormulaHom f K F ≫
        (pushforward f).map (tensorMapRight ((pullback f).obj K) k) := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_naturality_right_symm]
  dsimp only [projectionFormulaHom]
  dsimp only [adj]
  simp only [Equiv.symm_apply_apply]
  rw [← Category.assoc]
  rw [pullbackTensorComparison_naturality_right]
  simp only [Category.assoc]
  have h := adj.counit.naturality k
  have ht :
      tensorMapRight ((pullback f).obj K)
          ((pullback f).map ((pushforward f).map k)) ≫
          tensorMapRight ((pullback f).obj K) (adj.counit.app F') =
        tensorMapRight ((pullback f).obj K) (adj.counit.app F) ≫
          tensorMapRight ((pullback f).obj K) k := by
    simpa only [Functor.comp_map, Functor.id_map, tensorMapRight_comp] using
      congrArg (tensorMapRight ((pullback f).obj K)) h
  exact congrArg
    (fun q ↦ pullbackTensorComparison f K ((pushforward f).obj F) ≫ q) ht

set_option maxHeartbeats 800000 in
-- The proof compares adjoint mates and then uses tensor-unit coherence.
/-- The projection formula holds when the module on the base is the structure sheaf. -/
theorem projectionFormulaHom_isIso_unit
    (f : X ⟶ Y) (F : X.Modules) :
    IsIso (projectionFormulaHom f
      (SheafOfModules.unit Y.ringCatSheaf) F) := by
  let UY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let UX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let PF := (pullback f).obj ((pushforward f).obj F)
  let PU := (pullback f).obj UY
  let u : PU ⟶ UX :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  letI : IsIso u := isIso_pullbackObjUnitToUnit f
  let e : tensor PU F ≅ F :=
    tensorLeftIso (asIso u) F ≪≫ tensorLeftUnitIso F
  let p := projectionFormulaHom f
    (SheafOfModules.unit Y.ringCatSheaf) F
  have hp : p ≫ (pushforward f).map e.hom =
      (tensorLeftUnitIso ((pushforward f).obj F)).hom := by
    apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_right_symm]
    dsimp only [p, projectionFormulaHom]
    simp only [Equiv.symm_apply_apply]
    rw [(pullbackPushforwardAdjunction f).homEquiv_counit]
    dsimp only [e, Iso.trans_hom, tensorLeftIso, asIso_hom]
    let c := pullbackTensorComparison f UY ((pushforward f).obj F)
    let ε := (pullbackPushforwardAdjunction f).counit.app F
    have hex := tensorMap_exchange u ε
    have hunit := tensorLeftUnitIso_hom_naturality ε
    have hpull := pullbackTensorComparison_comp_leftUnit f
      ((pushforward f).obj F)
    change c ≫ tensorMapRight PU ε ≫ tensorMapLeft u F ≫
        (tensorLeftUnitIso F).hom =
      (pullback f).map
          (tensorLeftUnitIso ((pushforward f).obj F)).hom ≫ ε
    calc
      c ≫ tensorMapRight PU ε ≫ tensorMapLeft u F ≫
            (tensorLeftUnitIso F).hom =
          c ≫ tensorMapLeft u PF ≫ tensorMapRight UX ε ≫
            (tensorLeftUnitIso F).hom := by
        simpa only [PF, UX, Functor.comp_obj, Functor.id_obj,
          Category.assoc] using congrArg
            (fun q ↦ c ≫ q ≫ (tensorLeftUnitIso F).hom) hex
      _ = c ≫ tensorMapLeft u PF ≫
            (tensorLeftUnitIso PF).hom ≫ ε := by
        simpa only [PF, UX, Functor.comp_obj, Functor.id_obj,
          Category.assoc] using congrArg
          (fun q ↦ c ≫ tensorMapLeft u PF ≫ q) hunit
      _ = (pullback f).map
            (tensorLeftUnitIso ((pushforward f).obj F)).hom ≫ ε := by
        simpa only [c, UY, PU, PF, u, Category.assoc] using congrArg
          (fun q ↦ q ≫ ε) hpull
  haveI : IsIso (p ≫ (pushforward f).map e.hom) := hp ▸ inferInstance
  exact IsIso.of_isIso_comp_right p ((pushforward f).map e.hom)

/-- The projection formula is closed under finite biproducts in the module on the base. -/
theorem projectionFormulaHom_isIso_biproduct
    {J : Type u} [Finite J] (f : X ⟶ Y) (K : J → Y.Modules)
    (F : X.Modules) [∀ j, IsIso (projectionFormulaHom f (K j) F)] :
    IsIso (projectionFormulaHom f (⨁ K) F) := by
  let ⟨_⟩ := nonempty_fintype J
  let L := tensorRightFunctor ((pushforward f).obj F)
  let R := pullback f ⋙ tensorRightFunctor F ⋙ pushforward f
  let α := projectionFormulaNatTrans f F
  letI : PreservesBiproduct K L :=
    { preserves := fun hb ↦
        ⟨isBilimitOfTotal _ (by
          simp_rw [L.mapBicone_π, L.mapBicone_ι, ← L.map_comp]
          erw [← L.map_sum, ← L.map_id, IsBilimit.total hb])⟩ }
  letI : PreservesBiproduct K R :=
    { preserves := fun hb ↦
        ⟨isBilimitOfTotal _ (by
          simp_rw [R.mapBicone_π, R.mapBicone_ι, ← R.map_comp]
          erw [← R.map_sum, ← R.map_id, IsBilimit.total hb])⟩ }
  let eL := L.mapBiproduct K
  let eR := R.mapBiproduct K
  letI (j : J) : IsIso (α.app (K j)) := by
    dsimp only [α, projectionFormulaNatTrans]
    infer_instance
  let bIso := biproduct.mapIso fun j ↦ asIso (α.app (K j))
  let b := bIso.hom
  have hb : α.app (⨁ K) ≫ eR.hom = eL.hom ≫ b := by
    apply biproduct.hom_ext
    intro j
    have hR : eR.hom ≫ biproduct.π (R.obj ∘ K) j =
        R.map (biproduct.π K j) := by
      dsimp only [eR]
      rw [Functor.mapBiproduct_hom]
      exact biproduct.lift_π (fun j ↦ R.map (biproduct.π K j)) j
    have hL : eL.hom ≫ biproduct.π (L.obj ∘ K) j =
        L.map (biproduct.π K j) := by
      dsimp only [eL]
      rw [Functor.mapBiproduct_hom]
      exact biproduct.lift_π (fun j ↦ L.map (biproduct.π K j)) j
    have hbπ : b ≫ biproduct.π (R.obj ∘ K) j =
        biproduct.π (L.obj ∘ K) j ≫ α.app (K j) := by
      dsimp only [b, bIso, biproduct.mapIso_hom, asIso_hom]
      exact biproduct.map_π (fun j ↦ α.app (K j)) j
    calc
      (α.app (⨁ K) ≫ eR.hom) ≫ biproduct.π (R.obj ∘ K) j =
          α.app (⨁ K) ≫ R.map (biproduct.π K j) := by
        rw [Category.assoc, hR]
      _ = L.map (biproduct.π K j) ≫ α.app (K j) :=
        (α.naturality (biproduct.π K j)).symm
      _ = (eL.hom ≫ biproduct.π (L.obj ∘ K) j) ≫
          α.app (K j) := by rw [hL]
      _ = eL.hom ≫
          (biproduct.π (L.obj ∘ K) j ≫ α.app (K j)) :=
        Category.assoc _ _ _
      _ = eL.hom ≫ (b ≫ biproduct.π (R.obj ∘ K) j) := by rw [hbπ]
      _ = (eL.hom ≫ b) ≫ biproduct.π (R.obj ∘ K) j :=
        (Category.assoc _ _ _).symm
  letI : IsIso b := by
    change IsIso bIso.hom
    infer_instance
  haveI : IsIso (eL.hom ≫ b) := by infer_instance
  haveI : IsIso (α.app (⨁ K) ≫ eR.hom) := hb ▸ inferInstance
  haveI : IsIso (α.app (⨁ K)) :=
    IsIso.of_isIso_comp_right (α.app (⨁ K)) eR.hom
  exact this

/-- The projection formula is closed under finite coproducts in the module on the base. -/
theorem projectionFormulaHom_isIso_coproduct
    {J : Type u} [Finite J] (f : X ⟶ Y) (K : J → Y.Modules)
    (F : X.Modules) [∀ j, IsIso (projectionFormulaHom f (K j) F)] :
    IsIso (projectionFormulaHom f (∐ K) F) := by
  let e := biproduct.isoCoproduct K
  let a := tensorMapLeft e.hom ((pushforward f).obj F)
  let b := (pushforward f).map
    (tensorMapLeft ((pullback f).map e.hom) F)
  let p := projectionFormulaHom f (⨁ K) F
  let q := projectionFormulaHom f (∐ K) F
  haveI : IsIso p := projectionFormulaHom_isIso_biproduct f K F
  haveI : IsIso a := by
    change IsIso (tensorLeftIso e ((pushforward f).obj F)).hom
    infer_instance
  let ep := (pullback f).mapIso e
  haveI : IsIso (tensorMapLeft ((pullback f).map e.hom) F) := by
    change IsIso (tensorLeftIso ep F).hom
    infer_instance
  haveI : IsIso b := by
    dsimp only [b]
    infer_instance
  have h : a ≫ q = p ≫ b := by
    simpa only [a, b, p, q] using
      projectionFormulaHom_naturality_left f e.hom F
  haveI : IsIso (a ≫ q) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left a q

/-- The projection formula holds for a finite free module sheaf on the base. -/
theorem projectionFormulaHom_isIso_free
    {J : Type u} [Finite J] (f : X ⟶ Y) (F : X.Modules) :
    IsIso (projectionFormulaHom f
      (SheafOfModules.free (R := Y.ringCatSheaf) J) F) := by
  let K : J → Y.Modules := fun _ ↦
    SheafOfModules.unit Y.ringCatSheaf
  letI : ∀ j, IsIso (projectionFormulaHom f (K j) F) := fun _ ↦ by
    exact projectionFormulaHom_isIso_unit f F
  change IsIso (projectionFormulaHom f (∐ K) F)
  exact @projectionFormulaHom_isIso_coproduct X Y J _ f K F
    (fun _ ↦ projectionFormulaHom_isIso_unit f F)

/-- The projection formula descends from a module on the base to any retract of it. -/
theorem projectionFormulaHom_isIso_of_retract
    (f : X ⟶ Y) {K K' : Y.Modules}
    (i : K ⟶ K') (p : K' ⟶ K) (h : i ≫ p = 𝟙 K)
    (F : X.Modules) [IsIso (projectionFormulaHom f K' F)] :
    IsIso (projectionFormulaHom f K F) := by
  let L := tensorRightFunctor ((pushforward f).obj F)
  let R := pullback f ⋙ tensorRightFunctor F ⋙ pushforward f
  let α := projectionFormulaNatTrans f F
  letI : IsIso (α.app K') := by
    dsimp only [α, projectionFormulaNatTrans]
    infer_instance
  let q : R.obj K ⟶ L.obj K :=
    R.map i ≫ inv (α.app K') ≫ L.map p
  change IsIso (α.app K)
  refine ⟨q, ?_, ?_⟩
  · dsimp only [q]
    simp only [← Category.assoc]
    rw [← α.naturality i]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← L.map_comp, h, L.map_id]
  · dsimp only [q]
    simp only [Category.assoc]
    rw [α.naturality p]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [← R.map_comp, h, R.map_id]

end AlgebraicGeometry.Scheme.Modules

end

end
