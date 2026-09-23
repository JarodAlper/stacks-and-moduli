module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Filtered colimits and tensor products of presheaves of modules

For a presheaf of rings on a cofiltered category, the colimit of the pointwise tensor
product of two presheaves of modules is canonically the tensor product, over the colimit
ring, of their colimit modules.  This is the algebraic input for the corresponding
statement about stalks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

universe w v u

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)
  {M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
  {cM : Cocone M.presheaf} (hcM : IsColimit cM)
  {cN : Cocone N.presheaf} (hcN : IsColimit cN)
  {cMN : Cocone (M ⊗ N).presheaf} (hcMN : IsColimit cMN)

namespace ModuleColimit

local notation "hcR'" =>
  isColimitOfPreserves (forget₂ CommRingCat RingCat) hcR

@[instance_reducible]
noncomputable local instance moduleColimitOverCommRing
    {P : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
    {cP : Cocone P.presheaf} {hcP : IsColimit cP} :
    Module cR.pt (ModuleColimit hcR' hcP) :=
  inferInstanceAs (Module ((forget₂ CommRingCat RingCat).mapCocone cR).pt
    (ModuleColimit hcR' hcP))

/-- The cocone whose structure maps send `(m,n)` to the germ of `m ⊗ n`. -/
noncomputable def coconeTensor :
    Cocone (M.presheaf ⋙ forget AddCommGrpCat ⊗ N.presheaf ⋙ forget AddCommGrpCat) where
  pt := ModuleColimit hcR' hcMN
  ι.app U := ↾fun mn : (M.obj U × N.obj U) ↦
    ιM (hcR := hcR') (hcM := hcMN)
      (mn.1 ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] mn.2)
  ι.naturality V U f := by
    ext ⟨m, n⟩
    exact (ConcreteCategory.congr_arg (cMN.ι.app U)
      (Monoidal.tensorObj_map_tmul f m n).symm).trans
        (ConcreteCategory.congr_hom (cMN.w f) _)

/-- The bilinear pairing on colimit modules induced by tensoring representatives at a
common stage. -/
noncomputable def tensorDesc (m : ModuleColimit hcR' hcM) (n : ModuleColimit hcR' hcN) :
    ModuleColimit hcR' hcMN :=
  ((((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
    (isColimitOfPreserves (forget AddCommGrpCat) hcN)).desc
      (coconeTensor hcR hcMN)) ⟨m, n⟩)

@[simp]
lemma tensorDesc_ιM {U : Cᵒᵖ} (m : M.obj U) (n : N.obj U) :
    tensorDesc hcR hcM hcN hcMN
      (ιM (hcR := hcR') (hcM := hcM) m)
      (ιM (hcR := hcR') (hcM := hcN) n) =
      ιM (hcR := hcR') (hcM := hcMN)
        (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n) :=
  ConcreteCategory.congr_hom
    (((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcN)).fac
        (coconeTensor hcR hcMN) U) ⟨m, n⟩

lemma tensorDesc_add_left (m₁ m₂ : ModuleColimit hcR' hcM)
    (n : ModuleColimit hcR' hcN) :
    tensorDesc hcR hcM hcN hcMN (m₁ + m₂) n =
      tensorDesc hcR hcM hcN hcMN m₁ n + tensorDesc hcR hcM hcN hcMN m₂ n := by
  obtain ⟨U, m₁, m₂, n, rfl, rfl, rfl⟩ :=
    ιM_jointly_surjective₃ (hcR := hcR') (hcM := hcM) (hcM' := hcM) (hcM'' := hcN) m₁ m₂ n
  have hleft :
      ιM (hcR := hcR') (hcM := hcM) m₁ + ιM (hcR := hcR') (hcM := hcM) m₂ =
        ιM (hcR := hcR') (hcM := hcM) (m₁ + m₂) :=
    ((cM.ι.app U).hom.map_add m₁ m₂).symm
  rw [hleft, tensorDesc_ιM, tensorDesc_ιM, tensorDesc_ιM,
    TensorProduct.add_tmul, map_add]

lemma tensorDesc_add_right (m : ModuleColimit hcR' hcM)
    (n₁ n₂ : ModuleColimit hcR' hcN) :
    tensorDesc hcR hcM hcN hcMN m (n₁ + n₂) =
      tensorDesc hcR hcM hcN hcMN m n₁ + tensorDesc hcR hcM hcN hcMN m n₂ := by
  obtain ⟨U, m, n₁, n₂, rfl, rfl, rfl⟩ :=
    ιM_jointly_surjective₃ (hcR := hcR') (hcM := hcM) (hcM' := hcN) (hcM'' := hcN) m n₁ n₂
  have hright :
      ιM (hcR := hcR') (hcM := hcN) n₁ + ιM (hcR := hcR') (hcM := hcN) n₂ =
        ιM (hcR := hcR') (hcM := hcN) (n₁ + n₂) :=
    ((cN.ι.app U).hom.map_add n₁ n₂).symm
  rw [hright, tensorDesc_ιM, tensorDesc_ιM, tensorDesc_ιM,
    TensorProduct.tmul_add, map_add]

lemma tensorDesc_smul_left
    (r : cR.pt)
    (m : ModuleColimit hcR' hcM)
    (n : ModuleColimit hcR' hcN) :
    tensorDesc hcR hcM hcN hcMN (r • m) n =
      r • tensorDesc hcR hcM hcN hcMN m n := by
  obtain ⟨U, r, m, n, rfl, rfl, rfl⟩ :=
    jointly_surjective₃' (hcR := hcR') (hcM := hcM) (hcM' := hcN) r m n
  have hm := smul_eq (hcR := hcR') (hcM := hcM) r m
  have hmn := smul_eq (hcR := hcR') (hcM := hcMN) r
    (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n)
  rw [hm, tensorDesc_ιM, tensorDesc_ιM, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, hmn]

lemma tensorDesc_smul_right
    (r : cR.pt)
    (m : ModuleColimit hcR' hcM)
    (n : ModuleColimit hcR' hcN) :
    tensorDesc hcR hcM hcN hcMN m (r • n) =
      r • tensorDesc hcR hcM hcN hcMN m n := by
  obtain ⟨U, r, m, n, rfl, rfl, rfl⟩ :=
    jointly_surjective₃' (hcR := hcR') (hcM := hcM) (hcM' := hcN) r m n
  have hn := smul_eq (hcR := hcR') (hcM := hcN) r n
  have hmn := smul_eq (hcR := hcR') (hcM := hcMN) r
    (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n)
  rw [hn, tensorDesc_ιM, tensorDesc_ιM, TensorProduct.tmul_smul, hmn]

/-- The canonical map from the tensor product of colimit modules to the colimit of the
pointwise tensor product. -/
noncomputable def tensorComparisonInv :
    ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
      ModuleCat.of cR.pt (ModuleColimit hcR' hcN) ⟶
      ModuleCat.of cR.pt (ModuleColimit hcR' hcMN) :=
  ModuleCat.MonoidalCategory.tensorLift
    (tensorDesc hcR hcM hcN hcMN)
    (tensorDesc_add_left (hcR := hcR) (hcM := hcM) (hcN := hcN) (hcMN := hcMN))
    (tensorDesc_smul_left (hcR := hcR) (hcM := hcM) (hcN := hcN) (hcMN := hcMN))
    (tensorDesc_add_right (hcR := hcR) (hcM := hcM) (hcN := hcN) (hcMN := hcMN))
    (tensorDesc_smul_right (hcR := hcR) (hcM := hcM) (hcN := hcN) (hcMN := hcMN))

@[simp]
lemma tensorComparisonInv_tmul {U : Cᵒᵖ} (m : M.obj U) (n : N.obj U) :
    tensorComparisonInv hcR hcM hcN hcMN
      (ιM (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
        ιM (hcR := hcR') (hcM := hcN) n) =
      ιM (hcR := hcR') (hcM := hcMN)
        (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n) := by
  rw [tensorComparisonInv, ModuleCat.MonoidalCategory.tensorLift_tmul,
    tensorDesc_ιM]

/-- At a stage of the diagram, the canonical map from the pointwise tensor product to
the tensor product of the two colimit modules. -/
noncomputable def tensorStageMap (U : Cᵒᵖ) :
    M.obj U ⊗ N.obj U ⟶
      (ModuleCat.restrictScalars (cR.ι.app U).hom).obj
        (ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
          ModuleCat.of cR.pt (ModuleColimit hcR' hcN)) :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ ιM (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
      ιM (hcR := hcR') (hcM := hcN) n)
    (by
      intro m₁ m₂ n
      dsimp
      rw [map_add, TensorProduct.add_tmul])
    (by
      intro r m n
      dsimp
      rw [← smul_eq (hcR := hcR') (hcM := hcM) r m]
      rfl)
    (by
      intro m n₁ n₂
      dsimp
      rw [map_add, TensorProduct.tmul_add])
    (by
      intro r m n
      dsimp
      have hn :
          ιM (hcR := hcR') (hcM := hcN) (r • n) =
            (show cR.pt from
              ιR ((forget₂ CommRingCat RingCat).mapCocone cR) r) •
                ιM (hcR := hcR') (hcM := hcN) n := by
        exact (smul_eq (hcR := hcR') (hcM := hcN) r n).symm
      rw [hn, TensorProduct.tmul_smul (R := cR.pt) (R' := cR.pt)]
      rfl)

@[simp]
lemma tensorStageMap_tmul (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U) :
    tensorStageMap hcR hcM hcN U
      (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n) =
      ιM (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
        ιM (hcR := hcR') (hcM := hcN) n := by
  rfl

/-- The cocone from the pointwise tensor products to the tensor product of colimit
modules. -/
noncomputable def coconeTensorComparison : Cocone (M ⊗ N).presheaf where
  pt := (forget₂ (ModuleCat cR.pt) AddCommGrpCat).obj
    (ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
      ModuleCat.of cR.pt (ModuleColimit hcR' hcN))
  ι.app U :=
    (forget₂ (ModuleCat ((R ⋙ forget₂ CommRingCat RingCat).obj U))
      AddCommGrpCat).map (tensorStageMap hcR hcM hcN U)
  ι.naturality U V f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (tensorStageMap hcR hcM hcN U).hom.map_zero.symm
    | tmul m n =>
        change
          ιM (U := V) (hcR := hcR') (hcM := hcM) (M.map f m) ⊗ₜ[cR.pt]
              ιM (U := V) (hcR := hcR') (hcM := hcN) (N.map f n) =
            ιM (U := U) (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
              ιM (U := U) (hcR := hcR') (hcM := hcN) n
        exact congrArg₂ (fun x y ↦ x ⊗ₜ[cR.pt] y)
          (ConcreteCategory.congr_hom (cM.w f) m)
          (ConcreteCategory.congr_hom (cN.w f) n)
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- The maps from the pointwise tensor products to the tensor product of colimit
modules, regarded as a morphism to the constant presheaf. -/
noncomputable def tensorComparisonCoconeHom :
    M ⊗ N ⟶
      (constFunctor ((forget₂ CommRingCat RingCat).mapCocone cR)).obj
        (ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
          ModuleCat.of cR.pt (ModuleColimit hcR' hcN)) :=
  homMk (coconeTensorComparison hcR hcM hcN).ι (by
    intro U r t
    exact (tensorStageMap hcR hcM hcN U).hom.map_smul r t)

/-- The canonical map from the colimit of the pointwise tensor products to the tensor
product of the two colimit modules. -/
noncomputable def tensorComparison :
    ModuleCat.of cR.pt (ModuleColimit hcR' hcMN) ⟶
      ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
        ModuleCat.of cR.pt (ModuleColimit hcR' hcN) :=
  (homEquiv hcR' hcMN).symm (tensorComparisonCoconeHom hcR hcM hcN)

@[simp]
lemma tensorComparison_ιM {U : Cᵒᵖ} (t : (M ⊗ N).obj U) :
    tensorComparison hcR hcM hcN hcMN
      (ιM (U := U) (hcR := hcR') (hcM := hcMN) t) =
      (tensorComparisonCoconeHom hcR hcM hcN).app U t := by
  exact homEquiv_symm_apply hcR' hcMN
    (tensorComparisonCoconeHom hcR hcM hcN) t

lemma tensorComparison_comp_tensorComparisonInv :
    tensorComparison hcR hcM hcN hcMN ≫ tensorComparisonInv hcR hcM hcN hcMN =
      𝟙 (ModuleCat.of cR.pt (ModuleColimit hcR' hcMN)) := by
  ext z
  obtain ⟨U, t, rfl⟩ :=
    ιM_jointly_surjective (hcR := hcR') (hcM := hcMN) z
  change tensorComparisonInv hcR hcM hcN hcMN
      (tensorComparison hcR hcM hcN hcMN
        (ιM (U := U) (hcR := hcR') (hcM := hcMN) t)) =
    ιM (U := U) (hcR := hcR') (hcM := hcMN) t
  rw [tensorComparison_ιM]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      change tensorComparisonInv hcR hcM hcN hcMN
          (ιM (U := U) (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
            ιM (U := U) (hcR := hcR') (hcM := hcN) n) =
        ιM (U := U) (hcR := hcR') (hcM := hcMN)
          (m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] n)
      exact tensorComparisonInv_tmul hcR hcM hcN hcMN m n
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

lemma tensorComparisonInv_comp_tensorComparison :
    tensorComparisonInv hcR hcM hcN hcMN ≫ tensorComparison hcR hcM hcN hcMN =
      𝟙 (ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
        ModuleCat.of cR.pt (ModuleColimit hcR' hcN)) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  obtain ⟨U, m, n, rfl, rfl⟩ :=
    ιM_jointly_surjective₂ (hcR := hcR') (hcM := hcM) (hcM' := hcN) m n
  change tensorComparison hcR hcM hcN hcMN
      (tensorComparisonInv hcR hcM hcN hcMN
        (ιM (U := U) (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
          ιM (U := U) (hcR := hcR') (hcM := hcN) n)) =
    ιM (U := U) (hcR := hcR') (hcM := hcM) m ⊗ₜ[cR.pt]
      ιM (U := U) (hcR := hcR') (hcM := hcN) n
  rw [tensorComparisonInv_tmul, tensorComparison_ιM]
  rfl

/-- Filtered colimits of modules over a filtered colimit of commutative rings commute
with tensor products. -/
noncomputable def tensorComparisonIso :
    ModuleCat.of cR.pt (ModuleColimit hcR' hcMN) ≅
      ModuleCat.of cR.pt (ModuleColimit hcR' hcM) ⊗
        ModuleCat.of cR.pt (ModuleColimit hcR' hcN) where
  hom := tensorComparison hcR hcM hcN hcMN
  inv := tensorComparisonInv hcR hcM hcN hcMN
  hom_inv_id := tensorComparison_comp_tensorComparisonInv hcR hcM hcN hcMN
  inv_hom_id := tensorComparisonInv_comp_tensorComparison hcR hcM hcN hcMN

section Naturality

variable {M' N' : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}
  {cM' : Cocone M'.presheaf} (hcM' : IsColimit cM')
  {cN' : Cocone N'.presheaf} (hcN' : IsColimit cN')
  {cMN' : Cocone (M' ⊗ N').presheaf} (hcMN' : IsColimit cMN')

/-- The comparison between a colimit of pointwise tensor products and the tensor
product of the colimits is natural in both module diagrams. -/
lemma tensorComparison_natural (f : M ⟶ M') (g : N ⟶ N') :
    tensorComparison hcR hcM hcN hcMN ≫
        (ModuleCat.ofHom (map hcR' hcM hcM' f) ⊗ₘ
          ModuleCat.ofHom (map hcR' hcN hcN' g)) =
      ModuleCat.ofHom (map hcR' hcMN hcMN' (f ⊗ₘ g)) ≫
        tensorComparison hcR hcM' hcN' hcMN' := by
  ext z
  obtain ⟨U, t, rfl⟩ :=
    ιM_jointly_surjective (hcR := hcR') (hcM := hcMN) z
  change
    (ModuleCat.ofHom (map hcR' hcM hcM' f) ⊗ₘ
        ModuleCat.ofHom (map hcR' hcN hcN' g))
      (tensorComparison hcR hcM hcN hcMN
        (ιM (U := U) (hcR := hcR') (hcM := hcMN) t)) =
      tensorComparison hcR hcM' hcN' hcMN'
        (map hcR' hcMN hcMN' (f ⊗ₘ g)
          (ιM (U := U) (hcR := hcR') (hcM := hcMN) t))
  rw [map_apply, tensorComparison_ιM]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      change
        map hcR' hcM hcM' f
            (ιM (U := U) (hcR := hcR') (hcM := hcM) m) ⊗ₜ[cR.pt]
          map hcR' hcN hcN' g
            (ιM (U := U) (hcR := hcR') (hcM := hcN) n) =
          tensorComparison hcR hcM' hcN' hcMN'
            (ιM (U := U) (hcR := hcR') (hcM := hcMN')
              (f.app U m ⊗ₜ[((R ⋙ forget₂ CommRingCat RingCat).obj U)] g.app U n))
      rw [map_apply, map_apply, tensorComparison_ιM]
      rfl
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

end Naturality

end ModuleColimit

end PresheafOfModules
