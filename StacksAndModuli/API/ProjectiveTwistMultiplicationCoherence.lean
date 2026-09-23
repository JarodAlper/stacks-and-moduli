module

public import StacksAndModuli.API.ProjGammaStarTwist
public import StacksAndModuli.API.SchemeModulesTensorSymmetry

/-!
# Coherence for multiplication of projective twists

Multiplication of twisting sheaves is compatible with associativity, symmetry, degree
transport, and the tensor unit. These identities provide the coherence layer used by
projective-space pairing and Grassmannian comparison constructions.

Main declarations:

* `ProjectiveSpectrum.Twist.multiplyHom_assoc'`;
* `ProjectiveSpectrum.Twist.multiplyHom_comm'`;
* `ProjectiveSpectrum.Twist.tensorUnitIso_inv_tensorMapRight_zeroIso_inv_multiplyHom`;
* `ProjectiveSpectrum.Twist.mulHom_multiplyHom`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite TopCat

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

noncomputable local instance instBraidedPresheafOfModules :
    BraidedCategory (Proj R).PresheafOfModules :=
  inferInstanceAs (BraidedCategory
    (PresheafOfModules.{u}
      ((Proj R).presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- Transporting a projective-twist section across an equality of degrees preserves its
underlying value. -/
lemma eqToHom_twist_val_app_apply {a b : ℤ} (h : a = b)
    (U : (Opens (ProjectiveSpectrum.top R))ᵒᵖ)
    (s : (sheafInType R a).1.obj U) (x : U.unop) :
    (((((eqToHom
      (congrArg (fun z : ℤ ↦ (twist R z).val) h)).app U).hom s).1 x).1) =
      (s.1 x).1 := by
  subst b
  rfl

/-- Transporting a section through an equality morphism of twist sheaves preserves
its underlying value. -/
lemma eqToHom_twist_app_apply {a b : ℤ} (h : a = b)
    (U : (Opens (ProjectiveSpectrum.top R))ᵒᵖ)
    (s : (sheafInType R a).1.obj U) (x : U.unop) :
    (((((eqToHom (congrArg (twist R) h)).val.app U).hom s).1 x).1) =
      (s.1 x).1 := by
  subst b
  rfl

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
/-- Presheaf multiplication of three twists is associative. -/
lemma multiplyPresheafHom_assoc' (a b c : ℤ)
    (h : (a + b) + c = a + (b + c)) :
    MonoidalCategoryStruct.whiskerRight
          (C := (Proj R).PresheafOfModules)
          (multiplyPresheafHom R a b) (twist R c).val ≫
        multiplyPresheafHom R (a + b) c ≫
        eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) h) =
      (MonoidalCategoryStruct.associator
        (C := (Proj R).PresheafOfModules)
        (twist R a).val (twist R b).val (twist R c).val).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (C := (Proj R).PresheafOfModules)
          (twist R a).val (multiplyPresheafHom R b c) ≫
        multiplyPresheafHom R a (b + c) := by
  refine PresheafOfModules.hom_ext (fun U ↦ ?_)
  change
    (MonoidalCategoryStruct.whiskerRight
          (C := (Proj R).PresheafOfModules)
          (multiplyPresheafHom R a b) (twist R c).val).app U ≫
        (multiplyPresheafHom R (a + b) c).app U ≫
        (eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) h)).app U =
      ((MonoidalCategoryStruct.associator
        (C := (Proj R).PresheafOfModules)
        (twist R a).val (twist R b).val (twist R c).val).hom.app U ≫
        (MonoidalCategoryStruct.whiskerLeft
          (C := (Proj R).PresheafOfModules)
          (twist R a).val (multiplyPresheafHom R b c)).app U ≫
        (multiplyPresheafHom R a (b + c)).app U)
  refine ModuleCat.MonoidalCategory.tensor_ext₃' (fun s t v ↦ ?_)
  change ((eqToHom (congrArg
      (fun z : ℤ ↦ (twist R z).val) h)).app U).hom
        (mulSections R (a + b) c U
          (mulSections R a b U s t) v) =
    mulSections R a (b + c) U s (mulSections R b c U t v)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  calc
    (((((eqToHom (congrArg
        (fun z : ℤ ↦ (twist R z).val) h)).app U).hom
          (mulSections R (a + b) c U
            (mulSections R a b U s t) v)).1 x).1) =
        ((mulSections R (a + b) c U
          (mulSections R a b U s t) v).1 x).1 :=
      eqToHom_twist_val_app_apply R h U _ x
    _ = _ := by
      change ((s.1 x).1 * (t.1 x).1) * (v.1 x).1 =
        (s.1 x).1 * ((t.1 x).1 * (v.1 x).1)
      ring

/-- Presheaf multiplication of two twists is commutative after transporting the
output degree. -/
lemma multiplyPresheafHom_comm' (a b : ℤ) (h : b + a = a + b) :
    (β_ (twist R a).val (twist R b).val).hom ≫
        multiplyPresheafHom R b a ≫
        eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) h) =
      multiplyPresheafHom R a b := by
  refine PresheafOfModules.hom_ext (fun U ↦ ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun s t ↦ ?_)
  change ((eqToHom (congrArg
      (fun z : ℤ ↦ (twist R z).val) h)).app U).hom
        (mulSections R b a U t s) = mulSections R a b U s t
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  calc
    (((((eqToHom (congrArg
        (fun z : ℤ ↦ (twist R z).val) h)).app U).hom
          (mulSections R b a U t s)).1 x).1) =
        ((mulSections R b a U t s).1 x).1 :=
      eqToHom_twist_val_app_apply R h U _ x
    _ = _ := by
      change (t.1 x).1 * (s.1 x).1 = (s.1 x).1 * (t.1 x).1
      ring

/-- Multiplication from the zero twist agrees with the presheaf left unitor. -/
lemma zeroIso_inv_whisker_multiplyPresheafHom (b : ℤ) :
    ((zeroIso R).inv.val ▷ (twist R b).val) ≫
        multiplyPresheafHom R 0 b ≫
        eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) (zero_add b)) =
      (λ_ (twist R b).val).hom := by
  refine PresheafOfModules.hom_ext (fun U ↦ ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun s t ↦ ?_)
  change ((eqToHom (congrArg
      (fun z : ℤ ↦ (twist R z).val) (zero_add b))).app U).hom
        (mulSections R 0 b U ((zeroIso R).inv.val.app U s) t) = s • t
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  calc
    (((((eqToHom (congrArg
        (fun z : ℤ ↦ (twist R z).val) (zero_add b))).app U).hom
          (mulSections R 0 b U ((zeroIso R).inv.val.app U s) t)).1 x).1) =
        ((mulSections R 0 b U ((zeroIso R).inv.val.app U s) t).1 x).1 :=
      eqToHom_twist_val_app_apply R (zero_add b) U _ x
    _ = _ := by
      change (s.1 x).val * (t.1 x).1 = (s.1 x).val * (t.1 x).1
      rfl

/-- Multiplication from the zero twist agrees with the chosen sheaf-tensor left
unitor. -/
lemma tensorMapLeft_zeroIso_inv_multiplyHom (b : ℤ) :
    AlgebraicGeometry.Scheme.Modules.tensorMapLeft
          (zeroIso R).inv (twist R b) ≫
        multiplyHom R 0 b ≫
        eqToHom (congrArg (twist R) (zero_add b)) =
      (AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso (twist R b)).hom := by
  let X := Proj R
  let L := AlgebraicGeometry.Scheme.Modules.sheafification X
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let castS : twist R (0 + b) ⟶ twist R b :=
    eqToHom (congrArg (twist R) (zero_add b))
  let castP : (twist R (0 + b)).val ⟶ (twist R b).val :=
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
      ((SheafOfModules.forget X.ringCatSheaf).map castS)
  have castP_eq : castP =
      eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) (zero_add b)) := by
    dsimp only [castP, castS]
    simp only [eqToHom_map]
  have hcounit : adj.counit.app (twist R (0 + b)) ≫ castS =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map castP ≫
        adj.counit.app (twist R b) := by
    have ht := adj.counit.naturality castS
    simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, castP] using ht.symm
  rw [multiplyHom_eq]
  change L.map ((zeroIso R).inv.val ▷ (twist R b).val) ≫
        L.map (multiplyPresheafHom R 0 b) ≫
        adj.counit.app (twist R (0 + b)) ≫ castS =
      L.map (λ_ (twist R b).val).hom ≫ adj.counit.app (twist R b)
  rw [hcounit]
  change L.map ((zeroIso R).inv.val ▷ (twist R b).val) ≫
        L.map (multiplyPresheafHom R 0 b) ≫ L.map castP ≫
        adj.counit.app (twist R b) =
      L.map (λ_ (twist R b).val).hom ≫ adj.counit.app (twist R b)
  slice_lhs 1 3 => rw [← L.map_comp, ← L.map_comp]
  exact congrArg (fun k ↦ L.map k ≫ adj.counit.app (twist R b))
    (by simpa only [castP_eq] using
      zeroIso_inv_whisker_multiplyPresheafHom R b)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
/-- Changing the recorded output degree of multiplication is postcomposition by
the corresponding equality morphism. -/
lemma mulHom_comp_eqToHom {m : ℕ} (p : R m)
    (d dc dc' : ℤ) (hdc : dc = d + (m : ℤ))
    (hdc' : dc' = d + (m : ℤ)) :
    mulHom R p d dc hdc ≫
        eqToHom (congrArg (twist R) (hdc.trans hdc'.symm)) =
      mulHom R p d dc' hdc' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  change (((mulHom R p d dc hdc).val ≫
      (eqToHom (congrArg (twist R) (hdc.trans hdc'.symm))).val).app U).hom s = _
  rw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [show ((mulHom R p d dc hdc).val.app U).hom s =
      mulSectionHom R p d dc hdc U s from
    mulHom_val_app_apply R p d dc hdc U s]
  rw [show ((mulHom R p d dc' hdc').val.app U).hom s =
      mulSectionHom R p d dc' hdc' U s from
    mulHom_val_app_apply R p d dc' hdc' U s]
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  calc
    (((((eqToHom (congrArg (twist R)
          (hdc.trans hdc'.symm))).val.app U).hom
          (mulSectionHom R p d dc hdc U s)).1 x).1) =
        ((mulSectionHom R p d dc hdc U s).1 x).1 :=
      eqToHom_twist_app_apply R (hdc.trans hdc'.symm) U _ x
    _ = _ := rfl

/-- Sheaf multiplication of two twists is commutative with respect to the chosen
sheaf-tensor symmetry. -/
lemma multiplyHom_comm' (a b : ℤ) (h : b + a = a + b) :
    (AlgebraicGeometry.Scheme.Modules.tensorCommIso
        (twist R a) (twist R b)).hom ≫
        multiplyHom R b a ≫ eqToHom (congrArg (twist R) h) =
      multiplyHom R a b := by
  let X := Proj R
  let L := AlgebraicGeometry.Scheme.Modules.sheafification X
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let castS : twist R (b + a) ⟶ twist R (a + b) :=
    eqToHom (congrArg (twist R) h)
  let castP : (twist R (b + a)).val ⟶ (twist R (a + b)).val :=
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
      ((SheafOfModules.forget X.ringCatSheaf).map castS)
  have castP_eq : castP =
      eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) h) := by
    dsimp only [castP, castS]
    simp only [eqToHom_map]
  have hcounit : adj.counit.app (twist R (b + a)) ≫ castS =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map castP ≫
        adj.counit.app (twist R (a + b)) := by
    have ht := adj.counit.naturality castS
    simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, castP] using ht.symm
  rw [multiplyHom_eq, multiplyHom_eq]
  change L.map (β_ (twist R a).val (twist R b).val).hom ≫
        L.map (multiplyPresheafHom R b a) ≫
        adj.counit.app (twist R (b + a)) ≫ castS =
      L.map (multiplyPresheafHom R a b) ≫
        adj.counit.app (twist R (a + b))
  rw [hcounit]
  change L.map (β_ (twist R a).val (twist R b).val).hom ≫
        L.map (multiplyPresheafHom R b a) ≫ L.map castP ≫
        adj.counit.app (twist R (a + b)) =
      L.map (multiplyPresheafHom R a b) ≫
        adj.counit.app (twist R (a + b))
  slice_lhs 1 3 => rw [← L.map_comp, ← L.map_comp]
  exact congrArg
    (fun k ↦ L.map k ≫ adj.counit.app (twist R (a + b)))
    (by simpa only [castP_eq] using multiplyPresheafHom_comm' R a b h)

/-- Sheaf multiplication of three twists is associative with respect to the chosen
sheaf-tensor associator. -/
lemma multiplyHom_assoc' (a b c : ℤ)
    (h : (a + b) + c = a + (b + c)) :
    AlgebraicGeometry.Scheme.Modules.tensorMapLeft
          (multiplyHom R a b) (twist R c) ≫
        multiplyHom R (a + b) c ≫
        eqToHom (congrArg (twist R) h) =
      (AlgebraicGeometry.Scheme.Modules.tensorAssocIso
        (twist R a) (twist R b) (twist R c)).hom ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapRight
          (twist R a) (multiplyHom R b c) ≫
        multiplyHom R a (b + c) := by
  let X := Proj R
  let L := AlgebraicGeometry.Scheme.Modules.sheafification X
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let W := AlgebraicGeometry.Scheme.Modules.tensorLocalEquivalences X
  let Oa := twist R a
  let Ob := twist R b
  let Oc := twist R c
  let uab := adj.unit.app (Oa.val ⊗ Ob.val)
  let ubc := adj.unit.app (Ob.val ⊗ Oc.val)
  have hunitMem (A : X.PresheafOfModules) : W (adj.unit.app A) := by
    change (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (adj.unit.app A))
    simpa [adj] using
      (Opens.grothendieckTopology X).W_toSheafify A.presheaf
  have huabc : W (uab ▷ Oc.val) :=
    W.whiskerRight_mem uab (hunitMem (Oa.val ⊗ Ob.val)) Oc.val
  have hauBC : W (Oa.val ◁ ubc) :=
    W.whiskerLeft_mem Oa.val ubc (hunitMem (Ob.val ⊗ Oc.val))
  let iabc := Localization.isoOfHom L W (uab ▷ Oc.val) huabc
  let iaBC := Localization.isoOfHom L W (Oa.val ◁ ubc) hauBC
  have hab : uab ≫ (multiplyHom R a b).val =
      multiplyPresheafHom R a b := by
    have ht := adj.homEquiv_unit
      (X := Oa.val ⊗ Ob.val) (Y := twist R (a + b))
      (f := multiplyHom R a b)
    change adj.homEquiv (Oa.val ⊗ Ob.val) (twist R (a + b))
        (multiplyHom R a b) = uab ≫ (multiplyHom R a b).val at ht
    rw [← ht]
    exact Equiv.apply_symm_apply
      (adj.homEquiv (Oa.val ⊗ Ob.val) (twist R (a + b))) _
  have hbc' : ubc ≫ (multiplyHom R b c).val =
      multiplyPresheafHom R b c := by
    have ht := adj.homEquiv_unit
      (X := Ob.val ⊗ Oc.val) (Y := twist R (b + c))
      (f := multiplyHom R b c)
    change adj.homEquiv (Ob.val ⊗ Oc.val) (twist R (b + c))
        (multiplyHom R b c) = ubc ≫ (multiplyHom R b c).val at ht
    rw [← ht]
    exact Equiv.apply_symm_apply
      (adj.homEquiv (Ob.val ⊗ Oc.val) (twist R (b + c))) _
  have hleft :
      L.map (uab ▷ Oc.val) ≫
          L.map ((multiplyHom R a b).val ▷ Oc.val) =
        L.map (multiplyPresheafHom R a b ▷ Oc.val) := by
    rw [← L.map_comp, ← MonoidalCategory.comp_whiskerRight, hab]
  have hright :
      iaBC.hom ≫ L.map (Oa.val ◁ (multiplyHom R b c).val) =
        L.map (Oa.val ◁ multiplyPresheafHom R b c) := by
    change L.map (Oa.val ◁ ubc) ≫
        L.map (Oa.val ◁ (multiplyHom R b c).val) = _
    rw [← L.map_comp, ← MonoidalCategory.whiskerLeft_comp, hbc']
  let castS : twist R ((a + b) + c) ⟶ twist R (a + (b + c)) :=
    eqToHom (congrArg (twist R) h)
  let castP : (twist R ((a + b) + c)).val ⟶
      (twist R (a + (b + c))).val :=
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
      ((SheafOfModules.forget X.ringCatSheaf).map castS)
  have castP_eq : castP =
      eqToHom (congrArg (fun z : ℤ ↦ (twist R z).val) h) := by
    dsimp only [castP, castS]
    simp only [eqToHom_map]
  have hcounit : adj.counit.app (twist R ((a + b) + c)) ≫ castS =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map castP ≫
        adj.counit.app (twist R (a + (b + c))) := by
    have ht := adj.counit.naturality castS
    simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, castP] using ht.symm
  rw [← cancel_epi iabc.hom]
  change
    L.map (uab ▷ Oc.val) ≫
          L.map ((multiplyHom R a b).val ▷ Oc.val) ≫
          multiplyHom R (a + b) c ≫ eqToHom _ =
      iabc.hom ≫ iabc.inv ≫
          L.map (α_ Oa.val Ob.val Oc.val).hom ≫ iaBC.hom ≫
          L.map (Oa.val ◁ (multiplyHom R b c).val) ≫
          multiplyHom R a (b + c)
  rw [iabc.hom_inv_id_assoc]
  calc
    L.map (uab ▷ Oc.val) ≫
          L.map ((multiplyHom R a b).val ▷ Oc.val) ≫
          multiplyHom R (a + b) c ≫ eqToHom _ =
        L.map (multiplyPresheafHom R a b ▷ Oc.val) ≫
          multiplyHom R (a + b) c ≫ eqToHom _ :=
      congrArg (fun k ↦ k ≫ multiplyHom R (a + b) c ≫ eqToHom _) hleft
    _ = L.map (α_ Oa.val Ob.val Oc.val).hom ≫
          L.map (Oa.val ◁ multiplyPresheafHom R b c) ≫
          multiplyHom R a (b + c) := by
      rw [multiplyHom_eq, multiplyHom_eq]
      change L.map (multiplyPresheafHom R a b ▷ Oc.val) ≫
            L.map (multiplyPresheafHom R (a + b) c) ≫
            adj.counit.app (twist R ((a + b) + c)) ≫ castS =
        L.map (α_ Oa.val Ob.val Oc.val).hom ≫
            L.map (Oa.val ◁ multiplyPresheafHom R b c) ≫
            L.map (multiplyPresheafHom R a (b + c)) ≫
            adj.counit.app (twist R (a + (b + c)))
      rw [hcounit]
      change L.map (multiplyPresheafHom R a b ▷ Oc.val) ≫
            L.map (multiplyPresheafHom R (a + b) c) ≫
            L.map castP ≫ adj.counit.app (twist R (a + (b + c))) =
        L.map (α_ Oa.val Ob.val Oc.val).hom ≫
            L.map (Oa.val ◁ multiplyPresheafHom R b c) ≫
            L.map (multiplyPresheafHom R a (b + c)) ≫
            adj.counit.app (twist R (a + (b + c)))
      slice_lhs 1 3 => rw [← L.map_comp, ← L.map_comp]
      slice_rhs 1 3 => rw [← L.map_comp, ← L.map_comp]
      exact congrArg
        (fun k ↦ L.map k ≫ adj.counit.app (twist R (a + (b + c))))
        (by simpa only [castP_eq] using multiplyPresheafHom_assoc' R a b c h)
    _ = L.map (α_ Oa.val Ob.val Oc.val).hom ≫ iaBC.hom ≫
          L.map (Oa.val ◁ (multiplyHom R b c).val) ≫
          multiplyHom R a (b + c) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ L.map (α_ Oa.val Ob.val Oc.val).hom ≫ k ≫
          multiplyHom R a (b + c)) hright.symm

end ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable local instance instBraidedPresheafOfModules' :
    BraidedCategory X.PresheafOfModules :=
  inferInstanceAs (BraidedCategory
    (_root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- The chosen symmetry carries the inverse left unitor to the inverse right
unitor. -/
lemma tensorLeftUnitIso_inv_comp_tensorCommIso (F : X.Modules) :
    (tensorLeftUnitIso F).inv ≫
        (tensorCommIso (SheafOfModules.unit X.ringCatSheaf) F).hom =
      (tensorUnitIso F).inv := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  dsimp only [tensorLeftUnitIso, tensorCommIso, tensorUnitIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, asIso_inv, Iso.app_inv]
  rw [Category.assoc, ← (sheafification X).map_comp]
  exact congrArg
    (fun k ↦ (asIso adj.counit).inv.app F ≫ (sheafification X).map k)
    (CategoryTheory.leftUnitor_inv_braiding F.val)

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

/-- Multiplication by the inverse zero twist in the right factor is the inverse
right unitor. -/
lemma tensorUnitIso_inv_tensorMapRight_zeroIso_inv_multiplyHom
    (a : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso (twist R a)).inv ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
          (zeroIso R).inv ≫
        multiplyHom R a 0 ≫
        eqToHom (congrArg (twist R) (add_zero a)) =
      𝟙 (twist R a) := by
  let lu := AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso (twist R a)
  let bc := AlgebraicGeometry.Scheme.Modules.tensorCommIso
    (SheafOfModules.unit (Proj R).ringCatSheaf) (twist R a)
  have hunit :=
    AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso_inv_comp_tensorCommIso
      (twist R a)
  change lu.inv ≫ bc.hom =
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso (twist R a)).inv at hunit
  have hnat :=
    AlgebraicGeometry.Scheme.Modules.tensorCommIso_hom_naturality_left
      (zeroIso R).inv (twist R a)
  let hac : a + 0 = 0 + a := by omega
  have hcomm := multiplyHom_comm' R 0 a hac
  have hcast :
      eqToHom (congrArg (twist R) (add_zero a)) =
        eqToHom (congrArg (twist R) hac) ≫
          eqToHom (congrArg (twist R) (zero_add a)) := by
    rw [eqToHom_trans]
  have hcomm' :
      (AlgebraicGeometry.Scheme.Modules.tensorCommIso
          (twist R 0) (twist R a)).hom ≫
          multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a)) =
        multiplyHom R 0 a ≫
          eqToHom (congrArg (twist R) (zero_add a)) := by
    rw [hcast]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ eqToHom (congrArg (twist R) (zero_add a))) hcomm
  have hzero := tensorMapLeft_zeroIso_inv_multiplyHom R a
  calc
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso (twist R a)).inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
            (zeroIso R).inv ≫
          multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a)) =
        lu.inv ≫ bc.hom ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
            (zeroIso R).inv ≫
          multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a)) := by
      exact congrArg
        (fun k ↦ k ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
            (zeroIso R).inv ≫
          multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a))) hunit.symm
    _ = lu.inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapLeft
            (zeroIso R).inv (twist R a) ≫
          (AlgebraicGeometry.Scheme.Modules.tensorCommIso
            (twist R 0) (twist R a)).hom ≫
          multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ lu.inv ≫ k ≫ multiplyHom R a 0 ≫
          eqToHom (congrArg (twist R) (add_zero a))) hnat.symm
    _ = lu.inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapLeft
            (zeroIso R).inv (twist R a) ≫
          multiplyHom R 0 a ≫
          eqToHom (congrArg (twist R) (zero_add a)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ lu.inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapLeft
            (zeroIso R).inv (twist R a) ≫ k) hcomm'
    _ = lu.inv ≫ lu.hom := by rw [hzero]
    _ = _ := lu.inv_hom_id

/-- If multiplication by the zero twist is invertible, its inverse is obtained by
first transporting from degree `a` to degree `a + 0`, then applying the inverse
multiplication isomorphism. -/
lemma tensorUnitIso_inv_tensorMapRight_zeroIso_inv
    (a : ℤ) [IsIso (multiplyHom R a 0)] :
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso (twist R a)).inv ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
          (zeroIso R).inv =
      eqToHom (congrArg (twist R) (add_zero a).symm) ≫
        inv (multiplyHom R a 0) := by
  let t := multiplyHom R a 0 ≫
    eqToHom (congrArg (twist R) (add_zero a))
  letI : IsIso t := by
    dsimp only [t]
    infer_instance
  rw [← cancel_mono t]
  calc
    ((AlgebraicGeometry.Scheme.Modules.tensorUnitIso (twist R a)).inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorMapRight (twist R a)
            (zeroIso R).inv) ≫ t =
        𝟙 (twist R a) := by
      simpa only [t, Category.assoc] using
        tensorUnitIso_inv_tensorMapRight_zeroIso_inv_multiplyHom R a
    _ = (eqToHom (congrArg (twist R) (add_zero a).symm) ≫
          inv (multiplyHom R a 0)) ≫ t := by
      dsimp only [t]
      simp

/-- Multiplying a monomial into the left tensor factor and then multiplying the
two twists is the same as first multiplying the twists and then the monomial. -/
lemma mulHom_multiplyPresheafHom {m : ℕ} (p : R m)
    (a ac b : ℤ) (hac : ac = a + (m : ℤ))
    (habc : ac + b = (a + b) + (m : ℤ)) :
    MonoidalCategoryStruct.whiskerRight
          (C := (Proj R).PresheafOfModules)
          (mulHom R p a ac hac).val (twist R b).val ≫
        multiplyPresheafHom R ac b =
      multiplyPresheafHom R a b ≫
        (mulHom R p (a + b) (ac + b) habc).val := by
  refine PresheafOfModules.hom_ext (fun U ↦ ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun s t ↦ ?_)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((s.1 x).1 * Localization.mk (p : A) 1) * (t.1 x).1 =
    ((s.1 x).1 * (t.1 x).1) * Localization.mk (p : A) 1
  ring

/-- Sheaf multiplication is compatible with multiplying a monomial into its left
factor. -/
lemma mulHom_multiplyHom {m : ℕ} (p : R m)
    (a ac b : ℤ) (hac : ac = a + (m : ℤ))
    (habc : ac + b = (a + b) + (m : ℤ)) :
    AlgebraicGeometry.Scheme.Modules.tensorMapLeft
          (mulHom R p a ac hac) (twist R b) ≫
        multiplyHom R ac b =
      multiplyHom R a b ≫
        mulHom R p (a + b) (ac + b) habc := by
  rw [multiplyHom_eq, multiplyHom_eq]
  change (AlgebraicGeometry.Scheme.Modules.sheafification (Proj R)).map
      (MonoidalCategoryStruct.whiskerRight
        (C := (Proj R).PresheafOfModules)
        (mulHom R p a ac hac).val (twist R b).val) ≫ _ = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    mulHom_multiplyPresheafHom R p a ac b hac habc,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj R).ringCatSheaf.obj)).counit.naturality
      (mulHom R p (a + b) (ac + b) habc)

end ProjectiveSpectrum.Twist

end

end

