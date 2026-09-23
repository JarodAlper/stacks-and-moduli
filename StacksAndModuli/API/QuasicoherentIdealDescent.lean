module

public import StacksAndModuli.API.ClosedImmersionQuotient
public import StacksAndModuli.API.QuasicoherentDescentComparison
public import StacksAndModuli.API.QuasicoherentQuotientClassification

/-!
# Effective fpqc descent for quasicoherent ideal sheaves

This supporting module descends a quasicoherent ideal sheaf along a singleton
fpqc cover.  It regards the local closed quotient as a quasicoherent module,
constructs its canonical descent datum by classifying epimorphic quotients by
their kernels, and then applies effective fpqc descent for quasicoherent modules.
The quotient map descends by full faithfulness, and its global kernel is the
required ideal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {S' S : Scheme.{u}} (f : S' ⟶ S)
  (I' : S'.IdealSheafData)
  (h : I'.comap (Limits.pullback.fst f f) =
    I'.comap (Limits.pullback.snd f f))

namespace FpqcIdealDescent

include h in
/-- The kernel-pair equality identifies pullbacks of the ideal along any two
maps over the base. -/
lemma comap_eq_of_comp_eq {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) : I'.comap a = I'.comap b := by
  let l : Y ⟶ Limits.pullback f f := Limits.pullback.lift a b hab
  calc
    I'.comap a = (I'.comap (Limits.pullback.fst f f)).comap l := by
      rw [← IdealSheafData.comap_comp, Limits.pullback.lift_fst]
    _ = (I'.comap (Limits.pullback.snd f f)).comap l := by rw [h]
    _ = I'.comap b := by
      rw [← IdealSheafData.comap_comp, Limits.pullback.lift_snd]

/-- The closed immersion cut out by the local ideal. -/
noncomputable def localClosedImmersion : I'.subscheme ⟶ S' := I'.subschemeι

instance localClosedImmersion_isClosedImmersion :
    IsClosedImmersion (localClosedImmersion I') := by
  dsimp [localClosedImmersion]
  infer_instance

/-- The quasicoherent quotient of the local structure sheaf by the ideal. -/
noncomputable def localQuotient : S'.Modules :=
  (localClosedImmersion I').closedQuotient

/-- The canonical map from the local structure sheaf to its closed quotient. -/
noncomputable def localQuotientMap :
    SheafOfModules.unit S'.ringCatSheaf ⟶ localQuotient I' :=
  (localClosedImmersion I').toClosedQuotient

instance localQuotient_isQuasicoherent :
    (localQuotient I').IsQuasicoherent := by
  dsimp [localQuotient, localClosedImmersion]
  infer_instance

instance localQuotientMap_epi : Epi (localQuotientMap I') := by
  dsimp [localQuotientMap, localQuotient, localClosedImmersion]
  infer_instance

include h in
/-- Pullbacks of the local closed quotient along two maps over the base have
equal kernel ideal sheaves. -/
lemma pullback_kernel_eq {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    kernelIdealSheafData ((Modules.pullback a).obj (localQuotient I'))
        (pullbackUnitMap a (localQuotientMap I')) =
      kernelIdealSheafData ((Modules.pullback b).obj (localQuotient I'))
        (pullbackUnitMap b (localQuotientMap I')) := by
  let _ : (localQuotient I').IsQuasicoherent := by
    dsimp [localQuotient, localClosedImmersion]
    infer_instance
  let _ : ((Modules.pullback a).obj
      (localQuotient I')).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback a (localQuotient I')
  let _ : ((Modules.pullback b).obj
      (localQuotient I')).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback b (localQuotient I')
  let _ : Epi (localQuotientMap I') := localQuotientMap_epi I'
  let _ : Epi ((Modules.pullback a).map (localQuotientMap I')) :=
    CategoryTheory.Functor.map_epi (Modules.pullback a) (localQuotientMap I')
  let _ : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      a.toRingCatSheafHom)) := inferInstance
  let _ : Epi (pullbackUnitMap a (localQuotientMap I')) := by
    dsimp [pullbackUnitMap]
    infer_instance
  let _ : Epi ((Modules.pullback b).map (localQuotientMap I')) :=
    CategoryTheory.Functor.map_epi (Modules.pullback b) (localQuotientMap I')
  let _ : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      b.toRingCatSheafHom)) := inferInstance
  let _ : Epi (pullbackUnitMap b (localQuotientMap I')) := by
    dsimp [pullbackUnitMap]
    infer_instance
  rw [kernelIdealSheafData_pullback_of_epi,
    kernelIdealSheafData_pullback_of_epi]
  have hQ : kernelIdealSheafData (localQuotient I')
      (localQuotientMap I') = I' := by
    calc
      _ = (localClosedImmersion I').ker := by
        exact Hom.kernelIdealSheafData_toClosedQuotient
          (i := localClosedImmersion I')
      _ = I' := by
        dsimp [localClosedImmersion]
        rw [IdealSheafData.ker_subschemeι]
  rw [hQ]
  exact comap_eq_of_comp_eq f I' h a b hab

include h in
/-- Pullbacks of the local closed quotient along two maps over the base are
compatibly isomorphic. -/
lemma exists_pullback_iso {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    ∃ e : (Modules.pullback a).obj (localQuotient I') ≅
        (Modules.pullback b).obj (localQuotient I'),
      pullbackUnitMap a (localQuotientMap I') ≫ e.hom =
        pullbackUnitMap b (localQuotientMap I') := by
  let _ : (localQuotient I').IsQuasicoherent := by
    dsimp [localQuotient, localClosedImmersion]
    infer_instance
  let _ : ((Modules.pullback a).obj
      (localQuotient I')).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback a (localQuotient I')
  let _ : ((Modules.pullback b).obj
      (localQuotient I')).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback b (localQuotient I')
  let _ : Epi (localQuotientMap I') := localQuotientMap_epi I'
  let _ : Epi ((Modules.pullback a).map (localQuotientMap I')) :=
    CategoryTheory.Functor.map_epi (Modules.pullback a) (localQuotientMap I')
  let _ : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      a.toRingCatSheafHom)) := inferInstance
  let _ : Epi (pullbackUnitMap a (localQuotientMap I')) := by
    dsimp [pullbackUnitMap]
    infer_instance
  let _ : Epi ((Modules.pullback b).map (localQuotientMap I')) :=
    CategoryTheory.Functor.map_epi (Modules.pullback b) (localQuotientMap I')
  let _ : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      b.toRingCatSheafHom)) := inferInstance
  let _ : Epi (pullbackUnitMap b (localQuotientMap I')) := by
    dsimp [pullbackUnitMap]
    infer_instance
  apply exists_iso_of_kernelIdealSheafData_eq
  exact pullback_kernel_eq f I' h a b hab

include h in
/-- A chosen compatible isomorphism between two pullbacks of the local quotient. -/
noncomputable def pullbackIso {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    (Modules.pullback a).obj (localQuotient I') ≅
      (Modules.pullback b).obj (localQuotient I') :=
  (exists_pullback_iso f I' h a b hab).choose

include h in
/-- The chosen isomorphism carries the first normalized quotient map to the second. -/
lemma unit_comp_pullbackIso_hom {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    pullbackUnitMap a (localQuotientMap I') ≫
        (pullbackIso f I' h a b hab).hom =
      pullbackUnitMap b (localQuotientMap I') :=
  (exists_pullback_iso f I' h a b hab).choose_spec

include h in
/-- The inverse chosen isomorphism carries the second normalized quotient map
to the first. -/
lemma unit_comp_pullbackIso_inv {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    pullbackUnitMap b (localQuotientMap I') ≫
        (pullbackIso f I' h a b hab).inv =
      pullbackUnitMap a (localQuotientMap I') := by
  rw [← unit_comp_pullbackIso_hom f I' h a b hab, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The local closed quotient as an object of the quasicoherent subcategory. -/
noncomputable def localQuotientQC :
    (Scheme.Modules.isQuasicoherentProperty.prop
      (.mk (.op S'))).FullSubcategory :=
  ⟨localQuotient I', localQuotient_isQuasicoherent I'⟩

include h in
/-- The chosen pullback isomorphism as a morphism of quasicoherent modules. -/
noncomputable def pullbackQCHom {Y : Scheme.{u}} (a b : Y ⟶ S')
    (hab : a ≫ f = b ≫ f) :
    (Scheme.Modules.quasicoherentPseudofunctor.map a.op.toLoc).toFunctor.obj
        (localQuotientQC I') ⟶
      (Scheme.Modules.quasicoherentPseudofunctor.map b.op.toLoc).toFunctor.obj
        (localQuotientQC I') :=
  CategoryTheory.ObjectProperty.homMk (pullbackIso f I' h a b hab).hom

include h in
/-- The underlying module map of the pseudofunctorial pullback of the chosen
quasicoherent isomorphism. -/
lemma pullbackQCHom_pullHom_hom {Y Y' : Scheme.{u}}
    (a b : Y ⟶ S') (hab : a ≫ f = b ≫ f) (g : Y' ⟶ Y) :
    (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := Scheme.Modules.quasicoherentPseudofunctor)
      (pullbackQCHom f I' h a b hab) g (g ≫ a) (g ≫ b) rfl rfl).hom =
      (Modules.pullbackComp g a).inv.app (localQuotient I') ≫
        (Modules.pullback g).map (pullbackIso f I' h a b hab).hom ≫
        (Modules.pullbackComp g b).hom.app (localQuotient I') := by
  rfl

include h in
/-- Pulling back a chosen transition preserves compatibility with the normalized
quotient maps. -/
lemma unit_comp_pullbackQCHom_pullHom_comp {Y Y' : Scheme.{u}}
    (a b : Y ⟶ S') (hab : a ≫ f = b ≫ f) (g : Y' ⟶ Y) :
    pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
        (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := Scheme.Modules.quasicoherentPseudofunctor)
          (pullbackQCHom f I' h a b hab) g (g ≫ a) (g ≫ b) rfl rfl).hom =
      pullbackUnitMap (g ≫ b) (localQuotientMap I') := by
  rw [pullbackQCHom_pullHom_hom f I' h a b hab g]
  have hleft :
      pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
          (Modules.pullbackComp g a).inv.app (localQuotient I') =
        pullbackUnitMap g (pullbackUnitMap a (localQuotientMap I')) := by
    rw [← cancel_mono ((Modules.pullbackComp g a).hom.app
      (localQuotient I'))]
    calc
      (pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
          (Modules.pullbackComp g a).inv.app (localQuotient I')) ≫
          (Modules.pullbackComp g a).hom.app (localQuotient I') =
        pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
          ((Modules.pullbackComp g a).inv.app (localQuotient I') ≫
            (Modules.pullbackComp g a).hom.app (localQuotient I')) :=
        Category.assoc _ _ _
      _ = pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫ 𝟙 _ :=
        congrArg
          (fun k ↦ pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫ k)
          ((Modules.pullbackComp g a).inv_hom_id_app (localQuotient I'))
      _ = pullbackUnitMap (g ≫ a) (localQuotientMap I') :=
        Category.comp_id _
      _ = pullbackUnitMap g (pullbackUnitMap a (localQuotientMap I')) ≫
          (Modules.pullbackComp g a).hom.app (localQuotient I') :=
        (pullbackUnitMap_comp g a (localQuotientMap I')).symm
  rw [reassoc_of% hleft,
    ← pullbackUnitMap_comp g b (localQuotientMap I')]
  have hnat := pullbackUnitMap_naturality g _ _ _
    (unit_comp_pullbackIso_hom f I' h a b hab)
  exact (reassoc_of% hnat)
    ((Modules.pullbackComp g b).hom.app (localQuotient I'))

include h in
/-- The canonical singleton descent datum on the local closed quotient. -/
noncomputable def quotientDescentData :
    Scheme.Modules.quasicoherentPseudofunctor.DescentData
      (fun _ : PUnit.{1} ↦ f) where
  obj _ := localQuotientQC I'
  hom Y q _ _ a b ha hb :=
    pullbackQCHom f I' h a b (ha.trans hb.symm)
  pullHom_hom Y' Y g q q' hq i₁ i₂ a b ha hb ga gb hga hgb := by
    subst ga
    subst gb
    apply CategoryTheory.ObjectProperty.hom_ext
    rw [← cancel_epi
      (pullbackUnitMap (g ≫ a) (localQuotientMap I'))]
    calc
      pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
          (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := Scheme.Modules.quasicoherentPseudofunctor)
            (pullbackQCHom f I' h a b (ha.trans hb.symm))
            g (g ≫ a) (g ≫ b) rfl rfl).hom =
        pullbackUnitMap (g ≫ b) (localQuotientMap I') :=
          unit_comp_pullbackQCHom_pullHom_comp f I' h a b
            (ha.trans hb.symm) g
      _ = pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
          (pullbackQCHom f I' h (g ≫ a) (g ≫ b)
            (by rw [Category.assoc, ha, Category.assoc, hb])).hom := by
        change pullbackUnitMap (g ≫ b) (localQuotientMap I') =
          pullbackUnitMap (g ≫ a) (localQuotientMap I') ≫
            (pullbackIso f I' h (g ≫ a) (g ≫ b) _).hom
        exact (unit_comp_pullbackIso_hom f I' h
          (g ≫ a) (g ≫ b) _).symm
  hom_self Y q i a ha := by
    apply CategoryTheory.ObjectProperty.hom_ext
    rw [← cancel_epi (pullbackUnitMap a (localQuotientMap I'))]
    change pullbackUnitMap a (localQuotientMap I') ≫
        (pullbackIso f I' h a a (ha.trans ha.symm)).hom =
      pullbackUnitMap a (localQuotientMap I') ≫ 𝟙 _
    rw [unit_comp_pullbackIso_hom, Category.comp_id]
  hom_comp Y q i₁ i₂ i₃ a b c ha hb hc := by
    apply CategoryTheory.ObjectProperty.hom_ext
    rw [← cancel_epi (pullbackUnitMap a (localQuotientMap I'))]
    change pullbackUnitMap a (localQuotientMap I') ≫
          (pullbackIso f I' h a b (ha.trans hb.symm)).hom ≫
          (pullbackIso f I' h b c (hb.trans hc.symm)).hom =
        pullbackUnitMap a (localQuotientMap I') ≫
          (pullbackIso f I' h a c (ha.trans hc.symm)).hom
    rw [reassoc_of% unit_comp_pullbackIso_hom f I' h a b
      (ha.trans hb.symm)]
    rw [unit_comp_pullbackIso_hom, unit_comp_pullbackIso_hom]

include h in
/-- The transition in the quotient descent datum is the chosen pullback isomorphism. -/
lemma quotientDescentData_hom_hom {Y : Scheme.{u}} (q : Y ⟶ S)
    (i₁ i₂ : PUnit.{1}) (a b : Y ⟶ S')
    (ha : a ≫ f = q) (hb : b ≫ f = q) :
    ((quotientDescentData f I' h).hom (i₁ := i₁) (i₂ := i₂)
      q a b ha hb).hom =
      (pullbackIso f I' h a b (ha.trans hb.symm)).hom := by
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the commutativity field through the quasicoherent full subcategory is costly.
/-- The local quotient map as a morphism from the canonical structure-sheaf
descent datum to the quotient descent datum. -/
noncomputable def quotientDescentMap :
    (Scheme.Modules.quasicoherentPseudofunctor.toDescentData
      (fun _ : PUnit.{1} ↦ f)).obj (unitQuasicoherentObject S) ⟶
      quotientDescentData f I' h where
  hom _ := CategoryTheory.ObjectProperty.homMk
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
      localQuotientMap I')
  comm Y q i₁ i₂ a b ha hb := by
    apply CategoryTheory.ObjectProperty.hom_ext
    change
      ((Scheme.Modules.quasicoherentPseudofunctor.map
          a.op.toLoc).toFunctor.map
          (CategoryTheory.ObjectProperty.homMk
            (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom ≫ localQuotientMap I'))).hom ≫
        ((quotientDescentData f I' h).hom
          (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom =
      (((Scheme.Modules.quasicoherentPseudofunctor.toDescentData
          (fun _ : PUnit.{1} ↦ f)).obj
          (unitQuasicoherentObject S)).hom
          (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom ≫
        ((Scheme.Modules.quasicoherentPseudofunctor.map
          b.op.toLoc).toFunctor.map
          (CategoryTheory.ObjectProperty.homMk
            (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom ≫ localQuotientMap I'))).hom
    rw [quasicoherentMap_hom, quasicoherentMap_hom,
      quotientDescentData_hom_hom f I' h q i₁ i₂ a b ha hb,
      unitQuasicoherentObject_descent_hom_hom f q i₁ i₂ a b ha hb]
    let A := pullbackUnitMap f
      (𝟙 (SheafOfModules.unit S.ringCatSheaf))
    let _ : IsIso A := by
      dsimp [A, pullbackUnitMap]
      infer_instance
    have hAinv : inv A =
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
      dsimp only [A, pullbackUnitMap]
      simp only [IsIso.inv_comp, IsIso.inv_inv, IsIso.inv_comp_eq]
      have hmap : (Modules.pullback f).map
          (𝟙 (SheafOfModules.unit S.ringCatSheaf)) = 𝟙 _ :=
        (Modules.pullback f).map_id
          (SheafOfModules.unit S.ringCatSheaf)
      rw [hmap]
      exact (Category.id_comp
        (SheafOfModules.pullbackObjUnitToUnit
          f.toRingCatSheafHom)).symm
    rw [← cancel_epi (pullbackUnitMap a A)]
    rw [← hAinv]
    rw [reassoc_of% pullbackUnitMap_naturality a A
      (localQuotientMap I') (inv A ≫ localQuotientMap I') (by simp)]
    rw [unit_comp_pullbackIso_hom]
    rw [reassoc_of% pullbackUnitMap_comp_pullbackCompCongrIso
      a f b f (ha.trans hb.symm)
      (𝟙 (SheafOfModules.unit S.ringCatSheaf))]
    rw [pullbackUnitMap_naturality b A
      (localQuotientMap I') (inv A ≫ localQuotientMap I') (by simp)]

include h in
/-- Effective quasicoherent descent produces a global module, a global
structure-sheaf map, and a compatible local quotient isomorphism. -/
lemma exists_descendedLocalQuotient (hf : Scheme.IsFpqcCover f) :
    ∃ M : S.Modules, M.IsQuasicoherent ∧
      ∃ phi : SheafOfModules.unit S.ringCatSheaf ⟶ M,
        ∃ e : (Modules.pullback f).obj M ≅ localQuotient I',
          pullbackUnitMap f phi ≫ e.hom = localQuotientMap I' := by
  let _ : Scheme.Modules.quasicoherentPseudofunctor.IsStack
      Scheme.fpqcTopology :=
    Scheme.Modules.isStack_quasicoherentPseudofunctor
  have hcover : Sieve.ofArrows (fun _ : PUnit.{1} ↦ S')
      (fun _ : PUnit.{1} ↦ f) ∈ Scheme.fpqcTopology S := by
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
    exact Precoverage.generate_mem_toGrothendieck hf
  let T := Scheme.Modules.quasicoherentPseudofunctor.toDescentData
    (fun _ : PUnit.{1} ↦ f)
  let _ : T.IsEquivalence :=
    Scheme.Modules.quasicoherentPseudofunctor.isEquivalence_toDescentData _ hcover
  let D := quotientDescentData f I' h
  let Mqc := T.objPreimage D
  let eD : T.obj Mqc ≅ D := T.objObjPreimageIso D
  let mD : T.obj (unitQuasicoherentObject S) ⟶ D :=
    quotientDescentMap f I' h
  let phiQC := T.preimage (mD ≫ eD.inv)
  let phi : SheafOfModules.unit S.ringCatSheaf ⟶ Mqc.obj := phiQC.hom
  let e : (Modules.pullback f).obj Mqc.obj ≅ localQuotient I' :=
    { hom := (eD.hom.hom default).hom
      inv := (eD.inv.hom default).hom
      hom_inv_id := congrArg (fun k ↦ (k.hom default).hom) eD.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ (k.hom default).hom) eD.inv_hom_id }
  have hmap := T.map_preimage (mD ≫ eD.inv)
  have hmap₀ := congrArg (fun k ↦ (k.hom default).hom) hmap
  have hmap₁ : (Modules.pullback f).map phi =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        localQuotientMap I' ≫ e.inv := by
    exact hmap₀
  refine ⟨Mqc.obj, Mqc.property, phi, e, ?_⟩
  dsimp only [pullbackUnitMap]
  rw [hmap₁]
  simp

end FpqcIdealDescent

end

end AlgebraicGeometry.Scheme.Modules.Hom

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

open Modules.Hom Modules.Hom.FpqcIdealDescent

variable {S' S : Scheme.{u}} (f : S' ⟶ S)
  (I' : S'.IdealSheafData)
  (h : I'.comap (Limits.pullback.fst f f) =
    I'.comap (Limits.pullback.snd f f))

include h in
/-- Effective fpqc descent for a quasicoherent ideal sheaf presented in
kernel-pair form. -/
theorem exists_descended_of_fpqcCover (hf : Scheme.IsFpqcCover f) :
    ∃ I : S.IdealSheafData, I.comap f = I' := by
  obtain ⟨M, hM, phi, e, he⟩ :=
    Modules.Hom.FpqcIdealDescent.exists_descendedLocalQuotient f I' h hf
  let _ : M.IsQuasicoherent := hM
  let _ : ((Modules.pullback f).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback f M
  let _ : Flat f := hf.flat
  refine ⟨kernelIdealSheafData M phi, ?_⟩
  calc
    (kernelIdealSheafData M phi).comap f =
        kernelIdealSheafData ((Modules.pullback f).obj M)
          (pullbackUnitMap f phi) :=
      (kernelIdealSheafData_pullback_of_flat f M phi).symm
    _ = kernelIdealSheafData (localQuotient I')
        (localQuotientMap I') :=
      kernelIdealSheafData_eq_of_iso _ _ _ _ e he
    _ = (Modules.Hom.FpqcIdealDescent.localClosedImmersion I').ker :=
      Hom.kernelIdealSheafData_toClosedQuotient
        (i := Modules.Hom.FpqcIdealDescent.localClosedImmersion I')
    _ = I' := by
      dsimp only [Modules.Hom.FpqcIdealDescent.localClosedImmersion]
      rw [IdealSheafData.ker_subschemeι]

end

end AlgebraicGeometry.Scheme.IdealSheafData
