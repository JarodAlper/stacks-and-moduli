module

public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.QuasicoherentDescentComparison
public import StacksAndModuli.API.QuasicoherentFamilyStacks
public import StacksAndModuli.API.StrictQuotientKernelModel
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# Zariski descent for the Quot functor

This file develops effective Zariski descent for flat, finitely presented,
quasicoherent quotients.  Its kernel-normalization layer is the analogue for the
general Quot functor of the construction used in the proof that the relative
Grassmannian functor is a Zariski sheaf.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.normalizedAmbientIso`;
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.normalizedKernelι`;
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.restrictPullback`;
- `AlgebraicGeometry.Scheme.Modules.QuotientOpenDescent.isSheaf_quotFunctor`;
- `AlgebraicGeometry.Scheme.Modules.QuotientOpenDescent.isSheaf_strictQuotFunctor`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace CategoryTheory.Pseudofunctor.ObjectProperty.DescentData

universe t v' v u'

variable {C : Type u} [Category.{v} C]
variable {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (P : G.ObjectProperty) [P.IsClosedUnderMapObj]
variable {I : Type t} {B : C} {U : I → C} (p : ∀ i, U i ⟶ B)

/-- Lift descent data to the full subpseudofunctor cut out by an object
property, once that property is supplied on every local object. -/
noncomputable def lift
    (D : G.DescentData p) (hD : ∀ i, P.prop _ (D.obj i)) :
    P.fullsubcategory.DescentData p where
  obj i := ⟨D.obj i, hD i⟩
  hom Y q i₁ i₂ a b ha hb := ObjectProperty.homMk
    (D.hom q a b ha hb)
  pullHom_hom Y' Y g q q' hq i₁ i₂ a b ha hb ga gb hga hgb := by
    apply ObjectProperty.hom_ext
    exact D.pullHom_hom g q q' hq a b ha hb ga gb hga hgb
  hom_self Y q i a ha := by
    apply ObjectProperty.hom_ext
    exact D.hom_self q a ha
  hom_comp Y q i₁ i₂ i₃ a b c ha hb hc := by
    apply ObjectProperty.hom_ext
    exact D.hom_comp q a b c ha hb hc

/-- Forget an isomorphism of descent data for a full subpseudofunctor. -/
noncomputable def forgetIso
    {D E : P.fullsubcategory.DescentData p} (e : D ≅ E) :
    forget P p D ≅ forget P p E where
  hom := forgetHom P p e.hom
  inv := forgetHom P p e.inv
  hom_inv_id := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact congrArg (fun k ↦ (k.hom i).hom) e.hom_inv_id
  inv_hom_id := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact congrArg (fun k ↦ (k.hom i).hom) e.inv_hom_id

end CategoryTheory.Pseudofunctor.ObjectProperty.DescentData

namespace CategoryTheory.Pseudofunctor

universe t vC uC vD uD vE uE

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (H : C ⥤ D)
variable (G : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{vE, uE})

/-- The transition in the canonical descent datum for a precomposed
pseudofunctor is the canonical transition after applying the precomposition
functor. -/
lemma comp_toDescentData_obj_hom
    {I : Type t} {S Y : C} {X : I → C}
    (p : ∀ i, X i ⟶ S) (q : Y ⟶ S)
    (i₁ i₂ : I) (a : Y ⟶ X i₁) (b : Y ⟶ X i₂)
    (ha : a ≫ p i₁ = q) (hb : b ≫ p i₂ = q)
    (M : G.obj (.mk (op (H.obj S)))) :
    (((Pseudofunctor.comp H.op.toPseudofunctor G).toDescentData p).obj M).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb =
      ((G.toDescentData (fun i ↦ H.map (p i))).obj M).hom
        (i₁ := i₁) (i₂ := i₂) (H.map q) (H.map a) (H.map b)
        (by rw [← H.map_comp, ha]) (by rw [← H.map_comp, hb]) := by
  dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  rw [comp_mapComp'_eq H G (p i₁) a q ha,
    comp_mapComp'_eq H G (p i₂) b q hb]

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

variable {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S} (T : Over S)

/-- The base-changed map of total spaces is an open immersion when the map of test
schemes is one. -/
instance overPullbackMapLeft_isOpenImmersion {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] :
    IsOpenImmersion ((Over.pullback f).map g).left := by
  exact MorphismProperty.of_isPullback
    (CategoryTheory.Over.isPullback_pullback_map_left f g) inferInstance

/-- The comparison from the canonical source sheaf of a local Quot datum to the
literal restriction of the source sheaf on the covered test scheme. -/
noncomputable def normalizedAmbientIso {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] :
    (Modules.pullback ((Over.pullback f).obj T').hom).obj F ≅
      (Modules.restrictFunctor ((Over.pullback f).map g).left).obj
        ((Modules.pullback ((Over.pullback f).obj T).hom).obj F) :=
  PullbackQuotient.pullbackComparison F ((Over.pullback f).map g) ≪≫
    (Modules.restrictFunctorIsoPullback ((Over.pullback f).map g).left).symm.app _

/-- The kernel inclusion of a local Quot datum, normalized into the literal
restriction of the global source sheaf. -/
noncomputable def normalizedKernelι {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    kernel x.π ⟶
      (Modules.restrictFunctor ((Over.pullback f).map g).left).obj
        ((Modules.pullback ((Over.pullback f).obj T).hom).obj F) :=
  kernel.ι x.π ≫ (normalizedAmbientIso T g).hom

instance normalizedKernelι_mono {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    Mono (normalizedKernelι T g x) := by
  dsimp [normalizedKernelι]
  infer_instance

/-- Normalizing the ambient object transports the strict kernel by the same
isomorphism. -/
lemma range_normalizedKernelι {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    PresheafOfModules.Submodule.range (normalizedKernelι T g x).val =
      x.kernelData.mapIso
        ((SheafOfModules.forget ((Over.pullback f).obj T').left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) := by
  exact PresheafOfModules.Submodule.range_comp_iso (kernel.ι x.π).val
    ((SheafOfModules.forget ((Over.pullback f).obj T').left.ringCatSheaf).mapIso
      (normalizedAmbientIso T g))

/-- For an open immersion of test schemes, pull a Quot datum back using literal
restriction on the total spaces.  This is equivalent to the standard
pseudofunctorial pullback and is convenient for kernel descent. -/
noncomputable def restrictPullback {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T) :
    QuotientPullbackData F f T' where
  Q := (Modules.restrictFunctor ((Over.pullback f).map g).left).obj x.Q
  isQuasicoherent := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    infer_instance
  isFinitePresentation := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    letI : x.Q.IsFinitePresentation := x.isFinitePresentation
    have hpb : ((Modules.pullback
        ((Over.pullback f).map g).left).obj x.Q).IsFinitePresentation := by
      infer_instance
    exact ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation
        ((Over.pullback f).obj T').left.ringCatSheaf)
      ((Modules.restrictFunctorIsoPullback
        ((Over.pullback f).map g).left).app x.Q).symm hpb
  flatOver := by
    exact FlatOver.of_iso
      ((Modules.restrictFunctorIsoPullback ((Over.pullback f).map g).left).app x.Q).symm
      (x.pullback g).flatOver
  π := (normalizedAmbientIso T g).hom ≫
    (Modules.restrictFunctor ((Over.pullback f).map g).left).map x.π
  epi := by
    letI : Epi x.π := x.epi
    infer_instance

/-- The restriction-normalized pullback represents the same quotient class as the
standard pullback. -/
lemma restrictPullback_r_pullback {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T) :
    (QuotientPullbackData.setoid F f T').r (restrictPullback T g x) (x.pullback g) := by
  refine ⟨(Modules.restrictFunctorIsoPullback
    ((Over.pullback f).map g).left).app x.Q, ?_⟩
  dsimp [restrictPullback, QuotientPullbackData.pullback, normalizedAmbientIso]
  rw [Category.assoc, (Modules.restrictFunctorIsoPullback
    ((Over.pullback f).map g).left).hom.naturality]
  simp

/-- Equivalent standard and restriction-normalized pullbacks have the same strict
kernel. -/
lemma kernelData_restrictPullback_eq_pullback {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T) :
    (restrictPullback T g x).kernelData = (x.pullback g).kernelData :=
  kernelData_eq_of_r (restrictPullback_r_pullback T g x)

/-- After undoing ambient normalization, the kernel of a restriction-normalized
pullback is the literal restriction of the original kernel inclusion. -/
lemma kernelData_restrictPullback_mapIso {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T) :
    (restrictPullback T g x).kernelData.mapIso
        ((SheafOfModules.forget ((Over.pullback f).obj T').left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) =
      PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor ((Over.pullback f).map g).left).map
          (kernel.ι x.π)).val := by
  let G := ((Over.pullback f).map g).left
  let R := Modules.restrictFunctor G
  haveI := Scheme.Modules.restrictFunctor_preservesKernel G x.π
  let eK : R.obj (kernel x.π) ≅ kernel (R.map x.π) :=
    PreservesKernel.iso R x.π
  have heK : eK.hom ≫ kernel.ι (R.map x.π) = R.map (kernel.ι x.π) := by
    dsimp [eK]
    simp
  calc
    (restrictPullback T g x).kernelData.mapIso
        ((SheafOfModules.forget ((Over.pullback f).obj T').left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) =
      PresheafOfModules.Submodule.range (kernel.ι (R.map x.π)).val :=
        SheafOfModules.kernelRange_comp_iso (R.map x.π) (normalizedAmbientIso T g)
    _ = PresheafOfModules.Submodule.range (R.map (kernel.ι x.π)).val :=
      (PresheafOfModules.Submodule.range_eq_of_iso
        (R.map (kernel.ι x.π)).val (kernel.ι (R.map x.π)).val
        ((SheafOfModules.forget ((Over.pullback f).obj T').left.ringCatSheaf).mapIso eK)
        (congrArg SheafOfModules.Hom.val heK)).symm

/-- The cokernel of a normalized local kernel is canonically the original local
quotient sheaf. -/
noncomputable def normalizedKernelCokernelIso {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    cokernel (normalizedKernelι T g x) ≅ x.Q := by
  letI : Epi x.π := x.epi
  exact cokernel.mapIso (f := normalizedKernelι T g x) (kernel.ι x.π)
      (Iso.refl _) (normalizedAmbientIso T g).symm (by
        dsimp [normalizedKernelι]
        simp) ≪≫
    cokernelKernelIsoOfEpi x.π

/-- The normalized-kernel cokernel comparison identifies its projection with the
original Quot projection after undoing ambient normalization. -/
@[reassoc]
lemma cokernel_π_comp_normalizedKernelCokernelIso_hom {T' : Over S}
    (g : T' ⟶ T) [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    cokernel.π (normalizedKernelι T g x) ≫
        (normalizedKernelCokernelIso T g x).hom =
      (normalizedAmbientIso T g).inv ≫ x.π := by
  dsimp [normalizedKernelCokernelIso]
  rw [cokernel.mapIso_hom, ← Category.assoc, cokernel.π_desc]
  rw [Category.assoc, cokernel_π_comp_cokernelKernelIsoOfEpi_hom, Iso.symm_hom]

/-- The cokernel of a normalized local kernel remains quasicoherent. -/
lemma normalizedKernelCokernel_isQuasicoherent {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    (cokernel (normalizedKernelι T g x)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
    ((Over.pullback f).obj T').left.ringCatSheaf).prop_of_iso
      (normalizedKernelCokernelIso T g x).symm x.isQuasicoherent

/-- The cokernel of a normalized local kernel remains finitely presented. -/
lemma normalizedKernelCokernel_isFinitePresentation {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : QuotientPullbackData F f T') :
    (cokernel (normalizedKernelι T g x)).IsFinitePresentation :=
  ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation
      ((Over.pullback f).obj T').left.ringCatSheaf)
    (normalizedKernelCokernelIso T g x).symm x.isFinitePresentation

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
  (COV : Scheme.OpenCover.{u} T.left)

/-- Pulling an open cover of a test scheme across `T ×_S X ⟶ T`, with its
charts replaced by the definitionally preferred fiber products
`U_i ×_S X`.  Thus its chart maps are literally those induced by
`Over.pullback f` from the original cover maps. -/
noncomputable def quotientTotalOpenCover :
    Scheme.OpenCover.{u} ((Over.pullback f).obj T).left :=
  Cover.copy (COV.pullback₁ (pullback.fst T.hom f)) COV.I₀
    (fun i ↦ ((Over.pullback f).obj (openCoverObjectOver T COV i)).left)
    (fun i ↦ ((Over.pullback f).map (openCoverMapOver T COV i)).left)
    (Equiv.refl COV.I₀)
    (fun i ↦ (pullbackSymmetry (pullback.fst T.hom f) (COV.f i) ≪≫
      pullbackRightPullbackFstIso T.hom f (COV.f i)).symm)
    (fun i ↦ by
      apply pullback.hom_ext
      · dsimp only [Precoverage.ZeroHypercover.pullback₁,
          PreZeroHypercover.pullback₁, openCoverObjectOver]
        simp only [Over.pullback_map_left, openCoverMapOver_left,
          Over.mk_hom, Equiv.refl_apply,
          Iso.symm_hom, Iso.trans_inv,
          pullback.lift_fst, Category.assoc,
          pullbackSymmetry_inv_comp_fst_assoc,
          pullbackRightPullbackFstIso_inv_snd_fst]
      · dsimp only [Precoverage.ZeroHypercover.pullback₁,
          PreZeroHypercover.pullback₁, openCoverObjectOver]
        simp only [Over.pullback_map_left, openCoverMapOver_left,
          Over.mk_hom, Equiv.refl_apply,
          Iso.symm_hom, Iso.trans_inv,
          pullback.lift_snd, Category.assoc,
          pullbackSymmetry_inv_comp_fst_assoc,
          pullbackRightPullbackFstIso_inv_snd_snd])

@[simp]
lemma quotientTotalOpenCover_X (i : COV.I₀) :
    (quotientTotalOpenCover f T COV).X i =
      ((Over.pullback f).obj (openCoverObjectOver T COV i)).left :=
  rfl

@[simp]
lemma quotientTotalOpenCover_f (i : COV.I₀) :
    (quotientTotalOpenCover f T COV).f i =
      ((Over.pullback f).map (openCoverMapOver T COV i)).left :=
  rfl

namespace Modules.QuotientPullbackData

variable {F : X.Modules}

/-- Equality of pulled-back Quot kernels on one member of a base open cover gives
equality of the literal restrictions of the two global kernel ranges on the
corresponding member of the induced total-space cover. -/
lemma restrictedKernelData_eq_of_pullbackKernelData_eq
    (x y : QuotientPullbackData F f T) (i : COV.I₀)
    (h : (x.pullback (openCoverMapOver T COV i)).kernelData =
      (y.pullback (openCoverMapOver T COV i)).kernelData) :
    PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor
          ((Over.pullback f).map (openCoverMapOver T COV i)).left).map
            (kernel.ι x.π)).val =
      PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor
          ((Over.pullback f).map (openCoverMapOver T COV i)).left).map
            (kernel.ι y.π)).val := by
  rw [← kernelData_restrictPullback_eq_pullback,
    ← kernelData_restrictPullback_eq_pullback] at h
  let e := (SheafOfModules.forget
    ((Over.pullback f).obj (openCoverObjectOver T COV i)).left.ringCatSheaf).mapIso
      (normalizedAmbientIso (F := F) T (openCoverMapOver T COV i))
  calc
    _ = (restrictPullback T (openCoverMapOver T COV i) x).kernelData.mapIso e :=
      (kernelData_restrictPullback_mapIso T
        (openCoverMapOver T COV i) x).symm
    _ = (restrictPullback T (openCoverMapOver T COV i) y).kernelData.mapIso e :=
      congrArg (fun N ↦ N.mapIso e) h
    _ = _ := kernelData_restrictPullback_mapIso T
      (openCoverMapOver T COV i) y

/-- A global Quot kernel is determined by its pullbacks to an open cover of the
test scheme.  The proof uses the induced open cover of the total fiber product. -/
lemma kernelData_eq_of_openCover_pullbackKernelData_eq
    (x y : QuotientPullbackData F f T)
    (h : ∀ i, (x.pullback (openCoverMapOver T COV i)).kernelData =
      (y.pullback (openCoverMapOver T COV i)).kernelData) :
    x.kernelData = y.kernelData := by
  exact Modules.range_eq_of_openCover_restrict_range_eq
    (quotientTotalOpenCover f T COV)
    ((Modules.pullback ((Over.pullback f).obj T).hom).obj F)
    (kernel x.π) (kernel y.π) (kernel.ι x.π) (kernel.ι y.π)
    (fun i ↦ restrictedKernelData_eq_of_pullbackKernelData_eq
      f T COV x y i (h i))

end Modules.QuotientPullbackData

/-- Two points of the Quot functor which agree after restriction to every member
of an open cover are equal.  This is the separatedness half of Zariski descent. -/
lemma quotFunctor_eq_of_openCover_restrict {F : X.Modules}
    (z z' : (quotFunctor F f).obj (Opposite.op T))
    (h : ∀ i, (quotFunctor F f).map (openCoverMapOver T COV i).op z =
      (quotFunctor F f).map (openCoverMapOver T COV i).op z') :
    z = z' := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨y, rfl⟩ := Quotient.exists_rep z'
  apply Quotient.sound
  apply Modules.QuotientPullbackData.r_of_kernelData_eq
  apply Modules.QuotientPullbackData.kernelData_eq_of_openCover_pullbackKernelData_eq
    f T COV x y
  intro i
  exact Modules.QuotientPullbackData.kernelData_eq_of_r (Quotient.exact (h i))

namespace Modules.QuotientOpenDescent

/-- The arrows of an open cover, regarded in the slice, generate a
Zariski-covering sieve. -/
lemma openCoverMapOver_mem_zariskiTopology :
    Sieve.ofArrows (fun i : COV.I₀ ↦ openCoverObjectOver T COV i)
      (fun i ↦ openCoverMapOver T COV i) ∈ Scheme.zariskiTopology.over S T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.zariskiTopology.superset_covering ?_
    COV.mem_grothendieckTopology
  rw [Sieve.generate_le_iff]
  rintro W g ⟨i⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨openCoverObjectOver T COV i, Over.homMk (𝟙 _) rfl,
    openCoverMapOver T COV i, ⟨i⟩, by ext; rfl⟩

/-- The arrows of an open cover, regarded in the slice, also generate an
étale-covering sieve. -/
lemma openCoverMapOver_mem_etaleTopology :
    Sieve.ofArrows (fun i : COV.I₀ ↦ openCoverObjectOver T COV i)
      (fun i ↦ openCoverMapOver T COV i) ∈ Scheme.etaleTopology.over S T := by
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.zariskiTopology_le_etaleTopology
  rw [← GrothendieckTopology.mem_over_iff]
  exact openCoverMapOver_mem_zariskiTopology T COV

/-- The underlying component of the descent image of a family morphism is its
concrete pullback. -/
lemma familyModulesToDescentData_map_hom
    {M N : (familyModulesPseudofunctor (Over.mk f)).obj
      (.mk (Opposite.op T))} (k : M ⟶ N) (i : COV.I₀) :
    ((((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).map k).hom i).hom =
      (Modules.pullback ((Over.pullback f).map
        (openCoverMapOver T COV i)).left).map k.hom := by
  rfl

/-- Pulling back a morphism of quasicoherent families has the expected underlying
module morphism. -/
lemma familyModulesMap_hom {T' : Over S} (g : T' ⟶ T)
    {M N : (familyModulesPseudofunctor (Over.mk f)).obj
      (.mk (Opposite.op T))} (k : M ⟶ N) :
    (((familyModulesPseudofunctor (Over.mk f)).map g.op.toLoc).toFunctor.map
      k).hom =
      (Modules.pullback ((Over.pullback f).map g).left).map k.hom := by
  rfl

/-- The family-scheme functor sends a slice morphism to the underlying morphism
of its base change. -/
lemma familySchemeFunctor_map_eq {T' : Over S} (g : T' ⟶ T) :
    (familySchemeFunctor (Over.mk f)).map g =
      ((Over.pullback f).map g).left :=
  rfl

/-- The underlying module map of `pullHom` for the quasicoherent-module
pseudofunctor, including transport when the displayed composite arrows are only
propositionally equal. -/
lemma quasicoherentPullHom_hom {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ : (Scheme.Modules.isQuasicoherentProperty.prop (.mk (.op X₁))).FullSubcategory}
    {M₂ : (Scheme.Modules.isQuasicoherentProperty.prop (.mk (.op X₂))).FullSubcategory}
    (a : Y ⟶ X₁) (b : Y ⟶ X₂)
    (φ : (quasicoherentPseudofunctor.map a.op.toLoc).toFunctor.obj M₁ ⟶
      (quasicoherentPseudofunctor.map b.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (ga : Y' ⟶ X₁) (gb : Y' ⟶ X₂)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := quasicoherentPseudofunctor) φ g ga gb hga hgb).hom =
      (Modules.pullbackCongr hga.symm).hom.app M₁.obj ≫
        (Modules.pullbackComp g a).inv.app M₁.obj ≫
        (Modules.pullback g).map φ.hom ≫
        (Modules.pullbackComp g b).hom.app M₂.obj ≫
        (Modules.pullbackCongr hgb.symm).inv.app M₂.obj := by
  dsimp only [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  change
    (pseudofunctorToCat.mapComp' a.op.toLoc g.op.toLoc ga.op.toLoc
        (Hom.schemeOpCompEq g a ga hga)).hom.toNatTrans.app M₁.obj ≫
      (Modules.pullback g).map φ.hom ≫
      (pseudofunctorToCat.mapComp' b.op.toLoc g.op.toLoc gb.op.toLoc
        (Hom.schemeOpCompEq g b gb hgb)).inv.toNatTrans.app M₂.obj = _
  rw [Hom.pseudofunctorToCat_mapComp'_hom_app,
    Hom.pseudofunctorToCat_mapComp'_inv_app]
  · simp only [Category.assoc]
  · exact hgb
  · exact hga

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 3000000 in
-- Comparing flexible pseudofunctor compositors with concrete pullbacks is expensive.
/-- The transition in the canonical descent datum of a module is the concrete
comparison between the two iterated pullbacks. -/
lemma moduleObject_descent_hom
    {I : Type u} {B Y : Scheme.{u}} {U : I → Scheme.{u}}
    (p : ∀ i, U i ⟶ B) (q : Y ⟶ B)
    (i₁ i₂ : I) (a : Y ⟶ U i₁) (b : Y ⟶ U i₂)
    (ha : a ≫ p i₁ = q) (hb : b ≫ p i₂ = q)
    (M : B.Modules) :
    (((Scheme.Modules.pseudofunctorToCat.toDescentData p).obj M).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb) =
      (Scheme.Modules.Hom.pullbackCompCongrIso a (p i₁) b (p i₂)
        (ha.trans hb.symm) M).hom := by
  dsimp only [CategoryTheory.Pseudofunctor.toDescentData,
    CategoryTheory.Pseudofunctor.DescentData.ofObj]
  rw [Scheme.Modules.Hom.pseudofunctorToCat_mapComp'_inv_app a (p i₁) q ha,
    Scheme.Modules.Hom.pseudofunctorToCat_mapComp'_hom_app b (p i₂) q hb]
  dsimp only [Scheme.Modules.Hom.pullbackCompCongrIso, Iso.trans_hom]
  change
    ((Modules.pullbackComp a (p i₁)).hom.app M ≫
        (Modules.pullbackCongr ha.symm).inv.app M) ≫
      ((Modules.pullbackCongr hb.symm).hom.app M ≫
        (Modules.pullbackComp b (p i₂)).inv.app M) =
      (Modules.pullbackComp a (p i₁)).hom.app M ≫
        (Modules.pullbackCongr (ha.trans hb.symm)).hom.app M ≫
          (Modules.pullbackComp b (p i₂)).inv.app M
  have hcongr :
      (Modules.pullbackCongr ha.symm).inv.app M ≫
          (Modules.pullbackCongr hb.symm).hom.app M =
        (Modules.pullbackCongr (ha.trans hb.symm)).hom.app M := by
    dsimp only [Modules.pullbackCongr]
    simp only [eqToIso.inv, eqToIso.hom, eqToHom_app, eqToHom_trans]
  simp only [Category.assoc]
  rw [reassoc_of% hcongr]

set_option maxHeartbeats 1000000 in
-- Forgetting quasicoherence through the full-subcategory compositor is expensive.
/-- The preceding canonical transition formula after bundling quasicoherence. -/
lemma quasicoherentObject_descent_hom_hom
    {I : Type u} {B Y : Scheme.{u}} {U : I → Scheme.{u}}
    (p : ∀ i, U i ⟶ B) (q : Y ⟶ B)
    (i₁ i₂ : I) (a : Y ⟶ U i₁) (b : Y ⟶ U i₂)
    (ha : a ≫ p i₁ = q) (hb : b ≫ p i₂ = q)
    (M : (Scheme.Modules.isQuasicoherentProperty.prop
      (.mk (.op B))).FullSubcategory) :
    (((Scheme.Modules.quasicoherentPseudofunctor.toDescentData p).obj M).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom =
      (Scheme.Modules.Hom.pullbackCompCongrIso a (p i₁) b (p i₂)
        (ha.trans hb.symm) M.obj).hom := by
  change (((Scheme.Modules.pseudofunctorToCat.toDescentData p).obj M.obj).hom
    (i₁ := i₁) (i₂ := i₂) q a b ha hb) = _
  exact moduleObject_descent_hom p q i₁ i₂ a b ha hb M.obj

set_option maxHeartbeats 1000000 in
/-- The underlying canonical transition after precomposing the
quasicoherent-module pseudofunctor by a functor to schemes.  Keeping the
precomposition functor abstract avoids expanding large concrete base-change
functors when this coherence formula is specialized. -/
lemma compQuasicoherent_descent_hom_hom
    {C : Type (u + 1)} [Category.{u} C]
    (H : CategoryTheory.Functor C Scheme.{u})
    {I : Type u} {B Y : C} {U : I → C}
    (p : ∀ i, U i ⟶ B) (q : Y ⟶ B)
    (i₁ i₂ : I) (a : Y ⟶ U i₁) (b : Y ⟶ U i₂)
    (ha : a ≫ p i₁ = q) (hb : b ≫ p i₂ = q)
    (M : (Scheme.Modules.isQuasicoherentProperty.prop
      (.mk (.op (H.obj B)))).FullSubcategory) :
    ((((CategoryTheory.Pseudofunctor.comp H.op.toPseudofunctor
      quasicoherentPseudofunctor).toDescentData p).obj M).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom =
      (Scheme.Modules.Hom.pullbackCompCongrIso
        (H.map a) (H.map (p i₁)) (H.map b) (H.map (p i₂))
        (((by rw [← H.map_comp, ha]) :
            H.map a ≫ H.map (p i₁) = H.map q).trans
          ((by rw [← H.map_comp, hb]) :
            H.map b ≫ H.map (p i₂) = H.map q).symm)
        M.obj).hom := by
  rw [CategoryTheory.Pseudofunctor.comp_toDescentData_obj_hom H
    quasicoherentPseudofunctor p q i₁ i₂ a b ha hb M]
  exact quasicoherentObject_descent_hom_hom
    (fun i ↦ H.map (p i)) (H.map q) i₁ i₂
    (H.map a) (H.map b)
    (by rw [← H.map_comp, ha]) (by rw [← H.map_comp, hb]) M

/-- The two concrete presentations of the canonical pullback transition from a
module on the base agree after inserting the pullback-comparison isomorphisms. -/
lemma pullbackComparison_comp_pullbackCompCongrIso
    {B : Scheme.{u}} (V : B.Modules) {T U₁ U₂ Y : Over B}
    (u₁ : U₁ ⟶ T) (u₂ : U₂ ⟶ T) (a : Y ⟶ U₁) (b : Y ⟶ U₂)
    (q : Y ⟶ T) (ha : a ≫ u₁ = q) (hb : b ≫ u₂ = q) :
    ((PullbackQuotient.pullbackComparison V a).hom ≫
      (Modules.pullback a.left).map
        (PullbackQuotient.pullbackComparison V u₁).hom) ≫
        (Scheme.Modules.Hom.pullbackCompCongrIso a.left u₁.left b.left u₂.left
          (congrArg (fun k : Y ⟶ T ↦ k.left) (ha.trans hb.symm))
          ((Modules.pullback T.hom).obj V)).hom =
      (PullbackQuotient.pullbackComparison V b).hom ≫
        (Modules.pullback b.left).map
          (PullbackQuotient.pullbackComparison V u₂).hom := by
  have hi := PullbackQuotient.comparison_eq_comp_coherence V u₁ a ha
  have hj := PullbackQuotient.comparison_eq_comp_coherence V u₂ b hb
  have htransport :
      ((Modules.pullbackCongr
        ((congrArg (fun k : Y ⟶ T ↦ k.left) ha).symm)).app
          ((Modules.pullback T.hom).obj V)).hom ≫
        ((Modules.pullbackCongr
          (congrArg (fun k : Y ⟶ T ↦ k.left)
            (ha.trans hb.symm))).app
            ((Modules.pullback T.hom).obj V)).hom =
      ((Modules.pullbackCongr
        ((congrArg (fun k : Y ⟶ T ↦ k.left) hb).symm)).app
          ((Modules.pullback T.hom).obj V)).hom := by
    change
      (Modules.pullbackCongr
        ((congrArg (fun k : Y ⟶ T ↦ k.left) ha).symm)).hom.app
          ((Modules.pullback T.hom).obj V) ≫
        (Modules.pullbackCongr
          (congrArg (fun k : Y ⟶ T ↦ k.left)
            (ha.trans hb.symm))).hom.app
              ((Modules.pullback T.hom).obj V) =
      (Modules.pullbackCongr
        ((congrArg (fun k : Y ⟶ T ↦ k.left) hb).symm)).hom.app
          ((Modules.pullback T.hom).obj V)
    dsimp only [Modules.pullbackCongr]
    simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
  dsimp only [Scheme.Modules.Hom.pullbackCompCongrIso,
    Iso.trans_hom, Iso.symm_hom]
  change (PullbackQuotient.pullbackComparison V a).hom ≫
      (Modules.pullback a.left).map
        (PullbackQuotient.pullbackComparison V u₁).hom ≫
      (Modules.pullbackComp a.left u₁.left).hom.app
        ((Modules.pullback T.hom).obj V) ≫
      ((Modules.pullbackCongr
        (congrArg (fun k : Y ⟶ T ↦ k.left)
          (ha.trans hb.symm))).app
            ((Modules.pullback T.hom).obj V)).hom ≫
      (Modules.pullbackComp b.left u₂.left).inv.app
        ((Modules.pullback T.hom).obj V) =
    (PullbackQuotient.pullbackComparison V b).hom ≫
      (Modules.pullback b.left).map
        (PullbackQuotient.pullbackComparison V u₂).hom
  have hfirst := congrArg
    (fun k ↦ k ≫
      ((Modules.pullbackCongr
        (congrArg (fun k : Y ⟶ T ↦ k.left)
          (ha.trans hb.symm))).app
            ((Modules.pullback T.hom).obj V)).hom ≫
      (Modules.pullbackComp b.left u₂.left).inv.app
        ((Modules.pullback T.hom).obj V)) hi
  have hlast := congrArg
    (fun k ↦ k ≫
      (Modules.pullbackComp b.left u₂.left).inv.app
        ((Modules.pullback T.hom).obj V)) hj.symm
  calc
    _ = (((PullbackQuotient.pullbackComparison V q).hom ≫
          ((Modules.pullbackCongr
            ((congrArg (fun k : Y ⟶ T ↦ k.left) ha).symm)).app
              ((Modules.pullback T.hom).obj V)).hom) ≫
        ((Modules.pullbackCongr
          (congrArg (fun k : Y ⟶ T ↦ k.left)
            (ha.trans hb.symm))).app
              ((Modules.pullback T.hom).obj V)).hom) ≫
        (Modules.pullbackComp b.left u₂.left).inv.app
          ((Modules.pullback T.hom).obj V) := by
            simpa only [Category.assoc] using hfirst
    _ = ((PullbackQuotient.pullbackComparison V q).hom ≫
          ((Modules.pullbackCongr
            ((congrArg (fun k : Y ⟶ T ↦ k.left) hb).symm)).app
              ((Modules.pullback T.hom).obj V)).hom) ≫
        (Modules.pullbackComp b.left u₂.left).inv.app
          ((Modules.pullback T.hom).obj V) := by
            simpa only [Category.assoc] using congrArg
              (fun k ↦ (PullbackQuotient.pullbackComparison V q).hom ≫
                k ≫ (Modules.pullbackComp b.left u₂.left).inv.app
                  ((Modules.pullback T.hom).obj V)) htransport
    _ = _ := by
      simpa [Category.assoc] using hlast

/-- Canonically normalizing the two local source sheaves converts compatibility
of quotient maps into compatibility with the canonical source descent
transition. -/
lemma normalizedQuotientMap_transition
    {B : Scheme.{u}} (V : B.Modules) {T U₁ U₂ Y : Over B}
    (u₁ : U₁ ⟶ T) (u₂ : U₂ ⟶ T) (a : Y ⟶ U₁) (b : Y ⟶ U₂)
    (q : Y ⟶ T) (ha : a ≫ u₁ = q) (hb : b ≫ u₂ = q)
    {Q₁ : U₁.left.Modules} {Q₂ : U₂.left.Modules}
    (π₁ : (Modules.pullback U₁.hom).obj V ⟶ Q₁)
    (π₂ : (Modules.pullback U₂.hom).obj V ⟶ Q₂)
    (e : (Modules.pullback a.left).obj Q₁ ⟶
      (Modules.pullback b.left).obj Q₂)
    (he : ((PullbackQuotient.pullbackComparison V a).hom ≫
          (Modules.pullback a.left).map π₁) ≫ e =
        (PullbackQuotient.pullbackComparison V b).hom ≫
          (Modules.pullback b.left).map π₂) :
    (Modules.pullback a.left).map
          ((PullbackQuotient.pullbackComparison V u₁).inv ≫ π₁) ≫ e =
      (Scheme.Modules.Hom.pullbackCompCongrIso a.left u₁.left b.left u₂.left
        (congrArg (fun k : Y ⟶ T ↦ k.left) (ha.trans hb.symm))
        ((Modules.pullback T.hom).obj V)).hom ≫
        (Modules.pullback b.left).map
          ((PullbackQuotient.pullbackComparison V u₂).inv ≫ π₂) := by
  let A := (PullbackQuotient.pullbackComparison V a).hom ≫
    (Modules.pullback a.left).map
      (PullbackQuotient.pullbackComparison V u₁).hom
  haveI : Epi A := by
    dsimp only [A]
    infer_instance
  rw [← cancel_epi A]
  dsimp only [A]
  simp only [Functor.map_comp, Category.assoc]
  have hcancel₁ :
      (Modules.pullback a.left).map
          (PullbackQuotient.pullbackComparison V u₁).hom ≫
        (Modules.pullback a.left).map
          (PullbackQuotient.pullbackComparison V u₁).inv = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  have hcancel₂ :
      (Modules.pullback b.left).map
          (PullbackQuotient.pullbackComparison V u₂).hom ≫
        (Modules.pullback b.left).map
          (PullbackQuotient.pullbackComparison V u₂).inv = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  have he' := he
  simp only [Category.assoc] at he'
  have hsource :=
    pullbackComparison_comp_pullbackCompCongrIso V u₁ u₂ a b q ha hb
  simp only [Category.assoc] at hsource
  rw [reassoc_of% hcancel₁, he', reassoc_of% hsource,
    reassoc_of% hcancel₂]

variable {F : X.Modules}
variable
  (z : ∀ i, (quotFunctor F f).obj
    (Opposite.op (openCoverObjectOver T COV i)))
  (hz : Presieve.Arrows.Compatible (quotFunctor F f)
    (fun i ↦ openCoverMapOver T COV i) z)
  (x : ∀ i, QuotientPullbackData F f (openCoverObjectOver T COV i))
  (hx : ∀ i, Quotient.mk'' (x i) = z i)

include z hz hx

/-- The global source sheaf, bundled as a quasicoherent family. -/
noncomputable def ambientSourceQC [F.IsQuasicoherent] :
    (familyModulesPseudofunctor (Over.mk f)).obj (.mk (Opposite.op T)) :=
  ⟨(Modules.pullback ((Over.pullback f).obj T).hom).obj F,
    Scheme.Modules.isQuasicoherent_pullback _ F⟩

/-- Compatibility of local Quot classes gives compatible quotient presentations
after pullback along any two arrows with the same composite to the covered test
scheme. -/
lemma pullback_relation {Y : Over S} (q : Y ⟶ T) (i j : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i)
    (b : Y ⟶ openCoverObjectOver T COV j)
    (ha : a ≫ openCoverMapOver T COV i = q)
    (hb : b ≫ openCoverMapOver T COV j = q) :
    (QuotientPullbackData.setoid F f Y).r
      ((x i).pullback a) ((x j).pullback b) := by
  apply Quotient.exact
  have h := hz i j Y a b (ha.trans hb.symm)
  rw [← hx i, ← hx j] at h
  exact h

/-- A chosen quotient-sheaf comparison on an arbitrary overlap. -/
noncomputable def pullbackIso {Y : Over S} (q : Y ⟶ T) (i j : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i)
    (b : Y ⟶ openCoverObjectOver T COV j)
    (ha : a ≫ openCoverMapOver T COV i = q)
    (hb : b ≫ openCoverMapOver T COV j = q) :
    ((x i).pullback a).Q ≅ ((x j).pullback b).Q :=
  (pullback_relation f T COV z hz x hx q i j a b ha hb).choose

/-- The chosen overlap comparison carries the first pulled-back quotient map to
the second. -/
lemma π_comp_pullbackIso_hom {Y : Over S} (q : Y ⟶ T) (i j : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i)
    (b : Y ⟶ openCoverObjectOver T COV j)
    (ha : a ≫ openCoverMapOver T COV i = q)
    (hb : b ≫ openCoverMapOver T COV j = q) :
    ((x i).pullback a).π ≫
        (pullbackIso f T COV z hz x hx q i j a b ha hb).hom =
      ((x j).pullback b).π :=
  (pullback_relation f T COV z hz x hx q i j a b ha hb).choose_spec

/-- A local quotient sheaf as an object of the quasicoherent-family
pseudofunctor. -/
noncomputable def localQuotientQC (i : COV.I₀) :
    (familyModulesPseudofunctor (Over.mk f)).obj
      (.mk (Opposite.op (openCoverObjectOver T COV i))) :=
  ⟨(x i).Q, (x i).isQuasicoherent⟩

/-- The chosen overlap comparison as a morphism of quasicoherent families. -/
noncomputable def pullbackQCHom {Y : Over S} (q : Y ⟶ T)
    (i j : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i)
    (b : Y ⟶ openCoverObjectOver T COV j)
    (ha : a ≫ openCoverMapOver T COV i = q)
    (hb : b ≫ openCoverMapOver T COV j = q) :
    ((familyModulesPseudofunctor (Over.mk f)).map a.op.toLoc).toFunctor.obj
        (localQuotientQC f T COV x i) ⟶
      ((familyModulesPseudofunctor (Over.mk f)).map b.op.toLoc).toFunctor.obj
        (localQuotientQC f T COV x j) :=
  CategoryTheory.ObjectProperty.homMk
    (pullbackIso f T COV z hz x hx q i j a b ha hb).hom

/-- The concrete comparison from an iterated pullback of a local quotient sheaf
to its pullback along the composite arrow. -/
noncomputable def pullbackCompositionIso {Y Y' : Over S} (i : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i) (g : Y' ⟶ Y) :
    (((x i).pullback a).pullback g).Q ≅ ((x i).pullback (g ≫ a)).Q :=
  (Modules.pullbackComp (CommaMorphism.left ((Over.pullback f).map g))
      (CommaMorphism.left ((Over.pullback f).map a))).app (x i).Q ≪≫
    ((Modules.pullbackCongr ((congrArg CommaMorphism.left
      (((Over.pullback f).map_comp g a).symm :
        (Over.pullback f).map g ≫ (Over.pullback f).map a =
          (Over.pullback f).map (g ≫ a))).symm :
      CommaMorphism.left ((Over.pullback f).map (g ≫ a)) =
        CommaMorphism.left ((Over.pullback f).map g) ≫
          CommaMorphism.left ((Over.pullback f).map a))).app (x i).Q).symm

/-- The composite-pullback comparison carries the iterated quotient projection
to the quotient projection pulled back along the composite. -/
lemma π_comp_pullbackCompositionIso_hom {Y Y' : Over S} (i : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i) (g : Y' ⟶ Y) :
    (((x i).pullback a).pullback g).π ≫
        (pullbackCompositionIso f T COV x i a g).hom =
      ((x i).pullback (g ≫ a)).π := by
  exact PullbackQuotient.comparison_pullback_comp F
    ((Over.pullback f).map a) ((Over.pullback f).map g)
    (((Over.pullback f).map_comp g a).symm) ((x i).π)

set_option maxHeartbeats 1000000 in
/-- The canonical descent datum on the local quotient sheaves. -/
noncomputable def quotientDescentData :
    (familyModulesPseudofunctor (Over.mk f)).DescentData
      (fun i ↦ openCoverMapOver T COV i) where
  obj i := localQuotientQC f T COV x i
  hom Y q i₁ i₂ a b ha hb :=
    pullbackQCHom f T COV z hz x hx q i₁ i₂ a b ha hb
  pullHom_hom Y' Y g q q' hq i₁ i₂ a b ha hb ga gb hga hgb := by
    subst ga
    subst gb
    have hpre := CategoryTheory.Pseudofunctor.comp_pullHom_eq
      (familySchemeFunctor (Over.mk f)) quasicoherentPseudofunctor
      a b g (g ≫ a) (g ≫ b) rfl rfl
      (localQuotientQC f T COV x i₁) (localQuotientQC f T COV x i₂)
      (pullbackQCHom f T COV z hz x hx q i₁ i₂ a b ha hb)
    rw [hpre]
    apply CategoryTheory.ObjectProperty.hom_ext
    letI : Epi ((x i₁).pullback (g ≫ a)).π :=
      ((x i₁).pullback (g ≫ a)).epi
    rw [← cancel_epi ((x i₁).pullback (g ≫ a)).π]
    rw [quasicoherentPullHom_hom]
    change ((x i₁).pullback (g ≫ a)).π ≫
        (pullbackCompositionIso f T COV x i₁ a g).inv ≫
        (Modules.pullback ((Over.pullback f).map g).left).map
          (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom ≫
        (pullbackCompositionIso f T COV x i₂ b g).hom = _
    have hleft : ((x i₁).pullback (g ≫ a)).π ≫
        (pullbackCompositionIso f T COV x i₁ a g).inv =
        (((x i₁).pullback a).pullback g).π := by
      rw [← π_comp_pullbackCompositionIso_hom
        f T COV z hz x hx i₁ a g]
      simp
    rw [reassoc_of% hleft]
    change (((x i₁).pullback a).pullback g).π ≫
        (Modules.pullback ((Over.pullback f).map g).left).map
          (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom ≫
        (pullbackCompositionIso f T COV x i₂ b g).hom = _
    have hmid : (((x i₁).pullback a).pullback g).π ≫
        (Modules.pullback ((Over.pullback f).map g).left).map
          (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom =
        (((x i₂).pullback b).pullback g).π := by
      have hm := congrArg
        (fun k ↦ (Modules.pullback ((Over.pullback f).map g).left).map k)
        (π_comp_pullbackIso_hom f T COV z hz x hx q i₁ i₂ a b ha hb)
      rw [Functor.map_comp] at hm
      change (PullbackQuotient.pullbackComparison F
          ((Over.pullback f).map g)).hom ≫
          (Modules.pullback ((Over.pullback f).map g).left).map
            ((x i₁).pullback a).π ≫
          (Modules.pullback ((Over.pullback f).map g).left).map
            (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom =
        (PullbackQuotient.pullbackComparison F
          ((Over.pullback f).map g)).hom ≫
          (Modules.pullback ((Over.pullback f).map g).left).map
            ((x i₂).pullback b).π
      rw [hm]
    rw [reassoc_of% hmid,
      π_comp_pullbackCompositionIso_hom f T COV z hz x hx i₂ b g]
    exact (π_comp_pullbackIso_hom f T COV z hz x hx q' i₁ i₂
      (g ≫ a) (g ≫ b) (by rw [Category.assoc, ha, hq])
      (by rw [Category.assoc, hb, hq])).symm
  hom_self Y q i a ha := by
    apply CategoryTheory.ObjectProperty.hom_ext
    letI : Epi ((x i).pullback a).π := ((x i).pullback a).epi
    rw [← cancel_epi ((x i).pullback a).π]
    change ((x i).pullback a).π ≫
        (pullbackIso f T COV z hz x hx q i i a a ha ha).hom =
      ((x i).pullback a).π ≫ 𝟙 _
    rw [π_comp_pullbackIso_hom, Category.comp_id]
  hom_comp Y q i₁ i₂ i₃ a b c ha hb hc := by
    apply CategoryTheory.ObjectProperty.hom_ext
    letI : Epi ((x i₁).pullback a).π := ((x i₁).pullback a).epi
    rw [← cancel_epi ((x i₁).pullback a).π]
    change ((x i₁).pullback a).π ≫
          (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom ≫
          (pullbackIso f T COV z hz x hx q i₂ i₃ b c hb hc).hom =
        ((x i₁).pullback a).π ≫
          (pullbackIso f T COV z hz x hx q i₁ i₃ a c ha hc).hom
    rw [reassoc_of% π_comp_pullbackIso_hom,
      π_comp_pullbackIso_hom, π_comp_pullbackIso_hom]

/-- The underlying map of a transition in the quotient descent datum is its
chosen quotient-sheaf comparison. -/
lemma quotientDescentData_hom_hom {Y : Over S} (q : Y ⟶ T)
    (i₁ i₂ : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i₁)
    (b : Y ⟶ openCoverObjectOver T COV i₂)
    (ha : a ≫ openCoverMapOver T COV i₁ = q)
    (hb : b ≫ openCoverMapOver T COV i₂ = q) :
    ((quotientDescentData f T COV z hz x hx).hom
      (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom =
      (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom :=
  rfl

/-- A normalized local quotient map, viewed in the quasicoherent-family
category. -/
noncomputable def quotientDescentLocalMap [F.IsQuasicoherent]
    (i : COV.I₀) :
    (((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T)).obj i ⟶
      localQuotientQC f T COV x i :=
  CategoryTheory.ObjectProperty.homMk
    ((PullbackQuotient.pullbackComparison F
      ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π)

omit z hz hx in
/-- The underlying map of a normalized local quotient map. -/
lemma quotientDescentLocalMap_hom [F.IsQuasicoherent] (i : COV.I₀) :
    (quotientDescentLocalMap (F := F) (f := f) T COV x i).hom =
      (PullbackQuotient.pullbackComparison F
      ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π :=
  rfl

set_option maxHeartbeats 1000000 in
omit z hz hx in
/-- The canonical source transition for a quasicoherent family, expressed with
the family-scheme functor maps. -/
lemma ambientSourceQC_descent_hom_hom [F.IsQuasicoherent]
    {Y : Over S} (q : Y ⟶ T) (i₁ i₂ : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i₁)
    (b : Y ⟶ openCoverObjectOver T COV i₂)
    (ha : a ≫ openCoverMapOver T COV i₁ = q)
    (hb : b ≫ openCoverMapOver T COV i₂ = q) :
    ((((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T)).hom q a b ha hb).hom =
      (Scheme.Modules.Hom.pullbackCompCongrIso
        ((familySchemeFunctor (Over.mk f)).map a)
        ((familySchemeFunctor (Over.mk f)).map (openCoverMapOver T COV i₁))
        ((familySchemeFunctor (Over.mk f)).map b)
        ((familySchemeFunctor (Over.mk f)).map (openCoverMapOver T COV i₂))
        (((by rw [← Functor.map_comp, ha]) :
            (familySchemeFunctor (Over.mk f)).map a ≫
              (familySchemeFunctor (Over.mk f)).map
                (openCoverMapOver T COV i₁) =
                  (familySchemeFunctor (Over.mk f)).map q).trans
          ((by rw [← Functor.map_comp, hb]) :
            (familySchemeFunctor (Over.mk f)).map b ≫
              (familySchemeFunctor (Over.mk f)).map
                (openCoverMapOver T COV i₂) =
                  (familySchemeFunctor (Over.mk f)).map q).symm)
        (ambientSourceQC (F := F) (f := f) T).obj).hom := by
  exact compQuasicoherent_descent_hom_hom
    (familySchemeFunctor (Over.mk f))
    (fun i ↦ openCoverMapOver T COV i) q i₁ i₂ a b ha hb
    (ambientSourceQC (F := F) (f := f) T)

set_option maxHeartbeats 3000000 in
/-- The underlying sheaf maps in the normalized quotient family commute with
the canonical descent transitions. -/
lemma quotientDescentLocalMap_comm_hom [F.IsQuasicoherent]
    {Y : Over S} (q : Y ⟶ T) (i₁ i₂ : COV.I₀)
    (a : Y ⟶ openCoverObjectOver T COV i₁)
    (b : Y ⟶ openCoverObjectOver T COV i₂)
    (ha : a ≫ openCoverMapOver T COV i₁ = q)
    (hb : b ≫ openCoverMapOver T COV i₂ = q) :
    ((((familyModulesPseudofunctor (Over.mk f)).map a.op.toLoc).toFunctor.map
      (quotientDescentLocalMap (F := F) (f := f) T COV x i₁)).hom ≫
        ((quotientDescentData f T COV z hz x hx).hom q a b ha hb).hom) =
      ((((familyModulesPseudofunctor (Over.mk f)).toDescentData
        (fun i ↦ openCoverMapOver T COV i)).obj
          (ambientSourceQC (F := F) (f := f) T)).hom q a b ha hb).hom ≫
        (((familyModulesPseudofunctor (Over.mk f)).map b.op.toLoc).toFunctor.map
          (quotientDescentLocalMap (F := F) (f := f) T COV x i₂)).hom := by
    let l :=
      (((familyModulesPseudofunctor (Over.mk f)).map a.op.toLoc).toFunctor.map
        (quotientDescentLocalMap (F := F) (f := f) T COV x i₁))
    let t := (quotientDescentData f T COV z hz x hx).hom q a b ha hb
    let s :=
      (((familyModulesPseudofunctor (Over.mk f)).toDescentData
        (fun i ↦ openCoverMapOver T COV i)).obj
          (ambientSourceQC (F := F) (f := f) T)).hom q a b ha hb
    let r :=
      (((familyModulesPseudofunctor (Over.mk f)).map b.op.toLoc).toFunctor.map
        (quotientDescentLocalMap (F := F) (f := f) T COV x i₂))
    change l.hom ≫ t.hom = s.hom ≫ r.hom
    have hl : l.hom =
        (Modules.pullback ((Over.pullback f).map a).left).map
          ((PullbackQuotient.pullbackComparison F
            ((Over.pullback f).map (openCoverMapOver T COV i₁))).inv ≫
              (x i₁).π) := by
      dsimp only [l]
      rw [familyModulesMap_hom, quotientDescentLocalMap_hom]
    have hr : r.hom =
        (Modules.pullback ((Over.pullback f).map b).left).map
          ((PullbackQuotient.pullbackComparison F
            ((Over.pullback f).map (openCoverMapOver T COV i₂))).inv ≫
              (x i₂).π) := by
      dsimp only [r]
      rw [familyModulesMap_hom, quotientDescentLocalMap_hom]
    have ht : t.hom =
        (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom := by
      dsimp only [t]
      exact quotientDescentData_hom_hom
        (f := f) T COV z hz x hx q i₁ i₂ a b ha hb
    have hs := ambientSourceQC_descent_hom_hom
      (F := F) (f := f) T COV q i₁ i₂ a b ha hb
    rw [hl, ht, hr, hs]
    simp only [familySchemeFunctor_map_eq]
    let u₁ := (Over.pullback f).map (openCoverMapOver T COV i₁)
    let u₂ := (Over.pullback f).map (openCoverMapOver T COV i₂)
    let a' := (Over.pullback f).map a
    let b' := (Over.pullback f).map b
    let q' := (Over.pullback f).map q
    have ha' : a' ≫ u₁ = q' := by
      dsimp only [a', u₁, q']
      rw [← Functor.map_comp, ha]
    have hb' : b' ≫ u₂ = q' := by
      dsimp only [b', u₂, q']
      rw [← Functor.map_comp, hb]
    change (Modules.pullback a'.left).map
          ((PullbackQuotient.pullbackComparison F u₁).inv ≫ (x i₁).π) ≫
          (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom =
      (Scheme.Modules.Hom.pullbackCompCongrIso
        a'.left u₁.left b'.left u₂.left
        (congrArg CommaMorphism.left (ha'.trans hb'.symm))
        ((Modules.pullback ((Over.pullback f).obj T).hom).obj F)).hom ≫
        (Modules.pullback b'.left).map
          ((PullbackQuotient.pullbackComparison F u₂).inv ≫ (x i₂).π)
    exact normalizedQuotientMap_transition F u₁ u₂ a' b' q' ha' hb'
      (x i₁).π (x i₂).π
      (pullbackIso f T COV z hz x hx q i₁ i₂ a b ha hb).hom
      (π_comp_pullbackIso_hom f T COV z hz x hx q i₁ i₂ a b ha hb)

/-- The local quotient maps form a map from the canonical source descent datum. -/
noncomputable def quotientDescentMap [F.IsQuasicoherent] :
    ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
      quotientDescentData f T COV z hz x hx where
  hom i := quotientDescentLocalMap (F := F) (f := f) T COV x i
  comm Y q i₁ i₂ a b ha hb := by
    apply CategoryTheory.ObjectProperty.hom_ext
    exact quotientDescentLocalMap_comm_hom
      (F := F) (f := f) T COV z hz x hx q i₁ i₂ a b ha hb

/-- The component of the normalized source descent map is the prescribed local
quotient map. -/
lemma quotientDescentMap_hom [F.IsQuasicoherent] (i : COV.I₀) :
    ((quotientDescentMap (F := F) (f := f) T COV z hz x hx).hom i).hom =
      (PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π :=
  quotientDescentLocalMap_hom (F := F) (f := f) T COV x i

/-- A local Quot target, bundled with flatness and finite presentation as an
object of the coherent-family full subpseudofunctor. -/
noncomputable def localQuotientCoherent (i : COV.I₀) :
    (coherentFamilyProperty (Over.mk f)).Obj
      (.mk (Opposite.op (openCoverObjectOver T COV i))) :=
  ⟨localQuotientQC f T COV x i,
    ⟨(x i).flatOver, (x i).isFinitePresentation⟩⟩

/-- The quotient descent datum lifted to coherent flat quasicoherent families. -/
noncomputable def coherentQuotientDescentData :
    (coherentFamilyProperty (Over.mk f)).fullsubcategory.DescentData
      (fun i ↦ openCoverMapOver T COV i) :=
  CategoryTheory.Pseudofunctor.ObjectProperty.DescentData.lift
    (coherentFamilyProperty (Over.mk f))
    (fun i ↦ openCoverMapOver T COV i)
    (quotientDescentData f T COV z hz x hx)
    (fun i ↦ ⟨(x i).flatOver, (x i).isFinitePresentation⟩)

/-- The coherent local quotient descent datum is effective. -/
lemma coherentQuotientDescentData_effective :
    ∃ Q : (coherentFamilyProperty (Over.mk f)).Obj
        (.mk (Opposite.op T)),
      Nonempty
        (((coherentFamilyProperty (Over.mk f)).fullsubcategory.toDescentData
          (fun i ↦ openCoverMapOver T COV i)).obj Q ≅
            coherentQuotientDescentData f T COV z hz x hx) := by
  let _ : (familyModulesPseudofunctor (Over.mk f)).IsStack
      (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale (Over.mk f)
  let _ : (coherentFamilyProperty (Over.mk f)).fullsubcategory.IsStack
      (Scheme.etaleTopology.over S) :=
    (coherentFamilyProperty (Over.mk f)).fullsubcategory_isStack
  let D := coherentQuotientDescentData f T COV z hz x hx
  let E := (coherentFamilyProperty (Over.mk f)).fullsubcategory.toDescentData
    (fun i ↦ openCoverMapOver T COV i)
  let _ : E.IsEquivalence :=
    (coherentFamilyProperty (Over.mk f)).fullsubcategory.isEquivalence_toDescentData
      _ (openCoverMapOver_mem_etaleTopology T COV)
  exact ⟨E.objPreimage D, ⟨E.objObjPreimageIso D⟩⟩

/-- A chosen global coherent flat quotient target realizing the local descent
datum. -/
noncomputable def descendedCoherentQuotient :
    (coherentFamilyProperty (Over.mk f)).Obj (.mk (Opposite.op T)) :=
  (coherentQuotientDescentData_effective f T COV z hz x hx).choose

/-- The chosen global coherent target restricts to the prescribed coherent
descent datum. -/
noncomputable def descendedCoherentQuotientIso :
    ((coherentFamilyProperty (Over.mk f)).fullsubcategory.toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (descendedCoherentQuotient f T COV z hz x hx) ≅
      coherentQuotientDescentData f T COV z hz x hx :=
  (coherentQuotientDescentData_effective f T COV z hz x hx).choose_spec.some

/-- Forgetting the coherent-family property gives the corresponding
quasicoherent descent isomorphism. -/
noncomputable def descendedQuotientIso :
    ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (descendedCoherentQuotient f T COV z hz x hx).obj ≅
      quotientDescentData f T COV z hz x hx :=
  CategoryTheory.Pseudofunctor.ObjectProperty.DescentData.forgetIso
    (P := coherentFamilyProperty (Over.mk f))
    (fun i ↦ openCoverMapOver T COV i)
    (descendedCoherentQuotientIso f T COV z hz x hx)

/-- The underlying target-sheaf comparison on one member of the cover. -/
noncomputable def descendedQuotientIsoApp (i : COV.I₀) :
    (Modules.pullback ((Over.pullback f).map
      (openCoverMapOver T COV i)).left).obj
        (descendedCoherentQuotient f T COV z hz x hx).obj.obj ≅ (x i).Q :=
  (SheafOfModules.isQuasicoherent
    ((Over.pullback f).obj (openCoverObjectOver T COV i)).left.ringCatSheaf).ι.mapIso
      (CategoryTheory.Pseudofunctor.DescentData.isoApp
        (descendedQuotientIso f T COV z hz x hx) i)

/-- Descend a compatible map into the chosen quotient target. -/
noncomputable def descendMapToQuotient
    (M : (familyModulesPseudofunctor (Over.mk f)).obj (.mk (Opposite.op T)))
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj M ⟶
        quotientDescentData f T COV z hz x hx) :
    M ⟶ (descendedCoherentQuotient f T COV z hz x hx).obj := by
  let _ : (familyModulesPseudofunctor (Over.mk f)).IsStack
      (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale (Over.mk f)
  let E := (familyModulesPseudofunctor (Over.mk f)).toDescentData
    (fun i ↦ openCoverMapOver T COV i)
  let _ : E.IsEquivalence :=
    (familyModulesPseudofunctor (Over.mk f)).isEquivalence_toDescentData
      _ (openCoverMapOver_mem_etaleTopology T COV)
  exact E.preimage (m ≫ (descendedQuotientIso f T COV z hz x hx).inv)

/-- The descent image of `descendMapToQuotient` is the prescribed local map,
followed by the inverse target comparison. -/
lemma map_descendMapToQuotient
    (M : (familyModulesPseudofunctor (Over.mk f)).obj (.mk (Opposite.op T)))
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj M ⟶
        quotientDescentData f T COV z hz x hx) :
    ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).map
        (descendMapToQuotient f T COV z hz x hx M m) =
      m ≫ (descendedQuotientIso f T COV z hz x hx).inv := by
  let _ : (familyModulesPseudofunctor (Over.mk f)).IsStack
      (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale (Over.mk f)
  let E := (familyModulesPseudofunctor (Over.mk f)).toDescentData
    (fun i ↦ openCoverMapOver T COV i)
  let _ : E.IsEquivalence :=
    (familyModulesPseudofunctor (Over.mk f)).isEquivalence_toDescentData
      _ (openCoverMapOver_mem_etaleTopology T COV)
  exact E.map_preimage (m ≫ (descendedQuotientIso f T COV z hz x hx).inv)

/-- On a cover member, the pullback of a descended map is the prescribed local
map followed by the inverse target comparison. -/
lemma pullback_descendMapToQuotient_hom
    (M : (familyModulesPseudofunctor (Over.mk f)).obj (.mk (Opposite.op T)))
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj M ⟶
        quotientDescentData f T COV z hz x hx) (i : COV.I₀) :
    (Modules.pullback ((Over.pullback f).map
      (openCoverMapOver T COV i)).left).map
        (descendMapToQuotient f T COV z hz x hx M m).hom =
      (m.hom i).hom ≫ (descendedQuotientIsoApp f T COV z hz x hx i).inv := by
  have hmap := congrArg (fun k ↦ (k.hom i).hom)
    (map_descendMapToQuotient f T COV z hz x hx M m)
  rw [familyModulesToDescentData_map_hom] at hmap
  exact hmap

/-- If the prescribed local maps are epimorphisms, then their descended global
map is an epimorphism. -/
lemma descendMapToQuotient_epi
    (M : (familyModulesPseudofunctor (Over.mk f)).obj (.mk (Opposite.op T)))
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj M ⟶
        quotientDescentData f T COV z hz x hx)
    (hm : ∀ i, Epi (m.hom i).hom) :
    Epi (descendMapToQuotient f T COV z hz x hx M m).hom := by
  let _ : M.obj.IsQuasicoherent := M.property
  let _ : (descendedCoherentQuotient f T COV z hz x hx).obj.obj.IsQuasicoherent :=
    (descendedCoherentQuotient f T COV z hz x hx).obj.property
  apply Scheme.Modules.epi_of_openCover_restrict
    (descendMapToQuotient f T COV z hz x hx M m).hom
    (quotientTotalOpenCover f T COV)
  intro i
  change COV.I₀ at i
  let G := ((Over.pullback f).map (openCoverMapOver T COV i)).left
  let φ := descendMapToQuotient f T COV z hz x hx M m
  let e := descendedQuotientIso f T COV z hz x hx
  let eᵢ := CategoryTheory.Pseudofunctor.DescentData.isoApp e i
  let e₀ := (SheafOfModules.isQuasicoherent
    ((Over.pullback f).obj (openCoverObjectOver T COV i)).left.ringCatSheaf).ι.mapIso eᵢ
  have hmap := congrArg (fun k ↦ (k.hom i).hom)
    (map_descendMapToQuotient f T COV z hz x hx M m)
  have hpull : (Modules.pullback G).map φ.hom =
      (m.hom i).hom ≫ e₀.inv := by
    rw [familyModulesToDescentData_map_hom] at hmap
    exact hmap
  let _ : Epi (m.hom i).hom := hm i
  let _ : IsIso e₀.inv := e₀.isIso_inv
  let _ : Epi e₀.inv := CategoryTheory.IsIso.epi_of_iso e₀.inv
  let _ : Epi ((Modules.pullback G).map φ.hom) := by
    rw [hpull]
    exact epi_comp' (hm i) (CategoryTheory.IsIso.epi_of_iso e₀.inv)
  let R := Modules.restrictFunctor G
  let η := Modules.restrictFunctorIsoPullback G
  let ηM := η.app M.obj
  let ηQ := η.app (descendedCoherentQuotient f T COV z hz x hx).obj.obj
  have hη : R.map φ.hom ≫ ηQ.hom =
      ηM.hom ≫ (Modules.pullback G).map φ.hom :=
    η.hom.naturality φ.hom
  let _ : IsIso ηM.hom := ηM.isIso_hom
  let _ : IsIso ηQ.hom := ηQ.isIso_hom
  apply (epi_comp_iff_of_isIso (R.map φ.hom) ηQ.hom).mp
  rw [hη]
  infer_instance

/-- The global Quot datum associated with a descent-compatible family of local
quotient maps. -/
noncomputable def quotientPullbackDataOfDescentMap [F.IsQuasicoherent]
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
          quotientDescentData f T COV z hz x hx)
    (hm : ∀ i, Epi (m.hom i).hom) : QuotientPullbackData F f T where
  Q := (descendedCoherentQuotient f T COV z hz x hx).obj.obj
  isQuasicoherent :=
    (descendedCoherentQuotient f T COV z hz x hx).obj.property
  isFinitePresentation :=
    (descendedCoherentQuotient f T COV z hz x hx).property.2
  flatOver := (descendedCoherentQuotient f T COV z hz x hx).property.1
  π := (descendMapToQuotient f T COV z hz x hx
    (ambientSourceQC (F := F) (f := f) T) m).hom
  epi := descendMapToQuotient_epi f T COV z hz x hx
    (ambientSourceQC (F := F) (f := f) T) m hm

/-- The global Quot datum reconstructed from a normalized local source map
restricts to the prescribed local Quot datum. -/
lemma quotientPullbackDataOfDescentMap_pullback_r [F.IsQuasicoherent]
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
          quotientDescentData f T COV z hz x hx)
    (hm : ∀ i, Epi (m.hom i).hom)
    (hmcomp : ∀ i, (m.hom i).hom =
      (PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π)
    (i : COV.I₀) :
    (QuotientPullbackData.setoid F f (openCoverObjectOver T COV i)).r
      ((quotientPullbackDataOfDescentMap f T COV z hz x hx m hm).pullback
        (openCoverMapOver T COV i)) (x i) := by
  refine ⟨descendedQuotientIsoApp f T COV z hz x hx i, ?_⟩
  change (PullbackQuotient.pullbackComparison F
      ((Over.pullback f).map (openCoverMapOver T COV i))).hom ≫
      (Modules.pullback ((Over.pullback f).map
        (openCoverMapOver T COV i)).left).map
          (descendMapToQuotient f T COV z hz x hx
            (ambientSourceQC (F := F) (f := f) T) m).hom ≫
      (descendedQuotientIsoApp f T COV z hz x hx i).hom = (x i).π
  have hpull := pullback_descendMapToQuotient_hom f T COV z hz x hx
    (ambientSourceQC (F := F) (f := f) T) m i
  let c := PullbackQuotient.pullbackComparison F
    ((Over.pullback f).map (openCoverMapOver T COV i))
  let e := descendedQuotientIsoApp f T COV z hz x hx i
  change c.hom ≫
      (Modules.pullback ((Over.pullback f).map
        (openCoverMapOver T COV i)).left).map
          (descendMapToQuotient f T COV z hz x hx
            (ambientSourceQC (F := F) (f := f) T) m).hom ≫
      e.hom = (x i).π
  have hpull' : (Modules.pullback ((Over.pullback f).map
      (openCoverMapOver T COV i)).left).map
        (descendMapToQuotient f T COV z hz x hx
          (ambientSourceQC (F := F) (f := f) T) m).hom =
      (m.hom i).hom ≫ e.inv := hpull
  have h₁ := congrArg (fun k ↦ c.hom ≫ k ≫ e.hom) hpull'
  have hmcomp' : (m.hom i).hom = c.inv ≫ (x i).π := hmcomp i
  have h₂ := congrArg (fun k ↦ c.hom ≫ (k ≫ e.inv) ≫ e.hom) hmcomp'
  calc
    _ = c.hom ≫ ((m.hom i).hom ≫ e.inv) ≫ e.hom := h₁
    _ = c.hom ≫ ((c.inv ≫ (x i).π) ≫ e.inv) ≫ e.hom := h₂
    _ = (x i).π := by simp

/-- Normalized local source components are epimorphisms. -/
lemma normalizedDescentMap_components_epi [F.IsQuasicoherent]
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
          quotientDescentData f T COV z hz x hx)
    (hmcomp : ∀ i, (m.hom i).hom =
      (PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π) :
    ∀ i, Epi (m.hom i).hom := by
  intro i
  rw [hmcomp]
  let c := PullbackQuotient.pullbackComparison F
    ((Over.pullback f).map (openCoverMapOver T COV i))
  change Epi (c.inv ≫ (x i).π)
  let _ : IsIso c.inv := c.isIso_inv
  exact epi_comp' (CategoryTheory.IsIso.epi_of_iso c.inv) (x i).epi

/-- The Quot point obtained from a normalized descent-compatible family of
local quotient maps. -/
noncomputable def quotFunctorAmalgamationOfDescentMap [F.IsQuasicoherent]
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
          quotientDescentData f T COV z hz x hx)
    (hmcomp : ∀ i, (m.hom i).hom =
      (PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π) :
    (quotFunctor F f).obj (Opposite.op T) :=
  Quotient.mk'' (quotientPullbackDataOfDescentMap f T COV z hz x hx m
    (normalizedDescentMap_components_epi f T COV z hz x hx m hmcomp))

/-- The descended Quot point restricts to each prescribed member of the
compatible local family. -/
lemma quotFunctorAmalgamationOfDescentMap_restrict [F.IsQuasicoherent]
    (m : ((familyModulesPseudofunctor (Over.mk f)).toDescentData
      (fun i ↦ openCoverMapOver T COV i)).obj
        (ambientSourceQC (F := F) (f := f) T) ⟶
          quotientDescentData f T COV z hz x hx)
    (hmcomp : ∀ i, (m.hom i).hom =
      (PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map (openCoverMapOver T COV i))).inv ≫ (x i).π)
    (i : COV.I₀) :
    (quotFunctor F f).map (openCoverMapOver T COV i).op
      (quotFunctorAmalgamationOfDescentMap f T COV z hz x hx m hmcomp) = z i := by
  rw [← hx i]
  apply Quotient.sound
  exact quotientPullbackDataOfDescentMap_pullback_r f T COV z hz x hx m
    (normalizedDescentMap_components_epi f T COV z hz x hx m hmcomp) hmcomp i

/-- The Quot point obtained by descending the normalized quotient maps of a
compatible family. -/
noncomputable def quotFunctorAmalgamation [F.IsQuasicoherent] :
    (quotFunctor F f).obj (Opposite.op T) :=
  quotFunctorAmalgamationOfDescentMap f T COV z hz x hx
    (quotientDescentMap (F := F) (f := f) T COV z hz x hx)
    (quotientDescentMap_hom (F := F) (f := f) T COV z hz x hx)

/-- The descended Quot point restricts to each member of the original
compatible family. -/
lemma quotFunctorAmalgamation_restrict [F.IsQuasicoherent] (i : COV.I₀) :
    (quotFunctor F f).map (openCoverMapOver T COV i).op
      (quotFunctorAmalgamation (F := F) (f := f) T COV z hz x hx) = z i :=
  quotFunctorAmalgamationOfDescentMap_restrict f T COV z hz x hx
    (quotientDescentMap (F := F) (f := f) T COV z hz x hx)
    (quotientDescentMap_hom (F := F) (f := f) T COV z hz x hx) i

omit x hx in
/-- Every compatible family of Quot points on an ordinary open cover admits an
amalgamation. -/
lemma quotFunctor_openCover_effective [F.IsQuasicoherent] :
    ∃ t : (quotFunctor F f).obj (Opposite.op T),
      ∀ i, (quotFunctor F f).map (openCoverMapOver T COV i).op t = z i := by
  choose x hx using fun i ↦ Quotient.exists_rep (z i)
  exact ⟨quotFunctorAmalgamation (F := F) (f := f) T COV z hz x hx,
    quotFunctorAmalgamation_restrict f T COV z hz x hx⟩

omit z hz x hx in
/-- Effective descent on ordinary open covers implies the full relative Zariski
sheaf condition for the Quot functor. -/
theorem quotFunctor_isSheaf_of_openCover_effective
    (heffective : ∀ (T : Over S) (COV : Scheme.OpenCover.{u} T.left)
      (z : ∀ i, (quotFunctor F f).obj
        (Opposite.op (openCoverObjectOver T COV i))),
      Presieve.Arrows.Compatible (quotFunctor F f)
          (fun i ↦ openCoverMapOver T COV i) z →
        ∃ t : (quotFunctor F f).obj (Opposite.op T),
          ∀ i, (quotFunctor F f).map (openCoverMapOver T COV i).op t = z i) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (quotFunctor F f) := by
  rw [Scheme.zariskiTopology_eq]
  change Presieve.IsSheaf
    (((precoverage @IsOpenImmersion).toPretopology).toGrothendieck.over S)
      (quotFunctor F f)
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small
    (quotFunctor F f)).2
  intro T E
  rw [Presieve.isSheafFor_arrows_iff]
  intro z hz
  let COV : T.left.OpenCover := E.map (Over.forget S) le_rfl
  let c (i : E.I₀) : openCoverObjectOver T COV i ≅ E.X i :=
    Over.isoMk (Iso.refl _) (by
      change (E.X i).hom = (E.f i).left ≫ T.hom
      exact (Over.w (E.f i)).symm)
  let z' (i : COV.I₀) := (quotFunctor F f).map (c i).hom.op (z i)
  have hz' : Presieve.Arrows.Compatible (quotFunctor F f)
      (fun i ↦ openCoverMapOver T COV i) z' := by
    intro i j W gi gj hij
    have hci : (c i).hom ≫ E.f i = openCoverMapOver T COV i := by
      ext
      rfl
    have hcj : (c j).hom ≫ E.f j = openCoverMapOver T COV j := by
      ext
      rfl
    have h := hz i j W (gi ≫ (c i).hom) (gj ≫ (c j).hom) (by
      simp only [Category.assoc, hci, hcj, hij])
    simpa only [z', op_comp, Functor.map_comp, Function.comp_apply,
      ConcreteCategory.comp_apply] using h
  obtain ⟨t, ht⟩ := heffective T COV z' hz'
  refine ⟨t, ?_, ?_⟩
  · intro i
    have hti := ht i
    change (quotFunctor F f).map (E.f i).op t = z i
    apply injective_of_mono ((quotFunctor F f).map (c i).hom.op)
    have hci : (c i).hom ≫ E.f i = openCoverMapOver T COV i := by
      ext
      rfl
    simpa only [← Functor.map_comp_apply, ← op_comp, hci] using hti
  · intro t' ht'
    apply quotFunctor_eq_of_openCover_restrict f T COV t' t
    intro i
    have hi := ht' i
    have hti := ht i
    have h := (congrArg ((quotFunctor F f).map (c i).hom.op) hi).trans hti.symm
    simpa only [← Functor.map_comp_apply, ← op_comp, z', show
      (c i).hom ≫ E.f i = openCoverMapOver T COV i by ext; rfl] using h

omit z hz x hx in
/-- The Quot functor of a quasicoherent source is a sheaf for the relative
Zariski topology. -/
theorem isSheaf_quotFunctor [F.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (quotFunctor F f) :=
  quotFunctor_isSheaf_of_openCover_effective
    (F := F) (f := f) (fun T COV z hz ↦
      quotFunctor_openCover_effective f T COV z hz)

omit z hz x hx in
/-- The universe-small strict-kernel model of the Quot functor is a sheaf for
the relative Zariski topology. -/
theorem isSheaf_strictQuotFunctor [F.IsQuasicoherent] :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (strictQuotFunctor F f) :=
  (strictQuotFunctor_isSheaf_iff_quotFunctor_isSheaf F f).2
    (isSheaf_quotFunctor (F := F) (f := f))

end Modules.QuotientOpenDescent

end AlgebraicGeometry.Scheme

end
