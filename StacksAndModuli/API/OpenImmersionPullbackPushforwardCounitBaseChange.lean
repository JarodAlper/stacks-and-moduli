module

public import StacksAndModuli.API.AffineOpenGlobalSectionsBaseChange
public import StacksAndModuli.API.PushforwardProjectiveRank
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackageFromGeometry
public import StacksAndModuli.API.TwistedFreeQuotKernelGlobalGeneration

/-!
# Open restriction of pullback--pushforward evaluation maps

This file records the counit half of Beck--Chevalley for module sheaves in a
cartesian square with open horizontal maps.  The pullback and pushforward
comparisons already available in `OpenImmersionModuleBaseChange` combine to
identify the restriction of an evaluation map with the evaluation map after
base change.  In particular, epimorphicity of evaluation restricts to every
open subscheme of the base.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an open subscheme carries the kernel of a tensor map to
the kernel of the tensor map between the restricted factors. -/
noncomputable def restrictTensorMapLeftKernelIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {F F' : Y.Modules} (φ : F ⟶ F') (G : Y.Modules) :
    (restrictFunctor j).obj (kernel (tensorMapLeft φ G)) ≅
      kernel (tensorMapLeft ((restrictFunctor j).map φ)
        ((restrictFunctor j).obj G)) :=
  PreservesKernel.iso (restrictFunctor j) (tensorMapLeft φ G) ≪≫
    kernel.mapIso (f :=
      (restrictFunctor j).map (tensorMapLeft φ G))
      (tensorMapLeft ((restrictFunctor j).map φ)
        ((restrictFunctor j).obj G))
      (restrictTensorIso j F G) (restrictTensorIso j F' G)
      (restrictTensorIso_naturality_left j φ G)

/-- The canonical comparison from the restriction of a pullback--pushforward
object to the corresponding pullback--pushforward object on an open cartesian
square. -/
noncomputable def restrictPullbackPushforwardIsoOfOpenSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (M : W.Modules) :
    (restrictFunctor k).obj
        ((pullback i).obj ((pushforward i).obj M)) ≅
      (pullback g).obj
        ((pushforward g).obj ((restrictFunctor k).obj M)) :=
  (restrictPullbackIsoOfOpenSquare i g k j hsq).app
      ((pushforward i).obj M) ≪≫
    (pullback g).mapIso
      (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen M)

/-- Pullback--pushforward evaluation commutes with restriction through an open
cartesian square. -/
@[reassoc]
lemma restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (M : W.Modules) :
    (restrictPullbackPushforwardIsoOfOpenSquare
        i g k j hsq hopen M).hom ≫
      (pullbackPushforwardAdjunction g).counit.app
        ((restrictFunctor k).obj M) =
      (restrictFunctor k).map
        ((pullbackPushforwardAdjunction i).counit.app M) := by
  let N := (pushforward i).obj M
  let α := (restrictPullbackIsoOfOpenSquare i g k j hsq).app N
  let bc := restrictPushforwardIsoOfOpenSquare i g k j hsq hopen M
  change (α.hom ≫ (pullback g).map bc.hom) ≫
      (pullbackPushforwardAdjunction g).counit.app
        ((restrictFunctor k).obj M) =
    (restrictFunctor k).map
      ((pullbackPushforwardAdjunction i).counit.app M)
  rw [← cancel_epi α.inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ((pullbackPushforwardAdjunction g).homEquiv
    ((restrictFunctor j).obj N) ((restrictFunctor k).obj M)).injective
  have hcounit :
      (pullback g).map bc.hom ≫
          (pullbackPushforwardAdjunction g).counit.app
            ((restrictFunctor k).obj M) =
        (((pullbackPushforwardAdjunction g).homEquiv
          ((restrictFunctor j).obj N) ((restrictFunctor k).obj M)).symm
            bc.hom) :=
    ((pullbackPushforwardAdjunction g).homEquiv_counit
      ((restrictFunctor j).obj N) ((restrictFunctor k).obj M) bc.hom).symm
  rw [hcounit, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_apply]
  rw [← map_unit_restrictPushPullIsoOfOpenSquare'_hom
    i g k j hsq hopen N]
  simp only [restrictPushPullIsoOfOpenSquare', Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  dsimp only [α]
  rw [Iso.hom_inv_id_assoc]
  dsimp only [N]
  have hbc :
      (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen
          ((pullback i).obj ((pushforward i).obj M))).hom ≫
        (pushforward g).map ((restrictFunctor k).map
          ((pullbackPushforwardAdjunction i).counit.app M)) =
      (restrictFunctor j).map ((pushforward i).map
          ((pullbackPushforwardAdjunction i).counit.app M)) ≫ bc.hom := by
    exact (restrictPushforwardIsoOfOpenSquare_hom_naturality
      i g k j hsq hopen
        ((pullbackPushforwardAdjunction i).counit.app M)).symm
  rw [hbc]
  rw [← Functor.map_comp_assoc]
  rw [(pullbackPushforwardAdjunction i).right_triangle_components]
  simp

/-- An epimorphic pullback--pushforward evaluation map remains epimorphic after
restriction through an open cartesian square. -/
theorem epi_pullbackPushforwardCounit_of_openSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (M : W.Modules)
    [Epi ((pullbackPushforwardAdjunction i).counit.app M)] :
    Epi ((pullbackPushforwardAdjunction g).counit.app
      ((restrictFunctor k).obj M)) := by
  haveI : Epi ((restrictFunctor k).map
      ((pullbackPushforwardAdjunction i).counit.app M)) :=
    Functor.map_epi _ _
  have h := restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
    i g k j hsq hopen M
  haveI : Epi ((restrictPullbackPushforwardIsoOfOpenSquare
      i g k j hsq hopen M).hom ≫
        (pullbackPushforwardAdjunction g).counit.app
          ((restrictFunctor k).obj M)) := h ▸ inferInstance
  exact (epi_comp_iff_of_epi
    (restrictPullbackPushforwardIsoOfOpenSquare
      i g k j hsq hopen M).hom _).mp inferInstance

/-- On an open cartesian square, the local evaluation counit is epimorphic
exactly when the restriction of the global evaluation counit is epimorphic. -/
theorem epi_restrict_counit_iff_openSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (M : W.Modules) :
    Epi ((restrictFunctor k).map
        ((pullbackPushforwardAdjunction i).counit.app M)) ↔
      Epi ((pullbackPushforwardAdjunction g).counit.app
        ((restrictFunctor k).obj M)) := by
  constructor
  · intro h
    letI : Epi ((restrictFunctor k).map
        ((pullbackPushforwardAdjunction i).counit.app M)) := h
    have heq := restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
      i g k j hsq hopen M
    haveI : Epi ((restrictPullbackPushforwardIsoOfOpenSquare
        i g k j hsq hopen M).hom ≫
          (pullbackPushforwardAdjunction g).counit.app
            ((restrictFunctor k).obj M)) := heq ▸ inferInstance
    exact (epi_comp_iff_of_epi
      (restrictPullbackPushforwardIsoOfOpenSquare
        i g k j hsq hopen M).hom _).mp inferInstance
  · intro h
    letI : Epi ((pullbackPushforwardAdjunction g).counit.app
        ((restrictFunctor k).obj M)) := h
    have heq := restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
      i g k j hsq hopen M
    haveI : Epi ((restrictPullbackPushforwardIsoOfOpenSquare
        i g k j hsq hopen M).hom ≫
          (pullbackPushforwardAdjunction g).counit.app
            ((restrictFunctor k).obj M)) := epi_comp _ _
    exact heq ▸ inferInstance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- An open cover of the base induces an open cover of relative projective
space by the corresponding relative projective spaces. -/
noncomputable def projectiveSpaceOpenCover (n : ℕ) {T : Scheme.{u}}
    (𝒰 : T.OpenCover.{u}) : (projectiveSpaceOver n T).OpenCover.{u} :=
  Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i ↦ projectiveSpaceOver n (𝒰.X i))
    (fun i ↦ projectiveSpaceOverMap n (𝒰.f i)) (fun x ↦ by
      obtain ⟨y, hy⟩ := 𝒰.covers
        ((projectiveSpaceOverπ n T).base x)
      refine ⟨𝒰.idx ((projectiveSpaceOverπ n T).base x), ?_⟩
      have hx : x ∈ ((projectiveSpaceOverπ n T) ⁻¹ᵁ
          (𝒰.f (𝒰.idx ((projectiveSpaceOverπ n T).base x))).opensRange :
          Set (projectiveSpaceOver n T)) := by
        change (projectiveSpaceOverπ n T).base x ∈
          (𝒰.f (𝒰.idx ((projectiveSpaceOverπ n T).base x))).opensRange
        exact ⟨y, hy⟩
      rw [← range_projectiveSpaceOverMap n
        (𝒰.f (𝒰.idx ((projectiveSpaceOverπ n T).base x)))] at hx
      exact hx)

/-- Restriction of a projective-space pullback--pushforward object to an open
of the base is the corresponding pullback--pushforward object over that open. -/
noncomputable def projectiveSpaceRestrictPullbackPushforwardIso
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n T)).obj M)) ≅
      (Modules.pullback (projectiveSpaceOverπ n T')).obj
        ((Modules.pushforward (projectiveSpaceOverπ n T')).obj
          ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj M)) :=
  Modules.restrictPullbackPushforwardIsoOfOpenSquare
    (projectiveSpaceOverπ n T) (projectiveSpaceOverπ n T')
    (projectiveSpaceOverMap n j) j
    (projectiveSpaceOverMap_π n j).symm
    (projectiveSpaceOverMap_image_preimage' n j) M

/-- The projective-space evaluation counit commutes with restriction to an
open subscheme of the base. -/
@[reassoc]
lemma projectiveSpaceRestrictPullbackPushforwardIso_hom_counit
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules) :
    (projectiveSpaceRestrictPullbackPushforwardIso n j M).hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).obj M) =
      (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app M) := by
  exact Modules.restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
    (projectiveSpaceOverπ n T) (projectiveSpaceOverπ n T')
    (projectiveSpaceOverMap n j) j
    (projectiveSpaceOverMap_π n j).symm
    (projectiveSpaceOverMap_image_preimage' n j) M

/-- The projective-space restriction comparison followed by transport along
an arbitrary identification of the restricted module. -/
noncomputable def projectiveSpaceRestrictPullbackPushforwardIsoOfIso
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules)
    (M' : (projectiveSpaceOver n T').Modules)
    (e : (Modules.restrictFunctor
      (projectiveSpaceOverMap n j)).obj M ≅ M') :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n T)).obj M)) ≅
      (Modules.pullback (projectiveSpaceOverπ n T')).obj
        ((Modules.pushforward (projectiveSpaceOverπ n T')).obj M') :=
  projectiveSpaceRestrictPullbackPushforwardIso n j M ≪≫
    (Modules.pullback (projectiveSpaceOverπ n T')).mapIso
      ((Modules.pushforward (projectiveSpaceOverπ n T')).mapIso e)

/-- Evaluation commutes with the projective-space restriction comparison and
subsequent transport along any isomorphism of the restricted module. -/
@[reassoc]
lemma projectiveSpaceRestrictPullbackPushforwardIsoOfIso_hom_counit
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules)
    (M' : (projectiveSpaceOver n T').Modules)
    (e : (Modules.restrictFunctor
      (projectiveSpaceOverMap n j)).obj M ≅ M') :
    (projectiveSpaceRestrictPullbackPushforwardIsoOfIso
        n j M M' e).hom ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app M' =
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app M) ≫ e.hom := by
  let β := projectiveSpaceRestrictPullbackPushforwardIso n j M
  change (β.hom ≫
      (Modules.pullback (projectiveSpaceOverπ n T')).map
        ((Modules.pushforward (projectiveSpaceOverπ n T')).map e.hom)) ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app M' =
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app M) ≫ e.hom
  have hnat :
      (Modules.pullback (projectiveSpaceOverπ n T')).map
          ((Modules.pushforward (projectiveSpaceOverπ n T')).map e.hom) ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app M' =
      (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).obj M) ≫ e.hom := by
    exact (Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T')).counit.naturality e.hom
  rw [Category.assoc]
  rw [hnat]
  rw [← Category.assoc]
  rw [projectiveSpaceRestrictPullbackPushforwardIso_hom_counit]

/-- After identifying the restricted module with any chosen local model, the
restricted evaluation is epimorphic exactly when the local evaluation is. -/
theorem projectiveSpace_epi_restrict_counit_iff_of_iso
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules)
    (M' : (projectiveSpaceOver n T').Modules)
    (e : (Modules.restrictFunctor
      (projectiveSpaceOverMap n j)).obj M ≅ M') :
    Epi ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app M)) ↔
      Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app M') := by
  let α := projectiveSpaceRestrictPullbackPushforwardIsoOfIso
    n j M M' e
  have hsq :
      α.hom ≫ (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app M' =
        (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app M) ≫ e.hom :=
    projectiveSpaceRestrictPullbackPushforwardIsoOfIso_hom_counit
      n j M M' e
  constructor
  · intro h
    letI : Epi ((Modules.restrictFunctor
        (projectiveSpaceOverMap n j)).map
          ((Modules.pullbackPushforwardAdjunction
            (projectiveSpaceOverπ n T)).counit.app M)) := h
    haveI : Epi
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app M) ≫ e.hom) :=
      epi_comp _ _
    haveI : Epi (α.hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app M') := hsq.symm ▸ inferInstance
    exact (epi_comp_iff_of_epi α.hom _).mp inferInstance
  · intro h
    letI : Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app M') := h
    haveI : Epi (α.hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app M') := epi_comp _ _
    haveI : Epi
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app M) ≫ e.hom) :=
      hsq ▸ inferInstance
    exact (epi_comp_iff_of_isIso _ e.hom).mp inferInstance

/-- Epimorphicity of projective-space evaluation is Zariski local in the
literal restriction sense. -/
theorem projectiveSpace_epi_restrict_counit_iff
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (M : (projectiveSpaceOver n T).Modules) :
    Epi ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app M)) ↔
      Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app
          ((Modules.restrictFunctor
            (projectiveSpaceOverMap n j)).obj M)) := by
  exact Modules.epi_restrict_counit_iff_openSquare
    (projectiveSpaceOverπ n T) (projectiveSpaceOverπ n T')
    (projectiveSpaceOverMap n j) j
    (projectiveSpaceOverMap_π n j).symm
    (projectiveSpaceOverMap_image_preimage' n j) M

/-- The standard twisted-free quotient obtained by pulling a presentation to a
new base and normalizing its source by the canonical twisted-free comparison. -/
noncomputable def projectiveSpaceTwistedFreeQuotientPullback
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) :
    (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n T' (-l)) ⟶
      (Modules.pullback (projectiveSpaceOverMap n j)).obj Q :=
  (projectiveSpaceOverTwistedFree_pullbackIso n r l j).inv ≫
    (Modules.pullback (projectiveSpaceOverMap n j)).map q

/-- Restriction of the tensorized twisted-free source, normalized to the
standard twisted-free source over the open base. -/
noncomputable def projectiveSpaceTwistedFreeTensorSourceRestrictIso
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        (Modules.tensor
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l))
          (projectiveSpaceOverTwist n T (d : ℤ))) ≅
      Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T' (-l))
        (projectiveSpaceOverTwist n T' (d : ℤ)) :=
  (Modules.restrictFunctorIsoPullback
      (projectiveSpaceOverMap n j)).app _ ≪≫
    projectiveSpaceOverTwistModule_pullbackIso_nat n j
      (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n T (-l)) d ≪≫
    Modules.tensorLeftIso
      (projectiveSpaceOverTwistedFree_pullbackIso n r l j)
      (projectiveSpaceOverTwist n T' (d : ℤ))

/-- Restriction of a tensorized quotient target, normalized to the pullback
target and the standard twist over the open base. -/
noncomputable def projectiveSpaceTensorTargetRestrictIso
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        (Modules.tensor Q (projectiveSpaceOverTwist n T (d : ℤ))) ≅
      Modules.tensor
        ((Modules.pullback (projectiveSpaceOverMap n j)).obj Q)
        (projectiveSpaceOverTwist n T' (d : ℤ)) :=
  (Modules.restrictFunctorIsoPullback
      (projectiveSpaceOverMap n j)).app _ ≪≫
    projectiveSpaceOverTwistModule_pullbackIso_nat n j Q d

/-- The normalized restriction comparisons intertwine a tensorized Quot map
with the tensorization of its standard pulled-back presentation. -/
lemma projectiveSpaceTwistedFreeTensorRestrictIso_naturality
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
          (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ))) ≫
        (projectiveSpaceTensorTargetRestrictIso n j Q d).hom =
      (projectiveSpaceTwistedFreeTensorSourceRestrictIso
          n r j l d).hom ≫
        Modules.tensorMapLeft
          (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
          (projectiveSpaceOverTwist n T' (d : ℤ)) := by
  let m := projectiveSpaceOverMap n j
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let DT := projectiveSpaceOverTwist n T' (d : ℤ)
  let η := Modules.restrictFunctorIsoPullback m
  let EF := projectiveSpaceOverTwistModule_pullbackIso_nat n j F d
  let EQ := projectiveSpaceOverTwistModule_pullbackIso_nat n j Q d
  let eF := projectiveSpaceOverTwistedFree_pullbackIso n r l j
  change (Modules.restrictFunctor m).map (Modules.tensorMapLeft q D) ≫
      η.hom.app (projectiveSpaceOverTwistModule Q (d : ℤ)) ≫ EQ.hom =
    η.hom.app (projectiveSpaceOverTwistModule F (d : ℤ)) ≫ EF.hom ≫
      (Modules.tensorLeftIso eF DT).hom ≫
        Modules.tensorMapLeft
          (eF.inv ≫ (Modules.pullback m).map q) DT
  have hη :
      (Modules.restrictFunctor m).map (Modules.tensorMapLeft q D) ≫
          η.hom.app (projectiveSpaceOverTwistModule Q (d : ℤ)) =
        η.hom.app (projectiveSpaceOverTwistModule F (d : ℤ)) ≫
          (Modules.pullback m).map (Modules.tensorMapLeft q D) := by
    exact η.hom.naturality (Modules.tensorMapLeft q D)
  have htwist :
      (Modules.pullback m).map (Modules.tensorMapLeft q D) ≫ EQ.hom =
        EF.hom ≫ Modules.tensorMapLeft
          ((Modules.pullback m).map q) DT := by
    exact projectiveSpaceOverTwistModule_pullbackIso_nat_naturality
      n j q d
  slice_lhs 1 2 => rw [hη]
  slice_lhs 2 3 => rw [htwist]
  dsimp only [Modules.tensorLeftIso]
  simp only [← Modules.tensorMapLeft_comp,
    Iso.hom_inv_id_assoc]

/-- Restriction of a twisted Quot kernel, normalized to the kernel of the
standard pulled-back twisted-free quotient over the open base. -/
noncomputable def projectiveSpaceTwistedFreeQuotKernelStandardRestrictIso
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ)))) ≅
      kernel (Modules.tensorMapLeft
        (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
        (projectiveSpaceOverTwist n T' (d : ℤ))) :=
  PreservesKernel.iso
      (Modules.restrictFunctor (projectiveSpaceOverMap n j))
      (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ))) ≪≫
    kernel.mapIso (f :=
        (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
          (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ))))
      (Modules.tensorMapLeft
        (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
        (projectiveSpaceOverTwist n T' (d : ℤ)))
      (projectiveSpaceTwistedFreeTensorSourceRestrictIso n r j l d)
      (projectiveSpaceTensorTargetRestrictIso n j Q d)
      (projectiveSpaceTwistedFreeTensorRestrictIso_naturality
        n r j l q d)

/-- Source comparison for the evaluation of a twisted Quot kernel, with the
local target written using the standard pulled-back twisted-free quotient. -/
noncomputable def
    projectiveSpaceTwistedFreeQuotKernelStandardRestrictEvaluationIso
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) ≅
      (Modules.pullback (projectiveSpaceOverπ n T')).obj
        ((Modules.pushforward (projectiveSpaceOverπ n T')).obj
          (kernel (Modules.tensorMapLeft
            (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
            (projectiveSpaceOverTwist n T' (d : ℤ))))) :=
  projectiveSpaceRestrictPullbackPushforwardIsoOfIso n j
    (kernel (Modules.tensorMapLeft q
      (projectiveSpaceOverTwist n T (d : ℤ))))
    (kernel (Modules.tensorMapLeft
      (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
      (projectiveSpaceOverTwist n T' (d : ℤ))))
    (projectiveSpaceTwistedFreeQuotKernelStandardRestrictIso
      n r j l q d)

/-- The evaluation counit of a twisted Quot kernel restricts to the evaluation
counit of the kernel of the standard pulled-back twisted-free quotient. -/
@[reassoc]
lemma
    projectiveSpaceTwistedFreeQuotKernelStandardRestrictEvaluationIso_hom_counit
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (projectiveSpaceTwistedFreeQuotKernelStandardRestrictEvaluationIso
        n r j l q d).hom ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app
          (kernel (Modules.tensorMapLeft
            (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
            (projectiveSpaceOverTwist n T' (d : ℤ)))) =
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ))))) ≫
      (projectiveSpaceTwistedFreeQuotKernelStandardRestrictIso
        n r j l q d).hom := by
  exact projectiveSpaceRestrictPullbackPushforwardIsoOfIso_hom_counit
    n j
    (kernel (Modules.tensorMapLeft q
      (projectiveSpaceOverTwist n T (d : ℤ))))
    (kernel (Modules.tensorMapLeft
      (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
      (projectiveSpaceOverTwist n T' (d : ℤ))))
    (projectiveSpaceTwistedFreeQuotKernelStandardRestrictIso
      n r j l q d)

/-- Epimorphicity of the restricted global evaluation is equivalent to
relative global generation of the kernel of the standard pulled-back
twisted-free quotient over the open base. -/
theorem projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    Epi ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) ↔
      Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app
          (kernel (Modules.tensorMapLeft
            (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
            (projectiveSpaceOverTwist n T' (d : ℤ))))) := by
  exact projectiveSpace_epi_restrict_counit_iff_of_iso n j
    (kernel (Modules.tensorMapLeft q
      (projectiveSpaceOverTwist n T (d : ℤ))))
    (kernel (Modules.tensorMapLeft
      (projectiveSpaceTwistedFreeQuotientPullback n r j l q)
      (projectiveSpaceOverTwist n T' (d : ℤ))))
    (projectiveSpaceTwistedFreeQuotKernelStandardRestrictIso
      n r j l q d)

/-- The restricted evaluation map is epimorphic exactly when the standard
pulled-back twisted-free quotient satisfies the kernel-generation predicate. -/
theorem
    projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff_isGloballyGenerated
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    Epi ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) ↔
      TwistedFreeQuotKernelIsGloballyGenerated n T' l r
        (projectiveSpaceTwistedFreeQuotientPullback n r j l q) d := by
  exact projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff
    n r j l q d

/-- Kernel generation for a twisted-free quotient is preserved by pullback to
an open subscheme of the base, with the quotient written in its standard
pulled-back form. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.pullback_of_isOpenImmersion
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ)
    (h : TwistedFreeQuotKernelIsGloballyGenerated n T l r q d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T' l r
      (projectiveSpaceTwistedFreeQuotientPullback n r j l q) d := by
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ))))) := h
  haveI : Epi
      ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) :=
    Functor.map_epi _ _
  exact
    (projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff_isGloballyGenerated
      n r j l q d).mp inferInstance

/-- On an affine base, kernel generation can be transported back from the
canonical spectrum of global sections. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.of_isoSpec
    (n r : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ)
    (h : TwistedFreeQuotKernelIsGloballyGenerated n
      (Spec Γ(T, ⊤)) l r
        (projectiveSpaceTwistedFreeQuotientPullback
          n r T.isoSpec.inv l q) d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T l r q d := by
  let m := projectiveSpaceOverMap n T.isoSpec.inv
  haveI : IsIso m := inferInstance
  haveI hrest : Epi ((Modules.restrictFunctor m).map
      ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T)).counit.app
          (kernel (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ)))))) :=
    (projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff_isGloballyGenerated
      n r T.isoSpec.inv l q d).mpr h
  let φ := (Modules.pullbackPushforwardAdjunction
    (projectiveSpaceOverπ n T)).counit.app
      (kernel (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ))))
  let η := Modules.restrictFunctorIsoPullback m
  have hnat := η.hom.naturality φ
  haveI : Epi ((Modules.restrictFunctor m).map φ ≫ η.hom.app _) :=
    epi_comp _ _
  haveI : Epi (η.hom.app _ ≫ (Modules.pullback m).map φ) :=
    hnat ▸ inferInstance
  haveI : Epi ((Modules.pullback m).map φ) :=
    (epi_comp_iff_of_epi (η.hom.app _) _).mp inferInstance
  change Epi φ
  exact (Modules.pullback m).epi_of_epi_map inferInstance

/-- A uniform noetherian-spectrum evaluation theorem gives kernel generation
over any affine locally noetherian base. -/
theorem twistedFreeQuotKernelIsGloballyGenerated_of_affine_noetherian_bound
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) (d : ℕ)
    (hgen : ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (projectiveSpaceOverπ n (Spec (.of R))))
      (_ : HasFiberwiseHilbertPolynomial Q P),
      Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n (Spec (.of R)))).counit.app
          (kernel (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))))))
    (T : Scheme.{u}) [IsAffine T] [IsLocallyNoetherian T]
    (Q : (projectiveSpaceOver n T).Modules) [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
    (hflat : Q.FlatOver (projectiveSpaceOverπ n T))
    (hP : HasFiberwiseHilbertPolynomial Q P) :
    TwistedFreeQuotKernelIsGloballyGenerated n T l r q d := by
  let R := Γ(T, ⊤)
  let g := T.isoSpec.inv
  let m := projectiveSpaceOverMap n g
  let Q' := (Modules.pullback m).obj Q
  let q' := projectiveSpaceTwistedFreeQuotientPullback n r g l q
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  letI : Q'.IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation m inferInstance
  letI : Epi q' := by
    dsimp only [q', projectiveSpaceTwistedFreeQuotientPullback]
    infer_instance
  have hflat' : Q'.FlatOver
      (projectiveSpaceOverπ n (Spec (.of R))) :=
    Modules.FlatOver.pullback_of_isPullback m
      (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverπ n T) g
      (isPullback_projectiveSpaceOverMap n g).flip Q hflat
  have hP' : HasFiberwiseHilbertPolynomial Q' P :=
    HasFiberwiseHilbertPolynomial.pullback g hP
  have hlocal : TwistedFreeQuotKernelIsGloballyGenerated
      n (Spec (.of R)) l r q' d :=
    hgen R Q' inferInstance q' inferInstance hflat' hP'
  exact TwistedFreeQuotKernelIsGloballyGenerated.of_isoSpec
    n r T l q d hlocal

/-- Relative global generation of a twisted Quot kernel can be checked on an
open cover of the base, using the standard pulled-back quotient on every
member of the cover. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.of_openCover
    (n r : ℕ) {T : Scheme.{u}} (𝒰 : T.OpenCover.{u})
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ)
    (hlocal : ∀ i,
      TwistedFreeQuotKernelIsGloballyGenerated n (𝒰.X i) l r
        (projectiveSpaceTwistedFreeQuotientPullback n r (𝒰.f i) l q) d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T l r q d := by
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  letI : F.IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  letI : (Modules.tensor F
      (projectiveSpaceOverTwist n T (d : ℤ))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule F (d : ℤ)).IsQuasicoherent
    infer_instance
  letI : (Modules.tensor Q
      (projectiveSpaceOverTwist n T (d : ℤ))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule Q (d : ℤ)).IsQuasicoherent
    infer_instance
  let K := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  letI : K.IsQuasicoherent :=
    Modules.kernel_isQuasicoherent
      (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ)))
  letI : ((Modules.pushforward (projectiveSpaceOverπ n T)).obj K).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ n T) K
  letI : ((Modules.pushforward (projectiveSpaceOverπ n T) ⋙
      Modules.pullback (projectiveSpaceOverπ n T)).obj K).IsQuasicoherent := by
    change ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      ((Modules.pushforward (projectiveSpaceOverπ n T)).obj K)).IsQuasicoherent
    exact Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) _
  letI : ((𝟭 (projectiveSpaceOver n T).Modules).obj K).IsQuasicoherent := by
    change K.IsQuasicoherent
    infer_instance
  apply Modules.epi_of_openCover_restrict
    ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app K)
    (projectiveSpaceOpenCover n 𝒰)
  intro i
  change Epi ((Modules.restrictFunctor
      (projectiveSpaceOverMap n (𝒰.f i))).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app K))
  exact
    (projectiveSpaceTwistedFreeQuotKernelStandard_epi_restrict_counit_iff_isGloballyGenerated
      n r (𝒰.f i) l q d).mpr (hlocal i)

/-- The uniform noetherian-affine bound globalizes to every locally
noetherian base scheme. -/
theorem exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_locallyNoetherian
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
        (Q : (projectiveSpaceOver n T).Modules) [Q.IsFinitePresentation]
        (q : (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q],
        Q.FlatOver (projectiveSpaceOverπ n T) →
          HasFiberwiseHilbertPolynomial Q P →
            TwistedFreeQuotKernelIsGloballyGenerated n T l r q d := by
  obtain ⟨D, hD⟩ :=
    exists_bound_pullbackPushforwardCounit_epi_twistedFreeQuotKernel_noetherian_affine
      n r hn l P
  refine ⟨D, ?_⟩
  intro d hd T _ Q _ q _ hflat hP
  letI : Q.IsQuasicoherent := inferInstance
  apply TwistedFreeQuotKernelIsGloballyGenerated.of_openCover
    n r T.affineCover l q d
  intro i
  let g := T.affineCover.f i
  let m := projectiveSpaceOverMap n g
  let Q' := (Modules.pullback m).obj Q
  let q' := projectiveSpaceTwistedFreeQuotientPullback n r g l q
  letI : IsLocallyNoetherian (T.affineCover.X i) := inferInstance
  letI : Q'.IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation m inferInstance
  letI : Epi q' := by
    dsimp only [q', projectiveSpaceTwistedFreeQuotientPullback]
    infer_instance
  have hflat' : Q'.FlatOver
      (projectiveSpaceOverπ n (T.affineCover.X i)) :=
    Modules.FlatOver.pullback_of_isPullback m
      (projectiveSpaceOverπ n (T.affineCover.X i))
      (projectiveSpaceOverπ n T) g
      (isPullback_projectiveSpaceOverMap n g).flip Q hflat
  have hP' : HasFiberwiseHilbertPolynomial Q' P :=
    HasFiberwiseHilbertPolynomial.pullback g hP
  exact twistedFreeQuotKernelIsGloballyGenerated_of_affine_noetherian_bound
    n r l P d (hD d hd) (T.affineCover.X i) Q' q' hflat' hP'

/-- The locally noetherian kernel-generation bound in the `Over`-scheme
argument shape used by the eventual Quot-to-Grassmannian constructors. -/
theorem exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_over_locallyNoetherian
    (n r : ℕ) (hn : 0 < n) (S : Scheme.{u}) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Over S) [IsLocallyNoetherian T.left]
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d := by
  obtain ⟨D, hD⟩ :=
    exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_locallyNoetherian
      n r hn l P
  refine ⟨D, ?_⟩
  intro d hd T _ a hP
  let Q := quotDataOnProjectiveSpace
    (n := n) (S := S) (T := T)
    (Modules.QuotientPullbackData.twistedFreeAmbient
      (n := n) (r := r) (l := l)) a
  let q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  letI : Q.IsFinitePresentation :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over T a
  letI : Epi q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  exact hD d hd T.left Q q
    (Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over T a) hP

/-- The restriction of a twisted Quot kernel is canonically the kernel of the
restricted tensor map. -/
noncomputable def projectiveSpaceTwistedFreeQuotKernelRestrictIso
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ)))) ≅
      kernel (Modules.tensorMapLeft
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map q)
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
          (projectiveSpaceOverTwist n T (d : ℤ)))) :=
  Modules.restrictTensorMapLeftKernelIso
    (projectiveSpaceOverMap n j) q
      (projectiveSpaceOverTwist n T (d : ℤ))

/-- Source comparison for the evaluation map of a twisted Quot kernel after
restriction to an open subscheme of the base. -/
noncomputable def projectiveSpaceTwistedFreeQuotKernelRestrictEvaluationIso
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) ≅
      (Modules.pullback (projectiveSpaceOverπ n T')).obj
        ((Modules.pushforward (projectiveSpaceOverπ n T')).obj
          (kernel (Modules.tensorMapLeft
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).map q)
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).obj
                (projectiveSpaceOverTwist n T (d : ℤ)))))) :=
  projectiveSpaceRestrictPullbackPushforwardIso n j
      (kernel (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ)))) ≪≫
    (Modules.pullback (projectiveSpaceOverπ n T')).mapIso
      ((Modules.pushforward (projectiveSpaceOverπ n T')).mapIso
        (projectiveSpaceTwistedFreeQuotKernelRestrictIso
          n r j l q d))

/-- Evaluation of a twisted Quot kernel commutes with open restriction, after
identifying the restricted kernel with the kernel of the restricted tensor
map. -/
@[reassoc]
lemma projectiveSpaceTwistedFreeQuotKernelRestrictEvaluationIso_hom_counit
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (projectiveSpaceTwistedFreeQuotKernelRestrictEvaluationIso
      n r j l q d).hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app
            (kernel (Modules.tensorMapLeft
              ((Modules.restrictFunctor
                (projectiveSpaceOverMap n j)).map q)
              ((Modules.restrictFunctor
                (projectiveSpaceOverMap n j)).obj
                  (projectiveSpaceOverTwist n T (d : ℤ))))) =
      (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
          ((Modules.pullbackPushforwardAdjunction
            (projectiveSpaceOverπ n T)).counit.app
              (kernel (Modules.tensorMapLeft q
                (projectiveSpaceOverTwist n T (d : ℤ))))) ≫
        (projectiveSpaceTwistedFreeQuotKernelRestrictIso
          n r j l q d).hom := by
  let K := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let K' := kernel (Modules.tensorMapLeft
    ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map q)
    ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
      (projectiveSpaceOverTwist n T (d : ℤ))))
  let e := projectiveSpaceTwistedFreeQuotKernelRestrictIso
    n r j l q d
  let β := projectiveSpaceRestrictPullbackPushforwardIso n j K
  change (β.hom ≫
      (Modules.pullback (projectiveSpaceOverπ n T')).map
        ((Modules.pushforward (projectiveSpaceOverπ n T')).map e.hom)) ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app K' =
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app K) ≫ e.hom
  have hnat :
      (Modules.pullback (projectiveSpaceOverπ n T')).map
          ((Modules.pushforward (projectiveSpaceOverπ n T')).map e.hom) ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app K' =
      (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).obj K) ≫ e.hom := by
    exact (Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T')).counit.naturality e.hom
  rw [Category.assoc]
  rw [hnat]
  rw [← Category.assoc]
  rw [projectiveSpaceRestrictPullbackPushforwardIso_hom_counit]

/-- For a twisted Quot kernel, epimorphicity of the restricted global
evaluation map is equivalent to epimorphicity of the local evaluation map for
the kernel of the restricted tensor map. -/
theorem projectiveSpaceTwistedFreeQuotKernel_epi_restrict_counit_iff
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    Epi ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
        ((Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ)))))) ↔
      Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app
          (kernel (Modules.tensorMapLeft
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).map q)
            ((Modules.restrictFunctor
              (projectiveSpaceOverMap n j)).obj
                (projectiveSpaceOverTwist n T (d : ℤ)))))) := by
  let K := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let K' := kernel (Modules.tensorMapLeft
    ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map q)
    ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
      (projectiveSpaceOverTwist n T (d : ℤ))))
  let α := projectiveSpaceTwistedFreeQuotKernelRestrictEvaluationIso
    n r j l q d
  let e := projectiveSpaceTwistedFreeQuotKernelRestrictIso n r j l q d
  have hsq :
      α.hom ≫
          (Modules.pullbackPushforwardAdjunction
            (projectiveSpaceOverπ n T')).counit.app K' =
        (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app K) ≫ e.hom :=
    projectiveSpaceTwistedFreeQuotKernelRestrictEvaluationIso_hom_counit
      n r j l q d
  constructor
  · intro h
    letI : Epi ((Modules.restrictFunctor
        (projectiveSpaceOverMap n j)).map
          ((Modules.pullbackPushforwardAdjunction
            (projectiveSpaceOverπ n T)).counit.app K)) := h
    haveI : Epi
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app K) ≫ e.hom) :=
      epi_comp _ _
    haveI : Epi (α.hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app K') := hsq.symm ▸ inferInstance
    exact (epi_comp_iff_of_epi α.hom _).mp inferInstance
  · intro h
    letI : Epi ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app K') := h
    haveI : Epi (α.hom ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T')).counit.app K') := epi_comp _ _
    haveI : Epi
        ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
            ((Modules.pullbackPushforwardAdjunction
              (projectiveSpaceOverπ n T)).counit.app K) ≫ e.hom) :=
      hsq ▸ inferInstance
    exact (epi_comp_iff_of_isIso _ e.hom).mp inferInstance

/-- The preceding counit square specialized to the degree-`d` kernel of a
twisted-free Quot presentation. -/
lemma projectiveSpace_twistedFreeQuotKernel_restrict_counit
    (n r : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (projectiveSpaceRestrictPullbackPushforwardIso n j
      (kernel (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ))))).hom ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T')).counit.app
          ((Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj
            (kernel (Modules.tensorMapLeft q
              (projectiveSpaceOverTwist n T (d : ℤ))))) =
    (Modules.restrictFunctor (projectiveSpaceOverMap n j)).map
      ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T)).counit.app
          (kernel (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ))))) := by
  exact projectiveSpaceRestrictPullbackPushforwardIso_hom_counit n j _

end AlgebraicGeometry.Scheme

end

end
