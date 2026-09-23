module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Base change for module sheaves across open immersions

This file packages the Beck--Chevalley comparisons for sheaves of modules in a
cartesian square with an open side.  The constructions are independent of
quasi-coherence and are useful in Zariski gluing arguments.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The restriction of a scheme morphism to the inverse image of an open subset. -/
noncomputable def restrictToPreimage (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  f.resLE U (f ⁻¹ᵁ U) le_rfl

/-- The image in the source of an open in a restricted target is its inverse image
under the original morphism. -/
lemma image_preimage_restrict_eq (f : X ⟶ Y) (U : Y.Opens)
    (W : U.toScheme.Opens) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((restrictToPreimage f U) ⁻¹ᵁ W) =
      f ⁻¹ᵁ (U.ι ''ᵁ W) := by
  unfold restrictToPreimage
  rw [Scheme.Hom.resLE_preimage]
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  rw [Scheme.Opens.opensRange_ι, inf_eq_right]
  exact f.preimage_mono (U.ι_image_le W)

/-- The presheaf-level comparison underlying restriction--pushforward base change
across a cartesian open square.  It is split out from the sheaf-level isomorphism so
that sectionwise calculations can use the explicit comparison without unfolding a
full-faithful lift. -/
noncomputable def restrictPushforwardPresheafIsoOfOpenSquare
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) = f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) :
    ((restrictFunctor iY).obj ((pushforward f).obj M)).val ≅
      ((pushforward g).obj ((restrictFunctor iX).obj M)).val := by
  refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · let h := hopen W.unop
    refine ModuleCat.isoMk (M.presheaf.mapIso (eqToIso h).op) ?_
    intro r
    ext x
    have hr : X.presheaf.map (eqToHom h).op
        (f.app (iY ''ᵁ W.unop) ((iY.appIso W.unop).inv r)) =
        (iX.appIso (g ⁻¹ᵁ W.unop)).inv (g.app W.unop r) := by
      have hj : iX.app (f ⁻¹ᵁ (iY ''ᵁ W.unop)) ≫
            X'.presheaf.map
              (eqToHom (by
                rw [← h]
                exact iX.preimage_image_eq (g ⁻¹ᵁ W.unop) |>.symm)).op ≫
            (iX.appIso (g ⁻¹ᵁ W.unop)).inv =
          X.presheaf.map (eqToHom h).op := by
        change iX.appLE (f ⁻¹ᵁ (iY ''ᵁ W.unop)) (g ⁻¹ᵁ W.unop) _ ≫
            (iX.appIso (g ⁻¹ᵁ W.unop)).inv =
          X.presheaf.map (eqToHom h).op
        rw [iX.appLE_appIso_inv]
        rfl
      have hmor : (iY.appIso W.unop).inv ≫ f.app (iY ''ᵁ W.unop) ≫
            X.presheaf.map (eqToHom h).op =
          g.app W.unop ≫ (iX.appIso (g ⁻¹ᵁ W.unop)).inv := by
        rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
          g iY (iX ≫ f) hsq.symm]
        simp only [Scheme.Hom.comp_app, Category.assoc]
        rw [cancel_epi]
        convert congrArg (fun k ↦ f.app (iY ''ᵁ W.unop) ≫ k) hj.symm using 1
      exact ConcreteCategory.congr_hom hmor r
    change (M.smul ((iX.appIso (g ⁻¹ᵁ W.unop)).inv
      (g.app W.unop r))).hom (M.presheaf.map (eqToHom h).op x) =
      M.presheaf.map (eqToHom h).op
        ((M.smul (f.app (iY ''ᵁ W.unop)
          ((iY.appIso W.unop).inv r))).hom x)
    erw [M.map_smul]
    rw [hr]
    rfl
  · intro W W' k
    dsimp [restrictFunctor, pushforward,
      SheafOfModules.pushforward, PresheafOfModules.pushforward,
      PresheafOfModules.pushforward₀, PresheafOfModules.restrictScalars]
    ext x
    let x' : Γ(M, f ⁻¹ᵁ (iY ''ᵁ W.unop)) := x
    change M.presheaf.map _ (M.presheaf.map _ x') =
      M.presheaf.map _ (M.presheaf.map _ x')
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2

/-- Restriction commutes with pushforward across a cartesian open square.

The hypothesis `hopen` is the opens-level form of cartesianity. -/
noncomputable def restrictPushforwardIsoOfOpenSquare
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) = f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) :
    (restrictFunctor iY).obj ((pushforward f).obj M) ≅
      (pushforward g).obj ((restrictFunctor iX).obj M) :=
  (SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).preimageIso
    (restrictPushforwardPresheafIsoOfOpenSquare f g iX iY hsq hopen M)

/-- Forgetting the sheaf-level base-change isomorphism recovers its explicit
presheaf-level comparison. -/
@[simp]
lemma restrictPushforwardIsoOfOpenSquare_hom_val
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) = f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) :
    (restrictPushforwardIsoOfOpenSquare f g iX iY hsq hopen M).hom.val =
      (restrictPushforwardPresheafIsoOfOpenSquare f g iX iY hsq hopen M).hom := by
  change (SheafOfModules.forget Y'.ringCatSheaf).map
      ((SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).preimage
        (X := (restrictFunctor iY).obj ((pushforward f).obj M))
        (Y := (pushforward g).obj ((restrictFunctor iX).obj M))
        (restrictPushforwardPresheafIsoOfOpenSquare
          f g iX iY hsq hopen M).hom) = _
  exact (SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).map_preimage _

/-- The analogous equation for the inverse base-change comparison. -/
@[simp]
lemma restrictPushforwardIsoOfOpenSquare_inv_val
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) = f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) :
    (restrictPushforwardIsoOfOpenSquare f g iX iY hsq hopen M).inv.val =
      (restrictPushforwardPresheafIsoOfOpenSquare f g iX iY hsq hopen M).inv := by
  change (SheafOfModules.forget Y'.ringCatSheaf).map
      ((SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).preimage
        (X := (pushforward g).obj ((restrictFunctor iX).obj M))
        (Y := (restrictFunctor iY).obj ((pushforward f).obj M))
        (restrictPushforwardPresheafIsoOfOpenSquare
          f g iX iY hsq hopen M).inv) = _
  exact (SheafOfModules.fullyFaithfulForget Y'.ringCatSheaf).map_preimage _

/-- Restricting a morphism of module sheaves acts on a section by applying the
original morphism over the image open. -/
@[simp]
lemma restrictFunctor_map_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Hom.app ((restrictFunctor f).map φ) U = Hom.app φ (f ''ᵁ U) := rfl

/-- Elementwise form of `restrictFunctor_map_app`. -/
lemma restrictFunctor_map_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) (U : X.Opens) (m : Γ(M, f ''ᵁ U)) :
    (Hom.app ((restrictFunctor f).map φ) U).hom m =
      (Hom.app φ (f ''ᵁ U)).hom m := rfl

/-- The base-change comparison acts sectionwise by transport along the
opens-level cartesian equality. -/
lemma restrictPushforwardIsoOfOpenSquare_hom_app_apply
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y)
    [IsOpenImmersion iX] [IsOpenImmersion iY]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) =
      f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) (W : Y'.Opens)
    (m : Γ(M, f ⁻¹ᵁ (iY ''ᵁ W))) :
    (Hom.app
        (restrictPushforwardIsoOfOpenSquare f g iX iY hsq hopen M).hom W).hom m =
      (M.presheaf.map (eqToHom (hopen W)).op).hom m := by
  change (((restrictPushforwardIsoOfOpenSquare
    f g iX iY hsq hopen M).hom.val.app (op W)).hom m) = _
  rw [restrictPushforwardIsoOfOpenSquare_hom_val]
  rfl

/-- After one further open restriction, the base-change comparison still acts
sectionwise by transport along the original cartesian equality. -/
lemma restrictFunctor_map_restrictPushforwardIsoOfOpenSquare_hom_app_apply
    {X Y X' Y' Y'' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) (l : Y'' ⟶ Y')
    [IsOpenImmersion iX] [IsOpenImmersion iY] [IsOpenImmersion l]
    (hsq : g ≫ iY = iX ≫ f)
    (hopen : ∀ W : Y'.Opens, iX ''ᵁ (g ⁻¹ᵁ W) =
      f ⁻¹ᵁ (iY ''ᵁ W))
    (M : X.Modules) (W : Y''.Opens)
    (x : Γ((restrictFunctor iY ⋙ restrictFunctor l).obj
      ((pushforward f).obj M), W)) :
    (Hom.app ((restrictFunctor l).map
      (restrictPushforwardIsoOfOpenSquare f g iX iY hsq hopen M).hom) W).hom x =
      (M.presheaf.map (eqToHom (hopen (l ''ᵁ W))).op).hom x := by
  change (Hom.app
    (restrictPushforwardIsoOfOpenSquare f g iX iY hsq hopen M).hom
      (l ''ᵁ W)).hom x = _
  exact restrictPushforwardIsoOfOpenSquare_hom_app_apply
    f g iX iY hsq hopen M (l ''ᵁ W) x

/-- A further pushforward of the inverse restriction compositor acts on
sections by the corresponding transport of opens. -/
lemma pushforward_map_restrictFunctorComp_inv_app_apply
    {W P Q Y' : Scheme.{u}} (k : P ⟶ W) (m : Q ⟶ P)
    (h : Q ⟶ Y') [IsOpenImmersion k] [IsOpenImmersion m]
    (M : W.Modules) (V : Y'.Opens)
    (x : Γ((pushforward h).obj
      ((restrictFunctor k ⋙ restrictFunctor m).obj M), V)) :
    (Hom.app ((pushforward h).map
      ((restrictFunctorComp m k).inv.app M)) V).hom x =
      (M.presheaf.map (eqToHom (by simp)).op).hom x := by
  rw [pushforward_map_app, restrictFunctorComp_inv_app_app]
  congr 2

/-- A commutative square whose vertical arrows are isomorphisms satisfies the
opens-level cartesian equality used by `restrictPushforwardIsoOfOpenSquare`. -/
lemma image_preimage_eq_of_isIso_square
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsIso iX] [IsIso iY]
    (hsq : g ≫ iY = iX ≫ f) (W : Y'.Opens) :
    iX ''ᵁ (g ⁻¹ᵁ W) = f ⁻¹ᵁ (iY ''ᵁ W) := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨g x', hx', ?_⟩
    change (g ≫ iY) x' = (iX ≫ f) x'
    exact congrArg (fun k : X' ⟶ Y ↦ k x') hsq
  · rintro ⟨y', hy', hxy⟩
    obtain ⟨x', rfl⟩ := (ConcreteCategory.bijective_of_isIso iX.base).surjective x
    refine ⟨x', ?_, rfl⟩
    change g x' ∈ W
    have heq : iY (g x') = iY y' := by
      calc
        iY (g x') = f (iX x') := by
          change (g ≫ iY) x' = (iX ≫ f) x'
          exact congrArg (fun k : X' ⟶ Y ↦ k x') hsq
        _ = iY y' := hxy.symm
    have hgy : g x' = y' :=
      (ConcreteCategory.bijective_of_isIso iY.base).injective heq
    exact hgy.symm ▸ hy'

/-- Restricting a pushed-forward module to an open is the pushforward of the
module restricted to the inverse-image open. -/
noncomputable def restrictPushforwardIso (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) :
    (restrictFunctor U.ι).obj ((pushforward f).obj M) ≅
      (pushforward (restrictToPreimage f U)).obj
        ((restrictFunctor (f ⁻¹ᵁ U).ι).obj M) :=
  restrictPushforwardIsoOfOpenSquare f (restrictToPreimage f U)
    (f ⁻¹ᵁ U).ι U.ι (f.resLE_comp_ι le_rfl)
    (image_preimage_restrict_eq f U) M

/-- The two open subsets in the cartesian square obtained by pulling back an
open immersion agree. -/
lemma image_preimage_eq_pullback_openSquare
    {Y Z W : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (i : W ⟶ Z) (U : Y.Opens) :
    pullback.snd j i ''ᵁ (pullback.fst j i ⁻¹ᵁ U) =
      i ⁻¹ᵁ (j ''ᵁ U) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨pullback.fst j i w, hw, ?_⟩
    change (pullback.fst j i ≫ j) w = (pullback.snd j i ≫ i) w
    exact congrArg (fun k : Limits.pullback j i ⟶ Z ↦ k w)
      (pullback.condition (f := j) (g := i))
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨w, hwy, hwz⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := j) (g := i) y z hzy
    refine ⟨w, ?_, hwz⟩
    change pullback.fst j i w ∈ U
    rw [hwy]
    exact hy

/-- Pullback of a module through a cartesian square agrees with first
restricting across its open side and then pulling back. -/
noncomputable def restrictPullbackIsoPullbackRestrict
    {Y Z W : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (i : W ⟶ Z) (N : Z.Modules) :
    (restrictFunctor (pullback.snd j i)).obj ((pullback i).obj N) ≅
      (pullback (pullback.fst j i)).obj ((restrictFunctor j).obj N) :=
  (restrictFunctorIsoPullback (pullback.snd j i)).app ((pullback i).obj N) ≪≫
    (pullbackComp (pullback.snd j i) i).app N ≪≫
    (pullbackCongr (pullback.condition (f := j) (g := i)).symm).app N ≪≫
    (pullbackComp (pullback.fst j i) j).symm.app N ≪≫
    (pullback (pullback.fst j i)).mapIso ((restrictFunctorIsoPullback j).symm.app N)

/-- The two iterated pushforwards in a commutative square are naturally
isomorphic. -/
noncomputable def pushforwardCompIsoOfSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) (hsq : g ≫ j = k ≫ i) :
    pushforward k ⋙ pushforward i ≅ pushforward g ⋙ pushforward j :=
  pushforwardComp k i ≪≫ pushforwardCongr hsq.symm ≪≫
    (pushforwardComp g j).symm

/-- The canonical comparison between the two composite inverse-image functors
in a commutative square with open horizontal source maps. -/
noncomputable def restrictPullbackIsoOfOpenSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i) :
    pullback i ⋙ restrictFunctor k ≅ restrictFunctor j ⋙ pullback g :=
  Adjunction.leftAdjointUniq
    (((pullbackPushforwardAdjunction i).comp (restrictAdjunction k)).ofNatIsoRight
      (pushforwardCompIsoOfSquare i g k j hsq))
    ((restrictAdjunction j).comp (pullbackPushforwardAdjunction g))

/-- Restricting `i_* i^*` through an open cartesian square gives the
corresponding local pull-push object. -/
noncomputable def restrictPushPullIsoPullbackRestrict
    {Y Z W : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (i : W ⟶ Z) (N : Z.Modules) :
    (restrictFunctor j).obj ((pushforward i).obj ((pullback i).obj N)) ≅
      (pushforward (pullback.fst j i)).obj
        ((pullback (pullback.fst j i)).obj ((restrictFunctor j).obj N)) :=
  restrictPushforwardIsoOfOpenSquare i (pullback.fst j i)
      (pullback.snd j i) j (pullback.condition (f := j) (g := i))
      (image_preimage_eq_pullback_openSquare j i) ((pullback i).obj N) ≪≫
    (pushforward (pullback.fst j i)).mapIso
      ((restrictPullbackIsoOfOpenSquare i (pullback.fst j i)
        (pullback.snd j i) j (pullback.condition (f := j) (g := i))).app N)

/-- Naturality of open-square base change in the module being pushed forward. -/
@[reassoc]
lemma restrictPushforwardIsoOfOpenSquare_hom_naturality
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    {M N : W.Modules} (a : M ⟶ N) :
    (restrictFunctor j).map ((pushforward i).map a) ≫
        (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen N).hom =
      (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen M).hom ≫
        (pushforward g).map ((restrictFunctor k).map a) := by
  apply Modules.hom_ext
  intro V
  ext x
  simp [restrictPushforwardIsoOfOpenSquare]
  dsimp [restrictFunctor, pushforward, SheafOfModules.pushforward,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.restrictScalars]
  let h := hopen V
  change N.presheaf.map (eqToHom h).op
      (a.val.app (op (i ⁻¹ᵁ (j ''ᵁ V))) x) =
    a.val.app (op (k ''ᵁ (g ⁻¹ᵁ V)))
      (M.presheaf.map (eqToHom h).op x)
  have ha := (ConcreteCategory.congr_hom
    (a.val.naturality (eqToHom h).op) x).symm
  change N.presheaf.map (eqToHom h).op
      (a.val.app (op (i ⁻¹ᵁ (j ''ᵁ V))) x) =
    a.val.app (op (k ''ᵁ (g ⁻¹ᵁ V)))
      (M.presheaf.map (eqToHom h).op x) at ha
  exact ha

/-- The unit of restriction--pushforward is compatible with open-square base
change and composition of pushforwards. -/
@[reassoc]
lemma unit_restrictPushforwardIsoOfOpenSquare_hom
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (L : W.Modules) :
    (restrictAdjunction j).unit.app ((pushforward i).obj L) ≫
        (pushforward j).map
          (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen L).hom ≫
        (pushforwardComp g j).hom.app ((restrictFunctor k).obj L) =
      (pushforward i).map ((restrictAdjunction k).unit.app L) ≫
        (pushforwardComp k i).hom.app ((restrictFunctor k).obj L) ≫
        (pushforwardCongr hsq.symm).hom.app ((restrictFunctor k).obj L) := by
  apply Modules.hom_ext _ _ fun V ↦ ?_
  ext x
  simp [restrictPushforwardIsoOfOpenSquare]
  dsimp [restrictFunctor]
  change L.presheaf.map _ (L.presheaf.map _ x) =
    L.presheaf.map _ (L.presheaf.map _ x)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 2

section RestrictedFiniteLimits

/-- Restriction of module sheaves along an open immersion preserves finite
limits.  On every open subset this is preservation by restriction of scalars;
the sectionwise limit is reflected through the fully faithful forgetful
functor from sheaves of modules to presheaves of modules. -/
lemma restrictFunctor_preservesLimit
    (f : X ⟶ Y) [IsOpenImmersion f]
    {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Y.Modules) : PreservesLimit K (restrictFunctor f) := by
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  let c := (restrictFunctor f).mapCone (limit.cone K)
  let forget := SheafOfModules.forget X.ringCatSheaf
  have hc : IsLimit (forget.mapCone c) := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits _ _
    intro V
    change IsLimit
      ((ModuleCat.restrictScalars (f.appIso V.unop).inv.hom).mapCone
        ((SheafOfModules.evaluation Y.ringCatSheaf
          (op (f ''ᵁ V.unop))).mapCone (limit.cone K)))
    let hEvalPres : PreservesLimit K
        (SheafOfModules.evaluation Y.ringCatSheaf
          (op (f ''ᵁ V.unop))) :=
      SheafOfModules.evaluationPreservesLimit (F := K) _
    let hEval := @isLimitOfPreserves _ _ _ _ _ _ K
      (SheafOfModules.evaluation Y.ringCatSheaf
        (op (f ''ᵁ V.unop))) _ (limit.isLimit K) hEvalPres
    let RS := ModuleCat.restrictScalars.{u} (f.appIso V.unop).inv.hom
    let hFinite : PreservesFiniteLimits RS := by infer_instance
    let hShape : PreservesLimitsOfShape J RS :=
      @PreservesFiniteLimits.preservesFiniteLimits _ _ _ _ RS hFinite J _ _
    let hRestrict : PreservesLimit
        (K ⋙ SheafOfModules.evaluation Y.ringCatSheaf
          (op (f ''ᵁ V.unop))) RS :=
      @PreservesLimitsOfShape.preservesLimit _ _ _ _ J _ RS hShape _
    exact @isLimitOfPreserves _ _ _ _ _ _ _ _ _ hEval hRestrict
  let FF := SheafOfModules.fullyFaithfulForget X.ringCatSheaf
  exact
    { lift := fun s ↦ FF.preimage (hc.lift (forget.mapCone s))
      fac := fun s j ↦ by
        apply FF.map_injective
        change forget.map (FF.preimage (hc.lift (forget.mapCone s))) ≫
          (forget.mapCone c).π.app j = (forget.mapCone s).π.app j
        rw [FF.map_preimage]
        exact hc.fac (forget.mapCone s) j
      uniq := fun s m hm ↦ by
        apply FF.map_injective
        apply hc.uniq (forget.mapCone s)
        intro j
        have hπc : (forget.mapCone c).π.app j =
            forget.map (c.π.app j) := rfl
        have hπs : (forget.mapCone s).π.app j =
            forget.map (s.π.app j) := rfl
        rw [hπc, hπs]
        change (SheafOfModules.forget X.ringCatSheaf).map m ≫
            (SheafOfModules.forget X.ringCatSheaf).map (c.π.app j) =
          (SheafOfModules.forget X.ringCatSheaf).map (s.π.app j)
        calc
          _ = (SheafOfModules.forget X.ringCatSheaf).map
              (m ≫ c.π.app j) :=
            ((SheafOfModules.forget X.ringCatSheaf).map_comp _ _).symm
          _ = _ := congrArg (SheafOfModules.forget X.ringCatSheaf).map
            (hm j) }

noncomputable instance (priority := 900)
    restrictFunctor_preservesFiniteLimits_of_openImmersion
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) where
  preservesFiniteLimits _J _ _ :=
    { preservesLimit := fun {K} ↦ restrictFunctor_preservesLimit f K }

end RestrictedFiniteLimits

section RestrictedProducts

variable {J : Type} {P : X.Modules}

/-- Sections of a restricted product are the product of the sections of the
restricted factors.  This is the sectionwise limit comparison; it does not
require a global `PreservesLimits` instance for restriction. -/
noncomputable def restrictProductSectionsIso (f : X ⟶ Y) [IsOpenImmersion f]
    (A : J → Y.Modules) (W : X.Opensᵒᵖ) :
    ((restrictFunctor f).obj (∏ᶜ A)).val.obj W ≅
      ∏ᶜ fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W := by
  let E := SheafOfModules.evaluation Y.ringCatSheaf
      (op (f ''ᵁ W.unop)) ⋙
    ModuleCat.restrictScalars (f.appIso W.unop).inv.hom
  letI : PreservesLimit (Discrete.functor A)
      (SheafOfModules.evaluation Y.ringCatSheaf (op (f ''ᵁ W.unop))) :=
    SheafOfModules.evaluationPreservesLimit _ _
  letI : PreservesLimit (Discrete.functor A) E := by
    dsimp only [E]
    infer_instance
  exact PreservesProduct.iso E A

/-- The section/product comparison followed by a projection is evaluation of
the corresponding projection of module sheaves. -/
@[reassoc]
lemma restrictProductSectionsIso_hom_π (f : X ⟶ Y) [IsOpenImmersion f]
    (A : J → Y.Modules) (W : X.Opensᵒᵖ) (j : J) :
    (restrictProductSectionsIso f A W).hom ≫
      Pi.π (fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W) j =
      ((restrictFunctor f).map (Pi.π A j)).val.app W := by
  let E := SheafOfModules.evaluation Y.ringCatSheaf
      (op (f ''ᵁ W.unop)) ⋙
    ModuleCat.restrictScalars (f.appIso W.unop).inv.hom
  change (PreservesProduct.iso E A).hom ≫ Pi.π (fun j ↦ E.obj (A j)) j =
    E.map (Pi.π A j)
  exact piComparison_comp_π E A j

/-- The section/product comparison is natural in the open on the source,
after projection to each factor. -/
lemma restrictProductSectionsIso_naturality_π (f : X ⟶ Y)
    [IsOpenImmersion f] (A : J → Y.Modules) {W W' : X.Opensᵒᵖ}
    (i : W ⟶ W') (j : J) :
    ((restrictFunctor f).obj (∏ᶜ A)).val.map i ≫
      (ModuleCat.restrictScalars _).map
        ((restrictProductSectionsIso f A W').hom ≫
          Pi.π (fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W') j) =
      ((restrictProductSectionsIso f A W).hom ≫
        Pi.π (fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W) j) ≫
        ((restrictFunctor f).obj (A j)).val.map i := by
  rw [restrictProductSectionsIso_hom_π,
    restrictProductSectionsIso_hom_π]
  exact ((restrictFunctor f).map (Pi.π A j)).val.naturality i

/-- Assemble maps to the restrictions of the factors into a map to the
restriction of their product. -/
noncomputable def restrictProductLiftApp (f : X ⟶ Y) [IsOpenImmersion f]
    (A : J → Y.Modules)
    (a : ∀ j, P ⟶ (restrictFunctor f).obj (A j)) (W : X.Opensᵒᵖ) :
    P.val.obj W ⟶ ((restrictFunctor f).obj (∏ᶜ A)).val.obj W :=
  Pi.lift (fun j ↦ (a j).val.app W) ≫
    (restrictProductSectionsIso f A W).inv

/-- Projecting the sectionwise restricted-product lift recovers its chosen
component. -/
@[reassoc]
lemma restrictProductLiftApp_comp_sectionsIso_hom_π
    (f : X ⟶ Y) [IsOpenImmersion f] (A : J → Y.Modules)
    (a : ∀ j, P ⟶ (restrictFunctor f).obj (A j)) (W : X.Opensᵒᵖ) (j : J) :
    restrictProductLiftApp f A a W ≫
      (restrictProductSectionsIso f A W).hom ≫
      Pi.π (fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W) j =
        (a j).val.app W := by
  rw [restrictProductLiftApp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact Pi.lift_π _ _

/-- Assemble maps to the restrictions of the factors into a map to the
restriction of their product. -/
noncomputable def restrictProductLift (f : X ⟶ Y) [IsOpenImmersion f]
    (A : J → Y.Modules)
    (a : ∀ j, P ⟶ (restrictFunctor f).obj (A j)) :
    P ⟶ (restrictFunctor f).obj (∏ᶜ A) := by
  refine { val := ?_ }
  refine ⟨fun W ↦ restrictProductLiftApp f A a W, ?_⟩
  intro W W' i
  ext x
  apply (ConcreteCategory.bijective_of_isIso
    (restrictProductSectionsIso f A W').hom).1
  apply Concrete.limit_ext
  intro j
  calc
    _ = (a j.as).val.app W' (P.val.map i x) := by
      change (Pi.π (fun j : J ↦ ((restrictFunctor f).obj (A j)).val.obj W') j.as)
        ((restrictProductSectionsIso f A W').hom
          (restrictProductLiftApp f A a W' (P.val.map i x))) = _
      exact ConcreteCategory.congr_hom
        (restrictProductLiftApp_comp_sectionsIso_hom_π f A a W' j.as)
        (P.val.map i x)
    _ = ((restrictFunctor f).obj (A j.as)).val.map i
          ((a j.as).val.app W x) :=
      CategoryTheory.congr_fun ((a j.as).val.naturality i) x
    _ = _ := by
      change _ = (Pi.π (fun j : J ↦
          ((restrictFunctor f).obj (A j)).val.obj W') j.as)
        ((restrictProductSectionsIso f A W').hom
          (((restrictFunctor f).obj (∏ᶜ A)).val.map i
            (restrictProductLiftApp f A a W x)))
      have h := ConcreteCategory.congr_hom
        (restrictProductSectionsIso_naturality_π f A i j.as)
        (restrictProductLiftApp f A a W x)
      refine Eq.trans ?_ h.symm
      exact congrArg
        (fun z ↦ ((restrictFunctor f).obj (A j.as)).val.map i z)
        (ConcreteCategory.congr_hom
          (restrictProductLiftApp_comp_sectionsIso_hom_π f A a W j.as) x).symm

/-- Projecting an assembled restricted-product map recovers the chosen
component. -/
@[reassoc (attr := simp)]
lemma restrictProductLift_π (f : X ⟶ Y) [IsOpenImmersion f]
    (A : J → Y.Modules) (a : ∀ j, P ⟶ (restrictFunctor f).obj (A j))
    (j : J) :
    restrictProductLift f A a ≫ (restrictFunctor f).map (Pi.π A j) = a j := by
  apply Modules.hom_ext
  intro W
  ext x
  change ((restrictProductLiftApp f A a (op W) ≫
        ((restrictFunctor f).map (Pi.π A j)).val.app (op W)) x) = _
  rw [← restrictProductSectionsIso_hom_π]
  exact ConcreteCategory.congr_hom
    (restrictProductLiftApp_comp_sectionsIso_hom_π f A a (op W) j) x

end RestrictedProducts

end AlgebraicGeometry.Scheme.Modules
