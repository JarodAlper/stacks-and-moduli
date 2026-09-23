module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Local essential surjectivity of based functors

This file records the covering-sieve form of local essential surjectivity for a
functor between categories over a site.  It also packages the usual local criterion
for a morphism of prestacks to exhibit its target as a stackification, and proves
that such a local stackification preserves and reflects faithful projection to the
base.
-/

@[expose] public section

open CategoryTheory Functor

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

/-- A category fibered in groupoids whose fiber categories are thin has faithful
projection to the base. -/
theorem Functor.faithful_of_fiberwise_thin
    {C : Type u} [Category.{v} C]
    {X : Type u₁} [Category.{v₁} X] (p : X ⥤ C)
    [p.IsFiberedInGroupoids]
    (h : ∀ S : C, Quiver.IsThin (p.Fiber S)) : p.Faithful := by
  classical
  constructor
  intro a b alpha beta hab
  let R : C := p.obj a
  let g : R ⟶ p.obj b := p.map alpha
  let _ : IsHomLift p g beta := by
    change IsHomLift p (p.map alpha) beta
    rw [hab]
    exact IsHomLift.map beta
  let delta : a ⟶ a :=
    IsStronglyCartesian.map p g alpha (Category.id_comp g).symm beta
  let hdelta : IsHomLift p (𝟙 R) delta :=
    IsStronglyCartesian.map_isHomLift p g alpha
      (Category.id_comp g).symm beta
  let aa : p.Fiber R := Fiber.mk rfl
  let delta' : aa ⟶ aa := ⟨delta, hdelta⟩
  let _ : Quiver.IsThin (p.Fiber R) := h R
  have hdeltaid : delta' = 𝟙 aa := Subsingleton.elim _ _
  have hdelta_underlying : delta = 𝟙 a :=
    congrArg Fiber.fiberInclusion.map hdeltaid
  calc
    alpha = 𝟙 a ≫ alpha := (Category.id_comp alpha).symm
    _ = delta ≫ alpha := by rw [hdelta_underlying]
    _ = beta := IsStronglyCartesian.fac p g alpha
      (Category.id_comp g).symm beta

end CategoryTheory

namespace CategoryTheory.BasedFunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₂, u₂} C}
  (F : X ⥤ᵇ Y)

/-- A based functor is locally essentially surjective when every target object is
covered by arrows that lift to objects in its image. For prestacks, a hom lift is
cartesian, so this says precisely that the target object is locally isomorphic to an
object in the image. -/
def IsLocallyEssentiallySurjective : Prop :=
  ∀ y : Y.obj, ∃ R : Sieve (Y.p.obj y), R ∈ J (Y.p.obj y) ∧
    ∀ {T : C} (f : T ⟶ Y.p.obj y), R f →
      ∃ (x : X.obj) (q : F.obj x ⟶ y), Y.p.IsHomLift f q

/-- The local-equivalence criterion for a morphism to exhibit its target as a
stackification: the target is a stack, the morphism is fully faithful, and every
target object is locally in its essential image. -/
structure IsLocalStackification : Prop where
  /-- The target is a stack. -/
  isStack : BasedCategory.IsStack J Y
  /-- The morphism is full. -/
  full : F.toFunctor.Full
  /-- The morphism is faithful. -/
  faithful : F.toFunctor.Faithful
  /-- Every target object is locally in the essential image. -/
  locallyEssentiallySurjective : F.IsLocallyEssentiallySurjective (J := J)

/-- A full, locally essentially surjective morphism from a category fibered in sets
to a stack forces the target to be fibered in sets. -/
theorem projection_faithful_of_full_locallyEssentiallySurjective
    [X.p.IsFiberedInGroupoids] [X.p.Faithful]
    [BasedCategory.IsStack J Y] [F.toFunctor.Full]
    (hlocal : F.IsLocallyEssentiallySurjective (J := J)) :
    Y.p.Faithful := by
  let _ : Y.p.IsFiberedInGroupoids :=
    (inferInstance : BasedCategory.IsStack J Y).isFiberedInGroupoids
  apply Y.p.faithful_of_fiberwise_thin
  intro S a b
  constructor
  intro phi psi
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, hb⟩
  apply Fiber.hom_ext
  obtain ⟨R, hR, hlift⟩ := hlocal a
  apply Functor.IsStack.hom_ext_of_cover hR rfl hb phi.2 psi.2
  intro T q hq z xi hxi
  obtain ⟨x, ell, hell⟩ := hlift q hq
  let _ : IsHomLift Y.p q ell := hell
  let _ : IsStronglyCartesian Y.p q ell :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p q ell
  let kappa : z ⟶ F.obj x :=
    IsStronglyCartesian.map Y.p q ell (Category.id_comp q).symm xi
  have hkappa : kappa ≫ ell = xi :=
    IsStronglyCartesian.fac Y.p q ell (Category.id_comp q).symm xi
  have hphi : IsHomLift Y.p q (ell ≫ phi.1) := by
    let _ : IsHomLift Y.p (𝟙 (Y.p.obj a)) phi.1 := phi.2
    simpa only [Category.comp_id] using
      IsHomLift.comp Y.p q (𝟙 (Y.p.obj a)) ell phi.1
  have hpsi : IsHomLift Y.p q (ell ≫ psi.1) := by
    let _ : IsHomLift Y.p (𝟙 (Y.p.obj a)) psi.1 := psi.2
    simpa only [Category.comp_id] using
      IsHomLift.comp Y.p q (𝟙 (Y.p.obj a)) ell psi.1
  let _ : IsHomLift Y.p q (ell ≫ psi.1) := hpsi
  let _ : IsStronglyCartesian Y.p q (ell ≫ psi.1) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
      Y.p q (ell ≫ psi.1)
  let _ : IsHomLift Y.p q (ell ≫ phi.1) := hphi
  let delta : F.obj x ⟶ F.obj x :=
    IsStronglyCartesian.map Y.p q (ell ≫ psi.1)
      (Category.id_comp q).symm (ell ≫ phi.1)
  have hdelta : IsHomLift Y.p (𝟙 T) delta :=
    IsStronglyCartesian.map_isHomLift Y.p q (ell ≫ psi.1)
      (Category.id_comp q).symm (ell ≫ phi.1)
  have hfac : delta ≫ (ell ≫ psi.1) = ell ≫ phi.1 :=
    IsStronglyCartesian.fac Y.p q (ell ≫ psi.1)
      (Category.id_comp q).symm (ell ≫ phi.1)
  let hx : X.p.obj x = T :=
    (F.w_obj x).symm.trans (IsHomLift.domain_eq Y.p q ell)
  let xT : X.p.Fiber T := ⟨x, hx⟩
  let deltaT : (F.onFiber T).obj xT ⟶ (F.onFiber T).obj xT :=
    ⟨delta, hdelta⟩
  let _ : (F.onFiber T).Full := F.onFiber_full T
  let deltaPre : xT ⟶ xT := (F.onFiber T).preimage deltaT
  have hdeltaPre : deltaPre = 𝟙 xT := by
    apply Fiber.hom_ext
    apply X.p.map_injective
    let _ : IsHomLift X.p (𝟙 T) deltaPre.1 := deltaPre.2
    change X.p.map deltaPre.1 = X.p.map (𝟙 xT.1)
    rw [IsHomLift.fac' X.p (𝟙 T) deltaPre.1]
    simp
  have hdeltaT : deltaT = 𝟙 ((F.onFiber T).obj xT) := by
    calc
      deltaT = (F.onFiber T).map deltaPre :=
        ((F.onFiber T).map_preimage deltaT).symm
      _ = (F.onFiber T).map (𝟙 xT) := by rw [hdeltaPre]
      _ = 𝟙 ((F.onFiber T).obj xT) := (F.onFiber T).map_id xT
  have hdelta_underlying : delta = 𝟙 (F.obj x) :=
    congrArg Fiber.fiberInclusion.map hdeltaT
  calc
    xi ≫ phi.1 = (kappa ≫ ell) ≫ phi.1 := by rw [hkappa]
    _ = kappa ≫ (ell ≫ phi.1) := Category.assoc _ _ _
    _ = kappa ≫ (delta ≫ (ell ≫ psi.1)) := by rw [hfac]
    _ = kappa ≫ (ell ≫ psi.1) := by
      rw [hdelta_underlying, Category.id_comp]
    _ = (kappa ≫ ell) ≫ psi.1 := (Category.assoc _ _ _).symm
    _ = xi ≫ psi.1 := by rw [hkappa]

/-- A faithful based functor to a category fibered in sets has source fibered in
sets. -/
theorem source_projection_faithful_of_faithful
    [F.toFunctor.Faithful] [Y.p.Faithful] : X.p.Faithful := by
  constructor
  intro a b phi psi hbase
  apply F.toFunctor.map_injective
  apply Y.p.map_injective
  have hphi := Functor.congr_hom F.w phi
  have hpsi := Functor.congr_hom F.w psi
  simp only [Functor.comp_map] at hphi hpsi
  rw [hphi, hpsi, hbase]

/-- A local stackification has faithful source projection exactly when its target
projection is faithful. -/
theorem IsLocalStackification.projection_faithful_iff
    {F : X ⥤ᵇ Y} (hF : F.IsLocalStackification (J := J))
    [X.p.IsFiberedInGroupoids] : X.p.Faithful ↔ Y.p.Faithful := by
  constructor
  · intro hX
    let _ : X.p.Faithful := hX
    let _ : BasedCategory.IsStack J Y := hF.isStack
    let _ : F.toFunctor.Full := hF.full
    exact F.projection_faithful_of_full_locallyEssentiallySurjective
      hF.locallyEssentiallySurjective
  · intro hY
    let _ : Y.p.Faithful := hY
    let _ : F.toFunctor.Faithful := hF.faithful
    exact F.source_projection_faithful_of_faithful

end CategoryTheory.BasedFunctor
