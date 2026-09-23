module

public import StacksAndModuli.API.AlgebraicSpaceEtaleLocal
public import StacksAndModuli.API.FaithfulStackComponents
public import StacksAndModuli.API.FiberProductSmallSheafRepresentation
public import StacksAndModuli.API.IsomPresheafStack
public import StacksAndModuli.API.RepresentedSecondFiberBaseChange
public import StacksAndModuli.API.SchemeRepresentableSheafDescent
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6-isom-presheaves»

/-!
# Representability from one surjective étale base change

This file records the local-to-global step used in smooth descent of representable
morphisms.  A stack over a scheme which becomes a scheme after one surjective étale
base change is represented by an algebraic space.  The proof first descends the
set-valued condition, then shrinks the sheaf of fiberwise connected components, and
finally descends an algebraic-space presentation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

/-- A category fibered in groupoids whose fiber categories are thin has faithful
projection to the base. -/
theorem Functor.faithful_of_thin_fibers
    {C : Type u₁} [Category.{v₁} C]
    {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
    [p.IsFiberedInGroupoids]
    (h : ∀ S : C, Quiver.IsThin (p.Fiber S)) : p.Faithful := by
  classical
  constructor
  intro a b α β hαβ
  let R : C := p.obj a
  let g : R ⟶ p.obj b := p.map α
  haveI hβ : IsHomLift p g β := by
    change IsHomLift p (p.map α) β
    rw [hαβ]
    exact IsHomLift.map β
  let δ : a ⟶ a :=
    IsStronglyCartesian.map p g α (Category.id_comp g).symm β
  haveI hδ : IsHomLift p (𝟙 R) δ :=
    IsStronglyCartesian.map_isHomLift p g α
      (Category.id_comp g).symm β
  let aa : p.Fiber R := Fiber.mk rfl
  let δ' : aa ⟶ aa := ⟨δ, hδ⟩
  let _ : Quiver.IsThin (p.Fiber R) := h R
  have hδid : δ' = 𝟙 aa := Subsingleton.elim _ _
  have hδ_underlying : δ = 𝟙 a :=
    congrArg Fiber.fiberInclusion.map hδid
  calc
    α = 𝟙 a ≫ α := (Category.id_comp α).symm
    _ = δ ≫ α := by rw [hδ_underlying]
    _ = β := IsStronglyCartesian.fac p g α
      (Category.id_comp g).symm β

namespace Functor.IsStack

/-- A stack has faithful projection if every Isom presheaf becomes subterminal after
restriction along some singleton cover. -/
theorem projection_faithful_of_locally_subsingleton_isomPresheaf
    {C : Type u₁} [Category.{v₁} C]
    (X : BasedCategory.{v₂, u₂} C)
    {J : GrothendieckTopology C} [BasedCategory.IsStack J X]
    (hlocal : ∀ (S : C) (a b : X.p.Fiber S),
      let terminal : Over S := Over.mk (𝟙 S)
      ∃ (Z : Over S) (q : Z ⟶ terminal),
        Sieve.generate (Presieve.singleton q) ∈ (J.over S) terminal ∧
          Subsingleton
            ((BasedCategory.isomPresheaf (𝒳 := X) a b).obj (op Z))) :
    X.p.Faithful := by
  apply X.p.faithful_of_thin_fibers
  intro S
  intro a b
  constructor
  intro φ ψ
  let terminal : Over S := Over.mk (𝟙 S)
  obtain ⟨Z, k, hkcover, hthin⟩ := hlocal S a b
  have hsep :=
    (((isSheaf_iff_isSheaf_of_type _ _).mp
      (BasedCategory.isomPresheaf_isSheaf (𝒳 := X) a b)).isSheafFor
        (Presieve.singleton k) hkcover).isSeparatedFor
  let πa : BasedCategory.pullbackFiberObj a terminal ⟶ a :=
    ⟨IsPreFibered.pullbackMap a.2 terminal.hom, by
      change X.p.IsHomLift terminal.hom _
      infer_instance⟩
  let πb : BasedCategory.pullbackFiberObj b terminal ⟶ b :=
    ⟨IsPreFibered.pullbackMap b.2 terminal.hom, by
      change X.p.IsHomLift terminal.hom _
      infer_instance⟩
  let _ : IsIso πa := inferInstance
  let _ : IsIso πb := inferInstance
  let φ' : BasedCategory.pullbackFiberObj a terminal ⟶
      BasedCategory.pullbackFiberObj b terminal :=
    πa ≫ φ ≫ (asIso πb).inv
  let ψ' : BasedCategory.pullbackFiberObj a terminal ⟶
      BasedCategory.pullbackFiberObj b terminal :=
    πa ≫ ψ ≫ (asIso πb).inv
  have hrestrict :
      (BasedCategory.isomPresheaf (𝒳 := X) a b).map k.op φ' =
        (BasedCategory.isomPresheaf (𝒳 := X) a b).map k.op ψ' := by
    exact hthin.elim _ _
  have hglobal : φ' = ψ' :=
    (Presieve.isSeparatedFor_singleton.mp hsep) hrestrict
  dsimp only [φ', ψ'] at hglobal
  rw [← cancel_epi πa, ← cancel_mono (asIso πb).inv]
  simpa only [Category.assoc] using hglobal

end Functor.IsStack

end CategoryTheory

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
  (F : Xcat ⥤ᵇ Ycat) {T : Scheme.{u}} (g : overBased T ⥤ᵇ Ycat)

/-- The structural morphism to the test scheme carried by an object of a
scheme-valued fiber. -/
def fiberSecondHom {R : Scheme.{u}}
    (a : (fiberProduct F g).p.Fiber R) : R ⟶ T :=
  eqToHom a.2.symm ≫ eqToHom a.1.over_eq.symm ≫ a.1.snd.hom

/-- The structural morphism of a fiber object is compatible with any morphism
between fiber objects lying over a specified base morphism. -/
theorem fiberSecondHom_naturality {R S : Scheme.{u}}
    (a : (fiberProduct F g).p.Fiber R)
    (b : (fiberProduct F g).p.Fiber S) (f : R ⟶ S)
    (phi : a.1 ⟶ b.1) (hphi : IsHomLift (fiberProduct F g).p f phi) :
    fiberSecondHom F g a = f ≫ fiberSecondHom F g b := by
  have hsnd : IsHomLift (overBased T).p f phi.snd :=
    FiberProductHom.isHomLift_snd phi f hphi
  let ha : (overBased T).p.obj a.1.snd = R := a.1.over_eq.trans a.2
  let hb : (overBased T).p.obj b.1.snd = S := b.1.over_eq.trans b.2
  have hbase : phi.snd.left = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
    exact Eq.trans rfl (IsHomLift.fac' (overBased T).p f phi.snd)
  dsimp only [fiberSecondHom]
  rw [← Over.w phi.snd]
  simp only [eqToHom_trans]
  rw [hbase]
  simp [ha, hb]

/-- Pulling a fiber object back along a scheme morphism precomposes its
structural morphism by that scheme morphism. -/
theorem fiberSecondHom_pullbackFiberObj {R : Scheme.{u}}
    (a : (fiberProduct F g).p.Fiber R) (Z : Over R) :
    fiberSecondHom F g (pullbackFiberObj a Z) =
      Z.hom ≫ fiberSecondHom F g a := by
  let phi : (pullbackFiberObj a Z).1 ⟶ a.1 :=
    IsPreFibered.pullbackMap a.2 Z.hom
  have hphi : IsHomLift (fiberProduct F g).p Z.hom phi := inferInstance
  exact fiberSecondHom_naturality F g (pullbackFiberObj a Z) a Z.hom phi hphi

/-- The canonical comparison in `Sch/T` attached to a factorization of a fiber
object's structural morphism. -/
noncomputable def localFiberOverIso {R S : Scheme.{u}} (q : S ⟶ T)
    (a : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hl : l ≫ q = fiberSecondHom F g a) :
    (overBased.map q).obj (Over.mk l) ≅ a.1.snd := by
  dsimp only [fiberSecondHom] at hl
  exact Over.isoMk (eqToIso (a.2.symm.trans a.1.over_eq.symm)) (by
    change eqToHom (a.2.symm.trans a.1.over_eq.symm) ≫
      a.1.snd.hom = l ≫ q
    rw [← eqToHom_trans]
    simpa only [Category.assoc] using hl.symm)

theorem localFiberOverIso_inv_isHomLift {R S : Scheme.{u}} (q : S ⟶ T)
    (a : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hl : l ≫ q = fiberSecondHom F g a) :
    IsHomLift (overBased T).p (𝟙 R)
      (localFiberOverIso F g q a l hl).inv := by
  apply IsHomLift.of_fac' (overBased T).p (𝟙 R)
    (localFiberOverIso F g q a l hl).inv
    (a.1.over_eq.trans a.2) rfl
  change (eqToIso (a.2.symm.trans a.1.over_eq.symm)).inv =
    eqToHom (a.1.over_eq.trans a.2)
  simp

theorem localFiberOverIso_hom_isHomLift {R S : Scheme.{u}} (q : S ⟶ T)
    (a : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hl : l ≫ q = fiberSecondHom F g a) :
    IsHomLift (overBased T).p (𝟙 R)
      (localFiberOverIso F g q a l hl).hom := by
  let e := localFiberOverIso F g q a l hl
  haveI : IsHomLift (overBased T).p (𝟙 R) e.symm.hom := by
    change IsHomLift (overBased T).p (𝟙 R) e.inv
    exact localFiberOverIso_inv_isHomLift F g q a l hl
  change IsHomLift (overBased T).p (𝟙 R) e.symm.inv
  infer_instance

/-- An object of a scheme-valued fiber whose structural map factors through a
base-change morphism, regarded as an object of the base-changed fiber. -/
noncomputable def localFiberObj {R S : Scheme.{u}} (q : S ⟶ T)
    (a : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hl : l ≫ q = fiberSecondHom F g a) :
    (fiberProduct F ((overBased.map q).comp g)).p.Fiber R := by
  let e := localFiberOverIso F g q a l hl
  refine ⟨
    { fst := a.1.fst
      snd := Over.mk l
      over_eq := a.2.symm
      iso := a.1.iso ≪≫ (g.toFunctor.mapIso e).symm
      isHomLift := ?_ }, a.2⟩
  have ha : IsHomLift Ycat.p (𝟙 (Xcat.p.obj a.1.fst)) a.1.iso.hom :=
    a.1.isHomLift
  have he : IsHomLift (overBased T).p
      (𝟙 (Xcat.p.obj a.1.fst)) e.inv := by
    apply IsHomLift.of_fac' (overBased T).p
      (𝟙 (Xcat.p.obj a.1.fst)) e.inv a.1.over_eq a.2.symm
    change (eqToIso (a.2.symm.trans a.1.over_eq.symm)).inv =
      eqToHom a.1.over_eq ≫ eqToHom a.2
    simp
  have hge : IsHomLift Ycat.p
      (𝟙 (Xcat.p.obj a.1.fst)) (g.map e.inv) :=
    g.preserves_isHomLift _ e.inv
  have hcomp : IsHomLift Ycat.p
      ((𝟙 (Xcat.p.obj a.1.fst)) ≫
        (𝟙 (Xcat.p.obj a.1.fst)))
      (a.1.iso.hom ≫ g.map e.inv) := by
    exact IsHomLift.comp _ _ _ _ _
  simpa [e] using hcomp

/-- Forgetting the lifted factorization of a local fiber object returns an
object in the same connected component as the original fiber object. -/
noncomputable def localFiberObjForgetHom {R S : Scheme.{u}} (q : S ⟶ T)
    (a : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hl : l ≫ q = fiberSecondHom F g a) :
    ((fiberProductRightMap F g (overBased.map q)).onFiber R).obj
        (localFiberObj F g q a l hl) ⟶ a := by
  let e := localFiberOverIso F g q a l hl
  let inner :
      ((fiberProductRightMap F g (overBased.map q)).obj
        (localFiberObj F g q a l hl).1) ⟶ a.1 :=
    { fst := 𝟙 a.1.fst
      snd := e.hom
      isHomLift := by
        apply IsHomLift.of_fac' (overBased T).p
          (Xcat.p.map (𝟙 a.1.fst)) e.hom a.2.symm a.1.over_eq
        dsimp only [e, localFiberOverIso]
        simp
      w := by
        dsimp only [localFiberObj, e]
        change F.map (𝟙 a.1.fst) ≫ a.1.iso.hom =
          (a.1.iso.hom ≫ g.map e.inv) ≫ g.map e.hom
        rw [F.toFunctor.map_id, Category.id_comp, Category.assoc,
          ← g.toFunctor.map_comp]
        simp }
  have hinner : IsHomLift (fiberProduct F g).p (𝟙 R) inner := by
    apply FiberProductHom.isHomLift_of_fst inner (𝟙 R)
    exact IsHomLift.id a.2
  exact ⟨inner, hinner⟩

/-- A vertical morphism between two fiber objects whose structural maps use the
same lift through the base-change scheme induces a vertical morphism in the
base-changed fiber. -/
noncomputable def localFiberHom {R S : Scheme.{u}} (q : S ⟶ T)
    (a b : (fiberProduct F g).p.Fiber R) (l : R ⟶ S)
    (hla : l ≫ q = fiberSecondHom F g a)
    (hlb : l ≫ q = fiberSecondHom F g b) (phi : a ⟶ b) :
    localFiberObj F g q a l hla ⟶ localFiberObj F g q b l hlb := by
  let phi' := Fiber.fiberInclusion.map phi
  let ea := localFiberOverIso F g q a l hla
  let eb := localFiberOverIso F g q b l hlb
  let snd : Over.mk l ⟶ Over.mk l := 𝟙 _
  have hsnd : IsHomLift (overBased S).p
      (Xcat.p.map phi'.fst) snd := by
    apply IsHomLift.of_fac (overBased S).p
      (Xcat.p.map phi'.fst) snd a.2.symm b.2.symm
    have hphi : IsHomLift (fiberProduct F g).p (𝟙 R) phi' := phi.2
    have hfst : IsHomLift Xcat.p (𝟙 R) phi'.fst :=
      FiberProductHom.isHomLift_fst phi' (𝟙 R) hphi
    have hbase := IsHomLift.fac' Xcat.p (𝟙 R) phi'.fst
    simpa [snd] using hbase
  let inner : (localFiberObj F g q a l hla).1 ⟶
      (localFiberObj F g q b l hlb).1 :=
    { fst := phi'.fst
      snd := snd
      isHomLift := hsnd
      w := by
        dsimp only [localFiberObj, ea, eb, snd]
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
        rw [((overBased.map q).comp g).toFunctor.map_id, Category.comp_id]
        rw [← Category.assoc]
        have hover : phi'.snd ≫
            (localFiberOverIso F g q b l hlb).inv =
              (localFiberOverIso F g q a l hla).inv := by
          have hphi : IsHomLift (fiberProduct F g).p (𝟙 R) phi' := phi.2
          letI hphisnd : IsHomLift (overBased T).p (𝟙 R) phi'.snd :=
            FiberProductHom.isHomLift_snd phi' (𝟙 R) hphi
          letI heb : IsHomLift (overBased T).p (𝟙 R)
              (localFiberOverIso F g q b l hlb).inv :=
            localFiberOverIso_inv_isHomLift F g q b l hlb
          letI hea : IsHomLift (overBased T).p (𝟙 R)
              (localFiberOverIso F g q a l hla).inv :=
            localFiberOverIso_inv_isHomLift F g q a l hla
          letI hcomp : IsHomLift (overBased T).p (𝟙 R)
              (phi'.snd ≫ (localFiberOverIso F g q b l hlb).inv) := by
            simpa using IsHomLift.comp (overBased T).p
              (𝟙 R) (𝟙 R) phi'.snd
                (localFiberOverIso F g q b l hlb).inv
          exact hom_ext_of_faithful_of_isHomLift
            (overBased T).p (𝟙 R) _ _
        calc
          (F.map phi'.fst ≫ b.1.iso.hom) ≫
              g.map (localFiberOverIso F g q b l hlb).inv =
              (a.1.iso.hom ≫ g.map phi'.snd) ≫
                g.map (localFiberOverIso F g q b l hlb).inv :=
            congrArg (fun k ↦ k ≫
              g.map (localFiberOverIso F g q b l hlb).inv) phi'.w
          _ = a.1.iso.hom ≫ g.map
              (phi'.snd ≫ (localFiberOverIso F g q b l hlb).inv) := by
            rw [Category.assoc, ← g.toFunctor.map_comp]
          _ = a.1.iso.hom ≫
              g.map (localFiberOverIso F g q a l hla).inv := by rw [hover] }
  have hinner : IsHomLift
      (fiberProduct F ((overBased.map q).comp g)).p (𝟙 R) inner := by
    apply FiberProductHom.isHomLift_of_fst inner (𝟙 R)
    have hphi : IsHomLift (fiberProduct F g).p (𝟙 R) phi' := phi.2
    exact FiberProductHom.isHomLift_fst phi' (𝟙 R) hphi
  exact ⟨inner, hinner⟩

/-- A prestack equivalent over schemes to a representable prestack has faithful
projection. -/
theorem projection_faithful_of_scheme_representation
    {Zcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    (W : Scheme.{u}) (K : overBased W ⥤ᵇ Zcat)
    (hK : K.toFunctor.IsEquivalence) : Zcat.p.Faithful := by
  let _ : K.toFunctor.IsEquivalence := hK
  apply Zcat.p.faithful_of_comp_essSurj K.toFunctor
  intro x y phi psi h
  obtain ⟨phi', hphi'⟩ := K.toFunctor.map_surjective phi
  obtain ⟨psi', hpsi'⟩ := K.toFunctor.map_surjective psi
  rw [← hphi', ← hpsi']
  apply congrArg K.toFunctor.map
  apply (overBased W).p.map_injective
  have hwphi := Functor.congr_hom K.w phi'
  have hwpsi := Functor.congr_hom K.w psi'
  simp only [Functor.comp_map] at hwphi hwpsi
  rw [hphi'] at hwphi
  rw [hpsi'] at hwpsi
  rw [hwphi, hwpsi] at h
  simpa only [cancel_epi, cancel_mono] using h

/-- A prestack represented by a presheaf has faithful projection to the base. -/
theorem projection_faithful_of_presheaf_representation
    {A : Scheme.{u}ᵒᵖ ⥤ Type u}
    {Zcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    (K : ofPresheaf A ⥤ᵇ Zcat)
    (hK : K.toFunctor.IsEquivalence) : Zcat.p.Faithful := by
  let _ : K.toFunctor.IsEquivalence := hK
  apply Zcat.p.faithful_of_comp_essSurj K.toFunctor
  intro x y phi psi h
  obtain ⟨phi', hphi'⟩ := K.toFunctor.map_surjective phi
  obtain ⟨psi', hpsi'⟩ := K.toFunctor.map_surjective psi
  rw [← hphi', ← hpsi']
  apply congrArg K.toFunctor.map
  apply (ofPresheaf A).p.map_injective
  have hwphi := Functor.congr_hom K.w phi'
  have hwpsi := Functor.congr_hom K.w psi'
  simp only [Functor.comp_map] at hwphi hwpsi
  rw [hphi'] at hwphi
  rw [hpsi'] at hwpsi
  rw [hwphi, hwpsi] at h
  simpa only [cancel_epi, cancel_mono] using h

/-- The connected components of each fiber of a prestack represented by a
scheme form a universe-small type. -/
theorem small_connectedComponents_of_scheme_representation
    {Zcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    [Zcat.p.IsFiberedInGroupoids]
    (W : Scheme.{u}) (K : overBased W ⥤ᵇ Zcat)
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) :
    Small.{u} (CategoryTheory.ConnectedComponents (Zcat.p.Fiber R)) := by
  let _ : K.toFunctor.IsEquivalence := hK
  let _ : (K.onFiber R).EssSurj := onFiber_essSurj_of_essSurj K R
  let codeToComponent : (overBased W).p.Fiber R →
      CategoryTheory.ConnectedComponents (Zcat.p.Fiber R) := fun x ↦
    CategoryTheory.ConnectedComponents.mk ((K.onFiber R).obj x)
  have hsurj : Function.Surjective codeToComponent := by
    intro j
    let b := componentRepresentative (𝒳 := Zcat) j
    let x := (K.onFiber R).objPreimage b
    let e := (K.onFiber R).objObjPreimageIso b
    refine ⟨x, ?_⟩
    calc
      CategoryTheory.ConnectedComponents.mk ((K.onFiber R).obj x) =
          CategoryTheory.ConnectedComponents.mk b :=
        Quotient.sound' (Zigzag.of_hom e.hom)
      _ = j := componentRepresentative_component j
  let _ : Small.{u} ((overBased W).p.Fiber R) :=
    small_fiber_overBased W R
  exact small_of_surjective hsurj

/-- The connected components of each fiber of a prestack represented by a
universe-small presheaf form a universe-small type. -/
theorem small_connectedComponents_of_presheaf_representation
    {A : Scheme.{u}ᵒᵖ ⥤ Type u}
    {Zcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    [Zcat.p.IsFiberedInGroupoids]
    (K : ofPresheaf A ⥤ᵇ Zcat)
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) :
    Small.{u} (CategoryTheory.ConnectedComponents (Zcat.p.Fiber R)) := by
  let _ : K.toFunctor.IsEquivalence := hK
  let _ : (K.onFiber R).EssSurj := onFiber_essSurj_of_essSurj K R
  let codeToComponent : (ofPresheaf A).p.Fiber R →
      CategoryTheory.ConnectedComponents (Zcat.p.Fiber R) := fun x ↦
    CategoryTheory.ConnectedComponents.mk ((K.onFiber R).obj x)
  have hsurj : Function.Surjective codeToComponent := by
    intro j
    let b := componentRepresentative (𝒳 := Zcat) j
    let x := (K.onFiber R).objPreimage b
    let e := (K.onFiber R).objObjPreimageIso b
    refine ⟨x, ?_⟩
    calc
      CategoryTheory.ConnectedComponents.mk ((K.onFiber R).obj x) =
          CategoryTheory.ConnectedComponents.mk b :=
        Quotient.sound' (Zigzag.of_hom e.hom)
      _ = j := componentRepresentative_component j
  let _ : Small.{u} ((ofPresheaf A).p.Fiber R) :=
    small_fiber_ofPresheaf A R
  exact small_of_surjective hsurj

/-- The chosen structural morphism associated to a connected component of a
scheme-valued fiber. -/
noncomputable def fiberComponentSecondHom (R : Scheme.{u})
    (j : CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber R)) : R ⟶ T :=
  fiberSecondHom F g (componentRepresentative (𝒳 := fiberProduct F g) j)

/-- Connected components with a fixed chosen structural morphism to the test
scheme. -/
abbrev FixedFiberComponent (R : Scheme.{u}) (f : R ⟶ T) :=
  { j : CategoryTheory.ConnectedComponents ((fiberProduct F g).p.Fiber R) //
    fiberComponentSecondHom F g R j = f }

/-- Restrict a component with structural morphism `f` to the pullback of a
base-change scheme and use its canonical lift to the base-changed fiber. -/
noncomputable def fixedFiberComponentRestriction {S : Scheme.{u}}
    (q : S ⟶ T) (R : Scheme.{u}) (f : R ⟶ T)
    (j : FixedFiberComponent F g R f) :
    CategoryTheory.ConnectedComponents
      ((fiberProduct F ((overBased.map q).comp g)).p.Fiber
        (pullback f q)) := by
  let a := componentRepresentative (𝒳 := fiberProduct F g) j.1
  let r : pullback f q ⟶ R := pullback.fst f q
  let l : pullback f q ⟶ S := pullback.snd f q
  let a' := pullbackFiberObj a (Over.mk r)
  have hl : l ≫ q = fiberSecondHom F g a' := by
    rw [fiberSecondHom_pullbackFiberObj F g a (Over.mk r)]
    calc
      l ≫ q = r ≫ f := pullback.condition.symm
      _ = r ≫ fiberComponentSecondHom F g R j.1 := by rw [j.2]
      _ = r ≫ fiberSecondHom F g a := rfl
  exact CategoryTheory.ConnectedComponents.mk
    (localFiberObj F g q a' l hl)

/-- Restriction to a surjective étale base change detects connected
components with a fixed structural morphism. -/
theorem fixedFiberComponentRestriction_injective
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {S : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q) (R : Scheme.{u}) (f : R ⟶ T) :
    Function.Injective (fixedFiberComponentRestriction F g q R f) := by
  let _ : Etale q := hqEtale
  let _ : Surjective q := hqSurjective
  let H := fiberProduct F g
  let Hq := fiberProduct F ((overBased.map q).comp g)
  let C := fiberComponents (𝒳 := H)
  let P := pullback f q
  let r : P ⟶ R := pullback.fst f q
  let l : P ⟶ S := pullback.snd f q
  let Q := fiberProductRightMap F g (overBased.map q)
  have hrEtale : Etale r := by
    dsimp only [r]
    infer_instance
  have hrSurjective : Surjective r := by
    dsimp only [r]
    infer_instance
  let _ : Etale r := hrEtale
  let _ : Surjective r := hrSurjective
  have hcover : Sieve.generate (Presieve.singleton r) ∈
      Scheme.etaleTopology R :=
    Scheme.generate_singleton_mem_etaleTopology_of_smooth r
  have hsep := ((fiberComponents_isSheaf
    (J := Scheme.etaleTopology) (X := H)).isSheafFor
      (Presieve.singleton r) hcover).isSeparatedFor
  intro j k hjk
  have hlocal := congrArg (Functor.mapConnectedComponents (Q.onFiber P)) hjk
  have hj : C.map r.op j.1 =
      (Q.onFiber P).mapConnectedComponents
        (fixedFiberComponentRestriction F g q R f j) := by
    let a := componentRepresentative (𝒳 := H) j.1
    let a' := pullbackFiberObj a (Over.mk r)
    have hl : l ≫ q = fiberSecondHom F g a' := by
      rw [fiberSecondHom_pullbackFiberObj F g a (Over.mk r)]
      calc
        l ≫ q = r ≫ f := pullback.condition.symm
        _ = r ≫ fiberComponentSecondHom F g R j.1 := by rw [j.2]
        _ = r ≫ fiberSecondHom F g a := rfl
    rw [← componentRepresentative_component (𝒳 := H) j.1]
    change CategoryTheory.ConnectedComponents.mk a' =
      CategoryTheory.ConnectedComponents.mk
        ((Q.onFiber P).obj (localFiberObj F g q a' l hl))
    exact (Quotient.sound'
      (Zigzag.of_hom (localFiberObjForgetHom F g q a' l hl))).symm
  have hk : C.map r.op k.1 =
      (Q.onFiber P).mapConnectedComponents
        (fixedFiberComponentRestriction F g q R f k) := by
    let a := componentRepresentative (𝒳 := H) k.1
    let a' := pullbackFiberObj a (Over.mk r)
    have hl : l ≫ q = fiberSecondHom F g a' := by
      rw [fiberSecondHom_pullbackFiberObj F g a (Over.mk r)]
      calc
        l ≫ q = r ≫ f := pullback.condition.symm
        _ = r ≫ fiberComponentSecondHom F g R k.1 := by rw [k.2]
        _ = r ≫ fiberSecondHom F g a := rfl
    rw [← componentRepresentative_component (𝒳 := H) k.1]
    change CategoryTheory.ConnectedComponents.mk a' =
      CategoryTheory.ConnectedComponents.mk
        ((Q.onFiber P).obj (localFiberObj F g q a' l hl))
    exact (Quotient.sound'
      (Zigzag.of_hom (localFiberObjForgetHom F g q a' l hl))).symm
  apply Subtype.ext
  apply Presieve.isSeparatedFor_singleton.mp hsep
  exact hj.trans (hlocal.trans hk.symm)

/-- Components with a fixed structural morphism are universe-small when the
corresponding étale base change is represented by a scheme. -/
theorem small_fixedFiberComponent_of_etale_scheme_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {S W : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : overBased W ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) (f : R ⟶ T) :
    Small.{u} (FixedFiberComponent F g R f) := by
  let _ : Small.{u} (CategoryTheory.ConnectedComponents
      ((fiberProduct F ((overBased.map q).comp g)).p.Fiber (pullback f q))) :=
    small_connectedComponents_of_scheme_representation W K hK (pullback f q)
  exact small_of_injective
    (f := fixedFiberComponentRestriction F g q R f)
    (fixedFiberComponentRestriction_injective F g q hqEtale hqSurjective R f)

/-- Components with a fixed structural morphism are universe-small when the
corresponding étale base change is represented by a small presheaf. -/
theorem small_fixedFiberComponent_of_etale_presheaf_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {A : Scheme.{u}ᵒᵖ ⥤ Type u} {S : Scheme.{u}}
    (q : S ⟶ T) (hqEtale : Etale q) (hqSurjective : Surjective q)
    (K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) (f : R ⟶ T) :
    Small.{u} (FixedFiberComponent F g R f) := by
  let _ : Small.{u} (CategoryTheory.ConnectedComponents
      ((fiberProduct F ((overBased.map q).comp g)).p.Fiber (pullback f q))) :=
    small_connectedComponents_of_presheaf_representation K hK (pullback f q)
  exact small_of_injective
    (f := fixedFiberComponentRestriction F g q R f)
    (fixedFiberComponentRestriction_injective F g q hqEtale hqSurjective R f)

/-- Every connected-component type of a stack over a scheme is universe-small
if one surjective étale base change is represented by a scheme. -/
theorem small_connectedComponents_of_etale_scheme_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {S W : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : overBased W ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) :
    Small.{u} (CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber R)) := by
  let Code := Σ f : R ⟶ T, FixedFiberComponent F g R f
  let _ : ∀ f : R ⟶ T, Small.{u} (FixedFiberComponent F g R f) :=
    fun f ↦ small_fixedFiberComponent_of_etale_scheme_baseChange
      F g q hqEtale hqSurjective K hK R f
  let _ : Small.{u} Code := by
    dsimp only [Code]
    infer_instance
  let decode : Code → CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber R) := fun c ↦ c.2.1
  apply small_of_surjective (f := decode)
  intro j
  exact ⟨⟨fiberComponentSecondHom F g R j, ⟨j, rfl⟩⟩, rfl⟩

/-- Every connected-component type of a stack over a scheme is universe-small
if one surjective étale base change is represented by a small presheaf. -/
theorem small_connectedComponents_of_etale_presheaf_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {A : Scheme.{u}ᵒᵖ ⥤ Type u} {S : Scheme.{u}}
    (q : S ⟶ T) (hqEtale : Etale q) (hqSurjective : Surjective q)
    (K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) (R : Scheme.{u}) :
    Small.{u} (CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber R)) := by
  let Code := Σ f : R ⟶ T, FixedFiberComponent F g R f
  let _ : ∀ f : R ⟶ T, Small.{u} (FixedFiberComponent F g R f) :=
    fun f ↦ small_fixedFiberComponent_of_etale_presheaf_baseChange
      F g q hqEtale hqSurjective K hK R f
  let _ : Small.{u} Code := by
    dsimp only [Code]
    infer_instance
  let decode : Code → CategoryTheory.ConnectedComponents
      ((fiberProduct F g).p.Fiber R) := fun c ↦ c.2.1
  apply small_of_surjective (f := decode)
  intro j
  exact ⟨⟨fiberComponentSecondHom F g R j, ⟨j, rfl⟩⟩, rfl⟩

/-- A faithful stack over schemes with universe-small fiberwise components has
a representation by a universe-small sheaf. -/
noncomputable def smallEtaleSheafRepresentation_of_smallComponents
    (Zcat : BasedCategory.{v₂, u₂} Scheme.{u})
    [Zcat.p.IsFiberedInGroupoids] [Zcat.p.Faithful]
    [BasedCategory.IsStack Scheme.etaleTopology Zcat]
    (hsmall : ∀ R : Scheme.{u}, Small.{u}
      (CategoryTheory.ConnectedComponents (Zcat.p.Fiber R))) :
    SmallEtaleSheafRepresentation Zcat := by
  let C := fiberComponents (𝒳 := Zcat)
  have hsmall' : FunctorToTypes.Small.{u} C := by
    intro R
    exact hsmall R.unop
  let _ : FunctorToTypes.Small.{u} C := hsmall'
  let X := FunctorToTypes.shrink.{u} C
  let E : ofPresheaf X ⥤ᵇ Zcat :=
    { toFunctor :=
        (CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor ⋙
          (componentPrestackComparison (𝒳 := Zcat)).toFunctor
      w := by
        rw [Functor.assoc, Functor.assoc,
          (componentPrestackComparison (𝒳 := Zcat)).w,
          (shrinkElementsComparison C).w]
        rfl }
  have hE : E.toFunctor.IsEquivalence := by
    have h₁ :=
      (CategoryOfElements.costructuredArrowYonedaEquivalence X).isEquivalence_inverse
    have h₂ := isEquivalence_shrinkElementsComparison C
    have h₃ := isEquivalence_componentPrestackComparison (𝒳 := Zcat)
    have h₁₂ :
        ((CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor).IsEquivalence :=
      Functor.isEquivalence_trans _ _
    exact Functor.isEquivalence_trans _ _
  exact
    { X := X
      isSheaf := FunctorToTypes.isSheaf_shrink C
        (fiberComponents_isSheaf (X := Zcat))
      representation := E
      representation_isEquivalence := hE }

/-- A stack-valued fiber which is represented by a scheme after one
surjective étale base change is represented globally by an algebraic space. -/
theorem exists_isAlgebraicSpace_of_etale_scheme_baseChange_of_faithful
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {S W : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : overBased W ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧
      (fiberProduct F g).IsRepresentedByPresheaf X := by
  let D := smallEtaleSheafRepresentation_of_smallComponents
    (fiberProduct F g)
    (small_connectedComponents_of_etale_scheme_baseChange
      F g q hqEtale hqSurjective K hK)
  let _ : D.representation.toFunctor.IsEquivalence :=
    D.representation_isEquivalence
  let _ : Etale q := hqEtale
  let _ : Surjective q := hqSurjective
  have hlocal : IsAlgebraicSpace
      (pullback
        (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map q)) := by
    obtain ⟨L, hL⟩ := isRepresentedByPresheaf_fiber_secondBaseChange
      F g D.representation q
    let _ : L.toFunctor.IsEquivalence := hL
    let K' := (ofPresheafYonedaToOverBased W).comp K
    have hK' : K'.toFunctor.IsEquivalence := by
      let _ : K.toFunctor.IsEquivalence := hK
      exact Functor.isEquivalence_trans
        (ofPresheafYonedaToOverBased W).toFunctor K.toFunctor
    let _ : K'.toFunctor.IsEquivalence := hK'
    exact IsAlgebraicSpace.of_iso (ofPresheaf.comparisonIso L K')
  let _ : IsAlgebraicSpace
      (pullback
        (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map q)) := hlocal
  have hX : IsAlgebraicSpace D.X :=
    IsAlgebraicSpace.of_etale_surjective_base_change D.isSheaf
      (representedFiberSecondBaseMap F g D.representation) q
  exact ⟨D.X, hX, D.representation, D.representation_isEquivalence⟩

/-- A stack-valued fiber which is represented by an algebraic space after one
surjective étale base change is represented globally by an algebraic space,
provided its projection is already known to be faithful. -/
theorem exists_isAlgebraicSpace_of_etale_presheaf_baseChange_of_faithful
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    [(fiberProduct F g).p.Faithful]
    {A : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace A]
    {S : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧
      (fiberProduct F g).IsRepresentedByPresheaf X := by
  let D := smallEtaleSheafRepresentation_of_smallComponents
    (fiberProduct F g)
    (small_connectedComponents_of_etale_presheaf_baseChange
      F g q hqEtale hqSurjective K hK)
  let _ : D.representation.toFunctor.IsEquivalence :=
    D.representation_isEquivalence
  let _ : Etale q := hqEtale
  let _ : Surjective q := hqSurjective
  have hlocal : IsAlgebraicSpace
      (pullback
        (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map q)) := by
    obtain ⟨L, hL⟩ := isRepresentedByPresheaf_fiber_secondBaseChange
      F g D.representation q
    let _ : L.toFunctor.IsEquivalence := hL
    let _ : K.toFunctor.IsEquivalence := hK
    exact IsAlgebraicSpace.of_iso (ofPresheaf.comparisonIso L K)
  let _ : IsAlgebraicSpace
      (pullback
        (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map q)) := hlocal
  have hX : IsAlgebraicSpace D.X :=
    IsAlgebraicSpace.of_etale_surjective_base_change D.isSheaf
      (representedFiberSecondBaseMap F g D.representation) q
  exact ⟨D.X, hX, D.representation, D.representation_isEquivalence⟩

/-- Faithfulness of a stack-valued fiber descends from a surjective étale base
change. -/
theorem projection_faithful_of_etale_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    {S : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (hHq : (fiberProduct F ((overBased.map q).comp g)).p.Faithful) :
    (fiberProduct F g).p.Faithful := by
  let _ : Etale q := hqEtale
  let _ : Surjective q := hqSurjective
  let Hq := fiberProduct F ((overBased.map q).comp g)
  let _ : Hq.p.Faithful := hHq
  apply Functor.IsStack.projection_faithful_of_locally_subsingleton_isomPresheaf
    (J := Scheme.etaleTopology) (fiberProduct F g)
  intro R a b
  let f := fiberSecondHom F g a
  let P := pullback f q
  let r : P ⟶ R := pullback.fst f q
  let l : P ⟶ S := pullback.snd f q
  let terminal : Over R := Over.mk (𝟙 R)
  let Z : Over R := Over.mk (r ≫ 𝟙 R)
  let k : Z ⟶ terminal := Over.homMk r
  have hrEtale : Etale r := by
    dsimp only [r]
    infer_instance
  have hrSurjective : Surjective r := by
    dsimp only [r]
    infer_instance
  let _ : Etale r := hrEtale
  let _ : Surjective r := hrSurjective
  refine ⟨Z, k, ?_, ?_⟩
  · simpa [Z, k, terminal] using
      Scheme.generate_singleton_mem_etaleTopology_over_of_smooth r (𝟙 R)
  · constructor
    intro phi psi
    let aZ := pullbackFiberObj a Z
    let bZ := pullbackFiberObj b Z
    have hZhom : Z.hom = r := by simp [Z]
    have hla : l ≫ q = fiberSecondHom F g aZ := by
      rw [fiberSecondHom_pullbackFiberObj F g a Z, hZhom]
      exact pullback.condition.symm
    have hphiStruct : fiberSecondHom F g aZ =
        fiberSecondHom F g bZ := by
      let phi' := Fiber.fiberInclusion.map phi
      have hphi' : IsHomLift (fiberProduct F g).p (𝟙 P) phi' := phi.2
      exact (fiberSecondHom_naturality F g aZ bZ (𝟙 P) phi' hphi').trans
        (Category.id_comp _)
    have hlb : l ≫ q = fiberSecondHom F g bZ := hla.trans hphiStruct
    let phiLocal := localFiberHom F g q aZ bZ l hla hlb phi
    let psiLocal := localFiberHom F g q aZ bZ l hla hlb psi
    have hlocalUnderlying :
        Fiber.fiberInclusion.map phiLocal =
          Fiber.fiberInclusion.map psiLocal := by
      exact hom_ext_of_faithful_of_isHomLift Hq.p (𝟙 P) _ _
    have hfst :
        (Fiber.fiberInclusion.map phi).fst =
          (Fiber.fiberInclusion.map psi).fst := by
      have hfstLocal := congrArg FiberProductHom.fst hlocalUnderlying
      exact Eq.trans rfl (Eq.trans hfstLocal rfl)
    have hsnd :
        (Fiber.fiberInclusion.map phi).snd =
          (Fiber.fiberInclusion.map psi).snd := by
      let phi' := Fiber.fiberInclusion.map phi
      let psi' := Fiber.fiberInclusion.map psi
      have hphi' : IsHomLift (fiberProduct F g).p (𝟙 P) phi' := phi.2
      have hpsi' : IsHomLift (fiberProduct F g).p (𝟙 P) psi' := psi.2
      let _ : IsHomLift (overBased T).p (𝟙 P) phi'.snd :=
        FiberProductHom.isHomLift_snd phi' (𝟙 P) hphi'
      let _ : IsHomLift (overBased T).p (𝟙 P) psi'.snd :=
        FiberProductHom.isHomLift_snd psi' (𝟙 P) hpsi'
      exact hom_ext_of_faithful_of_isHomLift (overBased T).p (𝟙 P) _ _
    apply Fiber.hom_ext
    exact FiberProductHom.ext hfst hsnd

/-- If a stack over a scheme becomes represented by a scheme after a
surjective étale base change, then its projection to schemes is faithful. -/
theorem projection_faithful_of_etale_scheme_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    {S W : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : overBased W ⥤ᵇ
      fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    (fiberProduct F g).p.Faithful := by
  exact projection_faithful_of_etale_baseChange F g q hqEtale
    hqSurjective (projection_faithful_of_scheme_representation W K hK)

/-- If a stack over a scheme becomes represented by a presheaf after a
surjective étale base change, then its projection to schemes is faithful. -/
theorem projection_faithful_of_etale_presheaf_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    {A : Scheme.{u}ᵒᵖ ⥤ Type u} {S : Scheme.{u}}
    (q : S ⟶ T) (hqEtale : Etale q) (hqSurjective : Surjective q)
    (K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    (fiberProduct F g).p.Faithful := by
  exact projection_faithful_of_etale_baseChange F g q hqEtale
    hqSurjective (projection_faithful_of_presheaf_representation K hK)

/-- A stack-valued fiber which is represented by an algebraic space after one
surjective étale base change is represented globally by an algebraic space. -/
theorem exists_isAlgebraicSpace_of_etale_presheaf_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    {A : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace A]
    {S : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧
      (fiberProduct F g).IsRepresentedByPresheaf X := by
  let hp : (fiberProduct F g).p.Faithful :=
    projection_faithful_of_etale_presheaf_baseChange F g q hqEtale
      hqSurjective K hK
  let _ : (fiberProduct F g).p.Faithful := hp
  exact exists_isAlgebraicSpace_of_etale_presheaf_baseChange_of_faithful
    F g q hqEtale hqSurjective K hK

/-- A stack-valued fiber which is represented by a scheme after one
surjective étale base change is represented globally by an algebraic space. -/
theorem exists_isAlgebraicSpace_of_etale_scheme_baseChange
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    {S W : Scheme.{u}} (q : S ⟶ T) (hqEtale : Etale q)
    (hqSurjective : Surjective q)
    (K : overBased W ⥤ᵇ fiberProduct F ((overBased.map q).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧
      (fiberProduct F g).IsRepresentedByPresheaf X := by
  let hp : (fiberProduct F g).p.Faithful :=
    projection_faithful_of_etale_scheme_baseChange F g q hqEtale
      hqSurjective K hK
  let _ : (fiberProduct F g).p.Faithful := hp
  exact exists_isAlgebraicSpace_of_etale_scheme_baseChange_of_faithful
    F g q hqEtale hqSurjective K hK

end AlgebraicGeometry.BasedFunctor
