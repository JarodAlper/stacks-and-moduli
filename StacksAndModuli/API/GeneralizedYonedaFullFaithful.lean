module

public import StacksAndModuli.API.PresentationLocalEssentialSurjectivity
public import StacksAndModuli.API.FiberProductHomSmall
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.5-universal-families»

/-!
# Full faithfulness in the generalized 2-Yoneda lemma

This module proves the morphism-descent half of the generalized 2-Yoneda lemma.
For a morphism `q : Q ⟶ᵇ T` which is locally essentially surjective and whose
source is fibered in groupoids, restriction

`(T ⟶ᵇ X) ⟶ DescentData q X`

is fully faithful whenever `X` is a stack. The inverse on morphisms is constructed
explicitly: choose local lifts of every object of `T`, glue the components of a
morphism of descent data using morphism descent in `X`, and prove naturality after
refining the local covers.

## Main declarations

* `CategoryTheory.BasedCategory.descentHomPreimage`: the explicitly glued preimage of
  a morphism of descent data;
* `CategoryTheory.BasedCategory.toDescentData_map_descentHomPreimage`: restriction of
  that preimage is the original morphism;
* `CategoryTheory.BasedCategory.toDescentData_full_of_locallyEssentiallySurjective`;
* `CategoryTheory.BasedCategory.toDescentData_faithful_of_locallyEssentiallySurjective`;
* `CategoryTheory.BasedCategory.toDescentDataFullyFaithful_of_locallyEssentiallySurjective`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {Q : BasedCategory.{v₂, u₂} C}
  {T : BasedCategory.{v₃, u₃} C}
  {X : BasedCategory.{v₄, u₄} C}
  {J : GrothendieckTopology C}
  [T.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids] [X.p.IsStack J]

/-- A covering sieve together with a chosen presentation lift over each of its
arrows. -/
structure LocalLiftData (q : BasedFunctor Q T) (J : GrothendieckTopology C)
    (y : T.obj) where
  sieve : Sieve (T.p.obj y)
  cover : sieve ∈ J (T.p.obj y)
  obj : sieve.arrows.category → Q.obj
  hom : ∀ r : sieve.arrows.category, q.obj (obj r) ⟶ y
  hom_isHomLift : ∀ r : sieve.arrows.category,
    IsHomLift T.p r.obj.hom (hom r)

/-- Choose local lifts witnessing local essential surjectivity. -/
noncomputable def LocalLiftData.ofLocallyEssentiallySurjective
    (q : BasedFunctor Q T) (J : GrothendieckTopology C)
    (hq : q.IsLocallyEssentiallySurjective (J := J)) (y : T.obj) :
    LocalLiftData q J y := by
  classical
  let R := Classical.choose (hq y)
  let hs : R ∈ J (T.p.obj y) ∧
      ∀ {V : C} (f : V ⟶ T.p.obj y), R f →
        ∃ (x : Q.obj) (ell : q.obj x ⟶ y), IsHomLift T.p f ell :=
    Classical.choose_spec (hq y)
  let hR := hs.1
  let hlift : ∀ {V : C} (f : V ⟶ T.p.obj y), R f →
      ∃ (x : Q.obj) (ell : q.obj x ⟶ y), IsHomLift T.p f ell := hs.2
  let x (r : R.arrows.category) :=
    Classical.choose (hlift r.obj.hom r.property)
  let ell (r : R.arrows.category) :=
    Classical.choose (Classical.choose_spec (hlift r.obj.hom r.property))
  have hell (r : R.arrows.category) :
      IsHomLift T.p r.obj.hom (ell r) :=
    Classical.choose_spec (Classical.choose_spec
      (hlift r.obj.hom r.property))
  exact ⟨R, hR, x, ell, hell⟩

namespace LocalLiftData

variable {q : BasedFunctor Q T} {J : GrothendieckTopology C} {y : T.obj}
  (D : LocalLiftData q J y)

/-- The unique comparison between two chosen local lifts along an arrow of the
covering sieve. -/
noncomputable def map {r s : D.sieve.arrows.category} (k : r ⟶ s) :
    q.obj (D.obj r) ⟶ q.obj (D.obj s) := by
  letI : IsHomLift T.p r.obj.hom (D.hom r) := D.hom_isHomLift r
  letI : IsHomLift T.p s.obj.hom (D.hom s) := D.hom_isHomLift s
  exact IsStronglyCartesian.map T.p s.obj.hom (D.hom s)
    k.hom.w.symm (D.hom r)

lemma map_isHomLift {r s : D.sieve.arrows.category} (k : r ⟶ s) :
    IsHomLift T.p k.hom.left (D.map k) := by
  letI : IsHomLift T.p r.obj.hom (D.hom r) := D.hom_isHomLift r
  letI : IsHomLift T.p s.obj.hom (D.hom s) := D.hom_isHomLift s
  exact IsStronglyCartesian.map_isHomLift T.p s.obj.hom (D.hom s)
    k.hom.w.symm (D.hom r)

@[reassoc]
lemma map_fac {r s : D.sieve.arrows.category} (k : r ⟶ s) :
    D.map k ≫ D.hom s = D.hom r := by
  letI : IsHomLift T.p r.obj.hom (D.hom r) := D.hom_isHomLift r
  letI : IsHomLift T.p s.obj.hom (D.hom s) := D.hom_isHomLift s
  exact IsStronglyCartesian.fac T.p s.obj.hom (D.hom s)
    k.hom.w.symm (D.hom r)

/-- The functor formed by the chosen local presentation lifts. -/
noncomputable def diagram : Functor D.sieve.arrows.category T.obj where
  obj r := q.obj (D.obj r)
  map k := D.map k
  map_id r := by
    letI := D.hom_isHomLift r
    have hmap := D.map_isHomLift (𝟙 r)
    letI : IsHomLift T.p (𝟙 r.obj.left) (D.map (𝟙 r)) := by
      simpa using hmap
    letI : IsHomLift T.p (𝟙 r.obj.left) (𝟙 (q.obj (D.obj r))) :=
      IsHomLift.id (IsHomLift.domain_eq T.p r.obj.hom (D.hom r))
    apply IsStronglyCartesian.ext T.p r.obj.hom (D.hom r) (𝟙 r.obj.left)
    simp [D.map_fac]
  map_comp := fun {r s t} k l ↦ by
    letI := D.hom_isHomLift t
    letI := D.map_isHomLift k
    letI := D.map_isHomLift l
    letI := D.map_isHomLift (k ≫ l)
    letI : IsHomLift T.p (k.hom.left ≫ l.hom.left)
        (D.map k ≫ D.map l) := inferInstance
    letI : IsHomLift T.p (k.hom.left ≫ l.hom.left)
        (D.map (k ≫ l)) := by
      simpa using D.map_isHomLift (k ≫ l)
    apply IsStronglyCartesian.ext T.p t.obj.hom (D.hom t)
      (k.hom.left ≫ l.hom.left)
    rw [Category.assoc, D.map_fac, D.map_fac, D.map_fac]

/-- Compatibility of a morphism of presentation descent data with the comparison
maps between chosen local lifts. -/
lemma descentHom_map_naturality [Q.p.IsFiberedInGroupoids]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    {r s : D.sieve.arrows.category} (k : r ⟶ s) :
    f.map (D.map k) ≫
        (theta.hom.toNatTrans.app (D.obj s) ≫ g.map (D.hom s)) =
      theta.hom.toNatTrans.app (D.obj r) ≫ g.map (D.hom r) := by
  let tau : q.comp f ⟶ q.comp g := theta.hom
  change f.map (D.map k) ≫
      (tau.toNatTrans.app (D.obj s) ≫ g.map (D.hom s)) =
    tau.toNatTrans.app (D.obj r) ≫ g.map (D.hom r)
  letI : IsHomLift T.p r.obj.hom (D.hom r) := D.hom_isHomLift r
  letI : IsHomLift T.p s.obj.hom (D.hom s) := D.hom_isHomLift s
  have hrbase : Q.p.obj (D.obj r) = r.obj.left :=
    (q.w_obj (D.obj r)).symm.trans
      (IsHomLift.domain_eq T.p r.obj.hom (D.hom r))
  have hsbase : Q.p.obj (D.obj s) = s.obj.left :=
    (q.w_obj (D.obj s)).symm.trans
      (IsHomLift.domain_eq T.p s.obj.hom (D.hom s))
  let kQ : Q.p.obj (D.obj r) ⟶ Q.p.obj (D.obj s) :=
    eqToHom hrbase ≫ k.hom.left ≫ eqToHom hsbase.symm
  obtain ⟨x', rho, hrho⟩ :=
    Functor.IsFiberedInGroupoids.exists_isHomLift
      (p := Q.p) (a := D.obj s) kQ
  letI hmap : IsHomLift T.p k.hom.left (D.map k) := D.map_isHomLift k
  letI hrho' : IsHomLift Q.p kQ rho := hrho
  letI hqrho : IsHomLift T.p kQ (q.map rho) :=
    q.preserves_isHomLift kQ rho
  let kT : T.p.obj (q.obj (D.obj r)) ⟶
      T.p.obj (q.obj (D.obj s)) :=
    eqToHom (q.w_obj (D.obj r)) ≫ kQ ≫
      eqToHom (q.w_obj (D.obj s)).symm
  have hmapT : IsHomLift T.p kT (D.map k) := by
    exact inferInstance
  have hxbase : Q.p.obj x' = Q.p.obj (D.obj r) :=
    IsHomLift.domain_eq Q.p kQ rho
  have hqrhoT : IsHomLift T.p kT (q.map rho) := by
    exact inferInstance
  letI : IsHomLift T.p kT (D.map k) := hmapT
  letI : IsHomLift T.p kT (q.map rho) := hqrhoT
  let c : q.obj (D.obj r) ≅ q.obj x' :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso
      (p := T.p) kT (q.map rho) (D.map k)
  have hc_fac : c.hom ≫ q.map rho = D.map k :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso_hom_comp
      (p := T.p) kT (q.map rho) (D.map k)
  have hxr : Q.p.obj x' = Q.p.obj (D.obj r) :=
    hxbase
  have hcLift : IsHomLift T.p (𝟙 (Q.p.obj (D.obj r))) c.hom := by
    have hc := (inferInstance :
      IsHomLift T.p (𝟙 (T.p.obj (q.obj (D.obj r)))) c.hom)
    have hc' : IsHomLift T.p
        (eqToHom (q.w_obj (D.obj r)).symm ≫
          𝟙 (T.p.obj (q.obj (D.obj r))) ≫
          eqToHom (q.w_obj (D.obj r))) c.hom := inferInstance
    simpa using hc'
  let z : FiberProductObj q q :=
    (fiberProductPointOfIso q (D.obj r) x' hxr
      ⟨c, hcLift⟩).1
  have hw := theta.w z
  change f.map c.hom ≫ tau.toNatTrans.app x' =
    tau.toNatTrans.app (D.obj r) ≫ g.map c.hom at hw
  have hnat := tau.toNatTrans.naturality rho
  change f.map (q.map rho) ≫ tau.toNatTrans.app (D.obj s) =
    tau.toNatTrans.app x' ≫ g.map (q.map rho) at hnat
  calc
    f.map (D.map k) ≫
          (tau.toNatTrans.app (D.obj s) ≫ g.map (D.hom s)) =
        f.map (c.hom ≫ q.map rho) ≫
          (tau.toNatTrans.app (D.obj s) ≫ g.map (D.hom s)) := by
      rw [hc_fac]
    _ = (f.map c.hom ≫ f.map (q.map rho)) ≫
          (tau.toNatTrans.app (D.obj s) ≫ g.map (D.hom s)) := by
      rw [f.toFunctor.map_comp]
    _ = f.map c.hom ≫
          (f.map (q.map rho) ≫ tau.toNatTrans.app (D.obj s)) ≫
            g.map (D.hom s) := by simp only [Category.assoc]
    _ = f.map c.hom ≫
          (tau.toNatTrans.app x' ≫ g.map (q.map rho)) ≫
            g.map (D.hom s) := by
      rw [hnat]
    _ = (f.map c.hom ≫ tau.toNatTrans.app x') ≫
          g.map (q.map rho) ≫ g.map (D.hom s) := by
      simp only [Category.assoc]
    _ = (tau.toNatTrans.app (D.obj r) ≫ g.map c.hom) ≫
          g.map (q.map rho) ≫ g.map (D.hom s) := by rw [hw]
    _ = tau.toNatTrans.app (D.obj r) ≫
          g.map (c.hom ≫ q.map rho) ≫ g.map (D.hom s) := by
      rw [g.toFunctor.map_comp]
      simp only [Category.assoc]
    _ = tau.toNatTrans.app (D.obj r) ≫
          g.map (D.map k) ≫ g.map (D.hom s) := by rw [hc_fac]
    _ = tau.toNatTrans.app (D.obj r) ≫
          g.map (D.map k ≫ D.hom s) := by rw [g.toFunctor.map_comp]
    _ = tau.toNatTrans.app (D.obj r) ≫ g.map (D.hom r) := by rw [D.map_fac]

/-- A morphism of presentation descent data glues to a unique morphism over the
target object. -/
lemma existsUnique_descentHom_app [Q.p.IsFiberedInGroupoids] [X.p.IsStack J]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g) :
    ∃! phi : f.obj y ⟶ g.obj y,
      IsHomLift X.p (𝟙 (T.p.obj y)) phi ∧
        ∀ r : D.sieve.arrows.category,
          f.map (D.hom r) ≫ phi =
            theta.hom.toNatTrans.app (D.obj r) ≫ g.map (D.hom r) := by
  let tau : q.comp f ⟶ q.comp g := theta.hom
  let A : Functor D.sieve.arrows.category X.obj := D.diagram ⋙ f.toFunctor
  let eta : ∀ r : D.sieve.arrows.category, A.obj r ⟶ f.obj y :=
    fun r ↦ f.map (D.hom r)
  let zeta : ∀ r : D.sieve.arrows.category, A.obj r ⟶ g.obj y :=
    fun r ↦ tau.toNatTrans.app (D.obj r) ≫ g.map (D.hom r)
  have hAmap : ∀ {r s : D.sieve.arrows.category} (k : r ⟶ s),
      IsHomLift X.p k.hom.left (A.map k) := by
    intro r s k
    change IsHomLift X.p k.hom.left (f.map (D.map k))
    letI := D.map_isHomLift k
    exact f.preserves_isHomLift k.hom.left (D.map k)
  have heta : ∀ r : D.sieve.arrows.category,
      IsHomLift X.p r.obj.hom (eta r) := by
    intro r
    change IsHomLift X.p r.obj.hom (f.map (D.hom r))
    letI := D.hom_isHomLift r
    exact f.preserves_isHomLift r.obj.hom (D.hom r)
  have hzeta : ∀ r : D.sieve.arrows.category,
      IsHomLift X.p r.obj.hom (zeta r) := by
    intro r
    letI htau : IsHomLift X.p (𝟙 (Q.p.obj (D.obj r)))
        (tau.toNatTrans.app (D.obj r)) := inferInstance
    letI hhom : IsHomLift X.p r.obj.hom (g.map (D.hom r)) := by
      letI := D.hom_isHomLift r
      exact g.preserves_isHomLift r.obj.hom (D.hom r)
    change IsHomLift X.p r.obj.hom
      (tau.toNatTrans.app (D.obj r) ≫ g.map (D.hom r))
    exact IsHomLift.comp_lift_id_left' X.p (Q.p.obj (D.obj r))
      (tau.toNatTrans.app (D.obj r)) r.obj.hom (g.map (D.hom r))
  have hetanat : ∀ {r s : D.sieve.arrows.category} (k : r ⟶ s),
      A.map k ≫ eta s = eta r := by
    intro r s k
    change f.map (D.map k) ≫ f.map (D.hom s) = f.map (D.hom r)
    rw [← f.toFunctor.map_comp, D.map_fac]
  have hzetanat : ∀ {r s : D.sieve.arrows.category} (k : r ⟶ s),
      A.map k ≫ zeta s = zeta r := by
    intro r s k
    exact D.descentHom_map_naturality theta k
  obtain ⟨phi, hphi, huniq⟩ :=
    Functor.IsStack.existsUnique_gluing_hom_of_cocone D.cover A
      (f.w_obj y) (g.w_obj y) eta heta hAmap hetanat zeta hzeta hzetanat
  refine ⟨phi, ⟨hphi.1, ?_⟩, ?_⟩
  · intro r
    exact (hphi.2 r.property).symm
  · intro psi hpsi
    apply huniq psi
    refine ⟨hpsi.1, ?_⟩
    intro V r hr
    let r' := D.sieve.arrows.categoryMk r hr
    exact (hpsi.2 r').symm

/-- The glued component has the required comparison formula for every presentation
lift over the covering sieve, not only for the chosen lift. -/
lemma descentHom_app_fac_of_mem [Q.p.IsFiberedInGroupoids]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    (phi : f.obj y ⟶ g.obj y)
    (hphi : ∀ r : D.sieve.arrows.category,
      f.map (D.hom r) ≫ phi =
        theta.hom.toNatTrans.app (D.obj r) ≫ g.map (D.hom r))
    {V : C} {r : V ⟶ T.p.obj y} (hr : D.sieve r)
    {x : Q.obj} (ell : q.obj x ⟶ y) (hell : IsHomLift T.p r ell) :
    f.map ell ≫ phi =
      theta.hom.toNatTrans.app x ≫ g.map ell := by
  let tau : q.comp f ⟶ q.comp g := theta.hom
  change f.map ell ≫ phi = tau.toNatTrans.app x ≫ g.map ell
  let r' := D.sieve.arrows.categoryMk r hr
  letI : IsHomLift T.p r (D.hom r') := D.hom_isHomLift r'
  letI : IsHomLift T.p r ell := hell
  let c : q.obj x ≅ q.obj (D.obj r') :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso
      (p := T.p) r (D.hom r') ell
  have hc_fac : c.hom ≫ D.hom r' = ell :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso_hom_comp
      (p := T.p) r (D.hom r') ell
  have hxbase : Q.p.obj x = V :=
    (q.w_obj x).symm.trans (IsHomLift.domain_eq T.p r ell)
  have hDbase : Q.p.obj (D.obj r') = V :=
    (q.w_obj (D.obj r')).symm.trans
      (IsHomLift.domain_eq T.p r (D.hom r'))
  have hbase : Q.p.obj (D.obj r') = Q.p.obj x :=
    hDbase.trans hxbase.symm
  have hcLift : IsHomLift T.p (𝟙 (Q.p.obj x)) c.hom := by
    have hc := (inferInstance : IsHomLift T.p (𝟙 V) c.hom)
    have hc' : IsHomLift T.p
        (eqToHom hxbase ≫ 𝟙 V ≫ eqToHom hxbase.symm) c.hom :=
      inferInstance
    simpa using hc'
  let z : FiberProductObj q q :=
    (fiberProductPointOfIso q x (D.obj r') hbase ⟨c, hcLift⟩).1
  have hw := theta.w z
  change f.map c.hom ≫ tau.toNatTrans.app (D.obj r') =
    tau.toNatTrans.app x ≫ g.map c.hom at hw
  calc
    f.map ell ≫ phi = f.map (c.hom ≫ D.hom r') ≫ phi := by rw [hc_fac]
    _ = (f.map c.hom ≫ f.map (D.hom r')) ≫ phi := by
      rw [f.toFunctor.map_comp]
    _ = f.map c.hom ≫ (f.map (D.hom r') ≫ phi) :=
      Category.assoc _ _ _
    _ = f.map c.hom ≫
        (tau.toNatTrans.app (D.obj r') ≫ g.map (D.hom r')) := by
      rw [hphi r']
    _ = (f.map c.hom ≫ tau.toNatTrans.app (D.obj r')) ≫
        g.map (D.hom r') := (Category.assoc _ _ _).symm
    _ = (tau.toNatTrans.app x ≫ g.map c.hom) ≫
        g.map (D.hom r') := by rw [hw]
    _ = tau.toNatTrans.app x ≫
        (g.map c.hom ≫ g.map (D.hom r')) := Category.assoc _ _ _
    _ = tau.toNatTrans.app x ≫ g.map (c.hom ≫ D.hom r') := by
      rw [g.toFunctor.map_comp]
    _ = tau.toNatTrans.app x ≫ g.map ell := by rw [hc_fac]

/-- The component obtained by gluing a morphism of descent data over a local
presentation cover. -/
noncomputable def descentHomApp [Q.p.IsFiberedInGroupoids] [X.p.IsStack J]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g) :
    f.obj y ⟶ g.obj y :=
  Classical.choose (D.existsUnique_descentHom_app (J := J) theta)

lemma descentHomApp_isHomLift [Q.p.IsFiberedInGroupoids] [X.p.IsStack J]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g) :
    IsHomLift X.p (𝟙 (T.p.obj y)) (D.descentHomApp theta) :=
  (Classical.choose_spec (D.existsUnique_descentHom_app (J := J) theta)).1.1

lemma descentHomApp_fac [Q.p.IsFiberedInGroupoids] [X.p.IsStack J]
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    (r : D.sieve.arrows.category) :
    f.map (D.hom r) ≫ D.descentHomApp theta =
      theta.hom.toNatTrans.app (D.obj r) ≫ g.map (D.hom r) :=
  (Classical.choose_spec (D.existsUnique_descentHom_app (J := J) theta)).1.2 r

end LocalLiftData

/-- A morphism of presentation descent data is natural along every arrow between
objects in the image of the presentation, including arrows not themselves in the
image of a morphism upstairs. -/
lemma descentHom_naturality_of_map_between_presentation_objects
    [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T) {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    {a b : Q.obj} (ell : q.obj a ⟶ q.obj b) :
    f.map ell ≫ theta.hom.toNatTrans.app b =
      theta.hom.toNatTrans.app a ≫ g.map ell := by
  let tau : q.comp f ⟶ q.comp g := theta.hom
  change f.map ell ≫ tau.toNatTrans.app b =
    tau.toNatTrans.app a ≫ g.map ell
  let rQ : Q.p.obj a ⟶ Q.p.obj b :=
    eqToHom (q.w_obj a).symm ≫ T.p.map ell ≫ eqToHom (q.w_obj b)
  obtain ⟨a', rho, hrho⟩ :=
    Functor.IsFiberedInGroupoids.exists_isHomLift
      (p := Q.p) (a := b) rQ
  letI hell : IsHomLift T.p (T.p.map ell) ell := Functor.IsHomLift.map ell
  letI hrho' : IsHomLift Q.p rQ rho := hrho
  letI hqrho : IsHomLift T.p rQ (q.map rho) :=
    q.preserves_isHomLift rQ rho
  let rT : T.p.obj (q.obj a) ⟶ T.p.obj (q.obj b) :=
    eqToHom (q.w_obj a) ≫ rQ ≫ eqToHom (q.w_obj b).symm
  have hellT : IsHomLift T.p rT ell := by
    exact inferInstance
  have hqrhoT : IsHomLift T.p rT (q.map rho) := by
    exact inferInstance
  letI : IsHomLift T.p rT ell := hellT
  letI : IsHomLift T.p rT (q.map rho) := hqrhoT
  let c : q.obj a ≅ q.obj a' :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso
      (p := T.p) rT (q.map rho) ell
  have hc_fac : c.hom ≫ q.map rho = ell :=
    Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso_hom_comp
      (p := T.p) rT (q.map rho) ell
  have habase : Q.p.obj a' = Q.p.obj a :=
    IsHomLift.domain_eq Q.p rQ rho
  have hcLift : IsHomLift T.p (𝟙 (Q.p.obj a)) c.hom := by
    have hc := (inferInstance :
      IsHomLift T.p (𝟙 (T.p.obj (q.obj a))) c.hom)
    have hc' : IsHomLift T.p
        (eqToHom (q.w_obj a).symm ≫
          𝟙 (T.p.obj (q.obj a)) ≫ eqToHom (q.w_obj a)) c.hom :=
      inferInstance
    simpa using hc'
  let z : FiberProductObj q q :=
    (fiberProductPointOfIso q a a' habase ⟨c, hcLift⟩).1
  have hw := theta.w z
  change f.map c.hom ≫ tau.toNatTrans.app a' =
    tau.toNatTrans.app a ≫ g.map c.hom at hw
  have hnat := tau.toNatTrans.naturality rho
  change f.map (q.map rho) ≫ tau.toNatTrans.app b =
    tau.toNatTrans.app a' ≫ g.map (q.map rho) at hnat
  calc
    f.map ell ≫ tau.toNatTrans.app b =
        f.map (c.hom ≫ q.map rho) ≫ tau.toNatTrans.app b := by rw [hc_fac]
    _ = (f.map c.hom ≫ f.map (q.map rho)) ≫ tau.toNatTrans.app b := by
      rw [f.toFunctor.map_comp]
    _ = f.map c.hom ≫
        (f.map (q.map rho) ≫ tau.toNatTrans.app b) := Category.assoc _ _ _
    _ = f.map c.hom ≫
        (tau.toNatTrans.app a' ≫ g.map (q.map rho)) := by rw [hnat]
    _ = (f.map c.hom ≫ tau.toNatTrans.app a') ≫
        g.map (q.map rho) := (Category.assoc _ _ _).symm
    _ = (tau.toNatTrans.app a ≫ g.map c.hom) ≫
        g.map (q.map rho) := by rw [hw]
    _ = tau.toNatTrans.app a ≫
        (g.map c.hom ≫ g.map (q.map rho)) := Category.assoc _ _ _
    _ = tau.toNatTrans.app a ≫ g.map (c.hom ≫ q.map rho) := by
      rw [g.toFunctor.map_comp]
    _ = tau.toNatTrans.app a ≫ g.map ell := by rw [hc_fac]

/-- Arrows in a stack over the same base arrow can be compared after a cover of
their common source. -/
lemma hom_ext_of_cover_of_isHomLift
    {S V : C} {a b : X.obj} {h : S ⟶ V} {u v : a ⟶ b}
    (ha : X.p.obj a = S) (hb : X.p.obj b = V)
    (hu : IsHomLift X.p h u) (hv : IsHomLift X.p h v)
    {R : Sieve S} (hR : R ∈ J S)
    (H : ∀ {W : C} {r : W ⟶ S} (_hr : R r) {z : X.obj}
      (xi : z ⟶ a) (_hxi : IsHomLift X.p r xi), xi ≫ u = xi ≫ v) :
    u = v := by
  subst S
  subst V
  obtain ⟨b', psi, hpsi⟩ :=
    Functor.IsFiberedInGroupoids.exists_isHomLift (p := X.p) (a := b) h
  letI : IsHomLift X.p h psi := hpsi
  letI : IsStronglyCartesian X.p h psi :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p h psi
  let u' : a ⟶ b' :=
    IsStronglyCartesian.map X.p h psi (Category.id_comp h).symm u
  let v' : a ⟶ b' :=
    IsStronglyCartesian.map X.p h psi (Category.id_comp h).symm v
  have hu' : IsHomLift X.p (𝟙 (X.p.obj a)) u' :=
    IsStronglyCartesian.map_isHomLift X.p h psi (Category.id_comp h).symm u
  have hv' : IsHomLift X.p (𝟙 (X.p.obj a)) v' :=
    IsStronglyCartesian.map_isHomLift X.p h psi (Category.id_comp h).symm v
  have huv' : u' = v' := by
    apply Functor.IsStack.hom_ext_of_cover hR rfl
      (IsHomLift.domain_eq X.p h psi) hu' hv'
    intro W r hr z xi hxi
    apply IsStronglyCartesian.ext X.p h psi r
    rw [Category.assoc, IsStronglyCartesian.fac,
      Category.assoc, IsStronglyCartesian.fac]
    exact H hr xi hxi
  calc
    u = u' ≫ psi := (IsStronglyCartesian.fac X.p h psi
      (Category.id_comp h).symm u).symm
    _ = v' ≫ psi := by rw [huv']
    _ = v := IsStronglyCartesian.fac X.p h psi
      (Category.id_comp h).symm v

/-- The locally glued components of a morphism of descent data are natural. -/
lemma descentHomApp_naturality [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J))
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    {y z : T.obj} (h : y ⟶ z) :
    f.map h ≫
        (LocalLiftData.ofLocallyEssentiallySurjective q J hq z).descentHomApp theta =
      (LocalLiftData.ofLocallyEssentiallySurjective q J hq y).descentHomApp theta ≫
        g.map h := by
  let Dy := LocalLiftData.ofLocallyEssentiallySurjective q J hq y
  let Dz := LocalLiftData.ofLocallyEssentiallySurjective q J hq z
  let phiy := Dy.descentHomApp theta
  let phiz := Dz.descentHomApp theta
  let R : Sieve (T.p.obj y) :=
    Dy.sieve ⊓ Dz.sieve.pullback (T.p.map h)
  have hR : R ∈ J (T.p.obj y) :=
    J.intersection_covering Dy.cover
      (J.pullback_stable (T.p.map h) Dz.cover)
  letI hh : IsHomLift T.p (T.p.map h) h := Functor.IsHomLift.map h
  letI hfh : IsHomLift X.p (T.p.map h) (f.map h) :=
    f.preserves_isHomLift (T.p.map h) h
  letI hgh : IsHomLift X.p (T.p.map h) (g.map h) :=
    g.preserves_isHomLift (T.p.map h) h
  letI hphiy : IsHomLift X.p (𝟙 (T.p.obj y)) phiy :=
    Dy.descentHomApp_isHomLift theta
  letI hphiz : IsHomLift X.p (𝟙 (T.p.obj z)) phiz :=
    Dz.descentHomApp_isHomLift theta
  have hu : IsHomLift X.p (T.p.map h) (f.map h ≫ phiz) := by
    exact inferInstance
  have hv : IsHomLift X.p (T.p.map h) (phiy ≫ g.map h) := by
    exact inferInstance
  apply hom_ext_of_cover_of_isHomLift (J := J)
    (f.w_obj y) (g.w_obj z) hu hv hR
  intro W r hr a xi hxi
  have hry : Dy.sieve r := hr.1
  have hrz : Dz.sieve (r ≫ T.p.map h) := hr.2
  let rDy := Dy.sieve.arrows.categoryMk r hry
  let ell : q.obj (Dy.obj rDy) ⟶ y := Dy.hom rDy
  letI hell : IsHomLift T.p r ell := Dy.hom_isHomLift rDy
  letI hfell : IsHomLift X.p r (f.map ell) :=
    f.preserves_isHomLift r ell
  letI hcart : IsStronglyCartesian X.p r (f.map ell) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p r _
  let kappa : a ⟶ f.obj (q.obj (Dy.obj rDy)) :=
    IsStronglyCartesian.map X.p r (f.map ell)
      (Category.id_comp r).symm xi
  have hkappa : kappa ≫ f.map ell = xi :=
    IsStronglyCartesian.fac X.p r (f.map ell)
      (Category.id_comp r).symm xi
  have hcompLift : IsHomLift T.p (r ≫ T.p.map h) (ell ≫ h) := by
    exact inferInstance
  have hy := Dy.descentHom_app_fac_of_mem theta phiy
    (fun s ↦ Dy.descentHomApp_fac theta s) hry ell hell
  have hz := Dz.descentHom_app_fac_of_mem theta phiz
    (fun s ↦ Dz.descentHomApp_fac theta s) hrz (ell ≫ h) hcompLift
  let tau : q.comp f ⟶ q.comp g := theta.hom
  change f.map ell ≫ phiy =
      tau.toNatTrans.app (Dy.obj rDy) ≫ g.map ell at hy
  change f.map (ell ≫ h) ≫ phiz =
      tau.toNatTrans.app (Dy.obj rDy) ≫ g.map (ell ≫ h) at hz
  calc
    xi ≫ (f.map h ≫ phiz) =
        (kappa ≫ f.map ell) ≫ (f.map h ≫ phiz) := by rw [hkappa]
    _ = kappa ≫ ((f.map ell ≫ f.map h) ≫ phiz) := by simp
    _ = kappa ≫ (f.map (ell ≫ h) ≫ phiz) := by
      rw [f.toFunctor.map_comp]
    _ = kappa ≫
        (tau.toNatTrans.app (Dy.obj rDy) ≫ g.map (ell ≫ h)) := by rw [hz]
    _ = kappa ≫
        (tau.toNatTrans.app (Dy.obj rDy) ≫ (g.map ell ≫ g.map h)) := by
      rw [g.toFunctor.map_comp]
    _ = kappa ≫ ((tau.toNatTrans.app (Dy.obj rDy) ≫ g.map ell) ≫
        g.map h) := by simp
    _ = kappa ≫ ((f.map ell ≫ phiy) ≫ g.map h) := by rw [hy]
    _ = (kappa ≫ f.map ell) ≫ (phiy ≫ g.map h) := by simp
    _ = xi ≫ (phiy ≫ g.map h) := by rw [hkappa]

/-- The based natural transformation obtained by gluing a morphism of descent
data componentwise. -/
noncomputable def descentHomPreimage [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J))
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g) :
    f ⟶ g where
  toNatTrans :=
    { app := fun y ↦
        (LocalLiftData.ofLocallyEssentiallySurjective q J hq y).descentHomApp theta
      naturality := fun _ _ h ↦ descentHomApp_naturality q hq theta h }
  isHomLift' := fun y ↦
    (LocalLiftData.ofLocallyEssentiallySurjective q J hq y).descentHomApp_isHomLift theta

lemma descentHomPreimage_app_at_presentation [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J))
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g)
    (x : Q.obj) :
    (descentHomPreimage q hq theta).toNatTrans.app (q.obj x) =
      theta.hom.toNatTrans.app x := by
  let D := LocalLiftData.ofLocallyEssentiallySurjective q J hq (q.obj x)
  change D.descentHomApp theta = theta.hom.toNatTrans.app x
  have hthetaLift : IsHomLift X.p (𝟙 (T.p.obj (q.obj x)))
      (theta.hom.toNatTrans.app x) :=
    theta.hom.isHomLift (q.w_obj x).symm
  have hthetaFac : ∀ r : D.sieve.arrows.category,
      f.map (D.hom r) ≫ theta.hom.toNatTrans.app x =
        theta.hom.toNatTrans.app (D.obj r) ≫ g.map (D.hom r) := by
    intro r
    exact descentHom_naturality_of_map_between_presentation_objects
      q theta (D.hom r)
  exact ((Classical.choose_spec
    (D.existsUnique_descentHom_app (J := J) theta)).2 _
      ⟨hthetaLift, hthetaFac⟩).symm

/-- The componentwise glued preimage restricts to the original morphism of
descent data. -/
lemma toDescentData_map_descentHomPreimage [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J))
    {f g : BasedFunctor T X}
    (theta : (toDescentData q X).obj f ⟶ (toDescentData q X).obj g) :
    (toDescentData q X).map (descentHomPreimage q hq theta) = theta := by
  apply DescentData.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  ext x
  exact descentHomPreimage_app_at_presentation q hq theta x

/-- Restriction to locally essentially surjective descent data is full. -/
theorem toDescentData_full_of_locallyEssentiallySurjective
    [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J)) :
    (toDescentData q X).Full := by
  constructor
  intro f g theta
  exact ⟨descentHomPreimage q hq theta,
    toDescentData_map_descentHomPreimage q hq theta⟩

/-- Restriction to locally essentially surjective descent data is faithful. -/
theorem toDescentData_faithful_of_locallyEssentiallySurjective
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J)) :
    (toDescentData q X).Faithful := by
  constructor
  intro f g alpha beta h
  apply BasedNatTrans.ext
  apply NatTrans.ext
  ext y
  let S := T.p.obj y
  obtain ⟨R, hR, hlift⟩ := hq y
  apply Functor.IsStack.hom_ext_of_cover hR (f.w_obj y) (g.w_obj y)
      (alpha.isHomLift rfl) (beta.isHomLift rfl)
  intro V r hr z xi hxi
  obtain ⟨x, ell, hell⟩ := hlift r hr
  letI : IsHomLift T.p r ell := hell
  letI hfell : IsHomLift X.p r (f.map ell) :=
    f.preserves_isHomLift r ell
  letI : IsStronglyCartesian X.p r (f.map ell) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p r _
  let kappa : z ⟶ f.obj (q.obj x) :=
    IsStronglyCartesian.map X.p r (f.map ell)
      (Category.id_comp r).symm xi
  have hkappa : kappa ≫ f.map ell = xi :=
    IsStronglyCartesian.fac X.p r (f.map ell)
      (Category.id_comp r).symm xi
  have hcomp : alpha.toNatTrans.app (q.obj x) =
      beta.toNatTrans.app (q.obj x) := by
    have hhom := congrArg DescentData.Hom.hom h
    exact congrArg (fun eta ↦ eta.toNatTrans.app x) hhom
  calc
    xi ≫ alpha.toNatTrans.app y =
        (kappa ≫ f.map ell) ≫ alpha.toNatTrans.app y := by rw [hkappa]
    _ = kappa ≫ (f.map ell ≫ alpha.toNatTrans.app y) :=
      Category.assoc _ _ _
    _ = kappa ≫ (alpha.toNatTrans.app (q.obj x) ≫ g.map ell) := by
      rw [alpha.toNatTrans.naturality]
    _ = kappa ≫ (beta.toNatTrans.app (q.obj x) ≫ g.map ell) := by
      rw [hcomp]
    _ = kappa ≫ (f.map ell ≫ beta.toNatTrans.app y) := by
      rw [beta.toNatTrans.naturality]
    _ = (kappa ≫ f.map ell) ≫ beta.toNatTrans.app y :=
      (Category.assoc _ _ _).symm
    _ = xi ≫ beta.toNatTrans.app y := by rw [hkappa]

/-- Restriction to locally essentially surjective descent data is fully
faithful. -/
noncomputable def toDescentDataFullyFaithful_of_locallyEssentiallySurjective
    [Q.p.IsFiberedInGroupoids]
    (q : BasedFunctor Q T)
    (hq : q.IsLocallyEssentiallySurjective (J := J)) :
    (toDescentData q X).FullyFaithful where
  preimage := descentHomPreimage q hq
  map_preimage := toDescentData_map_descentHomPreimage q hq
  preimage_map phi := by
    apply (toDescentData_faithful_of_locallyEssentiallySurjective
      (X := X) q hq).map_injective
    rw [toDescentData_map_descentHomPreimage]

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.BasedCategory

/-- Restriction along a smooth-surjective representable presentation is full
against an étale stack. -/
theorem toDescentData_full_of_representableWith
    {𝒯 : BasedCategory.{v₂, u₂} Scheme.{u₁}}
    {𝒜 : BasedCategory.{v₃, u₃} Scheme.{u₁}}
    [IsAlgebraicStack 𝒯] [BasedCategory.IsStack Scheme.etaleTopology 𝒜]
    {U : Scheme.{u₁}} (q : overBased U ⥤ᵇ 𝒯)
    (hq : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u₁}) q) :
    (toDescentData q 𝒜).Full :=
  toDescentData_full_of_locallyEssentiallySurjective q
    hq.isLocallyEssentiallySurjective_etale

/-- Restriction along a smooth-surjective representable presentation is
faithful against an étale stack. -/
theorem toDescentData_faithful_of_representableWith
    {𝒯 : BasedCategory.{v₂, u₂} Scheme.{u₁}}
    {𝒜 : BasedCategory.{v₃, u₃} Scheme.{u₁}}
    [IsAlgebraicStack 𝒯] [BasedCategory.IsStack Scheme.etaleTopology 𝒜]
    {U : Scheme.{u₁}} (q : overBased U ⥤ᵇ 𝒯)
    (hq : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u₁}) q) :
    (toDescentData q 𝒜).Faithful :=
  toDescentData_faithful_of_locallyEssentiallySurjective q
    hq.isLocallyEssentiallySurjective_etale

/-- Restriction along a smooth-surjective representable presentation is fully
faithful against an étale stack. -/
noncomputable def toDescentDataFullyFaithful_of_representableWith
    {𝒯 : BasedCategory.{v₂, u₂} Scheme.{u₁}}
    {𝒜 : BasedCategory.{v₃, u₃} Scheme.{u₁}}
    [IsAlgebraicStack 𝒯] [BasedCategory.IsStack Scheme.etaleTopology 𝒜]
    {U : Scheme.{u₁}} (q : overBased U ⥤ᵇ 𝒯)
    (hq : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u₁}) q) :
    (toDescentData q 𝒜).FullyFaithful :=
  toDescentDataFullyFaithful_of_locallyEssentiallySurjective q
    hq.isLocallyEssentiallySurjective_etale

end AlgebraicGeometry
