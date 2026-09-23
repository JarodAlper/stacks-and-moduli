module

public import StacksAndModuli.API.GlobalPrincipalBundle
public import StacksAndModuli.API.ArrowCartesian

/-!
# Classifying prestacks of principal bundles

For a fixed group scheme `G` over `S`, this file constructs the category of
principal `G`-bundles over varying `S`-schemes.  A morphism is an equivariant
cartesian square.  Projection to the bundle base is fibered in groupoids.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- A principal `G`-bundle over a varying `S`-scheme. -/
structure ClassifyingObj where
  /-- The base of the bundle. -/
  base : Over S
  /-- The principal bundle. -/
  bundle : GlobalPrincipalBundle G base

/-- An equivariant cartesian square of principal `G`-bundles. -/
@[ext]
structure ClassifyingHom (x y : ClassifyingObj G) where
  /-- The map of bundle bases. -/
  base : x.base ⟶ y.base
  /-- The map of total spaces. -/
  total : x.bundle.P ⟶ y.bundle.P
  /-- The underlying square is cartesian. -/
  isPullback : IsPullback total x.bundle.p y.bundle.p base
  /-- The map on total spaces is `G`-equivariant. -/
  equivariant : IsModHom G total

namespace ClassifyingHom

variable {G} {x y z : ClassifyingObj G}

/-- The identity morphism of a principal bundle. -/
@[simps]
def id (x : ClassifyingObj G) : ClassifyingHom G x x where
  base := 𝟙 x.base
  total := 𝟙 x.bundle.P
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
  equivariant := inferInstance

/-- Composition of equivariant cartesian bundle morphisms. -/
@[simps]
def comp (f : ClassifyingHom G x y) (g : ClassifyingHom G y z) :
    ClassifyingHom G x z where
  base := f.base ≫ g.base
  total := f.total ≫ g.total
  isPullback := f.isPullback.paste_horiz g.isPullback
  equivariant := by
    letI := f.equivariant
    letI := g.equivariant
    infer_instance

end ClassifyingHom

instance : Category (ClassifyingObj G) where
  Hom := ClassifyingHom G
  id := ClassifyingHom.id
  comp := ClassifyingHom.comp
  id_comp f := by ext <;> simp [ClassifyingHom.id, ClassifyingHom.comp]
  comp_id f := by ext <;> simp [ClassifyingHom.id, ClassifyingHom.comp]
  assoc f g h := by ext <;> simp [ClassifyingHom.comp, Category.assoc]

/-- The category of principal `G`-bundles, based over the scheme carrying the
bundle. -/
abbrev classifyingPrestack : BasedCategory (Over S) where
  obj := ClassifyingObj G
  p :=
    { obj := ClassifyingObj.base
      map := fun f ↦ (show ClassifyingHom G _ _ from f).base
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

namespace classifyingPrestack

variable {G}

/-- Principal bundles are stable under arbitrary base change. -/
instance projection_isFiberedInGroupoids :
    (classifyingPrestack G).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    change ClassifyingObj G at a
    let B := a.bundle.pullback f
    let b : ClassifyingObj G := ⟨R, B⟩
    let phi : ClassifyingHom G b a :=
      { base := f
        total := pullback.fst a.bundle.p f
        isPullback := IsPullback.of_hasPullback a.bundle.p f
        equivariant := by
          constructor
          exact pullback.lift_fst _ _ _ }
    refine ⟨b, phi, ?_⟩
    exact Functor.IsHomLift.map (p := (classifyingPrestack G).p) phi
  · intro a b phi
    change ClassifyingObj G at a b
    change ClassifyingHom G a b at phi
    letI : IsHomLift (classifyingPrestack G).p phi.base phi :=
      Functor.IsHomLift.map (p := (classifyingPrestack G).p) phi
    constructor
    intro c g psi hpsi
    change ClassifyingObj G at c
    change ClassifyingHom G c b at psi
    have hg : g ≫ phi.base = psi.base := by
      exact IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
        (g ≫ (classifyingPrestack G).p.map phi) psi
    have hw : psi.total ≫ b.bundle.p = (c.bundle.p ≫ g) ≫ phi.base := by
      calc
        psi.total ≫ b.bundle.p = c.bundle.p ≫ psi.base := psi.isPullback.w
        _ = c.bundle.p ≫ (g ≫ phi.base) := by rw [hg]
        _ = (c.bundle.p ≫ g) ≫ phi.base := (Category.assoc _ _ _).symm
    let chiTotal : c.bundle.P ⟶ a.bundle.P :=
      phi.isPullback.lift psi.total (c.bundle.p ≫ g) hw
    have hchiTotal : chiTotal ≫ phi.total = psi.total :=
      phi.isPullback.lift_fst _ _ _
    have hchiBase : chiTotal ≫ a.bundle.p = c.bundle.p ≫ g :=
      phi.isPullback.lift_snd _ _ _
    have hchiPb : IsPullback chiTotal c.bundle.p a.bundle.p g := by
      have hout : IsPullback (chiTotal ≫ phi.total) c.bundle.p b.bundle.p
          (g ≫ phi.base) := by
        simpa only [hchiTotal, hg] using psi.isPullback
      exact hout.of_right hchiBase phi.isPullback
    have hchiEquivariant : IsModHom G chiTotal := by
      letI := phi.equivariant
      letI := psi.equivariant
      constructor
      apply phi.isPullback.hom_ext
      · simp only [Category.assoc, hchiTotal, IsModHom.smul_hom]
        slice_rhs 1 2 => rw [← MonoidalLeftAction.actionHomRight_comp]
        rw [hchiTotal]
      · calc
          (γ[G, c.bundle.P] ≫ chiTotal) ≫ a.bundle.p =
              γ[G, c.bundle.P] ≫ (c.bundle.p ≫ g) := by
            rw [Category.assoc, hchiBase]
          _ = (γ[G, c.bundle.P] ≫ c.bundle.p) ≫ g :=
            (Category.assoc _ _ _).symm
          _ = (snd G c.bundle.P ≫ c.bundle.p) ≫ g := by
            rw [c.bundle.invariant]
          _ = snd G c.bundle.P ≫ (c.bundle.p ≫ g) :=
            Category.assoc _ _ _
          _ = snd G c.bundle.P ≫ (chiTotal ≫ a.bundle.p) := by
            rw [hchiBase]
          _ = (snd G c.bundle.P ≫ chiTotal) ≫ a.bundle.p :=
            (Category.assoc _ _ _).symm
          _ = ((G ◁ chiTotal) ≫ snd G a.bundle.P) ≫ a.bundle.p := by
            rw [whiskerLeft_snd]
          _ = (G ◁ chiTotal) ≫ (snd G a.bundle.P ≫ a.bundle.p) :=
            Category.assoc _ _ _
          _ = (G ◁ chiTotal) ≫ (γ[G, a.bundle.P] ≫ a.bundle.p) := by
            rw [a.bundle.invariant]
          _ = ((G ◁ chiTotal) ≫ γ[G, a.bundle.P]) ≫ a.bundle.p :=
            (Category.assoc _ _ _).symm
    let chi : ClassifyingHom G c a :=
      { base := g
        total := chiTotal
        isPullback := hchiPb
        equivariant := hchiEquivariant }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · exact Functor.IsHomLift.map (p := (classifyingPrestack G).p) chi
    · apply ClassifyingHom.ext
      · exact hg
      · exact hchiTotal
    · intro chi' hchi'
      change ClassifyingHom G c a at chi'
      letI : IsHomLift (classifyingPrestack G).p g chi' := hchi'.1
      apply ClassifyingHom.ext
      · exact (IsHomLift.eq_of_isHomLift (classifyingPrestack G).p g chi').symm
      · apply phi.isPullback.hom_ext
        · have h := congrArg
            (fun q ↦ (show ClassifyingHom G c b from q).total) hchi'.2
          exact h.trans hchiTotal.symm
        · rw [chi'.isPullback.w]
          have hbase : chi'.base = g :=
            (IsHomLift.eq_of_isHomLift (classifyingPrestack G).p g chi').symm
          rw [hbase, hchiBase]

end classifyingPrestack

/-! ## Quotients by a fixed group scheme -/

variable (U : Over S) [ModObj G U]

/-- A principal `G`-bundle together with an equivariant map to `U`.  Fiberwise,
these are the objects of the quotient stack `[U/G]`. -/
structure ActionQuotientObj where
  /-- The underlying principal bundle. -/
  carrier : ClassifyingObj G
  /-- The equivariant map from its total space to `U`. -/
  map : carrier.bundle.P ⟶ U
  /-- Equivariance of the map to `U`. -/
  equivariant : IsModHom G map

/-- A morphism in `[U/G]` is a cartesian equivariant bundle morphism compatible
with the maps to `U`. -/
@[ext]
structure ActionQuotientHom (x y : ActionQuotientObj G U) where
  /-- The underlying cartesian morphism of principal bundles. -/
  carrier : ClassifyingHom G x.carrier y.carrier
  /-- Compatibility with the maps to `U`. -/
  map_naturality : carrier.total ≫ y.map = x.map

namespace ActionQuotientHom

variable {G U} {x y z : ActionQuotientObj G U}

/-- The identity quotient morphism. -/
@[simps]
def id (x : ActionQuotientObj G U) : ActionQuotientHom G U x x where
  carrier := ClassifyingHom.id x.carrier
  map_naturality := by simp [ClassifyingHom.id]

/-- Composition of quotient morphisms. -/
@[simps]
def comp (f : ActionQuotientHom G U x y) (g : ActionQuotientHom G U y z) :
    ActionQuotientHom G U x z where
  carrier := ClassifyingHom.comp f.carrier g.carrier
  map_naturality := by
    change (f.carrier.total ≫ g.carrier.total) ≫ z.map = x.map
    rw [Category.assoc, g.map_naturality, f.map_naturality]

end ActionQuotientHom

instance : Category (ActionQuotientObj G U) where
  Hom := ActionQuotientHom G U
  id := ActionQuotientHom.id
  comp := ActionQuotientHom.comp
  id_comp f := by ext <;> simp [ActionQuotientHom.id, ActionQuotientHom.comp]
  comp_id f := by ext <;> simp [ActionQuotientHom.id, ActionQuotientHom.comp]
  assoc f g h := by
    ext <;> simp [ActionQuotientHom.comp, ClassifyingHom.comp, Category.assoc]

/-- The quotient `[U/G]`, regarded first as a category fibered in groupoids over
`Scheme/S`. -/
abbrev actionQuotientPrestack : BasedCategory (Over S) where
  obj := ActionQuotientObj G U
  p :=
    { obj := fun x ↦ x.carrier.base
      map := fun f ↦ (show ActionQuotientHom G U _ _ from f).carrier.base
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

namespace actionQuotientPrestack

variable {G U}

/-- Forget the equivariant map from a quotient object, retaining its principal
bundle. -/
def forget : actionQuotientPrestack G U ⥤ᵇ classifyingPrestack G where
  obj x := x.carrier
  map q := q.carrier
  w := rfl

/-- Principal bundles with an equivariant map to `U` are stable under base
change, so `[U/G]` is a prestack. -/
noncomputable instance projection_isFiberedInGroupoids :
    (actionQuotientPrestack G U).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    change ActionQuotientObj G U at a
    obtain ⟨b, phi, hphi⟩ :=
      Functor.IsFiberedInGroupoids.exists_isHomLift
        (p := (classifyingPrestack G).p) (a := a.carrier) f
    change ClassifyingObj G at b
    change ClassifyingHom G b a.carrier at phi
    letI : IsModHom G phi.total := phi.equivariant
    letI : IsModHom G a.map := a.equivariant
    let x : ActionQuotientObj G U :=
      { carrier := b
        map := phi.total ≫ a.map
        equivariant := inferInstance }
    let Phi : ActionQuotientHom G U x a :=
      { carrier := phi
        map_naturality := rfl }
    refine ⟨x, Phi, ?_⟩
    exact IsHomLift.of_fac (actionQuotientPrestack G U).p f Phi
      (IsHomLift.domain_eq (classifyingPrestack G).p f phi)
      (IsHomLift.codomain_eq (classifyingPrestack G).p f phi)
      (by simpa only using IsHomLift.fac (classifyingPrestack G).p f phi)
  · intro x y phi
    change ActionQuotientObj G U at x y
    change ActionQuotientHom G U x y at phi
    letI hphi : IsHomLift (classifyingPrestack G).p phi.carrier.base
        phi.carrier := Functor.IsHomLift.map (p := (classifyingPrestack G).p) phi.carrier
    letI hcart : IsStronglyCartesian (classifyingPrestack G).p
        phi.carrier.base phi.carrier :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        (classifyingPrestack G).p phi.carrier.base phi.carrier
    letI hphiQuotient : IsHomLift (actionQuotientPrestack G U).p
        ((actionQuotientPrestack G U).p.map phi) phi :=
      Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p) phi
    constructor
    intro z g psi hpsi
    change ActionQuotientObj G U at z
    change ActionQuotientHom G U z y at psi
    have hg : g ≫ phi.carrier.base = psi.carrier.base := by
      exact IsHomLift.eq_of_isHomLift (actionQuotientPrestack G U).p
        (g ≫ (actionQuotientPrestack G U).p.map phi) psi
    letI hpsiCarrier : IsHomLift (classifyingPrestack G).p
        (g ≫ phi.carrier.base) psi.carrier := by
      rw [hg]
      exact Functor.IsHomLift.map (p := (classifyingPrestack G).p) psi.carrier
    let chiCarrier : ClassifyingHom G z.carrier x.carrier :=
      IsStronglyCartesian.map (classifyingPrestack G).p phi.carrier.base
        phi.carrier (g := g) (f' := g ≫ phi.carrier.base) rfl psi.carrier
    have hchiCarrier : IsHomLift (classifyingPrestack G).p g chiCarrier := by
      exact IsStronglyCartesian.map_isHomLift (classifyingPrestack G).p
        phi.carrier.base phi.carrier (g := g) (f' := g ≫ phi.carrier.base)
          rfl psi.carrier
    have hfac : ClassifyingHom.comp chiCarrier phi.carrier = psi.carrier := by
      exact IsStronglyCartesian.fac (classifyingPrestack G).p
        phi.carrier.base phi.carrier (g := g) (f' := g ≫ phi.carrier.base)
          rfl psi.carrier
    have hmap : chiCarrier.total ≫ x.map = z.map := by
      calc
        chiCarrier.total ≫ x.map =
            chiCarrier.total ≫ (phi.carrier.total ≫ y.map) := by
          rw [phi.map_naturality]
        _ = (chiCarrier.total ≫ phi.carrier.total) ≫ y.map :=
          (Category.assoc _ _ _).symm
        _ = psi.carrier.total ≫ y.map := by
          rw [show chiCarrier.total ≫ phi.carrier.total = psi.carrier.total from
            congrArg ClassifyingHom.total hfac]
        _ = z.map := psi.map_naturality
    let chi : ActionQuotientHom G U z x :=
      { carrier := chiCarrier
        map_naturality := hmap }
    refine ⟨chi, ⟨?_, ?_⟩, ?_⟩
    · have hbase := IsHomLift.eq_of_isHomLift
          (classifyingPrestack G).p g chiCarrier
      rw [hbase]
      exact Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p) chi
    · apply ActionQuotientHom.ext
      exact hfac
    · intro chi' hchi'
      change ActionQuotientHom G U z x at chi'
      apply ActionQuotientHom.ext
      letI hchi'Carrier : IsHomLift (classifyingPrestack G).p g chi'.carrier := by
        letI : IsHomLift (actionQuotientPrestack G U).p g chi' := hchi'.1
        have hbase := IsHomLift.eq_of_isHomLift
          (actionQuotientPrestack G U).p g chi'
        rw [hbase]
        exact Functor.IsHomLift.map (p := (classifyingPrestack G).p) chi'.carrier
      apply IsStronglyCartesian.ext (classifyingPrestack G).p
        phi.carrier.base phi.carrier g
      exact (congrArg ActionQuotientHom.carrier hchi'.2).trans hfac.symm

end actionQuotientPrestack

/-! ### Trivial objects and gauge transformations in a quotient stack -/

namespace ActionQuotientObj

variable {G U T} [Smooth G.hom] [IsAffineHom G.hom]

/-- The quotient-stack object over `T` induced by a map `u : T → U`: its
underlying torsor is `G ×ₛ T`, and its equivariant map is `(g,t) ↦ g • u(t)`. -/
noncomputable def trivial (u : T ⟶ U) : ActionQuotientObj G U where
  carrier :=
    { base := T
      bundle := GlobalPrincipalBundle.trivial G T }
  map := GlobalPrincipalBundle.trivialActionMapTo (G := G) u
  equivariant := GlobalPrincipalBundle.trivialActionMapTo_equivariant (G := G) u

end ActionQuotientObj

namespace ActionQuotientHom

variable {G U T} [Smooth G.hom] [IsAffineHom G.hom]

/-- A group-valued section `m : T → G` gives a gauge transformation from
the trivial quotient object defined by `m • u` to the one defined by `u`.
The equality argument permits a chosen presentation of the source map. -/
noncomputable def trivialGaugeOfEq (v : T ⟶ U) (m : T ⟶ G)
    (u : T ⟶ U) (h : m • u = v) :
    ActionQuotientHom G U (ActionQuotientObj.trivial (G := G) v)
      (ActionQuotientObj.trivial (G := G) u) where
  carrier :=
    { base := 𝟙 T
      total := GlobalPrincipalBundle.trivialRightTranslate (G := G) m
      isPullback := by
        letI : IsIso (GlobalPrincipalBundle.trivialRightTranslate (G := G) m) :=
          inferInstance
        letI : IsIso (𝟙 T) := by infer_instance
        apply IsPullback.of_horiz_isIso
        constructor
        change GlobalPrincipalBundle.trivialRightTranslate (G := G) m ≫
            GlobalPrincipalBundle.trivialSnd G T =
          GlobalPrincipalBundle.trivialSnd G T ≫ 𝟙 T
        simpa using GlobalPrincipalBundle.trivialRightTranslate_snd (G := G) m
      equivariant :=
        GlobalPrincipalBundle.trivialRightTranslate_equivariant (G := G) m }
  map_naturality := by
    change GlobalPrincipalBundle.trivialRightTranslate (G := G) m ≫
        GlobalPrincipalBundle.trivialActionMapTo (G := G) u =
      GlobalPrincipalBundle.trivialActionMapTo (G := G) v
    rw [GlobalPrincipalBundle.trivialRightTranslate_actionMap (G := G) m u, h]

end ActionQuotientHom

end AlgebraicGeometry.Scheme
