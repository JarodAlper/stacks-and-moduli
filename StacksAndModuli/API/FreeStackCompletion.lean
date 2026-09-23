module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# A free stack completion

This file constructs a category over a site by freely adjoining cartesian lifts,
effective objects for descent diagrams, and glued morphisms, then quotienting by the
corresponding equations.  The resulting based category is a stack.  Its universal
property is intentionally not asserted here.
-/

@[expose] public section

-- Every use of the type-level quotient below is written `_root_.Quotient`: this file lives
-- in the `CategoryTheory` namespace, where `Quotient` otherwise resolves to
-- `CategoryTheory.Quotient` (the quotient of a category by a `HomRel`) as soon as that
-- module is transitively imported.
open CategoryTheory CategoryTheory.Functor

universe v u w z yv yu

namespace CategoryTheory.BasedCategory.FreeStackCompletion

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (X : BasedCategory.{w,z} C)

/- One strictly-positive, untyped syntax is used because Lean does not support the
indexed inductive-inductive presentation (objects whose gluing constructor mentions
arrows, and arrows indexed by objects) directly. The mutually inductive predicates
below recover the typing. -/
inductive Pre : Type (max u v w z)
  | objIncl (a : X.obj)
  | objPull {S T : C} (b : Pre) (f : S ⟶ T)
  | objGlue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
  | homIncl {a b : X.obj} (f : a ⟶ b)
  | homId (a : Pre)
  | homComp (f g : Pre)
  | homPullMap {S T : C} (b : Pre) (f : S ⟶ T)
  | homFactor {R S T : C} (cart phi : Pre) (f : S ⟶ T) (g : R ⟶ S)
  | homGlueMap {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
      (q : R.1.arrows.category)
  | homGlue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
      (a b : Pre) (eta theta : ∀ q : R.1.arrows.category, Pre)
      (etaNat thetaNat : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
  | relRefl (f : Pre)
  | relBaseChange (f : Pre)
  | relSymm (r : Pre)
  | relTrans (r s : Pre)
  | relCompCongr (r s : Pre)
  | relIdComp (f : Pre)
  | relCompId (f : Pre)
  | relAssoc (f g h : Pre)
  | relInclId (a : X.obj)
  | relInclComp {a b c : X.obj} (f : a ⟶ b) (g : b ⟶ c)
  | relFactorFac {R S T : C} (cart phi : Pre) (f : S ⟶ T) (g : R ⟶ S)
  | relFactorUnique {R S T : C} (cart phi chi fac : Pre) (f : S ⟶ T) (g : R ⟶ S)
  | relGlueMapNatural {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
      {q r : R.1.arrows.category} (k : q ⟶ r)
  | relHomGlueFac {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
      (a b : Pre) (eta theta : ∀ q : R.1.arrows.category, Pre)
      (etaNat thetaNat : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (q : R.1.arrows.category)
  | relHomGlueUnique {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (idRel : ∀ q : R.1.arrows.category, Pre)
      (compRel : ∀ {q r s : R.1.arrows.category}, (q ⟶ r) → (r ⟶ s) → Pre)
      (a b : Pre) (eta theta : ∀ q : R.1.arrows.category, Pre)
      (etaNat thetaNat : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre)
      (phi : Pre) (fac : ∀ q : R.1.arrows.category, Pre)

mutual

/-- Well-typed formal objects. -/
inductive IsObj : Pre J X → C → Type (max u v w z)
  | incl (a : X.obj) : IsObj (.objIncl a) (X.p.obj a)
  | pull {S T : C} {b : Pre J X} (hb : IsObj b T) (f : S ⟶ T) :
      IsObj (.objPull b f) S
  | glue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (hDobj : ∀ q, IsObj (Dobj q) q.obj.left)
      (hDmap : ∀ {q r} (k : q ⟶ r), IsHom (Dmap k) (Dobj q) (Dobj r) k.hom.left)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hId : ∀ q, IsRel (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
        (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
      (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
        IsRel (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
          (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left) :
      IsObj (.objGlue R Dobj Dmap idRel compRel) S

/-- Well-typed formal arrows. -/
inductive IsHom : Pre J X → Pre J X → Pre J X →
    {S T : C} → (S ⟶ T) → Type (max u v w z)
  | incl {a b : X.obj} (f : a ⟶ b) :
      IsHom (.homIncl f) (.objIncl a) (.objIncl b) (X.p.map f)
  | id {S : C} {a : Pre J X} (ha : IsObj a S) : IsHom (.homId a) a a (𝟙 S)
  | comp {R S T : C} {a b c f g : Pre J X} {p : R ⟶ S} {q : S ⟶ T}
      (hf : IsHom f a b p) (hg : IsHom g b c q) :
      IsHom (.homComp f g) a c (p ≫ q)
  | pullMap {S T : C} {b : Pre J X} (hb : IsObj b T) (f : S ⟶ T) :
      IsHom (.homPullMap b f) (.objPull b f) b f
  | factor {R S T : C} {a b c cart phi : Pre J X} {p : R ⟶ T}
      (f : S ⟶ T) (g : R ⟶ S)
      (hcart : IsHom cart a b f) (hphi : IsHom phi c b p) (hp : p = g ≫ f) :
      IsHom (.homFactor cart phi f g) c a g
  | glueMap {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hglue : IsObj (.objGlue R Dobj Dmap idRel compRel) S)
      (q : R.1.arrows.category) :
      IsHom (.homGlueMap R Dobj Dmap idRel compRel q) (Dobj q)
        (.objGlue R Dobj Dmap idRel compRel) q.obj.hom
  | homGlue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      {a b : Pre J X} (eta theta : ∀ q : R.1.arrows.category, Pre J X)
      (ha : IsObj a S) (hb : IsObj b S)
      (hDobj : ∀ q, IsObj (Dobj q) q.obj.left)
      (hDmap : ∀ {q r} (k : q ⟶ r), IsHom (Dmap k) (Dobj q) (Dobj r) k.hom.left)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hId : ∀ q, IsRel (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
        (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
      (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
        IsRel (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
          (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
      (heta : ∀ q, IsHom (eta q) (Dobj q) a q.obj.hom)
      (htheta : ∀ q, IsHom (theta q) (Dobj q) b q.obj.hom)
      (etaNat thetaNat : ∀ {q r} (k : q ⟶ r), Pre J X)
      (hetaNat : ∀ {q r} (k : q ⟶ r),
        IsRel (etaNat k) (.homComp (Dmap k) (eta r)) (eta q) (Dobj q) a
          (k.hom.left ≫ r.obj.hom) q.obj.hom)
      (hthetaNat : ∀ {q r} (k : q ⟶ r),
        IsRel (thetaNat k) (.homComp (Dmap k) (theta r)) (theta q) (Dobj q) b
          (k.hom.left ≫ r.obj.hom) q.obj.hom) :
      IsHom (.homGlue R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat) a b (𝟙 S)

/-- Formal equations. Two base arrows are retained so that equations whose base maps
are propositionally, but not definitionally, equal are literal generators. -/
inductive IsRel : Pre J X → Pre J X → Pre J X → Pre J X → Pre J X →
    {S T : C} → (S ⟶ T) → (S ⟶ T) → Type (max u v w z)
  | refl {S T : C} {a b phi : Pre J X} {f : S ⟶ T} (hphi : IsHom phi a b f) :
      IsRel (.relRefl phi) phi phi a b f f
  | baseChange {S T : C} {a b phi : Pre J X} {f g : S ⟶ T}
      (hphi : IsHom phi a b f) (hfg : f = g) :
      IsRel (.relBaseChange phi) phi phi a b f g
  | symm {S T : C} {a b phi psi r : Pre J X} {f g : S ⟶ T}
      (hr : IsRel r phi psi a b f g) : IsRel (.relSymm r) psi phi a b g f
  | trans {S T : C} {a b phi psi chi r s : Pre J X} {f g h : S ⟶ T}
      (hr : IsRel r phi psi a b f g) (hs : IsRel s psi chi a b g h) :
      IsRel (.relTrans r s) phi chi a b f h
  | compCongr {R S T : C} {a b c phi phi' psi psi' r s : Pre J X}
      {f f' : R ⟶ S} {g g' : S ⟶ T}
      (hr : IsRel r phi phi' a b f f') (hs : IsRel s psi psi' b c g g') :
      IsRel (.relCompCongr r s) (.homComp phi psi) (.homComp phi' psi') a c
        (f ≫ g) (f' ≫ g')
  | idComp {S T : C} {a b phi : Pre J X} {f : S ⟶ T}
      (ha : IsObj a S) (hphi : IsHom phi a b f) :
      IsRel (.relIdComp phi) (.homComp (.homId a) phi) phi a b (𝟙 S ≫ f) f
  | compId {S T : C} {a b phi : Pre J X} {f : S ⟶ T}
      (hb : IsObj b T) (hphi : IsHom phi a b f) :
      IsRel (.relCompId phi) (.homComp phi (.homId b)) phi a b (f ≫ 𝟙 T) f
  | assoc {Q R S T : C} {a b c d phi psi chi : Pre J X}
      {f : Q ⟶ R} {g : R ⟶ S} {h : S ⟶ T}
      (hphi : IsHom phi a b f) (hpsi : IsHom psi b c g) (hchi : IsHom chi c d h) :
      IsRel (.relAssoc phi psi chi) (.homComp (.homComp phi psi) chi)
        (.homComp phi (.homComp psi chi)) a d ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | inclId (a : X.obj) :
      IsRel (.relInclId a) (.homIncl (𝟙 a)) (.homId (.objIncl a))
        (.objIncl a) (.objIncl a) (X.p.map (𝟙 a)) (𝟙 (X.p.obj a))
  | inclComp {a b c : X.obj} (f : a ⟶ b) (g : b ⟶ c) :
      IsRel (.relInclComp f g) (.homIncl (f ≫ g)) (.homComp (.homIncl f) (.homIncl g))
        (.objIncl a) (.objIncl c) (X.p.map (f ≫ g)) (X.p.map f ≫ X.p.map g)
  | factorFac {R S T : C} {a b c cart phi : Pre J X} {p : R ⟶ T}
      (f : S ⟶ T) (g : R ⟶ S)
      (hcart : IsHom cart a b f) (hphi : IsHom phi c b p) (hp : p = g ≫ f) :
      IsRel (.relFactorFac cart phi f g)
        (.homComp (.homFactor cart phi f g) cart) phi c b (g ≫ f) p
  | factorUnique {R S T : C} {a b c cart phi chi fac : Pre J X}
      {p : R ⟶ T} {q : R ⟶ S}
      (f : S ⟶ T) (g : R ⟶ S) (hcart : IsHom cart a b f)
      (hphi : IsHom phi c b p) (hp : p = g ≫ f) (hchi : IsHom chi c a q)
      (hq : q = g) (hfac : IsRel fac (.homComp chi cart) phi c b (q ≫ f) p) :
      IsRel (.relFactorUnique cart phi chi fac f g) chi (.homFactor cart phi f g)
        c a q g
  | glueMapNatural {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hglue : IsObj (.objGlue R Dobj Dmap idRel compRel) S)
      {q r : R.1.arrows.category}
      (k : q ⟶ r) :
      IsRel (.relGlueMapNatural R Dobj Dmap idRel compRel k)
        (.homComp (Dmap k) (.homGlueMap R Dobj Dmap idRel compRel r))
        (.homGlueMap R Dobj Dmap idRel compRel q) (Dobj q)
        (.objGlue R Dobj Dmap idRel compRel)
        (k.hom.left ≫ r.obj.hom) q.obj.hom
  | homGlueFac {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      {a b : Pre J X} (eta theta : ∀ q : R.1.arrows.category, Pre J X)
      (etaNat thetaNat : ∀ {q r} (k : q ⟶ r), Pre J X)
      (hglue : IsHom
        (.homGlue R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat) a b (𝟙 S))
      (heta : ∀ q, IsHom (eta q) (Dobj q) a q.obj.hom)
      (htheta : ∀ q, IsHom (theta q) (Dobj q) b q.obj.hom)
      (q : R.1.arrows.category) :
      IsRel (.relHomGlueFac R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat q)
        (theta q) (.homComp (eta q)
          (.homGlue R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat))
        (Dobj q) b q.obj.hom (q.obj.hom ≫ 𝟙 S)
  | homGlueUnique {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      {a b : Pre J X} (eta theta : ∀ q : R.1.arrows.category, Pre J X)
      (etaNat thetaNat : ∀ {q r} (k : q ⟶ r), Pre J X)
      {phi : Pre J X} (fac : ∀ q : R.1.arrows.category, Pre J X)
      (hglue : IsHom
        (.homGlue R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat) a b (𝟙 S))
      (hphi : IsHom phi a b (𝟙 S))
      (hfac : ∀ q, IsRel (fac q) (theta q) (.homComp (eta q) phi)
        (Dobj q) b q.obj.hom (q.obj.hom ≫ 𝟙 S)) :
      IsRel (.relHomGlueUnique R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat phi fac)
        phi (.homGlue R Dobj Dmap idRel compRel a b eta theta etaNat thetaNat)
        a b (𝟙 S) (𝟙 S)

end

lemma IsRel.base_eq {r phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    (h : IsRel J X r phi psi a b f g) : f = g := by
  cases h with
  | refl => rfl
  | baseChange hphi hfg => exact hfg
  | symm hr => exact (IsRel.base_eq hr).symm
  | trans hr hs => exact (IsRel.base_eq hr).trans (IsRel.base_eq hs)
  | compCongr hr hs => simp [IsRel.base_eq hr, IsRel.base_eq hs]
  | idComp => simp
  | compId => simp
  | assoc => simp
  | inclId => simp
  | inclComp => simp
  | factorFac f g hcart hphi hp => exact hp.symm
  | factorUnique f g hcart hphi hp hchi hq hfac => exact hq
  | glueMapNatural R Dobj Dmap idRel compRel hglue k => exact k.hom.w
  | homGlueFac => simp
  | homGlueUnique => rfl

/-- Objects of the free stack completion, with their object of the base retained. -/
structure Obj where
  base : C
  term : Pre J X
  valid : Nonempty (IsObj J X term base)

namespace Obj

variable {J X}

/-- Change the displayed base of a formal object along a proved equality. -/
def normalize (S : C) (a : Obj J X) (h : a.base = S) : Obj J X where
  base := S
  term := a.term
  valid := h ▸ a.valid

@[simp]
lemma normalize_eq (a : Obj J X) : normalize a.base a rfl = a := rfl

lemma normalize_eq_self (S : C) (a : Obj J X) (h : a.base = S) :
    normalize S a h = a := by
  subst S
  rfl

end Obj

/-- Representatives of arrows in the free stack completion. -/
structure RawHom (a b : Obj J X) where
  base : a.base ⟶ b.base
  term : Pre J X
  valid : Nonempty (IsHom J X term a.term b.term base)

namespace RawHom

variable {J X}

/-- The generated equivalence relation on formal arrows. -/
def Rel {a b : Obj J X} (f g : RawHom J X a b) : Prop :=
  ∃ rho, Nonempty (IsRel J X rho f.term g.term a.term b.term f.base g.base)

lemma rel_refl {a b : Obj J X} (f : RawHom J X a b) : Rel f f :=
  ⟨.relRefl f.term, f.valid.map IsRel.refl⟩

lemma rel_symm {a b : Obj J X} {f g : RawHom J X a b} (h : Rel f g) : Rel g f := by
  obtain ⟨rho, ⟨hrho⟩⟩ := h
  exact ⟨.relSymm rho, ⟨.symm hrho⟩⟩

lemma rel_trans {a b : Obj J X} {f g h : RawHom J X a b} (hfg : Rel f g)
    (hgh : Rel g h) : Rel f h := by
  obtain ⟨rho, ⟨hrho⟩⟩ := hfg
  obtain ⟨sigma, ⟨hsigma⟩⟩ := hgh
  exact ⟨.relTrans rho sigma, ⟨.trans hrho hsigma⟩⟩

instance setoid (a b : Obj J X) : Setoid (RawHom J X a b) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

def id (a : Obj J X) : RawHom J X a a where
  base := 𝟙 a.base
  term := .homId a.term
  valid := a.valid.map IsHom.id

def comp {a b c : Obj J X} (f : RawHom J X a b) (g : RawHom J X b c) :
    RawHom J X a c where
  base := f.base ≫ g.base
  term := .homComp f.term g.term
  valid := Nonempty.map2 IsHom.comp f.valid g.valid

lemma comp_rel {a b c : Obj J X} {f f' : RawHom J X a b} {g g' : RawHom J X b c}
    (hf : Rel f f') (hg : Rel g g') : Rel (comp f g) (comp f' g') := by
  obtain ⟨rho, ⟨hrho⟩⟩ := hf
  obtain ⟨sigma, ⟨hsigma⟩⟩ := hg
  exact ⟨.relCompCongr rho sigma, ⟨.compCongr hrho hsigma⟩⟩

end RawHom

/-- Morphisms in the free stack are formal arrows modulo the generated equations. -/
abbrev Hom (a b : Obj J X) := _root_.Quotient (RawHom.setoid (J := J) (X := X) a b)

namespace Hom

variable {J X}

def id (a : Obj J X) : Hom J X a a := ⟦RawHom.id a⟧

def comp {a b c : Obj J X} (f : Hom J X a b) (g : Hom J X b c) : Hom J X a c :=
  _root_.Quotient.map₂ RawHom.comp (fun _ _ hf _ _ hg ↦ RawHom.comp_rel hf hg) f g

@[simp]
lemma comp_mk {a b c : Obj J X} (f : RawHom J X a b) (g : RawHom J X b c) :
    comp (⟦f⟧ : Hom J X a b) (⟦g⟧ : Hom J X b c) = ⟦RawHom.comp f g⟧ := rfl

end Hom

instance : Category (Obj J X) where
  Hom := Hom J X
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro a b f
    induction f using _root_.Quotient.inductionOn with
    | _ f =>
      apply _root_.Quotient.sound
      exact ⟨.relIdComp f.term,
        Nonempty.map2 IsRel.idComp a.valid f.valid⟩
  comp_id := by
    intro a b f
    induction f using _root_.Quotient.inductionOn with
    | _ f =>
      apply _root_.Quotient.sound
      exact ⟨.relCompId f.term,
        Nonempty.map2 IsRel.compId b.valid f.valid⟩
  assoc := by
    intro a b c d f g h
    induction f using _root_.Quotient.inductionOn with
    | _ f =>
      induction g using _root_.Quotient.inductionOn with
      | _ g =>
        induction h using _root_.Quotient.inductionOn with
        | _ h =>
          apply _root_.Quotient.sound
          exact ⟨.relAssoc f.term g.term h.term,
            ⟨.assoc (Classical.choice f.valid) (Classical.choice g.valid)
              (Classical.choice h.valid)⟩⟩

/-- Projection of the free stack completion to the original base category. -/
def proj : Obj J X ⥤ C where
  obj a := a.base
  map {a b} f := _root_.Quotient.lift RawHom.base
    (fun f g h ↦ IsRel.base_eq (J := J) (X := X)
      (Classical.choice (Classical.choose_spec h))) f
  map_id _ := rfl
  map_comp f g := by
    induction f using _root_.Quotient.inductionOn with
    | _ f =>
      induction g using _root_.Quotient.inductionOn with
      | _ g => rfl

@[simp]
lemma proj_map_mk {a b : Obj J X} (f : RawHom J X a b) :
    (proj J X).map (⟦f⟧ : a ⟶ b) = f.base := rfl

/-- The free stack completion as a based category. -/
def completion : BasedCategory C where
  obj := Obj J X
  p := proj J X

/-- The canonical inclusion into the free stack completion. -/
def inclusion : X ⥤ᵇ completion J X where
  obj a := ⟨X.p.obj a, .objIncl a, ⟨.incl a⟩⟩
  map {a b} f := ⟦⟨X.p.map f, .homIncl f, ⟨.incl f⟩⟩⟧
  map_id a := by
    apply _root_.Quotient.sound
    exact ⟨.relInclId a, ⟨.inclId a⟩⟩
  map_comp f g := by
    apply _root_.Quotient.sound
    exact ⟨.relInclComp f g, ⟨.inclComp f g⟩⟩
  w := by
    refine CategoryTheory.Functor.ext_of_iso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro a b f
        change X.p.map f ≫ 𝟙 _ = 𝟙 _ ≫ X.p.map f
        simp))
      (fun _ ↦ rfl) (fun _ ↦ rfl)

namespace Hom

variable {J X}

/-- A chosen representative of a quotient arrow. -/
noncomputable def out {a b : Obj J X} (f : a ⟶ b) : RawHom J X a b :=
  _root_.Quotient.out f

@[simp]
lemma mk_out {a b : Obj J X} (f : a ⟶ b) :
    (⟦out f⟧ : a ⟶ b) = f := _root_.Quotient.out_eq f

@[simp]
lemma proj_map_eq_out_base {a b : Obj J X} (f : a ⟶ b) :
    (proj J X).map f = (out f).base := by
  exact (congrArg (proj J X).map (mk_out f)).symm.trans (proj_map_mk J X (out f))

/-- Normalize a chosen representative to a specified base arrow which the quotient
arrow lifts. -/
noncomputable def normalize {a b : Obj J X} (f : a.base ⟶ b.base) (phi : a ⟶ b)
    (hLift : IsHomLift (proj J X) f phi) : RawHom J X a b where
  base := f
  term := (out phi).term
  valid := by
    have hbase : f = (out phi).base :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (proj J X) _ _ f phi hLift).trans
        (proj_map_eq_out_base phi)
    exact hbase.symm ▸ (out phi).valid

@[simp]
lemma mk_normalize {a b : Obj J X} (f : a.base ⟶ b.base) (phi : a ⟶ b)
    (hLift : IsHomLift (proj J X) f phi) : (⟦normalize f phi hLift⟧ : a ⟶ b) = phi := by
  have hbase : f = (out phi).base :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (proj J X) _ _ f phi hLift).trans
      (proj_map_eq_out_base phi)
  calc
    (⟦normalize f phi hLift⟧ : a ⟶ b) = ⟦out phi⟧ := by
      apply _root_.Quotient.sound
      exact ⟨.relBaseChange (out phi).term,
        (normalize f phi hLift).valid.map (fun h ↦ .baseChange h hbase)⟩
    _ = phi := mk_out phi

end Hom

namespace Descent

variable {J X}

/-- Replace the objects of a descent functor by definitionally correctly based
copies.  The functor is pointwise equal to the original one. -/
noncomputable def normalizeFunctor {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left) :
    R.arrows.category ⥤ Obj J X where
  obj q := Obj.normalize q.obj.left (D.obj q) (hDobj q)
  map {q r} k :=
    eqToHom (Obj.normalize_eq_self q.obj.left (D.obj q) (hDobj q)) ≫
      D.map k ≫
      eqToHom (Obj.normalize_eq_self r.obj.left (D.obj r) (hDobj r)).symm
  map_id q := by simp
  map_comp k l := by simp [Category.assoc]

@[simp]
lemma normalizeFunctor_obj_base {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (q : R.arrows.category) :
    ((normalizeFunctor D hDobj).obj q).base = q.obj.left := rfl

lemma normalizeFunctor_map_isHomLift {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    {q r : R.arrows.category} (k : q ⟶ r) :
    IsHomLift (proj J X) k.hom.left ((normalizeFunctor D hDobj).map k) := by
  letI := hDmap k
  dsimp [normalizeFunctor]
  infer_instance

/-- A representative of a normalized descent arrow with its base definitionally
equal to the arrow in the sieve. -/
noncomputable def rawMap {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    {q r : R.arrows.category} (k : q ⟶ r) :
    RawHom J X ((normalizeFunctor D hDobj).obj q) ((normalizeFunctor D hDobj).obj r) :=
  Hom.normalize k.hom.left ((normalizeFunctor D hDobj).map k)
    (normalizeFunctor_map_isHomLift D hDobj hDmap k)

@[simp]
lemma mk_rawMap {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    {q r : R.arrows.category} (k : q ⟶ r) :
    (⟦rawMap D hDobj hDmap k⟧ :
      (normalizeFunctor D hDobj).obj q ⟶ (normalizeFunctor D hDobj).obj r) =
      (normalizeFunctor D hDobj).map k :=
  Hom.mk_normalize _ _ _

lemma rawMap_rel_id {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    (q : R.arrows.category) :
    RawHom.Rel (rawMap D hDobj hDmap (𝟙 q))
      (RawHom.id ((normalizeFunctor D hDobj).obj q)) := by
  have h :
      (⟦rawMap D hDobj hDmap (𝟙 q)⟧ :
        (normalizeFunctor D hDobj).obj q ⟶ (normalizeFunctor D hDobj).obj q) =
      ⟦RawHom.id ((normalizeFunctor D hDobj).obj q)⟧ := by
    rw [mk_rawMap, (normalizeFunctor D hDobj).map_id]
    rfl
  exact _root_.Quotient.exact h

lemma rawMap_rel_comp {S : C} {R : Sieve S}
    (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    {q r s : R.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
    RawHom.Rel
      (RawHom.comp (rawMap D hDobj hDmap k) (rawMap D hDobj hDmap l))
      (rawMap D hDobj hDmap (k ≫ l)) := by
  have h :
      (⟦RawHom.comp (rawMap D hDobj hDmap k) (rawMap D hDobj hDmap l)⟧ :
        (normalizeFunctor D hDobj).obj q ⟶ (normalizeFunctor D hDobj).obj s) =
      (⟦rawMap D hDobj hDmap (k ≫ l)⟧ :
        (normalizeFunctor D hDobj).obj q ⟶ (normalizeFunctor D hDobj).obj s) := by
    calc
      _ =
          (⟦rawMap D hDobj hDmap k⟧ :
              (normalizeFunctor D hDobj).obj q ⟶ (normalizeFunctor D hDobj).obj r) ≫
            (⟦rawMap D hDobj hDmap l⟧ :
              (normalizeFunctor D hDobj).obj r ⟶ (normalizeFunctor D hDobj).obj s) := rfl
      _ = (normalizeFunctor D hDobj).map k ≫
          (normalizeFunctor D hDobj).map l := by rw [mk_rawMap, mk_rawMap]
      _ = (normalizeFunctor D hDobj).map (k ≫ l) :=
        ((normalizeFunctor D hDobj).map_comp k l).symm
      _ = _ := (mk_rawMap D hDobj hDmap (k ≫ l)).symm
  exact _root_.Quotient.exact h

end Descent


/-- The formal cartesian factorization generators make the completion a prestack. -/
noncomputable instance proj_isFiberedInGroupoids :
    (proj J X).IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    let b : Obj J X :=
      ⟨R, .objPull a.term f, a.valid.map (fun ha ↦ .pull ha f)⟩
    let phi : RawHom J X b a :=
      ⟨f, .homPullMap a.term f, a.valid.map (fun ha ↦ .pullMap ha f)⟩
    have hphi : IsHomLift (proj J X) f (⟦phi⟧ : b ⟶ a) := by
      refine IsHomLift.of_fac' (proj J X) f (⟦phi⟧ : b ⟶ a) rfl rfl ?_
      change f = eqToHom rfl ≫ f ≫ eqToHom rfl
      simp
    exact ⟨b, ⟦phi⟧, hphi⟩
  isStronglyCartesian {a b} phi := by
    induction phi using _root_.Quotient.inductionOn with
    | _ cart =>
      rw [proj_map_mk]
      have hcartLift : IsHomLift (proj J X) cart.base (⟦cart⟧ : a ⟶ b) := by
        refine IsHomLift.of_fac' (proj J X) cart.base (⟦cart⟧ : a ⟶ b) rfl rfl ?_
        change cart.base = eqToHom rfl ≫ cart.base ≫ eqToHom rfl
        simp
      refine { toIsHomLift := hcartLift, universal_property' := ?_ }
      intro c g phi'
      induction phi' using _root_.Quotient.inductionOn with
      | _ phi =>
        intro hphiLift
        letI := hphiLift
        have hbase : g ≫ cart.base = phi.base :=
          IsHomLift.eq_of_isHomLift (proj J X) (g ≫ cart.base) (⟦phi⟧ : c ⟶ b)
        let chi : RawHom J X c a :=
          ⟨g, .homFactor cart.term phi.term cart.base g,
            ⟨.factor cart.base g (Classical.choice cart.valid)
              (Classical.choice phi.valid) hbase.symm⟩⟩
        have hchiLift : IsHomLift (proj J X) g (⟦chi⟧ : c ⟶ a) := by
          refine IsHomLift.of_fac' (proj J X) g (⟦chi⟧ : c ⟶ a) rfl rfl ?_
          change g = eqToHom rfl ≫ g ≫ eqToHom rfl
          simp
        refine ⟨⟦chi⟧, ⟨hchiLift, ?_⟩, ?_⟩
        · apply _root_.Quotient.sound
          exact ⟨.relFactorFac cart.term phi.term cart.base g,
            ⟨.factorFac cart.base g (Classical.choice cart.valid)
              (Classical.choice phi.valid) hbase.symm⟩⟩
        · intro chi' hchi'
          induction chi' using _root_.Quotient.inductionOn with
          | _ chi' =>
            rcases hchi' with ⟨hchiLift, hchiFac⟩
            letI := hchiLift
            have hchiBase : g = chi'.base :=
              IsHomLift.eq_of_isHomLift (proj J X) g (⟦chi'⟧ : c ⟶ a)
            have hrel : RawHom.Rel
                (RawHom.comp chi' cart) phi := _root_.Quotient.exact hchiFac
            obtain ⟨fac, ⟨hfac⟩⟩ := hrel
            apply _root_.Quotient.sound
            exact ⟨.relFactorUnique cart.term phi.term chi'.term fac cart.base g,
              ⟨.factorUnique cart.base g (Classical.choice cart.valid)
                (Classical.choice phi.valid) hbase.symm
                (Classical.choice chi'.valid) hchiBase.symm hfac⟩⟩

/-- The object-gluing half of the stack axiom for the free completion. -/
theorem completion_exists_gluing_obj {S : C} {R : Sieve S}
    (hR : R ∈ J S) (D : R.arrows.category ⥤ Obj J X)
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k)) :
    ∃ (a : Obj J X) (_ : (proj J X).obj a = S)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q : R.arrows.category, IsHomLift (proj J X) q.obj.hom (ε q)) ∧
      ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r), D.map k ≫ ε r = ε q := by
  let W : J.Cover S := ⟨R, hR⟩
  let D' : W.1.arrows.category ⥤ Obj J X := Descent.normalizeFunctor D hDobj
  let Dobj : W.1.arrows.category → Pre J X := fun q ↦ (D'.obj q).term
  let Dmap : ∀ {q r : W.1.arrows.category}, (q ⟶ r) → Pre J X :=
    fun {_ _} k ↦ (Descent.rawMap D hDobj hDmap k).term
  have hDobj' : ∀ q, IsObj J X (Dobj q) q.obj.left :=
    fun q ↦ Classical.choice (D'.obj q).valid
  have hDmap' : ∀ {q r} (k : q ⟶ r),
      IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left :=
    fun {_ _} k ↦ Classical.choice (Descent.rawMap D hDobj hDmap k).valid
  let idRel : ∀ q : W.1.arrows.category, Pre J X := fun q ↦
    Classical.choose (Descent.rawMap_rel_id D hDobj hDmap q)
  let compRel : ∀ {q r s : W.1.arrows.category},
      (q ⟶ r) → (r ⟶ s) → Pre J X := fun {_ _ _} k l ↦
    Classical.choose (Descent.rawMap_rel_comp D hDobj hDmap k l)
  have hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
      (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left) := fun q ↦
    Classical.choice (Classical.choose_spec (Descent.rawMap_rel_id D hDobj hDmap q))
  have hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
      IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
        (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left :=
    fun {_ _ _} k l ↦
      Classical.choice (Classical.choose_spec (Descent.rawMap_rel_comp D hDobj hDmap k l))
  have hglue : IsObj J X (.objGlue W Dobj Dmap idRel compRel) S :=
    .glue W Dobj Dmap hDobj' hDmap' idRel compRel hId hComp
  let a : Obj J X := ⟨S, .objGlue W Dobj Dmap idRel compRel, ⟨hglue⟩⟩
  let ε' : ∀ q : W.1.arrows.category, D'.obj q ⟶ a := fun q ↦
    ⟦⟨q.obj.hom, .homGlueMap W Dobj Dmap idRel compRel q,
      ⟨.glueMap W Dobj Dmap idRel compRel hglue q⟩⟩⟧
  have hε' : ∀ q : W.1.arrows.category,
      IsHomLift (proj J X) q.obj.hom (ε' q) := by
    intro q
    have hmap : (proj J X).map
      (⟦⟨q.obj.hom, .homGlueMap W Dobj Dmap idRel compRel q,
        ⟨.glueMap W Dobj Dmap idRel compRel hglue q⟩⟩⟧ : D'.obj q ⟶ a) = q.obj.hom :=
      proj_map_mk J X _
    exact hmap ▸
      (inferInstance : IsHomLift (proj J X) ((proj J X).map (ε' q)) (ε' q))
  have hε'nat : ∀ {q r : W.1.arrows.category} (k : q ⟶ r),
      D'.map k ≫ ε' r = ε' q := by
    intro q r k
    rw [← Descent.mk_rawMap D hDobj hDmap k]
    apply _root_.Quotient.sound
    exact ⟨.relGlueMapNatural W Dobj Dmap idRel compRel k,
      ⟨.glueMapNatural W Dobj Dmap idRel compRel hglue k⟩⟩
  let e (q : W.1.arrows.category) : D'.obj q = D.obj q :=
    Obj.normalize_eq_self q.obj.left (D.obj q) (hDobj q)
  let ε : ∀ q : R.arrows.category, D.obj q ⟶ a :=
    fun q ↦ eqToHom (e q).symm ≫ ε' q
  refine ⟨a, rfl, ε, ?_, ?_⟩
  · intro q
    letI := hε' q
    dsimp [ε]
    infer_instance
  · intro q r k
    dsimp [ε]
    apply (cancel_epi (eqToHom (e q))).mp
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    simpa only [D', Descent.normalizeFunctor, Category.assoc] using hε'nat k

/-- Morphisms in the free completion glue uniquely from a pair of cocones over a
covering sieve. -/
theorem completion_existsUnique_gluing_hom_of_cocone {S : C} {R : Sieve S}
    (hR : R ∈ J S) (D : R.arrows.category ⥤ Obj J X)
    {a b : Obj J X} (ha : (proj J X).obj a = S) (hb : (proj J X).obj b = S)
    (η : ∀ q : R.arrows.category, D.obj q ⟶ a)
    (hηlift : ∀ q, IsHomLift (proj J X) q.obj.hom (η q))
    (hDobj : ∀ q : R.arrows.category, (proj J X).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      IsHomLift (proj J X) k.hom.left (D.map k))
    (hηnat : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r), D.map k ≫ η r = η q)
    (θ : ∀ q : R.arrows.category, D.obj q ⟶ b)
    (hθlift : ∀ q, IsHomLift (proj J X) q.obj.hom (θ q))
    (hθnat : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r), D.map k ≫ θ r = θ q) :
    ∃! Φ : a ⟶ b, IsHomLift (proj J X) (𝟙 S) Φ ∧
      ∀ ⦃T : C⦄ ⦃q : T ⟶ S⦄ (hq : R q),
        θ (R.arrows.categoryMk q hq) = η (R.arrows.categoryMk q hq) ≫ Φ := by
  let W : J.Cover S := ⟨R, hR⟩
  let D' : W.1.arrows.category ⥤ Obj J X := Descent.normalizeFunctor D hDobj
  let eD (q : W.1.arrows.category) : D'.obj q = D.obj q :=
    Obj.normalize_eq_self q.obj.left (D.obj q) (hDobj q)
  let a' : Obj J X := Obj.normalize S a ha
  let b' : Obj J X := Obj.normalize S b hb
  let ea : a' = a := Obj.normalize_eq_self S a ha
  let eb : b' = b := Obj.normalize_eq_self S b hb
  let η' : ∀ q : W.1.arrows.category, D'.obj q ⟶ a' := fun q ↦
    eqToHom (eD q) ≫ η q ≫ eqToHom ea.symm
  let θ' : ∀ q : W.1.arrows.category, D'.obj q ⟶ b' := fun q ↦
    eqToHom (eD q) ≫ θ q ≫ eqToHom eb.symm
  have hη' : ∀ q : W.1.arrows.category,
      IsHomLift (proj J X) q.obj.hom (η' q) := by
    intro q
    letI := hηlift q
    dsimp [η']
    infer_instance
  have hθ' : ∀ q : W.1.arrows.category,
      IsHomLift (proj J X) q.obj.hom (θ' q) := by
    intro q
    letI := hθlift q
    dsimp [θ']
    infer_instance
  have hη'nat : ∀ {q r : W.1.arrows.category} (k : q ⟶ r),
      D'.map k ≫ η' r = η' q := by
    intro q r k
    have h := congrArg
      (fun t ↦ eqToHom (eD q) ≫ t ≫ eqToHom ea.symm) (hηnat k)
    simpa [η', eD, D', Descent.normalizeFunctor, Category.assoc] using h
  have hθ'nat : ∀ {q r : W.1.arrows.category} (k : q ⟶ r),
      D'.map k ≫ θ' r = θ' q := by
    intro q r k
    have h := congrArg
      (fun t ↦ eqToHom (eD q) ≫ t ≫ eqToHom eb.symm) (hθnat k)
    simpa [θ', eD, D', Descent.normalizeFunctor, Category.assoc] using h
  let Dobj : W.1.arrows.category → Pre J X := fun q ↦ (D'.obj q).term
  let Dmap : ∀ {q r : W.1.arrows.category}, (q ⟶ r) → Pre J X :=
    fun {_ _} k ↦ (Descent.rawMap D hDobj hDmap k).term
  let ηraw : ∀ q : W.1.arrows.category, RawHom J X (D'.obj q) a' := fun q ↦
    Hom.normalize q.obj.hom (η' q) (hη' q)
  let θraw : ∀ q : W.1.arrows.category, RawHom J X (D'.obj q) b' := fun q ↦
    Hom.normalize q.obj.hom (θ' q) (hθ' q)
  let ηterm : W.1.arrows.category → Pre J X := fun q ↦ (ηraw q).term
  let θterm : W.1.arrows.category → Pre J X := fun q ↦ (θraw q).term
  have hηRel : ∀ {q r : W.1.arrows.category} (k : q ⟶ r),
      RawHom.Rel
        (RawHom.comp (Descent.rawMap D hDobj hDmap k) (ηraw r)) (ηraw q) := by
    intro q r k
    have h :
        (⟦RawHom.comp (Descent.rawMap D hDobj hDmap k) (ηraw r)⟧ :
          D'.obj q ⟶ a') = (⟦ηraw q⟧ : D'.obj q ⟶ a') := by
      calc
        _ = (⟦Descent.rawMap D hDobj hDmap k⟧ : D'.obj q ⟶ D'.obj r) ≫
            (⟦ηraw r⟧ : D'.obj r ⟶ a') := rfl
        _ = D'.map k ≫ η' r := by
          have hDmk : (⟦Descent.rawMap D hDobj hDmap k⟧ :
              D'.obj q ⟶ D'.obj r) = D'.map k :=
            Descent.mk_rawMap D hDobj hDmap k
          have hηmk : (⟦ηraw r⟧ : D'.obj r ⟶ a') = η' r :=
            Hom.mk_normalize r.obj.hom (η' r) (hη' r)
          rw [hDmk, hηmk]
        _ = η' q := hη'nat k
        _ = (⟦ηraw q⟧ : D'.obj q ⟶ a') :=
          (Hom.mk_normalize q.obj.hom (η' q) (hη' q)).symm
    exact _root_.Quotient.exact h
  have hθRel : ∀ {q r : W.1.arrows.category} (k : q ⟶ r),
      RawHom.Rel
        (RawHom.comp (Descent.rawMap D hDobj hDmap k) (θraw r)) (θraw q) := by
    intro q r k
    have h :
        (⟦RawHom.comp (Descent.rawMap D hDobj hDmap k) (θraw r)⟧ :
          D'.obj q ⟶ b') = (⟦θraw q⟧ : D'.obj q ⟶ b') := by
      calc
        _ = (⟦Descent.rawMap D hDobj hDmap k⟧ : D'.obj q ⟶ D'.obj r) ≫
            (⟦θraw r⟧ : D'.obj r ⟶ b') := rfl
        _ = D'.map k ≫ θ' r := by
          have hDmk : (⟦Descent.rawMap D hDobj hDmap k⟧ :
              D'.obj q ⟶ D'.obj r) = D'.map k :=
            Descent.mk_rawMap D hDobj hDmap k
          have hθmk : (⟦θraw r⟧ : D'.obj r ⟶ b') = θ' r :=
            Hom.mk_normalize r.obj.hom (θ' r) (hθ' r)
          rw [hDmk, hθmk]
        _ = θ' q := hθ'nat k
        _ = (⟦θraw q⟧ : D'.obj q ⟶ b') :=
          (Hom.mk_normalize q.obj.hom (θ' q) (hθ' q)).symm
    exact _root_.Quotient.exact h
  let idRel : ∀ q : W.1.arrows.category, Pre J X := fun q ↦
    Classical.choose (Descent.rawMap_rel_id D hDobj hDmap q)
  let compRel : ∀ {q r s : W.1.arrows.category},
      (q ⟶ r) → (r ⟶ s) → Pre J X := fun {_ _ _} k l ↦
    Classical.choose (Descent.rawMap_rel_comp D hDobj hDmap k l)
  let ηNat : ∀ {q r : W.1.arrows.category}, (q ⟶ r) → Pre J X :=
    fun {_ _} k ↦ Classical.choose (hηRel k)
  let θNat : ∀ {q r : W.1.arrows.category}, (q ⟶ r) → Pre J X :=
    fun {_ _} k ↦ Classical.choose (hθRel k)
  have hΦterm : IsHom J X
      (.homGlue W Dobj Dmap idRel compRel a'.term b'.term ηterm θterm ηNat θNat)
      a'.term b'.term (𝟙 S) := by
    refine .homGlue W Dobj Dmap ηterm θterm
      (Classical.choice a'.valid) (Classical.choice b'.valid)
      (fun q ↦ Classical.choice (D'.obj q).valid)
      (fun {_ _} k ↦ Classical.choice (Descent.rawMap D hDobj hDmap k).valid)
      idRel compRel
      (fun q ↦ Classical.choice
        (Classical.choose_spec (Descent.rawMap_rel_id D hDobj hDmap q)))
      (fun {_ _ _} k l ↦
        Classical.choice
          (Classical.choose_spec (Descent.rawMap_rel_comp D hDobj hDmap k l)))
      (fun q ↦ Classical.choice (ηraw q).valid)
      (fun q ↦ Classical.choice (θraw q).valid)
      ηNat θNat
      (fun {_ _} k ↦ Classical.choice (Classical.choose_spec (hηRel k)))
      (fun {_ _} k ↦ Classical.choice (Classical.choose_spec (hθRel k)))
  let Φraw : RawHom J X a' b' :=
    ⟨𝟙 S, .homGlue W Dobj Dmap idRel compRel a'.term b'.term ηterm θterm ηNat θNat,
      ⟨hΦterm⟩⟩
  let Φ₀ : a' ⟶ b' := ⟦Φraw⟧
  have hΦ₀ : IsHomLift (proj J X) (𝟙 S) Φ₀ := by
    have hmap : (proj J X).map Φ₀ = 𝟙 S := proj_map_mk J X Φraw
    exact hmap ▸ (inferInstance :
      IsHomLift (proj J X) ((proj J X).map Φ₀) Φ₀)
  have hfac₀ : ∀ q : W.1.arrows.category, θ' q = η' q ≫ Φ₀ := by
    intro q
    rw [← Hom.mk_normalize q.obj.hom (θ' q) (hθ' q),
      ← Hom.mk_normalize q.obj.hom (η' q) (hη' q)]
    apply _root_.Quotient.sound
    exact ⟨.relHomGlueFac W Dobj Dmap idRel compRel a'.term b'.term ηterm θterm
        ηNat θNat q,
      ⟨.homGlueFac W Dobj Dmap idRel compRel ηterm θterm ηNat θNat hΦterm
        (fun q ↦ Classical.choice (ηraw q).valid)
        (fun q ↦ Classical.choice (θraw q).valid) q⟩⟩
  let Φ : a ⟶ b := eqToHom ea.symm ≫ Φ₀ ≫ eqToHom eb
  refine ⟨Φ, ⟨?_, ?_⟩, ?_⟩
  · letI := hΦ₀
    dsimp [Φ]
    infer_instance
  · intro T q hq
    let q' := R.arrows.categoryMk q hq
    have h := congrArg
      (fun t ↦ eqToHom (eD q').symm ≫ t ≫ eqToHom eb) (hfac₀ q')
    simpa [q', η', θ', Φ, Category.assoc] using h
  · intro Ψ hΨ
    let Ψ' : a' ⟶ b' := eqToHom ea ≫ Ψ ≫ eqToHom eb.symm
    have hΨ' : IsHomLift (proj J X) (𝟙 S) Ψ' := by
      letI := hΨ.1
      dsimp [Ψ']
      infer_instance
    let Ψraw : RawHom J X a' b' := Hom.normalize (𝟙 S) Ψ' hΨ'
    have hfacΨ : ∀ q : W.1.arrows.category,
        (⟦θraw q⟧ : D'.obj q ⟶ b') =
          ((⟦ηraw q⟧ : D'.obj q ⟶ a') ≫ (⟦Ψraw⟧ : a' ⟶ b') :
            D'.obj q ⟶ b') := by
      intro q
      have hq : R.arrows.categoryMk q.obj.hom q.property = q := by
        ext
        rfl
      have hlocal := hΨ.2 q.property
      rw [hq] at hlocal
      have h := congrArg
        (fun t ↦ eqToHom (eD q) ≫ t ≫ eqToHom eb.symm)
        hlocal
      have hθmk : (⟦θraw q⟧ : D'.obj q ⟶ b') = θ' q := by
        exact Hom.mk_normalize q.obj.hom (θ' q) (hθ' q)
      have hηmk : (⟦ηraw q⟧ : D'.obj q ⟶ a') = η' q := by
        exact Hom.mk_normalize q.obj.hom (η' q) (hη' q)
      have hΨmk : (⟦Ψraw⟧ : a' ⟶ b') = Ψ' := by
        exact Hom.mk_normalize (𝟙 S) Ψ' hΨ'
      rw [hθmk, hηmk, hΨmk]
      simpa [η', θ', Ψ', Category.assoc] using h
    let fac : W.1.arrows.category → Pre J X := fun q ↦
      Classical.choose (_root_.Quotient.exact (hfacΨ q))
    have hfac : ∀ q, IsRel J X (fac q) (θterm q)
        (.homComp (ηterm q) Ψraw.term) (Dobj q) b'.term
        q.obj.hom (q.obj.hom ≫ 𝟙 S) := fun q ↦
      Classical.choice (Classical.choose_spec (_root_.Quotient.exact (hfacΨ q)))
    have hrel : RawHom.Rel Ψraw Φraw :=
      ⟨.relHomGlueUnique W Dobj Dmap idRel compRel a'.term b'.term ηterm θterm
          ηNat θNat Ψraw.term fac,
        ⟨.homGlueUnique W Dobj Dmap idRel compRel ηterm θterm ηNat θNat fac
          hΦterm (Classical.choice Ψraw.valid) hfac⟩⟩
    have hΨ₀ : Ψ' = Φ₀ := by
      rw [← Hom.mk_normalize (𝟙 S) Ψ' hΨ']
      exact _root_.Quotient.sound hrel
    have h := congrArg (fun t ↦ eqToHom ea.symm ≫ t ≫ eqToHom eb) hΨ₀
    simpa [Ψ', Φ, Category.assoc] using h

/-- The full morphism-gluing axiom follows by applying the formal cocone gluing
constructor to a functorial choice of cartesian lifts. -/
theorem completion_existsUnique_gluing_hom {S : C} {R : Sieve S} (hR : R ∈ J S)
    {a b : Obj J X} (ha : (proj J X).obj a = S) (hb : (proj J X).obj b = S)
    (φ : ∀ ⦃T : C⦄ ⦃g : T ⟶ S⦄, R g → ∀ ⦃x : Obj J X⦄
      (ξ : x ⟶ a), IsHomLift (proj J X) g ξ → (x ⟶ b))
    (hφlift : ∀ ⦃T : C⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Obj J X⦄
      (ξ : x ⟶ a) (hξ : IsHomLift (proj J X) g ξ),
      IsHomLift (proj J X) g (φ hg ξ hξ))
    (hφnat : ∀ ⦃T' T : C⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃h : T' ⟶ T⦄
      ⦃x' x : Obj J X⦄ (χ : x' ⟶ x) (ξ : x ⟶ a)
      (hξ : IsHomLift (proj J X) g ξ) (hχ : IsHomLift (proj J X) h χ),
      φ (R.downward_closed hg h) (χ ≫ ξ) inferInstance = χ ≫ φ hg ξ hξ) :
    ∃! Φ : a ⟶ b, IsHomLift (proj J X) (𝟙 S) Φ ∧
      ∀ ⦃T : C⦄ ⦃g : T ⟶ S⦄ (hg : R g) ⦃x : Obj J X⦄
        (ξ : x ⟶ a) (hξ : IsHomLift (proj J X) g ξ), φ hg ξ hξ = ξ ≫ Φ := by
  let a' : Obj J X := Obj.normalize S a ha
  let ea : a' = a := Obj.normalize_eq_self S a ha
  obtain ⟨D, η₀, hη₀, hDmap, hη₀nat⟩ :=
    CategoryTheory.Functor.IsStack.exists_lift_cocone (p := proj J X) (a := a') R
  have hDobj : ∀ q : R.arrows.category,
      (proj J X).obj (D.obj q) = q.obj.left := by
    intro q
    exact @IsHomLift.domain_eq _ _ _ _ (proj J X) _ _ _ _
      q.obj.hom (η₀ q) (hη₀ q)
  let η : ∀ q : R.arrows.category, D.obj q ⟶ a := fun q ↦ η₀ q ≫ eqToHom ea
  have hη : ∀ q : R.arrows.category,
      IsHomLift (proj J X) q.obj.hom (η q) := by
    intro q
    exact (IsHomLift.eqToHom_comp_lift_iff (proj J X) q.obj.hom (η₀ q) ea).2
      (hη₀ q)
  have hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ η r = η q := by
    intro q r k
    change D.map k ≫ (η₀ r ≫ eqToHom ea) = η₀ q ≫ eqToHom ea
    rw [← Category.assoc, hη₀nat k]
  let θ : ∀ q : R.arrows.category, D.obj q ⟶ b := fun q ↦
    φ q.property (η q) (hη q)
  have hθ : ∀ q : R.arrows.category,
      IsHomLift (proj J X) q.obj.hom (θ q) := fun q ↦ hφlift q.property (η q) (hη q)
  have hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ θ r = θ q := by
    intro q r k
    have h := hφnat r.property (D.map k) (η r) (hη r) (hDmap k)
    have hq : R.arrows.categoryMk q.obj.hom q.property = q := by
      ext
      rfl
    have hr : R.arrows.categoryMk r.obj.hom r.property = r := by
      ext
      rfl
    change D.map k ≫ φ r.property (η r) (hη r) =
      φ q.property (η q) (hη q)
    rw [← h]
    simp only [k.hom.w, hηnat k]
  obtain ⟨Φ, hΦ, huniq⟩ := completion_existsUnique_gluing_hom_of_cocone
    (J := J) (X := X) hR D ha hb η hη hDobj
      (fun {_ _} k ↦ hDmap k) (fun {_ _} k ↦ hηnat k)
      θ hθ (fun {_ _} k ↦ hθnat k)
  refine ⟨Φ, ⟨hΦ.1, ?_⟩, ?_⟩
  · intro T g hg x ξ hξ
    let q : R.arrows.category := R.arrows.categoryMk g hg
    letI := hξ
    letI : IsHomLift (proj J X) g (η q) := by simpa [q] using hη q
    letI : IsStronglyCartesian (proj J X) g (η q) :=
      CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        (proj J X) g _
    let κ : x ⟶ D.obj q :=
      IsStronglyCartesian.map (proj J X) g (η q) (Category.id_comp g).symm ξ
    have hκ : IsHomLift (proj J X) (𝟙 T) κ := by
      simpa [κ] using IsStronglyCartesian.map_isHomLift
        (proj J X) g (η q) (Category.id_comp g).symm ξ
    have hκfac : κ ≫ η q = ξ := by
      simp [κ]
    have hlocal := hφnat hg κ (η q) (hη q) hκ
    have hφκ : φ hg ξ hξ = κ ≫ θ q := by
      simpa [q, θ, hκfac] using hlocal
    calc
      φ hg ξ hξ = κ ≫ θ q := hφκ
      _ = κ ≫ (η q ≫ Φ) := by rw [← hΦ.2 hg]
      _ = ξ ≫ Φ := by rw [← Category.assoc, hκfac]
  · intro Ψ hΨ
    apply huniq Ψ
    refine ⟨hΨ.1, ?_⟩
    intro T g hg
    let q : R.arrows.category := R.arrows.categoryMk g hg
    exact hΨ.2 hg (η q) (hη q)

/-- The formal generators satisfy both stack axioms. -/
noncomputable instance proj_isStack : (proj J X).IsStack J where
  existsUnique_gluing_hom := completion_existsUnique_gluing_hom (J := J) (X := X)
  exists_gluing_obj := completion_exists_gluing_obj (J := J) (X := X)

/-- The free completion is a stack as a based category. -/
noncomputable instance completion_isStack : (completion J X).IsStack J where
  isFiberedInGroupoids := proj_isFiberedInGroupoids J X
  isStack := proj_isStack J X

namespace Interpretation

variable {Y : BasedCategory.{yv, yu} C}
variable [BasedCategory.IsStack J Y]

/-- An interpreted formal object, together with its strict base. -/
structure ObjData (Y : BasedCategory.{yv, yu} C) (S : C) where
  obj : Y.obj
  base_eq : Y.p.obj obj = S

/-- A chosen pullback of an interpreted object. -/
structure PullData (Y : BasedCategory.{yv, yu} C)
    {T : C} (B : ObjData Y T) {S : C} (f : S ⟶ T)
    extends ObjData Y S where
  hom : toObjData.obj ⟶ B.obj
  isLift : IsHomLift Y.p f hom

/-- An interpreted formal arrow, together with its base-lift proof. -/
structure HomData (Y : BasedCategory.{yv, yu} C) {S T : C}
    (A : ObjData Y S) (B : ObjData Y T) (f : S ⟶ T) where
  hom : A.obj ⟶ B.obj
  isLift : IsHomLift Y.p f hom

/-- An interpreted arrow together with its interpreted endpoints. -/
structure ArrowData (Y : BasedCategory.{yv, yu} C) (S T : C) (f : S ⟶ T) where
  source : ObjData Y S
  target : ObjData Y T
  hom : source.obj ⟶ target.obj
  isLift : IsHomLift Y.p f hom

/-- The semantic content of an interpreted formal equation. -/
structure EquationData (Y : BasedCategory.{yv, yu} C) (S T : C)
    (f g : S ⟶ T) where
  source : ObjData Y S
  target : ObjData Y T
  left : source.obj ⟶ target.obj
  right : source.obj ⟶ target.obj
  leftLift : IsHomLift Y.p f left
  rightLift : IsHomLift Y.p g right
  eq : left = right

/-- Choose a cartesian lift with the displayed source and target bases. -/
noncomputable def pullData {T : C} (B : ObjData Y T) {S : C} (f : S ⟶ T) :
    PullData Y B f := by
  let f' : S ⟶ Y.p.obj B.obj := f ≫ eqToHom B.base_eq.symm
  let A := (Functor.IsFiberedInGroupoids.exists_isHomLift (p := Y.p) f').choose
  let phi := (Functor.IsFiberedInGroupoids.exists_isHomLift (p := Y.p) f').choose_spec.choose
  have hphi :=
    (Functor.IsFiberedInGroupoids.exists_isHomLift (p := Y.p) f').choose_spec.choose_spec
  letI := hphi
  have hA : Y.p.obj A = S := IsHomLift.domain_eq Y.p f' phi
  have hphi' : IsHomLift Y.p f phi := by
    apply IsHomLift.of_fac' Y.p f phi hA B.base_eq
    rw [IsHomLift.fac' Y.p f' phi]
    simp [f']
  exact ⟨⟨A, hA⟩, phi, hphi'⟩

/-- A chosen effective object for an interpreted descent functor. -/
structure GlueData {S : C} (R : J.Cover S) (D : R.1.arrows.category ⥤ Y.obj) where
  obj : Y.obj
  base_eq : Y.p.obj obj = S
  cocone : ∀ q : R.1.arrows.category, D.obj q ⟶ obj
  cocone_lift : ∀ q, IsHomLift Y.p q.obj.hom (cocone q)
  cocone_naturality : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
    D.map k ≫ cocone r = cocone q

/-- Choose the effective object supplied by the target stack axiom. -/
noncomputable def glueData {S : C} (R : J.Cover S)
    (D : R.1.arrows.category ⥤ Y.obj)
    (hDobj : ∀ q : R.1.arrows.category, Y.p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
      IsHomLift Y.p k.hom.left (D.map k)) : GlueData (J := J) (Y := Y) R D := by
  let ex := Functor.IsStack.exists_gluing_obj R.2 D hDobj (fun {_ _} k ↦ hDmap k)
  let a := ex.choose
  have ha := ex.choose_spec.choose
  let eta := ex.choose_spec.choose_spec.choose
  have heta := ex.choose_spec.choose_spec.choose_spec
  exact
    { obj := a
      base_eq := ha
      cocone := eta
      cocone_lift := fun q ↦ by simpa [eta] using heta.1 q
      cocone_naturality := fun {_ _} k ↦ by simpa [eta] using heta.2 k }

end Interpretation

namespace IsObj

variable {J X}

/-- The object witnesses carried by a gluing derivation. -/
def Children {S : C} (t : Pre J X) : Type (max u v w z) :=
  match t with
  | .objGlue R Dobj _ _ _ => ∀ q : R.1.arrows.category, IsObj J X (Dobj q) q.obj.left
  | _ => PUnit

/-- Extract the recursively typed objects of a formal gluing. -/
def children {t : Pre J X} {S : C} (h : IsObj J X t S) : Children (S := S) t :=
  match h with
  | .incl _ => PUnit.unit
  | .pull _ _ => PUnit.unit
  | .glue _ _ _ hDobj _ _ _ _ _ => hDobj

/-- The arrow witnesses carried by a gluing derivation. -/
def Maps {S : C} (t : Pre J X) : Type (max u v w z) :=
  match t with
  | .objGlue R Dobj Dmap _ _ =>
      ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
        IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left
  | _ => PUnit

/-- Extract the recursively typed arrows of a formal gluing. -/
def maps {t : Pre J X} {S : C} (h : IsObj J X t S) : Maps (S := S) t :=
  match h with
  | .incl _ => PUnit.unit
  | .pull _ _ => PUnit.unit
  | .glue _ _ _ _ hDmap _ _ _ _ => hDmap

end IsObj

namespace IsHom

variable {J X}

mutual

/-- The source typing derivation of a typed formal arrow. -/
def sourceObj {phi a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X phi a b f) : IsObj J X a S :=
  match h with
  | .incl f => .incl _
  | .id ha => ha
  | .comp hf _ => sourceObj hf
  | .pullMap hb f => .pull hb f
  | .factor _ _ _ hphi _ => sourceObj hphi
  | .glueMap _ _ _ _ _ hglue q => IsObj.children hglue q
  | .homGlue _ _ _ _ _ ha _ _ _ _ _ _ _ _ _ _ _ _ _ => ha

/-- The target typing derivation of a typed formal arrow. -/
def targetObj {phi a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X phi a b f) : IsObj J X b T :=
  match h with
  | .incl f => .incl _
  | .id ha => ha
  | .comp _ hg => targetObj hg
  | .pullMap hb _ => hb
  | .factor _ _ hcart _ _ => sourceObj hcart
  | .glueMap _ _ _ _ _ hglue _ => hglue
  | .homGlue _ _ _ _ _ _ hb _ _ _ _ _ _ _ _ _ _ _ _ => hb

end

end IsHom

namespace IsRel

variable {J X}

mutual

/-- Recover the typed left-hand arrow from a formal equation derivation. -/
def leftHom {rho phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    (h : IsRel J X rho phi psi a b f g) : IsHom J X phi a b f :=
  match h with
  | .refl hphi => hphi
  | .baseChange hphi _ => hphi
  | .symm hr => rightHom hr
  | .trans hr _ => leftHom hr
  | .compCongr hr hs => .comp (leftHom hr) (leftHom hs)
  | .idComp ha hphi => .comp (.id ha) hphi
  | .compId hb hphi => .comp hphi (.id hb)
  | .assoc hphi hpsi hchi => .comp (.comp hphi hpsi) hchi
  | .inclId a => .incl (𝟙 a)
  | .inclComp f g => .incl (f ≫ g)
  | .factorFac f g hcart hphi hp => .comp (.factor f g hcart hphi hp) hcart
  | .factorUnique f g hcart hphi hp hchi hq hfac => hchi
  | .glueMapNatural R Dobj Dmap idRel compRel hglue k =>
      .comp (IsObj.maps hglue k) (.glueMap R Dobj Dmap idRel compRel hglue _)
  | .homGlueFac R Dobj Dmap idRel compRel eta theta etaNat thetaNat hglue heta htheta q =>
      htheta q
  | .homGlueUnique _ _ _ _ _ _ _ _ _ _ _ hphi _ => hphi

/-- Recover the typed right-hand arrow from a formal equation derivation. -/
def rightHom {rho phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    (h : IsRel J X rho phi psi a b f g) : IsHom J X psi a b g :=
  match h with
  | .refl hphi => hphi
  | .baseChange hphi hfg => hfg ▸ hphi
  | .symm hr => leftHom hr
  | .trans _ hs => rightHom hs
  | .compCongr hr hs => .comp (rightHom hr) (rightHom hs)
  | .idComp _ hphi => hphi
  | .compId _ hphi => hphi
  | .assoc hphi hpsi hchi => .comp hphi (.comp hpsi hchi)
  | .inclId a => .id (.incl a)
  | .inclComp f g => .comp (.incl f) (.incl g)
  | .factorFac _ _ _ hphi _ => hphi
  | .factorUnique f g hcart hphi hp hchi hq hfac => .factor f g hcart hphi hp
  | .glueMapNatural R Dobj Dmap idRel compRel hglue k =>
      .glueMap R Dobj Dmap idRel compRel hglue _
  | .homGlueFac R Dobj Dmap idRel compRel eta theta etaNat thetaNat hglue heta htheta q =>
      .comp (heta q) hglue
  | .homGlueUnique _ _ _ _ _ _ _ _ _ _ hglue _ _ => hglue

end

end IsRel

end CategoryTheory.BasedCategory.FreeStackCompletion
