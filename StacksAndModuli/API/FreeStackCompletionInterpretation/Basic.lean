module

public import StacksAndModuli.API.FreeStackCompletion

/-!
# Semantic data for interpreting the free stack completion

This module develops the semantic packages and evaluation graphs used to interpret
the formal object, arrow, and relation syntax of `FreeStackCompletion` in an
arbitrary target stack.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe v u w z yv yu

namespace CategoryTheory.BasedCategory.FreeStackCompletion.Interpretation

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : BasedCategory.{w, z} C}
variable {Y : BasedCategory.{yv, yu} C} [BasedCategory.IsStack J Y]

/-- A semantic arrow with fixed endpoint packages. -/
def arrow (A : ObjData Y S) (B : ObjData Y T) (f : S ⟶ T)
    (phi : A.obj ⟶ B.obj) (hphi : IsHomLift Y.p f phi) : ArrowData Y S T f :=
  ⟨A, B, phi, hphi⟩

/-- The identity semantic arrow. -/
def idArrow (A : ObjData Y S) : ArrowData Y S S (𝟙 S) :=
  arrow A A (𝟙 S) (𝟙 A.obj) (IsHomLift.id A.base_eq)

/-- Composition of semantic arrows with literally equal middle package. -/
def compArrow {R S T : C} {f : R ⟶ S} {g : S ⟶ T}
    {A : ObjData Y R} {B : ObjData Y S} {D : ObjData Y T}
    (phi : HomData Y A B f) (psi : HomData Y B D g) : ArrowData Y R T (f ≫ g) :=
  arrow A D (f ≫ g) (phi.hom ≫ psi.hom) (by
    letI := phi.isLift
    letI := psi.isLift
    infer_instance)

/-- Semantic data for a descent diagram on a covering sieve. -/
structure DescentOutput {S : C} (R : J.Cover S) where
  obj : ∀ q : R.1.arrows.category, ObjData Y q.obj.left
  map : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → ((obj q).obj ⟶ (obj r).obj)
  mapLift : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
    IsHomLift Y.p k.hom.left (map k)
  map_id : ∀ q : R.1.arrows.category, map (𝟙 q) = 𝟙 (obj q).obj
  map_comp : ∀ {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s),
    map (k ≫ l) = map k ≫ map l

namespace DescentOutput

/-- The functor underlying semantic descent data. -/
def functor {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R) :
    R.1.arrows.category ⥤ Y.obj where
  obj q := (D.obj q).obj
  map k := D.map k
  map_id q := D.map_id q
  map_comp k l := D.map_comp k l

/-- The semantic arrow attached to a descent map. -/
def mapArrow {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R)
    {q r : R.1.arrows.category} (k : q ⟶ r) :
    ArrowData Y q.obj.left r.obj.left k.hom.left :=
  arrow (D.obj q) (D.obj r) k.hom.left (D.map k) (D.mapLift k)

/-- The identity equation of a semantic descent functor. -/
def idEquation {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R)
    (q : R.1.arrows.category) :
    EquationData Y q.obj.left q.obj.left (𝟙 q.obj.left) (𝟙 q.obj.left) where
  source := D.obj q
  target := D.obj q
  left := D.map (𝟙 q)
  right := 𝟙 (D.obj q).obj
  leftLift := D.mapLift (𝟙 q)
  rightLift := IsHomLift.id (D.obj q).base_eq
  eq := D.map_id q

/-- The composition equation of a semantic descent functor. -/
def compEquation {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R)
    {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
    EquationData Y q.obj.left s.obj.left
      (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left where
  source := D.obj q
  target := D.obj s
  left := D.map k ≫ D.map l
  right := D.map (k ≫ l)
  leftLift := by
    letI := D.mapLift k
    letI := D.mapLift l
    infer_instance
  rightLift := D.mapLift (k ≫ l)
  eq := (D.map_comp k l).symm

/-- The chosen glued object of semantic descent data. -/
noncomputable def glued {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R) :
    GlueData (J := J) (Y := Y) R D.functor :=
  glueData (J := J) (Y := Y) R D.functor
    (fun q ↦ (D.obj q).base_eq) (fun {_ _} k ↦ D.mapLift k)

/-- The object package underlying the chosen glued object. -/
noncomputable def gluedObj {S : C} {R : J.Cover S}
    (D : DescentOutput (Y := Y) R) : ObjData Y S :=
  ⟨D.glued.obj, D.glued.base_eq⟩

/-- A chosen cocone arrow into the glued object. -/
noncomputable def glueArrow {S : C} {R : J.Cover S}
    (D : DescentOutput (Y := Y) R) (q : R.1.arrows.category) :
    ArrowData Y q.obj.left S q.obj.hom :=
  arrow (D.obj q) D.gluedObj q.obj.hom (D.glued.cocone q) (D.glued.cocone_lift q)

end DescentOutput

/-- A semantic cocone from descent data to a fixed global object. -/
structure CoconeOutput {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R)
    (A : ObjData Y S) where
  hom : ∀ q : R.1.arrows.category, (D.obj q).obj ⟶ A.obj
  homLift : ∀ q, IsHomLift Y.p q.obj.hom (hom q)
  naturality : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
    D.map k ≫ hom r = hom q

namespace CoconeOutput

/-- The semantic arrow attached to a cocone component. -/
def arrow {S : C} {R : J.Cover S} {D : DescentOutput (Y := Y) R}
    {A : ObjData Y S} (eta : CoconeOutput D A) (q : R.1.arrows.category) :
    ArrowData Y q.obj.left S q.obj.hom :=
  Interpretation.arrow (D.obj q) A q.obj.hom (eta.hom q) (eta.homLift q)

end CoconeOutput

/-- The deterministic global morphism obtained by gluing two semantic cocones. -/
structure HomGlueOutput {S : C} {R : J.Cover S} (D : DescentOutput (Y := Y) R)
    (A B : ObjData Y S) (eta : CoconeOutput D A) (theta : CoconeOutput D B)
    extends HomData Y A B (𝟙 S) where
  fac : ∀ q : R.1.arrows.category, theta.hom q = eta.hom q ≫ hom
  unique : ∀ phi : A.obj ⟶ B.obj, IsHomLift Y.p (𝟙 S) phi →
    (∀ q, theta.hom q = eta.hom q ≫ phi) → phi = hom

/-- Choose the unique global morphism supplied by morphism descent in the target stack. -/
noncomputable def homGlueOutput {S : C} {R : J.Cover S}
    (D : DescentOutput (Y := Y) R) (A B : ObjData Y S)
    (eta : CoconeOutput D A) (theta : CoconeOutput D B) :
    HomGlueOutput D A B eta theta := by
  let ex := Functor.IsStack.existsUnique_gluing_hom_of_cocone
    (p := Y.p) R.2 D.functor A.base_eq B.base_eq eta.hom eta.homLift
      (fun {_ _} k ↦ D.mapLift k) (fun {_ _} k ↦ eta.naturality k)
      theta.hom theta.homLift (fun {_ _} k ↦ theta.naturality k)
  let phi := ex.choose
  have hphi := ex.choose_spec.1
  have huniq := ex.choose_spec.2
  exact
    { hom := phi
      isLift := hphi.1
      fac := fun q ↦ hphi.2 q.property
      unique := fun psi hpsi hfac ↦ huniq psi ⟨hpsi, fun {_ _} _hq ↦ hfac _⟩ }

/-- Package the global morphism supplied by semantic morphism gluing. -/
noncomputable def HomGlueOutput.arrow {S : C} {R : J.Cover S}
    {D : DescentOutput (Y := Y) R} {A B : ObjData Y S}
    {eta : CoconeOutput D A} {theta : CoconeOutput D B}
    (H : HomGlueOutput D A B eta theta) : ArrowData Y S S (𝟙 S) :=
  Interpretation.arrow A B (𝟙 S) H.hom H.isLift

/-- The semantic naturality equation of a cocone. -/
def CoconeOutput.naturalityEquation {S : C} {R : J.Cover S}
    {D : DescentOutput (Y := Y) R} {A : ObjData Y S}
    (eta : CoconeOutput D A) {q r : R.1.arrows.category} (k : q ⟶ r) :
    EquationData Y q.obj.left S (k.hom.left ≫ r.obj.hom) q.obj.hom where
  source := D.obj q
  target := A
  left := D.map k ≫ eta.hom r
  right := eta.hom q
  leftLift := by
    letI := D.mapLift k
    letI := eta.homLift r
    infer_instance
  rightLift := eta.homLift q
  eq := eta.naturality k

/-- Forget the packaged endpoints of a semantic arrow. -/
def ArrowData.toHomData {S T : C} {f : S ⟶ T} (phi : ArrowData Y S T f) :
    HomData Y phi.source phi.target f :=
  ⟨phi.hom, phi.isLift⟩

/-- Add packaged endpoints to semantic hom data. -/
def HomData.toArrowData {S T : C} {f : S ⟶ T} {A : ObjData Y S} {B : ObjData Y T}
    (phi : HomData Y A B f) : ArrowData Y S T f :=
  arrow A B f phi.hom phi.isLift

/-- Repackage an arrow with propositionally identified endpoint packages. -/
def ArrowData.toHomDataOfEndpoints {S T : C} {f : S ⟶ T}
    (phi : ArrowData Y S T f) (A : ObjData Y S) (B : ObjData Y T)
    (hA : phi.source = A) (hB : phi.target = B) : HomData Y A B f := by
  subst A
  subst B
  exact phi.toHomData

@[simp]
lemma ArrowData.toHomDataOfEndpoints_toArrowData {S T : C} {f : S ⟶ T}
    (phi : ArrowData Y S T f) (A : ObjData Y S) (B : ObjData Y T)
    (hA : phi.source = A) (hB : phi.target = B) :
    (phi.toHomDataOfEndpoints A B hA hB).toArrowData = phi := by
  subst A
  subst B
  cases phi
  rfl

/-- The left arrow packaged by a semantic equation. -/
def EquationData.leftArrow {S T : C} {f g : S ⟶ T} (e : EquationData Y S T f g) :
    ArrowData Y S T f :=
  arrow e.source e.target f e.left e.leftLift

/-- The right arrow packaged by a semantic equation. -/
def EquationData.rightArrow {S T : C} {f g : S ⟶ T} (e : EquationData Y S T f g) :
    ArrowData Y S T g :=
  arrow e.source e.target g e.right e.rightLift

/-- The object package interpreting an original object. -/
def inclObj (F : X ⥤ᵇ Y) (a : X.obj) : ObjData Y (X.p.obj a) :=
  ⟨F.obj a, F.w_obj a⟩

/-- The arrow package interpreting an original arrow. -/
def inclArrow (F : X ⥤ᵇ Y) {a b : X.obj} (f : a ⟶ b) :
    ArrowData Y (X.p.obj a) (X.p.obj b) (X.p.map f) :=
  arrow (inclObj F a) (inclObj F b) (X.p.map f) (F.map f)
    (BasedFunctor.preserves_isHomLift F _ f)

/-- The chosen pullback arrow as a semantic arrow package. -/
noncomputable def pullArrow {S T : C} (B : ObjData Y T) (f : S ⟶ T) :
    ArrowData Y S T f := by
  let P := pullData (J := J) (Y := Y) B f
  exact arrow P.toObjData B f P.hom P.isLift

/-- The deterministic cartesian factor of one semantic arrow through another. -/
noncomputable def factorArrow {R S T : C} {f : S ⟶ T} {g : R ⟶ S}
    {p : R ⟶ T} {A : ObjData Y S} {B : ObjData Y T} {D : ObjData Y R}
    (cart : HomData Y A B f) (phi : HomData Y D B p) (hp : p = g ≫ f) :
    ArrowData Y R S g := by
  letI := cart.isLift
  letI := phi.isLift
  letI : IsStronglyCartesian Y.p f cart.hom :=
    IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
  let chi := IsStronglyCartesian.map Y.p f cart.hom hp phi.hom
  exact arrow D A g chi
    (IsStronglyCartesian.map_isHomLift Y.p f cart.hom hp phi.hom)

@[simp]
lemma factorArrow_fac {R S T : C} {f : S ⟶ T} {g : R ⟶ S}
    {p : R ⟶ T} {A : ObjData Y S} {B : ObjData Y T} {D : ObjData Y R}
    (cart : HomData Y A B f) (phi : HomData Y D B p) (hp : p = g ≫ f) :
    (factorArrow (J := J) (Y := Y) cart phi hp).hom ≫ cart.hom = phi.hom := by
  letI := cart.isLift
  letI := phi.isLift
  letI : IsStronglyCartesian Y.p f cart.hom :=
    IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
  exact IsStronglyCartesian.fac Y.p f cart.hom hp phi.hom

/-- The equation package expressing reflexivity. -/
def reflEquation {S T : C} {f : S ⟶ T} (phi : ArrowData Y S T f) :
    EquationData Y S T f f :=
  { source := phi.source
    target := phi.target
    left := phi.hom
    right := phi.hom
    leftLift := phi.isLift
    rightLift := phi.isLift
    eq := rfl }

/-- Regard one semantic arrow as lifting two propositionally equal base arrows. -/
def baseChangeEquation {S T : C} {f g : S ⟶ T} (phi : ArrowData Y S T f)
    (hfg : f = g) : EquationData Y S T f g :=
  { source := phi.source
    target := phi.target
    left := phi.hom
    right := phi.hom
    leftLift := phi.isLift
    rightLift := hfg ▸ phi.isLift
    eq := rfl }

/-- Reverse a semantic equation. -/
def EquationData.symm {S T : C} {f g : S ⟶ T} (e : EquationData Y S T f g) :
    EquationData Y S T g f :=
  { source := e.source
    target := e.target
    left := e.right
    right := e.left
    leftLift := e.rightLift
    rightLift := e.leftLift
    eq := e.eq.symm }

/-- Vertically compose semantic equations with a literally shared middle arrow. -/
def transEquation {S T : C} {f g h : S ⟶ T}
    (A : ObjData Y S) (B : ObjData Y T)
    (phi psi chi : A.obj ⟶ B.obj)
    (hphi : IsHomLift Y.p f phi) (hpsi : IsHomLift Y.p g psi)
    (hchi : IsHomLift Y.p h chi) (h₁ : phi = psi) (h₂ : psi = chi) :
    EquationData Y S T f h :=
  ⟨A, B, phi, chi, hphi, hchi, h₁.trans h₂⟩

/-- Compose two semantic equations horizontally. -/
def compCongrEquation {R S T : C} {f f' : R ⟶ S} {g g' : S ⟶ T}
    {A : ObjData Y R} {B : ObjData Y S} {D : ObjData Y T}
    (phi phi' : A.obj ⟶ B.obj) (psi psi' : B.obj ⟶ D.obj)
    (hphi : IsHomLift Y.p f phi) (hphi' : IsHomLift Y.p f' phi')
    (hpsi : IsHomLift Y.p g psi) (hpsi' : IsHomLift Y.p g' psi')
    (h₁ : phi = phi') (h₂ : psi = psi') :
    EquationData Y R T (f ≫ g) (f' ≫ g') :=
  { source := A
    target := D
    left := phi ≫ psi
    right := phi' ≫ psi'
    leftLift := by letI := hphi; letI := hpsi; infer_instance
    rightLift := by letI := hphi'; letI := hpsi'; infer_instance
    eq := by rw [h₁, h₂] }

lemma ObjData.ext' {S : C} (A B : ObjData Y S) (h : A.obj = B.obj) : A = B := by
  cases A
  cases B
  cases h
  rfl

lemma congrArgHEq {A : Sort*} {B : A → Sort*} (f : ∀ a, B a) {a a' : A}
    (h : a = a') : HEq (f a) (f a') := by
  cases h
  rfl

lemma HomData.ext' {S T : C} {f : S ⟶ T} {A : ObjData Y S} {B : ObjData Y T}
    (phi psi : HomData Y A B f) (h : phi.hom = psi.hom) : phi = psi := by
  cases phi
  cases psi
  cases h
  rfl

lemma ArrowData.ext' {S T : C} {f : S ⟶ T} (phi psi : ArrowData Y S T f)
    (hs : phi.source = psi.source) (ht : phi.target = psi.target)
    (hh : HEq phi.hom psi.hom) : phi = psi := by
  cases phi
  cases psi
  cases hs
  cases ht
  cases hh
  rfl

lemma ArrowData.heq_of_base_eq {S T : C} {f g : S ⟶ T}
    (phi : ArrowData Y S T f) (psi : ArrowData Y S T g) (hfg : f = g)
    (hs : phi.source = psi.source) (ht : phi.target = psi.target)
    (hh : HEq phi.hom psi.hom) : HEq phi psi := by
  subst g
  exact (ArrowData.ext' phi psi hs ht hh).heq

lemma EquationData.ext' {S T : C} {f g : S ⟶ T} (e e' : EquationData Y S T f g)
    (hs : e.source = e'.source) (ht : e.target = e'.target)
    (hl : HEq e.left e'.left) (hr : HEq e.right e'.right) : e = e' := by
  cases e
  cases e'
  cases hs
  cases ht
  cases hl
  cases hr
  rfl

lemma DescentOutput.ext' {S : C} {R : J.Cover S} (D D' : DescentOutput (Y := Y) R)
    (hobj : D.obj = D'.obj)
    (hmap : ∀ {q r : R.1.arrows.category} (k : q ⟶ r), HEq (D.map k) (D'.map k)) :
    D = D' := by
  rcases D with ⟨obj, map, mapLift, map_id, map_comp⟩
  rcases D' with ⟨obj', map', mapLift', map_id', map_comp'⟩
  cases hobj
  have hmapEq : @map = @map' := by
    funext q r k
    exact eq_of_heq (hmap k)
  cases hmapEq
  rfl

lemma CoconeOutput.ext' {S : C} {R : J.Cover S} {D : DescentOutput (Y := Y) R}
    {A : ObjData Y S} (eta theta : CoconeOutput D A)
    (hhom : eta.hom = theta.hom) : eta = theta := by
  cases eta
  cases theta
  cases hhom
  rfl


/-- A completely packaged object evaluation, used to erase dependent graph indices. -/
structure ObjEvaluation where
  term : Pre J X
  base : C
  valid : IsObj J X term base
  value : ObjData Y base

/-- A completely packaged arrow evaluation, used to erase dependent graph indices. -/
structure HomEvaluation where
  term : Pre J X
  sourceTerm : Pre J X
  targetTerm : Pre J X
  sourceBase : C
  targetBase : C
  baseMap : sourceBase ⟶ targetBase
  valid : Nonempty (IsHom J X term sourceTerm targetTerm baseMap)
  value : ArrowData Y sourceBase targetBase baseMap

instance {phi a b : Pre J X} {S T : C} {f : S ⟶ T} :
    Coe (IsHom J X phi a b f) (Nonempty (IsHom J X phi a b f)) :=
  ⟨Nonempty.intro⟩

namespace _root_.Nonempty

theorem incl {a b : X.obj} (f : a ⟶ b) :
    Nonempty (IsHom J X (.homIncl f) (.objIncl a) (.objIncl b) (X.p.map f)) :=
  ⟨IsHom.incl f⟩

theorem id {S : C} {a : Pre J X} (ha : IsObj J X a S) :
    Nonempty (IsHom J X (.homId a) a a (𝟙 S)) :=
  ⟨IsHom.id ha⟩

theorem comp {R S T : C} {a b c f g : Pre J X} {p : R ⟶ S} {q : S ⟶ T}
    (hf : IsHom J X f a b p) (hg : IsHom J X g b c q) :
    Nonempty (IsHom J X (.homComp f g) a c (p ≫ q)) :=
  ⟨IsHom.comp hf hg⟩

theorem pullMap {S T : C} {b : Pre J X} (hb : IsObj J X b T) (f : S ⟶ T) :
    Nonempty (IsHom J X (.homPullMap b f) (.objPull b f) b f) :=
  ⟨IsHom.pullMap hb f⟩

theorem factor {R S T : C} {a b c cart phi : Pre J X} {p : R ⟶ T}
    (f : S ⟶ T) (g : R ⟶ S) (hcart : IsHom J X cart a b f)
    (hphi : IsHom J X phi c b p) (hp : p = g ≫ f) :
    Nonempty (IsHom J X (.homFactor cart phi f g) c a g) :=
  ⟨IsHom.factor f g hcart hphi hp⟩

end _root_.Nonempty

/-- A completely packaged relation evaluation, used to erase dependent graph indices. -/
structure RelEvaluation where
  term : Pre J X
  leftTerm : Pre J X
  rightTerm : Pre J X
  sourceTerm : Pre J X
  targetTerm : Pre J X
  sourceBase : C
  targetBase : C
  leftBase : sourceBase ⟶ targetBase
  rightBase : sourceBase ⟶ targetBase
  valid : IsRel J X term leftTerm rightTerm sourceTerm targetTerm leftBase rightBase
  value : EquationData Y sourceBase targetBase leftBase rightBase

/-- The semantic part of an object evaluation, omitting its typing derivation. -/
structure ObjSemantic where
  base : C
  value : ObjData Y base

/-- The semantic part of an arrow evaluation, omitting all raw syntax and typing data. -/
structure HomSemantic where
  sourceBase : C
  targetBase : C
  baseMap : sourceBase ⟶ targetBase
  value : ArrowData Y sourceBase targetBase baseMap

def ObjEvaluation.semantic (E : ObjEvaluation (J := J) (X := X) (Y := Y)) :
    ObjSemantic (Y := Y) := ⟨E.base, E.value⟩

def HomEvaluation.semantic (E : HomEvaluation (J := J) (X := X) (Y := Y)) :
    HomSemantic (Y := Y) := ⟨E.sourceBase, E.targetBase, E.baseMap, E.value⟩

lemma HomSemantic.baseMap_heq {A B : HomSemantic (C := C) (Y := Y)}
    (h : A = B) : HEq A.baseMap B.baseMap := by
  cases h
  rfl

lemma HomSemantic.value_heq {A B : HomSemantic (C := C) (Y := Y)}
    (h : A = B) : HEq A.value B.value := by
  cases h
  rfl

lemma HomEvaluation.baseMap_heq {E E' : HomEvaluation (J := J) (X := X) (Y := Y)}
    (h : E = E') : HEq E.baseMap E'.baseMap := by
  cases h
  rfl

lemma HomEvaluation.value_heq {E E' : HomEvaluation (J := J) (X := X) (Y := Y)}
    (h : E = E') : HEq E.value E'.value := by
  cases h
  rfl


mutual

/-- An evaluator graph whose dependent object output is hidden in one opaque package. -/
inductive ObjEvaluationStep (F : X ⥤ᵇ Y) :
    ObjEvaluation (J := J) (X := X) (Y := Y) → Type (max u v w z yv yu)
  | incl (a : X.obj) (E : ObjEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.objIncl a, X.p.obj a, .incl a, inclObj F a⟩) : ObjEvaluationStep F E
  | pull {S T : C} {b : Pre J X} (hb : IsObj J X b T)
      (B : ObjData Y T) (eB : ObjEvaluationStep F ⟨b, T, hb, B⟩) (f : S ⟶ T)
      (E : ObjEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.objPull b f, S, .pull hb f, (pullArrow (J := J) B f).source⟩) :
      ObjEvaluationStep F E
  | glue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
      (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
        (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
      (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
        IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
          (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
      (D : DescentOutput (Y := Y) R)
      (eObj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩)
      (eMap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
        ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left, hDmap k, D.mapArrow k⟩)
      (eId : ∀ q, RelEvaluationStep F
        ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
          q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩)
      (eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
        ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
          q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
          hComp k l, D.compEquation k l⟩)
      (E : ObjEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.objGlue R Dobj Dmap idRel compRel, S,
        .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp, D.gluedObj⟩) :
      ObjEvaluationStep F E

/-- An evaluator graph whose dependent arrow output is hidden in one opaque package. -/
inductive HomEvaluationStep (F : X ⥤ᵇ Y) :
    HomEvaluation (J := J) (X := X) (Y := Y) → Type (max u v w z yv yu)
  | incl {a b : X.obj} (f : a ⟶ b) (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homIncl f, .objIncl a, .objIncl b, X.p.obj a, X.p.obj b,
        X.p.map f, ⟨IsHom.incl f⟩, inclArrow F f⟩) : HomEvaluationStep F E
  | id {S : C} {a : Pre J X} (ha : IsObj J X a S) (A : ObjData Y S)
      (eA : ObjEvaluationStep F ⟨a, S, ha, A⟩)
      (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homId a, a, a, S, S, 𝟙 S, ⟨IsHom.id ha⟩, idArrow A⟩) :
      HomEvaluationStep F E
  | comp {R S T : C} {a b c phi psi : Pre J X} {p : R ⟶ S} {q : S ⟶ T}
      (hphi : IsHom J X phi a b p) (hpsi : IsHom J X psi b c q)
      (A : ObjData Y R) (B : ObjData Y S) (D : ObjData Y T)
      (phi' : HomData Y A B p) (psi' : HomData Y B D q)
      (ePhi : HomEvaluationStep F
        ⟨phi, a, b, R, S, p, hphi, phi'.toArrowData⟩)
      (ePsi : HomEvaluationStep F
        ⟨psi, b, c, S, T, q, hpsi, psi'.toArrowData⟩)
      (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homComp phi psi, a, c, R, T, p ≫ q, ⟨IsHom.comp hphi hpsi⟩,
        compArrow phi' psi'⟩) :
      HomEvaluationStep F E
  | pullMap {S T : C} {b : Pre J X} (hb : IsObj J X b T)
      (B : ObjData Y T) (eB : ObjEvaluationStep F ⟨b, T, hb, B⟩) (f : S ⟶ T)
      (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homPullMap b f, .objPull b f, b, S, T, f,
        ⟨IsHom.pullMap hb f⟩, pullArrow (J := J) B f⟩) : HomEvaluationStep F E
  | factor {R S T : C} {a b c cart phi : Pre J X} {p : R ⟶ T}
      (f : S ⟶ T) (g : R ⟶ S)
      (hcart : IsHom J X cart a b f) (hphi : IsHom J X phi c b p) (hp : p = g ≫ f)
      (A : ObjData Y S) (B : ObjData Y T) (D : ObjData Y R)
      (cart' : HomData Y A B f) (phi' : HomData Y D B p)
      (eCart : HomEvaluationStep F ⟨cart, a, b, S, T, f, hcart, cart'.toArrowData⟩)
      (ePhi : HomEvaluationStep F ⟨phi, c, b, R, T, p, hphi, phi'.toArrowData⟩)
      (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homFactor cart phi f g, c, a, R, S, g,
        ⟨IsHom.factor f g hcart hphi hp⟩, factorArrow (J := J) cart' phi' hp⟩) :
      HomEvaluationStep F E
  | glueMap {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
      (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
      (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
      (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
        (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
      (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
        IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
          (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
      (hglue_eq : hglue =
        .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp)
      (D : DescentOutput (Y := Y) R)
      (eObj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩)
      (eMap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
        ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left, hDmap k, D.mapArrow k⟩)
      (eId : ∀ q, RelEvaluationStep F
        ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
          q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩)
      (eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
        ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
          q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
          hComp k l, D.compEquation k l⟩)
      (q : R.1.arrows.category) (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨.homGlueMap R Dobj Dmap idRel compRel q, Dobj q,
        .objGlue R Dobj Dmap idRel compRel, q.obj.left, S, q.obj.hom,
        ⟨IsHom.glueMap R Dobj Dmap idRel compRel hglue q⟩, D.glueArrow q⟩) :
      HomEvaluationStep F E
  | homGlue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      {a b : Pre J X} (etaTerm thetaTerm : ∀ q : R.1.arrows.category, Pre J X)
      (ha : IsObj J X a S) (hb : IsObj J X b S)
      (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
      (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
        (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
      (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
        IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
          (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
      (heta : ∀ q, IsHom J X (etaTerm q) (Dobj q) a q.obj.hom)
      (htheta : ∀ q, IsHom J X (thetaTerm q) (Dobj q) b q.obj.hom)
      (etaNat thetaNat : ∀ {q r} (k : q ⟶ r), Pre J X)
      (hetaNat : ∀ {q r} (k : q ⟶ r),
        IsRel J X (etaNat k) (.homComp (Dmap k) (etaTerm r)) (etaTerm q) (Dobj q) a
          (k.hom.left ≫ r.obj.hom) q.obj.hom)
      (hthetaNat : ∀ {q r} (k : q ⟶ r),
        IsRel J X (thetaNat k) (.homComp (Dmap k) (thetaTerm r)) (thetaTerm q) (Dobj q) b
          (k.hom.left ≫ r.obj.hom) q.obj.hom)
      (D : DescentOutput (Y := Y) R) (A B : ObjData Y S)
      (eta : CoconeOutput D A) (theta : CoconeOutput D B)
      (eA : ObjEvaluationStep F ⟨a, S, ha, A⟩)
      (eB : ObjEvaluationStep F ⟨b, S, hb, B⟩)
      (eDobj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩)
      (eDmap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
        ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left, hDmap k, D.mapArrow k⟩)
      (eId : ∀ q, RelEvaluationStep F
        ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q, q.obj.left, q.obj.left,
          𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩)
      (eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
        ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
          q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
          hComp k l, D.compEquation k l⟩)
      (eEta : ∀ q, HomEvaluationStep F
        ⟨etaTerm q, Dobj q, a, q.obj.left, S, q.obj.hom, heta q, eta.arrow q⟩)
      (eTheta : ∀ q, HomEvaluationStep F
        ⟨thetaTerm q, Dobj q, b, q.obj.left, S, q.obj.hom, htheta q, theta.arrow q⟩)
      (eEtaNat : ∀ {q r} (k : q ⟶ r), RelEvaluationStep F
        ⟨etaNat k, .homComp (Dmap k) (etaTerm r), etaTerm q, Dobj q, a,
          q.obj.left, S, k.hom.left ≫ r.obj.hom, q.obj.hom, hetaNat k,
          eta.naturalityEquation k⟩)
      (eThetaNat : ∀ {q r} (k : q ⟶ r), RelEvaluationStep F
        ⟨thetaNat k, .homComp (Dmap k) (thetaTerm r), thetaTerm q, Dobj q, b,
          q.obj.left, S, k.hom.left ≫ r.obj.hom, q.obj.hom, hthetaNat k,
          theta.naturalityEquation k⟩)
      (E : HomEvaluation (J := J) (X := X) (Y := Y))
      (hE : E =
        ⟨.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat,
          a, b, S, S, 𝟙 S,
          ⟨IsHom.homGlue R Dobj Dmap etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
            hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat⟩,
          (homGlueOutput D A B eta theta).arrow⟩) :
      HomEvaluationStep F E

/-- An evaluator graph whose dependent equation output is hidden in one opaque package. -/
inductive RelEvaluationStep (F : X ⥤ᵇ Y) :
    RelEvaluation (J := J) (X := X) (Y := Y) → Type (max u v w z yv yu)
  | mk {rho phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
      (h : IsRel J X rho phi psi a b f g) (e : EquationData Y S T f g)
      (eLeft : HomEvaluationStep F ⟨phi, a, b, S, T, f, h.leftHom, e.leftArrow⟩)
      (eRight : HomEvaluationStep F ⟨psi, a, b, S, T, g, h.rightHom, e.rightArrow⟩)
      (E : RelEvaluation (J := J) (X := X) (Y := Y))
      (hE : E = ⟨rho, phi, psi, a, b, S, T, f, g, h, e⟩) : RelEvaluationStep F E

end

namespace RelEvaluationStep

/-- The evaluated left side stored by a relation-evaluation step. -/
def leftStep (F : X ⥤ᵇ Y)
    {E : RelEvaluation (J := J) (X := X) (Y := Y)}
    (s : RelEvaluationStep F E) : HomEvaluationStep F
      ⟨E.leftTerm, E.sourceTerm, E.targetTerm, E.sourceBase, E.targetBase,
        E.leftBase, E.valid.leftHom, E.value.leftArrow⟩ := by
  cases s with
  | mk h e eLeft eRight E hE =>
      cases hE
      exact eLeft

/-- The evaluated right side stored by a relation-evaluation step. -/
def rightStep (F : X ⥤ᵇ Y)
    {E : RelEvaluation (J := J) (X := X) (Y := Y)}
    (s : RelEvaluationStep F E) : HomEvaluationStep F
      ⟨E.rightTerm, E.sourceTerm, E.targetTerm, E.sourceBase, E.targetBase,
        E.rightBase, E.valid.rightHom, E.value.rightArrow⟩ := by
  cases s with
  | mk h e eLeft eRight E hE =>
      cases hE
      exact eRight

end RelEvaluationStep

/-- Transport an evaluator step across a change of base arrow, typing witness, and
semantic arrow package, while keeping its raw term and endpoints fixed. -/
def HomEvaluationStep.reindex (F : X ⥤ᵇ Y)
    {phi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    {hf : Nonempty (IsHom J X phi a b f)}
    {hg : Nonempty (IsHom J X phi a b g)}
    {p : ArrowData Y S T f} {q : ArrowData Y S T g}
    (e : HomEvaluationStep F ⟨phi, a, b, S, T, f, hf, p⟩)
    (hfg : f = g) (hpq : HEq p q) :
    HomEvaluationStep F ⟨phi, a, b, S, T, g, hg, q⟩ := by
  subst g
  have hp : p = q := eq_of_heq hpq
  subst q
  exact e

/-- The semantic data retained by an evaluation of a formal glued morphism. -/
structure HomGlueView (F : X ⥤ᵇ Y) {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q : R.1.arrows.category, Pre J X)
    (compRel : ∀ {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (a b : Pre J X) (etaTerm thetaTerm : ∀ q : R.1.arrows.category, Pre J X)
    (etaNat thetaNat : ∀ {q r : R.1.arrows.category} (k : q ⟶ r), Pre J X)
    (P : ArrowData Y S S (𝟙 S)) where
  heta : ∀ q, IsHom J X (etaTerm q) (Dobj q) a q.obj.hom
  htheta : ∀ q, IsHom J X (thetaTerm q) (Dobj q) b q.obj.hom
  D : DescentOutput (Y := Y) R
  A : ObjData Y S
  B : ObjData Y S
  eta : CoconeOutput D A
  theta : CoconeOutput D B
  eEta : ∀ q, HomEvaluationStep F
    ⟨etaTerm q, Dobj q, a, q.obj.left, S, q.obj.hom, heta q, eta.arrow q⟩
  eTheta : ∀ q, HomEvaluationStep F
    ⟨thetaTerm q, Dobj q, b, q.obj.left, S, q.obj.hom, htheta q, theta.arrow q⟩
  value_eq : P = (homGlueOutput D A B eta theta).arrow


/-- Semantic object values computed by the evaluator graph are unique. -/
theorem ObjEvaluationStep.value_unique (F : X ⥤ᵇ Y)
    {E E' : ObjEvaluation (J := J) (X := X) (Y := Y)}
    (eA : ObjEvaluationStep F E) (eB : ObjEvaluationStep F E')
    (ht : E.term = E'.term) : E.semantic = E'.semantic := by
  refine (ObjEvaluationStep.rec (C := C) (J := J) (X := X) (Y := Y) (F := F)
    (motive_1 := fun E _ ↦ ∀ {E'} (_ : ObjEvaluationStep F E'),
      E.term = E'.term → E.semantic = E'.semantic)
    (motive_2 := fun E _ ↦ ∀ {E'} (_ : HomEvaluationStep F E'),
      E.term = E'.term → E.semantic = E'.semantic)
    (motive_3 := fun _ _ ↦ True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ eA) eB ht
  · intro a E hE E' eB ht
    cases hE
    cases eB with
    | incl a' E' hE' =>
        cases hE'
        simp_all
        cases ht
        rfl
    | pull => simp_all
    | glue => simp_all
  · intro S T b hb B eChild f E hE ih E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | glue => simp_all
    | pull hb' B' eChild' f' E' hE' =>
        cases hE'
        simp only [Pre.objPull.injEq] at ht
        rcases ht with ⟨hS, hT, hbterm, hf⟩
        cases hS
        cases hT
        cases hbterm
        cases hf
        have hchild := ih eChild' rfl
        cases hchild
        rfl
  · intro S R Dobj Dmap hDobj hDmap idRel compRel hId hComp D eObj eMap eId eComp
      E hE ihObj ihMap _ihId _ihComp E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | pull => simp_all
    | glue R' Dobj' Dmap' hDobj' hDmap' idRel' compRel' hId' hComp' D'
        eObj' eMap' eId' eComp' E' hE' =>
        cases hE'
        simp_all
        rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel⟩
        cases hS
        cases hR
        cases hDobjTerm
        have hDmapEq : @Dmap = @Dmap' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
        cases hDmapEq
        cases hIdRel
        have hCompRelEq : @compRel = @compRel' := by
          funext q r s k l
          exact congrFun (congrFun (congrFun (congrFun (congrFun
            (eq_of_heq hCompRel) q) r) s) k) l
        cases hCompRelEq
        have hObjValue (q : R.1.arrows.category) := ihObj q (eObj' q) rfl
        have hMapValue {q r : R.1.arrows.category} (k : q ⟶ r) :=
          ihMap k (eMap' k) rfl
        have hObj : D.obj = D'.obj := by
          funext q
          exact eq_of_heq (congrArgHEq ObjSemantic.value (hObjValue q))
        have hMap : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
            HEq (D.map k) (D'.map k) := by
          intro q r k
          have hArrow : D.mapArrow k = D'.mapArrow k :=
            eq_of_heq (HomSemantic.value_heq (hMapValue k))
          exact congrArgHEq ArrowData.hom hArrow
        have hD : D = D' := DescentOutput.ext' D D' hObj hMap
        cases hD
        rfl
  · intro a b f E hE E' eB ht
    cases hE
    cases eB with
    | incl f' E' hE' =>
        cases hE'
        simp_all
        rcases ht with ⟨ha, hb, hf⟩
        cases ha
        cases hb
        cases hf
        rfl
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
  · intro S a ha A eObj E hE ih E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | id ha' A' eObj' E' hE' =>
        cases hE'
        simp only [Pre.homId.injEq] at ht
        cases ht
        have hObj := ih eObj' rfl
        have hBase := congrArg ObjSemantic.base hObj
        cases hBase
        have hValue : A = A' := eq_of_heq (congrArgHEq ObjSemantic.value hObj)
        cases hValue
        rfl
  · intro R S T a b c phi psi p q hphi hpsi A B D phi' psi' ePhi ePsi E hE
      ihPhi ihPsi E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | comp hphi' hpsi' A' B' D' phi'' psi'' ePhi' ePsi' E' hE' =>
        cases hE'
        simp only [Pre.homComp.injEq] at ht
        rcases ht with ⟨hphiTerm, hpsiTerm⟩
        cases hphiTerm
        cases hpsiTerm
        have hPhi := ihPhi ePhi' rfl
        have hPsi := ihPsi ePsi' rfl
        have hPhiMap := HomSemantic.baseMap_heq hPhi
        have hPhiValue := HomSemantic.value_heq hPhi
        cases congrArg HomSemantic.sourceBase hPhi
        cases congrArg HomSemantic.targetBase hPhi
        cases eq_of_heq hPhiMap
        have hPhiArrow : phi'.toArrowData = phi''.toArrowData :=
          eq_of_heq hPhiValue
        have hPhiSource := congrArg ArrowData.source hPhiArrow
        have hPhiTarget := congrArg ArrowData.target hPhiArrow
        cases hPhiSource
        cases hPhiTarget
        have hPhiData : phi' = phi'' := HomData.ext' phi' phi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPhiArrow))
        cases hPhiData
        have hPsiMap := HomSemantic.baseMap_heq hPsi
        have hPsiValue := HomSemantic.value_heq hPsi
        cases congrArg HomSemantic.sourceBase hPsi
        cases congrArg HomSemantic.targetBase hPsi
        cases eq_of_heq hPsiMap
        have hPsiArrow : psi'.toArrowData = psi''.toArrowData :=
          eq_of_heq hPsiValue
        have hPsiSource := congrArg ArrowData.source hPsiArrow
        have hPsiTarget := congrArg ArrowData.target hPsiArrow
        cases hPsiSource
        cases hPsiTarget
        have hPsiData : psi' = psi'' := HomData.ext' psi' psi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPsiArrow))
        cases hPsiData
        rfl
  · intro S T b hb B eObj f E hE ih E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | pullMap hb' B' eObj' f' E' hE' =>
        cases hE'
        simp only [Pre.homPullMap.injEq] at ht
        rcases ht with ⟨hS, hT, hbTerm, hf⟩
        cases hS
        cases hT
        cases hbTerm
        cases hf
        have hObj := ih eObj' rfl
        have hValue : B = B' := eq_of_heq (congrArgHEq ObjSemantic.value hObj)
        cases hValue
        rfl
  · intro R S T a b c cart phi p f g hcart hphi hp A B D cart' phi' eCart ePhi
      E hE ihCart ihPhi E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | factor f' g' hcart' hphi' hp' A' B' D' cart'' phi'' eCart' ePhi' E' hE' =>
        cases hE'
        simp only [Pre.homFactor.injEq] at ht
        rcases ht with ⟨hR, hS, hT, hCartTerm, hPhiTerm, hf, hg⟩
        cases hR
        cases hS
        cases hT
        cases hCartTerm
        cases hPhiTerm
        cases hf
        cases hg
        have hCart := ihCart eCart' rfl
        have hPhi := ihPhi ePhi' rfl
        have hCartMap := HomSemantic.baseMap_heq hCart
        have hCartValue := HomSemantic.value_heq hCart
        cases congrArg HomSemantic.sourceBase hCart
        cases congrArg HomSemantic.targetBase hCart
        cases eq_of_heq hCartMap
        have hCartArrow : cart'.toArrowData = cart''.toArrowData :=
          eq_of_heq hCartValue
        have hCartSource := congrArg ArrowData.source hCartArrow
        have hCartTarget := congrArg ArrowData.target hCartArrow
        cases hCartSource
        cases hCartTarget
        have hCartData : cart' = cart'' := HomData.ext' cart' cart''
          (eq_of_heq (congrArgHEq ArrowData.hom hCartArrow))
        cases hCartData
        have hPhiMap := HomSemantic.baseMap_heq hPhi
        have hPhiValue := HomSemantic.value_heq hPhi
        cases congrArg HomSemantic.sourceBase hPhi
        cases congrArg HomSemantic.targetBase hPhi
        cases eq_of_heq hPhiMap
        have hPhiArrow : phi'.toArrowData = phi''.toArrowData :=
          eq_of_heq hPhiValue
        have hPhiSource := congrArg ArrowData.source hPhiArrow
        have hPhiTarget := congrArg ArrowData.target hPhiArrow
        cases hPhiSource
        cases hPhiTarget
        have hPhiData : phi' = phi'' := HomData.ext' phi' phi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPhiArrow))
        cases hPhiData
        have hhp : hp = hp' := Subsingleton.elim _ _
        cases hhp
        rfl
  · intro S R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq D
      eObj eMap eId eComp q E hE ihObj ihMap _ihId _ihComp E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | homGlue => simp_all
    | glueMap R' Dobj' Dmap' idRel' compRel' hglue' hDobj' hDmap' hId' hComp'
        hglue_eq' D' eObj' eMap' eId' eComp' q' E' hE' =>
        cases hE'
        simp_all
        rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel, hq⟩
        cases hS
        cases hR
        cases hDobjTerm
        have hDmapEq : @Dmap = @Dmap' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
        cases hDmapEq
        cases hIdRel
        have hCompRelEq : @compRel = @compRel' := by
          funext q r s k l
          exact congrFun (congrFun (congrFun (congrFun (congrFun
            (eq_of_heq hCompRel) q) r) s) k) l
        cases hCompRelEq
        cases hq
        have hObjValue (r : R.1.arrows.category) := ihObj r (eObj' r) rfl
        have hMapValue {r s : R.1.arrows.category} (k : r ⟶ s) :=
          ihMap k (eMap' k) rfl
        have hObj : D.obj = D'.obj := by
          funext r
          exact eq_of_heq (congrArgHEq ObjSemantic.value (hObjValue r))
        have hMap : ∀ {r s : R.1.arrows.category} (k : r ⟶ s),
            HEq (D.map k) (D'.map k) := by
          intro r s k
          have hArrow : D.mapArrow k = D'.mapArrow k :=
            eq_of_heq (HomSemantic.value_heq (hMapValue k))
          exact congrArgHEq ArrowData.hom hArrow
        have hD : D = D' := DescentOutput.ext' D D' hObj hMap
        cases hD
        rfl
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat D A B eta theta
      eA' eB' eDobj eDmap eId eComp eEta eTheta eEtaNat eThetaNat E hE
      ihA ihB ihDobj ihDmap _ihId _ihComp ihEta ihTheta _ihEtaNat _ihThetaNat
      E' eOther ht
    cases hE
    cases eOther with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue R' Dobj' Dmap' etaTerm' thetaTerm' ha' hb' hDobj' hDmap' idRel'
        compRel' hId' hComp' heta' htheta' etaNat' thetaNat' hetaNat' hthetaNat'
        D' A' B' eta' theta' eA'' eB'' eDobj' eDmap' eId' eComp' eEta' eTheta'
        eEtaNat' eThetaNat' E' hE' =>
        cases hE'
        simp only [Pre.homGlue.injEq] at ht
        rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel,
          haTerm, hbTerm, hEtaTerm, hThetaTerm, hEtaNatTerm, hThetaNatTerm⟩
        cases hS
        cases hR
        cases hDobjTerm
        have hDmapEq : @Dmap = @Dmap' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
        cases hDmapEq
        cases hIdRel
        have hCompRelEq : @compRel = @compRel' := by
          funext q r s k l
          exact congrFun (congrFun (congrFun (congrFun (congrFun
            (eq_of_heq hCompRel) q) r) s) k) l
        cases hCompRelEq
        cases haTerm
        cases hbTerm
        cases hEtaTerm
        cases hThetaTerm
        have hEtaNatEq : @etaNat = @etaNat' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hEtaNatTerm) q) r) k
        cases hEtaNatEq
        have hThetaNatEq : @thetaNat = @thetaNat' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hThetaNatTerm) q) r) k
        cases hThetaNatEq
        have hAValue := ihA eA'' rfl
        have hBValue := ihB eB'' rfl
        have hDobjValue (q : R.1.arrows.category) := ihDobj q (eDobj' q) rfl
        have hDmapValue {q r : R.1.arrows.category} (k : q ⟶ r) :=
          ihDmap k (eDmap' k) rfl
        have hEtaValue (q : R.1.arrows.category) := ihEta q (eEta' q) rfl
        have hThetaValue (q : R.1.arrows.category) := ihTheta q (eTheta' q) rfl
        have hDObj : D.obj = D'.obj := by
          funext q
          exact eq_of_heq (congrArgHEq ObjSemantic.value (hDobjValue q))
        have hDMap : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
            HEq (D.map k) (D'.map k) := by
          intro q r k
          have hArrow : D.mapArrow k = D'.mapArrow k :=
            eq_of_heq (HomSemantic.value_heq (hDmapValue k))
          exact congrArgHEq ArrowData.hom hArrow
        have hD : D = D' := DescentOutput.ext' D D' hDObj hDMap
        cases hD
        have hA : A = A' := eq_of_heq (congrArgHEq ObjSemantic.value hAValue)
        have hB : B = B' := eq_of_heq (congrArgHEq ObjSemantic.value hBValue)
        cases hA
        cases hB
        have hEtaHom : eta.hom = eta'.hom := by
          funext q
          have hArrow : eta.arrow q = eta'.arrow q :=
            eq_of_heq (HomSemantic.value_heq (hEtaValue q))
          exact eq_of_heq (congrArgHEq ArrowData.hom hArrow)
        have hThetaHom : theta.hom = theta'.hom := by
          funext q
          have hArrow : theta.arrow q = theta'.arrow q :=
            eq_of_heq (HomSemantic.value_heq (hThetaValue q))
          exact eq_of_heq (congrArgHEq ArrowData.hom hArrow)
        have hEta : eta = eta' := CoconeOutput.ext' eta eta' hEtaHom
        have hTheta : theta = theta' := CoconeOutput.ext' theta theta' hThetaHom
        cases hEta
        cases hTheta
        rfl
  · intros
    exact True.intro


theorem HomEvaluationStep.value_unique (F : X ⥤ᵇ Y)
    {E E' : HomEvaluation (J := J) (X := X) (Y := Y)}
    (eA : HomEvaluationStep F E) (eB : HomEvaluationStep F E')
    (ht : E.term = E'.term) : E.semantic = E'.semantic := by
  refine (HomEvaluationStep.rec (C := C) (J := J) (X := X) (Y := Y) (F := F)
    (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun E _ ↦ ∀ {E'} (_ : HomEvaluationStep F E'),
      E.term = E'.term → E.semantic = E'.semantic)
    (motive_3 := fun _ _ ↦ True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ eA) eB ht
  · intros
    exact True.intro
  · intros
    exact True.intro
  · intros
    exact True.intro
  · intro a b f E hE E' eB ht
    cases hE
    cases eB with
    | incl f' E' hE' =>
        cases hE'
        simp_all
        rcases ht with ⟨ha, hb, hf⟩
        cases ha
        cases hb
        cases hf
        rfl
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
  · intro S a ha A eObj E hE _ih E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | id ha' A' eObj' E' hE' =>
        cases hE'
        simp only [Pre.homId.injEq] at ht
        cases ht
        have hObj := ObjEvaluationStep.value_unique F eObj eObj' rfl
        have hBase := congrArg ObjSemantic.base hObj
        cases hBase
        have hValue : A = A' := eq_of_heq (congrArgHEq ObjSemantic.value hObj)
        cases hValue
        rfl
  · intro R S T a b c phi psi p q hphi hpsi A B D phi' psi' ePhi ePsi E hE
      ihPhi ihPsi E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | comp hphi' hpsi' A' B' D' phi'' psi'' ePhi' ePsi' E' hE' =>
        cases hE'
        simp only [Pre.homComp.injEq] at ht
        rcases ht with ⟨hphiTerm, hpsiTerm⟩
        cases hphiTerm
        cases hpsiTerm
        have hPhi := ihPhi ePhi' rfl
        have hPsi := ihPsi ePsi' rfl
        have hPhiMap := HomSemantic.baseMap_heq hPhi
        have hPhiValue := HomSemantic.value_heq hPhi
        cases congrArg HomSemantic.sourceBase hPhi
        cases congrArg HomSemantic.targetBase hPhi
        cases eq_of_heq hPhiMap
        have hPhiArrow : phi'.toArrowData = phi''.toArrowData :=
          eq_of_heq hPhiValue
        have hPhiSource := congrArg ArrowData.source hPhiArrow
        have hPhiTarget := congrArg ArrowData.target hPhiArrow
        cases hPhiSource
        cases hPhiTarget
        have hPhiData : phi' = phi'' := HomData.ext' phi' phi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPhiArrow))
        cases hPhiData
        have hPsiMap := HomSemantic.baseMap_heq hPsi
        have hPsiValue := HomSemantic.value_heq hPsi
        cases congrArg HomSemantic.sourceBase hPsi
        cases congrArg HomSemantic.targetBase hPsi
        cases eq_of_heq hPsiMap
        have hPsiArrow : psi'.toArrowData = psi''.toArrowData :=
          eq_of_heq hPsiValue
        have hPsiSource := congrArg ArrowData.source hPsiArrow
        have hPsiTarget := congrArg ArrowData.target hPsiArrow
        cases hPsiSource
        cases hPsiTarget
        have hPsiData : psi' = psi'' := HomData.ext' psi' psi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPsiArrow))
        cases hPsiData
        rfl
  · intro S T b hb B eObj f E hE _ih E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | pullMap hb' B' eObj' f' E' hE' =>
        cases hE'
        simp only [Pre.homPullMap.injEq] at ht
        rcases ht with ⟨hS, hT, hbTerm, hf⟩
        cases hS
        cases hT
        cases hbTerm
        cases hf
        have hObj := ObjEvaluationStep.value_unique F eObj eObj' rfl
        have hValue : B = B' := eq_of_heq (congrArgHEq ObjSemantic.value hObj)
        cases hValue
        rfl
  · intro R S T a b c cart phi p f g hcart hphi hp A B D cart' phi' eCart ePhi
      E hE ihCart ihPhi E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | glueMap => simp_all
    | homGlue => simp_all
    | factor f' g' hcart' hphi' hp' A' B' D' cart'' phi'' eCart' ePhi' E' hE' =>
        cases hE'
        simp only [Pre.homFactor.injEq] at ht
        rcases ht with ⟨hR, hS, hT, hCartTerm, hPhiTerm, hf, hg⟩
        cases hR
        cases hS
        cases hT
        cases hCartTerm
        cases hPhiTerm
        cases hf
        cases hg
        have hCart := ihCart eCart' rfl
        have hPhi := ihPhi ePhi' rfl
        have hCartMap := HomSemantic.baseMap_heq hCart
        have hCartValue := HomSemantic.value_heq hCart
        cases congrArg HomSemantic.sourceBase hCart
        cases congrArg HomSemantic.targetBase hCart
        cases eq_of_heq hCartMap
        have hCartArrow : cart'.toArrowData = cart''.toArrowData :=
          eq_of_heq hCartValue
        have hCartSource := congrArg ArrowData.source hCartArrow
        have hCartTarget := congrArg ArrowData.target hCartArrow
        cases hCartSource
        cases hCartTarget
        have hCartData : cart' = cart'' := HomData.ext' cart' cart''
          (eq_of_heq (congrArgHEq ArrowData.hom hCartArrow))
        cases hCartData
        have hPhiMap := HomSemantic.baseMap_heq hPhi
        have hPhiValue := HomSemantic.value_heq hPhi
        cases congrArg HomSemantic.sourceBase hPhi
        cases congrArg HomSemantic.targetBase hPhi
        cases eq_of_heq hPhiMap
        have hPhiArrow : phi'.toArrowData = phi''.toArrowData :=
          eq_of_heq hPhiValue
        have hPhiSource := congrArg ArrowData.source hPhiArrow
        have hPhiTarget := congrArg ArrowData.target hPhiArrow
        cases hPhiSource
        cases hPhiTarget
        have hPhiData : phi' = phi'' := HomData.ext' phi' phi''
          (eq_of_heq (congrArgHEq ArrowData.hom hPhiArrow))
        cases hPhiData
        have hhp : hp = hp' := Subsingleton.elim _ _
        cases hhp
        rfl
  · intro S R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq D
      eObj eMap eId eComp q E hE _ihObj ihMap _ihId _ihComp E' eB ht
    cases hE
    cases eB with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | homGlue => simp_all
    | glueMap R' Dobj' Dmap' idRel' compRel' hglue' hDobj' hDmap' hId' hComp'
        hglue_eq' D' eObj' eMap' eId' eComp' q' E' hE' =>
        cases hE'
        simp_all
        rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel, hq⟩
        cases hS
        cases hR
        cases hDobjTerm
        have hDmapEq : @Dmap = @Dmap' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
        cases hDmapEq
        cases hIdRel
        have hCompRelEq : @compRel = @compRel' := by
          funext q r s k l
          exact congrFun (congrFun (congrFun (congrFun (congrFun
            (eq_of_heq hCompRel) q) r) s) k) l
        cases hCompRelEq
        cases hq
        have hObjValue (r : R.1.arrows.category) :=
          ObjEvaluationStep.value_unique F (eObj r) (eObj' r) rfl
        have hMapValue {r s : R.1.arrows.category} (k : r ⟶ s) :=
          ihMap k (eMap' k) rfl
        have hObj : D.obj = D'.obj := by
          funext r
          exact eq_of_heq (congrArgHEq ObjSemantic.value (hObjValue r))
        have hMap : ∀ {r s : R.1.arrows.category} (k : r ⟶ s),
            HEq (D.map k) (D'.map k) := by
          intro r s k
          have hArrow : D.mapArrow k = D'.mapArrow k :=
            eq_of_heq (HomSemantic.value_heq (hMapValue k))
          exact congrArgHEq ArrowData.hom hArrow
        have hD : D = D' := DescentOutput.ext' D D' hObj hMap
        cases hD
        rfl
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat D A B eta theta
      eA' eB' eDobj eDmap eId eComp eEta eTheta eEtaNat eThetaNat E hE
      _ihA _ihB _ihDobj ihDmap _ihId _ihComp ihEta ihTheta _ihEtaNat _ihThetaNat
      E' eOther ht
    cases hE
    cases eOther with
    | incl => simp_all
    | id => simp_all
    | comp => simp_all
    | pullMap => simp_all
    | factor => simp_all
    | glueMap => simp_all
    | homGlue R' Dobj' Dmap' etaTerm' thetaTerm' ha' hb' hDobj' hDmap' idRel'
        compRel' hId' hComp' heta' htheta' etaNat' thetaNat' hetaNat' hthetaNat'
        D' A' B' eta' theta' eA'' eB'' eDobj' eDmap' eId' eComp' eEta' eTheta'
        eEtaNat' eThetaNat' E' hE' =>
        cases hE'
        simp only [Pre.homGlue.injEq] at ht
        rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel,
          haTerm, hbTerm, hEtaTerm, hThetaTerm, hEtaNatTerm, hThetaNatTerm⟩
        cases hS
        cases hR
        cases hDobjTerm
        have hDmapEq : @Dmap = @Dmap' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
        cases hDmapEq
        cases hIdRel
        have hCompRelEq : @compRel = @compRel' := by
          funext q r s k l
          exact congrFun (congrFun (congrFun (congrFun (congrFun
            (eq_of_heq hCompRel) q) r) s) k) l
        cases hCompRelEq
        cases haTerm
        cases hbTerm
        cases hEtaTerm
        cases hThetaTerm
        have hEtaNatEq : @etaNat = @etaNat' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hEtaNatTerm) q) r) k
        cases hEtaNatEq
        have hThetaNatEq : @thetaNat = @thetaNat' := by
          funext q r k
          exact congrFun (congrFun (congrFun (eq_of_heq hThetaNatTerm) q) r) k
        cases hThetaNatEq
        have hAValue := ObjEvaluationStep.value_unique F eA' eA'' rfl
        have hBValue := ObjEvaluationStep.value_unique F eB' eB'' rfl
        have hDobjValue (q : R.1.arrows.category) :=
          ObjEvaluationStep.value_unique F (eDobj q) (eDobj' q) rfl
        have hDmapValue {q r : R.1.arrows.category} (k : q ⟶ r) :=
          ihDmap k (eDmap' k) rfl
        have hEtaValue (q : R.1.arrows.category) := ihEta q (eEta' q) rfl
        have hThetaValue (q : R.1.arrows.category) := ihTheta q (eTheta' q) rfl
        have hDObj : D.obj = D'.obj := by
          funext q
          exact eq_of_heq (congrArgHEq ObjSemantic.value (hDobjValue q))
        have hDMap : ∀ {q r : R.1.arrows.category} (k : q ⟶ r),
            HEq (D.map k) (D'.map k) := by
          intro q r k
          have hArrow : D.mapArrow k = D'.mapArrow k :=
            eq_of_heq (HomSemantic.value_heq (hDmapValue k))
          exact congrArgHEq ArrowData.hom hArrow
        have hD : D = D' := DescentOutput.ext' D D' hDObj hDMap
        cases hD
        have hA : A = A' := eq_of_heq (congrArgHEq ObjSemantic.value hAValue)
        have hB : B = B' := eq_of_heq (congrArgHEq ObjSemantic.value hBValue)
        cases hA
        cases hB
        have hEtaHom : eta.hom = eta'.hom := by
          funext q
          have hArrow : eta.arrow q = eta'.arrow q :=
            eq_of_heq (HomSemantic.value_heq (hEtaValue q))
          exact eq_of_heq (congrArgHEq ArrowData.hom hArrow)
        have hThetaHom : theta.hom = theta'.hom := by
          funext q
          have hArrow : theta.arrow q = theta'.arrow q :=
            eq_of_heq (HomSemantic.value_heq (hThetaValue q))
          exact eq_of_heq (congrArgHEq ArrowData.hom hArrow)
        have hEta : eta = eta' := CoconeOutput.ext' eta eta' hEtaHom
        have hTheta : theta = theta' := CoconeOutput.ext' theta theta' hThetaHom
        cases hEta
        cases hTheta
        rfl
  · intros
    exact True.intro

/-- The endpoints packaged by an evaluated arrow agree with every evaluation of its
source and target terms. -/
theorem HomEvaluationStep.endpoints_unique (F : X ⥤ᵇ Y)
    {E : HomEvaluation (J := J) (X := X) (Y := Y)}
    (e : HomEvaluationStep F E) :
    (∀ {O : ObjEvaluation (J := J) (X := X) (Y := Y)},
      ObjEvaluationStep F O → E.sourceTerm = O.term →
        (⟨E.sourceBase, E.value.source⟩ : ObjSemantic (Y := Y)) = O.semantic) ∧
    (∀ {O : ObjEvaluation (J := J) (X := X) (Y := Y)},
      ObjEvaluationStep F O → E.targetTerm = O.term →
        (⟨E.targetBase, E.value.target⟩ : ObjSemantic (Y := Y)) = O.semantic) := by
  refine HomEvaluationStep.rec (C := C) (J := J) (X := X) (Y := Y) (F := F)
    (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun E _ ↦
      (∀ {O : ObjEvaluation (J := J) (X := X) (Y := Y)},
        ObjEvaluationStep F O → E.sourceTerm = O.term →
          (⟨E.sourceBase, E.value.source⟩ : ObjSemantic (Y := Y)) = O.semantic) ∧
      (∀ {O : ObjEvaluation (J := J) (X := X) (Y := Y)},
        ObjEvaluationStep F O → E.targetTerm = O.term →
          (⟨E.targetBase, E.value.target⟩ : ObjSemantic (Y := Y)) = O.semantic))
    (motive_3 := fun _ _ ↦ True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intros
    exact True.intro
  · intros
    exact True.intro
  · intros
    exact True.intro
  · intro a b f E hE
    cases hE
    constructor
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F
        (ObjEvaluationStep.incl a _ rfl) eO ht
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F
        (ObjEvaluationStep.incl b _ rfl) eO ht
  · intro S a ha A eA E hE _ih
    cases hE
    constructor
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F eA eO ht
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F eA eO ht
  · intro R S T a b c phi psi p q hphi hpsi A B D phi' psi' ePhi ePsi E hE
      ihPhi ihPsi
    cases hE
    exact ⟨ihPhi.1, ihPsi.2⟩
  · intro S T b hb B eB f E hE _ih
    cases hE
    constructor
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F
        (ObjEvaluationStep.pull hb B eB f _ rfl) eO ht
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F eB eO ht
  · intro R S T a b c cart phi p f g hcart hphi hp A B D cart' phi'
      eCart ePhi E hE ihCart ihPhi
    cases hE
    exact ⟨ihPhi.1, ihCart.1⟩
  · intro S R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq D
      eObj eMap eId eComp q E hE _ihObj _ihMap _ihId _ihComp
    cases hE
    constructor
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F (eObj q) eO ht
    · intro O eO ht
      cases hglue_eq
      exact ObjEvaluationStep.value_unique F
        (ObjEvaluationStep.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp
          D eObj eMap eId eComp _ rfl) eO ht
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat D A B eta theta
      eA eB eDobj eDmap eId eComp eEta eTheta eEtaNat eThetaNat E hE
      _ihA _ihB _ihDobj _ihDmap _ihId _ihComp _ihEta _ihTheta _ihEtaNat _ihThetaNat
    cases hE
    constructor
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F eA eO ht
    · intro O eO ht
      exact ObjEvaluationStep.value_unique F eB eO ht
  · intros
    exact True.intro

/-- An object evaluator graph witnessing a fixed semantic endpoint, with the typing
derivation existentially packaged because typing derivations live in `Type`. -/
def EndpointStep (F : X ⥤ᵇ Y) (t : Pre J X) (S : C) (A : ObjData Y S) :=
  Σ h : IsObj J X t S, ObjEvaluationStep F ⟨t, S, h, A⟩

/-- Recover evaluator graphs for the source and target packages of an evaluated
arrow. -/
noncomputable def HomEvaluationStep.endpointSteps (F : X ⥤ᵇ Y)
    {E : HomEvaluation (J := J) (X := X) (Y := Y)}
    (e : HomEvaluationStep F E) :
    EndpointStep F E.sourceTerm E.sourceBase E.value.source ×
      EndpointStep F E.targetTerm E.targetBase E.value.target := by
  refine HomEvaluationStep.rec (C := C) (J := J) (X := X) (Y := Y) (F := F)
    (motive_1 := fun _ _ ↦ PUnit)
    (motive_2 := fun E _ ↦
      EndpointStep F E.sourceTerm E.sourceBase E.value.source ×
        EndpointStep F E.targetTerm E.targetBase E.value.target)
    (motive_3 := fun _ _ ↦ PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intro a b f E hE
    cases hE
    exact ⟨⟨.incl a, .incl a _ rfl⟩, ⟨.incl b, .incl b _ rfl⟩⟩
  · intro S a ha A eA E hE _ih
    cases hE
    exact ⟨⟨ha, eA⟩, ⟨ha, eA⟩⟩
  · intro R S T a b c phi psi p q hphi hpsi A B D phi' psi' ePhi ePsi E hE
      ihPhi ihPsi
    cases hE
    exact ⟨ihPhi.1, ihPsi.2⟩
  · intro S T b hb B eB f E hE _ih
    cases hE
    exact ⟨⟨.pull hb f, .pull hb B eB f _ rfl⟩, ⟨hb, eB⟩⟩
  · intro R S T a b c cart phi p f g hcart hphi hp A B D cart' phi'
      eCart ePhi E hE ihCart ihPhi
    cases hE
    exact ⟨ihPhi.1, ihCart.1⟩
  · intro S R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq D
      eObj eMap eId eComp q E hE _ihObj _ihMap _ihId _ihComp
    cases hE
    cases hglue_eq
    exact ⟨⟨hDobj q, eObj q⟩,
      ⟨.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp,
        .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp D
          eObj eMap eId eComp _ rfl⟩⟩
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat D A B eta theta
      eA eB eDobj eDmap eId eComp eEta eTheta eEtaNat eThetaNat E hE
      _ihA _ihB _ihDobj _ihDmap _ihId _ihComp _ihEta _ihTheta _ihEtaNat _ihThetaNat
    cases hE
    exact ⟨⟨ha, eA⟩, ⟨hb, eB⟩⟩
  · intros
    exact PUnit.unit

/-- Extract the semantic cocones and glued morphism from an evaluator step whose raw
term is a formal `homGlue` constructor. -/
noncomputable def HomEvaluationStep.homGlueView (F : X ⥤ᵇ Y) {S : C}
    (R : J.Cover S) (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (a b : Pre J X) (etaTerm thetaTerm : ∀ q, Pre J X)
    (etaNat thetaNat : ∀ {q r} (k : q ⟶ r), Pre J X)
    (hglue : IsHom J X
      (.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat)
      a b (𝟙 S)) (P : ArrowData Y S S (𝟙 S))
    (e : HomEvaluationStep F
      ⟨.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat,
        a, b, S, S, 𝟙 S, hglue, P⟩) :
    HomGlueView F R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat P := by
  let target : HomEvaluation (J := J) (X := X) (Y := Y) :=
    ⟨.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat,
      a, b, S, S, 𝟙 S, hglue, P⟩
  refine HomEvaluationStep.rec (C := C) (J := J) (X := X) (Y := Y) (F := F)
    (motive_1 := fun _ _ ↦ PUnit)
    (motive_2 := fun E _ ↦ E = target →
      HomGlueView F R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat P)
    (motive_3 := fun _ _ ↦ PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e rfl
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intro a' b' f E hE hroot
    cases hE
    simp_all [target]
  · intro S' a' ha A eA E hE _ih hroot
    cases hE
    simp_all [target]
  · intro Q S' T a' b' c phi psi p q hphi hpsi A B D phi' psi'
      ePhi ePsi E hE _ihPhi _ihPsi hroot
    cases hE
    simp_all [target]
  · intro S' T b' hb B eB f E hE _ih hroot
    cases hE
    simp_all [target]
  · intro Q S' T a' b' c cart phi p f g hcart hphi hp A B D cart' phi'
      eCart ePhi E hE _ihCart _ihPhi hroot
    cases hE
    simp_all [target]
  · intro S' R' Dobj' Dmap' idRel' compRel' hglue' hDobj' hDmap' hId' hComp'
      hglue_eq' D' eObj' eMap' eId' eComp' q E hE
      _ihObj _ihMap _ihId _ihComp hroot
    cases hE
    simp_all [target]
  · intro S' R' Dobj' Dmap' a' b' etaTerm' thetaTerm' ha' hb' hDobj' hDmap'
      idRel' compRel' hId' hComp' heta' htheta' etaNat' thetaNat' hetaNat'
      hthetaNat' D A B eta theta eA eB eDobj eDmap eId eComp eEta eTheta
      eEtaNat eThetaNat E hE _ihA _ihB _ihDobj _ihDmap _ihId _ihComp
      _ihEta _ihTheta _ihEtaNat _ihThetaNat hroot
    cases hE
    have ht := congrArg HomEvaluation.term hroot
    have hv := congrArgHEq HomEvaluation.value hroot
    dsimp [target] at ht hv
    simp only [Pre.homGlue.injEq] at ht
    rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel,
      haTerm, hbTerm, hEtaTerm, hThetaTerm, hEtaNatTerm, hThetaNatTerm⟩
    cases hS
    cases hR
    cases hDobjTerm
    have hDmapEq : @Dmap' = @Dmap := by
      funext q r k
      exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) q) r) k
    cases hDmapEq
    cases hIdRel
    have hCompRelEq : @compRel' = @compRel := by
      funext q r s k l
      exact congrFun (congrFun (congrFun (congrFun (congrFun
        (eq_of_heq hCompRel) q) r) s) k) l
    cases hCompRelEq
    cases haTerm
    cases hbTerm
    cases hEtaTerm
    cases hThetaTerm
    have hEtaNatEq : @etaNat' = @etaNat := by
      funext q r k
      exact congrFun (congrFun (congrFun (eq_of_heq hEtaNatTerm) q) r) k
    cases hEtaNatEq
    have hThetaNatEq : @thetaNat' = @thetaNat := by
      funext q r k
      exact congrFun (congrFun (congrFun (eq_of_heq hThetaNatTerm) q) r) k
    cases hThetaNatEq
    exact ⟨heta', htheta', D, A, B, eta, theta, eEta, eTheta,
      (eq_of_heq hv).symm⟩
  · intros
    exact PUnit.unit

/-- A formal relation forces equality of the semantic arrows assigned to its two
sides, independently of the particular evaluator derivations used for those sides. -/
theorem RelEvaluationStep.hom_heq (F : X ⥤ᵇ Y)
    {E : RelEvaluation (J := J) (X := X) (Y := Y)}
    (e : RelEvaluationStep F E)
    {L R : HomEvaluation (J := J) (X := X) (Y := Y)}
    (eL : HomEvaluationStep F L) (eR : HomEvaluationStep F R)
    (hL : E.leftTerm = L.term) (hR : E.rightTerm = R.term) :
    HEq L.value.hom R.value.hom := by
  cases e with
  | mk h equation leftStep rightStep E hE =>
      cases hE
      have hLeft := HomEvaluationStep.value_unique F leftStep eL hL
      have hRight := HomEvaluationStep.value_unique F rightStep eR hR
      have hhLeft : HEq equation.left L.value.hom :=
        congrArgHEq (fun s : HomSemantic (Y := Y) ↦ s.value.hom) hLeft
      have hhRight : HEq equation.right R.value.hom :=
        congrArgHEq (fun s : HomSemantic (Y := Y) ↦ s.value.hom) hRight
      have hhEq : HEq equation.left equation.right := equation.eq.heq
      exact hhLeft.symm.trans (hhEq.trans hhRight)


/-- The type of semantic object evaluations of a fixed typing derivation. -/
def ObjResult (F : X ⥤ᵇ Y) {t : Pre J X} {S : C} (h : IsObj J X t S) :=
  Σ A : ObjData Y S, ObjEvaluationStep F ⟨t, S, h, A⟩

/-- The type of semantic arrow evaluations of a fixed typing derivation. -/
def HomResult (F : X ⥤ᵇ Y) {phi a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X phi a b f) :=
  Σ p : ArrowData Y S T f, HomEvaluationStep F ⟨phi, a, b, S, T, f, h, p⟩

/-- The type of semantic relation evaluations of a fixed typing derivation. -/
def RelResult (F : X ⥤ᵇ Y) {rho phi psi a b : Pre J X} {S T : C}
    {f g : S ⟶ T} (h : IsRel J X rho phi psi a b f g) :=
  Σ e : EquationData Y S T f g,
    RelEvaluationStep F ⟨rho, phi, psi, a, b, S, T, f, g, h, e⟩

/-- Package a semantic equation from evaluated left and right arrows once equality
of their underlying total-category morphisms is known. Endpoint agreement is derived
from the evaluator graph. -/
noncomputable def makeRelResult (F : X ⥤ᵇ Y)
    {rho phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    (h : IsRel J X rho phi psi a b f g)
    (L : ArrowData Y S T f)
    (eL : HomEvaluationStep F ⟨phi, a, b, S, T, f, h.leftHom, L⟩)
    (R : ArrowData Y S T g)
    (eR : HomEvaluationStep F ⟨psi, a, b, S, T, g, h.rightHom, R⟩)
    (hh : HEq L.hom R.hom) : RelResult F h := by
  let leftEnds := HomEvaluationStep.endpointSteps F eL
  let rightEnds := HomEvaluationStep.endpointSteps F eR
  have hsource : L.source = R.source := by
    have hsem := ObjEvaluationStep.value_unique F leftEnds.1.2 rightEnds.1.2 rfl
    exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
  have htarget : L.target = R.target := by
    have hsem := ObjEvaluationStep.value_unique F leftEnds.2.2 rightEnds.2.2 rfl
    exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
  let rightData := R.toHomDataOfEndpoints L.source L.target hsource.symm htarget.symm
  have hrightArrow : rightData.toArrowData = R :=
    ArrowData.toHomDataOfEndpoints_toArrowData R L.source L.target
      hsource.symm htarget.symm
  have hrightHom : HEq rightData.hom R.hom :=
    congrArgHEq ArrowData.hom hrightArrow
  have heq : L.hom = rightData.hom := eq_of_heq (hh.trans hrightHom.symm)
  let equation : EquationData Y S T f g :=
    { source := L.source
      target := L.target
      left := L.hom
      right := rightData.hom
      leftLift := L.isLift
      rightLift := rightData.isLift
      eq := heq }
  have leftStep : HomEvaluationStep F
      ⟨phi, a, b, S, T, f, h.leftHom, equation.leftArrow⟩ := by
    apply HomEvaluationStep.reindex F eL rfl
    exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
  have rightStep : HomEvaluationStep F
      ⟨psi, a, b, S, T, g, h.rightHom, equation.rightArrow⟩ := by
    apply HomEvaluationStep.reindex F eR rfl
    exact hrightArrow.symm.heq
  exact ⟨equation, .mk h equation leftStep rightStep _ rfl⟩

/-- The semantic descent package retained by the enriched evaluator at an object
gluing constructor. -/
structure GlueWitness (F : X ⥤ᵇ Y) {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
    (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
      (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
    (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
      IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
        (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
    (A : ObjData Y S) where
  D : DescentOutput (Y := Y) R
  eObj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩
  eMap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
    ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
      hDmap k, D.mapArrow k⟩
  eId : ∀ q, RelEvaluationStep F
    ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
      q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩
  eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
    ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
      q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
      hComp k l, D.compEquation k l⟩
  value_eq : A = D.gluedObj

/-- A gluing witness whose typing constituents are existentially retained. -/
structure AnyGlueWitness (F : X ⥤ᵇ Y) {Sbase Scover : C} (R : J.Cover Scover)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj (@Dmap) idRel (@compRel)) Sbase)
    (A : ObjData Y Sbase) where
  base_eq : Sbase = Scover
  hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left
  hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left
  hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
    (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left)
  hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
    IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
      (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left
  hglue_heq : HEq hglue
    (IsObj.glue R Dobj (@Dmap) hDobj (@hDmap) idRel (@compRel) hId (@hComp))
  D : DescentOutput (Y := Y) R
  eObj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩
  eMap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
    ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
      hDmap k, D.mapArrow k⟩
  eId : ∀ q, RelEvaluationStep F
    ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
      q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩
  eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
    ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
      q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
      hComp k l, D.compEquation k l⟩
  value_heq : HEq A D.gluedObj

/-- Extra constructor-specific data retained by the object evaluator. -/
def ObjSpecial (F : X ⥤ᵇ Y) {t : Pre J X} {S : C}
    (h : IsObj J X t S) (A : ObjData Y S) : Type (max u v w z yv yu) :=
  match t with
  | .objGlue R Dobj Dmap idRel compRel =>
      AnyGlueWitness F R Dobj (@Dmap) idRel (@compRel) h A
  | _ => PUnit

/-- The enriched object result used internally by the mutual recursor. -/
def ObjCoreResult (F : X ⥤ᵇ Y) {t : Pre J X} {S : C} (h : IsObj J X t S) :=
  Σ r : ObjResult F h, ObjSpecial F h r.1

/-- A semantic descent diagram together with evaluator graphs for all of its
constituents. -/
structure DescentEvaluation (F : X ⥤ᵇ Y) {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
    (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
      (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
    (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
      IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
        (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left) where
  D : DescentOutput (Y := Y) R
  eObj : ∀ q, ObjEvaluationStep F ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩
  eMap : ∀ {q r} (k : q ⟶ r), HomEvaluationStep F
    ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
      hDmap k, D.mapArrow k⟩
  eId : ∀ q, RelEvaluationStep F
    ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
      q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q, D.idEquation q⟩
  eComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelEvaluationStep F
    ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l), Dobj q, Dobj s,
      q.obj.left, s.obj.left, k.hom.left ≫ l.hom.left, (k ≫ l).hom.left,
      hComp k l, D.compEquation k l⟩

/-- Assemble a semantic descent evaluation from the mutually recursive evaluator
results of its objects, arrows, and relations. -/
noncomputable def buildDescentEvaluation (F : X ⥤ᵇ Y) {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (hDobj : ∀ q, IsObj J X (Dobj q) q.obj.left)
    (hDmap : ∀ {q r} (k : q ⟶ r), IsHom J X (Dmap k) (Dobj q) (Dobj r) k.hom.left)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hId : ∀ q, IsRel J X (idRel q) (Dmap (𝟙 q)) (.homId (Dobj q))
      (Dobj q) (Dobj q) (𝟙 q.obj.left) (𝟙 q.obj.left))
    (hComp : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s),
      IsRel J X (compRel k l) (.homComp (Dmap k) (Dmap l)) (Dmap (k ≫ l))
        (Dobj q) (Dobj s) (k.hom.left ≫ l.hom.left) (k ≫ l).hom.left)
    (objResult : ∀ q, ObjResult F (hDobj q))
    (mapResult : ∀ {q r} (k : q ⟶ r), HomResult F (hDmap k))
    (idResult : ∀ q, RelResult F (hId q))
    (compResult : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), RelResult F (hComp k l)) :
    DescentEvaluation F R Dobj Dmap hDobj hDmap idRel compRel hId hComp := by
  have source_eq {q r : R.1.arrows.category} (k : q ⟶ r) :
      (mapResult k).1.source = (objResult q).1 := by
    have hsem := (HomEvaluationStep.endpoints_unique F (mapResult k).2).1
      (objResult q).2 rfl
    exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
  have target_eq {q r : R.1.arrows.category} (k : q ⟶ r) :
      (mapResult k).1.target = (objResult r).1 := by
    have hsem := (HomEvaluationStep.endpoints_unique F (mapResult k).2).2
      (objResult r).2 rfl
    exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
  let mapData {q r : R.1.arrows.category} (k : q ⟶ r) :
      HomData Y (objResult q).1 (objResult r).1 k.hom.left :=
    (mapResult k).1.toHomDataOfEndpoints (objResult q).1 (objResult r).1
      (source_eq k) (target_eq k)
  have mapStep {q r : R.1.arrows.category} (k : q ⟶ r) :
      HomEvaluationStep F
        ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
          hDmap k, (mapData k).toArrowData⟩ := by
    rw [ArrowData.toHomDataOfEndpoints_toArrowData]
    exact (mapResult k).2
  have map_id (q : R.1.arrows.category) :
      (mapData (𝟙 q)).hom = 𝟙 (objResult q).1.obj := by
    let identityStep : HomEvaluationStep F
        ⟨.homId (Dobj q), Dobj q, Dobj q, q.obj.left, q.obj.left,
          𝟙 q.obj.left, ⟨IsHom.id (hDobj q)⟩, idArrow (objResult q).1⟩ :=
      .id (hDobj q) (objResult q).1 (objResult q).2 _ rfl
    exact eq_of_heq (RelEvaluationStep.hom_heq F (idResult q).2
      (eL := mapStep (𝟙 q)) (eR := identityStep) (hL := rfl) (hR := rfl))
  have map_comp {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
      (mapData (k ≫ l)).hom = (mapData k).hom ≫ (mapData l).hom := by
    let compositeStep : HomEvaluationStep F
        ⟨.homComp (Dmap k) (Dmap l), Dobj q, Dobj s, q.obj.left, s.obj.left,
          k.hom.left ≫ l.hom.left, ⟨IsHom.comp (hDmap k) (hDmap l)⟩,
          compArrow (mapData k) (mapData l)⟩ :=
      .comp (hDmap k) (hDmap l) (objResult q).1 (objResult r).1 (objResult s).1
        (mapData k) (mapData l) (mapStep k) (mapStep l) _ rfl
    have hh := RelEvaluationStep.hom_heq F (compResult k l).2
      (eL := compositeStep) (eR := mapStep (k ≫ l)) (hL := rfl) (hR := rfl)
    exact (eq_of_heq hh).symm
  let D : DescentOutput (Y := Y) R :=
    { obj := fun q ↦ (objResult q).1
      map := fun {_ _} k ↦ (mapData k).hom
      mapLift := fun {_ _} k ↦ (mapData k).isLift
      map_id := map_id
      map_comp := map_comp }
  have eObj (q : R.1.arrows.category) : ObjEvaluationStep F
      ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩ := (objResult q).2
  have eMap {q r : R.1.arrows.category} (k : q ⟶ r) : HomEvaluationStep F
      ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
        hDmap k, D.mapArrow k⟩ := mapStep k
  have eId (q : R.1.arrows.category) : RelEvaluationStep F
      ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
        q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q,
        D.idEquation q⟩ := by
    have hleft : HomEvaluationStep F
        ⟨Dmap (𝟙 q), Dobj q, Dobj q, q.obj.left, q.obj.left,
          𝟙 q.obj.left, (hId q).leftHom, (D.idEquation q).leftArrow⟩ := by
      apply HomEvaluationStep.reindex F (eMap (𝟙 q)) (by simp)
      exact ArrowData.heq_of_base_eq _ _ (by simp) rfl rfl (HEq.rfl)
    have hright : HomEvaluationStep F
        ⟨.homId (Dobj q), Dobj q, Dobj q, q.obj.left, q.obj.left,
          𝟙 q.obj.left, (hId q).rightHom, (D.idEquation q).rightArrow⟩ := by
      apply HomEvaluationStep.reindex F
        (.id (hDobj q) (D.obj q) (eObj q) _ rfl) rfl
      exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
    exact .mk (hId q) (D.idEquation q) hleft hright _ rfl
  have eComp {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
      RelEvaluationStep F
        ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l),
          Dobj q, Dobj s, q.obj.left, s.obj.left,
          k.hom.left ≫ l.hom.left, (k ≫ l).hom.left, hComp k l,
          D.compEquation k l⟩ := by
    have hleft : HomEvaluationStep F
        ⟨.homComp (Dmap k) (Dmap l), Dobj q, Dobj s, q.obj.left, s.obj.left,
          k.hom.left ≫ l.hom.left, (hComp k l).leftHom,
          (D.compEquation k l).leftArrow⟩ := by
      apply HomEvaluationStep.reindex F
        (.comp (hDmap k) (hDmap l) (D.obj q) (D.obj r) (D.obj s)
          (mapData k) (mapData l) (eMap k) (eMap l) _ rfl) rfl
      exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
    have hright : HomEvaluationStep F
        ⟨Dmap (k ≫ l), Dobj q, Dobj s, q.obj.left, s.obj.left,
          (k ≫ l).hom.left, (hComp k l).rightHom,
          (D.compEquation k l).rightArrow⟩ := by
      apply HomEvaluationStep.reindex F (eMap (k ≫ l)) rfl
      exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
    exact .mk (hComp k l) (D.compEquation k l) hleft hright _ rfl
  exact ⟨D, eObj, eMap, eId, eComp⟩


end CategoryTheory.BasedCategory.FreeStackCompletion.Interpretation
