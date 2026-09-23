module

public import StacksAndModuli.API.FreeStackCompletionInterpretation

/-!
# Universal property of the free stack completion

This module proves the morphism-level universal property of
`FreeStackCompletion`. Transformations on the generators extend to the completion,
the extension is natural along the formal quotient arrows, and transformations out
of the completion are determined by their restriction to the generators.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe v u w z yv yu

namespace CategoryTheory.BasedCategory.FreeStackCompletion.UniversalGraph

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : BasedCategory.{w, z} C}
variable {Y : BasedCategory.{yv, yu} C} [BasedCategory.IsStack J Y]

abbrev objOf {t : Pre J X} {S : C} (h : IsObj J X t S) : Obj J X :=
  ⟨S, t, ⟨h⟩⟩

@[simp]
lemma objOf_eq {t : Pre J X} {S : C} (h h' : IsObj J X t S) :
    objOf h = objOf h' := rfl

def homOf {phi a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X phi a b f) : objOf h.sourceObj ⟶ objOf h.targetObj :=
  ⟦⟨f, phi, ⟨h⟩⟩⟧

lemma homOf_isHomLift {phi a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X phi a b f) : IsHomLift (completion J X).p f (homOf h) := by
  refine IsHomLift.of_fac' (completion J X).p f (homOf h) rfl rfl ?_
  change f = eqToHom rfl ≫ f ≫ eqToHom rfl
  simp

lemma homOf_rel {rho phi psi a b : Pre J X} {S T : C} {f g : S ⟶ T}
    (h : IsRel J X rho phi psi a b f g) :
    homOf h.leftHom = homOf h.rightHom := by
  apply _root_.Quotient.sound
  exact ⟨rho, ⟨h⟩⟩

lemma homOf_pullMap_irrel {S T : C} {b : Pre J X}
    (hb hb' : IsObj J X b T) (f : S ⟶ T) :
    homOf (.pullMap hb f) = homOf (.pullMap hb' f) := rfl

lemma homOf_glueMap_irrel {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (h h' : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (q : R.1.arrows.category) :
    homOf (.glueMap R Dobj Dmap idRel compRel h q) =
      homOf (.glueMap R Dobj Dmap idRel compRel h' q) := rfl

@[simp]
lemma homOf_id {a : Pre J X} {S : C} (ha : IsObj J X a S) :
    homOf (.id ha) = 𝟙 (objOf ha) := rfl

@[simp]
lemma homOf_comp {R S T : C} {a b c phi psi : Pre J X}
    {f : R ⟶ S} {g : S ⟶ T}
    (hphi : IsHom J X phi a b f) (hpsi : IsHom J X psi b c g) :
    homOf (.comp hphi hpsi) = homOf hphi ≫ homOf hpsi := rfl

variable (H K : completion J X ⥤ᵇ Y)
variable (alpha : BasedNatTrans ((inclusion J X).comp H) ((inclusion J X).comp K))

/-- A component and its typing data, with all dependent indices hidden in one
package. -/
structure ComponentEvaluation where
  base : C
  obj : (completion J X).obj
  base_eq : obj.base = base
  value : H.obj obj ⟶ K.obj obj
  isLift : IsHomLift Y.p (𝟙 base) value

/-- Package a component at a particular object-typing derivation. -/
abbrev ComponentEvaluation.of {t : Pre J X} {S : C} (h : IsObj J X t S)
    (phi : H.obj (objOf h) ⟶ K.obj (objOf h))
    (hphi : IsHomLift Y.p (𝟙 S) phi) : ComponentEvaluation H K :=
  ⟨S, objOf h, rfl, phi, hphi⟩

lemma ComponentEvaluation.value_heq {E E' : ComponentEvaluation H K}
    (h : E = E') : HEq E.value E'.value := by
  cases h
  rfl

/-- Recursive construction rules for components, indexed by an opaque package so
that higher-order fields of gluing syntax never enter dependent elimination. -/
inductive ComponentStep : ComponentEvaluation H K → Type (max u v w z yv yu)
  | incl (a : X.obj) (E : ComponentEvaluation H K)
      (hE : E = ComponentEvaluation.of H K (.incl a) (alpha.app a)
        (alpha.isHomLift rfl)) : ComponentStep E
  | pull {S T : C} {b : Pre J X} (hb : IsObj J X b T) (f : S ⟶ T)
      (psi : H.obj (objOf hb) ⟶ K.obj (objOf hb))
      (hpsi : IsHomLift Y.p (𝟙 T) psi)
      (ePsi : ComponentStep (ComponentEvaluation.of H K hb psi hpsi))
      (phi : H.obj (objOf (.pull hb f)) ⟶ K.obj (objOf (.pull hb f)))
      (hphi : IsHomLift Y.p (𝟙 S) phi)
      (fac : H.map (homOf (.pullMap hb f)) ≫ psi =
        phi ≫ K.map (homOf (.pullMap hb f)))
      (E : ComponentEvaluation H K)
      (hE : E = ComponentEvaluation.of H K (.pull hb f) phi hphi) :
      ComponentStep E
  | glue {S : C} (R : J.Cover S)
      (Dobj : R.1.arrows.category → Pre J X)
      (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
      (idRel : ∀ q, Pre J X)
      (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
      (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
      (psi : ∀ q, H.obj (objOf (IsObj.children hglue q)) ⟶
        K.obj (objOf (IsObj.children hglue q)))
      (hpsi : ∀ q, IsHomLift Y.p (𝟙 q.obj.left) (psi q))
      (ePsi : ∀ q, ComponentStep
        (ComponentEvaluation.of H K (IsObj.children hglue q) (psi q) (hpsi q)))
      (phi : H.obj (objOf hglue) ⟶ K.obj (objOf hglue))
      (hphi : IsHomLift Y.p (𝟙 S) phi)
      (fac : ∀ q, H.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q)) ≫ phi =
        psi q ≫ K.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q)))
      (E : ComponentEvaluation H K)
      (hE : E = ComponentEvaluation.of H K hglue phi hphi) :
      ComponentStep E

set_option maxHeartbeats 1000000 in
-- The dependent graph recursor compares three large constructor families and
-- exceeds the default heartbeat limit while normalizing their transport equalities.
/-- Component values produced by the recursive graph are unique for a fixed raw
object term. -/
theorem ComponentStep.value_unique {E E' : ComponentEvaluation H K}
    (e : ComponentStep H K alpha E) (e' : ComponentStep H K alpha E')
    (ht : E.obj.term = E'.obj.term) : HEq E.value E'.value := by
  refine (ComponentStep.rec (H := H) (K := K) (alpha := alpha)
    (motive := fun E _ ↦ ∀ {E'} (_ : ComponentStep H K alpha E'),
      E.obj.term = E'.obj.term → HEq E.value E'.value)
    ?_ ?_ ?_ e) e' ht
  · intro a E hE E' e' ht
    cases hE
    cases e' with
    | incl a' E' hE' =>
        cases hE'
        simp_all
        cases ht
        rfl
    | pull => simp_all
    | glue => simp_all
  · intro S T b hb f psi hpsi ePsi phi hphi fac E hE ihPsi E' e' ht
    cases hE
    cases e' with
    | incl => simp_all
    | glue => simp_all
    | pull hb' f' psi' hpsi' ePsi' phi' hphi' fac' E' hE' =>
        cases hE'
        simp only [Pre.objPull.injEq] at ht
        rcases ht with ⟨hS, hT, hbTerm, hf⟩
        cases hS
        cases hT
        cases hbTerm
        cases hf
        have hchild := ihPsi ePsi' rfl
        have hpsiEq : psi = psi' := eq_of_heq hchild
        cases hpsiEq
        let c : objOf (.pull hb f) ⟶ objOf hb := homOf (.pullMap hb f)
        have hc : IsHomLift (completion J X).p f c :=
          homOf_isHomLift (.pullMap hb f)
        letI := hc
        letI : IsHomLift Y.p f (K.map c) :=
          BasedFunctor.preserves_isHomLift K f c
        letI : IsStronglyCartesian Y.p f (K.map c) :=
          IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
        letI := hphi
        letI := hphi'
        apply heq_of_eq
        apply IsStronglyCartesian.ext Y.p f (K.map c) (𝟙 S)
        simpa [c, homOf_pullMap_irrel hb hb' f] using fac.symm.trans fac'
  · intro S R Dobj Dmap idRel compRel hglue psi hpsi ePsi phi hphi fac E hE
      ihPsi E' e' ht
    cases hE
    cases e' with
    | incl => simp_all
    | pull => simp_all
    | glue R' Dobj' Dmap' idRel' compRel' hglue' psi' hpsi' ePsi' phi' hphi'
        fac' E' hE' =>
        cases hE'
        simp only [Pre.objGlue.injEq] at ht
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
        apply heq_of_eq
        let a : (completion J X).obj := objOf hglue
        let c (q : R.1.arrows.category) :
            objOf (IsObj.children hglue q) ⟶ a :=
          homOf (.glueMap R Dobj Dmap idRel compRel hglue q)
        apply Functor.IsStack.hom_ext_of_cover R.2
          (show Y.p.obj (H.obj a) = S from (H.w_obj a).trans rfl)
          (show Y.p.obj (K.obj a) = S from (K.w_obj a).trans rfl)
          hphi hphi'
        intro T q hq x xi hxi
        let q' : R.1.arrows.category := R.1.arrows.categoryMk q hq
        have hc : IsHomLift (completion J X).p q (c q') :=
          homOf_isHomLift (.glueMap R Dobj Dmap idRel compRel hglue q')
        letI := hc
        letI : IsHomLift Y.p q (H.map (c q')) :=
          BasedFunctor.preserves_isHomLift H q (c q')
        letI : IsStronglyCartesian Y.p q (H.map (c q')) :=
          IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p q _
        letI := hxi
        let kappa : x ⟶ H.obj (objOf (IsObj.children hglue q')) :=
          IsStronglyCartesian.map Y.p q (H.map (c q'))
            (Category.id_comp q).symm xi
        have hkappa : kappa ≫ H.map (c q') = xi :=
          IsStronglyCartesian.fac Y.p q (H.map (c q'))
            (Category.id_comp q).symm xi
        have hlocal : psi q' = psi' q' :=
          eq_of_heq (ihPsi q' (ePsi' q') rfl)
        have hfac' : H.map (c q') ≫ phi' = psi' q' ≫ K.map (c q') := by
          simpa [c, homOf_glueMap_irrel R Dobj Dmap idRel compRel
            hglue hglue' q'] using fac' q'
        calc
          xi ≫ phi = kappa ≫ (H.map (c q') ≫ phi) := by
            rw [← Category.assoc, hkappa]
          _ = kappa ≫ psi q' ≫ K.map (c q') := by rw [fac q']
          _ = kappa ≫ psi' q' ≫ K.map (c q') := by rw [hlocal]
          _ = kappa ≫ (H.map (c q') ≫ phi') := by rw [hfac']
          _ = xi ≫ phi' := by rw [← Category.assoc, hkappa]

/-- A recursively constructed component at a typed formal object. -/
structure ObjResult {t : Pre J X} {S : C} (h : IsObj J X t S) where
  value : H.obj (objOf h) ⟶ K.obj (objOf h)
  isLift : IsHomLift Y.p (𝟙 S) value
  step : ComponentStep H K alpha (ComponentEvaluation.of H K h value isLift)

/-- Naturality data recursively constructed along a typed formal arrow. -/
structure HomResult {term a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X term a b f) where
  source : ObjResult H K alpha h.sourceObj
  target : ObjResult H K alpha h.targetObj
  naturality : H.map (homOf h) ≫ target.value =
    source.value ≫ K.map (homOf h)

/-- Construct the component at a formal pullback. -/
noncomputable def pullResult {S T : C} {b : Pre J X} (hb : IsObj J X b T)
    (f : S ⟶ T) (B : ObjResult H K alpha hb) :
    ObjResult H K alpha (.pull hb f) := by
  let c : objOf (.pull hb f) ⟶ objOf hb := homOf (.pullMap hb f)
  have hc : IsHomLift (completion J X).p f c := homOf_isHomLift (.pullMap hb f)
  letI := hc
  letI : IsHomLift Y.p f (H.map c) := BasedFunctor.preserves_isHomLift H f c
  letI : IsHomLift Y.p f (K.map c) := BasedFunctor.preserves_isHomLift K f c
  letI : IsStronglyCartesian Y.p f (K.map c) :=
    IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
  letI := B.isLift
  have hcomp : IsHomLift Y.p f (H.map c ≫ B.value) :=
    IsHomLift.comp_lift_id_right' Y.p f (H.map c) T B.value
  letI := hcomp
  let phi := IsStronglyCartesian.map Y.p f (K.map c)
    (Category.id_comp f).symm (H.map c ≫ B.value)
  have hphi : IsHomLift Y.p (𝟙 S) phi :=
    IsStronglyCartesian.map_isHomLift Y.p f (K.map c)
      (Category.id_comp f).symm (H.map c ≫ B.value)
  have hfac : H.map c ≫ B.value = phi ≫ K.map c :=
    (IsStronglyCartesian.fac Y.p f (K.map c) (Category.id_comp f).symm
      (H.map c ≫ B.value)).symm
  exact
    { value := phi
      isLift := hphi
      step := .pull hb f B.value B.isLift B.step phi hphi hfac _ rfl }

/-- The defining cartesian-factorization equation of `pullResult`. -/
lemma pullResult_fac {S T : C} {b : Pre J X} (hb : IsObj J X b T)
    (f : S ⟶ T) (B : ObjResult H K alpha hb) :
    H.map (homOf (.pullMap hb f)) ≫ B.value =
      (pullResult H K alpha hb f B).value ≫ K.map (homOf (.pullMap hb f)) := by
  let c : objOf (.pull hb f) ⟶ objOf hb := homOf (.pullMap hb f)
  letI : IsHomLift (completion J X).p f c := homOf_isHomLift (.pullMap hb f)
  letI : IsHomLift Y.p f (K.map c) :=
    BasedFunctor.preserves_isHomLift K f c
  letI : IsStronglyCartesian Y.p f (K.map c) :=
    IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
  letI := B.isLift
  letI : IsHomLift Y.p f (H.map c) :=
    BasedFunctor.preserves_isHomLift H f c
  letI : IsHomLift Y.p f (H.map c ≫ B.value) :=
    IsHomLift.comp_lift_id_right' Y.p f (H.map c) T B.value
  dsimp [pullResult]
  exact (IsStronglyCartesian.fac Y.p f
    (K.map (homOf (.pullMap hb f))) (Category.id_comp f).symm
      (H.map (homOf (.pullMap hb f)) ≫ B.value)).symm

/-- Local components and their cocone equations at a formal glued object. -/
structure GlueView {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (global : H.obj (objOf hglue) ⟶ K.obj (objOf hglue)) where
  value : ∀ q, H.obj (objOf (IsObj.children hglue q)) ⟶
    K.obj (objOf (IsObj.children hglue q))
  isLift : ∀ q, IsHomLift Y.p (𝟙 q.obj.left) (value q)
  step : ∀ q, ComponentStep H K alpha
    (ComponentEvaluation.of H K (IsObj.children hglue q) (value q) (isLift q))
  fac : ∀ q,
    H.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q)) ≫ global =
      value q ≫ K.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q))

/-- Recover the gluing view stored in an opaque component step. -/
noncomputable def ObjResult.glueView {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (A : ObjResult H K alpha hglue) :
    GlueView H K alpha R Dobj Dmap idRel compRel hglue A.value := by
  cases A.step with
  | incl a E hE =>
      have ht := congrArg (fun E : ComponentEvaluation H K ↦ E.obj.term) hE
      simp_all
  | pull hb f psi hpsi ePsi phi hphi fac E hE =>
      have ht := congrArg (fun E : ComponentEvaluation H K ↦ E.obj.term) hE
      simp_all
  | glue R' Dobj' Dmap' idRel' compRel' hglue' psi hpsi ePsi phi hphi fac E hE =>
      have ht := congrArg (fun E : ComponentEvaluation H K ↦ E.obj.term) hE
      simp only [Pre.objGlue.injEq] at ht
      rcases ht with ⟨hS, hR, hDobjTerm, hDmapTerm, hIdRel, hCompRel⟩
      cases hS
      cases hR
      cases hDobjTerm
      have hDmapEq : @Dmap = @Dmap' := by
        funext x y k
        exact congrFun (congrFun (congrFun (eq_of_heq hDmapTerm) x) y) k
      cases hDmapEq
      cases hIdRel
      have hCompRelEq : @compRel = @compRel' := by
        funext x y z k l
        exact congrFun (congrFun (congrFun (congrFun (congrFun
          (eq_of_heq hCompRel) x) y) z) k) l
      cases hCompRelEq
      have hvalue : A.value = phi :=
        eq_of_heq (ComponentEvaluation.value_heq (H := H) (K := K) hE)
      cases hvalue
      exact
        { value := psi
          isLift := hpsi
          step := ePsi
          fac := fun q ↦ by
            simpa [homOf_glueMap_irrel R Dobj Dmap idRel compRel
              hglue hglue' q] using fac q }

/-- The local component retained by a result at a formal glued object. -/
noncomputable def ObjResult.glueLocal {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (A : ObjResult H K alpha hglue) (q : R.1.arrows.category) :
    H.obj (objOf (IsObj.children hglue q)) ⟶
      K.obj (objOf (IsObj.children hglue q)) :=
  (ObjResult.glueView H K alpha R Dobj Dmap idRel compRel hglue A).value q

/-- The complete local result retained by a result at a formal glued object. -/
noncomputable def ObjResult.glueResult {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (A : ObjResult H K alpha hglue) (q : R.1.arrows.category) :
    ObjResult H K alpha (IsObj.children hglue q) :=
  let V := ObjResult.glueView H K alpha R Dobj Dmap idRel compRel hglue A
  { value := V.value q
    isLift := V.isLift q
    step := V.step q }

/-- The cocone equation retained by a result at a formal glued object. -/
lemma ObjResult.glueFac {S : C} (R : J.Cover S)
    (Dobj : R.1.arrows.category → Pre J X)
    (Dmap : ∀ {q r : R.1.arrows.category}, (q ⟶ r) → Pre J X)
    (idRel : ∀ q, Pre J X)
    (compRel : ∀ {q r s} (k : q ⟶ r) (l : r ⟶ s), Pre J X)
    (hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S)
    (A : ObjResult H K alpha hglue) (q : R.1.arrows.category) :
    H.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q)) ≫ A.value =
      ObjResult.glueLocal H K alpha R Dobj Dmap idRel compRel hglue A q ≫
        K.map (homOf (.glueMap R Dobj Dmap idRel compRel hglue q)) := by
  exact (ObjResult.glueView H K alpha R Dobj Dmap idRel compRel hglue A).fac q

/-- Two recursively constructed results at the same raw object term have the same
component. -/
lemma ObjResult.value_eq {t : Pre J X} {S : C} {h h' : IsObj J X t S}
    (A : ObjResult H K alpha h) (B : ObjResult H K alpha h') :
    A.value = B.value :=
  eq_of_heq (ComponentStep.value_unique H K alpha A.step B.step rfl)

/-- The result at an object from the original based category. -/
def inclResult (a : X.obj) : ObjResult H K alpha (.incl a) :=
  let hα := alpha.isHomLift rfl
  { value := alpha.app a
    isLift := hα
    step := .incl a _ rfl }

set_option maxHeartbeats 1000000 in
-- Elaborating the simultaneous object/arrow recursor traverses every constructor
-- of the free completion and exceeds the default heartbeat limit.
/-- Construct components on all formal objects and prove their naturality along all
formal arrows, simultaneously. -/
noncomputable def result {t : Pre J X} {S : C} (h : IsObj J X t S) :
    ObjResult H K alpha h := by
  refine (IsObj.rec (C := C) (J := J) (X := X)
    (motive_1 := fun _ _ h ↦ ObjResult H K alpha h)
    (motive_2 := fun _ _ _ _ _ _ h ↦ HomResult H K alpha h)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ ↦ PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h)
  · intro a
    exact inclResult H K alpha a
  · intro S T b hb f ihB
    exact pullResult H K alpha hb f ihB
  · intro S R Dobj Dmap hDobj hDmap idRel compRel hId hComp
      ihObj ihMap ihId ihComp
    let hglue : IsObj J X (.objGlue R Dobj Dmap idRel compRel) S :=
      .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp
    let A : (completion J X).obj := objOf hglue
    let c (q : R.1.arrows.category) : objOf (hDobj q) ⟶ A :=
      homOf (.glueMap R Dobj Dmap idRel compRel hglue q)
    let D : R.1.arrows.category ⥤ Y.obj :=
      { obj := fun q ↦ H.obj (objOf (hDobj q))
        map := fun {_ _} k ↦ H.map (homOf (hDmap k))
        map_id := fun q ↦ by
          rw [← H.toFunctor.map_id]
          exact congrArg H.map (homOf_rel (hId q))
        map_comp := fun k l ↦ by
          rw [← H.toFunctor.map_comp]
          exact congrArg H.map (homOf_rel (hComp k l)).symm }
    have etaNatural {q r : R.1.arrows.category} (k : q ⟶ r) :
        D.map k ≫ H.map (c r) = H.map (c q) := by
      rw [← H.toFunctor.map_comp]
      exact congrArg H.map (homOf_rel
        (.glueMapNatural R Dobj Dmap idRel compRel hglue k))
    have hs {q r : R.1.arrows.category} (k : q ⟶ r) :
        (ihMap k).source.value = (ihObj q).value :=
      ObjResult.value_eq H K alpha (ihMap k).source (ihObj q)
    have ht {q r : R.1.arrows.category} (k : q ⟶ r) :
        (ihMap k).target.value = (ihObj r).value :=
      ObjResult.value_eq H K alpha (ihMap k).target (ihObj r)
    have thetaNatural {q r : R.1.arrows.category} (k : q ⟶ r) :
        D.map k ≫ (ihObj r).value ≫ K.map (c r) =
          (ihObj q).value ≫ K.map (c q) := by
      rw [← Category.assoc, ← ht k, (ihMap k).naturality, hs k]
      rw [Category.assoc, ← K.toFunctor.map_comp]
      have hcNat : homOf (hDmap k) ≫ c r = c q :=
        homOf_rel (.glueMapNatural R Dobj Dmap idRel compRel hglue k)
      rw [hcNat]
    let eta (q : R.1.arrows.category) := H.map (c q)
    let theta (q : R.1.arrows.category) := (ihObj q).value ≫ K.map (c q)
    have etaLift (q : R.1.arrows.category) : IsHomLift Y.p q.obj.hom (eta q) := by
      letI : IsHomLift (completion J X).p q.obj.hom (c q) :=
        homOf_isHomLift (.glueMap R Dobj Dmap idRel compRel hglue q)
      exact BasedFunctor.preserves_isHomLift H q.obj.hom (c q)
    have mapLift {q r : R.1.arrows.category} (k : q ⟶ r) :
        IsHomLift Y.p k.hom.left (D.map k) := by
      letI : IsHomLift (completion J X).p k.hom.left (homOf (hDmap k)) :=
        homOf_isHomLift (hDmap k)
      exact BasedFunctor.preserves_isHomLift H k.hom.left (homOf (hDmap k))
    have thetaLift (q : R.1.arrows.category) : IsHomLift Y.p q.obj.hom (theta q) := by
      letI := (ihObj q).isLift
      letI : IsHomLift (completion J X).p q.obj.hom (c q) :=
        homOf_isHomLift (.glueMap R Dobj Dmap idRel compRel hglue q)
      letI : IsHomLift Y.p q.obj.hom (K.map (c q)) :=
        BasedFunctor.preserves_isHomLift K q.obj.hom (c q)
      exact IsHomLift.comp_lift_id_left' Y.p q.obj.left (ihObj q).value
        q.obj.hom (K.map (c q))
    let ex := Functor.IsStack.existsUnique_gluing_hom_of_cocone
      (p := Y.p) R.2 D
      (show Y.p.obj (H.obj A) = S from (H.w_obj A).trans rfl)
      (show Y.p.obj (K.obj A) = S from (K.w_obj A).trans rfl)
      eta etaLift (fun {_ _} k ↦ mapLift k) (fun {_ _} k ↦ etaNatural k)
      theta thetaLift (fun {_ _} k ↦ thetaNatural k)
    let phi := ex.choose
    have hphi := ex.choose_spec.1.1
    have hfac (q : R.1.arrows.category) : H.map (c q) ≫ phi =
        (ihObj q).value ≫ K.map (c q) :=
      (ex.choose_spec.1.2 q.property).symm
    exact
      { value := phi
        isLift := hphi
        step := .glue R Dobj Dmap idRel compRel hglue
          (fun q ↦ (ihObj q).value) (fun q ↦ (ihObj q).isLift)
          (fun q ↦ (ihObj q).step) phi hphi hfac _ rfl }
  · intro a b f
    let A := inclResult H K alpha a
    let B := inclResult H K alpha b
    exact ⟨A, B, alpha.naturality f⟩
  · intro S a ha ihA
    refine ⟨ihA, ihA, ?_⟩
    rw [homOf_id, H.toFunctor.map_id, K.toFunctor.map_id,
      Category.id_comp, Category.comp_id]
  · intro R S T a b c phi psi p q hphi hpsi ihPhi ihPsi
    refine ⟨ihPhi.source, ihPsi.target, ?_⟩
    have hmid := ObjResult.value_eq H K alpha ihPhi.target ihPsi.source
    rw [homOf_comp, H.toFunctor.map_comp, K.toFunctor.map_comp,
      Category.assoc, ihPsi.naturality, ← hmid, ← Category.assoc,
      ihPhi.naturality, Category.assoc]
  · intro S T b hb f ihB
    let P := pullResult H K alpha hb f ihB
    exact ⟨P, ihB, pullResult_fac H K alpha hb f ihB⟩
  · intro R S T a b c cart phi p f g hcart hphi hp ihCart ihPhi
    let factorHom := homOf (.factor f g hcart hphi hp)
    let cartHom := homOf hcart
    let phiHom := homOf hphi
    let gamma := ihPhi.source
    let delta := ihCart.source
    let mid := ihCart.target
    have hmid : ihCart.target.value = ihPhi.target.value :=
      ObjResult.value_eq H K alpha ihCart.target ihPhi.target
    have hCart := ihCart.naturality
    have hPhi : H.map phiHom ≫ mid.value = gamma.value ≫ K.map phiHom := by
      rw [hmid]
      exact ihPhi.naturality
    letI : IsHomLift (completion J X).p f cartHom := homOf_isHomLift hcart
    letI : IsHomLift Y.p f (K.map cartHom) :=
      BasedFunctor.preserves_isHomLift K f cartHom
    letI : IsStronglyCartesian Y.p f (K.map cartHom) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
    letI : IsHomLift (completion J X).p g factorHom :=
      homOf_isHomLift (.factor f g hcart hphi hp)
    letI : IsHomLift Y.p g (H.map factorHom) :=
      BasedFunctor.preserves_isHomLift H g factorHom
    letI : IsHomLift Y.p g (K.map factorHom) :=
      BasedFunctor.preserves_isHomLift K g factorHom
    letI := gamma.isLift
    letI := delta.isLift
    letI : IsHomLift Y.p g (H.map factorHom ≫ delta.value) :=
      IsHomLift.comp_lift_id_right' Y.p g (H.map factorHom) S delta.value
    letI : IsHomLift Y.p g (gamma.value ≫ K.map factorHom) :=
      IsHomLift.comp_lift_id_left' Y.p R gamma.value g (K.map factorHom)
    have hHfac : H.map factorHom ≫ H.map cartHom = H.map phiHom := by
      rw [← H.toFunctor.map_comp]
      exact congrArg H.map (homOf_rel (.factorFac f g hcart hphi hp))
    have hKfac : K.map factorHom ≫ K.map cartHom = K.map phiHom := by
      rw [← K.toFunctor.map_comp]
      exact congrArg K.map (homOf_rel (.factorFac f g hcart hphi hp))
    refine ⟨gamma, delta, ?_⟩
    apply IsStronglyCartesian.ext Y.p f (K.map cartHom) g
    calc
      (H.map factorHom ≫ delta.value) ≫ K.map cartHom =
          H.map factorHom ≫ (delta.value ≫ K.map cartHom) := Category.assoc _ _ _
      _ = H.map factorHom ≫ (H.map cartHom ≫ mid.value) := by rw [hCart]
      _ = (H.map factorHom ≫ H.map cartHom) ≫ mid.value := by simp
      _ = H.map phiHom ≫ mid.value := by rw [hHfac]
      _ = gamma.value ≫ K.map phiHom := hPhi
      _ = gamma.value ≫ (K.map factorHom ≫ K.map cartHom) := by rw [hKfac]
      _ = (gamma.value ≫ K.map factorHom) ≫ K.map cartHom := by simp
  · intro S R Dobj Dmap idRel compRel hglue q ihGlue
    let L := ObjResult.glueResult H K alpha R Dobj Dmap idRel compRel hglue ihGlue q
    exact ⟨L, ihGlue, ObjResult.glueFac H K alpha R Dobj Dmap idRel compRel
      hglue ihGlue q⟩
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat
      ihA ihB ihDobj ihDmap ihId ihComp ihEta ihTheta ihEtaNat ihThetaNat
    let hglueHom : IsHom J X
        (.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat)
        a b (𝟙 S) :=
      .homGlue R Dobj Dmap etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
        hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat
    let g : objOf ha ⟶ objOf hb := homOf hglueHom
    refine ⟨ihA, ihB, ?_⟩
    change H.map g ≫ ihB.value = ihA.value ≫ K.map g
    letI : IsHomLift (completion J X).p (𝟙 S) g := homOf_isHomLift hglueHom
    letI : IsHomLift Y.p (𝟙 S) (H.map g) :=
      BasedFunctor.preserves_isHomLift H (𝟙 S) g
    letI : IsHomLift Y.p (𝟙 S) (K.map g) :=
      BasedFunctor.preserves_isHomLift K (𝟙 S) g
    letI := ihA.isLift
    letI := ihB.isLift
    have hleft : IsHomLift Y.p (𝟙 S) (H.map g ≫ ihB.value) :=
      IsHomLift.comp_lift_id_right' Y.p (𝟙 S) (H.map g) S ihB.value
    have hright : IsHomLift Y.p (𝟙 S) (ihA.value ≫ K.map g) :=
      IsHomLift.comp_lift_id_left' Y.p S ihA.value (𝟙 S) (K.map g)
    apply Functor.IsStack.hom_ext_of_cover R.2
      (show Y.p.obj (H.obj (objOf ha)) = S from (H.w_obj (objOf ha)).trans rfl)
      (show Y.p.obj (K.obj (objOf hb)) = S from (K.w_obj (objOf hb)).trans rfl)
      hleft hright
    intro T q hq x xi hxi
    let q' : R.1.arrows.category := R.1.arrows.categoryMk q hq
    let e : objOf (hDobj q') ⟶ objOf ha := homOf (heta q')
    let th : objOf (hDobj q') ⟶ objOf hb := homOf (htheta q')
    have he : IsHomLift (completion J X).p q e := homOf_isHomLift (heta q')
    letI := he
    letI : IsHomLift Y.p q (H.map e) :=
      BasedFunctor.preserves_isHomLift H q e
    letI : IsStronglyCartesian Y.p q (H.map e) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p q _
    letI := hxi
    let kappa : x ⟶ H.obj (objOf (hDobj q')) :=
      IsStronglyCartesian.map Y.p q (H.map e) (Category.id_comp q).symm xi
    have hkappa : kappa ≫ H.map e = xi :=
      IsStronglyCartesian.fac Y.p q (H.map e) (Category.id_comp q).symm xi
    have hEtaSource : (ihEta q').source.value = (ihDobj q').value :=
      ObjResult.value_eq H K alpha (ihEta q').source (ihDobj q')
    have hEtaTarget : (ihEta q').target.value = ihA.value :=
      ObjResult.value_eq H K alpha (ihEta q').target ihA
    have hThetaSource : (ihTheta q').source.value = (ihDobj q').value :=
      ObjResult.value_eq H K alpha (ihTheta q').source (ihDobj q')
    have hThetaTarget : (ihTheta q').target.value = ihB.value :=
      ObjResult.value_eq H K alpha (ihTheta q').target ihB
    have hEta : H.map e ≫ ihA.value =
        (ihDobj q').value ≫ K.map e := by
      simpa [e, hEtaSource, hEtaTarget] using (ihEta q').naturality
    have hTheta : H.map th ≫ ihB.value =
        (ihDobj q').value ≫ K.map th := by
      simpa [th, hThetaSource, hThetaTarget] using (ihTheta q').naturality
    have hfac : homOf (htheta q') = homOf (heta q') ≫ g := by
      exact homOf_rel
        (.homGlueFac R Dobj Dmap idRel compRel etaTerm thetaTerm etaNat thetaNat
          hglueHom heta htheta q')
    have hHfac : H.map th = H.map e ≫ H.map g := by
      rw [← H.toFunctor.map_comp]
      exact congrArg H.map hfac
    have hKfac : K.map th = K.map e ≫ K.map g := by
      rw [← K.toFunctor.map_comp]
      exact congrArg K.map hfac
    calc
      xi ≫ (H.map g ≫ ihB.value) =
          kappa ≫ (H.map e ≫ (H.map g ≫ ihB.value)) := by
        rw [← hkappa]
        simp only [Category.assoc]
      _ = kappa ≫ (H.map th ≫ ihB.value) := by
        rw [hHfac]
        simp only [Category.assoc]
      _ = kappa ≫ ((ihDobj q').value ≫ K.map th) := by rw [hTheta]
      _ = kappa ≫ ((ihDobj q').value ≫ (K.map e ≫ K.map g)) := by
        rw [hKfac]
      _ = kappa ≫ (((ihDobj q').value ≫ K.map e) ≫ K.map g) := by
        simp only [Category.assoc]
      _ = kappa ≫ ((H.map e ≫ ihA.value) ≫ K.map g) := by rw [hEta]
      _ = kappa ≫ (H.map e ≫ (ihA.value ≫ K.map g)) := by
        simp only [Category.assoc]
      _ = xi ≫ (ihA.value ≫ K.map g) := by
        rw [← hkappa]
        simp only [Category.assoc]
  all_goals intros <;> exact PUnit.unit

set_option maxHeartbeats 1000000 in
-- This induction normalizes the large simultaneous evaluator at every arrow
-- constructor and exceeds the default heartbeat limit.
/-- The recursively constructed components are natural along every formal arrow. -/
theorem result_naturality {term a b : Pre J X} {S T : C} {f : S ⟶ T}
    (h : IsHom J X term a b f) :
    H.map (homOf h) ≫ (result H K alpha h.targetObj).value =
      (result H K alpha h.sourceObj).value ≫ K.map (homOf h) := by
  refine (IsHom.rec (C := C) (J := J) (X := X)
    (motive_1 := fun _ _ _ ↦ PUnit)
    (motive_2 := fun _ _ _ _ _ _ h ↦
      H.map (homOf h) ≫ (result H K alpha h.targetObj).value =
        (result H K alpha h.sourceObj).value ≫ K.map (homOf h))
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ ↦ PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h)
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intros
    exact PUnit.unit
  · intro a b f
    have hs := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.incl f).sourceObj) (inclResult H K alpha a)
    have ht := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.incl f).targetObj) (inclResult H K alpha b)
    rw [hs, ht]
    exact alpha.naturality f
  · intro S a ha ihA
    rw [homOf_id, H.toFunctor.map_id, K.toFunctor.map_id,
      Category.id_comp, Category.comp_id]
    exact ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.id ha).targetObj)
      (result H K alpha (IsHom.id ha).sourceObj)
  · intro R S T a b c phi psi p q hphi hpsi ihPhi ihPsi
    have hsource := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.comp hphi hpsi).sourceObj)
      (result H K alpha hphi.sourceObj)
    have htarget := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.comp hphi hpsi).targetObj)
      (result H K alpha hpsi.targetObj)
    have hmid := ObjResult.value_eq H K alpha
      (result H K alpha hphi.targetObj) (result H K alpha hpsi.sourceObj)
    rw [homOf_comp, H.toFunctor.map_comp, K.toFunctor.map_comp, hsource, htarget,
      Category.assoc, ihPsi, ← hmid, ← Category.assoc, ihPhi,
      Category.assoc]
  · intro S T b hb f ihB
    let B := result H K alpha hb
    let P := pullResult H K alpha hb f B
    have hs := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.pullMap hb f).sourceObj) P
    have ht := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.pullMap hb f).targetObj) B
    rw [hs, ht]
    exact pullResult_fac H K alpha hb f B
  · intro R S T a b c cart phi p f g hcart hphi hp ihCart ihPhi
    let factorHom := homOf (.factor f g hcart hphi hp)
    let cartHom := homOf hcart
    let phiHom := homOf hphi
    let gamma := result H K alpha hphi.sourceObj
    let delta := result H K alpha hcart.sourceObj
    let mid := result H K alpha hcart.targetObj
    have hsource := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.factor f g hcart hphi hp).sourceObj) gamma
    have htarget := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.factor f g hcart hphi hp).targetObj) delta
    have hmid : mid.value = (result H K alpha hphi.targetObj).value :=
      ObjResult.value_eq H K alpha mid (result H K alpha hphi.targetObj)
    have hPhi : H.map phiHom ≫ mid.value = gamma.value ≫ K.map phiHom := by
      rw [hmid]
      exact ihPhi
    letI : IsHomLift (completion J X).p f cartHom := homOf_isHomLift hcart
    letI : IsHomLift Y.p f (K.map cartHom) :=
      BasedFunctor.preserves_isHomLift K f cartHom
    letI : IsStronglyCartesian Y.p f (K.map cartHom) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
    letI : IsHomLift (completion J X).p g factorHom :=
      homOf_isHomLift (.factor f g hcart hphi hp)
    letI : IsHomLift Y.p g (H.map factorHom) :=
      BasedFunctor.preserves_isHomLift H g factorHom
    letI : IsHomLift Y.p g (K.map factorHom) :=
      BasedFunctor.preserves_isHomLift K g factorHom
    letI := gamma.isLift
    letI := delta.isLift
    letI : IsHomLift Y.p g (H.map factorHom ≫ delta.value) :=
      IsHomLift.comp_lift_id_right' Y.p g (H.map factorHom) S delta.value
    letI : IsHomLift Y.p g (gamma.value ≫ K.map factorHom) :=
      IsHomLift.comp_lift_id_left' Y.p R gamma.value g (K.map factorHom)
    have hHfac : H.map factorHom ≫ H.map cartHom = H.map phiHom := by
      rw [← H.toFunctor.map_comp]
      exact congrArg H.map (homOf_rel (.factorFac f g hcart hphi hp))
    have hKfac : K.map factorHom ≫ K.map cartHom = K.map phiHom := by
      rw [← K.toFunctor.map_comp]
      exact congrArg K.map (homOf_rel (.factorFac f g hcart hphi hp))
    rw [hsource, htarget]
    apply IsStronglyCartesian.ext Y.p f (K.map cartHom) g
    calc
      (H.map factorHom ≫ delta.value) ≫ K.map cartHom =
          H.map factorHom ≫ (delta.value ≫ K.map cartHom) := Category.assoc _ _ _
      _ = H.map factorHom ≫ (H.map cartHom ≫ mid.value) := by rw [ihCart]
      _ = (H.map factorHom ≫ H.map cartHom) ≫ mid.value := by simp
      _ = H.map phiHom ≫ mid.value := by rw [hHfac]
      _ = gamma.value ≫ K.map phiHom := hPhi
      _ = gamma.value ≫ (K.map factorHom ≫ K.map cartHom) := by rw [hKfac]
      _ = (gamma.value ≫ K.map factorHom) ≫ K.map cartHom := by simp
  · intro S R Dobj Dmap idRel compRel hglue q ihGlue
    let G := result H K alpha hglue
    let L := ObjResult.glueResult H K alpha R Dobj Dmap idRel compRel hglue G q
    have hs := ObjResult.value_eq H K alpha
      (result H K alpha
        (IsHom.glueMap R Dobj Dmap idRel compRel hglue q).sourceObj) L
    have ht := ObjResult.value_eq H K alpha
      (result H K alpha (IsHom.glueMap R Dobj Dmap idRel compRel hglue q).targetObj) G
    rw [hs, ht]
    exact ObjResult.glueFac H K alpha R Dobj Dmap idRel compRel hglue G q
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat
      ihA ihB ihDobj ihDmap ihId ihComp ihEta ihTheta ihEtaNat ihThetaNat
    let hglueHom : IsHom J X
        (.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat)
        a b (𝟙 S) :=
      .homGlue R Dobj Dmap etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
        hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat
    let g : objOf ha ⟶ objOf hb := homOf hglueHom
    let A := result H K alpha ha
    let B := result H K alpha hb
    change H.map g ≫ B.value = A.value ≫ K.map g
    letI : IsHomLift (completion J X).p (𝟙 S) g := homOf_isHomLift hglueHom
    letI : IsHomLift Y.p (𝟙 S) (H.map g) :=
      BasedFunctor.preserves_isHomLift H (𝟙 S) g
    letI : IsHomLift Y.p (𝟙 S) (K.map g) :=
      BasedFunctor.preserves_isHomLift K (𝟙 S) g
    letI := A.isLift
    letI := B.isLift
    have hleft : IsHomLift Y.p (𝟙 S) (H.map g ≫ B.value) :=
      IsHomLift.comp_lift_id_right' Y.p (𝟙 S) (H.map g) S B.value
    have hright : IsHomLift Y.p (𝟙 S) (A.value ≫ K.map g) :=
      IsHomLift.comp_lift_id_left' Y.p S A.value (𝟙 S) (K.map g)
    apply Functor.IsStack.hom_ext_of_cover R.2
      (show Y.p.obj (H.obj (objOf ha)) = S from (H.w_obj (objOf ha)).trans rfl)
      (show Y.p.obj (K.obj (objOf hb)) = S from (K.w_obj (objOf hb)).trans rfl)
      hleft hright
    intro T q hq x xi hxi
    let q' : R.1.arrows.category := R.1.arrows.categoryMk q hq
    let e : objOf (hDobj q') ⟶ objOf ha := homOf (heta q')
    let th : objOf (hDobj q') ⟶ objOf hb := homOf (htheta q')
    let D := result H K alpha (hDobj q')
    have he : IsHomLift (completion J X).p q e := homOf_isHomLift (heta q')
    letI := he
    letI : IsHomLift Y.p q (H.map e) :=
      BasedFunctor.preserves_isHomLift H q e
    letI : IsStronglyCartesian Y.p q (H.map e) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p q _
    letI := hxi
    let kappa : x ⟶ H.obj (objOf (hDobj q')) :=
      IsStronglyCartesian.map Y.p q (H.map e) (Category.id_comp q).symm xi
    have hkappa : kappa ≫ H.map e = xi :=
      IsStronglyCartesian.fac Y.p q (H.map e) (Category.id_comp q).symm xi
    have hEtaSource := ObjResult.value_eq H K alpha
      (result H K alpha (heta q').sourceObj) D
    have hEtaTarget := ObjResult.value_eq H K alpha
      (result H K alpha (heta q').targetObj) A
    have hThetaSource := ObjResult.value_eq H K alpha
      (result H K alpha (htheta q').sourceObj) D
    have hThetaTarget := ObjResult.value_eq H K alpha
      (result H K alpha (htheta q').targetObj) B
    have hEta : H.map e ≫ A.value = D.value ≫ K.map e := by
      rw [← hEtaTarget, ihEta q', hEtaSource]
    have hTheta : H.map th ≫ B.value = D.value ≫ K.map th := by
      rw [← hThetaTarget, ihTheta q', hThetaSource]
    have hfac : homOf (htheta q') = homOf (heta q') ≫ g := by
      exact homOf_rel
        (.homGlueFac R Dobj Dmap idRel compRel etaTerm thetaTerm etaNat thetaNat
          hglueHom heta htheta q')
    have hHfac : H.map th = H.map e ≫ H.map g := by
      rw [← H.toFunctor.map_comp]
      exact congrArg H.map hfac
    have hKfac : K.map th = K.map e ≫ K.map g := by
      rw [← K.toFunctor.map_comp]
      exact congrArg K.map hfac
    calc
      xi ≫ (H.map g ≫ B.value) =
          kappa ≫ (H.map e ≫ (H.map g ≫ B.value)) := by
        rw [← hkappa]
        simp only [Category.assoc]
      _ = kappa ≫ (H.map th ≫ B.value) := by
        rw [hHfac]
        simp only [Category.assoc]
      _ = kappa ≫ (D.value ≫ K.map th) := by rw [hTheta]
      _ = kappa ≫ (D.value ≫ (K.map e ≫ K.map g)) := by rw [hKfac]
      _ = kappa ≫ ((D.value ≫ K.map e) ≫ K.map g) := by
        simp only [Category.assoc]
      _ = kappa ≫ ((H.map e ≫ A.value) ≫ K.map g) := by rw [hEta]
      _ = kappa ≫ (H.map e ≫ (A.value ≫ K.map g)) := by
        simp only [Category.assoc]
      _ = xi ≫ (A.value ≫ K.map g) := by
        rw [← hkappa]
        simp only [Category.assoc]
  all_goals intros <;> exact PUnit.unit

lemma objOf_eq_obj (a : Obj J X) (h : IsObj J X a.term a.base) : objOf h = a := by
  cases a
  rfl

lemma homOf_eq_mk {a b : Obj J X} (phi : RawHom J X a b)
    (h : IsHom J X phi.term a.term b.term phi.base) :
    homOf h = (⟦phi⟧ : a ⟶ b) := by
  rfl

/-- Extend a transformation on the generators to the free completion. -/
noncomputable def extendNatTrans : BasedNatTrans H K where
  toNatTrans :=
    { app := fun a ↦ (result H K alpha (Classical.choice a.valid)).value
      naturality := by
        intro a b f
        induction f using _root_.Quotient.inductionOn with
        | _ phi =>
            let hphi := Classical.choice phi.valid
            have hn := result_naturality H K alpha hphi
            have hs := ObjResult.value_eq H K alpha
              (result H K alpha hphi.sourceObj)
              (result H K alpha (Classical.choice a.valid))
            have ht := ObjResult.value_eq H K alpha
              (result H K alpha hphi.targetObj)
              (result H K alpha (Classical.choice b.valid))
            rw [hs, ht] at hn
            exact hn }
  isHomLift' := fun a ↦ (result H K alpha (Classical.choice a.valid)).isLift

@[simp]
lemma extendNatTrans_inclusion_app (a : X.obj) :
    (extendNatTrans H K alpha).app ((inclusion J X).obj a) = alpha.app a := by
  exact ObjResult.value_eq H K alpha
    (result H K alpha (Classical.choice ((inclusion J X).obj a).valid))
    (inclResult H K alpha a)



theorem component_ext (H K : completion J X ⥤ᵇ Y)
    (α β : BasedNatTrans H K)
    (hincl : ∀ a : X.obj,
      α.app ((inclusion J X).obj a) = β.app ((inclusion J X).obj a))
    {t : Pre J X} {S : C} (h : IsObj J X t S) :
    α.app (objOf h) = β.app (objOf h) := by
  induction h using IsObj.rec
    (motive_2 := fun _ _ _ _ _ _ _ ↦ True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ ↦ True)
  · exact hincl _
  · rename_i S T b hb f ih
    let c : objOf (.pull hb f) ⟶ objOf hb := homOf (.pullMap hb f)
    have hc : IsHomLift (completion J X).p f c := by
      refine IsHomLift.of_fac' (completion J X).p f c rfl rfl ?_
      change f = eqToHom rfl ≫ f ≫ eqToHom rfl
      simp
    letI := hc
    have hcH : IsHomLift Y.p f (H.map c) :=
      BasedFunctor.preserves_isHomLift H f c
    have hcK : IsHomLift Y.p f (K.map c) :=
      BasedFunctor.preserves_isHomLift K f c
    letI := hcK
    letI : IsStronglyCartesian Y.p f (K.map c) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
    letI : IsHomLift Y.p (𝟙 S) (α.app (objOf (.pull hb f))) :=
      α.isHomLift (show (completion J X).p.obj (objOf (.pull hb f)) = S from rfl)
    letI : IsHomLift Y.p (𝟙 S) (β.app (objOf (.pull hb f))) :=
      β.isHomLift (show (completion J X).p.obj (objOf (.pull hb f)) = S from rfl)
    apply IsStronglyCartesian.ext Y.p f (K.map c) (𝟙 S)
    rw [← α.naturality c, ← β.naturality c, ih]
  · rename_i S R Dobj Dmap hDobj hDmap idRel compRel hId hComp ihObj _ _ _
    let a : (completion J X).obj := objOf
      (.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp)
    let c (q : R.1.arrows.category) : objOf (hDobj q) ⟶ a :=
      homOf (.glueMap R Dobj Dmap idRel compRel
        (.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp) q)
    apply Functor.IsStack.hom_ext_of_cover R.2
      (show Y.p.obj (H.obj a) = S from (H.w_obj a).trans rfl)
      (show Y.p.obj (K.obj a) = S from (K.w_obj a).trans rfl)
      (α.isHomLift rfl) (β.isHomLift rfl)
    intro T q hq x ξ hξ
    let q' : R.1.arrows.category := R.1.arrows.categoryMk q hq
    have hc : IsHomLift (completion J X).p q (c q') := by
      refine IsHomLift.of_fac' (completion J X).p q (c q') rfl rfl ?_
      change q = eqToHom rfl ≫ q ≫ eqToHom rfl
      simp
    letI := hc
    have hcH : IsHomLift Y.p q (H.map (c q')) :=
      BasedFunctor.preserves_isHomLift H q (c q')
    letI := hcH
    letI : IsStronglyCartesian Y.p q (H.map (c q')) :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p q _
    letI := hξ
    let κ : x ⟶ H.obj (objOf (hDobj q')) :=
      IsStronglyCartesian.map Y.p q (H.map (c q')) (Category.id_comp q).symm ξ
    have hκfac : κ ≫ H.map (c q') = ξ :=
      IsStronglyCartesian.fac Y.p q (H.map (c q'))
        (Category.id_comp q).symm ξ
    have hα : H.map (c q') ≫ α.app a =
        α.app (objOf (hDobj q')) ≫ K.map (c q') :=
      α.naturality (c q')
    have hβ : H.map (c q') ≫ β.app a =
        β.app (objOf (hDobj q')) ≫ K.map (c q') :=
      β.naturality (c q')
    calc
      ξ ≫ α.app a = κ ≫ (H.map (c q') ≫ α.app a) := by
        rw [← Category.assoc, hκfac]
      _ = κ ≫ (α.app (objOf (hDobj q')) ≫ K.map (c q')) := by
        rw [hα]
      _ = κ ≫ (β.app (objOf (hDobj q')) ≫ K.map (c q')) := by
        rw [ihObj q']
      _ = κ ≫ (H.map (c q') ≫ β.app a) := by
        rw [hβ]
      _ = ξ ≫ β.app a := by rw [← Category.assoc, hκfac]
  all_goals simp


end CategoryTheory.BasedCategory.FreeStackCompletion.UniversalGraph
