module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.3-quotient-stacks-of-groupoids»
public import StacksAndModuli.API.AlgebraicSpaceEtaleLocal
public import StacksAndModuli.API.PresheafFiberProduct
public import StacksAndModuli.API.PresheafPrestackHom
public import StacksAndModuli.API.RepresentedSecondFiberBaseChange
public import StacksAndModuli.API.RepresentableWithCharts
public import StacksAndModuli.API.RepresentableWithEtaleEquivalence
public import StacksAndModuli.API.TwoYonedaCartesianLift
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»

/-!
# Local criteria for quotient-stack presentations

This file isolates two descent bridges used in proving that a quotient-stack map is a
geometric presentation.

First, local essential surjectivity naturally gives lifts over every arrow of a
covering sieve.  A single surjective étale lift follows once lifts over the members of a
chosen covering family glue over the coproduct of that family.  The predicate
`PresheafGroupoid.CoproductLiftsGlue` records exactly this extra, quotient-specific
descent datum; it does not silently replace a covering sieve by one cover.

Second, `BasedFunctor.EtaleLocalFiberRepresentation` packages a small sheaf representing
a fiber of a prestack map together with one surjective étale base change on which that
sheaf is an algebraic space.  The local algebraic-space condition descends to the
original fiber, giving `BasedFunctor.Representable`.  In quotient applications the
represented self-intersection supplies the local algebraic space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}}
  {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
  {i : BasedFunctor 𝒢.quotientPrestack 𝒳st}

/-- Lifts of a target object to a quotient prestack glue across the coproduct of an
étale covering family.

This is the precise additional descent input needed to turn covering-sieve local
essential surjectivity into one surjective étale lift.  It is deliberately weaker than
object descent for arbitrary covers: only the disjoint coproduct of a chosen étale
covering family is involved. -/
def CoproductLiftsGlue : Prop :=
  ∀ (y : 𝒳st.obj)
    (𝒰 : Scheme.Cover (Scheme.precoverage
      (@Etale : MorphismProperty Scheme.{u})) (𝒳st.p.obj y)),
    (∀ j : 𝒰.I₀, ∃ (x : 𝒢.quotientPrestack.obj)
      (q : i.obj x ⟶ y), 𝒳st.p.IsHomLift (𝒰.f j) q) →
      ∃ (x : 𝒢.quotientPrestack.obj) (q : i.obj x ⟶ y),
        𝒳st.p.IsHomLift (Sigma.desc 𝒰.f) q

/-- A locally essentially surjective quotient-prestack map admits one surjective étale
lift of every target object, provided lifts glue over coproducts of étale covering
families. -/
theorem exists_etale_surjective_lift_of_coproductLiftsGlue
    (hlocal : i.IsLocallyEssentiallySurjective
      (J := Scheme.etaleTopology))
    (hglue : CoproductLiftsGlue (𝒢 := 𝒢) (i := i))
    (y : 𝒳st.obj) :
    ∃ (T' : Scheme.{u}) (p : T' ⟶ 𝒳st.p.obj y),
      Etale p ∧ Surjective p ∧
        ∃ (x : 𝒢.quotientPrestack.obj) (q : i.obj x ⟶ y),
          𝒳st.p.IsHomLift p q := by
  obtain ⟨R, hR, hLift⟩ := hlocal y
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  let T' : Scheme.{u} := ∐ 𝒰.X
  let p : T' ⟶ 𝒳st.p.obj y := Sigma.desc 𝒰.f
  have hpEtale : Etale p := by
    apply IsZariskiLocalAtSource.sigmaDesc
    intro j
    exact 𝒰.map_prop j
  have hpSurjective : Surjective p := by
    dsimp only [p]
    infer_instance
  have hFamily : ∀ j : 𝒰.I₀, ∃ (x : 𝒢.quotientPrestack.obj)
      (q : i.obj x ⟶ y), 𝒳st.p.IsHomLift (𝒰.f j) q := by
    intro j
    exact hLift (𝒰.f j) (h𝒰 _ _ ⟨j⟩)
  obtain ⟨x, q, hq⟩ := hglue y 𝒰 hFamily
  exact ⟨T', p, hpEtale, hpSurjective, x, q, hq⟩

variable [𝒳st.p.IsFiberedInGroupoids]

/-- The point of the presheaf `U` underlying an object `(T, x)` of the quotient
prestack, regarded as an object in the fiber of the associated presheaf prestack. -/
noncomputable def quotientPointFiberObj (x : 𝒢.quotientPrestack.obj) :
    (ofPresheaf 𝒢.U).p.Fiber x.base :=
  ⟨CostructuredArrow.mk (yonedaEquiv.symm x.pt), rfl⟩

/-- The scheme-valued point of `U` underlying an object of the quotient prestack. -/
noncomputable def quotientPoint (x : 𝒢.quotientPrestack.obj) :
    BasedFunctor (overBased x.base) (ofPresheaf 𝒢.U) :=
  twoYonedaPullback x.base (quotientPointFiberObj x)

/-- Applying the canonical quotient presentation to the underlying point recovers the
original quotient-prestack object. -/
@[simp]
lemma quotientPresentation_obj_quotientPointFiberObj
    (x : 𝒢.quotientPrestack.obj) :
    𝒢.quotientPresentation.obj (quotientPointFiberObj x).1 = x := by
  change ⟨x.base, yonedaEquiv (yonedaEquiv.symm x.pt)⟩ = x
  cases x
  simp

/-- The base map classified by a quotient lift to the value at the identity of a
scheme-valued point. -/
noncomputable def quotientLiftBaseMap
    {T : Scheme.{u}} (g : BasedFunctor (overBased T) 𝒳st)
    (x : 𝒢.quotientPrestack.obj)
    (q : i.obj x ⟶ ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).1) :
    x.base ⟶ T :=
  eqToHom (i.w_obj x).symm ≫ 𝒳st.p.map q ≫
    eqToHom ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).2

omit [𝒳st.p.IsFiberedInGroupoids] in
/-- The normalized base map of a quotient lift differs from any originally displayed
base map only by the equality identifying the base of the quotient object with the
displayed source. -/
lemma quotientLiftBaseMap_eq_of_isHomLift
    {S T : Scheme.{u}} (p : S ⟶ T)
    (g : BasedFunctor (overBased T) 𝒳st)
    (x : 𝒢.quotientPrestack.obj)
    (q : i.obj x ⟶ ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).1)
    [IsHomLift 𝒳st.p p q] :
    quotientLiftBaseMap g x q =
      eqToHom ((i.w_obj x).symm.trans
        (IsHomLift.domain_eq 𝒳st.p p q)) ≫ p := by
  unfold quotientLiftBaseMap
  rw [IsHomLift.fac' 𝒳st.p p q]
  simp

omit [𝒳st.p.IsFiberedInGroupoids] in
/-- A surjective étale quotient lift remains surjective and étale after normalizing
its base map. -/
lemma quotientLiftBaseMap_surjective_etale
    {S T : Scheme.{u}} (p : S ⟶ T)
    (g : BasedFunctor (overBased T) 𝒳st)
    (x : 𝒢.quotientPrestack.obj)
    (q : i.obj x ⟶ ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).1)
    [IsHomLift 𝒳st.p p q] (hpEtale : Etale p)
    (hpSurjective : Surjective p) :
    Etale (quotientLiftBaseMap g x q) ∧
      Surjective (quotientLiftBaseMap g x q) := by
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  rw [quotientLiftBaseMap_eq_of_isHomLift p g x q]
  constructor <;> infer_instance

/-- A cartesian quotient-prestack lift of a scheme-valued stack point gives the
expected local factorization of that point through the quotient presentation.

The base map is normalized from the displayed arrow `q`, so its source and target are
definitionally the bases of the two represented points.  If `q` was originally given
as a lift of a specified map, `IsHomLift.eq_of_isHomLift` identifies that map with this
normalization. -/
noncomputable def quotientLocalLiftIso
    {T : Scheme.{u}} (g : BasedFunctor (overBased T) 𝒳st)
    (x : 𝒢.quotientPrestack.obj)
    (q : i.obj x ⟶ ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).1) :
    (quotientPoint x).comp (𝒢.quotientPresentation.comp i) ≅
      (overBased.map (quotientLiftBaseMap g x q)).comp g := by
  let ux := quotientPointFiberObj x
  let a := quotientPoint x
  let F := 𝒢.quotientPresentation.comp i
  let y := (twoYonedaEval (𝒳 := 𝒳st) T).obj g
  let f := quotientLiftBaseMap g x q
  let e₀ : 𝒢.quotientPresentation.obj ux.1 ≅ x :=
    eqToIso (quotientPresentation_obj_quotientPointFiberObj x)
  haveI he₀ : IsHomLift 𝒢.quotientProj (𝟙 x.base) e₀.hom := by
    apply IsHomLift.of_fac 𝒢.quotientProj (𝟙 x.base) e₀.hom rfl rfl
    rw [show e₀.hom = eqToHom
      (quotientPresentation_obj_quotientPointFiberObj x) from rfl,
      eqToHom_map]
    simp
  let e : F.obj ux.1 ≅ i.obj x := i.toFunctor.mapIso e₀
  haveI he : IsHomLift 𝒳st.p (𝟙 x.base) e.hom := by
    exact i.preserves_isHomLift (𝟙 x.base) e₀.hom
  haveI hq : IsHomLift 𝒳st.p f q :=
    IsHomLift.of_fac 𝒳st.p f q (i.w_obj x) y.2 rfl
  let πu := IsPreFibered.pullbackMap ux.2 (𝟙 x.base)
  haveI hπu : IsHomLift (ofPresheaf 𝒢.U).p (𝟙 x.base) πu := inferInstance
  haveI hFπu : IsHomLift 𝒳st.p (𝟙 x.base) (F.map πu) :=
    F.preserves_isHomLift (𝟙 x.base) πu
  let q₀ : ((twoYonedaEval (𝒳 := 𝒳st) x.base).obj (a.comp F)).1 ⟶ y.1 :=
    F.map πu ≫ e.hom ≫ q
  haveI hq₀ : IsHomLift 𝒳st.p f q₀ := by
    infer_instance
  let e₀ := (twoYonedaPullbackEvalIso (a.comp F)).symm
  let e₁ := twoYonedaPullbackIsoOfIsHomLift f
    ((twoYonedaEval (𝒳 := 𝒳st) x.base).obj (a.comp F)) y q₀
  let e₂ := isoWhiskerLeft (overBased.map f) (twoYonedaPullbackEvalIso g)
  exact e₀ ≪≫ e₁ ≪≫ e₂

end AlgebraicGeometry.PresheafGroupoid

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  (F : BasedFunctor Xcat Ycat) (T : Scheme.{u})
  (g : BasedFunctor (overBased T) Ycat)

/-- Classifying the based functor induced by a presheaf map recovers the original
presheaf map. -/
@[simp]
lemma ofPresheafMapOfBasedFunctor_map
    {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    ofPresheafMapOfBasedFunctor (ofPresheaf.map f) = f := by
  ext S x
  let d : (ofPresheaf X).obj :=
    CostructuredArrow.mk (yonedaEquiv.symm x)
  have h := ofPresheafMapOfBasedFunctor_app (ofPresheaf.map f) d
  have h' := congrArg
    (fun k : yoneda.obj S.unop ⟶ Y ↦ k.app S (𝟙 S.unop)) h
  dsimp [d, ofPresheaf.map] at h'
  have hx : (yonedaEquiv.symm x).app S (𝟙 S.unop) = x :=
    Equiv.apply_symm_apply yonedaEquiv x
  change (ofPresheafMapOfBasedFunctor (ofPresheaf.map f)).app S
      ((yonedaEquiv.symm x).app S (𝟙 S.unop)) =
    f.app S ((yonedaEquiv.symm x).app S (𝟙 S.unop)) at h'
  rw [hx] at h'
  exact h'

/-- Pulling a represented self-intersection back along a scheme-valued point of the
source gives a scheme representation of the corresponding fiber.

More precisely, let `F : U → Y`, let `R` represent `U ×_Y U`, and use the first
projection of this representation to obtain a presheaf map `ρ : R → U`.  If `ρ` is
representable by schemes with property `P`, then the fiber of `F` over the image of any
scheme-valued point `a : S → U` is represented by the scheme obtained by pulling `ρ`
back along `a`; its structural map to `S` has property `P`.

The projection hypothesis is intentionally stated for the map classified by the chosen
self-intersection representation.  Quotient-groupoid applications discharge it by the
compatibility of the relation comparison with `s : R → U` (or, after symmetry, `t`). -/
theorem exists_scheme_representation_fiber_of_selfIntersection
    {U R : Scheme.{u}ᵒᵖ ⥤ Type u}
    {Zcat : BasedCategory.{v₃, u₃} Scheme.{u}}
    [Zcat.p.IsFiberedInGroupoids]
    (A : BasedFunctor (ofPresheaf U) Zcat)
    {P : MorphismProperty Scheme.{u}}
    (E : BasedFunctor (ofPresheaf R) (fiberProduct A A))
    (hE : E.toFunctor.IsEquivalence)
    (hρ : MorphismProperty.presheaf P
      (ofPresheafMapOfBasedFunctor
        (E.comp (fiberProductFst A A))))
    (S : Scheme.{u}) (a : BasedFunctor (overBased S) (ofPresheaf U)) :
    ∃ (W : Scheme.{u})
      (K : BasedFunctor (overBased W) (fiberProduct A (a.comp A))),
      K.toFunctor.IsEquivalence ∧
        P (K.comp (fiberProductSnd A (a.comp A))).overHom := by
  let H := E.comp (fiberProductFst A A)
  let ρ := ofPresheafMapOfBasedFunctor H
  let W := hρ.rep.pullback
    (CategoryTheory.BasedFunctor.ofPresheafHom a)
  let L₀ := ofPresheafFiberProductLift a hρ.rep
  let L₁ := fiberProductMapLeftIso
    (ofPresheafMapOfBasedFunctorIso H) a
  let L₂ := fiberProductSymm H a
  let L₃ := fiberProductRightMap a (fiberProductFst A A) E
  let L₄ := pasteFwd a A A
  let L₅ := fiberProductSymm (a.comp A) A
  let K := ((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp L₅
  refine ⟨W, K, ?_, ?_⟩
  · let _ : E.toFunctor.IsEquivalence := hE
    let _ : L₀.toFunctor.IsEquivalence :=
      isEquivalence_ofPresheafFiberProductLift a hρ.rep
    let _ : L₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapLeftIso
        (ofPresheafMapOfBasedFunctorIso H) a
    let _ : L₃.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductRightMap a (fiberProductFst A A) E
    let _ : L₄.toFunctor.IsEquivalence := inferInstance
    have h₀₁ : (L₀.comp L₁).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans L₀.toFunctor L₁.toFunctor
    let _ : (L₀.comp L₁).toFunctor.IsEquivalence := h₀₁
    have h₂ : ((L₀.comp L₁).comp L₂).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans (L₀.comp L₁).toFunctor L₂.toFunctor
    let _ : ((L₀.comp L₁).comp L₂).toFunctor.IsEquivalence := h₂
    have h₃ : (((L₀.comp L₁).comp L₂).comp L₃).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans
        ((L₀.comp L₁).comp L₂).toFunctor L₃.toFunctor
    let _ : (((L₀.comp L₁).comp L₂).comp L₃).toFunctor.IsEquivalence := h₃
    have h₄ : ((((L₀.comp L₁).comp L₂).comp L₃).comp
        L₄).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans
        (((L₀.comp L₁).comp L₂).comp L₃).toFunctor L₄.toFunctor
    exact Functor.isEquivalence_trans
      ((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).toFunctor L₅.toFunctor
  · exact hρ.property_snd
      (CategoryTheory.BasedFunctor.ofPresheafHom a)

/-- The represented relation of a quotient presentation gives a scheme chart for the
fiber over every quotient-local lift.  A property of the groupoid source map is
inherited by the structural map of this chart. -/
theorem _root_.AlgebraicGeometry.PresheafGroupoid.exists_scheme_representation_localFiber
    {𝒢 : PresheafGroupoid.{u}}
    {𝒳st : BasedCategory.{v₃, u₃} Scheme.{u}}
    [𝒳st.p.IsFiberedInGroupoids]
    (i : BasedFunctor 𝒢.quotientPrestack 𝒳st)
    [i.toFunctor.Full] [i.toFunctor.Faithful]
    {P : MorphismProperty Scheme.{u}}
    (hs : MorphismProperty.presheaf P 𝒢.s)
    {T : Scheme.{u}} (g : BasedFunctor (overBased T) 𝒳st)
    (x : 𝒢.quotientPrestack.obj)
    (q : i.obj x ⟶ ((twoYonedaEval (𝒳 := 𝒳st) T).obj g).1) :
    let A := 𝒢.quotientPresentation.comp i
    let f := PresheafGroupoid.quotientLiftBaseMap g x q
    ∃ (W : Scheme.{u})
      (K : BasedFunctor (overBased W)
        (fiberProduct A ((overBased.map f).comp g))),
      K.toFunctor.IsEquivalence ∧
        P (K.comp (fiberProductSnd A ((overBased.map f).comp g))).overHom := by
  let Q := 𝒢.quotientPresentation
  let A := Q.comp i
  let E₀ := 𝒢.relationComparison
  let E₁ := fiberProductPostcomp Q Q i
  let E := E₀.comp E₁
  have hE₀ : E₀.toFunctor.IsEquivalence :=
    PresheafGroupoid.relationComparison_isEquivalence
  let _ : E₀.toFunctor.IsEquivalence := hE₀
  have hE₁ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp Q Q i
  let _ : E₁.toFunctor.IsEquivalence := hE₁
  have hE : E.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E₀.toFunctor E₁.toFunctor
  have hEfst : E.comp (fiberProductFst A A) = ofPresheaf.map 𝒢.s := by
    apply BasedFunctor.ext_of_toFunctor_eq
    rfl
  have hρ : MorphismProperty.presheaf P
      (ofPresheafMapOfBasedFunctor
        (E.comp (fiberProductFst A A))) := by
    rw [hEfst, ofPresheafMapOfBasedFunctor_map]
    exact hs
  let a := PresheafGroupoid.quotientPoint x
  obtain ⟨W, K, hK, hPK⟩ :=
    exists_scheme_representation_fiber_of_selfIntersection
      A E hE hρ x.base a
  let η := PresheafGroupoid.quotientLocalLiftIso g x q
  let L := fiberProductMapRightIso A η
  let K' := K.comp L
  refine ⟨W, K', ?_, ?_⟩
  · let _ : K.toFunctor.IsEquivalence := hK
    let _ : L.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso A η
    exact Functor.isEquivalence_trans K.toFunctor L.toFunctor
  · change P (K.comp (fiberProductSnd A (a.comp A))).overHom
    exact hPK

/-- A small sheaf representation of a prestack fiber which becomes an algebraic space
after one surjective étale base change of the test scheme.

The structural map from `X` to `T` is the map classified by the second projection of
the represented fiber.  For quotient stacks, a local lift to the quotient prestack and
the represented self-intersection are intended to prove `localIsAlgebraicSpace`. -/
structure EtaleLocalFiberRepresentation where
  /-- The small presheaf representing the fiber. -/
  X : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- The representing presheaf is an étale sheaf. -/
  isSheaf : Presieve.IsSheaf Scheme.etaleTopology X
  /-- A representation of the prestack fiber by `X`. -/
  representation :
    BasedFunctor (ofPresheaf X) (fiberProduct F g)
  /-- The representation is an equivalence. -/
  representation_isEquivalence : representation.toFunctor.IsEquivalence
  /-- A scheme over which the represented fiber is already an algebraic space. -/
  localBase : Scheme.{u}
  /-- The surjective étale base change. -/
  localMap : localBase ⟶ T
  /-- The local map is étale. -/
  localMap_etale : Etale localMap
  /-- The local map is surjective. -/
  localMap_surjective : Surjective localMap
  /-- After the base change, the represented fiber is an algebraic space. -/
  localIsAlgebraicSpace :
    let _ : representation.toFunctor.IsEquivalence :=
      representation_isEquivalence
    IsAlgebraicSpace
      (pullback (representedFiberSecondBaseMap F g representation)
        (yoneda.map localMap))

/-- Build an étale-local fiber representation from a global small sheaf
representation and a scheme representation after one surjective étale base change. -/
noncomputable def EtaleLocalFiberRepresentation.of_localSchemeRepresentation
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    (hX : Presieve.IsSheaf Scheme.etaleTopology X)
    (E : BasedFunctor (ofPresheaf X) (fiberProduct F g))
    (hE : E.toFunctor.IsEquivalence)
    {S W : Scheme.{u}} (p : S ⟶ T) (hpEtale : Etale p)
    (hpSurjective : Surjective p)
    (K : BasedFunctor (overBased W)
      (fiberProduct F ((overBased.map p).comp g)))
    (hK : K.toFunctor.IsEquivalence) :
    EtaleLocalFiberRepresentation F T g := by
  let _ : E.toFunctor.IsEquivalence := hE
  refine
    { X := X
      isSheaf := hX
      representation := E
      representation_isEquivalence := hE
      localBase := S
      localMap := p
      localMap_etale := hpEtale
      localMap_surjective := hpSurjective
      localIsAlgebraicSpace := ?_ }
  obtain ⟨L, hL⟩ :=
    isRepresentedByPresheaf_fiber_secondBaseChange F g E p
  let _ : L.toFunctor.IsEquivalence := hL
  let K' := (ofPresheafYonedaToOverBased W).comp K
  have hK' : K'.toFunctor.IsEquivalence := by
    let _ : K.toFunctor.IsEquivalence := hK
    exact Functor.isEquivalence_trans
      (ofPresheafYonedaToOverBased W).toFunctor K.toFunctor
  let _ : K'.toFunctor.IsEquivalence := hK'
  let e := ofPresheaf.comparisonIso L K'
  exact IsAlgebraicSpace.of_iso e

/-- A prestack morphism is representable when every scheme-valued fiber admits an
étale-local fiber representation. -/
theorem Representable.of_etaleLocalFiberRepresentations
    (hF : ∀ (T : Scheme.{u}) (g : BasedFunctor (overBased T) Ycat),
      EtaleLocalFiberRepresentation F T g) :
    Representable F := by
  intro T g
  let D := hF T g
  let _ : D.representation.toFunctor.IsEquivalence :=
    D.representation_isEquivalence
  let _ : Etale D.localMap := D.localMap_etale
  let _ : Surjective D.localMap := D.localMap_surjective
  let _ : IsAlgebraicSpace
      (pullback (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map D.localMap)) := D.localIsAlgebraicSpace
  have hX : IsAlgebraicSpace D.X :=
    IsAlgebraicSpace.of_etale_surjective_base_change D.isSheaf
      (representedFiberSecondBaseMap F g D.representation) D.localMap
  exact ⟨D.X, hX, D.representation,
    D.representation_isEquivalence⟩

/-- Combined local-fiber criterion for representability with a morphism property.

The first hypothesis proves representability.  The final hypothesis supplies one good
scheme chart of each fiber; in quotient applications this chart is obtained from the
represented self-intersection after a local lift. -/
theorem RepresentableWith.of_etaleLocalFiberRepresentations
    {P : MorphismProperty Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (hF : ∀ (T : Scheme.{u}) (g : BasedFunctor (overBased T) Ycat),
      EtaleLocalFiberRepresentation F T g)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hgood : ∀ (T : Scheme.{u}) (g : BasedFunctor (overBased T) Ycat),
      ∃ (U : Scheme.{u})
        (p : BasedFunctor (overBased U) (fiberProduct F g)),
        RepresentableWith
          (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p ∧
        P (p.comp (BasedCategory.fiberProductSnd F g)).overHom) :
    RepresentableWith P F :=
  RepresentableWith.of_exists_good_chart
    (Representable.of_etaleLocalFiberRepresentations F hF) hlocal hgood

end AlgebraicGeometry.BasedFunctor
