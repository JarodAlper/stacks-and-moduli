module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.3-quotient-stacks-of-groupoids»
public import StacksAndModuli.API.PresheafLocalSurjectiveSingleton
public import StacksAndModuli.API.QuasiFiniteSourceLocal
public import StacksAndModuli.API.RelativePresheafOver
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.6-criterion-for-sheaf-to-be-scheme»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# The presentation of a pointwise quotient by an equivalence relation

For an étale equivalence relation `R ⇉ U`, this file identifies the fiber of the
pointwise quotient map `U → U/R` over the class of a point `b ∈ U(T)` with the
base change of `t : R → U` along `b`.  In particular, the pointwise quotient map is
representable by schemes, surjective, and étale.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite ConcreteCategory

universe u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}}

/-- Equality of two classes in the pointwise quotient of a groupoid comes from a
relation.  The raw quotient uses the equivalence closure of `quotientRel`; the
groupoid axioms show that `quotientRel` is already an equivalence relation. -/
lemma quotientRel_of_quot_mk_eq {T : Scheme.{u}ᵒᵖ} {a b : 𝒢.U.obj T}
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b) :
    𝒢.quotientRel T a b :=
  (𝒢.equivalence_quotientRel T).eqvGen_iff.mp (Quot.eqvGen_exact h)

/-- The unique relation underlying equality of two quotient classes. -/
noncomputable def relationOfQuotientEq (_hER : 𝒢.IsEquivalenceRelation)
    {T : Scheme.{u}ᵒᵖ} (a b : 𝒢.U.obj T)
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b) :
    𝒢.R.obj T :=
  Classical.choose (quotientRel_of_quot_mk_eq h)

@[simp]
lemma s_relationOfQuotientEq (hER : 𝒢.IsEquivalenceRelation)
    {T : Scheme.{u}ᵒᵖ} (a b : 𝒢.U.obj T)
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b) :
    𝒢.s.app T (relationOfQuotientEq hER a b h) = a :=
  (Classical.choose_spec (quotientRel_of_quot_mk_eq h)).1

@[simp]
lemma t_relationOfQuotientEq (hER : 𝒢.IsEquivalenceRelation)
    {T : Scheme.{u}ᵒᵖ} (a b : 𝒢.U.obj T)
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b) :
    𝒢.t.app T (relationOfQuotientEq hER a b h) = b :=
  (Classical.choose_spec (quotientRel_of_quot_mk_eq h)).2

/-- The chosen relation underlying equality of quotient classes is compatible with
restriction.  Uniqueness of relations is exactly what makes the pointwise choice
natural. -/
lemma map_relationOfQuotientEq (hER : 𝒢.IsEquivalenceRelation)
    {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T') (a b : 𝒢.U.obj T)
    (h : Quot.mk (𝒢.quotientRel T) a = Quot.mk (𝒢.quotientRel T) b)
    (h' : Quot.mk (𝒢.quotientRel T') (𝒢.U.map f a) =
      Quot.mk (𝒢.quotientRel T') (𝒢.U.map f b)) :
    𝒢.R.map f (relationOfQuotientEq hER a b h) =
      relationOfQuotientEq hER (𝒢.U.map f a) (𝒢.U.map f b) h' := by
  apply hER
  · simp
  · simp

/-- The pointwise quotient of an equivalence relation of representable presheaves
is separated for the étale topology.  Local relations witnessing equality of two
quotient classes glue because the relation presheaf is a sheaf; uniqueness of
relations makes the chosen local witnesses compatible. -/
theorem quotientPresheaf_isSeparated
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable] :
    Presieve.IsSeparated Scheme.etaleTopology 𝒢.quotientPresheaf := by
  intro T S hS family c₁ c₂ hc₁ hc₂
  obtain ⟨a, rfl⟩ := Quot.exists_rep c₁
  obtain ⟨b, rfl⟩ := Quot.exists_rep c₂
  apply Quot.sound
  let localEq {Y : Scheme.{u}} (f : Y ⟶ T) (hf : S f) :
      Quot.mk (𝒢.quotientRel (op Y)) (𝒢.U.map f.op a) =
        Quot.mk (𝒢.quotientRel (op Y)) (𝒢.U.map f.op b) := by
    exact (hc₁ f hf).trans (hc₂ f hf).symm
  let relFamily : S.arrows.FamilyOfElements 𝒢.R := fun _ f hf ↦
    relationOfQuotientEq hER (𝒢.U.map f.op a) (𝒢.U.map f.op b)
      (localEq f hf)
  have hrelFamily : relFamily.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
    apply hER
    · rw [𝒢.s_app_map, 𝒢.s_app_map]
      simp only [relFamily, s_relationOfQuotientEq]
      simpa only [← Functor.map_comp_apply, op_comp] using
        congrArg (fun k ↦ 𝒢.U.map k.op a) hcomp
    · rw [𝒢.t_app_map, 𝒢.t_app_map]
      simp only [relFamily, t_relationOfQuotientEq]
      simpa only [← Functor.map_comp_apply, op_comp] using
        congrArg (fun k ↦ 𝒢.U.map k.op b) hcomp
  have hR := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    𝒢.R).isSheafFor S.arrows (by simpa using hS)
  let r : 𝒢.R.obj (op T) := hR.amalgamate relFamily hrelFamily
  refine ⟨r, ?_, ?_⟩
  · have hU := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      𝒢.U).isSheafFor S.arrows (by simpa using hS)
    apply hU.isSeparatedFor.ext
    intro Y f hf
    rw [← 𝒢.s_app_map]
    rw [hR.valid_glue hrelFamily f hf]
    exact s_relationOfQuotientEq hER _ _ _
  · have hU := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      𝒢.U).isSheafFor S.arrows (by simpa using hS)
    apply hU.isSeparatedFor.ext
    intro Y f hf
    rw [← 𝒢.t_app_map]
    rw [hR.valid_glue hrelFamily f hf]
    exact t_relationOfQuotientEq hER _ _ _

/-- A locally injective comparison from the separated pointwise quotient to its
quotient sheaf is injective on sections. -/
theorem quotientSheafComparison_injective
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) (T : Scheme.{u}ᵒᵖ) :
    Function.Injective (q.app T) := by
  let _ : Presheaf.IsLocallyInjective Scheme.etaleTopology q :=
    hq.isLocallyInjective
  intro a b hab
  apply (quotientPresheaf_isSeparated hER _
    (Presheaf.equalizerSieve_mem Scheme.etaleTopology q a b hab)).ext
  intro Y f hf
  exact hf

/-- The comparison from a separated pointwise quotient to its quotient sheaf is
a monomorphism of presheaves. -/
theorem quotientSheafComparison_mono
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) : Mono q := by
  let _ (T : Scheme.{u}ᵒᵖ) : Mono (q.app T) :=
    ConcreteCategory.mono_of_injective _
      (quotientSheafComparison_injective hER hq T)
  exact NatTrans.mono_of_mono_app q

/-- For an equivalence relation, the relation presheaf is the pullback of the
diagonal of its quotient sheaf along the product of the quotient maps. -/
theorem isPullback_relation_quotientSheafDiagonal
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) :
    IsPullback (𝒢.s ≫ 𝒢.toQuotientPresheaf ≫ q) (prod.lift 𝒢.s 𝒢.t)
      (Limits.diag X)
      (prod.map (𝒢.toQuotientPresheaf ≫ q)
        (𝒢.toQuotientPresheaf ≫ q)) := by
  let φ := 𝒢.toQuotientPresheaf ≫ q
  let st := prod.lift 𝒢.s 𝒢.t
  let _ : Mono q := quotientSheafComparison_mono hER hq
  have hstQ : 𝒢.s ≫ 𝒢.toQuotientPresheaf =
      𝒢.t ≫ 𝒢.toQuotientPresheaf := by
    ext T r
    exact Quot.sound ⟨r, rfl, rfl⟩
  have hsquare : (𝒢.s ≫ φ) ≫ Limits.diag X =
      st ≫ prod.map φ φ := by
    apply prod.hom_ext
    · simp [φ, st]
    · simp only [Limits.diag, Category.assoc, prod.lift_snd, prod.map_snd,
        st, φ]
      rw [← Category.assoc, hstQ]
      simp
  have hquot (c : PullbackCone (Limits.diag X) (prod.map φ φ))
      (T : Scheme.{u}ᵒᵖ) (z : c.pt.obj T) :
      Quot.mk (𝒢.quotientRel T)
          ((c.snd ≫ prod.fst).app T z) =
        Quot.mk (𝒢.quotientRel T)
          ((c.snd ≫ prod.snd).app T z) := by
    have hc₁ := congrArg (fun k ↦ k ≫ prod.fst) c.condition
    have hc₂ := congrArg (fun k ↦ k ≫ prod.snd) c.condition
    have hc₁' : c.fst = (c.snd ≫ prod.fst) ≫ φ := by
      simpa only [Category.assoc, Limits.diag, prod.lift_fst,
        Category.comp_id, prod.map_fst] using hc₁
    have hc₂' : c.fst = (c.snd ≫ prod.snd) ≫ φ := by
      simpa only [Category.assoc, Limits.diag, prod.lift_snd,
        Category.comp_id, prod.map_snd] using hc₂
    have hφ : (c.snd ≫ prod.fst) ≫ φ =
        (c.snd ≫ prod.snd) ≫ φ := hc₁'.symm.trans hc₂'
    have hq0 : (c.snd ≫ prod.fst) ≫ 𝒢.toQuotientPresheaf =
        (c.snd ≫ prod.snd) ≫ 𝒢.toQuotientPresheaf := by
      rw [← cancel_mono q]
      simpa only [φ, Category.assoc] using hφ
    exact congr_hom (congr_app hq0 T) z
  let rel (c : PullbackCone (Limits.diag X) (prod.map φ φ)) :
      c.pt ⟶ 𝒢.R :=
    { app := fun T ↦ TypeCat.ofHom (fun z ↦
        relationOfQuotientEq hER
          ((c.snd ≫ prod.fst).app T z)
          ((c.snd ≫ prod.snd).app T z) (hquot c T z))
      naturality := fun T T' f ↦ by
        apply ConcreteCategory.hom_ext
        intro z
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        change relationOfQuotientEq hER
            ((c.snd ≫ prod.fst).app T' (c.pt.map f z))
            ((c.snd ≫ prod.snd).app T' (c.pt.map f z))
              (hquot c T' (c.pt.map f z)) =
          𝒢.R.map f (relationOfQuotientEq hER
            ((c.snd ≫ prod.fst).app T z)
            ((c.snd ≫ prod.snd).app T z) (hquot c T z))
        symm
        apply hER
        · rw [𝒢.s_app_map, s_relationOfQuotientEq,
              s_relationOfQuotientEq]
          exact (NatTrans.naturality_apply (c.snd ≫ prod.fst) f z).symm
        · rw [𝒢.t_app_map, t_relationOfQuotientEq,
              t_relationOfQuotientEq]
          exact (NatTrans.naturality_apply (c.snd ≫ prod.snd) f z).symm }
  have hrel_st (c : PullbackCone (Limits.diag X) (prod.map φ φ)) :
      rel c ≫ st = c.snd := by
    apply prod.hom_ext
    · ext T z
      simp [rel, st]
    · ext T z
      simp [rel, st]
  have hrel_top (c : PullbackCone (Limits.diag X) (prod.map φ φ)) :
      rel c ≫ (𝒢.s ≫ φ) = c.fst := by
    have hc₁ := congrArg (fun k ↦ k ≫ prod.fst) c.condition
    rw [← Category.assoc]
    rw [show rel c ≫ 𝒢.s = c.snd ≫ prod.fst by
      simpa only [st, Category.assoc, prod.lift_fst] using
        congrArg (fun k ↦ k ≫ prod.fst) (hrel_st c)]
    simpa only [Category.assoc, prod.map_fst, Limits.diag, prod.lift_fst,
      Category.comp_id] using hc₁.symm
  let lift (c : PullbackCone (Limits.diag X) (prod.map φ φ)) :
      c.pt ⟶ 𝒢.R := rel c
  have hlimit : IsLimit
      (PullbackCone.mk (𝒢.s ≫ φ) st hsquare) :=
    PullbackCone.IsLimit.mk hsquare lift hrel_top hrel_st
      (fun c m _ hmSt ↦ by
        ext T z
        apply hER
        · have hsource : m ≫ 𝒢.s = lift c ≫ 𝒢.s := by
            calc
              m ≫ 𝒢.s = (m ≫ st) ≫ prod.fst := by simp [st]
              _ = c.snd ≫ prod.fst := by rw [hmSt]
              _ = (lift c ≫ st) ≫ prod.fst := by rw [hrel_st]
              _ = lift c ≫ 𝒢.s := by simp [st]
          exact congr_hom (congr_app hsource T) z
        · have htarget : m ≫ 𝒢.t = lift c ≫ 𝒢.t := by
            calc
              m ≫ 𝒢.t = (m ≫ st) ≫ prod.snd := by simp [st]
              _ = c.snd ≫ prod.snd := by rw [hmSt]
              _ = (lift c ≫ st) ≫ prod.snd := by rw [hrel_st]
              _ = lift c ≫ 𝒢.t := by simp [st]
          exact congr_hom (congr_app htarget T) z)
  simpa only [φ, st, Category.assoc] using
    (IsPullback.mk ⟨hsquare⟩ ⟨hlimit⟩)

/-- For an étale equivalence relation of representable presheaves, the source-target
map `(s, t) : R → U × U` is represented by a locally finite type, locally
quasi-finite, separated morphism of schemes. -/
theorem presheaf_relationMap_locallyQuasiFinite_isSeparated [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable] :
    MorphismProperty.presheaf
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u}) (prod.lift 𝒢.s 𝒢.t) := by
  let eR : yoneda.obj 𝒢.R.reprX ≅ 𝒢.R := 𝒢.R.reprW
  let eU : yoneda.obj 𝒢.U.reprX ≅ 𝒢.U := 𝒢.U.reprW
  let eUU : yoneda.obj (𝒢.U.reprX ⨯ 𝒢.U.reprX) ≅ 𝒢.U ⨯ 𝒢.U :=
    asIso (prodComparison yoneda 𝒢.U.reprX 𝒢.U.reprX) ≪≫
      prod.mapIso eU eU
  let st := prod.lift 𝒢.s 𝒢.t
  let st₀ : 𝒢.R.reprX ⟶ 𝒢.U.reprX ⨯ 𝒢.U.reprX :=
    yoneda.preimage (eR.hom ≫ st ≫ eUU.inv)
  let _ : Mono st :=
    ⟨fun f g h ↦ by
      ext T z
      apply hER
      · have hs : f ≫ 𝒢.s = g ≫ 𝒢.s := by
          calc
            f ≫ 𝒢.s = (f ≫ st) ≫ prod.fst := by simp [st]
            _ = (g ≫ st) ≫ prod.fst := by rw [h]
            _ = g ≫ 𝒢.s := by simp [st]
        exact congr_hom (congr_app hs T) z
      · have ht : f ≫ 𝒢.t = g ≫ 𝒢.t := by
          calc
            f ≫ 𝒢.t = (f ≫ st) ≫ prod.snd := by simp [st]
            _ = (g ≫ st) ≫ prod.snd := by rw [h]
            _ = g ≫ 𝒢.t := by simp [st]
        exact congr_hom (congr_app ht T) z⟩
  let eSt : Arrow.mk (yoneda.map st₀) ≅ Arrow.mk st :=
    Arrow.isoMk eR eUU (by simp [st₀])
  let _ : Mono (yoneda.map st₀) := by
    rw [show yoneda.map st₀ = eR.hom ≫ st ≫ eUU.inv by
      exact yoneda.map_preimage _]
    infer_instance
  let _ : Mono st₀ := yoneda.mono_of_mono_map inferInstance
  let s₀ : 𝒢.R.reprX ⟶ 𝒢.U.reprX := st₀ ≫ prod.fst
  have heUU_fst : eUU.hom ≫ prod.fst =
      yoneda.map prod.fst ≫ eU.hom := by
    simp [eUU]
  have heSt : eR.hom ≫ st = yoneda.map st₀ ≫ eUU.hom := by
    simpa only [eSt, Arrow.isoMk_hom_left, Arrow.isoMk_hom_right,
      Arrow.mk_hom] using eSt.hom.w
  let eS : Arrow.mk (yoneda.map s₀) ≅ Arrow.mk 𝒢.s :=
    Arrow.isoMk eR eU (by
      change eR.hom ≫ 𝒢.s = yoneda.map (st₀ ≫ prod.fst) ≫ eU.hom
      calc
        eR.hom ≫ 𝒢.s = (eR.hom ≫ st) ≫ prod.fst := by simp [st]
        _ = (yoneda.map st₀ ≫ eUU.hom) ≫ prod.fst := by rw [heSt]
        _ = yoneda.map st₀ ≫ (yoneda.map prod.fst ≫ eU.hom) := by
          rw [Category.assoc, heUU_fst]
        _ = yoneda.map (st₀ ≫ prod.fst) ≫ eU.hom := by
          rw [yoneda.map_comp, Category.assoc])
  have hs₀pre : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u})
      (yoneda.map s₀) :=
    (MorphismProperty.arrow_mk_iso_iff _ eS).2 IsEtale.presheaf_s
  let _ : Etale s₀ := MorphismProperty.of_relative_map hs₀pre
  have hst₀ :
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u}) st₀ :=
    ⟨⟨locallyOfFiniteType_of_comp st₀ prod.fst,
      LocallyQuasiFinite.of_comp st₀ prod.fst⟩, inferInstance⟩
  have hst₀pre : MorphismProperty.presheaf
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u}) (yoneda.map st₀) :=
    MorphismProperty.relative_map hst₀
  exact (MorphismProperty.arrow_mk_iso_iff _ eSt).1 hst₀pre

/-- The fiber of `U → U/R` over the class of `b ∈ U(T)` is represented by the
same scheme as the fiber of `t : R → U` over `b`. -/
private lemma exists_quotientPresentation_pullback [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation) {T : Scheme.{u}} (b : 𝒢.U.obj (op T)) :
    ∃ (W : Scheme.{u}) (fst : yoneda.obj W ⟶ 𝒢.U) (snd : W ⟶ T),
      IsPullback fst (yoneda.map snd) 𝒢.toQuotientPresheaf
        (yonedaEquiv.symm (Quot.mk (𝒢.quotientRel (op T)) b)) ∧
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) snd := by
  let gb : yoneda.obj T ⟶ 𝒢.U := yonedaEquiv.symm b
  let ht := IsEtale.presheaf_t (𝒢 := 𝒢)
  let W := ht.rep.pullback gb
  let rW : yoneda.obj W ⟶ 𝒢.R := ht.rep.fst gb
  let snd : W ⟶ T := ht.rep.snd gb
  let fst : yoneda.obj W ⟶ 𝒢.U := rW ≫ 𝒢.s
  let gq : yoneda.obj T ⟶ 𝒢.quotientPresheaf :=
    yonedaEquiv.symm (Quot.mk (𝒢.quotientRel (op T)) b)
  have hsquare : fst ≫ 𝒢.toQuotientPresheaf = yoneda.map snd ≫ gq := by
    ext Z z
    apply Quot.sound
    refine ⟨rW.app Z z, rfl, ?_⟩
    have h := congr_hom (congr_app (ht.rep.w gb) Z) z
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    change 𝒢.t.app Z (rW.app Z z) =
      gb.app Z ((yoneda.map snd).app Z z) at h
    change 𝒢.t.app Z (rW.app Z z) =
      𝒢.U.map (snd.op ≫ z.op) b at h
    exact h
  have hpullback : IsPullback fst (yoneda.map snd)
      𝒢.toQuotientPresheaf gq := by
    have hquot (c : PullbackCone 𝒢.toQuotientPresheaf gq)
        (Z : Scheme.{u}ᵒᵖ) (z : c.pt.obj Z) :
        Quot.mk (𝒢.quotientRel Z) (c.fst.app Z z) =
          Quot.mk (𝒢.quotientRel Z)
            (𝒢.U.map (c.snd.app Z z).op b) := by
      have h := congr_hom (congr_app c.condition Z) z
      change Quot.mk (𝒢.quotientRel Z) (c.fst.app Z z) =
        Quot.mk (𝒢.quotientRel Z)
          (𝒢.U.map (c.snd.app Z z).op b) at h
      exact h
    let rel (c : PullbackCone 𝒢.toQuotientPresheaf gq) : c.pt ⟶ 𝒢.R :=
      { app := fun Z ↦ TypeCat.ofHom (fun z ↦
          relationOfQuotientEq hER (c.fst.app Z z)
            (𝒢.U.map (c.snd.app Z z).op b) (hquot c Z z))
        naturality := fun Z Z' f ↦ by
          apply ConcreteCategory.hom_ext
          intro z
          rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
          change relationOfQuotientEq hER
              (c.fst.app Z' (c.pt.map f z))
              (𝒢.U.map (c.snd.app Z' (c.pt.map f z)).op b)
                (hquot c Z' (c.pt.map f z)) =
            𝒢.R.map f
              (relationOfQuotientEq hER (c.fst.app Z z)
                (𝒢.U.map (c.snd.app Z z).op b) (hquot c Z z))
          symm
          apply hER
          · rw [s_relationOfQuotientEq, 𝒢.s_app_map,
              s_relationOfQuotientEq]
            exact (NatTrans.naturality_apply c.fst f z).symm
          · rw [t_relationOfQuotientEq, 𝒢.t_app_map,
              t_relationOfQuotientEq]
            have hn := NatTrans.naturality_apply c.snd f z
            rw [hn]
            simp }
    have hrel_s (c : PullbackCone 𝒢.toQuotientPresheaf gq) :
        rel c ≫ 𝒢.s = c.fst := by
      ext Z z
      simp [rel]
    have hrel_t (c : PullbackCone 𝒢.toQuotientPresheaf gq) :
        rel c ≫ 𝒢.t = c.snd ≫ gb := by
      ext Z z
      simp [rel, gb]
    let lift (c : PullbackCone 𝒢.toQuotientPresheaf gq) :
        c.pt ⟶ yoneda.obj W :=
      (ht.rep.isPullback gb).isLimit.lift
        (PullbackCone.mk (rel c) c.snd (hrel_t c))
    have hlift_rW (c : PullbackCone 𝒢.toQuotientPresheaf gq) :
        lift c ≫ rW = rel c := by
      exact (ht.rep.isPullback gb).isLimit.fac
        (PullbackCone.mk (rel c) c.snd (hrel_t c)) WalkingCospan.left
    have hlift_snd (c : PullbackCone 𝒢.toQuotientPresheaf gq) :
        lift c ≫ yoneda.map snd = c.snd := by
      exact (ht.rep.isPullback gb).isLimit.fac
        (PullbackCone.mk (rel c) c.snd (hrel_t c)) WalkingCospan.right
    have hlimit : IsLimit
        (PullbackCone.mk fst (yoneda.map snd) hsquare) :=
      PullbackCone.IsLimit.mk hsquare lift
        (fun c ↦ by
          rw [show fst = rW ≫ 𝒢.s from rfl, ← Category.assoc,
            hlift_rW c, hrel_s c])
        hlift_snd
        (fun c m hmfst hmsnd ↦ by
          apply (ht.rep.isPullback gb).hom_ext
          · ext Z z
            apply hER
            · have hs : (m ≫ rW) ≫ 𝒢.s = (lift c ≫ rW) ≫ 𝒢.s := by
                calc
                  (m ≫ rW) ≫ 𝒢.s = m ≫ fst := by
                    rw [Category.assoc]
                  _ = c.fst := hmfst
                  _ = rel c ≫ 𝒢.s := (hrel_s c).symm
                  _ = (lift c ≫ rW) ≫ 𝒢.s := by rw [hlift_rW c]
              exact congr_hom (congr_app hs Z) z
            · have htgt : (m ≫ rW) ≫ 𝒢.t =
                  (lift c ≫ rW) ≫ 𝒢.t := by
                calc
                  (m ≫ rW) ≫ 𝒢.t =
                      (m ≫ yoneda.map snd) ≫ gb := by
                    rw [Category.assoc, Category.assoc, ht.rep.w gb]
                  _ = c.snd ≫ gb := by rw [hmsnd]
                  _ = rel c ≫ 𝒢.t := (hrel_t c).symm
                  _ = (lift c ≫ rW) ≫ 𝒢.t := by rw [hlift_rW c]
              exact congr_hom (congr_app htgt Z) z
          · rw [hmsnd, hlift_snd c])
    exact IsPullback.mk ⟨hsquare⟩ ⟨hlimit⟩
  have hetale : Etale snd := ht.property_snd gb
  let sec : T ⟶ W := ht.rep.lift (gb ≫ 𝒢.e) (𝟙 T) (by
    simp [gb, Category.assoc, 𝒢.e_t])
  have hsec : sec ≫ snd = 𝟙 T := ht.rep.lift_snd _ _ _
  have hsurjective : Surjective snd := by
    have hcomp : Surjective (sec ≫ snd) := by
      rw [hsec]
      infer_instance
    exact @Surjective.of_comp _ _ _ sec snd hcomp
  exact ⟨W, fst, snd, hpullback, hsurjective, hetale⟩

private lemma exists_quotientPresentation_pullback_class [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation) {T : Scheme.{u}}
    (c : 𝒢.quotientPresheaf.obj (op T)) :
    ∃ (W : Scheme.{u}) (fst : yoneda.obj W ⟶ 𝒢.U) (snd : W ⟶ T),
      IsPullback fst (yoneda.map snd) 𝒢.toQuotientPresheaf
        (yonedaEquiv.symm c) ∧
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) snd := by
  induction c using Quot.ind with
  | mk b => exact exists_quotientPresentation_pullback (𝒢 := 𝒢) hER b

/-- For an étale equivalence relation, the canonical map from its object presheaf to
its pointwise quotient is representable by schemes, surjective, and étale. -/
theorem presheaf_toQuotientPresheaf [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation) :
    MorphismProperty.presheaf
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      𝒢.toQuotientPresheaf := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨W, fst, snd, hpullback, hP⟩ :=
    exists_quotientPresentation_pullback_class (𝒢 := 𝒢) hER (yonedaEquiv g)
  rw [yonedaEquiv.symm_apply_apply] at hpullback
  exact ⟨W, fst, snd, hpullback, hP⟩

/-- Every point of a quotient sheaf lifts to the object presheaf after one
surjective étale base change.  The singleton cover is obtained by gluing the local
preimages supplied by the quotient-sheaf comparison. -/
theorem exists_etale_surjective_quotient_lift
    [𝒢.U.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) {T : Scheme.{u}} (x : X.obj (op T)) :
    ∃ (T' : Scheme.{u}) (p : T' ⟶ T), Etale p ∧ Surjective p ∧
      ∃ u : 𝒢.U.obj (op T'),
        (𝒢.toQuotientPresheaf ≫ q).app (op T') u = X.map p.op x := by
  let φ := 𝒢.toQuotientPresheaf ≫ q
  let _ : Presheaf.IsLocallySurjective Scheme.etaleTopology
      𝒢.toQuotientPresheaf :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (fun _ ↦ Quot.mk_surjective)
  let _ : Presheaf.IsLocallySurjective Scheme.etaleTopology q :=
    hq.isLocallySurjective
  let _ : Presheaf.IsLocallySurjective Scheme.etaleTopology φ := inferInstance
  have hU : Presieve.IsSheaf Scheme.zariskiTopology 𝒢.U :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hX : Presieve.IsSheaf Scheme.zariskiTopology X :=
    Presieve.isSheaf_of_le X Scheme.zariskiTopology_le_etaleTopology hq.isSheaf
  exact Presheaf.exists_etale_surjective_lift φ hU hX x

/-- Two points of a quotient sheaf lift simultaneously to the object presheaf after
one surjective étale base change. -/
theorem exists_etale_surjective_quotient_pair_lift
    [𝒢.U.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) {T : Scheme.{u}} (x y : X.obj (op T)) :
    ∃ (T' : Scheme.{u}) (p : T' ⟶ T), Etale p ∧ Surjective p ∧
      ∃ (u v : 𝒢.U.obj (op T')),
        (𝒢.toQuotientPresheaf ≫ q).app (op T') u = X.map p.op x ∧
        (𝒢.toQuotientPresheaf ≫ q).app (op T') v = X.map p.op y := by
  let φ := 𝒢.toQuotientPresheaf ≫ q
  obtain ⟨T₁, p₁, hp₁Etale, hp₁Surjective, u₁, hu₁⟩ :=
    exists_etale_surjective_quotient_lift (𝒢 := 𝒢) hq x
  let _ : Etale p₁ := hp₁Etale
  let _ : Surjective p₁ := hp₁Surjective
  obtain ⟨T₂, p₂, hp₂Etale, hp₂Surjective, u₂, hu₂⟩ :=
    exists_etale_surjective_quotient_lift (𝒢 := 𝒢) hq (X.map p₁.op y)
  let _ : Etale p₂ := hp₂Etale
  let _ : Surjective p₂ := hp₂Surjective
  let p : T₂ ⟶ T := p₂ ≫ p₁
  let u₁' : 𝒢.U.obj (op T₂) := 𝒢.U.map p₂.op u₁
  refine ⟨T₂, p, inferInstance, inferInstance, u₁', u₂, ?_, ?_⟩
  · change φ.app (op T₂) (𝒢.U.map p₂.op u₁) = X.map p.op x
    rw [NatTrans.naturality_apply φ p₂.op u₁]
    have hu₁' : φ.app (op T₁) u₁ = X.map p₁.op x := hu₁
    rw [hu₁']
    simp [p]
  · change φ.app (op T₂) u₂ = X.map p.op y
    rw [hu₂]
    simp [p]

/-- The diagonal of the quotient sheaf of an étale equivalence relation of
representable presheaves is representable by schemes. -/
theorem relativelyRepresentable_quotientSheafDiagonal [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation)
    [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) :
    yoneda.relativelyRepresentable (Limits.diag X) := by
  let φ := 𝒢.toQuotientPresheaf ≫ q
  let st := prod.lift 𝒢.s 𝒢.t
  let hst := presheaf_relationMap_locallyQuasiFinite_isSeparated
    (hER := hER)
  let hRel := isPullback_relation_quotientSheafDiagonal hER hq
  intro T g
  let x : X.obj (op T) := yonedaEquiv (g ≫ prod.fst)
  let y : X.obj (op T) := yonedaEquiv (g ≫ prod.snd)
  obtain ⟨T', p, hpEtale, hpSurjective, a, b, ha, hb⟩ :=
    exists_etale_surjective_quotient_pair_lift (𝒢 := 𝒢) hq x y
  let ga : yoneda.obj T' ⟶ 𝒢.U := yonedaEquiv.symm a
  let gb : yoneda.obj T' ⟶ 𝒢.U := yonedaEquiv.symm b
  let k : yoneda.obj T' ⟶ 𝒢.U ⨯ 𝒢.U := prod.lift ga gb
  have hk : k ≫ prod.map φ φ = yoneda.map p ≫ g := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst]
      rw [← Category.assoc, show k ≫ prod.fst = ga by simp [k]]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      rw [show yonedaEquiv ga = a by exact Equiv.apply_symm_apply _ a]
      exact ha.trans (yonedaEquiv_naturality (g ≫ prod.fst) p)
    · simp only [Category.assoc, prod.map_snd]
      rw [← Category.assoc, show k ≫ prod.snd = gb by simp [k]]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      rw [show yonedaEquiv gb = b by exact Equiv.apply_symm_apply _ b]
      exact hb.trans (yonedaEquiv_naturality (g ≫ prod.snd) p)
  let W := hst.rep.pullback k
  let fstW := hst.rep.fst k
  let sndW := hst.rep.snd k
  have hW : IsPullback fstW (yoneda.map sndW) st k := hst.rep.isPullback k
  have hWΔ : IsPullback (fstW ≫ (𝒢.s ≫ φ)) (yoneda.map sndW)
      (Limits.diag X) (yoneda.map p ≫ g) := by
    rw [← hk]
    exact hW.paste_horiz hRel
  let Pabs := pullback (Limits.diag X) g
  let fstP := pullback.fst (Limits.diag X) g
  let η := pullback.snd (Limits.diag X) g
  have hP : IsPullback fstP η (Limits.diag X) g :=
    IsPullback.of_hasPullback _ _
  let liftW : yoneda.obj W ⟶ Pabs :=
    hP.lift (fstW ≫ (𝒢.s ≫ φ))
      (yoneda.map sndW ≫ yoneda.map p) (by
        simpa only [Category.assoc] using hWΔ.w)
  have hWP : IsPullback liftW (yoneda.map sndW) η (yoneda.map p) :=
    hWΔ.of_right' hP
  let eWP : Over.mk (yoneda.map sndW) ≅
      Over.mk (pullback.snd η (yoneda.map p)) :=
    Over.isoMk hWP.isoPullback (by exact hWP.isoPullback_hom_snd)
  let eLocal : yoneda.obj (Over.mk sndW) ≅
      (Over.map p).op ⋙ Presheaf.relativeOver η :=
    Presheaf.relativeOverYonedaIso (Over.mk sndW) ≪≫
      Presheaf.relativeOverMapIso eWP ≪≫
        Presheaf.relativeOverPullbackIso p η
  have hXX : Presieve.IsSheaf Scheme.etaleTopology (X ⨯ X) := by
    rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
    refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf Scheme.etaleTopology)
      (limit.isLimit (pair X X)) ?_
    rintro ⟨j⟩
    cases j with
    | left =>
        rw [pair_obj_left, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact hq.isSheaf
    | right =>
        rw [pair_obj_right, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact hq.isSheaf
  have hPabsSheaf : Presieve.IsSheaf Scheme.etaleTopology Pabs := by
    dsimp only [Pabs]
    exact AlgebraicGeometry.isSheaf_pullback Scheme.etaleTopology _ _
      hq.isSheaf
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (yoneda.obj T)) hXX
  let Frel : Sheaf (Scheme.etaleTopology.over T) (Type u) :=
    ⟨Presheaf.relativeOver η,
      (isSheaf_iff_isSheaf_of_type _ _).2
        (Presheaf.relativeOver_isSheaf Scheme.etaleTopology η hPabsSheaf)⟩
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  have hLocal :
      (Scheme.etaleTopology.representableByProperty
        (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
          MorphismProperty Scheme.{u})).prop (.mk (op T'))
        ((Scheme.etaleTopology.overMapPullback (Type u) p).obj Frel) := by
    refine ⟨Over.mk sndW, hst.property_snd k, ⟨?_⟩⟩
    exact eLocal
  obtain ⟨Z, _, ⟨eZ⟩⟩ :=
    MorphismProperty.presheaf_locallyQuasiFinite_isSeparated_of_pullback
      p Frel hLocal
  let eArrow := Presheaf.relativeOverRepresentationArrowIso η Z eZ
  have heArrow_right : eArrow.hom.right = 𝟙 (yoneda.obj T) := by
    rfl
  have hIso : IsPullback eArrow.hom.left (yoneda.map Z.hom) η
      (𝟙 (yoneda.obj T)) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [← heArrow_right]
    exact eArrow.hom.w
  refine ⟨Z.left, Z.hom, eArrow.hom.left ≫ fstP, ?_⟩
  simpa using hIso.paste_horiz hP

end AlgebraicGeometry.PresheafGroupoid
