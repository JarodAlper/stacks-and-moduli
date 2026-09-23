module

public import StacksAndModuli.API.PrincipalBundleInduction
public import StacksAndModuli.API.ClassifyingStackCartesianSupport
public import StacksAndModuli.API.ClassifyingPrestackFpqcMorphisms
public import StacksAndModuli.API.MorphismsGlueCocone

/-!
# Trivializing induced principal bundles along quotient-stack objects

An equivariant map from a principal `H`-bundle to the right-coset `H`-space `G`
canonically trivializes its induced principal `G`-bundle.  This file constructs
that trivialization from the fpqc-local transition charts and proves that it is
unique and functorial.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.PrincipalBundleInduction

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
  (phi : H ⟶ G) [IsMonHom phi] [ModObj H G]

variable {T : Over S} (x : ActionQuotientObj H G)

noncomputable abbrev trivialTarget [Smooth G.hom] [IsAffineHom G.hom] :
    ClassifyingObj G := ⟨x.carrier.base, GlobalPrincipalBundle.trivial G x.carrier.base⟩

/-- The canonical map between the trivial target bundles attached to the base
map of a morphism of underlying principal `H`-bundles. -/
noncomputable def trivialTargetCarrierMap [Smooth G.hom] [IsAffineHom G.hom]
    {y : ActionQuotientObj H G} (f : x.carrier ⟶ y.carrier) :
    trivialTarget x ⟶ trivialTarget y where
  base := f.base
  total := GlobalPrincipalBundle.trivialBaseMap (G := G) f.base
  isPullback := GlobalPrincipalBundle.trivialBaseMap_isPullback
    (G := G) f.base
  equivariant := GlobalPrincipalBundle.trivialBaseMap_equivariant
    (G := G) f.base

noncomputable def localTrivialization [Smooth G.hom] [IsAffineHom G.hom]
    (q : (coverSieve x.carrier.bundle).arrows.category) :
    (localFunctor phi x.carrier.bundle).obj q ⟶ trivialTarget x where
  base := q.obj.hom
  total :=
    GlobalPrincipalBundle.trivialRightTranslate (G := G)
        ((localSection x.carrier.bundle q ≫ x.map)⁻¹) ≫
      GlobalPrincipalBundle.trivialBaseMap (G := G) q.obj.hom
  isPullback := by
    have htranslate : IsPullback
        (GlobalPrincipalBundle.trivialRightTranslate (G := G)
          ((localSection x.carrier.bundle q ≫ x.map)⁻¹))
        (GlobalPrincipalBundle.trivialSnd G q.obj.left)
        (GlobalPrincipalBundle.trivialSnd G q.obj.left) (𝟙 q.obj.left) := by
      apply IsPullback.of_horiz_isIso
      exact ⟨by simp⟩
    exact htranslate.paste_horiz
      (GlobalPrincipalBundle.trivialBaseMap_isPullback (G := G) q.obj.hom)
  equivariant := by
    letI := GlobalPrincipalBundle.trivialRightTranslate_equivariant
      (G := G) ((localSection x.carrier.bundle q ≫ x.map)⁻¹)
    letI := GlobalPrincipalBundle.trivialBaseMap_equivariant
      (G := G) q.obj.hom
    infer_instance

lemma localTrivialization_naturality [Smooth G.hom] [IsAffineHom G.hom]
    (hcoset : ∀ {Z : Over S} (h : Z ⟶ H) (g : Z ⟶ G),
      h • g = g * (h ≫ phi)⁻¹)
    {q r : (coverSieve x.carrier.bundle).arrows.category} (k : q ⟶ r) :
    (localFunctor phi x.carrier.bundle).map k ≫ localTrivialization phi x r =
      localTrivialization phi x q := by
  let B := x.carrier.bundle
  let d : q.obj.left ⟶ H := B.torsorDifference (localSection B q)
    (k.hom.left ≫ localSection B r) (localSection_transition_eq B k)
  have hu : localSection B q ≫ x.map =
      (k.hom.left ≫ localSection B r ≫ x.map) * (d ≫ phi)⁻¹ := by
    letI : IsModHom H x.map := x.equivariant
    calc
      localSection B q ≫ x.map =
          (d • (k.hom.left ≫ localSection B r)) ≫ x.map := by
        rw [B.torsorDifference_smul]
      _ = d • ((k.hom.left ≫ localSection B r) ≫ x.map) :=
        IsModHom.map_smul x.map d (k.hom.left ≫ localSection B r)
      _ = ((k.hom.left ≫ localSection B r) ≫ x.map) * (d ≫ phi)⁻¹ :=
        hcoset d ((k.hom.left ≫ localSection B r) ≫ x.map)
      _ = (k.hom.left ≫ localSection B r ≫ x.map) * (d ≫ phi)⁻¹ := by
        rw [Category.assoc]
  have hgauge : (d ≫ phi) *
        (k.hom.left ≫ (localSection B r ≫ x.map)⁻¹) =
      (localSection B q ≫ x.map)⁻¹ := by
    have hi := congrArg (fun z ↦ z⁻¹) hu
    rw [_root_.mul_inv_rev, inv_inv] at hi
    calc
      (d ≫ phi) * (k.hom.left ≫ (localSection B r ≫ x.map)⁻¹) =
          (d ≫ phi) * ((k.hom.left ≫ localSection B r ≫ x.map)⁻¹) := by
        congr 1
      _ = (localSection B q ≫ x.map)⁻¹ := hi.symm
  apply ClassifyingHom.ext
  · exact k.hom.w
  · change
      (GlobalPrincipalBundle.trivialRightTranslate (G := G)
          (transitionGauge phi B k) ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) k.hom.left) ≫
          (GlobalPrincipalBundle.trivialRightTranslate (G := G)
              ((localSection B r ≫ x.map)⁻¹) ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) r.obj.hom) =
        GlobalPrincipalBundle.trivialRightTranslate (G := G)
            ((localSection B q ≫ x.map)⁻¹) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) q.obj.hom
    slice_lhs 2 3 =>
      rw [GlobalPrincipalBundle.trivialBaseMap_comp_rightTranslate]
    slice_lhs 1 2 =>
      rw [GlobalPrincipalBundle.trivialRightTranslate_comp]
    slice_lhs 2 3 =>
      rw [GlobalPrincipalBundle.trivialBaseMap_comp]
    change GlobalPrincipalBundle.trivialRightTranslate (G := G)
        ((d ≫ phi) * (k.hom.left ≫ (localSection B r ≫ x.map)⁻¹)) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G)
            (k.hom.left ≫ r.obj.hom) = _
    rw [hgauge, k.hom.w]

lemma localTrivialization_map [Smooth G.hom] [IsAffineHom G.hom]
    (hcoset : ∀ {Z : Over S} (h : Z ⟶ H) (g : Z ⟶ G),
      h • g = g * (h ≫ phi)⁻¹)
    {y : ActionQuotientObj H G} (f : x ⟶ y)
    (q : (coverSieve x.carrier.bundle).arrows.category) :
    mapLocalHom phi x.carrier.bundle y.carrier.bundle f.carrier q ≫
        localTrivialization phi y
          ((mapCoverFunctor x.carrier.bundle y.carrier.bundle f.carrier).obj q) =
      localTrivialization phi x q ≫
        ({ base := f.carrier.base
           total := GlobalPrincipalBundle.trivialBaseMap (G := G) f.carrier.base
           isPullback := GlobalPrincipalBundle.trivialBaseMap_isPullback
             (G := G) f.carrier.base
           equivariant := GlobalPrincipalBundle.trivialBaseMap_equivariant
             (G := G) f.carrier.base } : trivialTarget x ⟶ trivialTarget y) := by
  let B := x.carrier.bundle
  let B' := y.carrier.bundle
  let m : q.obj.left ⟶ H := mapSectionGauge B B' f.carrier q
  let t : q.obj.left ⟶ B'.P := mappedLocalSection B B' f.carrier q
  have hm : m • (localSection B q ≫ f.carrier.total) = t := by
    dsimp only [m, mapSectionGauge]
    simpa only [t] using B'.torsorDifference_smul
      (mappedLocalSection B B' f.carrier q)
      (localSection B q ≫ f.carrier.total) _
  have hu : t ≫ y.map =
      (localSection B q ≫ x.map) * (m ≫ phi)⁻¹ := by
    letI : IsModHom H y.map := y.equivariant
    calc
      t ≫ y.map = (m • (localSection B q ≫ f.carrier.total)) ≫ y.map := by
        rw [hm]
      _ = m • ((localSection B q ≫ f.carrier.total) ≫ y.map) :=
        IsModHom.map_smul y.map m (localSection B q ≫ f.carrier.total)
      _ = ((localSection B q ≫ f.carrier.total) ≫ y.map) * (m ≫ phi)⁻¹ :=
        hcoset m ((localSection B q ≫ f.carrier.total) ≫ y.map)
      _ = (localSection B q ≫ x.map) * (m ≫ phi)⁻¹ := by
        rw [Category.assoc, f.map_naturality]
  have htarget : (t ≫ y.map)⁻¹ =
      (m ≫ phi) * (localSection B q ≫ x.map)⁻¹ := by
    have hi := congrArg (fun z ↦ z⁻¹) hu
    rw [_root_.mul_inv_rev, inv_inv] at hi
    exact hi
  have hgauge : (m ≫ phi)⁻¹ *
        (t ≫ y.map)⁻¹ =
      (localSection B q ≫ x.map)⁻¹ := by
    rw [htarget, ← _root_.mul_assoc, inv_mul_cancel]
    simp
  apply ClassifyingHom.ext
  · rfl
  · change
      GlobalPrincipalBundle.trivialRightTranslate (G := G) ((m ≫ phi)⁻¹) ≫
        (GlobalPrincipalBundle.trivialRightTranslate (G := G)
            ((localSection B'
              ((mapCoverFunctor B B' f.carrier).obj q) ≫ y.map)⁻¹) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G)
            (q.obj.hom ≫ f.carrier.base)) =
      (GlobalPrincipalBundle.trivialRightTranslate (G := G)
          ((localSection B q ≫ x.map)⁻¹) ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) q.obj.hom) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) f.carrier.base
    slice_lhs 1 2 =>
      rw [GlobalPrincipalBundle.trivialRightTranslate_comp]
    slice_rhs 2 3 =>
      rw [GlobalPrincipalBundle.trivialBaseMap_comp]
    change GlobalPrincipalBundle.trivialRightTranslate (G := G)
        ((m ≫ phi)⁻¹ * (t ≫ y.map)⁻¹) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G)
            (q.obj.hom ≫ f.carrier.base) = _
    rw [hgauge]

/-- Conversely, compatibility of the local induced-bundle map with the
trivializations recovers compatibility of the original equivariant maps on the
chosen source section. -/
lemma local_map_naturality_of_trivializations
    [Smooth G.hom] [IsAffineHom G.hom]
    (hcoset : ∀ {Z : Over S} (h : Z ⟶ H) (g : Z ⟶ G),
      h • g = g * (h ≫ phi)⁻¹)
    {y : ActionQuotientObj H G} (f : x.carrier ⟶ y.carrier)
    (q : (coverSieve x.carrier.bundle).arrows.category)
    (hlocal :
      mapLocalHom phi x.carrier.bundle y.carrier.bundle f q ≫
          localTrivialization phi y
            ((mapCoverFunctor x.carrier.bundle y.carrier.bundle f).obj q) =
        localTrivialization phi x q ≫ trivialTargetCarrierMap x f) :
    (localSection x.carrier.bundle q ≫ f.total) ≫ y.map =
      localSection x.carrier.bundle q ≫ x.map := by
  let B := x.carrier.bundle
  let B' := y.carrier.bundle
  let s : q.obj.left ⟶ B.P := localSection B q
  let t : q.obj.left ⟶ B'.P := mappedLocalSection B B' f q
  let m : q.obj.left ⟶ H := mapSectionGauge B B' f q
  have htotal := congrArg ClassifyingHom.total hlocal
  have hgauge : (m ≫ phi)⁻¹ * (t ≫ y.map)⁻¹ = (s ≫ x.map)⁻¹ := by
    change
      GlobalPrincipalBundle.trivialRightTranslate (G := G) (m ≫ phi)⁻¹ ≫
          (GlobalPrincipalBundle.trivialRightTranslate (G := G) (t ≫ y.map)⁻¹ ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) (q.obj.hom ≫ f.base)) =
        (GlobalPrincipalBundle.trivialRightTranslate (G := G) (s ≫ x.map)⁻¹ ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) q.obj.hom) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) f.base at htotal
    rw [← Category.assoc, GlobalPrincipalBundle.trivialRightTranslate_comp,
      Category.assoc, GlobalPrincipalBundle.trivialBaseMap_comp] at htotal
    have hcoord := congrArg (fun z ↦
      GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫ z ≫
        GlobalPrincipalBundle.trivialFst G y.carrier.base) htotal
    have hcoord' : (1 : q.obj.left ⟶ G) * ((m ≫ phi)⁻¹ * (t ≫ y.map)⁻¹) =
        (1 : q.obj.left ⟶ G) * (s ≫ x.map)⁻¹ := by
      change (toUnit q.obj.left ≫ η[G]) * ((m ≫ phi)⁻¹ * (t ≫ y.map)⁻¹) =
        (toUnit q.obj.left ≫ η[G]) * (s ≫ x.map)⁻¹
      simpa only [mapLocalHom, localTrivialization, trivialTargetCarrierMap,
      s, t, m, Category.assoc, GlobalPrincipalBundle.trivialBaseMap_fst,
      GlobalPrincipalBundle.trivialRightTranslate_fst, MonObj.comp_mul,
      GlobalPrincipalBundle.trivialSection_fst,
      GlobalPrincipalBundle.trivialSection_snd_assoc, MonObj.comp_one,
      Category.id_comp] using hcoord
    simpa using hcoord'
  have hty : t ≫ y.map = ((s ≫ f.total) ≫ y.map) * (m ≫ phi)⁻¹ := by
    letI : IsModHom H y.map := y.equivariant
    calc
      t ≫ y.map = (m • (s ≫ f.total)) ≫ y.map := by
        dsimp only [m, mapSectionGauge]
        rw [GlobalPrincipalBundle.torsorDifference_smul]
      _ = m • ((s ≫ f.total) ≫ y.map) :=
        IsModHom.map_smul y.map m (s ≫ f.total)
      _ = ((s ≫ f.total) ≫ y.map) * (m ≫ phi)⁻¹ :=
        hcoset m ((s ≫ f.total) ≫ y.map)
  have hinv : (t ≫ y.map)⁻¹ =
      (m ≫ phi) * (((s ≫ f.total) ≫ y.map)⁻¹) := by
    rw [hty, _root_.mul_inv_rev, inv_inv]
  rw [hinv] at hgauge
  rw [← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul] at hgauge
  have h := congrArg (fun z ↦ z⁻¹) hgauge
  simpa only [s, inv_inv] using h

/-- Two equivariant maps out of a torsor agree if they agree after a chosen
local section over the torsor's own base change. -/
lemma equivariant_map_eq_of_localSection
    {U : Over S} [ModObj H U] (B : GlobalPrincipalBundle H T)
    (u v : B.P ⟶ U)
    [IsModHom H u] [IsModHom H v]
    (h : localSection B (selfCoverObj B) ≫ u =
      localSection B (selfCoverObj B) ≫ v) : u = v := by
  let s : B.P ⟶ B.P := localSection B (selfCoverObj B)
  let d : B.P ⟶ H := B.torsorDifference s (𝟙 B.P) (by
    dsimp only [s]
    rw [localSection_fac]
    simp)
  have hd : d • (𝟙 B.P) = s :=
    B.torsorDifference_smul s (𝟙 B.P) _
  have huv : d • u = d • v := by
    calc
      d • u = d • ((𝟙 B.P) ≫ u) := by rw [Category.id_comp]
      _ = (d • (𝟙 B.P)) ≫ u := (IsModHom.map_smul u d (𝟙 B.P)).symm
      _ = s ≫ u := by rw [hd]
      _ = s ≫ v := h
      _ = (d • (𝟙 B.P)) ≫ v := by rw [hd]
      _ = d • ((𝟙 B.P) ≫ v) := IsModHom.map_smul v d (𝟙 B.P)
      _ = d • v := by rw [Category.id_comp]
  have hcancel := congrArg (fun z ↦ d⁻¹ • z) huv
  simpa only [inv_smul_smul] using hcancel

structure Trivialization [Smooth G.hom] [IsAffineHom G.hom]
    (C : Cocone phi x.carrier.bundle) where
  hom : C.obj ⟶ trivialTarget x
  hom_isHomLift : IsHomLift (classifyingPrestack G).p
    (𝟙 x.carrier.base) hom
  comparison_fac : ∀ q : (coverSieve x.carrier.bundle).arrows.category,
    C.comparison q ≫ hom = localTrivialization phi x q

theorem Trivialization.nonempty [Smooth G.hom] [IsAffineHom G.hom]
    (hcoset : ∀ {Z : Over S} (h : Z ⟶ H) (g : Z ⟶ G),
      h • g = g * (h ≫ phi)⁻¹)
    (C : Cocone phi x.carrier.bundle) : Nonempty (Trivialization phi x C) := by
  let p := (classifyingPrestack G).p
  let hglue : p.MorphismsGlue (Scheme.fpqcTopology.over S) :=
    ClassifyingPrestackMorphisms.morphismsGlue_fpqc
  obtain ⟨F, hF, -⟩ :=
    MorphismsGlue.existsUnique_gluing_hom_of_cocone hglue
      (coverSieve_mem x.carrier.bundle) (localFunctor phi x.carrier.bundle)
      rfl rfl C.comparison C.comparison_isHomLift
      (fun {_ _} k ↦ localFunctor_map_isHomLift phi x.carrier.bundle k)
      C.comparison_naturality (localTrivialization phi x)
      (fun q ↦ Functor.IsHomLift.map (p := p) (localTrivialization phi x q))
      (localTrivialization_naturality phi x hcoset)
  exact ⟨
    { hom := F
      hom_isHomLift := hF.1
      comparison_fac := fun q ↦ by
        let q' := (coverSieve x.carrier.bundle).arrows.categoryMk
          q.obj.hom q.property
        let k : q ⟶ q' := ObjectProperty.homMk
          (Over.homMk (𝟙 q.obj.left) (by simp [q']))
        calc
          C.comparison q ≫ F =
              ((localFunctor phi x.carrier.bundle).map k ≫ C.comparison q') ≫ F := by
            rw [C.comparison_naturality k]
          _ = (localFunctor phi x.carrier.bundle).map k ≫
              (C.comparison q' ≫ F) := Category.assoc _ _ _
          _ = (localFunctor phi x.carrier.bundle).map k ≫
              localTrivialization phi x q' := by rw [← hF.2 q.property]
          _ = localTrivialization phi x q :=
            localTrivialization_naturality phi x hcoset k }⟩

@[ext]
lemma Trivialization.ext [Smooth G.hom] [IsAffineHom G.hom]
    {C : Cocone phi x.carrier.bundle}
    (F F' : Trivialization phi x C) : F = F' := by
  cases F with
  | mk hom hlift hfac =>
    cases F' with
    | mk hom' hlift' hfac' =>
      have heq : hom = hom' := by
        apply ClassifyingHom.ext
        · exact
            (IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
              (𝟙 x.carrier.base) hom).symm.trans
            (IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
              (𝟙 x.carrier.base) hom')
        · apply Over.OverMorphism.ext
          let q := selfCoverObj x.carrier.bundle
          let c := C.comparison q
          letI : EffectiveEpi c.total.left :=
            comparison_self_total_effectiveEpi phi x.carrier.bundle C
          apply (cancel_epi c.total.left).mp
          exact congrArg (fun k ↦ k.total.left) ((hfac q).trans (hfac' q).symm)
      subst hom'
      rfl

noncomputable def Trivialization.iso [Smooth G.hom] [IsAffineHom G.hom]
    {C : Cocone phi x.carrier.bundle} (F : Trivialization phi x C) :
    C.obj ≅ trivialTarget x := by
  letI := F.hom_isHomLift
  letI : IsIso F.hom :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_isIso
      (p := (classifyingPrestack G).p) (𝟙 x.carrier.base) F.hom
  exact asIso F.hom

noncomputable def trivialTargetMap [Smooth G.hom] [IsAffineHom G.hom]
    {y : ActionQuotientObj H G} (f : x ⟶ y) :
    trivialTarget x ⟶ trivialTarget y :=
  trivialTargetCarrierMap x f.carrier

lemma Trivialization.map_naturality [Smooth G.hom] [IsAffineHom G.hom]
    (hcoset : ∀ {Z : Over S} (h : Z ⟶ H) (g : Z ⟶ G),
      h • g = g * (h ≫ phi)⁻¹)
    (I : EffectiveInduction phi) {y : ActionQuotientObj H G} (f : x ⟶ y)
    (F : Trivialization phi x (I.cocone x.carrier))
    (F' : Trivialization phi y (I.cocone y.carrier)) :
    DescendedHom.normalizedHom phi _ _ _ _ _ (I.map f.carrier) ≫ F'.hom =
      F.hom ≫ trivialTargetMap x f := by
  let B := x.carrier.bundle
  let B' := y.carrier.bundle
  let C := I.cocone x.carrier
  let C' := I.cocone y.carrier
  let q := selfCoverObj B
  let c := C.comparison q
  let q' := (mapCoverFunctor B B' f.carrier).obj q
  have hind : c ≫
      DescendedHom.normalizedHom phi B B' C C' f.carrier (I.map f.carrier) =
        mapCoconeLeg phi B B' C' f.carrier q := by
    apply ClassifyingHom.ext
    · letI := (I.map f.carrier).hom_isHomLift
      have hbase : f.carrier.base = (I.map f.carrier).hom.base :=
        IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
          f.carrier.base (I.map f.carrier).hom
      have hb := congrArg ClassifyingHom.base
        ((I.map f.carrier).comparison_fac q)
      change c.base ≫ f.carrier.base = _
      rw [hbase]
      exact hb
    · have ht := congrArg ClassifyingHom.total
        ((I.map f.carrier).comparison_fac q)
      change c.total ≫ (I.map f.carrier).hom.total = _ at ht
      change c.total ≫ (I.map f.carrier).hom.total = _
      exact ht
  have hpre : c ≫
        (DescendedHom.normalizedHom phi B B' C C' f.carrier
            (I.map f.carrier) ≫ F'.hom) =
      c ≫ (F.hom ≫ trivialTargetMap x f) := by
    calc
      c ≫ (DescendedHom.normalizedHom phi B B' C C' f.carrier
            (I.map f.carrier) ≫ F'.hom) =
          (c ≫ DescendedHom.normalizedHom phi B B' C C' f.carrier
            (I.map f.carrier)) ≫ F'.hom :=
        (Category.assoc _ _ _).symm
      _ = mapCoconeLeg phi B B' C' f.carrier q ≫ F'.hom := by rw [hind]
      _ = (mapLocalHom phi B B' f.carrier q ≫ C'.comparison q') ≫ F'.hom := rfl
      _ = mapLocalHom phi B B' f.carrier q ≫
          (C'.comparison q' ≫ F'.hom) := Category.assoc _ _ _
      _ = mapLocalHom phi B B' f.carrier q ≫
          localTrivialization phi y q' := by rw [F'.comparison_fac]
      _ = localTrivialization phi x q ≫ trivialTargetMap x f :=
        localTrivialization_map phi x hcoset f q
      _ = (c ≫ F.hom) ≫ trivialTargetMap x f := by rw [F.comparison_fac]
      _ = c ≫ (F.hom ≫ trivialTargetMap x f) := Category.assoc _ _ _
  apply ClassifyingHom.ext
  · letI := F.hom_isHomLift
    letI := F'.hom_isHomLift
    have hFbase : 𝟙 x.carrier.base = F.hom.base :=
      IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
        (𝟙 x.carrier.base) F.hom
    have hF'base : 𝟙 y.carrier.base = F'.hom.base :=
      IsHomLift.eq_of_isHomLift (classifyingPrestack G).p
        (𝟙 y.carrier.base) F'.hom
    change f.carrier.base ≫ F'.hom.base = F.hom.base ≫ f.carrier.base
    rw [← hFbase, ← hF'base]
    simp
  · apply Over.OverMorphism.ext
    letI : EffectiveEpi c.total.left :=
      comparison_self_total_effectiveEpi phi B C
    apply (cancel_epi c.total.left).mp
    exact congrArg (fun k ↦ k.total.left) hpre

end AlgebraicGeometry.Scheme.PrincipalBundleInduction
