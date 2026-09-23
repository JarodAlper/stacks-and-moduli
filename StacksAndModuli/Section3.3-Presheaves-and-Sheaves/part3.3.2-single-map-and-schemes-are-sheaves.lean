module

public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Reduction of the sheaf axiom to a single morphism, and schemes as sheaves

This module formalizes Exercise 3.3.7 (`exer:sheaf-axiom-reduced-to-single-map`) and
Proposition 3.3.8 (`prop:schemes-are-sheaves-in-fpqc-topology`) of §3.3 (Presheaves and
sheaves) of *Stacks and Moduli*,
section label `sec:sheaves`.

Main results:
- `AlgebraicGeometry.Scheme.isUniversalColimit_coproduct`: arbitrary coproducts of schemes
  are universal colimits;
- `AlgebraicGeometry.Scheme.zariskiPrecoverage_eq_propQCPrecoverage`,
  `AlgebraicGeometry.Scheme.etalePrecoverage_eq_propQCPrecoverage`, and
  `AlgebraicGeometry.Scheme.fppfPrecoverage_eq_propQCPrecoverage`: étale and fppf coverings
  automatically satisfy the quasi-compactness condition of fpqc coverings;
- `AlgebraicGeometry.isSheaf_type_etaleTopology_iff` /
  `AlgebraicGeometry.isSheaf_type_fppfTopology_iff` (and the fpqc case, recalled from
  Mathlib's `isSheaf_type_propQCTopology_iff`): a presheaf on schemes is an étale
  (resp. fppf, fpqc) sheaf if and only if it is a Zariski sheaf and satisfies the sheaf
  condition for single surjective étale (resp. fppf, faithfully flat) morphisms of affine
  schemes;
- `AlgebraicGeometry.isSheaf_precoverage_of_bijective_sigma`: the general implication
  from coproduct preservation plus singleton descent to sheafhood;
- `AlgebraicGeometry.Scheme.etaleTopology_le_fpqcTopology`: étale coverings are fpqc
  coverings;
- the fact that representable presheaves are fpqc (hence étale and fppf) sheaves, recalled
  from Mathlib's `Subcanonical` instances.
-/

@[expose] public section

-- Mathlib declares `@Flat`, `@Etale`, ... under this option; without it their
-- `MorphismProperty` instances do not unify here.
set_option backward.isDefEq.respectTransparency.types false

section ExerSheafAxiomReducedToSingleMap

open CategoryTheory Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.Scheme

/-- The Zariski precoverage is the quasi-compact precoverage of open immersions.  The
quasi-compactness condition on a jointly surjective family of opens is automatic: every
quasi-compact open of the target is covered by finitely many members of the family.

This is the Zariski specialization of the quasi-compact-cover reduction used in Stacks
022H.
-/
lemma zariskiPrecoverage_eq_propQCPrecoverage :
    zariskiPrecoverage.{u} = propQCPrecoverage @IsOpenImmersion :=
  le_antisymm
    (le_inf
      (precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f hf ↦
        have : IsOpenImmersion f := hf
        f.isOpenMap)
      le_rfl)
    propQCPrecoverage_le_precoverage

/-- The big Zariski topology is the quasi-compact topology associated to open
immersions. -/
lemma zariskiTopology_eq_propQCTopology :
    zariskiTopology.{u} = propQCTopology @IsOpenImmersion :=
  congrArg Precoverage.toGrothendieck zariskiPrecoverage_eq_propQCPrecoverage

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary coproducts of schemes are universal: after pulling the coproduct cocone back
along any morphism, the resulting cocone is still a coproduct cocone. -/
lemma isUniversalColimit_coproduct {ι : Type u} (X : ι → Scheme.{u}) :
    IsUniversalColimit (Cofan.mk (∐ X) (Sigma.ι X)) := by
  intro F' c' α f h hα hpull
  let X' : ι → Scheme.{u} := fun i ↦ F'.obj ⟨i⟩
  let d : Cofan X' := Cofan.mk c'.pt fun i ↦ c'.ι.app ⟨i⟩
  haveI (i : ι) : IsOpenImmersion (d.inj i) := by
    apply MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpull ⟨i⟩).flip
    change IsOpenImmersion (Sigma.ι X i)
    infer_instance
  have hdisj : Pairwise fun i j ↦ Disjoint (d.inj i).opensRange (d.inj j).opensRange := by
    intro i j hij U hUi hUj z hz
    obtain ⟨zi, rfl⟩ := hUi hz
    obtain ⟨zj, hzj⟩ := hUj hz
    have hi : Sigma.ι X i (α.app ⟨i⟩ zi) = f (d.inj i zi) := by
      have hw := (hpull ⟨i⟩).w
      change d.inj i ≫ f = α.app ⟨i⟩ ≫ Sigma.ι X i at hw
      exact congrArg (fun k : F'.obj ⟨i⟩ ⟶ (∐ X) ↦ k zi) hw.symm
    have hj : Sigma.ι X j (α.app ⟨j⟩ zj) = f (d.inj i zi) := by
      have hw := (hpull ⟨j⟩).w
      change d.inj j ≫ f = α.app ⟨j⟩ ≫ Sigma.ι X j at hw
      have hwz := congrArg (fun k : F'.obj ⟨j⟩ ⟶ (∐ X) ↦ k zj) hw
      exact hwz.symm.trans (congrArg f hzj)
    have heq := (sigmaι_eq_iff X i j _ _).mp (hi.trans hj.symm)
    exact hij (congrArg Sigma.fst heq)
  have hcov : ⨆ i, (d.inj i).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z hz
    generalize hq : (sigmaMk X).symm (f z) = q
    obtain ⟨i, x⟩ := q
    have hx : f z = Sigma.ι X i x := by
      rw [← sigmaMk_mk, ← hq]
      exact (sigmaMk X).apply_symm_apply (f z) |>.symm
    obtain ⟨z', hz', -⟩ := exists_preimage_of_isPullback (hpull ⟨i⟩) z x hx
    exact by
      simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.mem_mk, Set.mem_iUnion]
      exact ⟨i, z', hz'⟩
  obtain ⟨hd⟩ := nonempty_isColimit_cofanMk_of d.inj hcov hdisj
  exact ⟨
    { desc := fun s ↦ hd.desc (Cofan.mk s.pt fun i ↦ s.ι.app ⟨i⟩)
      fac := fun s j ↦ by simpa [d, X'] using hd.fac (Cofan.mk s.pt fun i ↦ s.ι.app ⟨i⟩) j
      uniq := fun s m hm ↦ hd.uniq (Cofan.mk s.pt fun i ↦ s.ι.app ⟨i⟩) m fun j ↦ by
        simpa [d, X'] using hm j }⟩

/-- A jointly surjective family of étale morphisms automatically satisfies the
quasi-compactness condition defining fpqc coverings, because étale morphisms are open: the
étale precoverage coincides with the quasi-compact precoverage of étale morphisms. -/
lemma etalePrecoverage_eq_propQCPrecoverage :
    etalePrecoverage.{u} = propQCPrecoverage @Etale :=
  le_antisymm
    (le_inf
      (precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f hf ↦
        have : Etale f := hf
        f.isOpenMap)
      le_rfl)
    propQCPrecoverage_le_precoverage

/-- A jointly surjective family of flat morphisms locally of finite presentation
automatically satisfies the quasi-compactness condition defining fpqc coverings, because
fppf morphisms are open: the fppf precoverage coincides with the quasi-compact precoverage
of flat morphisms locally of finite presentation. -/
lemma fppfPrecoverage_eq_propQCPrecoverage :
    fppfPrecoverage.{u} = propQCPrecoverage (@Flat ⊓ @LocallyOfFinitePresentation) :=
  le_antisymm
    (le_inf
      (precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f hf ↦
        have : Flat f := hf.1
        have : LocallyOfFinitePresentation f := hf.2
        f.isOpenMap)
      le_rfl)
    propQCPrecoverage_le_precoverage

/-- The étale topology is the quasi-compact topology of étale morphisms. -/
lemma etaleTopology_eq_propQCTopology : etaleTopology.{u} = propQCTopology @Etale :=
  congrArg Precoverage.toGrothendieck etalePrecoverage_eq_propQCPrecoverage

/-- The fppf topology is the quasi-compact topology of flat morphisms locally of finite
presentation. -/
lemma fppfTopology_eq_propQCTopology :
    fppfTopology.{u} = propQCTopology (@Flat ⊓ @LocallyOfFinitePresentation) :=
  congrArg Precoverage.toGrothendieck fppfPrecoverage_eq_propQCPrecoverage

/-- Every étale covering is an fpqc covering. -/
lemma etalePrecoverage_le_fpqcPrecoverage :
    etalePrecoverage.{u} ≤ fpqcPrecoverage := by
  rw [etalePrecoverage_eq_propQCPrecoverage]
  exact propQCPrecoverage_monotone fun _ _ f hf ↦
    have : Etale f := hf
    inferInstance

/-- The étale topology is coarser than the fpqc topology. -/
lemma etaleTopology_le_fpqcTopology : etaleTopology.{u} ≤ fpqcTopology :=
  (Precoverage.galoisConnection_toGrothendieck_toPrecoverage _).monotone_l
    etalePrecoverage_le_fpqcPrecoverage

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

/-- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (3), étale): let
$F$ be a presheaf on the category of schemes. Then $F$ is a sheaf for the étale topology if
and only if $F$ is a sheaf for the Zariski topology and the sheaf sequence
$F(S) \to F(S') \rightrightarrows F(S' \times_S S')$ is exact for every surjective étale
morphism $S' \to S$ of affine schemes. -/
theorem isSheaf_type_etaleTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.etaleTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), Etale (Spec.map f) →
          Surjective (Spec.map f) → Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  rw [etaleTopology_eq_propQCTopology]
  exact isSheaf_type_propQCTopology_iff F

/-- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (3), fppf): let
$F$ be a presheaf on the category of schemes. Then $F$ is a sheaf for the fppf topology if
and only if $F$ is a sheaf for the Zariski topology and the sheaf sequence
$F(S) \to F(S') \rightrightarrows F(S' \times_S S')$ is exact for every fppf (surjective,
flat, and locally of finite presentation) morphism $S' \to S$ of affine schemes. -/
theorem isSheaf_type_fppfTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.fppfTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), Flat (Spec.map f) →
          LocallyOfFinitePresentation (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  have : MorphismProperty.IsMultiplicative
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X ↦ ⟨MorphismProperty.id_mem _ X, inferInstance⟩
      comp_mem := fun f g hf hg ↦ ⟨MorphismProperty.comp_mem _ f g hf.1 hg.1,
        MorphismProperty.comp_mem _ f g hf.2 hg.2⟩ }
  rw [fppfTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
  exact and_congr_right fun _ ↦
    ⟨fun H _ _ f hf hlf hs ↦ H f ⟨hf, hlf⟩ hs, fun H _ _ f hf hs ↦ H f hf.1 hf.2 hs⟩

/- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (3), fpqc): let $F$
be a presheaf on the category of schemes. Then $F$ is a sheaf for the fpqc topology if and
only if $F$ is a sheaf for the Zariski topology and the sheaf sequence is exact for every
faithfully flat morphism $S' \to S$ of affine schemes. This is Mathlib's
`isSheaf_type_propQCTopology_iff` applied to the flat morphism property. -/
example (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.fpqcTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), Flat (Spec.map f) →
          Surjective (Spec.map f) → Presieve.IsSheafFor F (.singleton (Spec.map f)) :=
  isSheaf_type_propQCTopology_iff F

/-- A presheaf that sends scheme coproducts to products preserves every discrete limit
whose diagram consists of schemes. -/
lemma preservesLimit_discrete_of_bijective_sigma (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    (hF : ∀ {ι : Type u} (U : ι → Scheme.{u}),
      Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x)
    {ι : Type u} (U : ι → Scheme.{u}) :
    PreservesLimit (Discrete.functor fun i ↦ op (U i)) F := by
  let c : Cofan U := Cofan.mk (∐ U) (Sigma.ι U)
  apply preservesLimit_of_preserves_limit_cone
    (Cofan.IsColimit.op (coproductIsCoproduct U))
  let e : F.obj (op (∐ U)) ≃ (∀ i, F.obj (op (U i))) :=
    Equiv.ofBijective _ (hF U)
  refine
    { lift := fun s ↦ ↾fun y ↦ e.symm (fun i ↦ s.π.app ⟨i⟩ y)
      fac := fun s ⟨i⟩ ↦ by
        ext y
        exact congrFun (e.apply_symm_apply (fun j ↦ s.π.app ⟨j⟩ y)) i
      uniq := fun s m hm ↦ by
        ext y
        apply e.injective
        funext i
        change e (m y) i = e (e.symm (fun j ↦ s.π.app ⟨j⟩ y)) i
        rw [e.apply_symm_apply]
        dsimp [e]
        change F.map (Sigma.ι U i).op (m y) = s.π.app ⟨i⟩ y
        simpa using ConcreteCategory.congr_hom (hm ⟨i⟩) y }

/-- Conversely, preservation of the discrete limit opposite a scheme coproduct gives the
usual elementwise coproduct-to-product bijection. -/
lemma bijective_sigma_of_preservesLimit_discrete (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    {ι : Type u} (U : ι → Scheme.{u})
    [PreservesLimit (Discrete.functor fun i ↦ op (U i)) F] :
    Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x := by
  let c : Cofan U := Cofan.mk (∐ U) (Sigma.ι U)
  let hc : IsLimit (F.mapCone c.op) :=
    isLimitOfPreserves F (Cofan.IsColimit.op (coproductIsCoproduct U))
  constructor
  · intro x y hxy
    let mx : PUnit ⟶ F.obj (op (∐ U)) := ↾fun _ ↦ x
    let my : PUnit ⟶ F.obj (op (∐ U)) := ↾fun _ ↦ y
    have hm : mx = my := hc.hom_ext fun ⟨i⟩ ↦ by
      ext
      exact congrFun hxy i
    exact ConcreteCategory.congr_hom hm PUnit.unit
  · intro x
    let xs : ((Discrete.functor fun i ↦ op (U i)) ⋙ F).sections :=
      ⟨fun ⟨i⟩ ↦ x i, by
        rintro ⟨i⟩ ⟨j⟩ f
        obtain rfl := Discrete.eq_of_hom f
        simp⟩
    let s := Types.coneOfSection xs.2
    refine ⟨hc.lift s PUnit.unit, ?_⟩
    funext i
    exact ConcreteCategory.congr_hom (hc.fac s ⟨i⟩) PUnit.unit

/-- If a presheaf sends arbitrary scheme coproducts to products and satisfies the sheaf
condition for every singleton cover belonging to a morphism precoverage, then it is a
sheaf for the generated topology. -/
lemma isSheaf_precoverage_of_bijective_sigma
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsJointlySurjectivePreserving P] [IsZariskiLocalAtSource P]
    (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    (hF : ∀ {ι : Type u} (U : ι → Scheme.{u}),
      Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x)
    (hsingle : ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S), P f → Surjective f →
      Presieve.IsSheafFor F (.singleton f)) :
    Presieve.IsSheaf (Scheme.precoverage P).toGrothendieck F := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro S 𝒰
  letI : PreservesLimit (Discrete.functor fun i ↦ op (𝒰.X i)) F :=
    preservesLimit_discrete_of_bijective_sigma F hF 𝒰.X
  letI : PreservesLimit
      (Discrete.functor fun ij : 𝒰.I₀ × 𝒰.I₀ ↦ op (pullback (𝒰.f ij.1) (𝒰.f ij.2))) F :=
    preservesLimit_discrete_of_bijective_sigma F hF _
  rw [← Presieve.isSheafFor_sigmaDesc_iff 𝒰.f (coproductIsCoproduct _)
    (Scheme.isUniversalColimit_coproduct 𝒰.X)]
  have hmem := 𝒰.mem₀
  rw [Scheme.ofArrows_mem_precoverage_iff] at hmem
  exact hsingle (Sigma.desc 𝒰.f) (IsZariskiLocalAtSource.sigmaDesc hmem.2)
    (inferInstanceAs (Surjective (Sigma.desc 𝒰.f)))

/-- The coproduct-and-singleton conditions imply the étale sheaf condition. -/
lemma isSheaf_etaleTopology_of_bijective_sigma
    (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    (hF : ∀ {ι : Type u} (U : ι → Scheme.{u}),
      Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x)
    (hsingle : ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S), Etale f → Surjective f →
      Presieve.IsSheafFor F (.singleton f)) :
    Presieve.IsSheaf Scheme.etaleTopology F :=
  isSheaf_precoverage_of_bijective_sigma @Etale F hF hsingle

/-- The coproduct-and-singleton conditions imply the fppf sheaf condition. -/
lemma isSheaf_fppfTopology_of_bijective_sigma
    (F : Scheme.{u}ᵒᵖ ⥤ Type v)
    (hF : ∀ {ι : Type u} (U : ι → Scheme.{u}),
      Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x)
    (hsingle : ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S), Flat f →
      LocallyOfFinitePresentation f → Surjective f →
      Presieve.IsSheafFor F (.singleton f)) :
    Presieve.IsSheaf Scheme.fppfTopology F := by
  exact isSheaf_precoverage_of_bijective_sigma
    (@Flat ⊓ @LocallyOfFinitePresentation) F hF
    (fun {_} {_} f hf hs ↦ hsingle f hf.1 hf.2 hs)

/-- A Zariski sheaf sends an arbitrary coproduct of schemes to the corresponding product
of types. This elementwise formulation has no smallness requirement on the indexing type
relative to the universe of values of the sheaf. -/
lemma bijective_sigma_of_isSheaf_zariskiTopology
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {ι : Type u} (U : ι → Scheme.{u}) :
    Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x := by
  have hcover : Presieve.IsSheafFor F (Presieve.ofArrows U (Sigma.ι U)) := by
    apply hF.isSheafFor
    exact (sigmaOpenCover U).mem_grothendieckTopology
  have hall : ∀ x : (i : ι) → F.obj (op (U i)),
      Presieve.Arrows.Compatible F (Sigma.ι U) x := by
    intro x i j Z gi gj hcomm
    by_cases hij : i = j
    · subst j
      have : gi = gj := by
        apply (cancel_mono (Sigma.ι U i)).mp
        exact hcomm
      subst gj
      rfl
    · let _ : IsEmpty Z := isEmpty_of_commSq_sigmaι_of_ne ⟨hcomm⟩ hij
      let ht := Presieve.isTerminal_of_isSheafFor_empty_presieve Z F (by
        rw [Presieve.ofArrows_of_isEmpty]
        apply hF.isSheafFor
        simpa using (Scheme.bot_mem_grothendieckTopology
          (P := @IsOpenImmersion) Z))
      exact ConcreteCategory.congr_hom
        (ht.hom_ext (↾fun _ : PUnit ↦ F.map gi.op (x i))
          (↾fun _ : PUnit ↦ F.map gj.op (x j))) PUnit.unit
  have hglue := (Presieve.isSheafFor_arrows_iff F (Sigma.ι U)).mp hcover
  constructor
  · intro a b hab
    obtain ⟨t, ht, htuniq⟩ := hglue (fun i ↦ F.map (Sigma.ι U i).op a) (hall _)
    exact (htuniq a fun _ ↦ rfl).trans
      (htuniq b fun i ↦ (congrFun hab i).symm).symm
  · intro x
    obtain ⟨t, ht, -⟩ := hglue x (hall x)
    exact ⟨t, funext ht⟩

/-- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (2), étale): let
$F$ be a presheaf on the category of schemes. Then $F$ is a sheaf for the étale topology if
and only if $F$ sends coproducts to products and the sheaf sequence
$F(S) \to F(S') \rightrightarrows F(S' \times_S S')$ is exact for every surjective étale
morphism $S' \to S$ of schemes. -/
theorem isSheaf_type_etaleTopology_iff_sigma (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.etaleTopology F ↔
      (∀ {ι : Type u} (U : ι → Scheme.{u}),
        Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x) ∧
        ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S), Etale f → Surjective f →
          Presieve.IsSheafFor F (.singleton f) := by
  constructor
  · intro h
    refine ⟨fun U ↦ bijective_sigma_of_isSheaf_zariskiTopology F
      (Presieve.isSheaf_of_le F Scheme.zariskiTopology_le_etaleTopology h) U, ?_⟩
    intro S' S f hf hs
    letI := hs
    apply h.isSheafFor_of_mem_precoverage
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩
  · rintro ⟨hcoprod, hsingle⟩
    exact isSheaf_etaleTopology_of_bijective_sigma F hcoprod hsingle

/-- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (2), fppf): let
$F$ be a presheaf on the category of schemes. Then $F$ is a sheaf for the fppf topology if
and only if $F$ sends coproducts to products and the sheaf sequence is exact for every fppf
(surjective, flat, locally of finite presentation) morphism $S' \to S$ of schemes. -/
theorem isSheaf_type_fppfTopology_iff_sigma (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.fppfTopology F ↔
      (∀ {ι : Type u} (U : ι → Scheme.{u}),
        Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x) ∧
        ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S), Flat f → LocallyOfFinitePresentation f →
          Surjective f → Presieve.IsSheafFor F (.singleton f) := by
  constructor
  · intro h
    refine ⟨fun U ↦ bijective_sigma_of_isSheaf_zariskiTopology F
      (Presieve.isSheaf_of_le F
        (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage) h) U, ?_⟩
    intro S' S f hf hlf hs
    letI := hs
    letI := hf
    letI := hlf
    apply h.isSheafFor_of_mem_precoverage
    exact f.singleton_mem_fppfPrecoverage
  · rintro ⟨hcoprod, hsingle⟩
    exact isSheaf_fppfTopology_of_bijective_sigma F hcoprod hsingle

/-- **Exercise 3.3.7** (`exer:sheaf-axiom-reduced-to-single-map`) ((1) ⟺ (2), fpqc): let
$F$ be a presheaf on the category of schemes. Then $F$ is a sheaf for the fpqc topology if
and only if $F$ sends coproducts to products and the sheaf sequence is exact for every
singleton fpqc covering $\{S' \to S\}$, i.e. every surjective flat morphism satisfying the
quasi-compactness condition of fpqc coverings.

Faithfulness caveat: the book says "every faithfully flat morphism" without this condition;
that stronger claim does not follow from its fpqc topology. See this section's COMMENTARY.md. -/
theorem isSheaf_type_fpqcTopology_iff_sigma (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf Scheme.fpqcTopology F ↔
      (∀ {ι : Type u} (U : ι → Scheme.{u}),
        Function.Bijective fun (x : F.obj (op (∐ U))) i ↦ F.map (Sigma.ι U i).op x) ∧
        ∀ ⦃S' S : Scheme.{u}⦄ (f : S' ⟶ S),
          Presieve.singleton f ∈ Scheme.fpqcPrecoverage S →
          Presieve.IsSheafFor F (.singleton f) := by
  constructor
  · intro h
    refine ⟨fun U ↦ bijective_sigma_of_isSheaf_zariskiTopology F
      (Presieve.isSheaf_of_le F Scheme.zariskiTopology_le_fpqcTopology h) U, ?_⟩
    intro S' S f hf
    exact h.isSheafFor_of_mem_precoverage hf
  · rintro ⟨hcoprod, hsingle⟩
    have het : Presieve.IsSheaf Scheme.etaleTopology F :=
      isSheaf_etaleTopology_of_bijective_sigma F hcoprod (by
        intro S' S f hf hs
        apply hsingle f
        apply Scheme.etalePrecoverage_le_fpqcPrecoverage
        change Presieve.singleton f ∈ Scheme.precoverage @Etale S
        rw [Scheme.singleton_mem_precoverage_iff]
        letI := hs
        exact ⟨f.surjective, hf⟩)
    have hzar : Presieve.IsSheaf Scheme.zariskiTopology F :=
      Presieve.isSheaf_of_le F Scheme.zariskiTopology_le_etaleTopology het
    rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
    refine ⟨hzar, ?_⟩
    intro R S f hf hs
    apply hsingle (Spec.map f)
    letI := hf
    letI := hs
    exact (Spec.map f).singleton_mem_fpqcPrecoverage

end AlgebraicGeometry

end ExerSheafAxiomReducedToSingleMap

section PropSchemesAreSheavesInFpqcTopology

open CategoryTheory AlgebraicGeometry

universe u

/- Supporting consequence of Proposition 3.3.8 (absolute fpqc case):
let $X$ be a scheme. Then $\Mor(-, X)$ is a sheaf on $\Sch_{\fpqc}$: the fpqc topology is
subcanonical. This is an instance in Mathlib. -/
example : Scheme.fpqcTopology.{u}.Subcanonical :=
  inferInstance

example (X : Scheme.{u}) : Presieve.IsSheaf Scheme.fpqcTopology (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.fpqcTopology) _

/-- Supporting consequence of Proposition 3.3.8 (the absolute étale case): the étale
topology on schemes is subcanonical — every representable presheaf
is an étale sheaf. -/
instance Scheme.subcanonical_etaleTopology : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_fpqcTopology

/- Supporting consequence of Proposition 3.3.8 (the absolute fppf
case): the fppf topology is likewise subcanonical (an instance in Mathlib). -/
example : Scheme.fppfTopology.{u}.Subcanonical :=
  inferInstance

/- **Proposition 3.3.8** (`prop:schemes-are-sheaves-in-fpqc-topology`) (the book's relative
statement): for a morphism of schemes $X \to S$, the presheaf $\Mor_S(-, X)$ on $\Sch/S$ is
a sheaf for the relative fpqc topology (and hence for the relative étale and fppf
topologies): the restricted topology on $\Sch/S$ of a subcanonical topology is
subcanonical. -/
example (S : Scheme.{u}) : (Scheme.fpqcTopology.over S).Subcanonical :=
  inferInstance

example (S : Scheme.{u}) (X : Over S) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology.over S) _

/- **Proposition 3.3.8** (`prop:schemes-are-sheaves-in-fpqc-topology`) (the relative
étale consequence): for a morphism of schemes `X ⟶ S`, the presheaf
`Mor_S(-, X)` is a sheaf for the relative étale topology. -/
example (S : Scheme.{u}) : (Scheme.etaleTopology.over S).Subcanonical :=
  inferInstance

example (S : Scheme.{u}) (X : Over S) :
    Presieve.IsSheaf (Scheme.etaleTopology.over S) (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.etaleTopology.over S) _

/- **Proposition 3.3.8** (`prop:schemes-are-sheaves-in-fpqc-topology`) (the relative fppf
consequence): for a morphism of schemes `X ⟶ S`, the presheaf `Mor_S(-, X)` is a sheaf
for the relative fppf topology. -/
example (S : Scheme.{u}) : (Scheme.fppfTopology.over S).Subcanonical :=
  inferInstance

example (S : Scheme.{u}) (X : Over S) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) _

end PropSchemesAreSheavesInFpqcTopology
