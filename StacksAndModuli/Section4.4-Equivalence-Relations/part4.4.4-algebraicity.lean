module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.2-examples-and-stabilizers»
public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.3-quotient-stacks-of-groupoids»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import StacksAndModuli.API.AlgebraicSpaceAtlasComposition
public import StacksAndModuli.API.PresheafFiberProductYoneda
public import StacksAndModuli.API.QuotientPresheafPresentation
public import StacksAndModuli.API.QuotientGeometricPresentation
public import StacksAndModuli.API.QuotientAffinePresentation
public import StacksAndModuli.API.SurjectiveEtaleSourceLocal

/-!
# Algebraicity of quotients by groupoids

This module formalizes **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`),
**Remark 4.4.14** (`rmk:algebraicity-of-quotients`) and the surrounding unlabelled remarks
and exercises of §4.4 (Equivalence relations and groupoids) of *Stacks and Moduli*,
section label
`subsec:equivalence-relations`.

The quotient stack `[U/R]` of a groupoid of presheaves is handled through the standard
local-equivalence criterion
`CategoryTheory.BasedFunctor.IsLocalStackification` of part 4.4.3: the target is a stack,
the map from the quotient prestack is fully faithful, and it is locally essentially
surjective. The sheaf quotient `U/R` is handled through
`AlgebraicGeometry.PresheafGroupoid.IsQuotientSheaf`.

Main results:
- `AlgebraicGeometry.PresheafGroupoid.isDeligneMumfordStack_of_isStackification` and
  `.isAlgebraicStack_of_isStackification`: `[U/R]` is a Deligne–Mumford (resp. algebraic)
  stack for an étale (resp. smooth) groupoid of algebraic spaces;
- `AlgebraicGeometry.PresheafGroupoid.representableWith_quotientPresentation_comp_of_isEtale`
  and `..._of_isSmooth`: `U → [U/R]` is an étale (resp. smooth) presentation;
- `AlgebraicGeometry.PresheafGroupoid.isAlgebraicSpace_of_isQuotientSheaf` and
  `.presheaf_toQuotientPresheaf_comp_of_isQuotientSheaf`: for an étale equivalence
  relation of schemes, `U/R` is an algebraic space and `U → U/R` an étale presentation.

The supporting declaration
`AlgebraicGeometry.PresheafGroupoid.exists_isStackification_quotientPrestack_of_presentation`
records the statement of the following unnumbered exercise: every algebraic stack with a
smooth presentation is a quotient stack `[U/R]`.

The block `ThmQuotientStackIsAlgebraic` additionally carries **Theorem 4.1.10**
(`thm:quotient-stack-is-algebraic`, §4.1; Algebraicity of Quotient Stacks), which lives
here rather than in §4.1 because it is *deduced* from Theorem 4.4.13 applied to the action
groupoid of Example 4.4.3 — the route advertised by the unlabelled remark "Quotient stacks
revisited" — and §4.1 cannot import §4.4:
- `AlgebraicGeometry.PresheafGroupoid.isAlgebraicStack_quotientPrestack_ofAction` and
  `.representableWith_quotientPresentation_comp_ofAction`: `[U/G]` is an algebraic stack
  and `U → [U/G]` is a smooth surjective presentation;
- `PresheafGroupoid.relativelyRepresentableWith_isAffineHom_quotientPresentation_comp_ofAction`:
  if `G → S` is affine, then `U → [U/G]` is affine;
- `AlgebraicGeometry.PresheafGroupoid.isAlgebraicStack_quotientPrestack_ofGroup` and
  the same for the classifying stack `BG = [S/G]`.

The block `CorFiniteQuotientAlgebraicSpace` likewise carries **Corollary 4.1.14**
(`cor:finite-quotient-algebraic-space`, §4.1):
`AlgebraicGeometry.PresheafGroupoid.isAlgebraicSpace_isQuotientSheaf_ofAction_of_free`, the
quotient of a scheme by a free action of a finite étale group scheme is an algebraic space.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmAlgebraicityOfGroupoidQuotients

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}} {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
  {i : 𝒢.quotientPrestack ⥤ᵇ 𝒳st}

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (1), `U → [U/R]`
is an étale presentation): let `R ⇉ U` be an étale groupoid of algebraic spaces and let
`i : [U/R]^pre → 𝒳` be a stackification. Then the projection `p : U → 𝒳 = [U/R]` is
representable, surjective and étale — an *étale presentation* of the quotient stack. -/
theorem representableWith_quotientPresentation_comp_of_isEtale [𝒢.IsEtale]
    [IsAlgebraicSpace 𝒢.U] [IsAlgebraicSpace 𝒢.R]
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      (𝒢.quotientPresentation.comp i) := by
  apply representableWith_quotientPresentation_of_isLocalStackification
    (P := @Surjective ⊓ @Etale)
    le_rfl
    (fun ⦃S' S T⦄ p f hp ↦
      surjectiveEtale_iff_comp_of_surjectiveEtale
        (X' := S') (X := S) (Y := T) p f hp)
    hi IsAlgebraicSpace.isSheaf
  exact presheaf_surjective_inf_s IsEtale.presheaf_s

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (1), `U → [U/R]`
is a smooth presentation): let `R ⇉ U` be a smooth groupoid of algebraic spaces and let
`i : [U/R]^pre → 𝒳` be a stackification. Then the projection `p : U → 𝒳 = [U/R]` is
representable, surjective and smooth — a *smooth presentation* of the quotient stack. -/
theorem representableWith_quotientPresentation_comp_of_isSmooth [𝒢.IsSmooth]
    [IsAlgebraicSpace 𝒢.U] [IsAlgebraicSpace 𝒢.R]
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
      (𝒢.quotientPresentation.comp i) := by
  apply representableWith_quotientPresentation_of_isLocalStackification
    (P := @Surjective ⊓ @Smooth)
    (inf_le_inf le_rfl etale_le_smooth)
    (fun ⦃S' S T⦄ p f hp ↦
      surjectiveSmooth_iff_comp_of_surjectiveEtale
        (X' := S') (X := S) (Y := T) p f hp)
    hi IsAlgebraicSpace.isSheaf
  exact presheaf_surjective_inf_s IsSmooth.presheaf_s

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (1), étale case;
Algebraicity of Quotients by Groupoids): let `R ⇉ U` be an étale groupoid of algebraic
spaces and let `i : [U/R]^pre → 𝒳` be a stackification, so that `𝒳 = [U/R]`. Then `𝒳` is
a Deligne–Mumford stack.

The morphism `U → 𝒳` is supplied by
`representableWith_quotientPresentation_comp_of_isEtale`.  Composing it with an étale
scheme presentation of the algebraic space `U` gives the required scheme presentation
of `𝒳`; the target is a stack by the stackification hypothesis. -/
theorem isDeligneMumfordStack_of_isStackification [𝒢.IsEtale] [IsAlgebraicSpace 𝒢.U]
    [IsAlgebraicSpace 𝒢.R]
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    IsDeligneMumfordStack 𝒳st := by
  let _ : 𝒳st.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  refine ⟨hi.isStack, ?_⟩
  obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := 𝒢.U)
  have hp := representableWith_quotientPresentation_comp_of_isEtale hi
  exact ⟨U, _, hp.comp_algebraicSpacePresentation hq
    (fun {S' S T} p f hp ↦
      surjectiveEtale_iff_comp_of_surjectiveEtale (X' := S') (X := S) (Y := T) p f hp)⟩

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (1), smooth case;
Algebraicity of Quotients by Groupoids): let `R ⇉ U` be a smooth groupoid of algebraic
spaces and let `i : [U/R]^pre → 𝒳` be a stackification, so that `𝒳 = [U/R]`. Then `𝒳` is
an algebraic stack. -/
theorem isAlgebraicStack_of_isStackification [𝒢.IsSmooth] [IsAlgebraicSpace 𝒢.U]
    [IsAlgebraicSpace 𝒢.R]
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    IsAlgebraicStack 𝒳st := by
  let _ : 𝒳st.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  refine ⟨hi.isStack, ?_⟩
  obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := 𝒢.U)
  have hp := representableWith_quotientPresentation_comp_of_isSmooth hi
  exact ⟨U, _, hp.comp_algebraicSpacePresentation hq
    (fun {S' S T} p f hp ↦
      surjectiveSmooth_iff_comp_of_surjectiveEtale (X' := S') (X := S) (Y := T) p f hp)⟩

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (2), `U → U/R` is
an étale presentation): let `R ⇉ U` be an étale equivalence relation of schemes and let
`(X, q)` be a quotient sheaf `U/R`. Then the projection `U → U/R` is representable by
schemes, surjective and étale — an *étale presentation* of the algebraic space `U/R`. -/
theorem presheaf_toQuotientPresheaf_comp_of_isQuotientSheaf [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation) [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) :
    MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      (𝒢.toQuotientPresheaf ≫ q) := by
  let P : MorphismProperty Scheme.{u} := @Surjective ⊓ @Etale
  let φ := 𝒢.toQuotientPresheaf ≫ q
  obtain ⟨U, ⟨rU⟩⟩ := Functor.IsRepresentable.has_representation (F := 𝒢.U)
  let eU : yoneda.obj U ≅ 𝒢.U := rU.toIso
  have hφe : yoneda.relativelyRepresentable (eU.hom ≫ φ) :=
    CategoryTheory.Functor.relativelyRepresentable.of_diag
      (relativelyRepresentable_quotientSheafDiagonal hER hq) (eU.hom ≫ φ)
  let hφrep : yoneda.relativelyRepresentable φ := by
    simpa using MorphismProperty.RespectsIso.precomp
      yoneda.relativelyRepresentable eU.inv (eU.hom ≫ φ) hφe
  apply MorphismProperty.relative_of_snd hφrep
  intro T g
  obtain ⟨T', p, hpEtale, hpSurjective, a, ha⟩ :=
    exists_etale_surjective_quotient_lift (𝒢 := 𝒢) hq (yonedaEquiv g)
  let c : 𝒢.quotientPresheaf.obj (op T') := Quot.mk _ a
  let gc : yoneda.obj T' ⟶ 𝒢.quotientPresheaf := yonedaEquiv.symm c
  have hgc : gc ≫ q = yoneda.map p ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rw [show yonedaEquiv gc = c by exact Equiv.apply_symm_apply _ c]
    change q.app (op T') (Quot.mk _ a) = g.app (op T') p
    exact ha.trans (yonedaEquiv_naturality g p)
  let h₀ := presheaf_toQuotientPresheaf hER
  let W := h₀.rep.pullback gc
  let fstW := h₀.rep.fst gc
  let sndW := h₀.rep.snd gc
  have hW : IsPullback fstW (yoneda.map sndW)
      𝒢.toQuotientPresheaf gc := h₀.rep.isPullback gc
  let _ : Mono q := quotientSheafComparison_mono hER hq
  have hWφ : IsPullback fstW (yoneda.map sndW)
      φ (yoneda.map p ≫ g) := by
    rw [← hgc]
    dsimp only [φ]
    have hsquare : fstW ≫ (𝒢.toQuotientPresheaf ≫ q) =
        yoneda.map sndW ≫ (gc ≫ q) := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ q) hW.w
    have hlimit : IsLimit (PullbackCone.mk fstW (yoneda.map sndW) hsquare) :=
      PullbackCone.isLimitOfCompMono
        𝒢.toQuotientPresheaf gc q hW.cone hW.isLimit
    exact IsPullback.mk ⟨hsquare⟩ ⟨hlimit⟩
  let g' : yoneda.obj T' ⟶ X := yoneda.map p ≫ g
  let eWZPresheaf : yoneda.obj W ≅ yoneda.obj (hφrep.pullback g') :=
    hWφ.isoIsPullback _ _ (hφrep.isPullback g')
  let eWZ : W ≅ hφrep.pullback g' := yoneda.preimageIso eWZPresheaf
  have heWZ_snd : eWZ.hom ≫ hφrep.snd g' = sndW := by
    apply yoneda.map_injective
    change yoneda.map eWZ.hom ≫ yoneda.map (hφrep.snd g') = yoneda.map sndW
    rw [← Functor.map_comp]
    change yoneda.map (yoneda.preimage eWZPresheaf.hom ≫ hφrep.snd g') = _
    rw [Functor.map_comp, yoneda.map_preimage]
    exact hWφ.isoIsPullback_hom_snd _ _ (hφrep.isPullback g')
  have hlocal : P (hφrep.snd g') := by
    rw [← P.cancel_left_of_respectsIso eWZ.hom]
    rw [heWZ_snd]
    exact h₀.property_snd gc
  have hlift_eq : hφrep.fst g' ≫ φ =
      yoneda.map (hφrep.snd g' ≫ p) ≫ g := by
    simpa only [g', Functor.map_comp, Category.assoc] using hφrep.w g'
  let l : hφrep.pullback g' ⟶ hφrep.pullback g :=
    hφrep.lift (hφrep.fst g') (hφrep.snd g' ≫ p) hlift_eq
  have houter : IsPullback
      (yoneda.map l ≫ hφrep.fst g) (yoneda.map (hφrep.snd g'))
      φ (yoneda.map p ≫ g) := by
    change IsPullback
      (yoneda.map (hφrep.lift (hφrep.fst g')
        (hφrep.snd g' ≫ p) hlift_eq) ≫ hφrep.fst g)
      (yoneda.map (hφrep.snd g')) φ (yoneda.map p ≫ g)
    rw [hφrep.lift_fst]
    exact hφrep.isPullback g'
  have hbaseMap : IsPullback (yoneda.map l) (yoneda.map (hφrep.snd g'))
      (yoneda.map (hφrep.snd g)) (yoneda.map p) := by
    apply houter.of_right
    · rw [← Functor.map_comp, ← Functor.map_comp]
      change yoneda.map
        (hφrep.lift (hφrep.fst g') (hφrep.snd g' ≫ p) hlift_eq ≫
          hφrep.snd g) = yoneda.map (hφrep.snd g' ≫ p)
      rw [hφrep.lift_snd]
    · exact hφrep.isPullback g
  have hbase : IsPullback l (hφrep.snd g') (hφrep.snd g) p := by
    apply IsPullback.of_map yoneda
    · exact hφrep.lift_snd _ _ _
    · exact hbaseMap
  have hp : P p := ⟨hpSurjective, hpEtale⟩
  have hl : P l := MorphismProperty.of_isPullback hbase.flip hp
  apply (surjectiveEtale_iff_comp_of_surjectiveEtale l (hφrep.snd g) hl).2
  rw [hbase.w]
  exact P.comp_mem _ _ hlocal hp

/-- **Theorem 4.4.13** (`thm:algebraicity-of-groupoid-quotients`) (part (2); Algebraicity
of Quotients by Groupoids): let `R ⇉ U` be an étale equivalence relation of schemes and
let `(X, q)` be a quotient sheaf `U/R` (an étale sheaf receiving the quotient presheaf by
a locally bijective map). Then `X` is an algebraic space.

The quotient-sheaf hypothesis supplies the sheaf condition, while
`presheaf_toQuotientPresheaf_comp_of_isQuotientSheaf` supplies a surjective étale map
`U → X`.  Transporting that map across a chosen representation of `U` by a scheme gives
the required étale scheme presentation of `X`. -/
theorem isAlgebraicSpace_of_isQuotientSheaf [𝒢.IsEtale]
    (hER : 𝒢.IsEquivalenceRelation) [𝒢.U.IsRepresentable] [𝒢.R.IsRepresentable]
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} {q : 𝒢.quotientPresheaf ⟶ X}
    (hq : 𝒢.IsQuotientSheaf X q) : IsAlgebraicSpace X := by
  refine ⟨hq.isSheaf, ?_⟩
  obtain ⟨U, ⟨r⟩⟩ := Functor.IsRepresentable.has_representation (F := 𝒢.U)
  let e : yoneda.obj U ≅ 𝒢.U := r.toIso
  let p := 𝒢.toQuotientPresheaf ≫ q
  have hp : MorphismProperty.presheaf
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p :=
    presheaf_toQuotientPresheaf_comp_of_isQuotientSheaf hER hq
  refine ⟨U, e.hom ≫ p, ?_⟩
  exact MorphismProperty.RespectsIso.precomp
    ((@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}).presheaf) e.hom p hp

end AlgebraicGeometry.PresheafGroupoid

end ThmAlgebraicityOfGroupoidQuotients

section RmkAlgebraicityOfQuotients

/- Deferred content from Remark 4.4.14: the quotient `U/R` of an étale
equivalence relation of *algebraic spaces* is again an algebraic space (Corollary 5.5.12,
`cor:algebraicity-of-smooth-equivalence-relations-of-algebraic-spaces`, §5.5): one does
not obtain new objects by considering sheaves which are étale-locally algebraic spaces.
That result is delayed until §5.5 (`sec:when-are-algebraic-spaces-schemes`) since it takes
more work to show that the diagonal of `U/R` is representable by *schemes*. More
generally, if `R ⇉ U` is an fppf groupoid (resp. fppf equivalence relation) of algebraic
spaces — the mixin `AlgebraicGeometry.PresheafGroupoid.IsFppf` — then `[U/R]` is an
algebraic stack (resp. `U/R` is an algebraic space); see Corollary 7.3.6,
`cor:algebraicity-of-fppf-equivalence-relations-and-groupoids` (§7.3). Neither corollary
is stated here; both belong to their own sections. -/

/- **Subsection 4.4** (`subsec:equivalence-relations`) (the unlabelled remark "Quotient
stacks revisited" following the proof of Theorem 4.4.13): as a consequence of
`thm:algebraicity-of-groupoid-quotients`, the hypothesis in Algebraicity of Quotient
Stacks (Theorem 4.1.10, `thm:quotient-stack-is-algebraic`, §4.1) that the group scheme
`G → S` be affine is not necessary for the quotient stack `[X/G]` or the classifying
stack `BG` to be algebraic. This is exactly the form in which Theorem 4.1.10 is stated
here: the section block `ThmQuotientStackIsAlgebraic` below deduces it from Theorem 4.4.13
applied to the action groupoid `G ×_S U ⇉ U` of Example 4.4.3, with no affineness
hypothesis. (The §3.4/§4.1 quotient prestack `[X/G]^pre` built from principal bundles is a
different — equivalent — rendering, over `Sch/S` rather than `Sch`; comparing the two is
recorded in this section's COMMENTARY.) -/

-- Both halves of Remark 4.4.14 are forward pointers: Corollary 5.5.12 belongs to §5.5 and
-- Corollary 7.3.6 to §7.3. The "quotient stacks revisited" strengthening is now realized
-- by the `ThmQuotientStackIsAlgebraic` block below. Deliberately part-prose in the sense
-- of AGENTS.md.
-- STATUS: remark-complete

end RmkAlgebraicityOfQuotients

section ThmQuotientStackIsAlgebraic

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {S G U₀ : Scheme.{u}} (πG : G ⟶ S) (πU : U₀ ⟶ S) (m : pullback πG πG ⟶ G)
  (eG : S ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 S)
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- The explicit fiber product of two representable presheaves of schemes is an algebraic
space: it is represented by the pullback (`CategoryTheory.Presheaf.fiberProductYonedaIso`),
and schemes are algebraic spaces. -/
lemma isAlgebraicSpace_fiberProduct_yoneda {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsAlgebraicSpace (Presheaf.fiberProduct (yoneda.map f) (yoneda.map g)) :=
  IsAlgebraicSpace.of_iso (Presheaf.fiberProductYonedaIso f g)

/-- **Theorem 4.1.10** (`thm:quotient-stack-is-algebraic`) (Algebraicity of Quotient
Stacks; §4.1): let `G → S` be a smooth group scheme acting on an `S`-scheme `U`, and let
`i : [U/G]^pre → 𝒳` be a stackification of the quotient prestack of the action groupoid
`G ×_S U ⇉ U` (Example 4.4.3), so that `𝒳 = [U/G]`. Then `𝒳` is
an algebraic stack.

The book proves this in §4.1 by hand, from the principal-bundle description of `[U/G]`;
here it is deduced from Theorem 4.4.13 applied
to the action groupoid, which is smooth because `G → S` is (`ofAction_isSmooth`) and whose
source and target are algebraic spaces because they are schemes. This is the route the
unlabelled remark "Quotient stacks revisited" following Theorem 4.4.13 advertises; in
particular the hypothesis of Theorem 4.1.10 that `G → S` be *affine* is not needed for
algebraicity. See this section's COMMENTARY (`[deviation]`, `[decision]`). -/
theorem isAlgebraicStack_quotientPrestack_ofAction [Smooth πG]
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    IsAlgebraicStack 𝒳st := by
  have := ofAction_isSmooth πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul
    hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one
  have : IsAlgebraicSpace (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc
      hm_one_mul hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one).U :=
    inferInstanceAs (IsAlgebraicSpace (yoneda.obj U₀))
  have : IsAlgebraicSpace (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc
      hm_one_mul hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one).R :=
    isAlgebraicSpace_fiberProduct_yoneda πG πU
  exact isAlgebraicStack_of_isStackification hi

/-- **Theorem 4.1.10** (`thm:quotient-stack-is-algebraic`) (`U → [U/G]` is a smooth
surjective presentation): in the situation above, the projection `U → 𝒳 = [U/G]` is
representable by schemes, surjective and smooth.

Deduced, like the algebraicity itself, from Theorem 4.4.13
(`representableWith_quotientPresentation_comp_of_isSmooth`). -/
theorem representableWith_quotientPresentation_comp_ofAction [Smooth πG]
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
      ((ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
        hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPresentation.comp i) := by
  have := ofAction_isSmooth πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul
    hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one
  have : IsAlgebraicSpace (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc
      hm_one_mul hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one).U :=
    inferInstanceAs (IsAlgebraicSpace (yoneda.obj U₀))
  have : IsAlgebraicSpace (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc
      hm_one_mul hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one).R :=
    isAlgebraicSpace_fiberProduct_yoneda πG πU
  exact representableWith_quotientPresentation_comp_of_isSmooth hi

/-- **Theorem 4.1.10** (`thm:quotient-stack-is-algebraic`) (`U → [U/G]` is affine, hence a
principal `G`-bundle): if in addition `G → S` is *affine*, then the presentation
`U → 𝒳 = [U/G]` is an affine morphism.

This is the clause of Theorem 4.1.10 that genuinely needs the affineness hypothesis, and it
is the one Theorem 4.4.13 does not supply. The source of the action groupoid is affine by
`ofAction_s_isAffine`. The proof constructs every scheme-valued fiber of `U → 𝒳` from
the local quotient chart, descends that chart along its surjective étale cover using
effective descent for affine schemes, and applies the resulting affine-fiber criterion.
See this section's COMMENTARY (`[deviation]`). -/
theorem relativelyRepresentableWith_isAffineHom_quotientPresentation_comp_ofAction [Smooth πG]
    [IsAffineHom πG] {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    BasedFunctor.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u})
      ((ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
        hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPresentation.comp i) := by
  apply relativelyRepresentableWith_isAffineHom_quotientPresentation_of_isLocalStackification
    hi
  · change Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj U₀)
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  · exact ofAction_s_isAffine πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul
      hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one

/-- **Theorem 4.1.10** (`thm:quotient-stack-is-algebraic`) (the classifying stack): for a
smooth group scheme `G → S`, the classifying stack `BG = [S/G]` — the stackification of the
quotient prestack of the groupoid `G ⇉ S` (Example 4.4.3, the
special case `U = S` of the action groupoid) — is an algebraic stack.

This is the "in particular" clause of Theorem 4.1.10, the case of the trivial action of `G`
on `S`. -/
theorem isAlgebraicStack_quotientPrestack_ofGroup [Smooth πG]
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofGroup πG m eG ι hm heG hι hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    IsAlgebraicStack 𝒳st :=
  isAlgebraicStack_quotientPrestack_ofAction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi

/-- Supporting specialization of Theorem 4.1.10: the tautological morphism `S → BG`
from the base is representable by
schemes, surjective and smooth. -/
theorem representableWith_quotientPresentation_comp_ofGroup [Smooth πG]
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofGroup πG m eG ι hm heG hι hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
      ((ofGroup πG m eG ι hm heG hι hm_assoc hm_one_mul hm_mul_one hm_inv_mul
        hm_mul_inv).quotientPresentation.comp i) :=
  representableWith_quotientPresentation_comp_ofAction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi

end AlgebraicGeometry.PresheafGroupoid

end ThmQuotientStackIsAlgebraic

section CorFiniteQuotientAlgebraicSpace

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {S G U₀ : Scheme.{u}} (πG : G ⟶ S) (πU : U₀ ⟶ S) (m : pullback πG πG ⟶ G)
  (eG : S ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 S)
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- **Corollary 4.1.14** (`cor:finite-quotient-algebraic-space`, §4.1): let `G → S` be a
finite étale group scheme acting *freely* on an `S`-scheme `U`, and let `(X, q)` be a
quotient sheaf `U/G` for the action groupoid. Then `X` is an algebraic space.

Freeness is stated on `T`-points: two elements of `G(T)` moving a point of `U(T)` to the
same place agree. It makes the action groupoid an equivalence relation
(`ofAction_isEquivalenceRelation`), and the group scheme being étale makes it an étale
groupoid (`ofAction_isEtale`), so part (2) of Theorem 4.4.13
(`isAlgebraicSpace_of_isQuotientSheaf`) applies. This is exactly the book's proof, which
reads the free quotient stack as a sheaf and appeals to Theorem 4.1.10; here the sheaf and
the equivalence relation are the primitive objects.

The book states the corollary for a *finite abstract group* `G` regarded as a constant
group scheme over `S`, which is a special case: such a `G → S` is finite and étale. The
constant group scheme is not constructed in the library, so the hypothesis is carried in
the finite-étale form; `IsFinite` is not used by this proof, only `Etale`. See this
section's COMMENTARY. -/
theorem isAlgebraicSpace_isQuotientSheaf_ofAction_of_free [Etale πG] [IsFinite πG]
    (hfree : ∀ {T : Scheme.{u}} (g g' : T ⟶ G) (u : T ⟶ U₀) (h : g ≫ πG = u ≫ πU)
      (h' : g' ≫ πG = u ≫ πU),
      pullback.lift g u h ≫ σ = pullback.lift g' u h' ≫ σ → g = g')
    {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    {q : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPresheaf ⟶ X}
    (hq : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).IsQuotientSheaf X q) :
    IsAlgebraicSpace X := by
  have := ofAction_isEtale πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul
    hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one
  have : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
        hm_inv_mul hm_mul_inv hσ_mul hσ_one).U.IsRepresentable :=
    inferInstanceAs ((yoneda.obj U₀).IsRepresentable)
  have : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
        hm_inv_mul hm_mul_inv hσ_mul hσ_one).R.IsRepresentable :=
    inferInstanceAs
      ((Presheaf.fiberProduct (yoneda.map πG) (yoneda.map πU)).IsRepresentable)
  exact isAlgebraicSpace_of_isQuotientSheaf
    (ofAction_isEquivalenceRelation πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul
      hm_mul_one hm_inv_mul hm_mul_inv hσ_mul hσ_one hfree) hq

end AlgebraicGeometry.PresheafGroupoid

end CorFiniteQuotientAlgebraicSpace

section ExerStackIsQuotientOfGroupoid

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

/-- The self-intersection of a representable presentation is represented by an algebraic
space.  This is the representability clause of the presentation, evaluated at the
presentation itself. -/
theorem exists_isAlgebraicSpace_selfIntersection_of_presentation
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {U₀ : Scheme.{u}}
    {F : overBased U₀ ⥤ᵇ 𝒳}
    (hF : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F) :
    ∃ R : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace R ∧
      (BasedCategory.fiberProduct F F).IsRepresentedByPresheaf R :=
  hF.representable U₀ F

/-- Every scheme chart of the self-intersection of a smooth presentation maps
surjectively and smoothly to the presentation scheme.  This is the source-map geometry of
the kernel-pair groupoid before a strict presheaf groupoid structure is chosen. -/
theorem selfIntersection_chart_isSurjectiveSmooth_of_presentation
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {U₀ : Scheme.{u}}
    {F : overBased U₀ ⥤ᵇ 𝒳}
    (hF : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F)
    {R : Scheme.{u}ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace R)
    (E : ofPresheaf R ⥤ᵇ BasedCategory.fiberProduct F F)
    (hE : E.toFunctor.IsEquivalence) (V : Scheme.{u}) (q : yoneda.obj V ⟶ R)
    (hq : MorphismProperty.presheaf
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) q) :
    (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
      ((overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map q).comp
        (E.comp (BasedCategory.fiberProductSnd F F)))).overHom :=
  hF.2 U₀ F R hR E hE V q hq

/-- Statement of the unnumbered exercise following the "Quotient stacks revisited"
remark: let
`𝒳` be an algebraic stack and let `p : U₀ → 𝒳` be a smooth presentation by a scheme. Then
`𝒳` is isomorphic to the quotient stack `[U/R]` of the smooth groupoid
`R = U ×_𝒳 U ⇉ U`: there is a groupoid of presheaves `𝒢` with `𝒢.U` the functor of
points of `U₀` and `𝒢.R` representing the fiber product `U ×_𝒳 U`, such that `𝒳` is a
stackification of the quotient prestack `[U/𝒢]^pre`. (The analogous statement for an
algebraic space `𝒳` produces the quotient sheaf `U/R` of an étale equivalence
relation.)

The proof now obtains an algebraic-space presheaf representation of `U ×_𝒳 U` and a
surjective smooth scheme chart of its projection to `U` directly from `hF`.  The remaining
obligation is to strictify that fiber-product prestack into the pointwise
`PresheafGroupoid` used in this section, coherently transport composition, identity and
inverse, and compare its quotient prestack with `𝒳`. -/
theorem exists_isStackification_quotientPrestack_of_presentation
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳] {U₀ : Scheme.{u}}
    {F : overBased U₀ ⥤ᵇ 𝒳}
    (hF : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F) :
    ∃ 𝒢 : PresheafGroupoid.{u}, 𝒢.U = yoneda.obj U₀ ∧
      (BasedCategory.fiberProduct F F).IsRepresentedByPresheaf 𝒢.R ∧
      ∃ i : 𝒢.quotientPrestack ⥤ᵇ 𝒳, i.IsStackification Scheme.etaleTopology := by
  obtain ⟨R, hR, hRrep⟩ :=
    exists_isAlgebraicSpace_selfIntersection_of_presentation hF
  obtain ⟨E, hE⟩ := hRrep
  obtain ⟨V, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := R)
  have hsource := selfIntersection_chart_isSurjectiveSmooth_of_presentation
    hF hR E hE V q hq
  -- The represented kernel pair is now available.  What remains is the strictification
  -- of its categorical groupoid structure through `E` and its quotient comparison.
  sorry

end AlgebraicGeometry.PresheafGroupoid

end ExerStackIsQuotientOfGroupoid
