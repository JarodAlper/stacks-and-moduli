module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Precomposition maps between Quot functors

An epimorphism of ambient sheaves `G ⟶ F` sends a quotient of `F` to the
composite quotient of `G`.  This file packages that operation first on literal
quotient data and then as natural transformations on the polynomial-free and
fixed-Hilbert-polynomial Quot functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

variable {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}
  {T T' : Over S}

/-- The pullback to the total space over `T` of a map between ambient sheaves. -/
noncomputable def ambientMap (p : G ⟶ F) (T : Over S) :
    (Modules.pullback ((Over.pullback f).obj T).hom).obj G ⟶
      (Modules.pullback ((Over.pullback f).obj T).hom).obj F :=
  (Modules.pullback ((Over.pullback f).obj T).hom).map p

instance ambientMap_epi (p : G ⟶ F) [Epi p] (T : Over S) :
    Epi (ambientMap (f := f) p T) := by
  dsimp [ambientMap]
  infer_instance

/-- Precompose a quotient presentation with an epimorphism of ambient sheaves. -/
noncomputable def precomp (p : G ⟶ F) [Epi p]
    (x : QuotientPullbackData F f T) : QuotientPullbackData G f T where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isFinitePresentation := x.isFinitePresentation
  flatOver := x.flatOver
  π := ambientMap (f := f) p T ≫ x.π
  epi := by
    haveI : Epi x.π := x.epi
    infer_instance

/-- Precomposition preserves equivalence of quotient presentations. -/
lemma precomp_r (p : G ⟶ F) [Epi p]
    {x y : QuotientPullbackData F f T}
    (h : (QuotientPullbackData.setoid F f T).r x y) :
    (QuotientPullbackData.setoid G f T).r (x.precomp p) (y.precomp p) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by simp only [precomp, Category.assoc, he]⟩

/-- Because the ambient map is epic, equivalence after precomposition already
implies equivalence before precomposition. -/
lemma precomp_r_iff (p : G ⟶ F) [Epi p]
    (x y : QuotientPullbackData F f T) :
    (QuotientPullbackData.setoid G f T).r (x.precomp p) (y.precomp p) ↔
      (QuotientPullbackData.setoid F f T).r x y := by
  constructor
  · rintro ⟨e, he⟩
    change x.Q ≅ y.Q at e
    change (ambientMap (f := f) p T ≫ x.π) ≫ e.hom =
      ambientMap (f := f) p T ≫ y.π at he
    refine ⟨e, ?_⟩
    rw [← cancel_epi (ambientMap (f := f) p T)]
    simpa only [Category.assoc] using he
  · exact precomp_r p

/-- The projection descended through an ambient epimorphism. -/
noncomputable def descendedProjection (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0) :
    (Modules.pullback ((Over.pullback f).obj T).hom).obj F ⟶ y.Q :=
  Abelian.epiDesc (ambientMap (f := f) p T) y.π h

@[reassoc]
lemma ambientMap_comp_descendedProjection (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0) :
    ambientMap (f := f) p T ≫ descendedProjection p y h = y.π :=
  Abelian.comp_epiDesc _ _ h

lemma descendedProjection_epi (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0) :
    Epi (descendedProjection p y h) := by
  haveI : Epi y.π := y.epi
  exact epi_of_epi_fac (ambientMap_comp_descendedProjection p y h)

/-- If a quotient of `G_T` kills the kernel of `G_T ⟶ F_T`, descend its
projection uniquely to a quotient of `F_T`. -/
noncomputable def descendPrecomp (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0) :
    QuotientPullbackData F f T where
  Q := y.Q
  isQuasicoherent := y.isQuasicoherent
  isFinitePresentation := y.isFinitePresentation
  flatOver := y.flatOver
  π := descendedProjection p y h
  epi := descendedProjection_epi p y h

/-- Descending a presentation and then precomposing recovers the original
presentation up to the Quot equivalence. -/
lemma precomp_descendPrecomp_r (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0) :
    (QuotientPullbackData.setoid G f T).r
      ((y.descendPrecomp p h).precomp p) y := by
  refine ⟨Iso.refl _, ?_⟩
  change (ambientMap (f := f) p T ≫ descendedProjection p y h) ≫ 𝟙 y.Q = y.π
  rw [Category.comp_id, ambientMap_comp_descendedProjection]

/-- A precomposed quotient kills the pulled-back kernel of the ambient
epimorphism. -/
lemma kernel_ι_comp_precomp_π (p : G ⟶ F) [Epi p]
    (x : QuotientPullbackData F f T) :
    kernel.ι (ambientMap (f := f) p T) ≫ (x.precomp p).π = 0 := by
  change kernel.ι (ambientMap (f := f) p T) ≫
    (ambientMap (f := f) p T ≫ x.π) = 0
  rw [← Category.assoc, kernel.condition, zero_comp]

/-- A literal quotient presentation of `G_T` lies in the essential image of
precomposition exactly when it kills the pulled-back kernel of `G ⟶ F`. -/
lemma exists_precomp_r_iff_kernel_ι_comp_eq_zero (p : G ⟶ F) [Epi p]
    (y : QuotientPullbackData G f T) :
    (∃ x : QuotientPullbackData F f T,
      (QuotientPullbackData.setoid G f T).r (x.precomp p) y) ↔
      kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0 := by
  constructor
  · rintro ⟨x, e, he⟩
    calc
      kernel.ι (ambientMap (f := f) p T) ≫ y.π =
          kernel.ι (ambientMap (f := f) p T) ≫
            ((x.precomp p).π ≫ e.hom) := by rw [he]
      _ = (kernel.ι (ambientMap (f := f) p T) ≫
            (x.precomp p).π) ≫ e.hom := by rw [Category.assoc]
      _ = 0 := by rw [kernel_ι_comp_precomp_π, zero_comp]
  · intro h
    exact ⟨y.descendPrecomp p h, precomp_descendPrecomp_r p y h⟩

/-- Killing the ambient kernel is invariant under equivalence of quotient
presentations. -/
lemma kernel_ι_comp_eq_zero_iff_of_r (p : G ⟶ F) [Epi p]
    {y y' : QuotientPullbackData G f T}
    (h : (QuotientPullbackData.setoid G f T).r y y') :
    kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0 ↔
      kernel.ι (ambientMap (f := f) p T) ≫ y'.π = 0 := by
  obtain ⟨e, he⟩ := h
  constructor
  · intro hy
    rw [← he, ← Category.assoc, hy, zero_comp]
  · intro hy'
    rw [← cancel_mono e.hom]
    rw [zero_comp, Category.assoc, he, hy']

/-- Pullback commutes with precomposition, up to equivalence of quotient
presentations. -/
lemma pullback_precomp_r (p : G ⟶ F) [Epi p]
    (g : T' ⟶ T) (x : QuotientPullbackData F f T) :
    (QuotientPullbackData.setoid G f T').r
      ((x.precomp p).pullback g) ((x.pullback g).precomp p) := by
  refine ⟨Iso.refl _, ?_⟩
  simp [precomp, ambientMap, QuotientPullbackData.pullback,
    PullbackQuotient.pullbackComparison]

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}

/-- An epimorphism `G ⟶ F` induces a natural map from quotients of `F` to
quotients of `G` by precomposition. -/
noncomputable def quotFunctorPrecomp (p : G ⟶ F) [Epi p] :
    quotFunctor F f ⟶ quotFunctor G f where
  app _ := ↾fun z ↦ Quotient.map
    (Modules.QuotientPullbackData.precomp p)
    (fun _ _ h ↦ Modules.QuotientPullbackData.precomp_r p h) z
  naturality T T' g := by
    ext z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    exact Quotient.sound
      ((Modules.QuotientPullbackData.setoid G f _).symm
        (Modules.QuotientPullbackData.pullback_precomp_r p g.unop x))

/-- Precomposition by an epimorphism is injective on Quot classes. -/
theorem quotFunctorPrecomp_app_injective (p : G ⟶ F) [Epi p] (T : (Over S)ᵒᵖ) :
    Function.Injective ((quotFunctorPrecomp (f := f) p).app T) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Quotient.exists_rep x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep y
  apply Quotient.sound
  apply (Modules.QuotientPullbackData.precomp_r_iff p x y).mp
  exact Quotient.exact hxy

instance quotFunctorPrecomp_mono (p : G ⟶ F) [Epi p] :
    Mono (quotFunctorPrecomp (f := f) p) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  exact quotFunctorPrecomp_app_injective p T

/-- A Quot class of `G_T` kills the kernel of the ambient epimorphism if it has
a representative whose projection does so. -/
def QuotientClassKillsAmbientKernel (p : G ⟶ F) [Epi p] (T : Over S)
    (z : (quotFunctor G f).obj (op T)) : Prop :=
  ∃ y : Modules.QuotientPullbackData G f T,
    Quotient.mk _ y = z ∧
      kernel.ι (Modules.QuotientPullbackData.ambientMap (f := f) p T) ≫ y.π = 0

/-- The image of precomposition on Quot classes is exactly the zero condition
on the pulled-back kernel of the ambient epimorphism. -/
theorem mem_range_quotFunctorPrecomp_app_iff (p : G ⟶ F) [Epi p]
    (T : Over S) (z : (quotFunctor G f).obj (op T)) :
    z ∈ Set.range ((quotFunctorPrecomp (f := f) p).app (op T)) ↔
      QuotientClassKillsAmbientKernel p T z := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep w
    exact ⟨x.precomp p, rfl,
      Modules.QuotientPullbackData.kernel_ι_comp_precomp_π p x⟩
  · rintro ⟨y, hy, hzero⟩
    let x := y.descendPrecomp p hzero
    refine ⟨Quotient.mk _ x, ?_⟩
    change Quotient.mk _ (x.precomp p) = z
    rw [← hy]
    exact Quotient.sound
      (Modules.QuotientPullbackData.precomp_descendPrecomp_r p y hzero)

/-- Precomposition does not change the quotient sheaf, so it restricts to the
fixed-Hilbert-polynomial Quot functors. -/
noncomputable def quotFunctorPPrecomp {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) : quotFunctorP F P ⟶ quotFunctorP G P where
  app T := ↾fun z ↦ ⟨(quotFunctorPrecomp p).app T z.1, by
    obtain ⟨x, hx, hP⟩ := z.2
    refine ⟨x.precomp p, ?_, ?_⟩
    · rw [← hx]
      rfl
    · exact hP⟩
  naturality T T' g := by
    ext z
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((quotFunctorPrecomp p).naturality g) z.1

/-- Precomposition by an epimorphism is injective on fixed-polynomial Quot
classes. -/
theorem quotFunctorPPrecomp_app_injective {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) (T : (Over S)ᵒᵖ) :
    Function.Injective ((quotFunctorPPrecomp p P).app T) := by
  intro x y hxy
  apply Subtype.ext
  apply quotFunctorPrecomp_app_injective (f := Scheme.projectiveSpaceOverπ n S) p T
  exact congrArg Subtype.val hxy

instance quotFunctorPPrecomp_mono {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) : Mono (quotFunctorPPrecomp p P) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  exact quotFunctorPPrecomp_app_injective p P T

/-- The image of fixed-polynomial precomposition is cut out by the same zero
condition as the ambient Quot functor. -/
theorem mem_range_quotFunctorPPrecomp_app_iff {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) (T : Over S) (z : (quotFunctorP G P).obj (op T)) :
    z ∈ Set.range ((quotFunctorPPrecomp p P).app (op T)) ↔
      QuotientClassKillsAmbientKernel p T z.1 := by
  constructor
  · rintro ⟨w, rfl⟩
    apply (mem_range_quotFunctorPrecomp_app_iff
      (f := Scheme.projectiveSpaceOverπ n S) p T _).mp
    exact ⟨w.1, rfl⟩
  · intro hz
    obtain ⟨y, hy, hzero⟩ := hz
    obtain ⟨a, ha, hP⟩ := z.2
    have hrya : (Modules.QuotientPullbackData.setoid G
        (Scheme.projectiveSpaceOverπ n S) T).r y a :=
      Quotient.exact (hy.trans ha.symm)
    have hzeroa : kernel.ι
        (Modules.QuotientPullbackData.ambientMap
          (f := Scheme.projectiveSpaceOverπ n S) p T) ≫ a.π = 0 :=
      (Modules.QuotientPullbackData.kernel_ι_comp_eq_zero_iff_of_r p hrya).mp hzero
    let x := a.descendPrecomp p hzeroa
    let w : (quotFunctorP F P).obj (op T) :=
      ⟨Quotient.mk _ x, ⟨x, rfl, hP⟩⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change Quotient.mk _ (x.precomp p) = z.1
    rw [← ha]
    exact Quotient.sound
      (Modules.QuotientPullbackData.precomp_descendPrecomp_r p a hzeroa)

@[simp]
lemma quotFunctorPToQuotFunctor_naturality_precomp {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) :
    quotFunctorPPrecomp p P ≫ quotFunctorPToQuotFunctor G P =
      quotFunctorPToQuotFunctor F P ≫ quotFunctorPrecomp p := by
  ext T z
  rfl

/-! ## Relative closedness from the universal zero locus -/

/-- A closed subscheme of a base scheme which universally cuts out the condition that a
fixed quotient kills the pulled-back kernel of an ambient epimorphism.

This is a background definition for Exercise 1.3.15, applied to the kernel map into the
flat quotient sheaf. The definition deliberately records only the universal vanishing
property; the represented pullback square for Quot is derived below. -/
structure QuotientKernelZeroLocusData {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ) (T : Over S) (z : (quotFunctorP G P).obj (op T)) where
  /-- The zero locus, regarded as an `S`-scheme. -/
  Z : Over S
  /-- Its inclusion into the parameter scheme. -/
  ι : Z ⟶ T
  /-- The zero locus is a closed subscheme. -/
  isClosedImmersion : IsClosedImmersion ι.left
  /-- A base change factors through the zero locus exactly when the pulled-back quotient
  kills the pulled-back ambient kernel. -/
  factor_iff : ∀ (W : Over S) (g : W ⟶ T),
    QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 ↔
      ∃ h : W ⟶ Z, h ≫ ι = g

namespace QuotientKernelZeroLocusData

variable {n : ℕ} {F G : (Scheme.projectiveSpaceOver n S).Modules}
  (p : G ⟶ F) [Epi p] (P : Polynomial ℚ) {T : Over S}
  {z : (quotFunctorP G P).obj (op T)}

/-- The quotient pulled back to the zero locus kills the ambient kernel. -/
lemma kills_pullback (D : QuotientKernelZeroLocusData p P T z) :
    QuotientClassKillsAmbientKernel p D.Z
      (((quotFunctorP G P).map D.ι.op) z).1 := by
  rw [D.factor_iff]
  exact ⟨𝟙 D.Z, by simp⟩

/-- The descended quotient of `F` over the universal zero locus. -/
noncomputable def descendedQuotient (D : QuotientKernelZeroLocusData p P T z) :
    (quotFunctorP F P).obj (op D.Z) :=
  Classical.choose ((mem_range_quotFunctorPPrecomp_app_iff p P D.Z
    ((quotFunctorP G P).map D.ι.op z)).2 (D.kills_pullback p P))

/-- Precomposing the descended quotient gives the pullback of the original quotient. -/
lemma precomp_descendedQuotient (D : QuotientKernelZeroLocusData p P T z) :
    (quotFunctorPPrecomp p P).app (op D.Z) (D.descendedQuotient p P) =
      (quotFunctorP G P).map D.ι.op z :=
  Classical.choose_spec ((mem_range_quotFunctorPPrecomp_app_iff p P D.Z
    ((quotFunctorP G P).map D.ι.op z)).2 (D.kills_pullback p P))

/-- The first leg of the square represented by the universal zero locus. -/
noncomputable def fst (D : QuotientKernelZeroLocusData p P T z) :
    uliftYoneda.{u + 1}.obj D.Z ⟶ quotFunctorP F P :=
  uliftYonedaEquiv.{u + 1}.symm (D.descendedQuotient p P)

/-- The square from the universal zero locus to fixed-polynomial precomposition commutes. -/
lemma square (D : QuotientKernelZeroLocusData p P T z) :
    D.fst p P ≫ quotFunctorPPrecomp p P =
      uliftYoneda.map D.ι ≫ uliftYonedaEquiv.{u + 1}.symm z := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp,
    uliftYonedaEquiv_uliftYoneda_map]
  simp only [fst, Equiv.apply_symm_apply, uliftYonedaEquiv_symm_apply_app]
  exact D.precomp_descendedQuotient p P

/-- The universal zero-locus square is a pullback square of presheaves. -/
theorem isPullback (D : QuotientKernelZeroLocusData p P T z) :
    IsPullback (D.fst p P) (uliftYoneda.map D.ι)
      (quotFunctorPPrecomp p P) (uliftYonedaEquiv.{u + 1}.symm z) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app W) (D.square p P), ?_, ?_⟩
  · intro a b hab
    apply ULift.ext
    letI : IsClosedImmersion D.ι.left := D.isClosedImmersion
    letI : Mono D.ι := Over.mono_of_mono_left D.ι
    rw [← cancel_mono D.ι]
    exact congrArg ULift.down hab.2
  · rintro L ⟨g⟩ h
    have h' : (quotFunctorPPrecomp p P).app W L =
        (quotFunctorP G P).map g.op z := by
      exact h.trans (by rfl)
    have hrange : ((quotFunctorP G P).map g.op z) ∈
        Set.range ((quotFunctorPPrecomp p P).app (op (unop W))) := by
      refine ⟨L, ?_⟩
      exact h'
    have hkill : QuotientClassKillsAmbientKernel p (unop W)
        (((quotFunctorP G P).map g.op) z).1 :=
      (mem_range_quotFunctorPPrecomp_app_iff p P (unop W) _).mp hrange
    obtain ⟨a, ha⟩ := (D.factor_iff (unop W) g).mp hkill
    refine ⟨⟨a⟩, ?_, ?_⟩
    · apply (quotFunctorPPrecomp_app_injective p P W)
      have hs := ConcreteCategory.congr_hom (NatTrans.congr_app (D.square p P) W) ⟨a⟩
      change (quotFunctorPPrecomp p P).app W ((D.fst p P).app W ⟨a⟩) =
        (uliftYonedaEquiv.{u + 1}.symm z).app W ⟨a ≫ D.ι⟩ at hs
      rw [ha] at hs
      exact hs.trans h.symm
    · apply ULift.ext
      exact ha

end QuotientKernelZeroLocusData

/-- If the universal kernel-vanishing zero locus exists for every test quotient, then
precomposition on fixed-polynomial Quot functors is representable by closed immersions. -/
theorem quotFunctorPPrecomp_relative_closed {n : ℕ}
    {F G : (Scheme.projectiveSpaceOver n S).Modules} (p : G ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S) (z : (quotFunctorP G P).obj (op T)),
      Nonempty (QuotientKernelZeroLocusData p P T z)) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (quotFunctorPPrecomp p P) := by
  letI : (MorphismProperty.over
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :
      MorphismProperty (Over S)).RespectsIso := by
    change (MorphismProperty.inverseImage
      (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (Over.forget S)).RespectsIso
    exact MorphismProperty.RespectsIso.inverseImage
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro T g
  let z : (quotFunctorP G P).obj (op T) := uliftYonedaEquiv g
  let D : QuotientKernelZeroLocusData p P T z := Classical.choice (H T z)
  refine ⟨D.Z, D.fst p P, D.ι, ?_, D.isClosedImmersion⟩
  simpa only [z, Equiv.symm_apply_apply] using D.isPullback p P

/-- Projective representability descends along an ambient epimorphism once its universal
kernel-vanishing loci are represented by closed subschemes. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_precomp_zeroLoci
    {n : ℕ} {F G : (Scheme.projectiveSpaceOver n S).Modules}
    (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
    (H : ∀ (T : Over S) (z : (quotFunctorP G P).obj (op T)),
      Nonempty (QuotientKernelZeroLocusData p P T z))
    (hG : ∃ Q₀ : Over S,
      Nonempty ((quotFunctorP G P).RepresentableBy Q₀) ∧ IsHProjective Q₀.hom) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧ IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_of_relative_closed
    (quotFunctorPPrecomp p P) (quotFunctorPPrecomp_relative_closed p P H) hG

/-- A single kernel-vanishing zero locus on the universal quotient is enough to
represent the Quot functor of the target ambient sheaf.

This is the form used after the twisted-free Quot functor has already been
represented.  It avoids constructing zero-locus data independently over every
test scheme: the universal square is a pullback, and its right-hand map is the
representing isomorphism. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
    {n : ℕ} {F G : (Scheme.projectiveSpaceOver n S).Modules}
    (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
    (Q₀ : Over S) (eG : (quotFunctorP G P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom)
    (D : QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧ IsHProjective Q.hom := by
  let z : (quotFunctorP G P).obj (op Q₀) := eG.homEquiv (𝟙 Q₀)
  let eG' : uliftYoneda.{u + 1}.obj Q₀ ≅ quotFunctorP G P :=
    (Functor.RepresentableBy.equivUliftYonedaIso (quotFunctorP G P) Q₀) eG
  have hright_eq : uliftYonedaEquiv.{u + 1}.symm z = eG'.hom := by
    ext T y
    change (quotFunctorP G P).map y.down.op z = eG.homEquiv y.down
    simpa only [z, Category.comp_id] using
      (eG.homEquiv_comp y.down (𝟙 Q₀)).symm
  haveI hright : IsIso (uliftYonedaEquiv.{u + 1}.symm z) := by
    rw [hright_eq]
    infer_instance
  haveI hfst : IsIso (D.fst p P) :=
    (D.isPullback p P).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj D.Z ≅ quotFunctorP F P :=
    asIso (D.fst p P)
  let eF : (quotFunctorP F P).RepresentableBy D.Z :=
    (Functor.RepresentableBy.equivUliftYonedaIso (quotFunctorP F P) D.Z).symm eF'
  refine ⟨D.Z, ⟨eF⟩, ?_⟩
  obtain ⟨m, i, hi, hcomp⟩ := hQ₀
  refine ⟨m, D.ι.left ≫ i, ?_, ?_⟩
  · letI : IsClosedImmersion D.ι.left := D.isClosedImmersion
    letI : IsClosedImmersion i := hi
    infer_instance
  · rw [Category.assoc, hcomp, Over.w D.ι]

end AlgebraicGeometry.Scheme
