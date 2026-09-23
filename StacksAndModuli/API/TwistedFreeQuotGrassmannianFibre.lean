module

public import StacksAndModuli.API.FlatteningIntersection
public import StacksAndModuli.API.FreeGrassmannianImmersion
public import StacksAndModuli.API.QuotGrassmannianReconstruction
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Fibres of the twisted-free Quot-to-Grassmannian transformation

This file supplies the categorical last mile for the relative-immersion step in the
construction of the Hilbert and Quot schemes.  Suppose `α : F ⟶ G` is a monomorphism of
presheaves on schemes over `S`, and fix a point `g : T ⟶ G`.  To prove that the fibre of
`α` over `g` is represented by an immersion, it is enough to provide:

* an immersion `Z ⟶ T` (in the application, a finite intersection of flattening loci);
* the canonical reconstructed point `Z ⟶ F`;
* compatibility of that point with `g`; and
* the pointwise statement that every compatible `F`-point has base map factoring through
  `Z`.

Injectivity of `α` identifies an arbitrary compatible point with the canonical reconstructed
one.  Thus callers do not have to construct both coordinates of the pullback lift.  The
resulting square is a pullback pointwise in `Type`, and
`relative_over_isImmersion_of_fibreLoci` feeds these squares directly to
`MorphismProperty.relative.of_exists`.

For the twisted-free Quot application, `reconstructedQuotient'` provides the canonical
point, while `interOverFin` and the general-base flattening representatives provide `Z`.
The remaining geometric input is precisely the factorization criterion relating a quotient
in the fibre to those flattening conditions.

Main declarations:

* `AlgebraicGeometry.ImmersionFibreLocus`;
* `AlgebraicGeometry.ImmersionFibreLocus.isPullback_of_injective`;
* `AlgebraicGeometry.FiniteImmersionFibreLocus`;
* `AlgebraicGeometry.relative_over_isImmersion_of_fibreLoci`;
* `AlgebraicGeometry.relative_over_isImmersion_of_finiteFibreLoci`;
* `AlgebraicGeometry.relative_over_isImmersion_of_fibreLoci_of_mono`;
* `AlgebraicGeometry.Scheme.
  twistedFreeQuotHasFreeGrassmannianImmersion_of_quotientNatTrans_finiteFibreLoci`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)}

/-- Data identifying a fibre of a monomorphism of presheaves with an immersion locus.

The field `liftBase` is deliberately weaker than the full pullback lifting property: it only
asks that the *base map* of a compatible pair factor through the proposed locus.  The
canonical point `fst`, the commutative square, and pointwise injectivity of `α` then force the
`F`-coordinate of the lift.  This is the form naturally supplied by a flattening-locus
criterion. -/
structure ImmersionFibreLocus (α : F ⟶ G) (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ G) where
  /-- The proposed fibre locus, regarded as an object over `S`. -/
  obj : Over S
  /-- The canonical point of `F` on the fibre locus. -/
  fst : uliftYoneda.{u + 1}.obj obj ⟶ F
  /-- The structure map from the fibre locus to the test object. -/
  snd : obj ⟶ T
  /-- The canonical point maps to the pullback of the fixed point `g`. -/
  square : fst ≫ α = uliftYoneda.map snd ≫ g
  /-- The fibre locus is immersed in the test object. -/
  isImmersion : IsImmersion snd.left
  /-- Pointwise fibre criterion: the base arrow of every compatible pair factors through
  the proposed locus. -/
  liftBase : ∀ (Y : (Over S)ᵒᵖ) (x : F.obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y),
    α.app Y x = g.app Y a →
      ∃ z : (uliftYoneda.{u + 1}.obj obj).obj Y,
        (uliftYoneda.map snd).app Y z = a

namespace ImmersionFibreLocus

variable {α : F ⟶ G} {T : Over S} {g : uliftYoneda.{u + 1}.obj T ⟶ G}

/-- The actual pointwise fibre criterion supplied by an immersion locus: compatible pairs
are exactly the pairs induced from points of the locus.  The forward direction uses
injectivity of `α` to identify the given `F`-point with the canonical reconstructed point. -/
theorem compatible_iff_exists_of_injective (D : ImmersionFibreLocus α T g)
    (hα : ∀ Y, Function.Injective (α.app Y)) (Y : (Over S)ᵒᵖ)
    (x : F.obj Y) (a : (uliftYoneda.{u + 1}.obj T).obj Y) :
    α.app Y x = g.app Y a ↔
      ∃ z : (uliftYoneda.{u + 1}.obj D.obj).obj Y,
        D.fst.app Y z = x ∧ (uliftYoneda.map D.snd).app Y z = a := by
  constructor
  · intro hxa
    obtain ⟨z, hz⟩ := D.liftBase Y x a hxa
    refine ⟨z, ?_, hz⟩
    apply hα Y
    have hsq := ConcreteCategory.congr_hom (NatTrans.congr_app D.square Y) z
    calc
      α.app Y (D.fst.app Y z) =
          g.app Y ((uliftYoneda.map D.snd).app Y z) := by simpa using hsq
      _ = g.app Y a := congrArg (g.app Y) hz
      _ = α.app Y x := hxa.symm
  · rintro ⟨z, hzx, hza⟩
    have hsq := ConcreteCategory.congr_hom (NatTrans.congr_app D.square Y) z
    calc
      α.app Y x = α.app Y (D.fst.app Y z) := congrArg (α.app Y) hzx.symm
      _ = g.app Y ((uliftYoneda.map D.snd).app Y z) := by simpa using hsq
      _ = g.app Y a := congrArg (g.app Y) hza

/-- A pointwise fibre-locus criterion gives the represented pullback square as soon as the
target transformation is pointwise injective. -/
theorem isPullback_of_injective (D : ImmersionFibreLocus α T g)
    (hα : ∀ Y, Function.Injective (α.app Y)) :
    IsPullback D.fst (uliftYoneda.map D.snd) α g := by
  apply IsPullback.of_forall_isPullback_app
  intro Y
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app Y) D.square, ?_, ?_⟩
  · rintro x y ⟨-, hxy⟩
    letI : IsImmersion D.snd.left := D.isImmersion
    haveI : Mono D.snd := Over.mono_of_mono_left _
    apply ULift.ext
    rw [← cancel_mono D.snd]
    exact congrArg ULift.down hxy
  · intro x a hxa
    exact (D.compatible_iff_exists_of_injective hα Y x a).mp hxa

end ImmersionFibreLocus

/-- Regard an object over the test scheme `T.left` as an object over `S`, and map it to
`T`.  This is the slice-category bookkeeping needed for a flattening locus constructed on
the test scheme. -/
def fibreLocusMap (T : Over S) (A : Over T.left) : (Over.map T.hom).obj A ⟶ T :=
  Over.homMk A.hom rfl

@[simp]
lemma fibreLocusMap_left (T : Over S) (A : Over T.left) :
    (fibreLocusMap T A).left = A.hom := rfl

/-- A fibre locus presented as a finite intersection of immersed objects over the test
scheme.  For the Quot application, the entries of `locus` are the general-base flattening
representatives of the relevant pushforward sheaves. -/
structure FiniteImmersionFibreLocus (α : F ⟶ G) (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ G) where
  /-- Number of conditions in the finite intersection. -/
  card : ℕ
  /-- The individual loci over the test scheme. -/
  locus : Fin card → Over T.left
  /-- Each individual locus is immersed in the test scheme. -/
  locusIsImmersion : ∀ i, IsImmersion (locus i).hom
  /-- The canonical point of `F` on the intersection. -/
  fst : uliftYoneda.{u + 1}.obj
      ((Over.map T.hom).obj (Scheme.interOverFin locus)) ⟶ F
  /-- The canonical point maps to the pullback of `g`. -/
  square : fst ≫ α =
    uliftYoneda.map (fibreLocusMap T (Scheme.interOverFin locus)) ≫ g
  /-- Every compatible pair has base arrow factoring through the finite intersection. -/
  liftBase : ∀ (Y : (Over S)ᵒᵖ) (x : F.obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y),
    α.app Y x = g.app Y a →
      ∃ z : (uliftYoneda.{u + 1}.obj
        ((Over.map T.hom).obj (Scheme.interOverFin locus))).obj Y,
        (uliftYoneda.map (fibreLocusMap T (Scheme.interOverFin locus))).app Y z = a

namespace FiniteImmersionFibreLocus

variable {α : F ⟶ G} {T : Over S} {g : uliftYoneda.{u + 1}.obj T ⟶ G}

/-- Forget the chosen finite-intersection presentation and retain its resulting immersion
fibre locus. -/
def toImmersionFibreLocus (D : FiniteImmersionFibreLocus α T g) :
    ImmersionFibreLocus α T g where
  obj := (Over.map T.hom).obj (Scheme.interOverFin D.locus)
  fst := D.fst
  snd := fibreLocusMap T (Scheme.interOverFin D.locus)
  square := D.square
  isImmersion := by
    change IsImmersion (Scheme.interOverFin D.locus).hom
    exact Scheme.interOverFin_isImmersion D.locus D.locusIsImmersion
  liftBase := D.liftBase

/-- The finite-intersection presentation gives the pullback square when `α` is pointwise
injective. -/
theorem isPullback_of_injective (D : FiniteImmersionFibreLocus α T g)
    (hα : ∀ Y, Function.Injective (α.app Y)) :
    IsPullback D.fst
      (uliftYoneda.map (fibreLocusMap T (Scheme.interOverFin D.locus))) α g :=
  D.toImmersionFibreLocus.isPullback_of_injective hα

end FiniteImmersionFibreLocus

/-- The proposition that every fibre of `α` admits a finite immersed-locus presentation.
This is the compact obligation left after constructing the Quot-to-Grassmannian natural
transformation and its pointwise injectivity. -/
def HasFiniteImmersionFibreLoci (α : F ⟶ G) : Prop :=
  ∀ (T : Over S) (g : uliftYoneda.{u + 1}.obj T ⟶ G),
    Nonempty (FiniteImmersionFibreLocus α T g)

/-- A pointwise identification of every fibre with an immersion locus proves that a
pointwise-injective transformation is relatively representable by immersions. -/
theorem relative_over_isImmersion_of_fibreLoci (α : F ⟶ G)
    (hα : ∀ Y, Function.Injective (α.app Y))
    (H : ∀ (T : Over S) (g : uliftYoneda.{u + 1}.obj T ⟶ G),
      ImmersionFibreLocus α T g) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let D := H T g
  exact ⟨D.obj, D.fst, D.snd, D.isPullback_of_injective hα, D.isImmersion⟩

/-- Finite-intersection form of
`relative_over_isImmersion_of_fibreLoci`.  This is the direct endpoint for fibres cut out by
finitely many flattening conditions. -/
theorem relative_over_isImmersion_of_finiteFibreLoci (α : F ⟶ G)
    (hα : ∀ Y, Function.Injective (α.app Y))
    (H : ∀ (T : Over S) (g : uliftYoneda.{u + 1}.obj T ⟶ G),
      FiniteImmersionFibreLocus α T g) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α :=
  relative_over_isImmersion_of_fibreLoci α hα
    (fun T g => (H T g).toImmersionFibreLocus)

/-- Proposition-valued form of `relative_over_isImmersion_of_finiteFibreLoci`. -/
theorem relative_over_isImmersion_of_hasFiniteFibreLoci (α : F ⟶ G)
    (hα : ∀ Y, Function.Injective (α.app Y))
    (H : HasFiniteImmersionFibreLoci α) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α :=
  relative_over_isImmersion_of_finiteFibreLoci α hα
    (fun T g => Classical.choice (H T g))

/-- Monomorphism-form of `relative_over_isImmersion_of_fibreLoci`.  In a functor category,
a monomorphism is componentwise injective, so no separate injectivity hypothesis is needed. -/
theorem relative_over_isImmersion_of_fibreLoci_of_mono (α : F ⟶ G) [Mono α]
    (H : ∀ (T : Over S) (g : uliftYoneda.{u + 1}.obj T ⟶ G),
      ImmersionFibreLocus α T g) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α :=
  relative_over_isImmersion_of_fibreLoci α
    (fun Y => injective_of_mono (α.app Y)) H

/-- Monomorphism-form of `relative_over_isImmersion_of_finiteFibreLoci`. -/
theorem relative_over_isImmersion_of_finiteFibreLoci_of_mono (α : F ⟶ G) [Mono α]
    (H : ∀ (T : Over S) (g : uliftYoneda.{u + 1}.obj T ⟶ G),
      FiniteImmersionFibreLocus α T g) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α :=
  relative_over_isImmersion_of_finiteFibreLoci α
    (fun Y => injective_of_mono (α.app Y)) H

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

namespace TwistedFreeQuotGrassmannianQuotientNatTransData

/-- The fixed-degree monomial quotient detects equivalence of the original
twisted-free Quot presentations.

This is the precise algebraic reconstruction statement needed for pointwise
injectivity of the Quot-to-Grassmannian transformation.  Equality of
Grassmannian points is already equivalent to equivalence of their strict free
quotient presentations by `Modules.FreeQuotient.r_of_kernelPoint_eq`; the
remaining implication says that this degree-`d` equivalence determines the
original quotient sheaf.  In the classical argument this is supplied by
regularity and Gotzmann persistence. -/
def ReflectsQuotientEquivalence
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ) : Prop :=
  ∀ (T : Over S)
    (a b : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hPa : a.HasFiberwiseHilbertPolynomial P)
    (hPb : b.HasFiberwiseHilbertPolynomial P),
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).r
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ
          (D.isProjectiveOfRank T a hPa) (D.surjective T a hPa))
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r b d e he σ
          (D.isProjectiveOfRank T b hPb) (D.surjective T b hPb)) →
    (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r a b

/-- Reflection of quotient equivalence by the fixed-degree monomial quotient
proves pointwise injectivity of the intrinsic Quot-to-Grassmannian map. -/
theorem natTrans_app_injective_of_reflectsQuotientEquivalence
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence)
    (T : (Over S)ᵒᵖ) : Function.Injective (D.natTrans.app T) := by
  intro x y hxy
  have hkernelPoint :
      (D.representativeFreeQuotient x).kernelPoint =
        (D.representativeFreeQuotient y).kernelPoint := by
    exact congrArg ULift.down hxy
  have hfree : (Modules.FreeQuotient.setoid q
      (ULift.{u} (Fin m)) (unop T).left).r
      (D.representativeFreeQuotient x)
      (D.representativeFreeQuotient y) :=
    Modules.FreeQuotient.r_of_kernelPoint_eq hkernelPoint
  let a := TwistedFreeQuotGrassmannianNatTransData.representative x
  let b := TwistedFreeQuotGrassmannianNatTransData.representative y
  let hPa :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
  let hPb :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial y
  have hab : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T)).r a b := by
    apply hreflect (unop T) a b hPa hPb
    exact hfree
  apply Subtype.ext
  calc
    x.1 = Quotient.mk _ a :=
      (TwistedFreeQuotGrassmannianNatTransData.representative_mk x).symm
    _ = Quotient.mk _ b := Quotient.sound hab
    _ = y.1 :=
      TwistedFreeQuotGrassmannianNatTransData.representative_mk y

/-- Reflection of quotient equivalence supplies pointwise injectivity in every
test scheme. -/
theorem natTrans_pointwise_injective_of_reflectsQuotientEquivalence
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence) :
    ∀ T, Function.Injective (D.natTrans.app T) :=
  fun T ↦ D.natTrans_app_injective_of_reflectsQuotientEquivalence hreflect T

/-- Pointwise injectivity of the intrinsic Quot-to-Grassmannian map reflects
equivalence of arbitrary fixed-polynomial raw representatives.  Together with
`natTrans_pointwise_injective_of_reflectsQuotientEquivalence`, this shows that
`ReflectsQuotientEquivalence` is the exact algebraic content of injectivity,
not a stronger auxiliary hypothesis. -/
theorem reflectsQuotientEquivalence_of_natTrans_pointwise_injective
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hinj : ∀ T, Function.Injective (D.natTrans.app T)) :
    D.ReflectsQuotientEquivalence := by
  intro T a b hPa hPb hab
  let x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj (op T) :=
    ⟨Quotient.mk _ a, a, rfl, hPa⟩
  let y : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj (op T) :=
    ⟨Quotient.mk _ b, b, rfl, hPb⟩
  have hxa : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r
      (TwistedFreeQuotGrassmannianNatTransData.representative x) a := by
    apply Quotient.exact
    exact TwistedFreeQuotGrassmannianNatTransData.representative_mk x
  have hyb : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r
      (TwistedFreeQuotGrassmannianNatTransData.representative y) b := by
    apply Quotient.exact
    exact TwistedFreeQuotGrassmannianNatTransData.representative_mk y
  let hPx :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
  let hPy :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial y
  have hfree_xa : (Modules.FreeQuotient.setoid q
      (ULift.{u} (Fin m)) T.left).r
      (D.representativeFreeQuotient x)
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ
          (D.isProjectiveOfRank T a hPa) (D.surjective T a hPa)) := by
    exact twistedFreeQuotGrassmannianFreeQuotient_r_of_r
      n S l r hxa d e he σ
        (D.isProjectiveOfRank T
          (TwistedFreeQuotGrassmannianNatTransData.representative x) hPx)
        (D.surjective T
          (TwistedFreeQuotGrassmannianNatTransData.representative x) hPx)
        (D.isProjectiveOfRank T a hPa) (D.surjective T a hPa)
  have hfree_yb : (Modules.FreeQuotient.setoid q
      (ULift.{u} (Fin m)) T.left).r
      (D.representativeFreeQuotient y)
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r b d e he σ
          (D.isProjectiveOfRank T b hPb) (D.surjective T b hPb)) := by
    exact twistedFreeQuotGrassmannianFreeQuotient_r_of_r
      n S l r hyb d e he σ
        (D.isProjectiveOfRank T
          (TwistedFreeQuotGrassmannianNatTransData.representative y) hPy)
        (D.surjective T
          (TwistedFreeQuotGrassmannianNatTransData.representative y) hPy)
        (D.isProjectiveOfRank T b hPb) (D.surjective T b hPb)
  have hfree_xy : (Modules.FreeQuotient.setoid q
      (ULift.{u} (Fin m)) T.left).r
      (D.representativeFreeQuotient x)
      (D.representativeFreeQuotient y) :=
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).trans
      hfree_xa
      ((Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).trans
        hab
        ((Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).symm hfree_yb))
  have hcomponent : D.component (op T) x = D.component (op T) y := by
    apply ULift.ext
    exact Modules.FreeQuotient.kernelPoint_eq_of_r hfree_xy
  have hxy : x = y := hinj (op T) hcomponent
  apply Quotient.exact
  exact congrArg Subtype.val hxy

/-- The fixed-degree reconstruction-reflection statement is equivalent to
pointwise injectivity of the associated Quot-to-Grassmannian natural
transformation. -/
theorem reflectsQuotientEquivalence_iff_natTrans_pointwise_injective
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ) :
    D.ReflectsQuotientEquivalence ↔
      ∀ T, Function.Injective (D.natTrans.app T) :=
  ⟨D.natTrans_pointwise_injective_of_reflectsQuotientEquivalence,
    D.reflectsQuotientEquivalence_of_natTrans_pointwise_injective⟩

end TwistedFreeQuotGrassmannianQuotientNatTransData

/-- Pointwise injectivity and finite immersed fibre loci give relative
representability by immersions for the intrinsic strict-quotient
Quot-to-Grassmannian transformation. -/
theorem
    TwistedFreeQuotGrassmannianQuotientNatTransData.relative_isImmersion_of_finiteFibreLoci
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hinj : ∀ Y, Function.Injective (D.natTrans.app Y))
    (H : HasFiniteImmersionFibreLoci D.natTrans) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) D.natTrans :=
  relative_over_isImmersion_of_hasFiniteFibreLoci D.natTrans hinj H

/-- The canonical strict-quotient natural transformation closes the precise
twisted-free W6 predicate once its target lies in the nonempty rank range and
its fibres have the finite immersed-locus presentation. -/
theorem
    twistedFreeQuotHasFreeGrassmannianImmersion_of_quotientNatTrans_finiteFibreLoci
    (hqm : q ≤ m)
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hinj : ∀ Y, Function.Injective (D.natTrans.app Y))
    (H : HasFiniteImmersionFibreLoci D.natTrans) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P q m hqm D.natTrans
      (D.relative_isImmersion_of_finiteFibreLoci hinj H)

/-- The general fixed-degree Quot-to-Grassmannian construction is relatively
representable by immersions once the exact reconstruction-reflection statement
and the finite flattening-locus description of its fibres are available. -/
theorem
    TwistedFreeQuotGrassmannianQuotientNatTransData.relative_isImmersion_of_reflection_finiteFibreLoci
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence)
    (H : HasFiniteImmersionFibreLoci D.natTrans) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) D.natTrans :=
  D.relative_isImmersion_of_finiteFibreLoci
    (D.natTrans_pointwise_injective_of_reflectsQuotientEquivalence hreflect) H

/-- Reconstruction reflection and finite immersed fibre loci close the exact
twisted-free W6 predicate for the canonical fixed-degree transformation. -/
theorem
    twistedFreeQuotHasFreeGrassmannianImmersion_of_quotientNatTrans_reflection_finiteFibreLoci
    (hqm : q ≤ m)
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence)
    (H : HasFiniteImmersionFibreLoci D.natTrans) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P q m hqm D.natTrans
      (D.relative_isImmersion_of_reflection_finiteFibreLoci hreflect H)

end AlgebraicGeometry.Scheme

end
