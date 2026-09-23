module

public import StacksAndModuli.API.ProjectiveFlatteningLocusBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningFibre

/-!
# Quot-to-Grassmannian fibres from a represented flattening locus

The finite-rank flattening presentation used by
`TwistedFreeQuotGrassmannianFlatteningFibreData` contains more information than the
fibre argument needs.  This file gives the geometric version of that argument.  Its
input is merely a representative of the projective flattening functor whose structure
map is an immersion.

This formulation is stable under arbitrary base change through
`ProjectiveFlatteningLocusWitness.baseChange`.  In particular, a flattening locus for
one universal reconstructed quotient can be pulled back to every Grassmannian-valued
test point without transporting a chosen list of finite modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The canonical Quot point on an arbitrary represented flattening locus of the
quotient reconstructed from a Grassmannian point. -/
noncomputable def grassmannianPointFlatteningUniversalQuotPointOfWitness
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P) :
    (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj
      (op ((Over.map T.hom).obj H.representative)) := by
  let Q := grassmannianPointReconstructedQuotient
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ) T g
  let Z := H.representative
  let hz := H.representableBy.homEquiv (𝟙 Z)
  let QZ := Modules.projectiveFamilyAt n Q Z
  let pZ := (projectiveSpaceOverTwistedFree_pullbackIso n r l Z.hom).inv ≫
    (Modules.pullback (projectiveSpaceOverMap n Z.hom)).map
      (grassmannianPointReconstructedQuotientMap
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g)
  exact Modules.QuotientPullbackData.quotFunctorPPointOfTwistedFreeQuotientOnProjectiveSpace
    ((Over.map T.hom).obj Z) QZ (by infer_instance) hz.down.down.1 pZ P hz.down.down.2

/-- The natural transformation classified by the universal reconstructed Quot point
on a represented flattening locus. -/
noncomputable def grassmannianPointFlatteningFstOfWitness
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P) :
    uliftYoneda.{u + 1}.obj ((Over.map T.hom).obj H.representative) ⟶
      quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P :=
  uliftYonedaEquiv.{u + 1}.symm
    (grassmannianPointFlatteningUniversalQuotPointOfWitness
      (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
        (d := d) (e := e) (he := he) (σ := σ) T g H)

/-- Data identifying a Quot-to-Grassmannian fibre with an arbitrary represented
immersed projective flattening locus. -/
structure TwistedFreeQuotGrassmannianFlatteningWitnessFibreData
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    Type (u + 1) where
  /-- A represented immersed flattening locus for the reconstructed quotient. -/
  flattening : Modules.ProjectiveFlatteningLocusWitness n
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g) P
  /-- The universal reconstructed point maps back to the chosen Grassmannian point. -/
  universalCompatibility :
    let Z := flattening.representative
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPointOfWitness
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g flattening) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z)))
  /-- Every compatible Quot point gives a point of the flattening functor. -/
  compatibleFlattening : ∀ (Y : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y),
    D.natTrans.app Y x = g.app Y a →
      (Modules.projectiveFlatteningFunctor n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P)).obj
          (op (Over.mk a.down.left))

namespace TwistedFreeQuotGrassmannianFlatteningWitnessFibreData

variable
    {D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ}
    {T : Over S}
    {g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m}

/-- The geometric fibre package forgets the chosen finite list in the original
finite-rank presentation package. -/
noncomputable def ofFiniteRankData
    (H : TwistedFreeQuotGrassmannianFlatteningFibreData D T g) :
    TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g where
  flattening := Modules.ProjectiveFlatteningLocusWitness.ofFiniteRankPresentation
    n _ P H.flattening
  universalCompatibility := H.universalCompatibility
  compatibleFlattening := H.compatibleFlattening

/-- The universal reconstructed point gives the commuting square over the chosen
Grassmannian point. -/
lemma universalSquare
    (H : TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g) :
    grassmannianPointFlatteningFstOfWitness
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g H.flattening ≫
      D.natTrans =
    uliftYoneda.map (fibreLocusMap T H.flattening.representative) ≫ g := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp,
    uliftYonedaEquiv_uliftYoneda_map]
  simp only [grassmannianPointFlatteningFstOfWitness, Equiv.apply_symm_apply]
  exact H.universalCompatibility

/-- Forget the construction and retain the represented immersed fibre locus. -/
noncomputable def toImmersionFibreLocus
    (H : TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g) :
    ImmersionFibreLocus D.natTrans T g where
  obj := (Over.map T.hom).obj H.flattening.representative
  fst := grassmannianPointFlatteningFstOfWitness
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H.flattening
  snd := fibreLocusMap T H.flattening.representative
  square := H.universalSquare
  isImmersion := H.flattening.representative_hom_isImmersion
  liftBase := by
    intro Y x a hxa
    let Q := grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g
    let Z := H.flattening.representative
    let E := H.flattening.representableBy
    let A : Over T.left := Over.mk a.down.left
    let ha := H.compatibleFlattening Y x a hxa
    let b : A ⟶ Z := E.homEquiv.symm ha
    let z₀ : Y.unop ⟶ (Over.map T.hom).obj Z :=
      Over.homMk b.left (by
        change b.left ≫ (Z.hom ≫ T.hom) = Y.unop.hom
        rw [← Category.assoc, Over.w b]
        change a.down.left ≫ T.hom = Y.unop.hom
        exact Over.w a.down)
    refine ⟨ULift.up z₀, ?_⟩
    apply ULift.ext
    apply Over.OverMorphism.ext
    change b.left ≫ Z.hom = a.down.left
    exact Over.w b

/-- Uniform represented flattening-fibre data give the immersed fibre loci needed
for relative representability. -/
noncomputable def immersionFibreLoci
    (H : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g)) :
    ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      ImmersionFibreLocus D.natTrans T g := fun T g ↦
  (Classical.choice (H T g)).toImmersionFibreLocus

end TwistedFreeQuotGrassmannianFlatteningWitnessFibreData

namespace TwistedFreeQuotGrassmannianQuotientNatTransData

/-- Reconstruction reflection and represented immersed flattening fibres make the
intrinsic Quot-to-Grassmannian transformation relatively representable by immersions. -/
theorem relative_isImmersion_of_reflection_witnessFibreLoci
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence)
    (H : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g)) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) D.natTrans :=
  relative_over_isImmersion_of_fibreLoci D.natTrans
    (D.natTrans_pointwise_injective_of_reflectsQuotientEquivalence hreflect)
    (TwistedFreeQuotGrassmannianFlatteningWitnessFibreData.immersionFibreLoci H)

end TwistedFreeQuotGrassmannianQuotientNatTransData

/-- The geometric flattening-witness formulation closes the twisted-free W6
predicate without choosing a finite-rank presentation on every test scheme. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_of_quotientNatTrans_reflection_witnessFibreLoci
    (hqm : q ≤ m)
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hreflect : D.ReflectsQuotientEquivalence)
    (H : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g)) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P q m hqm D.natTrans
      (D.relative_isImmersion_of_reflection_witnessFibreLoci hreflect H)

end AlgebraicGeometry.Scheme

end

end
