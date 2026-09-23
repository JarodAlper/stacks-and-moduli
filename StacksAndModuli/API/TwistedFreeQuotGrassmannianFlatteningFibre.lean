module

public import StacksAndModuli.API.TwistedFreeQuotDenormalization
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFibre
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection
public import StacksAndModuli.API.QuotGrassmannianReconstructionIso
public import StacksAndModuli.API.ProjectiveFlatteningLocus
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentationVectorBundle

/-!
# Constructing Quot-to-Grassmannian fibres from projective flattening loci

For a point of the free Grassmannian, the inverse of `FreeQuotient.kernelPointEquiv`
gives a strict quotient of a finite free sheaf.  Reindexing its source by the monomial
basis and applying `reconstructedQuotient'` produces the canonical candidate quotient
on relative projective space.  This file packages the formal last step: a finite-rank
presentation of the projective flattening condition produces the finite immersed fibre
locus required by `TwistedFreeQuotGrassmannianFibre`.

Only two genuinely geometric compatibilities remain as fields of
`TwistedFreeQuotGrassmannianFlatteningFibreData`: the reconstructed quotient on the
universal flattening locus maps back to the chosen Grassmannian point, and every
compatible Quot family makes the reconstructed quotient flat with the prescribed
Hilbert polynomial.  Representability, construction of the universal Quot point,
finite-intersection bookkeeping, and the base-factorization statement are proved here.
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

/-- The strict finite-free quotient classified by a point of the free Grassmannian. -/
noncomputable def grassmannianPointFreeQuotient
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    Modules.FreeQuotient q (ULift.{u} (Fin m)) T.left :=
  Classical.choose (Quotient.exists_rep
    (Modules.FreeQuotient.kernelPointEquiv.symm (uliftYonedaEquiv g).down))

/-- The chosen strict quotient representative recovers the Grassmannian point that
classified it. -/
@[simp]
lemma grassmannianPointFreeQuotient_kernelPoint
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    (grassmannianPointFreeQuotient (q := q) T g).kernelPoint =
      (uliftYonedaEquiv g).down := by
  let z := Modules.FreeQuotient.kernelPointEquiv.symm (uliftYonedaEquiv g).down
  have hrep : Quotient.mk'' (grassmannianPointFreeQuotient (q := q) T g) = z :=
    Classical.choose_spec (Quotient.exists_rep z)
  have h := congrArg Modules.FreeQuotient.kernelPointEquiv hrep
  simpa [Modules.FreeQuotient.kernelPointEquiv,
    Modules.FreeQuotient.kernelPointQuotient, z] using h

/-- Evaluating the classified Grassmannian point on a test arrow is represented by
pulling back the chosen strict quotient. -/
lemma grassmannianPointFreeQuotient_pullback_kernelPoint
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ} (a : (uliftYoneda.{u + 1}.obj T).obj Y) :
    ((grassmannianPointFreeQuotient (q := q) T g).pullback
      a.down.left).kernelPoint = (g.app Y a).down := by
  rcases a with ⟨a⟩
  rw [← Modules.FreeQuotient.kernelPoint_pullback,
    grassmannianPointFreeQuotient_kernelPoint]
  change ((Modules.grassmannianFunctorOver S q m).map a.op
    (uliftYonedaEquiv g)).down = (g.app Y (ULift.up a)).down
  let idT : (uliftYoneda.{u + 1}.obj T).obj (op T) := ULift.up (𝟙 T)
  have h := CategoryTheory.NatTrans.naturality_apply g a.op idT
  rw [uliftYonedaEquiv_apply]
  have h' := congrArg ULift.down h.symm
  have ha : (uliftYoneda.{u + 1}.obj T).map a.op idT = ULift.up a := rfl
  rw [ha] at h'
  simpa only [idT] using h'

/-- A point in the fibre of the Quot-to-Grassmannian map identifies the pulled-back
Grassmannian quotient presentation with the strict monomial quotient of its chosen
Quot representative. -/
lemma grassmannianPointFreeQuotient_pullback_r_representativeFreeQuotient
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (h : D.natTrans.app Y x = g.app Y a) :
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) (unop Y).left).r
      ((grassmannianPointFreeQuotient (q := q) T g).pullback a.down.left)
      (D.representativeFreeQuotient x) := by
  apply Modules.FreeQuotient.r_of_kernelPoint_eq
  rw [grassmannianPointFreeQuotient_pullback_kernelPoint]
  exact (congrArg ULift.down h).symm

/-- The target isomorphism underlying the equivalence of strict quotient presentations
attached to a compatible point of the fibre. -/
noncomputable def grassmannianPointFreeQuotientPullbackIsoRepresentative
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (h : D.natTrans.app Y x = g.app Y a) :
    ((grassmannianPointFreeQuotient (q := q) T g).pullback a.down.left).Q ≅
      (D.representativeFreeQuotient x).Q :=
  Classical.choose
    (grassmannianPointFreeQuotient_pullback_r_representativeFreeQuotient
      D T g x a h)

/-- The isomorphism of strict quotient targets commutes with their maps from the
canonical finite free sheaf. -/
lemma grassmannianPointFreeQuotientPullback_π_comp_isoRepresentative_hom
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (h : D.natTrans.app Y x = g.app Y a) :
    ((grassmannianPointFreeQuotient (q := q) T g).pullback a.down.left).π ≫
        (grassmannianPointFreeQuotientPullbackIsoRepresentative
          D T g x a h).hom =
      (D.representativeFreeQuotient x).π :=
  Classical.choose_spec
    (grassmannianPointFreeQuotient_pullback_r_representativeFreeQuotient
      D T g x a h)

/-- The Grassmannian quotient map, reindexed by the product monomial basis used in
the twisted-free reconstruction. -/
noncomputable def grassmannianPointMonomialQuotientMap
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    SheafOfModules.free (R := T.left.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶
      (grassmannianPointFreeQuotient (q := q) T g).Q :=
  SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
    (grassmannianPointFreeQuotient (q := q) T g).π

/-- The quotient on `ℙⁿ_T` reconstructed from a point of the free Grassmannian. -/
noncomputable def grassmannianPointReconstructedQuotient
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    (projectiveSpaceOver n T.left).Modules :=
  reconstructedQuotient' n T.left l r d e he
    (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)

/-- The canonical twisted-free quotient map onto the quotient reconstructed from a
Grassmannian point. -/
noncomputable def grassmannianPointReconstructedQuotientMap
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T.left (-l)) ⟶
      grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g :=
  reconstructedQuotientMap' n T.left l r d e he
    (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)

/-- A twisted-free quotient reconstructed from a quasicoherent target is
quasicoherent.  This low-dependency version keeps the geometric flattening-fibre
construction independent of the later one-step Gotzmann package. -/
lemma reconstructedQuotient'_isQuasicoherent_for_flatteningFibre
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (reconstructedQuotient' n T l r d e he u).IsQuasicoherent := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) (kernel u)
  letI : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  letI : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  dsimp only [reconstructedQuotient']
  apply Modules.isQuasicoherent_cokernel

/-- A twisted-free reconstruction is finitely presented whenever the relation
kernel on the base is finitely presented.  This is the assumption-exposing
form of `reconstructedQuotient'_isFinitePresentation`; it is useful over
non-noetherian bases when the relation kernel is finite projective for a
separate reason. -/
lemma reconstructedQuotient'_isFinitePresentation_of_kernel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hKfp : (kernel u).IsFinitePresentation) :
    (reconstructedQuotient' n T l r d e he u).IsFinitePresentation := by
  letI hKqc : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI hPullKqc : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) (kernel u)
  letI : (kernel u).IsFinitePresentation := hKfp
  letI hPullKfp : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation
      (projectiveSpaceOverπ n T) hKfp
  letI hSourceFp : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsFinitePresentation := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsFinitePresentation
    infer_instance
  letI hSourceQc : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  letI hTargetFp : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsFinitePresentation :=
    Modules.projectiveSpaceOverTwistCoproduct_isFinitePresentation _ n T _
  letI hTargetQc : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  dsimp only [reconstructedQuotient']
  exact Modules.cokernel_isFinitePresentation _

instance grassmannianPointReconstructedQuotient_isQuasicoherent
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g).IsQuasicoherent :=
  by
    letI : (grassmannianPointFreeQuotient (q := q) T g).Q.IsQuasicoherent :=
      (grassmannianPointFreeQuotient (q := q) T g).isQuasicoherent
    exact reconstructedQuotient'_isQuasicoherent_for_flatteningFibre
      n T.left l r d e he _

instance grassmannianPointReconstructedQuotient_isFinitePresentation
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g).IsFinitePresentation := by
  let x := grassmannianPointFreeQuotient (q := q) T g
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  let f := SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm
  letI : IsIso f := by
    dsimp only [f]
    exact Modules.freeMap_isIso_of_equiv σ.symm
  have hSource : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := T.left.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))) :=
    (Modules.free_isFiniteLocallyFree T.left m).of_iso (asIso f).symm
  have hTarget : Modules.IsFiniteLocallyFree x.Q :=
    x.isProjectiveOfRank.isFiniteLocallyFree
  letI : Epi x.π := x.epi
  let p := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) T g
  letI : Epi p := by
    dsimp only [p, grassmannianPointMonomialQuotientMap, x, f]
    infer_instance
  have hKfp : (kernel p).IsFinitePresentation :=
    Modules.kernel_isFinitePresentation_of_epi_of_isFiniteLocallyFree
      hSource hTarget p
  exact reconstructedQuotient'_isFinitePresentation_of_kernel
    n T.left l r d e he p hKfp

instance grassmannianPointReconstructedQuotientMap_epi
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    Epi (grassmannianPointReconstructedQuotientMap
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g) := by
  dsimp only [grassmannianPointReconstructedQuotientMap]
  infer_instance

/-- The individual ordinary flattening loci in a chosen finite-rank
presentation of the reconstructed quotient's projective flattening functor. -/
noncomputable def grassmannianPointFlatteningLocus
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) :
    Fin (Classical.choice h).count → Over T.left := fun i ↦
  let C := Classical.choice h
  @Modules.flatRankRepresentativeOfFinite T.left (C.sheaf i)
    (C.isQuasicoherent i) (C.rank i) (C.finite i)

/-- The canonical Quot point on the universal flattening locus of the
quotient reconstructed from a Grassmannian point. -/
noncomputable def grassmannianPointFlatteningUniversalQuotPoint
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) :
    (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj
      (op ((Over.map T.hom).obj
        (Modules.projectiveFlatteningRepresentative n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
              (he := he) (σ := σ) T g) (P := P) h))) := by
  let Q := grassmannianPointReconstructedQuotient
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ) T g
  let Z := Modules.projectiveFlatteningRepresentative n Q (P := P) h
  let E := Modules.projectiveFlatteningRepresentableBy n Q (P := P) h
  let hz := E.homEquiv (𝟙 Z)
  let QZ := Modules.projectiveFamilyAt n Q Z
  let pZ := (projectiveSpaceOverTwistedFree_pullbackIso n r l Z.hom).inv ≫
    (Modules.pullback (projectiveSpaceOverMap n Z.hom)).map
      (grassmannianPointReconstructedQuotientMap
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g)
  exact Modules.QuotientPullbackData.quotFunctorPPointOfTwistedFreeQuotientOnProjectiveSpace
    ((Over.map T.hom).obj Z) QZ (by infer_instance) hz.down.down.1 pZ P hz.down.down.2

/-- The natural transformation classified by the universal reconstructed Quot
point on the flattening locus. -/
noncomputable def grassmannianPointFlatteningFst
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) :
    uliftYoneda.{u + 1}.obj
        ((Over.map T.hom).obj
          (Modules.projectiveFlatteningRepresentative n
            (grassmannianPointReconstructedQuotient
              (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
                (he := he) (σ := σ) T g) (P := P) h)) ⟶
      quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P :=
  uliftYonedaEquiv.{u + 1}.symm
    (grassmannianPointFlatteningUniversalQuotPoint
      (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
        (d := d) (e := e) (he := he) (σ := σ) T g h)

/-- An isomorphism from a pulled-back reconstructed quotient to the normalized sheaf
underlying a fixed-polynomial Quot point supplies the corresponding point of the
projective flattening functor.  This separates the formal transport of flatness and
Hilbert polynomial from the geometric reconstruction argument that produces the
isomorphism. -/
noncomputable def grassmannianPointCompatibleFlatteningOfIso
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (E : Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (Over.mk a.down.left) ≅
      twistedFreeQuotientSheaf n S l r
        (TwistedFreeQuotGrassmannianNatTransData.representative x)) :
    (Modules.projectiveFlatteningFunctor n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)).obj
        (op (Over.mk a.down.left)) := by
  refine ULift.up (PLift.up ⟨?_, ?_⟩)
  · exact Modules.FlatOver.of_iso E.symm
      (Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over
        (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
  · exact Scheme.HasFiberwiseHilbertPolynomial.of_iso E.symm
      (TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x)

/-- Data identifying a fibre of the intrinsic Quot-to-Grassmannian transformation
with the projective flattening locus of the reconstructed Grassmannian quotient. -/
structure TwistedFreeQuotGrassmannianFlatteningFibreData
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m) :
    Type (u + 1) where
  /-- The reconstructed quotient has a finite-rank projective-flattening presentation. -/
  flattening : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)
  /-- On the universal flattening locus, the reconstructed quotient is sent back to
  the pullback of the chosen Grassmannian point. -/
  universalCompatibility :
    let Z := Modules.projectiveFlatteningRepresentative n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P) flattening
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPoint
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g flattening) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z)))
  /-- A compatible Quot point makes the corresponding pullback of the reconstructed
  quotient flat with fibrewise Hilbert polynomial `P`. -/
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

namespace TwistedFreeQuotGrassmannianFlatteningFibreData

variable
    {D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ}
    {T : Over S}
    {g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m}

/-- The universal reconstructed Quot point gives a commuting square over the
chosen Grassmannian point. -/
lemma universalSquare
    (H : TwistedFreeQuotGrassmannianFlatteningFibreData D T g) :
    grassmannianPointFlatteningFst
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g H.flattening ≫
      D.natTrans =
    uliftYoneda.map (fibreLocusMap T
      (Modules.projectiveFlatteningRepresentative n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P) H.flattening)) ≫ g := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp,
    uliftYonedaEquiv_uliftYoneda_map]
  simp only [grassmannianPointFlatteningFst, Equiv.apply_symm_apply]
  exact H.universalCompatibility

/-- A projective-flattening fibre package produces the finite immersed fibre
locus required by the Quot-to-Grassmannian representability argument. -/
noncomputable def toFiniteImmersionFibreLocus
    (H : TwistedFreeQuotGrassmannianFlatteningFibreData D T g) :
    FiniteImmersionFibreLocus D.natTrans T g where
  card := (Classical.choice H.flattening).count
  locus := grassmannianPointFlatteningLocus
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H.flattening
  locusIsImmersion := by
    intro i
    let C := Classical.choice H.flattening
    exact @Modules.flatRankRepresentativeOfFinite_hom_isImmersion
      T.left (C.sheaf i) (C.isQuasicoherent i) (C.rank i) (C.finite i)
  fst := grassmannianPointFlatteningFst
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H.flattening
  square := H.universalSquare
  liftBase := by
    intro Y x a hxa
    let Q := grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g
    let Z := Modules.projectiveFlatteningRepresentative n Q
      (P := P) H.flattening
    let E := Modules.projectiveFlatteningRepresentableBy n Q
      (P := P) H.flattening
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

/-- If every Grassmannian point admits the projective-flattening compatibility
package, the intrinsic Quot-to-Grassmannian transformation has finite immersed
fibre loci. -/
theorem hasFiniteImmersionFibreLoci
    (H : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (TwistedFreeQuotGrassmannianFlatteningFibreData D T g)) :
    HasFiniteImmersionFibreLoci D.natTrans := by
  intro T g
  exact ⟨(Classical.choice (H T g)).toFiniteImmersionFibreLocus⟩

end TwistedFreeQuotGrassmannianFlatteningFibreData

end AlgebraicGeometry.Scheme

end

end
