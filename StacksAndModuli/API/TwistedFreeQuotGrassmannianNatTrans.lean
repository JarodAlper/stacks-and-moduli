module

public import StacksAndModuli.API.TwistedFreeMonomialSpanAffine
public import StacksAndModuli.API.KernelGrassmannianPoint
public import StacksAndModuli.API.ModulesPullbackCoherence
public import StacksAndModuli.API.SchemeModulesPullbackTensorComp
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# The natural Quot-to-Grassmannian transformation

For a finite twisted-free ambient sheaf

`F = ∐_r 𝒪_{ℙⁿ_S}(-l)`

and a fixed twist `d`, the Grassmannian construction sends a quotient family
`F_T ↠ Q` to the kernel of the monomial map

`\mathcal O_T^m ⟶ π_*(Q(d))`.

This file first normalizes a raw `QuotientPullbackData` presentation from
`T ×_S ℙⁿ_S` to `ℙⁿ_T`, and then applies `Scheme.quotGrassmannianFreeMap`
(with a chosen reindexing of its monomial basis) and
`Modules.kernelGrassmannianPoint`.

The natural-transformation constructor is parameterized by exactly the inputs which are
not formal consequences of the definitions:

* finite local freeness of rank `q` of `π_*(Q(d))`;
* surjectivity of the monomial map on affine sections;
* compatibility of its kernel with arbitrary base change.

The second input is supplied uniformly by
`ProjectiveSpace.exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap`.  The first is
the rank/Cohomology-and-Base-Change theorem.  Invariance under equivalent quotient
presentations is proved here.  The last field isolates the remaining component-level
base-change coherence without imposing any choice of a representative of a Quotient class.

Main declarations:

* `Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver`;
* `Scheme.twistedFreeQuotGrassmannianFreeMap`;
* `Scheme.twistedFreeQuotGrassmannianKernelData_eq_of_r`;
* `Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom`;
* `ProjectiveSpace.exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap`;
* `Scheme.TwistedFreeQuotGrassmannianNatTransData`;
* `Scheme.TwistedFreeQuotGrassmannianNatTransData.natTrans`;
* `Scheme.TwistedFreeQuotGrassmannianCanonicalBaseChangeData`;
* `Scheme.TwistedFreeQuotGrassmannianQuotientNatTransData.ofCanonicalBaseChange`;
* `Scheme.TwistedFreeQuotGrassmannianQuotientNatTransData.natTrans`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Modules.QuotientPullbackData

variable {n r : ℕ} {l : ℤ} {S : Scheme.{u}}

/-- The ambient comparison used to read a twisted-free Quot presentation over an arbitrary
test scheme `T` as a quotient on the standard relative projective space `ℙⁿ_T`. -/
noncomputable def twistedFreeQuotientOnProjectiveSpaceAmbientIsoOver
    (T : Over S) :
    (Modules.pullback (projectiveSpaceOverMap n T.hom)).obj
        (twistedFreeAmbient (n := n) (r := r) (l := l)) ≅
      (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).inv).obj
        ((Modules.pullback
          ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
            (twistedFreeAmbient (n := n) (r := r) (l := l))) :=
  (Modules.pullbackPullbackIsoOfEq
    (projectiveSpaceOverBaseChangeIso n T.hom).inv
    ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom
    (projectiveSpaceOverMap n T.hom)
    (projectiveSpaceOverBaseChangeIso_inv_snd n T.hom)
    (twistedFreeAmbient (n := n) (r := r) (l := l))).symm

/-- A twisted-free Quot presentation, normalized to have the standard twisted-free source
on `ℙⁿ_T`. -/
noncomputable def twistedFreeQuotientOnProjectiveSpaceOver
    (T : Over S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T.left (-l)) ⟶
      quotDataOnProjectiveSpace
        (n := n) (S := S) (T := T)
        (twistedFreeAmbient (n := n) (r := r) (l := l)) a :=
  (projectiveSpaceOverTwistedFree_pullbackIso n r l T.hom).inv ≫
    (twistedFreeQuotientOnProjectiveSpaceAmbientIsoOver T).hom ≫
    (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).inv).map a.π

/-- An isomorphism of raw quotient sheaves induces an isomorphism of their normalized
projective-space sheaves. -/
noncomputable def quotDataOnProjectiveSpaceIsoOfIsoOver
    (T : Over S)
    {a b : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T} (e : a.Q ≅ b.Q) :
    quotDataOnProjectiveSpace
        (n := n) (S := S) (T := T)
        (twistedFreeAmbient (n := n) (r := r) (l := l)) a ≅
      quotDataOnProjectiveSpace
        (n := n) (S := S) (T := T)
        (twistedFreeAmbient (n := n) (r := r) (l := l)) b :=
  (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).inv).mapIso e

/-- Normalizing quotient presentations preserves a compatible isomorphism of their
targets. -/
lemma twistedFreeQuotientOnProjectiveSpaceOver_comp_iso
    (T : Over S)
    {a b : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T} (e : a.Q ≅ b.Q) (h : a.π ≫ e.hom = b.π) :
    twistedFreeQuotientOnProjectiveSpaceOver T a ≫
        (quotDataOnProjectiveSpaceIsoOfIsoOver T e).hom =
      twistedFreeQuotientOnProjectiveSpaceOver T b := by
  dsimp only [twistedFreeQuotientOnProjectiveSpaceOver,
    quotDataOnProjectiveSpaceIsoOfIsoOver, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp, h]

/-- Normalization preserves epimorphy of the quotient presentation. -/
lemma twistedFreeQuotientOnProjectiveSpaceOver_epi
    (T : Over S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    Epi (twistedFreeQuotientOnProjectiveSpaceOver T a) := by
  haveI : Epi a.π := a.epi
  dsimp only [twistedFreeQuotientOnProjectiveSpaceOver]
  infer_instance

/-- The normalized quotient sheaf is quasicoherent. -/
lemma quotDataOnProjectiveSpace_isQuasicoherent_over
    (T : Over S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (quotDataOnProjectiveSpace
      (n := n) (S := S) (T := T)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a).IsQuasicoherent := by
  letI : a.Q.IsQuasicoherent := a.isQuasicoherent
  change ((Modules.pullback
    (projectiveSpaceOverBaseChangeIso n T.hom).inv).obj a.Q).IsQuasicoherent
  infer_instance

/-- The normalized quotient sheaf is finitely presented. -/
lemma quotDataOnProjectiveSpace_isFinitePresentation_over
    (T : Over S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (quotDataOnProjectiveSpace
      (n := n) (S := S) (T := T)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a).IsFinitePresentation := by
  letI : a.Q.IsFinitePresentation := a.isFinitePresentation
  change ((Modules.pullback
    (projectiveSpaceOverBaseChangeIso n T.hom).inv).obj a.Q).IsFinitePresentation
  infer_instance

/-- Normalizing a Quot presentation preserves flatness over the parameter scheme. -/
lemma quotDataOnProjectiveSpace_flatOver_over
    (T : Over S)
    (a : QuotientPullbackData (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (quotDataOnProjectiveSpace
      (n := n) (S := S) (T := T)
      (twistedFreeAmbient (n := n) (r := r) (l := l)) a).FlatOver
        (projectiveSpaceOverπ n T.left) := by
  exact FlatOver.pullback_isIso
    (projectiveSpaceOverBaseChangeIso n T.hom).inv a.Q
    (projectiveSpaceOverBaseChangeIso_inv_fst n T.hom) a.flatOver

end Modules.QuotientPullbackData

namespace Modules

/-- The canonical base-change morphism for pushforward of module sheaves around a
commutative square.  It is the mate of the pulled-back counit; no cartesianness or
base-change theorem is assumed in its definition. -/
noncomputable def pushforwardBaseChangeHomOfComm
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules) :
    (pullback g).obj ((pushforward p).obj M) ⟶
      (pushforward p').obj ((pullback G).obj M) :=
  (pullbackPushforwardAdjunction p').homEquiv _ _
    ((pullbackComp p' g).hom.app ((pushforward p).obj M) ≫
      (pullbackCongr h.symm).hom.app ((pushforward p).obj M) ≫
      (pullbackComp G p).inv.app ((pushforward p).obj M) ≫
      (pullback G).map ((pullbackPushforwardAdjunction p).counit.app M))

/-- Applying the pullback--pushforward counit to the pullback of a global section recovers
the original section. -/
lemma counit_app_top_pullbackGlobalSections
    {X T : Scheme.{u}} (p : X ⟶ T) (M : X.Modules) (s : Γ(M, ⊤)) :
    Hom.app ((pullbackPushforwardAdjunction p).counit.app M) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections p ((pushforward p).obj M)
          (show Γ((pushforward p).obj M, ⊤) from s)) = s := by
  rw [pullbackGlobalSections_eq_unit_app]
  have htri := (pullbackPushforwardAdjunction p).right_triangle_components M
  have happ := congrArg
    (fun k : (pushforward p).obj M ⟶ (pushforward p).obj M ↦
      Hom.app k ⊤ (show Γ((pushforward p).obj M, ⊤) from s)) htri
  exact happ

/-- On global sections, the canonical pushforward base-change mate is the ordinary
pullback of sections around the upper horizontal map of the square. -/
lemma pushforwardBaseChangeHomOfComm_app_top_pullbackGlobalSections
    {X X' T T' : Scheme.{u}}
    (p : X ⟶ T) (p' : X' ⟶ T') (g : T' ⟶ T) (G : X' ⟶ X)
    (h : G ≫ p = p' ≫ g) (M : X.Modules) (s : Γ(M, ⊤)) :
    Hom.app (pushforwardBaseChangeHomOfComm p p' g G h M) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections g ((pushforward p).obj M)
          (show Γ((pushforward p).obj M, ⊤) from s)) =
      _root_.Scheme.Modules.pullbackGlobalSections G M s := by
  rw [pullbackGlobalSections_eq_unit_app G M s]
  rw [pullbackGlobalSections_eq_unit_app g ((pushforward p).obj M)
    (show Γ((pushforward p).obj M, ⊤) from s)]
  simp only [pushforwardBaseChangeHomOfComm, Adjunction.homEquiv_unit]
  let N := (pushforward p).obj M
  let sN : Γ(N, ⊤) := s
  let e := Hom.pullbackCompCongrIso p' g G p h.symm N
  change Hom.app ((pullback G).map
      ((pullbackPushforwardAdjunction p).counit.app M)) ⊤
      (Hom.app e.hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections p' ((pullback g).obj N)
          (_root_.Scheme.Modules.pullbackGlobalSections g N sN))) =
    _root_.Scheme.Modules.pullbackGlobalSections G M s
  rw [AlgebraicGeometry.pullbackGlobalSections_compCongrIso
    p' g G p h.symm N sN]
  calc
    _ = _root_.Scheme.Modules.pullbackGlobalSections G M
        (Hom.app ((pullbackPushforwardAdjunction p).counit.app M) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections p N sN)) :=
      pullbackGlobalSections_naturality G
        ((pullbackPushforwardAdjunction p).counit.app M)
        (_root_.Scheme.Modules.pullbackGlobalSections p N sN)
    _ = _ := congrArg (_root_.Scheme.Modules.pullbackGlobalSections G M)
      (by simpa only [N, sN] using counit_app_top_pullbackGlobalSections p M s)

/-- A family of global sections whose pullbacks agree through a target morphism gives a
commuting square between the associated maps out of free sheaves. -/
lemma pullback_freeHomOfSections_comp
    {X Y : Scheme.{u}} (g : X ⟶ Y) {I : Type u} {M : Y.Modules}
    {N : X.Modules} (s : I → Γ(M, ⊤)) (s' : I → Γ(N, ⊤))
    (β : (pullback g).obj M ⟶ N)
    (h : ∀ i, Hom.app β ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections g M (s i)) = s' i) :
    (pullbackFreeIso g I).inv ≫ (pullback g).map (freeHomOfSections s) ≫ β =
      freeHomOfSections s' := by
  apply AlgebraicGeometry.Scheme.free_hom_ext
  intro i
  have hs : Hom.app (freeHomOfSections s) ⊤
      (AlgebraicGeometry.Scheme.freeGenSection Y i) = s i := by
    simp only [AlgebraicGeometry.Scheme.freeGenSection, freeHomOfSections]
    change ((SheafOfModules.freeHomEquiv M) (freeHomOfSections s) i).val (op ⊤) = s i
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
    exact (sectionsTopEquiv M).apply_symm_apply (s i)
  have hs' : Hom.app (freeHomOfSections s') ⊤
      (AlgebraicGeometry.Scheme.freeGenSection X i) = s' i := by
    simp only [AlgebraicGeometry.Scheme.freeGenSection, freeHomOfSections]
    change ((SheafOfModules.freeHomEquiv N) (freeHomOfSections s') i).val (op ⊤) = s' i
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
    exact (sectionsTopEquiv N).apply_symm_apply (s' i)
  change Hom.app β ⊤
      (Hom.app ((pullback g).map (freeHomOfSections s)) ⊤
        (Hom.app (pullbackFreeIso g I).inv ⊤
          (AlgebraicGeometry.Scheme.freeGenSection X i))) =
    Hom.app (freeHomOfSections s') ⊤
      (AlgebraicGeometry.Scheme.freeGenSection X i)
  rw [AlgebraicGeometry.Scheme.pullbackFreeIso_inv_freeGenSection]
  have hnat := AlgebraicGeometry.Scheme.unit_app_naturality_top g
    (freeHomOfSections s) (AlgebraicGeometry.Scheme.freeGenSection Y i)
  calc
    _ = Hom.app β ⊤
        ((((pullbackPushforwardAdjunction g).unit.app M).app ⊤)
          (Hom.app (freeHomOfSections s) ⊤
            (AlgebraicGeometry.Scheme.freeGenSection Y i))) :=
      congrArg (fun z ↦ Hom.app β ⊤ z) hnat
    _ = Hom.app β ⊤ (_root_.Scheme.Modules.pullbackGlobalSections g M (s i)) := by
      rw [hs, pullbackGlobalSections_eq_unit_app]
    _ = s' i := h i
    _ = _ := hs'.symm

/-- The inverse canonical comparison from the pullback of a coproduct sends each
component inclusion to the pullback of the corresponding original inclusion. -/
@[reassoc]
lemma coproductPullbackIso_inv_ι {X Y : Scheme.{u}} (g : X ⟶ Y)
    {J : Type u} (F : J → Y.Modules) (F' : J → X.Modules)
    (e : ∀ j, (pullback g).obj (F j) ≅ F' j) (j : J) :
    Sigma.ι F' j ≫
        ((PreservesCoproduct.iso (pullback g) F ≪≫ Sigma.mapIso e).inv) =
      (e j).inv ≫ (pullback g).map (Sigma.ι F j) := by
  dsimp only [Iso.trans_inv]
  rw [Sigma.ι_mapIso_inv_assoc, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison]

/-- The forward pullback--coproduct comparison carries the pullback of each original
summand inclusion to the corresponding new summand inclusion. -/
lemma pullback_map_ι_coproductPullbackIso_hom {X Y : Scheme.{u}} (g : X ⟶ Y)
    {J : Type u} (F : J → Y.Modules) (F' : J → X.Modules)
    (e : ∀ j, (pullback g).obj (F j) ≅ F' j) (j : J) :
    (pullback g).map (Sigma.ι F j) ≫
        (PreservesCoproduct.iso (pullback g) F ≪≫ Sigma.mapIso e).hom =
      (e j).hom ≫ Sigma.ι F' j := by
  rw [← cancel_epi (e j).inv]
  rw [← Category.assoc, ← coproductPullbackIso_inv_ι g F F' e j]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- The inverse tensor--coproduct comparison sends a summand inclusion to the
corresponding tensor of that inclusion with the identity. -/
@[reassoc]
lemma ι_tensorCoproductIso_inv {X : Scheme.{u}} {J : Type u}
    (F : J → X.Modules) (G : X.Modules) (j : J) :
    Sigma.ι (fun j ↦ tensor (F j) G) j ≫ (tensorCoproductIso F G).inv =
      tensorMapLeft (Sigma.ι F j) G := by
  dsimp only [tensorCoproductIso, PreservesCoproduct.inv_hom]
  exact ι_comp_sigmaComparison (tensorRightFunctor G) F j

end Modules

/-- The normalized quotient sheaf underlying a twisted-free Quot presentation. -/
abbrev twistedFreeQuotientSheaf
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (projectiveSpaceOver n T.left).Modules :=
  quotDataOnProjectiveSpace
    (n := n) (S := S) (T := T)
    (Modules.QuotientPullbackData.twistedFreeAmbient
      (n := n) (r := r) (l := l)) a

/-- The pushforward of the `d`-th twist of a normalized twisted-free Quot family. -/
abbrev twistedFreeQuotientTwistPushforward
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) (d : ℕ) : T.left.Modules :=
  (Modules.pushforward (projectiveSpaceOverπ n T.left)).obj
    (projectiveSpaceOverTwistModule
      (twistedFreeQuotientSheaf n S l r a) (d : ℤ))

/-- A compatible isomorphism of quotient presentations induces an isomorphism of their
twisted pushforwards. -/
noncomputable def twistedFreeQuotientTwistPushforwardIsoOfIso
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    {a b : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T} (e : a.Q ≅ b.Q) (d : ℕ) :
    twistedFreeQuotientTwistPushforward n S l r a d ≅
      twistedFreeQuotientTwistPushforward n S l r b d :=
  (Modules.pushforward (projectiveSpaceOverπ n T.left)).mapIso
    (Modules.tensorLeftIso
      (Modules.QuotientPullbackData.quotDataOnProjectiveSpaceIsoOfIsoOver T e)
      (projectiveSpaceOverTwist n T.left (d : ℤ)))

/-- Twisting the normalized quotient sheaf commutes with pullback of a Quot datum. -/
noncomputable def twistedFreeQuotientTwistPullbackIso
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g.left)).obj
        (projectiveSpaceOverTwistModule
          (twistedFreeQuotientSheaf n S l r a) (d : ℤ)) ≅
      projectiveSpaceOverTwistModule
        (twistedFreeQuotientSheaf n S l r (a.pullback g)) (d : ℤ) :=
  projectiveSpaceOverTwistModule_pullbackIso_nat n g.left
      (twistedFreeQuotientSheaf n S l r a) d ≪≫
    Modules.tensorLeftIso
      (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).symm
      (projectiveSpaceOverTwist n T'.left (d : ℤ))

/-- The natural-degree twist comparison is natural in the module being twisted. -/
lemma projectiveSpaceOverTwistModule_pullbackIso_nat_naturality
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S)
    {F Q : (projectiveSpaceOver n S).Modules} (ψ : F ⟶ Q) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft ψ (projectiveSpaceOverTwist n S (d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d).hom =
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g F d).hom ≫
        Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverMap n g)).map ψ)
          (projectiveSpaceOverTwist n T (d : ℤ)) := by
  dsimp only [projectiveSpaceOverTwistModule_pullbackIso_nat, Iso.trans_hom,
    Modules.tensorRightIso]
  change (Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft ψ (projectiveSpaceOverTwist n S (d : ℤ))) ≫
        Modules.pullbackTensorComparison (projectiveSpaceOverMap n g) Q
          (projectiveSpaceOverTwist n S (d : ℤ)) ≫
        Modules.tensorMapRight
          ((Modules.pullback (projectiveSpaceOverMap n g)).obj Q)
          (projectiveSpaceOverTwist_pullbackIso n g (d : ℤ)).hom =
      Modules.pullbackTensorComparison (projectiveSpaceOverMap n g) F
          (projectiveSpaceOverTwist n S (d : ℤ)) ≫
        Modules.tensorMapRight
          ((Modules.pullback (projectiveSpaceOverMap n g)).obj F)
          (projectiveSpaceOverTwist_pullbackIso n g (d : ℤ)).hom ≫
        Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverMap n g)).map ψ)
          (projectiveSpaceOverTwist n T (d : ℤ))
  rw [← Category.assoc, Modules.pullbackTensorComparison_naturality_left]
  simp only [Category.assoc]
  congr 1
  exact (Modules.tensorMap_exchange _ _).symm

/-- Naturality of the twist pullback comparison remains compatible after a chosen
identification of the pulled-back target module. -/
lemma projectiveSpaceOverTwistModule_pullbackIso_nat_naturality_comp
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S)
    {F Q : (projectiveSpaceOver n S).Modules}
    (Q' : (projectiveSpaceOver n T).Modules)
    (e : (Modules.pullback (projectiveSpaceOverMap n g)).obj Q ≅ Q')
    (ψ : F ⟶ Q) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft ψ (projectiveSpaceOverTwist n S (d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d ≪≫
          Modules.tensorLeftIso e (projectiveSpaceOverTwist n T (d : ℤ))).hom =
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g F d).hom ≫
        Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverMap n g)).map ψ ≫ e.hom)
          (projectiveSpaceOverTwist n T (d : ℤ)) := by
  let t := Modules.tensorMapLeft e.hom
    (projectiveSpaceOverTwist n T (d : ℤ))
  have hn := projectiveSpaceOverTwistModule_pullbackIso_nat_naturality n g ψ d
  calc
    _ = ((Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft ψ (projectiveSpaceOverTwist n S (d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d).hom) ≫ t := rfl
    _ = ((projectiveSpaceOverTwistModule_pullbackIso_nat n g F d).hom ≫
        Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverMap n g)).map ψ)
          (projectiveSpaceOverTwist n T (d : ℤ))) ≫ t :=
      congrArg (fun k ↦ k ≫ t) hn
    _ = _ := by
      dsimp only [t]
      simp only [Category.assoc, ← Modules.tensorMapLeft_comp]

/-- Adding a natural-degree twist on relative projective space is compatible with
arbitrary change of the base scheme. -/
lemma projectiveSpaceOverTwist_addIso_nat_pullback
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) (a : ℤ) (d : ℕ) :
    let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g
        (projectiveSpaceOverTwist n S a) d ≪≫
      Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g a)
        (projectiveSpaceOverTwist n T (d : ℤ))
    E.hom ≫ (projectiveSpaceOverTwist_addIso_nat n T a d).hom =
      (Modules.pullback (projectiveSpaceOverMap n g)).map
          (projectiveSpaceOverTwist_addIso_nat n S a d).hom ≫
        (projectiveSpaceOverTwist_pullbackIso n g (a + (d : ℤ))).hom := by
  dsimp only
  let A := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let hS : projectiveSpaceOver n S ⟶ projectiveSpace n := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let hT : projectiveSpaceOver n T ⟶ projectiveSpace n := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let f : projectiveSpaceOver n T ⟶ projectiveSpaceOver n S :=
    projectiveSpaceOverMap n g
  let h : f ≫ hS = hT := projectiveSpaceOverMap_absolute_snd n g
  let Oa : (projectiveSpace n).Modules :=
    ProjectiveSpectrum.Twist.twist A a
  let Od : (projectiveSpace n).Modules :=
    ProjectiveSpectrum.Twist.twist A (d : ℤ)
  let Oad : (projectiveSpace n).Modules :=
    ProjectiveSpectrum.Twist.twist A (a + (d : ℤ))
  let μ : Modules.tensor Oa Od ⟶ Oad :=
    (ProjectiveSpectrum.Twist.polynomialMultiplyIso
      (R := ULift.{u} ℤ) (Fin (n + 1)) a (d : ℤ)).hom
  let eA := Modules.pullbackComp f hS ≪≫ Modules.pullbackCongr h
  let eD := Modules.pullbackComp f hS ≪≫ Modules.pullbackCongr h
  let eAD := Modules.pullbackComp f hS ≪≫ Modules.pullbackCongr h
  haveI : IsIso (Modules.pullbackTensorComparison hS Oa Od) :=
    MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) hS Oa d
  haveI : IsIso (Modules.pullbackTensorComparison hT Oa Od) :=
    MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) hT Oa d
  have hinv := Modules.pullbackTensorComparison_comp_congr_inv f hS hT h Oa Od
  have hnat := eAD.hom.naturality μ
  dsimp only [projectiveSpaceOverTwist_addIso_nat,
    projectiveSpaceOverTwistModule_pullbackIso_nat,
    projectiveSpaceOverTwist_pullbackIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Modules.tensorLeftIso, Modules.tensorRightIso]
  simp only [asIso_hom, asIso_inv, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  change Modules.pullbackTensorComparison f ((Modules.pullback hS).obj Oa)
          ((Modules.pullback hS).obj Od) ≫
        Modules.tensorMapRight ((Modules.pullback f).obj ((Modules.pullback hS).obj Oa))
          (eD.hom.app Od) ≫
        Modules.tensorMapLeft (eA.hom.app Oa) ((Modules.pullback hT).obj Od) ≫
        inv (Modules.pullbackTensorComparison hT Oa Od) ≫
        (Modules.pullback hT).map μ =
      (Modules.pullback f).map (inv (Modules.pullbackTensorComparison hS Oa Od)) ≫
        (Modules.pullback f).map ((Modules.pullback hS).map μ) ≫
        eAD.hom.app Oad
  have hex :
      Modules.tensorMapRight
          ((Modules.pullback f).obj ((Modules.pullback hS).obj Oa))
          (eD.hom.app Od) ≫
        Modules.tensorMapLeft (eA.hom.app Oa) ((Modules.pullback hT).obj Od) =
      Modules.tensorMapLeft (eA.hom.app Oa)
          ((Modules.pullback f).obj ((Modules.pullback hS).obj Od)) ≫
        Modules.tensorMapRight ((Modules.pullback hT).obj Oa) (eD.hom.app Od) :=
    Modules.tensorMap_exchange _ _
  slice_lhs 2 3 => rw [hex]
  simp only [Category.assoc]
  dsimp only [eA, eD, Iso.trans_hom, NatTrans.comp_app]
  slice_lhs 1 4 => rw [hinv]
  dsimp only [eAD, Iso.trans_hom, NatTrans.comp_app, Functor.comp_map] at hnat ⊢
  simp only [Category.assoc]
  have hnat' :
      (Modules.pullback f).map ((Modules.pullback hS).map μ) ≫
          (Modules.pullbackComp f hS).hom.app Oad ≫
          (Modules.pullbackCongr h).hom.app Oad =
        (Modules.pullbackComp f hS).hom.app (Modules.tensor Oa Od) ≫
          (Modules.pullbackCongr h).hom.app (Modules.tensor Oa Od) ≫
          (Modules.pullback hT).map μ := by
    simpa only [Category.assoc] using hnat
  slice_lhs 2 4 => rw [← hnat']

/-- Inverse form of `projectiveSpaceOverTwist_addIso_nat_pullback`. -/
lemma projectiveSpaceOverTwist_addIso_nat_pullback_inv
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) (a : ℤ) (d : ℕ) :
    let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g
        (projectiveSpaceOverTwist n S a) d ≪≫
      Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g a)
        (projectiveSpaceOverTwist n T (d : ℤ))
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (projectiveSpaceOverTwist_addIso_nat n S a d).inv ≫ E.hom =
      (projectiveSpaceOverTwist_pullbackIso n g (a + (d : ℤ))).hom ≫
        (projectiveSpaceOverTwist_addIso_nat n T a d).inv := by
  dsimp only
  rw [← cancel_epi ((Modules.pullback (projectiveSpaceOverMap n g)).map
    (projectiveSpaceOverTwist_addIso_nat n S a d).hom)]
  slice_lhs 1 2 => rw [← Functor.map_comp, Iso.hom_inv_id,
    (Modules.pullback (projectiveSpaceOverMap n g)).map_id]
  simp only [Category.id_comp]
  rw [← cancel_mono (projectiveSpaceOverTwist_addIso_nat n T a d).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact projectiveSpaceOverTwist_addIso_nat_pullback n g a d

/-- Equality transport between two degrees commutes with the canonical pullback
comparison for twisting sheaves. -/
lemma projectiveSpaceOverTwist_pullbackIso_degree_eq_naturality
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S)
    (a b : ℤ) (h : a = b) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (eqToHom (congrArg (fun c : ℤ ↦ projectiveSpaceOverTwist n S c) h)) ≫
        (projectiveSpaceOverTwist_pullbackIso n g b).hom =
      (projectiveSpaceOverTwist_pullbackIso n g a).hom ≫
        eqToHom (congrArg (fun c : ℤ ↦ projectiveSpaceOverTwist n T c) h) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]
  rw [(Modules.pullback (projectiveSpaceOverMap n g)).map_id]
  exact Category.id_comp _

set_option maxHeartbeats 1000000 in
-- Expanding the three pullback-composition cells is elaboration-heavy but deterministic.
/-- The canonical pullback comparison for a twisting sheaf satisfies the composition
coherence for two successive changes of base. -/
lemma projectiveSpaceOverTwist_pullbackIso_comp_inv
    (n : ℕ) {S T U : Scheme.{u}} (g : T ⟶ S) (h : U ⟶ T)
    (d : ℤ) :
    (projectiveSpaceOverTwist_pullbackIso n h d).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n h)).map
        (projectiveSpaceOverTwist_pullbackIso n g d).inv ≫
      (Modules.pullbackComp (projectiveSpaceOverMap n h)
        (projectiveSpaceOverMap n g)).hom.app
          (projectiveSpaceOverTwist n S d) ≫
      (Modules.pullbackCongr
        (projectiveSpaceOverMap_comp n h g)).hom.app
          (projectiveSpaceOverTwist n S d) =
    (projectiveSpaceOverTwist_pullbackIso n (h ≫ g) d).inv := by
  let A := ProjectiveSpectrum.Twist.twist
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d
  let pS := Limits.pullback.snd (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let pT := Limits.pullback.snd (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let pU := Limits.pullback.snd (specULiftZIsTerminal.from U)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let f := projectiveSpaceOverMap n g
  let k := projectiveSpaceOverMap n h
  let fk := projectiveSpaceOverMap n (h ≫ g)
  let hg : f ≫ pS = pT := projectiveSpaceOverMap_absolute_snd n g
  let hh : k ≫ pT = pU := projectiveSpaceOverMap_absolute_snd n h
  let hcomp : k ≫ f = fk := projectiveSpaceOverMap_comp n h g
  let hkg : fk ≫ pS = pU := projectiveSpaceOverMap_absolute_snd n (h ≫ g)
  dsimp only [projectiveSpaceOverTwist_pullbackIso, Iso.trans_inv]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [projectiveSpaceOverTwist]
  change (Modules.pullbackCongr hh).inv.app A ≫
      (Modules.pullbackComp k pT).inv.app A ≫
      (Modules.pullback k).map ((Modules.pullbackCongr hg).inv.app A) ≫
      (Modules.pullback k).map ((Modules.pullbackComp f pS).inv.app A) ≫
      (Modules.pullbackComp k f).hom.app ((Modules.pullback pS).obj A) ≫
      (Modules.pullbackCongr hcomp).hom.app ((Modules.pullback pS).obj A) =
    (Modules.pullbackCongr hkg).inv.app A ≫
      (Modules.pullbackComp fk pS).inv.app A
  rw [show (Modules.pullbackCongr hg).inv.app A =
      (Modules.pullbackCongr hg.symm).hom.app A by
        dsimp only [Modules.pullbackCongr]
        rfl]
  slice_lhs 2 3 =>
    rw [Modules.pullbackComp_inv_app_map_pullbackCongr_hom hg.symm A]
  simp only [Category.assoc]
  slice_lhs 3 5 =>
    rw [Modules.pullbackComp_assoc_inv_hom_app k f pS A]
  simp only [Category.assoc]
  slice_lhs 4 5 =>
    rw [Modules.pullbackComp_inv_app_pullbackCongr_hom hcomp A]
  dsimp only [Modules.pullbackCongr]
  simp only [Category.assoc, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_trans_assoc]

set_option maxHeartbeats 1000000 in
-- Coproduct extensionality elaborates the single-twist coherence once per summand type.
/-- The canonical pullback comparison for a finite twisted-free sheaf satisfies the
composition coherence for two successive changes of base. -/
lemma projectiveSpaceOverTwistedFree_pullbackIso_comp_inv
    (n r : ℕ) (l : ℤ) {S T U : Scheme.{u}}
    (g : T ⟶ S) (h : U ⟶ T) :
    (projectiveSpaceOverTwistedFree_pullbackIso n r l h).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n h)).map
        (projectiveSpaceOverTwistedFree_pullbackIso n r l g).inv ≫
      (Modules.pullbackComp (projectiveSpaceOverMap n h)
        (projectiveSpaceOverMap n g)).hom.app
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) ≫
      (Modules.pullbackCongr
        (projectiveSpaceOverMap_comp n h g)).hom.app
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) =
    (projectiveSpaceOverTwistedFree_pullbackIso n r l (h ≫ g)).inv := by
  let p := projectiveSpaceOverMap n h
  let q := projectiveSpaceOverMap n g
  let pq := projectiveSpaceOverMap n (h ≫ g)
  let FS := fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)
  let FT := fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let FU := fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n U (-l)
  let eP := fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist_pullbackIso n h (-l)
  let eQ := fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist_pullbackIso n g (-l)
  let ePQ := fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist_pullbackIso n (h ≫ g) (-l)
  let EP := projectiveSpaceOverTwistedFree_pullbackIso n r l h
  let EQ := projectiveSpaceOverTwistedFree_pullbackIso n r l g
  let EPQ := projectiveSpaceOverTwistedFree_pullbackIso n r l (h ≫ g)
  let C := (Modules.pullbackComp p q).hom.app (∐ FS)
  let D := (Modules.pullbackCongr
    (projectiveSpaceOverMap_comp n h g)).hom.app (∐ FS)
  apply Sigma.hom_ext
  intro j
  have hP := Modules.coproductPullbackIso_inv_ι p FT FU eP j
  have hQ := Modules.coproductPullbackIso_inv_ι q FS FT eQ j
  have hPQ := Modules.coproductPullbackIso_inv_ι pq FS FU ePQ j
  have hP' : Sigma.ι FU j ≫ EP.inv =
      (eP j).inv ≫ (Modules.pullback p).map (Sigma.ι FT j) := by
    change Sigma.ι FU j ≫
      (PreservesCoproduct.iso (Modules.pullback p) FT ≪≫
        Sigma.mapIso eP).inv = _
    exact hP
  have hQ' : Sigma.ι FT j ≫ EQ.inv =
      (eQ j).inv ≫ (Modules.pullback q).map (Sigma.ι FS j) := by
    change Sigma.ι FT j ≫
      (PreservesCoproduct.iso (Modules.pullback q) FS ≪≫
        Sigma.mapIso eQ).inv = _
    exact hQ
  have hPQ' : Sigma.ι FU j ≫ EPQ.inv =
      (ePQ j).inv ≫ (Modules.pullback pq).map (Sigma.ι FS j) := by
    change Sigma.ι FU j ≫
      (PreservesCoproduct.iso (Modules.pullback pq) FS ≪≫
        Sigma.mapIso ePQ).inv = _
    exact hPQ
  have hC := (Modules.pullbackComp p q).hom.naturality (Sigma.ι FS j)
  have hD := (Modules.pullbackCongr
    (projectiveSpaceOverMap_comp n h g)).hom.naturality (Sigma.ι FS j)
  have htwist := projectiveSpaceOverTwist_pullbackIso_comp_inv
    n g h (-l)
  change Sigma.ι FU j ≫ EP.inv ≫ (Modules.pullback p).map EQ.inv ≫ C ≫ D =
    Sigma.ι FU j ≫ EPQ.inv
  slice_lhs 1 2 => rw [hP']
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, hQ', Functor.map_comp]
  slice_lhs 3 4 => erw [hC]
  simp only [Category.assoc]
  slice_lhs 4 5 => erw [hD]
  rw [hPQ']
  slice_lhs 1 4 => rw [htwist]

/-- Composition coherence for the twisted-free pullback comparison, with a specified
identification of the composite base morphism. -/
lemma projectiveSpaceOverTwistedFree_pullbackIso_comp_inv_of_eq
    (n r : ℕ) (l : ℤ) {S T U : Scheme.{u}}
    (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (hk : h ≫ g = k) :
    (projectiveSpaceOverTwistedFree_pullbackIso n r l h).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n h)).map
        (projectiveSpaceOverTwistedFree_pullbackIso n r l g).inv ≫
      (Modules.pullbackComp (projectiveSpaceOverMap n h)
        (projectiveSpaceOverMap n g)).hom.app
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) ≫
      (Modules.pullbackCongr
        ((projectiveSpaceOverMap_comp n h g).trans
          (congrArg (projectiveSpaceOverMap n) hk))).hom.app
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) =
    (projectiveSpaceOverTwistedFree_pullbackIso n r l k).inv := by
  subst k
  exact projectiveSpaceOverTwistedFree_pullbackIso_comp_inv n r l g h

set_option maxHeartbeats 1000000 in
-- The normalizing comparison expands to seven pseudofunctor coherence cells.
/-- Normalization from a fibre product to relative projective space commutes with
pullback of the parameter scheme, before applying any quotient morphism. -/
lemma quotDataOnProjectiveSpace_normalization_pullback_coherence
    (n : ℕ) (S : Scheme.{u}) {T T' : Over S} (g : T' ⟶ T)
    (F : (projectiveSpaceOver n S).Modules) :
    let f := projectiveSpaceOverπ n S
    let R := (Over.pullback f).obj T
    let R' := (Over.pullback f).obj T'
    let E := projectiveSpaceOverBaseChangeIso n T.hom
    let E' := projectiveSpaceOverBaseChangeIso n T'.hom
    let G := ((Over.pullback f).map g).left
    let t := projectiveSpaceOverMap n T.hom
    let t' := projectiveSpaceOverMap n T'.hom
    let gl := projectiveSpaceOverMap n g.left
    let hgl : gl ≫ t = t' := by
      rw [projectiveSpaceOverMap_comp, Over.w g]
    let C := (Modules.pullbackComp gl t).app F ≪≫
      (Modules.pullbackCongr hgl).app F
    let N := (Modules.pullbackPullbackIsoOfEq E.inv R.hom t
      (projectiveSpaceOverBaseChangeIso_inv_snd n T.hom) F).symm
    let N' := (Modules.pullbackPullbackIsoOfEq E'.inv R'.hom t'
      (projectiveSpaceOverBaseChangeIso_inv_snd n T'.hom) F).symm
    let Q := (Modules.pullbackComp gl E.inv).app ((Modules.pullback R.hom).obj F) ≪≫
      (Modules.pullbackCongr
        (projectiveSpaceOverBaseChangeIso_inv_naturality n g)).symm.app
          ((Modules.pullback R.hom).obj F) ≪≫
      (Modules.pullbackComp E'.inv G).symm.app ((Modules.pullback R.hom).obj F)
    C.inv ≫ (Modules.pullback gl).map N.hom ≫ Q.hom =
      N'.hom ≫ (Modules.pullback E'.inv).map
        (Modules.PullbackQuotient.pullbackComparison F ((Over.pullback f).map g)).hom := by
  dsimp only
  let f := projectiveSpaceOverπ n S
  let R := (Over.pullback f).obj T
  let R' := (Over.pullback f).obj T'
  let E := projectiveSpaceOverBaseChangeIso n T.hom
  let E' := projectiveSpaceOverBaseChangeIso n T'.hom
  let G := ((Over.pullback f).map g).left
  let t := projectiveSpaceOverMap n T.hom
  let t' := projectiveSpaceOverMap n T'.hom
  let gl := projectiveSpaceOverMap n g.left
  let hT : E.inv ≫ R.hom = t :=
    projectiveSpaceOverBaseChangeIso_inv_snd n T.hom
  let hT' : E'.inv ≫ R'.hom = t' :=
    projectiveSpaceOverBaseChangeIso_inv_snd n T'.hom
  let hgl : gl ≫ t = t' := by
    rw [projectiveSpaceOverMap_comp, Over.w g]
  let hEG : E'.inv ≫ G = gl ≫ E.inv :=
    projectiveSpaceOverBaseChangeIso_inv_naturality n g
  let hR : G ≫ R.hom = R'.hom := Over.w ((Over.pullback f).map g)
  dsimp only [Modules.pullbackPullbackIsoOfEq,
    Modules.PullbackQuotient.pullbackComparison,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  simp only [Functor.map_comp, Category.assoc]
  change (Modules.pullbackCongr hgl).inv.app F ≫
      (Modules.pullbackComp gl t).inv.app F ≫
      (Modules.pullback gl).map ((Modules.pullbackCongr hT).inv.app F) ≫
      (Modules.pullback gl).map ((Modules.pullbackComp E.inv R.hom).inv.app F) ≫
      (Modules.pullbackComp gl E.inv).hom.app ((Modules.pullback R.hom).obj F) ≫
      (Modules.pullbackCongr hEG).inv.app ((Modules.pullback R.hom).obj F) ≫
      (Modules.pullbackComp E'.inv G).inv.app ((Modules.pullback R.hom).obj F) =
    (Modules.pullbackCongr hT').inv.app F ≫
      (Modules.pullbackComp E'.inv R'.hom).inv.app F ≫
      (Modules.pullback E'.inv).map ((Modules.pullbackCongr hR).inv.app F) ≫
      (Modules.pullback E'.inv).map ((Modules.pullbackComp G R.hom).inv.app F)
  rw [show (Modules.pullbackCongr hT).inv.app F =
      (Modules.pullbackCongr hT.symm).hom.app F by
        dsimp only [Modules.pullbackCongr]
        rfl]
  slice_lhs 2 3 =>
    rw [Modules.pullbackComp_inv_app_map_pullbackCongr_hom hT.symm F]
  simp only [Category.assoc]
  slice_lhs 3 5 =>
    rw [Modules.pullbackComp_assoc_inv_hom_app gl E.inv R.hom F]
  rw [show (Modules.pullbackCongr hEG).inv.app
      ((Modules.pullback R.hom).obj F) =
      (Modules.pullbackCongr hEG.symm).hom.app
        ((Modules.pullback R.hom).obj F) by
        dsimp only [Modules.pullbackCongr]
        rfl]
  simp only [Category.assoc]
  slice_lhs 4 5 =>
    rw [Modules.pullbackComp_inv_app_pullbackCongr_hom hEG.symm F]
  rw [show (Modules.pullbackCongr hR).inv.app F =
      (Modules.pullbackCongr hR.symm).hom.app F by
        dsimp only [Modules.pullbackCongr]
        rfl]
  slice_rhs 2 3 =>
    rw [Modules.pullbackComp_inv_app_map_pullbackCongr_hom hR.symm F]
  simp only [Category.assoc]
  rw [Modules.pullbackComp_inv_app_map_inv_app E'.inv G R.hom F]
  dsimp only [Modules.pullbackCongr]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_trans_assoc]

namespace Modules.QuotientPullbackData

set_option maxHeartbeats 5000000 in
-- Expanding both normalizations exposes several nested pullback associators.
/-- The normalized twisted-free quotient morphism commutes with arbitrary change of the
parameter scheme. -/
lemma twistedFreeQuotientOnProjectiveSpaceOver_pullback
    (n r : ℕ) (l : ℤ) (S : Scheme.{u})
    {T T' : Over S} (g : T' ⟶ T)
    (a : QuotientPullbackData
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) :
    (projectiveSpaceOverTwistedFree_pullbackIso n r l g.left).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n g.left)).map
        (twistedFreeQuotientOnProjectiveSpaceOver T a) ≫
      (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).inv =
    twistedFreeQuotientOnProjectiveSpaceOver T' (a.pullback g) := by
  let F := twistedFreeAmbient (n := n) (r := r) (l := l) (S := S)
  let f := projectiveSpaceOverπ n S
  let R := (Over.pullback f).obj T
  let R' := (Over.pullback f).obj T'
  let E := projectiveSpaceOverBaseChangeIso n T.hom
  let E' := projectiveSpaceOverBaseChangeIso n T'.hom
  let G := ((Over.pullback f).map g).left
  let t := projectiveSpaceOverMap n T.hom
  let t' := projectiveSpaceOverMap n T'.hom
  let gl := projectiveSpaceOverMap n g.left
  let hgl : gl ≫ t = t' := by
    rw [projectiveSpaceOverMap_comp, Over.w g]
  let C := (Modules.pullbackComp gl t).app F ≪≫
    (Modules.pullbackCongr hgl).app F
  let N := (Modules.pullbackPullbackIsoOfEq E.inv R.hom t
    (projectiveSpaceOverBaseChangeIso_inv_snd n T.hom) F).symm
  let N' := (Modules.pullbackPullbackIsoOfEq E'.inv R'.hom t'
    (projectiveSpaceOverBaseChangeIso_inv_snd n T'.hom) F).symm
  let Qn := Modules.pullbackComp gl E.inv ≪≫
    (Modules.pullbackCongr
      (projectiveSpaceOverBaseChangeIso_inv_naturality n g)).symm ≪≫
    (Modules.pullbackComp E'.inv G).symm
  let eG := projectiveSpaceOverTwistedFree_pullbackIso n r l g.left
  let eT := projectiveSpaceOverTwistedFree_pullbackIso n r l T.hom
  let eT' := projectiveSpaceOverTwistedFree_pullbackIso n r l T'.hom
  let PBC := Modules.PullbackQuotient.pullbackComparison F
    ((Over.pullback f).map g)
  have hc := projectiveSpaceOverTwistedFree_pullbackIso_comp_inv_of_eq
    n r l T.hom g.left T'.hom (Over.w g)
  change eG.inv ≫ (Modules.pullback gl).map eT.inv ≫ C.hom = eT'.inv at hc
  have hn := quotDataOnProjectiveSpace_normalization_pullback_coherence n S g F
  change C.inv ≫ (Modules.pullback gl).map N.hom ≫
      Qn.hom.app ((Modules.pullback R.hom).obj F) =
    N'.hom ≫ (Modules.pullback E'.inv).map PBC.hom at hn
  have hq := Qn.hom.naturality a.π
  have hq' :
      (Modules.pullback gl).map ((Modules.pullback E.inv).map a.π) ≫
          Qn.hom.app a.Q =
        Qn.hom.app ((Modules.pullback R.hom).obj F) ≫
          (Modules.pullback E'.inv).map ((Modules.pullback G).map a.π) := by
    simpa only [Functor.comp_map] using hq
  have hpaste :
      eG.inv ≫ (Modules.pullback gl).map eT.inv ≫
        (Modules.pullback gl).map N.hom ≫
        (Modules.pullback gl).map ((Modules.pullback E.inv).map a.π) ≫
        Qn.hom.app a.Q =
      eT'.inv ≫ N'.hom ≫
        (Modules.pullback E'.inv).map PBC.hom ≫
        (Modules.pullback E'.inv).map ((Modules.pullback G).map a.π) := by
    rw [hq']
    calc
      _ = (eG.inv ≫ (Modules.pullback gl).map eT.inv ≫ C.hom) ≫
          (C.inv ≫ (Modules.pullback gl).map N.hom ≫
            Qn.hom.app ((Modules.pullback R.hom).obj F)) ≫
          (Modules.pullback E'.inv).map ((Modules.pullback G).map a.π) := by simp
      _ = _ := by rw [hc, hn, Category.assoc]
  have hT : twistedFreeQuotientOnProjectiveSpaceOver T a =
      eT.inv ≫ N.hom ≫ (Modules.pullback E.inv).map a.π := by rfl
  have hT' : twistedFreeQuotientOnProjectiveSpaceOver T' (a.pullback g) =
      eT'.inv ≫ N'.hom ≫
        (Modules.pullback E'.inv).map (a.pullback g).π := by rfl
  have hQI :
      (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).inv =
        Qn.hom.app a.Q := by rfl
  have hπ : (a.pullback g).π =
      PBC.hom ≫ (Modules.pullback G).map a.π := by rfl
  have hT'' : twistedFreeQuotientOnProjectiveSpaceOver T' (a.pullback g) =
      eT'.inv ≫ N'.hom ≫
        (Modules.pullback E'.inv).map PBC.hom ≫
          (Modules.pullback E'.inv).map ((Modules.pullback G).map a.π) := by
    rw [hT', hπ]
    dsimp only [QuotientPullbackData.pullback, quotDataOnProjectiveSpace]
    rw [Functor.map_comp]
  rw [hT, hT'', hQI]
  dsimp only [quotDataOnProjectiveSpace, QuotientPullbackData.pullback]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  exact hpaste

end Modules.QuotientPullbackData

/-- The degree-identification part of a single twisted-free monomial section commutes
with arbitrary base change. -/
lemma twistedFreeSingleMonomialCore_pullback (n : ℕ)
    {S T : Scheme.{u}} (g : T ⟶ S) (l : ℤ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    Modules.Hom.app
        (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g)
          (projectiveSpaceOverTwist n S (-l + (d : ℤ)))
          (Modules.Hom.app
            (eqToHom (congrArg
              (fun c : ℤ ↦ projectiveSpaceOverTwist n S c)
              (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
            (he ▸ twistMonomialSection n S e i))) =
      Modules.Hom.app
        (eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
          (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
        (he ▸ twistMonomialSection n T e i) := by
  let f := projectiveSpaceOverMap n g
  let FS := fun c : ℤ ↦ projectiveSpaceOverTwist n S c
  let FT := fun c : ℤ ↦ projectiveSpaceOverTwist n T c
  let hneg : (d : ℤ) - l = -l + (d : ℤ) :=
    (neg_add_eq_sub l (d : ℤ)).symm
  let enS : FS ((d : ℤ) - l) ⟶ FS (-l + (d : ℤ)) :=
    eqToHom (congrArg FS hneg)
  let enT : FT ((d : ℤ) - l) ⟶ FT (-l + (d : ℤ)) :=
    eqToHom (congrArg FT hneg)
  let ehS : FS (e : ℤ) ⟶ FS ((d : ℤ) - l) :=
    eqToHom (congrArg FS he.symm)
  let ehT : FT (e : ℤ) ⟶ FT ((d : ℤ) - l) :=
    eqToHom (congrArg FT he.symm)
  let xS := twistMonomialSection n S e i
  let xT := twistMonomialSection n T e i
  have htransport (X : Scheme.{u}) (F : ℤ → X.Modules)
      {a b : ℤ} (h : a = b) (x : Γ(F b, ⊤)) :
      (h ▸ x) = Modules.Hom.app
        (eqToHom (congrArg F h.symm)) ⊤ x := by
    subst b
    rfl
  have hheS : (he ▸ xS) = Modules.Hom.app ehS ⊤ xS := by
    exact htransport (projectiveSpaceOver n S) FS he xS
  have hheT : (he ▸ xT) = Modules.Hom.app ehT ⊤ xT := by
    exact htransport (projectiveSpaceOver n T) FT he xT
  have hnatNeg := projectiveSpaceOverTwist_pullbackIso_degree_eq_naturality
    n g ((d : ℤ) - l) (-l + (d : ℤ)) hneg
  have hnatHe := projectiveSpaceOverTwist_pullbackIso_degree_eq_naturality
    n g (e : ℤ) ((d : ℤ) - l) he.symm
  have hmono := ProjectiveSpace.twistMonomialSection_pullback n g e i
  change Modules.Hom.app
      (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections f (FS (-l + (d : ℤ)))
        (Modules.Hom.app enS ⊤ (he ▸ xS))) =
    Modules.Hom.app enT ⊤ (he ▸ xT)
  rw [hheS, hheT]
  calc
    _ = Modules.Hom.app
        (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ⊤
        (Modules.Hom.app ((Modules.pullback f).map enS) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f (FS ((d : ℤ) - l))
            (Modules.Hom.app ehS ⊤ xS))) := by
      exact congrArg
        (fun z ↦ Modules.Hom.app
          (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ⊤ z)
        (Modules.pullbackGlobalSections_naturality f enS
          (Modules.Hom.app ehS ⊤ xS)).symm
    _ = Modules.Hom.app
        ((Modules.pullback f).map enS ≫
          (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f (FS ((d : ℤ) - l))
          (Modules.Hom.app ehS ⊤ xS)) := rfl
    _ = Modules.Hom.app
        ((projectiveSpaceOverTwist_pullbackIso n g ((d : ℤ) - l)).hom ≫ enT) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f (FS ((d : ℤ) - l))
          (Modules.Hom.app ehS ⊤ xS)) := by rw [hnatNeg]
    _ = Modules.Hom.app enT ⊤
        (Modules.Hom.app
          (projectiveSpaceOverTwist_pullbackIso n g ((d : ℤ) - l)).hom ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f (FS ((d : ℤ) - l))
            (Modules.Hom.app ehS ⊤ xS))) := rfl
    _ = Modules.Hom.app enT ⊤
        (Modules.Hom.app
          (projectiveSpaceOverTwist_pullbackIso n g ((d : ℤ) - l)).hom ⊤
          (Modules.Hom.app ((Modules.pullback f).map ehS) ⊤
            (_root_.Scheme.Modules.pullbackGlobalSections f (FS (e : ℤ)) xS))) := by
      exact congrArg
        (fun z ↦ Modules.Hom.app enT ⊤
          (Modules.Hom.app
            (projectiveSpaceOverTwist_pullbackIso n g ((d : ℤ) - l)).hom ⊤ z))
        (Modules.pullbackGlobalSections_naturality f ehS xS).symm
    _ = Modules.Hom.app enT ⊤
        (Modules.Hom.app
          ((Modules.pullback f).map ehS ≫
            (projectiveSpaceOverTwist_pullbackIso n g ((d : ℤ) - l)).hom) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f (FS (e : ℤ)) xS)) := rfl
    _ = Modules.Hom.app enT ⊤
        (Modules.Hom.app
          ((projectiveSpaceOverTwist_pullbackIso n g (e : ℤ)).hom ≫ ehT) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f (FS (e : ℤ)) xS)) := by
      rw [hnatHe]
    _ = Modules.Hom.app enT ⊤
        (Modules.Hom.app ehT ⊤
          (Modules.Hom.app
            (projectiveSpaceOverTwist_pullbackIso n g (e : ℤ)).hom ⊤
            (_root_.Scheme.Modules.pullbackGlobalSections f (FS (e : ℤ)) xS))) := rfl
    _ = _ := by rw [hmono]

/-- The single-summand monomial section used to define a twisted-free monomial section
commutes with arbitrary base change. -/
lemma twistedFreeSingleMonomialSection_pullback (n : ℕ)
    {S T : Scheme.{u}} (g : T ⟶ S) (l : ℤ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g
        (projectiveSpaceOverTwist n S (-l)) d ≪≫
      Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g (-l))
        (projectiveSpaceOverTwist n T (d : ℤ))
    Modules.Hom.app E.hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g)
          (projectiveSpaceOverTwistModule
            (projectiveSpaceOverTwist n S (-l)) (d : ℤ))
          (Modules.Hom.app
            (projectiveSpaceOverTwist_addIso_nat n S (-l) d).inv ⊤
            (Modules.Hom.app
              (eqToHom (congrArg
                (fun c : ℤ ↦ projectiveSpaceOverTwist n S c)
                (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
              (he ▸ twistMonomialSection n S e i)))) =
      Modules.Hom.app
        (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
        (Modules.Hom.app
          (eqToHom (congrArg
            (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
          (he ▸ twistMonomialSection n T e i)) := by
  dsimp only
  let f := projectiveSpaceOverMap n g
  let AS := projectiveSpaceOverTwist n S (-l)
  let AT := projectiveSpaceOverTwist n T (-l)
  let BS := projectiveSpaceOverTwist n S (-l + (d : ℤ))
  let BT := projectiveSpaceOverTwist n T (-l + (d : ℤ))
  let addS := (projectiveSpaceOverTwist_addIso_nat n S (-l) d).inv
  let addT := (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv
  let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g AS d ≪≫
    Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g (-l))
      (projectiveSpaceOverTwist n T (d : ℤ))
  let coreS : Γ(BS, ⊤) := Modules.Hom.app
    (eqToHom (congrArg
      (fun c : ℤ ↦ projectiveSpaceOverTwist n S c)
      (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
    (he ▸ twistMonomialSection n S e i)
  let coreT : Γ(BT, ⊤) := Modules.Hom.app
    (eqToHom (congrArg
      (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
      (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
    (he ▸ twistMonomialSection n T e i)
  have hadd := projectiveSpaceOverTwist_addIso_nat_pullback_inv
    n g (-l) d
  have hcore := twistedFreeSingleMonomialCore_pullback n g l d e he i
  change Modules.Hom.app E.hom ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections f
        (projectiveSpaceOverTwistModule AS (d : ℤ))
        (Modules.Hom.app addS ⊤ coreS)) =
    Modules.Hom.app addT ⊤ coreT
  calc
    _ = Modules.Hom.app E.hom ⊤
        (Modules.Hom.app ((Modules.pullback f).map addS) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f BS coreS)) := by
      exact congrArg (fun z ↦ Modules.Hom.app E.hom ⊤ z)
        (Modules.pullbackGlobalSections_naturality f addS coreS).symm
    _ = Modules.Hom.app ((Modules.pullback f).map addS ≫ E.hom) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f BS coreS) := rfl
    _ = Modules.Hom.app
        ((projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ≫ addT) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f BS coreS) := by
      rw [hadd]
    _ = Modules.Hom.app addT ⊤
        (Modules.Hom.app
          (projectiveSpaceOverTwist_pullbackIso n g (-l + (d : ℤ))).hom ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f BS coreS)) := rfl
    _ = _ := congrArg (fun z ↦ Modules.Hom.app addT ⊤ z) hcore

/-- A summand inclusion commutes with equality transport between finite coproducts of
twisting sheaves. -/
lemma projectiveSpaceOverTwist_ι_comp_degree_eqToIso_inv
    (n : ℕ) (S : Scheme.{u}) (r : ℕ) (a b : ℤ) (h : a = b)
    (j : ULift.{u} (Fin r)) :
    Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S b) j ≫
        (eqToIso (congrArg (fun c : ℤ ↦
          ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S c) h)).inv =
      eqToHom (congrArg (fun c : ℤ ↦ projectiveSpaceOverTwist n S c) h.symm) ≫
        Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S a) j := by
  subst b
  simp only [eqToIso_refl, Iso.refl_inv, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- A summand inclusion followed by the inverse coproduct twist-addition isomorphism
is tensoring the original summand inclusion, after the single-summand degree
identification. -/
lemma projectiveSpaceOverNegativeTwist_ι_inv
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r d : ℕ)
    (j : ULift.{u} (Fin r)) :
    Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n S ((d : ℤ) - l)) j ≫
      (projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
        (J := ULift.{u} (Fin r)) n S l d).inv =
    (eqToHom (by rw [neg_add_eq_sub]) :
        projectiveSpaceOverTwist n S ((d : ℤ) - l) ⟶
          projectiveSpaceOverTwist n S (-l + (d : ℤ))) ≫
      (projectiveSpaceOverTwist_addIso_nat n S (-l) d).inv ≫
      Modules.tensorMapLeft
        (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n S (-l)) j)
        (projectiveSpaceOverTwist n S (d : ℤ)) := by
  dsimp only [projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat,
    projectiveSpaceOverTwist_coproduct_addIso_nat,
    Iso.trans_inv, Iso.symm_inv]
  slice_lhs 1 2 =>
    rw [projectiveSpaceOverTwist_ι_comp_degree_eqToIso_inv n S r
      (-l + (d : ℤ)) ((d : ℤ) - l) (neg_add_eq_sub l (d : ℤ)) j]
  simp only [Category.assoc]
  rw [Sigma.ι_mapIso_inv_assoc]
  slice_lhs 3 4 => rw [Modules.ι_tensorCoproductIso_inv]

/-- Pullback of a tensorized summand inclusion in a twisted-free module is the
corresponding tensorized summand inclusion after the canonical twisted-free
pullback comparison. -/
lemma twistedFreeSummand_twistPullback
    (n r : ℕ) (l : ℤ) {S T : Scheme.{u}} (g : T ⟶ S) (d : ℕ)
    (j : ULift.{u} (Fin r)) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
        (Modules.tensorMapLeft
          (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) j)
          (projectiveSpaceOverTwist n S (d : ℤ))) ≫
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) d ≪≫
        Modules.tensorLeftIso (projectiveSpaceOverTwistedFree_pullbackIso n r l g)
          (projectiveSpaceOverTwist n T (d : ℤ))).hom =
    (projectiveSpaceOverTwistModule_pullbackIso_nat n g
          (projectiveSpaceOverTwist n S (-l)) d ≪≫
        Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g (-l))
          (projectiveSpaceOverTwist n T (d : ℤ))).hom ≫
      Modules.tensorMapLeft
        (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) j)
        (projectiveSpaceOverTwist n T (d : ℤ)) := by
  let FS := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n S (-l)
  let FT := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let eF : (Modules.pullback (projectiveSpaceOverMap n g)).obj FS ≅ FT :=
    projectiveSpaceOverTwistedFree_pullbackIso n r l g
  let ιS := Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n S (-l)) j
  let ιT := Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)) j
  have hn := projectiveSpaceOverTwistModule_pullbackIso_nat_naturality_comp
    n g FT eF ιS d
  have hι : (Modules.pullback (projectiveSpaceOverMap n g)).map ιS ≫ eF.hom =
      (projectiveSpaceOverTwist_pullbackIso n g (-l)).hom ≫ ιT := by
    exact Modules.pullback_map_ι_coproductPullbackIso_hom
      (projectiveSpaceOverMap n g)
      (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l))
      (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
      (fun _ ↦ projectiveSpaceOverTwist_pullbackIso n g (-l)) j
  change (Modules.pullback (projectiveSpaceOverMap n g)).map
        (Modules.tensorMapLeft ιS (projectiveSpaceOverTwist n S (d : ℤ))) ≫
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g FS d ≪≫
        Modules.tensorLeftIso eF
          (projectiveSpaceOverTwist n T (d : ℤ))).hom = _
  rw [hn, hι]
  dsimp only [Iso.trans_hom, Modules.tensorLeftIso]
  simp only [Category.assoc, Modules.tensorMapLeft_comp]
  rfl

/-- A twisted-free monomial section is obtained by applying the tensor of one
summand inclusion to the corresponding single-twist monomial section. -/
lemma twistedFreeMonomialSection_eq_summand
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r))
    (i : Fin ((n + e).choose n)) :
    twistedFreeMonomialSection n S l r d e he j i =
      Modules.Hom.app
        (Modules.tensorMapLeft
          (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n S (-l)) j)
          (projectiveSpaceOverTwist n S (d : ℤ))) ⊤
        (Modules.Hom.app
          (projectiveSpaceOverTwist_addIso_nat n S (-l) d).inv ⊤
          (Modules.Hom.app
            (eqToHom (congrArg
              (fun c : ℤ ↦ projectiveSpaceOverTwist n S c)
              (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
            (he ▸ twistMonomialSection n S e i))) := by
  have hm' := congrArg
    (fun k ↦ Modules.Hom.app k ⊤ (he ▸ twistMonomialSection n S e i))
    (projectiveSpaceOverNegativeTwist_ι_inv n S l r d j)
  change Modules.Hom.app
      (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n S ((d : ℤ) - l)) j ≫
        (projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
          (J := ULift.{u} (Fin r)) n S l d).inv) ⊤
      (he ▸ twistMonomialSection n S e i) = _
  exact hm'

/-- Pulling a twisted-free monomial section back along a base morphism gives the
corresponding twisted-free monomial section through the canonical tensor comparison. -/
lemma twistedFreeMonomialSection_pullback
    (n r : ℕ) (l : ℤ) {S T : Scheme.{u}} (g : T ⟶ S)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)) :
    let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n S (-l)) d ≪≫
      Modules.tensorLeftIso (projectiveSpaceOverTwistedFree_pullbackIso n r l g)
        (projectiveSpaceOverTwist n T (d : ℤ))
    Modules.Hom.app E.hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g)
          (projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n S (-l)) (d : ℤ))
          (twistedFreeMonomialSection n S l r d e he j i)) =
      twistedFreeMonomialSection n T l r d e he j i := by
  dsimp only
  let f := projectiveSpaceOverMap n g
  let FS := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n S (-l)
  let FT := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let AS := projectiveSpaceOverTwist n S (-l)
  let AT := projectiveSpaceOverTwist n T (-l)
  let DS := projectiveSpaceOverTwist n S (d : ℤ)
  let DT := projectiveSpaceOverTwist n T (d : ℤ)
  let E := projectiveSpaceOverTwistModule_pullbackIso_nat n g FS d ≪≫
    Modules.tensorLeftIso (projectiveSpaceOverTwistedFree_pullbackIso n r l g) DT
  let E' := projectiveSpaceOverTwistModule_pullbackIso_nat n g AS d ≪≫
    Modules.tensorLeftIso (projectiveSpaceOverTwist_pullbackIso n g (-l)) DT
  let ιS := Modules.tensorMapLeft
    (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n S (-l)) j) DS
  let ιT := Modules.tensorMapLeft
    (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) j) DT
  let singleS : Γ(projectiveSpaceOverTwistModule AS (d : ℤ), ⊤) :=
    Modules.Hom.app
      (projectiveSpaceOverTwist_addIso_nat n S (-l) d).inv ⊤
      (Modules.Hom.app
        (eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n S c)
          (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
        (he ▸ twistMonomialSection n S e i))
  let singleT : Γ(projectiveSpaceOverTwistModule AT (d : ℤ), ⊤) :=
    Modules.Hom.app
      (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
      (Modules.Hom.app
        (eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
          (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
        (he ▸ twistMonomialSection n T e i))
  have hdecS := twistedFreeMonomialSection_eq_summand
    n S l r d e he j i
  have hdecT := twistedFreeMonomialSection_eq_summand
    n T l r d e he j i
  have hsum := twistedFreeSummand_twistPullback n r l g d j
  have hsingle := twistedFreeSingleMonomialSection_pullback n g l d e he i
  change Modules.Hom.app E.hom ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections f
        (projectiveSpaceOverTwistModule FS (d : ℤ))
        (twistedFreeMonomialSection n S l r d e he j i)) =
    twistedFreeMonomialSection n T l r d e he j i
  rw [hdecS, hdecT]
  change Modules.Hom.app E.hom ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections f
        (projectiveSpaceOverTwistModule FS (d : ℤ))
        (Modules.Hom.app ιS ⊤ singleS)) =
    Modules.Hom.app ιT ⊤ singleT
  calc
    _ = Modules.Hom.app E.hom ⊤
        (Modules.Hom.app ((Modules.pullback f).map ιS) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f
            (projectiveSpaceOverTwistModule AS (d : ℤ)) singleS)) := by
      exact congrArg (fun z ↦ Modules.Hom.app E.hom ⊤ z)
        (Modules.pullbackGlobalSections_naturality f ιS singleS).symm
    _ = Modules.Hom.app ((Modules.pullback f).map ιS ≫ E.hom) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f
          (projectiveSpaceOverTwistModule AS (d : ℤ)) singleS) := rfl
    _ = Modules.Hom.app (E'.hom ≫ ιT) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f
          (projectiveSpaceOverTwistModule AS (d : ℤ)) singleS) := by
      exact congrArg
        (fun k ↦ Modules.Hom.app k ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f
            (projectiveSpaceOverTwistModule AS (d : ℤ)) singleS)) hsum
    _ = Modules.Hom.app ιT ⊤
        (Modules.Hom.app E'.hom ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f
            (projectiveSpaceOverTwistModule AS (d : ℤ)) singleS)) := rfl
    _ = _ := congrArg (fun z ↦ Modules.Hom.app ιT ⊤ z) hsingle

/-- A quotient monomial section commutes with arbitrary base change whenever the
underlying normalized quotient map does. -/
lemma quotMonomialSection_pullback_of_comm
    (n r : ℕ) (l : ℤ) {S T : Scheme.{u}} (g : T ⟶ S)
    {Q : (projectiveSpaceOver n S).Modules}
    {Q' : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n S (-l)) ⟶ Q)
    (p' : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q')
    (eQ : (Modules.pullback (projectiveSpaceOverMap n g)).obj Q ≅ Q')
    (hp : (projectiveSpaceOverTwistedFree_pullbackIso n r l g).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n g)).map p ≫ eQ.hom = p')
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)) :
    let EQ := projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d ≪≫
      Modules.tensorLeftIso eQ (projectiveSpaceOverTwist n T (d : ℤ))
    Modules.Hom.app EQ.hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g)
          (projectiveSpaceOverTwistModule Q (d : ℤ))
          (quotMonomialSection n S l r p d e he j i)) =
      quotMonomialSection n T l r p' d e he j i := by
  dsimp only
  let f := projectiveSpaceOverMap n g
  let FS := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n S (-l)
  let FT := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let DS := projectiveSpaceOverTwist n S (d : ℤ)
  let DT := projectiveSpaceOverTwist n T (d : ℤ)
  let eF := projectiveSpaceOverTwistedFree_pullbackIso n r l g
  let EF0 := projectiveSpaceOverTwistModule_pullbackIso_nat n g FS d
  let EF := EF0 ≪≫ Modules.tensorLeftIso eF DT
  let EQ := projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d ≪≫
    Modules.tensorLeftIso eQ DT
  let pDS := Modules.tensorMapLeft p DS
  let pDT := Modules.tensorMapLeft p' DT
  let sS := twistedFreeMonomialSection n S l r d e he j i
  let sT := twistedFreeMonomialSection n T l r d e he j i
  have hp' : (Modules.pullback f).map p ≫ eQ.hom = eF.hom ≫ p' := by
    rw [← hp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have htwist := projectiveSpaceOverTwistModule_pullbackIso_nat_naturality_comp
    n g Q' eQ p d
  have htwist' : (Modules.pullback f).map pDS ≫ EQ.hom =
      EF.hom ≫ pDT := by
    change (Modules.pullback f).map
        (Modules.tensorMapLeft p DS) ≫ EQ.hom = EF.hom ≫ pDT
    rw [htwist, hp']
    dsimp only [EF, EF0, pDT, eF, Iso.trans_hom,
      Modules.tensorLeftIso]
    simp only [Category.assoc, Modules.tensorMapLeft_comp]
    rfl
  have hs := twistedFreeMonomialSection_pullback n r l g d e he j i
  change Modules.Hom.app EQ.hom ⊤
      (_root_.Scheme.Modules.pullbackGlobalSections f
        (projectiveSpaceOverTwistModule Q (d : ℤ))
        (Modules.Hom.app pDS ⊤ sS)) =
    Modules.Hom.app pDT ⊤ sT
  calc
    _ = Modules.Hom.app EQ.hom ⊤
        (Modules.Hom.app ((Modules.pullback f).map pDS) ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f
            (projectiveSpaceOverTwistModule FS (d : ℤ)) sS)) := by
      exact congrArg (fun z ↦ Modules.Hom.app EQ.hom ⊤ z)
        (Modules.pullbackGlobalSections_naturality f pDS sS).symm
    _ = Modules.Hom.app ((Modules.pullback f).map pDS ≫ EQ.hom) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f
          (projectiveSpaceOverTwistModule FS (d : ℤ)) sS) := rfl
    _ = Modules.Hom.app (EF.hom ≫ pDT) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections f
          (projectiveSpaceOverTwistModule FS (d : ℤ)) sS) := by
      rw [htwist']
      rfl
    _ = Modules.Hom.app pDT ⊤
        (Modules.Hom.app EF.hom ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections f
            (projectiveSpaceOverTwistModule FS (d : ℤ)) sS)) := rfl
    _ = _ := congrArg (fun z ↦ Modules.Hom.app pDT ⊤ z) hs

/-- For a raw Quot datum, compatibility of its normalized quotient map with pullback
implies compatibility of every quotient monomial section. -/
lemma twistedFreeQuotientQuotMonomialSection_pullback_of_comm
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hp : (projectiveSpaceOverTwistedFree_pullbackIso n r l g.left).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n g.left)).map
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) ≫
      (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).inv =
        Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T'
          (a.pullback g))
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)) :
    Modules.Hom.app
        (twistedFreeQuotientTwistPullbackIso n S l r g a d).hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g.left)
          (projectiveSpaceOverTwistModule
            (twistedFreeQuotientSheaf n S l r a) (d : ℤ))
          (quotMonomialSection n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d e he j i)) =
      quotMonomialSection n T'.left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T'
          (a.pullback g)) d e he j i := by
  exact quotMonomialSection_pullback_of_comm n r l g.left
    (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
    (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T'
      (a.pullback g))
    (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).symm hp
    d e he j i

/-- The canonical arbitrary-base-change morphism for the twisted pushforward attached to
a raw Quot datum.  The fixed-degree Cohomology-and-Base-Change input needed by the
Quot-to-Grassmannian construction is precisely that this morphism is an isomorphism. -/
noncomputable def twistedFreeQuotientTwistPushforwardBaseChangeHom
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) (d : ℕ) :
    (Modules.pullback g.left).obj
        (twistedFreeQuotientTwistPushforward n S l r a d) ⟶
      twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d :=
  Modules.pushforwardBaseChangeHomOfComm
      (projectiveSpaceOverπ n T.left)
      (projectiveSpaceOverπ n T'.left) g.left
      (projectiveSpaceOverMap n g.left)
      (projectiveSpaceOverMap_π n g.left)
      (projectiveSpaceOverTwistModule
        (twistedFreeQuotientSheaf n S l r a) (d : ℤ)) ≫
    (Modules.pushforward (projectiveSpaceOverπ n T'.left)).map
      (twistedFreeQuotientTwistPullbackIso n S l r g a d).hom

/-- On global sections, the canonical twisted pushforward base-change morphism pulls a
section back to projective space and then applies the twist comparison. -/
lemma twistedFreeQuotientTwistPushforwardBaseChangeHom_app_top
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) (d : ℕ)
    (s : Γ(projectiveSpaceOverTwistModule
      (twistedFreeQuotientSheaf n S l r a) (d : ℤ), ⊤)) :
    Modules.Hom.app
        (twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections g.left
          (twistedFreeQuotientTwistPushforward n S l r a d)
          (show Γ(twistedFreeQuotientTwistPushforward n S l r a d, ⊤) from s)) =
      Modules.Hom.app
        (twistedFreeQuotientTwistPullbackIso n S l r g a d).hom ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections
          (projectiveSpaceOverMap n g.left)
          (projectiveSpaceOverTwistModule
            (twistedFreeQuotientSheaf n S l r a) (d : ℤ)) s) := by
  change Modules.Hom.app
      ((Modules.pushforward (projectiveSpaceOverπ n T'.left)).map
        (twistedFreeQuotientTwistPullbackIso n S l r g a d).hom) ⊤
      (Modules.Hom.app
        (Modules.pushforwardBaseChangeHomOfComm
          (projectiveSpaceOverπ n T.left)
          (projectiveSpaceOverπ n T'.left) g.left
          (projectiveSpaceOverMap n g.left)
          (projectiveSpaceOverMap_π n g.left)
          (projectiveSpaceOverTwistModule
            (twistedFreeQuotientSheaf n S l r a) (d : ℤ))) ⊤
        (_root_.Scheme.Modules.pullbackGlobalSections g.left
          (twistedFreeQuotientTwistPushforward n S l r a d)
          (show Γ(twistedFreeQuotientTwistPushforward n S l r a d, ⊤) from s))) = _
  rw [Modules.pushforwardBaseChangeHomOfComm_app_top_pullbackGlobalSections]
  rfl

/-- The twisted quotient pushforward is quasicoherent. -/
lemma twistedFreeQuotientTwistPushforward_isQuasicoherent
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T) (d : ℕ) :
    (twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent := by
  letI : (twistedFreeQuotientSheaf n S l r a).IsQuasicoherent :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isQuasicoherent_over T a
  infer_instance

namespace Modules

/-- Composing a map out of a finite free sheaf with an isomorphism does not change its
kernel submodule on any open. -/
lemma kernelSubmodule_eq_of_comp_iso {X : Scheme.{u}} {m : ℕ} {M N : X.Modules}
    (f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (e : M ≅ N)
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ N)
    (h : f ≫ e.hom = g) (U : X.Opens) :
    kernelSubmodule f U = kernelSubmodule g U := by
  ext x
  change finFreeSectionsMap' f U x = 0 ↔ finFreeSectionsMap' g U x = 0
  rw [← h, finFreeSectionsMap'_comp]
  constructor
  · intro hx
    rw [hx, map_zero]
  · intro hx
    apply (ConcreteCategory.bijective_of_isIso (Hom.app e.hom U)).injective
    simpa only [map_zero] using hx

/-- Composing a map out of a finite free sheaf with an isomorphism does not change the
associated quasicoherent kernel datum. -/
lemma kernelSubmoduleSheafData_eq_of_comp_iso
    {X : Scheme.{u}} {m : ℕ} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (e : M ≅ N)
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ N)
    (h : f ≫ e.hom = g) :
    kernelSubmoduleSheafData f = kernelSubmoduleSheafData g := by
  apply SubmoduleSheafData.ext
  funext U
  exact kernelSubmodule_eq_of_comp_iso f e g h U.1

/-- The two finite-free section maps in `FreeSheafSections` agree.  The primed form is
convenient for spanning arguments, while the unprimed form exposes the actual map on
sections of the free sheaf. -/
lemma finFreeSectionsMap_eq_finFreeSectionsMap'
    {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (U : X.Opens) : finFreeSectionsMap φ U = finFreeSectionsMap' φ U := by
  apply LinearMap.ext
  intro x
  classical
  let y : ULift.{u} (Fin m) → ↥Γ(X, U) := fun j ↦ x j.down
  have hy : y = ∑ i : Fin m, x i • Pi.single (ULift.up i) 1 := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j.down]
    · simp [y]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne]
      · simp
      · exact fun h ↦ hb (congrArg ULift.down h).symm
    · simp
  have hι (i : Fin m) :
      (freeSectionsEquiv U).symm (Pi.single (ULift.up i) 1) =
        Hom.app (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)) U
          (1 : ↥Γ(X, U)) := by
    apply (freeSectionsEquiv U).injective
    rw [LinearEquiv.apply_symm_apply]
    exact openSectionsFiniteCoproductLinearEquiv_ι U
      (fun _ : ULift.{u} (Fin m) => SheafOfModules.unit X.ringCatSheaf)
      (ULift.up i)
      (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : ↥Γ(X, U))) |>.symm
  change Hom.app φ U ((freeSectionsEquiv U).symm y) =
    ∑ i : Fin m, x i • Hom.app
      (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i) ≫ φ) U
        (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : ↥Γ(X, U)))
  rw [hy, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(freeSectionsEquiv U).symm.map_smul]
  change (PresheafOfModules.Hom.app φ.val (op U)).hom
      (x i • (freeSectionsEquiv U).symm (Pi.single (ULift.up i) 1)) = _
  calc
    _ = x i • (PresheafOfModules.Hom.app φ.val (op U)).hom
        ((freeSectionsEquiv U).symm (Pi.single (ULift.up i) 1)) :=
      (PresheafOfModules.Hom.app φ.val (op U)).hom.map_smul _ _
    _ = x i • (PresheafOfModules.Hom.app φ.val (op U)).hom
        (Hom.app (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)) U
          (1 : ↥Γ(X, U))) :=
      congrArg (fun z ↦ x i • (PresheafOfModules.Hom.app φ.val (op U)).hom z) (hι i)
    _ = _ := rfl

/-- Surjectivity of the generator-coordinate section map implies surjectivity of the
actual map on sections of the finite free sheaf. -/
lemma hom_app_surjective_of_finFreeSectionsMap'_surjective
    {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (h : ∀ U : X.affineOpens, Function.Surjective (finFreeSectionsMap' φ U.1)) :
    ∀ U : X.affineOpens, Function.Surjective (Hom.app φ U.1) := by
  intro U y
  obtain ⟨x, hx⟩ := h U y
  refine ⟨(freeSectionsEquiv U.1).symm (fun j ↦ x j.down), ?_⟩
  rw [← finFreeSectionsMap_eq_finFreeSectionsMap' φ U.1] at hx
  exact hx

end Modules

/-- The monomial free map attached to a normalized twisted-free Quot presentation, with
its product basis reindexed by `Fin m`. -/
def twistedFreeQuotGrassmannianFreeMap
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    SheafOfModules.free (R := T.left.ringCatSheaf) (ULift.{u} (Fin m)) ⟶
      twistedFreeQuotientTwistPushforward n S l r a d :=
  Modules.freeHomOfSections
    (fun i : ULift.{u} (Fin m) ↦
      quotMonomialSection n T.left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
        d e he (σ i).1 (σ i).2)

/-- If each quotient monomial section is preserved by the canonical twist comparison,
then the associated map from the finite free sheaf commutes with the canonical
pushforward base-change morphism. -/
lemma twistedFreeQuotGrassmannianFreeMap_baseChange_of_quotMonomialSection
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hsection : ∀ (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)),
      Modules.Hom.app
          (twistedFreeQuotientTwistPullbackIso n S l r g a d).hom ⊤
          (_root_.Scheme.Modules.pullbackGlobalSections
            (projectiveSpaceOverMap n g.left)
            (projectiveSpaceOverTwistModule
              (twistedFreeQuotientSheaf n S l r a) (d : ℤ))
            (quotMonomialSection n T.left l r
              (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
              d e he j i)) =
        quotMonomialSection n T'.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T'
            (a.pullback g)) d e he j i) :
    (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      twistedFreeQuotGrassmannianFreeMap
        n S l r (a.pullback g) d e he σ := by
  apply Modules.pullback_freeHomOfSections_comp
  intro k
  rw [twistedFreeQuotientTwistPushforwardBaseChangeHom_app_top]
  exact hsection (σ k).1 (σ k).2

/-- Compatibility of the normalized Quot presentation with pullback supplies the
canonical base-change square for its finite-free monomial map. -/
lemma twistedFreeQuotGrassmannianFreeMap_baseChange_of_normalizedQuotient
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hp : (projectiveSpaceOverTwistedFree_pullbackIso n r l g.left).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n g.left)).map
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) ≫
      (a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g).inv =
        Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T'
          (a.pullback g)) :
    (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      twistedFreeQuotGrassmannianFreeMap
        n S l r (a.pullback g) d e he σ := by
  apply twistedFreeQuotGrassmannianFreeMap_baseChange_of_quotMonomialSection
  intro j i
  exact twistedFreeQuotientQuotMonomialSection_pullback_of_comm
    n S l r g a hp d e he j i

/-- The finite-free monomial map attached to a twisted-free Quot presentation commutes
with its canonical pushforward base-change morphism. -/
lemma twistedFreeQuotGrassmannianFreeMap_baseChange
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      twistedFreeQuotGrassmannianFreeMap
        n S l r (a.pullback g) d e he σ :=
  twistedFreeQuotGrassmannianFreeMap_baseChange_of_normalizedQuotient
    n S l r g a d e he σ
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_pullback
        n r l S g a)

/-- The monomial free maps of equivalent quotient presentations agree through the induced
isomorphism of twisted pushforwards. -/
lemma twistedFreeQuotGrassmannianFreeMap_comp_iso_of_r
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    {a b : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T}
    (h : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r a b)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    ∃ ε : twistedFreeQuotientTwistPushforward n S l r a d ≅
        twistedFreeQuotientTwistPushforward n S l r b d,
      twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ ≫ ε.hom =
        twistedFreeQuotGrassmannianFreeMap n S l r b d e he σ := by
  obtain ⟨eQ, hQ⟩ := h
  let ε := twistedFreeQuotientTwistPushforwardIsoOfIso n S l r eQ d
  refine ⟨ε, ?_⟩
  change Modules.freeHomOfSections
      (M := twistedFreeQuotientTwistPushforward n S l r a d)
      (fun i : ULift.{u} (Fin m) ↦
        quotMonomialSection n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
          d e he (σ i).1 (σ i).2) ≫ ε.hom =
    Modules.freeHomOfSections
      (M := twistedFreeQuotientTwistPushforward n S l r b d)
      (fun i : ULift.{u} (Fin m) ↦
        quotMonomialSection n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T b)
          d e he (σ i).1 (σ i).2)
  rw [Modules.freeHomOfSections_comp]
  apply congrArg Modules.freeHomOfSections
  funext i
  change Modules.Hom.app
      (Modules.tensorMapLeft
        (Modules.QuotientPullbackData.quotDataOnProjectiveSpaceIsoOfIsoOver T eQ).hom
        (projectiveSpaceOverTwist n T.left (d : ℤ))) ⊤
      (quotMonomialSection n T.left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
        d e he (σ i).1 (σ i).2) =
    quotMonomialSection n T.left l r
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T b)
      d e he (σ i).1 (σ i).2
  dsimp only [quotMonomialSection]
  have htensor : Modules.tensorMapLeft
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
        (projectiveSpaceOverTwist n T.left (d : ℤ)) ≫
      Modules.tensorMapLeft
        (Modules.QuotientPullbackData.quotDataOnProjectiveSpaceIsoOfIsoOver T eQ).hom
        (projectiveSpaceOverTwist n T.left (d : ℤ)) =
      Modules.tensorMapLeft
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T b)
        (projectiveSpaceOverTwist n T.left (d : ℤ)) := by
    rw [← Modules.tensorMapLeft_comp,
      Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_comp_iso
        T eQ hQ]
  exact congrArg (fun k ↦ Modules.Hom.app k ⊤
    (twistedFreeMonomialSection n T.left l r d e he (σ i).1 (σ i).2)) htensor

/-- The kernel submodule datum underlying the Quot-to-Grassmannian point. -/
def twistedFreeQuotGrassmannianKernelData
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    T.left.SubmoduleSheafData m := by
  letI : (twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  exact Modules.kernelSubmoduleSheafData
    (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ)

/-- Equivalent twisted-free Quot presentations determine the same monomial kernel datum. -/
lemma twistedFreeQuotGrassmannianKernelData_eq_of_r
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    {a b : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T}
    (h : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r a b)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    twistedFreeQuotGrassmannianKernelData n S l r a d e he σ =
      twistedFreeQuotGrassmannianKernelData n S l r b d e he σ := by
  obtain ⟨ε, hε⟩ :=
    twistedFreeQuotGrassmannianFreeMap_comp_iso_of_r n S l r h d e he σ
  letI : (twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  letI : (twistedFreeQuotientTwistPushforward n S l r b d).IsQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r b d
  exact Modules.kernelSubmoduleSheafData_eq_of_comp_iso
    (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ε
    (twistedFreeQuotGrassmannianFreeMap n S l r b d e he σ) hε

/-- The Grassmannian point attached to a raw twisted-free Quot presentation. -/
def twistedFreeQuotGrassmannianPoint
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)) :
    (grassmannianFunctor q m).obj (op T.left) := by
  letI : (twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  exact Modules.kernelGrassmannianPoint
    (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) hM hsurj

@[simp]
lemma twistedFreeQuotGrassmannianPoint_val
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)) :
    (twistedFreeQuotGrassmannianPoint n S l r a d e he σ hM hsurj).1 =
      twistedFreeQuotGrassmannianKernelData n S l r a d e he σ := rfl

/-- The monomial map packaged as a strict rank-`q` quotient of the canonical finite free
sheaf.  This presentation is useful because `FreeQuotient.kernelData_comap` already
contains the full arbitrary-base-change proof for kernels of strict free quotients. -/
noncomputable def twistedFreeQuotGrassmannianFreeQuotient
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)) :
    Modules.FreeQuotient q (ULift.{u} (Fin m)) T.left where
  Q := twistedFreeQuotientTwistPushforward n S l r a d
  isQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  isProjectiveOfRank := hM
  π := twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  epi := Modules.epi_of_surjective_on_affineOpens _
    (Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective _ hsurj)

@[simp]
lemma twistedFreeQuotGrassmannianFreeQuotient_π
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)) :
    (twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ hM hsurj).π =
      twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ := rfl

/-- Equivalent raw Quot presentations give equivalent strict free quotients of the
monomial map.  The projectivity and surjectivity witnesses may be chosen independently
on the two presentations. -/
lemma twistedFreeQuotGrassmannianFreeQuotient_r_of_r
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    {a b : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T}
    (h : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T).r a b)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1))
    (hM' : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r b d))
    (hsurj' : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r b d e he σ) U.1)) :
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).r
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ hM hsurj)
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r b d e he σ hM' hsurj') := by
  obtain ⟨ε, hε⟩ :=
    twistedFreeQuotGrassmannianFreeMap_comp_iso_of_r n S l r h d e he σ
  exact ⟨ε, hε⟩

/-- A target base-change isomorphism compatible with the monomial maps identifies the
pulled-back strict free quotient with the strict free quotient of the pulled-back Quot
datum.  This is the presentation-level form of the remaining Cohomology-and-Base-Change
square. -/
lemma twistedFreeQuotGrassmannianFreeQuotient_pullback_r_of_iso
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1))
    (hM' : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d))
    (hsurj' : ∀ U : T'.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) U.1))
    (ε : (Modules.pullback g.left).obj
        (twistedFreeQuotientTwistPushforward n S l r a d) ≅
      twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d)
    (hε : (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫ ε.hom =
      twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) :
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T'.left).r
      ((twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ hM hsurj).pullback g.left)
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r (a.pullback g) d e he σ hM' hsurj') :=
  ⟨ε, hε⟩

/-- At the intrinsic `FreeQuotient.kernelData` level, the compatible base-change
isomorphism of targets already gives the desired comap equality. -/
lemma twistedFreeQuotGrassmannianFreeQuotient_kernelData_pullback_of_iso
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1))
    (hM' : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d))
    (hsurj' : ∀ U : T'.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) U.1))
    (ε : (Modules.pullback g.left).obj
        (twistedFreeQuotientTwistPushforward n S l r a d) ≅
      twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d)
    (hε : (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫ ε.hom =
      twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) :
    (twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ hM hsurj).kernelData.comap g.left =
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r (a.pullback g) d e he σ hM' hsurj').kernelData := by
  rw [Modules.FreeQuotient.kernelData_comap]
  exact Modules.FreeQuotient.kernelData_eq_of_r
    (twistedFreeQuotGrassmannianFreeQuotient_pullback_r_of_iso
      n S l r g a d e he σ hM hsurj hM' hsurj' ε hε)

/-- Reduction of the concrete section-kernel comap equality to two presentation-model
comparisons and the canonical strict-quotient base-change square.  The two `hK` hypotheses
are independent of projective geometry; they compare the direct
`kernelSubmoduleSheafData` construction with `FreeQuotient.kernelData`. -/
lemma twistedFreeQuotGrassmannianKernelData_pullback_of_iso
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m q : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hM : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ U : T.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1))
    (hM' : Modules.IsProjectiveOfRank q
      (twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d))
    (hsurj' : ∀ U : T'.left.affineOpens, Function.Surjective
      (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) U.1))
    (hK : twistedFreeQuotGrassmannianKernelData n S l r a d e he σ =
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r a d e he σ hM hsurj).kernelData)
    (hK' : twistedFreeQuotGrassmannianKernelData
        n S l r (a.pullback g) d e he σ =
      (twistedFreeQuotGrassmannianFreeQuotient
        n S l r (a.pullback g) d e he σ hM' hsurj').kernelData)
    (ε : (Modules.pullback g.left).obj
        (twistedFreeQuotientTwistPushforward n S l r a d) ≅
      twistedFreeQuotientTwistPushforward n S l r (a.pullback g) d)
    (hε : (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫ ε.hom =
      twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ) :
    twistedFreeQuotGrassmannianKernelData n S l r (a.pullback g) d e he σ =
      (twistedFreeQuotGrassmannianKernelData n S l r a d e he σ).comap g.left := by
  calc
    _ = (twistedFreeQuotGrassmannianFreeQuotient
          n S l r (a.pullback g) d e he σ hM' hsurj').kernelData := hK'
    _ = (twistedFreeQuotGrassmannianFreeQuotient
          n S l r a d e he σ hM hsurj).kernelData.comap g.left :=
      (twistedFreeQuotGrassmannianFreeQuotient_kernelData_pullback_of_iso
        n S l r g a d e he σ hM hsurj hM' hsurj' ε hε).symm
    _ = _ := congrArg (fun K ↦ K.comap g.left) hK.symm

namespace ProjectiveSpace

open _root_.AlgebraicGeometry.ProjectiveSpace

/-- Uniform affine-section surjectivity for the normalized monomial map attached to every
fixed-polynomial twisted-free Quot presentation. -/
theorem exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (S : Scheme.{u}) (T : Over S)
      [IsLocallyNoetherian T.left]
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
      ∀ (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
        (U : T.left.affineOpens),
      Function.Surjective (Modules.finFreeSectionsMap'
        (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ :=
    exists_bound_surjective_finFreeSectionsMap_quotGrassmannian.{u} n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro S T hT a hP d e he hd m σ U
  let Q := twistedFreeQuotientSheaf n S l r a
  let ψ := Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  haveI : Q.IsFinitePresentation :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over T a
  haveI : Epi ψ :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  have hflat : Q.FlatOver (projectiveSpaceOverπ n T.left) :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over T a
  exact hd₁ T.left Q (by infer_instance) ψ (by infer_instance)
    hflat hP d e he hd σ U

end ProjectiveSpace

/-- Inputs needed to turn the monomial kernel construction into a natural transformation
from fixed-polynomial twisted-free Quot to a free Grassmannian.

The field `kernel_pullback` is deliberately stated directly on `SubmoduleSheafData`: this
is the proof-irrelevant level at which the target Grassmannian is defined, and it avoids
transporting the chosen `IsProjectiveOfRank` and surjectivity proofs.  Invariance under
equivalent quotient presentations is unconditional
(`twistedFreeQuotGrassmannianKernelData_eq_of_r`). -/
structure TwistedFreeQuotGrassmannianNatTransData
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m q : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Type (u + 1) where
  /-- The normalized twisted pushforward has the fixed rank `q`. -/
  isProjectiveOfRank : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      Modules.IsProjectiveOfRank q
        (twistedFreeQuotientTwistPushforward n S l r a d)
  /-- The normalized monomial map is surjective on every affine open. -/
  surjective : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      ∀ U : T.left.affineOpens, Function.Surjective
        (Modules.finFreeSectionsMap'
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)
  /-- The monomial kernel commutes with arbitrary base change of the test scheme. -/
  kernel_pullback : ∀ {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      twistedFreeQuotGrassmannianKernelData n S l r (a.pullback g) d e he σ =
        (twistedFreeQuotGrassmannianKernelData n S l r a d e he σ).comap g.left

namespace TwistedFreeQuotGrassmannianNatTransData

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- A chosen raw representative of a fixed-polynomial Quot point. -/
noncomputable def representative
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T) :=
  Classical.choose x.2

/-- The chosen representative presents the underlying Quotient class. -/
lemma representative_mk
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    Quotient.mk _ (representative x) = x.1 :=
  (Classical.choose_spec x.2).1

/-- The chosen representative has the prescribed fibrewise Hilbert polynomial. -/
lemma representative_hasFiberwiseHilbertPolynomial
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    (representative x).HasFiberwiseHilbertPolynomial P :=
  (Classical.choose_spec x.2).2

/-- The pointwise map underlying the Quot-to-Grassmannian transformation. -/
noncomputable def component
    (D : TwistedFreeQuotGrassmannianNatTransData n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    (Modules.grassmannianFunctorOver S q m).obj T :=
  ULift.up (twistedFreeQuotGrassmannianPoint n S l r (representative x) d e he σ
    (D.isProjectiveOfRank (unop T) (representative x)
      (representative_hasFiberwiseHilbertPolynomial x))
    (D.surjective (unop T) (representative x)
      (representative_hasFiberwiseHilbertPolynomial x)))

/-- The component is represented by the monomial kernel of the chosen raw Quot
presentation. -/
lemma component_down_val
    (D : TwistedFreeQuotGrassmannianNatTransData n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    (D.component T x).down.1 =
      twistedFreeQuotGrassmannianKernelData n S l r (representative x) d e he σ := rfl

/-- The component kernel can be computed from any raw representative of the underlying
Quotient class, not only from the representative selected by `Classical.choose`. -/
lemma component_down_val_eq_of_mk_eq
    (D : TwistedFreeQuotGrassmannianNatTransData n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T))
    (ha : Quotient.mk _ a = x.1) :
    (D.component T x).down.1 =
      twistedFreeQuotGrassmannianKernelData n S l r a d e he σ := by
  rw [component_down_val]
  apply twistedFreeQuotGrassmannianKernelData_eq_of_r n S l r _ d e he σ
  exact Quotient.exact ((representative_mk x).trans ha.symm)

/-- The monomial-kernel construction defines a natural transformation from the
fixed-polynomial twisted-free Quot functor to the free Grassmannian. -/
noncomputable def natTrans
    (D : TwistedFreeQuotGrassmannianNatTransData n S l r P d e he m q σ) :
    quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P ⟶
      Modules.grassmannianFunctorOver S q m where
  app T := ↾fun x ↦ D.component T x
  naturality := by
    intro T T' g
    ext x
    apply ULift.ext
    apply Subtype.ext
    let a := representative x
    let x' := (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).map g x
    let b := representative x'
    change twistedFreeQuotGrassmannianKernelData n S l r b d e he σ =
      (twistedFreeQuotGrassmannianKernelData n S l r a d e he σ).comap g.unop.left
    let s' := Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T')
    have hmk : (Quotient.mk s' b : Quotient s') =
        Quotient.mk s' (a.pullback g.unop) := by
      calc
        Quotient.mk s' b = x'.1 := representative_mk x'
        _ = (quotFunctor
            (Modules.QuotientPullbackData.twistedFreeAmbient
              (n := n) (r := r) (l := l))
            (projectiveSpaceOverπ n S)).map g x.1 := rfl
        _ = Quotient.mk s' (a.pullback g.unop) := by
          rw [← representative_mk x]
          rfl
    have hr : (Modules.QuotientPullbackData.setoid
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) (unop T')).r b (a.pullback g.unop) :=
      Quotient.exact hmk
    exact (twistedFreeQuotGrassmannianKernelData_eq_of_r
      n S l r hr d e he σ).trans
      (D.kernel_pullback g.unop a
        (representative_hasFiberwiseHilbertPolynomial x))

@[simp]
lemma natTrans_app_apply
    (D : TwistedFreeQuotGrassmannianNatTransData n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    D.natTrans.app T x = D.component T x := rfl

end TwistedFreeQuotGrassmannianNatTransData

/-- The two canonical fixed-degree base-change statements needed by the intrinsic
Quot-to-Grassmannian construction.

The first field is the Cohomology-and-Base-Change theorem for the canonical morphism
`twistedFreeQuotientTwistPushforwardBaseChangeHom`.  The second is the naturality of the
monomial free map through that same canonical morphism.  The second statement does not
need the Hilbert-polynomial hypothesis or invertibility of the base-change map. -/
structure TwistedFreeQuotGrassmannianCanonicalBaseChangeData
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Type (u + 1) where
  /-- The canonical fixed-degree pushforward base-change morphism is invertible on every
  fixed-polynomial Quot family. -/
  baseChange_isIso : ∀ {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      IsIso (twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d)
  /-- The monomial map commutes with the canonical pushforward base-change morphism. -/
  freeMap_baseChange : ∀ {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    (Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Modules.pullback g.left).map
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      twistedFreeQuotGrassmannianFreeMap
        n S l r (a.pullback g) d e he σ

/-- Construct the canonical base-change data from the fixed-degree
Cohomology-and-Base-Change theorem.  Naturality of the monomial map is formal. -/
def TwistedFreeQuotGrassmannianCanonicalBaseChangeData.ofBaseChange
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m : ℕ}
    {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}
    (hBC : ∀ {T T' : Over S} (g : T' ⟶ T)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        IsIso (twistedFreeQuotientTwistPushforwardBaseChangeHom
          n S l r g a d)) :
    TwistedFreeQuotGrassmannianCanonicalBaseChangeData
      n S l r P d e he m σ where
  baseChange_isIso := hBC
  freeMap_baseChange := fun g a ↦
    twistedFreeQuotGrassmannianFreeMap_baseChange
      n S l r g a d e he σ

/-- Inputs for the intrinsic strict-quotient version of the monomial
Quot-to-Grassmannian transformation.

Unlike `TwistedFreeQuotGrassmannianNatTransData`, this constructor uses the already
functorial `FreeQuotient.kernelData`.  Its last field therefore asks only that the
strict monomial quotient commute with base change up to the defining equivalence
relation.  This is exactly the form produced by
`twistedFreeQuotGrassmannianFreeQuotient_pullback_r_of_iso` from a fixed-degree
base-change isomorphism and its monomial compatibility square. -/
structure TwistedFreeQuotGrassmannianQuotientNatTransData
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m q : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Type (u + 1) where
  /-- The normalized twisted pushforward has the fixed rank `q`. -/
  isProjectiveOfRank : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      Modules.IsProjectiveOfRank q
        (twistedFreeQuotientTwistPushforward n S l r a d)
  /-- The normalized monomial map is surjective on every affine open. -/
  surjective : ∀ (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      ∀ U : T.left.affineOpens, Function.Surjective
        (Modules.finFreeSectionsMap'
          (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1)
  /-- Pullback of the strict monomial quotient agrees with the strict quotient of the
  pulled-back Quot datum. -/
  freeQuotient_pullback_r : ∀ {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hP : a.HasFiberwiseHilbertPolynomial P),
    let hP' := a.hasFiberwiseHilbertPolynomial_pullback g hP
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T'.left).r
      ((twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ
        (isProjectiveOfRank T a hP) (surjective T a hP)).pullback g.left)
      (twistedFreeQuotGrassmannianFreeQuotient n S l r (a.pullback g) d e he σ
        (isProjectiveOfRank T' (a.pullback g) hP')
        (surjective T' (a.pullback g) hP'))

/-- Construct the intrinsic natural-transformation data from uniform rank and
surjectivity inputs together with the two canonical fixed-degree base-change
statements. -/
noncomputable def TwistedFreeQuotGrassmannianQuotientNatTransData.ofCanonicalBaseChange
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
    {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}
    (hM : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        Modules.IsProjectiveOfRank q
          (twistedFreeQuotientTwistPushforward n S l r a d))
    (hsurj : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        ∀ U : T.left.affineOpens, Function.Surjective
          (Modules.finFreeSectionsMap'
            (twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1))
    (B : TwistedFreeQuotGrassmannianCanonicalBaseChangeData
      n S l r P d e he m σ) :
    TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ where
  isProjectiveOfRank := hM
  surjective := hsurj
  freeQuotient_pullback_r := by
    intro T T' g a hP
    let hP' := a.hasFiberwiseHilbertPolynomial_pullback g hP
    let β := twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d
    letI : IsIso β := B.baseChange_isIso g a hP
    apply twistedFreeQuotGrassmannianFreeQuotient_pullback_r_of_iso
      n S l r g a d e he σ
      (hM T a hP) (hsurj T a hP)
      (hM T' (a.pullback g) hP') (hsurj T' (a.pullback g) hP')
      (asIso β)
    simpa only [asIso_hom] using B.freeMap_baseChange g a

namespace TwistedFreeQuotGrassmannianQuotientNatTransData

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The strict monomial quotient attached to the chosen representative of a fixed
Hilbert-polynomial Quot point. -/
noncomputable def representativeFreeQuotient
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    Modules.FreeQuotient q (ULift.{u} (Fin m)) (unop T).left :=
  let a := TwistedFreeQuotGrassmannianNatTransData.representative x
  let hP :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
  twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ
    (D.isProjectiveOfRank (unop T) a hP) (D.surjective (unop T) a hP)

/-- The pointwise map underlying the intrinsic strict-quotient construction. -/
noncomputable def component
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    (Modules.grassmannianFunctorOver S q m).obj T :=
  ULift.up (D.representativeFreeQuotient x).kernelPoint

/-- The underlying submodule datum of the intrinsic component is the glued kernel of
its strict monomial quotient. -/
@[simp]
lemma component_down_val
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    (D.component T x).down.1 = (D.representativeFreeQuotient x).kernelData := rfl

/-- The intrinsic strict-quotient construction is a natural transformation from the
fixed-polynomial twisted-free Quot functor to the free Grassmannian. -/
noncomputable def natTrans
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ) :
    quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P ⟶
      Modules.grassmannianFunctorOver S q m where
  app T := ↾fun x ↦ D.component T x
  naturality := by
    intro T T' g
    ext x
    apply ULift.ext
    apply Subtype.ext
    let a := TwistedFreeQuotGrassmannianNatTransData.representative x
    let hPa :=
      TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
    let x' := (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).map g x
    let b := TwistedFreeQuotGrassmannianNatTransData.representative x'
    let hPb :=
      TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x'
    let hPa' := a.hasFiberwiseHilbertPolynomial_pullback g.unop hPa
    let qa := twistedFreeQuotGrassmannianFreeQuotient n S l r a d e he σ
      (D.isProjectiveOfRank (unop T) a hPa) (D.surjective (unop T) a hPa)
    let qa' := twistedFreeQuotGrassmannianFreeQuotient
      n S l r (a.pullback g.unop) d e he σ
      (D.isProjectiveOfRank (unop T') (a.pullback g.unop) hPa')
      (D.surjective (unop T') (a.pullback g.unop) hPa')
    let qb := twistedFreeQuotGrassmannianFreeQuotient n S l r b d e he σ
      (D.isProjectiveOfRank (unop T') b hPb) (D.surjective (unop T') b hPb)
    change qb.kernelData = qa.kernelData.comap g.unop.left
    let s' := Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T')
    have hmk : (Quotient.mk s' b : Quotient s') =
        Quotient.mk s' (a.pullback g.unop) := by
      calc
        Quotient.mk s' b = x'.1 :=
          TwistedFreeQuotGrassmannianNatTransData.representative_mk x'
        _ = (quotFunctor
            (Modules.QuotientPullbackData.twistedFreeAmbient
              (n := n) (r := r) (l := l))
            (projectiveSpaceOverπ n S)).map g x.1 := rfl
        _ = Quotient.mk s' (a.pullback g.unop) := by
          rw [← TwistedFreeQuotGrassmannianNatTransData.representative_mk x]
          rfl
    have hr : (Modules.QuotientPullbackData.setoid
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) (unop T')).r b (a.pullback g.unop) :=
      Quotient.exact hmk
    have hrep : (Modules.FreeQuotient.setoid q
        (ULift.{u} (Fin m)) (unop T').left).r qb qa' :=
      twistedFreeQuotGrassmannianFreeQuotient_r_of_r
        n S l r hr d e he σ
        (D.isProjectiveOfRank (unop T') b hPb)
        (D.surjective (unop T') b hPb)
        (D.isProjectiveOfRank (unop T') (a.pullback g.unop) hPa')
        (D.surjective (unop T') (a.pullback g.unop) hPa')
    have hbase : (Modules.FreeQuotient.setoid q
        (ULift.{u} (Fin m)) (unop T').left).r (qa.pullback g.unop.left) qa' :=
      D.freeQuotient_pullback_r g.unop a hPa
    calc
      qb.kernelData = qa'.kernelData :=
        Modules.FreeQuotient.kernelData_eq_of_r hrep
      _ = (qa.pullback g.unop.left).kernelData :=
        (Modules.FreeQuotient.kernelData_eq_of_r hbase).symm
      _ = qa.kernelData.comap g.unop.left :=
        (Modules.FreeQuotient.kernelData_comap qa g.unop.left).symm

@[simp]
lemma natTrans_app_apply
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : (Over S)ᵒᵖ)
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    D.natTrans.app T x = D.component T x := rfl

end TwistedFreeQuotGrassmannianQuotientNatTransData

end AlgebraicGeometry.Scheme

end
