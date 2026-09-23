module

public import StacksAndModuli.API.GlobalPrincipalBundleFpqcDescent

/-!
# Descent of the torsor condition

For the structured fpqc descent construction of a principal bundle, this file
glues the inverses of the local torsor maps. It proves both inverse identities
by fpqc-local comparison with the original principal bundles. Consequently, the
torsor-isomorphism hypothesis in the underlying gluing reduction is automatic.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace ClassifyingObj.UnderlyingGluing

variable {G} {T : Over S} {R : Sieve T}
  {D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G)}
  {hDobj : ∀ q : R.arrows.category,
    (classifyingPrestack G).p.obj (D.obj q) = q.obj.left}
  {hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    IsHomLift (classifyingPrestack G).p k.hom.left (D.map k)}
  (A : ClassifyingObj.UnderlyingGluing D hDobj hDmap)

/-- The pullback of the descent sieve to the pair space of the descended
projection. -/
noncomputable def pairSieve : Sieve (pullback A.p A.p) :=
  R.pullback (pullback.snd A.p A.p ≫ A.p)

lemma pairSieve_mem (hR : R ∈ Scheme.fpqcTopology.over S T) :
    A.pairSieve ∈ Scheme.fpqcTopology.over S (pullback A.p A.p) :=
  (Scheme.fpqcTopology.over S).pullback_stable
    (pullback.snd A.p A.p ≫ A.p) hR

lemma pair_mem {Z : Over S} (l : Z ⟶ pullback A.p A.p)
    (hl : A.pairSieve l) :
    R ((l ≫ pullback.snd A.p A.p) ≫ A.p) := by
  exact hl

/-- The local descent object selected by a point of the pair space. -/
noncomputable abbrev pairLocalObj {Z : Over S} (l : Z ⟶ pullback A.p A.p)
    (hl : A.pairSieve l) : R.arrows.category :=
  A.localObj (l ≫ pullback.snd A.p A.p) (A.pair_mem l hl)

/-- The first component of a point of the pair space, lifted to the same local
total space selected by its second component. -/
noncomputable def pairPointFst {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    Z ⟶ (D.obj (A.pairLocalObj l hl)).bundle.P :=
  (A.isPullback (A.pairLocalObj l hl)).lift
    (l ≫ pullback.fst A.p A.p)
    (eqToHom (hDobj (A.pairLocalObj l hl)).symm) (by
      calc
        (l ≫ pullback.fst A.p A.p) ≫ A.p =
            (l ≫ pullback.snd A.p A.p) ≫ A.p := by
              simp only [Category.assoc, pullback.condition]
        _ = eqToHom (hDobj (A.pairLocalObj l hl)).symm ≫
            (eqToHom (hDobj (A.pairLocalObj l hl)) ≫
              (A.pairLocalObj l hl).obj.hom) := by
                simp [pairLocalObj, localObj, Category.assoc])

@[reassoc (attr := simp)]
lemma pairPointFst_total {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointFst l hl ≫ A.total (A.pairLocalObj l hl) =
      l ≫ pullback.fst A.p A.p :=
  (A.isPullback (A.pairLocalObj l hl)).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairPointFst_projection {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointFst l hl ≫ (D.obj (A.pairLocalObj l hl)).bundle.p =
      eqToHom (hDobj (A.pairLocalObj l hl)).symm :=
  (A.isPullback (A.pairLocalObj l hl)).lift_snd _ _ _

/-- The second component, lifted to the selected local total space. -/
noncomputable def pairPointSnd {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    Z ⟶ (D.obj (A.pairLocalObj l hl)).bundle.P :=
  A.point (l ≫ pullback.snd A.p A.p) (A.pair_mem l hl)

@[reassoc (attr := simp)]
lemma pairPointSnd_total {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointSnd l hl ≫ A.total (A.pairLocalObj l hl) =
      l ≫ pullback.snd A.p A.p :=
  A.point_total _ _

@[reassoc (attr := simp)]
lemma pairPointSnd_projection {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointSnd l hl ≫ (D.obj (A.pairLocalObj l hl)).bundle.p =
      eqToHom (hDobj (A.pairLocalObj l hl)).symm :=
  A.point_projection _ _

/-- The transition between the selected local objects after precomposition. -/
noncomputable def pairLocalMap {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairLocalObj (h ≫ l) (A.pairSieve.downward_closed hl h) ⟶
      A.pairLocalObj l hl :=
  ⟨Over.homMk h⟩

@[simp]
lemma pairLocalMap_hom_left {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    (A.pairLocalMap h l hl).hom.left = h := rfl

lemma pairPointFst_naturality {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointFst (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
        (D.map (A.pairLocalMap h l hl)).total =
      h ≫ A.pairPointFst l hl := by
  apply (A.isPullback (A.pairLocalObj l hl)).hom_ext
  · rw [Category.assoc, A.naturality (A.pairLocalMap h l hl)]
    simp [Category.assoc]
  · rw [Category.assoc, (D.map (A.pairLocalMap h l hl)).isPullback.w]
    simp only [← Category.assoc, A.pairPointFst_projection]
    have hLift : IsHomLift (classifyingPrestack G).p h
        (D.map (A.pairLocalMap h l hl)) := by
      simpa [pairLocalMap] using hDmap (A.pairLocalMap h l hl)
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p h
      (D.map (A.pairLocalMap h l hl))
    change (D.map (A.pairLocalMap h l hl)).base = _ at H
    rw [H]
    simp [Category.assoc, A.pairPointFst_projection]

lemma pairPointSnd_naturality {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPointSnd (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
        (D.map (A.pairLocalMap h l hl)).total =
      h ≫ A.pairPointSnd l hl := by
  apply (A.isPullback (A.pairLocalObj l hl)).hom_ext
  · rw [Category.assoc, A.naturality (A.pairLocalMap h l hl)]
    simp [Category.assoc]
  · rw [Category.assoc, (D.map (A.pairLocalMap h l hl)).isPullback.w]
    simp only [← Category.assoc, A.pairPointSnd_projection]
    have hLift : IsHomLift (classifyingPrestack G).p h
        (D.map (A.pairLocalMap h l hl)) := by
      simpa [pairLocalMap] using hDmap (A.pairLocalMap h l hl)
    letI := hLift
    have H := IsHomLift.fac' (classifyingPrestack G).p h
      (D.map (A.pairLocalMap h l hl))
    change (D.map (A.pairLocalMap h l hl)).base = _ at H
    rw [H]
    simp [Category.assoc, A.pairPointSnd_projection]

/-- A point of the descended pair space lifted to the pair space of its selected
local principal bundle. -/
noncomputable def pairPoint {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    Z ⟶ pullback (D.obj (A.pairLocalObj l hl)).bundle.p
      (D.obj (A.pairLocalObj l hl)).bundle.p :=
  pullback.lift (A.pairPointFst l hl)
    (A.pairPointSnd l hl) (by
      rw [A.pairPointFst_projection, A.pairPointSnd_projection])

@[reassoc (attr := simp)]
lemma pairPoint_fst {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPoint l hl ≫
      pullback.fst (D.obj (A.pairLocalObj l hl)).bundle.p
        (D.obj (A.pairLocalObj l hl)).bundle.p =
      A.pairPointFst l hl :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairPoint_snd {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPoint l hl ≫
      pullback.snd (D.obj (A.pairLocalObj l hl)).bundle.p
        (D.obj (A.pairLocalObj l hl)).bundle.p =
      A.pairPointSnd l hl :=
  pullback.lift_snd _ _ _

/-- The map of pair spaces induced by a transition morphism in the descent
datum. -/
noncomputable def localPairMap
    (A : ClassifyingObj.UnderlyingGluing D hDobj hDmap)
    {q r : R.arrows.category} (m : q ⟶ r) :
    pullback (D.obj q).bundle.p (D.obj q).bundle.p ⟶
      pullback (D.obj r).bundle.p (D.obj r).bundle.p :=
  pullback.lift
    (pullback.fst _ _ ≫ (D.map m).total)
    (pullback.snd _ _ ≫ (D.map m).total) (by
      simp only [Category.assoc, (D.map m).isPullback.w]
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (D.map m).base)
        (pullback.condition : pullback.fst (D.obj q).bundle.p
          (D.obj q).bundle.p ≫ (D.obj q).bundle.p = _))

@[reassoc (attr := simp)]
lemma localPairMap_fst {q r : R.arrows.category} (m : q ⟶ r) :
    A.localPairMap m ≫ pullback.fst (D.obj r).bundle.p (D.obj r).bundle.p =
      pullback.fst (D.obj q).bundle.p (D.obj q).bundle.p ≫
        (D.map m).total :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma localPairMap_snd {q r : R.arrows.category} (m : q ⟶ r) :
    A.localPairMap m ≫ pullback.snd (D.obj r).bundle.p (D.obj r).bundle.p =
      pullback.snd (D.obj q).bundle.p (D.obj q).bundle.p ≫
        (D.map m).total :=
  pullback.lift_snd _ _ _

lemma torsorMap_naturality {q r : R.arrows.category} (m : q ⟶ r) :
    ModObj.torsorMap (D.obj q).bundle.p (D.obj q).bundle.invariant ≫
        A.localPairMap m =
      (G ◁ (D.map m).total) ≫
        ModObj.torsorMap (D.obj r).bundle.p
          (D.obj r).bundle.invariant := by
  apply pullback.hom_ext
  · simp only [Category.assoc, A.localPairMap_fst,
      ModObj.torsorMap_fst_assoc]
    rw [ModObj.torsorMap_fst]
    exact (D.map m).equivariant.smul_hom
  · simp only [Category.assoc, A.localPairMap_snd,
      ModObj.torsorMap_snd_assoc, ModObj.torsorMap_snd]
    exact (whiskerLeft_snd G (D.map m).total).symm

lemma localTorsorInv_transition {q r : R.arrows.category} (m : q ⟶ r) :
    inv (ModObj.torsorMap (D.obj q).bundle.p
          (D.obj q).bundle.invariant) ≫
        (G ◁ (D.map m).total) =
      A.localPairMap m ≫
        inv (ModObj.torsorMap (D.obj r).bundle.p
          (D.obj r).bundle.invariant) := by
  rw [← cancel_epi (ModObj.torsorMap (D.obj q).bundle.p
    (D.obj q).bundle.invariant)]
  rw [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, A.torsorMap_naturality]
  simp

lemma pairPoint_naturality {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
        A.localPairMap (A.pairLocalMap h l hl) =
      h ≫ A.pairPoint l hl := by
  apply pullback.hom_ext
  · simp [Category.assoc, A.pairPointFst_naturality]
  · simp [Category.assoc, A.pairPointSnd_naturality]

/-- The inverse torsor value supplied by the selected local principal bundle,
then mapped to the descended total space. -/
noncomputable def localTorsorInv {Z : Over S}
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    Z ⟶ G ⊗ A.P :=
  A.pairPoint l hl ≫
    inv (ModObj.torsorMap (D.obj (A.pairLocalObj l hl)).bundle.p
      (D.obj (A.pairLocalObj l hl)).bundle.invariant) ≫
    (G ◁ A.total (A.pairLocalObj l hl))

lemma localTorsorInv_naturality {W Z : Over S} (h : W ⟶ Z)
    (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    A.localTorsorInv (h ≫ l) (A.pairSieve.downward_closed hl h) =
      h ≫ A.localTorsorInv l hl := by
  let m := A.pairLocalMap h l hl
  let q' := A.pairLocalObj (h ≫ l) (A.pairSieve.downward_closed hl h)
  let q := A.pairLocalObj l hl
  let tq' := ModObj.torsorMap (D.obj q').bundle.p
    (D.obj q').bundle.invariant
  let tq := ModObj.torsorMap (D.obj q).bundle.p
    (D.obj q).bundle.invariant
  change (A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
      inv tq') ≫ (G ◁ A.total q') =
    h ≫ ((A.pairPoint l hl ≫ inv tq) ≫ (G ◁ A.total q))
  calc
    _ = (A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
          inv tq') ≫
        ((G ◁ (D.map m).total) ≫ (G ◁ A.total q)) := by
      rw [← MonoidalCategory.whiskerLeft_comp, A.naturality m]
    _ = (A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
          (inv tq' ≫ (G ◁ (D.map m).total))) ≫
        (G ◁ A.total q) := by simp only [Category.assoc]
    _ = (A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
          (A.localPairMap m ≫ inv tq)) ≫
        (G ◁ A.total q) := by
      rw [A.localTorsorInv_transition m]
    _ = ((A.pairPoint (h ≫ l) (A.pairSieve.downward_closed hl h) ≫
          A.localPairMap m) ≫ inv tq) ≫
        (G ◁ A.total q) := by simp only [Category.assoc]
    _ = ((h ≫ A.pairPoint l hl) ≫ inv tq) ≫
        (G ◁ A.total q) := by
      rw [A.pairPoint_naturality h l hl]
    _ = h ≫ ((A.pairPoint l hl ≫ inv tq) ≫
        (G ◁ A.total q)) := by simp only [Category.assoc]

/-- The inverse of the descended torsor map, glued from the inverses of the
local torsor maps. -/
noncomputable def descendedTorsorInv
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    pullback A.p A.p ⟶ G ⊗ A.P :=
  let fam : Presieve.FamilyOfElements (yoneda.obj (G ⊗ A.P))
      A.pairSieve.arrows := fun _ l hl ↦ A.localTorsorInv l hl
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S)
      (yoneda.obj (G ⊗ A.P)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  (hP A.pairSieve (A.pairSieve_mem hR)).amalgamate fam (by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W l h hl
    exact A.localTorsorInv_naturality h l hl)

lemma descendedTorsorInv_local
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    l ≫ A.descendedTorsorInv hR = A.localTorsorInv l hl := by
  let fam : Presieve.FamilyOfElements (yoneda.obj (G ⊗ A.P))
      A.pairSieve.arrows := fun _ l hl ↦ A.localTorsorInv l hl
  let hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W l h hl
    exact A.localTorsorInv_naturality h l hl
  let hP : Presieve.IsSheaf (Scheme.fpqcTopology.over S)
      (yoneda.obj (G ⊗ A.P)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  exact (hP A.pairSieve (A.pairSieve_mem hR)).valid_glue hcompat l hl

lemma localTorsorInv_torsorMap
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ pullback A.p A.p) (hl : A.pairSieve l) :
    letI := A.descendedModObj hR
    A.localTorsorInv l hl ≫
        ModObj.torsorMap A.p (A.descended_invariant hR) = l := by
  letI := A.descendedModObj hR
  let q := A.pairLocalObj l hl
  let tq := ModObj.torsorMap (D.obj q).bundle.p
    (D.obj q).bundle.invariant
  apply pullback.hom_ext
  · change (A.pairPoint l hl ≫ inv tq ≫ (G ◁ A.total q)) ≫
        ModObj.torsorMap A.p (A.descended_invariant hR) ≫
          pullback.fst A.p A.p = l ≫ pullback.fst A.p A.p
    simp only [Category.assoc]
    rw [ModObj.torsorMap_fst]
    change A.pairPoint l hl ≫ inv tq ≫ (G ◁ A.total q) ≫
      A.descendedAction hR = l ≫ pullback.fst A.p A.p
    rw [← A.total_smul hR q]
    have hif : inv tq ≫ γ[G, (D.obj q).bundle.P] =
        pullback.fst (D.obj q).bundle.p (D.obj q).bundle.p := by
      rw [← ModObj.torsorMap_fst (D.obj q).bundle.p
        (D.obj q).bundle.invariant]
      simp [tq]
    change A.pairPoint l hl ≫ inv tq ≫ γ[G, (D.obj q).bundle.P] ≫
      A.total q = l ≫ pullback.fst A.p A.p
    have hif_assoc : inv tq ≫
        (γ[G, (D.obj q).bundle.P] ≫ A.total q) =
        pullback.fst (D.obj q).bundle.p (D.obj q).bundle.p ≫
          A.total q := by
      rw [← Category.assoc, hif]
    rw [hif_assoc]
    rw [← Category.assoc, A.pairPoint_fst, A.pairPointFst_total]
  · change (A.pairPoint l hl ≫ inv tq ≫ (G ◁ A.total q)) ≫
        ModObj.torsorMap A.p (A.descended_invariant hR) ≫
          pullback.snd A.p A.p = l ≫ pullback.snd A.p A.p
    simp only [Category.assoc]
    rw [ModObj.torsorMap_snd]
    rw [whiskerLeft_snd]
    have his : inv tq ≫ snd G (D.obj q).bundle.P =
        pullback.snd (D.obj q).bundle.p (D.obj q).bundle.p := by
      rw [← ModObj.torsorMap_snd (D.obj q).bundle.p
        (D.obj q).bundle.invariant]
      simp [tq]
    change A.pairPoint l hl ≫ inv tq ≫ snd G (D.obj q).bundle.P ≫
      A.total q = l ≫ pullback.snd A.p A.p
    have his_assoc : inv tq ≫
        (snd G (D.obj q).bundle.P ≫ A.total q) =
        pullback.snd (D.obj q).bundle.p (D.obj q).bundle.p ≫
          A.total q := by
      rw [← Category.assoc, his]
    rw [his_assoc]
    rw [← Category.assoc, A.pairPoint_snd, A.pairPointSnd_total]

lemma descendedTorsorInv_hom
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    letI := A.descendedModObj hR
    A.descendedTorsorInv hR ≫
      ModObj.torsorMap A.p (A.descended_invariant hR) = 𝟙 _ := by
  letI := A.descendedModObj hR
  let hF : Presieve.IsSheaf (Scheme.fpqcTopology.over S)
      (yoneda.obj (pullback A.p A.p)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply yoneda.map_injective
  apply (hF A.pairSieve (A.pairSieve_mem hR)).hom_ext
  ext Z l
  have hl : A.pairSieve l.val := l.property
  change l.val ≫ (A.descendedTorsorInv hR ≫
      ModObj.torsorMap A.p (A.descended_invariant hR)) =
    l.val ≫ 𝟙 (pullback A.p A.p)
  rw [← Category.assoc,
    A.descendedTorsorInv_local hR (Z := Z.unop) l.val hl]
  exact (A.localTorsorInv_torsorMap hR (Z := Z.unop) l.val hl).trans
    (Category.comp_id l.val).symm

lemma torsor_pair_mem
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    A.pairSieve
      (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR)) := by
  letI := A.descendedModObj hR
  change R (((l ≫ ModObj.torsorMap A.p (A.descended_invariant hR)) ≫
    pullback.snd A.p A.p) ≫ A.p)
  have hsnd : (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR)) ≫
      pullback.snd A.p A.p = l ≫ snd G A.P := by
    rw [Category.assoc, ModObj.torsorMap_snd]
  rw [hsnd]
  exact hl

/-- A point of `G × P` lifted to the local action space selected by the second
component of its image under the descended torsor map. -/
noncomputable def torsorActionPoint
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    Z ⟶ G ⊗ (D.obj (A.pairLocalObj
      (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
      (A.torsor_pair_mem hR l hl))).bundle.P := by
  letI := A.descendedModObj hR
  exact lift (l ≫ fst G A.P)
    (A.pairPointSnd
      (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
      (A.torsor_pair_mem hR l hl))

lemma torsorActionPoint_snd
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    A.torsorActionPoint hR l hl ≫
      snd G (D.obj (A.pairLocalObj
        (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
        (A.torsor_pair_mem hR l hl))).bundle.P =
      A.pairPointSnd
        (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
        (A.torsor_pair_mem hR l hl) := by
  letI := A.descendedModObj hR
  simp [torsorActionPoint]

lemma torsorActionPoint_total
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    A.torsorActionPoint hR l hl ≫
      (G ◁ A.total (A.pairLocalObj
        (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
        (A.torsor_pair_mem hR l hl))) = l := by
  letI := A.descendedModObj hR
  apply CartesianMonoidalCategory.hom_ext
  · simp [torsorActionPoint, Category.assoc]
  · simp only [Category.assoc, whiskerLeft_snd]
    rw [← Category.assoc, A.torsorActionPoint_snd hR l hl]
    rw [A.pairPointSnd_total]
    rw [Category.assoc, ModObj.torsorMap_snd]

lemma pairPoint_torsor_eq
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    A.pairPoint
        (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
        (A.torsor_pair_mem hR l hl) =
      A.torsorActionPoint hR l hl ≫
        ModObj.torsorMap
          (D.obj (A.pairLocalObj
            (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
            (A.torsor_pair_mem hR l hl))).bundle.p
          (D.obj (A.pairLocalObj
            (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
            (A.torsor_pair_mem hR l hl))).bundle.invariant := by
  letI := A.descendedModObj hR
  let lp := l ≫ ModObj.torsorMap A.p (A.descended_invariant hR)
  let hp := A.torsor_pair_mem hR l hl
  let q := A.pairLocalObj lp hp
  apply pullback.hom_ext
  · rw [A.pairPoint_fst]
    rw [Category.assoc, ModObj.torsorMap_fst]
    apply (A.isPullback q).hom_ext
    · rw [A.pairPointFst_total]
      change lp ≫ pullback.fst A.p A.p =
        A.torsorActionPoint hR l hl ≫
          (γ[G, (D.obj q).bundle.P] ≫ A.total q)
      rw [A.total_smul hR q]
      rw [← Category.assoc, A.torsorActionPoint_total hR l hl]
      simp [lp]
      change l ≫ A.descendedAction hR = l ≫ A.descendedAction hR
      rfl
    · rw [Category.assoc, (D.obj q).bundle.invariant]
      rw [← Category.assoc, A.torsorActionPoint_snd hR l hl]
      rw [A.pairPointFst_projection, A.pairPointSnd_projection]
  · rw [A.pairPoint_snd]
    rw [Category.assoc, ModObj.torsorMap_snd]
    exact (A.torsorActionPoint_snd hR l hl).symm

lemma torsorMap_localTorsorInv
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    {Z : Over S} (l : Z ⟶ G ⊗ A.P) (hl : A.actionSieve l) :
    letI := A.descendedModObj hR
    A.localTorsorInv
      (l ≫ ModObj.torsorMap A.p (A.descended_invariant hR))
      (A.torsor_pair_mem hR l hl) = l := by
  letI := A.descendedModObj hR
  let lp := l ≫ ModObj.torsorMap A.p (A.descended_invariant hR)
  let hp := A.torsor_pair_mem hR l hl
  let q := A.pairLocalObj lp hp
  let tq := ModObj.torsorMap (D.obj q).bundle.p
    (D.obj q).bundle.invariant
  change (A.pairPoint lp hp ≫ inv tq) ≫ (G ◁ A.total q) = l
  rw [A.pairPoint_torsor_eq hR l hl]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc]
  exact A.torsorActionPoint_total hR l hl

lemma descendedTorsorInv_inv_hom
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    letI := A.descendedModObj hR
    ModObj.torsorMap A.p (A.descended_invariant hR) ≫
      A.descendedTorsorInv hR = 𝟙 _ := by
  letI := A.descendedModObj hR
  let hF : Presieve.IsSheaf (Scheme.fpqcTopology.over S)
      (yoneda.obj (G ⊗ A.P)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply yoneda.map_injective
  apply (hF A.actionSieve (A.actionSieve_mem hR)).hom_ext
  ext Z l
  have hl : A.actionSieve l.val := l.property
  have hp := A.torsor_pair_mem hR l.val hl
  change l.val ≫ (ModObj.torsorMap A.p (A.descended_invariant hR) ≫
      A.descendedTorsorInv hR) = l.val ≫ 𝟙 (G ⊗ A.P)
  rw [← Category.assoc,
    A.descendedTorsorInv_local hR (Z := Z.unop)
      (l.val ≫ ModObj.torsorMap A.p (A.descended_invariant hR)) hp]
  rw [A.torsorMap_localTorsorInv hR (Z := Z.unop) l.val hl]
  exact (Category.comp_id l.val).symm

/-- The torsor condition descends automatically once the underlying total spaces
and cartesian comparison squares have been glued. -/
lemma descended_torsor_isIso
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    letI := A.descendedModObj hR
    IsIso (ModObj.torsorMap A.p (A.descended_invariant hR)) := by
  letI := A.descendedModObj hR
  exact ⟨⟨A.descendedTorsorInv hR,
    A.descendedTorsorInv_inv_hom hR,
    A.descendedTorsorInv_hom hR⟩⟩

/-- The raw object-gluing conclusion after underlying cartesian gluing and
descent of the four geometric properties.  The torsor condition is discharged
internally by `descended_torsor_isIso`. -/
theorem exists_gluing_of_underlying_of_properties
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hflat : Flat A.p.left) (hsurjective : Surjective A.p.left)
    (hlfp : LocallyOfFinitePresentation A.p.left)
    (hsmooth : Smooth A.p.left) :
    ∃ (a : ClassifyingObj G)
      (_ : (classifyingPrestack G).p.obj a = T)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q : R.arrows.category,
        IsHomLift (classifyingPrestack G).p q.obj.hom (ε q)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r),
        D.map k ≫ ε r = ε q := by
  exact ClassifyingObj.exists_gluing_of_underlying hR D hDobj hDmap A
    hflat hsurjective hlfp hsmooth (A.descended_torsor_isIso hR)

end ClassifyingObj.UnderlyingGluing

end AlgebraicGeometry.Scheme

