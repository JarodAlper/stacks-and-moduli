module

public import StacksAndModuli.«Section4.2-Representability».«part4.2.1-representability»
public import StacksAndModuli.API.DeligneMumfordDiagonal
public import StacksAndModuli.API.RepresentableWithSchemeModel
public import StacksAndModuli.API.UnramifiedQuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Stabilizer groups

This module formalizes `def:stabilizers` (Definition 4.2.5),
`exer:fiber-products-and-stabilizers` (Exercise 4.2.7) and
`exer:deligne-mumford-unramified-diagonal` (Exercise 4.2.8) of §4.2 (Representability of
the diagonal) of *Stacks and Moduli*,
subsection label `sec:stabilizers-and-inertia`
(first half).

The stabilizer of a point `x : S → 𝒳` of a prestack is realized pullback-free as the fiber
product of the diagonal `Δ : 𝒳 → 𝒳 × 𝒳` and the point `(x, x) : S → 𝒳 × 𝒳`; for an
algebraic stack `𝒳` and a field-valued point it is (representable by) an algebraic space.

Main book results:
- `CategoryTheory.BasedCategory.stabilizer`: the stabilizer of a point of a prestack;
- `AlgebraicGeometry.IsAlgebraicStack.exists_isAlgebraicSpace_stabilizer`: the stabilizer
  of a field-valued point of an algebraic stack is an algebraic space (`def:stabilizers`);
- the statements of `exer:fiber-products-and-stabilizers` (stabilizers of fiber products)
  and `exer:deligne-mumford-unramified-diagonal` (stabilizers of Deligne–Mumford stacks
  are separated étale, finite when quasi-compact; the diagonal is unramified).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefStabilizers

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- **Definition 4.2.5** (`def:stabilizers`) (prestack-level definition): the stabilizer
of a point `x : S → 𝒳` of a prestack `𝒳` over `𝒮` — the fiber product of the diagonal
`Δ : 𝒳 → 𝒳 × 𝒳` and the point `(x, x) : 𝒮/S → 𝒳 × 𝒳`. Its objects over `f : T → S` are
triples of an object `a` of `𝒳` over `T` and isomorphisms `a ≅ x(f) ≅ a` over identities;
over the identity of `S` these are the automorphisms of `x`. For an algebraic stack and a
field-valued point this is the stabilizer group of Definition 4.2.5; the group structure
is supplied on the slice by the `Aut` presheaf of Exercise 3.4.39. Transporting it to
the chosen small algebraic-space representative, and then to a scheme model, remains
separate — see the section's COMMENTARY.md. -/
abbrev stabilizer {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) :
    BasedCategory 𝒮 :=
  fiberProduct (diag 𝒳) (prodLift x x)

/-- The morphism of stabilizers induced by a morphism of prestacks: for `H : 𝒳 → 𝒴` and a
point `x : S → 𝒳`, the induced morphism `G_x → G_{H(x)}` sending an automorphism `α` of
`x` to `H(α)`. -/
abbrev stabilizerMap {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (H : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) :
    stabilizer x ⥤ᵇ stabilizer (x.comp H) :=
  fiberProductMap H (prodMap H H) (BasedFunctor.id (overBased S))
    (eqToIso (diag_comp_prodMap H).symm)
    (eqToIso (by rw [BasedFunctor.id_comp, prodLift_comp_prodMap]))

/-- The identity section of the stabilizer of a point `x : S → 𝒳` of a prestack: the
point of `G_x` over the identity of `S` given by the identity automorphism of `x`. -/
abbrev stabilizerUnit {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) :
    overBased S ⥤ᵇ stabilizer x :=
  fiberProductLift x (BasedFunctor.id (overBased S))
    (eqToIso (by rw [comp_diag, BasedFunctor.id_comp]))

/-- 2-isomorphic points of a prestack have canonically isomorphic stabilizers: a
2-isomorphism `η : x ≅ y` of points `S → 𝒳` induces a morphism (in fact an equivalence)
`G_x → G_y`, conjugation by `η`. -/
def stabilizerCongr {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} {x y : overBased S ⥤ᵇ 𝒳}
    (η : x ≅ y) : stabilizer x ⥤ᵇ stabilizer y :=
  fiberProductMap (BasedFunctor.id 𝒳) (BasedFunctor.id (prod 𝒳 𝒳))
    (BasedFunctor.id (overBased S))
    (eqToIso (by rw [BasedFunctor.id_comp, BasedFunctor.comp_id]))
    (prodLiftIso η.symm η.symm)

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.BasedCategory

/-- **Definition 4.2.5** (`def:stabilizers`) (the stabilizer is an algebraic space): let
`𝒳` be an algebraic stack and let `x : Spec K → 𝒳` be a field-valued point. Then the
stabilizer `G_x = Aut_{𝒳(K)}(x)`, realized as the fiber product of the diagonal
`Δ : 𝒳 → 𝒳 × 𝒳` and `(x, x) : Spec K → 𝒳 × 𝒳`, is (represented by) an algebraic space.
(The group structure of `G_x` — multiplication, inverse and identity as in
the group-scheme definition — exists on the slice as `BasedCategory.autPresheaf`; this
declaration records only the underlying algebraic-space representation.) -/
theorem IsAlgebraicStack.exists_isAlgebraicSpace_stabilizer
    (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack 𝒳]
    {K : Type u} [Field K] (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) :
    ∃ G : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace G ∧
      (BasedCategory.stabilizer x).IsRepresentedByPresheaf G :=
  IsAlgebraicStack.representable_diag 𝒳 _ (prodLift x x)

/- Deferred obligations from Definition 4.2.5 and the surrounding discussion:
- The description of `G_x` as the group `\uAut_{𝒳(K)}(x)` of automorphisms is
  formalized on the slice by `BasedCategory.autPresheaf`. Packaging the shrunken total
  presheaf used for the algebraic-space representation as a group object, and transporting
  that group object through a scheme representation, is not yet part of the API.
- `cor:stabilizers-are-group-schemes` (§5.5): `G_x` is a group *scheme* locally of finite
  type when the diagonal of `𝒳` is quasi-separated; forward reference, not formalized
  here.
- The unlabeled remark following `def:stabilizers`: for a group scheme `G` acting on `U`
  via `σ : G × U → U` and `u ∈ U(K)`, the stabilizer of the image of `u` in the quotient
  stack `[U/G]` is the fiber product of `(σ, p₂) : G × U → U × U` and
  `(u, u) : Spec K → U × U`. Quotient stacks `[U/G]` are themselves unformalized (tracked
  in the STATUS.md files of §3.4/§3.5), so this remark is deferred with them. -/

end AlgebraicGeometry

end DefStabilizers

section ExerFiberProductsAndStabilizers

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}

/-- The first component of a stabilizer isomorphism is carried pointwise by the induced map. -/
lemma stabilizerMap_obj_iso_hom_fst {𝒜 : BasedCategory.{v₂, u₂} 𝒮}
    {ℬ : BasedCategory.{v₃, u₃} 𝒮} (H : 𝒜 ⥤ᵇ ℬ) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒜) (q : (stabilizer x).obj) :
    ((stabilizerMap H x).obj q).iso.hom.fst = H.map q.iso.hom.fst := by
  have auxHom {L R : 𝒜 ⥤ᵇ prod ℬ ℬ} (h : L = R) (z : 𝒜.obj) :
      ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso (eqToIso h)).app z).hom).fst =
        eqToHom (congrArg (fun K ↦ (K.obj z).fst) h) := by
    subst R
    rfl
  have auxInv {L R : overBased S ⥤ᵇ prod ℬ ℬ} (h : L = R)
      (z : (overBased S).obj) :
      ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
        (eqToIso h)).app z).inv).fst =
          eqToHom (congrArg (fun K ↦ (K.obj z).fst) h.symm) := by
    subst R
    rfl
  have hleft (z : 𝒜.obj) :
      ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso
        (eqToIso (diag_comp_prodMap H).symm)).app z).hom).fst = 𝟙 (H.obj z) := by
    rw [auxHom]
    have hp : congrArg (fun K ↦ (K.obj z).fst)
        (diag_comp_prodMap H).symm = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  let hprod : (BasedFunctor.id (overBased S)).comp
      (prodLift (x.comp H) (x.comp H)) = (prodLift x x).comp (prodMap H H) := by
    rw [BasedFunctor.id_comp, prodLift_comp_prodMap]
  have hright (z : (overBased S).obj) :
      ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
        (eqToIso hprod)).app z).inv).fst = 𝟙 (H.obj (x.obj z)) := by
    rw [auxInv]
    have hp : congrArg (fun K ↦ (K.obj z).fst) hprod.symm = rfl :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  dsimp [stabilizerMap, fiberProductMap, fiberProductLift,
    whiskerLeftIso, whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoFst]
  change
    ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso
      (eqToIso (diag_comp_prodMap H).symm)).app q.fst).hom).fst ≫
      H.map q.iso.hom.fst ≫
    ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
      (eqToIso hprod)).app q.snd).inv).fst = H.map q.iso.hom.fst
  rw [hleft, hright]
  let a : q.fst ⟶ x.obj q.snd := q.iso.hom.fst
  change 𝟙 (H.obj q.fst) ≫ (H.map a ≫ 𝟙 (H.obj (x.obj q.snd))) = H.map a
  simp

/-- The second component of a stabilizer isomorphism is carried pointwise by the induced map. -/
lemma stabilizerMap_obj_iso_hom_snd {𝒜 : BasedCategory.{v₂, u₂} 𝒮}
    {ℬ : BasedCategory.{v₃, u₃} 𝒮} (H : 𝒜 ⥤ᵇ ℬ) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒜) (q : (stabilizer x).obj) :
    ((stabilizerMap H x).obj q).iso.hom.snd = H.map q.iso.hom.snd := by
  have auxHom {L R : 𝒜 ⥤ᵇ prod ℬ ℬ} (h : L = R) (z : 𝒜.obj) :
      ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso (eqToIso h)).app z).hom).snd =
        eqToHom (congrArg (fun K ↦ (K.obj z).snd) h) := by
    subst R
    rfl
  have auxInv {L R : overBased S ⥤ᵇ prod ℬ ℬ} (h : L = R)
      (z : (overBased S).obj) :
      ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
        (eqToIso h)).app z).inv).snd =
          eqToHom (congrArg (fun K ↦ (K.obj z).snd) h.symm) := by
    subst R
    rfl
  have hleft (z : 𝒜.obj) :
      ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso
        (eqToIso (diag_comp_prodMap H).symm)).app z).hom).snd = 𝟙 (H.obj z) := by
    rw [auxHom]
    have hp : congrArg (fun K ↦ (K.obj z).snd)
        (diag_comp_prodMap H).symm = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  let hprod : (BasedFunctor.id (overBased S)).comp
      (prodLift (x.comp H) (x.comp H)) = (prodLift x x).comp (prodMap H H) := by
    rw [BasedFunctor.id_comp, prodLift_comp_prodMap]
  have hright (z : (overBased S).obj) :
      ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
        (eqToIso hprod)).app z).inv).snd = 𝟙 (H.obj (x.obj z)) := by
    rw [auxInv]
    have hp : congrArg (fun K ↦ (K.obj z).snd) hprod.symm = rfl :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  dsimp [stabilizerMap, fiberProductMap, fiberProductLift,
    whiskerLeftIso, whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoSnd]
  change
    ((((BasedNatTrans.forgetful 𝒜 (prod ℬ ℬ)).mapIso
      (eqToIso (diag_comp_prodMap H).symm)).app q.fst).hom).snd ≫
      H.map q.iso.hom.snd ≫
    ((((BasedNatTrans.forgetful (overBased S) (prod ℬ ℬ)).mapIso
      (eqToIso hprod)).app q.snd).inv).snd = H.map q.iso.hom.snd
  rw [hleft, hright]
  let a : q.fst ⟶ x.obj q.snd := q.iso.hom.snd
  change 𝟙 (H.obj q.fst) ≫ (H.map a ≫ 𝟙 (H.obj (x.obj q.snd))) = H.map a
  simp

/-- Conjugating a point appends the point isomorphism to the first stabilizer component. -/
lemma stabilizerCongr_obj_iso_hom_fst {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮}
    {x y : overBased S ⥤ᵇ 𝒜} (η : x ≅ y) (q : (stabilizer x).obj) :
    ((stabilizerCongr η).obj q).iso.hom.fst =
      q.iso.hom.fst ≫ η.hom.toNatTrans.app q.snd := by
  let h : q.fst ⟶ x.obj q.snd := q.iso.hom.fst
  let e : x.obj q.snd ⟶ y.obj q.snd := η.hom.toNatTrans.app q.snd
  dsimp [stabilizerCongr, fiberProductMap, fiberProductLift,
    whiskerLeftIso, whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoFst]
  have hid : ((BasedNatTrans.id (diag 𝒜)).app q.fst).fst = 𝟙 q.fst := rfl
  have hmap : ((BasedFunctor.id (prod 𝒜 𝒜)).map
      ((fiberProductIsoComm (diag 𝒜) (prodLift x x)).hom.app q)).fst = h := rfl
  have heta : ((prodLiftIso η.symm η.symm).inv.toNatTrans.app q.snd).fst = e := rfl
  have halg : 𝟙 q.fst ≫ (h ≫ e) = h ≫ e := by simp
  simpa only [hid, hmap, heta, h, e] using halg

/-- Conjugating a point appends the point isomorphism to the second stabilizer component. -/
lemma stabilizerCongr_obj_iso_hom_snd {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮}
    {x y : overBased S ⥤ᵇ 𝒜} (η : x ≅ y) (q : (stabilizer x).obj) :
    ((stabilizerCongr η).obj q).iso.hom.snd =
      q.iso.hom.snd ≫ η.hom.toNatTrans.app q.snd := by
  let h : q.fst ⟶ x.obj q.snd := q.iso.hom.snd
  let e : x.obj q.snd ⟶ y.obj q.snd := η.hom.toNatTrans.app q.snd
  dsimp [stabilizerCongr, fiberProductMap, fiberProductLift,
    whiskerLeftIso, whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoSnd]
  have hid : ((BasedNatTrans.id (diag 𝒜)).app q.fst).snd = 𝟙 q.fst := rfl
  have hmap : ((BasedFunctor.id (prod 𝒜 𝒜)).map
      ((fiberProductIsoComm (diag 𝒜) (prodLift x x)).hom.app q)).snd = h := rfl
  have heta : ((prodLiftIso η.symm η.symm).inv.toNatTrans.app q.snd).snd = e := rfl
  have halg : 𝟙 q.fst ≫ (h ≫ e) = h ≫ e := by simp
  simpa only [hid, hmap, heta, h, e] using halg

/-- The image in the middle stabilizer obtained through the first projection of a fiber product. -/
def stabilizerFiberProductLeft (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    stabilizer x' ⥤ᵇ stabilizer
      ((x'.comp (fiberProductFst F G)).comp F) :=
  (stabilizerMap (fiberProductFst F G) x').comp
    (stabilizerMap F (x'.comp (fiberProductFst F G)))

/-- The image in the middle stabilizer obtained through the second projection and conjugation. -/
def stabilizerFiberProductRight (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    stabilizer x' ⥤ᵇ stabilizer
      ((x'.comp (fiberProductFst F G)).comp F) :=
  ((stabilizerMap (fiberProductSnd F G) x').comp
    (stabilizerMap G (x'.comp (fiberProductSnd F G)))).comp
      (stabilizerCongr ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))

/-- Normal form for the first isomorphism component along the first projection. -/
lemma stabilizerFiberProductLeft_obj_iso_hom_fst
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) (q : (stabilizer x').obj) :
    ((stabilizerFiberProductLeft F G x').obj q).iso.hom.fst =
      F.map q.iso.hom.fst.fst := by
  change ((stabilizerMap F (x'.comp (fiberProductFst F G))).obj
    ((stabilizerMap (fiberProductFst F G) x').obj q)).iso.hom.fst = _
  rw [stabilizerMap_obj_iso_hom_fst, stabilizerMap_obj_iso_hom_fst]
  rfl

/-- Normal form for the second isomorphism component along the first projection. -/
lemma stabilizerFiberProductLeft_obj_iso_hom_snd
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) (q : (stabilizer x').obj) :
    ((stabilizerFiberProductLeft F G x').obj q).iso.hom.snd =
      F.map q.iso.hom.snd.fst := by
  change ((stabilizerMap F (x'.comp (fiberProductFst F G))).obj
    ((stabilizerMap (fiberProductFst F G) x').obj q)).iso.hom.snd = _
  rw [stabilizerMap_obj_iso_hom_snd, stabilizerMap_obj_iso_hom_snd]
  rfl

/-- Normal form for the first isomorphism component along the second projection. -/
lemma stabilizerFiberProductRight_obj_iso_hom_fst
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) (q : (stabilizer x').obj) :
    ((stabilizerFiberProductRight F G x').obj q).iso.hom.fst =
      G.map q.iso.hom.fst.snd ≫ (x'.obj q.snd).iso.inv := by
  change ((stabilizerCongr
      ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm)).obj
    ((stabilizerMap G (x'.comp (fiberProductSnd F G))).obj
      ((stabilizerMap (fiberProductSnd F G) x').obj q))).iso.hom.fst = _
  rw [stabilizerCongr_obj_iso_hom_fst,
    stabilizerMap_obj_iso_hom_fst, stabilizerMap_obj_iso_hom_fst]
  rfl

/-- Normal form for the second isomorphism component along the second projection. -/
lemma stabilizerFiberProductRight_obj_iso_hom_snd
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) (q : (stabilizer x').obj) :
    ((stabilizerFiberProductRight F G x').obj q).iso.hom.snd =
      G.map q.iso.hom.snd.snd ≫ (x'.obj q.snd).iso.inv := by
  change ((stabilizerCongr
      ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm)).obj
    ((stabilizerMap G (x'.comp (fiberProductSnd F G))).obj
      ((stabilizerMap (fiberProductSnd F G) x').obj q))).iso.hom.snd = _
  rw [stabilizerCongr_obj_iso_hom_snd,
    stabilizerMap_obj_iso_hom_snd, stabilizerMap_obj_iso_hom_snd]
  rfl

/-- Normal form for the first component of the conjugated right leg. -/
lemma stabilizerFiberProductRightLeg_obj_iso_hom_fst
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G)
    (q : (stabilizer (x'.comp (fiberProductSnd F G))).obj) :
    ((((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
      (stabilizerCongr
        ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))).obj q).iso.hom.fst) =
      G.map q.iso.hom.fst ≫ (x'.obj q.snd).iso.inv := by
  change ((stabilizerCongr
      ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm)).obj
    ((stabilizerMap G (x'.comp (fiberProductSnd F G))).obj q)).iso.hom.fst = _
  rw [stabilizerCongr_obj_iso_hom_fst, stabilizerMap_obj_iso_hom_fst]
  rfl

/-- Normal form for the second component of the conjugated right leg. -/
lemma stabilizerFiberProductRightLeg_obj_iso_hom_snd
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G)
    (q : (stabilizer (x'.comp (fiberProductSnd F G))).obj) :
    ((((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
      (stabilizerCongr
        ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))).obj q).iso.hom.snd) =
      G.map q.iso.hom.snd ≫ (x'.obj q.snd).iso.inv := by
  change ((stabilizerCongr
      ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm)).obj
    ((stabilizerMap G (x'.comp (fiberProductSnd F G))).obj q)).iso.hom.snd = _
  rw [stabilizerCongr_obj_iso_hom_snd, stabilizerMap_obj_iso_hom_snd]
  rfl

/-- The objectwise compatibility isomorphism between the two maps to the middle stabilizer. -/
def stabilizerFiberProductIsoApp (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) (q : (stabilizer x').obj) :
    (stabilizerFiberProductLeft F G x').obj q ≅
      (stabilizerFiberProductRight F G x').obj q := by
  apply FiberProductObj.isoMk (a := (stabilizerFiberProductLeft F G x').obj q)
    (b := (stabilizerFiberProductRight F G x').obj q) q.fst.iso (Iso.refl q.snd)
  · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj q.fst.fst))
      q.fst.iso.hom (𝟙 q.snd) q.fst.isHomLift (IsHomLift.id q.over_eq)
  · apply FiberProductHom.ext
    · let h : q.fst ⟶ x'.obj q.snd := q.iso.hom.fst
      let γq : F.obj q.fst.fst ≅ G.obj q.fst.snd := q.fst.iso
      let γs : F.obj (x'.obj q.snd).fst ≅ G.obj (x'.obj q.snd).snd :=
        (x'.obj q.snd).iso
      have hw : F.map h.fst ≫ γs.hom = γq.hom ≫ G.map h.snd := h.w
      have halg₀ : γq.hom ≫ (G.map h.snd ≫ γs.inv) = F.map h.fst := by
        rw [← Category.assoc, ← hw, Category.assoc, γs.hom_inv_id, Category.comp_id]
      have halg : γq.hom ≫ (G.map h.snd ≫ γs.inv) =
          F.map h.fst ≫ 𝟙 (((x'.comp (fiberProductFst F G)).comp F).obj q.snd) :=
        halg₀.trans (Category.comp_id _).symm
      change q.fst.iso.hom ≫
          ((stabilizerFiberProductRight F G x').obj q).iso.hom.fst =
        ((stabilizerFiberProductLeft F G x').obj q).iso.hom.fst ≫
          (((x'.comp (fiberProductFst F G)).comp F).map (𝟙 q.snd))
      have hp : ((x'.comp (fiberProductFst F G)).comp F).map (𝟙 q.snd) =
          𝟙 (((x'.comp (fiberProductFst F G)).comp F).obj q.snd) :=
        ((x'.comp (fiberProductFst F G)).comp F).toFunctor.map_id q.snd
      rw [hp]
      simpa only [stabilizerFiberProductLeft_obj_iso_hom_fst,
        stabilizerFiberProductRight_obj_iso_hom_fst,
        h, γq, γs] using halg
    · let h : q.fst ⟶ x'.obj q.snd := q.iso.hom.snd
      let γq : F.obj q.fst.fst ≅ G.obj q.fst.snd := q.fst.iso
      let γs : F.obj (x'.obj q.snd).fst ≅ G.obj (x'.obj q.snd).snd :=
        (x'.obj q.snd).iso
      have hw : F.map h.fst ≫ γs.hom = γq.hom ≫ G.map h.snd := h.w
      have halg₀ : γq.hom ≫ (G.map h.snd ≫ γs.inv) = F.map h.fst := by
        rw [← Category.assoc, ← hw, Category.assoc, γs.hom_inv_id, Category.comp_id]
      have halg : γq.hom ≫ (G.map h.snd ≫ γs.inv) =
          F.map h.fst ≫ 𝟙 (((x'.comp (fiberProductFst F G)).comp F).obj q.snd) :=
        halg₀.trans (Category.comp_id _).symm
      change q.fst.iso.hom ≫
          ((stabilizerFiberProductRight F G x').obj q).iso.hom.snd =
        ((stabilizerFiberProductLeft F G x').obj q).iso.hom.snd ≫
          (((x'.comp (fiberProductFst F G)).comp F).map (𝟙 q.snd))
      have hp : ((x'.comp (fiberProductFst F G)).comp F).map (𝟙 q.snd) =
          𝟙 (((x'.comp (fiberProductFst F G)).comp F).obj q.snd) :=
        ((x'.comp (fiberProductFst F G)).comp F).toFunctor.map_id q.snd
      rw [hp]
      simpa only [stabilizerFiberProductLeft_obj_iso_hom_snd,
        stabilizerFiberProductRight_obj_iso_hom_snd,
        h, γq, γs] using halg

/-- The natural compatibility isomorphism between the two maps to the middle stabilizer. -/
def stabilizerFiberProductIso (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    stabilizerFiberProductLeft F G x' ≅ stabilizerFiberProductRight F G x' :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (stabilizerFiberProductIsoApp F G x')
      (fun {q r} φ ↦ by
        apply FiberProductHom.ext
        · change F.map φ.fst.fst ≫ r.fst.iso.hom =
            q.fst.iso.hom ≫ G.map φ.fst.snd
          exact φ.fst.w
        · change φ.snd ≫ 𝟙 r.snd = 𝟙 q.snd ≫ φ.snd
          simp))
    (fun q ↦ by
      exact FiberProductHom.isHomLift_of_fst
        (stabilizerFiberProductIsoApp F G x' q).hom
        (𝟙 (𝒳.p.obj q.fst.fst)) q.fst.isHomLift)

/-- The canonical comparison from the stabilizer of a fiber-product point to the fiber
product of stabilizers. -/
def stabilizerFiberProductComparison (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    stabilizer x' ⥤ᵇ
      fiberProduct (stabilizerMap F (x'.comp (fiberProductFst F G)))
        ((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
          (stabilizerCongr ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))) :=
  fiberProductLift (stabilizerMap (fiberProductFst F G) x')
    (stabilizerMap (fiberProductSnd F G) x')
    (stabilizerFiberProductIso F G x')

/-- The stabilizer fiber-product comparison is faithful. -/
lemma stabilizerFiberProductComparison_faithful
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    (stabilizerFiberProductComparison F G x').toFunctor.Faithful := by
  constructor
  intro q r φ ψ h
  apply FiberProductHom.ext
  · apply FiberProductHom.ext
    · exact congrArg (fun k ↦ k.fst.fst) h
    · exact congrArg (fun k ↦ k.snd.fst) h
  · exact congrArg (fun k ↦ k.fst.snd) h

/-- The stabilizer fiber-product comparison is full. -/
lemma stabilizerFiberProductComparison_full
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    (stabilizerFiberProductComparison F G x').toFunctor.Full := by
  constructor
  intro q r k
  have hs₀ := congrArg FiberProductHom.snd k.w
  have hs : k.fst.snd = k.snd.snd := by
    change k.fst.snd ≫ 𝟙 r.snd = 𝟙 q.snd ≫ k.snd.snd at hs₀
    have hs₁ : k.fst.snd ≫ 𝟙 r.snd = k.snd.snd := by
      simpa only [Category.id_comp] using hs₀
    exact (Category.comp_id _).symm.trans hs₁
  let φfst : q.fst ⟶ r.fst :=
    { fst := k.fst.fst
      snd := k.snd.fst
      isHomLift := by
        exact FiberProductHom.isHomLift_fst k.snd (𝒳.p.map k.fst.fst) k.isHomLift
      w := by
        have hw := congrArg FiberProductHom.fst k.w
        change F.map k.fst.fst ≫ r.fst.iso.hom =
          q.fst.iso.hom ≫ G.map k.snd.fst at hw
        exact hw }
  let φ : q ⟶ r :=
    { fst := φfst
      snd := k.fst.snd
      isHomLift := k.fst.isHomLift
      w := by
        dsimp [φfst]
        apply FiberProductHom.ext
        · apply FiberProductHom.ext
          · simpa only [FiberProductObj.comp_fst, diag_map_fst,
              fiberProductLift_map_fst, stabilizerMap_obj_iso_hom_fst,
              stabilizerFiberProductComparison, BasedFunctor.comp,
              BasedFunctor.id, fiberProductLift,
              fiberProductFst_map, Functor.id_map, Functor.comp_map] using
              congrArg FiberProductHom.fst k.fst.w
          · have hw := congrArg FiberProductHom.fst k.snd.w
            rw [← hs] at hw
            simpa only [FiberProductObj.comp_fst, FiberProductObj.comp_snd, diag_map_fst,
              fiberProductLift_map_fst, stabilizerMap_obj_iso_hom_fst,
              stabilizerFiberProductComparison, BasedFunctor.comp,
              BasedFunctor.id, fiberProductLift,
              fiberProductSnd_map, Functor.id_map, Functor.comp_map] using hw
        · apply FiberProductHom.ext
          · simpa only [FiberProductObj.comp_snd, FiberProductObj.comp_fst, diag_map_snd,
              fiberProductLift_map_snd, stabilizerMap_obj_iso_hom_snd,
              stabilizerFiberProductComparison, BasedFunctor.comp,
              BasedFunctor.id, fiberProductLift,
              fiberProductFst_map, Functor.id_map, Functor.comp_map] using
              congrArg FiberProductHom.snd k.fst.w
          · have hw := congrArg FiberProductHom.snd k.snd.w
            rw [← hs] at hw
            simpa only [FiberProductObj.comp_snd, diag_map_snd,
              fiberProductLift_map_snd, stabilizerMap_obj_iso_hom_snd,
              stabilizerFiberProductComparison, BasedFunctor.comp,
              BasedFunctor.id, fiberProductLift,
              fiberProductSnd_map, Functor.id_map, Functor.comp_map] using hw }
  refine ⟨φ, ?_⟩
  apply FiberProductHom.ext
  · apply FiberProductHom.ext <;> rfl
  · apply FiberProductHom.ext
    · rfl
    · exact hs

/-- The stabilizer fiber-product comparison is essentially surjective. -/
lemma stabilizerFiberProductComparison_essSurj
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    (stabilizerFiberProductComparison F G x').toFunctor.EssSurj := by
  constructor
  intro t
  let δ : F.obj t.fst.fst ≅ G.obj t.snd.fst := FiberProductObj.isoFst t.iso
  let σ : t.fst.snd ≅ t.snd.snd := FiberProductObj.isoSnd t.iso
  let xσ : x'.obj t.fst.snd ≅ x'.obj t.snd.snd := x'.toFunctor.mapIso σ
  let xσ₂ : (x'.obj t.fst.snd).snd ≅ (x'.obj t.snd.snd).snd :=
    FiberProductObj.isoSnd xσ
  let z : (fiberProduct F G).obj :=
    { fst := t.fst.fst
      snd := t.snd.fst
      over_eq := t.over_eq
      iso := δ
      isHomLift := by
        exact FiberProductHom.isHomLift_fst t.iso.hom
          (𝟙 (𝒳.p.obj t.fst.fst)) t.isHomLift }
  let a₁ : t.fst.fst ≅ (x'.obj t.fst.snd).fst :=
    FiberProductObj.isoFst t.fst.iso
  let a₂ : t.fst.fst ≅ (x'.obj t.fst.snd).fst :=
    FiberProductObj.isoSnd t.fst.iso
  let b₁ : t.snd.fst ≅ (x'.obj t.snd.snd).snd :=
    FiberProductObj.isoFst t.snd.iso
  let b₂ : t.snd.fst ≅ (x'.obj t.snd.snd).snd :=
    FiberProductObj.isoSnd t.snd.iso
  let c₁ : t.snd.fst ≅ (x'.obj t.fst.snd).snd := b₁ ≪≫ xσ₂.symm
  let c₂ : t.snd.fst ≅ (x'.obj t.fst.snd).snd := b₂ ≪≫ xσ₂.symm
  let e₁ : z ≅ x'.obj t.fst.snd := by
    apply FiberProductObj.isoMk a₁ c₁
    · have ha : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) a₁.hom :=
        FiberProductHom.isHomLift_fst t.fst.iso.hom _ t.fst.isHomLift
      have hb : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) b₁.hom := by
        have hb' := FiberProductHom.isHomLift_fst t.snd.iso.hom _ t.snd.isHomLift
        rw [t.over_eq] at hb'
        exact hb'
      have hσi : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) xσ₂.inv := by
        have htHom : IsHomLift
            (stabilizer ((x'.comp (fiberProductFst F G)).comp F)).p
            (𝟙 (𝒳.p.obj t.fst.fst)) t.iso.hom := t.isHomLift
        let _ := htHom
        have htInv : IsHomLift
            (stabilizer ((x'.comp (fiberProductFst F G)).comp F)).p
            (𝟙 (𝒳.p.obj t.fst.fst)) t.iso.inv :=
          IsHomLift.lift_id_inv _ (𝒳.p.obj t.fst.fst) t.iso
        have hσi' : IsHomLift (overBased S).p
            (𝟙 (𝒳.p.obj t.fst.fst)) σ.inv :=
          FiberProductHom.isHomLift_snd t.iso.inv _ htInv
        have hxσi : IsHomLift (fiberProduct F G).p
            (𝟙 (𝒳.p.obj t.fst.fst)) xσ.inv :=
          x'.preserves_isHomLift _ _
        exact FiberProductHom.isHomLift_snd xσ.inv _ hxσi
      have hc : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) c₁.hom :=
        isHomLift_id_comp 𝒴'.p _ _ hb hσi
      exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        a₁.hom c₁.hom ha hc
    · change F.map t.fst.iso.hom.fst ≫ (x'.obj t.fst.snd).iso.hom =
        t.iso.hom.fst ≫ G.map (t.snd.iso.hom.fst ≫ xσ₂.inv)
      let γ₁ : F.obj (x'.obj t.fst.snd).fst ≅ G.obj (x'.obj t.fst.snd).snd :=
        (x'.obj t.fst.snd).iso
      let γ₂ : F.obj (x'.obj t.snd.snd).fst ≅ G.obj (x'.obj t.snd.snd).snd :=
        (x'.obj t.snd.snd).iso
      have hout₀ := congrArg FiberProductHom.fst t.iso.hom.w
      have hright :
          ((((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
            (stabilizerCongr
              ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))).obj
                t.snd).iso.hom.fst) =
            G.map t.snd.iso.hom.fst ≫ (x'.obj t.snd.snd).iso.inv := by
        exact stabilizerFiberProductRightLeg_obj_iso_hom_fst F G x' t.snd
      have hpoint : (((x'.comp (fiberProductFst F G)).comp F).map
          t.iso.hom.snd) = F.map xσ.hom.fst := by
        rfl
      have hid : (BasedFunctor.id 𝒴).map t.iso.hom.fst = t.iso.hom.fst := rfl
      have hout : t.iso.hom.fst ≫
          (G.map t.snd.iso.hom.fst ≫ γ₂.inv) =
          F.map t.fst.iso.hom.fst ≫ F.map xσ.hom.fst := by
        simpa only [FiberProductObj.comp_fst, diag_map_fst,
          hright, stabilizerMap_obj_iso_hom_fst,
          fiberProductLift_map_fst, hpoint, hid] using hout₀
      have hnat : F.map xσ.hom.fst ≫ γ₂.hom =
          γ₁.hom ≫ G.map xσ₂.hom := xσ.hom.w
      have hδb : t.iso.hom.fst ≫ G.map t.snd.iso.hom.fst =
          (F.map t.fst.iso.hom.fst ≫ F.map xσ.hom.fst) ≫ γ₂.hom := by
        haveI : IsIso γ₂.inv := by infer_instance
        rw [← cancel_mono γ₂.inv]
        simpa only [Category.assoc, γ₂.hom_inv_id, Category.comp_id] using hout
      have hcmap : G.map (t.snd.iso.hom.fst ≫ xσ₂.inv) ≫ G.map xσ₂.hom =
          G.map t.snd.iso.hom.fst := by
        have hInv : (G.toFunctor.mapIso xσ₂).inv = G.map xσ₂.inv := rfl
        have hHom : (G.toFunctor.mapIso xσ₂).hom = G.map xσ₂.hom := rfl
        have hcmap₀ :
            (G.map t.snd.iso.hom.fst ≫ (G.toFunctor.mapIso xσ₂).inv) ≫
              (G.toFunctor.mapIso xσ₂).hom = G.map t.snd.iso.hom.fst :=
          (Category.assoc _ _ _).trans
            ((congrArg (fun u ↦ G.map t.snd.iso.hom.fst ≫ u)
              (G.toFunctor.mapIso xσ₂).inv_hom_id).trans (Category.comp_id _))
        simpa only [G.toFunctor.map_comp, hInv, hHom] using hcmap₀
      have hl : (F.map t.fst.iso.hom.fst ≫ γ₁.hom) ≫ G.map xσ₂.hom =
          (F.map t.fst.iso.hom.fst ≫ F.map xσ.hom.fst) ≫ γ₂.hom := by
        simp only [Category.assoc, ← hnat]
      have hr : (t.iso.hom.fst ≫
          G.map (t.snd.iso.hom.fst ≫ xσ₂.inv)) ≫ G.map xσ₂.hom =
          t.iso.hom.fst ≫ G.map t.snd.iso.hom.fst := by
        simp only [Category.assoc, hcmap]
      haveI : IsIso (G.map xσ₂.hom) := by infer_instance
      rw [← cancel_mono (G.map xσ₂.hom)]
      exact hl.trans (hδb.symm.trans hr.symm)
  let e₂ : z ≅ x'.obj t.fst.snd := by
    apply FiberProductObj.isoMk a₂ c₂
    · have ha : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) a₂.hom :=
        FiberProductHom.isHomLift_snd t.fst.iso.hom _ t.fst.isHomLift
      have hb : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) b₂.hom := by
        have hb' := FiberProductHom.isHomLift_snd t.snd.iso.hom _ t.snd.isHomLift
        rw [t.over_eq] at hb'
        exact hb'
      have hσi : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) xσ₂.inv := by
        have htHom : IsHomLift
            (stabilizer ((x'.comp (fiberProductFst F G)).comp F)).p
            (𝟙 (𝒳.p.obj t.fst.fst)) t.iso.hom := t.isHomLift
        let _ := htHom
        have htInv : IsHomLift
            (stabilizer ((x'.comp (fiberProductFst F G)).comp F)).p
            (𝟙 (𝒳.p.obj t.fst.fst)) t.iso.inv :=
          IsHomLift.lift_id_inv _ (𝒳.p.obj t.fst.fst) t.iso
        have hσi' : IsHomLift (overBased S).p
            (𝟙 (𝒳.p.obj t.fst.fst)) σ.inv :=
          FiberProductHom.isHomLift_snd t.iso.inv _ htInv
        have hxσi : IsHomLift (fiberProduct F G).p
            (𝟙 (𝒳.p.obj t.fst.fst)) xσ.inv :=
          x'.preserves_isHomLift _ _
        exact FiberProductHom.isHomLift_snd xσ.inv _ hxσi
      have hc : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj t.fst.fst)) c₂.hom :=
        isHomLift_id_comp 𝒴'.p _ _ hb hσi
      exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        a₂.hom c₂.hom ha hc
    · change F.map t.fst.iso.hom.snd ≫ (x'.obj t.fst.snd).iso.hom =
        t.iso.hom.fst ≫ G.map (t.snd.iso.hom.snd ≫ xσ₂.inv)
      let γ₁ : F.obj (x'.obj t.fst.snd).fst ≅ G.obj (x'.obj t.fst.snd).snd :=
        (x'.obj t.fst.snd).iso
      let γ₂ : F.obj (x'.obj t.snd.snd).fst ≅ G.obj (x'.obj t.snd.snd).snd :=
        (x'.obj t.snd.snd).iso
      have hout₀ := congrArg FiberProductHom.snd t.iso.hom.w
      have hright :
          ((((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
            (stabilizerCongr
              ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))).obj
                t.snd).iso.hom.snd) =
            G.map t.snd.iso.hom.snd ≫ (x'.obj t.snd.snd).iso.inv := by
        exact stabilizerFiberProductRightLeg_obj_iso_hom_snd F G x' t.snd
      have hpoint : (((x'.comp (fiberProductFst F G)).comp F).map
          t.iso.hom.snd) = F.map xσ.hom.fst := by
        rfl
      have hid : (BasedFunctor.id 𝒴).map t.iso.hom.fst = t.iso.hom.fst := rfl
      have hout : t.iso.hom.fst ≫
          (G.map t.snd.iso.hom.snd ≫ γ₂.inv) =
          F.map t.fst.iso.hom.snd ≫ F.map xσ.hom.fst := by
        simpa only [FiberProductObj.comp_snd, diag_map_snd,
          hright, stabilizerMap_obj_iso_hom_snd,
          fiberProductLift_map_snd, hpoint, hid] using hout₀
      have hnat : F.map xσ.hom.fst ≫ γ₂.hom =
          γ₁.hom ≫ G.map xσ₂.hom := xσ.hom.w
      have hδb : t.iso.hom.fst ≫ G.map t.snd.iso.hom.snd =
          (F.map t.fst.iso.hom.snd ≫ F.map xσ.hom.fst) ≫ γ₂.hom := by
        haveI : IsIso γ₂.inv := by infer_instance
        rw [← cancel_mono γ₂.inv]
        simpa only [Category.assoc, γ₂.hom_inv_id, Category.comp_id] using hout
      have hcmap : G.map (t.snd.iso.hom.snd ≫ xσ₂.inv) ≫ G.map xσ₂.hom =
          G.map t.snd.iso.hom.snd := by
        have hInv : (G.toFunctor.mapIso xσ₂).inv = G.map xσ₂.inv := rfl
        have hHom : (G.toFunctor.mapIso xσ₂).hom = G.map xσ₂.hom := rfl
        have hcmap₀ :
            (G.map t.snd.iso.hom.snd ≫ (G.toFunctor.mapIso xσ₂).inv) ≫
              (G.toFunctor.mapIso xσ₂).hom = G.map t.snd.iso.hom.snd :=
          (Category.assoc _ _ _).trans
            ((congrArg (fun u ↦ G.map t.snd.iso.hom.snd ≫ u)
              (G.toFunctor.mapIso xσ₂).inv_hom_id).trans (Category.comp_id _))
        simpa only [G.toFunctor.map_comp, hInv, hHom] using hcmap₀
      have hl : (F.map t.fst.iso.hom.snd ≫ γ₁.hom) ≫ G.map xσ₂.hom =
          (F.map t.fst.iso.hom.snd ≫ F.map xσ.hom.fst) ≫ γ₂.hom := by
        simp only [Category.assoc, ← hnat]
      have hr : (t.iso.hom.fst ≫
          G.map (t.snd.iso.hom.snd ≫ xσ₂.inv)) ≫ G.map xσ₂.hom =
          t.iso.hom.fst ≫ G.map t.snd.iso.hom.snd := by
        simp only [Category.assoc, hcmap]
      haveI : IsIso (G.map xσ₂.hom) := by infer_instance
      rw [← cancel_mono (G.map xσ₂.hom)]
      exact hl.trans (hδb.symm.trans hr.symm)
  have he₁ : IsHomLift (fiberProduct F G).p
      (𝟙 (𝒳.p.obj t.fst.fst)) e₁.hom := by
    have ha : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) a₁.hom :=
      FiberProductHom.isHomLift_fst t.fst.iso.hom _ t.fst.isHomLift
    exact FiberProductHom.isHomLift_of_fst e₁.hom _ ha
  have he₂ : IsHomLift (fiberProduct F G).p
      (𝟙 (𝒳.p.obj t.fst.fst)) e₂.hom := by
    have ha : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) a₂.hom :=
      FiberProductHom.isHomLift_snd t.fst.iso.hom _ t.fst.isHomLift
    exact FiberProductHom.isHomLift_of_fst e₂.hom _ ha
  let qiso : ((fiberProduct F G).diag.obj z) ≅
      (prodLift x' x').obj t.fst.snd := by
    apply FiberProductObj.isoMk e₁ e₂
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        e₁.hom e₂.hom he₁ he₂
    · haveI h₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj t.fst.fst))
          ((fiberProduct F G).toBase.map e₁.hom) :=
        (fiberProduct F G).toBase.preserves_isHomLift _ _
      haveI h₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj t.fst.fst))
          ((fiberProduct F G).toBase.map e₂.hom) :=
        (fiberProduct F G).toBase.preserves_isHomLift _ _
      haveI hs : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj t.fst.fst))
          (((fiberProduct F G).diag.obj z).iso.hom) :=
        ((fiberProduct F G).diag.obj z).isHomLift
      haveI ht : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj t.fst.fst))
          (((prodLift x' x').obj t.fst.snd).iso.hom) := by
        have ht' := ((prodLift x' x').obj t.fst.snd).isHomLift
        change IsHomLift (base 𝒮).p
          (𝟙 ((fiberProduct F G).p.obj (x'.obj t.fst.snd)))
          (((prodLift x' x').obj t.fst.snd).iso.hom) at ht'
        rw [x'.w_obj, t.fst.over_eq] at ht'
        exact ht'
      haveI hl := base_isHomLift_comp (S := 𝒳.p.obj t.fst.fst)
        (T := 𝒳.p.obj t.fst.fst) ((fiberProduct F G).toBase.map e₁.hom)
        (((prodLift x' x').obj t.fst.snd).iso.hom)
      haveI hr := base_isHomLift_comp (S := 𝒳.p.obj t.fst.fst)
        (T := 𝒳.p.obj t.fst.fst) (((fiberProduct F G).diag.obj z).iso.hom)
        ((fiberProduct F G).toBase.map e₂.hom)
      exact base_hom_ext (S := 𝒳.p.obj t.fst.fst)
        (T := 𝒳.p.obj t.fst.fst) _ _
  let q : (stabilizer x').obj :=
    { fst := z
      snd := t.fst.snd
      over_eq := t.fst.over_eq
      iso := qiso
      isHomLift := FiberProductHom.isHomLift_of_fst qiso.hom
        (𝟙 (𝒳.p.obj t.fst.fst)) he₁ }
  refine ⟨q, ⟨?_⟩⟩
  let eX : (stabilizerMap (fiberProductFst F G) x').obj q ≅ t.fst := by
    apply FiberProductObj.isoMk
      (a := (stabilizerMap (fiberProductFst F G) x').obj q) (b := t.fst)
      (Iso.refl t.fst.fst) (Iso.refl t.fst.snd)
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        (𝟙 t.fst.fst) (𝟙 t.fst.snd) (IsHomLift.id rfl)
          (IsHomLift.id t.fst.over_eq)
    · have hsrc₁ :
          ((stabilizerMap (fiberProductFst F G) x').obj q).iso.hom.fst =
            t.fst.iso.hom.fst := by
        rw [stabilizerMap_obj_iso_hom_fst]
        rfl
      have hsrc₂ :
          ((stabilizerMap (fiberProductFst F G) x').obj q).iso.hom.snd =
            t.fst.iso.hom.snd := by
        rw [stabilizerMap_obj_iso_hom_snd]
        rfl
      have hp : (x'.comp (fiberProductFst F G)).map (𝟙 t.fst.snd) =
          𝟙 ((x'.comp (fiberProductFst F G)).obj t.fst.snd) :=
        (x'.comp (fiberProductFst F G)).toFunctor.map_id t.fst.snd
      apply FiberProductHom.ext
      · change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.fst =
          ((stabilizerMap (fiberProductFst F G) x').obj q).iso.hom.fst ≫
            (x'.comp (fiberProductFst F G)).map (𝟙 t.fst.snd)
        rw [hsrc₁, hp]
        exact (Category.id_comp t.fst.iso.hom.fst).trans
          (Category.comp_id t.fst.iso.hom.fst).symm
      · change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.snd =
          ((stabilizerMap (fiberProductFst F G) x').obj q).iso.hom.snd ≫
            (x'.comp (fiberProductFst F G)).map (𝟙 t.fst.snd)
        rw [hsrc₂, hp]
        exact (Category.id_comp t.fst.iso.hom.snd).trans
          (Category.comp_id t.fst.iso.hom.snd).symm
  let eY : (stabilizerMap (fiberProductSnd F G) x').obj q ≅ t.snd := by
    apply FiberProductObj.isoMk
      (a := (stabilizerMap (fiberProductSnd F G) x').obj q) (b := t.snd)
      (Iso.refl t.snd.fst) σ
    · have hσ : IsHomLift (overBased S).p
          (𝟙 (𝒳.p.obj t.fst.fst)) σ.hom :=
        FiberProductHom.isHomLift_snd t.iso.hom _ t.isHomLift
      exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        (𝟙 t.snd.fst) σ.hom (IsHomLift.id t.over_eq) hσ
    · have hsrc₁ :
          ((stabilizerMap (fiberProductSnd F G) x').obj q).iso.hom.fst = c₁.hom := by
        rw [stabilizerMap_obj_iso_hom_fst]
        rfl
      have hsrc₂ :
          ((stabilizerMap (fiberProductSnd F G) x').obj q).iso.hom.snd = c₂.hom := by
        rw [stabilizerMap_obj_iso_hom_snd]
        rfl
      have hp : (x'.comp (fiberProductSnd F G)).map σ.hom = xσ₂.hom := rfl
      have hc₁ : c₁.hom ≫ xσ₂.hom = b₁.hom := by
        change (b₁.hom ≫ xσ₂.inv) ≫ xσ₂.hom = b₁.hom
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun u ↦ b₁.hom ≫ u) xσ₂.inv_hom_id).trans
            (Category.comp_id _))
      have hc₂ : c₂.hom ≫ xσ₂.hom = b₂.hom := by
        change (b₂.hom ≫ xσ₂.inv) ≫ xσ₂.hom = b₂.hom
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun u ↦ b₂.hom ≫ u) xσ₂.inv_hom_id).trans
            (Category.comp_id _))
      apply FiberProductHom.ext
      · change (𝟙 t.snd.fst) ≫ t.snd.iso.hom.fst =
          ((stabilizerMap (fiberProductSnd F G) x').obj q).iso.hom.fst ≫
            (x'.comp (fiberProductSnd F G)).map σ.hom
        rw [hsrc₁, hp, hc₁]
        simp only [Category.id_comp]
        rfl
      · change (𝟙 t.snd.fst) ≫ t.snd.iso.hom.snd =
          ((stabilizerMap (fiberProductSnd F G) x').obj q).iso.hom.snd ≫
            (x'.comp (fiberProductSnd F G)).map σ.hom
        rw [hsrc₂, hp, hc₂]
        simp only [Category.id_comp]
        rfl
  apply FiberProductObj.isoMk (a := (stabilizerFiberProductComparison F G x').obj q)
    (b := t) eX eY
  · have heX : IsHomLift (stabilizer (x'.comp (fiberProductFst F G))).p
        (𝟙 (𝒳.p.obj t.fst.fst)) eX.hom := by
      exact FiberProductHom.isHomLift_of_fst eX.hom _ (IsHomLift.id rfl)
    have heY : IsHomLift (stabilizer (x'.comp (fiberProductSnd F G))).p
        (𝟙 (𝒳.p.obj t.fst.fst)) eY.hom := by
      exact FiberProductHom.isHomLift_of_fst eY.hom _ (IsHomLift.id t.over_eq)
    exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
      eX.hom eY.hom heX heY
  · apply FiberProductHom.ext
    · change F.map (𝟙 t.fst.fst) ≫ t.iso.hom.fst =
        t.iso.hom.fst ≫ G.map (𝟙 t.snd.fst)
      have hF : F.map (𝟙 t.fst.fst) = 𝟙 (F.obj t.fst.fst) :=
        F.toFunctor.map_id t.fst.fst
      have hG : G.map (𝟙 t.snd.fst) = 𝟙 (G.obj t.snd.fst) :=
        G.toFunctor.map_id t.snd.fst
      have halg : 𝟙 (F.obj t.fst.fst) ≫ t.iso.hom.fst =
          t.iso.hom.fst ≫ 𝟙 (G.obj t.snd.fst) :=
        (Category.id_comp _).trans (Category.comp_id _).symm
      simpa only [hF, hG] using halg
    · change (𝟙 t.fst.snd) ≫ t.iso.hom.snd =
        𝟙 t.fst.snd ≫ σ.hom
      rfl

/-- **Exercise 4.2.7** (`exer:fiber-products-and-stabilizers`) (part (a), stabilizers of
fiber products): let `F : 𝒳 → 𝒴` and `G : 𝒴' → 𝒴` be morphisms of prestacks over `𝒮` and
let `x'` be a point of the fiber product `𝒳 ×_𝒴 𝒴'` over `S`, with images `x` in `𝒳` and
`y'` in `𝒴'` and the canonical 2-isomorphism `G(y') ≅ F(x)` over `S`. Then the stabilizer
of `x'` is the fiber product `G_x ×_{G_{F(x)}} G_{y'}` of the induced morphisms of
stabilizers. -/
theorem exists_equivalence_stabilizer_fiberProduct (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {S : 𝒮}
    (x' : overBased S ⥤ᵇ fiberProduct F G) :
    ∃ E : stabilizer x' ⥤ᵇ
      fiberProduct (stabilizerMap F (x'.comp (fiberProductFst F G)))
        ((stabilizerMap G (x'.comp (fiberProductSnd F G))).comp
          (stabilizerCongr ((whiskerLeftIso x' (fiberProductIsoComm F G)).symm))),
      E.toFunctor.IsEquivalence := by
  refine ⟨stabilizerFiberProductComparison F G x', ?_⟩
  let _ := stabilizerFiberProductComparison_faithful F G x'
  let _ := stabilizerFiberProductComparison_full F G x'
  let _ := stabilizerFiberProductComparison_essSurj F G x'
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- The stabilizer-kernel datum canonically associated to an object of a relative-diagonal
fiber. -/
def stabilizerKernelComparisonObj (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (fiberProduct (stabilizerMap F x) (stabilizerUnit (x.comp F))).obj := by
  let a₁ := FiberProductObj.isoFst q.iso
  let a₂ := FiberProductObj.isoSnd q.iso
  have ha₁hom : a₁.hom = q.iso.hom.fst := rfl
  have ha₂hom : a₂.hom = q.iso.hom.snd := rfl
  have ha₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst)) a₁.hom := by
    exact FiberProductHom.isHomLift_fst q.iso.hom _ q.isHomLift
  have ha₂ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst)) a₂.hom := by
    exact FiberProductHom.isHomLift_snd q.iso.hom _ q.isHomLift
  let beta : (diag 𝒳).obj q.fst ≅ (prodLift x x).obj q.snd := by
    apply FiberProductObj.isoMk (F := 𝒳.toBase) (G := 𝒳.toBase) a₁ a₂
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj q.fst))
        a₁.hom a₂.hom
        ha₁ ha₂
    · haveI h₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst))
          (𝒳.toBase.map a₁.hom) := by
        let _ := ha₁
        exact 𝒳.toBase.preserves_isHomLift _ _
      haveI h₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst))
          (𝒳.toBase.map a₂.hom) := by
        let _ := ha₂
        exact 𝒳.toBase.preserves_isHomLift _ _
      haveI hs : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst))
          (((diag 𝒳).obj q.fst).iso.hom) := ((diag 𝒳).obj q.fst).isHomLift
      haveI ht : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst))
          (((prodLift x x).obj q.snd).iso.hom) := by
        have ht' := ((prodLift x x).obj q.snd).isHomLift
        have hp : 𝒳.p.obj ((prodLift x x).obj q.snd).fst =
            𝒳.p.obj q.fst := (x.w_obj q.snd).trans q.over_eq
        rw [hp] at ht'
        exact ht'
      haveI hl := base_isHomLift_comp (S := 𝒳.p.obj q.fst)
        (T := 𝒳.p.obj q.fst) (𝒳.toBase.map a₁.hom)
        (((prodLift x x).obj q.snd).iso.hom)
      haveI hr := base_isHomLift_comp (S := 𝒳.p.obj q.fst)
        (T := 𝒳.p.obj q.fst) (((diag 𝒳).obj q.fst).iso.hom)
        (𝒳.toBase.map a₂.hom)
      exact base_hom_ext (S := 𝒳.p.obj q.fst) (T := 𝒳.p.obj q.fst) _ _
  let qx : (stabilizer x).obj :=
    { fst := q.fst
      snd := q.snd
      over_eq := q.over_eq
      iso := beta
      isHomLift := FiberProductHom.isHomLift_of_fst beta.hom
        (𝟙 (𝒳.p.obj q.fst)) (by
          exact FiberProductHom.isHomLift_fst q.iso.hom _ q.isHomLift) }
  have hqx₁ : qx.iso.hom.fst = a₁.hom := rfl
  have hqx₂ : qx.iso.hom.snd = a₂.hom := rfl
  let qyIso : (stabilizerMap F x).obj qx ≅
      (stabilizerUnit (x.comp F)).obj q.snd := by
    apply FiberProductObj.isoMk (F := diag 𝒴)
      (G := prodLift (x.comp F) (x.comp F))
      (F.toFunctor.mapIso a₁) (Iso.refl q.snd)
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj q.fst))
        (F.map a₁.hom) (𝟙 q.snd)
        (by
          let _ := ha₁
          exact F.preserves_isHomLift _ _)
        (IsHomLift.id q.over_eq)
    · apply FiberProductHom.ext
      · change F.map a₁.hom ≫ 𝟙 ((x.comp F).obj q.snd) =
          ((stabilizerMap F x).obj qx).iso.hom.fst ≫
            (x.comp F).map (𝟙 q.snd)
        rw [stabilizerMap_obj_iso_hom_fst]
        rw [hqx₁]
        change F.map a₁.hom ≫ 𝟙 ((x.comp F).obj q.snd) =
          F.map a₁.hom ≫ (x.comp F).map (𝟙 q.snd)
        rw [(x.comp F).toFunctor.map_id]
      · have hw := q.iso.hom.w
        have hw₀ : F.map q.iso.hom.fst = F.map q.iso.hom.snd := by
          change F.map q.iso.hom.fst ≫ 𝟙 (F.obj (x.obj q.snd)) =
            𝟙 (F.obj q.fst) ≫ F.map q.iso.hom.snd at hw
          simpa using hw
        have hw₁ : F.map a₁.hom = F.map a₂.hom := by
          rw [ha₁hom, ha₂hom]
          exact hw₀
        change F.map a₁.hom ≫ 𝟙 ((x.comp F).obj q.snd) =
          ((stabilizerMap F x).obj qx).iso.hom.snd ≫
            (x.comp F).map (𝟙 q.snd)
        rw [stabilizerMap_obj_iso_hom_snd]
        rw [hqx₂]
        calc
          F.map a₁.hom ≫ 𝟙 ((x.comp F).obj q.snd) =
              F.map a₁.hom := Category.comp_id _
          _ = F.map a₂.hom := hw₁
          _ = F.map a₂.hom ≫ 𝟙 ((x.comp F).obj q.snd) :=
            (Category.comp_id _).symm
          _ = F.map a₂.hom ≫ (x.comp F).map (𝟙 q.snd) := by
            rw [(x.comp F).toFunctor.map_id]
  exact
    { fst := qx
      snd := q.snd
      over_eq := q.over_eq
      iso := qyIso
      isHomLift := FiberProductHom.isHomLift_of_fst qyIso.hom
        (𝟙 (𝒳.p.obj q.fst)) (by
          change IsHomLift 𝒴.p (𝟙 (𝒳.p.obj q.fst)) (F.map a₁.hom)
          let _ := ha₁
          exact F.preserves_isHomLift _ _) }

/-- The underlying object of the source stabilizer in the kernel comparison. -/
lemma stabilizerKernelComparisonObj_fst_fst (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).fst.fst = q.fst := rfl

/-- The base object of the source stabilizer in the kernel comparison. -/
lemma stabilizerKernelComparisonObj_fst_snd (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).fst.snd = q.snd := rfl

/-- The first stabilizer arrow in the kernel comparison is the first diagonal-fiber arrow. -/
lemma stabilizerKernelComparisonObj_fst_iso_hom_fst
    (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).fst.iso.hom.fst =
      q.iso.hom.fst := rfl

/-- The second stabilizer arrow in the kernel comparison is the second diagonal-fiber arrow. -/
lemma stabilizerKernelComparisonObj_fst_iso_hom_snd
    (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).fst.iso.hom.snd =
      q.iso.hom.snd := rfl

/-- The first component of the comparison with the stabilizer identity section. -/
lemma stabilizerKernelComparisonObj_iso_hom_fst
    (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).iso.hom.fst =
      F.map q.iso.hom.fst := rfl

/-- The base component of the comparison with the stabilizer identity section. -/
lemma stabilizerKernelComparisonObj_iso_hom_snd
    (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳)
    (q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj) :
    (stabilizerKernelComparisonObj F x q).iso.hom.snd = 𝟙 q.snd := rfl

/-- The canonical comparison from a relative-diagonal fiber to the corresponding
stabilizer kernel. -/
def stabilizerKernelComparison (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳) :
    fiberProduct F.diag
        (fiberProductLift x x (Iso.refl (x.comp F))) ⥤ᵇ
      fiberProduct (stabilizerMap F x) (stabilizerUnit (x.comp F)) where
  obj := stabilizerKernelComparisonObj F x
  map {q r} φ := by
    let kfst : (stabilizerKernelComparisonObj F x q).fst ⟶
        (stabilizerKernelComparisonObj F x r).fst :=
      { fst := φ.fst
        snd := φ.snd
        isHomLift := φ.isHomLift
        w := by
          apply FiberProductHom.ext
          · have h := congrArg FiberProductHom.fst φ.w
            change φ.fst ≫ r.iso.hom.fst =
              q.iso.hom.fst ≫ x.map φ.snd at h
            change φ.fst ≫
                (stabilizerKernelComparisonObj F x r).fst.iso.hom.fst =
              (stabilizerKernelComparisonObj F x q).fst.iso.hom.fst ≫
                x.map φ.snd
            simpa only [stabilizerKernelComparisonObj_fst_iso_hom_fst] using h
          · have h := congrArg FiberProductHom.snd φ.w
            change φ.fst ≫ r.iso.hom.snd =
              q.iso.hom.snd ≫ x.map φ.snd at h
            change φ.fst ≫
                (stabilizerKernelComparisonObj F x r).fst.iso.hom.snd =
              (stabilizerKernelComparisonObj F x q).fst.iso.hom.snd ≫
                x.map φ.snd
            simpa only [stabilizerKernelComparisonObj_fst_iso_hom_snd] using h }
    exact
      { fst := kfst
        snd := φ.snd
        isHomLift := by
          have hkfst : IsHomLift (stabilizer x).p (𝒳.p.map φ.fst) kfst :=
            FiberProductHom.isHomLift_of_fst kfst _ (IsHomLift.map _ _)
          exact isHomLift_map_of_common_lift (𝒳.p.map φ.fst)
            kfst φ.snd hkfst φ.isHomLift
        w := by
          apply FiberProductHom.ext
          · have h := congrArg FiberProductHom.fst φ.w
            change φ.fst ≫ r.iso.hom.fst =
              q.iso.hom.fst ≫ x.map φ.snd at h
            have hF := congrArg F.map h
            change F.map φ.fst ≫
                (stabilizerKernelComparisonObj F x r).iso.hom.fst =
              (stabilizerKernelComparisonObj F x q).iso.hom.fst ≫
                (x.comp F).map φ.snd
            have hxmap : (x.comp F).map φ.snd = F.map (x.map φ.snd) := rfl
            rw [hxmap]
            simpa only [stabilizerKernelComparisonObj_iso_hom_fst,
              F.toFunctor.map_comp] using hF
          · change φ.snd ≫ 𝟙 r.snd = 𝟙 q.snd ≫ φ.snd
            simp }
  map_id q := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · rfl
  map_comp φ ψ := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · rfl
  w := rfl

/-- The stabilizer-kernel comparison is faithful. -/
lemma stabilizerKernelComparison_faithful (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳) :
    (stabilizerKernelComparison F x).toFunctor.Faithful := by
  constructor
  intro q r φ ψ h
  apply FiberProductHom.ext
  · exact congrArg (fun k ↦ k.fst.fst) h
  · exact congrArg
      (fun k : (stabilizerKernelComparison F x).obj q ⟶
        (stabilizerKernelComparison F x).obj r ↦ k.snd) h

/-- The stabilizer-kernel comparison is full. -/
lemma stabilizerKernelComparison_full (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳) :
    (stabilizerKernelComparison F x).toFunctor.Full := by
  constructor
  intro q r k
  have hs₀ := congrArg FiberProductHom.snd k.w
  have hs : k.fst.snd = k.snd := by
    change k.fst.snd ≫ 𝟙 r.snd = 𝟙 q.snd ≫ k.snd at hs₀
    have hs₁ : k.fst.snd ≫ 𝟙 r.snd = k.snd := by
      simpa only [Category.id_comp] using hs₀
    exact (Category.comp_id _).symm.trans hs₁
  let φ : q ⟶ r :=
    { fst := k.fst.fst
      snd := k.fst.snd
      isHomLift := k.fst.isHomLift
      w := by
        apply FiberProductHom.ext
        · have h := congrArg FiberProductHom.fst k.fst.w
          change k.fst.fst ≫
              (stabilizerKernelComparisonObj F x r).fst.iso.hom.fst =
            (stabilizerKernelComparisonObj F x q).fst.iso.hom.fst ≫
              x.map k.fst.snd at h
          change k.fst.fst ≫ r.iso.hom.fst =
            q.iso.hom.fst ≫ x.map k.fst.snd
          simpa only [stabilizerKernelComparisonObj_fst_iso_hom_fst] using h
        · have h := congrArg FiberProductHom.snd k.fst.w
          change k.fst.fst ≫
              (stabilizerKernelComparisonObj F x r).fst.iso.hom.snd =
            (stabilizerKernelComparisonObj F x q).fst.iso.hom.snd ≫
              x.map k.fst.snd at h
          change k.fst.fst ≫ r.iso.hom.snd =
            q.iso.hom.snd ≫ x.map k.fst.snd
          simpa only [stabilizerKernelComparisonObj_fst_iso_hom_snd] using h }
  refine ⟨φ, ?_⟩
  apply FiberProductHom.ext
  · apply FiberProductHom.ext <;> rfl
  · exact hs

/-- The stabilizer-kernel comparison is essentially surjective. -/
lemma stabilizerKernelComparison_essSurj (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳) :
    (stabilizerKernelComparison F x).toFunctor.EssSurj := by
  constructor
  intro t
  let e₁ := FiberProductObj.isoFst t.fst.iso
  let e₂ := FiberProductObj.isoSnd t.fst.iso
  let sigma := FiberProductObj.isoSnd t.iso
  have he₁hom : e₁.hom = t.fst.iso.hom.fst := rfl
  have he₂hom : e₂.hom = t.fst.iso.hom.snd := rfl
  have hsigmaHom : sigma.hom = t.iso.hom.snd := rfl
  have he₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) e₁.hom := by
    exact FiberProductHom.isHomLift_fst t.fst.iso.hom _ t.fst.isHomLift
  have he₂ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.fst)) e₂.hom := by
    exact FiberProductHom.isHomLift_snd t.fst.iso.hom _ t.fst.isHomLift
  have hsigma : IsHomLift (overBased S).p
      (𝟙 (𝒳.p.obj t.fst.fst)) sigma.hom := by
    exact FiberProductHom.isHomLift_snd t.iso.hom _ t.isHomLift
  have hout₁ := congrArg FiberProductHom.fst t.iso.hom.w
  have h₁ : t.iso.hom.fst =
      F.map e₁.hom ≫ (x.comp F).map sigma.hom := by
    change t.iso.hom.fst ≫ 𝟙 ((x.comp F).obj t.snd) =
      ((stabilizerMap F x).obj t.fst).iso.hom.fst ≫
        (x.comp F).map t.iso.hom.snd at hout₁
    rw [stabilizerMap_obj_iso_hom_fst] at hout₁
    calc
      t.iso.hom.fst = t.iso.hom.fst ≫ 𝟙 ((x.comp F).obj t.snd) :=
        (Category.comp_id _).symm
      _ = F.map t.fst.iso.hom.fst ≫
          (x.comp F).map t.iso.hom.snd := hout₁
      _ = F.map e₁.hom ≫ (x.comp F).map sigma.hom := by
        rw [he₁hom, hsigmaHom]
  have h₂ : t.iso.hom.fst =
      F.map e₂.hom ≫ (x.comp F).map sigma.hom := by
    have hout₂' := congrArg FiberProductHom.snd t.iso.hom.w
    change t.iso.hom.fst ≫ 𝟙 ((x.comp F).obj t.snd) =
      ((stabilizerMap F x).obj t.fst).iso.hom.snd ≫
        (x.comp F).map t.iso.hom.snd at hout₂'
    rw [stabilizerMap_obj_iso_hom_snd] at hout₂'
    calc
      t.iso.hom.fst = t.iso.hom.fst ≫ 𝟙 ((x.comp F).obj t.snd) :=
        (Category.comp_id _).symm
      _ = F.map t.fst.iso.hom.snd ≫
          (x.comp F).map t.iso.hom.snd := hout₂'
      _ = F.map e₂.hom ≫ (x.comp F).map sigma.hom := by
        rw [he₂hom, hsigmaHom]
  have heq : F.map e₁.hom = F.map e₂.hom := by
    have hright : F.map e₁.hom ≫ (x.comp F).map sigma.hom =
        F.map e₂.hom ≫ (x.comp F).map sigma.hom := h₁.symm.trans h₂
    haveI : IsIso ((x.comp F).map sigma.hom) := by infer_instance
    rw [← cancel_mono ((x.comp F).map sigma.hom)]
    exact hright
  let qiso : F.diag.obj t.fst.fst ≅
      (fiberProductLift x x (Iso.refl (x.comp F))).obj t.fst.snd := by
    apply FiberProductObj.isoMk (F := F) (G := F) e₁ e₂
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        e₁.hom e₂.hom he₁ he₂
    · change F.map e₁.hom ≫ 𝟙 (F.obj (x.obj t.fst.snd)) =
        𝟙 (F.obj t.fst.fst) ≫ F.map e₂.hom
      simpa using heq
  have hqiso₁ : qiso.hom.fst = e₁.hom := rfl
  have hqiso₂ : qiso.hom.snd = e₂.hom := rfl
  let q : (fiberProduct F.diag
      (fiberProductLift x x (Iso.refl (x.comp F)))).obj :=
    { fst := t.fst.fst
      snd := t.fst.snd
      over_eq := t.fst.over_eq
      iso := qiso
      isHomLift := FiberProductHom.isHomLift_of_fst qiso.hom
        (𝟙 (𝒳.p.obj t.fst.fst)) he₁ }
  refine ⟨q, ⟨?_⟩⟩
  let eX : (stabilizerKernelComparisonObj F x q).fst ≅ t.fst := by
    apply FiberProductObj.isoMk (F := diag 𝒳) (G := prodLift x x)
      (Iso.refl t.fst.fst) (Iso.refl t.fst.snd)
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
        (𝟙 t.fst.fst) (𝟙 t.fst.snd)
        (IsHomLift.id rfl) (IsHomLift.id t.fst.over_eq)
    · apply FiberProductHom.ext
      · change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.fst =
          (stabilizerKernelComparisonObj F x q).fst.iso.hom.fst ≫
            x.map (𝟙 t.fst.snd)
        rw [stabilizerKernelComparisonObj_fst_iso_hom_fst]
        rw [show q.iso.hom.fst = e₁.hom from hqiso₁]
        change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.fst =
          e₁.hom ≫ x.map (𝟙 t.fst.snd)
        rw [x.toFunctor.map_id]
        change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.fst = e₁.hom ≫ 𝟙 _
        rw [he₁hom]
        simp
      · change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.snd =
          (stabilizerKernelComparisonObj F x q).fst.iso.hom.snd ≫
            x.map (𝟙 t.fst.snd)
        rw [stabilizerKernelComparisonObj_fst_iso_hom_snd]
        rw [show q.iso.hom.snd = e₂.hom from hqiso₂]
        change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.snd =
          e₂.hom ≫ x.map (𝟙 t.fst.snd)
        rw [x.toFunctor.map_id]
        change (𝟙 t.fst.fst) ≫ t.fst.iso.hom.snd = e₂.hom ≫ 𝟙 _
        rw [he₂hom]
        simp
  apply FiberProductObj.isoMk (a := (stabilizerKernelComparison F x).obj q)
    (b := t) eX sigma
  · have heX : IsHomLift (stabilizer x).p
        (𝟙 (𝒳.p.obj t.fst.fst)) eX.hom :=
      FiberProductHom.isHomLift_of_fst eX.hom _ (IsHomLift.id rfl)
    exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.fst))
      eX.hom sigma.hom heX hsigma
  · apply FiberProductHom.ext
    · change F.map (𝟙 t.fst.fst) ≫ t.iso.hom.fst =
        (stabilizerKernelComparisonObj F x q).iso.hom.fst ≫
          (x.comp F).map sigma.hom
      rw [stabilizerKernelComparisonObj_iso_hom_fst]
      rw [show q.iso.hom.fst = e₁.hom from hqiso₁]
      rw [F.toFunctor.map_id, Category.id_comp]
      exact h₁
    · change (𝟙 t.fst.snd) ≫ t.iso.hom.snd =
        𝟙 q.snd ≫ sigma.hom
      rfl

/-- **Exercise 4.2.7** (`exer:fiber-products-and-stabilizers`) (part (b), the fiber of the
relative diagonal over `(x, x, id)`): let `F : 𝒳 → 𝒴` be a morphism of prestacks over `𝒮`
and let `x` be a point of `𝒳` over `S`. The fiber of the relative diagonal
`Δ_F : 𝒳 → 𝒳 ×_𝒴 𝒳` over the point `(x, x, id)` is the fiber product of `G_x → G_{F(x)}`
and the identity section of `G_{F(x)}` — group-theoretically, the kernel of
`G_x → G_{F(x)}`. -/
theorem exists_equivalence_fiberProduct_diag_stabilizerUnit (F : 𝒳 ⥤ᵇ 𝒴) {S : 𝒮}
    (x : overBased S ⥤ᵇ 𝒳) :
    ∃ E : fiberProduct F.diag (fiberProductLift x x (Iso.refl (x.comp F))) ⥤ᵇ
      fiberProduct (stabilizerMap F x) (stabilizerUnit (x.comp F)),
      E.toFunctor.IsEquivalence := by
  refine ⟨stabilizerKernelComparison F x, ?_⟩
  let _ := stabilizerKernelComparison_faithful F x
  let _ := stabilizerKernelComparison_full F x
  let _ := stabilizerKernelComparison_essSurj F x
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/- Remaining obligations from Exercise 4.2.7, part (b): the phrasing of the fiber of the
diagonal as the *kernel* `ker(G_x → G_y)`
of a homomorphism of group algebraic spaces, and the description of the fiber of `Δ_F`
over an *arbitrary* field-valued point `(x₁, x₂, γ)` of `𝒳 ×_𝒴 𝒳` (a torsor-like
transporter of `x₁` to `x₂` over `γ`), require transporting the group structure of
`BasedCategory.autPresheaf` to the chosen algebraic-space representatives and are not
formalized. -/

end CategoryTheory.BasedCategory

end ExerFiberProductsAndStabilizers

section ExerDeligneMumfordUnramifiedDiagonal

open CategoryTheory Functor Limits

universe v₂ u₂ u

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

variable (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack 𝒳]

/-- **Exercise 4.2.8** (`exer:deligne-mumford-unramified-diagonal`) (part (a), separated
étale): let `𝒳` be a Deligne–Mumford stack and let `x : Spec K → 𝒳` be a field-valued
point. Then the stabilizer `G_x` is a scheme, and the representing morphism `G_x → Spec K`
is separated and étale. -/
theorem IsDeligneMumfordStack.exists_scheme_stabilizer_isSeparated_etale {K : Type u}
    [Field K] (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) :
    ∃ (G : Scheme.{u}) (E : overBased G ⥤ᵇ BasedCategory.stabilizer x),
      E.toFunctor.IsEquivalence ∧
      IsSeparated (E.comp (fiberProductSnd (diag 𝒳) (prodLift x x))).overHom ∧
      Etale (E.comp (fiberProductSnd (diag 𝒳) (prodLift x x))).overHom := by
  sorry

/-- **Exercise 4.2.8** (`exer:deligne-mumford-unramified-diagonal`) (part (a),
finiteness): let `𝒳` be a Deligne–Mumford stack and let `x : Spec K → 𝒳` be a
field-valued point whose stabilizer is represented by a quasi-compact scheme `G`. Then the
representing morphism `G → Spec K` is finite (hence `G_x` is a finite étale group scheme
over `K`). The book's quasi-compactness hypothesis on `G_x` is rendered as `CompactSpace G`
on the representing scheme (see the section's COMMENTARY.md). -/
theorem IsDeligneMumfordStack.isFinite_stabilizer_of_compactSpace {K : Type u} [Field K]
    (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) (G : Scheme.{u}) [CompactSpace G]
    (E : overBased G ⥤ᵇ BasedCategory.stabilizer x) (hE : E.toFunctor.IsEquivalence) :
    IsFinite (E.comp (fiberProductSnd (diag 𝒳) (prodLift x x))).overHom := by
  let f := (E.comp (fiberProductSnd (diag 𝒳) (prodLift x x))).overHom
  have hdiag : BasedFunctor.RepresentableWith
      (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (diag 𝒳) :=
    IsDeligneMumfordStack.representableWith_unramified_diag_of_presentation 𝒳
  have hf : (@FormallyUnramified ⊓ @LocallyOfFiniteType :
      MorphismProperty Scheme.{u}) f :=
    hdiag.property_of_scheme_representation
      (Spec (CommRingCat.of K)) (prodLift x x) G E hE
  let _ : FormallyUnramified f := hf.1
  let _ : LocallyOfFiniteType f := hf.2
  let _ : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType f
  let _ : QuasiCompact f := by infer_instance
  exact IsFinite.of_locallyQuasiFinite f

/-- **Exercise 4.2.8** (`exer:deligne-mumford-unramified-diagonal`) (part (b), item label
part (b)): the diagonal `Δ : 𝒳 → 𝒳 × 𝒳` of a
Deligne–Mumford stack is unramified — it is representable, and on étale presentations of
its base changes to schemes it is formally unramified and locally of finite type. (Mathlib
has no combined unramified class for morphisms of schemes; unramified is rendered as
`FormallyUnramified ⊓ LocallyOfFiniteType`, which is stable under base change and étale
local on the source, so the notion is well defined for representable morphisms — see the
section's COMMENTARY.md.) -/
theorem IsDeligneMumfordStack.representableWith_unramified_diag :
    BasedFunctor.RepresentableWith
      (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (BasedCategory.diag 𝒳) := by
  exact IsDeligneMumfordStack.representableWith_unramified_diag_of_presentation 𝒳

/- **Section 4.2.2** (`sec:stabilizers-and-inertia`) (unlabeled remark following
Exercise 4.2.8): if `𝒳` is a
quasi-separated Deligne–Mumford stack, the exercise shows that the stabilizer `G_x` of a
field-valued point `x ∈ 𝒳(K)` is a finite étale group scheme over `K`. When `K` is
algebraically closed, a finite étale group scheme over `K` is determined by its group of
`K`-points, so `G_x` corresponds to the abstract finite group `Aut_{𝒳(K)}(x)`. This
remark is recorded as prose: the equivalence between finite étale group schemes over an
algebraically closed field and finite groups is not formalized here. -/

end AlgebraicGeometry

end ExerDeligneMumfordUnramifiedDiagonal
