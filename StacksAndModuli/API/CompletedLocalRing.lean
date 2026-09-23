module

public import StacksAndModuli.API.GlobalSectionsOverBase
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Completed local rings of schemes

For a morphism `f : X ⟶ Spec R` and a point `x : X`, this file provides the canonical
`R`-algebra structure on the stalk `𝒪_{X,x}` and its completion at the maximal ideal.

The algebra structures depend on `f`, so they are definitions rather than global instances.
Install them locally with `letI := Scheme.stalkAlgebra f x` and
`letI := Scheme.completedLocalRingAlgebra f x`.

## Main definitions

* `AlgebraicGeometry.Scheme.baseToStalk`: the canonical ring map `R → 𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme.stalkAlgebra`: the induced `R`-algebra structure on
  `𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme.completedLocalRing`: the completion of `𝒪_{X,x}` at its
  maximal ideal.
* `AlgebraicGeometry.Scheme.toCompletedLocalRing`: the canonical map from a stalk to its
  completed local ring.
* `AlgebraicGeometry.Scheme.completedLocalRingAlgebra`: the induced `R`-algebra structure on
  the completed local ring.
* `AdicCompletion.congrRingEquiv` and `AdicCompletion.congrAlgEquiv`: transport adic
  completions across equivalences carrying one ideal to another.
* `AlgebraicGeometry.Scheme.completedLocalRingAlgEquivOfIsoOver`: completed local rings at
  corresponding points of isomorphic schemes are equivalent over the base.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace

universe u

namespace AdicCompletion

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The equivalence on the quotients by the `n`th powers of corresponding ideals induced by a
ring equivalence. This is the levelwise map underlying `AdicCompletion.congrRingEquiv`. -/
def quotientRingEquiv (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (n : ℕ) :
    A ⧸ (I ^ n • ⊤ : Ideal A) ≃+* B ⧸ (J ^ n • ⊤ : Ideal B) :=
  Ideal.quotientEquiv _ _ e (by
    have hn : J ^ n = (I.map (e : A →+* B)) ^ n := congrArg (fun K ↦ K ^ n) hJ
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow] using hn)

/-- On a quotient representative, the levelwise equivalence applies the original ring
equivalence. -/
@[simp]
theorem quotientRingEquiv_mk (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (n : ℕ) (a : A) :
    quotientRingEquiv I J e hJ n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (e a) :=
  rfl

/-- The levelwise quotient equivalences commute with the transition maps in the inverse
systems defining the completions. -/
theorem transitionMap_quotientRingEquiv (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) {m n : ℕ} (hmn : m ≤ n)
    (a : A ⧸ (I ^ n • ⊤ : Ideal A)) :
    transitionMap J B hmn (quotientRingEquiv I J e hJ n a) =
      quotientRingEquiv I J e hJ m (transitionMap I A hmn a) := by
  induction a using Quotient.inductionOn' with
  | _ a => rfl

/-- If a ring equivalence carries `I` to `J`, its inverse carries `J` to `I`. -/
theorem ideal_eq_map_symm (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) : I = J.map (e.symm : B →+* A) :=
  (Ideal.map_of_equiv e).symm.trans
    (congrArg (fun K : Ideal B ↦ K.map (e.symm : B →+* A)) hJ).symm

/-- The levelwise quotient equivalence followed by that induced by the inverse ring
equivalence is the identity. -/
theorem quotientRingEquiv_left_inv (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (hI : I = J.map (e.symm : B →+* A))
    (n : ℕ) (a : A ⧸ (I ^ n • ⊤ : Ideal A)) :
    quotientRingEquiv J I e.symm hI n (quotientRingEquiv I J e hJ n a) = a := by
  induction a using Quotient.inductionOn' with
  | _ a =>
      change Ideal.Quotient.mk _ (e.symm (e a)) = Ideal.Quotient.mk _ a
      rw [e.symm_apply_apply]

/-- The levelwise quotient equivalence is a right inverse to that induced by the inverse ring
equivalence. -/
theorem quotientRingEquiv_right_inv (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (hI : I = J.map (e.symm : B →+* A))
    (n : ℕ) (b : B ⧸ (J ^ n • ⊤ : Ideal B)) :
    quotientRingEquiv I J e hJ n (quotientRingEquiv J I e.symm hI n b) = b := by
  induction b using Quotient.inductionOn' with
  | _ b =>
      change Ideal.Quotient.mk _ (e (e.symm b)) = Ideal.Quotient.mk _ b
      rw [e.apply_symm_apply]

/-- A ring equivalence carrying `I` to `J` induces an equivalence of the corresponding adic
completions. -/
def congrRingEquiv (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) : AdicCompletion I A ≃+* AdicCompletion J B where
  toFun a :=
    ⟨fun n ↦ quotientRingEquiv I J e hJ n (a.val n), fun hmn ↦ by
      rw [transitionMap_quotientRingEquiv, a.property hmn]⟩
  invFun b :=
    let hI := ideal_eq_map_symm I J e hJ
    ⟨fun n ↦ quotientRingEquiv J I e.symm hI n (b.val n), fun hmn ↦ by
      rw [transitionMap_quotientRingEquiv, b.property hmn]⟩
  left_inv a := by
    ext n
    exact quotientRingEquiv_left_inv I J e hJ (ideal_eq_map_symm I J e hJ) n (a.val n)
  right_inv b := by
    ext n
    exact quotientRingEquiv_right_inv I J e hJ (ideal_eq_map_symm I J e hJ) n (b.val n)
  map_add' a b := by
    ext n
    exact map_add (quotientRingEquiv I J e hJ n) (a.val n) (b.val n)
  map_mul' a b := by
    ext n
    exact map_mul (quotientRingEquiv I J e hJ n) (a.val n) (b.val n)

/-- Evaluation of the induced completion equivalence is the corresponding equivalence on
the finite-level quotient. -/
@[simp]
theorem congrRingEquiv_val_apply (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (a : AdicCompletion I A) (n : ℕ) :
    (congrRingEquiv I J e hJ a).val n = quotientRingEquiv I J e hJ n (a.val n) :=
  rfl

/-- The induced completion equivalence commutes with the canonical maps from the original
rings. -/
@[simp]
theorem congrRingEquiv_of (I : Ideal A) (J : Ideal B) (e : A ≃+* B)
    (hJ : J = I.map (e : A →+* B)) (a : A) :
    congrRingEquiv I J e hJ (AdicCompletion.of I A a) = AdicCompletion.of J B (e a) := by
  ext n
  exact quotientRingEquiv_mk I J e hJ n a

variable {K : Type u} [CommRing K] [Algebra K A] [Algebra K B]

/-- An algebra equivalence carrying `I` to `J` induces an algebra equivalence of the
corresponding adic completions. -/
noncomputable def congrAlgEquiv (I : Ideal A) (J : Ideal B) (e : A ≃ₐ[K] B)
    (hJ : J = I.map (e : A →+* B)) : AdicCompletion I A ≃ₐ[K] AdicCompletion J B :=
  AlgEquiv.ofRingEquiv (f := congrRingEquiv I J e.toRingEquiv hJ) fun k ↦ by
    rw [AdicCompletion.algebraMap_apply, congrRingEquiv_of,
      AdicCompletion.algebraMap_apply]
    congr 1
    exact e.commutes k

/-- The algebra equivalence on completions commutes with the canonical maps from the original
algebras. -/
@[simp]
theorem congrAlgEquiv_of (I : Ideal A) (J : Ideal B) (e : A ≃ₐ[K] B)
    (hJ : J = I.map (e : A →+* B)) (a : A) :
    congrAlgEquiv I J e hJ (AdicCompletion.of I A a) = AdicCompletion.of J B (e a) := by
  change congrRingEquiv I J e.toRingEquiv hJ (AdicCompletion.of I A a) =
    AdicCompletion.of J B (e.toRingEquiv a)
  exact congrRingEquiv_of I J e.toRingEquiv hJ a

end AdicCompletion

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

/-- The canonical ring map from the base ring to the stalk of a scheme over an affine base. -/
noncomputable def baseToStalk (f : X ⟶ Spec R) (x : X) :
    R ⟶ CommRingCat.of (X.presheaf.stalk x) :=
  Scheme.Modules.baseRingHom f ≫ X.presheaf.germ ⊤ x trivial

/-- The map from the base to a stalk sends an element first to a global function and then to
its germ. -/
@[simp]
theorem baseToStalk_apply (f : X ⟶ Spec R) (x : X) (r : R) :
    baseToStalk f x r = X.presheaf.germ ⊤ x trivial (Scheme.Modules.baseRingHom f r) :=
  rfl

/-- The map from the base ring to a stalk is compatible with changing the affine base. -/
@[reassoc]
theorem baseToStalk_comp {S : CommRingCat.{u}} (g : R ⟶ S)
    (f : X ⟶ Spec S) (x : X) :
    g ≫ baseToStalk f x = baseToStalk (f ≫ Spec.map g) x := by
  unfold baseToStalk
  rw [← Category.assoc, Scheme.Modules.baseRingHom_comp]

/-- The map from the base ring to a stalk is natural in the source scheme. -/
@[reassoc]
theorem baseToStalk_comp_stalkMap (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X) :
    baseToStalk p (g x) ≫ g.stalkMap x = baseToStalk (g ≫ p) x := by
  unfold baseToStalk
  rw [Category.assoc, Scheme.Hom.germ_stalkMap]
  change (Scheme.Modules.baseRingHom p ≫ g.appTop) ≫
    X.presheaf.germ ⊤ x trivial = _
  rw [Scheme.Modules.baseRingHom_comp_appTop]

/-- The stalk of a scheme over `Spec R` is canonically an `R`-algebra.

This is not an instance because it depends on the chosen morphism `f`. -/
@[instance_reducible]
noncomputable def stalkAlgebra (f : X ⟶ Spec R) (x : X) :
    Algebra R (X.presheaf.stalk x) :=
  (baseToStalk f x).hom.toAlgebra

/-- The algebra map for `stalkAlgebra` is `baseToStalk`. -/
@[simp]
theorem algebraMap_stalkAlgebra (f : X ⟶ Spec R) (x : X) (r : R) :
    @algebraMap R (X.presheaf.stalk x) _ _ (stalkAlgebra f x) r = baseToStalk f x r :=
  rfl

/-- A morphism of schemes induces an algebra homomorphism on stalks over any affine base of
its target. -/
noncomputable def Hom.stalkMapAlgHom (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X) :
    letI := stalkAlgebra p (g x)
    letI := stalkAlgebra (g ≫ p) x
    Y.presheaf.stalk (g x) →ₐ[R] X.presheaf.stalk x := by
  letI := stalkAlgebra p (g x)
  letI := stalkAlgebra (g ≫ p) x
  exact
    { (g.stalkMap x).hom with
      commutes' := fun r ↦ by
        change g.stalkMap x (baseToStalk p (g x) r) = baseToStalk (g ≫ p) x r
        exact DFunLike.congr_fun
          (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap g p x)) r }

/-- The underlying function of the algebra homomorphism on stalks is the usual stalk map. -/
@[simp]
theorem Hom.stalkMapAlgHom_apply (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X)
    (a : Y.presheaf.stalk (g x)) :
    g.stalkMapAlgHom p x a = g.stalkMap x a :=
  rfl

/-- An isomorphism of schemes induces an equivalence of the corresponding stalks. -/
noncomputable def stalkRingEquivOfIso (e : X ≅ Y) (x : X) :
    Y.presheaf.stalk (e.hom x) ≃+* X.presheaf.stalk x :=
  (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- The stalk equivalence induced by a scheme isomorphism is the usual stalk map in the
forward direction. -/
@[simp]
theorem stalkRingEquivOfIso_apply (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    stalkRingEquivOfIso e x a = e.hom.stalkMap x a :=
  rfl

/-- An isomorphism of schemes induces an equivalence of stalks as algebras over any affine
base of its target. -/
noncomputable def stalkAlgEquivOfIso (e : X ≅ Y) (p : Y ⟶ Spec R) (x : X) :
    letI := stalkAlgebra p (e.hom x)
    letI := stalkAlgebra (e.hom ≫ p) x
    Y.presheaf.stalk (e.hom x) ≃ₐ[R] X.presheaf.stalk x := by
  letI := stalkAlgebra p (e.hom x)
  letI := stalkAlgebra (e.hom ≫ p) x
  exact AlgEquiv.ofRingEquiv (f := stalkRingEquivOfIso e x) fun r ↦
    (e.hom.stalkMapAlgHom p x).commutes r

/-- The underlying function of the algebra equivalence on stalks is the usual stalk map. -/
@[simp]
theorem stalkAlgEquivOfIso_apply (e : X ≅ Y) (p : Y ⟶ Spec R) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    stalkAlgEquivOfIso e p x a = e.hom.stalkMap x a :=
  rfl

/-- The completed local ring of `X` at `x`, formed with respect to the maximal ideal of the
local ring `𝒪_{X,x}`. -/
abbrev completedLocalRing (X : Scheme.{u}) (x : X) :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The canonical ring map from a stalk to its completed local ring. -/
noncomputable def toCompletedLocalRing (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x →+* X.completedLocalRing x :=
  algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)

/-- The canonical map into a completed local ring is Mathlib's map into the adic
completion. -/
@[simp]
theorem toCompletedLocalRing_apply (X : Scheme.{u}) (x : X) (a : X.presheaf.stalk x) :
    X.toCompletedLocalRing x a =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) a := by
  simp [toCompletedLocalRing, AdicCompletion.algebraMap_apply]

/-- An isomorphism of schemes induces an equivalence of completed local rings. -/
noncomputable def completedLocalRingRingEquivOfIso (e : X ≅ Y) (x : X) :
    Y.completedLocalRing (e.hom x) ≃+* X.completedLocalRing x :=
  AdicCompletion.congrRingEquiv _ _ (stalkRingEquivOfIso e x)
    (IsLocalRing.map_ringEquiv_maximalIdeal (stalkRingEquivOfIso e x)).symm

/-- The equivalence of completed local rings induced by a scheme isomorphism commutes with
the canonical maps from the stalks. -/
@[simp]
theorem completedLocalRingRingEquivOfIso_toCompletedLocalRing (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    completedLocalRingRingEquivOfIso e x (Y.toCompletedLocalRing (e.hom x) a) =
      X.toCompletedLocalRing x (stalkRingEquivOfIso e x a) := by
  rw [toCompletedLocalRing_apply, toCompletedLocalRing_apply]
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ a

/-- The completed local ring of a scheme over `Spec R` is canonically an `R`-algebra.

This is not an instance because it depends on the chosen morphism `f`. -/
@[instance_reducible]
noncomputable def completedLocalRingAlgebra (f : X ⟶ Spec R) (x : X) :
    Algebra R (X.completedLocalRing x) := by
  letI := stalkAlgebra f x
  infer_instance

/-- The algebra map into a completed local ring is the composite of `baseToStalk` and the
canonical completion map. -/
@[simp]
theorem algebraMap_completedLocalRingAlgebra (f : X ⟶ Spec R) (x : X) (r : R) :
    @algebraMap R (X.completedLocalRing x) _ _ (completedLocalRingAlgebra f x) r =
      X.toCompletedLocalRing x (baseToStalk f x r) := by
  rfl

/-- An isomorphism of schemes induces an equivalence of completed local rings as algebras over
any affine base of its target. The source structure morphism is the composite with the
isomorphism. -/
noncomputable def completedLocalRingAlgEquivOfIso (e : X ≅ Y)
    (p : Y ⟶ Spec R) (x : X) :
    letI := completedLocalRingAlgebra p (e.hom x)
    letI := completedLocalRingAlgebra (e.hom ≫ p) x
    Y.completedLocalRing (e.hom x) ≃ₐ[R] X.completedLocalRing x := by
  letI := completedLocalRingAlgebra p (e.hom x)
  letI := completedLocalRingAlgebra (e.hom ≫ p) x
  exact AlgEquiv.ofRingEquiv (f := completedLocalRingRingEquivOfIso e x) fun r ↦ by
    rw [algebraMap_completedLocalRingAlgebra, algebraMap_completedLocalRingAlgebra,
      completedLocalRingRingEquivOfIso_toCompletedLocalRing]
    congr 1
    change e.hom.stalkMap x (baseToStalk p (e.hom x) r) = baseToStalk (e.hom ≫ p) x r
    exact DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap e.hom p x)) r

/-- The algebra equivalence of completed local rings induced by a scheme isomorphism commutes
with the canonical maps from the stalks. -/
@[simp]
theorem completedLocalRingAlgEquivOfIso_toCompletedLocalRing (e : X ≅ Y)
    (p : Y ⟶ Spec R) (x : X) (a : Y.presheaf.stalk (e.hom x)) :
    completedLocalRingAlgEquivOfIso e p x (Y.toCompletedLocalRing (e.hom x) a) =
      X.toCompletedLocalRing x (stalkAlgEquivOfIso e p x a) :=
  completedLocalRingRingEquivOfIso_toCompletedLocalRing e x a

/-- Variant of `completedLocalRingAlgEquivOfIso` for separately named structure morphisms
whose compatibility with the isomorphism is given by an equality. -/
noncomputable def completedLocalRingAlgEquivOfIsoOver (e : X ≅ Y)
    (f : X ⟶ Spec R) (p : Y ⟶ Spec R) (h : e.hom ≫ p = f) (x : X) :
    letI := completedLocalRingAlgebra p (e.hom x)
    letI := completedLocalRingAlgebra f x
    Y.completedLocalRing (e.hom x) ≃ₐ[R] X.completedLocalRing x := by
  subst f
  exact completedLocalRingAlgEquivOfIso e p x

end AlgebraicGeometry.Scheme
