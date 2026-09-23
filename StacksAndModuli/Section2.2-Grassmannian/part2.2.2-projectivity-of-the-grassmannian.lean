module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.1-representability-by-a-scheme»
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksAndModuli.API.LocalizedSurjectivity
public import StacksAndModuli.API.ExteriorPowerRestrict
public import StacksAndModuli.API.PullbackGeneration
public import StacksAndModuli.API.RepresentableByTransport
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Projectivity of the Grassmannian

This module formalizes the second subsection ("Projectivity of the Grassmannian") of
Section 2.2 (Projectivity of the Grassmannian) of Chapter 2 of *Stacks and Moduli*,
label `sec:grassmannian`: the Plücker
embedding and `prop:grassmannian-projective`, together with the supporting module-level
theory of exterior powers of finite projective modules (a Mathlib gap), and the
projectivity half of the relative version (`sec:relative-grassmannian`, i.e. §2.1's
Theorem 2.1.1 `thm:grassmannian-projective-relative`, stated here as
`Scheme.exists_grassmannianOverFunctor_representableBy` and proved in the free case).

The Plücker embedding sends a rank-`q` quotient `O^{⊕n} ↠ Q` to the line bundle quotient
`⋀^q O^{⊕n} ↠ ⋀^q Q`; identifying `⋀^q O^{⊕n}` with `O^{⊕C(n,q)}` via the basis of
`q`-element subsets (`Module.Basis.exteriorPower`), it is a morphism of functors
`Gr(q, n) ⟶ Gr(1, C(n,q)) = ℙ(⋀^q O^{⊕n})`. The affine operation is
`Module.Grassmannian.plucker`; its globalization and arbitrary-base-change naturality
give the explicit transformation `Scheme.pluckerMorphism`. The remaining geometric
step is the proof that its restrictions to the standard Plücker charts are closed
immersions.

Ledgered items of this section (see the chapter summary): the tangent-space exercise
(`exer:grassmannian-tangent-space`), the quotient descriptions `U/GL_q` and `GL_n/H`, the
Picard group exercise, the flag-varieties exercise, and the very-ampleness of the Plücker
line bundle (`cor:grassmannian-very-ample`, requiring determinants of sheaves and a notion
of relative very-ampleness).

Main book result:
- `AlgebraicGeometry.Scheme.exists_plucker_isClosedImmersion_presheaf`
  (`prop:grassmannian-projective`).

The exterior-power API, affine and global Plücker constructions, and free-case
projectivity results are supporting stages. The final relative Grassmannian theorem is in
the following part.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section PropGrassmannianProjective

open CategoryTheory Limits

universe u v

section ModuleLemmas

open AlgebraicGeometry.Scheme

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A linear equivalence induces a linear equivalence on every exterior power. -/
noncomputable def LinearEquiv.exteriorPower {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (k : ℕ) : (⋀[R]^k M) ≃ₗ[R] (⋀[R]^k N) :=
  LinearEquiv.ofLinear (_root_.exteriorPower.map k e.toLinearMap)
    (_root_.exteriorPower.map k e.symm.toLinearMap)
    (by
      rw [← _root_.exteriorPower.map_comp]
      have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [he, _root_.exteriorPower.map_id])
    (by
      rw [← _root_.exteriorPower.map_comp]
      have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [he, _root_.exteriorPower.map_id])

@[simp]
lemma LinearEquiv.exteriorPower_apply_ιMulti {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (k : ℕ) (v : Fin k → M) :
    e.exteriorPower k (exteriorPower.ιMulti R k v) =
      exteriorPower.ιMulti R k (e ∘ v) := by
  dsimp only [LinearEquiv.exteriorPower]
  change _root_.exteriorPower.map k e.toLinearMap (exteriorPower.ιMulti R k v) = _
  exact _root_.exteriorPower.map_apply_ιMulti e.toLinearMap v

/-- A finite set has a unique subset of cardinality equal to its own cardinality. -/
noncomputable def powersetCardSubtypeEquivPUnit {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) : Set.powersetCard (↑I) q ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨Finset.univ, by simp [hI]⟩
  left_inv s := by
    apply Subtype.ext
    exact (s.val.card_eq_iff_eq_univ.1 (by rw [s.property]; simp [hI])).symm
  right_inv x := Subsingleton.elim _ _

/-- The top exterior power of the free module on a `q`-element finite set is
canonically free of rank one, with the ordered exterior basis sent to `1`. -/
noncomputable def topExteriorPiEquiv (R : Type u) [CommRing R] {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q) :
    (⋀[R]^q (↑I → R)) ≃ₗ[R] R :=
  ((Pi.basisFun R (↑I)).exteriorPower q).equivFun |>.trans
    ((LinearEquiv.piCongrLeft R (fun _ : PUnit.{1} ↦ R)
      (powersetCardSubtypeEquivPUnit I hI)).trans
        (LinearEquiv.funUnique PUnit.{1} R R))

@[simp]
lemma topExteriorPiEquiv_apply_basis (R : Type u) [CommRing R] {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q) :
    topExteriorPiEquiv R I hI
      (((Pi.basisFun R (↑I)).exteriorPower q)
        ⟨Finset.univ, by simp [hI]⟩) = 1 := by
  simp only [topExteriorPiEquiv, LinearEquiv.trans_apply,
    LinearEquiv.funUnique_apply]
  change ((Pi.basisFun R (↑I)).exteriorPower q).equivFun
    (((Pi.basisFun R (↑I)).exteriorPower q) ⟨Finset.univ, by simp [hI]⟩)
      ((powersetCardSubtypeEquivPUnit I hI).symm PUnit.unit) = 1
  rw [Module.Basis.equivFun_self]
  simp [powersetCardSubtypeEquivPUnit]

/-- In the canonical trivialization of a top exterior power, an exterior product
is the determinant of its coordinate matrix. -/
lemma topExteriorPiEquiv_apply_ιMulti (R : Type u) [CommRing R] {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q) (v : Fin q → (↑I → R)) :
    topExteriorPiEquiv R I hI (exteriorPower.ιMulti R q v) =
      (Matrix.of fun k l ↦ v k (I.orderIsoOfFin hI l)).det := by
  let s : Set.powersetCard (↑I) q := ⟨Finset.univ, by simp [hI]⟩
  have he : Set.powersetCard.ofFinEmbEquiv.symm s =
      (I.orderIsoOfFin hI).toOrderEmbedding := by
    have hleft : Set.powersetCard.ofFinEmbEquiv.symm s =
        Finset.univ.orderEmbOfFin s.property := by
      apply Finset.orderEmbOfFin_unique'
      intro k
      exact Finset.mem_univ _
    have hright : (I.orderIsoOfFin hI).toOrderEmbedding =
        Finset.univ.orderEmbOfFin s.property := by
      apply Finset.orderEmbOfFin_unique'
      intro k
      exact Finset.mem_univ _
    exact hleft.trans hright.symm
  calc
    topExteriorPiEquiv R I hI (exteriorPower.ιMulti R q v) =
        ((Pi.basisFun R ↑I).exteriorPower q).repr
          (exteriorPower.ιMulti R q v) s := by
      rfl
    _ = exteriorPower.ιMultiDual R q (Pi.basisFun R ↑I) s
        (exteriorPower.ιMulti R q v) :=
      exteriorPower.basis_repr_apply R q (Pi.basisFun R ↑I)
        (exteriorPower.ιMulti R q v) s
    _ = _ := by
      rw [exteriorPower.ιMultiDual_apply_ιMulti, he]
      simp

/-- In a `q`-dimensional vector space, a `q`-tuple with nonzero exterior product is
linearly independent. -/
lemma linearIndependent_of_exteriorPower_ιMulti_ne_zero_of_finrank_eq
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : ℕ) (v : Fin q → V)
    (hdim : Module.finrank K V = q)
    (hv : exteriorPower.ιMulti K q v ≠ 0) : LinearIndependent K v := by
  classical
  let b : Module.Basis (Fin q) K V := Module.finBasisOfFinrankEq K V hdim
  let s : Set.powersetCard (Fin q) q := ⟨Finset.univ, by simp⟩
  let A : Matrix (Fin q) (Fin q) K := Matrix.of fun i j ↦
    b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i)
  have hdet : A.det ≠ 0 := by
    intro hdet
    apply hv
    apply ((b.exteriorPower q).repr).injective
    ext t
    have ht : t = s := by
      apply Subtype.ext
      exact t.val.card_eq_iff_eq_univ.1 (by rw [t.property]; simp)
    subst t
    rw [exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti]
    simpa [A] using hdet
  have hrows : LinearIndependent K (fun i ↦ A i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have he : Set.powersetCard.ofFinEmbEquiv.symm s =
      RelEmbedding.refl (fun x y : Fin q ↦ x ≤ y) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_univ i
  have hcoord : (fun i ↦ A i) = b.equivFun ∘ v := by
    funext i j
    change b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i) =
      b.equivFun (v i) j
    rw [he]
    rfl
  rw [hcoord] at hrows
  exact LinearIndependent.of_comp b.equivFun.toLinearMap hrows

/-- Replacing one row of the identity matrix by `v` changes its determinant to the
corresponding entry of `v`. -/
lemma Matrix.det_updateRow_one {K : Type u} [CommRing K]
    {m : Type v} [Fintype m] [DecidableEq m] (i : m) (v : m → K) :
    ((1 : Matrix m m K).updateRow i v).det = v i := by
  have hv : v = ∑ k, v k • (1 : Matrix m m K) k := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  calc
    ((1 : Matrix m m K).updateRow i v).det =
        ((1 : Matrix m m K).updateRow i
          (∑ k, v k • (1 : Matrix m m K) k)).det :=
      congrArg (fun w ↦ ((1 : Matrix m m K).updateRow i w).det) hv
    _ = v i := by
      rw [Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

/-- Replace a selected coordinate `i ∈ I` by an outside coordinate `j ∉ I`. -/
def replaceCoordinate {n : ℕ} (I : Finset (Fin n)) (i : ↑I) (j : ↑(Iᶜ)) :
    Finset (Fin n) := insert j.1 (I.erase i.1)

@[simp]
lemma replaceCoordinate_card {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) (i : ↑I) (j : ↑(Iᶜ)) :
    (replaceCoordinate I i j).card = q := by
  have hj : j.1 ∉ I.erase i.1 := by
    intro hj
    exact (Finset.mem_compl.mp j.2) (Finset.mem_of_mem_erase hj)
  rw [replaceCoordinate, Finset.card_insert_of_notMem hj,
    Finset.card_erase_of_mem i.2, hI]
  have hq : 0 < q := by
    rw [← hI, Finset.card_pos]
    exact ⟨i.1, i.2⟩
  omega

/-- Replacing `i` by `j` gives an equivalence between the selected coordinates and
the replacement coordinate set. -/
def replaceCoordinateEquiv {n : ℕ} (I : Finset (Fin n)) (i : ↑I)
    (j : ↑(Iᶜ)) : ↑I ≃ ↑(replaceCoordinate I i j) where
  toFun x := if h : x = i then
      ⟨j.1, by simp [replaceCoordinate]⟩
    else ⟨x.1, by simp [replaceCoordinate, h, x.2]⟩
  invFun x := if h : x.1 = j.1 then i else
    ⟨x.1, by
      have hx : x.1 ∈ insert j.1 (I.erase i.1) := x.2
      rw [Finset.mem_insert] at hx
      exact Finset.mem_of_mem_erase (hx.resolve_left h)⟩
  left_inv x := by
    by_cases hxi : x = i
    · subst x
      simp
    · apply Subtype.ext
      have hxj : x.1 ≠ j.1 := by
        intro hxj
        exact (Finset.mem_compl.mp j.2) (by simpa [hxj] using x.2)
      simp [hxi, hxj]
  right_inv x := by
    apply Subtype.ext
    by_cases hxj : x.1 = j.1
    · simp [hxj]
    · have hxi : (⟨x.1, by
          have hx : x.1 ∈ insert j.1 (I.erase i.1) := x.2
          rw [Finset.mem_insert] at hx
          exact Finset.mem_of_mem_erase (hx.resolve_left hxj)⟩ : ↑I) ≠ i := by
        intro h
        have : x.1 = i.1 := congrArg Subtype.val h
        have hxerase : x.1 ∈ I.erase i.1 := by
          have hx : x.1 ∈ insert j.1 (I.erase i.1) := x.2
          exact (Finset.mem_insert.mp hx).resolve_left hxj
        exact (Finset.notMem_erase i.1 I) (this ▸ hxerase)
      simp [hxj, hxi]

@[simp]
lemma replaceCoordinateEquiv_apply_self {n : ℕ} (I : Finset (Fin n))
    (i : ↑I) (j : ↑(Iᶜ)) :
    (replaceCoordinateEquiv I i j i).1 = j.1 := by
  simp [replaceCoordinateEquiv]

lemma replaceCoordinateEquiv_apply_of_ne {n : ℕ} (I : Finset (Fin n))
    (i x : ↑I) (j : ↑(Iᶜ)) (h : x ≠ i) :
    (replaceCoordinateEquiv I i j x).1 = x.1 := by
  simp [replaceCoordinateEquiv, h]

/-- The permutation comparing the direct replacement enumeration with the increasing
enumeration of the replacement coordinate set. -/
def replacementPermutation {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (i : ↑I) (j : ↑(Iᶜ)) : Equiv.Perm (Fin q) :=
  ((I.orderIsoOfFin hI).toEquiv.trans (replaceCoordinateEquiv I i j)).trans
    ((replaceCoordinate I i j).orderIsoOfFin
      (replaceCoordinate_card I hI i j)).symm.toEquiv

lemma replacementPermutation_orderIso_apply {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q)
    (i : ↑I) (j : ↑(Iᶜ)) (k : Fin q) :
    (((replaceCoordinate I i j).orderIsoOfFin
      (replaceCoordinate_card I hI i j))
        (replacementPermutation I hI i j k)).1 =
      (replaceCoordinateEquiv I i j (I.orderIsoOfFin hI k)).1 := by
  simp [replacementPermutation]

/-- The quotient by a coordinate graph, followed by its canonical coordinate
equivalence, sends each selected standard basis vector to the corresponding basis
vector on the selected coordinates. -/
@[simp]
lemma coordinateGraphQuotientEquiv_apply_basis {R : Type u} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (i : ↑I) :
    coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n) i.1)) =
      Pi.basisFun R (↑I) i := by
  let C : Submodule R (Fin n → R) :=
    Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥
  let c : C := ⟨Pi.basisFun R (Fin n) i.1, by
    rw [Submodule.mem_pi]
    intro j hj
    have hji : j ≠ i.1 := by
      intro e
      subst j
      exact (Finset.mem_compl.mp hj) i.2
    simp [Pi.basisFun_apply, hji]⟩
  change coordinateSubmoduleEquiv I
      ((coordinateGraph I a).quotientEquivOfIsCompl C
        (isCompl_coordinateGraph I a) (Submodule.Quotient.mk c.1)) = _
  rw [Submodule.quotientEquivOfIsCompl_apply_mk_right]
  ext j
  change c.1 j.1 = (Pi.basisFun R (↑I) i) j
  dsimp only [c]
  by_cases hij : i = j
  · subst j
    simp
  · have hij' : i.1 ≠ j.1 := fun e ↦ hij (Subtype.ext e)
    simp [hij, hij']

/-- In the quotient by a coordinate graph, an outside standard basis vector is the
negative of the corresponding matrix column in the selected basis. -/
lemma coordinateGraphQuotientEquiv_apply_basis_compl
    {R : Type u} [CommRing R] {n : ℕ}
    (I : Finset (Fin n)) (a : (i : ↑I) → (j : ↑(Iᶜ)) → R)
    (j : ↑(Iᶜ)) :
    coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n) j.1)) =
      fun i ↦ -a i j := by
  classical
  let w : Fin n → R := Pi.basisFun R (Fin n) j.1 +
    ∑ i : ↑I, a i j • Pi.basisFun R (Fin n) i.1
  have hwI (k : ↑I) : w k.1 = a k j := by
    simp only [w, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hkj : k.1 ≠ j.1 := by
      intro h
      exact (Finset.mem_compl.mp j.2) (h ▸ k.2)
    rw [show Pi.basisFun R (Fin n) j.1 k.1 = 0 by simp [hkj], zero_add,
      Finset.sum_eq_single k]
    · simp
    · intro l _ hlk
      have hne : l.1 ≠ k.1 := fun h ↦ hlk (Subtype.ext h)
      simp [hne]
    · simp
  have hwC (l : ↑(Iᶜ)) : w l.1 = if l = j then 1 else 0 := by
    simp only [w, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hzero : ∑ i : ↑I, a i j * Pi.basisFun R (Fin n) i.1 l.1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : i.1 ≠ l.1 := by
        intro h
        exact (Finset.mem_compl.mp l.2) (by simpa [h] using i.2)
      simp [hne]
    rw [hzero, add_zero]
    by_cases hlj : l = j
    · subst l
      simp
    · simp [hlj]
  have hw : w ∈ coordinateGraph I a := by
    rw [mem_coordinateGraph]
    intro k hk
    rw [hwI ⟨k, hk⟩, Finset.sum_eq_single j]
    · rw [hwC]
      simp
    · intro l _ hlj
      rw [hwC]
      simp [hlj]
    · simp
  have hw0 : (coordinateGraph I a).mkQ w = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hw
  have heq := congrArg (coordinateGraphQuotientEquiv I a) hw0
  rw [map_zero] at heq
  simp only [w, map_add, map_sum, map_smul] at heq
  have hsel (k : ↑I) : coordinateGraphQuotientEquiv I a
      ((coordinateGraph I a).mkQ (Pi.basisFun R (Fin n) k.1)) =
      Pi.basisFun R ↑I k := coordinateGraphQuotientEquiv_apply_basis I a k
  simp_rw [hsel] at heq
  funext i
  have hi := congrFun heq i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using eq_neg_of_add_eq_zero_left hi
  · intro k _ hki
    have hne : k ≠ i := hki
    simp [Pi.basisFun_apply, hne]
  · simp

/-- With the direct replacement ordering, the coordinate matrix of the selected
quotient vectors is the identity with one row replaced by the negative graph column. -/
lemma coordinateGraph_replacementMatrix {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (i : ↑I) (j : ↑(Iᶜ)) :
    Matrix.of (fun k l : Fin q ↦
      coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n)
          (replaceCoordinateEquiv I i j (I.orderIsoOfFin hI k)).1))
        (I.orderIsoOfFin hI l)) =
      (1 : Matrix (Fin q) (Fin q) R).updateRow
        ((I.orderIsoOfFin hI).symm i)
        (fun l ↦ -a (I.orderIsoOfFin hI l) j) := by
  classical
  ext k l
  by_cases hki : I.orderIsoOfFin hI k = i
  · have hk : k = (I.orderIsoOfFin hI).symm i := by
      apply (I.orderIsoOfFin hI).injective
      simpa using hki
    subst k
    rw [Matrix.of_apply, Matrix.updateRow_self]
    simp only [(I.orderIsoOfFin hI).apply_symm_apply]
    rw [replaceCoordinateEquiv_apply_self]
    change coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n) j.1))
          (I.orderIsoOfFin hI l) = _
    rw [coordinateGraphQuotientEquiv_apply_basis_compl]
  · have hk : k ≠ (I.orderIsoOfFin hI).symm i := by
      intro hk
      apply hki
      rw [hk, (I.orderIsoOfFin hI).apply_symm_apply]
    rw [Matrix.of_apply, Matrix.updateRow_ne hk]
    rw [replaceCoordinateEquiv_apply_of_ne _ _ _ _ hki]
    change coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n)
          (I.orderIsoOfFin hI k).1)) (I.orderIsoOfFin hI l) = _
    rw [coordinateGraphQuotientEquiv_apply_basis]
    by_cases hkl : k = l
    · subst l
      simp
    · have hne : I.orderIsoOfFin hI k ≠ I.orderIsoOfFin hI l :=
        fun h ↦ hkl ((I.orderIsoOfFin hI).injective h)
      simp [hkl, hne]

/-- The direct one-coordinate replacement minor of a coordinate graph is the
negative of the corresponding graph coefficient. -/
lemma coordinateGraph_replacementMatrix_det {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (i : ↑I) (j : ↑(Iᶜ)) :
    (Matrix.of (fun k l : Fin q ↦
      coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n)
          (replaceCoordinateEquiv I i j (I.orderIsoOfFin hI k)).1))
        (I.orderIsoOfFin hI l))).det = -a i j := by
  rw [coordinateGraph_replacementMatrix, Matrix.det_updateRow_one]
  simp

/-- For a coordinate graph on a `q`-element chart, the top exterior power of its
quotient is canonically identified with the coefficient ring. -/
noncomputable def coordinateGraphTopExteriorEquiv {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    (⋀[R]^q ((Fin n → R) ⧸ coordinateGraph I a)) ≃ₗ[R] R :=
  (coordinateGraphQuotientEquiv I a).exteriorPower q |>.trans
    (topExteriorPiEquiv R I hI)

/-- The distinguished `I`-Plücker basis vector maps to `1` for a point in the
standard coordinate chart `Gr_I`. -/
@[simp]
lemma coordinateGraphTopExteriorEquiv_map_ιMulti_family {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    coordinateGraphTopExteriorEquiv I hI a
      (_root_.exteriorPower.map q (coordinateGraph I a).mkQ
        (exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin n))
          (Set.powersetCard.ofCard hI))) = 1 := by
  rw [_root_.exteriorPower.map_apply_ιMulti_family]
  rw [coordinateGraphTopExteriorEquiv, LinearEquiv.trans_apply]
  change topExteriorPiEquiv R I hI
    (_root_.exteriorPower.map q (coordinateGraphQuotientEquiv I a).toLinearMap
      (exteriorPower.ιMulti_family R q
        ((coordinateGraph I a).mkQ ∘ Pi.basisFun R (Fin n))
        (Set.powersetCard.ofCard hI))) = 1
  rw [_root_.exteriorPower.map_apply_ιMulti_family]
  let sI : Set.powersetCard (Fin n) q := Set.powersetCard.ofCard hI
  let sU : Set.powersetCard (↑I) q :=
    ⟨Finset.univ, by simp [hI]⟩
  have hfamily :
      exteriorPower.ιMulti_family R q
          ((coordinateGraphQuotientEquiv I a) ∘
            (coordinateGraph I a).mkQ ∘ Pi.basisFun R (Fin n)) sI =
        exteriorPower.ιMulti_family R q (Pi.basisFun R (↑I)) sU := by
    unfold exteriorPower.ιMulti_family
    congr 1
    funext k
    let e := Set.powersetCard.ofFinEmbEquiv.symm sI
    have he_mem : e k ∈ I := by
      change e k ∈ sI.val
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem sI (e k)).mp
        ⟨k, rfl⟩
    let x : ↑I := ⟨e k, he_mem⟩
    change coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n) (e k))) =
      Pi.basisFun R (↑I) (Set.powersetCard.ofFinEmbEquiv.symm sU k)
    rw [show e k = x.1 from rfl, coordinateGraphQuotientEquiv_apply_basis]
    congr 1
    apply Subtype.ext
    let ex : Fin q ↪o ↑I :=
      { toFun := fun l ↦ ⟨e l, by
          change e l ∈ sI.val
          exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem sI (e l)).mp
            ⟨l, rfl⟩⟩
        inj' := fun l m hlm ↦ e.injective (congrArg Subtype.val hlm)
        map_rel_iff' := e.map_rel_iff }
    have hex : ex = Finset.univ.orderEmbOfFin sU.property :=
      Finset.orderEmbOfFin_unique' sU.property (fun _ ↦ Finset.mem_univ _)
    exact congrArg (fun f : Fin q ↪o ↑I ↦ (f k).1) hex
  rw [show exteriorPower.ιMulti_family R q
      ((coordinateGraphQuotientEquiv I a).toLinearMap ∘
        (coordinateGraph I a).mkQ ∘ Pi.basisFun R (Fin n))
        (Set.powersetCard.ofCard hI) =
      exteriorPower.ιMulti_family R q (Pi.basisFun R (↑I)) sU by
        simpa [sI] using hfamily]
  rw [← exteriorPower.basis_apply]
  simpa [sU] using topExteriorPiEquiv_apply_basis R I hI

/-- A fixed enumeration of the `q`-element subsets of `Fin n`.  Keeping this
enumeration independent of the coefficient ring is important for the base-change
naturality of Plücker coordinates. -/
noncomputable def powersetCardEquivFin (q n : ℕ) :
    Set.powersetCard (Fin n) q ≃ Fin (n.choose q) :=
  (Fintype.equivFin _).trans (finCongr (by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]))

/-- The Plücker-coordinate number corresponding to a chosen `q`-element subset.
It uses the same coefficient-independent enumeration as `exteriorPowerPiEquiv`. -/
noncomputable def pluckerCoordinate {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) : Fin (n.choose q) :=
  powersetCardEquivFin q n (Set.powersetCard.ofCard hI)

lemma pluckerCoordinate_injective {q n : ℕ} {I J : Finset (Fin n)}
    (hI : I.card = q) (hJ : J.card = q)
    (h : pluckerCoordinate I hI = pluckerCoordinate J hJ) : I = J := by
  exact congrArg Subtype.val ((powersetCardEquivFin q n).injective h)

lemma replaceCoordinate_ne {n : ℕ} (I : Finset (Fin n))
    (i : ↑I) (j : ↑(Iᶜ)) : replaceCoordinate I i j ≠ I := by
  intro h
  have hj : j.1 ∈ replaceCoordinate I i j := by
    simp [replaceCoordinate]
  rw [h] at hj
  exact (Finset.mem_compl.mp j.2) hj

@[simp]
lemma powersetCard_ofCard_orderEmbedding_apply {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q) (k : Fin q) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hI) k =
      (I.orderIsoOfFin hI k).1 := by
  have he : Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard hI) = I.orderEmbOfFin hI := by
    apply Finset.orderEmbOfFin_unique'
    intro l
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.ofCard hI) _).mp ⟨l, rfl⟩
  exact congrArg (fun e : Fin q ↪o Fin n ↦ e k) he

/-- The singleton coordinate set defining the standard target projective-space chart
associated to `I`. -/
noncomputable def pluckerChartIndex {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) : Finset (Fin (n.choose q)) :=
  {pluckerCoordinate I hI}

/-- The distinguished coordinate as an element of its singleton Plücker chart. -/
noncomputable def pluckerChartSelected {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) : ↑(pluckerChartIndex I hI) :=
  ⟨pluckerCoordinate I hI, by simp [pluckerChartIndex]⟩

/-- The replacement Plücker coordinate, regarded as an outside coordinate of the
standard target chart indexed by `I`. -/
noncomputable def pluckerReplacementOutside {q n : ℕ}
    (I : Finset (Fin n)) (hI : I.card = q) (i : ↑I) (j : ↑(Iᶜ)) :
    ↑((pluckerChartIndex I hI)ᶜ) :=
  ⟨pluckerCoordinate (replaceCoordinate I i j)
      (replaceCoordinate_card I hI i j), by
    change pluckerCoordinate (replaceCoordinate I i j)
      (replaceCoordinate_card I hI i j) ∈
        ({pluckerCoordinate I hI} : Finset (Fin (n.choose q)))ᶜ
    rw [Finset.mem_compl, Finset.mem_singleton]
    intro h
    exact replaceCoordinate_ne I i j
      (pluckerCoordinate_injective (replaceCoordinate_card I hI i j) hI h)⟩

@[simp]
lemma pluckerChartIndex_card {q n : ℕ} (I : Finset (Fin n))
    (hI : I.card = q) : (pluckerChartIndex I hI).card = 1 := by
  simp [pluckerChartIndex]

/-- The standard Plücker-coordinate identification
`R^(n choose q) ≃ ⋀^q R^n`, obtained from the exterior-power basis indexed by
`q`-element subsets of `Fin n`. -/
noncomputable def exteriorPowerPiEquiv (R : Type u) [CommRing R] (q n : ℕ) :
    (Fin (n.choose q) → R) ≃ₗ[R] ⋀[R]^q (Fin n → R) :=
  (LinearEquiv.piCongrLeft R (fun _ : Fin (n.choose q) ↦ R)
      (powersetCardEquivFin q n)).symm.trans
    ((Pi.basisFun R (Fin n)).exteriorPower q).equivFun.symm

@[simp]
lemma exteriorPowerPiEquiv_apply_single (R : Type u) [CommRing R] (q n : ℕ)
    (s : Set.powersetCard (Fin n) q) :
    exteriorPowerPiEquiv R q n
      (Pi.single (powersetCardEquivFin q n s) 1) =
        exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin n)) s := by
  classical
  rw [exteriorPowerPiEquiv, LinearEquiv.trans_apply,
    Module.Basis.equivFun_symm_apply]
  have hreindex :
      (LinearEquiv.piCongrLeft R (fun _ : Fin (n.choose q) ↦ R)
        (powersetCardEquivFin q n)).symm
          (Pi.single (powersetCardEquivFin q n s) 1) = Pi.single s 1 := by
    ext t
    change (Pi.single (powersetCardEquivFin q n s) (1 : R) :
      Fin (n.choose q) → R) (powersetCardEquivFin q n t) =
        (Pi.single s (1 : R) : Set.powersetCard (Fin n) q → R) t
    simp [Pi.single_apply, (powersetCardEquivFin q n).injective.eq_iff]
  rw [hreindex]
  simp

/-- The distinguished coordinate vector of the chart indexed by `I` is sent to the
standard exterior basis vector indexed by `I`. -/
@[simp]
lemma exteriorPowerPiEquiv_apply_pluckerCoordinate (R : Type u) [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q) :
    exteriorPowerPiEquiv R q n (Pi.single (pluckerCoordinate I hI) 1) =
      exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin n))
        (Set.powersetCard.ofCard hI) := by
  exact exteriorPowerPiEquiv_apply_single R q n (Set.powersetCard.ofCard hI)

/-- The exterior power of a finite module is finite. -/
theorem Module.Finite.exteriorPower [Module.Finite R M] (k : ℕ) :
    Module.Finite R (⋀[R]^k M) :=
  inferInstance

/-- Let `M` be a finite projective module over a commutative ring. Every exterior power
`⋀^k M` is again projective. (Locally on `Spec R`, `M` is free and the exterior power of
a free module is free.) -/
theorem Module.Projective.exteriorPower [Module.Finite R M] [Module.Projective R M]
    (k : ℕ) : Module.Projective R (⋀[R]^k M) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact Module.Projective.of_split (_root_.exteriorPower.map k g)
    (_root_.exteriorPower.map k f)
    (by rw [← _root_.exteriorPower.map_comp, hfg, _root_.exteriorPower.map_id])

section ExteriorBaseChange

variable (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Coordinatewise scalar extension for a finite product, with an arbitrary finite
index type. -/
noncomputable def piFintypeBaseChangeEquiv (ι : Type v) [Fintype ι] :
    TensorProduct R S (ι → R) ≃ₗ[S] (ι → S) :=
  ((Pi.basisFun R ι).baseChange S).equiv (Pi.basisFun S ι) (Equiv.refl ι)

@[simp]
lemma piFintypeBaseChangeEquiv_basis (ι : Type v) [Fintype ι] (i : ι) :
    piFintypeBaseChangeEquiv R S ι (((Pi.basisFun R ι).baseChange S) i) =
      Pi.basisFun S ι i := by
  rw [piFintypeBaseChangeEquiv]
  exact Module.Basis.equiv_apply _ _ _ _

/-- Scalar extension carries the coordinate summand supported on `I` to the same
coordinate summand over the target ring. -/
noncomputable def coordinateSubmoduleBaseChangeEquiv {n : ℕ}
    (I : Finset (Fin n)) :
    TensorProduct R S
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          (fun _ ↦ (⊥ : Submodule R R))) ≃ₗ[S]
      Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule S S)) :=
  ((coordinateSubmoduleEquiv (R := R) I).baseChange R S).trans
    ((piFintypeBaseChangeEquiv R S ↑I).trans
      (coordinateSubmoduleEquiv (R := S) I).symm)

/-- The standard basis of a coordinate summand, indexed by its selected
coordinates. -/
noncomputable def coordinateSubmoduleBasis (A : Type u) [CommRing A] {n : ℕ}
    (I : Finset (Fin n)) :
    Module.Basis ↑I A
      (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule A A))) :=
  (Pi.basisFun A ↑I).map (coordinateSubmoduleEquiv (R := A) I).symm

@[simp]
lemma coordinateSubmoduleBasis_val (A : Type u) [CommRing A] {n : ℕ}
    (I : Finset (Fin n)) (i : ↑I) :
    (coordinateSubmoduleBasis A I i).1 = Pi.basisFun A (Fin n) i.1 := by
  ext j
  by_cases hj : j ∈ I
  · by_cases hji : j = i.1
    · subst j
      simp [coordinateSubmoduleBasis, coordinateSubmoduleEquiv]
    · have hsub : (⟨j, hj⟩ : ↑I) ≠ i := by
        intro h
        exact hji (congrArg Subtype.val h)
      simp [coordinateSubmoduleBasis, coordinateSubmoduleEquiv,
        Pi.basisFun_apply, hji, hsub]
  · have hji : j ≠ i.1 := by
      intro h
      exact hj (h ▸ i.2)
    simp [coordinateSubmoduleBasis, coordinateSubmoduleEquiv,
      Pi.basisFun_apply, hj, hji]

@[simp]
lemma coordinateSubmoduleBaseChangeEquiv_basis {n : ℕ}
    (I : Finset (Fin n)) (i : ↑I) :
    coordinateSubmoduleBaseChangeEquiv R S I
        (((coordinateSubmoduleBasis R I).baseChange S) i) =
      coordinateSubmoduleBasis S I i := by
  rw [coordinateSubmoduleBaseChangeEquiv, coordinateSubmoduleBasis,
    Module.Basis.baseChange_apply, Module.Basis.map_apply,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply]
  rw [← Module.Basis.baseChange_apply,
    piFintypeBaseChangeEquiv_basis, coordinateSubmoduleBasis,
    Module.Basis.map_apply]

/-- The canonical coordinatewise identification between the scalar extension of a
finite free module and the corresponding finite free module over the target ring. -/
noncomputable def piBaseChangeEquiv (n : ℕ) :
    TensorProduct R S (Fin n → R) ≃ₗ[S] (Fin n → S) :=
  ((Pi.basisFun R (Fin n)).baseChange S).equiv
    (Pi.basisFun S (Fin n)) (Equiv.refl _)

@[simp]
lemma piBaseChangeEquiv_basis (n : ℕ) (i : Fin n) :
    piBaseChangeEquiv R S n (((Pi.basisFun R (Fin n)).baseChange S) i) =
      Pi.basisFun S (Fin n) i := by
  rw [piBaseChangeEquiv]
  exact Module.Basis.equiv_apply _ _ _ _

/-- An `S`-alternating map, viewed as an `R`-alternating map along an algebra `R → S`. -/
def _root_.AlternatingMap.restrictScalarsAlg {P Q : Type*} [AddCommGroup P]
    [AddCommGroup Q] [Module S P] [Module S Q] [Module R P] [Module R Q]
    [IsScalarTower R S P] [IsScalarTower R S Q] {k : ℕ}
    (f : P [⋀^Fin k]→ₗ[S] Q) : P [⋀^Fin k]→ₗ[R] Q where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq'

/-- The natural base-change comparison for exterior powers:
`S ⊗ ⋀^k_R N → ⋀^k_S (S ⊗ N)`, sending `1 ⊗ (v₁ ∧ ⋯ ∧ v_k)` to
`(1 ⊗ v₁) ∧ ⋯ ∧ (1 ⊗ v_k)`. -/
noncomputable def exteriorPowerBaseChange (k : ℕ) :
    TensorProduct R S (⋀[R]^k N) →ₗ[S] ⋀[S]^k (TensorProduct R S N) :=
  (exteriorPower.alternatingMapLinearEquiv
    (((exteriorPower.ιMulti S k (M := TensorProduct R S N)).restrictScalarsAlg
      R S).compLinearMap (TensorProduct.mk R S N 1))).liftBaseChange S

@[simp]
lemma exteriorPowerBaseChange_tmul_ιMulti (k : ℕ) (s : S) (v : Fin k → N) :
    exteriorPowerBaseChange R S k (s ⊗ₜ[R] exteriorPower.ιMulti R k v) =
      s • exteriorPower.ιMulti S k (fun i ↦ (1 : S) ⊗ₜ[R] v i) := by
  rw [exteriorPowerBaseChange, LinearMap.liftBaseChange_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

variable {R S} in
/-- Naturality of the exterior-power base-change comparison. -/
lemma exteriorPowerBaseChange_naturality {N' : Type*} [AddCommGroup N'] [Module R N']
    (k : ℕ) (f : N →ₗ[R] N') :
    exteriorPowerBaseChange R S k ∘ₗ (exteriorPower.map k f).baseChange S =
      exteriorPower.map k (f.baseChange S) ∘ₗ exteriorPowerBaseChange R S k := by
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro s x
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R k (M := N))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti,
      exteriorPowerBaseChange_tmul_ιMulti, map_smul]
    congr 1
  | zero =>
    simp [TensorProduct.tmul_zero]
  | add y z _ _ ihy ihz =>
    simp only [TensorProduct.tmul_add, map_add] at ihy ihz ⊢
    rw [ihy, ihz]
  | smul r y _ ih =>
    simp only [TensorProduct.tmul_smul, map_smul] at ih ⊢
    rw [ih]

variable {R S} in
/-- On the standard exterior-power basis, the base-change comparison sends the
base-changed basis vector to the exterior basis of the base-changed standard basis. -/
lemma exteriorPowerBaseChange_basis (k n : ℕ)
    (s : Set.powersetCard (Fin n) k) :
    exteriorPowerBaseChange R S k
      ((((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S) s) =
      (((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k) s := by
  rw [Module.Basis.baseChange_apply, exteriorPower.basis_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPowerBaseChange_tmul_ιMulti, one_smul]
  congr 1
  funext i
  rw [Function.comp_apply, Function.comp_apply, Module.Basis.baseChange_apply]

variable {R S} in
/-- The exterior power of the coordinatewise finite-free base-change equivalence sends
the exterior basis of the base-changed standard basis to the standard exterior basis. -/
lemma exteriorPower_map_piBaseChangeEquiv_basis (k n : ℕ)
    (s : Set.powersetCard (Fin n) k) :
    exteriorPower.map k (piBaseChangeEquiv R S n).toLinearMap
      ((((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k) s) =
      ((Pi.basisFun S (Fin n)).exteriorPower k) s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact piBaseChangeEquiv_basis R S n _

variable {R S} in
/-- Inverse form of `exteriorPower_map_piBaseChangeEquiv_basis`. -/
lemma exteriorPower_map_piBaseChangeEquiv_symm_basis (k n : ℕ)
    (s : Set.powersetCard (Fin n) k) :
    exteriorPower.map k (piBaseChangeEquiv R S n).symm.toLinearMap
      (((Pi.basisFun S (Fin n)).exteriorPower k) s) =
      (((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k) s := by
  have hcomp : (piBaseChangeEquiv R S n).symm.toLinearMap.comp
      (piBaseChangeEquiv R S n).toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [← exteriorPower_map_piBaseChangeEquiv_basis (R := R) (S := S) k n s,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp, hcomp,
    exteriorPower.map_id, LinearMap.id_apply]

variable {R S} in
/-- The standard-coordinate identification of a free exterior power commutes with
extension of scalars. This is the coordinate square needed for base-change naturality
of the affine Plücker map. -/
lemma exteriorPowerPiEquiv_baseChange (k n : ℕ) :
    (exteriorPowerBaseChange R S k (N := Fin n → R)).comp
        (LinearMap.baseChange S
          ((exteriorPowerPiEquiv R k n).toLinearMap :
            (Fin (n.choose k) → R) →ₗ[R] ⋀[R]^k (Fin n → R))) =
      (exteriorPower.map k (piBaseChangeEquiv R S n).symm.toLinearMap).comp
        ((exteriorPowerPiEquiv S k n).toLinearMap.comp
          (piBaseChangeEquiv R S (n.choose k)).toLinearMap) := by
  classical
  apply Module.Basis.ext ((Pi.basisFun R (Fin (n.choose k))).baseChange S)
  intro i
  let s : Set.powersetCard (Fin n) k := (powersetCardEquivFin k n).symm i
  have his : powersetCardEquivFin k n s = i :=
    (powersetCardEquivFin k n).apply_symm_apply i
  change exteriorPowerBaseChange R S k
      ((exteriorPowerPiEquiv R k n).toLinearMap.baseChange S
    (((Pi.basisFun R (Fin (n.choose k))).baseChange S) i)) = _
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    show Pi.basisFun R (Fin (n.choose k)) i =
      Pi.single (powersetCardEquivFin k n s) 1 by
        rw [Pi.basisFun_apply, his],
    show (exteriorPowerPiEquiv R k n).toLinearMap
        (Pi.single (powersetCardEquivFin k n s) 1) =
          exteriorPower.ιMulti_family R k (Pi.basisFun R (Fin n)) s from
      exteriorPowerPiEquiv_apply_single R k n s,
    show (1 : S) ⊗ₜ[R]
        exteriorPower.ιMulti_family R k (Pi.basisFun R (Fin n)) s =
      (((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S) s by
        rw [Module.Basis.baseChange_apply, exteriorPower.basis_apply],
    exteriorPowerBaseChange_basis,
    show (1 : S) ⊗ₜ[R] Pi.single (powersetCardEquivFin k n s) 1 =
      ((Pi.basisFun R (Fin (n.choose k))).baseChange S) i by
        rw [Module.Basis.baseChange_apply, Pi.basisFun_apply, his],
    LinearMap.comp_apply, LinearMap.comp_apply,
    show (piBaseChangeEquiv R S (n.choose k)).toLinearMap
        (((Pi.basisFun R (Fin (n.choose k))).baseChange S) i) =
          Pi.basisFun S (Fin (n.choose k)) i from
      piBaseChangeEquiv_basis R S (n.choose k) i,
    show Pi.basisFun S (Fin (n.choose k)) i =
      Pi.single (powersetCardEquivFin k n s) 1 by
        rw [Pi.basisFun_apply, his],
    show (exteriorPowerPiEquiv S k n).toLinearMap
        (Pi.single (powersetCardEquivFin k n s) 1) =
          exteriorPower.ιMulti_family S k (Pi.basisFun S (Fin n)) s from
      exteriorPowerPiEquiv_apply_single S k n s,
    show exteriorPower.ιMulti_family S k (Pi.basisFun S (Fin n)) s =
      ((Pi.basisFun S (Fin n)).exteriorPower k) s by
        rw [exteriorPower.basis_apply],
    exteriorPower_map_piBaseChangeEquiv_symm_basis]

variable {R S} in
/-- Inverse-coordinate form of `exteriorPowerPiEquiv_baseChange`. -/
lemma exteriorPowerPiEquiv_baseChange_inv (k n : ℕ) :
    (exteriorPower.map k (piBaseChangeEquiv R S n).symm.toLinearMap).comp
        (exteriorPowerPiEquiv S k n).toLinearMap =
      (exteriorPowerBaseChange R S k (N := Fin n → R)).comp
        ((LinearMap.baseChange S
          ((exteriorPowerPiEquiv R k n).toLinearMap :
            (Fin (n.choose k) → R) →ₗ[R] ⋀[R]^k (Fin n → R))).comp
          (piBaseChangeEquiv R S (n.choose k)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (exteriorPowerPiEquiv_baseChange (R := R) (S := S) k n)
    ((piBaseChangeEquiv R S (n.choose k)).symm x)
  simp only [LinearMap.comp_apply] at h ⊢
  rw [show (piBaseChangeEquiv R S (n.choose k)).toLinearMap
      ((piBaseChangeEquiv R S (n.choose k)).symm x) = x by simp] at h
  exact h.symm

/-- The quotient map defining scalar extension of a kernel-model Grassmannian point in
standard coordinates. -/
noncomputable def grassmannianPiBaseChangeLinearMap (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    (Fin n → S) →ₗ[S] TensorProduct R S ((Fin n → R) ⧸ N.toSubmodule) :=
  N.toSubmodule.mkQ.baseChange S ∘ₗ (piBaseChangeEquiv R S n).symm.toLinearMap

lemma grassmannianPiBaseChangeLinearMap_surjective (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    Function.Surjective (grassmannianPiBaseChangeLinearMap R S n N) :=
  (LinearMap.baseChange_surjective S (Submodule.mkQ_surjective N.toSubmodule)).comp
    (piBaseChangeEquiv R S n).symm.surjective

/-- The basis-defined presentation used by `Module.Grassmannian.baseChangePi` agrees
with the coordinatewise base-change presentation used by the sheaf pullback API. -/
lemma grassmannianPiBaseChangeLinearMap_eq_baseChangePi (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    grassmannianPiBaseChangeLinearMap R S n N =
      LinearMap.baseChangePi S N.toSubmodule.mkQ := by
  apply (Pi.basisFun S (Fin n)).ext
  intro i
  have hb : (piBaseChangeEquiv R S n).symm (Pi.basisFun S (Fin n) i) =
      ((Pi.basisFun R (Fin n)).baseChange S) i := by
    apply (piBaseChangeEquiv R S n).injective
    rw [LinearEquiv.apply_symm_apply, piBaseChangeEquiv_basis]
  rw [grassmannianPiBaseChangeLinearMap, LinearMap.comp_apply]
  change N.toSubmodule.mkQ.baseChange S
      ((piBaseChangeEquiv R S n).symm (Pi.basisFun S (Fin n) i)) = _
  rw [hb,
    Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    LinearMap.baseChangePi]
  simp [Pi.basisFun_apply]

/-- Scalar extension of a kernel-model Grassmannian point in standard coordinates.
The kernel is taken after identifying `S ⊗ R^n` with `S^n`. -/
noncomputable def Module.Grassmannian.baseChangePi (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    Module.Grassmannian S (Fin n → S) q := by
  let φ := grassmannianPiBaseChangeLinearMap R S n N
  have hφ : Function.Surjective φ :=
    grassmannianPiBaseChangeLinearMap_surjective R S n N
  let e : ((Fin n → S) ⧸ LinearMap.ker φ) ≃ₗ[S]
      TensorProduct R S ((Fin n → R) ⧸ N.toSubmodule) :=
    φ.quotKerEquivOfSurjective hφ
  exact
    { toSubmodule := LinearMap.ker φ
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq := fun p ↦ by
        rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p,
          Module.rankAtStalk_baseChange, N.rankAtStalk_eq] }

@[simp]
lemma Module.Grassmannian.baseChangePi_toSubmodule (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    (N.baseChangePi R S n).toSubmodule =
      LinearMap.ker (grassmannianPiBaseChangeLinearMap R S n N) := rfl

/-- The quotient underlying `baseChangePi` is canonically the scalar extension of the
original quotient. -/
noncomputable def Module.Grassmannian.baseChangePiQuotientEquiv (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    ((Fin n → S) ⧸ (N.baseChangePi R S n).toSubmodule) ≃ₗ[S]
      TensorProduct R S ((Fin n → R) ⧸ N.toSubmodule) :=
  (grassmannianPiBaseChangeLinearMap R S n N).quotKerEquivOfSurjective
    (grassmannianPiBaseChangeLinearMap_surjective R S n N)

lemma Module.Grassmannian.baseChangePiQuotientEquiv_comp_mkQ (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q) :
    (N.baseChangePiQuotientEquiv R S n).toLinearMap.comp
        (N.baseChangePi R S n).toSubmodule.mkQ =
      grassmannianPiBaseChangeLinearMap R S n N := by
  apply LinearMap.ext
  intro x
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (grassmannianPiBaseChangeLinearMap R S n N)
    (grassmannianPiBaseChangeLinearMap_surjective R S n N) x

/-- The selected-coordinate quotient map commutes with scalar extension, after the
canonical identifications of its coordinate summand and quotient. -/
lemma Module.Grassmannian.coordinateToQuotient_baseChange (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q)
    (I : Finset (Fin n)) :
    (N.baseChangePiQuotientEquiv R S n).toLinearMap.comp
        (coordinateToQuotient I (N.baseChangePi R S n).toSubmodule) =
      (LinearMap.baseChange S (coordinateToQuotient I N.toSubmodule)).comp
        (coordinateSubmoduleBaseChangeEquiv R S I).symm.toLinearMap := by
  apply (coordinateSubmoduleBasis S I).ext
  intro i
  simp only [LinearMap.comp_apply]
  have hinv : (coordinateSubmoduleBaseChangeEquiv R S I).symm
      (coordinateSubmoduleBasis S I i) =
      (coordinateSubmoduleBasis R I).baseChange S i := by
    apply (coordinateSubmoduleBaseChangeEquiv R S I).injective
    rw [LinearEquiv.apply_symm_apply,
      coordinateSubmoduleBaseChangeEquiv_basis]
  change _ = (LinearMap.baseChange S
    (coordinateToQuotient I N.toSubmodule))
      ((coordinateSubmoduleBaseChangeEquiv R S I).symm
        (coordinateSubmoduleBasis S I i))
  rw [hinv, Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul]
  change (N.baseChangePiQuotientEquiv R S n)
      ((N.baseChangePi R S n).toSubmodule.mkQ
        (coordinateSubmoduleBasis S I i).1) =
    1 ⊗ₜ[R] N.toSubmodule.mkQ (coordinateSubmoduleBasis R I i).1
  rw [show (N.baseChangePiQuotientEquiv R S n)
      ((N.baseChangePi R S n).toSubmodule.mkQ
        (coordinateSubmoduleBasis S I i).1) =
      grassmannianPiBaseChangeLinearMap R S n N
        (coordinateSubmoduleBasis S I i).1 by
      exact LinearMap.congr_fun
        (N.baseChangePiQuotientEquiv_comp_mkQ R S n) _]
  rw [grassmannianPiBaseChangeLinearMap, LinearMap.comp_apply,
    coordinateSubmoduleBasis_val]
  have hb : (piBaseChangeEquiv R S n).symm
      (Pi.basisFun S (Fin n) i.1) =
      ((Pi.basisFun R (Fin n)).baseChange S) i.1 := by
    apply (piBaseChangeEquiv R S n).injective
    rw [LinearEquiv.apply_symm_apply, piBaseChangeEquiv_basis]
  change N.toSubmodule.mkQ.baseChange S
      ((piBaseChangeEquiv R S n).symm
        (Pi.basisFun S (Fin n) i.1)) = _
  rw [hb, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    coordinateSubmoduleBasis_val]

/-- Surjectivity of the selected-coordinate map after base change is equivalent to
surjectivity of the scalar extension of the original coordinate map. -/
lemma Module.Grassmannian.coordinateToQuotient_baseChange_surjective_iff (n : ℕ)
    {q : ℕ} (N : Module.Grassmannian R (Fin n → R) q)
    (I : Finset (Fin n)) :
    Function.Surjective
        (coordinateToQuotient I (N.baseChangePi R S n).toSubmodule) ↔
      Function.Surjective
        (LinearMap.baseChange S (coordinateToQuotient I N.toSubmodule)) := by
  let eC := coordinateSubmoduleBaseChangeEquiv R S I
  let eQ := N.baseChangePiQuotientEquiv R S n
  have hcomm := N.coordinateToQuotient_baseChange R S n I
  constructor
  · intro h z
    obtain ⟨c, hc⟩ := h (eQ.symm z)
    refine ⟨eC.symm c, ?_⟩
    have h := LinearMap.congr_fun hcomm c
    simp only [LinearMap.comp_apply] at h
    rw [hc] at h
    dsimp [eQ, eC] at h ⊢
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · intro h z
    obtain ⟨d, hd⟩ := h (eQ z)
    refine ⟨eC d, ?_⟩
    have hc := LinearMap.congr_fun hcomm (eC d)
    simp only [LinearMap.comp_apply] at hc
    dsimp [eQ, eC] at hc hd ⊢
    simp only [LinearEquiv.symm_apply_apply] at hc
    rw [hd] at hc
    exact (N.baseChangePiQuotientEquiv R S n).injective hc

/-- After scalar extension, quotienting by the kernel of a surjective linear map has
the same kernel as the scalar extension of that map. -/
lemma LinearMap.ker_mkQ_baseChange_eq_ker_baseChange
    {M' N' : Type u} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M' →ₗ[R] N')
    (hf : Function.Surjective f) :
    LinearMap.ker ((LinearMap.ker f).mkQ.baseChange S) =
      LinearMap.ker (f.baseChange S) := by
  let e : (M' ⧸ LinearMap.ker f) ≃ₗ[R] N' := f.quotKerEquivOfSurjective hf
  have hfac : e.toLinearMap.comp (LinearMap.ker f).mkQ = f := by
    ext m
    exact LinearMap.quotKerEquivOfSurjective_apply_mk f hf m
  have hfacBC := congrArg (LinearMap.baseChange S) hfac
  rw [LinearMap.baseChange_comp] at hfacBC
  ext z
  change (LinearMap.ker f).mkQ.baseChange S z = 0 ↔ f.baseChange S z = 0
  rw [← LinearMap.congr_fun hfacBC z]
  exact (e.baseChange R S _ _).map_eq_zero_iff.symm

variable {R S} in
/-- The exterior-power base-change comparison is bijective for finite free modules:
it matches the exterior-power bases on both sides. -/
lemma exteriorPowerBaseChange_bijective_free (k n : ℕ) :
    Function.Bijective (exteriorPowerBaseChange R S k (N := Fin n → R)) := by
  classical
  have hφ : ∀ s, exteriorPowerBaseChange R S k
      ((((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S) s) =
      (((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k) s := by
    exact exteriorPowerBaseChange_basis k n
  have heq : exteriorPowerBaseChange R S k (N := Fin n → R) =
      ((((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S).equiv
        (((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k)
        (Equiv.refl _)).toLinearMap := by
    refine Module.Basis.ext (((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S)
      fun s ↦ ?_
    refine (hφ s).trans ?_
    exact (Module.Basis.equiv_apply
      (b := (((Pi.basisFun R (Fin n)).exteriorPower k).baseChange S))
      (b' := (((Pi.basisFun R (Fin n)).baseChange S).exteriorPower k))
      (i := s) (e := Equiv.refl _)).symm
  rw [heq]
  exact (Module.Basis.equiv _ _ _).bijective

variable {R S} in
/-- The exterior-power base-change comparison is bijective for finite projective
modules: the finite free case transfers along a retract. -/
lemma exteriorPowerBaseChange_bijective (k : ℕ) [Module.Finite R N]
    [Module.Projective R N] :
    Function.Bijective (exteriorPowerBaseChange R S k (N := N)) := by
  obtain ⟨n, u, w, -, -, huw⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  have hnat_w := exteriorPowerBaseChange_naturality (S := S) k w
  have hnat_u := exteriorPowerBaseChange_naturality (S := S) k u
  have hfree := exteriorPowerBaseChange_bijective_free (R := R) (S := S) k n
  have hretract : ∀ z : TensorProduct R S (⋀[R]^k N),
      ((exteriorPower.map k u).baseChange S)
        (((exteriorPower.map k w).baseChange S) z) = z := by
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← exteriorPower.map_comp,
      huw, exteriorPower.map_id, LinearMap.baseChange_id, LinearMap.id_apply]
  have hretract' : ∀ z : ⋀[S]^k (TensorProduct R S N),
      exteriorPower.map k (u.baseChange S)
        (exteriorPower.map k (w.baseChange S) z) = z := by
    intro z
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, ← LinearMap.baseChange_comp,
      huw, LinearMap.baseChange_id, exteriorPower.map_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    have h2 : ((exteriorPower.map k w).baseChange S) x =
        ((exteriorPower.map k w).baseChange S) y := by
      apply hfree.injective
      have hx := LinearMap.congr_fun hnat_w x
      have hy := LinearMap.congr_fun hnat_w y
      simp only [LinearMap.coe_comp, Function.comp_apply] at hx hy
      rw [hx, hy, hxy]
    have h3 := congrArg ((exteriorPower.map k u).baseChange S) h2
    rwa [hretract, hretract] at h3
  · intro z
    obtain ⟨w', hw'⟩ := hfree.surjective (exteriorPower.map k (w.baseChange S) z)
    refine ⟨((exteriorPower.map k u).baseChange S) w', ?_⟩
    have h5 := LinearMap.congr_fun hnat_u w'
    simp only [LinearMap.coe_comp, Function.comp_apply] at h5
    rw [h5, hw']
    exact hretract' z

end ExteriorBaseChange

/-- Let `M` be a finite projective module over a commutative ring. The rank of `⋀^k M` at
a prime `p` is the binomial coefficient `C(rank_p M, k)`. -/
theorem Module.rankAtStalk_exteriorPower [Module.Finite R M] [Module.Projective R M]
    (k : ℕ) (p : PrimeSpectrum R) :
    Module.rankAtStalk (⋀[R]^k M) p = (Module.rankAtStalk M p).choose k := by
  classical
  have e₁ : LocalizedModule p.asIdeal.primeCompl (⋀[R]^k M) ≃ₗ[Localization.AtPrime p.asIdeal]
      TensorProduct R (Localization.AtPrime p.asIdeal) (⋀[R]^k M) :=
    ((IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (⋀[R]^k M))).equiv).symm
  have e₂ : TensorProduct R (Localization.AtPrime p.asIdeal) (⋀[R]^k M)
      ≃ₗ[Localization.AtPrime p.asIdeal]
      ⋀[Localization.AtPrime p.asIdeal]^k
        (TensorProduct R (Localization.AtPrime p.asIdeal) M) :=
    LinearEquiv.ofBijective _
      (exteriorPowerBaseChange_bijective (S := Localization.AtPrime p.asIdeal) k)
  have e₃ : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      TensorProduct R (Localization.AtPrime p.asIdeal) M :=
    ((IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).equiv).symm
  haveI : Module.Finite (Localization.AtPrime p.asIdeal)
      (TensorProduct R (Localization.AtPrime p.asIdeal) M) :=
    Module.Finite.base_change R _ M
  haveI : Module.Free (Localization.AtPrime p.asIdeal)
      (TensorProduct R (Localization.AtPrime p.asIdeal) M) :=
    Module.free_of_flat_of_isLocalRing
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl (⋀[R]^k M)) = _
  rw [(e₁.trans e₂).finrank_eq, exteriorPower.finrank_eq]
  congr 1
  exact e₃.symm.finrank_eq

/-- The affine Plücker quotient map associated to a submodule `N ⊆ R^n`:
`R^(n choose q) ≃ ⋀^q R^n → ⋀^q (R^n/N)`. -/
noncomputable def pluckerLinearMap (R : Type u) [CommRing R] (q n : ℕ)
    (N : Submodule R (Fin n → R)) :
    (Fin (n.choose q) → R) →ₗ[R] ⋀[R]^q ((Fin n → R) ⧸ N) :=
  (exteriorPower.map q N.mkQ).comp (exteriorPowerPiEquiv R q n).toLinearMap

/-- The distinguished Plücker coordinate is the exterior product of the selected
quotient vectors. -/
lemma pluckerLinearMap_apply_pluckerCoordinate {K : Type u} [Field K]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (W : Submodule K (Fin n → K)) :
    pluckerLinearMap K q n W (Pi.single (pluckerCoordinate I hI) 1) =
      exteriorPower.ιMulti K q (fun j ↦ W.mkQ
        (Pi.basisFun K (Fin n)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofCard hI) j))) := by
  rw [pluckerLinearMap, LinearMap.comp_apply]
  change (exteriorPower.map q W.mkQ)
    (exteriorPowerPiEquiv K q n
      (Pi.single (pluckerCoordinate I hI) 1)) = _
  rw [exteriorPowerPiEquiv_apply_pluckerCoordinate,
    _root_.exteriorPower.map_apply_ιMulti_family]
  rfl

lemma pluckerLinearMap_surjective (R : Type u) [CommRing R] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    Function.Surjective (pluckerLinearMap R q n N.toSubmodule) :=
  (exteriorPower.map_surjective (Submodule.mkQ_surjective N.toSubmodule)).comp
    (exteriorPowerPiEquiv R q n).surjective

/-- **The Plücker kernel is the kernel of the exterior power of any presentation**: for a
surjection `φ : R^n ↠ N`, the kernel of `⋀^q φ` composed with the Plücker basis
identification is the Plücker kernel of `ker φ`.  (`pluckerLinearMap` is by definition the
case `φ = mkQ`; the general case follows because the two differ by an isomorphism.) -/
lemma ker_exteriorPower_map_comp_exteriorPowerPiEquiv (R : Type u) [CommRing R] (q n : ℕ)
    {N : Type u} [AddCommGroup N] [Module R N] (φ : (Fin n → R) →ₗ[R] N)
    (hφ : Function.Surjective φ) :
    LinearMap.ker ((_root_.exteriorPower.map q φ).comp
        (exteriorPowerPiEquiv R q n).toLinearMap) =
      LinearMap.ker (pluckerLinearMap R q n (LinearMap.ker φ)) := by
  have hfac : φ = (φ.quotKerEquivOfSurjective hφ).toLinearMap.comp
      (LinearMap.ker φ).mkQ := by
    apply LinearMap.ext
    intro x
    exact (LinearMap.quotKerEquivOfSurjective_apply_mk φ hφ x).symm
  have hmap : _root_.exteriorPower.map q φ =
      (_root_.exteriorPower.map q (φ.quotKerEquivOfSurjective hφ).toLinearMap).comp
        (_root_.exteriorPower.map q (LinearMap.ker φ).mkQ) := by
    rw [← _root_.exteriorPower.map_comp, ← hfac]
  have hinj : Function.Injective
      (_root_.exteriorPower.map q (φ.quotKerEquivOfSurjective hφ).toLinearMap) :=
    ((φ.quotKerEquivOfSurjective hφ).exteriorPower q).injective
  apply le_antisymm
  · intro x hx
    have hx' : (_root_.exteriorPower.map q φ)
        (exteriorPowerPiEquiv R q n x) = 0 := hx
    rw [hmap] at hx'
    have h0 : (_root_.exteriorPower.map q (LinearMap.ker φ).mkQ)
        (exteriorPowerPiEquiv R q n x) = 0 :=
      hinj (by simpa using hx')
    exact h0
  · intro x hx
    have hx' : (_root_.exteriorPower.map q (LinearMap.ker φ).mkQ)
        (exteriorPowerPiEquiv R q n x) = 0 := hx
    show (_root_.exteriorPower.map q φ) (exteriorPowerPiEquiv R q n x) = 0
    rw [hmap]
    change (_root_.exteriorPower.map q (φ.quotKerEquivOfSurjective hφ).toLinearMap)
      ((_root_.exteriorPower.map q (LinearMap.ker φ).mkQ)
        (exteriorPowerPiEquiv R q n x)) = 0
    rw [hx', map_zero]

/-- Over a field, membership of the Plücker point in its standard chart forces the
selected quotient vectors to be linearly independent. -/
lemma Module.Grassmannian.linearIndependent_selected_of_plucker_isCompl
    {K : Type u} [Field K] {q n : ℕ}
    (N : Module.Grassmannian K (Fin n → K) q)
    (I : Finset (Fin n)) (hI : I.card = q)
    (hplucker : IsCompl
      (LinearMap.ker (pluckerLinearMap K q n N.toSubmodule))
      (Submodule.pi
        (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
          Set (Fin (n.choose q))) fun _ ↦ ⊥)) :
    LinearIndependent K (fun j ↦ N.toSubmodule.mkQ
      (Pi.basisFun K (Fin n)
        (Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofCard hI) j))) := by
  letI : Module.Finite K ((Fin n → K) ⧸ N.toSubmodule) := N.finite_quotient
  letI : Module.Projective K ((Fin n → K) ⧸ N.toSubmodule) := N.projective_quotient
  have hdim : Module.finrank K ((Fin n → K) ⧸ N.toSubmodule) = q := by
    let p : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    simpa [Module.rankAtStalk_eq_finrank_of_free] using N.rankAtStalk_eq p
  apply linearIndependent_of_exteriorPower_ιMulti_ne_zero_of_finrank_eq q _ hdim
  rw [← pluckerLinearMap_apply_pluckerCoordinate I hI N.toSubmodule]
  intro hz
  let e : Fin (n.choose q) → K := Pi.single (pluckerCoordinate I hI) 1
  have heker : e ∈ LinearMap.ker
      (pluckerLinearMap K q n N.toSubmodule) := by
    rw [LinearMap.mem_ker]
    exact hz
  have hecoord : e ∈ Submodule.pi
      (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
        Set (Fin (n.choose q))) (fun _ ↦ (⊥ : Submodule K K)) := by
    rw [Submodule.mem_pi]
    intro j hj
    rw [Submodule.mem_bot]
    have hjne : pluckerCoordinate I hI ≠ j := by
      intro h
      subst j
      exact (Finset.mem_compl.mp hj) (by simp [pluckerChartIndex])
    simp [e, hjne]
  have hezero : e = 0 :=
    Submodule.disjoint_def.mp hplucker.disjoint e heker hecoord
  have := congrFun hezero (pluckerCoordinate I hI)
  simp [e] at this

/-- Over a field, the standard-chart condition for the Plücker point implies the
corresponding standard-chart condition for the original Grassmannian point. -/
lemma Module.Grassmannian.isCompl_of_plucker_isCompl
    {K : Type u} [Field K] {q n : ℕ}
    (N : Module.Grassmannian K (Fin n → K) q)
    (I : Finset (Fin n)) (hI : I.card = q)
    (hplucker : IsCompl
      (LinearMap.ker (pluckerLinearMap K q n N.toSubmodule))
      (Submodule.pi
        (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
          Set (Fin (n.choose q))) fun _ ↦ ⊥)) :
    IsCompl N.toSubmodule
      (Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n)) fun _ ↦ ⊥) := by
  letI : Module.Finite K ((Fin n → K) ⧸ N.toSubmodule) := N.finite_quotient
  letI : Module.Projective K ((Fin n → K) ⧸ N.toSubmodule) := N.projective_quotient
  have hdim : Module.finrank K ((Fin n → K) ⧸ N.toSubmodule) = q := by
    let p : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    simpa [Module.rankAtStalk_eq_finrank_of_free] using N.rankAtStalk_eq p
  let v : Fin q → ((Fin n → K) ⧸ N.toSubmodule) := fun j ↦
    N.toSubmodule.mkQ (Pi.basisFun K (Fin n)
      (Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard hI) j))
  have hv : LinearIndependent K v :=
    N.linearIndependent_selected_of_plucker_isCompl I hI hplucker
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hrange : LinearMap.range (coordinateToQuotient I N.toSubmodule) = ⊤ := by
    apply top_unique
    rw [← hspan, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    let i : Fin n := Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard hI) j
    have hi : i ∈ I := by
      exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        (Set.powersetCard.ofCard hI) i |>.mp ⟨j, rfl⟩
    let c : Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule K K)) := ⟨Pi.basisFun K (Fin n) i, by
      rw [Submodule.mem_pi]
      intro k hk
      rw [Submodule.mem_bot]
      have hik : i ≠ k := by
        intro hik
        subst k
        exact (Finset.mem_compl.mp hk) hi
      simp [hik]⟩
    refine ⟨c, ?_⟩
    rfl
  have hcodisjoint : Codisjoint N.toSubmodule
      (Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n)) fun _ ↦ ⊥) := by
    rw [codisjoint_iff_le_sup]
    have hmap : (Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule K K))).map N.toSubmodule.mkQ = ⊤ := by
      rw [← coordinateToQuotient_range]
      exact hrange
    have hsup := (Submodule.map_mkQ_eq_top
      (p := N.toSubmodule)
      (p' := Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n))
        (fun _ ↦ (⊥ : Submodule K K)))).mp hmap
    rw [hsup]
  exact isCompl_of_codisjoint_of_quotient_projective_rank I N.toSubmodule hI
    N.projective_quotient N.rankAtStalk_eq hcodisjoint

/-- On the standard graph chart `Gr_I`, the distinguished `I`-Plücker coordinate
is normalized to `1` after the canonical trivialization of the determinant line. -/
@[simp]
lemma coordinateGraph_pluckerLinearMap_single {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    coordinateGraphTopExteriorEquiv I hI a
      (pluckerLinearMap R q n (coordinateGraph I a)
        (Pi.single (pluckerCoordinate I hI) 1)) = 1 := by
  rw [pluckerLinearMap, LinearMap.comp_apply,
    show (exteriorPowerPiEquiv R q n).toLinearMap
        (Pi.single (pluckerCoordinate I hI) 1) =
      exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin n))
        (Set.powersetCard.ofCard hI) by
      exact exteriorPowerPiEquiv_apply_pluckerCoordinate R I hI]
  exact coordinateGraphTopExteriorEquiv_map_ιMulti_family I hI a

/-- A Plücker coordinate obtained by replacing `i ∈ I` by `j ∉ I` recovers,
up to the explicit ordering sign, the negative graph coefficient `a i j`. -/
lemma coordinateGraph_pluckerLinearMap_replacement {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (i : ↑I) (j : ↑(Iᶜ)) :
    (replacementPermutation I hI i j).sign •
        coordinateGraphTopExteriorEquiv I hI a
          (pluckerLinearMap R q n (coordinateGraph I a)
            (Pi.single (pluckerCoordinate (replaceCoordinate I i j)
              (replaceCoordinate_card I hI i j)) 1)) = -a i j := by
  classical
  let J := replaceCoordinate I i j
  let hJ := replaceCoordinate_card I hI i j
  let p := replacementPermutation I hI i j
  let B : Matrix (Fin q) (Fin q) R := Matrix.of fun k l ↦
    coordinateGraphQuotientEquiv I a
      (Submodule.Quotient.mk (Pi.basisFun R (Fin n)
        ((J.orderIsoOfFin hJ) k).1))
      (I.orderIsoOfFin hI l)
  have hmatrix : Matrix.of (fun k l : Fin q ↦
      coordinateGraphQuotientEquiv I a
        (Submodule.Quotient.mk (Pi.basisFun R (Fin n)
          (replaceCoordinateEquiv I i j (I.orderIsoOfFin hI k)).1))
        (I.orderIsoOfFin hI l)) = B.submatrix p id := by
    ext k l
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, B, p, J]
    rw [replacementPermutation_orderIso_apply]
  have hdet : p.sign • B.det = -a i j := by
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_eq_mul,
      ← Matrix.det_permute, ← hmatrix]
    exact coordinateGraph_replacementMatrix_det I hI a i j
  rw [pluckerLinearMap, LinearMap.comp_apply,
    show (exteriorPowerPiEquiv R q n).toLinearMap
        (Pi.single (pluckerCoordinate J hJ) 1) =
      exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin n))
        (Set.powersetCard.ofCard hJ) by
      exact exteriorPowerPiEquiv_apply_pluckerCoordinate R J hJ,
    _root_.exteriorPower.map_apply_ιMulti_family,
    coordinateGraphTopExteriorEquiv, LinearEquiv.trans_apply]
  unfold exteriorPower.ιMulti_family
  rw [LinearEquiv.exteriorPower_apply_ιMulti]
  rw [topExteriorPiEquiv_apply_ιMulti]
  simpa [B, J, hJ, p, exteriorPower.ιMulti_family] using hdet

/-- The Plücker point of a graph-chart point lies in the corresponding standard
projective-space chart. This is the module-theoretic chart-containment assertion in
the proof of Proposition 2.2.8. -/
lemma coordinateGraph_plucker_isCompl {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) :
    IsCompl (LinearMap.ker (pluckerLinearMap R q n (coordinateGraph I a)))
      (Submodule.pi
        (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
          Set (Fin (n.choose q))) fun _ ↦ ⊥) := by
  classical
  let φ := pluckerLinearMap R q n (coordinateGraph I a)
  let e := coordinateGraphTopExteriorEquiv I hI a
  let f : (Fin (n.choose q) → R) →ₗ[R] R := e.toLinearMap.comp φ
  let g : R →ₗ[R] (Fin (n.choose q) → R) :=
    LinearMap.single R (fun _ : Fin (n.choose q) ↦ R) (pluckerCoordinate I hI)
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro r
    change e (φ (Pi.single (pluckerCoordinate I hI) r)) = r
    rw [show Pi.single (pluckerCoordinate I hI) r =
      r • Pi.single (pluckerCoordinate I hI) (1 : R) by
        ext j
        by_cases hj : pluckerCoordinate I hI = j
        · subst j
          simp
        · simp [hj]]
    rw [map_smul, map_smul, coordinateGraph_pluckerLinearMap_single, smul_eq_mul,
      mul_one]
  have hcompl : IsCompl g.range f.ker :=
    ⟨by
      rw [Submodule.disjoint_def]
      intro x hxrange hxker
      obtain ⟨r, rfl⟩ := hxrange
      have hr := LinearMap.congr_fun hfg r
      rw [LinearMap.comp_apply, LinearMap.id_apply] at hr
      change f (g r) = 0 at hxker
      have hr0 : r = 0 := hr.symm.trans hxker
      simp [hr0], by
      apply codisjoint_iff.mpr
      rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨g (f x), LinearMap.mem_range_self g (f x), x - g (f x), ?_, by abel⟩
      apply LinearMap.mem_ker.mpr
      rw [map_sub]
      have hx := LinearMap.congr_fun hfg (f x)
      rw [LinearMap.comp_apply, LinearMap.id_apply] at hx
      rw [hx, sub_self]⟩
  have hker : f.ker = LinearMap.ker φ := by
    ext x
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply]
    constructor
    · intro hx
      apply e.injective
      simpa using hx
    · intro hx
      rw [hx, map_zero]
  have hrange : g.range =
      Submodule.pi
        (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
          Set (Fin (n.choose q))) fun _ ↦ ⊥ := by
    ext v
    constructor
    · rintro ⟨r, rfl⟩
      rw [Submodule.mem_pi]
      intro j hj
      have hjne : j ≠ pluckerCoordinate I hI := by
        intro eij
        subst j
        exact (Finset.mem_compl.mp hj) (by simp [pluckerChartIndex])
      simp [g, LinearMap.single_apply, hjne]
    · intro hv
      refine ⟨v (pluckerCoordinate I hI), ?_⟩
      ext j
      by_cases hj : pluckerCoordinate I hI = j
      · subst j
        simp [g, LinearMap.single_apply]
      · have hjmem : j ∈ (pluckerChartIndex I hI)ᶜ := by
          simp [pluckerChartIndex, Ne.symm hj]
        have hvj := (Submodule.mem_pi.mp hv) j hjmem
        rw [Submodule.mem_bot] at hvj
        simp [g, LinearMap.single_apply, hj, hvj]
  rw [← hker, ← hrange]
  exact hcompl.symm

/-- For a normalized linear functional, the graph coefficient of its kernel on a
singleton chart is the negative of the corresponding functional value. -/
lemma coordinateGraphMatrix_ker_singleton {R : Type u} [CommRing R] {m : ℕ}
    (φ : (Fin m → R) →ₗ[R] R) (s : Fin m)
    (hs : φ (Pi.single s 1) = 1)
    (hφ : IsCompl φ.ker
      (Submodule.pi ((({s} : Finset (Fin m))ᶜ : Finset (Fin m)) : Set (Fin m))
        fun _ ↦ (⊥ : Submodule R R)))
    (j : ↑(({s} : Finset (Fin m))ᶜ)) :
    coordinateGraphMatrix ({s} : Finset (Fin m)) φ.ker hφ
        ⟨s, by simp⟩ j = -φ (Pi.single j.1 1) := by
  classical
  let b := coordinateGraphMatrix ({s} : Finset (Fin m)) φ.ker hφ
  have hgraph : coordinateGraph ({s} : Finset (Fin m)) b = φ.ker :=
    coordinateGraph_coordinateGraphMatrix _ _ hφ
  have hg := coordinateGraphGenerator_mem ({s} : Finset (Fin m)) b j
  rw [hgraph, LinearMap.mem_ker] at hg
  have hgen : coordinateGraphGenerator ({s} : Finset (Fin m)) b j =
      b ⟨s, by simp⟩ j • Pi.single s 1 + Pi.single j.1 1 := by
    funext k
    by_cases hks : k = s
    · subst k
      have hjs : j.1 ≠ s := by
        intro h
        apply (Finset.mem_compl.mp j.2)
        rw [h]
        simp
      simp [coordinateGraphGenerator, hjs]
    · have hkn : k ∉ ({s} : Finset (Fin m)) := by simpa using hks
      simp [coordinateGraphGenerator, Pi.single_apply, hkn, hks]
  rw [hgen, map_add, map_smul, hs, smul_eq_mul, mul_one] at hg
  exact eq_neg_of_add_eq_zero_left hg

/-- In the target singleton chart, the signed graph coefficient of the Plücker
kernel is exactly the original graph coefficient. -/
lemma coordinateGraphMatrix_plucker_replacement {R : Type u} [CommRing R]
    {q n : ℕ} (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → R) (i : ↑I) (j : ↑(Iᶜ)) :
    (replacementPermutation I hI i j).sign •
      coordinateGraphMatrix (pluckerChartIndex I hI)
        (LinearMap.ker (pluckerLinearMap R q n (coordinateGraph I a)))
        (coordinateGraph_plucker_isCompl I hI a)
        ⟨pluckerCoordinate I hI, by simp [pluckerChartIndex]⟩
        (pluckerReplacementOutside I hI i j) = a i j := by
  classical
  let ψ := pluckerLinearMap R q n (coordinateGraph I a)
  let e := coordinateGraphTopExteriorEquiv I hI a
  let φ : (Fin (n.choose q) → R) →ₗ[R] R := e.toLinearMap.comp ψ
  have hker : LinearMap.ker φ = LinearMap.ker ψ := by
    ext x
    simp [φ, LinearMap.mem_ker]
  have hs : φ (Pi.single (pluckerCoordinate I hI) 1) = 1 :=
    coordinateGraph_pluckerLinearMap_single I hI a
  have hcompl : IsCompl (LinearMap.ker φ)
      (Submodule.pi
        ((({pluckerCoordinate I hI} : Finset (Fin (n.choose q)))ᶜ :
          Finset (Fin (n.choose q))) : Set (Fin (n.choose q))) fun _ ↦ ⊥) := by
    rw [hker]
    simpa [ψ, pluckerChartIndex] using coordinateGraph_plucker_isCompl I hI a
  have hb := coordinateGraphMatrix_ker_singleton φ
    (pluckerCoordinate I hI) hs hcompl (pluckerReplacementOutside I hI i j)
  have hb' : coordinateGraphMatrix (pluckerChartIndex I hI)
      (LinearMap.ker ψ) (coordinateGraph_plucker_isCompl I hI a)
      ⟨pluckerCoordinate I hI, by simp [pluckerChartIndex]⟩
      (pluckerReplacementOutside I hI i j) =
        -φ (Pi.single (pluckerReplacementOutside I hI i j).1 1) := by
    simpa only [pluckerChartIndex, hker, ψ] using hb
  rw [hb', smul_neg]
  have hrec := coordinateGraph_pluckerLinearMap_replacement I hI a i j
  change (replacementPermutation I hI i j).sign •
      φ (Pi.single (pluckerReplacementOutside I hI i j).1 1) = -a i j at hrec
  rw [hrec]
  simp

/-- The Plücker point of any Grassmannian point in the `I`-chart belongs to the
corresponding standard chart of projective space. -/
lemma Module.Grassmannian.plucker_isCompl_of_isCompl
    {R : Type u} [CommRing R] {q n : ℕ}
    (N : Module.Grassmannian R (Fin n → R) q)
    (I : Finset (Fin n)) (hI : I.card = q)
    (hN : IsCompl N.toSubmodule
      (Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n)) fun _ ↦ ⊥)) :
    IsCompl (LinearMap.ker (pluckerLinearMap R q n N.toSubmodule))
      (Submodule.pi
        (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
          Set (Fin (n.choose q))) fun _ ↦ ⊥) := by
  let a := coordinateGraphMatrix I N.toSubmodule hN
  have hgraph : coordinateGraph I a = N.toSubmodule :=
    coordinateGraph_coordinateGraphMatrix I N.toSubmodule hN
  rw [← hgraph]
  exact coordinateGraph_plucker_isCompl I hI a

/-- Over a field, the Grassmannian and Plücker standard-chart conditions are
equivalent. -/
lemma Module.Grassmannian.isCompl_iff_plucker_isCompl
    {K : Type u} [Field K] {q n : ℕ}
    (N : Module.Grassmannian K (Fin n → K) q)
    (I : Finset (Fin n)) (hI : I.card = q) :
    IsCompl N.toSubmodule
        (Submodule.pi (((Iᶜ : Finset (Fin n))) : Set (Fin n)) fun _ ↦ ⊥) ↔
      IsCompl (LinearMap.ker (pluckerLinearMap K q n N.toSubmodule))
        (Submodule.pi
          (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
            Set (Fin (n.choose q))) fun _ ↦ ⊥) :=
  ⟨N.plucker_isCompl_of_isCompl I hI,
    N.isCompl_of_plucker_isCompl I hI⟩

/-- The affine Plücker map on kernel-model Grassmannians. It sends the quotient
`R^n → R^n/N` to its top exterior-power quotient, whose kernel defines a point of
`Gr(1, n.choose q)`. -/
noncomputable def Module.Grassmannian.plucker {R : Type u} [CommRing R] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    Module.Grassmannian R (Fin (n.choose q) → R) 1 := by
  let φ := pluckerLinearMap R q n N.toSubmodule
  have hφ : Function.Surjective φ :=
    pluckerLinearMap_surjective R q n N
  let e : ((Fin (n.choose q) → R) ⧸ LinearMap.ker φ) ≃ₗ[R]
      ⋀[R]^q ((Fin n → R) ⧸ N.toSubmodule) :=
    φ.quotKerEquivOfSurjective hφ
  haveI : Module.Finite R (⋀[R]^q ((Fin n → R) ⧸ N.toSubmodule)) :=
    Module.Finite.exteriorPower q
  haveI : Module.Projective R (⋀[R]^q ((Fin n → R) ⧸ N.toSubmodule)) :=
    Module.Projective.exteriorPower q
  exact
    { toSubmodule := LinearMap.ker φ
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq := fun p ↦ by
        rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p,
          Module.rankAtStalk_exteriorPower, N.rankAtStalk_eq, Nat.choose_self] }

@[simp]
lemma Module.Grassmannian.plucker_toSubmodule {R : Type u} [CommRing R] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    (N.plucker q n).toSubmodule =
      LinearMap.ker (pluckerLinearMap R q n N.toSubmodule) := rfl

/-- The quotient underlying the affine Plücker point is canonically the top exterior
power of the original quotient. -/
noncomputable def Module.Grassmannian.pluckerQuotientEquiv
    {R : Type u} [CommRing R] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    ((Fin (n.choose q) → R) ⧸ (N.plucker q n).toSubmodule) ≃ₗ[R]
      ⋀[R]^q ((Fin n → R) ⧸ N.toSubmodule) :=
  (pluckerLinearMap R q n N.toSubmodule).quotKerEquivOfSurjective
    (pluckerLinearMap_surjective R q n N)

lemma Module.Grassmannian.pluckerQuotientEquiv_comp_mkQ
    {R : Type u} [CommRing R] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    (N.pluckerQuotientEquiv q n).toLinearMap.comp
        (N.plucker q n).toSubmodule.mkQ =
      pluckerLinearMap R q n N.toSubmodule := by
  apply LinearMap.ext
  intro x
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (pluckerLinearMap R q n N.toSubmodule)
    (pluckerLinearMap_surjective R q n N) x

/-- Expanded base-change naturality of the affine Plücker quotient map. The target is
identified using the exterior-power base-change comparison. -/
lemma pluckerLinearMap_baseChange {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (q n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    (exteriorPower.map q
      (grassmannianPiBaseChangeLinearMap R S n N)).comp
        (exteriorPowerPiEquiv S q n).toLinearMap =
      (exteriorPowerBaseChange R S q
        (N := ((Fin n → R) ⧸ N.toSubmodule))).comp
        ((pluckerLinearMap R q n N.toSubmodule).baseChange S |>.comp
          (piBaseChangeEquiv R S (n.choose q)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  rw [show grassmannianPiBaseChangeLinearMap R S n N =
      N.toSubmodule.mkQ.baseChange S ∘ₗ
        (piBaseChangeEquiv R S n).symm.toLinearMap from rfl,
    exteriorPower.map_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  have hcoord := LinearMap.congr_fun
    (exteriorPowerPiEquiv_baseChange_inv (R := R) (S := S) q n) x
  simp only [LinearMap.comp_apply] at hcoord
  rw [hcoord]
  let z := ((LinearMap.baseChange S
      ((exteriorPowerPiEquiv R q n).toLinearMap :
        (Fin (n.choose q) → R) →ₗ[R] ⋀[R]^q (Fin n → R))).comp
      (piBaseChangeEquiv R S (n.choose q)).symm.toLinearMap) x
  have hnat := LinearMap.congr_fun
    (exteriorPowerBaseChange_naturality (S := S) q N.toSubmodule.mkQ) z
  simp only [LinearMap.comp_apply] at hnat
  change exteriorPower.map q (N.toSubmodule.mkQ.baseChange S)
      (exteriorPowerBaseChange R S q z) = _
  rw [← hnat]
  simp only [LinearMap.comp_apply]
  congr 1
  change (exteriorPower.map q N.toSubmodule.mkQ).baseChange S z =
    (pluckerLinearMap R q n N.toSubmodule).baseChange S
      ((piBaseChangeEquiv R S (n.choose q)).symm x)
  rw [pluckerLinearMap, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rfl

/-- The affine Plücker operation commutes with arbitrary extension of scalars. -/
theorem Module.Grassmannian.plucker_baseChangePi
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q n : ℕ) (N : Module.Grassmannian R (Fin n → R) q) :
    (N.plucker q n).baseChangePi R S (n.choose q) =
      (N.baseChangePi R S n).plucker q n := by
  apply Module.Grassmannian.ext
  let φ := pluckerLinearMap R q n N.toSubmodule
  let ψ := grassmannianPiBaseChangeLinearMap R S n N
  let c := (piBaseChangeEquiv R S (n.choose q)).symm.toLinearMap
  let d := (exteriorPowerPiEquiv S q n).toLinearMap
  have hφ : Function.Surjective φ := pluckerLinearMap_surjective R q n N
  have hleft : LinearMap.ker ((LinearMap.ker φ).mkQ.baseChange S ∘ₗ c) =
      LinearMap.ker (φ.baseChange S ∘ₗ c) := by
    rw [LinearMap.ker_comp, LinearMap.ker_comp,
      LinearMap.ker_mkQ_baseChange_eq_ker_baseChange R S φ hφ]
  let e := N.baseChangePiQuotientEquiv R S n
  have hecomp : e.toLinearMap.comp
      (N.baseChangePi R S n).toSubmodule.mkQ = ψ := by
    exact N.baseChangePiQuotientEquiv_comp_mkQ R S n
  have hextInj : Function.Injective (exteriorPower.map q e.toLinearMap) := by
    apply exteriorPower.map_injective e.symm.toLinearMap
    ext x
    simp
  have hrightKernel : LinearMap.ker
      (exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ) =
      LinearMap.ker (exteriorPower.map q ψ) := by
    have hmaps : (exteriorPower.map q e.toLinearMap).comp
        (exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ) =
        exteriorPower.map q ψ := by
      rw [← exteriorPower.map_comp, hecomp]
    have hk := LinearMap.ker_comp_of_ker_eq_bot
      (exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ)
      (LinearMap.ker_eq_bot.mpr hextInj)
    rw [hmaps] at hk
    exact hk.symm
  have hbcInj : Function.Injective
      (exteriorPowerBaseChange R S q
        (N := ((Fin n → R) ⧸ N.toSubmodule))) :=
    (exteriorPowerBaseChange_bijective (R := R) (S := S) q).1
  have hexpanded := pluckerLinearMap_baseChange (R := R) (S := S) q n N
  have hLmap : grassmannianPiBaseChangeLinearMap R S (n.choose q) (N.plucker q n) =
      (LinearMap.ker φ).mkQ.baseChange S ∘ₗ c := rfl
  have hRmap : pluckerLinearMap S q n (N.baseChangePi R S n).toSubmodule =
      (exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ) ∘ₗ d := rfl
  change LinearMap.ker
      (grassmannianPiBaseChangeLinearMap R S (n.choose q) (N.plucker q n)) =
    LinearMap.ker (pluckerLinearMap S q n (N.baseChangePi R S n).toSubmodule)
  rw [hLmap, hRmap]
  change LinearMap.ker ((LinearMap.ker φ).mkQ.baseChange S ∘ₗ c) =
    LinearMap.ker
      ((exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ) ∘ₗ d)
  rw [hleft]
  rw [LinearMap.ker_comp
    d (exteriorPower.map q (N.baseChangePi R S n).toSubmodule.mkQ),
    hrightKernel,
    ← LinearMap.ker_comp d (exteriorPower.map q ψ)]
  rw [hexpanded]
  exact (LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr hbcInj)).symm

/-- The base change of a kernel-model Grassmannian point is the coordinatewise-image
span: the kernel presentation is stable under arbitrary extension of scalars. -/
lemma Module.Grassmannian.baseChangePi_toSubmodule_eq_span
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {q : ℕ} (n : ℕ)
    (N : Module.Grassmannian R (Fin n → R) q) :
    (N.baseChangePi R S n).toSubmodule =
      Submodule.span S ((fun w : Fin n → R ↦ fun i ↦ algebraMap R S (w i)) ''
        (N.toSubmodule : Set (Fin n → R))) := by
  rw [Module.Grassmannian.baseChangePi_toSubmodule,
    grassmannianPiBaseChangeLinearMap_eq_baseChangePi]
  have h := LinearMap.ker_baseChangePi_eq_span S
    (Submodule.mkQ_surjective N.toSubmodule)
  rwa [Submodule.ker_mkQ] at h


/-- **Base change along a ring isomorphism is transport**: if the structure map of the
algebra is an isomorphism, base change of a Grassmannian point is the transport of its
submodule along that isomorphism. -/
lemma Module.Grassmannian.baseChangePi_toSubmodule_eq_mapPiRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {q : ℕ} (n : ℕ)
    (e : R ≃+* S) (he : ∀ r : R, algebraMap R S r = e r)
    (N : Module.Grassmannian R (Fin n → R) q) :
    (N.baseChangePi R S n).toSubmodule = N.toSubmodule.mapPiRingEquiv e := by
  have hspan : N.toSubmodule.mapPiRingEquiv e =
      Submodule.span S ((fun (w : Fin n → R) (i : Fin n) ↦ e (w i)) ''
        (N.toSubmodule : Set (Fin n → R))) := by
    conv_lhs => rw [← Submodule.span_eq N.toSubmodule]
    rw [Submodule.mapPiRingEquiv_span]
  rw [Module.Grassmannian.baseChangePi_toSubmodule_eq_span, hspan]
  refine congrArg (Submodule.span S) ?_
  refine congrArg (fun (f : (Fin n → R) → Fin n → S) ↦
    f '' (N.toSubmodule : Set (Fin n → R))) ?_
  funext w i
  exact he (w i)

/-- **The Plücker kernel is compatible with transport along a ring isomorphism.** -/
lemma pluckerLinearMap_ker_mapPiRingEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {q : ℕ} (m : ℕ)
    (e : R ≃+* S) (he : ∀ r : R, algebraMap R S r = e r)
    (N : Module.Grassmannian R (Fin m → R) q) :
    (LinearMap.ker (pluckerLinearMap R q m N.toSubmodule)).mapPiRingEquiv e =
      LinearMap.ker (pluckerLinearMap S q m (N.toSubmodule.mapPiRingEquiv e)) := by
  have h1 := Module.Grassmannian.baseChangePi_toSubmodule_eq_mapPiRingEquiv m e he N
  have h2 := Module.Grassmannian.baseChangePi_toSubmodule_eq_mapPiRingEquiv
    (m.choose q) e he (N.plucker q m)
  rw [← h1, ← Module.Grassmannian.plucker_toSubmodule q m N, ← h2,
    Module.Grassmannian.plucker_baseChangePi q m N,
    Module.Grassmannian.plucker_toSubmodule]

/-- Over a local ring, codisjointness of a Grassmannian point with a coordinate
complement is detected on the residue field. The Fitting-ideal formulation turns
Nakayama into "an ideal of a local ring is the unit ideal iff its residue image is":
the coordinate Fitting ideal maps to the residue-field Fitting ideal of the reduced
point by base-change functoriality. -/
lemma Module.Grassmannian.codisjoint_piBot_iff_residue
    {R : Type u} [CommRing R] [IsLocalRing R] {r m : ℕ}
    (M : Module.Grassmannian R (Fin m → R) r) (A : Finset (Fin m)) :
    Codisjoint M.toSubmodule
        (Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
          (fun _ ↦ (⊥ : Submodule R R))) ↔
      Codisjoint
        (M.baseChangePi R (IsLocalRing.ResidueField R) m).toSubmodule
        (Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
          (fun _ ↦ (⊥ : Submodule (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField R)))) := by
  rw [codisjoint_iff, codisjoint_iff,
    ← Submodule.fittingIdeal_zero_eq_top_iff,
    ← Submodule.fittingIdeal_zero_eq_top_iff,
    Module.Grassmannian.baseChangePi_toSubmodule_eq_span,
    ← Submodule.span_image_piMap_piBot
      (algebraMap R (IsLocalRing.ResidueField R)) A,
    ← Submodule.span_image_piMap_sup,
    Submodule.fittingIdeal_span_image_map]
  constructor
  · intro h
    rw [h, Ideal.map_top]
  · intro h
    by_contra hne
    have hJm : (M.toSubmodule ⊔ Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
        (fun _ ↦ (⊥ : Submodule R R))).fittingIdeal 0 ≤
        IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hne
    have hbot : Ideal.map (algebraMap R (IsLocalRing.ResidueField R))
        ((M.toSubmodule ⊔ Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
          (fun _ ↦ (⊥ : Submodule R R))).fittingIdeal 0) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
      exact hJm
    rw [hbot] at h
    exact bot_ne_top h

/-- Over a local ring, a Grassmannian point is codisjoint with the `I`-coordinate
complement exactly when its Plücker point is codisjoint with the Plücker-coordinate
complement. Proof: reduce both sides to the residue field via the Fitting-ideal
Nakayama, identify the reduced Plücker point via `plucker_baseChangePi`, and use the
field-level equivalence together with the rank machinery upgrading codisjointness to
complementarity. -/
lemma Module.Grassmannian.codisjoint_piBot_plucker_iff_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {q n : ℕ}
    (N : Module.Grassmannian R (Fin n → R) q)
    (I : Finset (Fin n)) (hI : I.card = q) :
    Codisjoint (N.plucker q n).toSubmodule
        (Submodule.pi
          (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
            Set (Fin (n.choose q)))
          (fun _ ↦ (⊥ : Submodule R R))) ↔
      Codisjoint N.toSubmodule
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n))
          (fun _ ↦ (⊥ : Submodule R R))) := by
  rw [(N.plucker q n).codisjoint_piBot_iff_residue (pluckerChartIndex I hI),
    N.codisjoint_piBot_iff_residue I,
    Module.Grassmannian.plucker_baseChangePi]
  set κ := IsLocalRing.ResidueField R
  set N' := N.baseChangePi R κ n with hN'
  letI : Module.Projective κ ((Fin n → κ) ⧸ N'.toSubmodule) := N'.projective_quotient
  letI : Module.Projective κ
      ((Fin (n.choose q) → κ) ⧸ (N'.plucker q n).toSubmodule) :=
    (N'.plucker q n).projective_quotient
  constructor
  · intro h
    have hcompl := AlgebraicGeometry.Scheme.isCompl_of_codisjoint_of_quotient_projective_rank
      (pluckerChartIndex I hI) (N'.plucker q n).toSubmodule
      (pluckerChartIndex_card I hI) (N'.plucker q n).projective_quotient
      (N'.plucker q n).rankAtStalk_eq h
    rw [Module.Grassmannian.plucker_toSubmodule] at hcompl
    exact (N'.isCompl_of_plucker_isCompl I hI hcompl).codisjoint
  · intro h
    have hcompl := AlgebraicGeometry.Scheme.isCompl_of_codisjoint_of_quotient_projective_rank
      I N'.toSubmodule hI N'.projective_quotient N'.rankAtStalk_eq h
    have hplucker := N'.plucker_isCompl_of_isCompl I hI hcompl
    rw [← Module.Grassmannian.plucker_toSubmodule] at hplucker
    exact hplucker.codisjoint

/-- An ideal avoids a prime exactly when it generates the unit ideal in the
localization at that prime. -/
lemma _root_.Ideal.map_localization_atPrime_eq_top_iff_not_le
    {R : Type u} [CommRing R] (J : Ideal R) (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) J = ⊤ ↔
      ¬ (J ≤ p.asIdeal) := by
  constructor
  · intro h hle
    refine (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal) J).mpr ?_ h
    rw [Set.disjoint_left]
    intro a ha haJ
    exact ha (hle haJ)
  · intro hnle
    obtain ⟨h, hhJ, hhp⟩ := SetLike.not_le_iff_exists.mp hnle
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hhJ)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl)
        (Localization.AtPrime p.asIdeal) ⟨h, hhp⟩)

/-- Localized non-containment criterion: the coordinate Fitting ideal of a Grassmannian
point avoids a prime exactly when the point base-changed to the localization at that
prime is codisjoint with the coordinate complement. -/
lemma Module.Grassmannian.not_fittingIdeal_sup_piBot_le_iff_codisjoint_baseChangePi
    {R : Type u} [CommRing R] {q m : ℕ}
    (N : Module.Grassmannian R (Fin m → R) q) (A : Finset (Fin m))
    (p : PrimeSpectrum R) :
    ¬ ((N.toSubmodule ⊔ Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
        (fun _ ↦ (⊥ : Submodule R R))).fittingIdeal 0 ≤ p.asIdeal) ↔
      Codisjoint
        ((N.baseChangePi R (Localization.AtPrime p.asIdeal) m).toSubmodule)
        (Submodule.pi ((Aᶜ : Finset (Fin m)) : Set (Fin m))
          (fun _ ↦ (⊥ : Submodule (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal)))) := by
  rw [← Ideal.map_localization_atPrime_eq_top_iff_not_le,
    ← Submodule.fittingIdeal_span_image_map, Submodule.span_image_piMap_sup,
    Submodule.span_image_piMap_piBot, Submodule.fittingIdeal_zero_eq_top_iff,
    ← codisjoint_iff, ← Module.Grassmannian.baseChangePi_toSubmodule_eq_span]

/-- At every prime, the selected coordinates generate a Grassmannian quotient after
localization exactly when the corresponding Plücker coordinate generates its
determinant quotient. -/
lemma Module.Grassmannian.coordinateToQuotient_localized_surjective_iff_plucker
    {R : Type u} [CommRing R] {q n : ℕ}
    (N : Module.Grassmannian R (Fin n → R) q)
    (I : Finset (Fin n)) (hI : I.card = q) (p : PrimeSpectrum R) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl
        (coordinateToQuotient I N.toSubmodule)) ↔
      Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl
        (coordinateToQuotient (pluckerChartIndex I hI)
          (N.plucker q n).toSubmodule)) := by
  letI : Module.Finite R ((Fin n → R) ⧸ N.toSubmodule) := N.finite_quotient
  let NP := N.plucker q n
  letI : Module.Finite R
      ((Fin (n.choose q) → R) ⧸ NP.toSubmodule) := NP.finite_quotient
  let k := p.residueField
  let Nk := N.baseChangePi R k n
  calc
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl
        (coordinateToQuotient I N.toSubmodule)) ↔
        Function.Surjective (LinearMap.baseChange k
          (coordinateToQuotient I N.toSubmodule)) :=
      LinearMap.surjective_localizedMap_iff_surjective_baseChange_residueField _ p
    _ ↔ Function.Surjective (coordinateToQuotient I Nk.toSubmodule) := by
      exact (N.coordinateToQuotient_baseChange_surjective_iff R k n I).symm
    _ ↔ IsCompl Nk.toSubmodule
        (Submodule.pi ((Iᶜ : Finset (Fin n)) : Set (Fin n)) fun _ ↦ ⊥) :=
      coordinateToQuotient_surjective_iff_isCompl I Nk.toSubmodule hI
        Nk.projective_quotient Nk.rankAtStalk_eq
    _ ↔ IsCompl (LinearMap.ker
          (pluckerLinearMap k q n Nk.toSubmodule))
        (Submodule.pi
          (((pluckerChartIndex I hI)ᶜ : Finset (Fin (n.choose q))) :
            Set (Fin (n.choose q))) fun _ ↦ ⊥) :=
      Nk.isCompl_iff_plucker_isCompl I hI
    _ ↔ Function.Surjective (coordinateToQuotient
          (pluckerChartIndex I hI) (Nk.plucker q n).toSubmodule) := by
      rw [Module.Grassmannian.plucker_toSubmodule]
      exact (coordinateToQuotient_surjective_iff_isCompl
        (pluckerChartIndex I hI) (Nk.plucker q n).toSubmodule
        (pluckerChartIndex_card I hI) (Nk.plucker q n).projective_quotient
        (Nk.plucker q n).rankAtStalk_eq).symm
    _ ↔ Function.Surjective (coordinateToQuotient
          (pluckerChartIndex I hI)
          ((N.plucker q n).baseChangePi R k (n.choose q)).toSubmodule) := by
      rw [N.plucker_baseChangePi q n]
    _ ↔ Function.Surjective (LinearMap.baseChange k
          (coordinateToQuotient (pluckerChartIndex I hI)
            (N.plucker q n).toSubmodule)) :=
      (N.plucker q n).coordinateToQuotient_baseChange_surjective_iff
        R k (n.choose q) (pluckerChartIndex I hI)
    _ ↔ Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl
          (coordinateToQuotient (pluckerChartIndex I hI)
            (N.plucker q n).toSubmodule)) :=
      (LinearMap.surjective_localizedMap_iff_surjective_baseChange_residueField _ p).symm
end ModuleLemmas

namespace AlgebraicGeometry.Scheme

namespace SubmoduleSheafData

variable {X : Scheme.{u}} {n : ℕ}


/-- On an affine scheme, quasi-coherent submodule data whose global quotient is
finite projective of rank `q` determines a kernel-model Grassmannian point over the
ring of global functions. -/
noncomputable def grassmannianTop [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    Module.Grassmannian Γ(X, ⊤) (Fin n → Γ(X, ⊤)) q where
  toSubmodule := K.submodule ⟨⊤, isAffineOpen_top X⟩
  finite_quotient :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  projective_quotient := hproj
  rankAtStalk_eq := hrank

@[simp]
lemma grassmannianTop_toSubmodule [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    (K.grassmannianTop q hproj hrank).toSubmodule =
      K.submodule ⟨⊤, isAffineOpen_top X⟩ :=
  rfl

/-- The affine-chart Plücker kernel associated to a globally finite-projective
rank-`q` quotient.  It is obtained from the top exterior-power quotient over global
sections and extended to quasi-coherent submodule data on the affine scheme. -/
noncomputable def affinePlucker [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    X.SubmoduleSheafData (n.choose q) :=
  ofAffineSubmodule ((K.grassmannianTop q hproj hrank).plucker q n).toSubmodule

@[simp]
lemma affinePlucker_submodule_top [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    (K.affinePlucker q hproj hrank).submodule ⟨⊤, isAffineOpen_top X⟩ =
      ((K.grassmannianTop q hproj hrank).plucker q n).toSubmodule := by
  exact ofAffineSubmodule_submodule_top _

/-- The quotient by the affine-chart Plücker kernel is a line bundle. -/
lemma affinePlucker_quotientProjectiveOfRank [IsAffine X]
    (K : X.SubmoduleSheafData n) (q : ℕ)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    (K.affinePlucker q hproj hrank).QuotientProjectiveOfRank 1 := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top X⟩, trivial, ?_, ?_⟩
  · rw [affinePlucker_submodule_top]
    exact (K.grassmannianTop q hproj hrank).plucker q n |>.projective_quotient
  · intro p
    rw [affinePlucker_submodule_top]
    exact (K.grassmannianTop q hproj hrank).plucker q n |>.rankAtStalk_eq p

/-- The affine Plücker kernel attached directly to a sheaf-level Grassmannian point.
The affine local-to-global theorems supply the global projectivity and rank data
required by `affinePlucker`. -/
noncomputable def affinePluckerOfQuotientProjectiveOfRank [IsAffine X]
    (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    X.SubmoduleSheafData (n.choose q) :=
  K.affinePlucker q (hK.projective_affine ⟨⊤, isAffineOpen_top X⟩)
    (hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)

/-- The quotient by the canonical affine Plücker kernel of a Grassmannian datum is
a line bundle. -/
lemma affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank
    [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    (K.affinePluckerOfQuotientProjectiveOfRank q hK).QuotientProjectiveOfRank 1 :=
  K.affinePlucker_quotientProjectiveOfRank q
    (hK.projective_affine ⟨⊤, isAffineOpen_top X⟩)
    (hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)

/-- On an affine scheme, the Plücker chart open is exactly the corresponding
Grassmannian chart open. Pointwise, both memberships are prime-avoidance of a
coordinate Fitting ideal; localizing at the point they become codisjointness for the
base-changed Grassmannian point and its Plücker point over a local ring, which is the
residue-field Nakayama equivalence. -/
lemma affinePluckerOfQuotientProjectiveOfRank_coordinateChartOpen [IsAffine X]
    (K : X.SubmoduleSheafData n) (q : ℕ) (hK : K.QuotientProjectiveOfRank q)
    (I : Finset (Fin n)) (hI : I.card = q) :
    (K.affinePluckerOfQuotientProjectiveOfRank q hK).coordinateChartOpen
        (pluckerChartIndex I hI) =
      K.coordinateChartOpen I := by
  have hproj' := hK.projective_affine ⟨⊤, isAffineOpen_top X⟩
  have hrank' := hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩
  have hsub : (K.affinePluckerOfQuotientProjectiveOfRank q hK).submodule
      ⟨⊤, isAffineOpen_top X⟩ =
      ((K.grassmannianTop q hproj' hrank').plucker q n).toSubmodule :=
    affinePlucker_submodule_top K q hproj' hrank'
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe,
    (K.affinePluckerOfQuotientProjectiveOfRank q hK).mem_coordinateChartOpen_iff_not_le
      (pluckerChartIndex I hI) ⟨⊤, isAffineOpen_top X⟩ trivial,
    K.mem_coordinateChartOpen_iff_not_le I ⟨⊤, isAffineOpen_top X⟩ trivial,
    SubmoduleSheafData.coordinateFittingIdealAt,
    SubmoduleSheafData.coordinateFittingIdealAt,
    hsub, ← K.grassmannianTop_toSubmodule q hproj' hrank',
    Module.Grassmannian.not_fittingIdeal_sup_piBot_le_iff_codisjoint_baseChangePi,
    Module.Grassmannian.not_fittingIdeal_sup_piBot_le_iff_codisjoint_baseChangePi,
    Module.Grassmannian.plucker_baseChangePi]
  exact Module.Grassmannian.codisjoint_piBot_plucker_iff_of_isLocalRing
    ((K.grassmannianTop q hproj' hrank').baseChangePi _ _ n) I hI

/-- On an affine scheme, a Grassmannian coordinate-generation open is exactly the
corresponding Plücker coordinate-generation open. -/
lemma affinePlucker_coordinateGraphData_isComplementOfCoords [IsAffine X]
    (q : ℕ) (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    let K := coordinateGraphData X I a
    let hK : K.QuotientProjectiveOfRank q := hI ▸
      coordinateGraphData_quotientProjectiveOfRank X I a
    (K.affinePluckerOfQuotientProjectiveOfRank q hK).IsComplementOfCoords
      (pluckerChartIndex I hI) := by
  let K := coordinateGraphData X I a
  let hK : K.QuotientProjectiveOfRank q := hI ▸
    coordinateGraphData_quotientProjectiveOfRank X I a
  change (SubmoduleSheafData.ofAffineSubmodule
    (((K.grassmannianTop q
      (hK.projective_affine ⟨⊤, isAffineOpen_top X⟩)
      (hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)).plucker q n).toSubmodule))
      |>.IsComplementOfCoords (pluckerChartIndex I hI)
  apply ofAffineSubmodule_isComplementOfCoords
  change IsCompl
    (LinearMap.ker (pluckerLinearMap Γ(X, ⊤) q n
      (coordinateGraph I (restrictCoordinateMatrix X I a ⊤)))) _
  exact coordinateGraph_plucker_isCompl I hI
    (restrictCoordinateMatrix X I a ⊤)

/-- The signed replacement coordinate of an affine Plücker datum recovers a graph
coefficient of the original global kernel. -/
lemma affinePlucker_globalCoordinateMatrix_replacement [IsAffine X]
    (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤))
    (hKa : K.submodule ⟨⊤, isAffineOpen_top X⟩ = coordinateGraph I a)
    (hL : (K.affinePluckerOfQuotientProjectiveOfRank q hK).IsComplementOfCoords
      (pluckerChartIndex I hI)) (i : ↑I) (j : ↑(Iᶜ)) :
    (replacementPermutation I hI i j).sign •
      (K.affinePluckerOfQuotientProjectiveOfRank q hK).globalCoordinateMatrix
        (pluckerChartIndex I hI) hL
        ⟨pluckerCoordinate I hI, by simp [pluckerChartIndex]⟩
        (pluckerReplacementOutside I hI i j) = a i j := by
  rw [(K.affinePluckerOfQuotientProjectiveOfRank q hK)
    |>.globalCoordinateMatrix_eq_coordinateGraphMatrix_top
      (pluckerChartIndex I hI) hL]
  have hsub : (K.affinePluckerOfQuotientProjectiveOfRank q hK).submodule
      ⟨⊤, isAffineOpen_top X⟩ =
      LinearMap.ker (pluckerLinearMap Γ(X, ⊤) q n
        (K.submodule ⟨⊤, isAffineOpen_top X⟩)) := by
    exact affinePlucker_submodule_top K q
      (hK.projective_affine ⟨⊤, isAffineOpen_top X⟩)
      (hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)
  have hsub' : (K.affinePluckerOfQuotientProjectiveOfRank q hK).submodule
      ⟨⊤, isAffineOpen_top X⟩ =
      LinearMap.ker (pluckerLinearMap Γ(X, ⊤) q n (coordinateGraph I a)) :=
    hsub.trans (congrArg (fun W ↦
      LinearMap.ker (pluckerLinearMap Γ(X, ⊤) q n W)) hKa)
  have hmatrix := coordinateGraphMatrix_congr (pluckerChartIndex I hI) hsub'
    (hL ⟨⊤, isAffineOpen_top X⟩) (coordinateGraph_plucker_isCompl I hI a)
  rw [hmatrix]
  exact coordinateGraphMatrix_plucker_replacement I hI a i j

/-- The affine Plücker construction respects equality of its underlying submodule
data; the local-freeness witnesses are proposition-valued and hence proof-irrelevant. -/
lemma affinePluckerOfQuotientProjectiveOfRank_congr [IsAffine X]
    {K L : X.SubmoduleSheafData n} (h : K = L) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (hL : L.QuotientProjectiveOfRank q) :
    K.affinePluckerOfQuotientProjectiveOfRank q hK =
      L.affinePluckerOfQuotientProjectiveOfRank q hL := by
  subst L
  rfl

/-- On affine schemes, the global Grassmannian point associated to pulled-back
submodule data is the scalar extension of the original global Grassmannian point. -/
lemma grassmannianTop_comap {Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (K : Y.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) (f : X ⟶ Y) :
    let Ytop : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
    let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
    letI : Algebra Γ(Y, Ytop.1) Γ(X, Xtop.1) :=
      (f.appLE Ytop.1 Xtop.1 (by intro x _; trivial)).hom.toAlgebra
    (K.comap f).grassmannianTop q
        ((hK.comap f).projective_affine Xtop)
        ((hK.comap f).rankAtStalk_affine Xtop) =
      (K.grassmannianTop q
          (hK.projective_affine Ytop)
          (hK.rankAtStalk_affine Ytop)).baseChangePi
        Γ(Y, Ytop.1) Γ(X, Xtop.1) n := by
  let Ytop : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let R := Γ(Y, Ytop.1)
  let S := Γ(X, Xtop.1)
  let α : R →+* S :=
    (f.appLE Ytop.1 Xtop.1 (by intro x _; trivial)).hom
  letI : Algebra R S := α.toAlgebra
  let N := K.submodule Ytop
  apply Module.Grassmannian.ext
  rw [Module.Grassmannian.baseChangePi_toSubmodule,
    grassmannianPiBaseChangeLinearMap_eq_baseChangePi]
  change (K.comap f).submodule Xtop =
    LinearMap.ker (LinearMap.baseChangePi S N.mkQ)
  rw [K.comap_submodule_eq_span f
    (U' := Xtop) (V := Ytop) (by intro x _; trivial)]
  change Submodule.span S
      ((fun w i ↦ algebraMap R S (w i)) '' (N : Set (Fin n → R))) =
    LinearMap.ker (LinearMap.baseChangePi S N.mkQ)
  symm
  apply le_antisymm
  · have h := LinearMap.ker_baseChangePi_le_span S
      (Submodule.mkQ_surjective N)
    simpa [N, α] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change LinearMap.baseChangePi S N.mkQ
      (fun i ↦ algebraMap R S (w i)) = 0
    rw [LinearMap.baseChangePi_comp_algebraMap,
      show N.mkQ w = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hw,
      TensorProduct.tmul_zero]

/-- The global Grassmannian point of the canonical affine Plücker datum is the
module-level Plücker point. -/
lemma grassmannianTop_affinePluckerOfQuotientProjectiveOfRank [IsAffine X]
    (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    let L := K.affinePluckerOfQuotientProjectiveOfRank q hK
    let hL := K.affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank q hK
    L.grassmannianTop 1
        (hL.projective_affine ⟨⊤, isAffineOpen_top X⟩)
        (hL.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩) =
      (K.grassmannianTop q
          (hK.projective_affine ⟨⊤, isAffineOpen_top X⟩)
          (hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)).plucker q n := by
  apply Module.Grassmannian.ext
  exact affinePlucker_submodule_top _ _ _ _

/-- The canonical affine Plücker construction commutes with pullback between affine
schemes. -/
lemma affinePluckerOfQuotientProjectiveOfRank_comap
    {Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (K : Y.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) (f : X ⟶ Y) :
    (K.affinePluckerOfQuotientProjectiveOfRank q hK).comap f =
      (K.comap f).affinePluckerOfQuotientProjectiveOfRank q (hK.comap f) := by
  let Ytop : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let Xtop : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  letI : Algebra Γ(Y, Ytop.1) Γ(X, Xtop.1) :=
    (f.appLE Ytop.1 Xtop.1 (by intro x _; trivial)).hom.toAlgebra
  let L := K.affinePluckerOfQuotientProjectiveOfRank q hK
  let hL := K.affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank q hK
  let G := K.grassmannianTop q (hK.projective_affine Ytop)
    (hK.rankAtStalk_affine Ytop)
  let G' := (K.comap f).grassmannianTop q
    ((hK.comap f).projective_affine Xtop)
    ((hK.comap f).rankAtStalk_affine Xtop)
  let A := (L.comap f).grassmannianTop 1
    ((hL.comap f).projective_affine Xtop)
    ((hL.comap f).rankAtStalk_affine Xtop)
  let B := ((K.comap f).affinePluckerOfQuotientProjectiveOfRank q (hK.comap f))
    |>.grassmannianTop 1
      ((K.comap f).affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank
        q (hK.comap f) |>.projective_affine Xtop)
      ((K.comap f).affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank
        q (hK.comap f) |>.rankAtStalk_affine Xtop)
  have hcomapK : G' = G.baseChangePi Γ(Y, Ytop.1) Γ(X, Xtop.1) n := by
    exact grassmannianTop_comap K q hK f
  have hcomapL : A =
      (L.grassmannianTop 1 (hL.projective_affine Ytop)
        (hL.rankAtStalk_affine Ytop)).baseChangePi
          Γ(Y, Ytop.1) Γ(X, Xtop.1) (n.choose q) := by
    exact grassmannianTop_comap L 1 hL f
  have hpluckerY : L.grassmannianTop 1 (hL.projective_affine Ytop)
      (hL.rankAtStalk_affine Ytop) = G.plucker q n := by
    exact grassmannianTop_affinePluckerOfQuotientProjectiveOfRank K q hK
  have hpluckerX : B = G'.plucker q n := by
    exact grassmannianTop_affinePluckerOfQuotientProjectiveOfRank
      (K.comap f) q (hK.comap f)
  have hAB : A = B := by
    calc
      A = (L.grassmannianTop 1 (hL.projective_affine Ytop)
          (hL.rankAtStalk_affine Ytop)).baseChangePi
            Γ(Y, Ytop.1) Γ(X, Xtop.1) (n.choose q) := hcomapL
      _ = (G.plucker q n).baseChangePi
            Γ(Y, Ytop.1) Γ(X, Xtop.1) (n.choose q) := by rw [hpluckerY]
      _ = (G.baseChangePi Γ(Y, Ytop.1) Γ(X, Xtop.1) n).plucker q n :=
        Module.Grassmannian.plucker_baseChangePi
          (R := Γ(Y, Ytop.1)) (S := Γ(X, Xtop.1)) q n G
      _ = G'.plucker q n := by rw [hcomapK]
      _ = B := hpluckerX.symm
  have htop : (L.comap f).submodule Xtop =
      ((K.comap f).affinePluckerOfQuotientProjectiveOfRank q (hK.comap f)).submodule Xtop :=
    congrArg Module.Grassmannian.toSubmodule hAB
  apply le_antisymm
  · rw [le_iff_submodule_top_le]
    exact htop.le
  · rw [le_iff_submodule_top_le]
    exact htop.ge

/-- The canonical affine cover with its index lifted to the large universe required
by arbitrary Zariski descent data. -/
noncomputable def largeAffineCover : X.OpenCover.{u + 1} where
  I₀ := ULift.{u + 1} X.affineCover.I₀
  X i := X.affineCover.X i.down
  f i := X.affineCover.f i.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
    exact ⟨ULift.up i, y, hy⟩

instance largeAffineCover_isAffine (i : (largeAffineCover (X := X)).I₀) :
    IsAffine ((largeAffineCover (X := X)).X i) := by
  change IsAffine (X.affineCover.X i.down)
  infer_instance

/-- The affine Plücker kernel on a member of the canonical affine cover. -/
noncomputable def affineCoverPlucker (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) (i : (largeAffineCover (X := X)).I₀) :
    ((largeAffineCover (X := X)).X i).SubmoduleSheafData (n.choose q) :=
  (K.comap ((largeAffineCover (X := X)).f i)).affinePluckerOfQuotientProjectiveOfRank q
    (hK.comap ((largeAffineCover (X := X)).f i))

/-- The affine Plücker kernels on the canonical affine cover agree after pullback to
an affine overlap. -/
lemma affineCoverPlucker_compatible_of_isAffine (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (i j : (largeAffineCover (X := X)).I₀) (W : Scheme.{u}) [IsAffine W]
    (a : W ⟶ (largeAffineCover (X := X)).X i)
    (b : W ⟶ (largeAffineCover (X := X)).X j)
    (hab : a ≫ (largeAffineCover (X := X)).f i =
      b ≫ (largeAffineCover (X := X)).f j) :
    (affineCoverPlucker K q hK i).comap a =
      (affineCoverPlucker K q hK j).comap b := by
  have hdata : (K.comap ((largeAffineCover (X := X)).f i)).comap a =
      (K.comap ((largeAffineCover (X := X)).f j)).comap b := by
    calc
      (K.comap ((largeAffineCover (X := X)).f i)).comap a =
          K.comap (a ≫ (largeAffineCover (X := X)).f i) :=
        (K.comap_comp a ((largeAffineCover (X := X)).f i)).symm
      _ = K.comap (b ≫ (largeAffineCover (X := X)).f j) := congrArg (K.comap) hab
      _ = (K.comap ((largeAffineCover (X := X)).f j)).comap b :=
        K.comap_comp b ((largeAffineCover (X := X)).f j)
  have hplucker := affinePluckerOfQuotientProjectiveOfRank_congr hdata q
    ((hK.comap ((largeAffineCover (X := X)).f i)).comap a)
    ((hK.comap ((largeAffineCover (X := X)).f j)).comap b)
  calc
    (affineCoverPlucker K q hK i).comap a =
        (((K.comap ((largeAffineCover (X := X)).f i)).comap a)
          |>.affinePluckerOfQuotientProjectiveOfRank q
            ((hK.comap ((largeAffineCover (X := X)).f i)).comap a)) :=
      affinePluckerOfQuotientProjectiveOfRank_comap
        (K.comap ((largeAffineCover (X := X)).f i)) q
          (hK.comap ((largeAffineCover (X := X)).f i)) a
    _ = (((K.comap ((largeAffineCover (X := X)).f j)).comap b)
          |>.affinePluckerOfQuotientProjectiveOfRank q
            ((hK.comap ((largeAffineCover (X := X)).f j)).comap b)) := hplucker
    _ = (affineCoverPlucker K q hK j).comap b :=
      (affinePluckerOfQuotientProjectiveOfRank_comap
        (K.comap ((largeAffineCover (X := X)).f j)) q
          (hK.comap ((largeAffineCover (X := X)).f j)) b).symm

/-- The affine Plücker kernels on the canonical affine cover agree after arbitrary
pullback to an overlap. -/
lemma affineCoverPlucker_compatible (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (i j : (largeAffineCover (X := X)).I₀) (W : Scheme.{u})
    (a : W ⟶ (largeAffineCover (X := X)).X i)
    (b : W ⟶ (largeAffineCover (X := X)).X j)
    (hab : a ≫ (largeAffineCover (X := X)).f i =
      b ≫ (largeAffineCover (X := X)).f j) :
    (affineCoverPlucker K q hK i).comap a =
      (affineCoverPlucker K q hK j).comap b := by
  apply eq_of_comap_eq_openCover (largeAffineCover (X := W))
  intro k
  let c := (largeAffineCover (X := W)).f k
  calc
    ((affineCoverPlucker K q hK i).comap a).comap c =
        (affineCoverPlucker K q hK i).comap (c ≫ a) :=
      ((affineCoverPlucker K q hK i).comap_comp c a).symm
    _ = (affineCoverPlucker K q hK j).comap (c ≫ b) :=
      affineCoverPlucker_compatible_of_isAffine K q hK i j _ (c ≫ a) (c ≫ b)
        (by rw [Category.assoc, Category.assoc, hab])
    _ = ((affineCoverPlucker K q hK j).comap b).comap c :=
      (affineCoverPlucker K q hK j).comap_comp c b

/-- The global Plücker kernel of a sheaf-level Grassmannian point, obtained by
gluing the canonical affine Plücker kernels. -/
noncomputable def pluckerData (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    X.SubmoduleSheafData (n.choose q) :=
  glueOpenCover (largeAffineCover (X := X)) (affineCoverPlucker K q hK)
    (affineCoverPlucker_compatible K q hK)

/-- The global Plücker kernel restricts to the canonical construction on every member
of the canonical affine cover. -/
lemma pluckerData_comap_affineCover (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) (i : (largeAffineCover (X := X)).I₀) :
    (K.pluckerData q hK).comap ((largeAffineCover (X := X)).f i) =
      affineCoverPlucker K q hK i :=
  glueOpenCover_comap (largeAffineCover (X := X)) (affineCoverPlucker K q hK)
    (affineCoverPlucker_compatible K q hK) i

/-- The quotient by the global Plücker kernel is a line bundle. -/
lemma pluckerData_quotientProjectiveOfRank (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    (K.pluckerData q hK).QuotientProjectiveOfRank 1 := by
  apply QuotientProjectiveOfRank.of_comap_openCover _ (largeAffineCover (X := X))
  intro i
  rw [pluckerData_comap_affineCover]
  exact affinePluckerOfQuotientProjectiveOfRank_quotientProjectiveOfRank
    (K.comap ((largeAffineCover (X := X)).f i)) q
      (hK.comap ((largeAffineCover (X := X)).f i))

/-- The global Plücker construction respects equality of its underlying submodule
data. -/
lemma pluckerData_congr {K L : X.SubmoduleSheafData n} (h : K = L) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (hL : L.QuotientProjectiveOfRank q) :
    K.pluckerData q hK = L.pluckerData q hL := by
  subst L
  rfl

/-- Over an affine source, the affine Plücker construction is an amalgamation of the
canonical affine-cover Plücker kernels. -/
lemma affinePlucker_isAmalgamationAlong (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) {Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ X) :
    IsAmalgamationAlong (largeAffineCover (X := X)) (affineCoverPlucker K q hK) g
      ((K.comap g).affinePluckerOfQuotientProjectiveOfRank q (hK.comap g)) := by
  intro i
  let P := (largeAffineCover (X := X)).pullback₁ g
  apply eq_of_comap_eq_openCover (largeAffineCover (X := P.X i))
  intro j
  let c := (largeAffineCover (X := P.X i)).f j
  have hdata : ((K.comap g).comap (c ≫ P.f i)) =
      ((K.comap ((largeAffineCover (X := X)).f i)).comap
        (c ≫ (largeAffineCover (X := X)).pullbackHom g i)) := by
    calc
      (K.comap g).comap (c ≫ P.f i) = K.comap ((c ≫ P.f i) ≫ g) :=
        (K.comap_comp (c ≫ P.f i) g).symm
      _ = K.comap ((c ≫ (largeAffineCover (X := X)).pullbackHom g i) ≫
          (largeAffineCover (X := X)).f i) := by
        rw [Category.assoc, Category.assoc,
          (largeAffineCover (X := X)).pullbackHom_map g i]
      _ = (K.comap ((largeAffineCover (X := X)).f i)).comap
          (c ≫ (largeAffineCover (X := X)).pullbackHom g i) :=
        K.comap_comp (c ≫ (largeAffineCover (X := X)).pullbackHom g i)
          ((largeAffineCover (X := X)).f i)
  have hplucker := affinePluckerOfQuotientProjectiveOfRank_congr hdata q
    ((hK.comap g).comap (c ≫ P.f i))
    ((hK.comap ((largeAffineCover (X := X)).f i)).comap
      (c ≫ (largeAffineCover (X := X)).pullbackHom g i))
  calc
    (((K.comap g).affinePluckerOfQuotientProjectiveOfRank q (hK.comap g)).comap
        (P.f i)).comap c =
        ((K.comap g).affinePluckerOfQuotientProjectiveOfRank q (hK.comap g)).comap
          (c ≫ P.f i) :=
      (((K.comap g).affinePluckerOfQuotientProjectiveOfRank q
        (hK.comap g)).comap_comp _ _).symm
    _ = (((K.comap g).comap (c ≫ P.f i))
          |>.affinePluckerOfQuotientProjectiveOfRank q
            ((hK.comap g).comap (c ≫ P.f i))) :=
      affinePluckerOfQuotientProjectiveOfRank_comap (K.comap g) q (hK.comap g) _
    _ = (((K.comap ((largeAffineCover (X := X)).f i)).comap
            (c ≫ (largeAffineCover (X := X)).pullbackHom g i))
          |>.affinePluckerOfQuotientProjectiveOfRank q
            ((hK.comap ((largeAffineCover (X := X)).f i)).comap
              (c ≫ (largeAffineCover (X := X)).pullbackHom g i))) := hplucker
    _ = (affineCoverPlucker K q hK i).comap
          (c ≫ (largeAffineCover (X := X)).pullbackHom g i) :=
      (affinePluckerOfQuotientProjectiveOfRank_comap
        (K.comap ((largeAffineCover (X := X)).f i)) q
        (hK.comap ((largeAffineCover (X := X)).f i)) _).symm
    _ = ((affineCoverPlucker K q hK i).comap
          ((largeAffineCover (X := X)).pullbackHom g i)).comap c :=
      (affineCoverPlucker K q hK i).comap_comp _ _

/-- The pullback of the global Plücker datum is an amalgamation of the canonical
affine-cover Plücker kernels after every base change. -/
lemma pluckerData_isAmalgamationAlong (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) {Y : Scheme.{u}} (g : Y ⟶ X) :
    IsAmalgamationAlong (largeAffineCover (X := X)) (affineCoverPlucker K q hK) g
      ((K.pluckerData q hK).comap g) := by
  intro i
  calc
    ((K.pluckerData q hK).comap g).comap
        (((largeAffineCover (X := X)).pullback₁ g).f i) =
        (K.pluckerData q hK).comap
          (((largeAffineCover (X := X)).pullback₁ g).f i ≫ g) :=
      ((K.pluckerData q hK).comap_comp _ _).symm
    _ = (K.pluckerData q hK).comap
        ((largeAffineCover (X := X)).pullbackHom g i ≫
          (largeAffineCover (X := X)).f i) := by
      rw [(largeAffineCover (X := X)).pullbackHom_map g i]
    _ = ((K.pluckerData q hK).comap
          ((largeAffineCover (X := X)).f i)).comap
            ((largeAffineCover (X := X)).pullbackHom g i) :=
      (K.pluckerData q hK).comap_comp _ _
    _ = (affineCoverPlucker K q hK i).comap
          ((largeAffineCover (X := X)).pullbackHom g i) := by
      rw [pluckerData_comap_affineCover]

/-- On an affine source, the global Plücker datum is the canonical affine Plücker
kernel. -/
lemma pluckerData_comap_of_isAffine (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) {Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ X) :
    (K.pluckerData q hK).comap g =
      (K.comap g).affinePluckerOfQuotientProjectiveOfRank q (hK.comap g) := by
  calc
    (K.pluckerData q hK).comap g =
        affineAmalgamation (largeAffineCover (X := X))
          (affineCoverPlucker K q hK) (affineCoverPlucker_compatible K q hK) g :=
      eq_affineAmalgamation_of_isAmalgamationAlong
        (largeAffineCover (X := X)) (affineCoverPlucker K q hK)
        (affineCoverPlucker_compatible K q hK)
        (pluckerData_isAmalgamationAlong K q hK g)
    _ = (K.comap g).affinePluckerOfQuotientProjectiveOfRank q (hK.comap g) :=
      (eq_affineAmalgamation_of_isAmalgamationAlong
        (largeAffineCover (X := X)) (affineCoverPlucker K q hK)
        (affineCoverPlucker_compatible K q hK)
        (affinePlucker_isAmalgamationAlong K q hK g)).symm

/-- On an affine scheme, the global Plücker datum itself is the canonical affine
Plücker datum. -/
lemma pluckerData_eq_affinePluckerOfQuotientProjectiveOfRank
    [IsAffine X] (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) :
    K.pluckerData q hK =
      K.affinePluckerOfQuotientProjectiveOfRank q hK := by
  have h := pluckerData_comap_of_isAffine K q hK (𝟙 X)
  calc
    K.pluckerData q hK = (K.pluckerData q hK).comap (𝟙 X) :=
      (K.pluckerData q hK).comap_id.symm
    _ = (K.comap (𝟙 X)).affinePluckerOfQuotientProjectiveOfRank q
        (hK.comap (𝟙 X)) := h
    _ = K.affinePluckerOfQuotientProjectiveOfRank q hK :=
      affinePluckerOfQuotientProjectiveOfRank_congr K.comap_id q _ _

/-- The global Plücker construction commutes with arbitrary base change. -/
lemma pluckerData_comap (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q) {Y : Scheme.{u}} (g : Y ⟶ X) :
    (K.pluckerData q hK).comap g =
      (K.comap g).pluckerData q (hK.comap g) := by
  apply eq_of_comap_eq_openCover (largeAffineCover (X := Y))
  intro i
  let c := (largeAffineCover (X := Y)).f i
  have hdata : K.comap (c ≫ g) = (K.comap g).comap c := K.comap_comp c g
  have hplucker := affinePluckerOfQuotientProjectiveOfRank_congr hdata q
    (hK.comap (c ≫ g)) ((hK.comap g).comap c)
  calc
    ((K.pluckerData q hK).comap g).comap c =
        (K.pluckerData q hK).comap (c ≫ g) :=
      ((K.pluckerData q hK).comap_comp c g).symm
    _ = (K.comap (c ≫ g)).affinePluckerOfQuotientProjectiveOfRank q
          (hK.comap (c ≫ g)) :=
      pluckerData_comap_of_isAffine K q hK (c ≫ g)
    _ = ((K.comap g).comap c).affinePluckerOfQuotientProjectiveOfRank q
          ((hK.comap g).comap c) := hplucker
    _ = affineCoverPlucker (K.comap g) q (hK.comap g) i := rfl
    _ = ((K.comap g).pluckerData q (hK.comap g)).comap c :=
      (pluckerData_comap_affineCover (K.comap g) q (hK.comap g) i).symm

/-- The inverse image of the standard Plücker chart is exactly the corresponding
standard Grassmannian chart: the Plücker chart open of the Plücker datum equals the
Grassmannian chart open. Checked on an affine cover, where it is the pointwise
prime-avoidance equivalence of the two coordinate Fitting ideals. -/
lemma pluckerData_coordinateChartOpen_eq (K : X.SubmoduleSheafData n) (q : ℕ)
    (hK : K.QuotientProjectiveOfRank q)
    (I : Finset (Fin n)) (hI : I.card = q) :
    (K.pluckerData q hK).coordinateChartOpen (pluckerChartIndex I hI) =
      K.coordinateChartOpen I := by
  have hpre : ∀ i, (X.affineCover.f i) ⁻¹ᵁ
      ((K.pluckerData q hK).coordinateChartOpen (pluckerChartIndex I hI)) =
      (X.affineCover.f i) ⁻¹ᵁ (K.coordinateChartOpen I) := by
    intro i
    rw [← (K.pluckerData q hK).comap_coordinateChartOpen (pluckerChartIndex I hI)
        (X.affineCover.f i),
      ← K.comap_coordinateChartOpen I (X.affineCover.f i),
      pluckerData_comap_of_isAffine K q hK (X.affineCover.f i),
      affinePluckerOfQuotientProjectiveOfRank_coordinateChartOpen
        (K.comap (X.affineCover.f i)) q (hK.comap (X.affineCover.f i)) I hI]
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe]
  obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
  rw [← hy]
  constructor
  · intro h
    have hyL : y ∈ (X.affineCover.f i) ⁻¹ᵁ
        ((K.pluckerData q hK).coordinateChartOpen (pluckerChartIndex I hI)) := h
    rw [hpre i] at hyL
    exact hyL
  · intro h
    have hyR : y ∈ (X.affineCover.f i) ⁻¹ᵁ (K.coordinateChartOpen I) := h
    rw [← hpre i] at hyR
    exact hyR
lemma pluckerData_coordinateGraphData_isComplementOfCoords
    (q : ℕ) (I : Finset (Fin n)) (hI : I.card = q)
    (a : (i : ↑I) → (j : ↑(Iᶜ)) → Γ(X, ⊤)) :
    let K := coordinateGraphData X I a
    let hK : K.QuotientProjectiveOfRank q := hI ▸
      coordinateGraphData_quotientProjectiveOfRank X I a
    (K.pluckerData q hK).IsComplementOfCoords (pluckerChartIndex I hI) := by
  let K := coordinateGraphData X I a
  let hK : K.QuotientProjectiveOfRank q := hI ▸
    coordinateGraphData_quotientProjectiveOfRank X I a
  let L := K.pluckerData q hK
  let hL : L.QuotientProjectiveOfRank 1 :=
    pluckerData_quotientProjectiveOfRank K q hK
  apply (L.isComplementOfCoords_iff_coordinateChartOpen_eq_top_of_rank
    (pluckerChartIndex I hI) (pluckerChartIndex_card I hI) hL).mpr
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let f := X.affineCover.f i
  let b : (α : ↑I) → (β : ↑(Iᶜ)) → Γ(U, ⊤) :=
    fun α β ↦ f.appTop.hom (a α β)
  let KU := coordinateGraphData U I b
  let hKU : KU.QuotientProjectiveOfRank q := hI ▸
    coordinateGraphData_quotientProjectiveOfRank U I b
  have hKpull : K.comap f = KU := coordinateGraphData_comap f I a
  have hplucker : L.comap f =
      KU.affinePluckerOfQuotientProjectiveOfRank q hKU := by
    calc
      L.comap f = (K.comap f).affinePluckerOfQuotientProjectiveOfRank q
          (hK.comap f) := pluckerData_comap_of_isAffine K q hK f
      _ = KU.affinePluckerOfQuotientProjectiveOfRank q hKU :=
        affinePluckerOfQuotientProjectiveOfRank_congr hKpull q (hK.comap f) hKU
  have hpull : (L.comap f).IsComplementOfCoords (pluckerChartIndex I hI) := by
    rw [hplucker]
    exact affinePlucker_coordinateGraphData_isComplementOfCoords q I hI b
  have hopen : (L.comap f).coordinateChartOpen (pluckerChartIndex I hI) = ⊤ :=
    SubmoduleSheafData.coordinateChartOpen_eq_top_of_isComplementOfCoords hpull
  have hy' : y ∈ (L.comap f).coordinateChartOpen (pluckerChartIndex I hI) := by
    rw [hopen]
    trivial
  rw [L.comap_coordinateChartOpen (pluckerChartIndex I hI) f] at hy'
  exact hy ▸ hy'
end SubmoduleSheafData

/-- Background definition for Proposition 2.2.8 (the implicit definition of the
Plücker embedding `P : Gr(q, n) → ℙ(⋀^q O^{⊕n})`): the Plücker morphism of Grassmannian
functors, sending a rank-`q` quotient to its top exterior-power line quotient. The target
`ℙ(⋀^q O^{⊕n})` is rendered as `Gr(1, C(n, q))` via the exterior-power basis indexed by
`q`-element subsets. -/
noncomputable def pluckerMorphism (q n : ℕ) :
    grassmannianFunctor.{u} q n ⟶ grassmannianFunctor.{u} 1 (n.choose q) where
  app T := ↾fun K ↦ ⟨K.1.pluckerData q K.2,
    K.1.pluckerData_quotientProjectiveOfRank q K.2⟩
  naturality T T' f := by
    apply ConcreteCategory.hom_ext
    intro K
    apply Subtype.ext
    exact (K.1.pluckerData_comap q K.2 f.unop).symm

@[simp]
lemma pluckerMorphism_app_val (q n : ℕ) (T : Scheme.{u}ᵒᵖ)
    (K : (grassmannianFunctor q n).obj T) :
    ((pluckerMorphism q n).app T K).1 = K.1.pluckerData q K.2 := rfl

/-- Background definition for Proposition 2.2.8 (the chart restriction `P_I`
from the proof): the restriction of the Plücker morphism from the standard chart `Gr_I`
to the corresponding standard chart of projective space. -/
noncomputable def pluckerChartMorphism (q n : ℕ) (I : Finset (Fin n))
    (hI : I.card = q) :
    grassmannianChart.{u} q n I ⟶
      grassmannianChart.{u} 1 (n.choose q) (pluckerChartIndex I hI) where
  app T := ↾fun K ↦ ⟨(pluckerMorphism q n).app T K.1, by
    let G := coordinateGraphData T.unop I
      (K.1.1.globalCoordinateMatrix I K.2)
    let hG : G.QuotientProjectiveOfRank q := hI ▸
      coordinateGraphData_quotientProjectiveOfRank T.unop I
        (K.1.1.globalCoordinateMatrix I K.2)
    have hdata : G = K.1.1 :=
      K.1.1.coordinateGraphData_globalCoordinateMatrix I K.2
    have hplucker : G.pluckerData q hG = K.1.1.pluckerData q K.1.2 :=
      SubmoduleSheafData.pluckerData_congr hdata q hG K.1.2
    change (K.1.1.pluckerData q K.1.2).IsComplementOfCoords
      (pluckerChartIndex I hI)
    rw [← hplucker]
    exact SubmoduleSheafData.pluckerData_coordinateGraphData_isComplementOfCoords
      q I hI (K.1.1.globalCoordinateMatrix I K.2)⟩
  naturality T T' f := by
    refine ConcreteCategory.hom_ext _ _ fun K ↦ Subtype.ext ?_
    apply Subtype.ext
    exact (K.1.1.pluckerData_comap q K.1.2 f.unop).symm

/-- The affine space representing the standard Grassmannian chart indexed by `I`. -/
noncomputable abbrev grassmannianChartAffineSpace {n : ℕ}
    (I : Finset (Fin n)) : Scheme.{u} :=
  AffineSpace (ULift.{u} (↑I × ↑(Iᶜ))) (⊤_ Scheme.{u})

/-- The explicit affine chart representation is coherent under reindexing by an
equality of chart subsets. -/
lemma yoneda_map_eqToHom_comp_grassmannianChartAffineRepresentation
    (q n : ℕ) {I J : Finset (Fin n)} (hI : I.card = q) (hJ : J.card = q)
    (e : I = J) :
    yoneda.map (eqToHom (congrArg (fun K : Finset (Fin n) ↦
        grassmannianChartAffineSpace.{u} K) e)) ≫
        (grassmannianChartAffineRepresentation q n J hJ).toIso.hom ≫
        grassmannianChartι q n J =
      (grassmannianChartAffineRepresentation q n I hI).toIso.hom ≫
        grassmannianChartι q n I := by
  subst J
  simp

/-- The inclusion of a standard chart is coherent under transport of its index. -/
lemma eqToHom_grassmannianChart_comp_chartι
    (q n : ℕ) {I J : Finset (Fin n)} (e : I = J) :
    eqToHom (congrArg (grassmannianChart.{u} q n) e.symm) ≫
        grassmannianChartι q n I =
      grassmannianChartι q n J := by
  subst J
  simp

/-- The universal graph-coordinate matrix on the affine space representing a
standard Grassmannian chart. -/
noncomputable def grassmannianChartUniversalMatrix {n : ℕ} (I : Finset (Fin n)) :
    (i : ↑I) → (j : ↑(Iᶜ)) →
      Γ(grassmannianChartAffineSpace.{u} I, ⊤) :=
  fun i j ↦ AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j))

lemma grassmannianChartAffineRepresentation_homEquiv_id
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q) :
    (grassmannianChartAffineRepresentation q n I hI).homEquiv
        (𝟙 (grassmannianChartAffineSpace.{u} I)) =
      coordinateMatrixChartPoint q n I (grassmannianChartAffineSpace.{u} I) hI
        (grassmannianChartUniversalMatrix I) := by
  apply Subtype.ext
  apply Subtype.ext
  congr 1
lemma grassmannianChartAffineRepresentation_homEquiv
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q)
    {X : Scheme.{u}} (f : X ⟶ grassmannianChartAffineSpace.{u} I) :
    (grassmannianChartAffineRepresentation q n I hI).homEquiv f =
      coordinateMatrixChartPoint q n I X hI fun i j ↦
        f.appTop.hom (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j))) := by
  apply Subtype.ext
  apply Subtype.ext
  congr 1

/-- The scheme morphism between the representing affine spaces induced by the
standard-chart Plücker morphism. -/
noncomputable def pluckerChartSchemeMorphism (q n : ℕ) (I : Finset (Fin n))
    (hI : I.card = q) :
    grassmannianChartAffineSpace.{u} I ⟶
      grassmannianChartAffineSpace.{u} (pluckerChartIndex I hI) :=
  (grassmannianChartAffineRepresentation 1 (n.choose q)
      (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv.symm
    ((pluckerChartMorphism q n I hI).app
      (Opposite.op (grassmannianChartAffineSpace.{u} I))
      ((grassmannianChartAffineRepresentation q n I hI).homEquiv
        (𝟙 (grassmannianChartAffineSpace.{u} I))))

/-- The coordinate-extraction morphism from the target Plücker affine chart back to
the source graph chart. -/
noncomputable def pluckerChartSchemeRetraction (q n : ℕ)
    (I : Finset (Fin n)) (hI : I.card = q) :
    grassmannianChartAffineSpace.{u} (pluckerChartIndex I hI) ⟶
      grassmannianChartAffineSpace.{u} I :=
  (affineSpaceTerminalHomEquiv
    (grassmannianChartAffineSpace.{u} (pluckerChartIndex I hI))
    (ULift.{u} (↑I × ↑(Iᶜ)))).symm fun z ↦
      (replacementPermutation I hI z.down.1 z.down.2).sign •
        AffineSpace.coord (⊤_ Scheme.{u})
          (ULift.up (pluckerChartSelected I hI,
            pluckerReplacementOutside I hI z.down.1 z.down.2))

/-- Pulling back a signed replacement coordinate along the affine Plücker chart map
gives the corresponding source graph coordinate. -/
lemma pluckerChartSchemeMorphism_appTop_replacement_coord
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q)
    (i : ↑I) (j : ↑(Iᶜ)) :
    (replacementPermutation I hI i j).sign •
      (pluckerChartSchemeMorphism.{u} q n I hI).appTop.hom
        (AffineSpace.coord (⊤_ Scheme.{u})
          (ULift.up (pluckerChartSelected I hI,
            pluckerReplacementOutside I hI i j))) =
      AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j)) := by
  classical
  let S := grassmannianChartAffineSpace.{u} I
  let a := grassmannianChartUniversalMatrix I
  let K := coordinateGraphData S I a
  let hK : K.QuotientProjectiveOfRank q := hI ▸
    coordinateGraphData_quotientProjectiveOfRank S I a
  let L := K.affinePluckerOfQuotientProjectiveOfRank q hK
  let hL : L.IsComplementOfCoords (pluckerChartIndex I hI) :=
    SubmoduleSheafData.affinePlucker_coordinateGraphData_isComplementOfCoords q I hI a
  let b : (r : ↑(pluckerChartIndex I hI)) →
      (s : ↑((pluckerChartIndex I hI)ᶜ)) → Γ(S, ⊤) := fun r s ↦
    (pluckerChartSchemeMorphism.{u} q n I hI).appTop.hom
      (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (r, s)))
  have hf := (grassmannianChartAffineRepresentation 1 (n.choose q)
    (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv.apply_symm_apply
      ((pluckerChartMorphism q n I hI).app (Opposite.op S)
        ((grassmannianChartAffineRepresentation q n I hI).homEquiv (𝟙 S)))
  change (grassmannianChartAffineRepresentation 1 (n.choose q)
      (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv
        (pluckerChartSchemeMorphism q n I hI) = _ at hf
  rw [grassmannianChartAffineRepresentation_homEquiv,
    grassmannianChartAffineRepresentation_homEquiv_id] at hf
  have hfdata := congrArg (fun z :
      (grassmannianChart 1 (n.choose q) (pluckerChartIndex I hI)).obj
        (Opposite.op S) ↦ z.1.1) hf
  change coordinateGraphData S (pluckerChartIndex I hI) b =
      K.pluckerData q hK at hfdata
  rw [K.pluckerData_eq_affinePluckerOfQuotientProjectiveOfRank q hK] at hfdata
  have hm := SubmoduleSheafData.globalCoordinateMatrix_congr hfdata
    (pluckerChartIndex I hI)
    (coordinateGraphData_isComplementOfCoords S (pluckerChartIndex I hI) b) hL
  rw [SubmoduleSheafData.globalCoordinateMatrix_coordinateGraphData] at hm
  have hrecover := SubmoduleSheafData.affinePlucker_globalCoordinateMatrix_replacement
    K q hK I hI
    (restrictCoordinateMatrix S I a ⊤) rfl hL i j
  rw [← hm] at hrecover
  change (replacementPermutation I hI i j).sign • b
      (pluckerChartSelected I hI) (pluckerReplacementOutside I hI i j) = _ at hrecover
  rw [hrecover]
  change (S.presheaf.map (homOfLE le_top).op).hom (a i j) = a i j
  have he : (homOfLE le_top : (⊤ : S.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [he]
  have heop : (𝟙 (⊤ : S.Opens)).op = 𝟙 (Opposite.op (⊤ : S.Opens)) :=
    Subsingleton.elim _ _
  rw [heop]
  exact DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (S.presheaf.map_id _)) _

/-- The coordinate-extraction morphism is a retraction of the affine Plücker chart
morphism. -/
lemma pluckerChartSchemeMorphism_comp_retraction
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q) :
    pluckerChartSchemeMorphism.{u} q n I hI ≫
        pluckerChartSchemeRetraction q n I hI =
      𝟙 (grassmannianChartAffineSpace.{u} I) := by
  apply AffineSpace.hom_ext
  · exact Subsingleton.elim _ _
  · intro z
    obtain ⟨⟨i, j⟩⟩ := z
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    change (pluckerChartSchemeMorphism.{u} q n I hI).appTop.hom
      ((pluckerChartSchemeRetraction q n I hI).appTop.hom
        (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j)))) =
      AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j))
    rw [show (pluckerChartSchemeRetraction q n I hI).appTop.hom
        (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i, j))) =
      (replacementPermutation I hI i j).sign •
        AffineSpace.coord (⊤_ Scheme.{u})
          (ULift.up (pluckerChartSelected I hI,
            pluckerReplacementOutside I hI i j)) by
      simp [pluckerChartSchemeRetraction, affineSpaceTerminalHomEquiv]]
    simpa only [Units.smul_def, map_zsmul] using
      pluckerChartSchemeMorphism_appTop_replacement_coord q n I hI i j

/-- API lemma for Proposition 2.2.8 (the affine chart computation:
each `P_I` is a closed immersion): the morphism between affine spaces representing a
standard Plücker chart is a closed immersion, since it admits the coordinate-extraction
retraction and is therefore surjective on coordinate rings. -/
lemma isClosedImmersion_pluckerChartSchemeMorphism
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q) :
    IsClosedImmersion (pluckerChartSchemeMorphism.{u} q n I hI) := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro x
  refine ⟨(pluckerChartSchemeRetraction q n I hI).appTop.hom x, ?_⟩
  have h := congrArg (fun f : grassmannianChartAffineSpace.{u} I ⟶
      grassmannianChartAffineSpace.{u} I ↦ f.appTop.hom x)
    (pluckerChartSchemeMorphism_comp_retraction q n I hI)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.id_appTop, CommRingCat.id_apply] using h

/-- Under the explicit affine-space representations, the scheme-level chart map is
the natural Plücker chart morphism. -/
lemma yoneda_map_pluckerChartSchemeMorphism_comp_representation
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q) :
    yoneda.map (pluckerChartSchemeMorphism.{u} q n I hI) ≫
        (grassmannianChartAffineRepresentation 1 (n.choose q)
          (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).toIso.hom =
      (grassmannianChartAffineRepresentation q n I hI).toIso.hom ≫
        pluckerChartMorphism q n I hI := by
  ext T g
  change (grassmannianChartAffineRepresentation 1 (n.choose q)
      (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv
      (g ≫ pluckerChartSchemeMorphism q n I hI) =
    (pluckerChartMorphism q n I hI).app T
      ((grassmannianChartAffineRepresentation q n I hI).homEquiv g)
  rw [(grassmannianChartAffineRepresentation 1 (n.choose q)
      (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv_comp]
  rw [show (grassmannianChartAffineRepresentation 1 (n.choose q)
      (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).homEquiv
      (pluckerChartSchemeMorphism q n I hI) =
      (pluckerChartMorphism q n I hI).app
        (Opposite.op (grassmannianChartAffineSpace.{u} I))
        ((grassmannianChartAffineRepresentation q n I hI).homEquiv
          (𝟙 (grassmannianChartAffineSpace.{u} I))) by
    exact Equiv.apply_symm_apply _ _]
  rw [← (pluckerChartMorphism q n I hI).naturality_apply]
  congr 1
  rw [← (grassmannianChartAffineRepresentation q n I hI).homEquiv_comp]
  simp

/-- Each standard-chart restriction of the Plücker morphism is relatively
representable by closed immersions. -/
lemma presheaf_isClosedImmersion_pluckerChartMorphism
    (q n : ℕ) (I : Finset (Fin n)) (hI : I.card = q) :
    MorphismProperty.presheaf (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (pluckerChartMorphism q n I hI) := by
  let P : MorphismProperty Scheme.{u} := @IsClosedImmersion
  let eS := (grassmannianChartAffineRepresentation q n I hI).toIso
  let eT := (grassmannianChartAffineRepresentation 1 (n.choose q)
    (pluckerChartIndex I hI) (pluckerChartIndex_card I hI)).toIso
  have hf : MorphismProperty.presheaf
      (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (yoneda.map (pluckerChartSchemeMorphism.{u} q n I hI)) :=
    MorphismProperty.relative_map
      (isClosedImmersion_pluckerChartSchemeMorphism q n I hI)
  have hpost := MorphismProperty.RespectsIso.postcomp
    P.presheaf
    eT.hom _ hf
  have hpre := MorphismProperty.RespectsIso.precomp
    P.presheaf
    eS.inv _ hpost
  rw [yoneda_map_pluckerChartSchemeMorphism_comp_representation q n I hI] at hpre
  simpa [P, Category.assoc] using hpre

/-- The Plücker morphism realized on the canonical glued representatives. -/
noncomputable def pluckerGluedSchemeMorphism (q n : ℕ) :
    (grassmannianGlueData.{u} q n).glued ⟶
      (grassmannianGlueData.{u} 1 (n.choose q)).glued :=
  (grassmannianGluedRepresentation 1 (n.choose q)).homEquiv.symm
    ((pluckerMorphism q n).app
      (Opposite.op (grassmannianGlueData.{u} q n).glued)
      ((grassmannianGluedRepresentation q n).homEquiv
        (𝟙 (grassmannianGlueData.{u} q n).glued)))

/-- The scheme morphism between the canonical glued representatives realizes the
natural Plücker morphism. -/
lemma yoneda_map_pluckerGluedSchemeMorphism_comp_representation (q n : ℕ) :
    yoneda.map (pluckerGluedSchemeMorphism.{u} q n) ≫
        (grassmannianGluedRepresentation 1 (n.choose q)).toIso.hom =
      (grassmannianGluedRepresentation q n).toIso.hom ≫
        pluckerMorphism q n := by
  ext T g
  change (grassmannianGluedRepresentation 1 (n.choose q)).homEquiv
      (g ≫ pluckerGluedSchemeMorphism q n) =
    (pluckerMorphism q n).app T
      ((grassmannianGluedRepresentation q n).homEquiv g)
  rw [(grassmannianGluedRepresentation 1 (n.choose q)).homEquiv_comp]
  rw [show (grassmannianGluedRepresentation 1 (n.choose q)).homEquiv
      (pluckerGluedSchemeMorphism q n) =
      (pluckerMorphism q n).app
        (Opposite.op (grassmannianGlueData.{u} q n).glued)
        ((grassmannianGluedRepresentation q n).homEquiv
          (𝟙 (grassmannianGlueData.{u} q n).glued)) by
    exact Equiv.apply_symm_apply _ _]
  rw [← (pluckerMorphism q n).naturality_apply]
  congr 1
  rw [← (grassmannianGluedRepresentation q n).homEquiv_comp]
  simp

/-- The unique coordinate contained in a singleton target-chart index. -/
noncomputable def singletonTargetChartCoordinate (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) : Fin (n.choose q) :=
  (J.down.1.orderIsoOfFin J.down.2) 0

/-- The `q`-subset whose Plücker coordinate indexes a given singleton target chart. -/
noncomputable def pluckerSourceChartIndexOfTarget (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    grassmannianChartCoverIndex.{u} q n :=
  ULift.up ⟨((powersetCardEquivFin q n).symm
    (singletonTargetChartCoordinate q n J)).1,
    ((powersetCardEquivFin q n).symm
      (singletonTargetChartCoordinate q n J)).2⟩

lemma pluckerChartIndex_sourceOfTarget (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
        (pluckerSourceChartIndexOfTarget q n J).down.2 = J.down.1 := by
  let c := singletonTargetChartCoordinate q n J
  let I := pluckerSourceChartIndexOfTarget q n J
  have hJ : J.down.1 = {c} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact (J.down.1.orderIsoOfFin J.down.2 0).2
    · intro x hx
      change x = (J.down.1.orderIsoOfFin J.down.2 0).1
      exact congrArg Subtype.val (by
        apply (J.down.1.orderIsoOfFin J.down.2).symm.injective
        exact Subsingleton.elim _ _ :
          (⟨x, hx⟩ : ↑J.down.1) = J.down.1.orderIsoOfFin J.down.2 0)
  rw [hJ]
  rw [pluckerChartIndex]
  congr 1
  change powersetCardEquivFin q n
      ((powersetCardEquivFin q n).symm c) = c
  exact Equiv.apply_symm_apply _ _

/-- The global Plücker morphism between the canonical schemes glued from the standard
Grassmannian charts. -/
lemma pluckerChartMorphism_comp_chartι (q n : ℕ) (I : Finset (Fin n))
    (hI : I.card = q) :
    pluckerChartMorphism.{u} q n I hI ≫
        grassmannianChartι 1 (n.choose q) (pluckerChartIndex I hI) =
      grassmannianChartι q n I ≫ pluckerMorphism q n := by
  ext T K
  apply Subtype.ext
  change K.1.1.pluckerData q K.1.2 = K.1.1.pluckerData q K.1.2
  rfl

/-- The standard Plücker target chart attached to `J` is the affine chart used by
the canonical glued target cover. -/
noncomputable def pluckerTargetChartIso (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    grassmannianChartAffineSpace.{u}
        (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2) ≅
      grassmannianChartCoverScheme 1 (n.choose q) J :=
  eqToIso (congrArg (fun K : Finset (Fin (n.choose q)) ↦
      grassmannianChartAffineSpace.{u} K)
    (pluckerChartIndex_sourceOfTarget q n J))

/-- The represented target chart, transported from the arbitrary singleton index
`J` to its corresponding Plücker index. -/
noncomputable def pluckerTargetChartRepresentationIso (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    yoneda.obj (grassmannianChartCoverScheme 1 (n.choose q) J) ≅
      grassmannianChart.{u} 1 (n.choose q)
        (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2) :=
  (grassmannianChartCoverRepresentation 1 (n.choose q) J).toIso.trans
    (eqToIso (congrArg (grassmannianChart.{u} 1 (n.choose q))
      (pluckerChartIndex_sourceOfTarget q n J).symm))

/-- The closed affine Plücker chart morphism, with codomain reindexed to an arbitrary
member of the canonical singleton target cover. -/
noncomputable def pluckerAlignedChartSchemeMorphism (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    grassmannianChartCoverScheme q n (pluckerSourceChartIndexOfTarget q n J) ⟶
      grassmannianChartCoverScheme 1 (n.choose q) J :=
  pluckerChartSchemeMorphism q n
      (pluckerSourceChartIndexOfTarget q n J).down.1
      (pluckerSourceChartIndexOfTarget q n J).down.2 ≫
    (pluckerTargetChartIso q n J).hom

lemma isClosedImmersion_pluckerAlignedChartSchemeMorphism (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    IsClosedImmersion (pluckerAlignedChartSchemeMorphism q n J) := by
  let P : MorphismProperty Scheme.{u} := @IsClosedImmersion
  change P (pluckerAlignedChartSchemeMorphism q n J)
  rw [pluckerAlignedChartSchemeMorphism,
    P.cancel_right_of_respectsIso]
  exact isClosedImmersion_pluckerChartSchemeMorphism q n
    (pluckerSourceChartIndexOfTarget q n J).down.1
    (pluckerSourceChartIndexOfTarget q n J).down.2

lemma yoneda_map_pluckerTargetChartIso_comp_chartMap (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    yoneda.map (pluckerTargetChartIso q n J).hom ≫
        grassmannianRepresentableChartMap 1 (n.choose q) J =
      (grassmannianChartAffineRepresentation 1 (n.choose q)
        (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2)
        (pluckerChartIndex_card _ _)).toIso.hom ≫
      grassmannianChartι 1 (n.choose q)
        (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2) := by
  simpa [pluckerTargetChartIso, grassmannianRepresentableChartMap,
    grassmannianChartCoverRepresentation, eqToIso.hom] using
    yoneda_map_eqToHom_comp_grassmannianChartAffineRepresentation
      1 (n.choose q)
      (pluckerChartIndex_card
        (pluckerSourceChartIndexOfTarget q n J).down.1
        (pluckerSourceChartIndexOfTarget q n J).down.2)
      J.down.2 (pluckerChartIndex_sourceOfTarget q n J)

lemma yoneda_map_pluckerAlignedChartSchemeMorphism_comp_representation
    (q n : ℕ) (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    yoneda.map (pluckerAlignedChartSchemeMorphism q n J) ≫
        (pluckerTargetChartRepresentationIso q n J).hom =
      (grassmannianChartCoverRepresentation q n
        (pluckerSourceChartIndexOfTarget q n J)).toIso.hom ≫
        pluckerChartMorphism q n
          (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2 := by
  rw [← cancel_mono (grassmannianChartι 1 (n.choose q)
    (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
      (pluckerSourceChartIndexOfTarget q n J).down.2))]
  rw [Category.assoc, Category.assoc, pluckerChartMorphism_comp_chartι]
  rw [pluckerAlignedChartSchemeMorphism, Functor.map_comp]
  simp only [Category.assoc]
  rw [show (pluckerTargetChartRepresentationIso q n J).hom ≫
      grassmannianChartι 1 (n.choose q)
        (pluckerChartIndex (pluckerSourceChartIndexOfTarget q n J).down.1
          (pluckerSourceChartIndexOfTarget q n J).down.2) =
      grassmannianRepresentableChartMap 1 (n.choose q) J by
    rw [pluckerTargetChartRepresentationIso,
      grassmannianRepresentableChartMap]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [eqToHom_grassmannianChart_comp_chartι 1 (n.choose q)
      (pluckerChartIndex_sourceOfTarget q n J)]]
  rw [yoneda_map_pluckerTargetChartIso_comp_chartMap]
  rw [← Category.assoc]
  rw [yoneda_map_pluckerChartSchemeMorphism_comp_representation]
  simp only [grassmannianChartCoverRepresentation]
  rw [Category.assoc, pluckerChartMorphism_comp_chartι]

/-- The aligned affine chart map commutes with the canonical open-cover maps into the
two glued Grassmannians. -/
lemma pluckerAlignedChartSchemeMorphism_comp_openCover (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    pluckerAlignedChartSchemeMorphism q n J ≫
        (grassmannianGlueData 1 (n.choose q)).openCover.f J =
      (grassmannianGlueData q n).openCover.f
          (pluckerSourceChartIndexOfTarget q n J) ≫
        pluckerGluedSchemeMorphism q n := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  rw [← cancel_mono
    (grassmannianGluedRepresentation 1 (n.choose q)).toIso.hom]
  simp only [Category.assoc]
  rw [yoneda_map_grassmannianGlueData_openCover,
    yoneda_map_pluckerGluedSchemeMorphism_comp_representation]
  rw [← Category.assoc, yoneda_map_grassmannianGlueData_openCover]
  rw [pluckerAlignedChartSchemeMorphism]
  simp only [Functor.map_comp, Category.assoc]
  rw [yoneda_map_pluckerTargetChartIso_comp_chartMap]
  rw [grassmannianRepresentableChartMap]
  rw [← Category.assoc]
  rw [yoneda_map_pluckerChartSchemeMorphism_comp_representation]
  rw [Category.assoc]
  rw [pluckerChartMorphism_comp_chartι]
  simp [grassmannianChartCoverRepresentation, Category.assoc]
lemma isPullback_pluckerChartMorphism (q n : ℕ) (I : Finset (Fin n))
    (hI : I.card = q) :
    IsPullback (pluckerChartMorphism.{u} q n I hI)
      (grassmannianChartι q n I)
      (grassmannianChartι 1 (n.choose q) (pluckerChartIndex I hI))
      (pluckerMorphism q n) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun f ↦ f.app T)
      (pluckerChartMorphism_comp_chartι q n I hI), ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact hab.2
  · intro L K hLK
    have htarget : (K.1.pluckerData q K.2).IsComplementOfCoords
        (pluckerChartIndex I hI) := by
      have heq : L.1.1 = K.1.pluckerData q K.2 := by
        exact congrArg (fun z : (grassmannianFunctor 1 (n.choose q)).obj T ↦ z.1) hLK
      rw [← heq]
      exact L.2
    have hopenTarget :
        (K.1.pluckerData q K.2).coordinateChartOpen (pluckerChartIndex I hI) = ⊤ :=
      SubmoduleSheafData.coordinateChartOpen_eq_top_of_isComplementOfCoords htarget
    have hopenSource : K.1.coordinateChartOpen I = ⊤ := by
      rw [← K.1.pluckerData_coordinateChartOpen_eq q K.2 I hI]
      exact hopenTarget
    have hsource : K.1.IsComplementOfCoords I :=
      (K.1.isComplementOfCoords_iff_coordinateChartOpen_eq_top_of_rank
        I hI K.2).mpr hopenSource
    refine ⟨⟨K, hsource⟩, ?_, rfl⟩
    apply Subtype.ext
    exact hLK.symm
/-- The restriction square defining the aligned Plücker chart is cartesian. -/
lemma isPullback_pluckerAlignedChartSchemeMorphism (q n : ℕ)
    (J : grassmannianChartCoverIndex.{u} 1 (n.choose q)) :
    IsPullback (pluckerAlignedChartSchemeMorphism q n J)
      ((grassmannianGlueData q n).openCover.f
        (pluckerSourceChartIndexOfTarget q n J))
      ((grassmannianGlueData 1 (n.choose q)).openCover.f J)
      (pluckerGluedSchemeMorphism q n) := by
  apply IsPullback.of_map yoneda
  · exact pluckerAlignedChartSchemeMorphism_comp_openCover q n J
  · refine (isPullback_pluckerChartMorphism q n
      (pluckerSourceChartIndexOfTarget q n J).down.1
      (pluckerSourceChartIndexOfTarget q n J).down.2).of_iso'
      (grassmannianChartCoverRepresentation q n
        (pluckerSourceChartIndexOfTarget q n J)).toIso
      (pluckerTargetChartRepresentationIso q n J)
      (grassmannianGluedRepresentation q n).toIso
      (grassmannianGluedRepresentation 1 (n.choose q)).toIso
      ?_ ?_ ?_ ?_
    · exact (yoneda_map_pluckerAlignedChartSchemeMorphism_comp_representation
        q n J).symm
    · exact (yoneda_map_grassmannianGlueData_openCover q n
        (pluckerSourceChartIndexOfTarget q n J)).symm
    · rw [pluckerTargetChartRepresentationIso, Iso.trans_hom,
        Category.assoc]
      rw [eqToIso.hom, eqToHom_grassmannianChart_comp_chartι 1 (n.choose q)
        (pluckerChartIndex_sourceOfTarget q n J)]
      exact (yoneda_map_grassmannianGlueData_openCover 1 (n.choose q) J).symm
    · exact (yoneda_map_pluckerGluedSchemeMorphism_comp_representation q n).symm

/-- API lemma for Proposition 2.2.8 (scheme-level form): the global
Plücker morphism between the glued Grassmannian representatives is a closed immersion,
checked Zariski-locally on the target against the standard chart cover. -/
lemma isClosedImmersion_pluckerGluedSchemeMorphism (q n : ℕ) :
    IsClosedImmersion (pluckerGluedSchemeMorphism.{u} q n) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsClosedImmersion)
    (grassmannianGlueData 1 (n.choose q)).openCover]
  intro J
  change IsClosedImmersion (pullback.snd (pluckerGluedSchemeMorphism q n)
    ((grassmannianGlueData 1 (n.choose q)).openCover.f J))
  let h := (isPullback_pluckerAlignedChartSchemeMorphism q n J).flip
  let P : MorphismProperty Scheme.{u} := @IsClosedImmersion
  change P (pullback.snd (pluckerGluedSchemeMorphism q n)
    ((grassmannianGlueData 1 (n.choose q)).openCover.f J))
  rw [← P.cancel_left_of_respectsIso h.isoPullback.hom]
  rw [h.isoPullback_hom_snd]
  exact isClosedImmersion_pluckerAlignedChartSchemeMorphism q n J
/-- The Plücker morphism after base change from `Spec ℤ` to a scheme `S`. -/
noncomputable def pluckerOverMorphism (S : Scheme.{u}) (q n : ℕ) :
    (grassmannianOverRepresentation S q n).left ⟶
      (grassmannianOverRepresentation S 1 (n.choose q)).left :=
  pullback.lift
    (pullback.fst (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (grassmannianGlueData q n).glued))
    (pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (grassmannianGlueData q n).glued) ≫
      pluckerGluedSchemeMorphism q n)
    (specULiftZIsTerminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma pluckerOverMorphism_fst (S : Scheme.{u}) (q n : ℕ) :
    pluckerOverMorphism S q n ≫
        pullback.fst (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from
            (grassmannianGlueData 1 (n.choose q)).glued) =
      pullback.fst (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (grassmannianGlueData q n).glued) := by
  simp [pluckerOverMorphism]

@[reassoc (attr := simp)]
lemma pluckerOverMorphism_snd (S : Scheme.{u}) (q n : ℕ) :
    pluckerOverMorphism S q n ≫
        pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from
            (grassmannianGlueData 1 (n.choose q)).glued) =
      pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (grassmannianGlueData q n).glued) ≫
        pluckerGluedSchemeMorphism q n := by
  simp [pluckerOverMorphism]

/-- The relative Plücker square is cartesian. -/
lemma isPullback_pluckerOverMorphism (S : Scheme.{u}) (q n : ℕ) :
    IsPullback (pluckerOverMorphism S q n)
      (pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (grassmannianGlueData q n).glued))
      (pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from
          (grassmannianGlueData 1 (n.choose q)).glued))
      (pluckerGluedSchemeMorphism q n) := by
  refine IsPullback.of_isLimit' ⟨pluckerOverMorphism_snd S q n⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ pullback.lift
    (s.fst ≫ pullback.fst _ _) s.snd
    (specULiftZIsTerminal.hom_ext _ _)) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pluckerOverMorphism_snd]
      simpa using s.condition.symm
  · intro s
    simp
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hm₁, Category.assoc,
        pluckerOverMorphism_fst]
    · rw [pullback.lift_snd, ← hm₂]

/-- The relative Plücker morphism is a closed immersion. -/
lemma isClosedImmersion_pluckerOverMorphism (S : Scheme.{u}) (q n : ℕ) :
    IsClosedImmersion (pluckerOverMorphism S q n) :=
  MorphismProperty.of_isPullback (isPullback_pluckerOverMorphism S q n).flip
    (isClosedImmersion_pluckerGluedSchemeMorphism q n)

/-- API lemma for Theorem 2.1.1 (projectivity, free case):
the base-changed representative of the free relative Grassmannian is strongly projective
over its base, via the relative Plücker embedding (the book's Plücker-embedding equation,
here obtained by base-changing the absolute one from `Spec ℤ`). -/
theorem grassmannianOverRepresentation_isStronglyProjective
    (S : Scheme.{u}) (q n : ℕ) :
    IsStronglyProjective (grassmannianOverRepresentation S q n).hom := by
  let E := SheafOfModules.free (R := S.ringCatSheaf)
    (ULift.{u} (Fin (n.choose q)))
  have hqc : E.IsQuasicoherent := by
    dsimp [E]
    infer_instance
  have hfl : Modules.IsFiniteLocallyFree E := by
    dsimp [E]
    exact Modules.free_isFiniteLocallyFree S (n.choose q)
  refine ⟨E, hqc, hfl,
    grassmannianOverRepresentation S 1 (n.choose q), ?_,
    pluckerOverMorphism S q n,
    isClosedImmersion_pluckerOverMorphism S q n, ?_⟩
  · exact freeGrassmannianRepresentableBy S 1 (n.choose q)
  · exact pluckerOverMorphism_fst S q n

/-- API lemma for Theorem 2.1.1 (the case of a free
bundle): relative representability and strong projectivity for the Grassmannian of the
canonical rank-`n` free bundle. -/
theorem exists_free_grassmannianOverFunctor_representableBy
    (S : Scheme.{u}) (q n : ℕ) :
    ∃ P : Over S,
      Nonempty ((Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin n)))).RepresentableBy P) ∧
        IsStronglyProjective P.hom := by
  exact ⟨grassmannianOverRepresentation S q n,
    ⟨freeGrassmannianRepresentableBy S q n⟩,
    grassmannianOverRepresentation_isStronglyProjective S q n⟩

section ExteriorPowerSheafSections

/-! ### Sections of the exterior-power sheaf on affine opens

Supporting material for the general case of `thm:grassmannian-projective-relative`: the
exterior-power sheaf `⋀^q V` of a quasi-coherent sheaf (constructed in
`StacksAndModuli/API/ExteriorPowerQcoh.lean` and `.../ExteriorPowerRestrict.lean`) is
quasi-coherent and finite locally free of rank `C(n, q)` whenever `V` is finite locally
free of rank `n`.  The section computations transport the tilde comparison
`(⋀[R]^q M₀)~ ≅ ⋀^q (M₀~)` along restrictions to affine opens. -/

namespace Modules

open CategoryTheory

/-- Finiteness, projectivity and constant rank of sections transport from the
restriction along an open immersion to the corresponding image open. -/
lemma sections_finite_projective_rank_of_restrict_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    {q : ℕ}
    (hfin : Module.Finite Γ(X, U) Γ(M.restrict f, U))
    (hproj : Module.Projective Γ(X, U) Γ(M.restrict f, U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U),
      Module.rankAtStalk Γ(M.restrict f, U) p = q) :
    Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) ∧
      Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) ∧
      ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ U),
        Module.rankAtStalk Γ(M, f ''ᵁ U) p = q := by
  let eR := (f.appIso U).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M.restrict f, U) ≃ₛₗ[(eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))]
      Γ(M, f ''ᵁ U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).hom
          invFun := (M.restrictAppIso f U).inv
          left_inv := fun m => by simp
          right_inv := fun m => by simp }
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        change (M.restrictAppIso f U).hom (r • m) =
          (f.appIso U).inv r • (M.restrictAppIso f U).hom m
        simp }
  exact Module.finite_projective_rankAtStalk_of_semilinearEquiv eR rfl eM
    hfin hproj hrank

/-- The exterior power of a quasi-coherent sheaf on an affine scheme is
quasi-coherent. -/
instance spec_exteriorPower_isQuasicoherent {R : CommRingCat.{u}}
    (W : (Spec R).Modules) [W.IsQuasicoherent] (q : ℕ) :
    (Modules.exteriorPower W q).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (Modules.exteriorPowerIso (asIso (Scheme.Modules.fromTildeΓ W)) q)
    (inferInstance : (Modules.exteriorPower (ModuleCat.tilde
      ((modulesSpecToSheaf.obj W).presheaf.obj (Opposite.op ⊤))) q).IsQuasicoherent)

set_option maxHeartbeats 1600000 in

/-- **Sections of the exterior power over an affine scheme**: for a quasi-coherent sheaf
with finite projective sections of constant rank `n`, the exterior-power sheaf has finite
projective global sections of constant rank `C(n, q)`. -/
lemma spec_exteriorPower_sections_finite_projective_rank {R : CommRingCat.{u}}
    (W : (Spec R).Modules) [W.IsQuasicoherent] {n : ℕ} (q : ℕ)
    (hfin : Module.Finite Γ(Spec R, ⊤) Γ(W, ⊤))
    (hproj : Module.Projective Γ(Spec R, ⊤) Γ(W, ⊤))
    (hrank : ∀ p : PrimeSpectrum Γ(Spec R, ⊤), Module.rankAtStalk Γ(W, ⊤) p = n) :
    Module.Finite Γ(Spec R, ⊤) Γ(Modules.exteriorPower W q, ⊤) ∧
      Module.Projective Γ(Spec R, ⊤) Γ(Modules.exteriorPower W q, ⊤) ∧
      ∀ p : PrimeSpectrum Γ(Spec R, ⊤),
        Module.rankAtStalk Γ(Modules.exteriorPower W q, ⊤) p = n.choose q := by
  obtain ⟨hNfin, hNproj, hNrank⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_of_top W hfin hproj hrank
  set M₀ : ModuleCat R := (modulesSpecToSheaf.obj W).presheaf.obj (Opposite.op ⊤)
    with hM₀
  haveI h1 : Module.Finite R M₀ := hNfin
  haveI h2 : Module.Projective R M₀ := hNproj
  have h3 : ∀ p : PrimeSpectrum R, Module.rankAtStalk (M₀ : Type u) p = n := hNrank
  have hWfin : Module.Finite R
      (⋀[R]^q (M₀ : Type u) : Submodule R (ExteriorAlgebra R M₀)) := inferInstance
  have hWproj : Module.Projective R
      (⋀[R]^q (M₀ : Type u) : Submodule R (ExteriorAlgebra R M₀)) :=
    exteriorPower.projective_exteriorPower
  have hWrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        (⋀[R]^q (M₀ : Type u) : Submodule R (ExteriorAlgebra R M₀)) p = n.choose q := by
    intro p
    rw [exteriorPower.rankAtStalk_exteriorPower, h3]
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, (⊤ : (Spec R).Opens)) := eR.symm.toRingHom.toAlgebra
  letI : RingHomInvPair (eR.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens)))
      (eR.symm.symm : Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R) :=
    RingHomInvPair.of_ringEquiv eR.symm
  letI : RingHomInvPair (eR.symm.symm : Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R)
      (eR.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens))) := ⟨by ext; simp, by ext; simp⟩
  let eM : (⋀[R]^q (M₀ : Type u) : Submodule R (ExteriorAlgebra R M₀))
      ≃ₛₗ[(eR.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens)))]
      Γ(Modules.exteriorPower (ModuleCat.tilde M₀) q, (⊤ : (Spec R).Opens)) :=
    { toEquiv := (exteriorPowerTildeΓEquiv M₀ q).toEquiv
      map_add' := fun a b ↦ (exteriorPowerTildeΓEquiv M₀ q).map_add a b
      map_smul' := fun r w ↦ by
        change exteriorPowerTildeΓEquiv M₀ q (r • w) =
          (eR.symm r) • exteriorPowerTildeΓEquiv M₀ q w
        rw [LinearEquiv.map_smul, Scheme.Modules.smul_Spec_def]
        rw [show ((⊤ : (Spec R).Opens).leTop).op =
          𝟙 (Opposite.op (⊤ : (Spec R).Opens)) from rfl]
        rw [CategoryTheory.Functor.map_id]
        rfl }
  have hspec := Module.finite_projective_rankAtStalk_of_semilinearEquiv
    (q := n.choose q) eR.symm rfl eM hWfin hWproj hWrank
  exact sections_finite_projective_rank_of_iso
    (Modules.exteriorPowerIso (asIso (Scheme.Modules.fromTildeΓ W)) q) ⊤
    hspec.1 hspec.2.1 hspec.2.2

/-- **The exterior power of a rank-`n` vector bundle is a rank-`C(n, q)` vector
bundle.** -/
theorem isProjectiveOfRank_exteriorPower {X : Scheme.{u}} (V : X.Modules)
    [V.IsQuasicoherent] {n : ℕ} (hV : Modules.IsProjectiveOfRank n V) (q : ℕ) :
    Modules.IsProjectiveOfRank (n.choose q) (Modules.exteriorPower V q) := by
  intro x
  obtain ⟨U, hx, hfin, hproj, hrank⟩ := hV x
  have himU : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  obtain ⟨h1fin, h1proj, h1rank⟩ :=
    Scheme.Modules.restrict_sections_finite_projective_rank U.1.ι V ⊤ (q := n)
      (by rw [himU]; exact hfin) (by rw [himU]; exact hproj)
      (by rw [himU]; exact hrank)
  have himSpec : U.2.isoSpec.inv ''ᵁ
      (⊤ : (Spec (.of Γ(X, U.1))).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  obtain ⟨h2fin, h2proj, h2rank⟩ :=
    Scheme.Modules.restrict_sections_finite_projective_rank U.2.isoSpec.inv
      (V.restrict U.1.ι) ⊤ (q := n)
      (by rw [himSpec]; exact h1fin) (by rw [himSpec]; exact h1proj)
      (by rw [himSpec]; exact h1rank)
  obtain ⟨h3fin, h3proj, h3rank⟩ :=
    spec_exteriorPower_sections_finite_projective_rank
      ((V.restrict U.1.ι).restrict U.2.isoSpec.inv) q h2fin h2proj h2rank
  obtain ⟨h4fin, h4proj, h4rank⟩ :=
    sections_finite_projective_rank_of_iso
      (restrictExteriorPowerIso U.2.isoSpec.inv (V.restrict U.1.ι) q) ⊤
      h3fin h3proj h3rank
  obtain ⟨h5fin, h5proj, h5rank⟩ :=
    sections_finite_projective_rank_of_restrict_openImmersion U.2.isoSpec.inv
      (Modules.exteriorPower (V.restrict U.1.ι) q) ⊤ h4fin h4proj h4rank
  rw [himSpec] at h5fin h5proj h5rank
  obtain ⟨h6fin, h6proj, h6rank⟩ :=
    sections_finite_projective_rank_of_iso
      (restrictExteriorPowerIso U.1.ι V q) ⊤ h5fin h5proj h5rank
  obtain ⟨h7fin, h7proj, h7rank⟩ :=
    sections_finite_projective_rank_of_restrict_openImmersion U.1.ι
      (Modules.exteriorPower V q) ⊤ h6fin h6proj h6rank
  rw [himU] at h7fin h7proj h7rank
  exact ⟨U, hx, h7fin, h7proj, h7rank⟩

/-- The exterior power of a quasi-coherent sheaf is quasi-coherent. -/
instance isQuasicoherent_exteriorPower {X : Scheme.{u}} (V : X.Modules)
    [V.IsQuasicoherent] (q : ℕ) :
    (Modules.exteriorPower V q).IsQuasicoherent := by
  haveI : ∀ i, ((Modules.restrictFunctor (X.affineCover.f i)).obj
      (Modules.exteriorPower V q)).IsQuasicoherent := fun i ↦
    (SheafOfModules.isQuasicoherent (X.affineCover.X i).ringCatSheaf).prop_of_iso
      (restrictExteriorPowerIso (X.affineCover.f i) V q)
      (spec_exteriorPower_isQuasicoherent (V.restrict (X.affineCover.f i)) q)
  exact Modules.isQuasicoherent_of_openCover_restrict (Modules.exteriorPower V q)
    X.affineCover

/-- An epimorphism of quasi-coherent sheaves of modules is surjective on sections over
affine opens. -/
lemma app_surjective_of_epi {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] (U : X.affineOpens) :
    Function.Surjective (φ.app U.1) := by
  have himU : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have himSpec : U.2.isoSpec.inv ''ᵁ
      (⊤ : (Spec (.of Γ(X, U.1))).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  haveI : Epi ((Modules.restrictFunctor U.1.ι).map φ) := inferInstance
  haveI : Epi ((Modules.restrictFunctor U.2.isoSpec.inv).map
      ((Modules.restrictFunctor U.1.ι).map φ)) := inferInstance
  have hsurj := Scheme.Modules.moduleSpecΓFunctor_map_surjective_of_epi
    ((Modules.restrictFunctor U.2.isoSpec.inv).map
      ((Modules.restrictFunctor U.1.ι).map φ))
  have h2 : Function.Surjective
      (((Modules.restrictFunctor U.2.isoSpec.inv).map
        ((Modules.restrictFunctor U.1.ι).map φ)).app
          (⊤ : (Spec (.of Γ(X, U.1))).Opens)) := hsurj
  have h3 : Function.Surjective
      (((Modules.restrictFunctor U.1.ι).map φ).app
        (U.2.isoSpec.inv ''ᵁ (⊤ : (Spec (.of Γ(X, U.1))).Opens))) := h2
  rw [himSpec] at h3
  have h4 : Function.Surjective
      (φ.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) := h3
  rw [himU] at h4
  exact h4

set_option maxHeartbeats 1600000 in
/-- The exterior-power sheaf map of an epimorphism of quasi-coherent sheaves is an
epimorphism. -/
theorem epi_exteriorPowerMap {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] (q : ℕ) :
    Epi (Modules.exteriorPowerMap φ q) := by
  refine SheafOfModules.epi_of_isLocallySurjective (Modules.exteriorPowerMap φ q) ?_
  constructor
  intro U t x hx
  -- the sheafification unit is locally surjective: presheaf preimage near `x`
  obtain ⟨V₁, f₁, hf₁, hxV₁⟩ := Presheaf.imageSieve_mem
    (Opens.grothendieckTopology ↥X)
    ((_root_.PresheafOfModules.toPresheaf _).map (Modules.toExteriorPower N q))
    (U := Opposite.op U)
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        (Modules.exteriorPower N q).val)).obj (Opposite.op U)) from t) x hx
  obtain ⟨w, hw⟩ := hf₁
  -- shrink to an affine open around `x`
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV₁ V₁.2
  set A : X.affineOpens := ⟨W', hW'⟩
  -- the presheaf-level exterior power map is surjective over the affine open
  have hφs : Function.Surjective (φ.app A.1) := app_surjective_of_epi φ A
  have hpre : Function.Surjective
      (_root_.PresheafOfModules.exteriorPowerMapApp (R := X.sheaf.val)
        (M₁ := (M.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)))
        (M₂ := (N.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) q
        ((SheafOfModules.forget _).map φ) (Opposite.op A.1)) := by
    refine exteriorPower.map_surjective ?_
    exact hφs
  -- restrict the presheaf preimage and lift it through the exterior power map
  obtain ⟨v, hv⟩ := hpre
    ((_root_.PresheafOfModules.exteriorPower
      (M := (N.val : _root_.PresheafOfModules.{u}
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) q).map
          (homOfLE hWV).op w)
  refine ⟨A.1, homOfLE (hWV.trans (leOfHom f₁)), ?_, hxW⟩
  refine ⟨((_root_.PresheafOfModules.toPresheaf _).map
    (Modules.toExteriorPower M q)).app (Opposite.op A.1) v, ?_⟩
  -- naturality of the sheafification unit with respect to the exterior power map
  have hnat1 := CategoryTheory.congr_fun (NatTrans.congr_app
    (CategoryTheory.toSheafify_naturality
      (J := Opens.grothendieckTopology ↥X)
      ((_root_.PresheafOfModules.toPresheaf _).map
        (_root_.PresheafOfModules.exteriorPowerMap (R := X.sheaf.val) q
          (show (M.val : _root_.PresheafOfModules.{u}
              (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
            (N.val : _root_.PresheafOfModules.{u}
              (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
            (SheafOfModules.forget _).map φ)))) (Opposite.op A.1)) v
  have hv' := congrArg (ConcreteCategory.hom
    (((_root_.PresheafOfModules.toPresheaf _).map
      (Modules.toExteriorPower N q)).app (Opposite.op A.1))) hv
  have hnat2 := _root_.PresheafOfModules.naturality_apply
    (Modules.toExteriorPower N q) (homOfLE hWV).op w
  have hres := congrArg (ConcreteCategory.hom
    (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        (Modules.exteriorPower N q).val)).map (homOfLE hWV).op)) hw
  have hsplit := _root_.PresheafOfModules.map_comp_apply
    (M := (_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
      (Modules.exteriorPower N q).val) f₁.op (homOfLE hWV).op
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        (Modules.exteriorPower N q).val)).obj (Opposite.op U)) from t)
  exact hnat1.symm.trans (hv'.trans (hnat2.trans (hres.trans hsplit.symm)))

-- the sheaf-of-modules covering argument crosses several defeq spellings of sections
set_option maxHeartbeats 1600000 in
/-- Being an epimorphism of quasi-coherent sheaves of modules descends from the members
of an open cover. -/
theorem epi_of_openCover_restrict {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N)
    (𝒰 : Scheme.OpenCover.{u} X)
    (h : ∀ i, Epi ((Modules.restrictFunctor (𝒰.f i)).map g)) : Epi g := by
  refine SheafOfModules.epi_of_isLocallySurjective g ?_
  constructor
  intro U t x hx
  -- land in a chart and shrink to an affine open of the chart source
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have hyU : y ∈ (𝒰.f (𝒰.idx x)) ⁻¹ᵁ U := by
    change (𝒰.f (𝒰.idx x)).base y ∈ (U : Set X)
    have hyx : (𝒰.f (𝒰.idx x)).base y = x := hy
    rw [hyx]
    exact hx
  obtain ⟨_, ⟨W', hW', rfl⟩, hyW, hWU⟩ :=
    (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open hyU
      ((𝒰.f (𝒰.idx x)) ⁻¹ᵁ U).2
  set A : (𝒰.X (𝒰.idx x)).affineOpens := ⟨W', hW'⟩
  haveI := h (𝒰.idx x)
  have hsurj : Function.Surjective
      (((Modules.restrictFunctor (𝒰.f (𝒰.idx x))).map g).app A.1) :=
    app_surjective_of_epi ((Modules.restrictFunctor (𝒰.f (𝒰.idx x))).map g) A
  -- the restricted app is the app over the image open
  have himAU : (𝒰.f (𝒰.idx x)) ''ᵁ A.1 ≤ U :=
    ((𝒰.f (𝒰.idx x)).image_mono hWU).trans ((𝒰.f (𝒰.idx x)).image_preimage_le U)
  have hsurj' : Function.Surjective (g.app ((𝒰.f (𝒰.idx x)) ''ᵁ A.1)) := hsurj
  obtain ⟨s, hs⟩ := hsurj'
    (show ToType (Scheme.Modules.presheaf N |>.obj
        (Opposite.op ((𝒰.f (𝒰.idx x)) ''ᵁ A.1))) from
      (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).obj
          ((SheafOfModules.forget _).obj N)).map (homOfLE himAU).op)) t)
  exact ⟨(𝒰.f (𝒰.idx x)) ''ᵁ A.1, homOfLE himAU, ⟨s, hs⟩, ⟨y, hyW, hy⟩⟩


set_option maxHeartbeats 1600000 in
-- the localization transfer crosses the compHom module structures on sections
/-- Finite projectivity of constant rank passes from an affine open to its basic
opens. -/
lemma sections_finite_projective_rank_basicOpen {X : Scheme.{u}} (N : X.Modules)
    [N.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) {rk : ℕ}
    (hfin : Module.Finite Γ(X, U) Γ(N, U))
    (hproj : Module.Projective Γ(X, U) Γ(N, U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk Γ(N, U) p = rk) :
    Module.Finite Γ(X, X.basicOpen r) Γ(N, X.basicOpen r) ∧
      Module.Projective Γ(X, X.basicOpen r) Γ(N, X.basicOpen r) ∧
      ∀ p : PrimeSpectrum Γ(X, X.basicOpen r),
        Module.rankAtStalk Γ(N, X.basicOpen r) p = rk := by
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom).toAlgebra
  letI : Module Γ(X, U) Γ(N, X.basicOpen r) :=
    Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom)
  haveI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r) Γ(N, X.basicOpen r) :=
    ⟨fun a b m ↦ by
      show ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a * b) • m =
        ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom a) • b • m
      rw [mul_smul]⟩
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  haveI hloc := Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap N hU r
  haveI : Module.Finite Γ(X, U) Γ(N, U) := hfin
  haveI : Module.Projective Γ(X, U) Γ(N, U) := hproj
  refine ⟨?_, ?_, ?_⟩
  · exact Module.Finite.of_isLocalizedModule (Submonoid.powers r)
      (Scheme.Modules.resBasicOpenLinearMap N r)
  · exact Module.projective_of_isLocalizedModule (Submonoid.powers r)
      (Scheme.Modules.resBasicOpenLinearMap N r)
  · intro p
    have hbc : IsBaseChange Γ(X, X.basicOpen r)
        (Scheme.Modules.resBasicOpenLinearMap N r) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) _ _).mp hloc
    rw [Module.rankAtStalk_isBaseChange hbc p]
    exact hrank _


set_option maxHeartbeats 1600000 in
-- the two-step affine shrink crosses several section spellings
/-- **An epimorphism between vector bundles of the same rank is an isomorphism.** -/
theorem isIso_of_epi_of_isProjectiveOfRank {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {rk : ℕ}
    (hM : Modules.IsProjectiveOfRank rk M) (hN : Modules.IsProjectiveOfRank rk N)
    (φ : M ⟶ N) [Epi φ] : IsIso φ := by
  -- it suffices to prove `φ` is a monomorphism
  suffices hmono : Mono φ from isIso_of_mono_of_epi φ
  suffices hinj : ∀ (V : X.Opens), Function.Injective (φ.app V) by
    refine Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf) ?_
    exact _root_.PresheafOfModules.mono_of_injective (fun V ↦ hinj V.unop)
  intro V s₁ s₂ hs
  -- injectivity is local: shrink to affines where both bundles are free of rank `rk`
  refine (Scheme.Modules.isSheaf M).section_ext (U := Opposite.op V) ?_
  intro x hx
  obtain ⟨A, hxA, hAfin, hAproj, hArank⟩ := hM x
  obtain ⟨B, hxB, hBfin, hBproj, hBrank⟩ := hN x
  -- shrink `A` into `V`
  obtain ⟨f₀, hf₀V, hxf₀⟩ := A.2.exists_basicOpen_le (V := V) ⟨x, hx⟩ hxA
  obtain ⟨hA'fin, hA'proj, hA'rank⟩ :=
    sections_finite_projective_rank_basicOpen M A.2 f₀ hAfin hAproj hArank
  -- find a common basic open of the shrunk `A` and of `B`
  obtain ⟨g, h, hgh, hxg⟩ := exists_basicOpen_le_affine_inter
    (U := X.basicOpen f₀) (A.2.basicOpen f₀) (V := B.1) B.2 x ⟨hxf₀, hxB⟩
  obtain ⟨hWfinM, hWprojM, hWrankM⟩ :=
    sections_finite_projective_rank_basicOpen M (A.2.basicOpen f₀) g
      hA'fin hA'proj hA'rank
  obtain ⟨hWfinN, hWprojN, hWrankN⟩ :=
    sections_finite_projective_rank_basicOpen N B.2 h hBfin hBproj hBrank
  have hWV : X.basicOpen g ≤ V := (X.basicOpen_le g).trans hf₀V
  refine ⟨X.basicOpen g, hWV, hxg, ?_⟩
  -- on that basic open the section map is a surjection of equal-rank projectives
  haveI : Module.Finite Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) := hWfinM
  haveI : Module.Projective Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) := hWprojM
  haveI : Module.Finite Γ(X, X.basicOpen g) Γ(N, X.basicOpen g) := hgh ▸ hWfinN
  haveI : Module.Projective Γ(X, X.basicOpen g) Γ(N, X.basicOpen g) := hgh ▸ hWprojN
  have hrankM : ∀ p : PrimeSpectrum Γ(X, X.basicOpen g),
      Module.rankAtStalk Γ(M, X.basicOpen g) p = rk := hWrankM
  have hrankN : ∀ p : PrimeSpectrum Γ(X, X.basicOpen g),
      Module.rankAtStalk Γ(N, X.basicOpen g) p = rk := hgh ▸ hWrankN
  haveI : Module.Flat Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) :=
    Module.Flat.of_projective
  haveI : Module.Flat Γ(X, X.basicOpen g) Γ(N, X.basicOpen g) :=
    Module.Flat.of_projective
  have hsurj : Function.Surjective (φ.app (X.basicOpen g)) :=
    app_surjective_of_epi φ ⟨X.basicOpen g, (A.2.basicOpen f₀).basicOpen g⟩
  let ψ : Γ(M, X.basicOpen g) →ₗ[Γ(X, X.basicOpen g)] Γ(N, X.basicOpen g) :=
    { toFun := φ.app (X.basicOpen g)
      map_add' := map_add _
      map_smul' := fun c x ↦ Scheme.Modules.Hom.app_smul φ c x }
  have hbij : Function.Bijective ψ := by
    refine Module.bijective_of_surjective_of_rankAtStalk_eq hsurj ?_
    intro m hm
    rw [hrankM ⟨m, hm.isPrime⟩, hrankN ⟨m, hm.isPrime⟩]
  -- hence the two sections agree there
  have hres := congrArg (ConcreteCategory.hom
    (((_root_.PresheafOfModules.toPresheaf _).obj
      ((SheafOfModules.forget _).obj N)).map (homOfLE hWV).op)) hs
  have hnat₁ := _root_.PresheafOfModules.naturality_apply
    ((SheafOfModules.forget _).map φ) (homOfLE hWV).op s₁
  have hnat₂ := _root_.PresheafOfModules.naturality_apply
    ((SheafOfModules.forget _).map φ) (homOfLE hWV).op s₂
  exact hbij.1 (hnat₁.trans (hres.trans hnat₂.symm))



/-- **The pullback comparison for exterior powers is an isomorphism** for a vector bundle:
`f^*(⋀^q V) ≅ ⋀^q(f^* V)`. -/
theorem isIso_pullbackExteriorPower {T S : Scheme.{u}} (f : T ⟶ S) (V : S.Modules)
    [V.IsQuasicoherent] {n : ℕ} (hV : Modules.IsProjectiveOfRank n V) (q : ℕ) :
    IsIso (pullbackExteriorPower f V q) := by
  haveI := epi_pullbackExteriorPower f V q
  have h1 : Modules.IsProjectiveOfRank (n.choose q)
      ((Modules.pullback f).obj (Modules.exteriorPower V q)) :=
    (isProjectiveOfRank_exteriorPower V hV q).pullback f
  have h2 : Modules.IsProjectiveOfRank (n.choose q)
      (Modules.exteriorPower ((Modules.pullback f).obj V) q) :=
    isProjectiveOfRank_exteriorPower ((Modules.pullback f).obj V) (hV.pullback f) q
  exact isIso_of_epi_of_isProjectiveOfRank h1 h2 _

/-- The exterior-power comparison isomorphism for a vector bundle. -/
noncomputable def pullbackExteriorPowerIso {T S : Scheme.{u}} (f : T ⟶ S) (V : S.Modules)
    [V.IsQuasicoherent] {n : ℕ} (hV : Modules.IsProjectiveOfRank n V) (q : ℕ) :
    (Modules.pullback f).obj (Modules.exteriorPower V q) ≅
      Modules.exteriorPower ((Modules.pullback f).obj V) q :=
  letI := isIso_pullbackExteriorPower f V hV q
  asIso (pullbackExteriorPower f V q)



/-- **The Plücker quotient** (the Plücker-embedding equation): the top exterior power of a
rank-`q` locally free quotient `V_T ↠ Q` is a line bundle quotient of `(⋀^q V)_T`,
through the exterior-power pullback comparison. -/
noncomputable def PullbackQuotient.plucker {S : Scheme.{u}} {q : ℕ} {V : S.Modules}
    [V.IsQuasicoherent] {T : Over S} (x : PullbackQuotient q V T) :
    PullbackQuotient 1 (Modules.exteriorPower V q) T where
  Q := Modules.exteriorPower x.Q q
  isQuasicoherent := by
    haveI := x.isQuasicoherent
    infer_instance
  isProjectiveOfRank := by
    haveI := x.isQuasicoherent
    have h := isProjectiveOfRank_exteriorPower x.Q x.isProjectiveOfRank q
    rwa [Nat.choose_self] at h
  π := pullbackExteriorPower T.hom V q ≫ Modules.exteriorPowerMap x.π q
  epi := by
    haveI := x.isQuasicoherent
    haveI := x.epi
    haveI := epi_pullbackExteriorPower T.hom V q
    haveI := epi_exteriorPowerMap x.π q
    exact epi_comp _ _

/-- The Plücker quotient respects the equivalence of quotient presentations. -/
lemma PullbackQuotient.plucker_r {S : Scheme.{u}} {q : ℕ} {V : S.Modules}
    [V.IsQuasicoherent] {T : Over S} {x y : PullbackQuotient q V T}
    (h : (PullbackQuotient.setoid q V T).r x y) :
    (PullbackQuotient.setoid 1 (Modules.exteriorPower V q) T).r x.plucker y.plucker := by
  obtain ⟨e, he⟩ := h
  refine ⟨Modules.exteriorPowerIso e q, ?_⟩
  show (pullbackExteriorPower T.hom V q ≫ Modules.exteriorPowerMap x.π q) ≫
      (Modules.exteriorPowerIso e q).hom =
    pullbackExteriorPower T.hom V q ≫ Modules.exteriorPowerMap y.π q
  rw [Category.assoc]
  refine congrArg (fun k ↦ pullbackExteriorPower T.hom V q ≫ k) ?_
  rw [show (Modules.exteriorPowerIso e q).hom = Modules.exteriorPowerMap e.hom q from rfl,
    ← Modules.exteriorPowerMap_comp, he]



/-- **The Plücker morphism of representing schemes** (the Plücker-embedding equation): applying
the Plücker quotient to the universal quotient on a scheme representing `Gr(q, V)` gives a
point of `Gr(1, ⋀^q V)`, hence a morphism of representing schemes over `S`. -/
noncomputable def pluckerMorphismOfRepr {S : Scheme.{u}} {q : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P') :
    P ⟶ P' :=
  repr'.homEquiv.symm
    (Quotient.map PullbackQuotient.plucker
      (fun _ _ h ↦ PullbackQuotient.plucker_r h) (repr.homEquiv (𝟙 P)))

/-- API lemma for Theorem 2.1.1 (projectivity, general
vector bundle, modulo the closed-immersion property): given representing schemes for
`Gr(q, V)` and for `Gr(1, ⋀^q V)`, and given that the Plücker morphism between them is a
closed immersion, the relative Grassmannian is strongly projective over the base. -/
theorem isStronglyProjective_of_representableBy {S : Scheme.{u}} {q n : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V) {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P')
    (hclosed : IsClosedImmersion (pluckerMorphismOfRepr V repr repr').left) :
    IsStronglyProjective P.hom :=
  ⟨Modules.exteriorPower V q, inferInstance,
    (isProjectiveOfRank_exteriorPower V hV q).isFiniteLocallyFree, P', repr',
    (pluckerMorphismOfRepr V repr repr').left, hclosed, Over.w _⟩



set_option maxHeartbeats 3200000 in
-- the naturality square unfolds the two exterior-power coherences
/-- **The Plücker quotient is natural in the test object**: pulling back the Plücker
quotient agrees with the Plücker quotient of the pullback. -/
lemma PullbackQuotient.plucker_pullback_r {S : Scheme.{u}} {q : ℕ} {V : S.Modules}
    [V.IsQuasicoherent] {T T' : Over S} (g : T' ⟶ T) (x : PullbackQuotient q V T) :
    (PullbackQuotient.setoid 1 (Modules.exteriorPower V q) T').r
      ((x.plucker).pullback g) ((x.pullback g).plucker) := by
  haveI := x.isQuasicoherent
  -- the comparison of the two exterior powers of the pulled-back quotient
  refine ⟨pullbackExteriorPowerIso g.left x.Q x.isProjectiveOfRank q, ?_⟩
  show ((PullbackQuotient.pullbackComparison (Modules.exteriorPower V q) g).hom ≫
      (Modules.pullback g.left).map
        (pullbackExteriorPower T.hom V q ≫ Modules.exteriorPowerMap x.π q)) ≫
      pullbackExteriorPower g.left x.Q q =
    pullbackExteriorPower T'.hom V q ≫
      Modules.exteriorPowerMap
        ((PullbackQuotient.pullbackComparison V g).hom ≫
          (Modules.pullback g.left).map x.π) q
  -- expand the right-hand side through the two coherences
  rw [Modules.exteriorPowerMap_comp, pullbackExteriorPower_congr (Over.w g) V q,
    pullbackExteriorPower_comp g.left T.hom V q]
  -- the comparison isomorphism of iterated pullbacks
  have hcomparison : ∀ (M : S.Modules),
      (PullbackQuotient.pullbackComparison M g).hom =
        (Modules.pullbackCongr (Over.w g)).inv.app M ≫
          (Modules.pullbackComp g.left T.hom).inv.app M := fun _ ↦ rfl
  -- the two comparison isomorphisms cancel after applying `⋀^q`
  have hcancel :
      Modules.exteriorPowerMap
          ((Modules.pullbackComp g.left T.hom).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((Modules.pullbackCongr (Over.w g)).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((PullbackQuotient.pullbackComparison V g).hom) q = 𝟙 _ := by
    rw [hcomparison V, Modules.exteriorPowerMap_comp, ← Modules.exteriorPowerMap_comp,
      ← Modules.exteriorPowerMap_comp, Iso.hom_inv_id_app_assoc,
      ← Modules.exteriorPowerMap_comp, Iso.hom_inv_id_app,
      Modules.exteriorPowerMap_id]
  have hcancel' : ∀ {N : T'.left.Modules}
      (k : Modules.exteriorPower
        ((Modules.pullback T.hom ⋙ Modules.pullback g.left).obj V) q ⟶ N),
      Modules.exteriorPowerMap
          ((Modules.pullbackComp g.left T.hom).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((Modules.pullbackCongr (Over.w g)).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((PullbackQuotient.pullbackComparison V g).hom) q ≫ k = k := by
    intro N k
    calc Modules.exteriorPowerMap
          ((Modules.pullbackComp g.left T.hom).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((Modules.pullbackCongr (Over.w g)).hom.app V) q ≫
        Modules.exteriorPowerMap
          ((PullbackQuotient.pullbackComparison V g).hom) q ≫ k
        = (Modules.exteriorPowerMap
            ((Modules.pullbackComp g.left T.hom).hom.app V) q ≫
          Modules.exteriorPowerMap
            ((Modules.pullbackCongr (Over.w g)).hom.app V) q ≫
          Modules.exteriorPowerMap
            ((PullbackQuotient.pullbackComparison V g).hom) q) ≫ k := by
              simp only [Category.assoc]
      _ = 𝟙 _ ≫ k := by rw [hcancel]
      _ = k := Category.id_comp k
  -- assemble
  rw [hcomparison (Modules.exteriorPower V q)]
  simp only [Category.assoc]
  rw [hcancel', pullbackExteriorPower_naturality g.left
    ((Modules.pullback T.hom).obj V) q x.π, Functor.map_comp]
  simp only [Category.assoc]


/-- **The Plücker transformation** (`eqn:plucker-embedding`): the morphism of relative
Grassmannian functors sending a rank-`q` locally free quotient `V_T ↠ Q` to the line
bundle quotient `(⋀^q V)_T ↠ ⋀^q Q`. -/
noncomputable def pluckerTransformation {S : Scheme.{u}} (q : ℕ) (V : S.Modules)
    [V.IsQuasicoherent] :
    Modules.grassmannianOverFunctor q V ⟶
      Modules.grassmannianOverFunctor 1 (Modules.exteriorPower V q) where
  app T := ↾fun z ↦ Quotient.map PullbackQuotient.plucker
    (fun _ _ h ↦ PullbackQuotient.plucker_r h) z
  naturality {T T'} g := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    exact Quotient.sound
      ((PullbackQuotient.setoid 1 (Modules.exteriorPower V q) _).symm
        (PullbackQuotient.plucker_pullback_r g.unop x))

/-- The Plücker morphism of representing schemes classifies the Plücker transformation:
composing a classifying morphism with it computes the Plücker quotient. -/
lemma pluckerMorphismOfRepr_homEquiv {S : Scheme.{u}} {q : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P')
    {T : Over S} (t : T ⟶ P) :
    repr'.homEquiv (t ≫ pluckerMorphismOfRepr V repr repr') =
      (pluckerTransformation q V).app (Opposite.op T) (repr.homEquiv t) := by
  rw [repr'.homEquiv_comp]
  rw [pluckerMorphismOfRepr, Equiv.apply_symm_apply]
  have hnat := (pluckerTransformation q V).naturality t.op
  have happ := CategoryTheory.congr_fun hnat (repr.homEquiv (𝟙 P))
  have hcomp : (Modules.grassmannianOverFunctor q V).map t.op (repr.homEquiv (𝟙 P)) =
      repr.homEquiv t := by
    rw [← repr.homEquiv_comp, Category.comp_id]
  have happ' : (Modules.grassmannianOverFunctor 1
        (Modules.exteriorPower V q)).map t.op
        ((pluckerTransformation q V).app (Opposite.op P) (repr.homEquiv (𝟙 P))) =
      (pluckerTransformation q V).app (Opposite.op T)
        ((Modules.grassmannianOverFunctor q V).map t.op (repr.homEquiv (𝟙 P))) :=
    happ.symm
  exact happ'.trans
    (congrArg (fun y ↦ (pluckerTransformation q V).app (Opposite.op T) y) hcomp)



/-- **The Plücker quotient is compatible with a change of the ambient bundle**: it
intertwines transport along `e` with transport along `⋀^q e`. -/
lemma PullbackQuotient.plucker_mapAmbientIso_r {S : Scheme.{u}} {q : ℕ}
    {V W : S.Modules} [V.IsQuasicoherent] [W.IsQuasicoherent] (e : V ≅ W)
    {T : Over S} (x : PullbackQuotient q V T) :
    (PullbackQuotient.setoid 1 (Modules.exteriorPower W q) T).r
      ((PullbackQuotient.mapAmbientIso e x).plucker)
      (PullbackQuotient.mapAmbientIso (Modules.exteriorPowerIso e q) x.plucker) := by
  haveI := x.isQuasicoherent
  refine ⟨Iso.refl _, ?_⟩
  show _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  show pullbackExteriorPower T.hom W q ≫
      Modules.exteriorPowerMap
        ((Modules.pullback T.hom).map e.inv ≫ x.π) q =
    (Modules.pullback T.hom).map ((Modules.exteriorPowerIso e q).inv) ≫
      pullbackExteriorPower T.hom V q ≫ Modules.exteriorPowerMap x.π q
  rw [Modules.exteriorPowerMap_comp, ← Category.assoc,
    pullbackExteriorPower_naturality T.hom W q e.inv, Category.assoc]
  rfl

/-- **The Plücker quotient is compatible with rebasing along a morphism of the base.** -/
lemma PullbackQuotient.plucker_rebase_r {S U : Scheme.{u}} {q n : ℕ} {V : S.Modules}
    [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V) (j : U ⟶ S)
    (T : Over U) (x : PullbackQuotient q ((Modules.pullback j).obj V) T) :
    (PullbackQuotient.setoid 1 (Modules.exteriorPower V q) ((Over.map j).obj T)).r
      (PullbackQuotient.rebase j T
        (PullbackQuotient.mapAmbientIso
          (pullbackExteriorPowerIso j V hV q).symm x.plucker))
      ((PullbackQuotient.rebase j T x).plucker) := by
  haveI := x.isQuasicoherent
  refine ⟨Iso.refl _, ?_⟩
  show _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  show (Modules.pullbackComp T.hom j).inv.app (Modules.exteriorPower V q) ≫
      ((Modules.pullback T.hom).map
          ((pullbackExteriorPowerIso j V hV q).symm.inv) ≫
        pullbackExteriorPower T.hom ((Modules.pullback j).obj V) q ≫
          Modules.exteriorPowerMap x.π q) =
    pullbackExteriorPower (T.hom ≫ j) V q ≫
      Modules.exteriorPowerMap
        ((Modules.pullbackComp T.hom j).inv.app V ≫ x.π) q
  rw [Modules.exteriorPowerMap_comp, pullbackExteriorPower_comp T.hom j V q]
  simp only [Category.assoc]
  have hcancel : ∀ {N : T.left.Modules}
      (k : Modules.exteriorPower
        ((Modules.pullback T.hom).obj ((Modules.pullback j).obj V)) q ⟶ N),
      Modules.exteriorPowerMap ((Modules.pullbackComp T.hom j).hom.app V) q ≫
        Modules.exteriorPowerMap ((Modules.pullbackComp T.hom j).inv.app V) q ≫ k = k := by
    intro N k
    calc Modules.exteriorPowerMap ((Modules.pullbackComp T.hom j).hom.app V) q ≫
          Modules.exteriorPowerMap ((Modules.pullbackComp T.hom j).inv.app V) q ≫ k
        = (Modules.exteriorPowerMap ((Modules.pullbackComp T.hom j).hom.app V) q ≫
            Modules.exteriorPowerMap
              ((Modules.pullbackComp T.hom j).inv.app V) q) ≫ k := by
              simp only [Category.assoc]
      _ = 𝟙 _ ≫ k := by
            rw [← Modules.exteriorPowerMap_comp, Iso.hom_inv_id_app,
              Modules.exteriorPowerMap_id]
            rfl
      _ = k := Category.id_comp k
  rw [hcancel]
  rfl


/-- **The Plücker morphism of representing schemes is unique**: a morphism of representing
objects that classifies the Plücker transformation is the Plücker morphism. -/
lemma pluckerMorphismOfRepr_unique {S : Scheme.{u}} {q : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P')
    (g : P ⟶ P')
    (hg : ∀ {T : Over S} (t : T ⟶ P),
      repr'.homEquiv (t ≫ g) =
        (pluckerTransformation q V).app (Opposite.op T) (repr.homEquiv t)) :
    g = pluckerMorphismOfRepr V repr repr' := by
  rw [pluckerMorphismOfRepr, Equiv.eq_symm_apply]
  have h := hg (𝟙 P)
  rw [Category.id_comp] at h
  exact h

/-- **The Plücker transformation is natural in the ambient bundle**: transporting a point
of `Gr(q, V)` along `e : V ≅ W` and then applying the Plücker transformation agrees with
applying it first and then transporting along `⋀^q e`. -/
lemma pluckerTransformation_ambient_app {S : Scheme.{u}} {q : ℕ} {V W : S.Modules}
    [V.IsQuasicoherent] [W.IsQuasicoherent] (e : V ≅ W) (T : Over S)
    (x : (Modules.grassmannianOverFunctor q V).obj (Opposite.op T)) :
    (Modules.grassmannianOverFunctorIsoOfIso 1
        (Modules.exteriorPowerIso e q)).hom.app (Opposite.op T)
        ((pluckerTransformation q V).app (Opposite.op T) x) =
      (pluckerTransformation q W).app (Opposite.op T)
        ((Modules.grassmannianOverFunctorIsoOfIso q e).hom.app (Opposite.op T) x) := by
  obtain ⟨y, rfl⟩ := Quotient.exists_rep x
  exact Quotient.sound
    ((PullbackQuotient.setoid 1 (Modules.exteriorPower W q) T).symm
      (PullbackQuotient.plucker_mapAmbientIso_r e y))

/-- **The Plücker transformation is compatible with restriction of the base**: for an
open part `j : U ⟶ S` of the base, the Plücker transformation of the restricted bundle
`V|_U` is the restriction of the Plücker transformation of `V`, through the comparison
`⋀^q (V|_U) ≅ (⋀^q V)|_U`. -/
lemma pluckerTransformation_rebase_app {S U : Scheme.{u}} {q n : ℕ} {V : S.Modules}
    [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V) (j : U ⟶ S) (T : Over U)
    (x : (Modules.grassmannianOverFunctor q
      ((Modules.pullback j).obj V)).obj (Opposite.op T)) :
    (Modules.grassmannianOverFunctorPullbackIso j 1
          (Modules.exteriorPower V q)).hom.app (Opposite.op T)
        ((Modules.grassmannianOverFunctorIsoOfIso 1
            (pullbackExteriorPowerIso j V hV q).symm).hom.app (Opposite.op T)
          ((pluckerTransformation q ((Modules.pullback j).obj V)).app
            (Opposite.op T) x)) =
      (pluckerTransformation q V).app (Opposite.op ((Over.map j).obj T))
        ((Modules.grassmannianOverFunctorPullbackIso j q V).hom.app (Opposite.op T) x) := by
  obtain ⟨y, rfl⟩ := Quotient.exists_rep x
  exact Quotient.sound (PullbackQuotient.plucker_rebase_r hV j T y)


/-- **The Plücker morphism is unchanged by an isomorphism of the ambient bundle**:
transporting both representations along `e : V ≅ W` (and its exterior power) carries the
Plücker morphism of `V` to the Plücker morphism of `W`. -/
lemma pluckerMorphismOfRepr_ambient {S : Scheme.{u}} {q : ℕ} {V W : S.Modules}
    [V.IsQuasicoherent] [W.IsQuasicoherent] (e : V ≅ W) {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P') :
    pluckerMorphismOfRepr V repr repr' =
      pluckerMorphismOfRepr W
        (repr.ofIso (Modules.grassmannianOverFunctorIsoOfIso q e))
        (repr'.ofIso (Modules.grassmannianOverFunctorIsoOfIso 1
          (Modules.exteriorPowerIso e q))) := by
  apply pluckerMorphismOfRepr_unique
  intro T t
  dsimp only [Functor.RepresentableBy.ofIso]
  simp only [Equiv.trans_apply]
  rw [pluckerMorphismOfRepr_homEquiv]
  exact pluckerTransformation_ambient_app e T _

/-- **The Plücker morphism is independent of the chosen representatives**: two pairs of
representations give Plücker morphisms that differ by the canonical comparison
isomorphisms of representing objects. -/
lemma pluckerMorphismOfRepr_congr {S : Scheme.{u}} {q : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] {P₁ P₁' P₂ P₂' : Over S}
    (r₁ : (Modules.grassmannianOverFunctor q V).RepresentableBy P₁)
    (r₁' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P₁')
    (r₂ : (Modules.grassmannianOverFunctor q V).RepresentableBy P₂)
    (r₂' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P₂') :
    pluckerMorphismOfRepr V r₂ r₂' =
      (r₂.classifyingIso r₁).hom ≫ pluckerMorphismOfRepr V r₁ r₁' ≫
        (r₁'.classifyingIso r₂').hom := by
  symm
  apply pluckerMorphismOfRepr_unique
  intro T t
  rw [show t ≫ (r₂.classifyingIso r₁).hom ≫ pluckerMorphismOfRepr V r₁ r₁' ≫
        (r₁'.classifyingIso r₂').hom =
      ((t ≫ (r₂.classifyingIso r₁).hom) ≫ pluckerMorphismOfRepr V r₁ r₁') ≫
        (r₁'.classifyingIso r₂').hom by simp only [Category.assoc],
    Functor.RepresentableBy.classifyingIso_hom,
    Functor.RepresentableBy.classifyingIso_hom,
    Functor.RepresentableBy.homEquiv_comp_classifyingHom,
    pluckerMorphismOfRepr_homEquiv,
    Functor.RepresentableBy.homEquiv_comp_classifyingHom]

/-- Whether the Plücker morphism of representing schemes is a closed immersion does not
depend on the chosen representatives. -/
lemma isClosedImmersion_pluckerMorphismOfRepr_congr {S : Scheme.{u}} {q : ℕ} (V : S.Modules)
    [V.IsQuasicoherent] {P₁ P₁' P₂ P₂' : Over S}
    (r₁ : (Modules.grassmannianOverFunctor q V).RepresentableBy P₁)
    (r₁' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P₁')
    (r₂ : (Modules.grassmannianOverFunctor q V).RepresentableBy P₂)
    (r₂' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P₂')
    (h : IsClosedImmersion (pluckerMorphismOfRepr V r₁ r₁').left) :
    IsClosedImmersion (pluckerMorphismOfRepr V r₂ r₂').left := by
  haveI : IsIso ((Over.forget S).map (r₂.classifyingIso r₁).hom) :=
    Functor.map_isIso (Over.forget S) (r₂.classifyingIso r₁).hom
  haveI : IsIso ((Over.forget S).map (r₁'.classifyingIso r₂').hom) :=
    Functor.map_isIso (Over.forget S) (r₁'.classifyingIso r₂').hom
  rw [pluckerMorphismOfRepr_congr V r₁ r₁' r₂ r₂']
  show IsClosedImmersion (((r₂.classifyingIso r₁).hom ≫
    pluckerMorphismOfRepr V r₁ r₁' ≫ (r₁'.classifyingIso r₂').hom).left)
  rw [Over.comp_left, Over.comp_left]
  rw [MorphismProperty.cancel_left_of_respectsIso
      (@IsClosedImmersion : MorphismProperty Scheme.{u}),
    MorphismProperty.cancel_right_of_respectsIso
      (@IsClosedImmersion : MorphismProperty Scheme.{u})]
  exact h

end Modules

end ExteriorPowerSheafSections

/-! The general case of Theorem 2.1.1 — for a
quasi-coherent vector bundle `V` of rank `n` the relative Grassmannian `Gr(q, V)` is
representable by a scheme strongly projective over `S` — is assembled in part 2.2.3, which
supplies the representability of both `Gr(q, V)` and of `Gr(1, ⋀^q V)`.  The projectivity
input is `Modules.isStronglyProjective_of_representableBy` above; its remaining geometric
hypothesis is that the Plücker morphism `Modules.pluckerMorphismOfRepr` is a closed
immersion. -/

/-- **Proposition 2.2.8** (`prop:grassmannian-projective`): there is a morphism of
functors `P : Gr(q, n) ⟶ Gr(1, C(n, q))` — the Plücker embedding, sending a rank-`q`
quotient `O^{⊕n} ↠ Q` to the line bundle quotient `⋀^q O^{⊕n} ↠ ⋀^q Q` under the
identification `⋀^q O^{⊕n} ≅ O^{⊕C(n,q)}` by the basis of `q`-element subsets — which is
relatively representable by closed immersions. In particular `Gr(q, n)` is a projective
scheme over `ℤ` (the "in particular" clause is realized as
`grassmannianOverRepresentation_isStronglyProjective`). -/
theorem exists_plucker_isClosedImmersion_presheaf (q n : ℕ) :
    ∃ P : grassmannianFunctor.{u} q n ⟶ grassmannianFunctor.{u} 1 (n.choose q),
      MorphismProperty.presheaf (@IsClosedImmersion : MorphismProperty Scheme.{u}) P := by
  refine ⟨pluckerMorphism q n, ?_⟩
  let P : MorphismProperty Scheme.{u} := @IsClosedImmersion
  let eS := (grassmannianGluedRepresentation q n).toIso
  let eT := (grassmannianGluedRepresentation 1 (n.choose q)).toIso
  have hf : MorphismProperty.presheaf
      (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (yoneda.map (pluckerGluedSchemeMorphism.{u} q n)) :=
    MorphismProperty.relative_map
      (isClosedImmersion_pluckerGluedSchemeMorphism q n)
  have hpost := MorphismProperty.RespectsIso.postcomp
    P.presheaf eT.hom _ hf
  have hpre := MorphismProperty.RespectsIso.precomp
    P.presheaf eS.inv _ hpost
  rw [yoneda_map_pluckerGluedSchemeMorphism_comp_representation q n] at hpre
  simpa [P, Category.assoc] using hpre
end AlgebraicGeometry.Scheme

end PropGrassmannianProjective
