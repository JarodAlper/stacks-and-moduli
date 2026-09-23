module

public import StacksAndModuli.API.RegularSequenceClosedPointDimension
public import StacksAndModuli.API.RelativeFibreRegularSequenceLocusOver
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksProject.CommutativeAlgebra.DimensionOfFibres.«definition-relative-dimension»

/-!
# Relative-fibre dimension drop at a closed fibre point

The fibre of a quotient is the quotient of the fibre by the image of the same sequence.
At a point which is closed in its residue fibre, this identification and the local
dimension formula for a regular sequence give the expected drop in relative dimension.

This is the closed-fibre-point substitute for the full transcendence-degree dimension
formula in the polynomial specialization of relative regular-sequence openness.  Starting
from an arbitrary regular point, fixed-fibre openness allows one to choose a closed
specialization which remains regular; every open neighbourhood of that specialization
also contains the original point.

Main declarations:

* `Ideal.Fiber.quotientOfListAlgEquiv`;
* the relative-fibre dimension-drop theorem at a closed fibre point.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Ideal.Fiber

/-- Taking a residue fibre commutes with quotienting by an ideal. -/
noncomputable def quotientAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (I : Ideal S) :
    p.Fiber (S ⧸ I) ≃ₐ[p.ResidueField]
      (p.Fiber S ⧸
        I.map (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)) :=
  Algebra.TensorProduct.tensorQuotientEquiv
    (R := R) p.ResidueField S p.ResidueField I

/-- Taking a residue fibre commutes with quotienting by a finite sequence. -/
noncomputable def quotientOfListAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (rs : List S) :
    p.Fiber (S ⧸ Ideal.ofList rs) ≃ₐ[p.ResidueField]
      (p.Fiber S ⧸
        Ideal.ofList
          (rs.map (Algebra.TensorProduct.includeRight :
            S →ₐ[R] p.Fiber S))) :=
  (quotientAlgEquiv p (Ideal.ofList rs)).trans
    (Ideal.quotientEquivAlgOfEq p.ResidueField
      (Ideal.map_ofList
        (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom rs))

@[simp]
theorem quotientOfListAlgEquiv_includeRight_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (rs : List S) (s : S) :
    quotientOfListAlgEquiv p rs
        (Algebra.TensorProduct.includeRight
          (Ideal.Quotient.mk (Ideal.ofList rs) s)) =
      Ideal.Quotient.mk
        (Ideal.ofList
          (rs.map (Algebra.TensorProduct.includeRight :
            S →ₐ[R] p.Fiber S)))
        (Algebra.TensorProduct.includeRight s) := by
  change quotientOfListAlgEquiv p rs
      (1 ⊗ₜ[R] Ideal.Quotient.mk (Ideal.ofList rs) s) = _
  simp only [quotientOfListAlgEquiv, quotientAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlgOfEq_mk,
    Algebra.TensorProduct.includeRight_apply]

end Ideal.Fiber

namespace Algebra

/-- Relative dimension is pointwise dimension at the distinguished prime of the residue
fibre. -/
theorem relativeKrullDimAt_eq_topologicalKrullDimAtPoint_relativeFibrePrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    relativeKrullDimAt R S q =
      topologicalKrullDimAtPoint
        (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
        (PrimeSpectrum.relativeFibrePrime (R := R) q) :=
  rfl

/-- Relative dimension may be computed using any explicitly named copy of the contracted
prime.  This packages the dependent transport of the residue fibre and its distinguished
point. -/
theorem relativeKrullDimAt_eq_topologicalKrullDimAtPoint_fibre_of_comap_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (p : PrimeSpectrum R)
    (hp : q.comap (algebraMap R S) = p) :
    relativeKrullDimAt R S q =
      topologicalKrullDimAtPoint (PrimeSpectrum (p.asIdeal.Fiber S))
        ((PrimeSpectrum.preimageEquivFiber R S p) ⟨q, hp⟩) := by
  subst p
  rfl

/-- If a sequence is regular at a point which is closed in its residue fibre, passing to
the quotient lowers relative dimension at that point by the length of the sequence. -/
theorem
    relativeKrullDimAt_quotient_add_length_eq_of_regularSequenceAt_closedFibrePoint
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    {d : ℕ} (q : PrimeSpectrum S) (f : Fin d → S)
    (hmem : ∀ i, f i ∈ q.asIdeal)
    (hreg : Matrix.FiniteFreeComplex.IsRelativeFibreRegularSequenceAt
      (R := R) q f)
    (hclosed :
      (PrimeSpectrum.relativeFibrePrime (R := R) q).asIdeal.IsMaximal) :
    let rs := List.ofFn f
    let I := Ideal.ofList rs
    let hIq : I ≤ q.asIdeal := Ideal.span_le.mpr <|
      List.forall_mem_ofFn_iff.mpr hmem
    let qbar := PrimeSpectrum.quotientOfLE I q hIq
    relativeKrullDimAt R (S ⧸ I) qbar + d =
      relativeKrullDimAt R S q := by
  let rs : List S := List.ofFn f
  let I : Ideal S := Ideal.ofList rs
  have hrs_mem : ∀ x ∈ rs, x ∈ q.asIdeal := by
    dsimp only [rs]
    exact List.forall_mem_ofFn_iff.mpr hmem
  have hIq : I ≤ q.asIdeal := Ideal.span_le.mpr <|
    List.forall_mem_ofFn_iff.mpr hmem
  let qbar : PrimeSpectrum (S ⧸ I) :=
    PrimeSpectrum.quotientOfLE I q hIq
  change relativeKrullDimAt R (S ⧸ I) qbar + d =
    relativeKrullDimAt R S q
  let p : PrimeSpectrum R := q.comap (algebraMap R S)
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let rsF : List T :=
    rs.map (Algebra.TensorProduct.includeRight : S →ₐ[R] T)
  have hrsF_mem : ∀ x ∈ rsF,
      x ∈ (PrimeSpectrum.relativeFibrePrime (R := R) q).asIdeal := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    change s ∈
      (PrimeSpectrum.relativeFibrePrime (R := R) q).asIdeal.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] T).toRingHom
    rw [PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q]
    exact hrs_mem s hs
  have hregF : RingTheory.Sequence.IsRegularAfterLocalizationAt rsF
      (PrimeSpectrum.relativeFibrePrime (R := R) q) := by
    let qF' := PrimeSpectrum.relativeFibrePrime (R := R) q
    let A := Localization.AtPrime qF'.asIdeal
    have hrsF_eq :
        rsF = List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j) := by
      dsimp only [rsF, rs]
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      rfl
    rw [hrsF_eq]
    change RingTheory.Sequence.IsRegular A
      (List.map (algebraMap T A)
        (List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j)))
    change RingTheory.Sequence.IsRegular A
      (List.ofFn fun j ↦ algebraMap S A (f j)) at hreg
    have hfun : (fun j ↦ algebraMap S A (f j)) =
        (algebraMap T A) ∘
          (fun j ↦ Algebra.TensorProduct.includeRight (f j)) := by
      funext j
      exact (IsScalarTower.algebraMap_apply S T A (f j)).symm
    rw [List.map_ofFn, ← hfun]
    exact hreg
  let qF : PrimeSpectrum T :=
    PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Nontrivial T := qF.nontrivial
  let IF : Ideal T := Ideal.ofList rsF
  have hIFq : IF ≤ qF.asIdeal := Ideal.span_le.mpr hrsF_mem
  let qFbar : PrimeSpectrum (T ⧸ IF) :=
    PrimeSpectrum.quotientOfLE IF qF hIFq
  letI : qF.asIdeal.IsMaximal := hclosed
  have hdimF :
      topologicalKrullDimAtPoint (PrimeSpectrum (T ⧸ IF)) qFbar + rsF.length =
        topologicalKrullDimAtPoint (PrimeSpectrum T) qF := by
    simpa only [IF, qFbar] using
      (PrimeSpectrum.topologicalKrullDimAtPoint_quotient_add_length_eq_of_isRegular
        K T qF rsF hrsF_mem hregF)
  have hp : qbar.comap (algebraMap R (S ⧸ I)) = p := by
    calc
      qbar.comap (algebraMap R (S ⧸ I)) =
          qbar.comap
            ((Ideal.Quotient.mk I).comp (algebraMap R S)) := rfl
      _ = (qbar.comap (Ideal.Quotient.mk I)).comap
            (algebraMap R S) := rfl
      _ = q.comap (algebraMap R S) := by
        rw [PrimeSpectrum.comap_quotientOfLE]
      _ = p := rfl
  let U := p.asIdeal.Fiber (S ⧸ I)
  let e : U ≃ₐ[K] T ⧸ IF := by
    exact Ideal.Fiber.quotientOfListAlgEquiv p.asIdeal rs
  let xbar : PrimeSpectrum U :=
    PrimeSpectrum.comap e.toRingEquiv.toRingHom qFbar
  have hxbar_comap :
      xbar.asIdeal.comap
          (Algebra.TensorProduct.includeRight : (S ⧸ I) →ₐ[R] U).toRingHom =
        qbar.asIdeal := by
    ext sbar
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sbar
    change e
        (Algebra.TensorProduct.includeRight
          (Ideal.Quotient.mk I s)) ∈ qFbar.asIdeal ↔
      Ideal.Quotient.mk I s ∈ qbar.asIdeal
    rw [show e
        (Algebra.TensorProduct.includeRight
          (Ideal.Quotient.mk I s)) =
          Ideal.Quotient.mk IF
            (Algebra.TensorProduct.includeRight s) by
      exact Ideal.Fiber.quotientOfListAlgEquiv_includeRight_mk
        p.asIdeal rs s]
    calc
      Ideal.Quotient.mk IF
            (Algebra.TensorProduct.includeRight s) ∈ qFbar.asIdeal ↔
          Algebra.TensorProduct.includeRight s ∈ qF.asIdeal := by
        rw [← Ideal.mem_comap]
        exact iff_of_eq <| congrArg
          (Algebra.TensorProduct.includeRight s ∈ ·)
          (Ideal.comap_map_mk (I := IF) (J := qF.asIdeal) hIFq)
      _ ↔ s ∈ q.asIdeal := by
        change s ∈
          (PrimeSpectrum.relativeFibrePrime (R := R) q).asIdeal.comap
              (Algebra.TensorProduct.includeRight : S →ₐ[R] T).toRingHom ↔
            s ∈ q.asIdeal
        rw [PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q]
      _ ↔ Ideal.Quotient.mk I s ∈ qbar.asIdeal := by
        rw [← Ideal.mem_comap]
        exact (iff_of_eq <| congrArg (s ∈ ·)
          (Ideal.comap_map_mk (I := I) (J := q.asIdeal) hIq)).symm
  let E := PrimeSpectrum.preimageEquivFiber R (S ⧸ I) p
  let qbarF : PrimeSpectrum U := E ⟨qbar, hp⟩
  have hxbar_eq : xbar = qbarF := by
    apply E.symm.injective
    calc
      E.symm xbar = ⟨qbar, hp⟩ := by
        apply Subtype.ext
        exact PrimeSpectrum.ext hxbar_comap
      _ = E.symm qbarF := (E.symm_apply_apply ⟨qbar, hp⟩).symm
  let eSpec : PrimeSpectrum U ≃ₜ PrimeSpectrum (T ⧸ IF) :=
    PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  have heSpec : eSpec xbar = qFbar := by
    change eSpec (eSpec.symm qFbar) = qFbar
    exact eSpec.apply_symm_apply qFbar
  have hpoint :
      topologicalKrullDimAtPoint (PrimeSpectrum U) qbarF =
        topologicalKrullDimAtPoint (PrimeSpectrum (T ⧸ IF)) qFbar := by
    rw [← hxbar_eq, ← heSpec]
    exact eSpec.isOpenEmbedding.topologicalKrullDimAtPoint_eq xbar
  have hrelative :
      topologicalKrullDimAtPoint (PrimeSpectrum U) qbarF + d =
        topologicalKrullDimAtPoint (PrimeSpectrum T) qF := by
    rw [hpoint]
    simpa only [rsF, rs, List.length_map, List.length_ofFn] using hdimF
  rw [relativeKrullDimAt_eq_topologicalKrullDimAtPoint_fibre_of_comap_eq
      qbar p hp,
    relativeKrullDimAt_eq_topologicalKrullDimAtPoint_relativeFibrePrime q]
  simpa only [p, T, qF, U, qbarF, E] using hrelative

end Algebra

end

end
