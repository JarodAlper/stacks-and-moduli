module

public import StacksAndModuli.API.QuasicoherentFiniteCoproduct
public import StacksAndModuli.API.SchemeModulesFiniteLocallyFreeKernel
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection
public import StacksAndModuli.API.TwistedFreeReconstructionBaseChange

/-!
# The algebraic next-degree module for Grassmannian reconstruction

Let `u : O_T^(r * binom(n+e,n)) → E` be a finite locally free quotient and let
`K = ker(u)`.  The classical Hilbert--Grassmannian construction does not use the
pushforward of the reconstructed sheaf on the whole Grassmannian: that pushforward
need not commute with arbitrary base change.  Instead it multiplies `K` by the
`n+1` variables and takes the finite cokernel

`coker (K^(n+1) → O_T^(r * binom(n+e+1,n)))`.

This file constructs that module without projective pushforwards.  Its relation is
defined directly on the finite monomial bases, so it commutes with arbitrary base
change once pullback preservation of the kernel of `u` is used.  Quasicoherence and
finite presentation follow formally.

The remaining geometric input for the classical construction is the Gotzmann-range
statement identifying the prescribed-rank locus of this module with the flat,
fixed-Hilbert-polynomial locus of the reconstructed projective family.

Main declarations:

* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeRelation`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeModule`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeModulePullbackIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace MvPolynomial

/-- The finite homogeneous basis is the monomial selected by its finite
enumeration index. -/
theorem coe_homogeneousSubmoduleFinBasis (n : ℕ) (R : Type u) [CommRing R]
    (e : ℕ) (i : Fin ((n + e).choose n)) :
    ((homogeneousSubmoduleFinBasis n R e i :
      homogeneousSubmodule (Fin (n + 1)) R e) :
        MvPolynomial (Fin (n + 1)) R) =
      monomial ((degreeMonomialEquivFin n e).symm i).1 1 := by
  let b := (degreeMonomialEquivFin n e).symm i
  let p : homogeneousSubmodule (Fin (n + 1)) R e :=
    ⟨monomial b.1 1, isHomogeneous_monomial 1 b.2⟩
  have hp : homogeneousSubmoduleFinBasis n R e i = p := by
    apply (homogeneousSubmoduleFinFinsuppEquiv n R e).injective
    have hrepr := (homogeneousSubmoduleFinBasis n R e).repr_self i
    change homogeneousSubmoduleFinFinsuppEquiv n R e
      (homogeneousSubmoduleFinBasis n R e i) = Finsupp.single i 1 at hrepr
    rw [hrepr]
    ext j
    rw [homogeneousSubmoduleFinFinsuppEquiv_apply']
    dsimp only [p]
    rw [coeff_monomial]
    rcases eq_or_ne j i with rfl | hji
    · simp only [Finsupp.single_eq_same]
      rw [ite_eq_left (by rfl)]
    · have hbji : ((degreeMonomialEquivFin n e).symm j).1 ≠ b.1 := by
        intro h
        apply hji
        apply (degreeMonomialEquivFin n e).symm.injective
        exact Subtype.ext h
      rw [Finsupp.single_eq_of_ne hji,
        ite_eq_right (fun h ↦ (hbji h.symm).elim)]
  exact congrArg Subtype.val hp

end MvPolynomial

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplication of a degree-`e` monomial by the variable `X_j`, expressed in
the chosen finite enumeration of degree-`e+1` monomials. -/
noncomputable def twistedFreeNextMonomialIndex (n e : ℕ)
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    Fin ((n + (e + 1)).choose n) :=
  MvPolynomial.degreeMonomialEquivFin n (e + 1)
    ⟨((MvPolynomial.degreeMonomialEquivFin n e).symm i).1 +
      Finsupp.single j 1, by
        simpa using congrArg (fun z : ℕ ↦ z + 1)
          ((MvPolynomial.degreeMonomialEquivFin n e).symm i).2⟩

/-- The finite degree-one monomial index corresponding to the variable `X_j`. -/
noncomputable def twistedFreeDegreeOneMonomialIndex
    (n : ℕ) (j : Fin (n + 1)) : Fin ((n + 1).choose n) :=
  MvPolynomial.degreeMonomialEquivFin n 1
    ⟨Finsupp.single j 1, by simp⟩

/-- Multiplying a finite-basis degree-`e` monomial by `X_j` gives the
finite-basis monomial at `twistedFreeNextMonomialIndex`. -/
theorem twistedFreeMonomialBasis_mul_degreeOne
    (n : ℕ) (R : Type u) [CommRing R] (e : ℕ)
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    (((MvPolynomial.homogeneousSubmoduleFinBasis n R e i :
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e) :
          MvPolynomial (Fin (n + 1)) R) *
      ((MvPolynomial.homogeneousSubmoduleFinBasis n R 1
        (twistedFreeDegreeOneMonomialIndex n j) :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1) :
        MvPolynomial (Fin (n + 1)) R)) =
      ((MvPolynomial.homogeneousSubmoduleFinBasis n R (e + 1)
        (twistedFreeNextMonomialIndex n e j i) :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (e + 1)) :
        MvPolynomial (Fin (n + 1)) R) := by
  rw [MvPolynomial.coe_homogeneousSubmoduleFinBasis,
    MvPolynomial.coe_homogeneousSubmoduleFinBasis,
    MvPolynomial.coe_homogeneousSubmoduleFinBasis]
  dsimp only [twistedFreeDegreeOneMonomialIndex,
    twistedFreeNextMonomialIndex]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [MvPolynomial.monomial_mul]
  simp

/-- The algebraic degree-`e+1` relation obtained by multiplying the kernel of a
degree-`e` finite-free quotient by every projective variable. -/
noncomputable def twistedFreeNextDegreeRelation
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ⟶
      SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + (e + 1)).choose n)) :=
  Sigma.desc (fun j ↦ kernel.ι u ≫
    SheafOfModules.freeMap (R := T.ringCatSheaf)
      (fun x ↦ (x.1, twistedFreeNextMonomialIndex n e j.down x.2)))

/-- The finite algebraic degree-`e+1` quotient attached to a degree-`e`
Grassmannian quotient.  This is the module whose rank locus replaces a false
global base-change assertion for the reconstructed sheaf's pushforward. -/
noncomputable def twistedFreeNextDegreeModule
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : T.Modules :=
  cokernel (twistedFreeNextDegreeRelation n T r e u)

/-- The algebraic next-degree module is quasicoherent. -/
theorem twistedFreeNextDegreeModule_isQuasicoherent
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (twistedFreeNextDegreeModule n T r e u).IsQuasicoherent := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI : (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u).IsQuasicoherent :=
    Modules.isQuasicoherent_coproduct _
  letI : (SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) ×
        Fin ((n + (e + 1)).choose n))).IsQuasicoherent := by
    infer_instance
  dsimp only [twistedFreeNextDegreeModule]
  exact Modules.isQuasicoherent_cokernel _

/-- For a finite locally free quotient, the algebraic next-degree module is
finitely presented over an arbitrary base scheme. -/
theorem twistedFreeNextDegreeModule_isFinitePresentation
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (twistedFreeNextDegreeModule n T r e u).IsFinitePresentation := by
  let m := r * (n + e).choose n
  let σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n) :=
    twistedFreeMonomialIndexEquiv r ((n + e).choose n)
  let f := SheafOfModules.freeMap (R := T.ringCatSheaf) σ.symm
  letI : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  have hSource : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))) :=
    (Modules.free_isFiniteLocallyFree T m).of_iso (asIso f).symm
  have hK : Modules.IsFiniteLocallyFree (kernel u) :=
    Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
      hSource hE u
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI : (kernel u).IsFinitePresentation := hK.isFinitePresentation
  letI : (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u).IsQuasicoherent :=
    Modules.isQuasicoherent_coproduct _
  letI : (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u).IsFinitePresentation :=
    Modules.finiteCoproduct_isFinitePresentation _
  letI : (SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) ×
        Fin ((n + (e + 1)).choose n))).IsQuasicoherent := by
    infer_instance
  letI : (SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) ×
        Fin ((n + (e + 1)).choose n))).IsFinitePresentation :=
    Modules.isFinitePresentation_of_globalPresentation
      (Modules.freePresentation
        (ULift.{u} (Fin r) × Fin ((n + (e + 1)).choose n)))
  dsimp only [twistedFreeNextDegreeModule]
  exact Modules.cokernel_isFinitePresentation _

/-- Pullback of the source of the next-degree relation, using preservation of
the kernel of a finite locally free quotient. -/
noncomputable def twistedFreeNextDegreeRelationSourcePullbackIso
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (r e : ℕ)
    {E : Y.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback f).obj
        (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ≅
      (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦
        kernel (pullbackFreeQuotientMap f u)) :=
  PreservesCoproduct.iso (Modules.pullback f)
      (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ≪≫
    Sigma.mapIso (fun _ ↦ pullbackKernelIsoPullbackFreeQuotientMap f u hE)

/-- Pullback of the finite-free target of the next-degree relation. -/
noncomputable def twistedFreeNextDegreeRelationTargetPullbackIso
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (r e : ℕ) :
    (Modules.pullback f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf)
          (ULift.{u} (Fin r) × Fin ((n + (e + 1)).choose n))) ≅
      SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + (e + 1)).choose n)) :=
  Modules.pullbackFreeIso f _

/-- The forward normalized pullback-kernel comparison intertwines the two
kernel inclusions and the free-source pullback comparison. -/
lemma pullbackKernelIsoPullbackFreeQuotientMap_hom_comp_kernel_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) [Epi u]
    (hE : Modules.IsFiniteLocallyFree E) :
    (pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom ≫
        kernel.ι (pullbackFreeQuotientMap f u) =
      (Modules.pullback f).map (kernel.ι u) ≫
        (Modules.pullbackFreeIso f I).hom := by
  dsimp only [pullbackKernelIsoPullbackFreeQuotientMap, Iso.trans_hom]
  simp only [Category.assoc, PreservesKernel.iso_hom,
    kernel.mapIso, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, kernelComparison_comp_ι]

/-- The inverse normalized pullback-kernel comparison intertwines the two
kernel inclusions and the inverse free-source pullback comparison. -/
lemma pullbackKernelIsoPullbackFreeQuotientMap_inv_comp_kernel_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) [Epi u]
    (hE : Modules.IsFiniteLocallyFree E) :
    (pullbackKernelIsoPullbackFreeQuotientMap f u hE).inv ≫
        (Modules.pullback f).map (kernel.ι u) =
      kernel.ι (pullbackFreeQuotientMap f u) ≫
        (Modules.pullbackFreeIso f I).inv := by
  apply (cancel_epi
    (pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom).1
  calc
    (pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom ≫
          ((pullbackKernelIsoPullbackFreeQuotientMap f u hE).inv ≫
            (Modules.pullback f).map (kernel.ι u)) =
        (Modules.pullback f).map (kernel.ι u) := by simp
    _ = ((pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom ≫
          kernel.ι (pullbackFreeQuotientMap f u)) ≫
        (Modules.pullbackFreeIso f I).inv := by
          rw [pullbackKernelIsoPullbackFreeQuotientMap_hom_comp_kernel_ι]
          simp
    _ = (pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom ≫
        (kernel.ι (pullbackFreeQuotientMap f u) ≫
          (Modules.pullbackFreeIso f I).inv) := by rfl

/-- The algebraic next-degree relation commutes with normalized arbitrary
base change. -/
lemma twistedFreeNextDegreeRelation_baseChange
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (r e : ℕ)
    {E : Y.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback f).map (twistedFreeNextDegreeRelation n Y r e u) ≫
        (twistedFreeNextDegreeRelationTargetPullbackIso n f r e).hom =
      (twistedFreeNextDegreeRelationSourcePullbackIso n f r e u hE).hom ≫
        twistedFreeNextDegreeRelation n X r e
          (pullbackFreeQuotientMap f u) := by
  apply (cancel_epi
    (twistedFreeNextDegreeRelationSourcePullbackIso n f r e u hE).inv).1
  apply Sigma.hom_ext
  intro j
  dsimp only [twistedFreeNextDegreeRelationSourcePullbackIso]
  simp only [Iso.inv_hom_id_assoc]
  have hj := Modules.coproductPullbackIso_inv_ι f
    (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u)
    (fun _ : ULift.{u} (Fin (n + 1)) ↦
      kernel (pullbackFreeQuotientMap f u))
    (fun _ ↦ pullbackKernelIsoPullbackFreeQuotientMap f u hE) j
  slice_lhs 1 2 => rw [hj]
  dsimp only [twistedFreeNextDegreeRelationTargetPullbackIso,
    twistedFreeNextDegreeRelation]
  rw [Sigma.ι_desc]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, Sigma.ι_desc,
    Functor.map_comp]
  slice_lhs 1 2 =>
    rw [pullbackKernelIsoPullbackFreeQuotientMap_inv_comp_kernel_ι]
  slice_lhs 2 3 =>
    rw [← Modules.freeMap_comp_pullbackFreeIso_inv]
  simp

/-- The finite algebraic next-degree module commutes with arbitrary base
change.  Unlike pushforward base change for the reconstructed family, this is
formal from preservation of finite cokernels and the finite locally free
kernel comparison. -/
noncomputable def twistedFreeNextDegreeModulePullbackIso
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (r e : ℕ)
    {E : Y.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback f).obj (twistedFreeNextDegreeModule n Y r e u) ≅
      twistedFreeNextDegreeModule n X r e
        (pullbackFreeQuotientMap f u) :=
  PreservesCokernel.iso (Modules.pullback f)
      (twistedFreeNextDegreeRelation n Y r e u) ≪≫
    cokernel.mapIso
      ((Modules.pullback f).map (twistedFreeNextDegreeRelation n Y r e u))
      (twistedFreeNextDegreeRelation n X r e
        (pullbackFreeQuotientMap f u))
      (twistedFreeNextDegreeRelationSourcePullbackIso n f r e u hE)
      (twistedFreeNextDegreeRelationTargetPullbackIso n f r e)
      (twistedFreeNextDegreeRelation_baseChange n f r e u hE)

end AlgebraicGeometry.Scheme

end

end
