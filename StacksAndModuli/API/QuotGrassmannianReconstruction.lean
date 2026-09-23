module

public import StacksAndModuli.API.QuotGrassmannianMap
public import StacksAndModuli.API.CokernelEpiComp
public import StacksAndModuli.API.ProjTwistMulHom
public import StacksAndModuli.API.SchemeModulesTensorCoproduct
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent

/-!
# The reconstruction `E ↦ Q_E`

Step 3 of the Grassmannian argument — that `Quot^P → Gr` is relatively representable by
immersions — needs the *inverse* of the Quot-to-Grassmannian map: from a rank-`q` quotient
`u : 𝒪_T^m ↠ E` on the base, a candidate family on `ℙⁿ_T`.  The recipe is

`Q_E(d) := coker (π^*(ker u) ⟶ 𝒪^m_{ℙⁿ_T} ⟶ F(d))`,

where the second map is the tautological monomial map `Scheme.twistedFreeMonomialMap`, built
from `Scheme.twistedFreeMonomialSection` by `Scheme.Modules.freeHomOfSections`.  The fibre of
`α` over the Grassmannian point of `u` is then the locus in `T` where `Q_E` is flat with
Hilbert polynomial `P` and the comparison back to `E` is an isomorphism — a finite
intersection of flattening strata, which is where
`Modules.flatRankRepresentativeOfFinite_hom_isImmersion` enters.

Note that using a `Modules.PullbackQuotient` (equivalently, a rank-`q` quotient of the free
sheaf) as *input* is unproblematic: its `isQuasicoherent` field is given, not something to be
proved.  The warning in this folder's INSIGHTS is about using it as the *target* of `α`.

## Tensor-free reconstruction

The repo now has a chosen associator and braiding for `Scheme.Modules.tensor`, together
with twist-cancellation isomorphisms.  Nevertheless the direct reconstruction below uses
`Scheme.twistedFreeMonomialHom`: a degree-`e` monomial gives
`𝒪(a) ⟶ 𝒪(a + e)` by **multiplication**, `ProjectiveSpectrum.Twist.mulHom`, with no tensor
product anywhere; summing over the `m` monomials gives `∐_m 𝒪(-d) ⟶ F` directly.  The
reconstruction is then

`Q_E := coker (π^*(ker u) ⊗ 𝒪(-d) ⟶ π^*(𝒪_T^m) ⊗ 𝒪(-d) ≅ ∐_m 𝒪(-d) ⟶ F)`,

and the middle isomorphism needs only `Modules.tensorCoproductIso`,
`Modules.tensorLeftUnitIso` and `Modules.pullbackFreeIso`.  This multiplication model keeps
the defining quotient map and its reconstruction triangle computationally transparent;
the associator is used later only to compare this model with the twisted-kernel model.

Main declarations:

* `AlgebraicGeometry.Scheme.twistedFreeMonomialMap`;
* `AlgebraicGeometry.Scheme.reconstructedTwisted` and
  `AlgebraicGeometry.Scheme.reconstructedQuotient`;
* `AlgebraicGeometry.Scheme.twistMonomialMulHom` and
  `AlgebraicGeometry.Scheme.twistedFreeMonomialHom` — the untwisted, tensor-free form;
* `AlgebraicGeometry.Scheme.freeTensorTwistIso`;
* **`AlgebraicGeometry.Scheme.reconstructedQuotient'`** and
  `…reconstructedQuotientMap'` (with its `Epi` instance) — from a quotient
  `u : 𝒪_T^m ↠ E` on the base, an actual quotient `F ↠ Q_E` on `ℙⁿ_T`.  This is the datum
  the fibre of `α` is compared against; the *conditions* on it (quasi-coherence, flatness,
  Hilbert polynomial `P`) are what cut out the flattening locus.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The tautological monomial map** `𝒪_{ℙⁿ_S}^m ⟶ F(d)` for `F = 𝒪(-l)^{⊕r}`. -/
def twistedFreeMonomialMap (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) :
    SheafOfModules.free (R := (Scheme.projectiveSpaceOver n S).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶
      Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l))
        (d : ℤ) :=
  Scheme.Modules.freeHomOfSections
    (fun x => twistedFreeMonomialSection n S l r d e he x.1 x.2)

/-- **The reconstruction, twisted form.**  From a quotient `u : 𝒪_T^m ↠ E` on the base, the
induced family `Q_E(d)` on `ℙⁿ_T`: the cokernel of `π^*(ker u) ⟶ 𝒪^m ⟶ F(d)`. -/
def reconstructedTwisted (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (Scheme.projectiveSpaceOver n T).Modules :=
  Limits.cokernel
    ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverπ n T)).map
        (Limits.kernel.ι u) ≫
      (Scheme.Modules.pullbackFreeIso (Scheme.projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n T l r d e he)

/-- **The reconstruction.**  `Q_E`, untwisted. -/
def reconstructedQuotient (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (Scheme.projectiveSpaceOver n T).Modules :=
  Scheme.projectiveSpaceOverTwistModule
    (reconstructedTwisted n T l r d e he u) (-(d : ℤ))

/-- **Multiplication by the `i`-th degree-`e` monomial**, as a map of twisting sheaves
`𝒪(a) ⟶ 𝒪(b)` on relative projective space, where `b = a + e`.  No tensor products are
involved. -/
def twistMonomialMulHom (n : ℕ) (S : Scheme.{u}) (a b : ℤ) (e : ℕ) (hb : b = a + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    Scheme.projectiveSpaceOverTwist n S a ⟶ Scheme.projectiveSpaceOverTwist n S b :=
  (Scheme.Modules.pullback
      (Limits.pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))).map
    (ProjectiveSpectrum.Twist.mulHom
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i) a b hb)

/-- **The monomial map into `F` itself**, `∐_m 𝒪(-d) ⟶ F = ∐_r 𝒪(-l)`: on the summand
`(j, i)` it is multiplication by the `i`-th degree-`e` monomial into the `j`-th summand.
This is the untwisted form of the tautological map, built without any tensor product. -/
def twistedFreeMonomialHom (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) :
    (∐ fun _ : ULift.{u} (Fin r) × Fin ((n + e).choose n) =>
        Scheme.projectiveSpaceOverTwist n S (-(d : ℤ))) ⟶
      (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n S (-l)) :=
  Limits.Sigma.desc (fun x =>
    twistMonomialMulHom n S (-(d : ℤ)) (-l) e (by omega) x.2 ≫
      Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n S (-l)) x.1)

/-- `𝒪^I ⊗ 𝒪(a) ≅ ∐_I 𝒪(a)`: distribute over the coproduct and cancel the unit.  No
associator is involved. -/
def freeTensorTwistIso (n : ℕ) (T : Scheme.{u}) (I : Type u) (a : ℤ) :
    Scheme.Modules.tensor
        (SheafOfModules.free (R := (Scheme.projectiveSpaceOver n T).ringCatSheaf) I)
        (Scheme.projectiveSpaceOverTwist n T a) ≅
      ∐ fun _ : I => Scheme.projectiveSpaceOverTwist n T a :=
  Scheme.Modules.tensorCoproductIso _ _ ≪≫
    Limits.Sigma.mapIso (fun _ => Scheme.Modules.tensorLeftUnitIso _)

/-- **The untwisted reconstruction relation.**  From `u : 𝒪_T^m ↠ E`, pull its
kernel to `ℙⁿ_T`, tensor by `𝒪(-d)`, and map the resulting relations into the
twisted-free ambient sheaf through the degree-`e` monomial map. -/
def reconstructedRelation' (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    Scheme.Modules.tensor
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverπ n T)).obj (kernel u))
        (Scheme.projectiveSpaceOverTwist n T (-(d : ℤ))) ⟶
      (∐ fun _ : ULift.{u} (Fin r) ↦ Scheme.projectiveSpaceOverTwist n T (-l)) :=
  Scheme.Modules.tensorMapLeft
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverπ n T)).map
          (Limits.kernel.ι u))
        (Scheme.projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
      (Scheme.Modules.tensorLeftIso
        (Scheme.Modules.pullbackFreeIso (Scheme.projectiveSpaceOverπ n T)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)))
        (Scheme.projectiveSpaceOverTwist n T (-(d : ℤ)))).hom ≫
      (freeTensorTwistIso n T (ULift.{u} (Fin r) × Fin ((n + e).choose n))
        (-(d : ℤ))).hom ≫
      twistedFreeMonomialHom n T l r d e he

/-- **The reconstruction, untwisted.**  From `u : 𝒪_T^m ↠ E` on the base, the family
`Q_E` on `ℙⁿ_T`: the cokernel of `π^*(ker u) ⊗ 𝒪(-d) ⟶ ∐_m 𝒪(-d) ⟶ F`. -/
def reconstructedQuotient' (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (Scheme.projectiveSpaceOver n T).Modules :=
  Limits.cokernel (reconstructedRelation' n T l r d e he u)

/-- **The tautological quotient map onto the reconstruction**, `F ↠ Q_E`. -/
def reconstructedQuotientMap' (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n T (-l)) ⟶
      reconstructedQuotient' n T l r d e he u :=
  Limits.cokernel.π (reconstructedRelation' n T l r d e he u)

instance reconstructedQuotientMap'_epi (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    Epi (reconstructedQuotientMap' n T l r d e he u) :=
  Limits.coequalizer.π_epi

/-- A globally generating family of relations identifies the untwisted Grassmannian
reconstruction with a given quotient: the reconstruction relation factors epimorphically
onto the kernel of the quotient map. -/
structure ReconstructedRelationPresentsKernel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) : Type (u + 1) where
  /-- The relation map lifted to the kernel of the proposed quotient. -/
  lift :
    Scheme.Modules.tensor
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverπ n T)).obj (kernel u))
        (Scheme.projectiveSpaceOverTwist n T (-(d : ℤ))) ⟶ kernel p
  /-- The lift recovers the reconstruction relation after the kernel inclusion. -/
  lift_comp : lift ≫ kernel.ι p = reconstructedRelation' n T l r d e he u
  /-- Global generation of the kernel makes the lift epimorphic. -/
  epi : Epi lift

namespace ReconstructedRelationPresentsKernel

/-- If the reconstruction relations generate the kernel of an epimorphic quotient, the
reconstructed quotient is canonically isomorphic to that quotient. -/
noncomputable def quotientIso
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r d e : ℕ}
    {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E}
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q} [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he u p) :
    reconstructedQuotient' n T l r d e he u ≅ Q := by
  letI : Epi D.lift := D.epi
  exact cokernelIsoOfEq D.lift_comp.symm ≪≫
    cokernelEpiCompKernelIsoOfEpi p D.lift

/-- The canonical reconstruction comparison commutes with the quotient maps from the
twisted-free ambient sheaf. -/
@[reassoc (attr := simp)]
lemma reconstructedQuotientMap'_comp_quotientIso_hom
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r d e : ℕ}
    {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E}
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q} [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he u p) :
    reconstructedQuotientMap' n T l r d e he u ≫ D.quotientIso.hom = p := by
  letI : Epi D.lift := D.epi
  dsimp [quotientIso, reconstructedQuotientMap']
  have h₁ :
      cokernel.π (reconstructedRelation' n T l r d e he u) ≫
          (cokernelIsoOfEq D.lift_comp.symm).hom =
        cokernel.π (D.lift ≫ kernel.ι p) :=
    π_comp_cokernelIsoOfEq_hom D.lift_comp.symm
  have h₂ :
      cokernel.π (D.lift ≫ kernel.ι p) ≫
          (cokernelEpiCompKernelIsoOfEpi p D.lift).hom = p :=
    cokernel_π_comp_cokernelEpiCompKernelIsoOfEpi_hom p D.lift
  exact (congrArg
    (fun k ↦ k ≫ (cokernelEpiCompKernelIsoOfEpi p D.lift).hom) h₁).trans h₂

end ReconstructedRelationPresentsKernel

end AlgebraicGeometry.Scheme
