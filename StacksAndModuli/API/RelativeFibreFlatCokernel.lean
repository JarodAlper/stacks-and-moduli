module

public import StacksAndModuli.API.FlatLocal
public import StacksAndModuli.API.FlatLocusLocal
public import StacksAndModuli.API.LinearMapCokernelBaseChange
public import StacksAndModuli.API.LocalizedRelativeFibrePushout
public import StacksAndModuli.API.PresentationTensorKernelBaseChange
public import StacksAndModuli.API.PushoutFibreExactFlatCokernel
public import StacksAndModuli.API.RelativeFibreExactnessInterface

/-!
# Flat localized cokernels from relative-fibre exactness

Let `R → S` be a flat map of noetherian rings.  Consider two consecutive maps
`L → K → F` of finite `S`-modules, with `F` projective over `S`.  At a
prime of a relative fibre, exactness after passing to the local ring of that
fibre implies that the localized cokernel is flat over the corresponding local
ring of `R`.

The proof has three ingredients.  Iterated scalar extension is identified with
direct scalar extension, the localized relative fibre is identified with the
closed-fibre pushout, and the two-differential local flatness criterion is then
applied to the localized maps.  This packages the final local algebra step of
Stacks Project tag 00MI in the form used after relative-fibre exactness has been
spread by tag 00RB.

The converse is also proved from ordinary localized exactness and flatness of
the localized outgoing cokernel.  Consequently the relative-fibre exactness
locus is identified with the intersection of the ordinary exactness locus and
that concrete flatness locus.  If the cokernel is already flat over the source
algebra, the second condition is automatic and the locus is open.

Main declarations:

* `LinearMap.baseChange_exact_iff_iteratedBaseChange_exact`;
* `Module.Flat.localizedExactAndFlatCoker_of_localizedRelativeFibre_exact`;
* `Module.Flat.localizedCoker_of_localizedRelativeFibre_exact`;
* `Module.Flat.localizedCoker_of_isRelativeFibreExactAt`;
* `LinearMap.exact_baseChange_at_sourcePrime_of_isRelativeFibreExactAt`;
* `LinearMap.relativeFibreExactLocus_eq_exactLocalizationLocus_inter_flatLocalizedCokerLocus`;
* `LinearMap.hasOpenRelativeFibreExactLocus_of_isOpen_flatLocalizedCokerLocus`;
* `LinearMap.relativeFibreExactLocus_eq_exactLocalizationLocus_of_flat_coker`;
* `LinearMap.hasOpenRelativeFibreExactLocus_of_flat_coker`;
* `ChainComplex.hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded_of_flat_cokernels`;
* `Module.Flat.localizedTensorCoker_over_base_of_isRelativeFibreExactAt`;
* `Module.Flat.localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt`;
* `Module.Flat.isRelativeFibreExactAt_of_localized_exact_of_localizedTensorCoker_flat`;
* `Module.Flat.isRelativeFibreExactAt_of_exact_of_localizedTensorCoker_flat`;
* `Module.Flat.isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact`;
* `Module.Flat.exists_away_flat_coker_of_openRelativeFibreExactLocus`;
* `Module.Flat.coker_flat_of_openRelativeFibreExactLocus`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w x

open TensorProduct

namespace LinearMap

/-- Exactness after a direct scalar extension agrees with exactness after the
same scalar extension factored through an intermediate algebra. -/
theorem baseChange_exact_iff_iteratedBaseChange_exact
    {S : Type u} {T : Type v} {A : Type w} {L K F : Type x}
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] [Algebra T A] [IsScalarTower S T A]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K]
    [AddCommGroup F] [Module S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F) :
    Function.Exact (f.baseChange A) (g.baseChange A) ↔
      Function.Exact ((f.baseChange T).baseChange A)
        ((g.baseChange T).baseChange A) := by
  let eL := AlgebraTensorModule.cancelBaseChange S T A A L
  let eK := AlgebraTensorModule.cancelBaseChange S T A A K
  let eF := AlgebraTensorModule.cancelBaseChange S T A A F
  exact Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := (f.baseChange T).baseChange A)
    (f₂₃ := (g.baseChange T).baseChange A)
    (g₁₂ := f.baseChange A) (g₂₃ := g.baseChange A)
    (e₁ := eL) (e₂ := eK) (e₃ := eF)
    (cancelBaseChange_naturality (R := S) (A := T) (B := A) f).symm
    (cancelBaseChange_naturality (R := S) (A := T) (B := A) g).symm

end LinearMap

namespace Module.Flat

/-- Exactness on the local ring of a relative fibre makes the localized
pair exact and its cokernel flat over the corresponding localized coefficient
ring. -/
theorem localizedExactAndFlatCoker_of_localizedRelativeFibre_exact
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (p : PrimeSpectrum R) (qf : PrimeSpectrum (p.asIdeal.Fiber S))
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre :
      letI : Algebra S (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.rightAlgebra
      Function.Exact
        (f.baseChange (Localization.AtPrime qf.asIdeal))
        (g.baseChange (Localization.AtPrime qf.asIdeal))) :
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    Function.Exact (f.baseChange Sr) (g.baseChange Sr) ∧
      Module.Flat Rp
        ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) := by
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  let k := p.asIdeal.ResidueField
  let A := Localization.AtPrime qf.asIdeal
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hrp : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  haveI : r.LiesOver p.asIdeal := hrp
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  have hpush : Algebra.IsPushout Rp Sr k A :=
    PrimeSpectrum.localizedRelativeFibre_isPushout p qf
  letI : Algebra.IsPushout Rp k Sr A :=
    Algebra.IsPushout.symm hpush
  have hiter : Function.Exact
      ((f.baseChange Sr).baseChange A)
      ((g.baseChange Sr).baseChange A) :=
    (LinearMap.baseChange_exact_iff_iteratedBaseChange_exact
      (T := Sr) (A := A) f g).mp hfibre
  have hcompq : (g.baseChange Sr).comp (f.baseChange Sr) = 0 := by
    rw [← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero]
  letI : Module.Flat S F := Module.Flat.of_projective
  letI : Module.Flat Sr (Sr ⊗[S] F) :=
    Module.Flat.baseChange S Sr F
  letI : Module.Flat Rp Sr := inferInstance
  letI : Module.Flat Rp (Sr ⊗[S] F) :=
    Module.Flat.trans Rp Sr (Sr ⊗[S] F)
  exact Module.Flat.exact_and_flat_coker_of_isPushout_baseChange_exact
    (R := Rp) (S := Sr) (B := A)
    (f.baseChange Sr) (g.baseChange Sr) hcompq hiter

/-- Exactness on the local ring of a relative fibre makes the localized
cokernel flat over the corresponding localized coefficient ring. -/
theorem localizedCoker_of_localizedRelativeFibre_exact
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (p : PrimeSpectrum R) (qf : PrimeSpectrum (p.asIdeal.Fiber S))
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre :
      letI : Algebra S (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.rightAlgebra
      Function.Exact
        (f.baseChange (Localization.AtPrime qf.asIdeal))
        (g.baseChange (Localization.AtPrime qf.asIdeal))) :
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    Module.Flat Rp
      ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) :=
  (localizedExactAndFlatCoker_of_localizedRelativeFibre_exact
    p qf f g hcomp hfibre).2

/-- The preceding local flat-cokernel theorem expressed through the named
relative-fibre exactness predicate at a prime of `S`.

The output retains the contracted ideal of the induced fibre prime.  It equals
the original prime by
`PrimeSpectrum.relativeFibrePrime_comap_includeRight`; keeping this model avoids
transporting localization typeclass instances across that equality. -/
theorem localizedExactAndFlatCoker_of_isRelativeFibreExactAt
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    Function.Exact (f.baseChange Sr) (g.baseChange Sr) ∧
      Module.Flat Rp
        ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let A := Localization.AtPrime qf.asIdeal
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hfibre' : Function.Exact
      (f.baseChange A) (g.baseChange A) := by
    exact hfibre
  exact localizedExactAndFlatCoker_of_localizedRelativeFibre_exact
    p qf f g hcomp hfibre'

/-- The local flat-cokernel theorem expressed through the named relative-fibre exactness
predicate at a prime of the source algebra. -/
theorem localizedCoker_of_isRelativeFibreExactAt
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    Module.Flat Rp
      ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) :=
  (localizedExactAndFlatCoker_of_isRelativeFibreExactAt
    q f g hcomp hfibre).2

/-- Relative-fibre exactness at a source prime makes the localization of the original
cokernel flat over the original coefficient ring.

The localization is retained at the contraction of the induced fibre prime.  This ideal
equals the input prime by `PrimeSpectrum.relativeFibrePrime_comap_includeRight`; retaining
it avoids dependent transport of localization instances.  Compared with
`localizedCoker_of_isRelativeFibreExactAt`, the conclusion is transported across right
exactness of scalar extension and then descended from the localized coefficient ring. -/
theorem localizedTensorCoker_over_base_of_isRelativeFibreExactAt
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Rp := Localization.AtPrime p.asIdeal
    let Sr := Localization.AtPrime r
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    letI : r.LiesOver p.asIdeal :=
      Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
    letI : Algebra Rp Sr :=
      Localization.AtPrime.algebraOfLiesOver p.asIdeal r
    Module.Flat R (Sr ⊗[S] (F ⧸ LinearMap.range g)) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hrp : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  letI : r.LiesOver p.asIdeal := hrp
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  have hlocal : Module.Flat Rp
      ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) :=
    localizedCoker_of_isRelativeFibreExactAt q f g hcomp hfibre
  let e : ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) ≃ₗ[Sr]
      Sr ⊗[S] (F ⧸ LinearMap.range g) :=
    LinearMap.baseChangeCokerEquiv g
  let _ : Module.Flat Rp
      ((Sr ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sr)) := hlocal
  have htarget : Module.Flat Rp (Sr ⊗[S] (F ⧸ LinearMap.range g)) :=
    Module.Flat.of_linearEquiv (e.symm.restrictScalars Rp)
  let _ : Module.Flat Rp (Sr ⊗[S] (F ⧸ LinearMap.range g)) := htarget
  exact Module.Flat.trans R Rp (Sr ⊗[S] (F ⧸ LinearMap.range g))

/-- Relative-fibre exactness at a source prime makes the localization of the original
cokernel at that same prime flat over the coefficient ring.

This is the source-prime form of
`localizedTensorCoker_over_base_of_isRelativeFibreExactAt`.  The proof transports the
localization structure across equality of the relevant prime complements, then uses the
canonical equivalence between the two localization rings. -/
theorem localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    Module.Flat R
      (Localization.AtPrime q.asIdeal ⊗[S]
        (F ⧸ LinearMap.range g)) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hrp : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  letI : r.LiesOver p.asIdeal := hrp
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  have hrq : r = q.asIdeal :=
    PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q
  have hlocal : Module.Flat R
      (Sr ⊗[S] (F ⧸ LinearMap.range g)) :=
    localizedTensorCoker_over_base_of_isRelativeFibreExactAt
      q f g hcomp hfibre
  have hcompl : r.primeCompl = q.asIdeal.primeCompl := by
    ext x
    change (x ∉ r) ↔ (x ∉ q.asIdeal)
    rw [hrq]
  letI : IsLocalization q.asIdeal.primeCompl Sr := by
    exact hcompl ▸ (inferInstance : IsLocalization r.primeCompl Sr)
  let eRing : Sr ≃ₐ[S] Sq :=
    IsLocalization.algEquiv q.asIdeal.primeCompl Sr Sq
  let eTensor : (Sr ⊗[S] (F ⧸ LinearMap.range g)) ≃ₗ[S]
      Sq ⊗[S] (F ⧸ LinearMap.range g) :=
    TensorProduct.congr eRing.toLinearEquiv
      (LinearEquiv.refl S (F ⧸ LinearMap.range g))
  let _ : Module.Flat R (Sr ⊗[S] (F ⧸ LinearMap.range g)) := hlocal
  exact Module.Flat.of_linearEquiv (eTensor.symm.restrictScalars R)

/-- If two maps are exact after localization at a source prime and the localized
cokernel of the second map is flat over the coefficient ring, then the pair is
exact on the localized relative fibre at that prime.

This version needs only ordinary exactness at the chosen source prime, rather
than exactness of the original pair globally. -/
theorem isRelativeFibreExactAt_of_localized_exact_of_localizedTensorCoker_flat
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K]
    [AddCommGroup F] [Module S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hexact : Function.Exact
      (LocalizedModule.map q.asIdeal.primeCompl f)
      (LocalizedModule.map q.asIdeal.primeCompl g))
    (hflat : Module.Flat R
      (Localization.AtPrime q.asIdeal ⊗[S]
        (F ⧸ LinearMap.range g))) :
    LinearMap.IsRelativeFibreExactAt (R := R) f g q := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  let Sq := Localization.AtPrime q.asIdeal
  let k := p.asIdeal.ResidueField
  let A := Localization.AtPrime qf.asIdeal
  let M := F ⧸ LinearMap.range g
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hrp : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  letI : r.LiesOver p.asIdeal := hrp
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  have hpush : Algebra.IsPushout Rp Sr k A :=
    PrimeSpectrum.localizedRelativeFibre_isPushout p qf
  letI : Algebra.IsPushout Rp k Sr A :=
    Algebra.IsPushout.symm hpush
  have hrq : r = q.asIdeal :=
    PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q
  have hcompl : r.primeCompl = q.asIdeal.primeCompl := by
    ext x
    change (x ∉ r) ↔ (x ∉ q.asIdeal)
    rw [hrq]
  have hflatSrR : Module.Flat R (Sr ⊗[S] M) := by
    letI : IsLocalization q.asIdeal.primeCompl Sr := by
      exact hcompl ▸ (inferInstance : IsLocalization r.primeCompl Sr)
    let eRing : Sr ≃ₐ[S] Sq :=
      IsLocalization.algEquiv q.asIdeal.primeCompl Sr Sq
    let eTensor : (Sr ⊗[S] M) ≃ₗ[S] (Sq ⊗[S] M) :=
      TensorProduct.congr eRing.toLinearEquiv (LinearEquiv.refl S M)
    let _ : Module.Flat R (Sq ⊗[S] M) := hflat
    exact Module.Flat.of_linearEquiv (eTensor.restrictScalars R)
  have hflatSrRp : Module.Flat Rp (Sr ⊗[S] M) :=
    (Module.flat_iff_of_isLocalization Rp p.asIdeal.primeCompl
      (Sr ⊗[S] M)).mpr hflatSrR
  let qmap : F →ₗ[S] M := (LinearMap.range g).mkQ
  let fSr := f.baseChange Sr
  let gSr := g.baseChange Sr
  let qSr := qmap.baseChange Sr
  have hfgSr : Function.Exact fSr gSr := by
    apply (LinearMap.exact_localizedMap_iff_baseChange
      r.primeCompl f g).mp
    exact hcompl.symm ▸ hexact
  have hgqSr : Function.Exact gSr qSr := by
    simpa only [gSr, qSr, qmap, LinearMap.baseChange_eq_ltensor] using
      _root_.lTensor_exact Sr (LinearMap.exact_map_mkQ_range g)
        (Submodule.mkQ_surjective (LinearMap.range g))
  have hqSr : Function.Surjective qSr :=
    LinearMap.baseChange_surjective Sr
      (Submodule.mkQ_surjective (LinearMap.range g))
  let _ : Module.Flat Rp (Sr ⊗[S] M) := hflatSrRp
  have hresidue : Function.Exact
      ((fSr.restrictScalars Rp).lTensor k)
      ((gSr.restrictScalars Rp).lTensor k) :=
    LinearMap.lTensor_exact_of_exact_of_flat_cokernel
      (fSr.restrictScalars Rp) (gSr.restrictScalars Rp) hfgSr
        (qSr.restrictScalars Rp) hgqSr hqSr
  have hiter : Function.Exact (fSr.baseChange A) (gSr.baseChange A) :=
    (LinearMap.baseChange_exact_iff_lTensor_exact_of_isPushout
      (R := Rp) (k := k) (S := Sr) (B := A) fSr gSr).mpr
        hresidue
  exact (LinearMap.baseChange_exact_iff_iteratedBaseChange_exact
    (S := S) (T := Sr) (A := A) f g).mpr hiter

/-- If two maps are exact before base change and the localization of the second map's
cokernel at a source prime is flat over the coefficient ring, then the pair is exact on
the localized relative fibre at that prime.

This is the converse local-algebra direction to
`localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt`.  The proof transports the
flat module to the contracted localization model, passes flatness from the coefficient ring
to its localization, and uses flat-cokernel preservation of exactness on the pushout fibre. -/
theorem isRelativeFibreExactAt_of_exact_of_localizedTensorCoker_flat
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K]
    [AddCommGroup F] [Module S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hexact : Function.Exact f g)
    (hflat : Module.Flat R
      (Localization.AtPrime q.asIdeal ⊗[S]
        (F ⧸ LinearMap.range g))) :
    LinearMap.IsRelativeFibreExactAt (R := R) f g q := by
  apply isRelativeFibreExactAt_of_localized_exact_of_localizedTensorCoker_flat
    q f g
  · exact LocalizedModule.map_exact q.asIdeal.primeCompl f g hexact
  · exact hflat

/-- For an exact presentation by finite modules with projective final term, relative-fibre
exactness at a source prime is equivalent to coefficient-flatness of the localized concrete
cokernel at that prime. -/
theorem isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact
    {R : Type u} {S L K F : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hexact : Function.Exact f g) :
    LinearMap.IsRelativeFibreExactAt (R := R) f g q ↔
      Module.Flat R
        (Localization.AtPrime q.asIdeal ⊗[S]
          (F ⧸ LinearMap.range g)) := by
  constructor
  · intro hfibre
    exact localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
      q f g hexact.linearMap_comp_eq_zero hfibre
  · exact isRelativeFibreExactAt_of_exact_of_localizedTensorCoker_flat
      q f g hexact

/-- If relative-fibre exactness is open and holds at a source prime, then the original
cokernel is flat over the coefficient ring after localizing on some basic-open
neighbourhood of that prime. -/
theorem exists_away_flat_coker_of_openRelativeFibreExactLocus
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hopen : LinearMap.HasOpenRelativeFibreExactLocus (R := R) f g)
    (q : PrimeSpectrum S)
    (hq : LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    ∃ a ∉ q.asIdeal,
      Module.Flat R
        (LocalizedModule.Away a (F ⧸ LinearMap.range g)) := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  obtain ⟨V, hVsub, hVopen, hqV⟩ :=
    (isOpen_iff_forall_mem_open.mp hopen) q hq
  obtain ⟨W, ⟨a, rfl⟩, hqW, hWsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hqV hVopen
  refine ⟨a, hqW, Module.Flat.away_of_forall_mem_basicOpen_flat_localizationAtPrime
    a ?_⟩
  intro q' hq'
  exact localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
    q' f g hcomp (hVsub (hWsub hq'))

/-- If relative-fibre exactness is open and holds at every source prime, then the original
cokernel is flat over the coefficient ring. -/
theorem coker_flat_of_openRelativeFibreExactLocus
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hopen : LinearMap.HasOpenRelativeFibreExactLocus (R := R) f g)
    (hall : ∀ q : PrimeSpectrum S,
      LinearMap.IsRelativeFibreExactAt (R := R) f g q) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    Module.Flat R (F ⧸ LinearMap.range g) := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  apply Module.Flat.of_forall_prime_exists_away (S := S)
  intro q
  exact exists_away_flat_coker_of_openRelativeFibreExactLocus
    f g hcomp hopen q (hall q)

end Module.Flat

namespace LinearMap

/-- Relative-fibre exactness at a source prime implies ordinary exactness after localizing
the original pair at that prime.

This is the pointwise 00MI step used at the start of the proof of Stacks Project tag 00RB.
The proof first obtains exactness in the localization model indexed by the contraction of
the induced fibre prime, then transports only the prime-complement submonoid before
returning to scalar extension. -/
theorem exact_baseChange_at_sourcePrime_of_isRelativeFibreExactAt
    {R : Type u} {S L K F : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (q : PrimeSpectrum S) (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hfibre : IsRelativeFibreExactAt (R := R) f g q) :
    Function.Exact
      (f.baseChange (Localization.AtPrime q.asIdeal))
      (g.baseChange (Localization.AtPrime q.asIdeal)) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Rp := Localization.AtPrime p.asIdeal
  let Sr := Localization.AtPrime r
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  have hrp : r.LiesOver p.asIdeal :=
    Ideal.under_liesOver_of_liesOver S qf.asIdeal p.asIdeal
  letI : r.LiesOver p.asIdeal := hrp
  letI : Algebra Rp Sr :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal r
  have hlocal : Function.Exact
      (f.baseChange Sr) (g.baseChange Sr) :=
    (Module.Flat.localizedExactAndFlatCoker_of_isRelativeFibreExactAt
      q f g hcomp hfibre).1
  have hrq : r = q.asIdeal :=
    PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q
  have hlocalLM : Function.Exact
      (LocalizedModule.map r.primeCompl f)
      (LocalizedModule.map r.primeCompl g) := by
    apply (exact_localizedMap_iff_baseChange r.primeCompl f g).mpr
    simpa only [Sr] using hlocal
  have hcompl : r.primeCompl = q.asIdeal.primeCompl := by
    ext x
    change (x ∉ r) ↔ (x ∉ q.asIdeal)
    rw [hrq]
  have hqLM : Function.Exact
      (LocalizedModule.map q.asIdeal.primeCompl f)
      (LocalizedModule.map q.asIdeal.primeCompl g) := by
    exact hcompl ▸ hlocalLM
  exact (exact_localizedMap_iff_baseChange
    q.asIdeal.primeCompl f g).mp hqLM

/-- The relative-fibre exactness locus is exactly the intersection of the
ordinary localization-exactness locus with the locus where the localized
cokernel is flat over the coefficient ring.

This is the complete pointwise local-algebra reduction behind 00RB.  The only
remaining issue for openness is the variation of the second condition. -/
theorem relativeFibreExactLocus_eq_exactLocalizationLocus_inter_flatLocalizedCokerLocus
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    relativeFibreExactLocus (R := R) f g =
      exactLocalizationLocus f g ∩
        {q | Module.Flat R
          (Localization.AtPrime q.asIdeal ⊗[S]
            (F ⧸ LinearMap.range g))} := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  ext q
  constructor
  · intro hq
    refine ⟨?_, Module.Flat.localizedTensorCoker_at_sourcePrime_of_isRelativeFibreExactAt
      q f g hcomp hq⟩
    exact (exact_localizedMap_iff_baseChange
      q.asIdeal.primeCompl f g).mpr
        (exact_baseChange_at_sourcePrime_of_isRelativeFibreExactAt
          q f g hcomp hq)
  · rintro ⟨hexact, hflat⟩
    exact Module.Flat.isRelativeFibreExactAt_of_localized_exact_of_localizedTensorCoker_flat
      q f g hexact hflat

/-- Openness of the localized coefficient-flatness locus of the outgoing
cokernel supplies openness of the relative-fibre exactness locus. -/
theorem hasOpenRelativeFibreExactLocus_of_isOpen_flatLocalizedCokerLocus
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    (hopen :
      letI : Module R (F ⧸ LinearMap.range g) :=
        Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
      letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
        IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
      IsOpen {q : PrimeSpectrum S | Module.Flat R
        (Localization.AtPrime q.asIdeal ⊗[S]
          (F ⧸ LinearMap.range g))}) :
    HasOpenRelativeFibreExactLocus (R := R) f g := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  change IsOpen (relativeFibreExactLocus (R := R) f g)
  rw [relativeFibreExactLocus_eq_exactLocalizationLocus_inter_flatLocalizedCokerLocus
    f g hcomp]
  exact (isOpen_exactLocalizationLocus f g hcomp).inter hopen

/-- When the cokernel of the second map is already flat over the source algebra,
relative-fibre exactness and ordinary exactness at a source prime are equivalent.

The forward implication is the pointwise 00MI argument.  Conversely, ordinary
localized exactness survives the further base change to the corresponding
relative-fibre local ring because the localized cokernel is flat. -/
theorem relativeFibreExactLocus_eq_exactLocalizationLocus_of_flat_coker
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    [Module.Flat S (F ⧸ LinearMap.range g)] :
    relativeFibreExactLocus (R := R) f g =
      exactLocalizationLocus f g := by
  ext q
  constructor
  · intro hq
    apply (exact_localizedMap_iff_baseChange
      q.asIdeal.primeCompl f g).mpr
    exact exact_baseChange_at_sourcePrime_of_isRelativeFibreExactAt
      q f g hcomp hq
  · intro hq
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    let Sq := Localization.AtPrime q.asIdeal
    let A := Localization.AtPrime qf.asIdeal
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    have hqf : qf.asIdeal.LiesOver q.asIdeal := ⟨by
      rw [Ideal.under_def, Algebra.TensorProduct.algebraMap_eq_includeRight]
      exact (PrimeSpectrum.relativeFibrePrime_comap_includeRight
        (R := R) q).symm⟩
    letI : qf.asIdeal.LiesOver q.asIdeal := hqf
    letI : Algebra Sq A :=
      Localization.AtPrime.algebraOfLiesOver q.asIdeal qf.asIdeal
    have hlocal : Function.Exact
        (f.baseChange Sq) (g.baseChange Sq) :=
      (exact_localizedMap_iff_baseChange
        q.asIdeal.primeCompl f g).mp hq
    letI : Module.Flat Sq
        (Sq ⊗[S] (F ⧸ LinearMap.range g)) :=
      Module.Flat.baseChange S Sq (F ⧸ LinearMap.range g)
    let eC :
        ((Sq ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sq)) ≃ₗ[Sq]
          Sq ⊗[S] (F ⧸ LinearMap.range g) :=
      LinearMap.baseChangeCokerEquiv g
    letI : Module.Flat Sq
        ((Sq ⊗[S] F) ⧸ LinearMap.range (g.baseChange Sq)) :=
      Module.Flat.of_linearEquiv eC
    have hiter : Function.Exact
        ((f.baseChange Sq).baseChange A)
        ((g.baseChange Sq).baseChange A) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        LinearMap.lTensor_exact_of_exact_of_coker_flat
          (f.baseChange Sq) (g.baseChange Sq) hlocal
          (A := A)
    exact (LinearMap.baseChange_exact_iff_iteratedBaseChange_exact
      (T := Sq) (A := A) f g).mpr hiter

/-- The relative-fibre exactness locus is open when the cokernel of the second
map is flat over the source algebra. -/
theorem hasOpenRelativeFibreExactLocus_of_flat_coker
    {R S L K F : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hcomp : g.comp f = 0)
    [Module.Flat S (F ⧸ LinearMap.range g)] :
    HasOpenRelativeFibreExactLocus (R := R) f g := by
  change IsOpen (relativeFibreExactLocus (R := R) f g)
  rw [relativeFibreExactLocus_eq_exactLocalizationLocus_of_flat_coker
    f g hcomp]
  exact isOpen_exactLocalizationLocus f g hcomp

end LinearMap

namespace ChainComplex

open CategoryTheory

/-- A bounded complex of finite projective modules has open positive-degree
relative-fibre exactness locus when the cokernel of every displayed outgoing
differential is flat.

This is the bounded-complex form of
`LinearMap.hasOpenRelativeFibreExactLocus_of_flat_coker`.  Unlike the full
00RB theorem, it assumes the flatness which makes exactness stable under the
second base change to the relative fibre. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded_of_flat_cokernels
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (C : ChainComplex (ModuleCat.{u} S) ℕ) (N : ℕ)
    (hfinite : ∀ i, Module.Finite S (C.X i))
    (hprojective : ∀ i, Module.Projective S (C.X i))
    (hflatCoker : ∀ i, 0 < i → i ≤ N →
      Module.Flat S
        ((C.X (i - 1)) ⧸ LinearMap.range (C.d i (i - 1)).hom))
    (hzero : ∀ i, N < i → CategoryTheory.Limits.IsZero (C.X i)) :
    HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C := by
  apply hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded_of_pairwise
    C N
  · intro i hi hiN
    letI : Module.Finite S (C.X i) := hfinite i
    letI : Module.Finite S (C.X (i - 1)) := hfinite (i - 1)
    letI : Module.Projective S (C.X (i - 1)) := hprojective (i - 1)
    letI : Module.Flat S
        ((C.X (i - 1)) ⧸ LinearMap.range (C.d i (i - 1)).hom) :=
      hflatCoker i hi hiN
    apply LinearMap.hasOpenRelativeFibreExactLocus_of_flat_coker
    exact congrArg ModuleCat.Hom.hom (C.d_comp_d (i + 1) i (i - 1))
  · exact hzero

end ChainComplex

end

end
