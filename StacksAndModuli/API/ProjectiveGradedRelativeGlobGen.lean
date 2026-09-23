module

public import StacksAndModuli.API.ProjectiveGradedRelativeCBC

/-!
# Global generation of a flat family, checked on fibres

Supporting API with no Stacks Project counterpart: Proposition 2.3.18(3) in the graded model.

`(π_* M(d)) ⊗ S_{e-d} → π_* M(e)` is surjective as soon as it is surjective on every fibre
(`Module.surjective_of_forall_quotient_maximal`), provided the formation of `π_* M(e)` commutes
with base change in every twist involved — which is what Cohomology and Base Change gives when
the higher cohomology vanishes fibrewise in every twist `≥ d`.

Main declarations:
- `GradedModule.cechHgrZeroBaseChangeEquiv_mulX`: the base-change comparison for `π_*` is
  compatible with multiplication by a variable.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct
open AlgebraicGeometry.ProjectiveSpace.CochainComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
  (M : GradedModule R n) (A : Type u) [CommRing A] [Algebra R A] (j : Fin (n + 1)) (d : ℤ)

/-- Square 4: the Čech-complex base-change isomorphism intertwines multiplication by a
variable on cohomology. -/
lemma homologyMap_cechHgrBaseChangeHomologyIso (q : ℕ) :
    HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) q
        ≫ (cechHgrBaseChangeHomologyIso M (d + 1) A q).hom
      = (cechHgrBaseChangeHomologyIso M d A q).hom
        ≫ HomologicalComplex.homologyMap
            (cochainBaseChangeMap A (M.cechMulX j d)) q := by
  have h := congrArg (fun t => HomologicalComplex.homologyMap t q)
    (cechMulX_cechComplexBaseChangeIso A M j d)
  simpa only [HomologicalComplex.homologyMap_comp, cechHgrBaseChangeHomologyIso,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map] using h

variable {M d}

/-- **The base-change comparison for `π_* M(d)` is compatible with multiplication by a
variable.** This is what upgrades `cechHgrZeroBaseChangeEquiv` from a degreewise comparison to
a comparison of graded modules in the twists where it is available. -/
lemma cechHgrZeroBaseChangeEquiv_mulX (hM : IsFG M) (hflat : IsFlat M)
    (h0 : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (h1 : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d + 1)))
    (x : A ⊗[R] ((M.cechHgr 0).obj d)) :
    cechHgrZeroBaseChangeEquiv (d := d + 1) hM hflat h1 A
        ((LinearMap.baseChange A (((M.cechHgr 0).mulX j d).hom)) x)
      = ((((M.baseChange A).cechHgr 0).mulX j d).hom)
          (cechHgrZeroBaseChangeEquiv (d := d) hM hflat h0 A x) := by
  have hfl0 := flat_cechComplex_X M d hflat
  have hfl1 := flat_cechComplex_X M (d + 1) hflat
  have hvan0 : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex d).X p) :=
    fun p hp => subsingleton_cechComplex_X M d hp
  have hvan1 : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex (d + 1)).X p) :=
    fun p hp => subsingleton_cechComplex_X M (d + 1) hp
  have hex0 := exactAtSucc_cechComplex_of_fibrewise M d hM hflat h0
  have hex1 := exactAtSucc_cechComplex_of_fibrewise M (d + 1) hM hflat h1
  -- Square 1: the comparison of `homology 0` with cocycles, base-changed.
  have hcomp1 : (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap ∘ₗ
        ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)
      = (cocyclesMap (M.cechMulX j d) 0) ∘ₗ
        (homologyZeroEquiv (M.cechComplex d)).toLinearMap :=
    LinearMap.ext (fun y => homologyZeroEquiv_naturality (M.cechMulX j d) y)
  have step1 : ∀ z : A ⊗[R] ((M.cechComplex d).homology 0),
      (LinearMap.baseChange A (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap)
          ((LinearMap.baseChange A
            ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)) z)
        = (LinearMap.baseChange A (cocyclesMap (M.cechMulX j d) 0))
            ((LinearMap.baseChange A
              (homologyZeroEquiv (M.cechComplex d)).toLinearMap) z) := by
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp1,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
  -- Square 2: the cocycle base-change comparison.
  have step2 : ∀ w : A ⊗[R] (cocyclesSub (M.cechComplex d) 0),
      cocyclesBaseChangeEquiv (M.cechComplex (d + 1)) hfl1 hvan1 hex1 A 0
          ((LinearMap.baseChange A (cocyclesMap (M.cechMulX j d) 0)) w)
        = cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0
            (cocyclesBaseChangeEquiv (M.cechComplex d) hfl0 hvan0 hex0 A 0 w) := fun w =>
    Subtype.ext (cocyclesBaseChangeEquiv_naturality (M.cechMulX j d)
      hfl0 hvan0 hex0 hfl1 hvan1 hex1 A 0 w)
  -- Square 3: back from cocycles to `homology 0`, after base change.
  have step3 : ∀ v : cocyclesSub (cochainBaseChange A (M.cechComplex d)) 0,
      (HomologicalComplex.homologyMap (cochainBaseChangeMap A (M.cechMulX j d)) 0).hom
          ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm v)
        = (homologyZeroEquiv (cochainBaseChange A (M.cechComplex (d + 1)))).symm
            (cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0 v) := fun v =>
    homologyZeroEquiv_symm_naturality (cochainBaseChangeMap A (M.cechMulX j d)) v
      (cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0 v).2
  -- Square 4: the Čech-complex base-change isomorphism.
  have hM4 := homologyMap_cechHgrBaseChangeHomologyIso M A j d 0
  have step4 : ∀ u : (cochainBaseChange A (M.cechComplex d)).homology 0,
      (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv.hom
          ((HomologicalComplex.homologyMap
            (cochainBaseChangeMap A (M.cechMulX j d)) 0).hom u)
        = (HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) 0).hom
            ((cechHgrBaseChangeHomologyIso M d A 0).inv.hom u) := by
    intro u
    have h := congrArg
      (fun t => (cechHgrBaseChangeHomologyIso M d A 0).inv ≫ t
        ≫ (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv) hM4
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
    have h' := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp] at h'
    exact (LinearMap.congr_fun h' u).symm
  change (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv.hom
      ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex (d + 1)))).symm
        (cocyclesBaseChangeEquiv (M.cechComplex (d + 1)) hfl1 hvan1 hex1 A 0
          ((LinearMap.baseChange A (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap)
            ((LinearMap.baseChange A
              ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)) x))))
    = (HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) 0).hom
      ((cechHgrBaseChangeHomologyIso M d A 0).inv.hom
        ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm
          (cocyclesBaseChangeEquiv (M.cechComplex d) hfl0 hvan0 hex0 A 0
            ((LinearMap.baseChange A
              (homologyZeroEquiv (M.cechComplex d)).toLinearMap) x))))
  rw [step1, step2, ← step3, step4]

/-- The cochain-flat form of
`GradedModule.cechHgrZeroBaseChangeEquiv_mulX`.  This is the form needed for a
flat quasicoherent sheaf: its Čech terms are flat over the base even when the
graded pieces of a chosen module model are not. -/
lemma cechHgrZeroBaseChangeEquiv'_mulX (hM : IsFG M)
    (hflat0 : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hflat1 : ∀ p : ℕ, Module.Flat R ((M.cechComplex (d + 1)).X p))
    (h0 : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj d))
    (h1 : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d + 1)))
    (x : A ⊗[R] ((M.cechHgr 0).obj d)) :
    cechHgrZeroBaseChangeEquiv' (d := d + 1) hM hflat1 h1 A
        ((LinearMap.baseChange A (((M.cechHgr 0).mulX j d).hom)) x)
      = ((((M.baseChange A).cechHgr 0).mulX j d).hom)
          (cechHgrZeroBaseChangeEquiv' (d := d) hM hflat0 h0 A x) := by
  have hvan0 : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex d).X p) :=
    fun p hp => subsingleton_cechComplex_X M d hp
  have hvan1 : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex (d + 1)).X p) :=
    fun p hp => subsingleton_cechComplex_X M (d + 1) hp
  have hex0 := exactAtSucc_cechComplex_of_fibrewise' (M := M) (d := d) hM hflat0 h0
  have hex1 := exactAtSucc_cechComplex_of_fibrewise' (M := M) (d := d + 1) hM hflat1 h1
  have hcomp1 : (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap ∘ₗ
        ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)
      = (cocyclesMap (M.cechMulX j d) 0) ∘ₗ
        (homologyZeroEquiv (M.cechComplex d)).toLinearMap :=
    LinearMap.ext (fun y => homologyZeroEquiv_naturality (M.cechMulX j d) y)
  have step1 : ∀ z : A ⊗[R] ((M.cechComplex d).homology 0),
      (LinearMap.baseChange A (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap)
          ((LinearMap.baseChange A
            ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)) z)
        = (LinearMap.baseChange A (cocyclesMap (M.cechMulX j d) 0))
            ((LinearMap.baseChange A
              (homologyZeroEquiv (M.cechComplex d)).toLinearMap) z) := by
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp1,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
  have step2 : ∀ w : A ⊗[R] (cocyclesSub (M.cechComplex d) 0),
      cocyclesBaseChangeEquiv (M.cechComplex (d + 1)) hflat1 hvan1 hex1 A 0
          ((LinearMap.baseChange A (cocyclesMap (M.cechMulX j d) 0)) w)
        = cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0
            (cocyclesBaseChangeEquiv (M.cechComplex d) hflat0 hvan0 hex0 A 0 w) := fun w =>
    Subtype.ext (cocyclesBaseChangeEquiv_naturality (M.cechMulX j d)
      hflat0 hvan0 hex0 hflat1 hvan1 hex1 A 0 w)
  have step3 : ∀ v : cocyclesSub (cochainBaseChange A (M.cechComplex d)) 0,
      (HomologicalComplex.homologyMap (cochainBaseChangeMap A (M.cechMulX j d)) 0).hom
          ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm v)
        = (homologyZeroEquiv (cochainBaseChange A (M.cechComplex (d + 1)))).symm
            (cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0 v) := fun v =>
    homologyZeroEquiv_symm_naturality (cochainBaseChangeMap A (M.cechMulX j d)) v
      (cocyclesMap (cochainBaseChangeMap A (M.cechMulX j d)) 0 v).2
  have hM4 := homologyMap_cechHgrBaseChangeHomologyIso M A j d 0
  have step4 : ∀ z : (cochainBaseChange A (M.cechComplex d)).homology 0,
      (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv.hom
          ((HomologicalComplex.homologyMap
            (cochainBaseChangeMap A (M.cechMulX j d)) 0).hom z)
        = (HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) 0).hom
            ((cechHgrBaseChangeHomologyIso M d A 0).inv.hom z) := by
    intro z
    have h := congrArg
      (fun t => (cechHgrBaseChangeHomologyIso M d A 0).inv ≫ t
        ≫ (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv) hM4
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
    have h' := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp] at h'
    exact (LinearMap.congr_fun h' z).symm
  change (cechHgrBaseChangeHomologyIso M (d + 1) A 0).inv.hom
      ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex (d + 1)))).symm
        (cocyclesBaseChangeEquiv (M.cechComplex (d + 1)) hflat1 hvan1 hex1 A 0
          ((LinearMap.baseChange A (homologyZeroEquiv (M.cechComplex (d + 1))).toLinearMap)
            ((LinearMap.baseChange A
              ((HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom)) x))))
    = (HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) 0).hom
      ((cechHgrBaseChangeHomologyIso M d A 0).inv.hom
        ((homologyZeroEquiv (cochainBaseChange A (M.cechComplex d))).symm
          (cocyclesBaseChangeEquiv (M.cechComplex d) hflat0 hvan0 hex0 A 0
            ((LinearMap.baseChange A
              (homologyZeroEquiv (M.cechComplex d)).toLinearMap) x))))
  rw [step1, step2, ← step3, step4]

/-- **Nakayama for multiplication spans**: a multiplication span is everything as soon as it is
everything after tensoring with each residue field. -/
lemma mulSpan_eq_top_of_forall_quotient_maximal (V : GradedModule R n) (d e : ℤ)
    [Module.Finite R (V.obj e)]
    (h : ∀ m : Ideal R, m.IsMaximal → (V.baseChange (R ⧸ m)).mulSpan d e = ⊤) :
    V.mulSpan d e = ⊤ := by
  haveI : Module.Finite R ((V.obj e : Type u) ⧸ V.mulSpan d e) := Module.Finite.quotient R _
  have hsub : Subsingleton ((V.obj e : Type u) ⧸ V.mulSpan d e) := by
    refine Module.subsingleton_of_forall_quotient_maximal (R := R) (fun m hm => ?_)
    have htop : LinearMap.range
        (LinearMap.baseChange (R ⧸ m) (V.mulSpan d e).subtype) = ⊤ :=
      range_baseChange_mulSpan_subtype_eq_top (R ⧸ m) V d e (h m hm)
    haveI : Subsingleton (((R ⧸ m) ⊗[R] (V.obj e)) ⧸
        (LinearMap.range (LinearMap.baseChange (R ⧸ m) (V.mulSpan d e).subtype))) :=
      Submodule.Quotient.subsingleton_iff.mpr htop
    exact (quotBaseChangeEquiv (R ⧸ m) (V.mulSpan d e)).symm.injective.subsingleton
  rw [← Submodule.Quotient.subsingleton_iff]
  exact hsub

variable (M d)

/-- **The base-change comparison for `π_*` is compatible with multiplication by a monomial**,
in every twist where it is defined. -/
lemma cechHgrZeroBaseChangeEquiv_mulList (hM : IsFG M) (hflat : IsFlat M)
    (hv : ∀ (e : ℤ), d ≤ e → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e)) :
    ∀ (l : List (Fin (n + 1))) (d' e : ℤ) (h : d' + (l.length : ℤ) = e) (hd' : d ≤ d')
      (x : A ⊗[R] ((M.cechHgr 0).obj d')),
      cechHgrZeroBaseChangeEquiv (d := e) hM hflat (hv e (by omega)) A
          ((LinearMap.baseChange A (((M.cechHgr 0).mulList l d' e h).hom)) x)
        = ((((M.baseChange A).cechHgr 0).mulList l d' e h).hom)
            (cechHgrZeroBaseChangeEquiv (d := d') hM hflat (hv d' hd') A x) := by
  intro l
  induction l with
  | nil =>
      intro d' e h hd' x
      have he : d' = e := by simpa using h
      subst he
      have h1 : ((M.cechHgr 0).mulList [] d' d' h) = 𝟙 _ := eqToHom_refl _ _
      have h2 : ((((M.baseChange A).cechHgr 0)).mulList [] d' d' h) = 𝟙 _ :=
        eqToHom_refl _ _
      rw [h1, h2]
      simp
  | cons i t ih =>
      intro d' e h hd' x
      have h' : d' + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
      have hstep := cechHgrZeroBaseChangeEquiv_mulX (M := M) (d := d') A i hM hflat
        (hv d' hd') (hv (d' + 1) (by omega)) x
      change cechHgrZeroBaseChangeEquiv (d := e) hM hflat (hv e (by omega)) A
          ((LinearMap.baseChange A
            ((((M.cechHgr 0).mulList t (d' + 1) e h').hom).comp
              (((M.cechHgr 0).mulX i d').hom))) x)
        = ((((M.baseChange A).cechHgr 0).mulList t (d' + 1) e h').hom)
            (((((M.baseChange A).cechHgr 0).mulX i d').hom)
              (cechHgrZeroBaseChangeEquiv (d := d') hM hflat (hv d' hd') A x))
      rw [LinearMap.baseChange_comp, LinearMap.comp_apply,
        ih (d' + 1) e h' (by omega), hstep]

/-- The cochain-flat form of
`GradedModule.cechHgrZeroBaseChangeEquiv_mulList`. -/
lemma cechHgrZeroBaseChangeEquiv'_mulList (hM : IsFG M)
    (hflat : ∀ (e : ℤ), d ≤ e → ∀ p : ℕ, Module.Flat R ((M.cechComplex e).X p))
    (hv : ∀ (e : ℤ), d ≤ e → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e)) :
    ∀ (l : List (Fin (n + 1))) (d' e : ℤ) (h : d' + (l.length : ℤ) = e) (hd' : d ≤ d')
      (x : A ⊗[R] ((M.cechHgr 0).obj d')),
      cechHgrZeroBaseChangeEquiv' (d := e) hM (hflat e (by omega)) (hv e (by omega)) A
          ((LinearMap.baseChange A (((M.cechHgr 0).mulList l d' e h).hom)) x)
        = ((((M.baseChange A).cechHgr 0).mulList l d' e h).hom)
            (cechHgrZeroBaseChangeEquiv' (d := d') hM (hflat d' hd') (hv d' hd') A x) := by
  intro l
  induction l with
  | nil =>
      intro d' e h hd' x
      have he : d' = e := by simpa using h
      subst he
      have h1 : ((M.cechHgr 0).mulList [] d' d' h) = 𝟙 _ := eqToHom_refl _ _
      have h2 : ((((M.baseChange A).cechHgr 0)).mulList [] d' d' h) = 𝟙 _ :=
        eqToHom_refl _ _
      rw [h1, h2]
      simp
  | cons i t ih =>
      intro d' e h hd' x
      have h' : d' + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
      have hstep := cechHgrZeroBaseChangeEquiv'_mulX (M := M) (d := d') A i hM
        (hflat d' hd') (hflat (d' + 1) (by omega))
        (hv d' hd') (hv (d' + 1) (by omega)) x
      change cechHgrZeroBaseChangeEquiv' (d := e) hM (hflat e (by omega))
          (hv e (by omega)) A
          ((LinearMap.baseChange A
            ((((M.cechHgr 0).mulList t (d' + 1) e h').hom).comp
              (((M.cechHgr 0).mulX i d').hom))) x)
        = ((((M.baseChange A).cechHgr 0).mulList t (d' + 1) e h').hom)
            (((((M.baseChange A).cechHgr 0).mulX i d').hom)
              (cechHgrZeroBaseChangeEquiv' (d := d') hM (hflat d' hd') (hv d' hd') A x))
      rw [LinearMap.baseChange_comp, LinearMap.comp_apply,
        ih (d' + 1) e h' (by omega), hstep]

variable {M d}

variable (M d)

/-- Transfer of the multiplication span across the base-change comparison. -/
lemma mulSpan_baseChange_cechHgr_zero (hM : IsFG M) (hflat : IsFlat M)
    (hv : ∀ (e : ℤ), d ≤ e → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e))
    (e : ℤ) (hde : d ≤ e)
    (h : (((M.baseChange A).cechHgr 0)).mulSpan d e = ⊤) :
    (((M.cechHgr 0)).baseChange A).mulSpan d e = ⊤ := by
  classical
  set Ψd := cechHgrZeroBaseChangeEquiv (d := d) hM hflat (hv d le_rfl) A with hΨd
  set Ψe := cechHgrZeroBaseChangeEquiv (d := e) hM hflat (hv e hde) A with hΨe
  refine eq_top_iff.mpr fun y _ => ?_
  have hy : Ψe y ∈ (((M.baseChange A).cechHgr 0)).mulSpan d e := h ▸ Submodule.mem_top
  have hmain : Ψe.symm (Ψe y) ∈ (((M.cechHgr 0)).baseChange A).mulSpan d e := by
    refine Submodule.iSup_induction
      (fun l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e} =>
        LinearMap.range ((((M.baseChange A).cechHgr 0).mulList l.1 d e l.2).hom))
      (motive := fun w => Ψe.symm w ∈ (((M.cechHgr 0)).baseChange A).mulSpan d e)
      hy ?_ ?_ ?_
    · rintro l _ ⟨z, rfl⟩
      have hkey := cechHgrZeroBaseChangeEquiv_mulList M A (d := d) hM hflat hv l.1 d e l.2
        le_rfl (Ψd.symm z)
      rw [LinearEquiv.apply_symm_apply] at hkey
      rw [← hkey, LinearEquiv.symm_apply_apply]
      refine le_mulSpan ((M.cechHgr 0).baseChange A) d e l.1 l.2 ?_
      rw [baseChange_mulList A (M.cechHgr 0) l.1 d e l.2]
      exact ⟨Ψd.symm z, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro w₁ w₂ hw₁ hw₂
      rw [map_add]
      exact Submodule.add_mem _ hw₁ hw₂
  rwa [LinearEquiv.symm_apply_apply] at hmain

/-- Transfer of the multiplication span across the cochain-flat base-change comparison. -/
lemma mulSpan_baseChange_cechHgr_zero' (hM : IsFG M)
    (hflat : ∀ (e : ℤ), d ≤ e → ∀ p : ℕ, Module.Flat R ((M.cechComplex e).X p))
    (hv : ∀ (e : ℤ), d ≤ e → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e))
    (e : ℤ) (hde : d ≤ e)
    (h : (((M.baseChange A).cechHgr 0)).mulSpan d e = ⊤) :
    (((M.cechHgr 0)).baseChange A).mulSpan d e = ⊤ := by
  classical
  set Ψd := cechHgrZeroBaseChangeEquiv' (d := d) hM (hflat d le_rfl) (hv d le_rfl) A
    with hΨd
  set Ψe := cechHgrZeroBaseChangeEquiv' (d := e) hM (hflat e hde) (hv e hde) A
    with hΨe
  refine eq_top_iff.mpr fun y _ => ?_
  have hy : Ψe y ∈ (((M.baseChange A).cechHgr 0)).mulSpan d e := h ▸ Submodule.mem_top
  have hmain : Ψe.symm (Ψe y) ∈ (((M.cechHgr 0)).baseChange A).mulSpan d e := by
    refine Submodule.iSup_induction
      (fun l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e} =>
        LinearMap.range ((((M.baseChange A).cechHgr 0).mulList l.1 d e l.2).hom))
      (motive := fun w => Ψe.symm w ∈ (((M.cechHgr 0)).baseChange A).mulSpan d e)
      hy ?_ ?_ ?_
    · rintro l _ ⟨z, rfl⟩
      have hkey := cechHgrZeroBaseChangeEquiv'_mulList M A (d := d) hM hflat hv
        l.1 d e l.2 le_rfl (Ψd.symm z)
      rw [LinearEquiv.apply_symm_apply] at hkey
      rw [← hkey, LinearEquiv.symm_apply_apply]
      refine le_mulSpan ((M.cechHgr 0).baseChange A) d e l.1 l.2 ?_
      rw [baseChange_mulList A (M.cechHgr 0) l.1 d e l.2]
      exact ⟨Ψd.symm z, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro w₁ w₂ hw₁ hw₂
      rw [map_add]
      exact Submodule.add_mem _ hw₁ hw₂
  rwa [LinearEquiv.symm_apply_apply] at hmain

variable {M d}

/-- Partial graded-model result toward Proposition 2.3.18(3), the Nakayama half: if the
higher cohomology vanishes on every field fibre in every twist `≥ d`, and the
fibrewise multiplication maps `H⁰(M_κ(d)) ⊗ S_{e-d} → H⁰(M_κ(e))` are surjective for every
`e ≥ d`, then the same holds over the base — `M(d)` is globally generated relative to `S`. -/
theorem isGloballyGenerated_of_fibres_cech {M : GradedModule R n} {d : ℤ}
    (hM : IsFG M) (hflat : IsFlat M)
    (hvan : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e →
      (((M.baseChange κ).cechHgr 0)).mulSpan d e = ⊤) :
    ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e → (M.cechHgr 0).mulSpan d e = ⊤ := by
  refine ⟨d, fun e hde => ?_⟩
  haveI : Module.Finite R ((M.cechHgr 0).obj e) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 e
  refine mulSpan_eq_top_of_forall_quotient_maximal (M.cechHgr 0) d e (fun m hm => ?_)
  letI : Field (R ⧸ m) := @Ideal.Quotient.field _ _ m hm
  have hv : ∀ (e' : ℤ), d ≤ e' → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e') :=
    fun e' he' κ _ _ i hi => hvan κ e' he' i hi
  have hgen : (((M.baseChange (R ⧸ m)).cechHgr 0)).mulSpan d e = ⊤ := hfib (R ⧸ m) e hde
  exact mulSpan_baseChange_cechHgr_zero (M := M) (A := R ⧸ m) (d := d) hM hflat hv e hde hgen

/-- The cochain-flat form of `GradedModule.isGloballyGenerated_of_fibres_cech`.
Only the flatness of the Čech terms in twists `≥ d` is needed. -/
theorem isGloballyGenerated_of_fibres_cech' {M : GradedModule R n} {d : ℤ}
    (hM : IsFG M)
    (hflat : ∀ (e : ℤ), d ≤ e → ∀ p : ℕ, Module.Flat R ((M.cechComplex e).X p))
    (hvan : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e →
      (((M.baseChange κ).cechHgr 0)).mulSpan d e = ⊤) :
    ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e → (M.cechHgr 0).mulSpan d e = ⊤ := by
  refine ⟨d, fun e hde => ?_⟩
  haveI : Module.Finite R ((M.cechHgr 0).obj e) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 e
  refine mulSpan_eq_top_of_forall_quotient_maximal (M.cechHgr 0) d e (fun m hm => ?_)
  letI : Field (R ⧸ m) := @Ideal.Quotient.field _ _ m hm
  have hv : ∀ (e' : ℤ), d ≤ e' → ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e') :=
    fun e' he' κ _ _ i hi => hvan κ e' he' i hi
  have hgen : (((M.baseChange (R ⧸ m)).cechHgr 0)).mulSpan d e = ⊤ :=
    hfib (R ⧸ m) e hde
  exact mulSpan_baseChange_cechHgr_zero' (M := M) (A := R ⧸ m) (d := d)
    hM hflat hv e hde hgen

/-- Direct, fixed-start form of
`GradedModule.isGloballyGenerated_of_fibres_cech'`. -/
theorem mulSpan_eq_top_of_fibres_cech' {M : GradedModule R n} {d : ℤ}
    (hM : IsFG M)
    (hflat : ∀ (e : ℤ), d ≤ e → ∀ p : ℕ, Module.Flat R ((M.cechComplex e).X p))
    (hvan : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj e))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e →
      (((M.baseChange κ).cechHgr 0)).mulSpan d e = ⊤) :
    ∀ e : ℤ, d ≤ e → (M.cechHgr 0).mulSpan d e = ⊤ := by
  intro e hde
  haveI : Module.Finite R ((M.cechHgr 0).obj e) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 e
  refine mulSpan_eq_top_of_forall_quotient_maximal (M.cechHgr 0) d e (fun m hm => ?_)
  letI : Field (R ⧸ m) := @Ideal.Quotient.field _ _ m hm
  have hv : ∀ (e' : ℤ), d ≤ e' →
      ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
        Subsingleton (((M.baseChange κ).cechHgr i).obj e') :=
    fun e' he' κ _ _ i hi ↦ hvan κ e' he' i hi
  exact mulSpan_baseChange_cechHgr_zero' (M := M) (A := R ⧸ m) (d := d)
    hM hflat hv e hde (hfib (R ⧸ m) e hde)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
