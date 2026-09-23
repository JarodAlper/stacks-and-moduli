module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»
public import StacksAndModuli.API.BaseChangePi
public import StacksAndModuli.API.FreeBasicOpen
public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.API.SpecSections
public import StacksAndModuli.API.SemilinearTransport
public import StacksAndModuli.API.KernelBaseChange
public import StacksAndModuli.API.FlatLocal
public import StacksAndModuli.API.PresheafSubmoduleRange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Flat.Localization
public import StacksAndModuli.«Section2.1-Intro».«part2.1.1a-affine-quotient-descent»
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Grassmannian

/-!
# The Grassmannian functor and the statement of its projectivity

This module formalizes the Grassmannian functor of Theorem 2.1.1
(`thm:grassmannian-projective-relative`) of §2.1 (The Grassmannian, Hilbert, and Quot
functors) of Chapter 2 of *Stacks and Moduli*
(the section heading carries no `sec:` label).

Two models are provided:

- the **absolute** Grassmannian `Gr(q, n)` as a `Type u`-valued presheaf
  `AlgebraicGeometry.Scheme.grassmannianFunctor q n : Scheme.{u}ᵒᵖ ⥤ Type u`, whose points
  over `T` are quasi-coherent submodule sheaves `K ⊆ O_T^{⊕n}` with rank-`q` locally free
  quotient (the kernel encoding of `rem:quot-remarks`(2), mirroring Mathlib's
  `Module.Grassmannian`);
- the **relative** Grassmannian `Gr(q, V)` of an arbitrary sheaf of modules `V` on a base
  scheme `S`, as the presheaf
  `AlgebraicGeometry.Scheme.grassmannianOverFunctor q V : (Over S)ᵒᵖ ⥤ Type (u + 1)`
  of isomorphism classes of rank-`q` locally free quotients of the pullback of `V`. Here the
  points are (necessarily) isomorphism classes of quotients, and functoriality uses the
  pullback pseudofunctor (`Modules.pullbackComp`/`pullbackCongr`); the isomorphism classes
  absorb the pseudofunctor coherence.

Main book-facing declaration:
- `Module.ProjectiveQuotientData.quotientEquivGrassmannian`: affine finite-projective
  quotients up to compatible isomorphism are equivalent to the kernel model.

The vector-bundle predicates, quotient data, Grassmannian functors, and projectivity
notion developed below are supporting definitions for Theorem 2.1.1; its final combined
declaration occurs after the representability and Plücker constructions in §2.2.
-/

@[expose] public section

section ThmGrassmannianProjectiveRelative

open CategoryTheory Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace Module

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- A finite projective quotient of an `R`-module `M`, of constant rank `q`.

This is the affine algebraic model underlying the quotient description of the
Grassmannian. Unlike `Module.Grassmannian`, which remembers the kernel, this structure
remembers the quotient module and its surjection. -/
structure ProjectiveQuotientData (q : ℕ) where
  /-- The quotient module. -/
  Q : Type u
  /-- The additive structure on the quotient. -/
  [addCommGroup : AddCommGroup Q]
  /-- The scalar action on the quotient. -/
  [module : Module R Q]
  /-- The quotient is finite. -/
  [finite : Module.Finite R Q]
  /-- The quotient is projective. -/
  [projective : Module.Projective R Q]
  /-- The quotient map. -/
  π : M →ₗ[R] Q
  /-- The quotient map is surjective. -/
  surjective : Function.Surjective π
  /-- The quotient has constant rank `q`. -/
  rankAtStalk_eq : ∀ p : PrimeSpectrum R, Module.rankAtStalk Q p = q

attribute [instance] ProjectiveQuotientData.addCommGroup ProjectiveQuotientData.module
  ProjectiveQuotientData.finite ProjectiveQuotientData.projective

namespace ProjectiveQuotientData

variable {R M} {q : ℕ}

/-- Two quotient presentations are equivalent when their targets are linearly
isomorphic compatibly with the quotient maps. -/
protected def setoid : Setoid (ProjectiveQuotientData R M q) where
  r x y := ∃ e : x.Q ≃ₗ[R] y.Q, e.toLinearMap.comp x.π = y.π
  iseqv := by
    refine ⟨fun x ↦ ⟨LinearEquiv.refl R x.Q, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      ext m
      change e.symm (e (x.π m)) = x.π m
      simp
    · rintro x y z ⟨e, he⟩ ⟨e', he'⟩
      refine ⟨e.trans e', ?_⟩
      ext m
      change e' (e (x.π m)) = z.π m
      rw [show e (x.π m) = y.π m from DFunLike.congr_fun he m,
        show e' (y.π m) = z.π m from DFunLike.congr_fun he' m]

/-- The kernel of a finite projective quotient is a point of the kernel-model
Grassmannian. -/
noncomputable def toGrassmannian (x : ProjectiveQuotientData R M q) :
    Module.Grassmannian R M q := by
  let e : (M ⧸ LinearMap.ker x.π) ≃ₗ[R] x.Q :=
    x.π.quotKerEquivOfSurjective x.surjective
  exact
    { toSubmodule := LinearMap.ker x.π
      finite_quotient := Module.Finite.equiv e.symm
      projective_quotient := Module.Projective.of_equiv e.symm
      rankAtStalk_eq := fun p ↦
        (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (x.rankAtStalk_eq p) }

/-- Equivalent quotient presentations determine the same kernel-model Grassmannian
point. -/
lemma toGrassmannian_eq {x y : ProjectiveQuotientData R M q}
    (h : ProjectiveQuotientData.setoid.r x y) :
    x.toGrassmannian = y.toGrassmannian := by
  obtain ⟨e, he⟩ := h
  apply Module.Grassmannian.ext
  ext m
  change x.π m = 0 ↔ y.π m = 0
  rw [← show e (x.π m) = y.π m from DFunLike.congr_fun he m]
  exact e.map_eq_zero_iff.symm

/-- A kernel-model Grassmannian point gives its canonical quotient presentation. -/
def ofGrassmannian (N : Module.Grassmannian R M q) :
    ProjectiveQuotientData R M q where
  Q := M ⧸ N.toSubmodule
  π := N.toSubmodule.mkQ
  surjective := Submodule.mkQ_surjective _
  rankAtStalk_eq := N.rankAtStalk_eq

section RemQuotRemarks

/-- **Remark 2.1.5** (`rem:quot-remarks`) (part (2), affine case): the affine quotient
model and Mathlib's kernel model of the Grassmannian are canonically equivalent — finite
projective constant-rank quotients of `M` up to compatible isomorphism correspond to
their kernels. -/
noncomputable def quotientEquivGrassmannian :
    Quotient (ProjectiveQuotientData.setoid (R := R) (M := M) (q := q)) ≃
      Module.Grassmannian R M q := by
  refine Equiv.ofBijective
    (Quotient.lift toGrassmannian fun _ _ h ↦ toGrassmannian_eq h) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    obtain ⟨y, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    let ex : (M ⧸ LinearMap.ker x.π) ≃ₗ[R] x.Q :=
      x.π.quotKerEquivOfSurjective x.surjective
    let ey : (M ⧸ LinearMap.ker y.π) ≃ₗ[R] y.Q :=
      y.π.quotKerEquivOfSurjective y.surjective
    have hker : LinearMap.ker x.π = LinearMap.ker y.π := by
      simpa [toGrassmannian] using congrArg Module.Grassmannian.toSubmodule hxy
    let ek : (M ⧸ LinearMap.ker x.π) ≃ₗ[R]
        (M ⧸ LinearMap.ker y.π) :=
      Submodule.quotEquivOfEq _ _ hker
    refine ⟨ex.symm.trans (ek.trans ey), ?_⟩
    ext m
    change ey (ek (ex.symm (x.π m))) = y.π m
    rw [show ex.symm (x.π m) = Submodule.Quotient.mk m from
      LinearMap.quotKerEquivOfSurjective_symm_apply x.π x.surjective m,
      Submodule.quotEquivOfEq_mk,
      show ey (Submodule.Quotient.mk m) = y.π m from
        LinearMap.quotKerEquivOfSurjective_apply_mk y.π y.surjective m]
  · intro N
    refine ⟨Quotient.mk _ (ofGrassmannian N), ?_⟩
    apply Module.Grassmannian.ext
    exact N.toSubmodule.ker_mkQ

@[simp]
lemma quotientEquivGrassmannian_mk (x : ProjectiveQuotientData R M q) :
    quotientEquivGrassmannian (Quotient.mk _ x) = x.toGrassmannian := rfl

@[simp]
lemma quotientEquivGrassmannian_symm_apply (N : Module.Grassmannian R M q) :
    quotientEquivGrassmannian.symm N = Quotient.mk _ (ofGrassmannian N) := by
  apply quotientEquivGrassmannian.injective
  rw [Equiv.apply_symm_apply]
  apply Module.Grassmannian.ext
  symm
  exact N.toSubmodule.ker_mkQ

end RemQuotRemarks

end ProjectiveQuotientData

end Module

namespace AlgebraicGeometry.Scheme

variable {S X Y : Scheme.{u}}

namespace Modules

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The affine open of `X` obtained by transporting a principal open in the spectrum
attached to an affine open `U`. -/
noncomputable def affinePrincipalRefinement (U : X.affineOpens) (f : Γ(X, U.1)) :
    X.affineOpens :=
  ⟨U.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen f,
    (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.2.fromSpec).mpr
      (IsAffineOpen.Spec_basicOpen f)⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma affinePrincipalRefinement_le (U : X.affineOpens) (f : Γ(X, U.1)) :
    (affinePrincipalRefinement U f).1 ≤ U.1 := by
  calc
    U.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤
        U.2.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U.1)).Opens) :=
      Set.image_mono le_top
    _ = U.1 := by
      rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The transported principal refinement is canonically the principal-open subscheme
of the spectrum attached to `U`. -/
noncomputable def affinePrincipalRefinementIsoBasicOpen
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    (affinePrincipalRefinement U f).1.toScheme ≅
      Scheme.Opens.toScheme (X := Spec (.of Γ(X, U.1)))
        (PrimeSpectrum.basicOpen f) :=
  IsOpenImmersion.isoOfRangeEq
    (affinePrincipalRefinement U f).1.ι
    (Scheme.Opens.ι (X := Spec (.of Γ(X, U.1)))
      (PrimeSpectrum.basicOpen f) ≫ U.2.fromSpec) (by
      rw [Scheme.Opens.range_ι]
      change U.2.fromSpec.base '' (PrimeSpectrum.basicOpen f :
          Set (PrimeSpectrum Γ(X, U.1))) =
        Set.range (Scheme.Opens.ι (X := Spec (.of Γ(X, U.1)))
          (PrimeSpectrum.basicOpen f) ≫ U.2.fromSpec).base
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl)

/-- The transported principal refinement is the spectrum of the away localization. -/
noncomputable def affinePrincipalRefinementIsoSpecAway
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    (affinePrincipalRefinement U f).1.toScheme ≅
      Spec (.of <| Localization.Away f) :=
  affinePrincipalRefinementIsoBasicOpen U f ≪≫ basicOpenIsoSpecAway f

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
@[reassoc]
lemma affinePrincipalRefinementIsoSpecAway_hom_fac
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    (affinePrincipalRefinementIsoSpecAway U f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
          (Localization.Away f))) ≫ U.2.fromSpec =
      (affinePrincipalRefinement U f).1.ι := by
  simp only [affinePrincipalRefinementIsoSpecAway, Iso.trans_hom,
    Category.assoc, basicOpenIsoSpecAway_hom_SpecMap_assoc]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma mem_affinePrincipalRefinement_of_mem_basicOpen (U : X.affineOpens)
    (f : Γ(X, U.1)) {x : X} (hxU : x ∈ U.1)
    (hxf : U.2.isoSpec.hom.base ⟨x, hxU⟩ ∈ PrimeSpectrum.basicOpen f) :
    x ∈ (affinePrincipalRefinement U f).1 := by
  refine ⟨U.2.isoSpec.hom.base ⟨x, hxU⟩, hxf, ?_⟩
  change (U.2.isoSpec.hom ≫ U.2.fromSpec).base ⟨x, hxU⟩ = x
  rw [U.2.isoSpec_hom_fromSpec]
  rfl

/-- Let `M` be a sheaf of modules on a scheme `X`. We say `M` is finite locally free (a
vector bundle of possibly non-constant rank) if every point has an affine open neighborhood
`U` such that the module of sections `Γ(M, U)` is finite and projective over `Γ(X, U)`.

For quasi-coherent `M` this is the usual notion of a vector bundle; the predicate does not
impose quasi-coherence, which should be assumed separately where needed. -/
def IsFiniteLocallyFree (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    Module.Finite Γ(X, U.1) Γ(M, U.1) ∧ Module.Projective Γ(X, U.1) Γ(M, U.1)

/-- Let `M` be a sheaf of modules on a scheme `X` and `q` a natural number. We say `M` is
finite locally free of rank `q` (a vector bundle of rank `q`) if every point has an affine
open neighborhood `U` such that the module of sections `Γ(M, U)` is finite projective over
`Γ(X, U)` of rank `q` at every prime. -/
def IsProjectiveOfRank (q : ℕ) (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    Module.Finite Γ(X, U.1) Γ(M, U.1) ∧ Module.Projective Γ(X, U.1) Γ(M, U.1) ∧
    ∀ p : PrimeSpectrum Γ(X, U.1), Module.rankAtStalk Γ(M, U.1) p = q

/-- Finite local freeness of fixed rank can be checked after pullback to every
affine open subscheme. -/
lemma IsProjectiveOfRank.of_affineOpen_pullbacks {q : ℕ} {M : X.Modules}
    (h : ∀ U : X.affineOpens,
      IsProjectiveOfRank q ((Modules.pullback U.1.ι).obj M)) :
    IsProjectiveOfRank q M := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  let A : X.affineOpens := ⟨U, hU⟩
  obtain ⟨V, hxV, hfin, hproj, hrank⟩ := h A ⟨x, hxU⟩
  let W : X.affineOpens :=
    ⟨A.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion A.1.ι⟩
  refine ⟨W, ?_, ?_⟩
  · exact ⟨⟨x, hxU⟩, hxV, rfl⟩
  · exact Modules.sections_finite_projective_rank_of_pullback_openImmersion
      A.1.ι M V.1 hfin hproj hrank

/-- The module on the coordinate spectrum obtained by first restricting to an affine
open and then transporting across its canonical spectrum isomorphism. -/
noncomputable def affineCoordinateSheaf (M : X.Modules) (U : X.affineOpens) :
    (Spec (.of Γ(X, U.1))).Modules :=
  (Modules.pullback U.2.isoSpec.inv).obj ((Modules.pullback U.1.ι).obj M)

/-- The coordinate module of a sheaf on an affine open.  This convention is tailored
to `tilde` and affine base change. -/
noncomputable def affineCoordinateModule (M : X.Modules) (U : X.affineOpens) :
    ModuleCat Γ(X, U.1) := moduleSpecΓFunctor.obj (affineCoordinateSheaf M U)

instance affineCoordinateSheaf_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) : (affineCoordinateSheaf M U).IsQuasicoherent := by
  dsimp [affineCoordinateSheaf]
  infer_instance

/-- Finite projectivity and constant rank pass from sections on an affine open to its
coordinate module. -/
lemma affineCoordinateModule_finite_projective_rank {q : ℕ} (M : X.Modules)
    (U : X.affineOpens)
    (hfin : Module.Finite Γ(X, U.1) Γ(M, U.1))
    (hproj : Module.Projective Γ(X, U.1) Γ(M, U.1))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U.1),
      Module.rankAtStalk Γ(M, U.1) p = q) :
    Module.Finite Γ(X, U.1) (affineCoordinateModule M U) ∧
      Module.Projective Γ(X, U.1) (affineCoordinateModule M U) ∧
      ∀ p : PrimeSpectrum Γ(X, U.1),
        Module.rankAtStalk (affineCoordinateModule M U) p = q := by
  let MU := (Modules.pullback U.1.ι).obj M
  have himU : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hMU := pullback_openImmersion_sections_finite_projective_rank
    U.1.ι M ⊤ (q := q) (by rw [himU]; exact hfin)
      (by rw [himU]; exact hproj) (by rw [himU]; exact hrank)
  have himSpec : U.2.isoSpec.inv ''ᵁ
      (⊤ : (Spec (.of Γ(X, U.1))).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hMspec := pullback_openImmersion_sections_finite_projective_rank
    U.2.isoSpec.inv MU ⊤ (q := q) (by rw [himSpec]; exact hMU.1)
      (by rw [himSpec]; exact hMU.2.1) (by rw [himSpec]; exact hMU.2.2)
  exact moduleSpecΓFunctor_finite_projective_rank_of_top
    (affineCoordinateSheaf M U) hMspec.1 hMspec.2.1 hMspec.2.2

/-- On an affine scheme, a finite-projective constant-rank statement for global
sections supplies the defining affine neighborhood at every point. -/
lemma isProjectiveOfRank_of_top [IsAffine X] {q : ℕ} {M : X.Modules}
    (hfin : Module.Finite Γ(X, ⊤) Γ(M, ⊤))
    (hproj : Module.Projective Γ(X, ⊤) Γ(M, ⊤))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤), Module.rankAtStalk Γ(M, ⊤) p = q) :
    IsProjectiveOfRank q M := by
  intro x
  exact ⟨⟨⊤, isAffineOpen_top X⟩, trivial, hfin, hproj, hrank⟩

/-- A sheaf of modules which is finite locally free of some rank is finite locally free. -/
lemma IsProjectiveOfRank.isFiniteLocallyFree {q : ℕ} {M : X.Modules}
    (h : IsProjectiveOfRank q M) : IsFiniteLocallyFree M := by
  intro x
  obtain ⟨U, hx, hfin, hproj, -⟩ := h x
  exact ⟨U, hx, hfin, hproj⟩

/-- Around every point, a fixed-rank vector bundle admits an affine neighborhood and a
principal-open refinement on which its module of sections is free of the prescribed
rank. This is the algebraic refinement datum used to build relative Grassmannian
charts. -/
lemma IsProjectiveOfRank.exists_basicOpen_free {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (f : Γ(X, U.1)),
      U.2.isoSpec.hom.base ⟨x, by assumption⟩ ∈ PrimeSpectrum.basicOpen f ∧
      x ∈ (affinePrincipalRefinement U f).1 ∧
      Module.Finite (Localization.Away f)
        (LocalizedModule.Away f Γ(M, U.1)) ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away f Γ(M, U.1)) ∧
      Module.finrank (Localization.Away f)
        (LocalizedModule.Away f Γ(M, U.1)) = q := by
  obtain ⟨U, hx, hfin, hproj, hrank⟩ := hM x
  letI : Module.Finite Γ(X, U.1) Γ(M, U.1) := hfin
  letI : Module.Projective Γ(X, U.1) Γ(M, U.1) := hproj
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom.base ⟨x, hx⟩
  obtain ⟨f, hpf, hfree, hfrank⟩ :=
    Module.exists_basicOpen_free_of_finite_projective
      Γ(X, U.1) Γ(M, U.1) p
  exact ⟨U, hx, f, hpf,
    mem_affinePrincipalRefinement_of_mem_basicOpen U f hx hpf,
    inferInstance, hfree, hfrank.trans (hrank p)⟩

/-- A principal affine neighborhood on which the coordinate module used by `tilde`
is free.  Unlike `exists_basicOpen_free`, this formulation needs no later comparison
between intrinsic affine-open sections and `moduleSpecΓFunctor`. -/
lemma IsProjectiveOfRank.exists_coordinateBasicOpen_free {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (f : Γ(X, U.1)),
      U.2.isoSpec.hom.base ⟨x, by assumption⟩ ∈ PrimeSpectrum.basicOpen f ∧
      x ∈ (affinePrincipalRefinement U f).1 ∧
      Module.Finite (Localization.Away f)
        (LocalizedModule.Away f (affineCoordinateModule M U)) ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away f (affineCoordinateModule M U)) ∧
      Module.finrank (Localization.Away f)
        (LocalizedModule.Away f (affineCoordinateModule M U)) = q := by
  obtain ⟨U, hx, hfin, hproj, hrank⟩ := hM x
  obtain ⟨hfin', hproj', hrank'⟩ :=
    affineCoordinateModule_finite_projective_rank M U hfin hproj hrank
  letI : Module.Finite Γ(X, U.1) (affineCoordinateModule M U) := hfin'
  letI : Module.Projective Γ(X, U.1) (affineCoordinateModule M U) := hproj'
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom.base ⟨x, hx⟩
  obtain ⟨f, hpf, hfree, hfrank⟩ :=
    Module.exists_basicOpen_free_of_finite_projective
      Γ(X, U.1) (affineCoordinateModule M U) p
  exact ⟨U, hx, f, hpf,
    mem_affinePrincipalRefinement_of_mem_basicOpen U f hx hpf,
    inferInstance, hfree, hfrank.trans (hrank' p)⟩

/-- The chosen affine chart for the coordinate-module trivialization at `x`. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenAmbient {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) : X.affineOpens :=
  (hM.exists_coordinateBasicOpen_free x).choose

/-- The chosen principal element for the coordinate-module trivialization at `x`. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenElement {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Γ(X, (hM.coordinateBasicOpenAmbient x).1) :=
  (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose

/-- The chosen coordinate principal open. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenAffine {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) : X.affineOpens :=
  affinePrincipalRefinement (hM.coordinateBasicOpenAmbient x)
    (hM.coordinateBasicOpenElement x)

lemma IsProjectiveOfRank.mem_coordinateBasicOpenAffine {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    x ∈ (hM.coordinateBasicOpenAffine x).1 :=
  (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose_spec.2.1

lemma IsProjectiveOfRank.coordinateBasicOpen_free {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Free (Localization.Away (hM.coordinateBasicOpenElement x))
      (LocalizedModule.Away (hM.coordinateBasicOpenElement x)
        (affineCoordinateModule M (hM.coordinateBasicOpenAmbient x))) :=
  (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.2.1

lemma IsProjectiveOfRank.coordinateBasicOpen_finite {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Finite (Localization.Away (hM.coordinateBasicOpenElement x))
      (LocalizedModule.Away (hM.coordinateBasicOpenElement x)
        (affineCoordinateModule M (hM.coordinateBasicOpenAmbient x))) :=
  (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.1

lemma IsProjectiveOfRank.coordinateBasicOpen_rank {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.finrank (Localization.Away (hM.coordinateBasicOpenElement x))
      (LocalizedModule.Away (hM.coordinateBasicOpenElement x)
        (affineCoordinateModule M (hM.coordinateBasicOpenAmbient x))) = q :=
  (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.2.2

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- An explicit basis of the localized coordinate module. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenBasis {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Basis (Fin q) (Localization.Away (hM.coordinateBasicOpenElement x))
      (LocalizedModule.Away (hM.coordinateBasicOpenElement x)
        (affineCoordinateModule M (hM.coordinateBasicOpenAmbient x))) := by
  let p := (hM.coordinateBasicOpenAmbient x).2.isoSpec.hom.base
    ⟨x, (hM.exists_coordinateBasicOpen_free x).choose_spec.choose⟩
  have hf : hM.coordinateBasicOpenElement x ∉ p.asIdeal :=
    (hM.exists_coordinateBasicOpen_free x).choose_spec.choose_spec.choose_spec.1
  letI : Nontrivial (Localization.Away (hM.coordinateBasicOpenElement x)) :=
    IsLocalization.Away.nontrivial_of_notMem hf _
  letI := hM.coordinateBasicOpen_free x
  letI := hM.coordinateBasicOpen_finite x
  exact Module.finBasisOfFinrankEq _ _ (hM.coordinateBasicOpen_rank x)

/-- The localized coordinate module is explicitly free of rank `q`. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenEquiv {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    LocalizedModule.Away (hM.coordinateBasicOpenElement x)
        (affineCoordinateModule M (hM.coordinateBasicOpenAmbient x)) ≃ₗ[
      Localization.Away (hM.coordinateBasicOpenElement x)]
        (Fin q → Localization.Away (hM.coordinateBasicOpenElement x)) :=
  (hM.coordinateBasicOpenBasis x).equivFun

/-- On the spectrum of the chosen localization, the pullback of the coordinate sheaf
is the trivial rank-`q` sheaf. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenSpecTildeIso {q : ℕ}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) (x : X) :
    (Modules.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (hM.coordinateBasicOpenAmbient x).1)
        (Localization.Away (hM.coordinateBasicOpenElement x)))))).obj
        (affineCoordinateSheaf M (hM.coordinateBasicOpenAmbient x)) ≅
      AlgebraicGeometry.tilde
        (R := CommRingCat.of (Localization.Away (hM.coordinateBasicOpenElement x)))
        (ModuleCat.of (Localization.Away (hM.coordinateBasicOpenElement x))
          (Fin q → Localization.Away (hM.coordinateBasicOpenElement x))) := by
  let A := Γ(X, (hM.coordinateBasicOpenAmbient x).1)
  let f : A := hM.coordinateBasicOpenElement x
  let N := affineCoordinateModule M (hM.coordinateBasicOpenAmbient x)
  let φ : CommRingCat.of A ⟶ CommRingCat.of (Localization.Away f) :=
    CommRingCat.ofHom (algebraMap A (Localization.Away f))
  let eLoc : (ModuleCat.extendScalars φ.hom).obj N ≅
      ModuleCat.of (Localization.Away f) (LocalizedModule.Away f N) := by
    dsimp [φ, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
    letI : IsScalarTower A (Localization.Away f)
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let eTensor :
        (TensorProduct A
          ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f))) N) ≃ₗ[
          Localization.Away f]
        (TensorProduct A (Localization.Away f) N) :=
      TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.Away f) (Localization.Away f))
        (LinearEquiv.refl A N)
    exact (eTensor.trans
      (LocalizedModule.equivTensorProduct (Submonoid.powers f) N).symm).toModuleIso
  let eFree : ModuleCat.of (Localization.Away f) (LocalizedModule.Away f N) ≅
      ModuleCat.of (Localization.Away f) (Fin q → Localization.Away f) :=
    (hM.coordinateBasicOpenEquiv x).toModuleIso
  exact pullbackQuasicoherentIso φ (affineCoordinateSheaf M
      (hM.coordinateBasicOpenAmbient x)) ≪≫
    (AlgebraicGeometry.tilde.functor (CommRingCat.of (Localization.Away f))).mapIso
      (eLoc ≪≫ eFree)

/-- The preceding trivialization expressed using the canonical free sheaf. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenSpecFreeIso {q : ℕ}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) (x : X) :
    (Modules.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (hM.coordinateBasicOpenAmbient x).1)
        (Localization.Away (hM.coordinateBasicOpenElement x)))))).obj
        (affineCoordinateSheaf M (hM.coordinateBasicOpenAmbient x)) ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of
        (Localization.Away (hM.coordinateBasicOpenElement x)))).ringCatSheaf)
        (ULift.{u} (Fin q)) :=
  hM.coordinateBasicOpenSpecTildeIso x ≪≫
    (AlgebraicGeometry.tilde.functor (CommRingCat.of
      (Localization.Away (hM.coordinateBasicOpenElement x)))).mapIso
        ((Finsupp.linearEquivFunOnFinite
            (Localization.Away (hM.coordinateBasicOpenElement x))
            (Localization.Away (hM.coordinateBasicOpenElement x)) (Fin q)).symm.trans
          (Finsupp.mapDomain.linearEquiv
            (Localization.Away (hM.coordinateBasicOpenElement x))
            (Localization.Away (hM.coordinateBasicOpenElement x))
            Equiv.ulift.symm)).toModuleIso ≪≫
    AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of
      (Localization.Away (hM.coordinateBasicOpenElement x))) (ULift.{u} (Fin q))

/-- The morphism from the chosen localization spectrum to the original base. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenSpecToBase {q : ℕ}
    {M : X.Modules} (hM : IsProjectiveOfRank q M) (x : X) :
    Spec (CommRingCat.of (Localization.Away (hM.coordinateBasicOpenElement x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, (hM.coordinateBasicOpenAmbient x).1)
      (Localization.Away (hM.coordinateBasicOpenElement x)))) ≫
    (hM.coordinateBasicOpenAmbient x).2.fromSpec

/-- The pullback of the original vector bundle to the chosen localization spectrum is
the canonical free sheaf of rank `q`. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenPullbackFreeIso {q : ℕ}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) (x : X) :
    (Modules.pullback (hM.coordinateBasicOpenSpecToBase x)).obj M ≅
      SheafOfModules.free (R := (Spec (CommRingCat.of
        (Localization.Away (hM.coordinateBasicOpenElement x)))).ringCatSheaf)
        (ULift.{u} (Fin q)) := by
  let U := hM.coordinateBasicOpenAmbient x
  let f := hM.coordinateBasicOpenElement x
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U.1) (Localization.Away f)))
  dsimp [coordinateBasicOpenSpecToBase, affineCoordinateSheaf, U, f, g]
  exact ((Modules.pullbackComp g U.2.fromSpec).app M).symm ≪≫
    (Modules.pullback g).mapIso
      ((Modules.pullbackComp U.2.isoSpec.inv U.1.ι).app M).symm ≪≫
    hM.coordinateBasicOpenSpecFreeIso x

/-- The pullback to the actual principal-open subscheme is a free sheaf. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenAffinePullbackFreeIso {q : ℕ}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) (x : X) :
    (Modules.pullback (hM.coordinateBasicOpenAffine x).1.ι).obj M ≅
      SheafOfModules.free
        (R := (hM.coordinateBasicOpenAffine x).1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin q)) := by
  let U := hM.coordinateBasicOpenAmbient x
  let f := hM.coordinateBasicOpenElement x
  let W := hM.coordinateBasicOpenAffine x
  let e := affinePrincipalRefinementIsoSpecAway U f
  let j := hM.coordinateBasicOpenSpecToBase x
  letI : IsOpenImmersion e.hom := inferInstance
  letI : (Opens.map e.hom.base).IsEquivalence := by
    change (Opens.map (asIso e.hom.base).hom).IsEquivalence
    rw [← Opens.mapMapIso_functor]
    infer_instance
  have hfac : e.hom ≫ j = W.1.ι := by
    exact affinePrincipalRefinementIsoSpecAway_hom_fac U f
  exact (Modules.pullbackCongr hfac.symm).app M ≪≫
    ((Modules.pullbackComp e.hom j).app M).symm ≪≫
    (Modules.pullback e.hom).mapIso (hM.coordinateBasicOpenPullbackFreeIso x) ≪≫
    SheafOfModules.pullbackObjFreeIso e.hom.toRingCatSheafHom (ULift.{u} (Fin q))

lemma IsProjectiveOfRank.iSup_coordinateBasicOpenAffine_eq_top {q : ℕ}
    {M : X.Modules} (hM : IsProjectiveOfRank q M) :
    ⨆ x : X, (hM.coordinateBasicOpenAffine x).1 = ⊤ := by
  apply top_unique
  intro x
  simp only [Opens.mem_iSup]
  intro _
  exact ⟨x, hM.mem_coordinateBasicOpenAffine x⟩

/-- The chosen coordinate principal opens, bundled as a Zariski open cover. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenCover {q : ℕ}
    {M : X.Modules} (hM : IsProjectiveOfRank q M) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun x : X ↦ (hM.coordinateBasicOpenAffine x).1) (by
    rw [TopologicalSpace.IsOpenCover]
    exact hM.iSup_coordinateBasicOpenAffine_eq_top)

/-- The chosen ambient affine neighborhood used for local trivialization at `x`. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeAmbient {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) : X.affineOpens :=
  (hM.exists_basicOpen_free x).choose

/-- The chosen principal element defining the local trivialization at `x`. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeElement {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Γ(X, (hM.basicOpenFreeAmbient x).1) :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose

lemma IsProjectiveOfRank.basicOpenFree_mem {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    (hM.basicOpenFreeAmbient x).2.isoSpec.hom.base
        ⟨x, (hM.exists_basicOpen_free x).choose_spec.choose⟩ ∈
      PrimeSpectrum.basicOpen (hM.basicOpenFreeElement x) :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose_spec.1

lemma IsProjectiveOfRank.basicOpenFree_free {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Free
      (Localization.Away (hM.basicOpenFreeElement x))
      (LocalizedModule.Away (hM.basicOpenFreeElement x)
        Γ(M, (hM.basicOpenFreeAmbient x).1)) :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.2.1

lemma IsProjectiveOfRank.basicOpenFree_finite {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Finite
      (Localization.Away (hM.basicOpenFreeElement x))
      (LocalizedModule.Away (hM.basicOpenFreeElement x)
        Γ(M, (hM.basicOpenFreeAmbient x).1)) :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.1

lemma IsProjectiveOfRank.basicOpenFree_rank {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.finrank
      (Localization.Away (hM.basicOpenFreeElement x))
      (LocalizedModule.Away (hM.basicOpenFreeElement x)
        Γ(M, (hM.basicOpenFreeAmbient x).1)) = q :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose_spec.2.2.2.2

/-- A chosen affine principal-open trivializing neighborhood at a point of a fixed-rank
vector bundle. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeAffine {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) : X.affineOpens :=
  affinePrincipalRefinement
    (hM.basicOpenFreeAmbient x) (hM.basicOpenFreeElement x)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A basis of the localized module on the chosen trivializing principal open. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeBasis {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    Module.Basis (Fin q)
      (Localization.Away (hM.basicOpenFreeElement x))
      (LocalizedModule.Away (hM.basicOpenFreeElement x)
        Γ(M, (hM.basicOpenFreeAmbient x).1)) := by
  let p := (hM.basicOpenFreeAmbient x).2.isoSpec.hom.base
    ⟨x, (hM.exists_basicOpen_free x).choose_spec.choose⟩
  have hf : hM.basicOpenFreeElement x ∉ p.asIdeal := hM.basicOpenFree_mem x
  letI : Nontrivial (Localization.Away (hM.basicOpenFreeElement x)) :=
    IsLocalization.Away.nontrivial_of_notMem hf _
  letI := hM.basicOpenFree_free x
  letI := hM.basicOpenFree_finite x
  exact Module.finBasisOfFinrankEq _ _ (hM.basicOpenFree_rank x)

/-- The explicit rank-`q` trivialization on the chosen principal neighborhood. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeEquiv {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    LocalizedModule.Away (hM.basicOpenFreeElement x)
        Γ(M, (hM.basicOpenFreeAmbient x).1) ≃ₗ[
      Localization.Away (hM.basicOpenFreeElement x)]
        (Fin q → Localization.Away (hM.basicOpenFreeElement x)) :=
  (hM.basicOpenFreeBasis x).equivFun

/-- The sheaf associated to the localized module is the trivial rank-`q` sheaf on the
corresponding affine spectrum. -/
noncomputable def IsProjectiveOfRank.basicOpenFreeTildeIso {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    AlgebraicGeometry.tilde
      (R := CommRingCat.of (Localization.Away (hM.basicOpenFreeElement x))) (ModuleCat.of
        (Localization.Away (hM.basicOpenFreeElement x))
        (LocalizedModule.Away (hM.basicOpenFreeElement x)
          Γ(M, (hM.basicOpenFreeAmbient x).1))) ≅
      AlgebraicGeometry.tilde
        (R := CommRingCat.of (Localization.Away (hM.basicOpenFreeElement x))) (ModuleCat.of
        (Localization.Away (hM.basicOpenFreeElement x))
        (Fin q → Localization.Away (hM.basicOpenFreeElement x))) :=
  (AlgebraicGeometry.tilde.functor
    (CommRingCat.of (Localization.Away (hM.basicOpenFreeElement x)))).mapIso
      (hM.basicOpenFreeEquiv x).toModuleIso

lemma IsProjectiveOfRank.mem_basicOpenFreeAffine {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) (x : X) :
    x ∈ (hM.basicOpenFreeAffine x).1 :=
  (hM.exists_basicOpen_free x).choose_spec.choose_spec.choose_spec.2.1

/-- The chosen principal-open trivializing neighborhoods cover the base scheme. -/
lemma IsProjectiveOfRank.iSup_basicOpenFreeAffine_eq_top {q : ℕ} {M : X.Modules}
    (hM : IsProjectiveOfRank q M) :
    ⨆ x : X, (hM.basicOpenFreeAffine x).1 = ⊤ := by
  apply top_unique
  intro x
  simp only [Opens.mem_iSup]
  intro _
  exact ⟨x, hM.mem_basicOpenFreeAffine x⟩

/-- Finite local freeness is invariant under isomorphism of sheaves of modules. -/
lemma IsFiniteLocallyFree.of_iso {M N : X.Modules} (e : M ≅ N)
    (hM : IsFiniteLocallyFree M) : IsFiniteLocallyFree N := by
  intro x
  obtain ⟨U, hx, hfin, hproj⟩ := hM x
  let eUCat : M.val.obj (op U.1) ≅ N.val.obj (op U.1) :=
    { hom := e.hom.val.app (op U.1)
      inv := e.inv.val.app (op U.1)
      hom_inv_id := congrArg (fun f ↦ f.val.app (op U.1)) e.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.val.app (op U.1)) e.inv_hom_id }
  let eU : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) := eUCat.toLinearEquiv
  exact ⟨U, hx, Module.Finite.equiv eU,
    Module.Projective.of_equiv eU⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A quasicoherent finite locally free sheaf is of finite presentation, and hence of
finite type. -/
lemma IsFiniteLocallyFree.isFinitePresentation {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) : M.IsFinitePresentation := by
  choose U hxU hfinU hprojU using hM
  let presData (x : X) :
      { P : SheafOfModules.Presentation (M.restrict (U x).1.ι) // P.IsFinite } := by
    let MU := (Modules.pullback (U x).1.ι).obj M
    have himU : (U x).1.ι ''ᵁ ⊤ = (U x).1 := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    have hMU := pullback_openImmersion_sections_finite_projective
      (U x).1.ι M ⊤ (by rw [himU]; exact hfinU x) (by rw [himU]; exact hprojU x)
    let Mspec := (Modules.pullback (U x).2.isoSpec.inv).obj MU
    have himSpec : (U x).2.isoSpec.inv ''ᵁ ⊤ = ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    have hMspec := pullback_openImmersion_sections_finite_projective
      (U x).2.isoSpec.inv MU ⊤ (by rw [himSpec]; exact hMU.1)
        (by rw [himSpec]; exact hMU.2)
    have hΓ := moduleSpecΓFunctor_finite_projective_of_top Mspec hMspec.1 hMspec.2
    letI : Module.Finite Γ(X, (U x).1) (moduleSpecΓFunctor.obj Mspec) := hΓ.1
    letI : Module.Projective Γ(X, (U x).1) (moduleSpecΓFunctor.obj Mspec) := hΓ.2
    letI : Module.FinitePresentation Γ(X, (U x).1)
        (moduleSpecΓFunctor.obj Mspec) :=
      Module.finitePresentation_of_projective _ _
    let P := (exists_finitePresentation_of_moduleSpecΓFunctor Mspec).choose
    let hP := (exists_finitePresentation_of_moduleSpecΓFunctor Mspec).choose_spec
    letI : P.IsFinite := hP
    let Pback := presentationPullback (U x).2.isoSpec.hom P
    let eBack : (Modules.pullback (U x).2.isoSpec.hom).obj Mspec ≅ MU :=
      (pullbackComp (U x).2.isoSpec.hom (U x).2.isoSpec.inv).app MU ≪≫
        (pullbackCongr (U x).2.isoSpec.hom_inv_id).app MU ≪≫
        (pullbackId _).app MU
    let PMU : MU.Presentation := Pback.ofIsIso eBack.hom
    let eRestrict := (Modules.restrictFunctorIsoPullback (U x).1.ι).app M
    exact ⟨PMU.ofIsIso eRestrict.inv, inferInstance⟩
  let pres (x : X) : SheafOfModules.Presentation (M.restrict (U x).1.ι) :=
    (presData x).1
  letI (x : X) : (pres x).IsFinite := (presData x).2
  apply isFinitePresentation_of_isOpenCover M (fun x ↦ (U x).1) ?_ pres
  · rw [TopologicalSpace.IsOpenCover]
    apply top_unique
    rintro x -
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A quasicoherent finite locally free sheaf is of finite type. -/
lemma IsFiniteLocallyFree.isFiniteType {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) : M.IsFiniteType := by
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  infer_instance

/-- A quasicoherent vector bundle of fixed rank is of finite presentation. -/
lemma IsProjectiveOfRank.isFinitePresentation {q : ℕ} {M : X.Modules}
    [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) : M.IsFinitePresentation :=
  hM.isFiniteLocallyFree.isFinitePresentation

/-- A quasicoherent vector bundle of fixed rank is of finite type. -/
lemma IsProjectiveOfRank.isFiniteType {q : ℕ} {M : X.Modules}
    [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M) : M.IsFiniteType :=
  hM.isFiniteLocallyFree.isFiniteType

/-- Being finite locally free of a fixed rank is invariant under isomorphism of sheaves
of modules. -/
lemma IsProjectiveOfRank.of_iso {q : ℕ} {M N : X.Modules} (e : M ≅ N)
    (hM : IsProjectiveOfRank q M) : IsProjectiveOfRank q N := by
  intro x
  obtain ⟨U, hx, hfin, hproj, hrank⟩ := hM x
  let eUCat : M.val.obj (op U.1) ≅ N.val.obj (op U.1) :=
    { hom := e.hom.val.app (op U.1)
      inv := e.inv.val.app (op U.1)
      hom_inv_id := congrArg (fun f ↦ f.val.app (op U.1)) e.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.val.app (op U.1)) e.inv_hom_id }
  let eU : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) := eUCat.toLinearEquiv
  refine ⟨U, hx, Module.Finite.equiv eU,
    Module.Projective.of_equiv eU, ?_⟩
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv eU) p).symm.trans (hrank p)

/-- Finite local freeness of fixed rank descends from the members of an arbitrary
scheme-theoretic open cover. -/
lemma IsProjectiveOfRank.of_openCover_restrict {q : ℕ} {M : X.Modules}
    (𝒰 : X.OpenCover) (h : ∀ i,
      IsProjectiveOfRank q ((Modules.restrictFunctor (𝒰.f i)).obj M)) :
    IsProjectiveOfRank q M := by
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  let i := 𝒰.idx x
  have hPull : IsProjectiveOfRank q ((Modules.pullback (𝒰.f i)).obj M) :=
    (h i).of_iso ((Modules.restrictFunctorIsoPullback (𝒰.f i)).app M)
  obtain ⟨U, hyU, hfin, hproj, hrank⟩ := hPull y
  let W : X.affineOpens :=
    ⟨𝒰.f i ''ᵁ U.1, U.2.image_of_isOpenImmersion (𝒰.f i)⟩
  refine ⟨W, ?_, ?_⟩
  · exact ⟨y, hyU, hy⟩
  · exact Modules.sections_finite_projective_rank_of_pullback_openImmersion
      (𝒰.f i) M U.1 hfin hproj hrank

/-- Pullback along an isomorphism of schemes preserves finite local freeness of fixed
rank. -/
lemma IsProjectiveOfRank.pullback_of_isIso {Y : Scheme.{u}} {q : ℕ} {M : Y.Modules}
    (f : X ⟶ Y) [IsIso f] (hM : IsProjectiveOfRank q M) :
    IsProjectiveOfRank q ((Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hxU, hfin, hproj, hrank⟩ := hM (f x)
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage_of_isIso f⟩
  have hVU : f ''ᵁ V.1 = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hfin' : Module.Finite Γ(Y, f ''ᵁ V.1) Γ(M, f ''ᵁ V.1) := by
    rw [hVU]
    exact hfin
  have hproj' : Module.Projective Γ(Y, f ''ᵁ V.1) Γ(M, f ''ᵁ V.1) := by
    rw [hVU]
    exact hproj
  have hrank' : ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ V.1),
      Module.rankAtStalk Γ(M, f ''ᵁ V.1) p = q := by
    rw [hVU]
    exact hrank
  obtain ⟨hfinV, hprojV, hrankV⟩ :=
    pullback_openImmersion_sections_finite_projective_rank f M V.1 hfin' hproj' hrank'
  exact ⟨V, hxU, hfinV, hprojV, hrankV⟩

/-- On an affine spectrum, the canonical finite free sheaf has its expected
constant rank. -/
lemma free_isProjectiveOfRank_spec (R : CommRingCat.{u}) (m : ℕ) :
    IsProjectiveOfRank m
      (SheafOfModules.free (R := (Spec R).ringCatSheaf)
        (ULift.{u} (Fin m))) := by
  let e := (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin m))).toLinearEquiv
  have hfin : Module.Finite R
      (moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf)
          (ULift.{u} (Fin m)))) :=
    Module.Finite.equiv e
  have hproj : Module.Projective R
      (moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf)
          (ULift.{u} (Fin m)))) :=
    Module.Projective.of_equiv e
  have hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        (moduleSpecΓFunctor.obj
          (SheafOfModules.free (R := (Spec R).ringCatSheaf)
            (ULift.{u} (Fin m)))) p = m := by
    intro p
    let _ := p.nontrivial
    rw [← Module.rankAtStalk_eq_of_equiv e]
    calc
      Module.rankAtStalk (ULift.{u} (Fin m) →₀ R) p =
          Module.rankAtStalk (ULift.{u} (Fin m) → R) p :=
        congrFun (Module.rankAtStalk_eq_of_equiv
          (Finsupp.linearEquivFunOnFinite R R (ULift.{u} (Fin m)))) p
      _ = _ := by
        rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
        simp
  obtain ⟨hfin', hproj', hrank'⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_top
      (SheafOfModules.free (R := (Spec R).ringCatSheaf)
        (ULift.{u} (Fin m))) hfin hproj hrank
  exact isProjectiveOfRank_of_top hfin' hproj' hrank'

/-- On an affine scheme, the canonical finite free sheaf has its expected
constant rank. -/
lemma free_isProjectiveOfRank_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (m : ℕ) :
    IsProjectiveOfRank m
      (SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin m))) := by
  let h := IsProjectiveOfRank.pullback_of_isIso X.isoSpec.hom
    (free_isProjectiveOfRank_spec (CommRingCat.of Γ(X, ⊤)) m)
  exact IsProjectiveOfRank.of_iso
    (Modules.pullbackFreeIso X.isoSpec.hom (ULift.{u} (Fin m))) h

/-- The canonical finite free sheaf on an arbitrary scheme is finite locally
free of its expected rank. -/
lemma free_isProjectiveOfRank (X : Scheme.{u}) (m : ℕ) :
    IsProjectiveOfRank m
      (SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin m))) := by
  apply IsProjectiveOfRank.of_affineOpen_pullbacks
  intro U
  exact IsProjectiveOfRank.of_iso
    (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin m))).symm
    (free_isProjectiveOfRank_of_isAffine U.1.toScheme m)

/-- The canonical finite free sheaf on a scheme is finite locally free. -/
lemma free_isFiniteLocallyFree (X : Scheme.{u}) (m : ℕ) :
    IsFiniteLocallyFree
      (SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin m))) :=
  (free_isProjectiveOfRank X m).isFiniteLocallyFree

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of a quasicoherent finite locally free sheaf of fixed rank has the same
rank.  The proof reduces on affine charts to tensor-product base change. -/
lemma IsProjectiveOfRank.pullback {Y : Scheme.{u}} {q : ℕ} {M : Y.Modules}
    [M.IsQuasicoherent] (f : X ⟶ Y) (hM : IsProjectiveOfRank q M) :
    IsProjectiveOfRank q ((pullback f).obj M) := by
  intro x
  obtain ⟨U, hxU, hfinU, hprojU, hrankU⟩ := hM (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U.1).2
  let VA : X.affineOpens := ⟨V, hV⟩
  let MU := (Modules.pullback U.1.ι).obj M
  have himU : U.1.ι ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hMUtop := pullback_openImmersion_sections_finite_projective_rank
    U.1.ι M ⊤ (q := q) (by rw [himU]; exact hfinU) (by rw [himU]; exact hprojU)
      (by rw [himU]; exact hrankU)
  let Mspec := (Modules.pullback U.2.isoSpec.inv).obj MU
  have himSpec : U.2.isoSpec.inv ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hMspecTop := pullback_openImmersion_sections_finite_projective_rank
    U.2.isoSpec.inv MU ⊤ (q := q) (by rw [himSpec]; exact hMUtop.1)
      (by rw [himSpec]; exact hMUtop.2.1) (by rw [himSpec]; exact hMUtop.2.2)
  have hMspecΓ := moduleSpecΓFunctor_finite_projective_rank_of_top Mspec
    hMspecTop.1 hMspecTop.2.1 hMspecTop.2.2
  let g := f.appLE U.1 VA.1 hVU
  have hAffΓ := pullbackQuasicoherentSections_finite_projective_rank g Mspec
    hMspecΓ.1 hMspecΓ.2.1 hMspecΓ.2.2
  have hAffTop := moduleSpecΓFunctor_finite_projective_rank_top
    ((Modules.pullback (Spec.map g)).obj Mspec) hAffΓ.1 hAffΓ.2.1 hAffΓ.2.2
  let Aff := (Modules.pullback (Spec.map g)).obj Mspec
  have hAff : IsProjectiveOfRank q Aff :=
    isProjectiveOfRank_of_top hAffTop.1 hAffTop.2.1 hAffTop.2.2
  have hcomp := IsAffineOpen.SpecMap_appLE_fromSpec f U.2 VA.2 hVU
  let e : Aff ≅
      (Modules.pullback VA.2.isoSpec.inv).obj
        ((Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M)) :=
    (Modules.pullback (Spec.map g)).mapIso
        ((pullbackComp U.2.isoSpec.inv U.1.ι).app M) ≪≫
      (pullbackComp (Spec.map g) U.2.fromSpec).app M ≪≫
      (pullbackCongr hcomp).app M ≪≫
      ((pullbackComp VA.2.fromSpec f).app M).symm ≪≫
      ((pullbackComp VA.2.isoSpec.inv VA.1.ι).app ((Modules.pullback f).obj M)).symm
  have hSpecV : IsProjectiveOfRank q
      ((Modules.pullback VA.2.isoSpec.inv).obj
        ((Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M))) :=
    hAff.of_iso e
  have hBack := hSpecV.pullback_of_isIso VA.2.isoSpec.hom
  let NV := (Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M)
  let eBack : (Modules.pullback VA.2.isoSpec.hom).obj
      ((Modules.pullback VA.2.isoSpec.inv).obj NV) ≅ NV :=
    (pullbackComp VA.2.isoSpec.hom VA.2.isoSpec.inv).app NV ≪≫
      (pullbackCongr VA.2.isoSpec.hom_inv_id).app NV ≪≫ (pullbackId _).app NV
  have hNV : IsProjectiveOfRank q NV := hBack.of_iso eBack
  obtain ⟨W, hxW, hfinW, hprojW, hrankW⟩ := hNV ⟨x, hxV⟩
  let W' : X.affineOpens := ⟨VA.1.ι ''ᵁ W.1,
    (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion VA.1.ι).mpr W.2⟩
  have hxW' : x ∈ W'.1 := ⟨⟨x, hxV⟩, hxW, rfl⟩
  have hsec := sections_finite_projective_rank_of_pullback_openImmersion
    VA.1.ι ((Modules.pullback f).obj M) W.1 hfinW hprojW hrankW
  have himage : VA.1.ι ''ᵁ W.1 = W'.1 := rfl
  exact ⟨W', hxW', by simpa [himage] using hsec.1,
    by simpa [himage] using hsec.2.1, by simpa [himage] using hsec.2.2⟩

end Modules

/-- Background definition for Theorem 2.1.1 (the implicit definition of
the functor; trivial bundle case): let `q` and `n` be natural numbers. The Grassmannian
functor `Gr(q, n)` on schemes: its points over a scheme `T` are the quasi-coherent
submodule sheaves `K ⊆ O_T^{⊕n}` whose quotient `O_T^{⊕n}/K` is a vector bundle of rank
`q`. By Remark 2.1.5(2)  this kernel encoding agrees with the book's
description as rank-`q` vector bundle quotients of `O_T^{⊕n}` up to isomorphism; it is
strictly functorial and takes values in `Type u`. See the section COMMENTARY.md entry on
the kernel encoding. -/
def grassmannianFunctor (q n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := {K : (unop T).SubmoduleSheafData n // K.QuotientProjectiveOfRank q}
  map f := ↾fun K ↦ ⟨K.1.comap f.unop, K.2.comap f.unop⟩
  map_id _ :=
    ConcreteCategory.hom_ext _ _ fun K ↦ Subtype.ext (SubmoduleSheafData.comap_id K.1)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ fun K ↦
      Subtype.ext (SubmoduleSheafData.comap_comp K.1 g.unop f.unop)

namespace Modules

variable (q : ℕ) {S : Scheme.{u}} (V : S.Modules)

/-- Background definition for Theorem 2.1.1 (the implicit definition of
a point of `Gr(q, V)`): let `V` be a sheaf of modules on a scheme `S`, let `T` be a scheme
over `S` and `q` a natural number. A rank-`q` locally free quotient of the pullback `V_T`:
a quasi-coherent sheaf of modules `Q` on `T`, finite locally free of rank `q`, together
with an epimorphism `V_T ↠ Q`. Two such quotients define the same point of the
Grassmannian `Gr(q, V)` when they are isomorphic compatibly with the projections; see
`PullbackQuotient.setoid`. -/
structure PullbackQuotient (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf of modules. -/
  Q : T.left.Modules
  /-- The quotient is quasi-coherent. -/
  isQuasicoherent : Q.IsQuasicoherent
  /-- The quotient is a vector bundle of rank `q`. -/
  isProjectiveOfRank : IsProjectiveOfRank q Q
  /-- The projection from the pullback of `V`. -/
  π : (Modules.pullback T.hom).obj V ⟶ Q
  /-- The projection is an epimorphism. -/
  epi : Epi π

/-- A quotient presentation whose ambient sheaf is literally the canonical free sheaf
on the test scheme.  This strict model is the intermediate object between relative
quotients of a free sheaf and the kernel-encoded absolute Grassmannian. -/
structure FreeQuotient (q : ℕ) (I : Type u) (T : Scheme.{u}) : Type (u + 1) where
  /-- The quotient sheaf. -/
  Q : T.Modules
  /-- The quotient is quasi-coherent. -/
  isQuasicoherent : Q.IsQuasicoherent
  /-- The quotient has the required locally free rank. -/
  isProjectiveOfRank : IsProjectiveOfRank q Q
  /-- The quotient map from the canonical free sheaf. -/
  π : SheafOfModules.free (R := T.ringCatSheaf) I ⟶ Q
  /-- The quotient map is epic. -/
  epi : Epi π

set_option backward.isDefEq.respectTransparency.types false in
/-- Transposing after the canonical comparison from literal restriction to
pullback agrees with transposing for the pullback–pushforward adjunction. -/
lemma restrict_homEquiv_iso_hom_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (N : X.Modules)
    (g : (pullback f).obj M ⟶ N) :
    (restrictAdjunction f).homEquiv M N
        ((restrictFunctorIsoPullback f).hom.app M ≫ g) =
      (pullbackPushforwardAdjunction f).homEquiv M N g := by
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Functor.map_comp]
  rw [← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (pushforward f).map g)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (restrictAdjunction f) (pullbackPushforwardAdjunction f) M)

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse transposition through the pullback--pushforward adjunction is
inverse transposition through literal restriction, followed by the canonical
comparison from restriction to pullback. -/
lemma restrict_homEquiv_symm_eq_iso_hom_comp {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (N : X.Modules)
    (k : M ⟶ (pushforward f).obj N) :
    ((restrictAdjunction f).homEquiv M N).symm k =
      (restrictFunctorIsoPullback f).hom.app M ≫
        ((pullbackPushforwardAdjunction f).homEquiv M N).symm k := by
  apply ((restrictAdjunction f).homEquiv M N).injective
  rw [restrict_homEquiv_iso_hom_comp]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison from literal restriction to pullback intertwines
the counits of their two adjunctions with pushforward. -/
lemma restrictFunctorIsoPullback_hom_app_pushforward_comp_counit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (N : X.Modules) :
    (restrictFunctorIsoPullback f).hom.app ((pushforward f).obj N) ≫
        (pullbackPushforwardAdjunction f).counit.app N =
      (restrictAdjunction f).counit.app N := by
  exact Adjunction.leftAdjointUniq_hom_app_counit
    (restrictAdjunction f) (pullbackPushforwardAdjunction f) N

set_option backward.isDefEq.respectTransparency.types false in
/-- For an open immersion, the canonical pullback map on structure sheaves,
transported to literal restriction, is the inverse transpose of the canonical
map from the structure sheaf to its pushforward. -/
lemma restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
    ((restrictAdjunction f).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply (restrictAdjunction f).homEquiv _ _ |>.injective
  rw [restrict_homEquiv_iso_hom_comp]
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom).trans (Equiv.apply_symm_apply _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- In inverse-normalized form, the canonical pullback map on structure
sheaves is obtained by first returning to literal restriction and then taking
the inverse transpose of the canonical structure-sheaf map. -/
lemma pullbackObjUnitToUnit_eq_restrictFunctorIsoPullback_inv_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
      (restrictFunctorIsoPullback f).inv.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        ((restrictAdjunction f).homEquiv _ _).symm
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  rw [← restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit f]
  exact ((restrictFunctorIsoPullback f).app
    (SheafOfModules.unit Y.ringCatSheaf)).inv_hom_id_assoc _ |>.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction-theoretic structure-sheaf comparison agrees with the
explicit restriction isomorphism for an open immersion. -/
lemma restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
    (restrictUnitIso f).hom := by
  rw [restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit]
  apply (restrictAdjunction f).homEquiv _ _ |>.injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_apply]
  ext U x
  simp only [Functor.comp_obj, Hom.comp_app, pushforward_obj_obj,
    restrictAdjunction_unit_app_app, homOfLE_leOfHom, pushforward_map_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  change f.app U x = (f.appIso (f ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op x)
  have h : f.app U =
      Y.presheaf.map (homOfLE (Set.image_preimage_subset f U.1)).op ≫
        (f.appIso (f ⁻¹ᵁ U)).hom := by
    rw [← f.app_appIso_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Expanded inverse form of the compatibility with the explicit restriction
isomorphism. -/
lemma pullbackObjUnitToUnit_inv_comp_restrictFunctorIsoPullback_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (restrictFunctorIsoPullback f).inv.app
          (SheafOfModules.unit Y.ringCatSheaf) =
      (restrictUnitIso f).inv := by
  rw [← cancel_mono (restrictUnitIso f).hom]
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [← restrictFunctorIsoPullback_hom_comp_pullbackObjUnitToUnit_eq f]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The inverse canonical pullback map is the explicit inverse restriction
isomorphism followed by the comparison from literal restriction to pullback. -/
lemma pullbackObjUnitToUnit_inv_eq_restrictUnitIso_inv_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      (restrictUnitIso f).inv ≫
        (restrictFunctorIsoPullback f).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) := by
  rw [← cancel_mono ((restrictFunctorIsoPullback f).inv.app
    (SheafOfModules.unit Y.ringCatSheaf))]
  slice_rhs 2 3 => simp
  exact pullbackObjUnitToUnit_inv_comp_restrictFunctorIsoPullback_inv f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality-strengthened inverse normalization: pulling a morphism out of
the structure sheaf after the inverse pullback comparison is the same as
restricting it literally between the explicit restriction isomorphisms. -/
lemma pullbackObjUnitToUnit_inv_comp_pullback_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (pullback f).map g =
      (restrictUnitIso f).inv ≫ (restrictFunctor f).map g ≫
        (restrictFunctorIsoPullback f).hom.app M := by
  rw [pullbackObjUnitToUnit_inv_eq_restrictUnitIso_inv_comp]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t ↦ (restrictUnitIso f).inv ≫ t)
      ((restrictFunctorIsoPullback f).hom.naturality g).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Under the pullback--pushforward adjunction for an open immersion, the
canonical pullback morphism of structure sheaves transposes to the canonical
morphism from the structure sheaf to its pushforward. -/
lemma pullbackPushforwardAdjunction_unit_comp_pushforward_pullbackObjUnitToUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pushforward f).map
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  rw [Adjunction.homEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse composition cocycle for the canonical pullback morphisms of
structure sheaves. -/
lemma pullbackObjUnitToUnit_inv_comp_pullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (f ≫ g).toRingCatSheafHom) := inferInstance
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (pullback f).map
          (inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
        (pullbackComp f g).hom.app
          (SheafOfModules.unit Z.ringCatSheaf) =
      inv (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom) := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    (f ≫ g).toRingCatSheafHom) := inferInstance
  have hunit :
      (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom =
        (pullback f).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
    exact SheafOfModules.pullbackObjUnitToUnit_comp
      g.toRingCatSheafHom f.toRingCatSheafHom
  rw [← cancel_mono
    (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom)]
  simp only [Category.assoc]
  rw [hunit]
  simp only [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
  rw [show (pullback f).map
      (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) = 𝟙 _ from
    (pullback f).map_id _]
  calc
    _ = inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
      congrArg (fun k ↦ k ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
          (Category.comp_id _)
    _ = _ := IsIso.inv_hom_id_assoc
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) (𝟙 _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse structure-sheaf pullback comparison is compatible with
replacing a scheme morphism by an equal one. -/
lemma pullbackObjUnitToUnit_inv_comp_pullbackCongr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) :
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (pullbackCongr h).hom.app (SheafOfModules.unit Y.ringCatSheaf) =
      inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := by
  subst h
  simp [pullbackCongr]
  rfl
namespace FreeQuotient

variable {q : ℕ} {I : Type u} {T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Equivalence of strict free quotient presentations. -/
protected def setoid (q : ℕ) (I : Type u) (T : Scheme.{u}) :
    Setoid (FreeQuotient q I T) where
  r x y := ∃ e : x.Q ≅ y.Q, x.π ≫ e.hom = y.π
  iseqv := by
    refine ⟨fun x ↦ ⟨Iso.refl _, Category.comp_id _⟩, ?_, ?_⟩
    · rintro x y ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      rw [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
    · rintro x y z ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e ≪≫ e', by rw [Iso.trans_hom, ← Category.assoc, he, he']⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Replace the target of a strict free quotient by an isomorphic sheaf. -/
noncomputable def postcompIso (x : FreeQuotient q I T) {Q' : T.Modules}
    (e : x.Q ≅ Q') : FreeQuotient q I T where
  Q := Q'
  isQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank.of_iso e
  π := x.π ≫ e.hom
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _

/-- Replacing the target of a strict free quotient by an isomorphic sheaf does not
change the quotient presentation it defines. -/
lemma postcompIso_r (x : FreeQuotient q I T) {Q' : T.Modules} (e : x.Q ≅ Q') :
    (FreeQuotient.setoid q I T).r x (x.postcompIso e) :=
  ⟨e, rfl⟩

/-- The map on affine global sections associated to a strict free quotient. -/
noncomputable def moduleMap {R : CommRingCat.{u}}
    (x : FreeQuotient q I (Spec R)) :
    (I →₀ R) →ₗ[R] moduleSpecΓFunctor.obj x.Q :=
  ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π).hom

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The affine module map of a strict free quotient is surjective. -/
lemma moduleMap_surjective {R : CommRingCat.{u}}
    (x : FreeQuotient q I (Spec R)) : Function.Surjective x.moduleMap := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : Epi x.π := x.epi
  have hπ : Function.Surjective (moduleSpecΓFunctor.map x.π) :=
    Scheme.Modules.moduleSpecΓFunctor_map_surjective_of_epi x.π
  exact hπ.comp (freeModuleSpecΓIso (R := R) I).toLinearEquiv.surjective

/-- The standard equivalence from the free module indexed by `ULift (Fin n)` to the
function model `R^n` used by `SubmoduleSheafData`. -/
noncomputable def uliftFinFinsuppEquivPi {R : Type u} [CommRing R] (n : ℕ) :
    (ULift.{u} (Fin n) →₀ R) ≃ₗ[R] (Fin n → R) :=
  (Finsupp.mapDomain.linearEquiv R R Equiv.ulift).trans
    (Finsupp.linearEquivFunOnFinite R R (Fin n))

/-- The quasicoherent sheaf on an affine spectrum associated to the quotient of a
finite free module by a specified submodule. -/
noncomputable def affineQuotientSheaf {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) : (Spec R).Modules :=
  AlgebraicGeometry.tilde (ModuleCat.of R ((Fin n → R) ⧸ K))

/-- The canonical epimorphism from the finite free sheaf to the affine quotient sheaf
associated to a submodule. -/
noncomputable def affineQuotientMap {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      affineQuotientSheaf K :=
  (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin n))).inv ≫
    (AlgebraicGeometry.tilde.functor R).map
      (ModuleCat.ofHom (K.mkQ.comp (uliftFinFinsuppEquivPi n).toLinearMap))

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
instance affineQuotientMap_epi {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) : Epi (affineQuotientMap K) := by
  let f := K.mkQ.comp (uliftFinFinsuppEquivPi n).toLinearMap
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective K).comp (uliftFinFinsuppEquivPi n).surjective
  letI : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).2 hf
  letI : Epi ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom f)) :=
    Functor.map_epi (AlgebraicGeometry.tilde.functor R) (ModuleCat.ofHom f)
  change Epi ((AlgebraicGeometry.tildeFinsupp
      (R := R) (ULift.{u} (Fin n))).inv ≫
    (AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom f))
  exact epi_comp _ _
instance affineQuotientSheaf_isQuasicoherent {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) : (affineQuotientSheaf K).IsQuasicoherent := by
  change (AlgebraicGeometry.tilde
    (ModuleCat.of R ((Fin n → R) ⧸ K))).IsQuasicoherent
  infer_instance

/-- Global sections of the affine quotient sheaf identify with the original quotient
module. -/
noncomputable def affineQuotientModuleIso {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    ModuleCat.of R ((Fin n → R) ⧸ K) ≅
      moduleSpecΓFunctor.obj (affineQuotientSheaf K) :=
  AlgebraicGeometry.tilde.toTildeΓNatIso.app
    (ModuleCat.of R ((Fin n → R) ⧸ K))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical affine global-sections identifications,
`affineQuotientMap K` is the ordinary quotient map of finite free modules. -/
lemma affineQuotientMap_moduleSpecΓ {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
        moduleSpecΓFunctor.map (affineQuotientMap K) ≫
      (affineQuotientModuleIso K).inv =
    ModuleCat.ofHom (K.mkQ.comp (uliftFinFinsuppEquivPi n).toLinearMap) := by
  let f := ModuleCat.ofHom
    (K.mkQ.comp (uliftFinFinsuppEquivPi n).toLinearMap)
  change (AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
        (ModuleCat.of R (ULift.{u} (Fin n) →₀ R)) ≫
      moduleSpecΓFunctor.map
        (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin n))).hom) ≫
      moduleSpecΓFunctor.map
        ((AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin n))).inv ≫
          (AlgebraicGeometry.tilde.functor R).map f) ≫
      (AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
        (ModuleCat.of R ((Fin n → R) ⧸ K))) = f
  rw [Functor.map_comp]
  let e := moduleSpecΓFunctor.mapIso
    (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin n)))
  change (AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
      (ModuleCat.of R (ULift.{u} (Fin n) →₀ R)) ≫ e.hom) ≫ e.inv ≫
        moduleSpecΓFunctor.map ((AlgebraicGeometry.tilde.functor R).map f) ≫
      AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
        (ModuleCat.of R ((Fin n → R) ⧸ K)) = f
  have hn := AlgebraicGeometry.tilde.toTildeΓNatIso.hom.naturality f
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
    Functor.comp_map] at hn
  calc
    _ = AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin n) →₀ R)) ≫
        (e.hom ≫ e.inv ≫
          (moduleSpecΓFunctor.map ((AlgebraicGeometry.tilde.functor R).map f) ≫
            AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
              (ModuleCat.of R ((Fin n → R) ⧸ K)))) := by
      simp only [Category.assoc]
    _ = AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin n) →₀ R)) ≫
        (moduleSpecΓFunctor.map ((AlgebraicGeometry.tilde.functor R).map f) ≫
          AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
            (ModuleCat.of R ((Fin n → R) ⧸ K))) := by
      rw [e.hom_inv_id_assoc]
    _ = (AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin n) →₀ R)) ≫
        moduleSpecΓFunctor.map ((AlgebraicGeometry.tilde.functor R).map f)) ≫
          AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
            (ModuleCat.of R ((Fin n → R) ⧸ K)) := by
      simp only [Category.assoc]
    _ = (f ≫ AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R ((Fin n → R) ⧸ K))) ≫
        AlgebraicGeometry.tilde.toTildeΓNatIso.inv.app
          (ModuleCat.of R ((Fin n → R) ⧸ K)) := by rw [hn]
    _ = f := by simp

/-- The global-sections map of `affineQuotientMap`, transported to the standard
finite-function coordinates on both sides. -/
noncomputable def affineQuotientModuleMapPi {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    (Fin n → R) →ₗ[R] ((Fin n → R) ⧸ K) :=
  ((freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
      moduleSpecΓFunctor.map (affineQuotientMap K) ≫
        (affineQuotientModuleIso K).inv).hom.comp
    (uliftFinFinsuppEquivPi n).symm.toLinearMap

/-- In standard coordinates the affine sheaf quotient map is literally the module
quotient map. -/
lemma affineQuotientModuleMapPi_eq_mkQ {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    affineQuotientModuleMapPi K = K.mkQ := by
  rw [affineQuotientModuleMapPi]
  have h := congrArg ModuleCat.Hom.hom (affineQuotientMap_moduleSpecΓ K)
  rw [h]
  apply LinearMap.ext
  intro z
  simp

/-- The kernel recovered from the affine quotient sheaf is the original submodule. -/
lemma ker_affineQuotientModuleMapPi {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) :
    LinearMap.ker (affineQuotientModuleMapPi K) = K := by
  rw [affineQuotientModuleMapPi_eq_mkQ, Submodule.ker_mkQ]

/-- A finite-projective constant-rank quotient of a finite free module determines a
strict free quotient presentation on the affine spectrum. -/
noncomputable def affineFreeQuotientOfSubmodule {R : CommRingCat.{u}} {n : ℕ}
    (K : Submodule R (Fin n → R)) (q : ℕ)
    (hfin : Module.Finite R ((Fin n → R) ⧸ K))
    (hproj : Module.Projective R ((Fin n → R) ⧸ K))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ K) p = q) :
    FreeQuotient q (ULift.{u} (Fin n)) (Spec R) where
  Q := affineQuotientSheaf K
  isQuasicoherent := affineQuotientSheaf_isQuasicoherent K
  isProjectiveOfRank := by
    let e := (affineQuotientModuleIso K).toLinearEquiv
    have hfin' : Module.Finite R
        (moduleSpecΓFunctor.obj (affineQuotientSheaf K)) :=
      Module.Finite.equiv e
    have hproj' : Module.Projective R
        (moduleSpecΓFunctor.obj (affineQuotientSheaf K)) :=
      Module.Projective.of_equiv e
    have hrank' : ∀ p : PrimeSpectrum R,
        Module.rankAtStalk
          (moduleSpecΓFunctor.obj (affineQuotientSheaf K)) p = q := by
      intro p
      exact (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (hrank p)
    obtain ⟨htfin, htproj, htrank⟩ :=
      moduleSpecΓFunctor_finite_projective_rank_top
        (affineQuotientSheaf K) hfin' hproj' hrank'
    exact isProjectiveOfRank_of_top htfin htproj htrank
  π := affineQuotientMap K
  epi := affineQuotientMap_epi K

/-- The affine module map of a strict quotient with `n` generators, expressed in the
`Fin n → R` convention. -/
noncomputable def moduleMapPi {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    (Fin n → R) →ₗ[R] moduleSpecΓFunctor.obj x.Q :=
  x.moduleMap.comp (uliftFinFinsuppEquivPi n).symm.toLinearMap

/-- The affine linear functional associated to a presentation of the unit sheaf by a
finite free sheaf. -/
noncomputable def unitPresentationLinearMapPi {n : ℕ} {R : CommRingCat.{u}}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) :
    (Fin n → R) →ₗ[R] R :=
  (unitModuleSpecΓIso R).inv.hom.comp
    (((freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
      moduleSpecΓFunctor.map π).hom.comp
        (uliftFinFinsuppEquivPi n).symm.toLinearMap)

/-- The coefficient of a presentation of the unit sheaf at a free generator. -/
noncomputable def unitPresentationCoefficient {n : ℕ} {R : CommRingCat.{u}}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) (i : Fin n) : R :=
  (unitPresentationLinearMapPi π) (Pi.single i 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A coefficient of a finite-free presentation of the unit sheaf is obtained by
applying affine global sections to the corresponding generator morphism. -/
lemma unitPresentationCoefficient_eq {n : ℕ} {R : CommRingCat.{u}}
    (π : SheafOfModules.free
        (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf) (i : Fin n) :
    unitPresentationCoefficient π i =
      (unitModuleSpecΓIso R).inv.hom
        (((moduleSpecΓFunctor (R := R)).map π).hom
          (((moduleSpecΓFunctor (R := R)).map
            (SheafOfModules.ιFree (ULift.up i))).hom
              ((unitModuleSpecΓIso R).hom.hom 1))) := by
  have hcoord :
      (uliftFinFinsuppEquivPi (R := R) n).symm (Pi.single i 1) =
        Finsupp.single (ULift.up i) 1 := by
    ext j
    simp [uliftFinFinsuppEquivPi]
  unfold unitPresentationCoefficient unitPresentationLinearMapPi
  simp only [LinearMap.comp_apply]
  calc
    _ = (unitModuleSpecΓIso R).inv.hom
        (((freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
          (moduleSpecΓFunctor (R := R)).map π).hom
            (Finsupp.single (ULift.up i) 1)) :=
      congrArg (fun z : ULift.{u} (Fin n) →₀ R ↦
        (unitModuleSpecΓIso R).inv.hom
          (((freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
            (moduleSpecΓFunctor (R := R)).map π).hom z)) hcoord
    _ = _ := by
      congr 1
      have h := lsingle_comp_freeModuleSpecΓIso_hom
        (R := R) (ULift.{u} (Fin n)) (ULift.up i)
      have happ₀ := ConcreteCategory.congr_hom h 1
      have hsingle :
          (ModuleCat.ofHom (Finsupp.lsingle (ULift.up i) (R := R)
            (M := ModuleCat.of R R))).hom 1 =
            Finsupp.single (ULift.up i) 1 := by
        ext j
        simp
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply] at happ₀
      rw [hsingle] at happ₀
      exact congrArg ((moduleSpecΓFunctor (R := R)).map π).hom happ₀

lemma moduleMapPi_surjective {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    Function.Surjective x.moduleMapPi :=
  x.moduleMap_surjective.comp (uliftFinFinsuppEquivPi n).symm.surjective

/-- The kernel of a strict free quotient on an affine spectrum, in the finite-function
coordinate convention of the absolute Grassmannian. -/
noncomputable def kernelSubmodule {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    Submodule R (Fin n → R) := LinearMap.ker x.moduleMapPi

/-- After identifying its global sections with the module quotient, the map induced by
`affineFreeQuotientOfSubmodule` is the standard quotient map. -/
lemma affineFreeQuotientOfSubmodule_moduleMapPi_comp {R : CommRingCat.{u}} {n q : ℕ}
    (K : Submodule R (Fin n → R))
    (hfin : Module.Finite R ((Fin n → R) ⧸ K))
    (hproj : Module.Projective R ((Fin n → R) ⧸ K))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ K) p = q) :
    (affineQuotientModuleIso K).inv.hom.comp
      (affineFreeQuotientOfSubmodule K q hfin hproj hrank).moduleMapPi =
        affineQuotientModuleMapPi K := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Passing from an affine submodule to its strict quotient and then taking the kernel
recovers the original submodule. -/
@[simp]
lemma affineFreeQuotientOfSubmodule_kernelSubmodule {R : CommRingCat.{u}} {n q : ℕ}
    (K : Submodule R (Fin n → R))
    (hfin : Module.Finite R ((Fin n → R) ⧸ K))
    (hproj : Module.Projective R ((Fin n → R) ⧸ K))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((Fin n → R) ⧸ K) p = q) :
    (affineFreeQuotientOfSubmodule K q hfin hproj hrank).kernelSubmodule = K := by
  change LinearMap.ker
    (affineFreeQuotientOfSubmodule K q hfin hproj hrank).moduleMapPi = K
  have hinj : Function.Injective (affineQuotientModuleIso K).inv.hom := by
    intro a b hab
    apply_fun (affineQuotientModuleIso K).hom.hom at hab
    simpa using hab
  have hker : LinearMap.ker
      (affineFreeQuotientOfSubmodule K q hfin hproj hrank).moduleMapPi =
      LinearMap.ker ((affineQuotientModuleIso K).inv.hom.comp
        (affineFreeQuotientOfSubmodule K q hfin hproj hrank).moduleMapPi) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hx
      exact hx ▸ map_zero _
    · intro hx
      apply hinj
      exact hx.trans (map_zero _).symm
  calc
    _ = LinearMap.ker ((affineQuotientModuleIso K).inv.hom.comp
          (affineFreeQuotientOfSubmodule K q hfin hproj hrank).moduleMapPi) :=
      hker
    _ = LinearMap.ker (affineQuotientModuleMapPi K) := by
      rw [affineFreeQuotientOfSubmodule_moduleMapPi_comp]
    _ = K := ker_affineQuotientModuleMapPi K

/-- The kernel of the scalar extension of an affine strict quotient map is the span of
the componentwise images of its original kernel. -/
lemma ker_baseChangePi_moduleMapPi {n : ℕ} {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : Algebra R S := φ.hom.toAlgebra
    LinearMap.ker (LinearMap.baseChangePi S x.moduleMapPi) =
      Submodule.span S ((fun w ↦ fun i ↦ φ.hom (w i)) ''
        (x.kernelSubmodule : Set (Fin n → R))) := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact LinearMap.ker_baseChangePi_eq_span S x.moduleMapPi_surjective

/-- The affine kernel, promoted to quasicoherent submodule data. -/
noncomputable def intrinsicKernelSubmodule {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    Submodule Γ(Spec R, ⊤) (Fin n → Γ(Spec R, ⊤)) :=
  x.kernelSubmodule.mapPiRingEquiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

/-- The affine kernel, promoted to quasicoherent submodule data. -/
noncomputable def affineKernelData {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    (Spec R).SubmoduleSheafData n :=
  SubmoduleSheafData.ofAffineSubmodule x.intrinsicKernelSubmodule

/-- The quotient by the affine kernel is canonically the global-sections module of the
given quotient sheaf. -/
noncomputable def affineKernelQuotientEquiv {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    ((Fin n → R) ⧸ x.kernelSubmodule) ≃ₗ[R] moduleSpecΓFunctor.obj x.Q :=
  x.moduleMapPi.quotKerEquivOfSurjective x.moduleMapPi_surjective

attribute [local instance] RingHomInvPair.of_ringEquiv
  RingHomInvPair.of_ringEquiv_symm

/-- The intrinsic top-section quotient used by `SubmoduleSheafData` is semilinearly
equivalent to the coordinate-ring quotient. -/
noncomputable def intrinsicKernelQuotientSemilinearEquiv {n : ℕ}
    {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    letI : RingHomInvPair (e : Γ(Spec R, ⊤) →+* R) (e.symm : R →+* Γ(Spec R, ⊤)) :=
      RingHomInvPair.of_ringEquiv e
    ((Fin n → Γ(Spec R, ⊤)) ⧸ x.intrinsicKernelSubmodule) ≃ₛₗ[(e : Γ(Spec R, ⊤) →+* R)]
      ((Fin n → R) ⧸ x.kernelSubmodule) := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : RingHomInvPair (e : Γ(Spec R, ⊤) →+* R) (e.symm : R →+* Γ(Spec R, ⊤)) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* Γ(Spec R, ⊤)) (e : Γ(Spec R, ⊤) →+* R) :=
    RingHomInvPair.of_ringEquiv_symm e
  apply Submodule.Quotient.equiv x.intrinsicKernelSubmodule x.kernelSubmodule
    (e.piSemilinearEquiv n)
  change (x.kernelSubmodule.mapPiRingEquiv e.symm).mapPiRingEquiv e =
    x.kernelSubmodule
  exact Submodule.mapPiRingEquiv_symm_mapPiRingEquiv e.symm x.kernelSubmodule

@[simp]
lemma affineKernelQuotientEquiv_mk {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) (v : Fin n → R) :
    x.affineKernelQuotientEquiv (Submodule.Quotient.mk v) = x.moduleMapPi v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- The map on affine global sections induced by a morphism from the canonical finite
free sheaf, expressed in `Fin n → R` coordinates. -/
noncomputable def moduleMapPiOfHom {n : ℕ} {R : CommRingCat.{u}}
    {N : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N) :
    (Fin n → R) →ₗ[R] moduleSpecΓFunctor.obj N :=
  (moduleSpecΓFunctor.map g).hom.comp
    ((freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom.hom.comp
      (uliftFinFinsuppEquivPi n).symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Postcomposition of free-sheaf morphisms becomes postcomposition of their affine
coordinate maps. -/
lemma moduleMapPiOfHom_comp {n : ℕ} {R : CommRingCat.{u}}
    {N P : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N) (t : N ⟶ P) :
    moduleMapPiOfHom (g ≫ t) =
      (moduleSpecΓFunctor.map t).hom.comp (moduleMapPiOfHom g) := by
  ext v
  simp [moduleMapPiOfHom]

/-- Postcomposition by an isomorphism does not change the kernel of an affine
free-source coordinate map. -/
lemma ker_moduleMapPiOfHom_comp_of_isIso {n : ℕ} {R : CommRingCat.{u}}
    {N P : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N) (t : N ⟶ P) [IsIso t] :
    LinearMap.ker (moduleMapPiOfHom (g ≫ t)) =
      LinearMap.ker (moduleMapPiOfHom g) := by
  rw [moduleMapPiOfHom_comp]
  ext v
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hv
    apply (ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map t)).mp inferInstance
    simpa using hv
  · intro hv
    rw [hv, map_zero]

/-- The module map induced on the target of an affine quotient when a morphism from
the finite free sheaf kills the quotient kernel. -/
noncomputable def descModuleMapOfKernelLe {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R))
    {N : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N)
    (h : x.kernelSubmodule ≤ LinearMap.ker (moduleMapPiOfHom g)) :
    moduleSpecΓFunctor.obj x.Q ⟶ moduleSpecΓFunctor.obj N := by
  let G : ModuleCat R := moduleSpecΓFunctor.obj N
  letI : Module R G := ModuleCat.isModule G
  let f : (Fin n → R) →ₗ[R] G := moduleMapPiOfHom g
  have hf : x.kernelSubmodule ≤ LinearMap.ker f := h
  let l : ModuleCat.of R ((Fin n → R) ⧸ x.kernelSubmodule) ⟶ G :=
    ConcreteCategory.ofHom (C := ModuleCat R) (x.kernelSubmodule.liftQ f hf)
  change moduleSpecΓFunctor.obj x.Q ⟶ G
  exact x.affineKernelQuotientEquiv.symm.toModuleIso.hom ≫
    l

lemma moduleMap_comp_descModuleMapOfKernelLe {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R))
    {N : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N)
    (h : x.kernelSubmodule ≤ LinearMap.ker (moduleMapPiOfHom g)) :
    moduleSpecΓFunctor.map x.π ≫ descModuleMapOfKernelLe x g h =
      moduleSpecΓFunctor.map g := by
  rw [← cancel_epi (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := (uliftFinFinsuppEquivPi n).symm.surjective z
  change (descModuleMapOfKernelLe x g h).hom (x.moduleMapPi v) =
    moduleMapPiOfHom g v
  simp only [descModuleMapOfKernelLe]
  change (x.kernelSubmodule.liftQ (moduleMapPiOfHom g) h)
      (x.affineKernelQuotientEquiv.symm (x.moduleMapPi v)) =
    moduleMapPiOfHom g v
  have hv : x.affineKernelQuotientEquiv.symm (x.moduleMapPi v) =
      Submodule.Quotient.mk v := by
    apply x.affineKernelQuotientEquiv.injective
    rw [x.affineKernelQuotientEquiv.apply_symm_apply,
      affineKernelQuotientEquiv_mk]
  rw [hv]
  exact Submodule.liftQ_apply _ _ _

/-- Universal property of an affine strict quotient: a morphism from the canonical
finite free sheaf descends whenever its affine global-sections map kills the kernel. -/
noncomputable def descOfKernelLe {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R))
    {N : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N)
    (h : x.kernelSubmodule ≤ LinearMap.ker (moduleMapPiOfHom g)) : x.Q ⟶ N :=
  let η := Scheme.Modules.fromTildeΓNatTrans (R := R)
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : IsIso (η.app x.Q) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent x.Q
  inv (η.app x.Q) ≫
    ((AlgebraicGeometry.tilde.adjunction (R := R)).homEquiv
      (moduleSpecΓFunctor.obj x.Q) N).symm
        (descModuleMapOfKernelLe x g h)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The descended affine morphism recovers the original map from the finite free
sheaf. -/
@[reassoc (attr := simp)]
lemma comp_descOfKernelLe {n : ℕ} {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R))
    {N : (Spec R).Modules}
    (g : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin n)) ⟶ N)
    (h : x.kernelSubmodule ≤ LinearMap.ker (moduleMapPiOfHom g)) :
    x.π ≫ descOfKernelLe x g h = g := by
  let F : (Spec R).Modules := SheafOfModules.free
    (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n))
  let η := Scheme.Modules.fromTildeΓNatTrans (R := R)
  let adj := AlgebraicGeometry.tilde.adjunction (R := R)
  letI : F.IsQuasicoherent := free_isQuasicoherent (R := R) (ULift.{u} (Fin n))
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : IsIso (η.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  letI : IsIso (η.app x.Q) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent x.Q
  have hn := η.naturality x.π
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← cancel_epi (η.app F)]
  change η.app F ≫ x.π ≫
      (inv (η.app x.Q) ≫
        (adj.homEquiv (moduleSpecΓFunctor.obj x.Q) N).symm
          (descModuleMapOfKernelLe x g h)) = η.app F ≫ g
  rw [← Category.assoc, ← Category.assoc]
  rw [← hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← adj.homEquiv_naturality_left_symm]
  rw [moduleMap_comp_descModuleMapOfKernelLe]
  rw [adj.homEquiv_counit]
  exact η.naturality g

/-- If the global sections of an affine free quotient are finite projective of rank
`q`, its intrinsic affine kernel datum satisfies the Grassmannian rank condition. -/
lemma affineKernelData_quotientProjectiveOfRank_of_top {n : ℕ}
    {R : CommRingCat.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R))
    (hfin : Module.Finite R (moduleSpecΓFunctor.obj x.Q))
    (hproj : Module.Projective R (moduleSpecΓFunctor.obj x.Q))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (moduleSpecΓFunctor.obj x.Q) p = q) :
    x.affineKernelData.QuotientProjectiveOfRank q := by
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, ⊤) := e.symm.toRingHom.toAlgebra
  letI : RingHomInvPair (e : Γ(Spec R, ⊤) →+* R)
      (e.symm : R →+* Γ(Spec R, ⊤)) := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* Γ(Spec R, ⊤))
      (e : Γ(Spec R, ⊤) →+* R) := RingHomInvPair.of_ringEquiv_symm e
  let eQ := x.affineKernelQuotientEquiv.symm.trans
    x.intrinsicKernelQuotientSemilinearEquiv.symm
  have htransport := Module.finite_projective_rankAtStalk_of_semilinearEquiv
    e.symm rfl eQ hfin hproj hrank
  intro t
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_, ?_⟩
  · change Module.Projective Γ(Spec R, ⊤)
      ((Fin n → Γ(Spec R, ⊤)) ⧸
        x.affineKernelData.submodule ⟨⊤, isAffineOpen_top _⟩)
    rw [affineKernelData, SubmoduleSheafData.ofAffineSubmodule_submodule_top]
    exact htransport.2.1
  · intro p
    change Module.rankAtStalk
      ((Fin n → Γ(Spec R, ⊤)) ⧸
        x.affineKernelData.submodule ⟨⊤, isAffineOpen_top _⟩) p = q
    rw [affineKernelData, SubmoduleSheafData.ofAffineSubmodule_submodule_top]
    exact htransport.2.2 p

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Pull back a strict quotient of a canonical free sheaf along a morphism of
schemes. -/
noncomputable def pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : FreeQuotient q I Y) : FreeQuotient q I X where
  Q := (Modules.pullback f).obj x.Q
  isQuasicoherent :=
    haveI := x.isQuasicoherent
    inferInstance
  isProjectiveOfRank := by
    haveI := x.isQuasicoherent
    exact x.isProjectiveOfRank.pullback f
  π := (Modules.pullbackFreeIso f I).inv ≫ (Modules.pullback f).map x.π
  epi := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    letI : Epi x.π := x.epi
    letI : Epi ((Modules.pullback f).map x.π) := inferInstance
    letI : Epi (Modules.pullbackFreeIso f I).inv := inferInstance
    infer_instance

/-- On an arbitrary affine scheme, global kernel data with finite-projective
constant-rank quotient determine a strict quotient of the canonical finite free sheaf.
The construction first forms the associated quotient on the spectrum of global
sections and then transports it across `X.isoSpec`. -/
noncomputable def affineFreeQuotientOfKernelData {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (K : X.SubmoduleSheafData n)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    FreeQuotient q (ULift.{u} (Fin n)) X :=
  (affineFreeQuotientOfSubmodule
    (K.submodule ⟨⊤, isAffineOpen_top X⟩) q
    (Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)) hproj hrank).pullback
      X.isoSpec.hom

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Pullback preserves equivalence of strict free quotient presentations. -/
lemma pullback_r {X Y : Scheme.{u}} (f : X ⟶ Y) {x y : FreeQuotient q I Y}
    (h : (FreeQuotient.setoid q I Y).r x y) :
    (FreeQuotient.setoid q I X).r (x.pullback f) (y.pullback f) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(Modules.pullback f).mapIso e, ?_⟩
  simp only [pullback, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp, he]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Pulling a strict free quotient back successively is equivalent to pulling it back
along the composite morphism. -/
lemma pullback_comp_r {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : FreeQuotient q I Z) :
    (FreeQuotient.setoid q I X).r ((x.pullback g).pullback f)
      (x.pullback (f ≫ g)) := by
  refine ⟨(Modules.pullbackComp f g).app x.Q, ?_⟩
  change (((Modules.pullbackFreeIso f I).inv ≫
      (Modules.pullback f).map ((Modules.pullbackFreeIso g I).inv ≫
        (Modules.pullback g).map x.π)) ≫
      (Modules.pullbackComp f g).hom.app x.Q) =
    (Modules.pullbackFreeIso (f ≫ g) I).inv ≫
      (Modules.pullback (f ≫ g)).map x.π
  rw [Functor.map_comp, Category.assoc, Category.assoc, ← Functor.comp_map,
    (Modules.pullbackComp f g).hom.naturality x.π, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (Modules.pullback (f ≫ g)).map x.π)
    (Modules.pullbackFreeIso_comp f g I)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Pulling a strict free quotient back along an identity morphism gives an equivalent
presentation. -/
lemma pullback_id_r {X : Scheme.{u}} (x : FreeQuotient q I X) :
    (FreeQuotient.setoid q I X).r (x.pullback (𝟙 X)) x := by
  refine ⟨(Modules.pullbackId X).app x.Q, ?_⟩
  change ((Modules.pullbackFreeIso (𝟙 X) I).inv ≫
      (Modules.pullback (𝟙 X)).map x.π) ≫
    (Modules.pullbackId X).hom.app x.Q = x.π
  rw [Category.assoc, (Modules.pullbackId X).hom.naturality x.π,
    ← Category.assoc, Modules.pullbackFreeIso_id, Category.id_comp]
  rfl

/-- Pulling a strict quotient from an affine scheme to its canonical spectrum and
back gives an equivalent presentation. -/
lemma isoSpec_roundtrip_r {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q I X) :
    (FreeQuotient.setoid q I X).r
      ((x.pullback X.isoSpec.inv).pullback X.isoSpec.hom) x := by
  exact (FreeQuotient.setoid q I X).trans
    (pullback_comp_r X.isoSpec.hom X.isoSpec.inv x)
    ((FreeQuotient.setoid q I X).trans (by rw [X.isoSpec.hom_inv_id])
      (pullback_id_r x))

/-- The selected quotient-sheaf isomorphism for the canonical affine-spectrum
round trip. -/
noncomputable def isoSpecRoundtripIso {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q I X) :
    ((x.pullback X.isoSpec.inv).pullback X.isoSpec.hom).Q ≅ x.Q :=
  (isoSpec_roundtrip_r x).choose

/-- The affine-spectrum round-trip isomorphism commutes with quotient maps. -/
@[reassoc]
lemma isoSpecRoundtripIso_hom_comp {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q I X) :
    ((x.pullback X.isoSpec.inv).pullback X.isoSpec.hom).π ≫
      (isoSpecRoundtripIso x).hom = x.π :=
  (isoSpec_roundtrip_r x).choose_spec

/-- Transport a morphism from a finite free sheaf on an affine scheme to its
canonical spectrum. -/
noncomputable def homOnIsoSpec {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    {N : X.Modules}
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N) :
    SheafOfModules.free (R := (Spec (.of Γ(X, ⊤))).ringCatSheaf)
        (ULift.{u} (Fin n)) ⟶
      (Modules.pullback X.isoSpec.inv).obj N :=
  (Modules.pullbackFreeIso X.isoSpec.inv (ULift.{u} (Fin n))).inv ≫
    (Modules.pullback X.isoSpec.inv).map g

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Canonical-spectrum transport commutes with postcomposition. -/
lemma homOnIsoSpec_comp {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    {N P : X.Modules}
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
    (t : N ⟶ P) :
    homOnIsoSpec (g ≫ t) =
      homOnIsoSpec g ≫ (Modules.pullback X.isoSpec.inv).map t := by
  simp [homOnIsoSpec, Functor.map_comp, Category.assoc]

/-- Passing a quotient presentation to canonical-spectrum coordinates agrees with
the general coordinate map attached to its quotient morphism. -/
lemma moduleMapPiOfHom_homOnIsoSpec_π {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    moduleMapPiOfHom (homOnIsoSpec x.π) =
      (x.pullback X.isoSpec.inv).moduleMapPi :=
  rfl

/-- Affine quotient descent transported from the canonical spectrum back to the
original affine scheme. -/
noncomputable def descOfKernelLeOfIsAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) {N : X.Modules}
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
    (h : (x.pullback X.isoSpec.inv).kernelSubmodule ≤
      LinearMap.ker (moduleMapPiOfHom (homOnIsoSpec g))) : x.Q ⟶ N :=
  (isoSpecRoundtripIso x).inv ≫
    (Modules.pullback X.isoSpec.hom).map
      (descOfKernelLe (x.pullback X.isoSpec.inv) (homOnIsoSpec g) h) ≫
    (Modules.pullbackIsoSpecInvHomIso X).hom.app N

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The canonical finite-free identifications agree with the affine-spectrum
round-trip comparison. -/
lemma pullbackFreeIso_isoSpec_roundtrip {n : ℕ} {X : Scheme.{u}} [IsAffine X] :
    (Modules.pullbackFreeIso X.isoSpec.hom (ULift.{u} (Fin n))).inv ≫
        (Modules.pullback X.isoSpec.hom).map
          (Modules.pullbackFreeIso X.isoSpec.inv (ULift.{u} (Fin n))).inv ≫
        (Modules.pullbackIsoSpecInvHomIso X).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) =
      𝟙 _ := by
  let pc := Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv
  let pg := Modules.pullbackCongr X.isoSpec.hom_inv_id
  let pi := Modules.pullbackId X
  have hc := Modules.pullbackFreeIso_congr
    X.isoSpec.hom_inv_id.symm (ULift.{u} (Fin n))
  change (Modules.pullbackFreeIso (X.isoSpec.hom ≫ X.isoSpec.inv)
      (ULift.{u} (Fin n))).inv ≫ pg.hom.app _ =
    (Modules.pullbackFreeIso (𝟙 X) (ULift.{u} (Fin n))).inv at hc
  change (Modules.pullbackFreeIso X.isoSpec.hom (ULift.{u} (Fin n))).inv ≫
      (Modules.pullback X.isoSpec.hom).map
        (Modules.pullbackFreeIso X.isoSpec.inv (ULift.{u} (Fin n))).inv ≫
      pc.hom.app _ ≫ pg.hom.app _ ≫ pi.hom.app _ = 𝟙 _
  rw [← Category.assoc, ← Category.assoc,
    Modules.pullbackFreeIso_comp]
  have hc' := congrArg (fun k ↦ k ≫ pi.hom.app
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))) hc
  simpa only [Category.assoc] using hc'.trans
    (Modules.pullbackFreeIso_id X (ULift.{u} (Fin n)))

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The transported affine descent map recovers the original morphism. -/
@[reassoc (attr := simp)]
lemma comp_descOfKernelLeOfIsAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) {N : X.Modules}
    (g : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ N)
    (h : (x.pullback X.isoSpec.inv).kernelSubmodule ≤
      LinearMap.ker (moduleMapPiOfHom (homOnIsoSpec g))) :
    x.π ≫ descOfKernelLeOfIsAffine x g h = g := by
  let y := x.pullback X.isoSpec.inv
  let d := descOfKernelLe y (homOnIsoSpec g) h
  let e := isoSpecRoundtripIso x
  let eN := (Modules.pullbackIsoSpecInvHomIso X).app N
  have he : x.π ≫ e.inv = (y.pullback X.isoSpec.hom).π := by
    rw [← isoSpecRoundtripIso_hom_comp x, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  change x.π ≫ (e.inv ≫ (Modules.pullback X.isoSpec.hom).map d ≫ eN.hom) = g
  rw [← Category.assoc, he]
  change ((Modules.pullbackFreeIso X.isoSpec.hom (ULift.{u} (Fin n))).inv ≫
      (Modules.pullback X.isoSpec.hom).map y.π) ≫
        (Modules.pullback X.isoSpec.hom).map d ≫ eN.hom = g
  have hd := congrArg (fun k ↦ (Modules.pullback X.isoSpec.hom).map k)
    (comp_descOfKernelLe y (homOnIsoSpec g) h)
  rw [Functor.map_comp] at hd
  have hd' := congrArg (fun k ↦ k ≫ eN.hom) hd
  simp only [Category.assoc] at hd'
  rw [Category.assoc, hd']
  rw [homOnIsoSpec, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (Modules.pullbackIsoSpecInvHomIso X).hom.naturality g
  change (Modules.pullback X.isoSpec.hom).map
      ((Modules.pullback X.isoSpec.inv).map g) ≫ eN.hom =
    (Modules.pullbackIsoSpecInvHomIso X).hom.app _ ≫ g at hn
  let p := (Modules.pullbackFreeIso X.isoSpec.hom (ULift.{u} (Fin n))).inv ≫
    (Modules.pullback X.isoSpec.hom).map
      (Modules.pullbackFreeIso X.isoSpec.inv (ULift.{u} (Fin n))).inv
  change p ≫ ((Modules.pullback X.isoSpec.hom).map
      ((Modules.pullback X.isoSpec.inv).map g) ≫ eN.hom) = g
  rw [hn]
  have hp := pullbackFreeIso_isoSpec_roundtrip (n := n) (X := X)
  change p ≫ (Modules.pullbackIsoSpecInvHomIso X).hom.app
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) = 𝟙 _ at hp
  change (p ≫ (Modules.pullbackIsoSpecInvHomIso X).hom.app
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))) ≫ g = g
  have hpg := congrArg (fun k ↦ k ≫ g) hp
  simpa only [Category.assoc, Category.id_comp] using hpg
private lemma comp_prefix_two {C : Type*} [Category C]
    {A B C₁ D E F G : C}
    (d : A ⟶ B) (e : B ⟶ C₁) (p : C₁ ⟶ D) (a : D ⟶ E)
    (b : C₁ ⟶ F) (c : F ⟶ E) (r : F ⟶ G) (s : G ⟶ E)
    (h₁ : p ≫ a = b ≫ c) (h₂ : r ≫ s = c) :
    d ≫ (e ≫ (p ≫ a)) = ((d ≫ (e ≫ b)) ≫ r) ≫ s := by
  calc
    _ = d ≫ (e ≫ (b ≫ c)) := by rw [h₁]
    _ = d ≫ (e ≫ (b ≫ (r ≫ s))) := by rw [h₂]
    _ = ((d ≫ (e ≫ b)) ≫ r) ≫ s := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The presentation map of an affine pulled-back strict free quotient, transported
to scalar-extended global sections, is scalar extension of the original presentation
after the canonical free-source coordinate comparison. -/
lemma pullback_freePresentation_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : FreeQuotient q I (Spec R)) :
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    (freeModuleSpecΓIso (R := S) I).hom ≫
        moduleSpecΓFunctor.map (Modules.pullbackFreeIso (Spec.map f) I).inv ≫
          moduleSpecΓFunctor.map ((Modules.pullback (Spec.map f)).map x.π) ≫
            (pullbackQuasicoherentSectionsIso f x.Q).hom =
      (freePullbackCoordinateIso f I).hom ≫
        (ModuleCat.extendScalars f.hom).map
          ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π) := by
  let _ : x.Q.IsQuasicoherent := x.isQuasicoherent
  have hn := pullbackQuasicoherentSectionsIso_naturality f x.π
  have hr :
      (ModuleCat.extendScalars f.hom).map (freeModuleSpecΓIso (R := R) I).inv ≫
        (ModuleCat.extendScalars f.hom).map
          ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π) =
      (ModuleCat.extendScalars f.hom).map (moduleSpecΓFunctor.map x.π) := by
    rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
  dsimp only [freePullbackCoordinateIso, freePullbackSectionsIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simpa only [Category.assoc] using comp_prefix_two
    (freeModuleSpecΓIso (R := S) I).hom
    (moduleSpecΓFunctor.map (Modules.pullbackFreeIso (Spec.map f) I).inv)
    (moduleSpecΓFunctor.map ((Modules.pullback (Spec.map f)).map x.π))
    (pullbackQuasicoherentSectionsIso f x.Q).hom
    (pullbackQuasicoherentSectionsIso f
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) I)).hom
    ((ModuleCat.extendScalars f.hom).map (moduleSpecΓFunctor.map x.π))
    ((ModuleCat.extendScalars f.hom).map (freeModuleSpecΓIso (R := R) I).inv)
      ((ModuleCat.extendScalars f.hom).map
      ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π)) hn hr

/-- The presentation map on an affine pullback, with its target transported to
scalar-extended global sections. -/
noncomputable def pullbackModuleMapTransported {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q I (Spec R)) :
    (I →₀ S) →ₗ[S]
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj x.Q) := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact ((freeModuleSpecΓIso (R := S) I).hom ≫
    moduleSpecΓFunctor.map (Modules.pullbackFreeIso (Spec.map f) I).inv ≫
      moduleSpecΓFunctor.map ((Modules.pullback (Spec.map f)).map x.π) ≫
        (pullbackQuasicoherentSectionsIso f x.Q).hom).hom

/-- Scalar extension of the module presentation underlying an affine strict free
quotient, expressed in canonical free coordinates. -/
noncomputable def scalarExtendedModuleMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q I (Spec R)) :
    (I →₀ S) →ₗ[S]
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj x.Q) :=
  ((ModuleCat.extendScalars f.hom).map
    ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π)).hom.comp
    (ModuleCat.extendScalarsFinsuppEquiv f I).symm.toLinearMap

/-- Scalar extension of an affine presentation after the canonical coordinate
comparison for the pulled-back free sheaf. -/
noncomputable def scalarExtendedAfterCoordinateMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : FreeQuotient q I (Spec R)) :
    (I →₀ S) →ₗ[S]
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj x.Q) :=
  ((freePullbackCoordinateIso f I).hom ≫
    (ModuleCat.extendScalars f.hom).map
      ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π)).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Transporting the presentation of an affine pullback gives scalar extension
after the canonical coordinate comparison. -/
lemma pullbackModuleMapTransported_eq {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q I (Spec R)) :
    pullbackModuleMapTransported f x = scalarExtendedAfterCoordinateMap f x := by
  let _ : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact congrArg ModuleCat.Hom.hom (pullback_freePresentation_naturality f x)

/-- The canonical free-source coordinate comparison does not change the kernel
of a scalar-extended affine presentation. -/
lemma ker_pullbackModuleMapTransported {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q I (Spec R)) :
    LinearMap.ker (pullbackModuleMapTransported f x) =
      LinearMap.ker (scalarExtendedModuleMap f x) := by
  rw [pullbackModuleMapTransported_eq]
  have h : scalarExtendedAfterCoordinateMap f x =
      (scalarExtendedModuleMap f x).comp
        (freePullbackCoordinateLinearEquiv f I).toLinearMap := by
    apply LinearMap.ext
    intro z
    have hz : (ModuleCat.extendScalarsFinsuppEquiv f I).symm
          (freePullbackCoordinateLinearEquiv f I z) =
        (freePullbackCoordinateIso f I).toLinearEquiv z := by
      simp [freePullbackCoordinateLinearEquiv]
    simp only [scalarExtendedAfterCoordinateMap, scalarExtendedModuleMap,
      LinearMap.comp_apply]
    exact (congrArg
      ((ModuleCat.extendScalars f.hom).map
        ((freeModuleSpecΓIso (R := R) I).hom ≫ moduleSpecΓFunctor.map x.π)).hom hz).symm
  rw [h]
  exact ker_comp_freePullbackCoordinateLinearEquiv f I (scalarExtendedModuleMap f x)

noncomputable def scalarExtendedModuleMapPi
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    (Fin n → S) →ₗ[S]
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj x.Q) :=
  (scalarExtendedModuleMap f x).comp
    (uliftFinFinsuppEquivPi n).symm.toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma scalarExtendedModuleMapPi_single
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) (i : Fin n) (s : S) :
    letI : Algebra R S := f.hom.toAlgebra
    scalarExtendedModuleMapPi f x (Pi.single i s) =
      s ⊗ₜ[R] x.moduleMapPi (Pi.single i 1) := by
  let _ : Algebra R S := f.hom.toAlgebra
  have hcoord : (uliftFinFinsuppEquivPi (R := S) n).symm (Pi.single i s) =
      Finsupp.single (ULift.up i) s := by
    ext j
    simp [uliftFinFinsuppEquivPi]
  have htensor : (ModuleCat.extendScalarsFinsuppEquiv f (ULift (Fin n))).symm
      (Finsupp.single (ULift.up i) s) =
      s ⊗ₜ[R, f.hom] Finsupp.single (ULift.up i) 1 := by
    apply (ModuleCat.extendScalarsFinsuppEquiv f (ULift (Fin n))).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (ModuleCat.extendScalarsFinsuppEquiv_tmul_single
      f (ULift (Fin n)) (ULift.up i) s).symm
  change ((ModuleCat.extendScalars f.hom).map
      ((freeModuleSpecΓIso (R := R) (ULift (Fin n))).hom ≫
        moduleSpecΓFunctor.map x.π)).hom
        ((ModuleCat.extendScalarsFinsuppEquiv f (ULift (Fin n))).symm
          ((uliftFinFinsuppEquivPi (R := S) n).symm (Pi.single i s))) = _
  rw [hcoord, htensor, ModuleCat.ExtendScalars.map_tmul]
  have hcoordR : (uliftFinFinsuppEquivPi (R := R) n).symm (Pi.single i 1) =
      Finsupp.single (ULift.up i) 1 := by
    ext j
    simp [uliftFinFinsuppEquivPi]
  have hsource :
      ((freeModuleSpecΓIso (R := R) (ULift (Fin n))).hom ≫
        moduleSpecΓFunctor.map x.π).hom (Finsupp.single (ULift.up i) 1) =
        x.moduleMapPi (Pi.single i 1) := by
    calc
      _ = x.moduleMap (Finsupp.single (ULift.up i) 1) := rfl
      _ = x.moduleMap
          ((uliftFinFinsuppEquivPi (R := R) n).symm (Pi.single i 1)) :=
        congrArg x.moduleMap hcoordR.symm
      _ = _ := rfl
  rw [hsource]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma scalarExtendedModuleMapPi_eq_baseChangePi
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : Algebra R S := f.hom.toAlgebra
    scalarExtendedModuleMapPi f x = LinearMap.baseChangePi S x.moduleMapPi := by
  let _ : Algebra R S := f.hom.toAlgebra
  apply LinearMap.pi_ext
  intro i s
  rw [scalarExtendedModuleMapPi_single]
  show s ⊗ₜ[R] x.moduleMapPi (Pi.single i 1) =
    (LinearMap.baseChange S x.moduleMapPi)
      ((TensorProduct.piScalarRight R S S (Fin n)).symm (Pi.single i s))
  rw [TensorProduct.piScalarRight_symm_single, LinearMap.baseChange_tmul]
noncomputable def pullbackModuleMapTransportedPi
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    (Fin n → S) →ₗ[S]
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj x.Q) :=
  (pullbackModuleMapTransported f x).comp
    (uliftFinFinsuppEquivPi n).symm.toLinearMap

/-- The kernel of the transported affine pullback presentation is the kernel of
the standard base-changed finite presentation. -/
lemma ker_pullbackModuleMapTransportedPi
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : Algebra R S := f.hom.toAlgebra
    LinearMap.ker (pullbackModuleMapTransportedPi f x) =
      LinearMap.ker (LinearMap.baseChangePi S x.moduleMapPi) := by
  let _ : Algebra R S := f.hom.toAlgebra
  rw [← scalarExtendedModuleMapPi_eq_baseChangePi]
  ext z
  change
    (uliftFinFinsuppEquivPi n).symm z ∈
        LinearMap.ker (pullbackModuleMapTransported f x) ↔
      (uliftFinFinsuppEquivPi n).symm z ∈
        LinearMap.ker (scalarExtendedModuleMap f x)
  rw [ker_pullbackModuleMapTransported]

/-- The kernel of a transported affine pullback presentation is the componentwise
scalar-extension span of the original affine kernel. -/
lemma ker_pullbackModuleMapTransportedPi_eq_span
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : Algebra R S := f.hom.toAlgebra
    LinearMap.ker (pullbackModuleMapTransportedPi f x) =
      Submodule.span S ((fun w ↦ fun i ↦ f.hom (w i)) ''
        (x.kernelSubmodule : Set (Fin n → R))) := by
  let _ : Algebra R S := f.hom.toAlgebra
  rw [ker_pullbackModuleMapTransportedPi, ker_baseChangePi_moduleMapPi]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma pullbackModuleMapTransportedPi_eq
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    pullbackModuleMapTransportedPi f x =
      (pullbackQuasicoherentSectionsIso f x.Q).hom.hom.comp
        ((x.pullback (Spec.map f)).moduleMapPi) := by
  let _ : x.Q.IsQuasicoherent := x.isQuasicoherent
  apply LinearMap.ext
  intro z
  simp only [pullbackModuleMapTransportedPi, pullbackModuleMapTransported,
    LinearMap.comp_apply]
  rfl

lemma kernelSubmodule_pullback_specMap
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    (x.pullback (Spec.map f)).kernelSubmodule =
      LinearMap.ker (pullbackModuleMapTransportedPi f x) := by
  let _ : x.Q.IsQuasicoherent := x.isQuasicoherent
  rw [kernelSubmodule, pullbackModuleMapTransportedPi_eq]
  ext z
  simp only [LinearMap.mem_ker]
  exact (pullbackQuasicoherentSectionsIso f x.Q).toLinearEquiv.map_eq_zero_iff.symm

lemma kernelSubmodule_pullback_specMap_eq_span
    {n : ℕ} {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    letI : Algebra R S := f.hom.toAlgebra
    (x.pullback (Spec.map f)).kernelSubmodule =
      Submodule.span S ((fun w ↦ fun i ↦ f.hom (w i)) ''
        (x.kernelSubmodule : Set (Fin n → R))) := by
  let _ : Algebra R S := f.hom.toAlgebra
  rw [kernelSubmodule_pullback_specMap,
    ker_pullbackModuleMapTransportedPi_eq_span]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Equivalent affine free quotient presentations have the same kernel in the
coordinate free module. -/
lemma kernelSubmodule_eq_of_r {n : ℕ} {R : CommRingCat.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)}
    (h : (FreeQuotient.setoid q (ULift.{u} (Fin n)) (Spec R)).r x y) :
    x.kernelSubmodule = y.kernelSubmodule := by
  obtain ⟨e, he⟩ := h
  have hmap : (moduleSpecΓFunctor.map e.hom).hom.comp x.moduleMapPi = y.moduleMapPi := by
    apply LinearMap.ext
    intro z
    have he' := congrArg (fun k ↦ moduleSpecΓFunctor.map k) he
    rw [Functor.map_comp] at he'
    have he'' :
        (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
            moduleSpecΓFunctor.map x.π ≫ moduleSpecΓFunctor.map e.hom =
          (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom ≫
            moduleSpecΓFunctor.map y.π := by
      rw [he']
    simpa [moduleMapPi, moduleMap, Category.assoc] using congrArg
      (fun k : ModuleCat.of R (ULift.{u} (Fin n) →₀ R) ⟶
        moduleSpecΓFunctor.obj y.Q ↦
          k.hom ((uliftFinFinsuppEquivPi n).symm z)) he''
  apply le_antisymm
  · intro z hz
    rw [kernelSubmodule, LinearMap.mem_ker] at hz ⊢
    rw [← hmap, LinearMap.comp_apply, hz, map_zero]
  · intro z hz
    rw [kernelSubmodule, LinearMap.mem_ker] at hz ⊢
    have hz' : (moduleSpecΓFunctor.map e.hom).hom (x.moduleMapPi z) = 0 := by
      calc
        _ = y.moduleMapPi z := LinearMap.congr_fun hmap z
        _ = 0 := hz
    apply (ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map e.hom)).mp inferInstance
    simpa using hz'

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Conversely, affine strict quotient presentations with the same kernel are
equivalent.  Quasicoherence identifies each target with the tilde sheaf of its global
sections, while the first isomorphism theorem identifies those global sections through
the common quotient of the finite free module. -/
lemma r_of_kernelSubmodule_eq {n : ℕ} {R : CommRingCat.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)}
    (hker : x.kernelSubmodule = y.kernelSubmodule) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) (Spec R)).r x y := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : y.Q.IsQuasicoherent := y.isQuasicoherent
  let Kx := x.kernelSubmodule
  let Ky := y.kernelSubmodule
  let ek : ((Fin n → R) ⧸ Kx) ≃ₗ[R] ((Fin n → R) ⧸ Ky) :=
    Submodule.quotEquivOfEq Kx Ky hker
  let eLinear := x.affineKernelQuotientEquiv.symm.trans
    (ek.trans y.affineKernelQuotientEquiv)
  let eΓIso : moduleSpecΓFunctor.obj x.Q ≅ moduleSpecΓFunctor.obj y.Q :=
    eLinear.toModuleIso
  let eΓ := eΓIso.hom
  let η := Scheme.Modules.fromTildeΓNatTrans (R := R)
  letI : IsIso (η.app x.Q) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent x.Q
  letI : IsIso (η.app y.Q) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent y.Q
  let F : (Spec R).Modules := SheafOfModules.free
    (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n))
  letI : F.IsQuasicoherent :=
    free_isQuasicoherent (R := R) (ULift.{u} (Fin n))
  letI : ((𝟭 ((Spec R).Modules)).obj F).IsQuasicoherent := by
    change F.IsQuasicoherent
    infer_instance
  letI : IsIso (η.app F) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  let e : x.Q ≅ y.Q :=
    (asIso (η.app x.Q)).symm ≪≫
      (tilde.functor R).mapIso eΓIso ≪≫ asIso (η.app y.Q)
  refine ⟨e, ?_⟩
  have hmodule : moduleSpecΓFunctor.map x.π ≫ eΓ =
      moduleSpecΓFunctor.map y.π := by
    rw [← cancel_epi (freeModuleSpecΓIso (R := R) (ULift.{u} (Fin n))).hom]
    apply ModuleCat.Hom.ext
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (uliftFinFinsuppEquivPi n).symm.surjective z
    change eΓ.hom (x.moduleMapPi v) = y.moduleMapPi v
    change eLinear (x.moduleMapPi v) = y.moduleMapPi v
    have hxmk : x.affineKernelQuotientEquiv.symm (x.moduleMapPi v) =
        Submodule.Quotient.mk v := by
      apply x.affineKernelQuotientEquiv.injective
      rw [x.affineKernelQuotientEquiv.apply_symm_apply,
        affineKernelQuotientEquiv_mk]
    calc
      _ = eLinear (x.affineKernelQuotientEquiv (Submodule.Quotient.mk v)) := by
        rw [affineKernelQuotientEquiv_mk]
      _ = y.affineKernelQuotientEquiv (ek (Submodule.Quotient.mk v)) := by
        change y.affineKernelQuotientEquiv
          (ek (x.affineKernelQuotientEquiv.symm (x.moduleMapPi v))) = _
        rw [hxmk]
      _ = y.affineKernelQuotientEquiv (Submodule.Quotient.mk v) := by
        rw [Submodule.quotEquivOfEq_mk]
      _ = y.moduleMapPi v := affineKernelQuotientEquiv_mk y v
  have hηx : (tilde.functor R).map (moduleSpecΓFunctor.map x.π) ≫ η.app x.Q =
      η.app F ≫ x.π := by
    simpa [F] using η.naturality x.π
  have hηy : (tilde.functor R).map (moduleSpecΓFunctor.map y.π) ≫ η.app y.Q =
      η.app F ≫ y.π := by
    simpa [F] using η.naturality y.π
  rw [← cancel_epi (η.app F)]
  change (η.app F ≫ x.π) ≫ inv (η.app x.Q) ≫
      (tilde.functor R).map eΓ ≫ η.app y.Q = η.app F ≫ y.π
  rw [← hηx]
  rw [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, hmodule, hηy]

/-- Equivalent affine free quotient presentations determine the same intrinsic
quasicoherent kernel datum. -/
lemma affineKernelData_eq_of_r {n : ℕ} {R : CommRingCat.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)}
    (h : (FreeQuotient.setoid q (ULift.{u} (Fin n)) (Spec R)).r x y) :
    x.affineKernelData = y.affineKernelData := by
  rw [affineKernelData, affineKernelData, intrinsicKernelSubmodule,
    intrinsicKernelSubmodule, kernelSubmodule_eq_of_r h]

/-- Pulling the canonical affine quotient back to the canonical spectrum recovers
the original top-section kernel literally. -/
lemma affineFreeQuotientOfKernelData_pullback_isoSpec_inv_kernelSubmodule
    {X : Scheme.{u}} [IsAffine X] {n q : ℕ} (K : X.SubmoduleSheafData n)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    ((affineFreeQuotientOfKernelData K hproj hrank).pullback
      X.isoSpec.inv).kernelSubmodule =
        K.submodule ⟨⊤, isAffineOpen_top X⟩ := by
  let L := K.submodule ⟨⊤, isAffineOpen_top X⟩
  let y := affineFreeQuotientOfSubmodule L q
    (Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)) hproj hrank
  let x := y.pullback X.isoSpec.hom
  have hxy : (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).r
      (x.pullback X.isoSpec.inv) y := by
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans
      (pullback_comp_r X.isoSpec.inv X.isoSpec.hom y)
      ((FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans
        (by rw [X.isoSpec.inv_hom_id]) (pullback_id_r y))
  change (x.pullback X.isoSpec.inv).kernelSubmodule = L
  rw [kernelSubmodule_eq_of_r hxy]
  exact affineFreeQuotientOfSubmodule_kernelSubmodule L
    (Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)) hproj hrank

/-- The intrinsic affine kernel datum commutes with pullback along a morphism of
affine spectra. -/
lemma affineKernelData_comap_specMap {n : ℕ} {R S : CommRingCat.{u}}
    (f : R ⟶ S) (x : FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    x.affineKernelData.comap (Spec.map f) =
      (x.pullback (Spec.map f)).affineKernelData := by
  rw [← SubmoduleSheafData.ofAffineSubmodule_submodule
      (x.affineKernelData.comap (Spec.map f)),
    ← SubmoduleSheafData.ofAffineSubmodule_submodule
      (x.pullback (Spec.map f)).affineKernelData]
  congr 1
  rw [SubmoduleSheafData.comap_submodule_eq_span x.affineKernelData (Spec.map f)
    (U' := ⟨⊤, isAffineOpen_top _⟩) (V := ⟨⊤, isAffineOpen_top _⟩)
    (by intro z _; trivial)]
  rw [affineKernelData, SubmoduleSheafData.ofAffineSubmodule_submodule_top,
    affineKernelData, SubmoduleSheafData.ofAffineSubmodule_submodule_top]
  rw [intrinsicKernelSubmodule, intrinsicKernelSubmodule,
    kernelSubmodule_pullback_specMap_eq_span]
  rw [Submodule.mapPiRingEquiv_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i ↦ f.hom (v i), ⟨v, hv, rfl⟩, ?_⟩
    funext i
    change (Scheme.ΓSpecIso S).inv.hom (f.hom (v i)) =
      (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom (v i))
    exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of Γ(Spec S, ⊤) ↦
      k.hom (v i)) (Scheme.ΓSpecIso_inv_naturality f)
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i ↦ (Scheme.ΓSpecIso R).inv.hom (v i), ⟨v, hv, rfl⟩, ?_⟩
    funext i
    change (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom (v i)) =
      (Scheme.ΓSpecIso S).inv.hom (f.hom (v i))
    exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of Γ(Spec S, ⊤) ↦
      k.hom (v i)) (Scheme.ΓSpecIso_inv_naturality f).symm

/-- The intrinsic kernel datum of a strict free quotient on an affine scheme, obtained
by transport through the canonical isomorphism with its spectrum of global sections. -/
noncomputable def affineKernelDataOfIsAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) : X.SubmoduleSheafData n :=
  (x.pullback X.isoSpec.inv).affineKernelData.comap X.isoSpec.hom

/-- Equivalent strict free quotient presentations on an affine scheme determine the
same intrinsic kernel datum. -/
lemma affineKernelDataOfIsAffine_eq_of_r {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y) :
    x.affineKernelDataOfIsAffine = y.affineKernelDataOfIsAffine := by
  unfold affineKernelDataOfIsAffine
  rw [affineKernelData_eq_of_r (pullback_r X.isoSpec.inv h)]

/-- The intrinsic kernel datum on affine schemes commutes with arbitrary affine
pullback. -/
lemma affineKernelDataOfIsAffine_comap {n : ℕ} {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : FreeQuotient q (ULift.{u} (Fin n)) Y) :
    x.affineKernelDataOfIsAffine.comap f =
      (x.pullback f).affineKernelDataOfIsAffine := by
  have hp₁ := pullback_comp_r (Spec.map f.appTop) Y.isoSpec.inv x
  have hp₂ := pullback_comp_r X.isoSpec.inv f x
  have hp : (FreeQuotient.setoid q (ULift.{u} (Fin n)) (Spec Γ(X, ⊤))).r
      ((x.pullback Y.isoSpec.inv).pullback (Spec.map f.appTop))
      ((x.pullback f).pullback X.isoSpec.inv) := by
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans hp₁
      ((FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans
        (by rw [Scheme.isoSpec_inv_naturality f])
        ((FreeQuotient.setoid q (ULift.{u} (Fin n)) _).symm hp₂))
  calc
    x.affineKernelDataOfIsAffine.comap f =
        (x.pullback Y.isoSpec.inv).affineKernelData.comap
          (f ≫ Y.isoSpec.hom) :=
      ((x.pullback Y.isoSpec.inv).affineKernelData.comap_comp f Y.isoSpec.hom).symm
    _ = (x.pullback Y.isoSpec.inv).affineKernelData.comap
          (X.isoSpec.hom ≫ Spec.map f.appTop) := by
      exact congrArg
        (fun k ↦ (x.pullback Y.isoSpec.inv).affineKernelData.comap k)
        (Scheme.toSpecΓ_naturality f)
    _ = ((x.pullback Y.isoSpec.inv).affineKernelData.comap
          (Spec.map f.appTop)).comap X.isoSpec.hom :=
      (x.pullback Y.isoSpec.inv).affineKernelData.comap_comp _ _
    _ = ((x.pullback Y.isoSpec.inv).pullback
          (Spec.map f.appTop)).affineKernelData.comap X.isoSpec.hom := by
      rw [affineKernelData_comap_specMap]
    _ = ((x.pullback f).pullback X.isoSpec.inv).affineKernelData.comap
          X.isoSpec.hom := by
      rw [affineKernelData_eq_of_r hp]
    _ = (x.pullback f).affineKernelDataOfIsAffine := rfl

/-- Intrinsic affine kernel data obtained from a common quotient agree on an affine
common pullback. -/
lemma affineKernelDataOfIsAffine_compatible_of_isAffine {n : ℕ}
    {X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) (h : Z ⟶ X)
    (W : Scheme.{u}) [IsAffine W] (a : W ⟶ Y) (b : W ⟶ Z)
    (hab : a ≫ g = b ≫ h) :
    (x.pullback g).affineKernelDataOfIsAffine.comap a =
      (x.pullback h).affineKernelDataOfIsAffine.comap b := by
  have hg := pullback_comp_r a g x
  have hh := pullback_comp_r b h x
  have hp : (FreeQuotient.setoid q (ULift.{u} (Fin n)) W).r
      ((x.pullback g).pullback a) ((x.pullback h).pullback b) := by
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) W).trans hg
      ((FreeQuotient.setoid q (ULift.{u} (Fin n)) W).trans
        (by rw [hab])
        ((FreeQuotient.setoid q (ULift.{u} (Fin n)) W).symm hh))
  calc
    (x.pullback g).affineKernelDataOfIsAffine.comap a =
        ((x.pullback g).pullback a).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_comap a (x.pullback g)
    _ = ((x.pullback h).pullback b).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_eq_of_r hp
    _ = (x.pullback h).affineKernelDataOfIsAffine.comap b :=
      (affineKernelDataOfIsAffine_comap b (x.pullback h)).symm

/-- Intrinsic affine kernel data obtained from a common quotient agree after an
arbitrary common pullback. -/
lemma affineKernelDataOfIsAffine_compatible {n : ℕ} {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) (h : Z ⟶ X)
    (W : Scheme.{u}) (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ g = b ≫ h) :
    (x.pullback g).affineKernelDataOfIsAffine.comap a =
      (x.pullback h).affineKernelDataOfIsAffine.comap b := by
  apply SubmoduleSheafData.eq_of_comap_eq_openCover W.affineCover
  intro i
  let c := W.affineCover.f i
  calc
    ((x.pullback g).affineKernelDataOfIsAffine.comap a).comap c =
        (x.pullback g).affineKernelDataOfIsAffine.comap (c ≫ a) :=
      ((x.pullback g).affineKernelDataOfIsAffine.comap_comp c a).symm
    _ = (x.pullback h).affineKernelDataOfIsAffine.comap (c ≫ b) :=
      affineKernelDataOfIsAffine_compatible_of_isAffine x g h _ (c ≫ a) (c ≫ b)
        (by rw [Category.assoc, Category.assoc, hab])
    _ = ((x.pullback h).affineKernelDataOfIsAffine.comap b).comap c :=
      (x.pullback h).affineKernelDataOfIsAffine.comap_comp c b

/-- Restrict a strict free quotient to an affine open and transport it to the
canonical spectrum of that open's ring of functions. -/
noncomputable def affineCoordinatePullback {X : Scheme.{u}}
    (x : FreeQuotient q I X) (U : X.affineOpens) :
    FreeQuotient q I (Spec (.of Γ(X, U.1))) :=
  (x.pullback U.1.ι).pullback U.2.isoSpec.inv

/-- The quotient sheaf in the affine-coordinate pullback is definitionally the
affine coordinate sheaf of the original quotient. -/
lemma affineCoordinatePullback_Q {X : Scheme.{u}}
    (x : FreeQuotient q I X) (U : X.affineOpens) :
    (x.affineCoordinatePullback U).Q = Modules.affineCoordinateSheaf x.Q U :=
  rfl

/-- Every point of a strict finite-free quotient has an affine coordinate chart whose
kernel datum satisfies the absolute Grassmannian rank condition. -/
lemma exists_affineCoordinatePullback_kernelData {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (t : X) :
    ∃ (U : X.affineOpens) (_ : t ∈ U.1),
      (x.affineCoordinatePullback U).affineKernelData.QuotientProjectiveOfRank q := by
  obtain ⟨U, htU, hfin, hproj, hrank⟩ := x.isProjectiveOfRank t
  have hcoord := Modules.affineCoordinateModule_finite_projective_rank
    x.Q U hfin hproj hrank
  refine ⟨U, htU, ?_⟩
  apply affineKernelData_quotientProjectiveOfRank_of_top
    (x.affineCoordinatePullback U) hcoord.1 hcoord.2.1 hcoord.2.2

/-- The affine kernel datum transported from the coordinate spectrum back to the
chosen affine open. -/
noncomputable def affineOpenKernelData {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U : X.affineOpens) :
    U.1.toScheme.SubmoduleSheafData n :=
  (x.affineCoordinatePullback U).affineKernelData.comap U.2.isoSpec.hom

/-- The affine-open kernel construction agrees with the intrinsic affine kernel datum
of the restricted quotient.  This comparison transports between the section-ring
coordinates `Γ(X, U)` and `Γ(U, ⊤)` through `U.topIso`. -/
lemma affineOpenKernelData_eq_affineKernelDataOfIsAffine {n : ℕ}
    {X : Scheme.{u}} (x : FreeQuotient q (ULift.{u} (Fin n)) X)
    (U : X.affineOpens) :
    x.affineOpenKernelData U =
      (x.pullback U.1.ι).affineKernelDataOfIsAffine := by
  let D := U.1.toScheme
  let y := x.pullback U.1.ι
  let φ : CommRingCat.of Γ(D, ⊤) ⟶ CommRingCat.of Γ(X, U.1) := U.1.topIso.hom
  let ψ : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of Γ(D, ⊤) := U.1.topIso.inv
  let y₀ := y.pullback D.isoSpec.inv
  have hφψ : Spec.map ψ ≫ Spec.map φ = 𝟙 _ := by
    rw [← Spec.map_comp, show φ ≫ ψ = 𝟙 _ from U.1.topIso.hom_inv_id,
      Spec.map_id]
  have hq := pullback_comp_r (Spec.map φ) D.isoSpec.inv y
  have hz : x.affineCoordinatePullback U =
      y.pullback (Spec.map φ ≫ D.isoSpec.inv) := by
    rfl
  change (x.affineCoordinatePullback U).affineKernelData.comap U.2.isoSpec.hom = _
  rw [hz]
  have hdata : (y.pullback (Spec.map φ ≫ D.isoSpec.inv)).affineKernelData =
      (y₀.pullback (Spec.map φ)).affineKernelData :=
    affineKernelData_eq_of_r
      ((FreeQuotient.setoid q (ULift.{u} (Fin n)) _).symm hq)
  have hc := pullback_comp_r (Spec.map ψ) (Spec.map φ) y₀
  have hid : (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).r
      ((y₀.pullback (Spec.map φ)).pullback (Spec.map ψ)) y₀ := by
    rw [hφψ] at hc
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans hc
      (pullback_id_r y₀)
  calc
    (y.pullback (Spec.map φ ≫ D.isoSpec.inv)).affineKernelData.comap U.2.isoSpec.hom =
        (y₀.pullback (Spec.map φ)).affineKernelData.comap
          (D.isoSpec.hom ≫ Spec.map ψ) := by
      rw [hdata]
      rfl
    _ = ((y₀.pullback (Spec.map φ)).affineKernelData.comap
          (Spec.map ψ)).comap D.isoSpec.hom :=
      (y₀.pullback (Spec.map φ)).affineKernelData.comap_comp _ _
    _ = ((y₀.pullback (Spec.map φ)).pullback
          (Spec.map ψ)).affineKernelData.comap D.isoSpec.hom := by
      rw [affineKernelData_comap_specMap]
    _ = y₀.affineKernelData.comap D.isoSpec.hom := by
      rw [affineKernelData_eq_of_r hid]
    _ = (x.pullback U.1.ι).affineKernelDataOfIsAffine := rfl

/-- Affine-open kernel data agree after pullback to an affine common overlap. -/
lemma affineOpenKernelData_compatible_of_isAffine {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U V : X.affineOpens)
    (W : Scheme.{u}) [IsAffine W] (a : W ⟶ U.1.toScheme)
    (b : W ⟶ V.1.toScheme) (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    (x.affineOpenKernelData U).comap a =
      (x.affineOpenKernelData V).comap b := by
  have hu := pullback_comp_r a U.1.ι x
  have hv := pullback_comp_r b V.1.ι x
  have hq : (FreeQuotient.setoid q (ULift.{u} (Fin n)) W).r
      ((x.pullback U.1.ι).pullback a)
      ((x.pullback V.1.ι).pullback b) := by
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) W).trans hu
      ((FreeQuotient.setoid q (ULift.{u} (Fin n)) W).trans
        (by rw [hab])
        ((FreeQuotient.setoid q (ULift.{u} (Fin n)) W).symm hv))
  calc
    (x.affineOpenKernelData U).comap a =
        (x.pullback U.1.ι).affineKernelDataOfIsAffine.comap a := by
      rw [affineOpenKernelData_eq_affineKernelDataOfIsAffine]
    _ = ((x.pullback U.1.ι).pullback a).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_comap a (x.pullback U.1.ι)
    _ = ((x.pullback V.1.ι).pullback b).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_eq_of_r hq
    _ = (x.pullback V.1.ι).affineKernelDataOfIsAffine.comap b :=
      (affineKernelDataOfIsAffine_comap b (x.pullback V.1.ι)).symm
    _ = (x.affineOpenKernelData V).comap b := by
      rw [affineOpenKernelData_eq_affineKernelDataOfIsAffine]

/-- Affine-open kernel data agree after arbitrary pullback to a common overlap. -/
lemma affineOpenKernelData_compatible {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U V : X.affineOpens)
    (W : Scheme.{u}) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    (x.affineOpenKernelData U).comap a =
      (x.affineOpenKernelData V).comap b := by
  apply SubmoduleSheafData.eq_of_comap_eq_openCover W.affineCover
  intro i
  let c := W.affineCover.f i
  calc
    ((x.affineOpenKernelData U).comap a).comap c =
        (x.affineOpenKernelData U).comap (c ≫ a) :=
      ((x.affineOpenKernelData U).comap_comp c a).symm
    _ = (x.affineOpenKernelData V).comap (c ≫ b) :=
      affineOpenKernelData_compatible_of_isAffine x U V _ (c ≫ a) (c ≫ b)
        (by rw [Category.assoc, Category.assoc, hab])
    _ = ((x.affineOpenKernelData V).comap b).comap c :=
      (x.affineOpenKernelData V).comap_comp c b

/-- On every vector-bundle chart supplied by the quotient, the transported affine
kernel datum is an absolute Grassmannian point. -/
lemma exists_affineOpenKernelData_quotientProjectiveOfRank {n : ℕ}
    {X : Scheme.{u}} (x : FreeQuotient q (ULift.{u} (Fin n)) X) (t : X) :
    ∃ (U : X.affineOpens) (_ : t ∈ U.1),
      (x.affineOpenKernelData U).QuotientProjectiveOfRank q := by
  obtain ⟨U, htU, hK⟩ := x.exists_affineCoordinatePullback_kernelData t
  exact ⟨U, htU, hK.comap U.2.isoSpec.hom⟩

/-- A chosen affine neighborhood at `t` on which the quotient presentation has a
rank-certified kernel datum. -/
noncomputable def kernelChart {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (t : X) : X.affineOpens :=
  (x.exists_affineOpenKernelData_quotientProjectiveOfRank t).choose

lemma mem_kernelChart {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (t : X) :
    t ∈ (x.kernelChart t).1 :=
  (x.exists_affineOpenKernelData_quotientProjectiveOfRank t).choose_spec.choose

lemma affineOpenKernelData_kernelChart_quotientProjectiveOfRank {n : ℕ}
    {X : Scheme.{u}} (x : FreeQuotient q (ULift.{u} (Fin n)) X) (t : X) :
    (x.affineOpenKernelData (x.kernelChart t)).QuotientProjectiveOfRank q :=
  (x.exists_affineOpenKernelData_quotientProjectiveOfRank t).choose_spec.choose_spec

/-- The chosen affine kernel charts form a Zariski open cover. -/
noncomputable def kernelChartCover {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) : X.OpenCover.{u + 1} :=
  X.openCoverOfIsOpenCover
    (fun t : ULift.{u + 1} X ↦ (x.kernelChart t.down).1) (by
    rw [TopologicalSpace.IsOpenCover]
    apply top_unique
    intro t
    simp only [Opens.mem_iSup]
    intro _
    exact ⟨ULift.up t, x.mem_kernelChart t⟩)

/-- The global quasicoherent kernel datum obtained by gluing the affine kernels of a
strict free quotient. -/
noncomputable def kernelData {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    X.SubmoduleSheafData n :=
  SubmoduleSheafData.glueOpenCover x.kernelChartCover
    (fun t ↦ x.affineOpenKernelData (x.kernelChart t.down))
    (fun i j W a b hab ↦
      x.affineOpenKernelData_compatible (x.kernelChart i.down) (x.kernelChart j.down)
        W a b hab)

/-- The glued global kernel datum restricts to the affine kernel chosen on every
member of the kernel-chart cover. -/
lemma kernelData_comap_kernelChart {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (i : ULift.{u + 1} X) :
    x.kernelData.comap (x.kernelChartCover.f i) =
      x.affineOpenKernelData (x.kernelChart i.down) :=
  SubmoduleSheafData.glueOpenCover_comap x.kernelChartCover
    (fun s ↦ x.affineOpenKernelData (x.kernelChart s.down))
    (fun i j W a b hab ↦
      x.affineOpenKernelData_compatible (x.kernelChart i.down) (x.kernelChart j.down)
        W a b hab) i

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The quotient by the glued global kernel is finite locally free of the prescribed
rank. -/
lemma kernelData_quotientProjectiveOfRank {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    x.kernelData.QuotientProjectiveOfRank q := by
  apply SubmoduleSheafData.QuotientProjectiveOfRank.of_comap_openCover
    x.kernelData x.kernelChartCover
  intro i
  rw [kernelData_comap_kernelChart]
  exact x.affineOpenKernelData_kernelChart_quotientProjectiveOfRank i.down

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Pullback of the glued kernel datum is an amalgamation of the kernel-chart data
after every base change. -/
lemma kernelData_isAmalgamationAlong {n : ℕ} {X Y : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) :
    SubmoduleSheafData.IsAmalgamationAlong x.kernelChartCover
      (fun i ↦ x.affineOpenKernelData (x.kernelChart i.down)) g
      (x.kernelData.comap g) := by
  intro i
  let j : x.kernelChartCover.I₀ := i
  calc
    (x.kernelData.comap g).comap ((x.kernelChartCover.pullback₁ g).f i) =
        x.kernelData.comap ((x.kernelChartCover.pullback₁ g).f i ≫ g) :=
      (x.kernelData.comap_comp _ _).symm
    _ = x.kernelData.comap
        (x.kernelChartCover.pullbackHom g j ≫ x.kernelChartCover.f j) := by
      rw [x.kernelChartCover.pullbackHom_map g j]
    _ = (x.kernelData.comap (x.kernelChartCover.f j)).comap
          (x.kernelChartCover.pullbackHom g j) :=
      x.kernelData.comap_comp _ _
    _ = (x.affineOpenKernelData (x.kernelChart j.down)).comap
          (x.kernelChartCover.pullbackHom g j) := by
      rw [kernelData_comap_kernelChart]

/-- On an affine test scheme, the intrinsic kernel of the pulled-back quotient is an
amalgamation of the kernel-chart data. -/
lemma affineKernelDataOfIsAffine_isAmalgamationAlong {n : ℕ}
    {X Y : Scheme.{u}} [IsAffine Y]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) :
    SubmoduleSheafData.IsAmalgamationAlong x.kernelChartCover
      (fun i ↦ x.affineOpenKernelData (x.kernelChart i.down)) g
      ((x.pullback g).affineKernelDataOfIsAffine) := by
  intro i
  let j : x.kernelChartCover.I₀ := i
  letI : IsAffine (x.kernelChartCover.X j) := (x.kernelChart j.down).2
  change ((x.pullback g).affineKernelDataOfIsAffine.comap
      ((x.kernelChartCover.pullback₁ g).f i)) =
    (x.affineOpenKernelData (x.kernelChart j.down)).comap
      (x.kernelChartCover.pullbackHom g j)
  rw [affineOpenKernelData_eq_affineKernelDataOfIsAffine]
  exact affineKernelDataOfIsAffine_compatible x g
    (x.kernelChartCover.f j) _
    ((x.kernelChartCover.pullback₁ g).f i)
    (x.kernelChartCover.pullbackHom g j)
    (x.kernelChartCover.pullbackHom_map g j).symm

/-- Pullback of the glued global kernel along a morphism with affine source is the
intrinsic affine kernel of the pulled-back quotient. -/
lemma kernelData_comap_of_isAffine {n : ℕ} {X Y : Scheme.{u}} [IsAffine Y]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) :
    x.kernelData.comap g = (x.pullback g).affineKernelDataOfIsAffine := by
  let K : ∀ i : x.kernelChartCover.I₀,
      (x.kernelChartCover.X i).SubmoduleSheafData n :=
    fun i ↦ x.affineOpenKernelData (x.kernelChart i.down)
  let hcompat : ∀ (i j : x.kernelChartCover.I₀) (W : Scheme.{u})
      (a : W ⟶ x.kernelChartCover.X i) (b : W ⟶ x.kernelChartCover.X j),
      a ≫ x.kernelChartCover.f i = b ≫ x.kernelChartCover.f j →
        (K i).comap a = (K j).comap b :=
    fun i j W a b hab ↦
      x.affineOpenKernelData_compatible (x.kernelChart i.down) (x.kernelChart j.down)
        W a b hab
  calc
    x.kernelData.comap g =
        SubmoduleSheafData.affineAmalgamation x.kernelChartCover K hcompat g :=
      SubmoduleSheafData.eq_affineAmalgamation_of_isAmalgamationAlong
        x.kernelChartCover K hcompat (kernelData_isAmalgamationAlong x g)
    _ = (x.pullback g).affineKernelDataOfIsAffine :=
      (SubmoduleSheafData.eq_affineAmalgamation_of_isAmalgamationAlong
        x.kernelChartCover K hcompat
        (affineKernelDataOfIsAffine_isAmalgamationAlong x g)).symm

/-- On an affine scheme, the globally glued kernel datum agrees with the intrinsic
kernel computed from global sections. -/
lemma kernelData_eq_affineKernelDataOfIsAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    x.kernelData = x.affineKernelDataOfIsAffine := by
  calc
    x.kernelData = x.kernelData.comap (𝟙 X) := x.kernelData.comap_id.symm
    _ = (x.pullback (𝟙 X)).affineKernelDataOfIsAffine :=
      kernelData_comap_of_isAffine x (𝟙 X)
    _ = x.affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_eq_of_r (pullback_id_r x)

/-- The affine quotient constructed from global kernel data has exactly the prescribed
global kernel datum. -/
lemma affineFreeQuotientOfKernelData_kernelData {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (K : X.SubmoduleSheafData n)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    (affineFreeQuotientOfKernelData K hproj hrank).kernelData = K := by
  let L := K.submodule ⟨⊤, isAffineOpen_top X⟩
  let y := affineFreeQuotientOfSubmodule L q
    (Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)) hproj hrank
  let x := y.pullback X.isoSpec.hom
  change x.kernelData = K
  rw [kernelData_eq_affineKernelDataOfIsAffine]
  have hxy : (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).r
      (x.pullback X.isoSpec.inv) y := by
    have hcomp := pullback_comp_r X.isoSpec.inv X.isoSpec.hom y
    rw [X.isoSpec.inv_hom_id] at hcomp
    exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).trans hcomp
      (pullback_id_r y)
  change (x.pullback X.isoSpec.inv).affineKernelData.comap X.isoSpec.hom = K
  rw [affineKernelData_eq_of_r hxy]
  rw [← SubmoduleSheafData.ofAffineSubmodule_submodule
    (y.affineKernelData.comap X.isoSpec.hom),
    ← SubmoduleSheafData.ofAffineSubmodule_submodule K]
  congr 1
  rw [y.affineKernelData.comap_submodule_eq_span X.isoSpec.hom
    (U' := ⟨⊤, isAffineOpen_top X⟩)
    (V := ⟨⊤, isAffineOpen_top (Spec (.of Γ(X, ⊤)))⟩)
    (by intro z _; trivial)]
  rw [affineKernelData, SubmoduleSheafData.ofAffineSubmodule_submodule_top,
    intrinsicKernelSubmodule,
    affineFreeQuotientOfSubmodule_kernelSubmodule]
  have hi : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
    simp [Scheme.isoSpec]
  have himage : X.isoSpec.hom.appPi (⊤ : (Spec (.of Γ(X, ⊤))).Opens)
      (by intro z _; trivial) n ''
        (L.mapPiRingEquiv
          (Scheme.ΓSpecIso (.of Γ(X, ⊤))).symm.commRingCatIsoToRingEquiv :
            Set (Fin n → Γ(Spec (.of Γ(X, ⊤)), ⊤))) =
              (L : Set (Fin n → Γ(X, (⊤ : X.Opens)))) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Submodule.mapPiRingEquiv] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      convert hv using 1
      funext i
      rw [Scheme.Hom.appPi_top]
      change X.isoSpec.hom.appTop.hom
          ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom (v i)) = v i
      rw [hi]
      exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of Γ(X, ⊤))) (v i)
    · intro hv
      let e := (Scheme.ΓSpecIso (.of Γ(X, ⊤))).symm.commRingCatIsoToRingEquiv
      refine ⟨e.piSemilinearEquiv n v, ?_, ?_⟩
      · rw [Submodule.mapPiRingEquiv]
        exact ⟨v, hv, rfl⟩
      · funext i
        rw [Scheme.Hom.appPi_top]
        change X.isoSpec.hom.appTop.hom
            ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom (v i)) = v i
        rw [hi]
        exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of Γ(X, ⊤))) (v i)
  change Submodule.span Γ(X, ⊤)
      (X.isoSpec.hom.appPi (⊤ : (Spec (.of Γ(X, ⊤))).Opens)
        (by intro z _; trivial) n ''
          (L.mapPiRingEquiv
            (Scheme.ΓSpecIso (.of Γ(X, ⊤))).symm.commRingCatIsoToRingEquiv :
              Set (Fin n → Γ(Spec (.of Γ(X, ⊤)), ⊤)))) = L
  rw [himage, Submodule.span_eq]

/-- The glued kernel construction commutes with arbitrary pullback. -/
lemma kernelData_comap {n : ℕ} {X Y : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (g : Y ⟶ X) :
    x.kernelData.comap g = (x.pullback g).kernelData := by
  apply SubmoduleSheafData.eq_of_comap_eq_openCover Y.affineCover
  intro i
  let c := Y.affineCover.f i
  have hp := pullback_comp_r c g x
  calc
    (x.kernelData.comap g).comap c = x.kernelData.comap (c ≫ g) :=
      (x.kernelData.comap_comp c g).symm
    _ = (x.pullback (c ≫ g)).affineKernelDataOfIsAffine :=
      kernelData_comap_of_isAffine x (c ≫ g)
    _ = ((x.pullback g).pullback c).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_eq_of_r
        ((FreeQuotient.setoid q (ULift.{u} (Fin n)) _).symm hp)
    _ = (x.pullback g).kernelData.comap c :=
      (kernelData_comap_of_isAffine (x.pullback g) c).symm
    _ = ((x.pullback g).kernelData).comap c := rfl

/-- Equivalent strict quotient presentations determine the same glued kernel datum. -/
lemma kernelData_eq_of_r {n : ℕ} {X : Scheme.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y) :
    x.kernelData = y.kernelData := by
  apply SubmoduleSheafData.eq_of_comap_eq_openCover X.affineCover
  intro i
  let c := X.affineCover.f i
  calc
    x.kernelData.comap c = (x.pullback c).affineKernelDataOfIsAffine :=
      kernelData_comap_of_isAffine x c
    _ = (y.pullback c).affineKernelDataOfIsAffine :=
      affineKernelDataOfIsAffine_eq_of_r (pullback_r c h)
    _ = y.kernelData.comap c := (kernelData_comap_of_isAffine y c).symm

/-- On an affine scheme, equality of the glued kernel data determines the strict
free quotient presentation up to its defining equivalence relation. -/
lemma r_of_kernelData_eq_of_isAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : x.kernelData = y.kernelData) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y := by
  let x' := x.pullback X.isoSpec.inv
  let y' := y.pullback X.isoSpec.inv
  have hdata : x'.affineKernelData = y'.affineKernelData := by
    have h' : x.affineKernelDataOfIsAffine = y.affineKernelDataOfIsAffine := by
      rw [← kernelData_eq_affineKernelDataOfIsAffine x,
        ← kernelData_eq_affineKernelDataOfIsAffine y]
      exact h
    have h'' := congrArg (fun K ↦ K.comap X.isoSpec.inv) h'
    unfold affineKernelDataOfIsAffine at h''
    rw [← SubmoduleSheafData.comap_comp,
      ← SubmoduleSheafData.comap_comp] at h''
    simpa only [X.isoSpec.inv_hom_id,
      SubmoduleSheafData.comap_id] using h''
  have hintrinsic : x'.intrinsicKernelSubmodule = y'.intrinsicKernelSubmodule := by
    have htop := congrArg
      (fun K : (Spec (.of Γ(X, ⊤))).SubmoduleSheafData n ↦
        K.submodule ⟨⊤, isAffineOpen_top _⟩) hdata
    simpa only [affineKernelData,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top] using htop
  have hkernel : x'.kernelSubmodule = y'.kernelSubmodule := by
    let e := (Scheme.ΓSpecIso Γ(X, ⊤)).symm.commRingCatIsoToRingEquiv
    have h' := congrArg (fun K ↦ K.mapPiRingEquiv e.symm) hintrinsic
    dsimp only [e] at h'
    simpa only [intrinsicKernelSubmodule,
      Submodule.mapPiRingEquiv_symm_mapPiRingEquiv] using h'
  have hxy : (FreeQuotient.setoid q (ULift.{u} (Fin n)) _).r x' y' :=
    r_of_kernelSubmodule_eq hkernel
  have hback := pullback_r X.isoSpec.hom hxy
  have hxcomp := pullback_comp_r X.isoSpec.hom X.isoSpec.inv x
  have hycomp := pullback_comp_r X.isoSpec.hom X.isoSpec.inv y
  rw [X.isoSpec.hom_inv_id] at hxcomp hycomp
  have hxback : (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r
      (x'.pullback X.isoSpec.hom) x :=
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).trans hxcomp (pullback_id_r x)
  have hyback : (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r
      (y'.pullback X.isoSpec.hom) y :=
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).trans hycomp (pullback_id_r y)
  exact (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).trans
    ((FreeQuotient.setoid q (ULift.{u} (Fin n)) X).symm hxback)
    ((FreeQuotient.setoid q (ULift.{u} (Fin n)) X).trans hback hyback)

/-- If two global quotient presentations have the same kernel data, then their
pullbacks to every affine open are equivalent presentations. -/
lemma pullback_affineOpen_r_of_kernelData_eq {n : ℕ} {X : Scheme.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X} (h : x.kernelData = y.kernelData)
    (U : X.affineOpens) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) U.1.toScheme).r
      (x.pullback U.1.ι) (y.pullback U.1.ι) := by
  apply r_of_kernelData_eq_of_isAffine
  rw [kernelData_eq_affineKernelDataOfIsAffine,
    kernelData_eq_affineKernelDataOfIsAffine]
  rw [← kernelData_comap_of_isAffine x U.1.ι,
    ← kernelData_comap_of_isAffine y U.1.ι, h]

/-- The quotient-sheaf isomorphism on an affine open canonically selected by equality
of the two global kernel data. -/
noncomputable def pullbackAffineOpenIsoOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (U : X.affineOpens) :
    (x.pullback U.1.ι).Q ≅ (y.pullback U.1.ι).Q :=
  (pullback_affineOpen_r_of_kernelData_eq h U).choose

/-- The selected affine restriction isomorphism commutes with the pulled-back quotient
maps. -/
@[reassoc]
lemma pullbackAffineOpenIsoOfKernelDataEq_hom_comp {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (U : X.affineOpens) :
    (x.pullback U.1.ι).π ≫ (pullbackAffineOpenIsoOfKernelDataEq x y h U).hom =
      (y.pullback U.1.ι).π :=
  (pullback_affineOpen_r_of_kernelData_eq h U).choose_spec

/-- Equality of global kernel data determines an isomorphism between the literal
restrictions of the two quotient sheaves to every affine open. -/
noncomputable def restrictAffineOpenIsoOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).obj x.Q ≅
      (Modules.restrictFunctor U.1.ι).obj y.Q :=
  (Modules.restrictFunctorIsoPullback U.1.ι).app x.Q ≪≫
    pullbackAffineOpenIsoOfKernelDataEq x y h U ≪≫
    (Modules.restrictFunctorIsoPullback U.1.ι).symm.app y.Q

/-- Restriction of the ambient canonical free sheaf to an affine open is canonically
the canonical free sheaf on that open. -/
noncomputable def restrictFreeIso {n : ℕ} {X : Scheme.{u}} (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) :=
  (Modules.restrictFunctorIsoPullback U.1.ι).app _ ≪≫
    Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))

/-- The restriction to an affine open of a strict quotient presentation, normalized
to have the canonical free sheaf on that open as source. -/
noncomputable def restrictPresentation {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U : X.affineOpens) :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      (Modules.restrictFunctor U.1.ι).obj x.Q :=
  (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
    (Modules.restrictFunctorIsoPullback U.1.ι).inv.app
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ≫
    (Modules.restrictFunctor U.1.ι).map x.π

/-- Conceptual expression for the normalized restricted presentation. -/
lemma restrictPresentation_eq_restrictFreeIso_inv {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U : X.affineOpens) :
    restrictPresentation x U =
      (restrictFreeIso U).inv ≫ (Modules.restrictFunctor U.1.ι).map x.π := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The normalized literal restriction agrees with the pulled-back presentation after
transporting its target from inverse image to restriction. -/
lemma restrictPresentation_eq_pullback {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (U : X.affineOpens) :
    restrictPresentation x U =
      (x.pullback U.1.ι).π ≫
        (Modules.restrictFunctorIsoPullback U.1.ι).inv.app x.Q := by
  rw [restrictPresentation]
  change (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
      ((Modules.restrictFunctorIsoPullback U.1.ι).inv.app _ ≫
        (Modules.restrictFunctor U.1.ι).map x.π) =
    (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
      ((Modules.pullback U.1.ι).map x.π ≫
        (Modules.restrictFunctorIsoPullback U.1.ι).inv.app x.Q)
  rw [cancel_epi]
  exact ((Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality x.π).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The affine restriction isomorphism selected by equal kernel data commutes with the
normalized restricted quotient presentations. -/
@[reassoc]
lemma restrictPresentation_comp_restrictAffineOpenIsoOfKernelDataEq_hom
    {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (U : X.affineOpens) :
    restrictPresentation x U ≫ (restrictAffineOpenIsoOfKernelDataEq x y h U).hom =
      restrictPresentation y U := by
  rw [restrictPresentation_eq_pullback, restrictPresentation_eq_pullback,
    restrictAffineOpenIsoOfKernelDataEq, Iso.trans_hom, Iso.trans_hom]
  let ex := (Modules.restrictFunctorIsoPullback U.1.ι).app x.Q
  let ey := (Modules.restrictFunctorIsoPullback U.1.ι).app y.Q
  let e := pullbackAffineOpenIsoOfKernelDataEq x y h U
  change (x.pullback U.1.ι).π ≫ ex.inv ≫ ex.hom ≫ e.hom ≫ ey.inv =
    (y.pullback U.1.ι).π ≫ ey.inv
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, pullbackAffineOpenIsoOfKernelDataEq_hom_comp]

/-- A point of the affine kernel chart, regarded as a point of its open subscheme. -/
noncomputable def pointInKernelChart {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (z : X) :
    (x.kernelChart z).1.toScheme :=
  ⟨z, x.mem_kernelChart z⟩

/-- Equality of global kernel data induces an isomorphism of quotient-sheaf stalks at
every point, obtained from the selected isomorphism on an affine kernel chart. -/
noncomputable def stalkIsoOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (z : X) :
    (Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor (X := X) Ab z).obj x.Q ≅
      (Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) Ab z).obj y.Q :=
  ((Modules.restrictStalkNatIso (x.kernelChart z).1.ι
      (pointInKernelChart x z)).app x.Q).symm ≪≫
    ((Modules.toPresheaf (x.kernelChart z).1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor (X := (x.kernelChart z).1.toScheme) Ab
        (pointInKernelChart x z)).mapIso
        (restrictAffineOpenIsoOfKernelDataEq x y h (x.kernelChart z))) ≪≫
    (Modules.restrictStalkNatIso (x.kernelChart z).1.ι
      (pointInKernelChart x z)).app y.Q

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The stalk isomorphism determined by equal kernel data intertwines the two global
quotient presentations. -/
lemma map_π_comp_stalkIsoOfKernelDataEq_hom {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData)
    (z : X) :
    (Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) Ab z).map x.π ≫
        (stalkIsoOfKernelDataEq x y h z).hom =
      (Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) Ab z).map y.π := by
  let U := x.kernelChart z
  let zU := pointInKernelChart x z
  let Φ := Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor (X := X) Ab z
  let Ψ := Modules.toPresheaf U.1.toScheme ⋙
    TopCat.Presheaf.stalkFunctor (X := U.1.toScheme) Ab zU
  let s := (Modules.restrictStalkNatIso U.1.ι zU).app
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
  let tx := (Modules.restrictStalkNatIso U.1.ι zU).app x.Q
  let ty := (Modules.restrictStalkNatIso U.1.ι zU).app y.Q
  let rf := Ψ.mapIso (restrictFreeIso (n := n) U)
  let e := Ψ.mapIso (restrictAffineOpenIsoOfKernelDataEq x y h U)
  have hxnat := (Modules.restrictStalkNatIso U.1.ι zU).hom.naturality x.π
  have hynat := (Modules.restrictStalkNatIso U.1.ι zU).hom.naturality y.π
  change Ψ.map ((Modules.restrictFunctor U.1.ι).map x.π) ≫ tx.hom =
    s.hom ≫ Φ.map x.π at hxnat
  change Ψ.map ((Modules.restrictFunctor U.1.ι).map y.π) ≫ ty.hom =
    s.hom ≫ Φ.map y.π at hynat
  have hlocal := congrArg (fun f ↦ Ψ.map f)
    (restrictPresentation_comp_restrictAffineOpenIsoOfKernelDataEq_hom x y h U)
  rw [Functor.map_comp] at hlocal
  rw [restrictPresentation_eq_restrictFreeIso_inv,
    restrictPresentation_eq_restrictFreeIso_inv,
    Functor.map_comp, Functor.map_comp] at hlocal
  have hx := congrArg (fun f ↦ rf.inv ≫ f ≫ tx.inv ≫ e.hom ≫ ty.hom) hxnat
  have hy := congrArg (fun f ↦ rf.inv ≫ f) hynat
  have hl := congrArg (fun f ↦ f ≫ ty.hom) hlocal
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hx hl hy
  rw [← cancel_epi (rf.inv ≫ s.hom)]
  change (rf.inv ≫ s.hom) ≫ Φ.map x.π ≫
      (tx.inv ≫ e.hom ≫ ty.hom) =
    (rf.inv ≫ s.hom) ≫ Φ.map y.π
  simpa only [Category.assoc] using hx.symm.trans (hl.trans hy)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
noncomputable def homOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData) :
    x.Q ⟶ y.Q := by
  letI := x.epi
  apply Modules.epiDescOfStalkFactorization x.π y.π
  intro z
  exact ⟨(stalkIsoOfKernelDataEq x y h z).hom,
    (map_π_comp_stalkIsoOfKernelDataEq_hom x y h z).symm⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma comp_homOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData) :
    x.π ≫ homOfKernelDataEq x y h = y.π := by
  letI := x.epi
  apply Modules.comp_epiDescOfStalkFactorization
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Equal glued kernel data determine an isomorphism of the corresponding global
quotient sheaves. -/
noncomputable def isoOfKernelDataEq {n : ℕ} {X : Scheme.{u}}
    (x y : FreeQuotient q (ULift.{u} (Fin n)) X) (h : x.kernelData = y.kernelData) :
    x.Q ≅ y.Q where
  hom := homOfKernelDataEq x y h
  inv := homOfKernelDataEq y x h.symm
  hom_inv_id := by
    letI := x.epi
    apply (cancel_epi x.π).1
    rw [← Category.assoc, comp_homOfKernelDataEq, comp_homOfKernelDataEq, Category.comp_id]
  inv_hom_id := by
    letI := y.epi
    apply (cancel_epi y.π).1
    rw [← Category.assoc, comp_homOfKernelDataEq, comp_homOfKernelDataEq, Category.comp_id]

/-- Strict free quotients with equal glued kernel data are equivalent. -/
lemma r_of_kernelData_eq {n : ℕ} {X : Scheme.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X} (h : x.kernelData = y.kernelData) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y :=
  ⟨isoOfKernelDataEq x y h, comp_homOfKernelDataEq x y h⟩

/-- The absolute Grassmannian point defined by the kernel of a strict free quotient. -/
noncomputable def kernelPoint {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    (grassmannianFunctor q n).obj (op X) :=
  ⟨x.kernelData, x.kernelData_quotientProjectiveOfRank⟩

/-- Equivalent strict quotient presentations define the same absolute Grassmannian
point. -/
lemma kernelPoint_eq_of_r {n : ℕ} {X : Scheme.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y) :
    x.kernelPoint = y.kernelPoint := by
  apply Subtype.ext
  exact kernelData_eq_of_r h

/-- Replacing the target of a strict free quotient by an isomorphic sheaf leaves its
absolute Grassmannian kernel point unchanged. -/
@[simp]
lemma postcompIso_kernelPoint {n : ℕ} {X : Scheme.{u}}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) {Q' : X.Modules} (e : x.Q ≅ Q') :
    (x.postcompIso e).kernelPoint = x.kernelPoint :=
  (kernelPoint_eq_of_r (postcompIso_r x e)).symm

/-- Equality of Grassmannian kernel points is exactly equivalence of strict
finite-free quotient presentations. -/
lemma r_of_kernelPoint_eq {n : ℕ} {X : Scheme.{u}}
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : x.kernelPoint = y.kernelPoint) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y := by
  apply r_of_kernelData_eq
  exact congrArg Subtype.val h

/-- Affine compatibility alias for the global kernel-point criterion. -/
lemma r_of_kernelPoint_eq_of_isAffine {n : ℕ} {X : Scheme.{u}} [IsAffine X]
    {x y : FreeQuotient q (ULift.{u} (Fin n)) X}
    (h : x.kernelPoint = y.kernelPoint) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r x y :=
  r_of_kernelPoint_eq h

/-- Formation of the absolute Grassmannian point commutes with pullback. -/
lemma kernelPoint_pullback {n : ℕ} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    (grassmannianFunctor q n).map g.op x.kernelPoint =
      (x.pullback g).kernelPoint := by
  apply Subtype.ext
  exact kernelData_comap x g

/-- On an affine scheme, the strict quotient constructed from a Grassmannian kernel
point maps back to that point. -/
@[simp]
lemma affineFreeQuotientOfKernelData_kernelPoint {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (K : X.SubmoduleSheafData n)
    (hK : K.QuotientProjectiveOfRank q)
    (hproj : Module.Projective Γ(X, ⊤)
      ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩))
    (hrank : ∀ p : PrimeSpectrum Γ(X, ⊤),
      Module.rankAtStalk
        ((Fin n → Γ(X, ⊤)) ⧸ K.submodule ⟨⊤, isAffineOpen_top X⟩) p = q) :
    (affineFreeQuotientOfKernelData K hproj hrank).kernelPoint = ⟨K, hK⟩ := by
  apply Subtype.ext
  exact affineFreeQuotientOfKernelData_kernelData K hproj hrank

/-- Every kernel-model Grassmannian point on an affine scheme canonically determines
a strict quotient presentation. -/
noncomputable def affineFreeQuotientOfPoint {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X)) :
    FreeQuotient q (ULift.{u} (Fin n)) X :=
  affineFreeQuotientOfKernelData K.1
    (K.2.projective_affine ⟨⊤, isAffineOpen_top X⟩)
    (K.2.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)

/-- The affine strict-quotient inverse is a right inverse to the global kernel map. -/
@[simp]
lemma affineFreeQuotientOfPoint_kernelPoint {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X)) :
    (affineFreeQuotientOfPoint K).kernelPoint = K := by
  apply Subtype.ext
  exact affineFreeQuotientOfKernelData_kernelData K.1
    (K.2.projective_affine ⟨⊤, isAffineOpen_top X⟩)
    (K.2.rankAtStalk_affine ⟨⊤, isAffineOpen_top X⟩)

/-- The affine strict-quotient inverse is also a left inverse, up to the defining
equivalence relation on quotient presentations. -/
lemma affineFreeQuotientOfPoint_kernelPoint_r {X : Scheme.{u}} [IsAffine X]
    {n q : ℕ} (x : FreeQuotient q (ULift.{u} (Fin n)) X) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) X).r
      (affineFreeQuotientOfPoint x.kernelPoint) x := by
  apply r_of_kernelPoint_eq_of_isAffine
  rw [affineFreeQuotientOfPoint_kernelPoint]

/-- Restriction of a global Grassmannian kernel point to an affine open. -/
noncomputable def affineOpenPoint {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (grassmannianFunctor q n).obj (op U.1.toScheme) :=
  (grassmannianFunctor q n).map U.1.ι.op K

/-- The canonical strict quotient presentation attached to the restriction of a
Grassmannian point to an affine open. -/
noncomputable def affineOpenFreeQuotient {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    FreeQuotient q (ULift.{u} (Fin n)) U.1.toScheme :=
  affineFreeQuotientOfPoint (affineOpenPoint K U)

/-- The kernel of the canonical affine-open quotient is the restriction of the
original global kernel point. -/
@[simp]
lemma affineOpenFreeQuotient_kernelPoint {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineOpenFreeQuotient K U).kernelPoint = affineOpenPoint K U :=
  affineFreeQuotientOfPoint_kernelPoint (affineOpenPoint K U)

/-- The intrinsic kernel datum of the canonical quotient on an affine open is the
restriction of the original global kernel datum. -/
lemma affineOpenFreeQuotient_kernelData {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineOpenFreeQuotient K U).kernelData = K.1.comap U.1.ι := by
  exact congrArg Subtype.val (affineOpenFreeQuotient_kernelPoint K U)

/-- In canonical affine coordinates, the kernel of the quotient attached to an
affine open is exactly the top-section submodule of the restricted kernel datum. -/
lemma affineOpenFreeQuotient_pullback_isoSpec_inv_kernelSubmodule
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    ((affineOpenFreeQuotient K U).pullback
      U.1.toScheme.isoSpec.inv).kernelSubmodule =
        (K.1.comap U.1.ι).submodule
          ⟨⊤, isAffineOpen_top U.1.toScheme⟩ := by
  apply affineFreeQuotientOfKernelData_pullback_isoSpec_inv_kernelSubmodule

/-- The canonical quotient map on an affine chart, written in canonical-spectrum
coordinates, has exactly the prescribed restricted kernel. -/
lemma ker_moduleMapPiOfHom_homOnIsoSpec_affineOpenFreeQuotient_π
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    LinearMap.ker (moduleMapPiOfHom
      (homOnIsoSpec (affineOpenFreeQuotient K U).π)) =
        (K.1.comap U.1.ι).submodule
          ⟨⊤, isAffineOpen_top U.1.toScheme⟩ := by
  rw [moduleMapPiOfHom_homOnIsoSpec_π]
  exact affineOpenFreeQuotient_pullback_isoSpec_inv_kernelSubmodule K U

/-- Canonical quotient presentations on two affine opens become equivalent on every
affine scheme mapping to their overlap.  This is the presentation-level overlap
compatibility used to descend the local quotients. -/
lemma affineOpenFreeQuotient_pullback_r {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U V : X.affineOpens) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) W).r
      ((affineOpenFreeQuotient K U).pullback a)
      ((affineOpenFreeQuotient K V).pullback b) := by
  apply FreeQuotient.r_of_kernelPoint_eq_of_isAffine
  rw [← FreeQuotient.kernelPoint_pullback,
    ← FreeQuotient.kernelPoint_pullback,
    affineOpenFreeQuotient_kernelPoint,
    affineOpenFreeQuotient_kernelPoint]
  change (grassmannianFunctor q n).map a.op
      ((grassmannianFunctor q n).map U.1.ι.op K) =
    (grassmannianFunctor q n).map b.op
      ((grassmannianFunctor q n).map V.1.ι.op K)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have habop := congrArg Quiver.Hom.op hab
  change U.1.ι.op ≫ a.op = V.1.ι.op ≫ b.op at habop
  rw [habop]

/-- The canonical isomorphism between the two quotient sheaves obtained on an affine
scheme over an overlap. -/
noncomputable def affineOpenFreeQuotientPullbackIso {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U V : X.affineOpens) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    ((affineOpenFreeQuotient K U).pullback a).Q ≅
      ((affineOpenFreeQuotient K V).pullback b).Q :=
  (affineOpenFreeQuotient_pullback_r K U V a b hab).choose

/-- The overlap isomorphism commutes with the canonical quotient presentations. -/
@[reassoc]
lemma affineOpenFreeQuotientPullbackIso_hom_comp {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U V : X.affineOpens) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    ((affineOpenFreeQuotient K U).pullback a).π ≫
        (affineOpenFreeQuotientPullbackIso K U V a b hab).hom =
      ((affineOpenFreeQuotient K V).pullback b).π :=
  (affineOpenFreeQuotient_pullback_r K U V a b hab).choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- An isomorphism between the targets of two epic quotient presentations is uniquely
determined by compatibility with the quotient maps. -/
lemma iso_ext {T : Scheme.{u}} {I : Type u} {q : ℕ}
    (x y : FreeQuotient q I T) (e e' : x.Q ≅ y.Q)
    (he : x.π ≫ e.hom = y.π) (he' : x.π ≫ e'.hom = y.π) : e = e' := by
  letI : Epi x.π := x.epi
  apply Iso.ext
  rw [← cancel_epi x.π, he, he']
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma affineOpenFreeQuotientPullbackIso_self {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U : X.affineOpens) (a : W ⟶ U.1.toScheme) :
    affineOpenFreeQuotientPullbackIso K U U a a rfl = Iso.refl _ := by
  apply iso_ext _ _
  · exact affineOpenFreeQuotientPullbackIso_hom_comp K U U a a rfl
  · rw [Iso.refl_hom, Category.comp_id]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The chosen overlap isomorphisms are inverse to one another. -/
lemma affineOpenFreeQuotientPullbackIso_symm {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U V : X.affineOpens) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (hab : a ≫ U.1.ι = b ≫ V.1.ι) :
    affineOpenFreeQuotientPullbackIso K U V a b hab =
      (affineOpenFreeQuotientPullbackIso K V U b a hab.symm).symm := by
  apply iso_ext _ _
  · exact affineOpenFreeQuotientPullbackIso_hom_comp K U V a b hab
  · rw [← affineOpenFreeQuotientPullbackIso_hom_comp K V U b a hab.symm]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The chosen affine-overlap isomorphisms satisfy the cocycle condition. -/
lemma affineOpenFreeQuotientPullbackIso_trans {X W : Scheme.{u}} [IsAffine W]
    {n q : ℕ} (K : (grassmannianFunctor q n).obj (op X))
    (U V Z : X.affineOpens) (a : W ⟶ U.1.toScheme) (b : W ⟶ V.1.toScheme)
    (c : W ⟶ Z.1.toScheme) (hab : a ≫ U.1.ι = b ≫ V.1.ι)
    (hbc : b ≫ V.1.ι = c ≫ Z.1.ι) :
    affineOpenFreeQuotientPullbackIso K U V a b hab ≪≫
        affineOpenFreeQuotientPullbackIso K V Z b c hbc =
      affineOpenFreeQuotientPullbackIso K U Z a c (hab.trans hbc) := by
  apply iso_ext _ _
  · rw [Iso.trans_hom, ← Category.assoc,
      affineOpenFreeQuotientPullbackIso_hom_comp,
      affineOpenFreeQuotientPullbackIso_hom_comp]
  · exact affineOpenFreeQuotientPullbackIso_hom_comp K U Z a c (hab.trans hbc)

/-- The local quotient map, transposed across pullback–pushforward adjunction, is a
map from the global finite free sheaf to the pushforward of the affine quotient. -/
noncomputable def affineOpenDetectionMap {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      (Modules.pushforward U.1.ι).obj (affineOpenFreeQuotient K U).Q :=
  (Modules.pullbackPushforwardAdjunction U.1.ι).homEquiv _ _
    ((Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom ≫
      (affineOpenFreeQuotient K U).π)

/-- Restricting the detection map for an affine open back to that open and applying
the adjunction counit recovers its canonical quotient map. -/
lemma pullback_affineOpenDetectionMap_comp_counit
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.pullback U.1.ι).map (affineOpenDetectionMap K U) ≫
        (Modules.pullbackPushforwardAdjunction U.1.ι).counit.app
          (affineOpenFreeQuotient K U).Q =
      (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom ≫
        (affineOpenFreeQuotient K U).π := by
  change (Modules.pullback U.1.ι).map
      ((Modules.pullbackPushforwardAdjunction U.1.ι).homEquiv _ _
        ((Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom ≫
          (affineOpenFreeQuotient K U).π)) ≫
      (Modules.pullbackPushforwardAdjunction U.1.ι).counit.app _ = _
  let adj := Modules.pullbackPushforwardAdjunction U.1.ι
  let f := (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom ≫
    (affineOpenFreeQuotient K U).π
  have h := adj.homEquiv_counit
    (g := adj.homEquiv (SheafOfModules.free (ULift.{u} (Fin n)))
      (affineOpenFreeQuotient K U).Q f)
  exact h.symm.trans (Equiv.symm_apply_apply _ f)

/-- The detection coordinate indexed by `V`, restricted to the affine open `U` and
normalized so that its source is literally the canonical free sheaf on `U`. -/
noncomputable def affineOpenDetectionComponent
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      (Modules.pullback U.1.ι).obj
        ((Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) :=
  (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
    (Modules.pullback U.1.ι).map (affineOpenDetectionMap K V)

/-- The self-coordinate of the normalized restricted detection map, followed by the
adjunction counit, is the canonical affine quotient map. -/
@[reassoc]
lemma affineOpenDetectionComponent_self_comp_counit
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineOpenDetectionComponent K U U ≫
        (Modules.pullbackPushforwardAdjunction U.1.ι).counit.app
          (affineOpenFreeQuotient K U).Q =
      (affineOpenFreeQuotient K U).π := by
  rw [affineOpenDetectionComponent]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t ↦ (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫ t)
    (pullback_affineOpenDetectionMap_comp_counit K U)).trans (Iso.inv_hom_id_assoc _ _)

/-- The self-coordinate factors through the canonical affine quotient; its factor is
the inverse of the pullback–pushforward counit for the open immersion. -/
instance {X : Scheme.{u}} (U : X.affineOpens) (M : U.1.toScheme.Modules) :
    IsIso ((Modules.pullbackPushforwardAdjunction U.1.ι).counit.app M) :=
  inferInstance

/-- The self-detection component factors as the affine quotient map followed by the
inverse of the pullback-pushforward adjunction counit. -/
lemma affineOpenDetectionComponent_self_factorization
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineOpenDetectionComponent K U U =
      (affineOpenFreeQuotient K U).π ≫
        (asIso ((Modules.pullbackPushforwardAdjunction U.1.ι).counit.app
          (affineOpenFreeQuotient K U).Q)).inv := by
  exact (Iso.eq_comp_inv _).mpr (affineOpenDetectionComponent_self_comp_counit K U)

/-- The detection coordinate expressed using literal restriction along the
open immersion `U ⟶ X`. -/
noncomputable def affineOpenDetectionRestrictComponent
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      (Modules.restrictFunctor U.1.ι).obj
        ((Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) :=
  affineOpenDetectionComponent K U V ≫
    (Modules.restrictFunctorIsoPullback U.1.ι).inv.app _

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Expanded form of the literal-restriction component: first identify the free sheaf
on `U` with the restriction of the free sheaf on `X`, then restrict the original
detection morphism. -/
lemma affineOpenDetectionRestrictComponent_eq
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    affineOpenDetectionRestrictComponent K U V =
      (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
        (Modules.restrictFunctorIsoPullback U.1.ι).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ≫
        (Modules.restrictFunctor U.1.ι).map (affineOpenDetectionMap K V) := by
  rw [affineOpenDetectionRestrictComponent, affineOpenDetectionComponent,
    Category.assoc, cancel_epi]
  exact (Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality
    (affineOpenDetectionMap K V)

/-- Sections of the literal-restriction target are exactly sections of the `V`-chart
quotient on the open-theoretic intersection with the image of `W ⊆ U`. -/
lemma affineOpenDetectionRestrictTarget_sections
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens)
    (W : U.1.toScheme.Opens) :
    Γ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q), W) =
      Γ((affineOpenFreeQuotient K V).Q,
        V.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ W)) :=
  rfl

/-- The intersection with `V`, regarded as an open subscheme of the affine open `U`. -/
noncomputable def affineOpenOverlapLeft {X : Scheme.{u}} (U V : X.affineOpens) :
    U.1.toScheme.Opens :=
  U.1.ι ⁻¹ᵁ V.1

/-- The overlap inclusion into its left affine chart. -/
noncomputable def affineOpenOverlapToLeft {X : Scheme.{u}} (U V : X.affineOpens) :
    (affineOpenOverlapLeft U V).toScheme ⟶ U.1.toScheme :=
  (affineOpenOverlapLeft U V).ι

/-- The overlap inclusion into its right affine chart. -/
noncomputable def affineOpenOverlapToRight {X : Scheme.{u}} (U V : X.affineOpens) :
    (affineOpenOverlapLeft U V).toScheme ⟶ V.1.toScheme :=
  IsOpenImmersion.lift V.1.ι
    ((affineOpenOverlapLeft U V).ι ≫ U.1.ι) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨_, x.2⟩, rfl⟩)

/-- The two maps from the overlap to the ambient scheme agree. -/
lemma affineOpenOverlap_fac {X : Scheme.{u}} (U V : X.affineOpens) :
    affineOpenOverlapToLeft U V ≫ U.1.ι =
      affineOpenOverlapToRight U V ≫ V.1.ι := by
  symm
  exact IsOpenImmersion.lift_fac _ _ _

/-- The first projection from the intersection of two affine opens is an open
immersion. -/
instance affineOpenOverlapToLeft_isOpenImmersion {X : Scheme.{u}}
    (U V : X.affineOpens) : IsOpenImmersion (affineOpenOverlapToLeft U V) := by
  dsimp [affineOpenOverlapToLeft]
  infer_instance

/-- The second projection from the intersection of two affine opens is an open
immersion. -/
instance affineOpenOverlapToRight_isOpenImmersion {X : Scheme.{u}}
    (U V : X.affineOpens) : IsOpenImmersion (affineOpenOverlapToRight U V) := by
  have hcomp : IsOpenImmersion (affineOpenOverlapToLeft U V ≫ U.1.ι) := by
    dsimp [affineOpenOverlapToLeft, affineOpenOverlapLeft]
    infer_instance
  rw [affineOpenOverlap_fac U V] at hcomp
  let _ : IsOpenImmersion (affineOpenOverlapToRight U V ≫ V.1.ι) := hcomp
  apply IsOpenImmersion.of_comp _ V.1.ι

/-- In the right affine chart, the image of the part of the overlap lying over
`W ⊆ U` is the inverse image of the image of `W` in the ambient scheme. -/
lemma affineOpenOverlapToRight_image_preimage {X : Scheme.{u}}
    (U V : X.affineOpens) (W : U.1.toScheme.Opens) :
    affineOpenOverlapToRight U V ''ᵁ (affineOpenOverlapToLeft U V ⁻¹ᵁ W) =
      V.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ W) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change affineOpenOverlapToLeft U V z ∈ W at hz
    change V.1.ι (affineOpenOverlapToRight U V z) ∈ U.1.ι ''ᵁ W
    refine ⟨affineOpenOverlapToLeft U V z, hz, ?_⟩
    exact congrArg
      (fun f : (affineOpenOverlapLeft U V).toScheme ⟶ X ↦ f z)
      (affineOpenOverlap_fac U V)
  · intro hy
    change V.1.ι y ∈ U.1.ι ''ᵁ W at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxV : U.1.ι x ∈ V.1 := hxy ▸ y.2
    let z : (affineOpenOverlapLeft U V).toScheme := ⟨x, hxV⟩
    refine ⟨z, ?_, ?_⟩
    · change affineOpenOverlapToLeft U V z ∈ W
      exact hx
    · change affineOpenOverlapToRight U V z = y
      apply V.1.ι.isOpenEmbedding.injective
      have hzfac := congrArg
        (fun f : (affineOpenOverlapLeft U V).toScheme ⟶ X ↦ f z)
        (affineOpenOverlap_fac U V)
      exact hzfac.symm.trans hxy

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Restricting a module pushed forward from `V` to `U` is canonically the
pushforward from the overlap `U ∩ V` of its restriction from `V`. -/
noncomputable def affineOpenRestrictPushforwardIso {X : Scheme.{u}}
    (U V : X.affineOpens) (M : V.1.toScheme.Modules) :
    (Modules.restrictFunctor U.1.ι).obj ((Modules.pushforward V.1.ι).obj M) ≅
      (Modules.pushforward (affineOpenOverlapToLeft U V)).obj
        ((Modules.restrictFunctor (affineOpenOverlapToRight U V)).obj M) := by
  refine (SheafOfModules.fullyFaithfulForget U.1.toScheme.ringCatSheaf).preimageIso ?_
  refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · let h := affineOpenOverlapToRight_image_preimage U V W.unop
    refine ModuleCat.isoMk (M.presheaf.mapIso (eqToIso h).op) ?_
    intro r
    ext x
    have hr : V.1.toScheme.presheaf.map (eqToHom h).op
      (V.1.ι.app (U.1.ι ''ᵁ W.unop) ((U.1.ι.appIso W.unop).inv r)) =
      ((affineOpenOverlapToRight U V).appIso
          (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop)).inv
      ((affineOpenOverlapToLeft U V).app W.unop r) := by
      have hj : (affineOpenOverlapToRight U V).app
            (V.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ W.unop)) ≫
            (affineOpenOverlapLeft U V).toScheme.presheaf.map
              (eqToHom (by
                rw [← h]
                exact (affineOpenOverlapToRight U V).preimage_image_eq
                  (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop) |>.symm)).op ≫
            ((affineOpenOverlapToRight U V).appIso
              (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop)).inv =
          V.1.toScheme.presheaf.map (eqToHom h).op := by
        change (affineOpenOverlapToRight U V).appLE
            (V.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ W.unop))
            (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop) _ ≫
            ((affineOpenOverlapToRight U V).appIso
              (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop)).inv =
          V.1.toScheme.presheaf.map (eqToHom h).op
        rw [(affineOpenOverlapToRight U V).appLE_appIso_inv]
        rfl
      have hmor : (U.1.ι.appIso W.unop).inv ≫
            V.1.ι.app (U.1.ι ''ᵁ W.unop) ≫
            V.1.toScheme.presheaf.map (eqToHom h).op =
          (affineOpenOverlapToLeft U V).app W.unop ≫
            ((affineOpenOverlapToRight U V).appIso
              (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop)).inv := by
        rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
          (affineOpenOverlapToLeft U V) U.1.ι
          (affineOpenOverlapToRight U V ≫ V.1.ι)
          (affineOpenOverlap_fac U V).symm]
        simp only [Scheme.Hom.comp_app, Category.assoc]
        rw [cancel_epi]
        convert congrArg (fun k ↦
          V.1.ι.app (U.1.ι ''ᵁ W.unop) ≫ k) hj.symm using 1
      exact ConcreteCategory.congr_hom hmor r
    change (M.smul (((affineOpenOverlapToRight U V).appIso
        (affineOpenOverlapToLeft U V ⁻¹ᵁ W.unop)).inv
      ((affineOpenOverlapToLeft U V).app W.unop r))).hom
        (M.presheaf.map (eqToHom h).op x) =
    M.presheaf.map (eqToHom h).op
      ((M.smul (V.1.ι.app (U.1.ι ''ᵁ W.unop)
        ((U.1.ι.appIso W.unop).inv r))).hom x)
    erw [M.map_smul]
    rw [hr]
    rfl
  · intro W W' f
    dsimp [Modules.restrictFunctor, Modules.pushforward,
      SheafOfModules.pushforward, PresheafOfModules.pushforward,
      PresheafOfModules.pushforward₀, PresheafOfModules.restrictScalars]
    ext x
    let x' : Γ(M, V.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ W.unop)) := x
    change M.presheaf.map _ (M.presheaf.map _ x') =
      M.presheaf.map _ (M.presheaf.map _ x')
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- On sections, the restriction-form affine-open base-change isomorphism is
the restriction map induced by the equality between the two descriptions of
the relevant open subset of the right chart. -/
lemma affineOpenRestrictPushforwardIso_hom_app_apply {X : Scheme.{u}}
    (U V : X.affineOpens) (M : V.1.toScheme.Modules)
    (W : U.1.toScheme.Opens)
    (x : Γ((Modules.restrictFunctor U.1.ι).obj
      ((Modules.pushforward V.1.ι).obj M), W)) :
    (affineOpenRestrictPushforwardIso U V M).hom.app W x =
      M.presheaf.map (eqToHom
        (affineOpenOverlapToRight_image_preimage U V W)).op x := by
  change (((SheafOfModules.forget U.1.toScheme.ringCatSheaf).map
    (affineOpenRestrictPushforwardIso U V M).hom).app (op W)).hom x = _
  simp only [affineOpenRestrictPushforwardIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  rfl

/-- Mapping a morphism under literal restriction evaluates sectionwise as the
original morphism on the image open. -/
lemma restrictFunctor_map_app_apply {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (k : M ⟶ N)
    (W : X.Opens) (x : Γ((Modules.restrictFunctor f).obj M, W)) :
    ((Modules.restrictFunctor f).map k).app W x = k.app (f ''ᵁ W) x :=
  rfl

/-- The presheaf restriction map of a pushed-forward module, evaluated on an
arbitrary morphism in the opposite category of opens, is the original
presheaf restriction map along the image morphism. -/
lemma pushforward_obj_presheaf_map_apply_op {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
    (x : ((Modules.pushforward f).obj M).presheaf.obj U) :
    ((Modules.pushforward f).obj M).presheaf.map i x =
      M.presheaf.map ((Opens.map f.base).op.map i) x :=
  rfl

/-- Two two-step restriction paths in the presheaf underlying a module give
the same morphism whenever they have the same endpoints.  This is the
thin-category coherence of the opposite category of opens. -/
lemma presheaf_map_twoStep_eq {X : Scheme.{u}} (M : X.Modules)
    {A B B' E : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ E)
    (f' : A ⟶ B') (g' : B' ⟶ E) :
    M.presheaf.map f ≫ M.presheaf.map g =
      M.presheaf.map f' ≫ M.presheaf.map g' := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [Subsingleton.elim (f ≫ g) (f' ≫ g')]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The restriction-form affine-open base-change isomorphism is natural in
the module on the second affine open. -/
lemma affineOpenRestrictPushforwardIso_naturality {X : Scheme.{u}}
    (U V : X.affineOpens) {M N : V.1.toScheme.Modules} (f : M ⟶ N) :
    (Modules.restrictFunctor U.1.ι).map ((Modules.pushforward V.1.ι).map f) ≫
        (affineOpenRestrictPushforwardIso U V N).hom =
      (affineOpenRestrictPushforwardIso U V M).hom ≫
        (Modules.pushforward (affineOpenOverlapToLeft U V)).map
          ((Modules.restrictFunctor (affineOpenOverlapToRight U V)).map f) := by
  apply (SheafOfModules.forget U.1.toScheme.ringCatSheaf).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  simp only [affineOpenRestrictPushforwardIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  ext W x
  let h := affineOpenOverlapToRight_image_preimage U V W.unop
  dsimp [Modules.restrictFunctor, Modules.pushforward,
    SheafOfModules.pushforward, PresheafOfModules.pushforward,
    PresheafOfModules.pushforward₀, PresheafOfModules.restrictScalars]
  change N.presheaf.map (eqToHom h).op (f.val.app _ x) =
    f.val.app _ (M.presheaf.map (eqToHom h).op x)
  exact (ConcreteCategory.congr_hom
    (f.val.naturality (eqToHom h).op) x).symm

/-- Pullback to the overlap through its two projections gives canonically
isomorphic modules. -/
noncomputable def affineOpenOverlapIteratedPullbackIso {X : Scheme.{u}}
    (U V : X.affineOpens) (M : X.Modules) :
    (Modules.pullback (affineOpenOverlapToLeft U V)).obj
        ((Modules.pullback U.1.ι).obj M) ≅
      (Modules.pullback (affineOpenOverlapToRight U V)).obj
        ((Modules.pullback V.1.ι).obj M) :=
  (Modules.pullbackComp (affineOpenOverlapToLeft U V) U.1.ι).app M ≪≫
    (Modules.pullbackCongr (affineOpenOverlap_fac U V)).app M ≪≫
    ((Modules.pullbackComp
      (affineOpenOverlapToRight U V) V.1.ι).app M).symm

/-- Pullback of a module pushed forward from `V` to `X` identifies with the
pushforward from `U ∩ V` to `U` of its pullback from `V`.  This is the
pullback-form Beck–Chevalley isomorphism obtained from literal restriction. -/
noncomputable def affineOpenPullbackPushforwardIso {X : Scheme.{u}}
    (U V : X.affineOpens) (M : V.1.toScheme.Modules) :
    (Modules.pullback U.1.ι).obj ((Modules.pushforward V.1.ι).obj M) ≅
      (Modules.pushforward (affineOpenOverlapToLeft U V)).obj
        ((Modules.pullback (affineOpenOverlapToRight U V)).obj M) :=
  ((Modules.restrictFunctorIsoPullback U.1.ι).app _).symm ≪≫
    affineOpenRestrictPushforwardIso U V M ≪≫
    (Modules.pushforward (affineOpenOverlapToLeft U V)).mapIso
      ((Modules.restrictFunctorIsoPullback
        (affineOpenOverlapToRight U V)).app M)

/-- Expanded hom of the pullback-form open-square base-change isomorphism. -/
lemma affineOpenPullbackPushforwardIso_hom {X : Scheme.{u}}
    (U V : X.affineOpens) (M : V.1.toScheme.Modules) :
    (affineOpenPullbackPushforwardIso U V M).hom =
      (Modules.restrictFunctorIsoPullback U.1.ι).inv.app _ ≫
        (affineOpenRestrictPushforwardIso U V M).hom ≫
        (Modules.pushforward (affineOpenOverlapToLeft U V)).map
          ((Modules.restrictFunctorIsoPullback
            (affineOpenOverlapToRight U V)).hom.app M) :=
  rfl

/-- The pullback-form affine-open base-change isomorphism is natural in the
module on the second affine open. -/
lemma affineOpenPullbackPushforwardIso_naturality {X : Scheme.{u}}
    (U V : X.affineOpens) {M N : V.1.toScheme.Modules} (f : M ⟶ N) :
    (Modules.pullback U.1.ι).map ((Modules.pushforward V.1.ι).map f) ≫
        (affineOpenPullbackPushforwardIso U V N).hom =
      (affineOpenPullbackPushforwardIso U V M).hom ≫
        (Modules.pushforward (affineOpenOverlapToLeft U V)).map
          ((Modules.pullback (affineOpenOverlapToRight U V)).map f) := by
  rw [affineOpenPullbackPushforwardIso_hom,
    affineOpenPullbackPushforwardIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc]
  rw [(Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality]
  simp only [Category.assoc]
  rw [cancel_epi, ← Category.assoc]
  rw [affineOpenRestrictPushforwardIso_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [(Modules.restrictFunctorIsoPullback
    (affineOpenOverlapToRight U V)).hom.naturality]

/-- The affine-open pullback--pushforward base-change isomorphisms, assembled
as a natural isomorphism. -/
noncomputable def affineOpenPullbackPushforwardNatIso {X : Scheme.{u}}
    (U V : X.affineOpens) :
    Modules.pushforward V.1.ι ⋙ Modules.pullback U.1.ι ≅
      Modules.pullback (affineOpenOverlapToRight U V) ⋙
        Modules.pushforward (affineOpenOverlapToLeft U V) :=
  NatIso.ofComponents
    (fun M ↦ affineOpenPullbackPushforwardIso U V M)
    (fun f ↦ affineOpenPullbackPushforwardIso_naturality U V f)

/-- The comparison between the two iterated pullbacks over an affine-open
overlap obtained from base change and the two pullback--pushforward
adjunctions. -/
noncomputable def affineOpenOverlapAdjunctionComparison {X : Scheme.{u}}
    (U V : X.affineOpens) (M : X.Modules) :
    (Modules.pullback (affineOpenOverlapToLeft U V)).obj
        ((Modules.pullback U.1.ι).obj M) ⟶
      (Modules.pullback (affineOpenOverlapToRight U V)).obj
        ((Modules.pullback V.1.ι).obj M) :=
  (Modules.pullback (affineOpenOverlapToLeft U V)).map
      ((Modules.pullback U.1.ι).map
        ((Modules.pullbackPushforwardAdjunction V.1.ι).unit.app M)) ≫
    (Modules.pullback (affineOpenOverlapToLeft U V)).map
      (affineOpenPullbackPushforwardIso U V
        ((Modules.pullback V.1.ι).obj M)).hom ≫
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V)).counit.app _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical normalization from the structure sheaf on an affine-open
overlap to the iterated pullback through the left affine chart. -/
noncomputable def affineOpenOverlapUnitNormalizationLeft {X : Scheme.{u}}
    (U V : X.affineOpens) :
    SheafOfModules.unit (affineOpenOverlapLeft U V).toScheme.ringCatSheaf ⟶
      (Modules.pullback (affineOpenOverlapToLeft U V)).obj
        ((Modules.pullback U.1.ι).obj
          (SheafOfModules.unit X.ringCatSheaf)) := by
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      U.1.ι.toRingCatSheafHom) := inferInstance
  exact inv (SheafOfModules.pullbackObjUnitToUnit
      (affineOpenOverlapToLeft U V).toRingCatSheafHom) ≫
    (Modules.pullback (affineOpenOverlapToLeft U V)).map
      (inv (SheafOfModules.pullbackObjUnitToUnit U.1.ι.toRingCatSheafHom))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical normalization from the structure sheaf on an affine-open
overlap to the iterated pullback through the right affine chart. -/
noncomputable def affineOpenOverlapUnitNormalizationRight {X : Scheme.{u}}
    (U V : X.affineOpens) :
    SheafOfModules.unit (affineOpenOverlapLeft U V).toScheme.ringCatSheaf ⟶
      (Modules.pullback (affineOpenOverlapToRight U V)).obj
        ((Modules.pullback V.1.ι).obj
          (SheafOfModules.unit X.ringCatSheaf)) := by
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      V.1.ι.toRingCatSheafHom) := inferInstance
  exact inv (SheafOfModules.pullbackObjUnitToUnit
      (affineOpenOverlapToRight U V).toRingCatSheafHom) ≫
    (Modules.pullback (affineOpenOverlapToRight U V)).map
      (inv (SheafOfModules.pullbackObjUnitToUnit V.1.ι.toRingCatSheafHom))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
instance affineOpenOverlapUnitNormalizationLeft_isIso {X : Scheme.{u}}
    (U V : X.affineOpens) :
    IsIso (affineOpenOverlapUnitNormalizationLeft U V) := by
  rw [affineOpenOverlapUnitNormalizationLeft]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
instance affineOpenOverlapUnitNormalizationRight_isIso {X : Scheme.{u}}
    (U V : X.affineOpens) :
    IsIso (affineOpenOverlapUnitNormalizationRight U V) := by
  rw [affineOpenOverlapUnitNormalizationRight]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Explicit inverse of the left iterated structure-sheaf normalization. -/
lemma affineOpenOverlapUnitNormalizationLeft_inv {X : Scheme.{u}}
    (U V : X.affineOpens) :
    inv (affineOpenOverlapUnitNormalizationLeft U V) =
      (Modules.pullback (affineOpenOverlapToLeft U V)).map
          (SheafOfModules.pullbackObjUnitToUnit U.1.ι.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit
          (affineOpenOverlapToLeft U V).toRingCatSheafHom := by
  unfold affineOpenOverlapUnitNormalizationLeft
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Explicit inverse of the right iterated structure-sheaf normalization. -/
lemma affineOpenOverlapUnitNormalizationRight_inv {X : Scheme.{u}}
    (U V : X.affineOpens) :
    inv (affineOpenOverlapUnitNormalizationRight U V) =
      (Modules.pullback (affineOpenOverlapToRight U V)).map
          (SheafOfModules.pullbackObjUnitToUnit V.1.ι.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit
          (affineOpenOverlapToRight U V).toRingCatSheafHom := by
  unfold affineOpenOverlapUnitNormalizationRight
  simp

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- set_option backward.isDefEq.respectTransparency.types false in
-- set_option backward.isDefEq.respectTransparency false in
-- /-- The left and right rank-one overlap normalizations agree through the
-- canonical comparison between the two iterated pullbacks. -/
-- lemma affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso
--     {X : Scheme.{u}} (U V : X.affineOpens) :
--     affineOpenOverlapUnitNormalizationLeft U V ≫
--         (affineOpenOverlapIteratedPullbackIso U V
--           (SheafOfModules.unit X.ringCatSheaf)).hom =
--       affineOpenOverlapUnitNormalizationRight U V := by
--   let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
--     V.1.ι.toRingCatSheafHom) := inferInstance
--   unfold affineOpenOverlapUnitNormalizationLeft
--   unfold affineOpenOverlapUnitNormalizationRight
--   rw [affineOpenOverlapIteratedPullbackIso]
--   simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
--   slice_lhs 1 3 => exact
--     (Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp
--       (affineOpenOverlapToLeft U V) U.1.ι)
--   slice_lhs 1 2 => exact
--     (Modules.pullbackObjUnitToUnit_inv_comp_pullbackCongr
--       (f := affineOpenOverlapToLeft U V ≫ U.1.ι)
--       (g := affineOpenOverlapToRight U V ≫ V.1.ι)
--       (affineOpenOverlap_fac U V))
--   rw [← Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp]
--   let e := (Modules.pullbackComp
--     (affineOpenOverlapToRight U V) V.1.ι).app
--       (SheafOfModules.unit X.ringCatSheaf)
--   slice_lhs 3 4 => exact e.hom_inv_id
--   slice_lhs 2 3 => exact (Category.comp_id
--     ((Modules.pullback (affineOpenOverlapToRight U V)).map
--       (inv (SheafOfModules.pullbackObjUnitToUnit V.1.ι.toRingCatSheafHom))))
--
-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- -- set_option backward.isDefEq.respectTransparency.types false in
-- -- set_option backward.isDefEq.respectTransparency false in
-- -- /-- The normalized rank-one Beck--Chevalley equation is equivalent to the
-- -- adjunction-induced overlap comparison being the canonical comparison of the
-- -- two iterated pullbacks. -/
-- lemma affineOpenOverlapUnitNormalization_naturality_iff {X : Scheme.{u}}
--     (U V : X.affineOpens) :
--     (affineOpenOverlapUnitNormalizationLeft U V ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.unit X.ringCatSheaf) =
--       affineOpenOverlapUnitNormalizationRight U V) ↔
--     affineOpenOverlapAdjunctionComparison U V
--         (SheafOfModules.unit X.ringCatSheaf) =
--       (affineOpenOverlapIteratedPullbackIso U V
--         (SheafOfModules.unit X.ringCatSheaf)).hom := by
--   constructor
--   · intro h
--     rw [← cancel_epi (affineOpenOverlapUnitNormalizationLeft U V)]
--     rw [h]
--     exact (affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso U V).symm
--   · intro h
--     rw [h]
--     exact affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso U V
--
-- set_option backward.isDefEq.respectTransparency.types false in
-- set_option backward.isDefEq.respectTransparency false in
-- /-- Normalization from the canonical finite free sheaf on an affine-open
-- overlap to the iterated pullback through the left chart. -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The left and right rank-one overlap normalizations agree through the
canonical comparison between the two iterated pullbacks. -/
lemma affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso
    {X : Scheme.{u}} (U V : X.affineOpens) :
    affineOpenOverlapUnitNormalizationLeft U V ≫
        (affineOpenOverlapIteratedPullbackIso U V
          (SheafOfModules.unit X.ringCatSheaf)).hom =
      affineOpenOverlapUnitNormalizationRight U V := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    V.1.ι.toRingCatSheafHom) := inferInstance
  unfold affineOpenOverlapUnitNormalizationLeft
  unfold affineOpenOverlapUnitNormalizationRight
  rw [affineOpenOverlapIteratedPullbackIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  slice_lhs 1 3 => exact
    (Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp
      (affineOpenOverlapToLeft U V) U.1.ι)
  slice_lhs 1 2 => exact
    (Modules.pullbackObjUnitToUnit_inv_comp_pullbackCongr
      (f := affineOpenOverlapToLeft U V ≫ U.1.ι)
      (g := affineOpenOverlapToRight U V ≫ V.1.ι)
      (affineOpenOverlap_fac U V))
  rw [← Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp]
  let e := (Modules.pullbackComp
    (affineOpenOverlapToRight U V) V.1.ι).app
      (SheafOfModules.unit X.ringCatSheaf)
  slice_lhs 3 4 => exact e.hom_inv_id
  slice_lhs 2 3 => exact (Category.comp_id
    ((Modules.pullback (affineOpenOverlapToRight U V)).map
      (inv (SheafOfModules.pullbackObjUnitToUnit V.1.ι.toRingCatSheafHom))))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized rank-one Beck--Chevalley equation is equivalent to the
adjunction-induced overlap comparison being the canonical comparison of the
two iterated pullbacks. -/
lemma affineOpenOverlapUnitNormalization_naturality_iff {X : Scheme.{u}}
    (U V : X.affineOpens) :
    (affineOpenOverlapUnitNormalizationLeft U V ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.unit X.ringCatSheaf) =
      affineOpenOverlapUnitNormalizationRight U V) ↔
    affineOpenOverlapAdjunctionComparison U V
        (SheafOfModules.unit X.ringCatSheaf) =
      (affineOpenOverlapIteratedPullbackIso U V
        (SheafOfModules.unit X.ringCatSheaf)).hom := by
  constructor
  · intro h
    rw [← cancel_epi (affineOpenOverlapUnitNormalizationLeft U V)]
    rw [h]
    exact (affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso U V).symm
  · intro h
    rw [h]
    exact affineOpenOverlapUnitNormalization_comp_iteratedPullbackIso U V

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Normalization from the canonical finite free sheaf on an affine-open
overlap to the iterated pullback through the left chart. -/
noncomputable def affineOpenOverlapFreeNormalizationLeft {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) :
    SheafOfModules.free
        (R := (affineOpenOverlapLeft U V).toScheme.ringCatSheaf) I ⟶
      (Modules.pullback (affineOpenOverlapToLeft U V)).obj
        ((Modules.pullback U.1.ι).obj
          (SheafOfModules.free (R := X.ringCatSheaf) I)) :=
  (Modules.pullbackFreeIso (affineOpenOverlapToLeft U V) I).inv ≫
    (Modules.pullback (affineOpenOverlapToLeft U V)).map
      (Modules.pullbackFreeIso U.1.ι I).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Normalization from the canonical finite free sheaf on an affine-open
overlap to the iterated pullback through the right chart. -/
noncomputable def affineOpenOverlapFreeNormalizationRight {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) :
    SheafOfModules.free
        (R := (affineOpenOverlapLeft U V).toScheme.ringCatSheaf) I ⟶
      (Modules.pullback (affineOpenOverlapToRight U V)).obj
        ((Modules.pullback V.1.ι).obj
          (SheafOfModules.free (R := X.ringCatSheaf) I)) :=
  (Modules.pullbackFreeIso (affineOpenOverlapToRight U V) I).inv ≫
    (Modules.pullback (affineOpenOverlapToRight U V)).map
      (Modules.pullbackFreeIso V.1.ι I).inv

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
instance affineOpenOverlapFreeNormalizationLeft_isIso {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) :
    IsIso (affineOpenOverlapFreeNormalizationLeft U V I) := by
  dsimp [affineOpenOverlapFreeNormalizationLeft]
  infer_instance
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
instance affineOpenOverlapFreeNormalizationRight_isIso {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) :
    IsIso (affineOpenOverlapFreeNormalizationRight U V I) := by
  dsimp [affineOpenOverlapFreeNormalizationRight]
  infer_instance
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- On every free generator, the left finite-free overlap normalization is
the rank-one normalization followed by the twice-pulled-back generator. -/
lemma ιFree_comp_affineOpenOverlapFreeNormalizationLeft {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) (i : I) :
    SheafOfModules.ιFree
          (R := (affineOpenOverlapLeft U V).toScheme.ringCatSheaf) i ≫
        affineOpenOverlapFreeNormalizationLeft U V I =
      affineOpenOverlapUnitNormalizationLeft U V ≫
        (Modules.pullback (affineOpenOverlapToLeft U V)).map
          ((Modules.pullback U.1.ι).map
            (SheafOfModules.ιFree (R := X.ringCatSheaf) i)) := by
  rw [affineOpenOverlapFreeNormalizationLeft,
    affineOpenOverlapUnitNormalizationLeft]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [Modules.ιFree_comp_pullbackFreeIso_inv]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [Modules.ιFree_comp_pullbackFreeIso_inv]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- On every free generator, the right finite-free overlap normalization is
the rank-one normalization followed by the twice-pulled-back generator. -/
lemma ιFree_comp_affineOpenOverlapFreeNormalizationRight {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) (i : I) :
    SheafOfModules.ιFree
          (R := (affineOpenOverlapLeft U V).toScheme.ringCatSheaf) i ≫
        affineOpenOverlapFreeNormalizationRight U V I =
      affineOpenOverlapUnitNormalizationRight U V ≫
        (Modules.pullback (affineOpenOverlapToRight U V)).map
          ((Modules.pullback V.1.ι).map
            (SheafOfModules.ιFree (R := X.ringCatSheaf) i)) := by
  rw [affineOpenOverlapFreeNormalizationRight,
    affineOpenOverlapUnitNormalizationRight]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [Modules.ιFree_comp_pullbackFreeIso_inv]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [Modules.ιFree_comp_pullbackFreeIso_inv]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The two finite-free overlap normalizations agree through the canonical
comparison between the two iterated pullbacks. -/
lemma affineOpenOverlapFreeNormalization_comp_iteratedPullbackIso {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u) :
    affineOpenOverlapFreeNormalizationLeft U V I ≫
        (affineOpenOverlapIteratedPullbackIso U V
          (SheafOfModules.free (R := X.ringCatSheaf) I)).hom =
      affineOpenOverlapFreeNormalizationRight U V I := by
  rw [affineOpenOverlapFreeNormalizationLeft,
    affineOpenOverlapFreeNormalizationRight,
    affineOpenOverlapIteratedPullbackIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  slice_lhs 1 3 => exact
    (Modules.pullbackFreeIso_comp
      (affineOpenOverlapToLeft U V) U.1.ι I)
  slice_lhs 1 2 => exact
    (Modules.pullbackFreeIso_congr (affineOpenOverlap_fac U V).symm I)
  rw [← Modules.pullbackFreeIso_comp]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Transposing a morphism from the pullback to `V` and then applying affine-open
base change agrees with transposing its pullback to the overlap after the
adjunction-induced comparison of the two iterated pullbacks. -/
lemma affineOpenPullbackPushforwardIso_homEquiv {X : Scheme.{u}}
    (U V : X.affineOpens) (A : X.Modules) (M : V.1.toScheme.Modules)
    (a : (Modules.pullback V.1.ι).obj A ⟶ M) :
    (Modules.pullback U.1.ι).map
        ((Modules.pullbackPushforwardAdjunction V.1.ι).homEquiv A M a) ≫
      (affineOpenPullbackPushforwardIso U V M).hom =
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V)).homEquiv _ _
        (affineOpenOverlapAdjunctionComparison U V A ≫
          (Modules.pullback (affineOpenOverlapToRight U V)).map a) := by
  apply (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).homEquiv _ _ |>.symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply,
    Functor.map_comp, Adjunction.homEquiv_apply]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have h := congrArg
    (fun f ↦ (Modules.pullback (affineOpenOverlapToLeft U V)).map f)
    (affineOpenPullbackPushforwardIso_naturality U V a)
  simp only [Functor.map_comp] at h
  slice_lhs 2 3 => rw [h]
  have hc := (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).counit.naturality
      ((Modules.pullback (affineOpenOverlapToRight U V)).map a)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map] at hc
  slice_lhs 3 4 => exact hc
  simp only [affineOpenOverlapAdjunctionComparison, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction-induced comparison between the two iterated pullbacks on an
affine-open overlap is natural in the module on the ambient scheme. -/
lemma affineOpenOverlapAdjunctionComparison_naturality {X : Scheme.{u}}
    (U V : X.affineOpens) {A B : X.Modules} (f : A ⟶ B) :
    affineOpenOverlapAdjunctionComparison U V A ≫
        (Modules.pullback (affineOpenOverlapToRight U V)).map
          ((Modules.pullback V.1.ι).map f) =
      (Modules.pullback (affineOpenOverlapToLeft U V)).map
          ((Modules.pullback U.1.ι).map f) ≫
        affineOpenOverlapAdjunctionComparison U V B := by
  simp only [affineOpenOverlapAdjunctionComparison, Category.assoc]
  have hc := (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).counit.naturality
      ((Modules.pullback (affineOpenOverlapToRight U V)).map
        ((Modules.pullback V.1.ι).map f))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map] at hc
  slice_lhs 3 4 => exact hc.symm
  have hb := congrArg
    (fun g ↦ (Modules.pullback (affineOpenOverlapToLeft U V)).map g)
    (affineOpenPullbackPushforwardIso_naturality U V
      ((Modules.pullback V.1.ι).map f))
  simp only [Functor.map_comp] at hb
  slice_lhs 2 3 => exact hb.symm
  simp only [Category.assoc]
  have hu := congrArg
    (fun g ↦ (Modules.pullback (affineOpenOverlapToLeft U V)).map
      ((Modules.pullback U.1.ι).map g))
    ((Modules.pullbackPushforwardAdjunction V.1.ι).unit.naturality f)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Functor.id_map, Functor.map_comp] at hu
  slice_lhs 1 2 => exact hu.symm
  simp only [Category.assoc]

/-- The pullback-form affine-open base-change isomorphism as a square between
the right adjoints and the remaining pullback functors. -/
noncomputable def affineOpenPullbackPushforwardTwoSquare {X : Scheme.{u}}
    (U V : X.affineOpens) :
    TwoSquare (Modules.pushforward V.1.ι)
      (Modules.pullback (affineOpenOverlapToRight U V))
      (Modules.pullback U.1.ι)
      (Modules.pushforward (affineOpenOverlapToLeft U V)) :=
  TwoSquare.mk _ _ _ _ (affineOpenPullbackPushforwardNatIso U V).hom

/-- The mate of affine-open base change with respect to the two
pullback--pushforward adjunctions. -/
noncomputable def affineOpenPullbackPushforwardMate {X : Scheme.{u}}
    (U V : X.affineOpens) :
    TwoSquare (Modules.pullback U.1.ι) (Modules.pullback V.1.ι)
      (Modules.pullback (affineOpenOverlapToLeft U V))
      (Modules.pullback (affineOpenOverlapToRight U V)) :=
  (mateEquiv (Modules.pullbackPushforwardAdjunction V.1.ι)
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V))).symm
    (affineOpenPullbackPushforwardTwoSquare U V)

/-- The canonical pseudofunctorial identification of the two iterated
pullbacks over an affine-open overlap, assembled as a natural isomorphism. -/
noncomputable def affineOpenOverlapIteratedPullbackNatIso {X : Scheme.{u}}
    (U V : X.affineOpens) :
    Modules.pullback U.1.ι ⋙
        Modules.pullback (affineOpenOverlapToLeft U V) ≅
      Modules.pullback V.1.ι ⋙
        Modules.pullback (affineOpenOverlapToRight U V) :=
  Modules.pullbackComp (affineOpenOverlapToLeft U V) U.1.ι ≪≫
    Modules.pullbackCongr (affineOpenOverlap_fac U V) ≪≫
    (Modules.pullbackComp
      (affineOpenOverlapToRight U V) V.1.ι).symm

/-- The canonical pseudofunctorial overlap identification as a square of
pullback functors. -/
noncomputable def affineOpenOverlapIteratedPullbackTwoSquare {X : Scheme.{u}}
    (U V : X.affineOpens) :
    TwoSquare (Modules.pullback U.1.ι) (Modules.pullback V.1.ι)
      (Modules.pullback (affineOpenOverlapToLeft U V))
      (Modules.pullback (affineOpenOverlapToRight U V)) :=
  TwoSquare.mk _ _ _ _ (affineOpenOverlapIteratedPullbackNatIso U V).hom

/-- The component of the canonical natural overlap identification is the
previously defined iterated-pullback isomorphism. -/
lemma affineOpenOverlapIteratedPullbackNatIso_hom_app {X : Scheme.{u}}
    (U V : X.affineOpens) (M : X.Modules) :
    (affineOpenOverlapIteratedPullbackNatIso U V).hom.app M =
      (affineOpenOverlapIteratedPullbackIso U V M).hom :=
  rfl

/-- Conjugating the forward pullback-composition comparison gives the inverse
pushforward-composition comparison.  Mathlib provides the reverse orientation;
this form is convenient when decomposing iterated mates. -/
lemma conjugateEquiv_pullbackComp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Modules.pullbackPushforwardAdjunction g).comp
        (Modules.pullbackPushforwardAdjunction f))
      (Modules.pullbackComp f g).hom =
      (Modules.pushforwardComp f g).inv := by
  rw [← cancel_epi (Modules.pushforwardComp f g).hom]
  rw [← Modules.conjugateEquiv_pullbackComp_inv]
  rw [conjugateEquiv_comm _ _
    (Modules.pullbackComp f g).hom_inv_id]
  rw [Modules.conjugateEquiv_pullbackComp_inv]
  exact (Modules.pushforwardComp f g).hom_inv_id.symm

/-- Conjugating transport between pullbacks along equal scheme morphisms gives
inverse transport between the corresponding pushforwards. -/
lemma conjugateEquiv_pullbackCongr_hom {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Modules.pullbackPushforwardAdjunction g)
      (Modules.pullbackPushforwardAdjunction f)
      (Modules.pullbackCongr h).hom =
      (Modules.pushforwardCongr h).inv := by
  subst h
  simp only [Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  ext M U x
  simp [Modules.pushforwardCongr_inv_app_app]

/-- The pushforward coherence isomorphism around the commutative square of two
affine-open inclusions and their overlap. -/
noncomputable def affineOpenOverlapIteratedPushforwardNatIso {X : Scheme.{u}}
    (U V : X.affineOpens) :
    Modules.pushforward (affineOpenOverlapToRight U V) ⋙
        Modules.pushforward V.1.ι ≅
      Modules.pushforward (affineOpenOverlapToLeft U V) ⋙
        Modules.pushforward U.1.ι :=
  Modules.pushforwardComp (affineOpenOverlapToRight U V) V.1.ι ≪≫
    Modules.pushforwardCongr (affineOpenOverlap_fac U V).symm ≪≫
    (Modules.pushforwardComp
      (affineOpenOverlapToLeft U V) U.1.ι).symm

/-- Taking mates in both directions sends the canonical iterated-pullback
overlap square to the canonical iterated-pushforward overlap comparison. -/
lemma iteratedMate_affineOpenOverlapIteratedPullbackTwoSquare {X : Scheme.{u}}
    (U V : X.affineOpens) :
    (mateEquiv
      (Modules.pullbackPushforwardAdjunction (affineOpenOverlapToRight U V))
      (Modules.pullbackPushforwardAdjunction U.1.ι)
      (mateEquiv
        (Modules.pullbackPushforwardAdjunction V.1.ι)
        (Modules.pullbackPushforwardAdjunction
          (affineOpenOverlapToLeft U V))
        (affineOpenOverlapIteratedPullbackTwoSquare U V))).natTrans =
      (affineOpenOverlapIteratedPushforwardNatIso U V).hom := by
  rw [iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv
      ((Modules.pullbackPushforwardAdjunction V.1.ι).comp
        (Modules.pullbackPushforwardAdjunction
          (affineOpenOverlapToRight U V)))
      ((Modules.pullbackPushforwardAdjunction U.1.ι).comp
        (Modules.pullbackPushforwardAdjunction
          (affineOpenOverlapToLeft U V)))
      ((Modules.pullbackComp
          (affineOpenOverlapToLeft U V) U.1.ι).hom ≫
        (Modules.pullbackCongr (affineOpenOverlap_fac U V)).hom ≫
        (Modules.pullbackComp
          (affineOpenOverlapToRight U V) V.1.ι).inv) = _
  rw [← conjugateEquiv_comp
    ((Modules.pullbackPushforwardAdjunction V.1.ι).comp
      (Modules.pullbackPushforwardAdjunction
        (affineOpenOverlapToRight U V)))
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V ≫ U.1.ι))
    ((Modules.pullbackPushforwardAdjunction U.1.ι).comp
      (Modules.pullbackPushforwardAdjunction
        (affineOpenOverlapToLeft U V)))
    ((Modules.pullbackCongr (affineOpenOverlap_fac U V)).hom ≫
      (Modules.pullbackComp
        (affineOpenOverlapToRight U V) V.1.ι).inv)
    (Modules.pullbackComp
      (affineOpenOverlapToLeft U V) U.1.ι).hom]
  rw [← conjugateEquiv_comp
    ((Modules.pullbackPushforwardAdjunction V.1.ι).comp
      (Modules.pullbackPushforwardAdjunction
        (affineOpenOverlapToRight U V)))
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToRight U V ≫ V.1.ι))
    (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V ≫ U.1.ι))
    (Modules.pullbackComp
      (affineOpenOverlapToRight U V) V.1.ι).inv
    (Modules.pullbackCongr (affineOpenOverlap_fac U V)).hom]
  rw [Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_pullbackCongr_hom,
    conjugateEquiv_pullbackComp_hom]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise coherence between literal affine-open base change followed by
the restriction counit and the canonical iterated-pushforward comparison. -/
lemma affineOpenRestrictPushforward_counit_apply {X : Scheme.{u}}
    (U V : X.affineOpens)
    (M : (affineOpenOverlapLeft U V).toScheme.Modules)
    (W : U.1.toScheme.Opens)
    (x : Γ((Modules.restrictFunctor U.1.ι).obj
      ((Modules.pushforward V.1.ι).obj
        ((Modules.pushforward (affineOpenOverlapToRight U V)).obj M)), W)) :
    (((Modules.pushforward (affineOpenOverlapToLeft U V)).map
        ((Modules.restrictAdjunction
          (affineOpenOverlapToRight U V)).counit.app M)).app W)
      ((affineOpenRestrictPushforwardIso U V
        ((Modules.pushforward (affineOpenOverlapToRight U V)).obj M)).hom.app W x) =
    (((Modules.restrictAdjunction U.1.ι).counit.app
        ((Modules.pushforward (affineOpenOverlapToLeft U V)).obj M)).app W)
      (((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M).app
        (U.1.ι ''ᵁ W) x) := by
  rw [Modules.pushforward_map_app,
    Modules.restrictAdjunction_counit_app_app,
    Modules.restrictAdjunction_counit_app_app,
    affineOpenRestrictPushforwardIso_hom_app_apply]
  simp only [Functor.id_obj, Modules.pushforward_obj_obj,
    Functor.comp_obj, eqToHom_op]
  exact ConcreteCategory.congr_hom (presheaf_map_twoStep_eq M _ _ _ _) x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Literal affine-open base change intertwines the two restriction counits
with the canonical iterated-pushforward comparison. -/
lemma affineOpenRestrictPushforwardIso_comp_counit {X : Scheme.{u}}
    (U V : X.affineOpens)
    (M : (affineOpenOverlapLeft U V).toScheme.Modules) :
    (affineOpenRestrictPushforwardIso U V
        ((Modules.pushforward (affineOpenOverlapToRight U V)).obj M)).hom ≫
      (Modules.pushforward (affineOpenOverlapToLeft U V)).map
        ((Modules.restrictAdjunction
          (affineOpenOverlapToRight U V)).counit.app M) =
    (Modules.restrictFunctor U.1.ι).map
        ((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M) ≫
      (Modules.restrictAdjunction U.1.ι).counit.app
        ((Modules.pushforward (affineOpenOverlapToLeft U V)).obj M) := by
  ext W x
  simp only [Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply]
  have h := restrictFunctor_map_app_apply U.1.ι
    ((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M) W x
  calc
    _ = (((Modules.restrictAdjunction U.1.ι).counit.app
        ((Modules.pushforward (affineOpenOverlapToLeft U V)).obj M)).app W)
      (((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M).app
        (U.1.ι ''ᵁ W) x) :=
      affineOpenRestrictPushforward_counit_apply U V M W x
    _ = _ := congrArg
      (fun y ↦ ((Modules.restrictAdjunction U.1.ι).counit.app
        ((Modules.pushforward (affineOpenOverlapToLeft U V)).obj M)).app W y) h.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking the horizontal mate of restriction-defined affine-open base change
gives the canonical iterated-pushforward comparison. -/
lemma mate_affineOpenPullbackPushforwardTwoSquare {X : Scheme.{u}}
    (U V : X.affineOpens) :
    (mateEquiv
      (Modules.pullbackPushforwardAdjunction (affineOpenOverlapToRight U V))
      (Modules.pullbackPushforwardAdjunction U.1.ι)
      (affineOpenPullbackPushforwardTwoSquare U V)).natTrans =
      (affineOpenOverlapIteratedPushforwardNatIso U V).hom := by
  apply NatTrans.ext
  funext M
  apply ((Modules.restrictAdjunction U.1.ι).homEquiv _ _).symm.injective
  rw [Modules.restrict_homEquiv_symm_eq_iso_hom_comp,
    Modules.restrict_homEquiv_symm_eq_iso_hom_comp]
  rw [Adjunction.homEquiv_symm_apply]
  have hm := mateEquiv_counit
    (Modules.pullbackPushforwardAdjunction (affineOpenOverlapToRight U V))
    (Modules.pullbackPushforwardAdjunction U.1.ι)
    (affineOpenPullbackPushforwardTwoSquare U V) M
  slice_lhs 2 3 => exact hm
  rw [Adjunction.homEquiv_symm_apply]
  change (Modules.restrictFunctorIsoPullback U.1.ι).hom.app _ ≫
      ((affineOpenPullbackPushforwardIso U V
          ((Modules.pushforward (affineOpenOverlapToRight U V)).obj M)).hom ≫
        (Modules.pushforward (affineOpenOverlapToLeft U V)).map
          ((Modules.pullbackPushforwardAdjunction
            (affineOpenOverlapToRight U V)).counit.app M)) =
    (Modules.restrictFunctorIsoPullback U.1.ι).hom.app _ ≫
      ((Modules.pullback U.1.ι).map
          ((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M) ≫
        (Modules.pullbackPushforwardAdjunction U.1.ι).counit.app _)
  rw [affineOpenPullbackPushforwardIso_hom]
  simp only [Category.assoc]
  slice_lhs 1 2 => exact
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _).hom_inv_id
  rw [Category.id_comp]
  slice_lhs 2 3 => rw [← Functor.map_comp,
    Modules.restrictFunctorIsoPullback_hom_app_pushforward_comp_counit]
  slice_rhs 1 2 => exact
    ((Modules.restrictFunctorIsoPullback U.1.ι).hom.naturality
      ((affineOpenOverlapIteratedPushforwardNatIso U V).hom.app M)).symm
  slice_rhs 2 3 => exact
    Modules.restrictFunctorIsoPullback_hom_app_pushforward_comp_counit U.1.ι _
  exact affineOpenRestrictPushforwardIso_comp_counit U V M

/-- The mate of restriction-defined affine-open base change is the canonical
pseudofunctorial comparison between the two iterated pullbacks. -/
lemma affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare
    {X : Scheme.{u}} (U V : X.affineOpens) :
    affineOpenPullbackPushforwardMate U V =
      affineOpenOverlapIteratedPullbackTwoSquare U V := by
  let inner :
      TwoSquare (Modules.pullback U.1.ι) (Modules.pullback V.1.ι)
          (Modules.pullback (affineOpenOverlapToLeft U V))
          (Modules.pullback (affineOpenOverlapToRight U V)) ≃
        TwoSquare (Modules.pushforward V.1.ι)
          (Modules.pullback (affineOpenOverlapToRight U V))
          (Modules.pullback U.1.ι)
          (Modules.pushforward (affineOpenOverlapToLeft U V)) := mateEquiv
    (Modules.pullbackPushforwardAdjunction V.1.ι)
    (Modules.pullbackPushforwardAdjunction (affineOpenOverlapToLeft U V))
  let outer :
      TwoSquare (Modules.pushforward V.1.ι)
          (Modules.pullback (affineOpenOverlapToRight U V))
          (Modules.pullback U.1.ι)
          (Modules.pushforward (affineOpenOverlapToLeft U V)) ≃
        TwoSquare (Modules.pushforward (affineOpenOverlapToRight U V))
          (Modules.pushforward (affineOpenOverlapToLeft U V))
          (Modules.pushforward V.1.ι) (Modules.pushforward U.1.ι) := mateEquiv
    (Modules.pullbackPushforwardAdjunction (affineOpenOverlapToRight U V))
    (Modules.pullbackPushforwardAdjunction U.1.ι)
  have hinner : inner (affineOpenOverlapIteratedPullbackTwoSquare U V) =
      affineOpenPullbackPushforwardTwoSquare U V := by
    apply outer.injective
    apply TwoSquare.ext
    intro M
    have hc := congrArg (fun k ↦ k.app M)
      (iteratedMate_affineOpenOverlapIteratedPullbackTwoSquare U V)
    have hb := congrArg (fun k ↦ k.app M)
      (mate_affineOpenPullbackPushforwardTwoSquare U V)
    exact hc.trans hb.symm
  apply inner.injective
  rw [affineOpenPullbackPushforwardMate, Equiv.apply_symm_apply]
  exact hinner.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise, the mate of affine-open base change is the explicit
adjunction-induced overlap comparison. -/
lemma affineOpenPullbackPushforwardMate_app {X : Scheme.{u}}
    (U V : X.affineOpens) (M : X.Modules) :
    (affineOpenPullbackPushforwardMate U V).app M =
      affineOpenOverlapAdjunctionComparison U V M := by
  simp [affineOpenPullbackPushforwardMate,
    affineOpenPullbackPushforwardTwoSquare,
    affineOpenPullbackPushforwardNatIso,
    affineOpenOverlapAdjunctionComparison, mateEquiv]

/-- Square-level Beck--Chevalley coherence identifies the explicit
adjunction comparison with the canonical iterated-pullback comparison on
every module.  This isolates the only non-formal compatibility needed from
the restriction model of affine-open base change. -/
lemma affineOpenOverlapAdjunctionComparison_eq_iteratedPullbackIso_of_mate_eq
    {X : Scheme.{u}} (U V : X.affineOpens)
    (h : affineOpenPullbackPushforwardMate U V =
      affineOpenOverlapIteratedPullbackTwoSquare U V)
    (M : X.Modules) :
    affineOpenOverlapAdjunctionComparison U V M =
      (affineOpenOverlapIteratedPullbackIso U V M).hom := by
  rw [← affineOpenPullbackPushforwardMate_app]
  exact (congrArg (fun k ↦ k.app M) h).trans
    (affineOpenOverlapIteratedPullbackNatIso_hom_app U V M)

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- /-- Square-level Beck--Chevalley coherence implies the normalized rank-one
-- overlap equation. -/
-- lemma affineOpenOverlapUnitNormalization_naturality_of_mate_eq
--     {X : Scheme.{u}} (U V : X.affineOpens)
--     (h : affineOpenPullbackPushforwardMate U V =
--       affineOpenOverlapIteratedPullbackTwoSquare U V) :
--     affineOpenOverlapUnitNormalizationLeft U V ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.unit X.ringCatSheaf) =
--       affineOpenOverlapUnitNormalizationRight U V := by
--   apply (affineOpenOverlapUnitNormalization_naturality_iff U V).2
--   exact affineOpenOverlapAdjunctionComparison_eq_iteratedPullbackIso_of_mate_eq
--     U V h _
--
-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- -- set_option backward.isDefEq.respectTransparency.types false in
-- -- set_option backward.isDefEq.respectTransparency false in
-- -- /-- Rank-one coherence of the overlap adjunction comparison implies coherence
-- -- for a free sheaf on any index type. -/
-- lemma affineOpenOverlapFreeNormalization_naturality_of_unit {X : Scheme.{u}}
--     (U V : X.affineOpens) (I : Type u)
--     (hunit : affineOpenOverlapUnitNormalizationLeft U V ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.unit X.ringCatSheaf) =
--       affineOpenOverlapUnitNormalizationRight U V) :
--     affineOpenOverlapFreeNormalizationLeft U V I ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.free (R := X.ringCatSheaf) I) =
--       affineOpenOverlapFreeNormalizationRight U V I := by
--   apply Cofan.IsColimit.hom_ext
--     (SheafOfModules.isColimitFreeCofan I)
--   intro i
--   simp only [SheafOfModules.freeCofan_inj]
--   rw [← Category.assoc]
--   rw [ιFree_comp_affineOpenOverlapFreeNormalizationLeft]
--   rw [Category.assoc]
--   rw [← affineOpenOverlapAdjunctionComparison_naturality]
--   rw [← Category.assoc]
--   rw [hunit]
--   rw [← ιFree_comp_affineOpenOverlapFreeNormalizationRight]
--
-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- -- set_option backward.isDefEq.respectTransparency.types false in
-- -- set_option backward.isDefEq.respectTransparency false in
-- -- /-- If the adjunction-induced overlap comparison has the canonical rank-one
-- -- normalization, then on every free sheaf it is the canonical comparison between
-- -- the two iterated pullbacks. -/
-- lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso
--     {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u)
--     (hunit : affineOpenOverlapUnitNormalizationLeft U V ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.unit X.ringCatSheaf) =
--       affineOpenOverlapUnitNormalizationRight U V) :
--     affineOpenOverlapAdjunctionComparison U V
--         (SheafOfModules.free (R := X.ringCatSheaf) I) =
--       (affineOpenOverlapIteratedPullbackIso U V
--         (SheafOfModules.free (R := X.ringCatSheaf) I)).hom := by
--   rw [← cancel_epi (affineOpenOverlapFreeNormalizationLeft U V I)]
--   rw [affineOpenOverlapFreeNormalization_naturality_of_unit U V I hunit]
--   exact (affineOpenOverlapFreeNormalization_comp_iteratedPullbackIso U V I).symm
--
-- -- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- -- out; it no longer elaborates.
-- -- /-- Square-level Beck--Chevalley coherence specializes to the canonical
-- -- comparison on every finite free sheaf. -/
-- -- lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso_of_mate_eq
-- --     {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u)
-- --     (h : affineOpenPullbackPushforwardMate U V =
-- --       affineOpenOverlapIteratedPullbackTwoSquare U V) :
-- --     affineOpenOverlapAdjunctionComparison U V
-- --         (SheafOfModules.free (R := X.ringCatSheaf) I) =
-- --       (affineOpenOverlapIteratedPullbackIso U V
-- --         (SheafOfModules.free (R := X.ringCatSheaf) I)).hom :=
-- --   affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso U V I
-- --     (affineOpenOverlapUnitNormalization_naturality_of_mate_eq U V h)
-- --
-- -- /-- The adjunction-induced affine-open overlap comparison is the canonical
-- -- iterated-pullback comparison on every module. -/

/-- Square-level Beck--Chevalley coherence implies the normalized rank-one
overlap equation. -/
lemma affineOpenOverlapUnitNormalization_naturality_of_mate_eq
    {X : Scheme.{u}} (U V : X.affineOpens)
    (h : affineOpenPullbackPushforwardMate U V =
      affineOpenOverlapIteratedPullbackTwoSquare U V) :
    affineOpenOverlapUnitNormalizationLeft U V ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.unit X.ringCatSheaf) =
      affineOpenOverlapUnitNormalizationRight U V := by
  apply (affineOpenOverlapUnitNormalization_naturality_iff U V).2
  exact affineOpenOverlapAdjunctionComparison_eq_iteratedPullbackIso_of_mate_eq
    U V h _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Rank-one coherence of the overlap adjunction comparison implies coherence
for a free sheaf on any index type. -/
lemma affineOpenOverlapFreeNormalization_naturality_of_unit {X : Scheme.{u}}
    (U V : X.affineOpens) (I : Type u)
    (hunit : affineOpenOverlapUnitNormalizationLeft U V ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.unit X.ringCatSheaf) =
      affineOpenOverlapUnitNormalizationRight U V) :
    affineOpenOverlapFreeNormalizationLeft U V I ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.free (R := X.ringCatSheaf) I) =
      affineOpenOverlapFreeNormalizationRight U V I := by
  apply Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan I)
  intro i
  simp only [SheafOfModules.freeCofan_inj]
  rw [← Category.assoc]
  rw [ιFree_comp_affineOpenOverlapFreeNormalizationLeft]
  rw [Category.assoc]
  rw [← affineOpenOverlapAdjunctionComparison_naturality]
  rw [← Category.assoc]
  rw [hunit]
  rw [← ιFree_comp_affineOpenOverlapFreeNormalizationRight]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- If the adjunction-induced overlap comparison has the canonical rank-one
normalization, then on every free sheaf it is the canonical comparison between
the two iterated pullbacks. -/
lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso
    {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u)
    (hunit : affineOpenOverlapUnitNormalizationLeft U V ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.unit X.ringCatSheaf) =
      affineOpenOverlapUnitNormalizationRight U V) :
    affineOpenOverlapAdjunctionComparison U V
        (SheafOfModules.free (R := X.ringCatSheaf) I) =
      (affineOpenOverlapIteratedPullbackIso U V
        (SheafOfModules.free (R := X.ringCatSheaf) I)).hom := by
  rw [← cancel_epi (affineOpenOverlapFreeNormalizationLeft U V I)]
  rw [affineOpenOverlapFreeNormalization_naturality_of_unit U V I hunit]
  exact (affineOpenOverlapFreeNormalization_comp_iteratedPullbackIso U V I).symm

/-- Square-level Beck--Chevalley coherence specializes to the canonical
comparison on every finite free sheaf. -/
lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso_of_mate_eq
    {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u)
    (h : affineOpenPullbackPushforwardMate U V =
      affineOpenOverlapIteratedPullbackTwoSquare U V) :
    affineOpenOverlapAdjunctionComparison U V
        (SheafOfModules.free (R := X.ringCatSheaf) I) =
      (affineOpenOverlapIteratedPullbackIso U V
        (SheafOfModules.free (R := X.ringCatSheaf) I)).hom :=
  affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso U V I
    (affineOpenOverlapUnitNormalization_naturality_of_mate_eq U V h)

/-- The adjunction-induced affine-open overlap comparison is the canonical
iterated-pullback comparison on every module. -/
lemma affineOpenOverlapAdjunctionComparison_eq_iteratedPullbackIso
    {X : Scheme.{u}} (U V : X.affineOpens) (M : X.Modules) :
    affineOpenOverlapAdjunctionComparison U V M =
      (affineOpenOverlapIteratedPullbackIso U V M).hom :=
  affineOpenOverlapAdjunctionComparison_eq_iteratedPullbackIso_of_mate_eq
    U V (affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare U V) M

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- /-- The rank-one affine-open overlap normalizations are compatible with the
-- adjunction-induced comparison. -/
-- lemma affineOpenOverlapUnitNormalization_naturality {X : Scheme.{u}}
--     (U V : X.affineOpens) :
--     affineOpenOverlapUnitNormalizationLeft U V ≫
--         affineOpenOverlapAdjunctionComparison U V
--           (SheafOfModules.unit X.ringCatSheaf) =
--       affineOpenOverlapUnitNormalizationRight U V :=
--   affineOpenOverlapUnitNormalization_naturality_of_mate_eq U V
--     (affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare U V)
--
-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- -- /-- On every finite free sheaf, the adjunction-induced affine-open overlap
-- -- comparison is the canonical iterated-pullback comparison. -/
-- lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso'
--     {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u) :
--     affineOpenOverlapAdjunctionComparison U V
--         (SheafOfModules.free (R := X.ringCatSheaf) I) =
--       (affineOpenOverlapIteratedPullbackIso U V
--         (SheafOfModules.free (R := X.ringCatSheaf) I)).hom :=
--   affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso_of_mate_eq
--     U V I (affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare U V)
--
-- /-- A quotient presentation restricted along an arbitrary open immersion, with
-- its source normalized to the canonical free sheaf on the source scheme. -/

/-- The rank-one affine-open overlap normalizations are compatible with the
adjunction-induced comparison. -/
lemma affineOpenOverlapUnitNormalization_naturality {X : Scheme.{u}}
    (U V : X.affineOpens) :
    affineOpenOverlapUnitNormalizationLeft U V ≫
        affineOpenOverlapAdjunctionComparison U V
          (SheafOfModules.unit X.ringCatSheaf) =
      affineOpenOverlapUnitNormalizationRight U V :=
  affineOpenOverlapUnitNormalization_naturality_of_mate_eq U V
    (affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare U V)

/-- On every finite free sheaf, the adjunction-induced affine-open overlap
comparison is the canonical iterated-pullback comparison. -/
lemma affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso'
    {X : Scheme.{u}} (U V : X.affineOpens) (I : Type u) :
    affineOpenOverlapAdjunctionComparison U V
        (SheafOfModules.free (R := X.ringCatSheaf) I) =
      (affineOpenOverlapIteratedPullbackIso U V
        (SheafOfModules.free (R := X.ringCatSheaf) I)).hom :=
  affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso_of_mate_eq
    U V I (affineOpenPullbackPushforwardMate_eq_iteratedPullbackTwoSquare U V)

/-- A quotient presentation restricted along an arbitrary open immersion, with
its source normalized to the canonical free sheaf on the source scheme. -/
noncomputable def restrictPresentationHom {X Y : Scheme.{u}} {n q : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (f : Y ⟶ X)
    [IsOpenImmersion f] :
    SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      (Modules.restrictFunctor f).obj x.Q :=
  (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫
    (Modules.restrictFunctorIsoPullback f).inv.app _ ≫
    (Modules.restrictFunctor f).map x.π

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma ιFree_comp_restrictPresentationHom {X Y : Scheme.{u}} {n q : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (f : Y ⟶ X)
    [IsOpenImmersion f] (i : ULift.{u} (Fin n)) :
    SheafOfModules.ιFree i ≫ restrictPresentationHom x f =
      (Modules.restrictUnitIso f).inv ≫
        (Modules.restrictFunctor f).map (SheafOfModules.ιFree i ≫ x.π) := by
  rw [restrictPresentationHom, ← Category.assoc,
    Modules.ιFree_comp_pullbackFreeIso_inv]
  simp only [Category.assoc]
  slice_lhs 1 2 =>
    rw [Modules.pullbackObjUnitToUnit_inv_comp_pullback_map]
  simp

/-- Restriction of the canonical free sheaf along an open immersion, normalized
to the canonical free sheaf on the source. -/
noncomputable def restrictFreeHom {X Y : Scheme.{u}} {n : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (Modules.restrictFunctor f).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ⟶
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)) :=
  (Modules.restrictFunctorIsoPullback f).hom.app _ ≫
    (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a quotient map is the normalized restricted presentation after
the canonical comparison of free sheaves. -/
lemma restrict_map_eq_restrictFreeHom_comp {X Y : Scheme.{u}} {n q : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (f : Y ⟶ X)
    [IsOpenImmersion f] :
    (Modules.restrictFunctor f).map x.π =
      restrictFreeHom (n := n) f ≫ restrictPresentationHom x f := by
  rw [restrictFreeHom, restrictPresentationHom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact ((Modules.restrictFunctorIsoPullback f).app _).hom_inv_id_assoc
    ((Modules.restrictFunctor f).map x.π) |>.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized literal restriction agrees with the pullback presentation
for every open immersion. -/
lemma restrictPresentationHom_eq_pullback {X Y : Scheme.{u}} {n q : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin n)) X) (f : Y ⟶ X)
    [IsOpenImmersion f] :
    restrictPresentationHom x f =
      (x.pullback f).π ≫ (Modules.restrictFunctorIsoPullback f).inv.app x.Q := by
  rw [restrictPresentationHom]
  change (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫
      ((Modules.restrictFunctorIsoPullback f).inv.app _ ≫
        (Modules.restrictFunctor f).map x.π) =
    (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫
      ((Modules.pullback f).map x.π ≫
        (Modules.restrictFunctorIsoPullback f).inv.app x.Q)
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (Modules.pullbackFreeIso f (ULift.{u} (Fin n))).inv ≫ k)
    ((Modules.restrictFunctorIsoPullback f).inv.naturality x.π).symm

/-- The two canonical quotient presentations have the same kernel point after
restriction to the whole (possibly non-affine) overlap. -/
lemma affineOpenFreeQuotient_overlap_kernelPoint {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    ((affineOpenFreeQuotient K U).pullback
        (affineOpenOverlapToLeft U V)).kernelPoint =
      ((affineOpenFreeQuotient K V).pullback
        (affineOpenOverlapToRight U V)).kernelPoint := by
  rw [← FreeQuotient.kernelPoint_pullback,
    ← FreeQuotient.kernelPoint_pullback,
    affineOpenFreeQuotient_kernelPoint,
    affineOpenFreeQuotient_kernelPoint]
  change (grassmannianFunctor q n).map (affineOpenOverlapToLeft U V).op
      ((grassmannianFunctor q n).map U.1.ι.op K) =
    (grassmannianFunctor q n).map (affineOpenOverlapToRight U V).op
      ((grassmannianFunctor q n).map V.1.ι.op K)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have h := congrArg Quiver.Hom.op (affineOpenOverlap_fac U V)
  change U.1.ι.op ≫ (affineOpenOverlapToLeft U V).op =
    V.1.ι.op ≫ (affineOpenOverlapToRight U V).op at h
  rw [h]

/-- Consequently the two restricted quotient presentations have identical glued
kernel data on the overlap. -/
lemma affineOpenFreeQuotient_overlap_kernelData {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    ((affineOpenFreeQuotient K U).pullback
        (affineOpenOverlapToLeft U V)).kernelData =
      ((affineOpenFreeQuotient K V).pullback
        (affineOpenOverlapToRight U V)).kernelData :=
  congrArg Subtype.val (affineOpenFreeQuotient_overlap_kernelPoint K U V)

/-- The canonical quotient sheaves on two affine charts become canonically
isomorphic after literal restriction to their overlap. -/
noncomputable def affineOpenOverlapRestrictIso {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    (Modules.restrictFunctor (affineOpenOverlapToLeft U V)).obj
        (affineOpenFreeQuotient K U).Q ≅
      (Modules.restrictFunctor (affineOpenOverlapToRight U V)).obj
        (affineOpenFreeQuotient K V).Q :=
  (Modules.restrictFunctorIsoPullback (affineOpenOverlapToLeft U V)).app _ ≪≫
    isoOfKernelDataEq
      ((affineOpenFreeQuotient K U).pullback (affineOpenOverlapToLeft U V))
      ((affineOpenFreeQuotient K V).pullback (affineOpenOverlapToRight U V))
      (affineOpenFreeQuotient_overlap_kernelData K U V) ≪≫
    (Modules.restrictFunctorIsoPullback
      (affineOpenOverlapToRight U V)).symm.app _

set_option backward.isDefEq.respectTransparency.types false in
/-- The overlap isomorphism intertwines the two normalized restricted quotient
presentations. -/
lemma restrictPresentationHom_overlap_comp_iso {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    restrictPresentationHom (affineOpenFreeQuotient K U)
        (affineOpenOverlapToLeft U V) ≫
      (affineOpenOverlapRestrictIso K U V).hom =
    restrictPresentationHom (affineOpenFreeQuotient K V)
      (affineOpenOverlapToRight U V) := by
  rw [restrictPresentationHom_eq_pullback, restrictPresentationHom_eq_pullback]
  let x := (affineOpenFreeQuotient K U).pullback (affineOpenOverlapToLeft U V)
  let y := (affineOpenFreeQuotient K V).pullback (affineOpenOverlapToRight U V)
  let ex := (Modules.restrictFunctorIsoPullback
    (affineOpenOverlapToLeft U V)).app (affineOpenFreeQuotient K U).Q
  let ey := (Modules.restrictFunctorIsoPullback
    (affineOpenOverlapToRight U V)).app (affineOpenFreeQuotient K V).Q
  let e := isoOfKernelDataEq x y (affineOpenFreeQuotient_overlap_kernelData K U V)
  change x.π ≫ (ex.inv ≫ ex.hom ≫ e.hom ≫ ey.inv) = y.π ≫ ey.inv
  rw [← comp_homOfKernelDataEq x y
    (affineOpenFreeQuotient_overlap_kernelData K U V)]
  let _ := x.epi
  rw [Category.assoc, cancel_epi]
  exact ex.inv_hom_id_assoc (e.hom ≫ ey.inv)

/-- The comparison from the canonical quotient on `U` to the `V`-detection
coordinate restricted to `U`, obtained by descent across the overlap `U ∩ V`. -/
noncomputable def affineOpenDetectionRestrictFactor
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    (affineOpenFreeQuotient K U).Q ⟶
      (Modules.restrictFunctor U.1.ι).obj
        ((Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) :=
  (Modules.pullbackPushforwardAdjunction
      (affineOpenOverlapToLeft U V)).homEquiv _ _
      (isoOfKernelDataEq
        ((affineOpenFreeQuotient K U).pullback
          (affineOpenOverlapToLeft U V))
        ((affineOpenFreeQuotient K V).pullback
          (affineOpenOverlapToRight U V))
        (affineOpenFreeQuotient_overlap_kernelData K U V)).hom ≫
    (affineOpenPullbackPushforwardIso U V
      (affineOpenFreeQuotient K V).Q).inv ≫
    (Modules.restrictFunctorIsoPullback U.1.ι).inv.app _

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- set_option backward.isDefEq.respectTransparency.types false in
-- set_option backward.isDefEq.respectTransparency false in
-- /-- Every cross-chart detection coordinate restricted to `U` factors through
-- the canonical quotient presentation on `U`. -/
-- lemma affineOpenFreeQuotient_comp_detectionRestrictFactor
--     {X : Scheme.{u}} {n q : ℕ}
--     (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
--     (affineOpenFreeQuotient K U).π ≫ affineOpenDetectionRestrictFactor K U V =
--       affineOpenDetectionRestrictComponent K U V := by
--   rw [affineOpenDetectionRestrictComponent]
--   rw [← cancel_mono ((Modules.restrictFunctorIsoPullback U.1.ι).hom.app _)]
--   rw [affineOpenDetectionRestrictFactor]
--   simp only [Category.assoc]
--   slice_lhs 4 5 => exact
--     ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv_hom_id
--   slice_rhs 2 3 => exact
--     ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv_hom_id
--   simp only [Category.comp_id]
--   rw [← cancel_mono (affineOpenPullbackPushforwardIso U V
--     (affineOpenFreeQuotient K V).Q).hom]
--   simp only [Category.assoc]
--   slice_lhs 3 4 => exact
--     (affineOpenPullbackPushforwardIso U V
--       (affineOpenFreeQuotient K V).Q).inv_hom_id
--   slice_lhs 2 3 => exact Category.comp_id _
--   apply (Modules.pullbackPushforwardAdjunction
--     (affineOpenOverlapToLeft U V)).homEquiv _ _ |>.symm.injective
--   rw [← (Modules.pullbackPushforwardAdjunction
--     (affineOpenOverlapToLeft U V)).homEquiv_naturality_left]
--   erw [Equiv.symm_apply_apply]
--   rw [affineOpenDetectionComponent, affineOpenDetectionMap]
--   rw [Category.assoc, affineOpenPullbackPushforwardIso_homEquiv]
--   rw [(Modules.pullbackPushforwardAdjunction
--     (affineOpenOverlapToLeft U V)).homEquiv_counit]
--   rw [Functor.map_comp, Category.assoc]
--   rw [← (Modules.pullbackPushforwardAdjunction
--     (affineOpenOverlapToLeft U V)).homEquiv_counit]
--   erw [Equiv.symm_apply_apply]
--   rw [← cancel_epi (Modules.pullbackFreeIso
--     (affineOpenOverlapToLeft U V) (ULift.{u} (Fin n))).inv]
--   change
--     (((affineOpenFreeQuotient K U).pullback
--         (affineOpenOverlapToLeft U V)).π ≫
--       (isoOfKernelDataEq
--         ((affineOpenFreeQuotient K U).pullback
--           (affineOpenOverlapToLeft U V))
--         ((affineOpenFreeQuotient K V).pullback
--           (affineOpenOverlapToRight U V))
--         (affineOpenFreeQuotient_overlap_kernelData K U V)).hom) = _
--   slice_lhs 1 2 =>
--     exact comp_homOfKernelDataEq _ _
--       (affineOpenFreeQuotient_overlap_kernelData K U V)
--   change ((affineOpenFreeQuotient K V).pullback
--       (affineOpenOverlapToRight U V)).π =
--     affineOpenOverlapFreeNormalizationLeft U V (ULift.{u} (Fin n)) ≫
--       affineOpenOverlapAdjunctionComparison U V
--         (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ≫
--       (Modules.pullback (affineOpenOverlapToRight U V)).map
--         ((Modules.pullbackFreeIso V.1.ι (ULift.{u} (Fin n))).hom ≫
--           (affineOpenFreeQuotient K V).π)
--   rw [affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso']
--   rw [← Category.assoc,
--     affineOpenOverlapFreeNormalization_comp_iteratedPullbackIso]
--   rw [affineOpenOverlapFreeNormalizationRight, Functor.map_comp]
--   simp only [Category.assoc]
--   slice_rhs 2 3 => exact
--     ((Modules.pullback (affineOpenOverlapToRight U V)).mapIso
--       (Modules.pullbackFreeIso V.1.ι (ULift.{u} (Fin n)))).inv_hom_id
--   rfl
--
-- /-- Product of the pushforwards of all canonical affine-open quotient sheaves. -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every cross-chart detection coordinate restricted to `U` factors through
the canonical quotient presentation on `U`. -/
lemma affineOpenFreeQuotient_comp_detectionRestrictFactor
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U V : X.affineOpens) :
    (affineOpenFreeQuotient K U).π ≫ affineOpenDetectionRestrictFactor K U V =
      affineOpenDetectionRestrictComponent K U V := by
  rw [affineOpenDetectionRestrictComponent]
  rw [← cancel_mono ((Modules.restrictFunctorIsoPullback U.1.ι).hom.app _)]
  rw [affineOpenDetectionRestrictFactor]
  simp only [Category.assoc]
  slice_lhs 4 5 => exact
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv_hom_id
  slice_rhs 2 3 => exact
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv_hom_id
  simp only [Category.comp_id]
  rw [← cancel_mono (affineOpenPullbackPushforwardIso U V
    (affineOpenFreeQuotient K V).Q).hom]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact
    (affineOpenPullbackPushforwardIso U V
      (affineOpenFreeQuotient K V).Q).inv_hom_id
  slice_lhs 2 3 => exact Category.comp_id _
  apply (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).homEquiv _ _ |>.symm.injective
  rw [← (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).homEquiv_naturality_left]
  erw [Equiv.symm_apply_apply]
  rw [affineOpenDetectionComponent, affineOpenDetectionMap]
  rw [Category.assoc, affineOpenPullbackPushforwardIso_homEquiv]
  rw [(Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).homEquiv_counit]
  rw [Functor.map_comp, Category.assoc]
  rw [← (Modules.pullbackPushforwardAdjunction
    (affineOpenOverlapToLeft U V)).homEquiv_counit]
  erw [Equiv.symm_apply_apply]
  rw [← cancel_epi (Modules.pullbackFreeIso
    (affineOpenOverlapToLeft U V) (ULift.{u} (Fin n))).inv]
  change
    (((affineOpenFreeQuotient K U).pullback
        (affineOpenOverlapToLeft U V)).π ≫
      (isoOfKernelDataEq
        ((affineOpenFreeQuotient K U).pullback
          (affineOpenOverlapToLeft U V))
        ((affineOpenFreeQuotient K V).pullback
          (affineOpenOverlapToRight U V))
        (affineOpenFreeQuotient_overlap_kernelData K U V)).hom) = _
  slice_lhs 1 2 =>
    exact comp_homOfKernelDataEq _ _
      (affineOpenFreeQuotient_overlap_kernelData K U V)
  change ((affineOpenFreeQuotient K V).pullback
      (affineOpenOverlapToRight U V)).π =
    affineOpenOverlapFreeNormalizationLeft U V (ULift.{u} (Fin n)) ≫
      affineOpenOverlapAdjunctionComparison U V
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) ≫
      (Modules.pullback (affineOpenOverlapToRight U V)).map
        ((Modules.pullbackFreeIso V.1.ι (ULift.{u} (Fin n))).hom ≫
          (affineOpenFreeQuotient K V).π)
  rw [affineOpenOverlapAdjunctionComparison_free_eq_iteratedPullbackIso']
  rw [← Category.assoc,
    affineOpenOverlapFreeNormalization_comp_iteratedPullbackIso]
  rw [affineOpenOverlapFreeNormalizationRight, Functor.map_comp]
  simp only [Category.assoc]
  slice_rhs 2 3 => exact
    ((Modules.pullback (affineOpenOverlapToRight U V)).mapIso
      (Modules.pullbackFreeIso V.1.ι (ULift.{u} (Fin n)))).inv_hom_id
  rfl

/-- Product of the pushforwards of all canonical affine-open quotient sheaves. -/
noncomputable def affineDetectionTarget {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) : X.Modules :=
  ∏ᶜ fun U : X.affineOpens ↦
    (Modules.pushforward U.1.ι).obj (affineOpenFreeQuotient K U).Q

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the restricted simultaneous detection target are canonically
the product of the sections of its restricted chartwise factors. -/
noncomputable def affineDetectionRestrictSectionsIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens)
    (W : U.1.toScheme.Opensᵒᵖ) :
    ((Modules.restrictFunctor U.1.ι).obj (affineDetectionTarget K)).val.obj W ≅
      ∏ᶜ fun V : X.affineOpens ↦
        ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.1.ι).obj
            (affineOpenFreeQuotient K V).Q)).val.obj W := by
  let F : X.affineOpens → X.Modules := fun V ↦
    (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q
  let E := SheafOfModules.evaluation X.ringCatSheaf
      (op (U.1.ι ''ᵁ W.unop)) ⋙
    ModuleCat.restrictScalars (U.1.ι.appIso W.unop).inv.hom
  letI : PreservesLimit (Discrete.functor F)
      (SheafOfModules.evaluation X.ringCatSheaf
        (op (U.1.ι ''ᵁ W.unop))) :=
    SheafOfModules.evaluationPreservesLimit _ _
  letI : PreservesLimit (Discrete.functor F) E := by
    dsimp only [E]
    infer_instance
  exact PreservesProduct.iso E F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The sections/product comparison followed by a projection is evaluation
of the corresponding projection of module sheaves. -/
@[reassoc]
lemma affineDetectionRestrictSectionsIso_hom_π
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens)
    (W : U.1.toScheme.Opensᵒᵖ) (V : X.affineOpens) :
    (affineDetectionRestrictSectionsIso K U W).hom ≫
      Pi.π (fun V : X.affineOpens ↦
        ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.1.ι).obj
            (affineOpenFreeQuotient K V).Q)).val.obj W) V =
      ((Modules.restrictFunctor U.1.ι).map
        (Pi.π (fun V : X.affineOpens ↦
          (Modules.pushforward V.1.ι).obj
            (affineOpenFreeQuotient K V).Q) V)).val.app W := by
  let F : X.affineOpens → X.Modules := fun V ↦
    (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q
  let E := SheafOfModules.evaluation X.ringCatSheaf
      (op (U.1.ι ''ᵁ W.unop)) ⋙
    ModuleCat.restrictScalars (U.1.ι.appIso W.unop).inv.hom
  change (PreservesProduct.iso E F).hom ≫
      Pi.π (fun V ↦ E.obj (F V)) V = E.map (Pi.π F V)
  exact piComparison_comp_π E F V

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The sections/product comparison commutes with restriction maps after
projection to every affine chart. -/
lemma affineDetectionRestrictSectionsIso_naturality_π
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens)
    {W W' : U.1.toScheme.Opensᵒᵖ} (i : W ⟶ W') (V : X.affineOpens) :
    ((Modules.restrictFunctor U.1.ι).obj (affineDetectionTarget K)).val.map i ≫
      (ModuleCat.restrictScalars _).map
        ((affineDetectionRestrictSectionsIso K U W').hom ≫
          Pi.π (fun V : X.affineOpens ↦
            ((Modules.restrictFunctor U.1.ι).obj
              ((Modules.pushforward V.1.ι).obj
                (affineOpenFreeQuotient K V).Q)).val.obj W') V) =
      ((affineDetectionRestrictSectionsIso K U W).hom ≫
        Pi.π (fun V : X.affineOpens ↦
          ((Modules.restrictFunctor U.1.ι).obj
            ((Modules.pushforward V.1.ι).obj
              (affineOpenFreeQuotient K V).Q)).val.obj W) V) ≫
        ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.1.ι).obj
            (affineOpenFreeQuotient K V).Q)).val.map i := by
  rw [affineDetectionRestrictSectionsIso_hom_π,
    affineDetectionRestrictSectionsIso_hom_π]
  exact ((Modules.restrictFunctor U.1.ι).map
    (Pi.π (fun V : X.affineOpens ↦
      (Modules.pushforward V.1.ι).obj
        (affineOpenFreeQuotient K V).Q) V)).val.naturality i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise simultaneous factor through the canonical quotient on
an affine chart. -/
noncomputable def affineDetectionRestrictFactorApp
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens)
    (W : U.1.toScheme.Opensᵒᵖ) :
    (affineOpenFreeQuotient K U).Q.val.obj W ⟶
      ((Modules.restrictFunctor U.1.ι).obj
        (affineDetectionTarget K)).val.obj W :=
  Pi.lift (fun V ↦
    (affineOpenDetectionRestrictFactor K U V).val.app W) ≫
    (affineDetectionRestrictSectionsIso K U W).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Projecting the sectionwise simultaneous factor recovers the chosen
cross-chart factor. -/
@[reassoc]
lemma affineDetectionRestrictFactorApp_comp_sectionsIso_hom_π
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens)
    (W : U.1.toScheme.Opensᵒᵖ) (V : X.affineOpens) :
    affineDetectionRestrictFactorApp K U W ≫
      (affineDetectionRestrictSectionsIso K U W).hom ≫
      Pi.π (fun V : X.affineOpens ↦
        ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.1.ι).obj
            (affineOpenFreeQuotient K V).Q)).val.obj W) V =
      (affineOpenDetectionRestrictFactor K U V).val.app W := by
  rw [affineDetectionRestrictFactorApp]
  simp only [Category.assoc]
  slice_lhs 2 3 => exact
    (affineDetectionRestrictSectionsIso K U W).inv_hom_id
  slice_lhs 1 2 => exact Category.comp_id _
  exact Pi.lift_π _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The restricted simultaneous detection map factors through the canonical
quotient on every affine chart.  This morphism assembles the sectionwise
factors using the pointwise product isomorphism. -/
noncomputable def affineDetectionRestrictFactor
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineOpenFreeQuotient K U).Q ⟶
      (Modules.restrictFunctor U.1.ι).obj (affineDetectionTarget K) := by
  refine { val := ?_ }
  refine ⟨fun W ↦ affineDetectionRestrictFactorApp K U W, ?_⟩
  intro W W' i
  ext x
  apply (ConcreteCategory.bijective_of_isIso
    (affineDetectionRestrictSectionsIso K U W').hom).1
  apply Concrete.limit_ext
  intro V
  calc
    _ = (affineOpenDetectionRestrictFactor K U V.as).val.app W'
        ((affineOpenFreeQuotient K U).Q.val.map i x) := by
      change (Pi.π (fun V : X.affineOpens ↦
          ((Modules.restrictFunctor U.1.ι).obj
            ((Modules.pushforward V.1.ι).obj
              (affineOpenFreeQuotient K V).Q)).val.obj W') V.as)
        ((affineDetectionRestrictSectionsIso K U W').hom
          (affineDetectionRestrictFactorApp K U W'
            ((affineOpenFreeQuotient K U).Q.val.map i x))) = _
      exact ConcreteCategory.congr_hom
        (affineDetectionRestrictFactorApp_comp_sectionsIso_hom_π
          K U W' V.as)
        ((affineOpenFreeQuotient K U).Q.val.map i x)
    _ = ((Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.as.1.ι).obj
            (affineOpenFreeQuotient K V.as).Q)).val.map i
          ((affineOpenDetectionRestrictFactor K U V.as).val.app W x) :=
      CategoryTheory.congr_fun
        ((affineOpenDetectionRestrictFactor K U V.as).val.naturality i) x
    _ = _ := by
      calc
        _ = ((Modules.restrictFunctor U.1.ι).obj
              ((Modules.pushforward V.as.1.ι).obj
                (affineOpenFreeQuotient K V.as).Q)).val.map i
              ((Pi.π (fun V : X.affineOpens ↦
                ((Modules.restrictFunctor U.1.ι).obj
                  ((Modules.pushforward V.1.ι).obj
                    (affineOpenFreeQuotient K V).Q)).val.obj W) V.as)
                ((affineDetectionRestrictSectionsIso K U W).hom
                  (affineDetectionRestrictFactorApp K U W x))) := by
            exact congrArg
              (fun z ↦ ((Modules.restrictFunctor U.1.ι).obj
                ((Modules.pushforward V.as.1.ι).obj
                  (affineOpenFreeQuotient K V.as).Q)).val.map i z)
              (ConcreteCategory.congr_hom
                (affineDetectionRestrictFactorApp_comp_sectionsIso_hom_π
                  K U W V.as) x).symm
        _ = _ := by
          exact (ConcreteCategory.congr_hom
            (affineDetectionRestrictSectionsIso_naturality_π K U i V.as)
            (affineDetectionRestrictFactorApp K U W x)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The literal-restriction self-coordinate factors through the canonical quotient. -/
lemma affineOpenDetectionRestrictComponent_self_factorization
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineOpenDetectionRestrictComponent K U U =
      (affineOpenFreeQuotient K U).π ≫
        ((asIso ((Modules.pullbackPushforwardAdjunction U.1.ι).counit.app
            (affineOpenFreeQuotient K U).Q)).inv ≫
          (Modules.restrictFunctorIsoPullback U.1.ι).inv.app _) := by
  rw [affineOpenDetectionRestrictComponent,
    affineOpenDetectionComponent_self_factorization, Category.assoc]
noncomputable def affineOpenDetectionRestrictSelfIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineOpenFreeQuotient K U).Q ≅
      (Modules.restrictFunctor U.1.ι).obj
        ((Modules.pushforward U.1.ι).obj (affineOpenFreeQuotient K U).Q) :=
  (asIso ((Modules.pullbackPushforwardAdjunction U.1.ι).counit.app
      (affineOpenFreeQuotient K U).Q)).symm ≪≫
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _).symm

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- /-- The self-coordinate is the canonical quotient followed by its restriction
-- isomorphism. -/
-- lemma affineOpenDetectionRestrictComponent_self_eq_comp_iso_hom
--     {X : Scheme.{u}} {n q : ℕ}
--     (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
--     affineOpenDetectionRestrictComponent K U U =
--       (affineOpenFreeQuotient K U).π ≫
--         (affineOpenDetectionRestrictSelfIso K U).hom := by
--   exact affineOpenDetectionRestrictComponent_self_factorization K U
--
-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- -- /-- The normalized self-detection coordinate has exactly the restricted kernel datum
-- -- in canonical-spectrum coordinates. -/
-- lemma ker_moduleMapPiOfHom_homOnIsoSpec_affineOpenDetectionRestrictComponent_self
--     {X : Scheme.{u}} {n q : ℕ}
--     (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
--     LinearMap.ker (moduleMapPiOfHom (homOnIsoSpec
--       (affineOpenDetectionRestrictComponent K U U))) =
--         (K.1.comap U.1.ι).submodule
--           ⟨⊤, isAffineOpen_top U.1.toScheme⟩ := by
--   rw [affineOpenDetectionRestrictComponent_self_eq_comp_iso_hom,
--     homOnIsoSpec_comp]
--   rw [ker_moduleMapPiOfHom_comp_of_isIso]
--   exact ker_moduleMapPiOfHom_homOnIsoSpec_affineOpenFreeQuotient_π K U
--
-- /-- The simultaneous affine detection map from the global finite free sheaf. -/

/-- The self-coordinate is the canonical quotient followed by its restriction
isomorphism. -/
lemma affineOpenDetectionRestrictComponent_self_eq_comp_iso_hom
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineOpenDetectionRestrictComponent K U U =
      (affineOpenFreeQuotient K U).π ≫
        (affineOpenDetectionRestrictSelfIso K U).hom := by
  exact affineOpenDetectionRestrictComponent_self_factorization K U

/-- The normalized self-detection coordinate has exactly the restricted kernel datum
in canonical-spectrum coordinates. -/
lemma ker_moduleMapPiOfHom_homOnIsoSpec_affineOpenDetectionRestrictComponent_self
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    LinearMap.ker (moduleMapPiOfHom (homOnIsoSpec
      (affineOpenDetectionRestrictComponent K U U))) =
        (K.1.comap U.1.ι).submodule
          ⟨⊤, isAffineOpen_top U.1.toScheme⟩ := by
  rw [affineOpenDetectionRestrictComponent_self_eq_comp_iso_hom,
    homOnIsoSpec_comp]
  rw [ker_moduleMapPiOfHom_comp_of_isIso]
  exact ker_moduleMapPiOfHom_homOnIsoSpec_affineOpenFreeQuotient_π K U

/-- The simultaneous affine detection map from the global finite free sheaf. -/
noncomputable def affineDetectionMap {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      affineDetectionTarget K :=
  Pi.lift (f := fun U : X.affineOpens ↦
      (Modules.pushforward U.1.ι).obj (affineOpenFreeQuotient K U).Q)
    fun U ↦ affineOpenDetectionMap K U

@[reassoc (attr := simp)]
lemma affineDetectionMap_π {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineDetectionMap K ≫ Pi.π (fun V : X.affineOpens ↦
      (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) U =
      affineOpenDetectionMap K U := by
  simp only [affineDetectionMap]
  exact Limits.limit.lift_π
    (Limits.Fan.mk (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
      fun V : X.affineOpens ↦ affineOpenDetectionMap K V) ⟨U⟩
noncomputable def affineDetectionRestrictMap {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin n)) ⟶
      (Modules.restrictFunctor U.1.ι).obj (affineDetectionTarget K) :=
  (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫
    (Modules.restrictFunctorIsoPullback U.1.ι).inv.app _ ≫
    (Modules.restrictFunctor U.1.ι).map (affineDetectionMap K)

/-- The source normalization identifying the canonical free sheaf on an affine
chart with the restriction of the ambient free sheaf. -/
noncomputable def affineDetectionRestrictSourceIso
    {X : Scheme.{u}} {n : ℕ}
    (U : X.affineOpens) :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin n)) ≅
      (Modules.restrictFunctor U.1.ι).obj
        (SheafOfModules.free (R := X.ringCatSheaf)
          (ULift.{u} (Fin n))) :=
  (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).symm ≪≫
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _).symm

/-- The normalized restricted detection map is restriction of the global map
precomposed by the source-normalization isomorphism. -/
lemma affineDetectionRestrictSourceIso_hom_comp
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineDetectionRestrictSourceIso (n := n) U).hom ≫
        (Modules.restrictFunctor U.1.ι).map (affineDetectionMap K) =
      affineDetectionRestrictMap K U := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Passing from pullback to restriction and then undoing the free-source
normalization is the canonical pullback-free comparison. -/
lemma restrictFunctorIsoPullback_inv_comp_detectionSourceIso_inv
    {X : Scheme.{u}} {n : ℕ} (U : X.affineOpens) :
    ((Modules.restrictFunctorIsoPullback U.1.ι).app
          (SheafOfModules.free (R := X.ringCatSheaf)
            (ULift.{u} (Fin n)))).inv ≫
        (affineDetectionRestrictSourceIso (n := n) U).inv =
      (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom := by
  rw [affineDetectionRestrictSourceIso, Iso.trans_inv]
  simp

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
-- set_option backward.isDefEq.respectTransparency.types false in
-- set_option backward.isDefEq.respectTransparency false in
-- /-- The restricted simultaneous detection map factors through the canonical
-- affine quotient via `affineDetectionRestrictFactor`. -/
-- lemma affineOpenFreeQuotient_comp_affineDetectionRestrictFactor
--     {X : Scheme.{u}} {n q : ℕ}
--     (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
--     (affineOpenFreeQuotient K U).π ≫ affineDetectionRestrictFactor K U =
--       affineDetectionRestrictMap K U := by
--   have hcoord (V : X.affineOpens) :
--       affineDetectionRestrictMap K U ≫
--         (Modules.restrictFunctor U.1.ι).map
--           (Pi.π (fun V : X.affineOpens ↦
--             (Modules.pushforward V.1.ι).obj
--               (affineOpenFreeQuotient K V).Q) V) =
--         affineOpenDetectionRestrictComponent K U V := by
--     rw [affineDetectionRestrictMap,
--       affineOpenDetectionRestrictComponent_eq]
--     simp only [Category.assoc]
--     rw [← Functor.map_comp, affineDetectionMap_π]
--   apply SheafOfModules.hom_ext
--   apply PresheafOfModules.hom_ext
--   intro W
--   apply (cancel_mono
--     (affineDetectionRestrictSectionsIso K U W).hom).mp
--   apply limit.hom_ext
--   intro V
--   change (affineOpenFreeQuotient K U).π.val.app W ≫
--       affineDetectionRestrictFactorApp K U W ≫
--       (affineDetectionRestrictSectionsIso K U W).hom ≫ _ = _
--   simp only [Category.assoc]
--   slice_lhs 2 4 => exact
--     affineDetectionRestrictFactorApp_comp_sectionsIso_hom_π K U W V.as
--   slice_lhs 1 2 =>
--     exact congrArg (fun k :
--       SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
--           (ULift.{u} (Fin n)) ⟶
--         (Modules.restrictFunctor U.1.ι).obj
--           ((Modules.pushforward V.as.1.ι).obj
--             (affineOpenFreeQuotient K V.as).Q) ↦ k.val.app W)
--       (affineOpenFreeQuotient_comp_detectionRestrictFactor K U V.as)
--   rw [affineDetectionRestrictSectionsIso_hom_π]
--   exact (congrArg (fun k :
--     SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
--         (ULift.{u} (Fin n)) ⟶
--       (Modules.restrictFunctor U.1.ι).obj
--         ((Modules.pushforward V.as.1.ι).obj
--           (affineOpenFreeQuotient K V.as).Q) ↦ k.val.app W)
--     (hcoord V.as)).symm
--
-- /-- Projection to the self-coordinate retracts the simultaneous affine-chart
-- factorization onto the canonical quotient. -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The restricted simultaneous detection map factors through the canonical
affine quotient via `affineDetectionRestrictFactor`. -/
lemma affineOpenFreeQuotient_comp_affineDetectionRestrictFactor
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineOpenFreeQuotient K U).π ≫ affineDetectionRestrictFactor K U =
      affineDetectionRestrictMap K U := by
  have hcoord (V : X.affineOpens) :
      affineDetectionRestrictMap K U ≫
        (Modules.restrictFunctor U.1.ι).map
          (Pi.π (fun V : X.affineOpens ↦
            (Modules.pushforward V.1.ι).obj
              (affineOpenFreeQuotient K V).Q) V) =
        affineOpenDetectionRestrictComponent K U V := by
    rw [affineDetectionRestrictMap,
      affineOpenDetectionRestrictComponent_eq]
    simp only [Category.assoc]
    rw [← Functor.map_comp, affineDetectionMap_π]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply (cancel_mono
    (affineDetectionRestrictSectionsIso K U W).hom).mp
  apply limit.hom_ext
  intro V
  change (affineOpenFreeQuotient K U).π.val.app W ≫
      affineDetectionRestrictFactorApp K U W ≫
      (affineDetectionRestrictSectionsIso K U W).hom ≫ _ = _
  simp only [Category.assoc]
  slice_lhs 2 4 => exact
    affineDetectionRestrictFactorApp_comp_sectionsIso_hom_π K U W V.as
  slice_lhs 1 2 =>
    exact congrArg (fun k :
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
          (ULift.{u} (Fin n)) ⟶
        (Modules.restrictFunctor U.1.ι).obj
          ((Modules.pushforward V.as.1.ι).obj
            (affineOpenFreeQuotient K V.as).Q) ↦ k.val.app W)
      (affineOpenFreeQuotient_comp_detectionRestrictFactor K U V.as)
  rw [affineDetectionRestrictSectionsIso_hom_π]
  exact (congrArg (fun k :
    SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin n)) ⟶
      (Modules.restrictFunctor U.1.ι).obj
        ((Modules.pushforward V.as.1.ι).obj
          (affineOpenFreeQuotient K V.as).Q) ↦ k.val.app W)
    (hcoord V.as)).symm

/-- Projection to the self-coordinate retracts the simultaneous affine-chart
factorization onto the canonical quotient. -/
noncomputable def affineDetectionRestrictRetraction
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).obj (affineDetectionTarget K) ⟶
      (affineOpenFreeQuotient K U).Q :=
  (Modules.restrictFunctor U.1.ι).map
      (Pi.π (fun V : X.affineOpens ↦
        (Modules.pushforward V.1.ι).obj
          (affineOpenFreeQuotient K V).Q) U) ≫
    (affineOpenDetectionRestrictSelfIso K U).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The simultaneous factor on an affine chart is a split monomorphism, split
by projection to that chart's own coordinate. -/
@[reassoc (attr := simp)]
lemma affineDetectionRestrictFactor_comp_retraction
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    affineDetectionRestrictFactor K U ≫
      affineDetectionRestrictRetraction K U = 𝟙 _ := by
  let _ : Epi (affineOpenFreeQuotient K U).π :=
    (affineOpenFreeQuotient K U).epi
  rw [← cancel_epi (affineOpenFreeQuotient K U).π]
  rw [Category.comp_id, ← Category.assoc,
    affineOpenFreeQuotient_comp_affineDetectionRestrictFactor]
  have hcoord :
      affineDetectionRestrictMap K U ≫
        (Modules.restrictFunctor U.1.ι).map
          (Pi.π (fun V : X.affineOpens ↦
            (Modules.pushforward V.1.ι).obj
              (affineOpenFreeQuotient K V).Q) U) =
        affineOpenDetectionRestrictComponent K U U := by
    rw [affineDetectionRestrictMap,
      affineOpenDetectionRestrictComponent_eq]
    simp only [Category.assoc]
    rw [← Functor.map_comp, affineDetectionMap_π]
  rw [affineDetectionRestrictRetraction, ← Category.assoc, hcoord,
    affineOpenDetectionRestrictComponent_self_eq_comp_iso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The categorical image of the normalized restricted detection map is
canonically isomorphic to the canonical affine quotient. -/
noncomputable instance affineDetectionRestrictImageToQuotient_isIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    IsIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
      affineDetectionRestrictRetraction K U) := by
  let _ : Epi (affineOpenFreeQuotient K U).π :=
    (affineOpenFreeQuotient K U).epi
  exact Abelian.isIso_image_ι_comp_of_epi_splitMono
      (affineDetectionRestrictMap K U) (affineOpenFreeQuotient K U).π
      (affineDetectionRestrictFactor K U)
      (affineDetectionRestrictRetraction K U)
      (affineOpenFreeQuotient_comp_affineDetectionRestrictFactor K U)
      (affineDetectionRestrictFactor_comp_retraction K U)

/-- The image epimorphism of the normalized restricted detection map followed
by the canonical image-to-quotient isomorphism is the affine quotient map. -/
lemma affineDetectionRestrictFactorThruImage_comp_imageToQuotientIso_hom
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    Abelian.factorThruImage (affineDetectionRestrictMap K U) ≫
        (asIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
          affineDetectionRestrictRetraction K U)).hom =
      (affineOpenFreeQuotient K U).π := by
  let _ : IsIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
      affineDetectionRestrictRetraction K U) :=
    affineDetectionRestrictImageToQuotient_isIso K U
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t ↦ t ≫ affineDetectionRestrictRetraction K U)
    (Abelian.image.fac (affineDetectionRestrictMap K U))) ?_
  refine Eq.trans (congrArg (fun t ↦ t ≫ affineDetectionRestrictRetraction K U)
    (affineOpenFreeQuotient_comp_affineDetectionRestrictFactor K U).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact Eq.trans (congrArg (fun t ↦ (affineOpenFreeQuotient K U).π ≫ t)
    (affineDetectionRestrictFactor_comp_retraction K U)) (Category.comp_id _)

/-- The global quotient candidate is the categorical image of the simultaneous map
to all pushed-forward affine quotients. -/
noncomputable def kernelPointQuotientSheaf {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) : X.Modules :=
  Abelian.image (affineDetectionMap K)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Restriction to an affine open preserves the categorical image defining the
global quotient candidate. -/
noncomputable def kernelPointQuotientRestrictImageIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).obj (kernelPointQuotientSheaf K) ≅
      Abelian.image ((Modules.restrictFunctor U.1.ι).map
        (affineDetectionMap K)) := by
  let _ : PreservesLimit
      (parallelPair (cokernel.π (affineDetectionMap K)) 0)
      (Modules.restrictFunctor U.1.ι) :=
    Modules.restrictFunctor_preservesKernel U.1.ι
      (cokernel.π (affineDetectionMap K))
  exact Abelian.PreservesImage.iso
    (Modules.restrictFunctor U.1.ι) (affineDetectionMap K)

/-- Changing from the restricted ambient free sheaf to the canonically
normalized affine free sheaf does not change the detection image. -/
noncomputable def affineDetectionRestrictImageIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    Abelian.image (affineDetectionRestrictMap K U) ≅
      Abelian.image ((Modules.restrictFunctor U.1.ι).map
        (affineDetectionMap K)) := by
  exact Abelian.imageIsoImageOfIsoComp
    (affineDetectionRestrictSourceIso (n := n) U)
    ((Modules.restrictFunctor U.1.ι).map (affineDetectionMap K))

/-- The source-normalization image comparison commutes with the canonical
epimorphisms onto the two images. -/
@[reassoc]
lemma affineDetectionRestrictFactorThruImage_comp_imageIso_hom
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    Abelian.factorThruImage (affineDetectionRestrictMap K U) ≫
        (affineDetectionRestrictImageIso K U).hom =
      (affineDetectionRestrictSourceIso (n := n) U).hom ≫
        Abelian.factorThruImage
          ((Modules.restrictFunctor U.1.ι).map (affineDetectionMap K)) := by
  exact Abelian.factorThruImage_comp_imageIsoImageOfIsoComp_hom
    (affineDetectionRestrictSourceIso (n := n) U)
    ((Modules.restrictFunctor U.1.ι).map (affineDetectionMap K))

/-- The source-normalization image comparison followed by the hom of its
inverse is the identity. -/
@[reassoc (attr := simp)]
lemma affineDetectionRestrictImageIso_hom_comp_symm_hom
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (affineDetectionRestrictImageIso K U).hom ≫
      (affineDetectionRestrictImageIso K U).symm.hom = 𝟙 _ :=
  (affineDetectionRestrictImageIso K U).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- On an affine chart, restriction of the global image quotient is
canonically isomorphic to the chart's canonical quotient. -/
noncomputable def kernelPointQuotientRestrictIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).obj (kernelPointQuotientSheaf K) ≅
      (affineOpenFreeQuotient K U).Q := by
  let _ : IsIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
      affineDetectionRestrictRetraction K U) :=
    affineDetectionRestrictImageToQuotient_isIso K U
  exact kernelPointQuotientRestrictImageIso K U ≪≫
    (affineDetectionRestrictImageIso K U).symm ≪≫
    asIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
      affineDetectionRestrictRetraction K U)

/-- Canonical epimorphism from the finite free sheaf to the global quotient candidate. -/
noncomputable def kernelPointQuotientMap {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      kernelPointQuotientSheaf K :=
  Abelian.factorThruImage (affineDetectionMap K)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The restricted global quotient presentation agrees with the canonical
affine quotient presentation under the restriction isomorphism. -/
lemma restrict_kernelPointQuotientMap_comp_restrictIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.restrictFunctor U.1.ι).map (kernelPointQuotientMap K) ≫
        (kernelPointQuotientRestrictIso K U).hom =
      (affineDetectionRestrictSourceIso (n := n) U).inv ≫
        (affineOpenFreeQuotient K U).π := by
  let _ := Modules.restrictFunctor_preservesKernel U.1.ι
    (cokernel.π (affineDetectionMap K))
  let _ : IsIso (Abelian.image.ι (affineDetectionRestrictMap K U) ≫
      affineDetectionRestrictRetraction K U) :=
    affineDetectionRestrictImageToQuotient_isIso K U
  rw [kernelPointQuotientMap]
  dsimp only [kernelPointQuotientRestrictIso]
  simp only [Iso.trans_hom]
  rw [kernelPointQuotientRestrictImageIso, ← Category.assoc,
    Abelian.PreservesImage.factorThruImage_iso_hom]
  rw [← cancel_epi (affineDetectionRestrictSourceIso (n := n) U).hom]
  rw [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  rw [← affineDetectionRestrictFactorThruImage_comp_imageIso_hom_assoc]
  rw [affineDetectionRestrictImageIso_hom_comp_symm_hom_assoc]
  exact affineDetectionRestrictFactorThruImage_comp_imageToQuotientIso_hom K U
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
instance kernelPointQuotientMap_epi {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    Epi (kernelPointQuotientMap K) := by
  dsimp [kernelPointQuotientMap]
  infer_instance

@[reassoc]
lemma kernelPointQuotientMap_imageι {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    kernelPointQuotientMap K ≫ Abelian.image.ι (affineDetectionMap K) =
      affineDetectionMap K :=
  Abelian.image.fac (affineDetectionMap K)

@[reassoc]
lemma kernelPointQuotientMap_to_affineOpen {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    kernelPointQuotientMap K ≫ Abelian.image.ι (affineDetectionMap K) ≫
        Pi.π (fun V : X.affineOpens ↦
          (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) U =
      affineOpenDetectionMap K U := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t ↦ t ≫ Pi.π (fun V : X.affineOpens ↦
      (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) U)
    (kernelPointQuotientMap_imageι K)) ?_
  exact affineDetectionMap_π K U

/-- Projection from the global image quotient to the pushed-forward quotient on one
affine open. -/
noncomputable def kernelPointQuotientToAffineOpenPushforward
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    kernelPointQuotientSheaf K ⟶
      (Modules.pushforward U.1.ι).obj (affineOpenFreeQuotient K U).Q :=
  Abelian.image.ι (affineDetectionMap K) ≫
    Pi.π (fun V : X.affineOpens ↦
      (Modules.pushforward V.1.ι).obj (affineOpenFreeQuotient K V).Q) U

/-- Adjunction transports the preceding projection to a comparison from the
restriction of the global quotient candidate to the canonical affine quotient. -/
noncomputable def kernelPointQuotientToAffineOpen
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.pullback U.1.ι).obj (kernelPointQuotientSheaf K) ⟶
      (affineOpenFreeQuotient K U).Q :=
  (Modules.pullbackPushforwardAdjunction U.1.ι).homEquiv _ _ |>.symm
    (kernelPointQuotientToAffineOpenPushforward K U)

/-- The canonical pullback of the global image quotient is isomorphic to the
canonical quotient on every affine chart. -/
noncomputable def kernelPointQuotientPullbackIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.pullback U.1.ι).obj (kernelPointQuotientSheaf K) ≅
      (affineOpenFreeQuotient K U).Q :=
  ((Modules.restrictFunctorIsoPullback U.1.ι).app
    (kernelPointQuotientSheaf K)).symm ≪≫
      kernelPointQuotientRestrictIso K U

/-- On every affine open, the global image presentation followed by the local
comparison is the canonical local quotient presentation. -/
lemma pullback_kernelPointQuotientMap_comp_toAffineOpen
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (Modules.pullback U.1.ι).map (kernelPointQuotientMap K) ≫
        kernelPointQuotientToAffineOpen K U =
      (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).hom ≫
        (affineOpenFreeQuotient K U).π := by
  apply (Modules.pullbackPushforwardAdjunction U.1.ι).homEquiv _ _ |>.injective
  refine Eq.trans (Adjunction.homEquiv_naturality_left _ _ _) ?_
  simp only [kernelPointQuotientToAffineOpen, Equiv.apply_symm_apply]
  change kernelPointQuotientMap K ≫
      kernelPointQuotientToAffineOpenPushforward K U = affineOpenDetectionMap K U
  exact kernelPointQuotientMap_to_affineOpen K U

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The adjunction-defined affine comparison is the canonical pullback image
isomorphism. -/
lemma kernelPointQuotientPullbackIso_hom
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (kernelPointQuotientPullbackIso K U).hom =
      kernelPointQuotientToAffineOpen K U := by
  let _ : Epi (kernelPointQuotientMap K) := kernelPointQuotientMap_epi K
  let _ : Epi ((Modules.pullback U.1.ι).map
      (kernelPointQuotientMap K)) := by
    infer_instance
  rw [← cancel_epi ((Modules.pullback U.1.ι).map
    (kernelPointQuotientMap K))]
  rw [pullback_kernelPointQuotientMap_comp_toAffineOpen]
  rw [kernelPointQuotientPullbackIso, Iso.trans_hom]
  rw [Iso.symm_hom, ← Category.assoc]
  have hnat :
      (Modules.pullback U.1.ι).map (kernelPointQuotientMap K) ≫
          ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv =
        ((Modules.restrictFunctorIsoPullback U.1.ι).app _).inv ≫
          (Modules.restrictFunctor U.1.ι).map
            (kernelPointQuotientMap K) := by
    exact (Modules.restrictFunctorIsoPullback U.1.ι).inv.naturality
      (kernelPointQuotientMap K)
  rw [hnat]
  rw [Category.assoc, restrict_kernelPointQuotientMap_comp_restrictIso]
  rw [← Category.assoc,
    restrictFunctorIsoPullback_inv_comp_detectionSourceIso_inv]

/-- The global quotient candidate restricts isomorphically to the canonical
quotient on each affine open. -/
noncomputable instance kernelPointQuotientToAffineOpen_isIso
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    IsIso (kernelPointQuotientToAffineOpen K U) := by
  rw [← kernelPointQuotientPullbackIso_hom K U]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherence is preserved by transporting a module on an open subscheme
back across the equivalence with modules over that open. -/
lemma isQuasicoherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (N : U.toScheme.Modules) [N.IsQuasicoherent] :
    ((Modules.overEquiv U).inverse.obj N).IsQuasicoherent := by
  let _ :=
    U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  let _ (Z : Over U) :
      (Over.post (X := Z) U.overEquivalence.symm.inverse).IsContinuous
        (((Opens.grothendieckTopology X).over U).over Z)
        ((Opens.grothendieckTopology U.carrier).over
          (U.overEquivalence.symm.inverse.obj Z)) := by
    have h : CoverPreserving
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology U.carrier)
        U.overEquivalence.functor :=
      Functor.IsDenseSubsite.coverPreserving
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology U.carrier) U.overEquivalence.functor
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _
        (Over.post (X := Z) U.overEquivalence.symm.inverse))
    exact h.overPost Z
  dsimp [Modules.overEquiv, TopologicalSpace.Opens.sheafOfModulesEquivOver]
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (η := U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

/-- Quasi-coherence can be detected after restriction along an isomorphism of schemes. -/
lemma isQuasicoherent_of_restrict_iso {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)
    [((Modules.restrictFunctor e.hom).obj M).IsQuasicoherent] : M.IsQuasicoherent := by
  let _ : ((Modules.restrictFunctor e.inv).obj
      ((Modules.restrictFunctor e.hom).obj M)).IsQuasicoherent := by infer_instance
  let iso : M ≅ (Modules.restrictFunctor e.inv).obj
      ((Modules.restrictFunctor e.hom).obj M) :=
    ((Modules.restrictFunctorId.app M).symm ≪≫
      (Modules.restrictFunctorCongr e.inv_hom_id).symm.app M) ≪≫
        (Modules.restrictFunctorComp e.inv e.hom).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso iso.symm inferInstance

/-- Quasi-coherence descends from the members of an arbitrary scheme-theoretic open cover. -/
lemma isQuasicoherent_of_openCover_restrict {X : Scheme.{u}} (M : X.Modules)
    (𝒰 : Scheme.OpenCover.{u} X)
    [h : ∀ i, ((Modules.restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent] :
    M.IsQuasicoherent := by
  let _ (i : 𝒰.I₀) :
      ((Modules.restrictFunctor (𝒰.f i).opensRange.ι).obj M).IsQuasicoherent := by
    let e : 𝒰.X i ≅ (𝒰.f i).opensRange.toScheme :=
      IsOpenImmersion.isoOfRangeEq (𝒰.f i) (𝒰.f i).opensRange.ι (by simp)
    let N := (Modules.restrictFunctor (𝒰.f i).opensRange.ι).obj M
    let iso : (Modules.restrictFunctor (𝒰.f i)).obj M ≅
        (Modules.restrictFunctor e.hom).obj N :=
      (Modules.restrictFunctorCongr
          (IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i)
            (𝒰.f i).opensRange.ι (by simp))).symm.app M ≪≫
        (Modules.restrictFunctorComp e.hom (𝒰.f i).opensRange.ι).app M
    let _ : ((Modules.restrictFunctor e.hom).obj N).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (𝒰.X i).ringCatSheaf).prop_of_iso iso (h i)
    exact isQuasicoherent_of_restrict_iso e N
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop
      (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) := by
    rw [_root_.Opens.coversTop_iff]
    exact 𝒰.isOpenCover_opensRange
  let _ (i : 𝒰.I₀) : (M.over (𝒰.f i).opensRange).IsQuasicoherent := by
    let U := (𝒰.f i).opensRange
    let e := Modules.overEquiv U
    let oe := Modules.overFunctorEquiv U
    let _ : (e.inverse.obj ((Modules.restrictFunctor U.ι).obj M)).IsQuasicoherent :=
      isQuasicoherent_overEquiv_inverse U _
    let iso : e.inverse.obj ((Modules.restrictFunctor U.ι).obj M) ≅ M.over U :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso iso
      (by infer_instance)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) hcov

/-- The global image quotient attached to a Grassmannian kernel point is
quasi-coherent. -/
lemma kernelPointQuotientSheaf_isQuasicoherent
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    (kernelPointQuotientSheaf K).IsQuasicoherent := by
  let M := kernelPointQuotientSheaf K
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop
      (fun U : X.affineOpens ↦ U.1) := by
    rw [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover,
      iSup_affineOpens_eq_top]
  let _ (U : X.affineOpens) : (M.over U.1).IsQuasicoherent := by
    let e := Modules.overEquiv U.1
    let oe := Modules.overFunctorEquiv U.1
    let _ : ((Modules.restrictFunctor U.1.ι).obj M).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
        (kernelPointQuotientRestrictIso K U).symm
        (affineOpenFreeQuotient K U).isQuasicoherent
    let _ : (e.inverse.obj ((Modules.restrictFunctor U.1.ι).obj M)).IsQuasicoherent :=
      isQuasicoherent_overEquiv_inverse U.1 _
    let iso : e.inverse.obj ((Modules.restrictFunctor U.1.ι).obj M) ≅ M.over U.1 :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U.1)).prop_of_iso iso
      (by infer_instance)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M (fun U : X.affineOpens ↦ U.1) hcov

/-- The global image quotient attached to a Grassmannian kernel point is
finite locally free of the prescribed rank. -/
lemma kernelPointQuotientSheaf_isProjectiveOfRank
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    IsProjectiveOfRank q (kernelPointQuotientSheaf K) := by
  apply IsProjectiveOfRank.of_affineOpen_pullbacks
  intro U
  exact (affineOpenFreeQuotient K U).isProjectiveOfRank.of_iso
    (kernelPointQuotientPullbackIso K U).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- The comparison from the restricted global quotient candidate to each canonical
affine quotient is an epimorphism. -/
instance kernelPointQuotientToAffineOpen_epi
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    Epi (kernelPointQuotientToAffineOpen K U) := by
  letI : Epi (affineOpenFreeQuotient K U).π :=
    (affineOpenFreeQuotient K U).epi
  haveI : Epi ((Modules.pullback U.1.ι).map (kernelPointQuotientMap K) ≫
      kernelPointQuotientToAffineOpen K U) := by
    rw [pullback_kernelPointQuotientMap_comp_toAffineOpen]
    infer_instance
  exact epi_of_epi
    ((Modules.pullback U.1.ι).map (kernelPointQuotientMap K))
    (kernelPointQuotientToAffineOpen K U)

/-- The global quotient presentation reconstructed from Grassmannian kernel
data. -/
noncomputable def freeQuotientOfKernelPoint {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    FreeQuotient q (ULift.{u} (Fin n)) X where
  Q := kernelPointQuotientSheaf K
  isQuasicoherent := kernelPointQuotientSheaf_isQuasicoherent K
  isProjectiveOfRank := kernelPointQuotientSheaf_isProjectiveOfRank K
  π := kernelPointQuotientMap K
  epi := kernelPointQuotientMap_epi K

/-- On an affine open, the pullback of the reconstructed global quotient is
equivalent to the canonical affine quotient. -/
lemma freeQuotientOfKernelPoint_pullback_affineOpen_r
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) (U : X.affineOpens) :
    (FreeQuotient.setoid q (ULift.{u} (Fin n)) U.1.toScheme).r
      ((freeQuotientOfKernelPoint K).pullback U.1.ι)
      (affineOpenFreeQuotient K U) := by
  refine ⟨kernelPointQuotientPullbackIso K U, ?_⟩
  dsimp only [FreeQuotient.pullback, freeQuotientOfKernelPoint]
  rw [kernelPointQuotientPullbackIso_hom]
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t ↦ (Modules.pullbackFreeIso U.1.ι (ULift.{u} (Fin n))).inv ≫ t)
    (pullback_kernelPointQuotientMap_comp_toAffineOpen K U)).trans (Iso.inv_hom_id_assoc _ _)

/-- Reconstructing a quotient presentation from a Grassmannian kernel point
recovers the original point. -/
@[simp]
lemma freeQuotientOfKernelPoint_kernelPoint
    {X : Scheme.{u}} {n q : ℕ}
    (K : (grassmannianFunctor q n).obj (op X)) :
    (freeQuotientOfKernelPoint K).kernelPoint = K := by
  apply Subtype.ext
  apply SubmoduleSheafData.eq_of_forall_affineOpen_comap_eq
  intro U
  have hlocal := FreeQuotient.kernelPoint_eq_of_r
    (freeQuotientOfKernelPoint_pullback_affineOpen_r K U)
  have hpull := FreeQuotient.kernelPoint_pullback U.1.ι
    (freeQuotientOfKernelPoint K)
  exact congrArg Subtype.val
    (hpull.trans (hlocal.trans (affineOpenFreeQuotient_kernelPoint K U)))

/-- Kernel construction on equivalence classes of strict free quotient
presentations. -/
noncomputable def kernelPointQuotient {n : ℕ} {X : Scheme.{u}} :
    Quotient (FreeQuotient.setoid q (ULift.{u} (Fin n)) X) →
      (grassmannianFunctor q n).obj (op X) :=
  Quotient.lift kernelPoint (fun _ _ h ↦ kernelPoint_eq_of_r h)

/-- Isomorphism classes of rank-`q` quotients of the finite free sheaf are
equivalent to Grassmannian kernel data on an arbitrary scheme. -/
noncomputable def kernelPointEquiv {n : ℕ} {X : Scheme.{u}} :
    Quotient (FreeQuotient.setoid q (ULift.{u} (Fin n)) X) ≃
      (grassmannianFunctor q n).obj (op X) where
  toFun := kernelPointQuotient
  invFun K := Quotient.mk'' (freeQuotientOfKernelPoint K)
  left_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    apply r_of_kernelPoint_eq
    simp only [kernelPointQuotient, Quotient.lift_mk]
    rw [freeQuotientOfKernelPoint_kernelPoint]
  right_inv K := freeQuotientOfKernelPoint_kernelPoint K

/-- The global kernel construction on quotient classes is bijective. -/
lemma kernelPointQuotient_bijective {n : ℕ} {X : Scheme.{u}} :
    Function.Bijective
      (kernelPointQuotient (q := q) (n := n) (X := X)) :=
  (kernelPointEquiv (q := q) (n := n) (X := X)).bijective

/-- On an affine scheme, isomorphism classes of rank-`q` quotients of the finite
free sheaf are equivalent to Grassmannian kernel data. -/
noncomputable def affineKernelPointEquiv {n : ℕ} {X : Scheme.{u}} [IsAffine X] :
    Quotient (FreeQuotient.setoid q (ULift.{u} (Fin n)) X) ≃
      (grassmannianFunctor q n).obj (op X) where
  toFun := kernelPointQuotient
  invFun K := Quotient.mk'' (affineFreeQuotientOfPoint K)
  left_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact affineFreeQuotientOfPoint_kernelPoint_r x
  right_inv K := affineFreeQuotientOfPoint_kernelPoint K

/-- On affine schemes, the kernel construction on quotient classes is bijective. -/
lemma kernelPointQuotient_bijective_of_isAffine {n : ℕ} {X : Scheme.{u}}
    [IsAffine X] : Function.Bijective
      (kernelPointQuotient (q := q) (n := n) (X := X)) :=
  (affineKernelPointEquiv (q := q) (n := n) (X := X)).bijective

/-- Kernel construction on quotient classes commutes with pullback. -/
lemma kernelPointQuotient_pullback {n : ℕ} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (z : Quotient (FreeQuotient.setoid q (ULift.{u} (Fin n)) X)) :
    (grassmannianFunctor q n).map g.op (kernelPointQuotient z) =
      kernelPointQuotient
        (Quotient.map (FreeQuotient.pullback g)
          (fun _ _ h ↦ FreeQuotient.pullback_r g h) z) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact kernelPoint_pullback g x

/-- The affine quotient/kernel equivalence commutes with pullback between affine
schemes. -/
lemma affineKernelPointEquiv_naturality {n : ℕ} {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (z : Quotient (FreeQuotient.setoid q (ULift.{u} (Fin n)) X)) :
    (grassmannianFunctor q n).map g.op (affineKernelPointEquiv z) =
      affineKernelPointEquiv
        (Quotient.map (FreeQuotient.pullback g)
          (fun _ _ h ↦ FreeQuotient.pullback_r g h) z) :=
  kernelPointQuotient_pullback g z

end FreeQuotient

/-- Quasi-coherence descends from the members of an arbitrary scheme-theoretic open
cover. This namespace-level entry point exposes the generic descent result independently
of the free-quotient construction in which its proof is used first. -/
lemma isQuasicoherent_of_openCover_restrict {X : Scheme.{u}} (M : X.Modules)
    (𝒰 : Scheme.OpenCover.{u} X)
    [∀ i, ((Modules.restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent] :
    M.IsQuasicoherent :=
  FreeQuotient.isQuasicoherent_of_openCover_restrict M 𝒰

namespace PullbackQuotient

variable {q V} {T T' T'' : Over S}

/-- Construct a relative quotient presentation from a submodule inclusion once its
cokernel is known to be a rank-`q` vector bundle. This is the effectivity constructor
used when descending quotient kernels on an open cover. -/
noncomputable def ofKernel (K : T.left.Modules)
    (k : K ⟶ (Modules.pullback T.hom).obj V) [Mono k]
    (hqc : (cokernel k).IsQuasicoherent)
    (hrank : IsProjectiveOfRank q (cokernel k)) :
    PullbackQuotient q V T where
  Q := cokernel k
  isQuasicoherent := hqc
  isProjectiveOfRank := hrank
  π := cokernel.π k
  epi := by infer_instance

/-- Transport a relative Grassmannian quotient across an isomorphism of the ambient
sheaves. -/
noncomputable def mapAmbientIso {V W : S.Modules} (e : V ≅ W)
    (x : PullbackQuotient q V T) : PullbackQuotient q W T where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank
  π := (Modules.pullback T.hom).map e.inv ≫ x.π
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _

/-- The quotient sheaf in a relative Grassmannian point is finitely presented. -/
lemma isFinitePresentation (x : PullbackQuotient q V T) : x.Q.IsFinitePresentation := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact x.isProjectiveOfRank.isFinitePresentation

/-- The quotient sheaf in a relative Grassmannian point is of finite type. -/
lemma isFiniteType (x : PullbackQuotient q V T) : x.Q.IsFiniteType := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact x.isProjectiveOfRank.isFiniteType

/-- Two rank-`q` locally free quotients of `V_T` are equivalent if they are isomorphic
compatibly with the projections from `V_T`. -/
protected def setoid (q : ℕ) (V : S.Modules) (T : Over S) :
    Setoid (PullbackQuotient q V T) where
  r x y := ∃ e : x.Q ≅ y.Q, x.π ≫ e.hom = y.π
  iseqv := by
    refine ⟨fun x ↦ ⟨Iso.refl _, Category.comp_id _⟩, ?_, ?_⟩
    · rintro x y ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      simp
    · rintro x y z ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e ≪≫ e', by rw [Iso.trans_hom, ← Category.assoc, he, he']⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Two epimorphic quotient presentations with compatibly isomorphic kernels have
compatibly isomorphic targets.  This is the abelian-category uniqueness principle
needed to descend quotient presentations by descending their kernels. -/
noncomputable def compatibleIsoOfKernelIso (x y : PullbackQuotient q V T)
    (e : kernel x.π ≅ kernel y.π)
    (he : e.hom ≫ kernel.ι y.π = kernel.ι x.π) : x.Q ≅ y.Q := by
  letI : Epi x.π := x.epi
  letI : Epi y.π := y.epi
  have hxy : kernel.ι x.π ≫ y.π = 0 := by
    rw [← he, Category.assoc, kernel.condition, comp_zero]
  have he' : e.inv ≫ kernel.ι x.π = kernel.ι y.π := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hyx : kernel.ι y.π ≫ x.π = 0 := by
    rw [← he', Category.assoc, kernel.condition, comp_zero]
  let f : x.Q ⟶ y.Q := Abelian.epiDesc x.π y.π hxy
  let g : y.Q ⟶ x.Q := Abelian.epiDesc y.π x.π hyx
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        rw [← cancel_epi x.π]
        simp [f, g]
      inv_hom_id := by
        rw [← cancel_epi y.π]
        simp [f, g] }
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma comp_compatibleIsoOfKernelIso_hom (x y : PullbackQuotient q V T)
    (e : kernel x.π ≅ kernel y.π)
    (he : e.hom ≫ kernel.ι y.π = kernel.ι x.π) :
    x.π ≫ (compatibleIsoOfKernelIso x y e he).hom = y.π := by
  letI : Epi x.π := x.epi
  letI : Epi y.π := y.epi
  dsimp [compatibleIsoOfKernelIso]
  rw [Abelian.comp_epiDesc]
lemma r_iff_exists_kernelIso (x y : PullbackQuotient q V T) :
    PullbackQuotient.setoid q V T x y ↔
      ∃ e : kernel x.π ≅ kernel y.π,
        e.hom ≫ kernel.ι y.π = kernel.ι x.π := by
  constructor
  · rintro ⟨e, he⟩
    let eK : kernel x.π ≅ kernel y.π :=
      kernel.mapIso (f := x.π) y.π (Iso.refl _) e he
    refine ⟨eK, ?_⟩
    dsimp [eK, kernel.mapIso, kernel.map]
    rw [kernel.lift_ι, Category.comp_id]
  · rintro ⟨e, he⟩
    exact ⟨compatibleIsoOfKernelIso x y e he,
      comp_compatibleIsoOfKernelIso_hom x y e he⟩

/-- The kernel of a relative quotient, represented sectionwise as the pointwise range
submodule of the categorical kernel inclusion. -/
noncomputable def kernelRangeSubmodule (x : PullbackQuotient q V T) :
    ((Modules.pullback T.hom).obj V).val.Submodule :=
  PresheafOfModules.Submodule.range (kernel.ι x.π).val

/-- Changing the ambient sheaf through an isomorphism transports the pointwise range
of the quotient kernel through the induced pullback isomorphism. -/
lemma kernelRangeSubmodule_mapAmbientIso {W : S.Modules} (e : V ≅ W)
    (x : PullbackQuotient q V T) :
    ((mapAmbientIso e x).kernelRangeSubmodule).mapIso
      ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
        ((Modules.pullback T.hom).mapIso e).symm) =
      x.kernelRangeSubmodule := by
  let a := (Modules.pullback T.hom).mapIso e
  let eK : kernel (mapAmbientIso e x).π ≅ kernel x.π :=
    kernel.mapIso (f := (mapAmbientIso e x).π) x.π a.symm (Iso.refl _) rfl
  have he : eK.hom ≫ kernel.ι x.π =
      kernel.ι (mapAmbientIso e x).π ≫ a.symm.hom := by
    dsimp [eK, kernel.mapIso, kernel.map]
    exact kernel.lift_ι _ _ _
  let a' := (SheafOfModules.forget T.left.ringCatSheaf).mapIso a.symm
  refine Eq.trans
    (PresheafOfModules.Submodule.range_comp_iso
      (kernel.ι (mapAmbientIso e x).π).val a').symm
    (PresheafOfModules.Submodule.range_eq_of_iso
      ((kernel.ι (mapAmbientIso e x).π).val ≫ a'.hom)
      (kernel.ι x.π).val
      ((SheafOfModules.forget T.left.ringCatSheaf).mapIso eK)
      (congrArg SheafOfModules.Hom.val he))

/-- The sectionwise kernel range is well-defined on isomorphism classes of relative
quotient presentations. -/
noncomputable def kernelRangeSubmoduleQuotient :
    Quotient (PullbackQuotient.setoid q V T) →
      ((Modules.pullback T.hom).obj V).val.Submodule :=
  Quotient.lift (fun x ↦ x.kernelRangeSubmodule) (fun x y h ↦ by
    obtain ⟨e, he⟩ := (r_iff_exists_kernelIso x y).1 h
    exact PresheafOfModules.Submodule.range_eq_of_iso
      (kernel.ι x.π).val (kernel.ι y.π).val
      ((SheafOfModules.forget T.left.ringCatSheaf).mapIso e)
      (congrArg SheafOfModules.Hom.val he))

@[simp]
lemma kernelRangeSubmoduleQuotient_mk (x : PullbackQuotient q V T) :
    kernelRangeSubmoduleQuotient (Quotient.mk'' x) = x.kernelRangeSubmodule := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A relative quotient class is determined by the sectionwise range of its kernel
inclusion. -/
lemma kernelRangeSubmoduleQuotient_injective :
    Function.Injective
      (kernelRangeSubmoduleQuotient (q := q) (V := V) (T := T)) := by
  intro z z' h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨y, rfl⟩ := Quotient.exists_rep z'
  apply Quotient.sound
  apply (r_iff_exists_kernelIso x y).2
  haveI : Mono (kernel.ι x.π).val :=
    Functor.map_mono (SheafOfModules.forget T.left.ringCatSheaf) (kernel.ι x.π)
  haveI : Mono (kernel.ι y.π).val :=
    Functor.map_mono (SheafOfModules.forget T.left.ringCatSheaf) (kernel.ι y.π)
  let e := ((Modules.pullback T.hom).obj V).isoOfRangeEq
    (kernel.ι x.π) (kernel.ι y.π) h
  exact ⟨e, SheafOfModules.isoOfRangeEq_hom_comp
    ((Modules.pullback T.hom).obj V) (kernel.ι x.π) (kernel.ι y.π) h⟩

/-- Equality of relative Grassmannian points can be checked on the sectionwise
range submodules of their kernel inclusions. -/
lemma eq_iff_kernelRangeSubmoduleQuotient_eq
    (z z' : Quotient (PullbackQuotient.setoid q V T)) :
    z = z' ↔ kernelRangeSubmoduleQuotient z = kernelRangeSubmoduleQuotient z' :=
  (kernelRangeSubmoduleQuotient_injective (q := q) (V := V) (T := T)).eq_iff.symm

/-- The kernel subobject of the fixed ambient pullback sheaf attached to an
isomorphism class of quotient presentations. -/
noncomputable def kernelSubobjectQuotient :
    Quotient (PullbackQuotient.setoid q V T) →
      Subobject ((Modules.pullback T.hom).obj V) :=
  Quotient.lift (fun x ↦ kernelSubobject x.π) (fun x y h ↦ by
    obtain ⟨e, he⟩ := (r_iff_exists_kernelIso x y).1 h
    exact Subobject.mk_eq_mk_of_comm _ _ e he)

@[simp]
lemma kernelSubobjectQuotient_mk (x : PullbackQuotient q V T) :
    kernelSubobjectQuotient (Quotient.mk'' x) = kernelSubobject x.π := rfl

/-- A relative quotient class is determined by its kernel as a subobject of the
pulled-back ambient sheaf. -/
lemma kernelSubobjectQuotient_injective :
    Function.Injective (kernelSubobjectQuotient (q := q) (V := V) (T := T)) := by
  intro z z' h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨y, rfl⟩ := Quotient.exists_rep z'
  apply Quotient.sound
  apply (r_iff_exists_kernelIso x y).2
  let e := Subobject.isoOfMkEqMk (kernel.ι x.π) (kernel.ι y.π) h
  exact ⟨e, Subobject.ofMkLEMk_comp h.le⟩
lemma eq_iff_kernelSubobjectQuotient_eq
    (z z' : Quotient (PullbackQuotient.setoid q V T)) :
    z = z' ↔ kernelSubobjectQuotient z = kernelSubobjectQuotient z' :=
  (kernelSubobjectQuotient_injective (q := q) (V := V) (T := T)).eq_iff.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Normalize a relative quotient of a canonical free sheaf so that its source is
literally the canonical free sheaf on the test scheme. -/
noncomputable def toFreeQuotient {I : Type u}
    (x : PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) I) T) :
    FreeQuotient q I T.left where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank
  π := (Modules.pullbackFreeIso T.hom I).inv ≫ x.π
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Regard a strict quotient of the free sheaf on a test scheme as a relative quotient
of the free sheaf on the base. -/
noncomputable def ofFreeQuotient {I : Type u} (x : FreeQuotient q I T.left) :
    PullbackQuotient q (SheafOfModules.free (R := S.ringCatSheaf) I) T where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank
  π := (Modules.pullbackFreeIso T.hom I).hom ≫ x.π
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma toFreeQuotient_r {I : Type u}
    {x y : PullbackQuotient q (SheafOfModules.free (R := S.ringCatSheaf) I) T}
    (h : (PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) I) T).r x y) :
    (FreeQuotient.setoid q I T.left).r x.toFreeQuotient y.toFreeQuotient := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by simp only [toFreeQuotient, Category.assoc, he]⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma ofFreeQuotient_r {I : Type u} {x y : FreeQuotient q I T.left}
    (h : (FreeQuotient.setoid q I T.left).r x y) :
    (PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) I) T).r
      (ofFreeQuotient x) (ofFreeQuotient y) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by simp only [ofFreeQuotient, Category.assoc, he]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Relative quotients of a free sheaf are equivalent to strict free quotient
presentations on the test scheme. -/
noncomputable def quotientEquivFreeQuotient {I : Type u} :
    Quotient (PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) I) T) ≃
      Quotient (FreeQuotient.setoid q I T.left) where
  toFun := Quotient.map toFreeQuotient (fun _ _ h ↦ toFreeQuotient_r h)
  invFun := Quotient.map ofFreeQuotient (fun _ _ h ↦ ofFreeQuotient_r h)
  left_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [toFreeQuotient, ofFreeQuotient]⟩
  right_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [toFreeQuotient, ofFreeQuotient]⟩

/-- Transport of ambient sheaves respects equivalence of quotient presentations. -/
lemma mapAmbientIso_r {V W : S.Modules} (e : V ≅ W)
    {x y : PullbackQuotient q V T} (h : (PullbackQuotient.setoid q V T).r x y) :
    (PullbackQuotient.setoid q W T).r (x.mapAmbientIso e) (y.mapAmbientIso e) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simp only [mapAmbientIso, Category.assoc, hi]⟩

/-- An isomorphism of ambient sheaves induces an equivalence on relative
Grassmannian points over every test scheme. -/
noncomputable def quotientEquivOfAmbientIso {V W : S.Modules} (e : V ≅ W) (T : Over S) :
    Quotient (PullbackQuotient.setoid q V T) ≃
      Quotient (PullbackQuotient.setoid q W T) where
  toFun := Quotient.map (mapAmbientIso e) (fun _ _ h ↦ mapAmbientIso_r e h)
  invFun := Quotient.map (mapAmbientIso e.symm) (fun _ _ h ↦ mapAmbientIso_r e.symm h)
  left_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [mapAmbientIso]⟩
  right_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [mapAmbientIso]⟩

/-- On quotient classes, transport of the ambient sheaf transports the literal kernel
range through the induced pullback isomorphism. -/
lemma kernelRangeSubmoduleQuotient_quotientEquivOfAmbientIso
    {V W : S.Modules} (e : V ≅ W) (T : Over S)
    (z : Quotient (PullbackQuotient.setoid q V T)) :
    (kernelRangeSubmoduleQuotient
      ((quotientEquivOfAmbientIso (q := q) e T) z)).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullback T.hom).mapIso e).symm) =
      kernelRangeSubmoduleQuotient z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact kernelRangeSubmodule_mapAmbientIso e x

/-- The comparison isomorphism between the pullback of `V` to `T'` and the pullback to
`T'` of the pullback of `V` to `T`, along a morphism `T' ⟶ T` of schemes over `S`. -/
noncomputable def pullbackComparison (V : S.Modules) (g : T' ⟶ T) :
    (Modules.pullback T'.hom).obj V ≅
      (Modules.pullback g.left).obj ((Modules.pullback T.hom).obj V) :=
  ((pullbackCongr (Over.w g)).app V).symm ≪≫ ((pullbackComp g.left T.hom).app V).symm

/-- Pull back a rank-`q` locally free quotient of `V_T` along a morphism `T' ⟶ T` of
schemes over `S`. -/
noncomputable def pullback (g : T' ⟶ T) (x : PullbackQuotient q V T) :
    PullbackQuotient q V T' where
  Q := (Modules.pullback g.left).obj x.Q
  isQuasicoherent :=
    haveI := x.isQuasicoherent
    inferInstance
  isProjectiveOfRank := by
    haveI := x.isQuasicoherent
    exact x.isProjectiveOfRank.pullback g.left
  π := (pullbackComparison V g).hom ≫ (Modules.pullback g.left).map x.π
  epi :=
    haveI := x.epi
    inferInstance

/-- Pulling back rank-`q` locally free quotients preserves equivalence. -/
lemma pullback_r {g : T' ⟶ T} {x y : PullbackQuotient q V T}
    (h : (PullbackQuotient.setoid q V T).r x y) :
    (PullbackQuotient.setoid q V T').r (x.pullback g) (y.pullback g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(Modules.pullback g.left).mapIso e, ?_⟩
  simp only [PullbackQuotient.pullback, Functor.mapIso_hom, Category.assoc,
    ← Functor.map_comp, he]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Normalizing a pulled-back relative quotient of a free sheaf agrees, up to the
strict-presentation equivalence, with pulling back its normalization. -/
lemma toFreeQuotient_pullback_r {I : Type u}
    (g : T' ⟶ T)
    (x : PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) I) T) :
    (FreeQuotient.setoid q I T'.left).r
      (x.pullback g).toFreeQuotient (x.toFreeQuotient.pullback g.left) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((Modules.pullbackFreeIso T'.hom I).inv ≫
      (Modules.pullbackCongr (Over.w g)).inv.app (SheafOfModules.free I) ≫
      (Modules.pullbackComp g.left T.hom).inv.app (SheafOfModules.free I) ≫
      (Modules.pullback g.left).map x.π) ≫ 𝟙 _ =
    (Modules.pullbackFreeIso g.left I).inv ≫
      (Modules.pullback g.left).map
        ((Modules.pullbackFreeIso T.hom I).inv ≫ x.π)
  rw [Category.comp_id, Functor.map_comp]
  conv_lhs => rw [← Category.assoc]
  rw [Modules.pullbackFreeIso_congr (Over.w g)]
  rw [← Modules.pullbackFreeIso_comp g.left T.hom I]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Transport across an ambient isomorphism commutes with pullback, up to the
equivalence relation on quotient presentations. -/
lemma mapAmbientIso_pullback_r {V W : S.Modules} (e : V ≅ W) (g : T' ⟶ T)
    (x : PullbackQuotient q V T) :
    (PullbackQuotient.setoid q W T').r
      ((x.mapAmbientIso e).pullback g) ((x.pullback g).mapAmbientIso e) := by
  refine ⟨Iso.refl _, ?_⟩
  simp [mapAmbientIso, pullback, pullbackComparison]

/-- The cocycle coherence for the pullback comparison isomorphisms, in a form where the
base morphisms are free variables so that the defining equalities can be substituted. -/
lemma cocycle_aux {X Y Z B : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hZ : Z ⟶ B)
    {p' : Y ⟶ B} (hp' : g ≫ hZ = p') {p'' : X ⟶ B} (hp'' : f ≫ p' = p'')
    (hq : (f ≫ g) ≫ hZ = p'') (V : B.Modules) :
    ((((Modules.pullbackCongr hp'').app V).symm ≪≫
        ((Modules.pullbackComp f p').app V).symm).hom ≫
      (Modules.pullback f).map ((((Modules.pullbackCongr hp').app V).symm ≪≫
        ((Modules.pullbackComp g hZ).app V).symm).hom)) ≫
      (Modules.pullbackComp f g).hom.app ((Modules.pullback hZ).obj V) =
    ((((Modules.pullbackCongr hq).app V).symm ≪≫
      ((Modules.pullbackComp (f ≫ g) hZ).app V).symm).hom) := by
  subst hp' hp''
  have hassoc := NatTrans.congr_app (Modules.pseudofunctor_associativity
    (f := f) (g := g) (h := hZ)) V
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at hassoc
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
    Modules.pullbackCongr, eqToIso.inv, eqToHom_refl, NatTrans.id_app,
    Category.id_comp]
  have hshuf : (Modules.pullbackComp f (g ≫ hZ)).inv.app V ≫
      (Modules.pullback f).map ((Modules.pullbackComp g hZ).inv.app V) ≫
        (Modules.pullbackComp f g).hom.app ((Modules.pullback hZ).obj V) =
      eqToHom (by simp) ≫ ((Modules.pullbackComp (f ≫ g) hZ).app V).inv := by
    rw [Iso.eq_comp_inv]
    simpa using hassoc
  rw [hshuf]
  rfl

/-- The unit coherence of the pullback comparison isomorphisms. -/
lemma comparison_id_coherence (V : S.Modules) (T : Over S) :
    (pullbackComparison V (𝟙 T)).hom ≫
      (Modules.pullbackId T.left).hom.app ((Modules.pullback T.hom).obj V) = 𝟙 _ := by
  have hcoh := NatTrans.congr_app
    (Modules.pseudofunctor_right_unitality (f := T.hom)) V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at hcoh
  rw [pullbackComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  have hcoh' : (Modules.pullbackComp (𝟙 T.left) T.hom).inv.app V ≫
      (Modules.pullbackId T.left).hom.app ((Modules.pullback T.hom).obj V) =
      eqToHom (by simp) := by simpa using hcoh
  rw [show (Modules.pullbackComp (Over.Hom.left (𝟙 T)) T.hom).inv.app V =
    (Modules.pullbackComp (𝟙 T.left) T.hom).inv.app V from rfl, hcoh']
  simp only [Modules.pullbackCongr, eqToIso.inv, eqToHom_refl]
  congr 1

/-- The unit coherence of the pullback comparison, for a morphism equal to the identity
(substitution-friendly form). -/
lemma comparison_eq_id_coherence (V : S.Modules) {T : Over S} (g₀ : T ⟶ T)
    (hg₀ : g₀ = 𝟙 T) :
    (pullbackComparison V g₀).hom ≫
      ((Modules.pullbackCongr
        (congrArg CommaMorphism.left hg₀ : g₀.left = 𝟙 T.left)).app
          ((Modules.pullback T.hom).obj V)).hom ≫
      (Modules.pullbackId T.left).hom.app ((Modules.pullback T.hom).obj V) = 𝟙 _ := by
  subst hg₀
  rw [show ((Modules.pullbackCongr (congrArg CommaMorphism.left
      (rfl : 𝟙 T = 𝟙 T) : CommaMorphism.left (𝟙 T) = 𝟙 T.left)).app
        ((Modules.pullback T.hom).obj V)).hom = 𝟙 _ from rfl, Category.id_comp]
  exact comparison_id_coherence V T

/-- The cocycle coherence of the pullback comparison isomorphisms. -/
lemma comparison_comp_coherence (V : S.Modules) {T T' T'' : Over S}
    (g : T' ⟶ T) (g' : T'' ⟶ T') :
    ((pullbackComparison V g').hom ≫
      (Modules.pullback g'.left).map (pullbackComparison V g).hom) ≫
        (Modules.pullbackComp g'.left g.left).hom.app ((Modules.pullback T.hom).obj V) =
    (pullbackComparison V (g' ≫ g)).hom :=
  cocycle_aux g'.left g.left T.hom (Over.w g) (Over.w g')
    (by rw [Category.assoc, Over.w g, Over.w g']) V

/-- The cocycle coherence of the pullback comparison, for a morphism equal to the
composite (substitution-friendly form). -/
lemma comparison_eq_comp_coherence (V : S.Modules) {T T' T'' : Over S}
    (g : T' ⟶ T) (g' : T'' ⟶ T') {g'' : T'' ⟶ T} (hg : g' ≫ g = g'') :
    ((pullbackComparison V g').hom ≫
      (Modules.pullback g'.left).map (pullbackComparison V g).hom) ≫
        (Modules.pullbackComp g'.left g.left).hom.app ((Modules.pullback T.hom).obj V) =
    (pullbackComparison V g'').hom ≫
      ((Modules.pullbackCongr
        ((congrArg CommaMorphism.left hg).symm : g''.left = g'.left ≫ g.left)).app
          ((Modules.pullback T.hom).obj V)).hom := by
  subst hg
  rw [show ((Modules.pullbackCongr ((congrArg CommaMorphism.left
      (rfl : g' ≫ g = g' ≫ g)).symm :
        CommaMorphism.left (g' ≫ g) = g'.left ≫ g.left)).app
        ((Modules.pullback T.hom).obj V)).hom = 𝟙 _ from rfl, Category.comp_id]
  exact comparison_comp_coherence V g g'

/-- Packaged identity law: pulling back a projection along a morphism equal to the
identity and collapsing returns the projection. -/
lemma comparison_pullback_id (V : S.Modules) {T : Over S} (g₀ : T ⟶ T)
    (hg₀ : g₀ = 𝟙 T) {Q : T.left.Modules}
    (π : (Modules.pullback T.hom).obj V ⟶ Q) :
    ((pullbackComparison V g₀).hom ≫ (Modules.pullback g₀.left).map π) ≫
      (((Modules.pullbackCongr (congrArg CommaMorphism.left hg₀ :
        g₀.left = 𝟙 T.left)).app Q) ≪≫ (Modules.pullbackId T.left).app Q).hom = π := by
  subst hg₀
  have hco := comparison_eq_id_coherence V (𝟙 T) rfl
  rw [Iso.app_hom] at hco
  rw [Iso.trans_hom, Iso.app_hom, Iso.app_hom, Category.assoc,
    (Modules.pullbackCongr (congrArg CommaMorphism.left (rfl : 𝟙 T = 𝟙 T) :
      CommaMorphism.left (𝟙 T) = 𝟙 T.left)).hom.naturality_assoc π,
    show (Modules.pullback (CommaMorphism.left (𝟙 T))).map π =
      (Modules.pullback (𝟙 T.left)).map π from rfl,
    (Modules.pullbackId T.left).hom.naturality π, reassoc_of% hco]
  rfl

/-- Packaged composition law: iterated pullback of a projection along a factorization
of a morphism agrees with the pullback along the composite. -/
lemma comparison_pullback_comp (V : S.Modules) {T T' T'' : Over S} (g : T' ⟶ T)
    (g' : T'' ⟶ T') {g'' : T'' ⟶ T} (hg : g' ≫ g = g'') {Q : T.left.Modules}
    (π : (Modules.pullback T.hom).obj V ⟶ Q) :
    ((pullbackComparison V g').hom ≫ (Modules.pullback g'.left).map
      ((pullbackComparison V g).hom ≫ (Modules.pullback g.left).map π)) ≫
      ((Modules.pullbackComp g'.left g.left).app Q ≪≫
        ((Modules.pullbackCongr ((congrArg CommaMorphism.left hg).symm :
          g''.left = g'.left ≫ g.left)).app Q).symm).hom =
    (pullbackComparison V g'').hom ≫ (Modules.pullback g''.left).map π := by
  subst hg
  rw [Iso.trans_hom,
    show (((Modules.pullbackCongr ((congrArg CommaMorphism.left
      (rfl : g' ≫ g = g' ≫ g)).symm : CommaMorphism.left (g' ≫ g) =
        g'.left ≫ g.left)).app Q).symm).hom =
      𝟙 ((Modules.pullback (g'.left ≫ g.left)).obj Q) from rfl, Category.comp_id,
    Iso.app_hom, Functor.map_comp, Category.assoc, Category.assoc, ← Functor.comp_map,
    (Modules.pullbackComp g'.left g.left).hom.naturality π, ← Category.assoc,
    ← Category.assoc]
  have hcc := comparison_comp_coherence V g g'
  rw [hcc]
  rfl

/-- Pulling back along the identity is equivalent to not pulling back at all. -/
lemma pullback_id_r (a : PullbackQuotient q V T) :
    (PullbackQuotient.setoid q V T).r (a.pullback (𝟙 T)) a := by
  refine ⟨(Modules.pullbackId T.left).app a.Q, ?_⟩
  change ((pullbackComparison V (𝟙 T)).hom ≫
    (Modules.pullback (𝟙 T.left)).map a.π) ≫
      (Modules.pullbackId T.left).hom.app a.Q = a.π
  rw [Category.assoc, (Modules.pullbackId T.left).hom.naturality a.π, ← Category.assoc]
  have hcoh := NatTrans.congr_app
    (Modules.pseudofunctor_right_unitality (f := T.hom)) V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at hcoh
  rw [show (pullbackComparison V (𝟙 T)).hom ≫
      (Modules.pullbackId T.left).hom.app ((Modules.pullback T.hom).obj V) = 𝟙 _ from ?_]
  · rw [Category.id_comp]
    rfl
  · rw [pullbackComparison]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
    have hcoh' : (Modules.pullbackComp (𝟙 T.left) T.hom).inv.app V ≫
        (Modules.pullbackId T.left).hom.app ((Modules.pullback T.hom).obj V) =
        eqToHom (by simp) := by simpa using hcoh
    rw [show (Modules.pullbackComp (Over.Hom.left (𝟙 T)) T.hom).inv.app V =
      (Modules.pullbackComp (𝟙 T.left) T.hom).inv.app V from rfl, hcoh']
    simp only [Modules.pullbackCongr, eqToIso.inv, eqToHom_refl]
    congr 1

/-- Pulling back along a composition is equivalent to the composite of the pullbacks. -/
lemma pullback_comp_r (g : T' ⟶ T) (g' : T'' ⟶ T') (a : PullbackQuotient q V T) :
    (PullbackQuotient.setoid q V T'').r ((a.pullback g).pullback g')
      (a.pullback (g' ≫ g)) := by
  refine ⟨(Modules.pullbackComp g'.left g.left).app a.Q, ?_⟩
  change ((pullbackComparison V g').hom ≫
    (Modules.pullback g'.left).map ((pullbackComparison V g).hom ≫
      (Modules.pullback g.left).map a.π)) ≫
    (Modules.pullbackComp g'.left g.left).hom.app a.Q =
    (pullbackComparison V (g' ≫ g)).hom ≫ (Modules.pullback (g' ≫ g).left).map a.π
  rw [Functor.map_comp, Category.assoc, Category.assoc, ← Functor.comp_map,
    (Modules.pullbackComp g'.left g.left).hom.naturality a.π,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact cocycle_aux g'.left g.left T.hom (Over.w g) (Over.w g')
    (by rw [Category.assoc, Over.w g, Over.w g']) V

end PullbackQuotient

namespace PullbackQuotient

variable {B U : Scheme.{u}} {q : ℕ} {V : B.Modules}

lemma pullbackComp_inv_comp_pullbackCongr_inv {X Y Z : Scheme.{u}}
    {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z) (M : Z.Modules) :
    (Modules.pullbackComp f' g).inv.app M ≫
        (Modules.pullbackCongr h).inv.app ((Modules.pullback g).obj M) =
      (Modules.pullbackCongr (congrArg (fun k ↦ k ≫ g) h)).inv.app M ≫
        (Modules.pullbackComp f g).inv.app M := by
  subst h
  rfl

/-- Regard a quotient after base change to `U` as a quotient of the original ambient
sheaf, with the test scheme viewed over `B`. -/
noncomputable def rebase (j : U ⟶ B) (T : Over U)
    (x : PullbackQuotient q ((Modules.pullback j).obj V) T) :
    PullbackQuotient q V ((Over.map j).obj T) where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank
  π := (Modules.pullbackComp T.hom j).inv.app V ≫ x.π
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _

noncomputable def unrebase (j : U ⟶ B) (T : Over U)
    (x : PullbackQuotient q V ((Over.map j).obj T)) :
    PullbackQuotient q ((Modules.pullback j).obj V) T where
  Q := x.Q
  isQuasicoherent := x.isQuasicoherent
  isProjectiveOfRank := x.isProjectiveOfRank
  π := (Modules.pullbackComp T.hom j).hom.app V ≫ x.π
  epi := by
    letI : Epi x.π := x.epi
    exact epi_comp _ _

lemma rebase_r (j : U ⟶ B) (T : Over U)
    {x y : PullbackQuotient q ((Modules.pullback j).obj V) T}
    (h : (PullbackQuotient.setoid q ((Modules.pullback j).obj V) T).r x y) :
    (PullbackQuotient.setoid q V ((Over.map j).obj T)).r
      (x.rebase j T) (y.rebase j T) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by simp only [rebase, Category.assoc, he]⟩

lemma unrebase_r (j : U ⟶ B) (T : Over U)
    {x y : PullbackQuotient q V ((Over.map j).obj T)}
    (h : (PullbackQuotient.setoid q V ((Over.map j).obj T)).r x y) :
    (PullbackQuotient.setoid q ((Modules.pullback j).obj V) T).r
      (x.unrebase j T) (y.unrebase j T) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by simp only [unrebase, Category.assoc, he]⟩

/-- Base change of the ambient sheaf induces the expected equivalence on relative
Grassmannian points over a test scheme. -/
noncomputable def quotientEquivRebase (j : U ⟶ B) (T : Over U) :
    Quotient (PullbackQuotient.setoid q ((Modules.pullback j).obj V) T) ≃
      Quotient (PullbackQuotient.setoid q V ((Over.map j).obj T)) where
  toFun := Quotient.map (rebase j T) (fun _ _ h ↦ rebase_r j T h)
  invFun := Quotient.map (unrebase j T) (fun _ _ h ↦ unrebase_r j T h)
  left_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [rebase, unrebase]⟩
  right_inv z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    apply Quotient.sound
    exact ⟨Iso.refl _, by simp [rebase, unrebase]⟩

-- OBLIGATION (deleted upstream API / Mathlib drift): retained verbatim but commented
-- out; it no longer elaborates.
/-- Rebasing a relative quotient transports its kernel range through the canonical
two-stage pullback comparison. -/
lemma kernelRangeSubmodule_rebase (j : U ⟶ B) (T : Over U)
    (x : PullbackQuotient q ((Modules.pullback j).obj V) T) :
    ((x.rebase j T).kernelRangeSubmodule).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullbackComp T.hom j).app V).symm) =
      x.kernelRangeSubmodule := by
  change
    (PresheafOfModules.Submodule.range
      (kernel.ι (((Modules.pullbackComp T.hom j).app V).symm.hom ≫ x.π)).val).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullbackComp T.hom j).app V).symm) =
      PresheafOfModules.Submodule.range (kernel.ι x.π).val
  exact SheafOfModules.kernelRange_comp_iso x.π
    ((Modules.pullbackComp T.hom j).app V).symm

/-- The quotient-level rebase equivalence transports kernel ranges through the
canonical two-stage pullback comparison. -/
lemma kernelRangeSubmoduleQuotient_quotientEquivRebase
    (j : U ⟶ B) (T : Over U)
    (z : Quotient
      (PullbackQuotient.setoid q ((Modules.pullback j).obj V) T)) :
    (kernelRangeSubmoduleQuotient ((quotientEquivRebase j T) z)).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullbackComp T.hom j).app V).symm) =
      kernelRangeSubmoduleQuotient z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact kernelRangeSubmodule_rebase j T x

lemma rebase_pullback_r (j : U ⟶ B) {T T' : Over U} (g : T' ⟶ T)
    (x : PullbackQuotient q ((Modules.pullback j).obj V) T) :
    (PullbackQuotient.setoid q V ((Over.map j).obj T')).r
      ((x.pullback g).rebase j T')
      ((x.rebase j T).pullback ((Over.map j).map g)) := by
  let hgj : g.left ≫ (T.hom ≫ j) = T'.hom ≫ j := by
    rw [← Category.assoc, Over.w g]
  let hgj' : (g.left ≫ T.hom) ≫ j = T'.hom ≫ j := Over.w g =≫ j
  have hcoh := cocycle_aux g.left T.hom j rfl hgj hgj' V
  have htransport := pullbackComp_inv_comp_pullbackCongr_inv
    (Over.w g) j V
  have hprefix :
      (Modules.pullbackComp T'.hom j).inv.app V ≫
          (Modules.pullbackCongr (Over.w g)).inv.app ((Modules.pullback j).obj V) ≫
            (Modules.pullbackComp g.left T.hom).inv.app
              ((Modules.pullback j).obj V) =
        (((Modules.pullbackCongr hgj).app V).symm ≪≫
            ((Modules.pullbackComp g.left (T.hom ≫ j)).app V).symm).hom ≫
          (Modules.pullback g.left).map
            ((Modules.pullbackComp T.hom j).inv.app V) := by
    rw [← cancel_mono
      ((Modules.pullbackComp g.left T.hom).hom.app ((Modules.pullback j).obj V))]
    calc
      _ = (((Modules.pullbackCongr hgj').app V).symm ≪≫
              ((Modules.pullbackComp (g.left ≫ T.hom) j).app V).symm).hom ≫
            (Modules.pullbackComp g.left T.hom).inv.app
              ((Modules.pullback j).obj V) ≫
            (Modules.pullbackComp g.left T.hom).hom.app
              ((Modules.pullback j).obj V) :=
        congrArg (fun k ↦ k ≫
          (Modules.pullbackComp g.left T.hom).inv.app ((Modules.pullback j).obj V) ≫
          (Modules.pullbackComp g.left T.hom).hom.app ((Modules.pullback j).obj V))
          htransport
      _ = (((Modules.pullbackCongr hgj').app V).symm ≪≫
            ((Modules.pullbackComp (g.left ≫ T.hom) j).app V).symm).hom := by
        rw [Iso.inv_hom_id_app]
        exact Category.comp_id _
      _ = _ := hcoh.symm
  have hx := hprefix =≫ (Modules.pullback g.left).map x.π
  refine ⟨Iso.refl _, ?_⟩
  simpa [rebase, PullbackQuotient.pullback, PullbackQuotient.pullbackComparison,
    Modules.pullbackCongr, Category.assoc, Functor.map_comp] using hx

end PullbackQuotient

/-- Background definition for Theorem 2.1.1 (the implicit definition of
the functor): let `V` be a sheaf of modules on a scheme `S` and `q` a natural number. The
relative Grassmannian functor `Gr(q, V)` on schemes over `S`: its points over `T → S` are
the isomorphism classes of rank-`q` locally free quotients `V_T ↠ Q` of the pullback of
`V`. For `V` a vector bundle of rank `n` this is the functor of the theorem; the
definition makes sense for arbitrary `V` (cf. EGA I.9.7). Functoriality is induced by the
pullback pseudofunctor of sheaves of modules; isomorphism classes absorb its coherence
isomorphisms, and the functor laws are proved below. -/
noncomputable def grassmannianOverFunctor (q : ℕ) (V : S.Modules) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (PullbackQuotient.setoid q V (unop T))
  map g := ↾fun x ↦ Quotient.map (PullbackQuotient.pullback (q := q) (V := V) g.unop)
    (fun _ _ h ↦ PullbackQuotient.pullback_r h) x
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    exact Quotient.sound (PullbackQuotient.pullback_id_r a)
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    exact Quotient.sound ((PullbackQuotient.setoid q V _).symm
      (PullbackQuotient.pullback_comp_r f.unop g.unop a))

/-- Formation of the relative Grassmannian commutes with base change of its ambient
sheaf. -/
noncomputable def grassmannianOverFunctorPullbackIso {U : Scheme.{u}} (j : U ⟶ S)
    (q : ℕ) (V : S.Modules) :
    grassmannianOverFunctor q ((Modules.pullback j).obj V) ≅
      (Over.map j).op ⋙ grassmannianOverFunctor q V :=
  NatIso.ofComponents
    (fun T ↦ (PullbackQuotient.quotientEquivRebase j (unop T)).toIso)
    (fun {T T'} g ↦ by
      ext z
      obtain ⟨x, rfl⟩ := Quotient.exists_rep z
      apply Quotient.sound
      exact PullbackQuotient.rebase_pullback_r j g.unop x)

/-- Over an affine test scheme, the relative Grassmannian of a canonical finite free
sheaf is the absolute Grassmannian kernel functor. -/
noncomputable def freeGrassmannianAffineEquiv {n : ℕ} (q : ℕ) (T : Over S)
    [IsAffine T.left] :
    (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).obj (op T) ≃
      (grassmannianFunctor q n).obj (op T.left) :=
  (PullbackQuotient.quotientEquivFreeQuotient (q := q) (T := T)).trans
    FreeQuotient.affineKernelPointEquiv

/-- Over every test scheme, the relative Grassmannian of a canonical finite
free sheaf is the absolute Grassmannian kernel functor. -/
noncomputable def freeGrassmannianEquiv {n : ℕ} (q : ℕ) (T : Over S) :
    (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).obj (op T) ≃
      (grassmannianFunctor q n).obj (op T.left) :=
  (PullbackQuotient.quotientEquivFreeQuotient (q := q) (T := T)).trans
    FreeQuotient.kernelPointEquiv

/-- The absolute Grassmannian functor viewed on schemes over a fixed base.
This explicit definition avoids a universe mismatch in the formal composite
with the forgetful functor from `Over S`. -/
noncomputable def grassmannianFunctorOver (S : Scheme.{u}) (q n : ℕ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift.{u + 1, u}
    ((grassmannianFunctor.{u} q n).obj (op (unop T).left))
  map g := ↾ULift.map.{u, u, u + 1, u + 1}
    ((grassmannianFunctor.{u} q n).map g.unop.left.op)
  map_id T := by
    ext x
    rw [show (grassmannianFunctor.{u} q n).map
        (Over.Hom.left (𝟙 T).unop).op = 𝟙 _ by
      exact (grassmannianFunctor.{u} q n).map_id (op (unop T).left)]
    rfl
  map_comp f g := by
    ext x
    rw [show (grassmannianFunctor.{u} q n).map
        (Over.Hom.left (f ≫ g).unop).op =
          (grassmannianFunctor.{u} q n).map f.unop.left.op ≫
            (grassmannianFunctor.{u} q n).map g.unop.left.op by
      exact (grassmannianFunctor.{u} q n).map_comp
        f.unop.left.op g.unop.left.op]
    rfl

/-- The global comparison for a free relative Grassmannian is natural under
arbitrary morphisms of test schemes. -/
lemma freeGrassmannianEquiv_naturality {n : ℕ} (q : ℕ) {T T' : Over S}
    (g : T' ⟶ T)
    (z : (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).obj (op T)) :
    (grassmannianFunctor q n).map g.left.op (freeGrassmannianEquiv q T z) =
      freeGrassmannianEquiv q T'
        ((grassmannianOverFunctor q
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).map g.op z) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  change (grassmannianFunctor q n).map g.left.op x.toFreeQuotient.kernelPoint =
    (x.pullback g).toFreeQuotient.kernelPoint
  rw [FreeQuotient.kernelPoint_pullback]
  exact FreeQuotient.kernelPoint_eq_of_r
    ((FreeQuotient.setoid q (ULift.{u} (Fin n)) T'.left).symm
      (PullbackQuotient.toFreeQuotient_pullback_r g x))

/-- Inverse form of naturality for the global free-Grassmannian comparison. -/
lemma freeGrassmannianEquiv_symm_naturality {n : ℕ} (q : ℕ)
    {T T' : Over S} (g : T' ⟶ T)
    (K : (grassmannianFunctor q n).obj (op T.left)) :
    (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).map g.op
        ((freeGrassmannianEquiv q T).symm K) =
      (freeGrassmannianEquiv q T').symm
        ((grassmannianFunctor q n).map g.left.op K) := by
  apply (freeGrassmannianEquiv q T').injective
  rw [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using
    (freeGrassmannianEquiv_naturality q g
      ((freeGrassmannianEquiv q T).symm K)).symm

/-- The relative Grassmannian of the canonical finite free sheaf is naturally
isomorphic to the absolute Grassmannian functor viewed on the slice over the
base. -/
noncomputable def freeGrassmannianIsoGrassmannianFunctorOver {n : ℕ} (q : ℕ) :
    grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) ≅
      grassmannianFunctorOver S q n :=
  NatIso.ofComponents (fun T ↦
    ((freeGrassmannianEquiv q (unop T)).trans
      (Equiv.ulift.{u + 1, u}).symm).toIso)
    (fun {T T'} g ↦ by
      ext z
      apply ULift.ext
      change freeGrassmannianEquiv q (unop T')
          ((grassmannianOverFunctor q
            (SheafOfModules.free (R := S.ringCatSheaf)
              (ULift.{u} (Fin n)))).map g z) =
        (grassmannianFunctor q n).map g.unop.left.op
          (freeGrassmannianEquiv q (unop T) z)
      exact (freeGrassmannianEquiv_naturality q g.unop z).symm)

/-- The canonical kernel map from the free relative Grassmannian is bijective on every
affine test scheme. -/
lemma freeGrassmannianAffineEquiv_bijective {n : ℕ} (q : ℕ) (T : Over S)
    [IsAffine T.left] : Function.Bijective
      (freeGrassmannianAffineEquiv (n := n) q T) :=
  (freeGrassmannianAffineEquiv (n := n) q T).bijective

/-- The affine comparison for a free relative Grassmannian is natural under morphisms
whose source and target schemes are affine. -/
lemma freeGrassmannianAffineEquiv_naturality {n : ℕ} (q : ℕ) {T T' : Over S}
    [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    (z : (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).obj (op T)) :
    (grassmannianFunctor q n).map g.left.op (freeGrassmannianAffineEquiv q T z) =
      freeGrassmannianAffineEquiv q T'
        ((grassmannianOverFunctor q
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).map g.op z) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  change (grassmannianFunctor q n).map g.left.op x.toFreeQuotient.kernelPoint =
    (x.pullback g).toFreeQuotient.kernelPoint
  rw [FreeQuotient.kernelPoint_pullback]
  exact FreeQuotient.kernelPoint_eq_of_r
    ((FreeQuotient.setoid q (ULift.{u} (Fin n)) T'.left).symm
      (PullbackQuotient.toFreeQuotient_pullback_r g x))

lemma freeGrassmannianAffineEquiv_symm_naturality {n : ℕ} (q : ℕ)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    (K : (grassmannianFunctor q n).obj (op T.left)) :
    (grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))).map g.op
        ((freeGrassmannianAffineEquiv q T).symm K) =
      (freeGrassmannianAffineEquiv q T').symm
        ((grassmannianFunctor q n).map g.left.op K) := by
  apply (freeGrassmannianAffineEquiv q T').injective
  rw [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using
    (freeGrassmannianAffineEquiv_naturality q g
      ((freeGrassmannianAffineEquiv q T).symm K)).symm

/-- Isomorphic ambient sheaves define naturally isomorphic relative Grassmannian
functors. -/
noncomputable def grassmannianOverFunctorIsoOfIso {V W : S.Modules} (e : V ≅ W) :
    grassmannianOverFunctor q V ≅ grassmannianOverFunctor q W :=
  NatIso.ofComponents
    (fun T ↦ (PullbackQuotient.quotientEquivOfAmbientIso e (unop T)).toIso)
    (fun {T T'} g ↦ by
      ext z
      obtain ⟨x, rfl⟩ := Quotient.exists_rep z
      apply Quotient.sound
      exact (PullbackQuotient.setoid q W _).symm
        (PullbackQuotient.mapAmbientIso_pullback_r e g.unop x))

/-- On every chosen trivializing member of the coordinate principal-open cover, the
relative Grassmannian of a vector bundle is naturally the relative Grassmannian of a
canonical finite free sheaf. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenGrassmannianIso
    {n : ℕ} {M : S.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank n M)
    (q : ℕ) (x : S) :
    grassmannianOverFunctor q
        ((Modules.pullback (hM.coordinateBasicOpenAffine x).1.ι).obj M) ≅
      grassmannianOverFunctor q
        (SheafOfModules.free
          (R := (hM.coordinateBasicOpenAffine x).1.toScheme.ringCatSheaf)
          (ULift.{u} (Fin n))) :=
  grassmannianOverFunctorIsoOfIso q
    (hM.coordinateBasicOpenAffinePullbackFreeIso x)

/-- The coordinate-trivialization equivalence transports the kernel range of every
relative Grassmannian point through the corresponding ambient pullback isomorphism. -/
lemma IsProjectiveOfRank.coordinateBasicOpenGrassmannianIso_kernelRange
    {n : ℕ} {M : S.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank n M)
    (q : ℕ) (x : S)
    (T : Over (hM.coordinateBasicOpenAffine x).1.toScheme)
    (z : (grassmannianOverFunctor q
      ((Modules.pullback (hM.coordinateBasicOpenAffine x).1.ι).obj M)).obj (op T)) :
    (PullbackQuotient.kernelRangeSubmoduleQuotient
      ((hM.coordinateBasicOpenGrassmannianIso q x).hom.app (op T) z)).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullback T.hom).mapIso
            (hM.coordinateBasicOpenAffinePullbackFreeIso x)).symm) =
      PullbackQuotient.kernelRangeSubmoduleQuotient z := by
  exact PullbackQuotient.kernelRangeSubmoduleQuotient_quotientEquivOfAmbientIso
    (q := q) (hM.coordinateBasicOpenAffinePullbackFreeIso x) T z

/-- On a chosen coordinate trivialization, the free relative Grassmannian is naturally
the restriction of the relative Grassmannian of the original vector bundle. -/
noncomputable def IsProjectiveOfRank.coordinateBasicOpenGrassmannianRestrictionIso
    {n : ℕ} {M : S.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank n M)
    (q : ℕ) (x : S) :
    grassmannianOverFunctor q
        (SheafOfModules.free
          (R := (hM.coordinateBasicOpenAffine x).1.toScheme.ringCatSheaf)
          (ULift.{u} (Fin n))) ≅
      (Over.map (hM.coordinateBasicOpenAffine x).1.ι).op ⋙
        grassmannianOverFunctor q M :=
  (hM.coordinateBasicOpenGrassmannianIso q x).symm ≪≫
    grassmannianOverFunctorPullbackIso
      (hM.coordinateBasicOpenAffine x).1.ι q M

/-- The full coordinate-restriction equivalence carries kernel ranges through the
two-stage pullback comparison and then through the chosen free trivialization. -/
lemma IsProjectiveOfRank.coordinateBasicOpenGrassmannianRestrictionIso_kernelRange
    {n : ℕ} {M : S.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank n M)
    (q : ℕ) (x : S)
    (T : Over (hM.coordinateBasicOpenAffine x).1.toScheme)
    (z : (grassmannianOverFunctor q
      (SheafOfModules.free
        (R := (hM.coordinateBasicOpenAffine x).1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin n)))).obj (op T)) :
    ((PullbackQuotient.kernelRangeSubmoduleQuotient
      ((hM.coordinateBasicOpenGrassmannianRestrictionIso q x).hom.app (op T) z)).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullbackComp T.hom
            (hM.coordinateBasicOpenAffine x).1.ι).app M).symm)).mapIso
        ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
          ((Modules.pullback T.hom).mapIso
            (hM.coordinateBasicOpenAffinePullbackFreeIso x).symm).symm) =
      PullbackQuotient.kernelRangeSubmoduleQuotient z := by
  let j := (hM.coordinateBasicOpenAffine x).1.ι
  let e := hM.coordinateBasicOpenAffinePullbackFreeIso x
  change
    ((PullbackQuotient.kernelRangeSubmoduleQuotient
      ((PullbackQuotient.quotientEquivRebase j T)
        ((PullbackQuotient.quotientEquivOfAmbientIso (q := q) e.symm T) z))).mapIso
          ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
            ((Modules.pullbackComp T.hom j).app M).symm)).mapIso
          ((SheafOfModules.forget T.left.ringCatSheaf).mapIso
            ((Modules.pullback T.hom).mapIso e.symm).symm) =
      PullbackQuotient.kernelRangeSubmoduleQuotient z
  rw [PullbackQuotient.kernelRangeSubmoduleQuotient_quotientEquivRebase]
  exact PullbackQuotient.kernelRangeSubmoduleQuotient_quotientEquivOfAmbientIso
    (q := q) e.symm T z
end Modules

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open CategoryTheory AlgebraicGeometry.Scheme

/-- Background definition for Subsection 2.4.4 (the implicit definition
of *strongly projective*): a morphism of schemes `f : X ⟶ S` is **strongly projective** if
there is a finite locally free sheaf of modules `E` on `S`, a scheme `P` over `S`
representing the projective bundle `ℙ(E) = Gr(1, E)`, and a factorization of `f` through a
closed immersion `X ⟶ P`.

This is the middle notion among the three notions of projectivity discussed in §2.4
(H-projective ⟹ strongly projective ⟹ EGA-projective); it is the conclusion in the main
theorems of Chapter 2 of *Stacks and Moduli*. -/
def IsStronglyProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : Modules.IsFiniteLocallyFree E) (P : Over S)
    (_ : (Modules.grassmannianOverFunctor 1 E).RepresentableBy P) (ι : X ⟶ P.left),
    IsClosedImmersion ι ∧ ι ≫ P.hom = f

end AlgebraicGeometry

end ThmGrassmannianProjectiveRelative
