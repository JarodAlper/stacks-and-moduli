module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import StacksAndModuli.API.EpiKernelClassification
public import StacksAndModuli.API.OpenCoverQuotient
public import StacksAndModuli.API.DVRGenericFiber
public import StacksAndModuli.API.DVRHilbertPolynomial
public import StacksAndModuli.API.DVRQuotientExtension
public import StacksAndModuli.API.DVRSpecialization
public import StacksAndModuli.API.DVRValuativeCriterion
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.FlatOverGlobalSectionsDVR
public import StacksAndModuli.API.ProperImmersion
public import StacksAndModuli.API.ProjectiveQuasicoherentSectionsLocalization
public import StacksAndModuli.API.QuasicoherentSectionsCriterion
public import StacksAndModuli.API.ProjectiveDVRFiberGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSheafGlobalSectionsBaseChange
public import StacksAndModuli.API.RepresentableValuativeCriterion
public import StacksAndModuli.API.SchemeModulesKernelSections
public import StacksAndModuli.API.SchemeModulesEmptyOpen
public import StacksAndModuli.API.QuotFunctorPrecomposition
public import StacksAndModuli.API.QuotientKernelFiniteModelZeroLocus
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksAndModuli.API.ExteriorPowerQcoh
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianImmersion
public import StacksAndModuli.API.ProjectiveSpaceZeroLocalCohomology
public import StacksAndModuli.API.ProjectiveSpaceTwistedFree
public import StacksAndModuli.API.ProjDVRQuotEventualBaseChange
public import StacksAndModuli.API.QuotFunctorEmptyRepresentation
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualImmersionPackage

/-!
# Valuative criteria for Hilb and Quot

This module corresponds to §2.4 (Projectivity of Hilb and Quot) of Chapter 2 of *Stacks
and Moduli*, label
`sec:representability-of-hilb-quot` — specifically its first two subsections.

**Proposition 2.4.1** (`prop:quot-locally-closed`) and **Theorem 2.4.5**
(`thm:quot-closed-embedding`) are stated here in their "in particular" form — that
`Quot^P(F/ℙ^n_S)` is representable by a quasi-projective, respectively projective, scheme
over `S`. The embedding `Quot^P(F/ℙ^n_S) → Gr(P(d), π_* F(d))` of Steps 1–3, which is how
the book proves them, additionally needs the pushforward `π_* F(d)` identified as a vector
bundle, Regularity in Families (§2.3) and the flattening stratification (§A.2, Stacks 05P9);
see this folder's COMMENTARY.md. The module also formalizes the polynomial-free content of
**Proposition 2.4.2** (`prop:quot-proper`): the valuative criterion for the Quot functor.

The unlabeled remark following the proposition (the unique-lifting diagram against
`Spec K → Spec R`) is exactly the shape of the statement below;
**Remark 2.4.4** (`rmk:hilbert-valuative-criterion`: the extension of a closed
subscheme is its schematic image, flat because all associated points lie over the
generic point) is tracked in STATUS.md pending scheme-theoretic-image API for ideal
sheaves.

Main results:
- `AlgebraicGeometry.Scheme.exists_quotFunctorP_representableBy_isHQuasiProjective`
  (**Proposition 2.4.1**, `prop:quot-locally-closed`).
- `AlgebraicGeometry.Scheme.quotFunctor_map_bijective_isFractionRing`
  (**Proposition 2.4.2**, `prop:quot-proper`, polynomial-free form).
- `AlgebraicGeometry.Scheme.exists_quotFunctorP_representableBy_isHProjective`
  (**Theorem 2.4.5**, `thm:quot-closed-embedding`).
- `AlgebraicGeometry.Scheme.hilbFunctor_map_bijective_fractionRing`
  (**Remark 2.4.4**, `rmk:hilbert-valuative-criterion`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropQuotLocallyClosed

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- Background definition for Proposition 2.4.1 (the implicit definition of
*quasi-projective*): a morphism `f : X ⟶ S` is **H-quasi-projective** if it factors as a
locally closed immersion `X ⟶ ℙ^n_S` followed by the projection, for some `n`.

This is the quasi-projective counterpart of `AlgebraicGeometry.IsHProjective` (§2.1), with
`IsClosedImmersion` relaxed to `IsImmersion`. -/
def AlgebraicGeometry.IsHQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (ι : X ⟶ Scheme.projectiveSpaceOver n S),
    IsImmersion ι ∧ ι ≫ Scheme.projectiveSpaceOverπ n S = f

/-- An H-quasi-projective morphism over a locally noetherian base is quasi-compact.  The
immersion is quasi-compact because relative projective space is locally noetherian: factor
it as a closed immersion followed by an open immersion and use noetherianity for the latter. -/
theorem AlgebraicGeometry.IsHQuasiProjective.quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    (hf : IsHQuasiProjective f) : QuasiCompact f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsImmersion ι := hι
  haveI : IsLocallyNoetherian (Scheme.projectiveSpaceOver n S) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.projectiveSpaceOverπ n S)
  haveI : QuasiCompact ι := by
    rw [← ι.liftCoborder_ι]
    infer_instance
  have hqc : QuasiCompact (ι ≫ Scheme.projectiveSpaceOverπ n S) := inferInstance
  rwa [hcomp] at hqc

/-- An H-quasi-projective morphism is locally of finite type. -/
theorem AlgebraicGeometry.IsHQuasiProjective.locallyOfFiniteType
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsHQuasiProjective f) :
    LocallyOfFiniteType f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsImmersion ι := hι
  have hlft : LocallyOfFiniteType (ι ≫ Scheme.projectiveSpaceOverπ n S) := inferInstance
  rwa [hcomp] at hlft

/-- An H-quasi-projective morphism is quasi-separated. -/
theorem AlgebraicGeometry.IsHQuasiProjective.quasiSeparated
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsHQuasiProjective f) :
    QuasiSeparated f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsImmersion ι := hι
  have hsep : IsSeparated (ι ≫ Scheme.projectiveSpaceOverπ n S) := inferInstance
  letI : IsSeparated (ι ≫ Scheme.projectiveSpaceOverπ n S) := hsep
  have hqs : QuasiSeparated (ι ≫ Scheme.projectiveSpaceOverπ n S) := inferInstance
  rwa [hcomp] at hqs

/-- Every H-projective morphism is H-quasi-projective, since a closed immersion is a
locally closed immersion. -/
theorem AlgebraicGeometry.IsHProjective.isHQuasiProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHProjective f) : IsHQuasiProjective f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsClosedImmersion ι := hι
  exact ⟨n, ι, inferInstance, hcomp⟩

/-- API lemma for Proposition 2.4.1 (representability
transport): a functor admitting a relatively representable immersion into a
functor represented by an H-projective scheme is represented by an
H-quasi-projective scheme.

This is the formal categorical endgame of Steps 1--3: once the natural map from
`Quot^P` to the relative Grassmannian has been shown to be a relatively
representable immersion, its representing object is the corresponding pullback
of the projective Grassmannian. -/
theorem AlgebraicGeometry.Scheme.exists_representableBy_isHQuasiProjective_of_relative_immersion
    {S : Scheme.{u}} {F G : CategoryTheory.Functor (Over S)ᵒᵖ (Type (u + 1))}
    (α : F ⟶ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α)
    (hG : ∃ Q₀ : Over S, Nonempty (G.RepresentableBy Q₀) ∧
      IsHProjective Q₀.hom) :
    ∃ Q : Over S, Nonempty (F.RepresentableBy Q) ∧
      IsHQuasiProjective Q.hom := by
  obtain ⟨Q₀, ⟨eG⟩, hQ₀⟩ := hG
  let eG' : uliftYoneda.{u + 1}.obj Q₀ ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G Q₀) eG
  let Q : Over S := hα.rep.pullback eG'.hom
  let j : Q ⟶ Q₀ := hα.rep.snd eG'.hom
  have hj : IsImmersion j.left := hα.property_snd eG'.hom
  haveI : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q ≅ F :=
    asIso (hα.rep.fst eG'.hom)
  let eF : F.RepresentableBy Q :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Q).symm eF'
  refine ⟨Q, ⟨eF⟩, ?_⟩
  obtain ⟨m, i, hi, hcomp⟩ := hQ₀
  refine ⟨m, j.left ≫ i, ?_, ?_⟩
  · letI : IsImmersion j.left := hj
    letI : IsClosedImmersion i := hi
    infer_instance
  · rw [Category.assoc, hcomp, Over.w j]

/-- The geometric package used in the nonempty branch of the Quot projectivity
argument: in every sufficiently large degree, the canonical map from the twisted-free
Quot functor to the corresponding free Grassmannian is relatively representable by
immersions.

In positive relative dimension, the remaining proof is the common regularity,
cohomology-and-base-change, kernel-generation, and projective-flattening input for both
the quasi-projective representability theorem and determinant very ampleness. The point
over a nonempty test scheme supplies the numerical Grassmannian rank inequality; without
it the Quot functor can be empty while `P(d)` exceeds the ambient rank. -/
theorem AlgebraicGeometry.Scheme.hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_isLocallyNoetherian
    (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (Scheme.quotFunctorP
      (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj (Opposite.op T)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  sorry

/-- **Proposition 2.4.1** (`prop:quot-locally-closed`): let `S` be a noetherian scheme and
`π : ℙ^n_S → S` relative projective space. If `F = 𝒪_{ℙ^n_S}(-l)^{⊕r}` and `P ∈ ℚ[z]`, then
`Quot^P(F/ℙ^n_S)` is representable by a quasi-projective scheme over `S`.

The book obtains this from a sharper statement: there is an `m₀` such that for every
`d ≥ m₀` the natural map `Quot^P(F/ℙ^n_S) → Gr(P(d), π_* F(d))` is a locally closed
immersion. That map is built in Steps 1–3 of §2.4 out of Regularity in Families
(Proposition 2.3.18) and the flattening stratification
(the flattening-stratification theorem, Stacks 05P9); with those still open, only the "in
particular" clause is stated here. See this folder's COMMENTARY.md.

Faithfulness note: `IsLocallyNoetherian S` stands for the book's noetherian `S`, matching the
convention already used for the Hilb and Quot functors in §2.1. -/
theorem AlgebraicGeometry.Scheme.exists_quotFunctorP_representableBy_isHQuasiProjective
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHQuasiProjective Q.hom := by
  by_cases hempty : ∀ T : Over S, Nonempty T.left →
      IsEmpty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj
          (Opposite.op T))
  · obtain ⟨Q, hQ, hproj⟩ :=
      Scheme.exists_quotFunctorP_representableBy_isHProjective_of_emptyOnNonempty
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P hempty
    exact ⟨Q, hQ, hproj.isHQuasiProjective⟩
  · obtain ⟨T, hbad⟩ := Classical.not_forall.mp hempty
    obtain ⟨hT, hz⟩ := Classical.not_imp.mp hbad
    have hz' : Nonempty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj
          (Opposite.op T)) := not_isEmpty_iff.mp hz
    cases n with
    | zero =>
        obtain ⟨Q, hQ, N, ι, hι, hcomp⟩ :=
          Scheme.exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
            0 S l r P
              (Scheme.twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)
        exact ⟨Q, hQ, N, ι, hι, hcomp⟩
    | succ n =>
        let H :=
          Scheme.hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_isLocallyNoetherian
            (n + 1) (Nat.zero_lt_succ n) S l r P T hT (Classical.choice hz')
        obtain ⟨Q, hQ, N, ι, hι, hcomp⟩ :=
          Scheme.exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
            (n + 1) S l r P H.w6
        exact ⟨Q, hQ, N, ι, hι, hcomp⟩

end PropQuotLocallyClosed

section PropQuotProper

open CategoryTheory Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

section KernelSaturation

variable {P W : Scheme.{u}} (G : W ⟶ P) [IsOpenImmersion G]
variable {M Q : P.Modules} (π : M ⟶ Q)

/-- Membership in the saturation condition attached to the kernel of the restricted
morphism says exactly that the image of the section dies on the intersection with the
range of the open immersion. -/
lemma Modules.mem_openSubmoduleCondition_kernel_iff (U : P.Opens) (s : Γ(M, U)) :
    s ∈ (Modules.openSubmoduleCondition G M
        (kernel.ι ((Modules.restrictFunctor G).map π))).obj (op U) ↔
      (Q.presheaf.map (homOfLE (G.image_preimage_le U)).op).hom ((π.app U).hom s) = 0 := by
  rw [Modules.mem_openSubmoduleCondition_iff,
    Modules.exists_kernel_ι_app_eq_iff ((Modules.restrictFunctor G).map π) (G ⁻¹ᵁ U)]
  have hnat : (π.app (G ''ᵁ (G ⁻¹ᵁ U))).hom
      ((M.presheaf.map (homOfLE (G.image_preimage_le U)).op).hom s) =
      (Q.presheaf.map (homOfLE (G.image_preimage_le U)).op).hom ((π.app U).hom s) :=
    CategoryTheory.congr_fun
      (π.mapPresheaf.naturality (homOfLE (G.image_preimage_le U)).op) s
  exact Eq.congr hnat rfl

/-- **The kernel of a torsion-free quotient is the saturation of its generic fibre.**
Let `G : W ⟶ P` be an open immersion whose range is the basic open of a global function
`t`, and `π : M ⟶ Q` a morphism of sheaves of modules with `Q` quasicoherent and
`t`-torsion-free on affine sections.  Then the sectionwise range of `kernel.ι π` is the
open-immersion saturation condition of the kernel of the restriction of `π` to `W`: a
section of `M` maps to zero under `π` if and only if it does so on the generic part.
This is the heart of both directions of Proposition 2.4.2. -/
lemma Modules.range_kernel_ι_eq_openSubmoduleCondition
    (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t) [Q.IsQuasicoherent]
    (htf : ∀ (V : P.affineOpens) (q : Γ(Q, V.1)),
      (P.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom t • q = 0 → q = 0) :
    PresheafOfModules.Submodule.range (kernel.ι π).val =
      Modules.openSubmoduleCondition G M
        (kernel.ι ((Modules.restrictFunctor G).map π)) := by
  refine Modules.presheafSubmodule_eq_of_isLocal_of_affine
    (Modules.presheafSubmoduleIsLocal_range _)
    (Modules.presheafSubmoduleIsLocal_openSubmoduleCondition _ _ _) ?_
  intro V
  ext s
  rw [Modules.mem_openSubmoduleCondition_kernel_iff]
  have hker : s ∈ (PresheafOfModules.Submodule.range (kernel.ι π).val).obj
      (op V.1) ↔ (π.app V.1).hom s = 0 := by
    rw [PresheafOfModules.Submodule.mem_range_iff]
    exact Modules.exists_kernel_ι_app_eq_iff π V.1 s
  rw [hker]
  set tV : Γ(P, V.1) := (P.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom t with htV
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    -- the image open is the basic open of the restricted function
    have him : G ''ᵁ (G ⁻¹ᵁ V.1) = P.basicOpen tV := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, htV]
      rw [Scheme.basicOpen_res]
      exact inf_comm _ _
    -- hence `π(s)` vanishes on the basic open of `tV`
    have hvan : (Q.presheaf.map (homOfLE (P.basicOpen_le tV)).op).hom
        ((π.app V.1).hom s) = 0 := by
      have hfuse : Q.presheaf.map (homOfLE (G.image_preimage_le V.1)).op ≫
          Q.presheaf.map (eqToHom him.symm).op =
          Q.presheaf.map (homOfLE (P.basicOpen_le tV)).op := by
        rw [← Functor.map_comp]
        congr 1
      have := CategoryTheory.congr_fun hfuse ((π.app V.1).hom s)
      rw [← this]
      have happ := congrArg (Q.presheaf.map (eqToHom him.symm).op).hom h
      rw [map_zero] at happ
      exact happ
    -- a power of `tV` kills `π(s)`, and torsion-freeness removes the power
    obtain ⟨n, hn⟩ := Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
      Q V.2 tV ((π.app V.1).hom s) hvan
    -- induct the torsion-freeness through the power
    clear hvan him hker
    induction n with
    | zero =>
      rw [pow_zero, one_smul] at hn
      exact hn
    | succ m ih =>
      refine ih ?_
      rw [pow_succ, mul_comm, mul_smul] at hn
      exact htf V _ hn

/-- A morphism pulled back from an open immersion is an open immersion. -/
lemma isOpenImmersion_of_isPullback {P' P T' T : Scheme.{u}}
    {G : P' ⟶ P} {p' : P' ⟶ T'} {p : P ⟶ T} {j : T' ⟶ T}
    [IsOpenImmersion j] (H : IsPullback G p' p j) : IsOpenImmersion G := by
  rw [← H.isoPullback_hom_fst]
  infer_instance

/-- The range of a pullback of an open immersion is the preimage of its range. -/
lemma opensRange_of_isPullback {P' P T' T : Scheme.{u}}
    {G : P' ⟶ P} {p' : P' ⟶ T'} {p : P ⟶ T} {j : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion G] (H : IsPullback G p' p j) :
    G.opensRange = p ⁻¹ᵁ j.opensRange := by
  have hG : G = H.isoPullback.hom ≫ pullback.fst p j := H.isoPullback_hom_fst.symm
  refine TopologicalSpace.Opens.ext ?_
  show Set.range G.base = ((p ⁻¹ᵁ j.opensRange : P.Opens) : Set P)
  have hsurj : Function.Surjective (⇑H.isoPullback.hom) :=
    (Scheme.homeoOfIso H.isoPullback).surjective
  rw [hG, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst (f := j) (g := p)

end KernelSaturation

section CokernelSections

/-- Sections of the cokernel of a monomorphism of sheaves of modules vanish exactly on
the range of the monomorphism: a mono is the kernel of its cokernel, and kernels are
computed sectionwise. -/
lemma Modules.cokernel_π_app_eq_zero_iff {X : Scheme.{u}} {N M : X.Modules}
    (ι : N ⟶ M) [Mono ι] (V : X.Opens) (s : Γ(M, V)) :
    ((cokernel.π ι).app V).hom s = 0 ↔ ∃ y : Γ(N, V), (ι.app V).hom y = s := by
  rw [← Modules.exists_kernel_ι_app_eq_iff (cokernel.π ι) V s]
  let e : kernel (cokernel.π ι) ≅ N :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π ι))
      (Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι))
        (cokernelIsCokernel ι))
  have he : e.hom ≫ ι = kernel.ι (cokernel.π ι) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel (cokernel.π ι))
      (Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι))
        (cokernelIsCokernel ι)) WalkingParallelPair.zero
  constructor
  · rintro ⟨y', rfl⟩
    refine ⟨(e.hom.app V).hom y', ?_⟩
    exact CategoryTheory.congr_fun
      (congrArg (fun (k : kernel (cokernel.π ι) ⟶ M) ↦ k.app V) he) y'
  · rintro ⟨y, rfl⟩
    refine ⟨(e.inv.app V).hom y, ?_⟩
    have hi : e.inv ≫ kernel.ι (cokernel.π ι) = ι := by
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact CategoryTheory.congr_fun (congrArg (fun (k : N ⟶ M) ↦ k.app V) hi) y

/-- Over an affine scheme, the cokernel of a morphism of quasicoherent sheaves of
modules is the tilde of the cokernel of its global sections: the tilde functor is a left
adjoint (`tilde.adjunction`) and the counit is invertible on quasicoherent modules. -/
noncomputable def Modules.cokernelSpecTildeIso {A : CommRingCat.{u}}
    {N M : (Spec A).Modules} (ι : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent] :
    cokernel ι ≅ (tilde.functor A).obj (cokernel (moduleSpecΓFunctor.map ι)) :=
  haveI : IsIso (Scheme.Modules.fromTildeΓNatTrans.app N) :=
    inferInstanceAs (IsIso N.fromTildeΓ)
  haveI : IsIso (Scheme.Modules.fromTildeΓNatTrans.app M) :=
    inferInstanceAs (IsIso M.fromTildeΓ)
  haveI := (tilde.adjunction (R := A)).leftAdjoint_preservesColimits
  (cokernel.mapIso ((moduleSpecΓFunctor ⋙ tilde.functor A).map ι) ι
      (asIso (Scheme.Modules.fromTildeΓNatTrans.app N))
      (asIso (Scheme.Modules.fromTildeΓNatTrans.app M))
      (by simpa using Scheme.Modules.fromTildeΓNatTrans.naturality ι)).symm ≪≫
    (PreservesCokernel.iso (tilde.functor A) (moduleSpecΓFunctor.map ι)).symm

/-- Over an affine scheme, the cokernel of a morphism of quasicoherent sheaves of
modules is quasicoherent. -/
lemma Modules.cokernel_isQuasicoherent_spec {A : CommRingCat.{u}}
    {N M : (Spec A).Modules} (ι : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent] :
    (cokernel ι).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (Modules.cokernelSpecTildeIso ι).symm
    (inferInstanceAs (((tilde.functor A).obj
      (cokernel (moduleSpecΓFunctor.map ι))).IsQuasicoherent))

/-- The cokernel of a morphism of quasicoherent sheaves of modules on any scheme is
quasicoherent: quasicoherence is checked on an affine cover, and restriction (a left
adjoint) preserves cokernels. -/
lemma Modules.cokernel_isQuasicoherent {P : Scheme.{u}} {N M : P.Modules}
    (ι : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent] :
    (cokernel ι).IsQuasicoherent := by
  haveI : ∀ i, ((Modules.restrictFunctor (P.affineCover.f i)).obj
      (cokernel ι)).IsQuasicoherent := by
    intro i
    haveI : (cokernel ((Modules.restrictFunctor (P.affineCover.f i)).map
        ι)).IsQuasicoherent :=
      Modules.cokernel_isQuasicoherent_spec
        ((Modules.restrictFunctor (P.affineCover.f i)).map ι)
    exact (SheafOfModules.isQuasicoherent (P.affineCover.X i).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso (Modules.restrictFunctor (P.affineCover.f i)) ι).symm
      inferInstance
  exact Modules.isQuasicoherent_of_openCover_restrict _ P.affineCover

/-- The projection to the cokernel of a morphism of quasicoherent sheaves of modules is
surjective on sections over any affine open. -/
lemma Modules.cokernel_π_app_surjective_of_affine {P : Scheme.{u}} {N M : P.Modules}
    (ι : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent]
    {U : P.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((cokernel.π ι).app U).hom := by
  classical
  set j : Spec Γ(P, U) ⟶ P := hU.fromSpec with hj
  have him : j ''ᵁ (⊤ : (Spec Γ(P, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  -- the restricted projection is the projection of the restricted inclusion
  set e : (Modules.restrictFunctor j).obj (cokernel ι) ≅
      cokernel ((Modules.restrictFunctor j).map ι) :=
    PreservesCokernel.iso (Modules.restrictFunctor j) ι with he
  have hcomp : (Modules.restrictFunctor j).map (cokernel.π ι) ≫ e.hom =
      cokernel.π ((Modules.restrictFunctor j).map ι) :=
    PreservesCokernel.π_iso_hom _ _
  haveI : (cokernel ((Modules.restrictFunctor j).map ι)).IsQuasicoherent :=
    Modules.cokernel_isQuasicoherent_spec _
  have hsurj0 : Function.Surjective
      (moduleSpecΓFunctor.map (cokernel.π ((Modules.restrictFunctor j).map ι))) :=
    moduleSpecΓFunctor_map_surjective_of_epi _
  intro s'
  have hsurj1 : Function.Surjective
      ((cokernel.π ((Modules.restrictFunctor j).map ι)).app ⊤).hom := hsurj0
  obtain ⟨m'', hm''⟩ := hsurj1 ((e.hom.app ⊤).hom
    (((cokernel ι).presheaf.map (eqToHom him).op).hom s'))
  refine ⟨(M.presheaf.map (eqToHom him.symm).op).hom m'', ?_⟩
  have hminj : Function.Injective
      (((cokernel ι).presheaf.map (eqToHom him).op).hom) :=
    (ConcreteCategory.bijective_of_isIso
      ((cokernel ι).presheaf.map (eqToHom him).op)).injective
  apply hminj
  have hnat0 := CategoryTheory.congr_fun
    ((cokernel.π ι).mapPresheaf.naturality (eqToHom him).op)
    ((M.presheaf.map (eqToHom him.symm).op).hom m'')
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat0
  have hmm : (M.presheaf.map (eqToHom him).op).hom
      ((M.presheaf.map (eqToHom him.symm).op).hom m'') = m'' := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
    rfl
  refine Eq.trans hnat0.symm ?_
  rw [hmm]
  apply Modules.app_injective_of_mono e.hom ⊤
  have happ := CategoryTheory.congr_fun (congrArg
    (fun (k : (Modules.restrictFunctor j).obj M ⟶
      cokernel ((Modules.restrictFunctor j).map ι)) ↦ k.app ⊤) hcomp) m''
  exact happ.trans hm''

end CokernelSections

section SaturationQcoh

variable {P W : Scheme.{u}} (G : W ⟶ P) [IsOpenImmersion G]
variable {M : P.Modules} {QW : W.Modules}

/-- Sections of the pushforward of a quasicoherent sheaf along an open immersion whose
range meets every affine open in an affine open still satisfy the annihilation half of
the localization property: a section vanishing on a basic open is killed by a power of
the function. -/
lemma Modules.pushforward_exists_pow_smul_eq_zero [QW.IsQuasicoherent]
    (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t)
    {U : P.Opens} (hU : IsAffineOpen U) (r : Γ(P, U))
    (v : Γ((Modules.pushforward G).obj QW, U))
    (hv : (((Modules.pushforward G).obj QW).presheaf.map
      (homOfLE (P.basicOpen_le r)).op).hom v = 0) :
    ∃ m : ℕ, r ^ m • v = 0 := by
  classical
  -- the preimage of `U` is affine
  have haffim : IsAffineOpen (G ''ᵁ (G ⁻¹ᵁ U)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_comm,
      ← Scheme.basicOpen_res _ _ (homOfLE (le_top : U ≤ ⊤)).op]
    exact hU.basicOpen _
  have haffpre : IsAffineOpen (G ⁻¹ᵁ U) :=
    (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion G).mp haffim
  -- the pulled-back function and its basic open
  set rW : Γ(W, G ⁻¹ᵁ U) := (G.app U).hom r with hrW
  have hpre : G ⁻¹ᵁ (P.basicOpen r) = W.basicOpen rW := Scheme.preimage_basicOpen G r
  -- the section as a section of `QW` over the preimage, vanishing on `D(rW)`
  have hv' : (QW.presheaf.map (homOfLE (W.basicOpen_le rW)).op).hom
      (v : Γ(QW, G ⁻¹ᵁ U)) = 0 := by
    have hcomp : QW.presheaf.map ((TopologicalSpace.Opens.map G.base).map
        (homOfLE (P.basicOpen_le r))).op ≫
        QW.presheaf.map (eqToHom hpre.symm).op =
        QW.presheaf.map (homOfLE (W.basicOpen_le rW)).op := by
      rw [← Functor.map_comp]
      congr 1
    have happ := CategoryTheory.congr_fun hcomp (v : Γ(QW, G ⁻¹ᵁ U))
    have hv0 : (QW.presheaf.map ((TopologicalSpace.Opens.map G.base).map
        (homOfLE (P.basicOpen_le r))).op).hom (v : Γ(QW, G ⁻¹ᵁ U)) = 0 := hv
    exact happ.symm.trans
      ((congrArg (QW.presheaf.map (eqToHom hpre.symm).op).hom hv0).trans (map_zero _))
  obtain ⟨m, hm⟩ := Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
    QW haffpre rW (v : Γ(QW, G ⁻¹ᵁ U)) hv'
  refine ⟨m, ?_⟩
  let v' : ToType Γ(QW, G ⁻¹ᵁ U) := v
  have hstep : ((G.app U).hom (r ^ m)) • v' = r ^ m • v := rfl
  rw [← hstep, map_pow]
  exact hm

/-- **The saturated kernel is quasicoherent.**  For `M` quasicoherent, `G` an open
immersion with range the basic open of a global function, and `QW` a quasicoherent
sheaf on the source, the kernel of any morphism `M ⟶ G_* QW` is quasicoherent.  The
point is that `G_* QW` need not be quasicoherent, but its sections still satisfy the
annihilation half of the localization property over affine opens. -/
lemma Modules.kernel_to_pushforward_isQuasicoherent
    [M.IsQuasicoherent] [QW.IsQuasicoherent]
    (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t)
    (φ : M ⟶ (Modules.pushforward G).obj QW) :
    (kernel φ).IsQuasicoherent := by
  classical
  apply Modules.isQuasicoherent_of_sections_localization
  · -- annihilation: transfer to `M` through the monic inclusion
    intro U r y hy
    have hres : ((kernel.ι φ).app (P.basicOpen r)).hom
        (((kernel φ).presheaf.map (homOfLE (P.basicOpen_le r)).op).hom y) =
        (M.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom
          (((kernel.ι φ).app U.1).hom y) :=
      CategoryTheory.congr_fun
        ((kernel.ι φ).mapPresheaf.naturality (homOfLE (P.basicOpen_le r)).op) y
    obtain ⟨n, hn⟩ := Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
      M U.2 r (((kernel.ι φ).app U.1).hom y) (by rw [← hres, hy, map_zero])
    refine ⟨n, Modules.app_injective_of_mono (kernel.ι φ) U.1 ?_⟩
    rw [map_zero, Scheme.Modules.Hom.app_smul]
    exact hn
  · -- extension: extend in `M`, then correct by the torsion bound in the pushforward
    intro U r y
    set s : Γ(M, P.basicOpen r) := ((kernel.ι φ).app (P.basicOpen r)).hom y with hs
    obtain ⟨z₀, n, hz₀⟩ := Modules.exists_pow_smul_res_of_basicOpen M U.2 r s
    -- the obstruction section of the pushforward vanishes on the basic open
    have hφs : (φ.app (P.basicOpen r)).hom s = 0 := by
      have h0 : ((kernel.ι φ ≫ φ).app (P.basicOpen r)).hom y = 0 := by
        rw [kernel.condition]
        rfl
      exact h0
    have hφz₀ : (((Modules.pushforward G).obj QW).presheaf.map
        (homOfLE (P.basicOpen_le r)).op).hom ((φ.app U.1).hom z₀) = 0 := by
      have hnat := CategoryTheory.congr_fun
        (φ.mapPresheaf.naturality (homOfLE (P.basicOpen_le r)).op) z₀
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
      simp only [Scheme.Modules.mapPresheaf_app] at hnat
      rw [← hnat, hz₀, Scheme.Modules.Hom.app_smul, hφs, smul_zero]
    obtain ⟨m, hm⟩ := Modules.pushforward_exists_pow_smul_eq_zero G t hrange U.2 r
      ((φ.app U.1).hom z₀) hφz₀
    -- the corrected extension lies in the kernel
    have hker : (φ.app U.1).hom ((r ^ m : Γ(P, U.1)) • z₀) = 0 := by
      rw [Scheme.Modules.Hom.app_smul]
      exact hm
    obtain ⟨y₀, hy₀⟩ := (Modules.exists_kernel_ι_app_eq_iff φ U.1
      ((r ^ m : Γ(P, U.1)) • z₀)).mpr hker
    refine ⟨y₀, n + m, ?_⟩
    apply Modules.app_injective_of_mono (kernel.ι φ) (P.basicOpen r)
    have hres := CategoryTheory.congr_fun
      ((kernel.ι φ).mapPresheaf.naturality (homOfLE (P.basicOpen_le r)).op) y₀
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hres
    simp only [Scheme.Modules.mapPresheaf_app] at hres
    rw [hres, hy₀, Scheme.Modules.map_smul, map_pow, hz₀, Scheme.Modules.Hom.app_smul,
      smul_smul, ← pow_add, add_comm m n]

/-- A global function whose basic open is everything is a unit. -/
lemma isUnit_of_basicOpen_eq_top {X : Scheme.{u}} (f : Γ(X, ⊤))
    (h : X.basicOpen f = ⊤) : IsUnit f := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ X.basicOpen f := by
    rw [h]
    trivial
  exact (X.mem_basicOpen_top f x).mp hx'

/-- A morphism whose range is the basic open of a function pulls that function back to
a unit. -/
lemma isUnit_appTop_of_opensRange_eq_basicOpen {P W : Scheme.{u}} (G : W ⟶ P)
    [IsOpenImmersion G] (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t) :
    IsUnit ((G.app ⊤).hom t) := by
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen, ← hrange]
  exact G.preimage_opensRange

/-- A section whose basic open is the whole open on which it is defined is a unit. -/
lemma isUnit_of_basicOpen_eq {X : Scheme.{u}} {V : X.Opens} (f : Γ(X, V))
    (h : X.basicOpen f = V) : IsUnit f := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ X.basicOpen f := by
    rw [h]
    exact hx
  exact (X.mem_basicOpen f x hx).mp hx'

/-- The restriction of the generic function to the preimage of any open is a unit on
the source of the open immersion. -/
lemma isUnit_app_res_of_opensRange_eq_basicOpen {P W : Scheme.{u}} (G : W ⟶ P)
    [IsOpenImmersion G] (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t)
    (U : P.Opens) :
    IsUnit ((G.app U).hom ((P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom t)) := by
  apply isUnit_of_basicOpen_eq
  rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res, ← hrange]
  refine TopologicalSpace.Opens.ext ?_
  have h1 : (G ⁻¹ᵁ (U ⊓ G.opensRange) : Set W) =
      (G ⁻¹ᵁ U : Set W) ∩ (G ⁻¹ᵁ G.opensRange : Set W) := rfl
  rw [h1, show ((G ⁻¹ᵁ G.opensRange : W.Opens) : Set W) = ((⊤ : W.Opens) : Set W) from
    congrArg _ G.preimage_opensRange]
  simp

/-- Sections of the extension `coker(ker φ ⟶ M)` have no torsion with respect to the
function cutting out the generic fibre: a class killed by a power of `t` vanishes,
because its lift is generically killed and hence lies in the saturated kernel. -/
lemma Modules.cokernel_t_smul_regular {P W : Scheme.{u}} {G : W ⟶ P} [IsOpenImmersion G]
    {M : P.Modules} {QW : W.Modules} [M.IsQuasicoherent] [QW.IsQuasicoherent]
    (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t)
    (φ : M ⟶ (Modules.pushforward G).obj QW)
    (U : P.affineOpens) (k : ℕ) (q : Γ(cokernel (kernel.ι φ), U.1))
    (hq : ((P.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t) ^ k • q = 0) :
    q = 0 := by
  haveI : (kernel φ).IsQuasicoherent :=
    Modules.kernel_to_pushforward_isQuasicoherent G t hrange φ
  obtain ⟨z, rfl⟩ := Modules.cokernel_π_app_surjective_of_affine (kernel.ι φ) U.2 q
  set tU := (P.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t with htU
  have hker : ((cokernel.π (kernel.ι φ)).app U.1).hom (tU ^ k • z) = 0 := by
    rw [Scheme.Modules.Hom.app_smul]
    exact hq
  obtain ⟨y, hy⟩ := (Modules.cokernel_π_app_eq_zero_iff (kernel.ι φ) U.1 _).mp hker
  -- apply `φ`: the lift is generically killed
  have hφ : (φ.app U.1).hom (tU ^ k • z) = 0 := by
    rw [← hy]
    have h0 : ((kernel.ι φ ≫ φ).app U.1).hom y = 0 := by
      rw [kernel.condition]
      rfl
    exact h0
  rw [Scheme.Modules.Hom.app_smul] at hφ
  -- the action of `tU` on the pushforward is by a unit
  have hφz : (φ.app U.1).hom z = 0 := by
    have hunit : IsUnit ((G.app U.1).hom tU) :=
      isUnit_app_res_of_opensRange_eq_basicOpen G t hrange U.1
    obtain ⟨u, hu⟩ := hunit.pow k
    let v' : ToType Γ(QW, G ⁻¹ᵁ U.1) := (φ.app U.1).hom z
    have hstep : ((G.app U.1).hom (tU ^ k)) • v' = tU ^ k • (φ.app U.1).hom z := rfl
    have hv0 : ((G.app U.1).hom tU) ^ k • v' = 0 := by
      rw [← map_pow, hstep]
      exact hφ
    rw [← hu] at hv0
    have h3 := congrArg (fun w ↦
      ((u⁻¹ : (Γ(W, G ⁻¹ᵁ U.1))ˣ) : Γ(W, G ⁻¹ᵁ U.1)) • w) hv0
    beta_reduce at h3
    rw [smul_smul, Units.inv_mul, one_smul, smul_zero] at h3
    exact h3
  -- hence `z` lies in the kernel, and its class vanishes
  obtain ⟨y₀, hy₀⟩ := (Modules.exists_kernel_ι_app_eq_iff φ U.1 z).mpr hφz
  rw [← hy₀]
  have h0 : ((kernel.ι φ ≫ cokernel.π (kernel.ι φ)).app U.1).hom y₀ = 0 := by
    rw [cokernel.condition]
    rfl
  exact h0

/-- The opens of the spectrum of a discrete valuation ring: the empty set, the generic
point (the basic open of a uniformizer), and the whole space. -/
lemma DVR_opens_trichotomy {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (V : (Spec (CommRingCat.of R)).Opens) :
    V = ⊥ ∨ V = (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of R)).Opens) ∨
      V = ⊤ := by
  classical
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  have hV : (V : Set (Spec (CommRingCat.of R))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hbot (TopologicalSpace.Opens.ext (by simpa using h))
  obtain ⟨q₀, hq₀⟩ := hV
  have hgen : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) ∈ V := by
    have hspec : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) ⤳ q₀ := by
      rw [← PrimeSpectrum.le_iff_specializes]
      exact bot_le
    exact hspec.mem_open V.2 hq₀
  have hclosed : ∀ q : PrimeSpectrum R, q.asIdeal ≠ ⊥ →
      q = IsLocalRing.closedPoint R := by
    intro q hq
    have hmax : q.asIdeal.IsMaximal := by
      haveI := q.2
      exact IsPrime.to_maximal_ideal hq
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
  by_cases hcl : IsLocalRing.closedPoint R ∈ V
  · refine Or.inr (Or.inr (top_unique fun q _ ↦ ?_))
    rcases eq_or_ne q.asIdeal ⊥ with hq | hq
    · have : q = (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) := PrimeSpectrum.ext hq
      rw [this]
      exact hgen
    · rw [hclosed q hq]
      exact hcl
  · refine Or.inr (Or.inl (TopologicalSpace.Opens.ext ?_))
    ext q
    constructor
    · intro hq
      show q ∈ PrimeSpectrum.basicOpen ϖ
      rw [PrimeSpectrum.mem_basicOpen]
      intro hmem
      rcases eq_or_ne q.asIdeal ⊥ with h0 | h0
      · rw [h0] at hmem
        exact hϖ.ne_zero (Ideal.mem_bot.mp hmem)
      · exact hcl (by rw [← hclosed q h0]; exact hq)
    · intro hq
      have h0 : q.asIdeal = ⊥ := by
        by_contra h0
        have hqc := hclosed q h0
        have hq' : ϖ ∉ q.asIdeal := hq
        apply hq'
        rw [hqc]
        exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
      have : q = (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) := PrimeSpectrum.ext h0
      rw [this]
      exact hgen

/-- **Flatness of the extension over the discrete valuation ring.**  The quotient of
`M` by the saturated kernel is flat over `Spec R`: its sections have no `ϖ`-torsion by
the saturation property, torsion-free modules over a discrete valuation ring are flat,
and over the generic point (respectively the empty set) the section ring is a field
(respectively trivial). -/
lemma Modules.flatOver_cokernel_kernel_to_pushforward
    {P W : Scheme.{u}} {G : W ⟶ P} [IsOpenImmersion G]
    {M : P.Modules} {QW : W.Modules} [M.IsQuasicoherent] [QW.IsQuasicoherent]
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (p : P ⟶ Spec (CommRingCat.of R)) (t : Γ(P, ⊤))
    (ht : (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) = t)
    (hrange : G.opensRange = P.basicOpen t)
    (φ : M ⟶ (Modules.pushforward G).obj QW) :
    (cokernel (kernel.ι φ)).FlatOver p := by
  intro U V hUV
  letI := Module.compHom Γ(cokernel (kernel.ι φ), U.1)
    ((P.presheaf.map (homOfLE hUV).op).hom.comp ((p.app V.1).hom))
  rcases DVR_opens_trichotomy hϖ V.1 with hV | hV | hV
  · -- the empty open: the sections are trivial
    have hU : U.1 = ⊥ := by
      refine le_bot_iff.mp (le_trans hUV ?_)
      rw [hV]
      intro x hx
      simpa using hx
    haveI : Subsingleton Γ(cokernel (kernel.ι φ), U.1) := by
      rw [hU]
      exact Modules.subsingleton_sections_bot _
    infer_instance
  · -- the generic point: the section ring is a field
    have hfield : IsField Γ(Spec (CommRingCat.of R), V.1) := by
      set w : Γ(Spec (CommRingCat.of R), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ with hw
      haveI hloc := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_basicOpen w
      haveI := IsDiscreteValuationRing.isLocalization_away_of_irreducible hϖ
        (FractionRing R)
      have hwϖ : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w = ϖ := by
        rw [hw, ← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl
      have hmap : (Submonoid.powers w).map
          (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMonoidHom =
          Submonoid.powers ϖ := by
        rw [Submonoid.map_powers]
        exact congrArg Submonoid.powers hwϖ
      let e₀ : Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen w) ≃+*
          FractionRing R :=
        IsLocalization.ringEquivOfRingEquiv
          Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen w)
          (FractionRing R)
          (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv hmap
      have hfield₀ : IsField
          Γ(Spec (CommRingCat.of R), (Spec (CommRingCat.of R)).basicOpen w) :=
        MulEquiv.isField (Field.toIsField (FractionRing R)) e₀.toMulEquiv
      have hV' : V.1 = (Spec (CommRingCat.of R)).basicOpen w := by
        rw [hV, hw]
        exact (AlgebraicGeometry.basicOpen_eq_of_affine
          (R := CommRingCat.of R) ϖ).symm
      refine MulEquiv.isField hfield₀ ?_
      exact (CategoryTheory.Iso.commRingCatIsoToRingEquiv
        ((Spec (CommRingCat.of R)).presheaf.mapIso (eqToIso hV').op)).symm.toMulEquiv
    letI : Field Γ(Spec (CommRingCat.of R), V.1) := hfield.toField
    infer_instance
  · -- the whole space: torsion-freeness over the discrete valuation ring
    -- the coefficient equivalence `R ≃ Γ(Spec R, V)`
    let e : R ≃+* Γ(Spec (CommRingCat.of R), V.1) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.trans
        (CategoryTheory.Iso.commRingCatIsoToRingEquiv
          ((Spec (CommRingCat.of R)).presheaf.mapIso (eqToIso hV).op))
    set d : Γ(Spec (CommRingCat.of R), V.1) →+* Γ(P, U.1) :=
      ((P.presheaf.map (homOfLE hUV).op).hom.comp ((p.app V.1).hom)) with hd
    have hflatR :
        letI := Module.compHom Γ(cokernel (kernel.ι φ), U.1) (d.comp e.toRingHom)
        Module.Flat R Γ(cokernel (kernel.ι φ), U.1) := by
      letI := Module.compHom Γ(cokernel (kernel.ι φ), U.1) (d.comp e.toRingHom)
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
      rw [Submodule.eq_bot_iff]
      rintro q hq
      rw [Submodule.mem_torsion_iff] at hq
      obtain ⟨⟨r, hr⟩, hrq⟩ := hq
      have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
      -- remove the unit
      have hu : IsUnit ((d.comp e.toRingHom) ((u : Rˣ) : R)) :=
        (Units.isUnit u).map (d.comp e.toRingHom)
      have hq1 : (ϖ ^ k : R) • q = 0 := by
        have h1 : ((u : Rˣ) : R) • ((ϖ ^ k : R) • q) = 0 := by
          rw [smul_smul]
          exact hrq
        obtain ⟨w, hw⟩ := hu
        have h2 : ((u : Rˣ) : R) • ((ϖ ^ k : R) • q) =
            (w : Γ(P, U.1)) • ((ϖ ^ k : R) • q) := by
          show (d.comp e.toRingHom) ((u : Rˣ) : R) • ((ϖ ^ k : R) • q) = _
          rw [hw]
        rw [h2] at h1
        have h3 := congrArg (fun z ↦ ((w⁻¹ : (Γ(P, U.1))ˣ) : Γ(P, U.1)) • z) h1
        beta_reduce at h3
        rwa [smul_smul, Units.inv_mul, one_smul, smul_zero] at h3
      -- the `ϖ`-action is the `t`-action
      have hϖt0 : ∀ z : Γ(cokernel (kernel.ι φ), U.1),
          (ϖ : R) • z = ((P.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t) • z := by
        intro z
        show (d.comp e.toRingHom) ϖ • z = _
        congr 1
        -- `d (e ϖ)` is the restriction of `t`
        rw [← ht]
        have hnat := CategoryTheory.congr_fun
          (p.naturality (homOfLE (le_top : V.1 ≤ ⊤)).op)
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
        -- identify `e ϖ` with the restriction of the global section
        have he' : e.toRingHom ϖ =
            ((Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) := by
          show ((Spec (CommRingCat.of R)).presheaf.map ((eqToIso hV).op).hom).hom
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) = _
          have hmapeq : (Spec (CommRingCat.of R)).presheaf.map ((eqToIso hV).op).hom =
              (Spec (CommRingCat.of R)).presheaf.map
                (homOfLE (le_top : V.1 ≤ ⊤)).op := by
            congr 1
          rw [hmapeq]
        rw [hd]
        show (P.presheaf.map (homOfLE hUV).op).hom ((p.app V.1).hom (e.toRingHom ϖ)) = _
        rw [he', hnat]
        -- collapse the two restrictions on `P`
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        congr 1
      have hpow2 : ∀ (i : ℕ) (z : Γ(cokernel (kernel.ι φ), U.1)),
          (ϖ ^ i : R) • z =
            ((P.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t) ^ i • z := by
        intro i
        induction i with
        | zero =>
          intro z
          rw [pow_zero, pow_zero, one_smul, one_smul]
        | succ i ih =>
          intro z
          rw [pow_succ, pow_succ, mul_comm, mul_smul, mul_comm, mul_smul, ih, hϖt0]
      -- conclude by the saturation torsion-freeness
      have hq2 : ((P.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom t) ^ k • q = 0 := by
        rw [← hpow2 k q]
        exact hq1
      exact Modules.cokernel_t_smul_regular t hrange φ U k q hq2
    exact Module.Flat.compHom_of_ringEquiv e (d.comp e.toRingHom) d rfl hflatR

/-- Restrict a presentation of the restriction to a larger open to a smaller open. -/
noncomputable def Modules.presentationRestrictOfLE {P : Scheme.{u}} (M : P.Modules)
    {V X₀ : P.Opens} (h : V ≤ X₀)
    (Pr : SheafOfModules.Presentation (M.restrict X₀.ι)) :
    SheafOfModules.Presentation (M.restrict V.ι) := by
  haveI := (Modules.restrictAdjunction (P.homOfLE h)).leftAdjoint_preservesColimits
  exact SheafOfModules.Presentation.ofIsIso
    (((Modules.restrictFunctorComp (P.homOfLE h) X₀.ι).symm.app M ≪≫
      (Modules.restrictFunctorCongr (P.homOfLE_ι h)).app M).hom)
    (Pr.map (Modules.restrictFunctor (P.homOfLE h))
      ((Modules.restrictUnitIso (P.homOfLE h)).symm))

instance Modules.presentationRestrictOfLE_isFinite {P : Scheme.{u}} (M : P.Modules)
    {V X₀ : P.Opens} (h : V ≤ X₀)
    (Pr : SheafOfModules.Presentation (M.restrict X₀.ι)) [Pr.IsFinite] :
    (Modules.presentationRestrictOfLE M h Pr).IsFinite := by
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite Pr.generators.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite }
    isFiniteType_relations := {
      finite := by
        change Finite Pr.relations.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite } }

/-- A sheaf of modules on an affine spectrum with a finite presentation has finitely
generated global sections: the generators give an epimorphism from a finite free
sheaf, whose global sections surject by quasicoherence. -/
lemma Modules.finite_moduleSpecΓ_of_presentation {A : CommRingCat.{u}}
    {N : (Spec A).Modules} (Pr : SheafOfModules.Presentation N) [Pr.IsFinite] :
    Module.Finite A (moduleSpecΓFunctor.obj N) := by
  haveI : N.IsQuasicoherent := Pr.isQuasicoherent
  haveI : (SheafOfModules.free (R := (Spec A).ringCatSheaf)
      Pr.generators.I).IsQuasicoherent := free_isQuasicoherent _
  haveI : Epi Pr.generators.π := Pr.generators.epi
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map Pr.generators.π) :=
    moduleSpecΓFunctor_map_surjective_of_epi Pr.generators.π
  haveI : Finite Pr.generators.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  haveI : Module.Finite A (Pr.generators.I →₀ A) :=
    Module.Finite.of_basis Finsupp.basisSingleOne
  haveI : Module.Finite A
      (moduleSpecΓFunctor.obj (SheafOfModules.free
        (R := (Spec A).ringCatSheaf) Pr.generators.I)) :=
    Module.Finite.equiv (freeModuleSpecΓIso Pr.generators.I).toLinearEquiv
  exact Module.Finite.of_surjective (moduleSpecΓFunctor.map Pr.generators.π).hom hsurj

/-- Transport a presentation of a module on an affine open subscheme to the canonical
spectrum model. -/
noncomputable def Modules.presentationSpecModel {P : Scheme.{u}} {V : P.Opens}
    (hV : IsAffineOpen V) (K : V.toScheme.Modules)
    (Pr : SheafOfModules.Presentation K) :
    haveI : IsAffine V.toScheme := hV
    SheafOfModules.Presentation
      ((Modules.restrictFunctor V.toScheme.isoSpec.inv).obj K) := by
  haveI : IsAffine V.toScheme := hV
  haveI := (Modules.restrictAdjunction
    V.toScheme.isoSpec.inv).leftAdjoint_preservesColimits
  exact Pr.map (Modules.restrictFunctor V.toScheme.isoSpec.inv)
    ((Modules.restrictUnitIso V.toScheme.isoSpec.inv).symm)

instance Modules.presentationSpecModel_isFinite {P : Scheme.{u}} {V : P.Opens}
    (hV : IsAffineOpen V) (K : V.toScheme.Modules)
    (Pr : SheafOfModules.Presentation K) [Pr.IsFinite] :
    (Modules.presentationSpecModel hV K Pr).IsFinite := by
  haveI : IsAffine V.toScheme := hV
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite Pr.generators.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite }
    isFiniteType_relations := {
      finite := by
        change Finite Pr.relations.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite } }

/-- Transport a presentation from the canonical spectrum model of an affine open
subscheme back to the subscheme. -/
noncomputable def Modules.presentationOfSpecModel {P : Scheme.{u}} {V : P.Opens}
    (hV : IsAffineOpen V) (K : V.toScheme.Modules)
    (Pr : haveI : IsAffine V.toScheme := hV
      SheafOfModules.Presentation
        ((Modules.restrictFunctor V.toScheme.isoSpec.inv).obj K)) :
    SheafOfModules.Presentation K := by
  haveI : IsAffine V.toScheme := hV
  haveI := (Modules.restrictAdjunction
    V.toScheme.isoSpec.hom).leftAdjoint_preservesColimits
  exact SheafOfModules.Presentation.ofIsIso
    (((Modules.restrictFunctorComp V.toScheme.isoSpec.hom
        V.toScheme.isoSpec.inv).symm.app K ≪≫
      (Modules.restrictFunctorCongr V.toScheme.isoSpec.hom_inv_id).app K ≪≫
      Modules.restrictFunctorId.app K).hom)
    (Pr.map (Modules.restrictFunctor V.toScheme.isoSpec.hom)
      ((Modules.restrictUnitIso V.toScheme.isoSpec.hom).symm))

instance Modules.presentationOfSpecModel_isFinite {P : Scheme.{u}} {V : P.Opens}
    (hV : IsAffineOpen V) (K : V.toScheme.Modules)
    (Pr : haveI : IsAffine V.toScheme := hV
      SheafOfModules.Presentation
        ((Modules.restrictFunctor V.toScheme.isoSpec.inv).obj K)) [hPr : Pr.IsFinite] :
    (Modules.presentationOfSpecModel hV K Pr).IsFinite := by
  haveI : IsAffine V.toScheme := hV
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite Pr.generators.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite }
    isFiniteType_relations := {
      finite := by
        change Finite Pr.relations.I
        exact SheafOfModules.GeneratingSections.IsFiniteType.finite } }

set_option maxHeartbeats 1600000 in
/-- Per-chart form: an epimorphic image of a sheaf whose restriction to an affine open
admits a finite presentation itself admits one over that open, when the section ring
is Noetherian. -/
noncomputable def Modules.psigma_finite_presentation_restrict_of_epi
    {P : Scheme.{u}} {N C : P.Modules} [N.IsQuasicoherent] [C.IsQuasicoherent]
    (π₀ : N ⟶ C) [Epi π₀] (V : P.affineOpens) [IsNoetherianRing Γ(P, V.1)]
    (PrN : SheafOfModules.Presentation (N.restrict V.1.ι)) [PrN.IsFinite] :
    Σ' Pr : SheafOfModules.Presentation (C.restrict V.1.ι), Pr.IsFinite := by
  haveI hVaff : IsAffine V.1.toScheme := V.2
  haveI : IsNoetherianRing Γ(V.1.toScheme, ⊤) :=
    isNoetherianRing_of_ringEquiv Γ(P, V.1)
      V.1.topIso.symm.commRingCatIsoToRingEquiv
  -- global sections of the model of `N` are finitely generated
  haveI hMfin := Modules.finite_moduleSpecΓ_of_presentation
    (Modules.presentationSpecModel V.2 _ PrN)
  -- the projection of the models is epi
  haveI := (Modules.restrictAdjunction V.1.ι).leftAdjoint_preservesColimits
  haveI := (Modules.restrictAdjunction
    V.1.toScheme.isoSpec.inv).leftAdjoint_preservesColimits
  set ψ := (Modules.restrictFunctor V.1.toScheme.isoSpec.inv).map
    ((Modules.restrictFunctor V.1.ι).map π₀) with hψ
  haveI : Epi ψ := by
    rw [hψ]
    infer_instance
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map ψ) :=
    moduleSpecΓFunctor_map_surjective_of_epi ψ
  haveI hCfin := Module.Finite.of_surjective (hM := hMfin)
    (moduleSpecΓFunctor.map ψ).hom hsurj
  haveI hCfin' : Module.Finite Γ(V.1.toScheme, ⊤)
      (moduleSpecΓFunctor.obj
        ((Modules.restrictFunctor V.1.toScheme.isoSpec.inv).obj
          ((Modules.restrictFunctor V.1.ι).obj C))) := hCfin
  haveI : Module.FinitePresentation Γ(V.1.toScheme, ⊤)
      (moduleSpecΓFunctor.obj
        ((Modules.restrictFunctor V.1.toScheme.isoSpec.inv).obj
          ((Modules.restrictFunctor V.1.ι).obj C))) :=
    Module.finitePresentation_of_finite _ _
  have hex := exists_finitePresentation_of_moduleSpecΓFunctor
    ((Modules.restrictFunctor V.1.toScheme.isoSpec.inv).obj
      ((Modules.restrictFunctor V.1.ι).obj C))
  haveI := hex.choose_spec
  exact ⟨Modules.presentationOfSpecModel V.2
    ((Modules.restrictFunctor V.1.ι).obj C) hex.choose, inferInstance⟩

set_option maxHeartbeats 1600000 in
/-- **Finite presentation of the extension.**  Over a locally Noetherian scheme, the
quotient of a finitely presented quasicoherent sheaf by the saturated kernel is
finitely presented: its sections over small affine opens are finitely generated over
the Noetherian section rings, hence finitely presented, and finite presentation of
sheaves of modules is local. -/
lemma Modules.isFinitePresentation_cokernel_kernel_to_pushforward
    {P W : Scheme.{u}} {G : W ⟶ P} [IsOpenImmersion G]
    {M : P.Modules} {QW : W.Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [QW.IsQuasicoherent] [IsLocallyNoetherian P]
    (t : Γ(P, ⊤)) (hrange : G.opensRange = P.basicOpen t)
    (φ : M ⟶ (Modules.pushforward G).obj QW) :
    (cokernel (kernel.ι φ)).IsFinitePresentation := by
  classical
  haveI : (kernel φ).IsQuasicoherent :=
    Modules.kernel_to_pushforward_isQuasicoherent G t hrange φ
  haveI : (cokernel (kernel.ι φ)).IsQuasicoherent :=
    Modules.cokernel_isQuasicoherent (kernel.ι φ)
  -- the finite-presentation data of `M`, converted to restrictions
  obtain ⟨σdata, hσfin⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  haveI := hσfin
  -- the refined cover: affine opens contained in members of the presentation cover
  let I := Σ l : σdata.I, {V : P.affineOpens // V.1 ≤ σdata.X l}
  let U : I → P.Opens := fun i ↦ i.2.1.1
  have hUcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    apply top_unique
    intro x _
    have hx : x ∈ iSup σdata.X := by
      rw [(_root_.Opens.coversTop_iff _ _).mp σdata.coversTop]
      trivial
    obtain ⟨l, hxl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hVaff, hxV, hVl⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      P.isBasis_affineOpens) hxl
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨l, ⟨⟨V, hVaff⟩, hVl⟩⟩, hxV⟩
  -- per-chart finite presentations of the restriction of the extension
  have presC : ∀ i : I, Σ' Pr : SheafOfModules.Presentation
      ((cokernel (kernel.ι φ)).restrict (U i).ι), Pr.IsFinite := by
    rintro ⟨l, V, hVl⟩
    haveI : IsNoetherianRing Γ(P, V.1) :=
      IsLocallyNoetherian.component_noetherian V
    exact Modules.psigma_finite_presentation_restrict_of_epi
      (cokernel.π (kernel.ι φ)) V
      (Modules.presentationRestrictOfLE M hVl
        (Modules.presentationRestrictOfOver M (σdata.X l) (σdata.presentation l)))
  -- conclude by locality of finite presentation
  haveI : ∀ i : I, ((fun i ↦ (presC i).1) i).IsFinite := fun i ↦ (presC i).2
  exact Modules.isFinitePresentation_of_isOpenCover (cokernel (kernel.ι φ)) U hUcov
    (fun i ↦ (presC i).1)

/-- The restriction of the kernel of the adjoint morphism has the same sectionwise
range as the kernel of the original quotient of the restricted sheaf: both consist of
the sections killed by the quotient. -/
lemma Modules.range_restrict_kernel_ι_adjoint {P W : Scheme.{u}} (G : W ⟶ P)
    [IsOpenImmersion G] {M : P.Modules} {QW : W.Modules}
    (π'' : (Modules.restrictFunctor G).obj M ⟶ QW) :
    PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor G).map (kernel.ι
        (((Modules.restrictAdjunction G).homEquiv M QW) π''))).val =
    PresheafOfModules.Submodule.range (kernel.ι π'').val := by
  set φ : M ⟶ (Modules.pushforward G).obj QW :=
    ((Modules.restrictAdjunction G).homEquiv M QW) π'' with hφ
  refine PresheafOfModules.Submodule.ext fun V ↦ ?_
  ext s
  rw [PresheafOfModules.Submodule.mem_range_iff, PresheafOfModules.Submodule.mem_range_iff]
  -- the left side: sections killed by `φ` over the image open
  have hL : (∃ y, ((Modules.restrictFunctor G).map (kernel.ι φ)).app V.unop y = s) ↔
      (φ.app (G ''ᵁ V.unop)).hom s = 0 :=
    Modules.exists_kernel_ι_app_eq_iff φ (G ''ᵁ V.unop) s
  -- the right side: sections killed by `π''`
  have hR : (∃ y, (kernel.ι π'').app V.unop y = s) ↔ (π''.app V.unop).hom s = 0 :=
    Modules.exists_kernel_ι_app_eq_iff π'' V.unop s
  -- the two vanishing conditions agree through naturality along equal opens
  have hbridge : (φ.app (G ''ᵁ V.unop)).hom s = 0 ↔ (π''.app V.unop).hom s = 0 := by
    have hunit : φ.app (G ''ᵁ V.unop) =
        (M.presheaf.map (homOfLE (G.image_preimage_le (G ''ᵁ V.unop))).op) ≫
          π''.app (G ⁻¹ᵁ (G ''ᵁ V.unop)) := by
      rw [hφ]
      rfl
    have hnat := π''.mapPresheaf.naturality
      (homOfLE ((G.preimage_image_eq V.unop).le)).op
    have hres : ((Modules.restrictFunctor G).obj M).presheaf.map
        (homOfLE ((G.preimage_image_eq V.unop).le)).op =
        M.presheaf.map (homOfLE (G.image_preimage_le (G ''ᵁ V.unop))).op := by
      rw [Scheme.Modules.restrict_map]
      congr 1
    have hchain : (φ.app (G ''ᵁ V.unop)).hom s =
        (QW.presheaf.map (homOfLE ((G.preimage_image_eq V.unop).le)).op).hom
          ((π''.app V.unop).hom s) := by
      have h1 := CategoryTheory.congr_fun hnat s
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h1
      simp only [Scheme.Modules.mapPresheaf_app] at h1
      have h2 : (φ.app (G ''ᵁ V.unop)).hom s =
          (π''.app (G ⁻¹ᵁ (G ''ᵁ V.unop))).hom
            ((M.presheaf.map (homOfLE (G.image_preimage_le (G ''ᵁ V.unop))).op).hom s) := by
        rw [hunit]
        rfl
      rw [h2]
      exact (congrArg (π''.app (G ⁻¹ᵁ (G ''ᵁ V.unop))).hom
        (CategoryTheory.congr_fun hres s)).symm.trans h1
    rw [hchain]
    constructor
    · intro h0
      have hinj : Function.Injective
          ((QW.presheaf.map (homOfLE ((G.preimage_image_eq V.unop).le)).op).hom) := by
        have : IsIso (QW.presheaf.map
            (homOfLE ((G.preimage_image_eq V.unop).le)).op) := by
          have heq : (homOfLE ((G.preimage_image_eq V.unop).le)) =
              eqToHom (G.preimage_image_eq V.unop) := Subsingleton.elim _ _
          rw [heq]
          infer_instance
        exact (ConcreteCategory.bijective_of_isIso _).injective
      apply hinj
      rw [h0, map_zero]
    · intro h0
      rw [h0, map_zero]
  exact hL.trans (hbridge.trans hR.symm)

end SaturationQcoh

/-- A point of the Quot functor is determined by the kernel of its projection: the
setoid of `QuotientPullbackData` identifies two quotients exactly when their kernels
agree as subobjects of the pulled-back sheaf.  (Supporting lemma for the proof of
Proposition 2.4.2.) -/
lemma Modules.QuotientPullbackData.setoid_r_iff_kernelSubobject_eq
    {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S} {T : Over S}
    (x y : Modules.QuotientPullbackData F f T) :
    (Modules.QuotientPullbackData.setoid F f T).r x y ↔
      Limits.kernelSubobject x.π = Limits.kernelSubobject y.π := by
  constructor
  · rintro ⟨e, he⟩
    rw [← he, Limits.kernelSubobject_comp_mono]
  · intro h
    haveI := x.epi
    haveI := y.epi
    exact CategoryTheory.Abelian.exists_iso_comp_eq_of_kernelSubobject_eq x.π y.π h

set_option maxHeartbeats 1600000 in
/-- **Proposition 2.4.2** (`prop:quot-proper`, polynomial-free form): the valuative
criterion of properness for the Quot functor. Let `S` be a locally noetherian scheme
and `F` a finitely presented quasi-coherent sheaf on `ℙ^n_S`. Let `R` be a discrete
valuation ring with fraction field `K` and `Spec R → S` a morphism. Then restriction
from `Spec R` to the generic point `Spec K` is a bijection on points of the Quot
functor: every flat family of finitely presented quotients of `F` over `K` extends
uniquely to one over `R` (the extension is the image of `F_R → j_* Q`, which is
torsion free and hence flat over the DVR `R`).

Faithfulness caveat: the book states the criterion for a noetherian base, coherent
`F`, and quotients with a fixed Hilbert polynomial `P`, including the constancy of the
Hilbert polynomial of the extension. The fixed-`P` uniqueness clause and the exact
remaining polynomial-preservation condition are formalized below; see the `[decision]`
entry for Proposition 2.4.2 in this folder's COMMENTARY.md. -/
theorem quotFunctor_map_bijective_isFractionRing (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : Spec (.of R) ⟶ S) :
    Function.Bijective ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
          Over.mk σ))) := by
  classical
  set f := Scheme.projectiveSpaceOverπ n S with hf
  set jK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) with hjK
  set T : Over S := Over.mk σ with hT
  set T' : Over S := Over.mk (jK ≫ σ) with hT'
  set g : T' ⟶ T := Over.homMk jK rfl with hg
  -- discrete valuation ring data
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI hjKoi : IsOpenImmersion jK :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (R := R) K
  set G : ((Over.pullback f).obj T').left ⟶ ((Over.pullback f).obj T).left :=
    ((Over.pullback f).map g).left with hG
  haveI hgloi : IsOpenImmersion g.left := hjKoi
  have HPB : IsPullback G (pullback.fst T'.hom f) (pullback.fst T.hom f) g.left :=
    overPullbackMap_isPullback g
  haveI hGoi : IsOpenImmersion G := isOpenImmersion_of_isPullback HPB
  set p : ((Over.pullback f).obj T).left ⟶ Spec (CommRingCat.of R) :=
    pullback.fst T.hom f with hp
  set w : Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ with hw'
  set t : Γ(((Over.pullback f).obj T).left, ⊤) := (p.app ⊤).hom w with ht'
  have hw : w ∈ nonZeroDivisors Γ(Spec (CommRingCat.of R), ⊤) :=
    mem_nonZeroDivisors_of_commRingCatIso (Scheme.ΓSpecIso (CommRingCat.of R)) ϖ
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have hrange : G.opensRange = ((Over.pullback f).obj T).left.basicOpen t := by
    rw [opensRange_of_isPullback HPB]
    have hjKrange : Scheme.Hom.opensRange g.left =
        (Spec (CommRingCat.of R)).basicOpen w :=
      IsDiscreteValuationRing.opensRange_specMap_fractionRing hϖ K
    rw [hjKrange]
    exact Scheme.preimage_basicOpen p w
  set MF := (Modules.pullback ((Over.pullback f).obj T).hom).obj F with hMF
  constructor
  · -- INJECTIVITY: two flat extensions of equivalent generic quotients are equivalent.
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    have hxy' : (⟦a.pullback g⟧ :
        Quotient (Modules.QuotientPullbackData.setoid F f T')) = ⟦b.pullback g⟧ := hxy
    obtain ⟨e', he'⟩ := Quotient.exact hxy'
    apply Quotient.sound
    haveI := a.isQuasicoherent
    haveI := b.isQuasicoherent
    haveI := a.epi
    haveI := b.epi
    -- torsion-freeness of both quotients over the base
    have htfa : ∀ (V : ((Over.pullback f).obj T).left.affineOpens) (q : Γ(a.Q, V.1)),
        (((Over.pullback f).obj T).left.presheaf.map
          (homOfLE (le_top : V.1 ≤ ⊤)).op).hom t • q = 0 → q = 0 :=
      fun V q hq ↦ Modules.FlatOver.smul_regular_sections a.flatOver
        (isAffineOpen_top (Spec (CommRingCat.of R))) w hw V q hq
    have htfb : ∀ (V : ((Over.pullback f).obj T).left.affineOpens) (q : Γ(b.Q, V.1)),
        (((Over.pullback f).obj T).left.presheaf.map
          (homOfLE (le_top : V.1 ≤ ⊤)).op).hom t • q = 0 → q = 0 :=
      fun V q hq ↦ Modules.FlatOver.smul_regular_sections b.flatOver
        (isAffineOpen_top (Spec (CommRingCat.of R))) w hw V q hq
    -- the saturation description of both kernels
    have hka := Modules.range_kernel_ι_eq_openSubmoduleCondition G a.π t hrange htfa
    have hkb := Modules.range_kernel_ι_eq_openSubmoduleCondition G b.π t hrange htfb
    -- the generic-fibre equivalence identifies the pulled-back kernels
    have hcancel : (Modules.pullback G).map a.π ≫ e'.hom =
        (Modules.pullback G).map b.π := by
      have h0 : (Modules.PullbackQuotient.pullbackComparison F
            ((Over.pullback f).map g)).hom ≫
            ((Modules.pullback G).map a.π ≫ e'.hom) =
          (Modules.PullbackQuotient.pullbackComparison F
            ((Over.pullback f).map g)).hom ≫ (Modules.pullback G).map b.π := by
        rw [← Category.assoc]
        exact he'
      exact (cancel_epi (Modules.PullbackQuotient.pullbackComparison F
        ((Over.pullback f).map g)).hom).mp h0
    have hgen : PresheafOfModules.Submodule.range
          (kernel.ι ((Modules.pullback G).map a.π)).val =
        PresheafOfModules.Submodule.range
          (kernel.ι ((Modules.pullback G).map b.π)).val := by
      rw [← hcancel]
      exact (SheafOfModules.kernelRange_comp_isIso ((Modules.pullback G).map a.π) e').symm
    -- transfer the identification to the restriction functor
    set η := Scheme.Modules.restrictFunctorIsoPullback G with hη
    have hresa : (Modules.restrictFunctor G).map a.π =
        η.hom.app MF ≫ (Modules.pullback G).map a.π ≫ η.inv.app a.Q :=
      (NatIso.naturality_2 η a.π).symm
    have hresb : (Modules.restrictFunctor G).map b.π =
        η.hom.app MF ≫ (Modules.pullback G).map b.π ≫ η.inv.app b.Q :=
      (NatIso.naturality_2 η b.π).symm
    have hresrange : PresheafOfModules.Submodule.range
          (kernel.ι ((Modules.restrictFunctor G).map a.π)).val =
        PresheafOfModules.Submodule.range
          (kernel.ι ((Modules.restrictFunctor G).map b.π)).val := by
      refine (SheafOfModules.kernelRange_congr hresa).trans
        (Eq.trans ?_ (SheafOfModules.kernelRange_congr hresb).symm)
      refine SheafOfModules.kernelRange_precomp_iso_eq_of_eq (η.app MF) _ _ ?_
      calc PresheafOfModules.Submodule.range
            (kernel.ι ((Modules.pullback G).map a.π ≫ (η.app a.Q).inv)).val
          = PresheafOfModules.Submodule.range
              (kernel.ι ((Modules.pullback G).map a.π)).val :=
            SheafOfModules.kernelRange_comp_isIso _ (η.app a.Q).symm
        _ = PresheafOfModules.Submodule.range
              (kernel.ι ((Modules.pullback G).map b.π)).val := hgen
        _ = PresheafOfModules.Submodule.range
              (kernel.ι ((Modules.pullback G).map b.π ≫ (η.app b.Q).inv)).val :=
            (SheafOfModules.kernelRange_comp_isIso _ (η.app b.Q).symm).symm
    -- both kernels have the same sectionwise range in the ambient pulled-back sheaf
    have hfinal : PresheafOfModules.Submodule.range (kernel.ι a.π).val =
        PresheafOfModules.Submodule.range (kernel.ι b.π).val := by
      rw [hka, hkb]
      exact Modules.openSubmoduleCondition_eq_of_range_eq G MF _ _ hresrange
    -- hence equal kernel subobjects, and the classification concludes
    haveI : Mono (kernel.ι a.π).val := Modules.val_mono_of_mono _
    haveI : Mono (kernel.ι b.π).val := Modules.val_mono_of_mono _
    refine (Modules.QuotientPullbackData.setoid_r_iff_kernelSubobject_eq a b).mpr ?_
    exact Subobject.mk_eq_mk_of_comm _ _
      (MF.isoOfRangeEq (kernel.ι a.π) (kernel.ι b.π) hfinal)
      (SheafOfModules.isoOfRangeEq_hom_comp MF (kernel.ι a.π) (kernel.ι b.π) hfinal)
  · -- SURJECTIVITY: every generic quotient extends by the saturation of its kernel.
    intro y
    obtain ⟨y', rfl⟩ := Quotient.exists_rep y
    haveI := y'.isQuasicoherent
    haveI := y'.epi
    haveI hMFqc : MF.IsQuasicoherent := by
      haveI := ‹F.IsQuasicoherent›
      infer_instance
    haveI hMFfp : MF.IsFinitePresentation := by
      haveI := ‹F.IsFinitePresentation›
      infer_instance
    -- the base-change scheme is locally Noetherian
    haveI : IsNoetherianRing (CommRingCat.of R) :=
      inferInstanceAs (IsNoetherianRing R)
    haveI : IsLocallyNoetherian T.left :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    haveI : IsLocallyNoetherian ((Over.pullback f).obj T).left :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst T.hom f)
    -- the adjoint of the generic quotient
    set η := Scheme.Modules.restrictFunctorIsoPullback G with hη
    set C := Modules.PullbackQuotient.pullbackComparison F ((Over.pullback f).map g)
      with hCdef
    set π'' : (Modules.restrictFunctor G).obj MF ⟶ y'.Q :=
      η.hom.app MF ≫ C.inv ≫ y'.π with hπ''
    haveI : Epi π'' := by
      rw [hπ'']
      infer_instance
    set φ : MF ⟶ (Modules.pushforward G).obj y'.Q :=
      ((Modules.restrictAdjunction G).homEquiv MF y'.Q) π'' with hφdef
    haveI hkerqc : (kernel φ).IsQuasicoherent :=
      Modules.kernel_to_pushforward_isQuasicoherent G t hrange φ
    -- the extension
    let xdata : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T :=
      { Q := cokernel (kernel.ι φ)
        isQuasicoherent := Modules.cokernel_isQuasicoherent (kernel.ι φ)
        isFinitePresentation :=
          Modules.isFinitePresentation_cokernel_kernel_to_pushforward t hrange φ
        flatOver := Modules.flatOver_cokernel_kernel_to_pushforward hϖ p t ht'.symm
          hrange φ
        π := cokernel.π (kernel.ι φ)
        epi := inferInstance }
    refine ⟨⟦xdata⟧, ?_⟩
    have hgoal : (⟦Modules.QuotientPullbackData.pullback g xdata⟧ :
        Quotient (Modules.QuotientPullbackData.setoid F f T')) = ⟦y'⟧ := by
      apply Quotient.sound
      -- the kernel of the extension restricts to the kernel of the generic quotient
      haveI hml : Mono ((Modules.restrictFunctor G).map (kernel.ι φ)).val := by
        apply PresheafOfModules.mono_of_injective
        intro V
        exact Modules.app_injective_of_mono (kernel.ι φ) (G ''ᵁ V.unop)
      haveI hmr : Mono (kernel.ι π'').val := Modules.val_mono_of_mono _
      set eK : (Modules.restrictFunctor G).obj (kernel φ) ≅ kernel π'' :=
        ((Modules.restrictFunctor G).obj MF).isoOfRangeEq
          ((Modules.restrictFunctor G).map (kernel.ι φ)) (kernel.ι π'')
          (Modules.range_restrict_kernel_ι_adjoint G π'') with heK
      have heKcomp : eK.hom ≫ kernel.ι π'' =
          (Modules.restrictFunctor G).map (kernel.ι φ) :=
        SheafOfModules.isoOfRangeEq_hom_comp _ _ _ _
      -- the comparison of the restricted extension with the generic quotient
      set epres : (Modules.restrictFunctor G).obj (cokernel (kernel.ι φ)) ≅
          cokernel ((Modules.restrictFunctor G).map (kernel.ι φ)) :=
        PreservesCokernel.iso (Modules.restrictFunctor G) (kernel.ι φ) with hepres
      set ecoker : cokernel ((Modules.restrictFunctor G).map (kernel.ι φ)) ≅
          cokernel (kernel.ι π'') :=
        cokernel.mapIso _ _ eK (Iso.refl _) (by
          rw [Iso.refl_hom, Category.comp_id]
          exact heKcomp.symm) with hecoker
      set efin : cokernel (kernel.ι π'') ≅ y'.Q :=
        cokernelKernelIsoOfEpi π'' with hefin
      set eres : (Modules.restrictFunctor G).obj (cokernel (kernel.ι φ)) ≅ y'.Q :=
        epres ≪≫ ecoker ≪≫ efin with heres
      have hrescompat : (Modules.restrictFunctor G).map (cokernel.π (kernel.ι φ)) ≫
          eres.hom = π'' := by
        rw [heres, Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← Category.assoc,
          hepres]
        rw [PreservesCokernel.π_iso_hom]
        rw [Category.assoc, ← Category.assoc, hecoker, cokernel.mapIso_hom,
          cokernel.π_desc]
        rw [Iso.refl_hom, Category.id_comp, hefin]
        exact cokernel_π_comp_cokernelKernelIsoOfEpi_hom π''
      -- assemble the compatible isomorphism on the pullback side
      refine ⟨(η.app (cokernel (kernel.ι φ))).symm ≪≫ eres, ?_⟩
      show (C.hom ≫ (Modules.pullback G).map (cokernel.π (kernel.ι φ))) ≫
        (η.app (cokernel (kernel.ι φ))).symm.hom ≫ eres.hom = y'.π
      have hnat : (Modules.pullback G).map (cokernel.π (kernel.ι φ)) ≫
          η.inv.app (cokernel (kernel.ι φ)) =
          η.inv.app MF ≫ (Modules.restrictFunctor G).map (cokernel.π (kernel.ι φ)) :=
        η.inv.naturality (cokernel.π (kernel.ι φ))
      calc (C.hom ≫ (Modules.pullback G).map (cokernel.π (kernel.ι φ))) ≫
            (η.app (cokernel (kernel.ι φ))).symm.hom ≫ eres.hom
          = C.hom ≫ ((Modules.pullback G).map (cokernel.π (kernel.ι φ)) ≫
              η.inv.app (cokernel (kernel.ι φ))) ≫ eres.hom := by
            simp only [Category.assoc, Iso.symm_hom]
            rfl
        _ = C.hom ≫ (η.inv.app MF ≫
              (Modules.restrictFunctor G).map (cokernel.π (kernel.ι φ))) ≫ eres.hom := by
            rw [hnat]
        _ = C.hom ≫ η.inv.app MF ≫ π'' := by
            rw [Category.assoc, hrescompat]
        _ = C.hom ≫ η.inv.app MF ≫ η.hom.app MF ≫ C.inv ≫ y'.π := by
            rw [hπ'']
        _ = y'.π := by
            rw [← Category.assoc (η.inv.app MF), Iso.inv_hom_id_app, Category.id_comp,
              ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact hgoal

/-- API lemma for Proposition 2.4.2 (fixed-polynomial injectivity):
injectivity of a map on the ambient Quot functor implies injectivity on its
fixed-Hilbert-polynomial subfunctor. -/
theorem quotFunctorP_map_injective_of_quotFunctor_map_injective
    {n : ℕ} {S : Scheme.{u}}
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T')
    (h : Function.Injective
      ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g)) :
    Function.Injective ((quotFunctorP F P).map g) := by
  intro x y hxy
  apply Subtype.ext
  apply h
  exact congrArg Subtype.val hxy

/-- API lemma for Proposition 2.4.2 (the precise
fixed-polynomial obstruction): if the ambient Quot map is bijective, then the
fixed-polynomial map is surjective exactly when the unique ambient preimage of
every fixed-polynomial point again admits a representative with that Hilbert
polynomial. -/
theorem quotFunctorP_map_surjective_iff_extension_hasFiberwiseHilbertPolynomial
    {n : ℕ} {S : Scheme.{u}}
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T')
    (h : Function.Bijective
      ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g)) :
    Function.Surjective ((quotFunctorP F P).map g) ↔
      ∀ x : (quotFunctorP F P).obj T',
        ∃ a : Modules.QuotientPullbackData F
            (Scheme.projectiveSpaceOverπ n S) T.unop,
          Quotient.mk _ a = Function.surjInv h.2 x.1 ∧
          a.HasFiberwiseHilbertPolynomial P := by
  constructor
  · intro hsurj x
    obtain ⟨y, hy⟩ := hsurj x
    obtain ⟨a, ha, hP⟩ := y.2
    refine ⟨a, ha.trans ?_, hP⟩
    apply h.1
    rw [Function.rightInverse_surjInv h.2]
    exact congrArg Subtype.val hy
  · intro hP x
    obtain ⟨a, ha, hPa⟩ := hP x
    let y : (quotFunctorP F P).obj T :=
      ⟨Function.surjInv h.2 x.1,
        ⟨a, ha, hPa⟩⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact Function.rightInverse_surjInv h.2 x.1

/-- API lemma for Proposition 2.4.2 (fixed-polynomial uniqueness):
over a discrete valuation ring, restriction to the fraction field is injective
on the fixed-Hilbert-polynomial Quot functor. -/
theorem quotFunctorP_map_injective_isFractionRing (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Injective ((quotFunctorP F P).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
          Over.mk σ))) := by
  apply quotFunctorP_map_injective_of_quotFunctor_map_injective F P
  exact (quotFunctor_map_bijective_isFractionRing n S F R K σ).1

/-- The canonical-fraction-field specialization of
`quotFunctor_map_bijective_isFractionRing`. -/
theorem quotFunctor_map_bijective_fractionRing (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (σ : Spec (.of R) ⟶ S) :
    Function.Bijective ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ σ) ⟶
          Over.mk σ))) :=
  quotFunctor_map_bijective_isFractionRing n S F R (FractionRing R) σ

/-- API lemma for Proposition 2.4.2 (isomorphism transport):
the fibrewise Hilbert-polynomial condition is invariant under an isomorphism
of the corresponding sheaves on projective space. -/
theorem HasFiberwiseHilbertPolynomial.iso
    {n : ℕ} {T : Scheme.{u}}
    {Q Q' : (Scheme.projectiveSpaceOver n T).Modules}
    {P : Polynomial ℚ} (e : Q ≅ Q')
    (hQ : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    Scheme.HasFiberwiseHilbertPolynomial Q' P := by
  intro K hK s
  apply Scheme.HasHilbertPolynomialOver.iso
    ((Scheme.Modules.pullback
      (Scheme.projectiveSpaceOverMap n s)).mapIso e)
  exact hQ K hK s

/-- API lemma for Proposition 2.4.2 (representative transport):
equivalent Quot representatives have the same fibrewise Hilbert polynomial. -/
theorem Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_r
    {n : ℕ} {S : Scheme.{u}}
    {F : (Scheme.projectiveSpaceOver n S).Modules} {T : Over S}
    {a b : Modules.QuotientPullbackData F
      (Scheme.projectiveSpaceOverπ n S) T} {P : Polynomial ℚ}
    (hab : (Modules.QuotientPullbackData.setoid F
      (Scheme.projectiveSpaceOverπ n S) T).r a b)
    (hPb : b.HasFiberwiseHilbertPolynomial P) :
    a.HasFiberwiseHilbertPolynomial P := by
  obtain ⟨e, _⟩ := hab
  apply Scheme.HasFiberwiseHilbertPolynomial.iso
    ((Scheme.Modules.pullback
      (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).inv).mapIso e.symm)
  exact hPb

/-- API lemma for Proposition 2.4.2 (projective-space pullback):
the projective-space sheaf attached to a pulled-back Quot datum is the pullback
of the sheaf attached to the original datum, so its Hilbert polynomial
transports across that comparison. -/
theorem Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_on_projectiveSpace_pullback
    {n : ℕ} {S : Scheme.{u}}
    {F : (Scheme.projectiveSpaceOver n S).Modules} {T T' : Over S}
    (g : T' ⟶ T)
    {a : Modules.QuotientPullbackData F
      (Scheme.projectiveSpaceOverπ n S) T} {P : Polynomial ℚ}
    (hP : (a.pullback g).HasFiberwiseHilbertPolynomial P) :
    Scheme.HasFiberwiseHilbertPolynomial
      ((Scheme.Modules.pullback
        (Scheme.projectiveSpaceOverMap n g.left)).obj
          (Scheme.quotDataOnProjectiveSpace F a)) P := by
  apply Scheme.HasFiberwiseHilbertPolynomial.iso
    (a.quotDataOnProjectiveSpace_pullbackIso g)
  exact hP

/-- API lemma for Proposition 2.4.2 (eventual cohomology-and-base-change
bridge): if the quotient sheaf of a Quot datum over a DVR has finite-projective global
sections commuting with field base change in every sufficiently large twist, then the
Hilbert polynomial of its generic restriction determines the Hilbert polynomial of the
whole family.

This packages the exact output of relative Serre vanishing and Cohomology and Base Change
needed in the book's constancy argument. -/
theorem Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_eventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u})
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (a : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S)
      (Over.mk σ))
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange
      (Scheme.quotDataOnProjectiveSpace
        (n := n) (S := S) (T := Over.mk σ) F a))
    (hgeneric : Modules.QuotientPullbackData.HasFiberwiseHilbertPolynomial
      (a.pullback (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ)) P) :
    a.HasFiberwiseHilbertPolynomial P := by
  let g : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  have hpull : Scheme.HasFiberwiseHilbertPolynomial
      ((Scheme.Modules.pullback
        (Scheme.projectiveSpaceOverMap n g.left)).obj
          (Scheme.quotDataOnProjectiveSpace F a)) P :=
    a.hasFiberwiseHilbertPolynomial_on_projectiveSpace_pullback g
      (by simpa [g] using hgeneric)
  change Scheme.HasFiberwiseHilbertPolynomial
    (Scheme.quotDataOnProjectiveSpace F a) P
  apply H.hasFiberwiseHilbertPolynomial_of_baseChange
    (FractionRing R) (algebraMap R (FractionRing R)) P
  exact hpull.hasHilbertPolynomialOver (Field.toIsField (FractionRing R))

/-- Background definition for Proposition 2.4.2 (the remaining closed-fibre
condition): a sheaf on projective space over a DVR has Hilbert polynomial `P`
after restriction to the closed residue-field point. -/
def HasClosedFiberHilbertPolynomial
    (n : ℕ) (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    (P : Polynomial ℚ) : Prop :=
  Scheme.HasFiberwiseHilbertPolynomial
    ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n
      ((Spec (CommRingCat.of R)).fromSpecResidueField
        (IsLocalRing.closedPoint R)))).obj Q) P

/-- Background definition for Proposition 2.4.2 (closed-fibre condition for a
Quot representative): the quotient sheaf associated to a Quot datum has
Hilbert polynomial `P` after pulling the datum back to the closed point of the
DVR. -/
def Modules.QuotientPullbackData.HasClosedFiberHilbertPolynomial
    (n : ℕ) (S : Scheme.{u})
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (a : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S)
      (Over.mk σ)) (P : Polynomial ℚ) : Prop :=
  (a.pullback (Over.homMk
    ((Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)) rfl :
        Over.mk (((Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R)) ≫ σ) ⟶ Over.mk σ)).HasFiberwiseHilbertPolynomial P

/-- API lemma for Proposition 2.4.2 (generic and closed fibres):
let `a` be a Quot datum over a DVR whose generic restriction represents a
given `Quot^P` point. If the closed restriction of `a` has Hilbert polynomial
`P`, then `a` has fibrewise Hilbert polynomial `P` over the DVR.

The projective-space and DVR parameters are passed explicitly in the final
generic/closed comparison to avoid unfolding relative projective space during
type inference. -/
theorem Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_fractionRing_eq_of_closed
    (n : ℕ) (S : Scheme.{u})
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (x : (quotFunctorP F P).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ))))
    (a : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S)
      (Over.mk σ))
    (hgeneric : Quotient.mk _ (a.pullback (Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl)) = x.1)
    (hclosed : Modules.QuotientPullbackData.HasClosedFiberHilbertPolynomial
      n S F R σ a P) :
    a.HasFiberwiseHilbertPolynomial P := by
  obtain ⟨b, hb, hPb⟩ := x.2
  let g : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  have hgenericPullback :
      (a.pullback g).HasFiberwiseHilbertPolynomial P := by
    apply Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_r
      (Quotient.exact (hgeneric.trans hb.symm))
    exact hPb
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)
  let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
  change (a.pullback gc).HasFiberwiseHilbertPolynomial P at hclosed
  apply Scheme.HasFiberwiseHilbertPolynomial.of_dvr_generic_and_closed
    (n := n) (R := R)
      (Scheme.quotDataOnProjectiveSpace
        (n := n) (S := S) (T := Over.mk σ) F a) P
  · simpa [g] using
      a.hasFiberwiseHilbertPolynomial_on_projectiveSpace_pullback
        g hgenericPullback
  · simpa [c, gc] using
      a.hasFiberwiseHilbertPolynomial_on_projectiveSpace_pullback gc hclosed

/-- API lemma for Proposition 2.4.2 (exact fixed-polynomial
boundary): assuming the ambient Quot restriction map is bijective, restriction
on `Quot^P` is surjective exactly when the canonical ambient extension of every
generic `Quot^P` point has Hilbert polynomial `P` on the closed fibre.

The generic-fibre condition is automatic from the input point; the theorem
`hasFiberwiseHilbertPolynomial_of_fractionRing_eq_of_closed` and the DVR
generic/closed-point dichotomy then propagate the polynomial to every field
point of the extension. -/
theorem quotFunctorP_map_surjective_fractionRing_iff_extension_hasClosedFiberHilbertPolynomial
    (n : ℕ) (S : Scheme.{u})
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (h : Function.Bijective
      ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map
        (Quiver.Hom.op (Over.homMk
          (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R)))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ)))) :
    Function.Surjective
      ((quotFunctorP F P).map
        (Quiver.Hom.op (Over.homMk
          (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R)))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ))) ↔
      ∀ x : (quotFunctorP F P).obj
          (op (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap R (FractionRing R))) ≫ σ))),
        ∃ a : Modules.QuotientPullbackData F
            (Scheme.projectiveSpaceOverπ n S) (Over.mk σ),
          Quotient.mk _ a = Function.surjInv h.2 x.1 ∧
          a.HasClosedFiberHilbertPolynomial n S F R σ P := by
  let g : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  change Function.Surjective ((quotFunctorP F P).map g.op) ↔ _
  constructor
  · intro hsurj
    have hall :=
      (quotFunctorP_map_surjective_iff_extension_hasFiberwiseHilbertPolynomial
        F P g.op h).mp hsurj
    intro x
    obtain ⟨a, ha, hPa⟩ := hall x
    refine ⟨a, ha, ?_⟩
    let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
    change (a.pullback gc).HasFiberwiseHilbertPolynomial P
    exact a.hasFiberwiseHilbertPolynomial_pullback gc hPa
  · intro hclosed
    apply
      (quotFunctorP_map_surjective_iff_extension_hasFiberwiseHilbertPolynomial
        F P g.op h).mpr
    intro x
    obtain ⟨a, ha, hPa⟩ := hclosed x
    refine ⟨a, ha, ?_⟩
    apply a.hasFiberwiseHilbertPolynomial_of_fractionRing_eq_of_closed
      n S F P R σ x
    · change Quotient.mk _ (a.pullback g) = x.1
      calc
        Quotient.mk _ (a.pullback g) =
            (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g.op
              (Quotient.mk _ a) := rfl
        _ = (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g.op
              (Function.surjInv h.2 x.1) := congrArg _ ha
        _ = x.1 := Function.rightInverse_surjInv h.2 x.1
    · exact hPa

/-- API lemma for Proposition 2.4.2 (canonical fraction-field
specialization): restriction to `FractionRing R` is injective on `Quot^P`. -/
theorem quotFunctorP_map_injective_fractionRing (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S) :
    Function.Injective ((quotFunctorP F P).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ σ) ⟶
          Over.mk σ))) :=
  quotFunctorP_map_injective_isFractionRing n S F P R (FractionRing R) σ

/-- API lemma for Proposition 2.4.2 (fraction-field transport): for a
presheaf on schemes over `S`, bijectivity of restriction from a DVR to its canonical
fraction field implies bijectivity for any chosen fraction field of that DVR.

The comparison is induced by the unique `R`-algebra equivalence
`FractionRing R ≃ₐ[R] K`; contravariance identifies the arbitrary restriction map with
the canonical one followed by the functor's map of an isomorphism. -/
theorem map_bijective_isFractionRing_of_fractionRing
    {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S)
    (hcanonical : Function.Bijective (G.map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ)))) :
    Function.Bijective (G.map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
          Over.mk σ))) := by
  let eRing : CommRingCat.of (FractionRing R) ≅ CommRingCat.of K :=
    (FractionRing.algEquiv R K).toRingEquiv.toCommRingCatIso
  let eSpec : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (FractionRing R)) :=
    Scheme.Spec.mapIso eRing.op
  have heSpec : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    dsimp only [eSpec, eRing]
    rw [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext r
    exact (FractionRing.algEquiv R K).commutes r
  let eOver :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ≅
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) :=
    Over.isoMk eSpec (by
      change eSpec.hom ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) =
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ
      rw [← Category.assoc, heSpec])
  let gFrac :
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  let gK : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
      Over.mk σ :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl
  have hcomp : eOver.hom ≫ gFrac = gK := by
    apply CostructuredArrow.hom_ext
    exact heSpec
  change Function.Bijective (G.map gK.op)
  rw [← hcomp, op_comp, G.map_comp]
  exact (G.mapIso eOver.op).toEquiv.bijective.comp hcanonical

/-- Background definition for Proposition 2.4.2 (closed-fibre constancy boundary):
every canonical ambient extension of a fixed-polynomial Quot point over a DVR admits a
representative whose closed fibre still has Hilbert polynomial `P`.

Ambient extension and uniqueness are already supplied by
`quotFunctor_map_bijective_fractionRing`; this predicate records only the remaining
polynomial condition. -/
def CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (x : (quotFunctorP F P).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ)))),
    ∃ a : Modules.QuotientPullbackData F
        (Scheme.projectiveSpaceOverπ n S) (Over.mk σ),
      Quotient.mk _ a = Function.surjInv
        (quotFunctor_map_bijective_fractionRing n S F R σ).2 x.1 ∧
      a.HasClosedFiberHilbertPolynomial n S F R σ P

/-- Background definition for Proposition 2.4.2 (cohomology-and-base-change boundary):
every canonical ambient extension of a fixed-polynomial Quot point over a DVR admits a
representative whose quotient sheaf has eventual finite-projective global sections and
whose global sections commute with every field base change.

Relative Serre vanishing and Cohomology and Base Change for finitely presented flat
sheaves on projective space are expected to construct this datum. -/
def CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S)
    (x : (quotFunctorP F P).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ)))),
    ∃ a : Modules.QuotientPullbackData F
        (Scheme.projectiveSpaceOverπ n S) (Over.mk σ),
      Quotient.mk _ a = Function.surjInv
        (quotFunctor_map_bijective_fractionRing n S F R σ).2 x.1 ∧
      Nonempty (Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange
        (Scheme.quotDataOnProjectiveSpace
          (n := n) (S := S) (T := Over.mk σ) F a))

/-- API lemma for Proposition 2.4.2 (Cohomology and Base Change implies
closed-fibre constancy): eventual finite-projective global sections with field base
change for every canonical DVR extension imply the exact closed-fibre
Hilbert-polynomial condition in the valuative criterion. -/
theorem canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_eventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ)
    (hcbc : CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
      n S F P) :
    CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial n S F P := by
  intro R _ _ _ σ x
  obtain ⟨a, ha, ⟨H⟩⟩ := hcbc R σ x
  refine ⟨a, ha, ?_⟩
  let g : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  have hclass : Quotient.mk _ (a.pullback g) = x.1 := by
    calc
      Quotient.mk _ (a.pullback g) =
          (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g.op
            (Quotient.mk _ a) := rfl
      _ = (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g.op
            (Function.surjInv
              (quotFunctor_map_bijective_fractionRing n S F R σ).2 x.1) :=
        congrArg _ ha
      _ = x.1 := Function.rightInverse_surjInv
        (quotFunctor_map_bijective_fractionRing n S F R σ).2 x.1
  obtain ⟨b, hb, hPb⟩ := x.2
  have hgeneric : (a.pullback g).HasFiberwiseHilbertPolynomial P := by
    apply Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_r
      (Quotient.exact (hclass.trans hb.symm))
    exact hPb
  have hall : a.HasFiberwiseHilbertPolynomial P :=
    a.hasFiberwiseHilbertPolynomial_of_eventualGlobalSectionsBaseChange
      n S F P R σ H (by simpa [g] using hgeneric)
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)
  let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
  change (a.pullback gc).HasFiberwiseHilbertPolynomial P
  exact a.hasFiberwiseHilbertPolynomial_pullback gc hall

/-- API lemma for Proposition 2.4.2 (conditional fixed-polynomial
valuative criterion): if every canonical ambient DVR extension has Hilbert polynomial
`P` on its closed fibre, then restriction on `Quot^P` is bijective for every chosen
fraction field of every DVR. -/
theorem quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (P : Polynomial ℚ)
    (hclosed : CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S F P)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective ((quotFunctorP F P).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
          Over.mk σ))) := by
  have hambient := quotFunctor_map_bijective_fractionRing n S F R σ
  have hsurjective : Function.Surjective ((quotFunctorP F P).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ))) :=
    (quotFunctorP_map_surjective_fractionRing_iff_extension_hasClosedFiberHilbertPolynomial
      n S F P R σ hambient).2 (hclosed R σ)
  have hcanonical : Function.Bijective ((quotFunctorP F P).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ))) :=
    ⟨quotFunctorP_map_injective_fractionRing n S F P R σ, hsurjective⟩
  exact map_bijective_isFractionRing_of_fractionRing
    (quotFunctorP F P) R K σ hcanonical

/-- A representative of the Quot functor has a unique lift in every valuative square
whose valuation ring is discrete. -/
theorem nonempty_unique_lift_of_quotFunctor_representableBy_dvr
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] {Q : Over S}
    (hrep : (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).RepresentableBy Q)
    (sq : ValuativeCommSq Q.hom) [IsDiscreteValuationRing sq.R] :
    Nonempty (Unique sq.commSq.LiftStruct) :=
  nonempty_unique_lift_of_representableBy_map_bijective hrep sq
    (quotFunctor_map_bijective_isFractionRing n S F sq.R sq.K sq.i₂)

section ClosedFiberFromCohomologyAndBaseChange

open Modules.QuotientPullbackData

/-- Scheme-level Serre vanishing on projective space over every DVR forces the
canonical twisted-free extension of each generic fixed-polynomial Quot point to
retain that polynomial on its closed fibre.

All intervening inputs in the book's argument are constructed internally: the
ambient Quot extension, its normalized twisted-free epimorphism on `ℙⁿ_R`,
quasicoherence and finite presentation of the source and kernel, flatness of the
quotient, and field-extension invariance of the generic Hilbert polynomial. -/
theorem canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial n S
      (projectiveSpaceOverTwistedFree n S l r) P := by
  intro R _ _ _ σ x
  let F := projectiveSpaceOverTwistedFree n S l r
  let hbij := quotFunctor_map_bijective_fractionRing n S F R σ
  obtain ⟨a, ha⟩ := Quotient.exists_rep (Function.surjInv hbij.2 x.1)
  refine ⟨a, ha, ?_⟩
  let g : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))) ≫ σ) ⟶ Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  have hclass : Quotient.mk _ (a.pullback g) = x.1 := by
    calc
      Quotient.mk _ (a.pullback g) =
          (quotFunctor F (projectiveSpaceOverπ n S)).map g.op
            (Quotient.mk _ a) := rfl
      _ = (quotFunctor F (projectiveSpaceOverπ n S)).map g.op
            (Function.surjInv hbij.2 x.1) := congrArg _ ha
      _ = x.1 := Function.rightInverse_surjInv hbij.2 x.1
  obtain ⟨b, hb, hPb⟩ := x.2
  have hgeneric : (a.pullback g).HasFiberwiseHilbertPolynomial P := by
    apply Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_of_r
      (Quotient.exact (hclass.trans hb.symm))
    exact hPb
  change HasFiberwiseHilbertPolynomial
    (quotDataOnProjectiveSpace F (a.pullback g)) P at hgeneric
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)
  let gc : Over.mk (c ≫ σ) ⟶ Over.mk σ := Over.homMk c rfl
  change (a.pullback gc).HasFiberwiseHilbertPolynomial P
  exact
    closedPullback_hasFiberwiseHilbertPolynomial_of_twistedFree_of_serre
      σ a (hserre R) ϖ hϖ P (by
        simpa [g, F, projectiveSpaceOverTwistedFree,
          Modules.QuotientPullbackData.twistedFreeAmbient] using hgeneric)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- API lemma for Proposition 2.4.2 (the DVR base-change obligation, for a
twisted-free ambient sheaf): every canonical DVR extension of a fixed-polynomial Quot point has
eventual finite-projective global sections whose formation commutes with field base change.

This is the graded Čech model of §2.3 applied to the kernel-route graded module
`Γ_*(𝒪(-l)^{⊕r}) ⧸ Γ_*(K)`; see
`AlgebraicGeometry.ProjectiveSpace.hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_twistedFreeEpi`.
The hypothesis `0 < n` is essential and not an artefact: on `ℙ⁰` the graded module `Γ_*(𝒪)` is
the base ring in *every* degree of `ℤ`, hence not finitely generated.  The dimension-zero case
is handled separately, by `canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_zero`
below. -/
theorem canonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange_twistedFree
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
      n S (projectiveSpaceOverTwistedFree n S l r) P := by
  intro A _ _ _ σ x
  set a := Quotient.out (Function.surjInv
    (quotFunctor_map_bijective_fractionRing n S _ A σ).2 x.1) with ha
  refine ⟨a, Quotient.out_eq _, ?_⟩
  haveI : (quotDataOnProjectiveSpace
      (projectiveSpaceOverTwistedFree n S l r) a).IsQuasicoherent :=
    quotDataOnProjectiveSpace_isQuasicoherent σ a
  haveI : a.Q.IsFinitePresentation := a.isFinitePresentation
  haveI : (quotDataOnProjectiveSpace
      (projectiveSpaceOverTwistedFree n S l r) a).IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : Epi (twistedFreeQuotientOnProjectiveSpace σ a) :=
    twistedFreeQuotientOnProjectiveSpace_epi σ a
  exact ⟨ProjectiveSpace.hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_twistedFreeEpi
    n A l r _ hn (twistedFreeQuotientOnProjectiveSpace σ a)
    (projectiveSpaceOverTwistedFree_isFinitePresentation n (Spec (.of A)) l r)
    (quotDataOnProjectiveSpace_flatOver σ a)⟩

/-- API lemma for Proposition 2.4.2 (closed-fibre constancy, unconditionally): the
canonical DVR extension of a fixed-polynomial Quot point of a twisted-free sheaf keeps its
Hilbert polynomial on the closed fibre, in every dimension.

For `0 < n` this is Cohomology and Base Change through the graded Čech model; for `n = 0` it is
the dimension-zero cohomology computation. -/
theorem canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_twistedFree
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S (projectiveSpaceOverTwistedFree n S l r) P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre
      0 S l r P (fun A _ _ _ =>
        projectiveSpaceHasSerreVanishing_zero_spec_of_isLocalRing A)
  · exact canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_eventualGlobalSectionsBaseChange
      n S _ P
      (canonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange_twistedFree
        n S hn l r P)

end ClosedFiberFromCohomologyAndBaseChange

end AlgebraicGeometry.Scheme

end PropQuotProper

section RmkHilbertValuativeCriterion

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- **Remark 2.4.4** (`rmk:hilbert-valuative-criterion`): the valuative criterion for the
Hilbert functor. For a DVR `R` with fraction field `K` over `S`, restriction along
`Spec K → Spec R` is a bijection on points of `Hilb(ℙ^n_S/S)`: every flat family of closed
subschemes of `ℙ^n_K` extends uniquely to one over `Spec R`.

The book's argument is the ideal-sheaf translation of Proposition 2.4.2: the unique
extension of a closed subscheme `Z ⊆ X_K` is the scheme-theoretic image
`Z̃ = im(Z → X_K ↪ X_R)`, which is flat over `R` because all of its associated points lie
over the generic point of `Spec R`.

Stated in the same polynomial-free form as `quotFunctor_map_bijective_fractionRing` above,
and for the same reason (see this folder's COMMENTARY.md): the Hilbert-polynomial refinement
needs the fibrewise Hilbert polynomial, which is available for the scheme model only through
the bridge described there.

The proof transports `quotFunctor_map_bijective_fractionRing` for `F = 𝒪_X` through
the natural Hilbert–Quot correspondence. -/
theorem AlgebraicGeometry.Scheme.hilbFunctor_map_bijective_fractionRing
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective ((Scheme.hilbFunctor (Scheme.projectiveSpaceOverπ n S)).map
      (Quiver.Hom.op (Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ σ) ⟶
          Over.mk σ))) := by
  let j :
      Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))) ≫ σ) ⟶
        Over.mk σ :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) rfl
  rw [← ULift.map_bijective]
  change Function.Bijective
    ((Scheme.hilbFunctor (Scheme.projectiveSpaceOverπ n S) ⋙
      uliftFunctor.{u + 1, u}).map j.op)
  letI : (SheafOfModules.unit
      (Scheme.projectiveSpaceOver n S).ringCatSheaf).IsQuasicoherent :=
    Scheme.Modules.unit_isQuasicoherent (Scheme.projectiveSpaceOver n S)
  letI : (SheafOfModules.unit
      (Scheme.projectiveSpaceOver n S).ringCatSheaf).IsFinitePresentation :=
    Scheme.Modules.unit_isFinitePresentation (Scheme.projectiveSpaceOver n S)
  rw [CategoryTheory.Functor.map_bijective_iff_of_iso
    (Scheme.hilbertStructureSheafQuotientNatIso
      (Scheme.projectiveSpaceOverπ n S)) j.op]
  exact Scheme.quotFunctor_map_bijective_fractionRing n S
    (SheafOfModules.unit (Scheme.projectiveSpaceOver n S).ringCatSheaf)
      R σ

end RmkHilbertValuativeCriterion

section ThmQuotClosedEmbedding

open CategoryTheory AlgebraicGeometry Limits

universe u v

/-- An H-quasi-projective proper morphism is H-projective: in a factorization through an
immersion into relative projective space, the immersion is proper and hence closed. -/
theorem AlgebraicGeometry.IsHQuasiProjective.isHProjective_of_isProper
    {X S : Scheme.{u}} {f : X ⟶ S} [IsProper f] (hf : IsHQuasiProjective f) :
    IsHProjective f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsImmersion ι := hι
  haveI : IsProper (ι ≫ Scheme.projectiveSpaceOverπ n S) := by
    rw [hcomp]
    infer_instance
  haveI : IsProper ι := IsProper.of_comp ι (Scheme.projectiveSpaceOverπ n S)
  exact ⟨n, ι, IsImmersion.isClosedImmersion_of_isProper ι, hcomp⟩

/-- The DVR-valuative projectivity endgame for one chosen quasi-projective
factorization.  If DVRs realize specializations of the immersion and the structure
morphism has unique DVR-valuative lifts, separatedness of relative projective space
transfers those lifts to the immersion; quasi-compactness then makes the immersion
closed.

The geometric realization hypothesis is exactly the input supplied by Proposition
A.4.4 for finite-type morphisms of noetherian schemes. -/
theorem AlgebraicGeometry.IsHProjective.of_dvrValuativeCriterion
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S]
    (n : ℕ) (ι : X ⟶ Scheme.projectiveSpaceOver n S)
    (hι : IsImmersion ι)
    (hcomp : ι ≫ Scheme.projectiveSpaceOverπ n S = f)
    (hreal : DVRRealizesSpecializations ι)
    (hvc : DVRValuativeCriterion f) :
    IsHProjective f := by
  letI : IsImmersion ι := hι
  haveI : IsLocallyNoetherian (Scheme.projectiveSpaceOver n S) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.projectiveSpaceOverπ n S)
  haveI : QuasiCompact ι := by
    rw [← ι.liftCoborder_ι]
    infer_instance
  have hcompvc : DVRValuativeCriterion
      (ι ≫ Scheme.projectiveSpaceOverπ n S) := by
    rw [hcomp]
    exact hvc
  have hιvc : DVRValuativeCriterion ι :=
    DVRValuativeCriterion.of_comp_of_isSeparated ι
      (Scheme.projectiveSpaceOverπ n S) hcompvc
  haveI : IsClosedImmersion ι :=
    IsClosedImmersion.of_dvrValuativeCriterion ι hreal hιvc
  exact ⟨n, ι, inferInstance, hcomp⟩

/-- The projectivity endgame for a represented moduli functor: H-quasi-projectivity over a
locally noetherian base supplies the finiteness hypotheses, and bijectivity across all
valuation rings supplies properness. -/
theorem AlgebraicGeometry.Scheme.isHProjective_of_representableBy_map_bijective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {Q : Over S}
    [IsLocallyNoetherian S] (hrep : F.RepresentableBy Q)
    (hq : IsHQuasiProjective Q.hom)
    (hbij : ∀ sq : ValuativeCommSq Q.hom,
      Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    IsHProjective Q.hom := by
  letI : QuasiCompact Q.hom := hq.quasiCompact
  letI : QuasiSeparated Q.hom := hq.quasiSeparated
  letI : LocallyOfFiniteType Q.hom := hq.locallyOfFiniteType
  letI : IsProper Q.hom := isProper_of_representableBy_map_bijective hrep hbij
  exact hq.isHProjective_of_isProper

/-- The DVR analogue of
`Scheme.isHProjective_of_representableBy_map_bijective`. A representation transports DVR
restriction bijectivity to unique lifts. Since an immersion into relative projective space
is locally of finite type and the latter is locally noetherian, Proposition A.4.4 supplies
the required DVR realizations of specializations automatically; then
`IsHProjective.of_dvrValuativeCriterion` closes the chosen immersion. -/
theorem AlgebraicGeometry.Scheme.isHProjective_of_representableBy_dvr_map_bijective
    {S : Scheme.{u}} {F : CategoryTheory.Functor (Over S)ᵒᵖ (Type v)} {Q : Over S}
    [IsLocallyNoetherian S] (hrep : F.RepresentableBy Q)
    (n : ℕ) (ι : Q.left ⟶ Scheme.projectiveSpaceOver n S)
    (hι : IsImmersion ι)
    (hcomp : ι ≫ Scheme.projectiveSpaceOverπ n S = Q.hom)
    (hbij : ∀ sq : ValuativeCommSq Q.hom, IsDiscreteValuationRing sq.R →
      Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    IsHProjective Q.hom := by
  letI : IsImmersion ι := hι
  haveI : IsLocallyNoetherian (Scheme.projectiveSpaceOver n S) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.projectiveSpaceOverπ n S)
  have hreal : DVRRealizesSpecializations ι :=
    ι.dvrRealizesSpecializations_of_locallyOfFiniteType
  apply IsHProjective.of_dvrValuativeCriterion n ι hι hcomp hreal
  exact dvrValuativeCriterion_of_representableBy_map_bijective hrep hbij

namespace AlgebraicGeometry.Scheme

/-- API lemma for Theorem 2.4.5 (categorical conditional
endgame): a relatively representable immersion of fixed-polynomial Quot into an
H-projectively represented functor, together with closed-fibre Hilbert-polynomial
constancy for canonical DVR extensions, makes Quot H-projective.

Unlike the specialized conditional theorem below, this formulation does not pass
through Proposition 2.4.1: it constructs the quasi-projective representative directly
from the relative immersion and therefore isolates exactly the two geometric inputs of
the book's proof. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_relative_immersion_of_closedFiber
    {n : ℕ} {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Scheme.projectiveSpaceOver n S).Modules}
    [F.IsQuasicoherent] [F.IsFinitePresentation] {P : Polynomial ℚ}
    {G : CategoryTheory.Functor (Over S)ᵒᵖ (Type (u + 1))}
    (α : Scheme.quotFunctorP F P ⟶ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α)
    (hG : ∃ Q₀ : Over S, Nonempty (G.RepresentableBy Q₀) ∧
      IsHProjective Q₀.hom)
    (hclosed : Scheme.CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S F P) :
    ∃ Q : Over S, Nonempty ((Scheme.quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hrep⟩, hq⟩ :=
    Scheme.exists_representableBy_isHQuasiProjective_of_relative_immersion α hα hG
  obtain ⟨m, ι, hι, hcomp⟩ := hq
  refine ⟨Q, ⟨hrep⟩,
    Scheme.isHProjective_of_representableBy_dvr_map_bijective
      hrep m ι hι hcomp ?_⟩
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  exact Scheme.quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    n S F P hclosed sq.R sq.K sq.i₂

/-- API lemma for Theorem 2.4.5 (closed-fibre reduction):
assume the twisted-free sheaf has the standard quasicoherence and finite-presentation
properties. If every canonical ambient extension over a DVR retains Hilbert polynomial
`P` on its closed fibre, then `Quot^P` is represented by a projective scheme over `S`.

Proposition 2.4.1 supplies a quasi-projective representing object. The closed-fibre
hypothesis gives bijectivity on all DVR fraction-field restrictions by Proposition 2.4.2,
and `isHProjective_of_representableBy_dvr_map_bijective` closes the immersion into relative
projective space. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hclosed : Scheme.CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hrep⟩, hq⟩ :=
    Scheme.exists_quotFunctorP_representableBy_isHQuasiProjective n S l r P
  obtain ⟨m, ι, hι, hcomp⟩ := hq
  refine ⟨Q, ⟨hrep⟩,
    Scheme.isHProjective_of_representableBy_dvr_map_bijective
      hrep m ι hι hcomp ?_⟩
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  exact Scheme.quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P hclosed
    sq.R sq.K sq.i₂

/-- API lemma for Theorem 2.4.5 (Cohomology and Base Change
conditional endgame): if every canonical twisted-free Quot extension over a DVR has
eventual finite-projective global sections commuting with field base change, then
`Quot^P` is represented by a projective scheme.

The generic point already has polynomial `P`; the base-change package propagates it to
the closed point, and the preceding valuative argument closes the quasi-projective
representative. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_eventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hcbc : Scheme.CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  Scheme.exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
    n S l r P
      (Scheme.canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_eventualGlobalSectionsBaseChange
        n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P hcbc)

/-- API lemma for Theorem 2.4.5 (general-ambient conditional
endgame): let a twisted-free sheaf surject onto `F`. If the universal vanishing loci of
the pulled-back ambient kernels are closed subschemes, and canonical DVR extensions for
the twisted-free Quot functor retain their Hilbert polynomial on the closed fibre, then
`Quot^P(F)` is represented by an H-projective scheme.

The proof contains no remaining functor or quotient-class bookkeeping: relative closedness
is supplied by `quotFunctorPPrecomp_relative_closed`, and projectivity descends from the
twisted-free representative by a closed immersion. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_presentation_zeroLoci_closedFiber
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : Scheme.projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj (Opposite.op T)),
      Nonempty (Scheme.QuotientKernelZeroLocusData p P T z))
    (hclosed : Scheme.CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  Scheme.exists_quotFunctorP_representableBy_isHProjective_of_precomp_zeroLoci
    p P H
    (Scheme.exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
      n S l r P hclosed)

/-- API lemma for Theorem 2.4.5 (finite-model conditional
endgame): a twisted-free presentation of `F`, compatible affine finite-free models for
the vanishing of its pulled-back kernel, and closed-fibre Hilbert-polynomial constancy
for canonical twisted-free DVR quotients imply projective representability of
`Quot^P(F)`.

The compatible affine models glue by uniqueness to the universal closed zero loci
required in the preceding theorem. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_presentation_finiteFreeModels_closedFiber
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : Scheme.projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj (Opposite.op T)),
      Nonempty (Scheme.CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)))
    (hclosed : Scheme.CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  Scheme.exists_quotFunctorP_representableBy_isHProjective_of_presentation_zeroLoci_closedFiber
    n S F l r p P
      (fun T z ↦
        ⟨Scheme.CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData
          p P (Classical.choice (H T z))⟩)
      hclosed

/-- API lemma for Theorem 2.4.5 (general-ambient CBC conditional
endgame): a twisted-free presentation of `F`, universal closed zero loci for its kernel,
and eventual Cohomology and Base Change for canonical twisted-free DVR quotients imply
projective representability of `Quot^P(F)`.

This is the complete formal reduction of the general theorem to the two geometric inputs
used in the book: Exercise 1.3.15 for the kernel zero locus and relative
Serre-vanishing/Cohomology and Base Change for the DVR family. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_presentation_zeroLoci_eventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : Scheme.projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj (Opposite.op T)),
      Nonempty (Scheme.QuotientKernelZeroLocusData p P T z))
    (hcbc : Scheme.CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  Scheme.exists_quotFunctorP_representableBy_isHProjective_of_presentation_zeroLoci_closedFiber
    n S F l r p P H
      (Scheme.canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_eventualGlobalSectionsBaseChange
        n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P hcbc)

/-- API lemma for Theorem 2.4.5 (finite-model and CBC conditional
endgame): compatible affine finite-free kernel-vanishing models and eventual Cohomology
and Base Change for the canonical twisted-free DVR quotients imply projective
representability of `Quot^P(F)`. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_presentation_finiteFreeModels_eventualGlobalSectionsBaseChange
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : Scheme.projectiveSpaceOverTwistedFree n S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).obj (Opposite.op T)),
      Nonempty (Scheme.CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)))
    (hcbc : Scheme.CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange
      n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  Scheme.exists_quotFunctorP_representableBy_isHProjective_of_presentation_finiteFreeModels_closedFiber
    n S F l r p P H
      (Scheme.canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_eventualGlobalSectionsBaseChange
        n S (Scheme.projectiveSpaceOverTwistedFree n S l r) P hcbc)

end AlgebraicGeometry.Scheme

/-- **Theorem 2.4.5** (`thm:quot-closed-embedding`): let `S` be a noetherian scheme and
`π : ℙ^n_S → S` relative projective space. If `F = 𝒪_{ℙ^n_S}(-l)^{⊕r}` and `P ∈ ℚ[z]`, then
`Quot^P(F/ℙ^n_S)` is representable by a projective scheme over `S`.

Together with Proposition 2.4.1 and Proposition 2.4.2 this completes the proofs of
Theorem 2.1.2 and Theorem 2.1.3: the Quot functor is
quasi-projective by the first, proper by the second, and quasi-projective plus proper is
projective.

The book obtains it from the sharper statement that for `d ≫ 0` the map
`Quot^P(F/ℙ^n_S) → Gr(P(d), π_* F(d))` is a *closed* immersion, and then descends to an
arbitrary coherent `F` by choosing a surjection `𝒪(-l)^{⊕r} ↠ F` and showing the induced map
of Quot functors is representable by closed immersions
(Exercise 2.4.3). Only the "in particular" clause is stated
here; see this folder's COMMENTARY.md.

The proof is the valuative endgame: Proposition 2.4.2 supplies properness through
`canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_twistedFree`, which is now
unconditional (Cohomology and Base Change in the graded Čech model for `0 < n`, the
dimension-zero cohomology computation for `n = 0`), and Proposition 2.4.1 supplies the
quasi-projective representative.  The latter is still open, so this theorem is complete modulo
`exists_quotFunctorP_representableBy_isHQuasiProjective` alone. -/
theorem AlgebraicGeometry.Scheme.exists_quotFunctorP_representableBy_isHProjective
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((Scheme.quotFunctorP
        (Scheme.projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  cases n with
  | zero =>
      exact Scheme.exists_quotFunctorP_zero_representableBy_isHProjective S l r P
  | succ n =>
      exact
        Scheme.exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
          (n + 1) S l r P
          (Scheme.canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_twistedFree
            (n + 1) S l r P)

end ThmQuotClosedEmbedding
