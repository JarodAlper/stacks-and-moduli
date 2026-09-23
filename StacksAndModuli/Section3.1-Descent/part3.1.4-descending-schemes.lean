module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.3-descending-morphisms»
public import StacksAndModuli.Util.FpqcCover
public import StacksAndModuli.API.QuasicoherentIdealDescent
public import StacksAndModuli.API.RepresentableSheafProperty
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Fpqc descent for schemes

This module formalizes Proposition 3.1.11 (`prop:fpqc-descent-for-open-closed-subschemes`)
of §3.1 (Descent theory, `sec:descent-theory`) of *Stacks and Moduli*.

For open and closed subschemes, descent data along a covering `{f : S' ⟶ S}` need no
cocycle condition (immersions are monomorphisms): a subscheme `Z' ⊆ S'` descends as soon
as its two pullbacks to `S' ×_S S'` agree.

Main results:
- `AlgebraicGeometry.Scheme.exists_opens_preimage_eq_of_fpqcCover` (proved): descent of
  open subschemes;
- `AlgebraicGeometry.Scheme.exists_isClosedImmersion_of_fpqcCover`: descent of closed
  subschemes, reduced to effective descent of quasi-coherent ideal sheaves.

The later results of this subsection — Proposition 3.1.12
(`prop:fpqc-descent-for-affine-quasi-affine-schemes`), Theorem 3.1.14
(`thm:fppf-descent-for-separated-locally-quasi-finite-schemes`), and Proposition 3.1.17
(`prop:fpqc-descent-for-principal-G-bundles`) — are not yet formalized here; per-label
completeness is tracked in this folder's STATUS.md. Related stack-property statements in
the pseudofunctor language appear in `StacksAndModuli.«Section3.5-Stacks»` (`ex:stack-of-schemes`).
The example of non-effective descent (`ex:non-effective-descent`) and the historical
remarks carry no formalizable statements beyond the counterexamples cited there.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropFpqcDescentForOpenClosedSubschemes

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {S' S : Scheme.{u}} {f : S' ⟶ S}

/-- Symmetric form of `IdealSheafData.ker_fst_of_isClosedImmersion`: the kernel ideal of
the second projection from a pullback of a closed immersion is the pullback of its kernel
ideal. -/
lemma IdealSheafData.ker_snd_of_isClosedImmersion {X Y Z : Scheme.{u}}
    (i : Z ⟶ Y) (g : X ⟶ Y) [IsClosedImmersion i] :
    (pullback.snd i g).ker = i.ker.comap g := by
  calc
    (pullback.snd i g).ker =
        ((pullbackSymmetry i g).hom ≫ pullback.fst g i).ker := by
          rw [pullbackSymmetry_hom_comp_fst]
    _ = (pullback.fst g i).ker :=
      Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry i g).hom _
    _ = i.ker.comap g := IdealSheafData.ker_fst_of_isClosedImmersion i g

/-- An isomorphism over the base between two pullbacks of a closed subscheme identifies
their defining ideal sheaves.  This extracts the quasi-coherent ideal descent datum from
the geometric hypothesis in `exists_isClosedImmersion_of_fpqcCover`. -/
lemma pulledBackKernel_eq_of_iso {Z' : Scheme.{u}} (i' : Z' ⟶ S') [IsClosedImmersion i']
    (e : pullback i' (pullback.fst f f) ≅ pullback i' (pullback.snd f f))
    (he : e.hom ≫ pullback.snd i' (pullback.snd f f) =
      pullback.snd i' (pullback.fst f f)) :
    i'.ker.comap (pullback.fst f f) = i'.ker.comap (pullback.snd f f) := by
  rw [← IdealSheafData.ker_snd_of_isClosedImmersion,
    ← IdealSheafData.ker_snd_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso e.hom, he]

/-- Helper lemma used in the proof of Proposition 3.1.11 (ideal-sheaf
step of the closed case, implicit in the proof): effective fpqc descent for quasi-coherent
ideal sheaves, in the kernel-pair form needed for closed subschemes.  The equality is the
descent datum; no separate cocycle hypothesis is needed because inclusions of ideal
sheaves are monomorphisms. -/
theorem IdealSheafData.exists_of_fpqcCover (hf : Scheme.IsFpqcCover f)
    (I' : S'.IdealSheafData)
    (h : I'.comap (pullback.fst f f) = I'.comap (pullback.snd f f)) :
    ∃ I : S.IdealSheafData, I.comap f = I' := by
  exact I'.exists_descended_of_fpqcCover f h hf

/-- A subset of the source of a scheme morphism whose two inverse images along the kernel
pair agree is saturated: its inverse image from its set-theoretic image is itself. -/
lemma preimage_image_eq_of_pullback_preimage_eq (U' : Set S')
    (h : (pullback.fst f f) ⁻¹' U' = (pullback.snd f f) ⁻¹' U') :
    f.base ⁻¹' (f.base '' U') = U' := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    obtain ⟨z, hfst, hsnd⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x y hxy.symm
    have hz : pullback.snd f f z ∈ U' := by simpa [hsnd] using hy
    have : pullback.fst f f z ∈ U' := by
      change z ∈ (pullback.fst f f) ⁻¹' U'
      rw [h]
      exact hz
    simpa [hfst] using this
  · intro x hx
    exact ⟨x, hx, rfl⟩

/-- Open subschemes descend along surjective flat quasi-compact morphisms. This is the
global quotient-map form of fpqc descent; the more general `fpqcCover` statement below is
obtained by applying it to quasi-compact restrictions over affine opens. -/
lemma exists_opens_preimage_eq_of_surjective_flat_quasiCompact (f : S' ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] (U' : S'.Opens)
    (h : (pullback.fst f f) ⁻¹ᵁ U' = (pullback.snd f f) ⁻¹ᵁ U') :
    ∃ U : S.Opens, f ⁻¹ᵁ U = U' := by
  have hsaturated := preimage_image_eq_of_pullback_preimage_eq (f := f) (U' : Set S')
    (congrArg SetLike.coe h)
  let U : S.Opens :=
    ⟨f.base '' (U' : Set S'), by
      apply (Flat.isQuotientMap_of_surjective f).isOpen_preimage.mp
      rw [hsaturated]
      exact U'.2⟩
  refine ⟨U, ?_⟩
  ext x
  exact Set.ext_iff.mp hsaturated x

set_option backward.isDefEq.respectTransparency.types false in
/-- The image of an open saturated for the kernel pair of a singleton fpqc cover is open. -/
lemma IsFpqcCover.isOpen_image_of_preimage_image_eq (hf : Scheme.IsFpqcCover f)
    (U' : S'.Opens) (hsaturated : f.base ⁻¹' (f.base '' (U' : Set S')) = (U' : Set S')) :
    IsOpen (f.base '' (U' : Set S')) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨V, hVc, hVA⟩ := hf.exists_compact_opens_image_eq hA
  haveI : Flat f := by
    have hflat : Presieve.singleton f ∈ Scheme.precoverage @Flat S := hf.2
    exact (Scheme.singleton_mem_precoverage_iff (P := @Flat) f).mp hflat |>.2
  have eVA : V ≤ f ⁻¹ᵁ A := by
    intro y hy
    change f y ∈ (A : Set S)
    rw [← hVA]
    exact ⟨y, hy, rfl⟩
  let g : (V : Scheme) ⟶ (A : Scheme) := f.resLE A V eVA
  letI : Surjective g := ⟨fun y ↦ by
    obtain ⟨z, hzV, hz⟩ := Set.ext_iff.mp hVA y.1 |>.mpr y.2
    refine ⟨⟨z, hzV⟩, ?_⟩
    apply Subtype.ext
    simpa [g, Scheme.Hom.coe_resLE_apply] using hz⟩
  letI : Flat g := by
    dsimp [g]
    infer_instance
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  letI : IsAffine A := hA
  letI : QuasiCompact g := by infer_instance
  let B : Set A := Subtype.val ⁻¹' (f.base '' (U' : Set S'))
  have hpre : g.base ⁻¹' B = V.ι.base ⁻¹' (U' : Set S') := by
    ext y
    simp only [Set.mem_preimage]
    simpa [g, B, Scheme.Hom.coe_resLE_apply] using Set.ext_iff.mp hsaturated y.1
  have hB : IsOpen B := by
    apply (Flat.isQuotientMap_of_surjective g).isOpen_preimage.mp
    rw [hpre]
    exact U'.2.preimage V.ι.continuous
  refine ⟨(Scheme.Opens.ι A).base '' B, ?_,
    (Scheme.Opens.ι A).isOpenMap _ hB, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · exact ⟨⟨x, hxA⟩, hx, rfl⟩

/-- **Proposition 3.1.11** (`prop:fpqc-descent-for-open-closed-subschemes`) (open case):
fpqc descent for open subschemes. Let `{f : S' ⟶ S}` be an fpqc covering (e.g. a
surjective flat quasi-compact morphism) and let `U' ⊆ S'` be an open subscheme whose two
preimages in `S' ×_S S'` agree. Then `U'` descends to an open subscheme of `S`: there is a
(unique) open `U ⊆ S` with `f⁻¹(U) = U'`. -/
theorem exists_opens_preimage_eq_of_fpqcCover (hf : Scheme.IsFpqcCover f) (U' : S'.Opens)
    (h : (pullback.fst f f) ⁻¹ᵁ U' = (pullback.snd f f) ⁻¹ᵁ U') :
    ∃ U : S.Opens, f ⁻¹ᵁ U = U' := by
  have hsaturated := preimage_image_eq_of_pullback_preimage_eq (f := f) (U' : Set S')
    (congrArg SetLike.coe h)
  let U : S.Opens :=
    ⟨f.base '' (U' : Set S'), hf.isOpen_image_of_preimage_image_eq U' hsaturated⟩
  refine ⟨U, ?_⟩
  ext x
  exact Set.ext_iff.mp hsaturated x

/-- **Proposition 3.1.11** (`prop:fpqc-descent-for-open-closed-subschemes`) (closed case):
fpqc descent for closed subschemes. Let `{f : S' ⟶ S}` be an fpqc covering and let
`i' : Z' ⟶ S'` be a closed immersion such that the two pullbacks of `Z'` to `S' ×_S S'`
coincide (as closed subschemes: they are isomorphic over `S' ×_S S'`). Then `Z'` descends:
there exists a closed immersion `i : Z ⟶ S` and an isomorphism `Z' ≅ Z ×_S S'` over
`S'`. -/
theorem exists_isClosedImmersion_of_fpqcCover (hf : Scheme.IsFpqcCover f) {Z' : Scheme.{u}}
    (i' : Z' ⟶ S') [IsClosedImmersion i']
    (e : pullback i' (pullback.fst f f) ≅ pullback i' (pullback.snd f f))
    (he : e.hom ≫ pullback.snd i' (pullback.snd f f) =
      pullback.snd i' (pullback.fst f f)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ S) (_ : IsClosedImmersion i)
      (e' : Z' ≅ pullback i f), i' = e'.hom ≫ pullback.snd i f := by
  obtain ⟨I, hI⟩ := IdealSheafData.exists_of_fpqcCover hf i'.ker
    (pulledBackKernel_eq_of_iso i' e he)
  let j : (I.comap f).subscheme ⟶ S' := (I.comap f).subschemeι
  let a : Z' ⟶ (I.comap f).subscheme :=
    IsClosedImmersion.lift j i' (by rw [IdealSheafData.ker_subschemeι, hI])
  haveI : IsIso a := by
    apply IsClosedImmersion.isIso_of_ker_eq i' j a
    · exact IsClosedImmersion.lift_fac j i' _
    · change i'.ker = (I.comap f).subschemeι.ker
      rw [IdealSheafData.ker_subschemeι, hI]
  let e' : Z' ≅ pullback I.subschemeι f :=
    asIso a ≪≫ I.comapIso f ≪≫ pullbackSymmetry f I.subschemeι
  refine ⟨I.subscheme, I.subschemeι, inferInstance, e', ?_⟩
  dsimp [e']
  rw [Category.assoc, Category.assoc,
    pullbackSymmetry_hom_comp_snd, IdealSheafData.comapIso_hom_fst]
  exact (IsClosedImmersion.lift_fac j i' _).symm

end AlgebraicGeometry.Scheme

end PropFpqcDescentForOpenClosedSubschemes
