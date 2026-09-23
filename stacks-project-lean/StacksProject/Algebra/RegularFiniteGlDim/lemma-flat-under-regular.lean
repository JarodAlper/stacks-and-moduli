module

public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension

/-!
# A Noetherian local ring flat under a regular local ring is regular

Stacks Project tag **00OF**, label `algebra-lemma-flat-under-regular`, in `algebra.tex`,
§`065U` (`section-regular-finite-gl-dim`, Regular rings and global dimension).

> Let `R → S` be a local homomorphism of local Noetherian rings. Assume that `R → S` is flat
> and that `S` is regular. Then `R` is regular.

The proof uses the finite-module portion of the classical chain
`00OF ← 00OC ← 00O7`.  A finite partial projective resolution of the residue field of `R`
becomes a resolution over `S`; the regular-local projective-dimension bound makes its last
syzygy projective.  Faithful flatness descends flatness of that syzygy, and finite flat modules
over local rings are free.  The resulting finite projective dimension of the residue field
implies regularity by the minimal-resolution/Kaplansky-retract proof of `00OC` in
`ProjectiveDimension.lean`.
-/

@[expose] public section

universe u

open TensorProduct

section Tag00OF

/-- **Stacks 00OF** (`algebra-lemma-flat-under-regular`). Let `A → B` be a flat local
homomorphism of Noetherian local rings. If `B` is regular, then so is `A`. -/
@[stacks 00OF]
theorem isRegularLocalRing_of_flat_of_isLocalHom (A : Type u) (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [IsLocalRing A] [IsNoetherianRing A]
    [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing B] : IsRegularLocalRing A := by
  classical
  obtain ⟨s, -, hs⟩ :=
    IsRegularLocalRing.maximalIdeal_generated_by_dim (R := B)
  have hBdim : ∀ (M : Type u) [AddCommGroup M] [Module B M]
      [Module.Finite B M], Module.HasProjectiveDimensionLE B s.card M :=
    Module.hasProjectiveDimensionLE_of_isRegularLocalRing s.card B hs.symm
  haveI : Module.Finite A (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (IsLocalRing.maximalIdeal A).mkQ
      (Submodule.mkQ_surjective _)
  obtain ⟨K, _, _, _, hres⟩ := Module.exists_isPartialProjectiveResolution_finite
    A (IsLocalRing.ResidueField A) s.card
  haveI : Module.Projective B (B ⊗[A] K) :=
    (hres.baseChange B).projective_of_projectiveDimension_le (by omega)
      (hBdim (B ⊗[A] IsLocalRing.ResidueField A))
  haveI : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat A K :=
    Module.Flat.of_flat_tensorProduct (R := A) (M := K) B
  haveI : Module.FinitePresentation A K :=
    Module.finitePresentation_of_finite A K
  haveI : Module.Free A K := Module.free_of_flat_of_isLocalRing
  have hK0 : Module.HasProjectiveDimensionLE A 0 K :=
    (Module.hasProjectiveDimensionLE_zero_iff_projective A K).mpr
      Module.Projective.of_free
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField
    (0 + s.card + 1) A (hres.hasProjectiveDimensionLE hK0)

end Tag00OF
