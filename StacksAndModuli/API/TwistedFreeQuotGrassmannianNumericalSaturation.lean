module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianRelationKernelCohomology
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianLineSaturation

/-!
# Numerical saturation for reconstructed twisted-free quotients

The relation-kernel condition in next-degree saturation is not automatic, even on the
projective line.  It does follow on the locus where the algebraic and geometric
degree-`d+1` objects are vector bundles of the same rank.

Precisely, epimorphy of the reconstructed monomial map makes the canonical comparison

`twistedFreeNextDegreeModule ⟶ projectiveTwistedPushforward`

an epimorphism.  If its source and target are both projective of rank `k`,
`Modules.isIso_of_epi_of_isProjectiveOfRank` makes it an isomorphism.  Comparing the two
cokernel presentations then forces the reconstructed kernel lift to be an epimorphism.
Thus equality of the two next-degree ranks supplies exactly the missing relation-generation
condition; finite local freeness of the degree-`d` coefficient alone does not.

On a projective line over a noetherian affine base, finite local freeness of the degree-`d`
relation coefficient makes the reconstructed monomial map epic.  The same equal-rank
hypothesis therefore gives both vanishing of the remaining relation-kernel `H¹` and full
next-degree saturation.

Main declarations:

* `CategoryTheory.Limits.kernelLift_epi_of_cokernelDesc_isIso`;
* `Scheme.twistedFreeNextDegreeReconstructedKernelLift_epi_of_equal_rank`;
* `Scheme.twistedFreeNextDegreeReconstructionSaturation_of_equal_rank`;
* `Scheme.subsingleton_H_one_reconstructedNextDegreeRelationKernel_line_of_equal_rank`;
* `Scheme.twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_of_equal_rank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `f` be an epimorphism and let `g` be a proposed family of generators for
`kernel f`.  If the induced morphism from the cokernel of `g ≫ kernel.ι f` to the
target of `f` is an isomorphism, then `g` is an epimorphism. -/
lemma kernelLift_epi_of_cokernelDesc_isIso
    {W X Y : C} (f : X ⟶ Y) [Epi f] (g : W ⟶ kernel f)
    [IsIso (cokernel.desc (g ≫ kernel.ι f) f (by simp))] :
    Epi g := by
  let c := cokernel.desc (g ≫ kernel.ι f) f (by simp)
  let S := ShortComplex.mk (g ≫ kernel.ι f) f (by simp)
  haveI hc : IsIso c := by
    dsimp only [c]
    infer_instance
  have hfac : cokernel.π (g ≫ kernel.ι f) ≫ c = f := by
    dsimp only [c]
    exact cokernel.π_desc _ _ _
  have hexact : S.Exact := by
    rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
    change kernel.ι f ≫ cokernel.π (g ≫ kernel.ι f) = 0
    apply (cancel_mono c).mp
    calc
      (kernel.ι f ≫ cokernel.π (g ≫ kernel.ι f)) ≫ c =
          kernel.ι f ≫ (cokernel.π (g ≫ kernel.ι f) ≫ c) :=
        Category.assoc _ _ _
      _ = kernel.ι f ≫ f := congrArg (fun z ↦ kernel.ι f ≫ z) hfac
      _ = 0 := kernel.condition f
      _ = 0 ≫ c := zero_comp.symm
  have hepi : Epi (kernel.lift f (g ≫ kernel.ι f) (by simp)) :=
    S.exact_iff_epi_kernel_lift.mp hexact
  have hlift : kernel.lift f (g ≫ kernel.ι f) (by simp) = g := by
    apply (cancel_mono (kernel.ι f)).mp
    simp
  rw [hlift] at hepi
  exact hepi

end CategoryTheory.Limits

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The kernel of an epimorphic finite monomial-free quotient is finite locally free
whenever its target is finite locally free. -/
lemma twistedFreeMonomialQuotientMap_kernel_isFiniteLocallyFree
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ)
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [hu : Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    Modules.IsFiniteLocallyFree (kernel u) := by
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
  exact @Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
    T _ E (by infer_instance) (by infer_instance) hSource hE u hu

/-- If the reconstructed degree-`d+1` monomial map is epic and the algebraic
next-degree module and geometric twisted pushforward are vector bundles of the same rank,
then the degree-one-generated relations generate the full reconstructed kernel. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_epi_of_equal_rank
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e k : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hq : Epi (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)))
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule n T r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward n
        (reconstructedQuotient' n T l r d e he u) (d + 1))) :
    Epi (twistedFreeNextDegreeReconstructedKernelLift
      n T l r d e he u) := by
  let q := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let g := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he u
  let c := twistedFreeNextDegreeModuleToReconstructedPushforward
    n T l r d e he u
  letI : Epi q := hq
  letI hnextQC : (twistedFreeNextDegreeModule n T r e u).IsQuasicoherent :=
    twistedFreeNextDegreeModule_isQuasicoherent n T r e u
  letI hquotQC : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  letI hpushQC : (Modules.projectiveTwistedPushforward n
      (reconstructedQuotient' n T l r d e he u) (d + 1)).IsQuasicoherent := by
    infer_instance
  letI : Epi c := by
    dsimp only [c]
    exact twistedFreeNextDegreeModuleToReconstructedPushforward_epi_of_epi
      n T l r d e he u hq
  letI hc : IsIso c :=
    Modules.isIso_of_epi_of_isProjectiveOfRank hnext hpush c
  have hrel : g ≫ kernel.ι q = twistedFreeNextDegreeRelation n T r e u := by
    dsimp only [g, q]
    exact twistedFreeNextDegreeReconstructedKernelLift_comp n T l r d e he u
  have hzero := Eq.trans
    (congrArg (fun z ↦ z ≫ q) hrel)
    (twistedFreeNextDegreeRelation_comp_reconstructedPushforwardMap
      n T l r d e he u)
  let I := cokernel.mapIso (g ≫ kernel.ι q)
    (twistedFreeNextDegreeRelation n T r e u)
    (Iso.refl _) (Iso.refl _)
    (Eq.trans (Category.comp_id _)
      (Eq.trans hrel (Category.id_comp _).symm))
  letI hIiso : IsIso I.hom := by
    dsimp only [I]
    infer_instance
  let c' := cokernel.desc (g ≫ kernel.ι q) q hzero
  have hI : cokernel.π (g ≫ kernel.ι q) ≫ I.hom =
      cokernel.π (twistedFreeNextDegreeRelation n T r e u) := by
    dsimp only [I, cokernel.mapIso_hom]
    exact cokernel.π_desc _ _ _
  have hfac : cokernel.π (twistedFreeNextDegreeRelation n T r e u) ≫ c = q := by
    dsimp only [c, q]
    exact twistedFreeNextDegreeModuleToReconstructedPushforward_fac
      n T l r d e he u
  have hfac' : cokernel.π (g ≫ kernel.ι q) ≫ c' = q := by
    dsimp only [c']
    exact cokernel.π_desc _ _ _
  have hc' : I.hom ≫ c = c' := by
    apply (cancel_epi (cokernel.π (g ≫ kernel.ι q))).mp
    have hleft :
        cokernel.π (g ≫ kernel.ι q) ≫ (I.hom ≫ c) =
          cokernel.π (twistedFreeNextDegreeRelation n T r e u) ≫ c := by
      calc
        cokernel.π (g ≫ kernel.ι q) ≫ (I.hom ≫ c) =
            (cokernel.π (g ≫ kernel.ι q) ≫ I.hom) ≫ c :=
          (Category.assoc _ _ _).symm
        _ = cokernel.π (twistedFreeNextDegreeRelation n T r e u) ≫ c :=
          congrArg (fun z ↦ z ≫ c) hI
    exact hleft.trans (hfac.trans hfac'.symm)
  haveI hcomp : IsIso (I.hom ≫ c) :=
    @IsIso.comp_isIso _ _ _ _ _ I.hom c hIiso hc
  haveI hdesc : IsIso c' := by
    rw [← hc']
    exact hcomp
  dsimp only [c'] at hdesc
  exact @CategoryTheory.Limits.kernelLift_epi_of_cokernelDesc_isIso
    _ _ _ _ _ _ q _ g hdesc

/-- The common next-degree rank condition, together with epimorphy of the reconstructed
monomial map, supplies both fields of reconstructed next-degree saturation. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_equal_rank
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e k : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hq : Epi (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)))
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule n T r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward n
        (reconstructedQuotient' n T l r d e he u) (d + 1))) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u where
  reconstructedPushforwardMap_epi := hq
  relationKernelLift_epi :=
    twistedFreeNextDegreeReconstructedKernelLift_epi_of_equal_rank
      n T l r d e k he u hq hnext hpush

/-- On a projective line over a noetherian affine base, finite local freeness of the
degree-`d` relation coefficient and equality of the algebraic and geometric next-degree
ranks imply vanishing of the reconstructed relation-kernel `H¹`. -/
theorem subsingleton_H_one_reconstructedNextDegreeRelationKernel_line_of_equal_rank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e k : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule 1 (Spec (.of R)) r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) (d + 1))) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1) := by
  haveI hKqc : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  have hpullback1 :=
    @subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
      R _ _ (kernel u) hKqc hK
  have hsource1 := Modules.subsingleton_H_of_iso
    (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
      1 (Spec (.of R)) d (kernel u)).symm 1 hpullback1
  have hq := reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing_line
    R l r d e he u hpullback1
  have hlift := twistedFreeNextDegreeReconstructedKernelLift_epi_of_equal_rank
    1 (Spec (.of R)) l r d e k he u hq hnext hpush
  exact
    (subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_kernelLift_epi
      1 (Spec (.of R)) l r d e he u hK hsource1).2 hlift

/-- On a projective line over a noetherian affine base, finite local freeness of the
degree-`d` relation coefficient and equality of the two next-degree ranks imply full
reconstructed saturation. -/
theorem
    twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_of_equal_rank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e k : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule 1 (Spec (.of R)) r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) (d + 1))) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  haveI hKqc : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  have hpullback1 :=
    @subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_of_isFiniteLocallyFree
      R _ _ (kernel u) hKqc hK
  have hq := reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing_line
    R l r d e he u hpullback1
  exact twistedFreeNextDegreeReconstructionSaturation_of_equal_rank
    1 (Spec (.of R)) l r d e k he u hq hnext hpush

/-- For an epimorphic degree-`d` monomial quotient on a projective line, projective rank
of its coefficient target and equality of the algebraic and geometric next-degree ranks
imply vanishing of the reconstructed relation-kernel `H¹`. -/
theorem
    subsingleton_H_one_reconstructedNextDegreeRelationKernel_of_projectiveOfRank_line_of_equal_rank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r d e k : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsProjectiveOfRank q E)
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule 1 (Spec (.of R)) r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) (d + 1))) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R))
            ((d + 1 : ℕ) : ℤ))))).H 1) := by
  have hK := twistedFreeMonomialQuotientMap_kernel_isFiniteLocallyFree
    1 (Spec (.of R)) r e u hE.isFiniteLocallyFree
  exact subsingleton_H_one_reconstructedNextDegreeRelationKernel_line_of_equal_rank
    R l r d e k he u hK hnext hpush

/-- Strong projective-line numerical endpoint: an epimorphic degree-`d` monomial quotient
with projective coefficient target is fully saturated whenever its algebraic and geometric
degree-`d+1` objects are projective of the same rank. -/
theorem
    twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_of_equal_rank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r d e k : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsProjectiveOfRank q E)
    (hnext : Modules.IsProjectiveOfRank k
      (twistedFreeNextDegreeModule 1 (Spec (.of R)) r e u))
    (hpush : Modules.IsProjectiveOfRank k
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) (d + 1))) :
    TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u := by
  have hK := twistedFreeMonomialQuotientMap_kernel_isFiniteLocallyFree
    1 (Spec (.of R)) r e u hE.isFiniteLocallyFree
  exact
    twistedFreeNextDegreeReconstructionSaturation_of_finiteLocallyFree_kernel_line_of_equal_rank
      R l r d e k he u hK hnext hpush

end AlgebraicGeometry.Scheme

end

end
