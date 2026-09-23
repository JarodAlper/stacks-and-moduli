module

public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»

/-!
# Splitting quasicoherent epimorphisms on affine schemes

An epimorphism of quasicoherent module sheaves onto a module whose global sections are
finite projective splits on an arbitrary affine scheme.  The proof transports the
epimorphism to the canonical affine spectrum, uses the tilde--global-sections equivalence
there, and transports the resulting section back.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- An epimorphism of quasicoherent modules on an affine scheme splits if the global
sections of its target form a finite projective module. -/
theorem isSplitEpi_of_epi_of_projective_sections_of_isAffine
    {X : Scheme.{u}} [IsAffine X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) [Epi p]
    (hfin : Module.Finite Γ(X, ⊤) Γ(G, ⊤))
    (hproj : Module.Projective Γ(X, ⊤) Γ(G, ⊤)) : IsSplitEpi p := by
  let e := X.isoSpec
  let E := pullback e.inv
  let H := pullback e.hom
  let q : E.obj F ⟶ E.obj G := E.map p
  letI : (E.obj F).IsQuasicoherent := by
    let eF := (restrictFunctorIsoPullback e.inv).app F
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      eF inferInstance
  letI : (E.obj G).IsQuasicoherent := by
    let eG := (restrictFunctorIsoPullback e.inv).app G
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      eG inferInstance
  letI : Epi q := inferInstance
  have him : e.inv ''ᵁ (⊤ : (Spec (.of Γ(X, ⊤))).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hGtop := pullback_openImmersion_sections_finite_projective
    e.inv G ⊤ (by rw [him]; exact hfin) (by rw [him]; exact hproj)
  have hΓ := moduleSpecΓFunctor_finite_projective_of_top (E.obj G)
    hGtop.1 hGtop.2
  letI : Module.Projective Γ(X, ⊤) (moduleSpecΓFunctor.obj (E.obj G)) := hΓ.2
  have hsplitq : IsSplitEpi q :=
    isSplitEpi_of_epi_of_projective_globalSections q
  letI : IsSplitEpi q := hsplitq
  let i := pullbackIsoSpecInvHomIso X
  exact IsSplitEpi.mk' {
    section_ := i.inv.app G ≫ H.map (section_ q) ≫ i.hom.app F
    id := by
      have hn := (i.hom.naturality p).symm
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      simp only [Category.assoc]
      rw [hn]
      change i.inv.app G ≫ H.map (section_ q) ≫ H.map q ≫ i.hom.app G = 𝟙 G
      rw [← H.map_comp_assoc, IsSplitEpi.id]
      simp }

end AlgebraicGeometry.Scheme.Modules

end

end
