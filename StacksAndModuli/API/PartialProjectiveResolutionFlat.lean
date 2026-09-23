module

public import StacksAndModuli.API.FlatColimit
public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension

/-!
# Coefficient-flat syzygies in partial projective resolutions

Suppose `R → S` is flat and a partial projective resolution over `S` resolves a module
which is flat over `R`.  Every projective term in the resolution is then flat over `R`, so
successive applications of kernel-flatness show that the final syzygy is flat over `R`.

This is the coefficient-flatness induction used in the Noetherian proof of openness of the
relative flat locus.  The restricted `R`-module structures are written explicitly with
`Module.compHom`, allowing the result to be applied to resolutions initially constructed
only in the category of `S`-modules.

Main declaration:

* `Module.IsPartialProjectiveResolution.flat_final_of_flat`.
-/

@[expose] public section

universe u v w

namespace Module.IsPartialProjectiveResolution

set_option linter.style.haveILetI false

/-- The final syzygy of a partial projective resolution over a flat `R`-algebra is
`R`-flat when the resolved module is `R`-flat. -/
theorem flat_final_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    {e : ℕ} {M K : Type w}
    [AddCommGroup M] [Module S M]
    [AddCommGroup K] [Module S K]
    (hres : Module.IsPartialProjectiveResolution S e M K)
    (hM : @Module.Flat R M _ _ (Module.compHom M (algebraMap R S))) :
    @Module.Flat R K _ _ (Module.compHom K (algebraMap R S)) := by
  induction hres with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      letI : Module R M := Module.compHom M (algebraMap R S)
      letI : Module R K := Module.compHom K (algebraMap R S)
      letI : Module R F := Module.compHom F (algebraMap R S)
      letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
      letI : IsScalarTower R S K := IsScalarTower.of_compHom R S K
      letI : IsScalarTower R S F := IsScalarTower.of_compHom R S F
      letI : Module.Flat R M := hM
      letI : Module.Flat S F := Module.Flat.of_projective
      letI : Module.Flat R F := Module.Flat.trans R S F
      have hex : Function.Exact (i.restrictScalars R) (f.restrictScalars R) := by
        change Function.Exact i f
        exact LinearMap.exact_iff.mpr hexact.symm
      exact Module.Flat.of_shortExact (i.restrictScalars R) (f.restrictScalars R)
        hi hex hf
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact ih =>
      letI : Module R M := Module.compHom M (algebraMap R S)
      letI : Module R K' := Module.compHom K' (algebraMap R S)
      letI : Module R K := Module.compHom K (algebraMap R S)
      letI : Module R F := Module.compHom F (algebraMap R S)
      letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
      letI : IsScalarTower R S K' := IsScalarTower.of_compHom R S K'
      letI : IsScalarTower R S K := IsScalarTower.of_compHom R S K
      letI : IsScalarTower R S F := IsScalarTower.of_compHom R S F
      have hK' : Module.Flat R K' := ih hM
      letI : Module.Flat R K' := hK'
      letI : Module.Flat S F := Module.Flat.of_projective
      letI : Module.Flat R F := Module.Flat.trans R S F
      have hex : Function.Exact (i.restrictScalars R) (f.restrictScalars R) := by
        change Function.Exact i f
        exact LinearMap.exact_iff.mpr hexact.symm
      exact Module.Flat.of_shortExact (i.restrictScalars R) (f.restrictScalars R)
        hi hex hf

end Module.IsPartialProjectiveResolution
