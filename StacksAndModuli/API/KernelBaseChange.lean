module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Base change of kernels and generalized inverses

Supporting API with no Stacks Project counterpart of its own, used by the formalization of
`prop:linear-algebra` in §A.6 (Cohomology and Base Change).

The proposition characterises when a map of vector bundles has locally constant rank. Its
affine-local content is a comparison between the kernel of a linear map and the kernel of its
base change, together with the equivalence between "the comparison is surjective at a point"
and "the map admits a generalized (inner) inverse near that point". A linear map `f` has an
**inner inverse** `g` when `f ∘ g ∘ f = f`; over a ring this is the basis-free form of the
block normal form `(x₁,…,x_e) ↦ (x₁,…,x_r,0,…,0)` in condition (2) of the proposition.

Mathlib has none of this comparison API. It does have the ingredients: `LinearMap.baseChange`,
`Module.Flat`, `Module.free_of_flat_of_isLocalRing`, and `Ideal.ResidueField`.

Main declarations:
- `PrimeSpectrum.residueField`: the residue field at a point of `Spec R`;
- `LinearMap.kerBaseChangeHom`: the canonical map `S ⊗[R] ker f → ker (S ⊗[R] f)`;
- the inner-inverse lemmas relating its surjectivity to local normal forms.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u v w

/-- The residue field of `R` at a point of `Spec R`. -/
abbrev PrimeSpectrum.residueField {R : Type u} [CommRing R] (p : PrimeSpectrum R) : Type u :=
  p.asIdeal.ResidueField

namespace LinearMap

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Base change kills the inclusion of the kernel: `(S ⊗ f) ∘ (S ⊗ ker f ↪ S ⊗ M) = 0`. -/
theorem baseChange_comp_ker_subtype (f : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S] :
    (f.baseChange S) ∘ₗ (LinearMap.baseChange S (LinearMap.ker f).subtype) = 0 := by
  rw [← LinearMap.baseChange_comp]
  convert LinearMap.baseChange_zero (R := R) (A := S) (M := LinearMap.ker f) (N := N)
  ext x
  simpa using x.2

/-- Background definition for Proposition A.6.6: the canonical comparison map
`S ⊗[R] ker f → ker (S ⊗[R] f)`. Surjectivity after passing to a residue field is
condition (3) of that proposition. -/
noncomputable def kerBaseChangeHom (f : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S] :
    S ⊗[R] (LinearMap.ker f) →ₗ[S] LinearMap.ker (f.baseChange S) :=
  LinearMap.codRestrict _ (LinearMap.baseChange S (LinearMap.ker f).subtype) fun x ↦ by
    have := congrArg (fun l ↦ l x) (baseChange_comp_ker_subtype f S)
    simpa using this

/-- A map admitting an inner inverse has kernel commuting with every base change.

Proof route: if `f ∘ g ∘ f = f` then `ker f` is a direct summand of `M`, split off by
`1 - g ∘ f`, and base change preserves direct sums. -/
theorem kerBaseChangeHom_bijective_of_innerInverse {f : M →ₗ[R] N} (S : Type*) [CommRing S]
    [Algebra R S] (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f) :
    Function.Bijective (f.kerBaseChangeHom S) := by
  set p : M →ₗ[R] M := g.comp f with hp
  have hfp : ∀ x, f (((LinearMap.id : M →ₗ[R] M) - p) x) = 0 := by
    intro x
    have hx := congrArg (fun l ↦ l x) h
    simp only [LinearMap.comp_apply] at hx
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [sub_eq_zero]
    exact hx.symm
  let r : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict _ ((LinearMap.id : M →ₗ[R] M) - p) fun x ↦ LinearMap.mem_ker.mpr (hfp x)
  have hri : r.comp (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    show ((LinearMap.id : M →ₗ[R] M) - p) x.1 = x.1
    have hpx : p x.1 = 0 := by
      simp [p, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2]
    simp [hpx]
  have hir : (LinearMap.ker f).subtype.comp r = (LinearMap.id : M →ₗ[R] M) - p := rfl
  constructor
  · intro t t' htt
    have h1 : (LinearMap.baseChange S (LinearMap.ker f).subtype) t =
        (LinearMap.baseChange S (LinearMap.ker f).subtype) t' := congrArg Subtype.val htt
    have h2 := congrArg (LinearMap.baseChange S r) h1
    have h3 : ∀ u : S ⊗[R] (LinearMap.ker f),
        (LinearMap.baseChange S r) ((LinearMap.baseChange S (LinearMap.ker f).subtype) u)
          = u := by
      intro u
      have := congrArg (fun l ↦ l u)
        ((LinearMap.baseChange_comp (LinearMap.ker f).subtype r
          (A := S)).symm.trans (by rw [hri, LinearMap.baseChange_id]))
      simpa using this
    rw [h3 t, h3 t'] at h2
    exact h2
  · rintro ⟨y, hy⟩
    refine ⟨LinearMap.baseChange S r y, ?_⟩
    apply Subtype.ext
    show (LinearMap.baseChange S (LinearMap.ker f).subtype)
      ((LinearMap.baseChange S r) y) = y
    have h4 := LinearMap.congr_fun
      (LinearMap.baseChange_comp r (LinearMap.ker f).subtype (A := S)).symm y
    have hpy : (LinearMap.baseChange S p) y = 0 := by
      rw [hp, LinearMap.baseChange_comp]
      have hy0 : (f.baseChange S) y = 0 := LinearMap.mem_ker.mp hy
      simp [LinearMap.comp_apply, hy0]
    calc (LinearMap.baseChange S (LinearMap.ker f).subtype)
          ((LinearMap.baseChange S r) y)
        = (LinearMap.baseChange S ((LinearMap.ker f).subtype ∘ₗ r)) y := h4
      _ = y := by
          rw [hir, LinearMap.baseChange_sub, LinearMap.baseChange_id,
            LinearMap.sub_apply, hpy, sub_zero, LinearMap.id_apply]

/-- Over a local ring, surjectivity of the kernel comparison at the residue field yields an
inner inverse.

Proof route: Nakayama. Surjectivity at the residue field means `ker f ⊗ κ → ker (f ⊗ κ)` is
onto, so a κ-basis of `ker (f ⊗ κ)` lifts to `ker f`; since `N` is free and finite, complete to
a splitting of `f` and lift it back by Nakayama. -/
theorem exists_innerInverse_of_kerBaseChangeHom_residueField_surjective [IsLocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (hker : Function.Surjective (f.kerBaseChangeHom (IsLocalRing.ResidueField R))) :
    ∃ g : N →ₗ[R] M, f.comp (g.comp f) = f := by
  classical
  -- the induced map out of the quotient by the kernel
  set K := LinearMap.ker f with hK
  set f' : (M ⧸ K) →ₗ[R] N := K.liftQ f (le_of_eq hK) with hf'
  -- the residue-field fibre of `f'` is injective, by surjectivity of the comparison
  have hinj : Function.Injective (f'.lTensor (IsLocalRing.ResidueField R)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (IsLocalRing.ResidueField R)
      (Submodule.mkQ_surjective K) z
    have hcomp : (f'.lTensor (IsLocalRing.ResidueField R)) ∘ₗ
        (K.mkQ.lTensor (IsLocalRing.ResidueField R)) =
        f.lTensor (IsLocalRing.ResidueField R) := by
      rw [← LinearMap.lTensor_comp, K.liftQ_mkQ f (le_of_eq hK)]
    have hw : (f.baseChange (IsLocalRing.ResidueField R)) w = 0 := by
      rw [LinearMap.baseChange_eq_ltensor]
      have := congrArg (fun l ↦ l w) hcomp
      simp only [LinearMap.comp_apply] at this
      rw [← this]
      exact LinearMap.mem_ker.mp hz
    obtain ⟨u, hu⟩ := hker ⟨w, LinearMap.mem_ker.mpr hw⟩
    have huval : (LinearMap.baseChange (IsLocalRing.ResidueField R) K.subtype) u = w :=
      congrArg Subtype.val hu
    have hzero : K.mkQ ∘ₗ K.subtype = 0 := by
      ext x
      simpa [Submodule.Quotient.mk_eq_zero] using x.2
    have huval' : (K.subtype.lTensor (IsLocalRing.ResidueField R)) u = w := by
      rw [← LinearMap.baseChange_eq_ltensor]
      exact huval
    calc (K.mkQ.lTensor (IsLocalRing.ResidueField R)) w
        = (K.mkQ.lTensor (IsLocalRing.ResidueField R))
            ((K.subtype.lTensor (IsLocalRing.ResidueField R)) u) := by
          rw [huval']
      _ = ((K.mkQ ∘ₗ K.subtype).lTensor (IsLocalRing.ResidueField R)) u := by
          rw [LinearMap.lTensor_comp]; rfl
      _ = 0 := by rw [hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  -- split the injection using freeness of `N`
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f').mpr hinj
  -- lift the retraction through the quotient using projectivity of `N`
  obtain ⟨g, hg⟩ := Module.projective_lifting_property K.mkQ l' (Submodule.mkQ_surjective K)
  refine ⟨g, ?_⟩
  ext m
  have h1 : K.mkQ (g (f m)) = K.mkQ m := by
    have hgm := congrArg (fun l ↦ l (f m)) hg
    simp only [LinearMap.comp_apply] at hgm
    have hfm : f m = f' (K.mkQ m) := (Submodule.liftQ_apply K f _).symm
    have hlm := congrArg (fun l ↦ l (K.mkQ m)) hl'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hlm
    rw [hgm, hfm, hlm]
  have h3 : g (f m) - m ∈ K := by
    have h1' : (Submodule.Quotient.mk (g (f m)) : M ⧸ K) = Submodule.Quotient.mk m := h1
    rw [← Submodule.Quotient.mk_eq_zero K, Submodule.Quotient.mk_sub, h1', sub_self]
  have h4 : f (g (f m)) - f m = 0 := by
    have := LinearMap.mem_ker.mp h3
    rw [map_sub] at this
    exact this
  simp only [LinearMap.comp_apply]
  exact sub_eq_zero.mp h4

/-- The kernel comparison for a tower `R → S → T` with `S` flat over `R`: surjectivity for
`R → T` gives surjectivity for the `S`-linear map `S ⊗ f` at `T`.

Proof route: flatness of `S` over `R` makes `S ⊗ ker f = ker (S ⊗ f)`, so the two comparison
maps for `T` agree under the associativity isomorphism `T ⊗_S (S ⊗_R -) ≅ T ⊗_R -`. -/
theorem kerBaseChangeHom_surjective_of_tower_of_flat {f : M →ₗ[R] N} (S : Type*) [CommRing S]
    [Algebra R S] [Module.Flat R S] (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    (hker : Function.Surjective (f.kerBaseChangeHom T)) :
    Function.Surjective ((f.baseChange S).kerBaseChangeHom T) := by
  classical
  set eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M with heM
  set eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N with heN
  set eK := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T
    (LinearMap.ker f) with heK
  -- the two base changes agree through the cancellation isomorphisms
  have key : ((f.baseChange S).baseChange T) =
      eN.symm.toLinearMap ∘ₗ ((f.baseChange T) ∘ₗ eM.toLinearMap) := by
    ext x
    simp [eM, eN]
  have key2 : (((LinearMap.ker f).subtype.baseChange S).baseChange T) =
      eM.symm.toLinearMap ∘ₗ
        (((LinearMap.ker f).subtype.baseChange T) ∘ₗ eK.toLinearMap) := by
    ext x
    simp [eM, eK]
  rintro ⟨y, hy⟩
  -- transport the kernel element along the cancellation isomorphism
  have hy' : (f.baseChange T) (eM y) = 0 := by
    have h0 := LinearMap.mem_ker.mp hy
    rw [key] at h0
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h0
    have := congrArg eN h0
    simpa using this
  obtain ⟨x, hx⟩ := hker ⟨eM y, LinearMap.mem_ker.mpr hy'⟩
  have hxval : (LinearMap.baseChange T (LinearMap.ker f).subtype) x = eM y :=
    congrArg Subtype.val hx
  -- the preimage: base-change the `S`-level comparison and cancel
  refine ⟨((f.kerBaseChangeHom S).baseChange T) (eK.symm x), ?_⟩
  apply Subtype.ext
  show (LinearMap.baseChange T (LinearMap.ker (f.baseChange S)).subtype)
    (((f.kerBaseChangeHom S).baseChange T) (eK.symm x)) = y
  have hsub : (LinearMap.ker (f.baseChange S)).subtype ∘ₗ f.kerBaseChangeHom S =
      LinearMap.baseChange S (LinearMap.ker f).subtype := rfl
  have hstep1 : (LinearMap.baseChange T (LinearMap.ker (f.baseChange S)).subtype) ∘ₗ
      ((f.kerBaseChangeHom S).baseChange T) =
      (((LinearMap.ker f).subtype.baseChange S).baseChange T) := by
    rw [← LinearMap.baseChange_comp, hsub]
  have happ := LinearMap.congr_fun hstep1 (eK.symm x)
  simp only [LinearMap.comp_apply] at happ
  rw [happ]
  have happ2 := LinearMap.congr_fun key2 (eK.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at happ2
  rw [happ2, LinearEquiv.apply_symm_apply, hxval]
  exact eM.symm_apply_apply y

/-- Clearing denominators: an inner inverse for `f` after localizing at `p` comes from a
"scaled" inner inverse `f ∘ h ∘ f = a • f` with `a ∉ p` over `R` itself.

Proof route: `M` and `N` are finite, so the finitely many denominators appearing in `g` can be
cleared simultaneously by a single `a ∉ p`. -/
theorem exists_scaled_innerInverse_of_innerInverse_baseChange_atPrime
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (p : PrimeSpectrum R)
    (g : (Localization.AtPrime p.asIdeal) ⊗[R] N →ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⊗[R] M)
    (hg : (f.baseChange (Localization.AtPrime p.asIdeal)).comp
        (g.comp (f.baseChange (Localization.AtPrime p.asIdeal))) =
      f.baseChange (Localization.AtPrime p.asIdeal)) :
    ∃ (a : R) (_ : a ∉ p.asIdeal) (h : N →ₗ[R] M), f.comp (h.comp f) = a • f := by
  classical
  set A := Localization.AtPrime p.asIdeal with hA
  haveI : Module.FinitePresentation R N :=
    Module.finitePresentation_of_projective R N
  -- the canonical localized-module structures on the base-changed modules
  set mkM : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1 with hmkM
  set mkN : N →ₗ[R] A ⊗[R] N := TensorProduct.mk R A N 1 with hmkN
  haveI hlM : IsLocalizedModule p.asIdeal.primeCompl mkM :=
    (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl A mkM).mpr
      (TensorProduct.isBaseChange R M A)
  haveI hlN : IsLocalizedModule p.asIdeal.primeCompl mkN :=
    (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl A mkN).mpr
      (TensorProduct.isBaseChange R N A)
  -- the localized Hom-module: clear denominators of `g`
  haveI := Module.FinitePresentation.isLocalizedModule_mapExtendScalars
    p.asIdeal.primeCompl mkN mkM A
  obtain ⟨⟨h₀, s⟩, hs⟩ := IsLocalizedModule.surj p.asIdeal.primeCompl
    (IsLocalizedModule.mapExtendScalars p.asIdeal.primeCompl mkN mkM A) g
  -- on each element of `M`, the two candidate maps agree after localization
  have himg : ∀ m : M, mkN ((f.comp (h₀.comp f)) m) = mkN (((s : R) • f) m) := by
    intro m
    have hfm : (f.baseChange A) (mkM m) = mkN (f m) := by simp [hmkM, hmkN]
    have hhm : (f.baseChange A) (mkM (h₀ (f m))) = mkN (f (h₀ (f m))) := by
      simp [hmkM, hmkN]
    have hsg := LinearMap.congr_fun hs (mkN (f m))
    rw [Submonoid.smul_def] at hsg
    have hext : (IsLocalizedModule.mapExtendScalars p.asIdeal.primeCompl mkN mkM A)
        h₀ (mkN (f m)) = mkM (h₀ (f m)) := by simp
    rw [hext] at hsg
    have hsg2 : (s : R) • g (mkN (f m)) = mkM (h₀ (f m)) := hsg
    have happ := congrArg (f.baseChange A) hsg2
    rw [LinearMap.map_smul_of_tower, hhm] at happ
    have hgm := LinearMap.congr_fun hg (mkM m)
    simp only [LinearMap.comp_apply] at hgm
    rw [hfm] at hgm
    rw [hgm] at happ
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [map_smul]
    exact happ.symm
  -- clear the denominators over the finitely many generators of `M`
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose c hc using fun i ↦ IsLocalizedModule.exists_of_eq
    (S := p.asIdeal.primeCompl) (f := mkN) (himg (v i))
  set ctot : p.asIdeal.primeCompl := ∏ i, c i with hctot
  refine ⟨(ctot : R) * (s : R), fun hmem ↦ (ctot * s).2 hmem, (ctot : R) • h₀, ?_⟩
  apply LinearMap.ext_on hv
  rintro x ⟨i, rfl⟩
  have hcc : ∃ d : p.asIdeal.primeCompl, (d : R) * (c i : R) = (ctot : R) := by
    refine ⟨∏ j ∈ Finset.univ.erase i, c j, ?_⟩
    rw [hctot]
    push_cast
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  obtain ⟨d, hd⟩ := hcc
  have hci' : (c i : R) • ((f.comp (h₀.comp f)) (v i)) =
      (c i : R) • (((s : R) • f) (v i)) := by
    have := hc i
    rwa [Submonoid.smul_def, Submonoid.smul_def] at this
  have hmul := congrArg (fun z ↦ (d : R) • z) hci'
  simp only [smul_smul, hd] at hmul
  show f (((ctot : R) • h₀) (f (v i))) = (((ctot : R) * (s : R)) • f) (v i)
  rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, ← smul_smul]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using hmul

/-- On the basic open `D(a)` the scalar `a` is invertible, so a scaled inner inverse becomes an
honest inner inverse after base change to `Localization.Away a`. -/
theorem exists_innerInverse_baseChange_away_of_scaled_innerInverse (f : M →ₗ[R] N) (a : R)
    (h : N →ₗ[R] M) (hh : f.comp (h.comp f) = a • f) :
    ∃ g : (Localization.Away a) ⊗[R] N →ₗ[Localization.Away a] (Localization.Away a) ⊗[R] M,
      (f.baseChange (Localization.Away a)).comp
          (g.comp (f.baseChange (Localization.Away a))) =
        f.baseChange (Localization.Away a) := by
  set A := Localization.Away a with hA
  refine ⟨IsLocalization.Away.invSelf (S := A) a • h.baseChange A, ?_⟩
  have hb := congrArg (fun l ↦ LinearMap.baseChange A l) hh
  simp only [LinearMap.baseChange_comp, LinearMap.baseChange_smul] at hb
  calc (f.baseChange A).comp
        ((IsLocalization.Away.invSelf (S := A) a • h.baseChange A).comp (f.baseChange A))
      = IsLocalization.Away.invSelf (S := A) a •
          ((f.baseChange A).comp ((h.baseChange A).comp (f.baseChange A))) := by
        rw [LinearMap.smul_comp, LinearMap.comp_smul]
    _ = IsLocalization.Away.invSelf (S := A) a • (a • f.baseChange A) := by rw [hb]
    _ = f.baseChange A := by
        rw [← algebraMap_smul A a (f.baseChange A), smul_smul,
          show IsLocalization.Away.invSelf (S := A) a * algebraMap R A a = 1 from
            (mul_comm _ _).trans (IsLocalization.Away.mul_invSelf a), one_smul]

end LinearMap
