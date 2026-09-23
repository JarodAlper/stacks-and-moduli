module

public import StacksAndModuli.API.TildeInjectiveFlasque

/-!
# `M ↦ M̃` is an exact functor

`AlgebraicGeometry.tilde.functor R : ModuleCat R ⥤ (Spec R).Modules` is a fully faithful
left adjoint, so Mathlib already gives it every colimit; what is missing — and what an
injective resolution of a module needs in order to become a resolution of `M̃` by flasque
sheaves — is that it preserves *monomorphisms*.

The proof is the concrete one.  On a basic open `D(f)` the sections of `M̃` are `M_f`, and a
localization of an injective map is injective; the sheaf axiom then propagates injectivity
from the basic opens to every open.  Since a `Spec` of a noetherian ring has all of its opens
covered by finitely many basic opens (`AlgebraicGeometry.tilde.exists_finsetOpen`), the
propagation step is the two-line separation argument.

Combining "preserves monos" with "preserves cokernels" gives that `~` carries a short exact
sequence of modules to a short exact sequence of sheaves of modules.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry PrimeSpectrum Limits

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- The section map of `tilde.map ι` over an open `U`. -/
noncomputable abbrev mapApp (ι : M ⟶ N) (U : (Spec R).Opens) :
    (modulesSpecToSheaf.obj (tilde M)).1.obj (op U) ⟶
      (modulesSpecToSheaf.obj (tilde N)).1.obj (op U) :=
  (modulesSpecToSheaf.map (tilde.map ι)).1.app (op U)

lemma mapApp_toOpen (ι : M ⟶ N) (U : (Spec R).Opens) (m : M) :
    (mapApp ι U).hom ((toOpen M U).hom m) = (toOpen N U).hom (ι.hom m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app ι U) m

/-- **Localizing an injective map keeps it injective**, read on a basic open. -/
lemma injective_mapApp_basicOpen (ι : M ⟶ N) (hι : Function.Injective ι.hom) (f : R) :
    Function.Injective (mapApp ι (basicOpen f)).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨m, s⟩, hm⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (toOpen M (basicOpen f)).hom x
  obtain ⟨k, hk⟩ := s.2
  have hsx : (f ^ k) • x = (toOpen M (basicOpen f)).hom m := by
    show (f ^ k) • x = _
    rw [show f ^ k = (s : R) from hk]
    exact hm
  have h0 : (toOpen N (basicOpen f)).hom (ι.hom m) = 0 := by
    rw [← mapApp_toOpen ι _ m, ← hsx, map_smul, hx, smul_zero]
  obtain ⟨j, hj⟩ := (toOpen_basicOpen_eq_zero_iff N f (ι.hom m)).mp h0
  have hjm : (f ^ j) • m = 0 := by
    apply hι
    rw [_root_.map_zero, ← hj, _root_.map_smul]
  have hm0 : (toOpen M (basicOpen f)).hom m = 0 :=
    (toOpen_basicOpen_eq_zero_iff M f m).mpr ⟨j, hjm⟩
  have hunit := IsLocalizedModule.map_units (S := Submonoid.powers f)
    (toOpen M (basicOpen f)).hom ⟨f ^ k, k, rfl⟩
  rw [Module.End.isUnit_iff] at hunit
  refine hunit.1 ?_
  show (f ^ k) • x = (f ^ k) • (0 : _)
  rw [hsx, hm0, smul_zero]

variable [IsNoetherianRing R]

/-- **Injectivity propagates from the basic opens to every open**, by the sheaf axiom. -/
lemma injective_mapApp (ι : M ⟶ N) (hι : Function.Injective ι.hom) (U : (Spec R).Opens) :
    Function.Injective (mapApp ι U).hom := by
  obtain ⟨S, rfl⟩ := exists_finsetOpen U
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hnat : ∀ (V W : (Spec R).Opens) (h : W ≤ V)
      (y : (modulesSpecToSheaf.obj (tilde M)).1.obj (op V)),
      (mapApp ι W).hom ((modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE h).op y)
        = (modulesSpecToSheaf.obj (tilde N)).1.map (homOfLE h).op ((mapApp ι V).hom y) := by
    intro V W h y
    simp only []
    exact ConcreteCategory.congr_hom
      ((modulesSpecToSheaf.map (tilde.map ι)).1.naturality (homOfLE h).op) y
  refine (modulesSpecToSheaf.obj (tilde M)).eq_of_locally_eq'
    (fun f : (S : Set R) => basicOpen (f : R)) (finsetOpen S)
    (fun f => homOfLE (basicOpen_le_finsetOpen f.2))
    (le_of_eq (finsetOpen_eq_iSup_coe S)) _ _ fun f => ?_
  rw [_root_.map_zero]
  refine injective_mapApp_basicOpen ι hι (f : R) ?_
  rw [hnat _ _ (basicOpen_le_finsetOpen f.2), hx, _root_.map_zero, _root_.map_zero]

/-- **`~` preserves monomorphisms.**  On a basic open it is the localization of an injective
map, which is injective; the sheaf axiom does the rest. -/
theorem mono_tilde_map (ι : M ⟶ N) (hι : Function.Injective ι.hom) :
    Mono (tilde.map ι) := by
  refine modulesSpecToSheaf.mono_of_mono_map ⟨fun {Z} g h hgh => ?_⟩
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  have h1 := congrArg (fun (t : Z ⟶ _) => t.1.app U) hgh
  have : Mono ((modulesSpecToSheaf.map (tilde.map ι)).1.app U) := by
    rw [ModuleCat.mono_iff_injective]
    exact injective_mapApp ι hι U.unop
  exact (cancel_mono _).mp h1

omit [IsNoetherianRing R] in
/-- `Γ(Spec R, Ñ) = N`, so a surjection of modules stays surjective on global sections. -/
lemma surjective_mapApp_top (π : M ⟶ N) (hπ : Function.Surjective π.hom) :
    Function.Surjective (mapApp π ⊤).hom := by
  intro y
  have hiso : Function.Surjective (toOpen N ⊤).hom := by
    have := isIso_toOpen_top (M := N)
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨q, rfl⟩ := hiso y
  obtain ⟨p, rfl⟩ := hπ q
  exact ⟨(toOpen M ⊤).hom p, mapApp_toOpen π ⊤ p⟩

omit [IsNoetherianRing R] in
/-- Localization is right exact, so a surjection of modules stays surjective on the sections
over a basic open. -/
lemma surjective_mapApp_basicOpen (π : M ⟶ N) (hπ : Function.Surjective π.hom) (f : R) :
    Function.Surjective (mapApp π (basicOpen f)).hom := by
  intro y
  obtain ⟨⟨q, s⟩, hq⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (toOpen N (basicOpen f)).hom y
  obtain ⟨p, rfl⟩ := hπ q
  have hunitM := IsLocalizedModule.map_units (S := Submonoid.powers f)
    (toOpen M (basicOpen f)).hom s
  have hunitN := IsLocalizedModule.map_units (S := Submonoid.powers f)
    (toOpen N (basicOpen f)).hom s
  rw [Module.End.isUnit_iff] at hunitM hunitN
  obtain ⟨x, hx⟩ := hunitM.2 ((toOpen M (basicOpen f)).hom p)
  refine ⟨x, hunitN.1 ?_⟩
  show (s : R) • (mapApp π (basicOpen f)).hom x = (s : R) • y
  rw [← map_smul]
  show (mapApp π (basicOpen f)).hom ((s : R) • x) = (s : R) • y
  rw [show ((s : R) • x) = (toOpen M (basicOpen f)).hom p from hx, mapApp_toOpen]
  exact hq.symm

/-- **`~` is exact.**  It preserves monomorphisms by `mono_tilde_map` and cokernels because it
is a left adjoint, and those two together carry short exact sequences to short exact
sequences. -/
theorem shortExact_tilde_map {T : ShortComplex (ModuleCat.{u} R)} (hT : T.ShortExact) :
    (T.map (tilde.functor R)).ShortExact := by
  have hm : Mono ((tilde.functor R).map T.f) :=
    mono_tilde_map T.f ((ModuleCat.mono_iff_injective _).mp hT.mono_f)
  have hpe : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  have he : Epi ((tilde.functor R).map T.g) := by
    have := hT.epi_g
    exact hpe.preserves T.g
  have hpc : PreservesColimit (parallelPair T.f 0) (tilde.functor R) := inferInstance
  exact { exact := hT.exact.map_of_epi_of_preservesCokernel (tilde.functor R) hT.epi_g hpc
          mono_f := hm
          epi_g := he }

end AlgebraicGeometry.tilde
