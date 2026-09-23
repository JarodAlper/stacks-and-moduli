module

public import StacksAndModuli.API.InjectiveModuleNoetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Sheaves.Flasque

/-!
# `Ĩ` is flasque for `I` an injective module over a noetherian ring

**Hartshorne III.3.4.**  Let `R` be a noetherian commutative ring and let `I` be an injective
`R`-module.  Then the quasicoherent sheaf `Ĩ` on `Spec R` is flasque.

This is the engine behind the acyclicity of quasicoherent sheaves on affine schemes: an
injective resolution `0 → M → I⁰ → I¹ → ⋯` in `ModuleCat R` becomes, after applying `~`, a
resolution of `M̃` by flasque sheaves, whose global sections are the original complex.

The proof given here avoids Matlis theory and local cohomology.  It has two algebraic inputs,
both in `StacksAndModuli/API/InjectiveModuleNoetherian.lean`:

* `Module.Injective.surjective_of_isLocalizedModule_powers` — `I → I_f` is surjective, which
  is the statement for a *basic* open `D(f)`;
* `Module.Injective.exists_add_of_mul_smul_eq_zero` — the Artin–Rees splitting of an element
  killed by `𝔞 * 𝔟` into a piece killed by `𝔟` and a piece killed by a power of `𝔞`.

Every open of `Spec R` is a *finite* union of basic opens because `R` is noetherian, and the
splitting lemma is exactly what merges a lift over `D(f₁) ∪ ⋯ ∪ D(f_{r-1})` with a lift over
`D(f_r)`.  This is `surjective_toOpen`, from which flasqueness is immediate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry PrimeSpectrum

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The finite union of the basic opens attached to a finite subset of `R`. -/
noncomputable def finsetOpen (S : Finset R) : Opens (PrimeSpectrum R) :=
  ⨆ f ∈ S, basicOpen f

@[simp] lemma finsetOpen_empty : finsetOpen (R := R) ∅ = ⊥ := by simp [finsetOpen]

lemma basicOpen_le_finsetOpen {S : Finset R} {f : R} (hf : f ∈ S) :
    basicOpen f ≤ finsetOpen S :=
  le_trans (le_iSup (fun _ : f ∈ S => basicOpen f) hf)
    (le_iSup (fun g => ⨆ _ : g ∈ S, basicOpen g) f)

lemma finsetOpen_singleton (g : R) : finsetOpen (R := R) {g} = basicOpen g := by
  rw [finsetOpen]
  simp only [Finset.mem_singleton, iSup_iSup_eq_left]

lemma inf_finsetOpen [DecidableEq R] (g : R) (S : Finset R) :
    basicOpen g ⊓ finsetOpen S = finsetOpen (S.image (fun f => g * f)) := by
  refine le_antisymm ?_ ?_
  · rw [finsetOpen, inf_iSup_eq]
    refine iSup_le fun f => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun hf => ?_
    rw [← PrimeSpectrum.basicOpen_mul]
    exact basicOpen_le_finsetOpen (Finset.mem_image_of_mem _ hf)
  · rw [finsetOpen]
    refine iSup_le fun x => iSup_le fun hx => ?_
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hx
    rw [PrimeSpectrum.basicOpen_mul]
    exact le_inf inf_le_left (le_trans inf_le_right (basicOpen_le_finsetOpen hf))

lemma finsetOpen_insert [DecidableEq R] (g : R) (S : Finset R) :
    finsetOpen (insert g S) = basicOpen g ⊔ finsetOpen S := by
  rw [finsetOpen, finsetOpen, Finset.iSup_insert]

/-- Sections of a sheaf over the empty open are unique. -/
lemma subsingleton_sections_bot :
    Subsingleton ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊥)) := by
  constructor
  intro s t
  exact (modulesSpecToSheaf.obj (tilde M)).eq_of_locally_eq' (fun _ : PEmpty.{u+1} => ⊥) ⊥
    (fun i => i.elim) (by simp) s t (fun i => i.elim)

lemma finsetOpen_eq_iSup_coe (S : Finset R) :
    finsetOpen S = ⨆ f : (S : Set R), basicOpen (f : R) := by
  rw [finsetOpen, iSup_subtype']
  rfl

/-- Restriction along `V ≤ U` of a section coming from `M`. -/
lemma res_toOpen {U V : (Spec R).Opens} (h : V ≤ U) (x : M) :
    (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE h).op ((toOpen M U).hom x)
      = (toOpen M V).hom x :=
  ConcreteCategory.congr_hom (toOpen_res M U V (homOfLE h)) x

/-- Restrictions compose. -/
lemma res_res {U V W : (Spec R).Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : (modulesSpecToSheaf.obj (tilde M)).1.obj (op U)) :
    (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE h₂).op
        ((modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE h₁).op s)
      = (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A section of `M` dies in `M_f` exactly when a power of `f` kills it. -/
lemma toOpen_basicOpen_eq_zero_iff (f : R) (x : M) :
    (toOpen M (basicOpen f)).hom x = 0 ↔ ∃ n : ℕ, (f ^ n) • x = 0 := by
  rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers f)]
  constructor
  · rintro ⟨⟨s, n, rfl⟩, hs⟩
    exact ⟨n, hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩

variable [IsNoetherianRing R]

/-- **The basic-open case.**  `Γ(Spec R, Ĩ) = I ↠ I_f = Γ(D(f), Ĩ)`. -/
theorem surjective_toOpen_basicOpen (hM : Module.Baer R M) (f : R) :
    Function.Surjective (toOpen M (basicOpen f)).hom :=
  Module.Injective.surjective_of_isLocalizedModule_powers hM f (toOpen M (basicOpen f)).hom

/-- **Merging a lift over `D(g)` with a lift over a finite union.**  This is the inductive
step of Hartshorne III.3.4, and the only place the Artin–Rees splitting is used. -/
theorem surjective_toOpen_finsetOpen (hM : Module.Baer R M) (S : Finset R) :
    Function.Surjective (toOpen M (finsetOpen S)).hom := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hsub : Subsingleton
          ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (finsetOpen (∅ : Finset R)))) := by
        rw [finsetOpen_empty]
        exact subsingleton_sections_bot M
      exact fun s => ⟨0, hsub.elim _ _⟩
  | insert g S hg ih =>
      rw [finsetOpen_insert]
      intro s
      have hVU : basicOpen g ≤ basicOpen g ⊔ finsetOpen S := le_sup_left
      have hWU : finsetOpen S ≤ basicOpen g ⊔ finsetOpen S := le_sup_right
      obtain ⟨t, ht⟩ :=
        ih ((modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hWU).op s)
      obtain ⟨u, hu⟩ := surjective_toOpen_basicOpen M hM g
        ((modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hVU).op s)
      -- the difference of the two lifts dies on every overlap `D(g f)`, `f ∈ S`
      have hle₁ : ∀ f ∈ S, basicOpen (g * f) ≤ finsetOpen S := fun f hf =>
        le_trans (basicOpen_mul_le_right g f) (basicOpen_le_finsetOpen hf)
      have hle₂ : ∀ f : R, basicOpen (g * f) ≤ basicOpen g := fun f => basicOpen_mul_le_left g f
      have key : ∀ f ∈ S, (toOpen M (basicOpen (g * f))).hom (t - u) = 0 := by
        intro f hf
        rw [_root_.map_sub, ← res_toOpen M (hle₁ f hf), ← res_toOpen M (hle₂ f), ht, hu,
          res_res, res_res, sub_eq_zero]
      -- a uniform exponent
      have hex : ∀ f : (S : Set R), ∃ m : ℕ, ((g * (f : R)) ^ m) • (t - u) = 0 := fun f =>
        (toOpen_basicOpen_eq_zero_iff M _ _).mp (key f f.2)
      choose nn hnn using hex
      set N : ℕ := Finset.univ.sup nn with hN
      have hkill : ∀ f : (S : Set R), ((g * (f : R)) ^ N) • (t - u) = 0 := by
        intro f
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := nn) (Finset.mem_univ f))
        rw [hN, hc, pow_add, mul_comm ((g * (f : R)) ^ nn f), mul_smul, hnn f, smul_zero]
      -- split the difference into a piece supported on `V(g)` and one on `V(f), f ∈ S`
      obtain ⟨n, d₁, d₂, hd, hd₁, hd₂⟩ :=
        Module.Injective.exists_add_of_mul_smul_eq_zero hM
          (Ideal.span ((fun f : R => f ^ N) '' (S : Set R))) (Ideal.span {g ^ N}) (t - u)
          (by
            rw [Ideal.span_mul_span, Ideal.span_le]
            rintro _ ⟨_, ⟨f, hf, rfl⟩, _, rfl, rfl⟩
            simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, SetLike.mem_coe]
            rw [show f ^ N * g ^ N = (g * f) ^ N by rw [mul_pow, mul_comm]]
            exact hkill ⟨f, hf⟩)
      · have hz₁ : (toOpen M (basicOpen g)).hom d₁ = 0 :=
          (toOpen_basicOpen_eq_zero_iff M g d₁).mpr
            ⟨N, hd₁ (g ^ N) (Ideal.subset_span rfl)⟩
        have hz₂ : (toOpen M (finsetOpen S)).hom d₂ = 0 := by
          refine (modulesSpecToSheaf.obj (tilde M)).eq_of_locally_eq'
            (fun f : (S : Set R) => basicOpen (f : R)) (finsetOpen S)
            (fun f => homOfLE (basicOpen_le_finsetOpen f.2))
            (le_of_eq (finsetOpen_eq_iSup_coe S)) _ _ fun f => ?_
          rw [res_toOpen M (basicOpen_le_finsetOpen f.2), _root_.map_zero]
          have hmem : ((f : R) ^ N) ^ n ∈
              Ideal.span ((fun f : R => f ^ N) '' (S : Set R)) ^ n :=
            Ideal.pow_mem_pow
              (Ideal.subset_span (Set.mem_image_of_mem (fun f : R => f ^ N) f.2)) n
          have hpow : ((f : R) ^ (N * n)) • d₂ = 0 := by
            rw [pow_mul]; exact hd₂ _ hmem
          exact (toOpen_basicOpen_eq_zero_iff M (f : R) d₂).mpr ⟨N * n, hpow⟩
        have hsplit : t - d₂ = u + d₁ := by
          have ht' : t = d₁ + d₂ + u := sub_eq_iff_eq_add.mp hd
          rw [ht']
          abel
        refine ⟨t - d₂, ?_⟩
        have hV : (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hVU).op
              ((toOpen M (basicOpen g ⊔ finsetOpen S)).hom (t - d₂))
            = (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hVU).op s := by
          rw [res_toOpen M hVU, hsplit, _root_.map_add, hu, hz₁, add_zero]
        have hW : (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hWU).op
              ((toOpen M (basicOpen g ⊔ finsetOpen S)).hom (t - d₂))
            = (modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE hWU).op s := by
          rw [res_toOpen M hWU, _root_.map_sub, ht, hz₂, sub_zero]
        refine (modulesSpecToSheaf.obj (tilde M)).eq_of_locally_eq'
          (fun b : Bool => cond b (basicOpen g) (finsetOpen S)) (basicOpen g ⊔ finsetOpen S)
          (fun b => homOfLE (by cases b; exacts [hWU, hVU]))
          (by rw [iSup_bool_eq]; exact le_rfl) _ _ fun b => ?_
        cases b
        · exact hW
        · exact hV

omit [IsNoetherianRing R] in
/-- The underlying set of a finite union of basic opens. -/
lemma coe_finsetOpen (S : Finset R) :
    (finsetOpen S : Set (PrimeSpectrum R)) = (zeroLocus (S : Set R))ᶜ := by
  simp only [finsetOpen, TopologicalSpace.Opens.coe_iSup,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter₂, ← zeroLocus_iUnion₂]
  have hU : (⋃ i ∈ S, ({i} : Set R)) = (S : Set R) := by ext x; simp
  rw [hU]

/-- **Every open of a noetherian affine scheme is a finite union of basic opens.** -/
lemma exists_finsetOpen (U : Opens (PrimeSpectrum R)) :
    ∃ S : Finset R, finsetOpen S = U := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff (U : Set (PrimeSpectrum R))).mp U.2
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (R := R) (M := R) (Ideal.span s))
  refine ⟨T, TopologicalSpace.Opens.ext ?_⟩
  rw [coe_finsetOpen]
  have hT' : Ideal.span (T : Set R) = Ideal.span s := hT
  have : zeroLocus ((T : Set R)) = zeroLocus s := by
    rw [← zeroLocus_span (T : Set R), hT', zeroLocus_span]
  rw [this, ← hs, compl_compl]

/-- **Hartshorne III.3.4, section form.**  For `R` noetherian and `M` an injective (Baer)
`R`-module, `M = Γ(Spec R, M̃)` surjects onto `Γ(U, M̃)` for *every* open `U`. -/
theorem surjective_toOpen (hM : Module.Baer R M) (U : Opens (PrimeSpectrum R)) :
    Function.Surjective (toOpen M U).hom := by
  obtain ⟨S, rfl⟩ := exists_finsetOpen U
  exact surjective_toOpen_finsetOpen M hM S

/-- Every restriction map of `M̃` is surjective, for `M` injective over a noetherian ring. -/
theorem surjective_res (hM : Module.Baer R M) {U V : (Spec R).Opens} (h : V ≤ U) :
    Function.Surjective ((modulesSpecToSheaf.obj (tilde M)).1.map (homOfLE h).op) := by
  intro y
  obtain ⟨x, hx⟩ := surjective_toOpen M hM V y
  exact ⟨(toOpen M U).hom x, by rw [res_toOpen M h, hx]⟩

/-- **Hartshorne III.3.4.**  For `R` noetherian and `M` an injective `R`-module, the
quasicoherent sheaf `M̃` on `Spec R` is flasque. -/
theorem isFlasque_tilde (hM : Module.Baer R M) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_res M hM (i.unop.le)

end AlgebraicGeometry.tilde
