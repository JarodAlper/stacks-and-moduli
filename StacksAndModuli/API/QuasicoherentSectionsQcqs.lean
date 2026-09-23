module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»
public import StacksAndModuli.API.OpenCoverQuotient
public import StacksAndModuli.API.GlobalSectionsOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasicoherent sections on qcqs basic opens

For a quasicoherent module sheaf `N` on a scheme and a section `f` of the structure
sheaf over a compact quasi-separated open `U`, restriction from `U` to `D(f)` is module
localization: a section over `D(f)` extends after multiplication by a power of `f`, and
a section over `U` vanishing on `D(f)` is killed by a power of `f`.

This is the module-sheaf analogue of Mathlib's qcqs lemma
`isLocalization_basicOpen_of_qcqs` for the structure sheaf.  It is the generic-fibre
base-change input for global sections in the DVR argument for projectivity of Quot.

Main declarations:

* `Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`;
* `Scheme.Modules.exists_pow_smul_res_of_basicOpen_of_qcqs`;
* `Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap_of_qcqs`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- Restricting a module section successively through two inclusions is the same as
restricting it through their composite. -/
lemma map_res_res {X : Scheme.{u}} (N : X.Modules)
    {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (hUW : U ≤ W)
    (x : Γ(N, W)) :
    (N.presheaf.map (homOfLE hUV).op).hom
        ((N.presheaf.map (homOfLE hVW).op).hom x) =
      (N.presheaf.map (homOfLE hUW).op).hom x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1

/-- Restricting a structure-sheaf section successively through two inclusions is the
same as restricting it through their composite. -/
lemma ringMap_res_res {X : Scheme.{u}}
    {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (hUW : U ≤ W)
    (x : Γ(X, W)) :
    (X.presheaf.map (homOfLE hUV).op).hom
        ((X.presheaf.map (homOfLE hVW).op).hom x) =
      (X.presheaf.map (homOfLE hUW).op).hom x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1

/-- Two compatible module sections glue over the union. -/
lemma exists_glue_sup {X : Scheme.{u}} (N : X.Modules)
    {U V : X.Opens} (xU : Γ(N, U)) (xV : Γ(N, V))
    (h : (N.presheaf.map (homOfLE inf_le_left).op).hom xU =
      (N.presheaf.map (homOfLE inf_le_right).op).hom xV) :
    ∃ x : Γ(N, U ⊔ V),
      (N.presheaf.map (homOfLE le_sup_left).op).hom x = xU ∧
      (N.presheaf.map (homOfLE le_sup_right).op).hom x = xV := by
  let W : Bool → X.Opens
    | false => U
    | true => V
  let s : ∀ b : Bool, Γ(N, W b)
    | false => xU
    | true => xV
  have hcompat : TopCat.Presheaf.IsCompatible N.presheaf W s := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact h
    · have h' := congrArg
        ((N.presheaf.map (eqToHom (inf_comm V U)).op).hom) h.symm
      have hL : eqToHom (inf_comm V U) ≫
          (homOfLE (inf_le_right : U ⊓ V ≤ V)) =
          (homOfLE (inf_le_left : V ⊓ U ≤ V)) := Subsingleton.elim _ _
      have hR : eqToHom (inf_comm V U) ≫
          (homOfLE (inf_le_left : U ⊓ V ≤ U)) =
          (homOfLE (inf_le_right : V ⊓ U ≤ U)) := Subsingleton.elim _ _
      have hLL : (homOfLE (inf_le_left : V ⊓ U ≤ V)) =
          Opens.infLELeft V U := Subsingleton.elim _ _
      have hRR : (homOfLE (inf_le_right : V ⊓ U ≤ U)) =
          Opens.infLERight V U := Subsingleton.elim _ _
      simpa only [W, s, ← CategoryTheory.comp_apply, ← Functor.map_comp,
        ← op_comp, hL, hR, hLL, hRR] using h'
    · rfl
  have hcover : U ⊔ V ≤ iSup W := by
    rw [sup_le_iff]
    constructor
    · exact le_iSup_of_le false (by simp [W])
    · exact le_iSup_of_le true (by simp [W])
  obtain ⟨x, hx, -⟩ := (abSheaf N).existsUnique_gluing'
    W (U ⊔ V) (fun b => homOfLE (by cases b <;> simp [W])) hcover s hcompat
  refine ⟨x, ?_, ?_⟩
  · simpa [W, s] using hx false
  · simpa [W, s] using hx true

/-- Compact-open annihilation for a quasicoherent module sheaf. -/
theorem exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    {X : Scheme.{u}} (N : X.Modules) [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (r : Γ(X, U)) (z : Γ(N, U))
    (hz : (N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom z = 0) :
    ∃ n : ℕ, r ^ n • z = 0 := by
  classical
  obtain ⟨s, hs, e⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1
    simpa using e
  have hle (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have hzlocal (i : s) :
      (N.presheaf.map
        (homOfLE (X.basicOpen_le
          ((X.presheaf.map (homOfLE (hle i)).op).hom r))).op).hom
          ((N.presheaf.map (homOfLE (hle i)).op).hom z) = 0 := by
    have hbasic : X.basicOpen
        ((X.presheaf.map (homOfLE (hle i)).op).hom r) =
        X.basicOpen r ⊓ i.1.1 := by
      rw [Scheme.basicOpen_res]
      exact inf_comm _ _
    have hcomp :
        N.presheaf.map (homOfLE (hle i)).op ≫
          N.presheaf.map (homOfLE
            (X.basicOpen_le
              ((X.presheaf.map (homOfLE (hle i)).op).hom r))).op =
        N.presheaf.map (homOfLE (X.basicOpen_le r)).op ≫
          N.presheaf.map (homOfLE (by
            rw [hbasic]
            exact inf_le_left)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    rw [← CategoryTheory.comp_apply, hcomp, CategoryTheory.comp_apply, hz, map_zero]
  have H := fun i : s =>
    Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
      N i.1.2
        ((X.presheaf.map (homOfLE (hle i)).op).hom r)
        ((N.presheaf.map (homOfLE (hle i)).op).hom z) (hzlocal i)
  choose n hn using H
  letI : Finite s := hs.to_subtype
  letI : Fintype s := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, ?_⟩
  apply (abSheaf N).eq_of_locally_eq'
    (fun i : s => (i : X.Opens)) U (fun i => homOfLE (hle i))
      (by rw [e]) _ 0
  intro i
  rw [map_zero]
  change (N.presheaf.map (homOfLE (hle i)).op).hom
      (r ^ Finset.univ.sup n • z) = 0
  rw [Scheme.Modules.map_smul, map_pow]
  have hni : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  rw [← tsub_add_cancel_of_le hni, pow_add, mul_smul, hn i, smul_zero]

set_option maxHeartbeats 800000 in
/-- Clearing denominators for a quasicoherent module sheaf on a qcqs open. -/
theorem exists_pow_smul_res_of_basicOpen_of_qcqs
    {X : Scheme.{u}} (N : X.Modules) [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (r : Γ(X, U)) (z : Γ(N, X.basicOpen r)) :
    ∃ (z₀ : Γ(N, U)) (n : ℕ),
      (N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom z₀ =
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r ^ n • z := by
  classical
  revert hU' r z
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ r z
    refine ⟨0, 0, ?_⟩
    apply (abSheaf N).eq_of_locally_eq'
      (fun i : PEmpty.{u + 1} => ⊥) (X.basicOpen r)
      (fun i => i.elim) (by
        simpa only [iSup_of_empty] using X.basicOpen_le r) _ _
    exact fun i => i.elim
  · intro S hS V hV hSV r z
    let rS : Γ(X, S) := (X.presheaf.map (homOfLE le_sup_left).op).hom r
    let rV : Γ(X, V.1) := (X.presheaf.map (homOfLE le_sup_right).op).hom r
    have hDS : X.basicOpen rS ≤ X.basicOpen r := by
      dsimp [rS]
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have hDV : X.basicOpen rV ≤ X.basicOpen r := by
      dsimp [rV]
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    let zS : Γ(N, X.basicOpen rS) :=
      (N.presheaf.map (homOfLE hDS).op).hom z
    let zV : Γ(N, X.basicOpen rV) :=
      (N.presheaf.map (homOfLE hDV).op).hom z
    obtain ⟨yS, nS, hyS⟩ := hV
      (hSV.of_subset Set.subset_union_left) rS zS
    obtain ⟨yV, nV, hyV⟩ :=
      Scheme.Modules.exists_pow_smul_res_of_basicOpen N V.2 rV zV
    let W : X.Opens := S ⊓ V.1
    let rW : Γ(X, W) :=
      (X.presheaf.map (homOfLE (inf_le_left : W ≤ S)).op).hom rS
    let a : Γ(N, W) :=
      (N.presheaf.map (homOfLE (inf_le_left : W ≤ S)).op).hom
        (rS ^ nV • yS)
    let b : Γ(N, W) :=
      (N.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom
        (rV ^ nS • yV)
    have hWcompact : IsCompact W.1 := by
      exact hSV _ _ Set.subset_union_left S.2 hS Set.subset_union_right
        V.1.2 V.2.isCompact
    have hrWV :
        (X.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom rV = rW := by
      calc
        (X.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom rV =
            (X.presheaf.map (homOfLE (show W ≤ S ⊔ V.1 from
              inf_le_right.trans le_sup_right)).op).hom r := by
          exact ringMap_res_res _ _ _ r
        _ = rW := by
          symm
          exact ringMap_res_res _ _ _ r
    have hDWS : X.basicOpen rW ≤ X.basicOpen rS := by
      dsimp [rW]
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have hDWV : X.basicOpen rW ≤ X.basicOpen rV := by
      calc
        X.basicOpen rW = X.basicOpen
            ((X.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom rV) :=
          congrArg X.basicOpen hrWV.symm
        _ = W ⊓ X.basicOpen rV := Scheme.basicOpen_res _ _ _
        _ ≤ X.basicOpen rV := inf_le_right
    have hDWW : X.basicOpen rW ≤ W := X.basicOpen_le rW
    have hDWr : X.basicOpen rW ≤ X.basicOpen r := hDWS.trans hDS
    let c : Γ(X, X.basicOpen rW) :=
      (X.presheaf.map (homOfLE hDWW).op).hom rW
    let zz : Γ(N, X.basicOpen rW) :=
      (N.presheaf.map (homOfLE hDWr).op).hom z
    have hySDW :
        (N.presheaf.map (homOfLE (hDWW.trans inf_le_left)).op).hom yS =
          c ^ nS • zz := by
      have h := congrArg
        ((N.presheaf.map (homOfLE hDWS).op).hom) hyS
      rw [Scheme.Modules.map_smul, map_pow] at h
      have hL :
          (N.presheaf.map (homOfLE hDWS).op).hom
              ((N.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom yS) =
            (N.presheaf.map (homOfLE (hDWW.trans inf_le_left)).op).hom yS :=
        map_res_res N _ _ _ yS
      have hc :
          (X.presheaf.map (homOfLE hDWS).op).hom
              ((X.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom rS) = c := by
        calc
          _ = (X.presheaf.map (homOfLE (hDWW.trans inf_le_left)).op).hom rS :=
            ringMap_res_res _ _ _ rS
          _ = (X.presheaf.map (homOfLE hDWW).op).hom
              ((X.presheaf.map (homOfLE (inf_le_left : W ≤ S)).op).hom rS) := by
            symm
            exact ringMap_res_res _ _ _ rS
          _ = c := rfl
      have hzS :
          (N.presheaf.map (homOfLE hDWS).op).hom zS = zz := by
        dsimp [zS, zz]
        exact map_res_res N _ _ _ z
      rw [hL, hc, hzS] at h
      exact h
    have hyVDW :
        (N.presheaf.map (homOfLE (hDWW.trans inf_le_right)).op).hom yV =
          c ^ nV • zz := by
      have h := congrArg
        ((N.presheaf.map (homOfLE hDWV).op).hom) hyV
      rw [Scheme.Modules.map_smul, map_pow] at h
      have hL :
          (N.presheaf.map (homOfLE hDWV).op).hom
              ((N.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom yV) =
            (N.presheaf.map (homOfLE (hDWW.trans inf_le_right)).op).hom yV :=
        map_res_res N _ _ _ yV
      have hc :
          (X.presheaf.map (homOfLE hDWV).op).hom
              ((X.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom rV) = c := by
        calc
          _ = (X.presheaf.map (homOfLE (hDWW.trans inf_le_right)).op).hom rV :=
            ringMap_res_res _ _ _ rV
          _ = (X.presheaf.map (homOfLE hDWW).op).hom
              ((X.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom rV) := by
            symm
            exact ringMap_res_res _ _ _ rV
          _ = c := by rw [hrWV]
      have hzV :
          (N.presheaf.map (homOfLE hDWV).op).hom zV = zz := by
        dsimp [zV, zz]
        exact map_res_res N _ _ _ z
      rw [hL, hc, hzV] at h
      exact h
    have hδ :
        (N.presheaf.map (homOfLE (X.basicOpen_le rW)).op).hom (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      dsimp [a, b]
      rw [map_res_res N hDWW inf_le_left (hDWW.trans inf_le_left)
          (rS ^ nV • yS),
        map_res_res N hDWW inf_le_right (hDWW.trans inf_le_right)
          (rV ^ nS • yV),
        Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_pow, map_pow]
      have hrS :
          (X.presheaf.map (homOfLE (hDWW.trans inf_le_left)).op).hom rS = c := by
        change (X.presheaf.map (homOfLE (hDWW.trans inf_le_left)).op).hom rS =
          (X.presheaf.map (homOfLE hDWW).op).hom rW
        dsimp [rW]
        symm
        exact ringMap_res_res _ _ _ rS
      have hrV :
          (X.presheaf.map (homOfLE (hDWW.trans inf_le_right)).op).hom rV = c := by
        calc
          _ = (X.presheaf.map (homOfLE hDWW).op).hom
              ((X.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom rV) := by
            symm
            exact ringMap_res_res _ _ _ rV
          _ = c := by rw [hrWV]
      rw [hrS, hrV, hySDW, hyVDW, smul_smul, smul_smul, ← pow_add, ← pow_add,
        add_comm nV nS]
    obtain ⟨m, hm⟩ :=
      exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        N hWcompact rW (a - b) hδ
    have hab :
        (N.presheaf.map (homOfLE (inf_le_left : W ≤ S)).op).hom
            (rS ^ (m + nV) • yS) =
          (N.presheaf.map (homOfLE (inf_le_right : W ≤ V.1)).op).hom
            (rV ^ (m + nS) • yV) := by
      have hm' : rW ^ m • a = rW ^ m • b := by
        rw [← sub_eq_zero, ← smul_sub]
        exact hm
      dsimp [a, b] at hm'
      rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_pow, map_pow,
        hrWV] at hm'
      have hrWS :
          (X.presheaf.map (homOfLE (inf_le_left : W ≤ S)).op).hom rS = rW := rfl
      simpa only [Scheme.Modules.map_smul, map_pow, map_mul, pow_add, smul_smul,
        hrWV, hrWS] using hm'
    obtain ⟨y, hyS', hyV'⟩ := exists_glue_sup N
      (rS ^ (m + nV) • yS) (rV ^ (m + nS) • yV) hab
    refine ⟨y, m + nS + nV, ?_⟩
    have hDSeq : X.basicOpen rS = S ⊓ X.basicOpen r := by
        dsimp [rS]
        rw [Scheme.basicOpen_res]
    have hDVeq : X.basicOpen rV = V.1 ⊓ X.basicOpen r := by
        dsimp [rV]
        rw [Scheme.basicOpen_res]
    have hcover : X.basicOpen r ≤ X.basicOpen rS ⊔ X.basicOpen rV := by
      intro x hx
      have hxSV := X.basicOpen_le r hx
      change x ∈ S ∨ x ∈ V.1 at hxSV
      rcases hxSV with hxS | hxV
      · apply Or.inl
        rw [hDSeq]
        exact ⟨hxS, hx⟩
      · apply Or.inr
        rw [hDVeq]
        exact ⟨hxV, hx⟩
    apply (abSheaf N).eq_of_locally_eq₂
      (homOfLE hDS) (homOfLE hDV) hcover
    · change (N.presheaf.map (homOfLE hDS).op).hom
          ((N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) =
        (N.presheaf.map (homOfLE hDS).op).hom
          ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r ^
            (m + nS + nV) • z)
      have hleft :
          (N.presheaf.map (homOfLE hDS).op).hom
              ((N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) =
            (N.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom
              ((N.presheaf.map (homOfLE le_sup_left).op).hom y) := by
        calc
          _ = (N.presheaf.map (homOfLE
              (hDS.trans (X.basicOpen_le r))).op).hom y :=
            map_res_res N _ _ _ y
          _ = _ := (map_res_res N _ _ _ y).symm
      have hscalar :
          (X.presheaf.map (homOfLE hDS).op).hom
              ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r) =
            (X.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom rS := by
        calc
          _ = (X.presheaf.map (homOfLE
              (hDS.trans (X.basicOpen_le r))).op).hom r :=
            ringMap_res_res _ _ _ r
          _ = _ := (ringMap_res_res _ _ _ r).symm
      rw [hleft, Scheme.Modules.map_smul, map_pow, hscalar]
      change (N.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom
          ((N.presheaf.map (homOfLE le_sup_left).op).hom y) =
        (X.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom rS ^
          (m + nS + nV) • zS
      have h := congrArg
        ((N.presheaf.map (homOfLE (X.basicOpen_le rS)).op).hom) hyS'
      rw [Scheme.Modules.map_smul, map_pow, hyS, smul_smul, ← pow_add] at h
      have hexp : m + nV + nS = m + nS + nV := by omega
      rwa [hexp] at h
    · change (N.presheaf.map (homOfLE hDV).op).hom
          ((N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) =
        (N.presheaf.map (homOfLE hDV).op).hom
          ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r ^
            (m + nS + nV) • z)
      have hleft :
          (N.presheaf.map (homOfLE hDV).op).hom
              ((N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) =
            (N.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom
              ((N.presheaf.map (homOfLE le_sup_right).op).hom y) := by
        calc
          _ = (N.presheaf.map (homOfLE
              (hDV.trans (X.basicOpen_le r))).op).hom y :=
            map_res_res N _ _ _ y
          _ = _ := (map_res_res N _ _ _ y).symm
      have hscalar :
          (X.presheaf.map (homOfLE hDV).op).hom
              ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom r) =
            (X.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom rV := by
        calc
          _ = (X.presheaf.map (homOfLE
              (hDV.trans (X.basicOpen_le r))).op).hom r :=
            ringMap_res_res _ _ _ r
          _ = _ := (ringMap_res_res _ _ _ r).symm
      rw [hleft, Scheme.Modules.map_smul, map_pow, hscalar]
      change (N.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom
          ((N.presheaf.map (homOfLE le_sup_right).op).hom y) =
        (X.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom rV ^
          (m + nS + nV) • zV
      have h := congrArg
        ((N.presheaf.map (homOfLE (X.basicOpen_le rV)).op).hom) hyV'
      rw [Scheme.Modules.map_smul, map_pow, hyV, smul_smul, ← pow_add] at h
      exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- **The qcqs module-localization lemma.**  For a quasicoherent module sheaf on a
compact quasi-separated open `U`, restriction to `D(r)` identifies its sections with
the localization of the sections over `U` away from `r`.

This upgrades the two denominator-clearing theorems above to the standard
`IsLocalizedModule` interface. -/
theorem isLocalizedModule_resBasicOpenLinearMap_of_qcqs
    {X : Scheme.{u}} (N : X.Modules) [N.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (r : Γ(X, U)) :
    letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom).toAlgebra
    letI : Module Γ(X, U) Γ(N, X.basicOpen r) :=
      Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom)
    IsLocalizedModule (Submonoid.powers r) (resBasicOpenLinearMap N r) := by
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom).toAlgebra
  letI : Module Γ(X, U) Γ(N, X.basicOpen r) :=
    Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom)
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) :=
    isLocalization_basicOpen_of_qcqs hU hU' r
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, k, rfl⟩
    have hunit :
        IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ k)) := by
      rw [map_pow]
      exact ((IsLocalization.Away.algebraMap_isUnit
        (S := Γ(X, X.basicOpen r)) r)).pow k
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hunit
    constructor
    · intro a b hab
      have hstep : ((u⁻¹ : Γ(X, X.basicOpen r)ˣ) : Γ(X, X.basicOpen r)) •
          (((u : Γ(X, X.basicOpen r))) • a) =
          ((u⁻¹ : Γ(X, X.basicOpen r)ˣ) : Γ(X, X.basicOpen r)) •
            (((u : Γ(X, X.basicOpen r))) • b) := by
        rw [show ((u : Γ(X, X.basicOpen r))) • a =
          (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ k) • a from by rw [hu]]
        rw [show ((u : Γ(X, X.basicOpen r))) • b =
          (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ k) • b from by rw [hu]]
        exact congrArg _ hab
      rwa [smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at hstep
    · intro y
      refine ⟨((u⁻¹ : Γ(X, X.basicOpen r)ˣ) : Γ(X, X.basicOpen r)) • y, ?_⟩
      show (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ k) •
        (((u⁻¹ : Γ(X, X.basicOpen r)ˣ) : Γ(X, X.basicOpen r)) • y) = y
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  · intro y
    obtain ⟨z₀, n, hz₀⟩ := exists_pow_smul_res_of_basicOpen_of_qcqs N hU hU' r y
    refine ⟨⟨z₀, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    show (r ^ n : Γ(X, U)) • y = resBasicOpenLinearMap N r z₀
    rw [← map_pow] at hz₀
    exact hz₀.symm
  · intro x₁ x₂ hx
    have hsub :
        (N.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (x₁ - x₂) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hx
    obtain ⟨n, hn⟩ :=
      exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        N hU r (x₁ - x₂) hsub
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    show (r ^ n : Γ(X, U)) • x₁ = (r ^ n : Γ(X, U)) • x₂
    rw [smul_sub] at hn
    exact sub_eq_zero.mp hn

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Qcqs localization for a function pulled back from an affine base.  If
`p : X → Spec R`, then restricting a quasicoherent sheaf from `X` to the basic open
of the image of `r : R` localizes its global sections away from `r`, after restricting
scalars from `Γ(X, 𝒪_X)` to `R`.

This is the form used for a DVR uniformizer: the resulting basic open is the generic
fibre. -/
theorem isLocalizedModule_resBasicOpenLinearMap_of_qcqs_overBase
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (N : X.Modules) [N.IsQuasicoherent]
    (hX : IsCompact (⊤ : X.Opens).1) (hX' : IsQuasiSeparated (⊤ : X.Opens).1)
    (r : R) :
    letI : Algebra R Γ(X, ⊤) := globalSectionsAlgebra p
    let t : Γ(X, ⊤) := algebraMap R Γ(X, ⊤) r
    letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen t) :=
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom).toAlgebra
    letI : Module Γ(X, ⊤) Γ(N, X.basicOpen t) :=
      Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom)
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Module R Γ(N, X.basicOpen t) :=
      Module.compHom _ (baseRingHom p).hom
    letI : IsScalarTower R Γ(X, ⊤) Γ(N, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower R Γ(X, ⊤) Γ(N, X.basicOpen t) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsLocalizedModule (Submonoid.powers r)
      ((resBasicOpenLinearMap N t).restrictScalars R) := by
  letI : Algebra R Γ(X, ⊤) := globalSectionsAlgebra p
  let t : Γ(X, ⊤) := algebraMap R Γ(X, ⊤) r
  letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen t) :=
    ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom).toAlgebra
  letI : Module Γ(X, ⊤) Γ(N, X.basicOpen t) :=
    Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom)
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Module R Γ(N, X.basicOpen t) :=
    Module.compHom _ (baseRingHom p).hom
  letI : IsScalarTower R Γ(X, ⊤) Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R Γ(X, ⊤) Γ(N, X.basicOpen t) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI := isLocalizedModule_resBasicOpenLinearMap_of_qcqs N hX hX' t
  exact IsLocalizedModule.restrictScalars_powers r (resBasicOpenLinearMap N t)

end AlgebraicGeometry.Scheme.Modules
