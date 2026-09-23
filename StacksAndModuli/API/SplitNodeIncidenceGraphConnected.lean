module

public import StacksAndModuli.API.SplitNodeIncidenceGraph
public import StacksAndModuli.API.SmoothPointComponents
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.JacobsonSpace

/-!
# Connectivity of the split-node incidence graph

This file proves that the split-node incidence graph of a connected nodal curve over an
algebraically closed field is connected. The topological core is that the intersection graph
of a finite closed cover of a connected space is connected. For a Noetherian scheme, the
irreducible components form such a cover.

To connect this topological argument to formal branches, the file proves that every
irreducible component through a point arises from a minimal prime of its local ring and,
under local Noetherianity, from a minimal prime of its completed local ring. Consequently,
every irreducible component through a split node is one of that node's incident components.
Finally, two distinct intersecting components of a nodal curve meet at a split node: a closed
point in their intersection cannot be smooth because its local ring would then be a domain.

## Main results

* `AlgebraicGeometry.Scheme.exists_stalkBranchComponent_eq_of_mem`: every component through
  a point comes from a minimal prime of the stalk.
* `AlgebraicGeometry.Scheme.exists_formalBranchComponent_eq_of_mem`: every component through
  a point of a locally Noetherian scheme comes from a formal branch.
* `AlgebraicGeometry.Scheme.SplitNodePoints.mem_incidentComponents_of_mem`: every component
  through a split node is incident to it.
* `AlgebraicGeometry.Scheme.splitNodeIncidenceGraph_adj_of_inter_nonempty`: distinct
  intersecting components of a nodal curve are adjacent.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.splitNodeIncidenceGraph_connected`: the
  split-node incidence graph of a connected nodal curve is connected.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- For a finite cover of a connected space by nonempty closed sets, the relation of
nonempty intersection has a single reflexive-transitive component. -/
theorem reflTransGen_nonempty_inter_of_connected_iUnion_of_finite_closed
    {T : Type u} {I : Type*} [TopologicalSpace T] [ConnectedSpace T] [Finite I]
    (s : I → Set T) (hs_nonempty : ∀ i, (s i).Nonempty)
    (hs_closed : ∀ i, IsClosed (s i)) (hs_cover : ⋃ i, s i = Set.univ)
    (i j : I) :
    Relation.ReflTransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let A : Set I :=
    {a | Relation.ReflTransGen (fun b c ↦ (s b ∩ s c).Nonempty) i a}
  let U : Set T := ⋃ a ∈ A, s a
  let V : Set T := ⋃ a ∈ Aᶜ, s a
  have hiA : i ∈ A := Relation.ReflTransGen.refl
  have hjA : j ∉ A := hij
  have hU_closed : IsClosed U :=
    A.toFinite.isClosed_biUnion fun a _ ↦ hs_closed a
  have hV_closed : IsClosed V :=
    Aᶜ.toFinite.isClosed_biUnion fun a _ ↦ hs_closed a
  have hUV : U ∪ V = Set.univ := by
    have hsplit : (⋃ a, s a) = U ∪ V := iSup_split s (· ∈ A)
    exact hsplit.symm.trans hs_cover
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    simp only [U, V, Set.mem_iUnion, exists_prop] at hxU hxV
    obtain ⟨a, haA, hxa⟩ := hxU
    obtain ⟨b, hbA, hxb⟩ := hxV
    exact hbA (haA.tail ⟨x, hxa, hxb⟩)
  have hU_nonempty : U.Nonempty := by
    obtain ⟨x, hx⟩ := hs_nonempty i
    exact ⟨x, Set.mem_iUnion₂_of_mem hiA hx⟩
  have hV_nonempty : V.Nonempty := by
    obtain ⟨x, hx⟩ := hs_nonempty j
    exact ⟨x, Set.mem_iUnion₂_of_mem hjA hx⟩
  have hcompl : IsCompl U V := by
    rw [isCompl_iff, Set.disjoint_iff_inter_eq_empty, codisjoint_iff]
    exact ⟨Set.disjoint_iff_inter_eq_empty.mp hdisj, hUV⟩
  have hU_open : IsOpen U := by
    rw [hcompl.eq_compl]
    exact hV_closed.isOpen_compl
  have hU_univ : U = Set.univ := IsClopen.eq_univ ⟨hU_closed, hU_open⟩ hU_nonempty
  obtain ⟨x, hxV⟩ := hV_nonempty
  exact Set.disjoint_left.mp hdisj (hU_univ.symm ▸ Set.mem_univ x) hxV

/-- Every irreducible component through a point is the component assigned to some minimal
prime of the local ring at that point. -/
theorem exists_stalkBranchComponent_eq_of_mem
    (X : Scheme.{u}) (x : X) (Z : irreducibleComponents X) (hx : x ∈ Z.1) :
    ∃ p : minimalPrimes (X.presheaf.stalk x), X.stalkBranchComponent x p = Z := by
  let U := X.branchAffineOpen x
  let hU : IsAffineOpen U :=
    isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let hxU : x ∈ U := X.affineCover.covers x
  let xU : U := ⟨x, hxU⟩
  let e : U ≃ₜ Spec Γ(X, U) := hU.isoSpec.hom.homeomorph
  let ZU : Set U := U.ι ⁻¹' Z.1
  have hZU : ZU ∈ irreducibleComponents U := by
    apply preimage_mem_irreducibleComponents Z.2 U.ι.isOpenEmbedding
    exact ⟨x, hx, xU, rfl⟩
  let SZ : Set (Spec Γ(X, U)) := e '' ZU
  have he_fiber : ∀ y, IsPreirreducible (e ⁻¹' ({y} : Set (Spec Γ(X, U)))) :=
    fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible
  have hSZ : SZ ∈ irreducibleComponents (Spec Γ(X, U)) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
      e.isOpenMap he_fiber e.surjective hZU
  let qZ : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal SZ
  have hqZ : qZ ∈ minimalPrimes Γ(X, U) := by
    rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents]
    exact ⟨SZ, hSZ, rfl⟩
  let _ : qZ.IsPrime := hqZ.isPrime
  let p₀ : Ideal Γ(X, U) := (hU.primeIdealOf xU).asIdeal
  have hqZp₀ : qZ ≤ p₀ := by
    intro a ha
    exact (PrimeSpectrum.mem_vanishingIdeal SZ a).mp ha (e xU) ⟨xU, hx, rfl⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p₀ :=
    hU.isLocalization_stalk xU
  let p : minimalPrimes (X.presheaf.stalk x) := ⟨
    qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x)), by
      have hmem : qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
          ((⊥ : Ideal Γ(X, U)).map
            (algebraMap Γ(X, U) (X.presheaf.stalk x))).minimalPrimes := by
        rw [IsLocalization.minimalPrimes_map p₀.primeCompl (X.presheaf.stalk x)]
        change (qZ.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).under Γ(X, U) ∈
          minimalPrimes Γ(X, U)
        rw [Ideal.under_map_of_isLocalizationAtPrime p₀ hqZp₀]
        exact hqZ
      simpa only [Ideal.map_bot] using hmem⟩
  have hcontraction : (X.stalkBranchContraction x p : Ideal Γ(X, U)) = qZ := by
    exact Ideal.under_map_of_isLocalizationAtPrime p₀ hqZp₀
  have hgeneric_mem : X.stalkBranchGenericPoint x p ∈ SZ := by
    have hzero : PrimeSpectrum.zeroLocus qZ = SZ := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        (isClosed_of_mem_irreducibleComponents SZ hSZ).closure_eq]
    rw [← hzero, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    change a ∈ (X.stalkBranchGenericPoint x p).asIdeal
    rw [X.stalkBranchGenericPoint_asIdeal x p, hcontraction]
    exact ha
  have hpoint_mem :
      X.fromSpecStalk x (X.stalkBranchPoint x p) ∈ Z.1 := by
    rw [X.fromSpecStalk_stalkBranchPoint_eq x p]
    change hU.fromSpec (X.stalkBranchGenericPoint x p) ∈ Z.1
    obtain ⟨z, hzZU, hz⟩ := hgeneric_mem
    have hzmap : hU.fromSpec (e z) = U.ι z := by
      change (hU.isoSpec.hom ≫ hU.fromSpec) z = U.ι z
      rw [hU.isoSpec_hom_fromSpec]
    rw [← hz, hzmap]
    exact hzZU
  refine ⟨p, Subtype.ext ?_⟩
  apply Set.Subset.antisymm
  · rw [X.stalkBranchComponent_val x p]
    exact closure_minimal (Set.singleton_subset_iff.mpr hpoint_mem)
      (isClosed_of_mem_irreducibleComponents Z.1 Z.2)
  · exact (X.stalkBranchComponent x p).2.2 Z.2.1
      (by
        rw [X.stalkBranchComponent_val x p]
        exact closure_minimal (Set.singleton_subset_iff.mpr hpoint_mem)
          (isClosed_of_mem_irreducibleComponents Z.1 Z.2))

/-- On a locally Noetherian scheme, every irreducible component through a point is the
component assigned to some formal branch of the completed local ring at that point. -/
theorem exists_formalBranchComponent_eq_of_mem
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    (Z : irreducibleComponents X) (hx : x ∈ Z.1) :
    ∃ b : X.FormalBranchesAt x, X.formalBranchComponent x b = Z := by
  obtain ⟨p, hp⟩ := X.exists_stalkBranchComponent_eq_of_mem x Z hx
  have hinj : Function.Injective (X.toCompletedLocalRing x) := by
    intro a b hab
    apply AdicCompletion.of_injective
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
    simpa only [X.toCompletedLocalRing_apply] using hab
  have hpmin : p.1 ∈
      ((⊥ : Ideal (X.completedLocalRing x)).comap (X.toCompletedLocalRing x)).minimalPrimes := by
    rw [Ideal.comap_bot_of_injective (X.toCompletedLocalRing x) hinj]
    exact p.2
  obtain ⟨Q, hQ, hQp⟩ :=
    Ideal.exists_minimalPrimes_comap_eq (X.toCompletedLocalRing x) p.1 hpmin
  let b : X.FormalBranchesAt x := ⟨Q, hQ⟩
  have hbp : b.toStalkBranch = p := by
    apply Subtype.ext
    exact hQp
  refine ⟨b, ?_⟩
  change X.stalkBranchComponent x b.toStalkBranch = Z
  rw [hbp]
  exact hp

/-- Every irreducible component containing a split node belongs to the node's canonical
set of incident components. -/
theorem SplitNodePoints.mem_incidentComponents_of_mem
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (Z : irreducibleComponents X) (hqZ : q.1 ∈ Z.1) :
    Z ∈ q.incidentComponents := by
  obtain ⟨b, hb⟩ := X.exists_formalBranchComponent_eq_of_mem q.1 Z hqZ
  refine ⟨b, ?_⟩
  change X.formalBranchComponent q.1 b = Z
  exact hb

/-- Two distinct irreducible components containing a split node are the two endpoints of
the corresponding edge of the split-node incidence graph. -/
theorem splitNodeIncidenceGraph_isLink_of_ne_of_mem
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (Z W : irreducibleComponents X) (hZW : Z ≠ W)
    (hqZ : q.1 ∈ Z.1) (hqW : q.1 ∈ W.1) :
    (X.splitNodeIncidenceGraph k).IsLink q Z W := by
  have hZ := q.mem_incidentComponents_of_mem Z hqZ
  have hW := q.mem_incidentComponents_of_mem W hqW
  obtain ⟨A, B, hAB⟩ := q.exists_incidentComponents_eq_pair
  rw [hAB] at hZ hW
  apply (splitNodeIncidenceGraph_isLink_iff q Z W).mpr
  rw [hAB, Set.pair_eq_pair_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ hW
  aesop

/-- Two distinct irreducible components of a nodal curve over an algebraically closed
field are adjacent in the split-node incidence graph whenever they intersect. -/
theorem splitNodeIncidenceGraph_adj_of_inter_nonempty
    {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (h : IsNodalCurveOver k X)
    (Z W : irreducibleComponents X) (hZW : Z ≠ W)
    (hinter : (Z.1 ∩ W.1).Nonempty) :
    (X.splitNodeIncidenceGraph k).Adj Z W := by
  let _ : IsNodalCurveOver k X := h
  let _ : JacobsonSpace X :=
    LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of k))
  have hinter_closed : IsClosed (Z.1 ∩ W.1) :=
    (isClosed_of_mem_irreducibleComponents Z.1 Z.2).inter
      (isClosed_of_mem_irreducibleComponents W.1 W.2)
  obtain ⟨q, ⟨hqZ, hqW⟩, hqclosed⟩ :=
    nonempty_inter_closedPoints hinter hinter_closed.isLocallyClosed
  rcases h.smooth_or_isSplitNode q hqclosed with hsmooth | hnode
  · let _ : IsRegularLocalRing (X.presheaf.stalk q) :=
      isRegularLocalRing_stalk_of_formallySmooth_toSpec_field
        (X ↘ Spec (CommRingCat.of k)) q hsmooth
    let _ : IsDomain (X.presheaf.stalk q) := IsRegularLocalRing.isDomain
    exact (hZW (X.eq_of_mem_irreducibleComponents_of_isDomain_stalk
      q Z W hqZ hqW)).elim
  · exact ⟨⟨q, hnode⟩,
      splitNodeIncidenceGraph_isLink_of_ne_of_mem ⟨q, hnode⟩ Z W hZW hqZ hqW⟩

/-- The simple graph underlying the split-node incidence graph of a connected nodal curve
over an algebraically closed field is connected. -/
theorem IsNodalCurveOver.splitNodeIncidenceGraph_connected
    {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    [ConnectedSpace X] (h : IsNodalCurveOver k X) :
    (X.splitNodeIncidenceGraph k).toSimpleGraph.Connected := by
  let _ : IsNoetherian X := h.isNoetherian
  let _ : Finite (irreducibleComponents X) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  let G := X.splitNodeIncidenceGraph k
  have hvertex_nonempty : Nonempty G.vertexSet := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨⟨⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩, Set.mem_univ _⟩⟩
  let _ : Nonempty G.vertexSet := hvertex_nonempty
  refine ⟨?_⟩
  intro V W
  apply (G.toSimpleGraph.reachable_iff_reflTransGen V W).mpr
  have hcover : (⋃ A : G.vertexSet, A.1.1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ x
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion_of_mem
      (⟨⟨Z, hZ⟩, Set.mem_univ _⟩ : G.vertexSet) hxZ
  have hchain : Relation.ReflTransGen
      (fun A B : G.vertexSet ↦ (A.1.1 ∩ B.1.1).Nonempty) V W :=
    reflTransGen_nonempty_inter_of_connected_iUnion_of_finite_closed
      (fun A : G.vertexSet ↦ A.1.1)
      (fun A ↦ A.1.2.1.nonempty)
      (fun A ↦ isClosed_of_mem_irreducibleComponents A.1.1 A.1.2)
      hcover V W
  exact hchain.lift' id fun A B hinter ↦ by
    by_cases hAB : A = B
    · subst B
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      change A ≠ B ∧ G.Adj A.1 B.1
      refine ⟨hAB, ?_⟩
      apply splitNodeIncidenceGraph_adj_of_inter_nonempty h A.1 B.1
      · intro hval
        exact hAB (Subtype.ext hval)
      · exact hinter

end AlgebraicGeometry.Scheme
