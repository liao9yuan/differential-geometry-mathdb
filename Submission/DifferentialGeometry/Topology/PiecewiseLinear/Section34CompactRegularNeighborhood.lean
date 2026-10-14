import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Submission.DifferentialGeometry.Topology.Homotopy

open _root_.IsCompact in
theorem IsCompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin
    {X : Type*} [TopologicalSpace X] {B : ℕ → Set X}
    (hc : IsCompact (⋃ i, B i)) (hm : Monotone B)
    (hn : ∀ i, ∀ x ∈ B i, B (i + 1) ∈ 𝓝[⋃ j, B j] x) :
    ∃ i, B i = ⋃ j, B j := by
  classical
  choose k hk using fun x : (⋃ i, B i) => mem_iUnion.mp x.2
  obtain ⟨s, hs⟩ := hc.elim_nhdsWithin_subcover'
    (fun x hx => B (k ⟨x, hx⟩ + 1)) (fun x hx => hn _ x (hk ⟨x, hx⟩))
  refine ⟨s.sup (fun x => k x + 1), Subset.antisymm (_root_.Set.subset_iUnion _ _) ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact hm (Finset.le_sup (f := fun x => k x + 1) hy) hxy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsCompact
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration IsCompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin ``Submission.IsCompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin

namespace DifferentialGeometry.Topology.Homotopy

theorem CompatibleStrongDeformationRetractSystem.core_eq_of_stage_eq_iUnion
    {X : Type*} [TopologicalSpace X] {A B : ℕ → Set X}
    (R : CompatibleStrongDeformationRetractSystem A B) {i : ℕ}
    (hi : B i = ⋃ j, B j) : A i = ⋃ j, A j := by
  refine Subset.antisymm (_root_.Set.subset_iUnion _ _) ?_
  intro x hx
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  have hxB : x ∈ ⋃ j, B j := mem_iUnion.mpr ⟨j, R.core_subset j hxj⟩
  have hxi : x ∈ B i := hi.symm ▸ hxB
  have heq : R.retractionValue ⟨x, hxB⟩ = x := by
    rw [R.retractionValue_eq_stage _ (R.core_subset j hxj)]
    exact congrArg Subtype.val ((R.stage j).retraction_eq hxj)
  have hmem : R.retractionValue ⟨x, hxB⟩ ∈ A i := by
    rw [R.retractionValue_eq_stage _ hxi]
    exact ((R.stage i).retraction ⟨x, hxi⟩).2
  exact heq ▸ hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.CompatibleStrongDeformationRetractSystem.core_eq_of_stage_eq_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.CompatibleStrongDeformationRetractSystem.core_eq_of_stage_eq_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.CompatibleStrongDeformationRetractSystem.core_eq_of_stage_eq_iUnion ``Submission.DifferentialGeometry.Topology.Homotopy.CompatibleStrongDeformationRetractSystem.core_eq_of_stage_eq_iUnion

end DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem compact_exhaustion_ambient
    {n m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {N U : Set X}
    (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) n X U)
    (A L : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hJ : T.complex.faces = ⋃ i, (A i).faces)
    (hN : Set.range (fun x : derivedNeighborhoodExhaustionAmbient A L => T.map x) = N)
    (hc : IsCompact N) : IsCompact (derivedNeighborhoodExhaustionAmbient A L) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let B := fun i => (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space
  have hsub : (⋃ i, B i) ⊆ T.complex.space := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    refine space_mono_of_faces_subset ?_ (derivedNeighborhood_space_subset (A i) (L i) hxi)
    intro s hs
    rw [hJ]
    exact mem_iUnion.mpr ⟨i, hs⟩
  let f : (⋃ i, B i) → X := fun x => T.map x
  have hf : _root_.Topology.IsEmbedding f :=
    T.isEmbedding.comp (IsEmbedding.inclusion hsub)
  have hN' : Set.range f = N := hN
  have hcompact : IsCompact (⋃ i, B i) := by
    have hu : IsCompact (_root_.Set.univ : Set (⋃ i, B i)) :=
      hf.isCompact_iff.mpr (by rw [_root_.Set.image_univ, hN']; exact hc)
    simpa only [_root_.Set.image_univ, Subtype.range_coe] using hu.image continuous_subtype_val
  exact hcompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compact_exhaustion_ambient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.compact_exhaustion_ambient target :: scope.openDecls } }

open _root_.Classical in
theorem IsPLDerivedNeighborhoodExhaustion.exists_finite_stage_of_isCompact
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {N K U : Set X}
    (h : IsPLDerivedNeighborhoodExhaustion (n := n) N K U) (hc : IsCompact N) :
    ∃ (m : ℕ) (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) n X U)
      (A L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      A.faces.Finite ∧ L.faces.Finite ∧ A.faces ⊆ T.complex.faces ∧ L.faces ⊆ A.faces ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧ IsCombinatorialManifoldWithBoundary n A ∧
      IsCombinatorialManifoldWithBoundary n (@derivedNeighborhood _ _ _ (Classical.decEq _) A L) ∧
      T.map '' (@derivedNeighborhood _ _ _ (Classical.decEq _) A L).space = N ∧
      T.map '' L.space = K := by
  obtain ⟨m, T, A, L, hJ, hfin, hLA, hcard, hA, hD, hAm, hLm, hres, hnhds, hN, hK⟩ := h
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let _ : ∀ i, Finite (A i).faces := fun i => (hfin i).to_subtype
  let B := fun i => (@derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)).space
  have hcompact : IsCompact (⋃ i, B i) := compact_exhaustion_ambient T A L hJ hN hc
  have hmono : Monotone B := by
    intro i j hij
    exact space_mono_of_faces_subset (derivedNeighborhood_faces_mono (hAm hij) (hLm hij))
  obtain ⟨i, hi⟩ := hcompact.exists_eq_iUnion_of_monotone_mem_nhdsWithin hmono
    (fun i x hx => hnhds i hx)
  let R := derivedNeighborhoodCompatibleStrongDeformationRetractSystem A L hLA hAm hLm
    hres hnhds
  have hcore : (L i).space = ⋃ j, (L j).space := R.core_eq_of_stage_eq_iUnion hi
  have himage : T.map '' B i = N := by
    rw [hi, ← hN]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  have hcoreimage : T.map '' (L i).space = K := by
    rw [hcore, ← hK]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyB : y ∈ ⋃ i, B i := by
        obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨j, subcomplex_space_subset_derivedNeighborhood (hLA j) hyj⟩
      exact ⟨⟨y, hyB⟩, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  refine ⟨m, T, A i, L i, hfin i, (hfin i).subset (hLA i), ?_, hLA i, hcard i,
    hA i, hD i, himage, hcoreimage⟩
  intro s hs
  rw [hJ]
  exact mem_iUnion.mpr ⟨i, hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDerivedNeighborhoodExhaustion.exists_finite_stage_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLDerivedNeighborhoodExhaustion.exists_finite_stage_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDerivedNeighborhoodExhaustion.exists_finite_stage_of_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDerivedNeighborhoodExhaustion.exists_finite_stage_of_isCompact

end DifferentialGeometry.Topology.PiecewiseLinear
