import Submission.DifferentialGeometry.Topology.Connected.RegularClosedComponents
import Submission.DifferentialGeometry.Geometry.Neck.Spatial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

theorem connectedComponentIn_interval_side
    {X Z : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} {x : X} {r : ℝ} (f : Z → ℝ → X)
    (hcontinuous : ∀ z, ContinuousOn (f z) (_root_.Set.Ioo (-r) r))
    (hside : ∀ z, ∀ t ∈ _root_.Set.Ioo (-r) r, f z t ∈ K ↔ t ≤ 0)
    (hinterior : ∀ z, ∀ t ∈ _root_.Set.Ioo (-r) r, f z t ∈ interior K ↔ t < 0)
    (hzero : ∀ z, f z 0 ∈ connectedComponentIn K x) :
    (∀ z, ∀ t ∈ _root_.Set.Ioo (-r) r,
      f z t ∈ connectedComponentIn K x ↔ t ≤ 0) ∧
    ∀ z, ∀ t ∈ _root_.Set.Ioo (-r) r,
      f z t ∈ interior (connectedComponentIn K x) ↔ t < 0 := by
  have hmem : ∀ z, ∀ t ∈ _root_.Set.Ioo (-r) r,
      f z t ∈ connectedComponentIn K x ↔ t ≤ 0 := by
    intro z t ht
    constructor
    · intro h
      exact (hside z t ht).mp (connectedComponentIn_subset K x h)
    · intro ht0
      let γ : ℝ → X := f z
      have hr : 0 < r := neg_lt_zero.mp (ht.1.trans_le ht0)
      have hI : _root_.Set.Icc t 0 ⊆ _root_.Set.Ioo (-r) r := by
        intro s hs
        exact ⟨ht.1.trans_le hs.1, hs.2.trans_lt hr⟩
      have hγ : ContinuousOn γ (_root_.Set.Icc t 0) := (hcontinuous z).mono hI
      have hsub : γ '' _root_.Set.Icc t 0 ⊆ K := by
        rintro w ⟨s, hs, rfl⟩
        exact (hside z s (hI hs)).mpr hs.2
      have hzero' : γ 0 ∈ connectedComponentIn K x := by
        simpa only [γ] using hzero z
      rw [connectedComponentIn_eq hzero']
      exact (isPreconnected_Icc.image γ hγ).subset_connectedComponentIn
        (_root_.Set.mem_image_of_mem γ ⟨ht0, le_rfl⟩) hsub (_root_.Set.mem_image_of_mem γ ⟨le_rfl, ht0⟩)
  refine ⟨hmem, ?_⟩
  intro z t ht
  constructor
  · intro h
    exact (hinterior z t ht).mp (interior_mono (connectedComponentIn_subset K x) h)
  · intro ht0
    apply (mem_interior_iff_notMem_frontier ((hmem z t ht).mpr ht0.le)).mpr
    intro hf
    exact (frontier_connectedComponentIn_subset K x hf).2
      ((hinterior z t ht).mpr ht0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_interval_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_interval_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_interval_side ``Submission.DifferentialGeometry.Topology.connectedComponentIn_interval_side

end DifferentialGeometry.Topology
