import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingFillingQuadrant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem regular_closed_side_topology {E : Type*} [TopologicalSpace E] {X : Set E}
    (hX : IsClosed X) (hreg : closure (interior X) = X) (b : Bool) :
    IsClosed (if b then X else (interior X)ᶜ) ∧
      closure (interior (if b then X else (interior X)ᶜ)) =
        (if b then X else (interior X)ᶜ) ∧
      frontier (if b then X else (interior X)ᶜ) = frontier X := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨isOpen_interior.isClosed_compl, ?_, ?_⟩
    · rw [interior_compl, hreg, closure_compl]
    · rw [frontier_compl, frontier, interior_interior, hreg, frontier, hX.closure_eq]
  · exact ⟨hX, hreg, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regular_closed_side_topology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regular_closed_side_topology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regular_closed_side_topology ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regular_closed_side_topology

theorem exists_closed_side_of_frontier_contact
    {E : Type*} [TopologicalSpace E] {R X : Set E} (hX : IsClosed X)
    (hregR : closure (interior R) = R) (hconnR : IsPreconnected (interior R))
    (hcontact : R ∩ frontier X ⊆ frontier R) :
    ∃ b : Bool, R ⊆ (if b then X else (interior X)ᶜ) := by
  rcases interior_subset_one_side_of_frontier_contact hX hregR hconnR hcontact with
    ⟨-, hin⟩ | ⟨-, hout⟩
  · exact ⟨true, hin⟩
  · refine ⟨false, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, closure_compl] using hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_closed_side_of_frontier_contact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_closed_side_of_frontier_contact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_closed_side_of_frontier_contact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_closed_side_of_frontier_contact

end DifferentialGeometry.Topology.PiecewiseLinear
