import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



open _root_.Set _root_.Filter _root_.Uniformity _root_.UniformSpace
open scoped _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis



theorem exists_uniform_diagonal_radius {M : Type*} [PseudoEMetricSpace M] [CompactSpace M]
    {U : Set (M × M)} (hU : IsOpen U) (hdiag : ∀ x, (x, x) ∈ U) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ x y, _root_.EDist.edist x y ≤ (ρ : ℝ≥0∞) → (x, y) ∈ U := by
  have hu : U ∈ 𝓤 M := by
    rw [compactSpace_uniformity]
    exact mem_iSup.mpr (fun x => hU.mem_nhds (hdiag x))
  obtain ⟨ρ, hρ, hρU⟩ := uniformity_basis_edist_nnreal_le.mem_iff.mp hu
  exact ⟨ρ, hρ, fun x y hxy => hρU hxy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_diagonal_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_diagonal_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_diagonal_radius ``Submission.DifferentialGeometry.Analysis.exists_uniform_diagonal_radius

end DifferentialGeometry.Analysis
