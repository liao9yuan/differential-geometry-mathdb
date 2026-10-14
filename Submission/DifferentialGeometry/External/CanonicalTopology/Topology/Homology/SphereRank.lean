import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OneDimensionalSphere
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyOne
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoPointReducedZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Finite-dimensional sphere prerequisites on the actual vector spaces -/

noncomputable section

open _root_.Set _root_.Metric _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

/-- Positive actual dimension supplies an actual unit vector. -/
def unitSpherePointOfFinrankPos (h : 0 < _root_.Module.finrank ℝ E) : _root_.Metric.sphere (0 : E) 1 := by
  letI := Module.nontrivial_of_finrank_pos h
  exact ⟨(NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose,
    (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose_spec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSpherePointOfFinrankPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSpherePointOfFinrankPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSpherePointOfFinrankPos ``Submission.DifferentialGeometry.Topology.unitSpherePointOfFinrankPos

/-- The actual reduced H0 of a zero-sphere is Z, with a proved two-point
model and the normalized original augmentation. -/
def integralZeroSphereReducedEquiv (hd : _root_.Module.finrank ℝ E = 1) :
    integralReducedHomologyZero (_root_.Metric.sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  let v := unitSpherePointOfFinrankPos (E := E) (by omega)
  letI := oneDimUnitSphere_finite hd v
  exact integralTwoPointReducedZeroEquiv (oneDimUnitSphereEquivBool hd v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroSphereReducedEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroSphereReducedEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroSphereReducedEquiv ``Submission.DifferentialGeometry.Topology.integralZeroSphereReducedEquiv

end

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Passing to the actual pole hyperplane lowers dimension by exactly one. -/
theorem unitSpherePoleHyperplane_finrank (n : ℕ) (hd : _root_.Module.finrank ℝ E = n + 1)
    (v : _root_.Metric.sphere (0 : E) 1) : _root_.Module.finrank ℝ (ℝ ∙ (v : E))ᗮ = n := by
  let : Fact (_root_.Module.finrank ℝ E = n + 1) := ⟨hd⟩
  apply Submodule.finrank_orthogonal_span_singleton
  intro h
  have hn := norm_eq_of_mem_sphere v
  rw [h, norm_zero] at hn
  norm_num at hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank ``Submission.DifferentialGeometry.Topology.unitSpherePoleHyperplane_finrank

/-- Dimension at least two supplies actual sphere path-connectedness. -/
theorem unitSphere_pathConnected_of_finrank (hd : 1 < _root_.Module.finrank ℝ E) :
    PathConnectedSpace (_root_.Metric.sphere (0 : E) 1) := by
  apply unitSphere_pathConnected_of_rank
  rw [← _root_.Module.finrank_eq_rank ℝ E]
  exact_mod_cast hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank ``Submission.DifferentialGeometry.Topology.unitSphere_pathConnected_of_finrank

end DifferentialGeometry.Topology
