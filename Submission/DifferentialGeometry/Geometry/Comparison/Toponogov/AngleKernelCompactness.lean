import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.AngleKernel
import Submission.DifferentialGeometry.Topology.MetricSpace.TotallyBounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Toponogov

variable {ι : Type*}

theorem AngleKernel.totallyBounded_iff_finset_angle_net (K : AngleKernel ι) :
    let _ := K.metricSpace
    TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)) ↔
      ∀ eps > 0, ∃ A : Finset ι, ∀ i, ∃ a ∈ A, K.angle a i < eps := by
  classical
  let _ := K.metricSpace
  change TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)) ↔ _
  rw [Metric.totallyBounded_univ_iff_finset_net]
  choose rep hrep using K.classOf_surjective
  constructor
  · intro h eps heps
    obtain ⟨S, hS⟩ := h eps heps
    refine ⟨S.image rep, fun i => ?_⟩
    obtain ⟨q, hq, hd⟩ := hS (K.classOf i)
    refine ⟨rep q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
    have heq : K.angle (rep q) i = Dist.dist q (K.classOf i) := by
      change K.dist (K.classOf (rep q)) (K.classOf i) = _
      rw [hrep]
      rfl
    rw [heq, _root_.dist_comm]
    exact hd
  · intro h eps heps
    obtain ⟨A, hA⟩ := h eps heps
    refine ⟨A.image K.classOf, fun q => ?_⟩
    obtain ⟨i, rfl⟩ := K.classOf_surjective q
    obtain ⟨a, ha, hd⟩ := hA i
    refine ⟨K.classOf a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [_root_.dist_comm]
    exact hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.AngleKernel.totallyBounded_iff_finset_angle_net then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.AngleKernel.totallyBounded_iff_finset_angle_net"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.AngleKernel.totallyBounded_iff_finset_angle_net ``Submission.DifferentialGeometry.Toponogov.AngleKernel.totallyBounded_iff_finset_angle_net

end DifferentialGeometry.Toponogov
