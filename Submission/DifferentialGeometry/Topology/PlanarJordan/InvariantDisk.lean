import Submission.DifferentialGeometry.Topology.PlanarJordan.ClosedInterior
import Submission.DifferentialGeometry.Topology.PlanarJordan.PeriodicOrbit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PlanarJordan

theorem exists_invariant_disk_of_periodic_orbit
    (φ : _root_.Flow ℝ ℂ) {x : ℂ}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ frontier U = φ.orbit x ∧
      Nonempty (_root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ closure U) ∧ IsInvariant φ (closure U) := by
  obtain ⟨U, _, hU, _, hconn, _, _, _, hfrontier, _, hcompact, _, hinv, _⟩ :=
    exists_invariant_regions_of_periodic_orbit φ hnon hreturn
  obtain ⟨γ, hγ, hclose, hinj, himage⟩ :=
    DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit φ hnon hreturn
  refine ⟨U, hU, hconn, hfrontier,
    nonempty_homeomorph_closedBall_closure hU hconn hcompact hγ.continuousOn
      hclose hinj (hfrontier.trans himage.symm), ?_⟩
  intro t
  exact (hinv t).closure (φ.continuous continuous_const continuous_id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_invariant_disk_of_periodic_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_invariant_disk_of_periodic_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_invariant_disk_of_periodic_orbit ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_invariant_disk_of_periodic_orbit

end DifferentialGeometry.Topology.PlanarJordan
