import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import Submission.DifferentialGeometry.Topology.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set

namespace DifferentialGeometry.CheegerGromovCompactness

theorem MapCInfConvergenceOnCompacts.eventually_dist_comp_lt
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U K : Set E} {V L : Set F}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hA : MapCInfConvergenceOnCompacts V A Ainf)
    (hB : MapCInfConvergenceOnCompacts U B Binf)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hL : IsCompact L) (hLV : L ⊆ V)
    (hAinf : ContinuousOn Ainf L)
    (hmap : ∀ᶠ k in _root_.Filter.atTop, _root_.Set.MapsTo (B k) K L)
    (hmapInf : _root_.Set.MapsTo Binf K L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, _root_.Dist.dist (A k (B k x)) (Ainf (Binf x)) < ε := by
  have hAu := tendstoUniformlyOn_of_cPConvergence (hA.cPConvergenceOn hL hLV 0)
  have hBu := tendstoUniformlyOn_of_cPConvergence (hB.cPConvergenceOn hK hKU 0)
  have hcomp := hAu.comp_of_eventually_mapsTo
    (hL.uniformContinuousOn_of_continuous hAinf) hBu hmap hmapInf
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hcomp) ε hε] with k hk x hx
  simpa only [dist_comm] using hk x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.eventually_dist_comp_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.eventually_dist_comp_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.eventually_dist_comp_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts.eventually_dist_comp_lt

end DifferentialGeometry.CheegerGromovCompactness
