import Submission.DifferentialGeometry.Topology.LoopSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Topology

variable {Q : Type*} [PseudoEMetricSpace Q]



theorem cylinder_lipschitz_of_lift {F : ℝ × loopCircle → Q} {K : ℝ≥0}
    (hF : LipschitzWith K (fun p : ℝ × ℝ => F (p.1, (p.2 : loopCircle)))) :
    LipschitzWith (K + K) F := by
  have htime (θ : loopCircle) : LipschitzWith K (fun v : ℝ => F (v, θ)) := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    intro v w
    simpa only [Prod.edist_eq, _root_.PseudoEMetricSpace.edist_self, max_eq_left (show (0 : ℝ≥0∞) ≤ _root_.EDist.edist v w from bot_le)] using hF (v, t) (w, t)
  have hcircle (v : ℝ) : LipschitzWith K (fun θ : loopCircle => F (v, θ)) := by
    apply loop_lipschitz_of_lift
    intro s t
    simpa only [Prod.edist_eq, _root_.PseudoEMetricSpace.edist_self, max_eq_right (show (0 : ℝ≥0∞) ≤ _root_.EDist.edist s t from bot_le)] using hF (v, s) (v, t)
  exact LipschitzWith.uncurry htime hcircle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cylinder_lipschitz_of_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cylinder_lipschitz_of_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cylinder_lipschitz_of_lift ``Submission.DifferentialGeometry.Topology.cylinder_lipschitz_of_lift

end DifferentialGeometry.Topology
