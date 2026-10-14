import Submission.DifferentialGeometry.Geometry.Metric.Path.Length
import Submission.DifferentialGeometry.Topology.Manifold.Path.Reparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Path
open _root_.Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x y : M}

variable [(x : M) → ENorm (TangentSpace I x)]
  [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]

open _root_.Path in
theorem riemannianELength_withSittingInstants (p : Path x y)
    (hp : MDifferentiableOn 𝓘(ℝ, ℝ) I p.extend (_root_.Set.Icc 0 1)) :
    p.withSittingInstants.riemannianELength (I := I) = p.riemannianELength (I := I) := by
  rw [riemannianELength, extend_withSittingInstants]
  have h0 : Real.smoothTransition (3 * (0 : ℝ) - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : Real.smoothTransition (3 * (1 : ℝ) - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by norm_num)
  have hmono : Monotone (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.monotone.comp (by
      intro t s hts
      dsimp
      linarith)
  have hcd : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  rw [Manifold.pathELength_comp_of_monotoneOn zero_le_one
    (hmono.monotoneOn _)
    (hcd.differentiable (by norm_num)).differentiableOn
    (by simpa only [h0, h1] using hp), h0, h1]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.riemannianELength_withSittingInstants then
    throwError "Refusing to shadow existing declaration Path.riemannianELength_withSittingInstants"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.riemannianELength_withSittingInstants ``Submission.Path.riemannianELength_withSittingInstants

end Path
