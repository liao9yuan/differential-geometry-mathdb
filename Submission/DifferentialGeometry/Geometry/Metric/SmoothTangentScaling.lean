import Submission.DifferentialGeometry.Geometry.Metric.TangentScaling
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M X : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace X] [ChartedSpace H' X] {n : ℕ∞ω}



theorem contMDiffAt_tangent_smul {a : X → ℝ} {v : X → TangentBundle I M} {x : X}
    (ha : ContMDiffAt J 𝓘(ℝ, ℝ) n a x) (hv : ContMDiffAt J I.tangent n v x) :
    ContMDiffAt J I.tangent n
      (fun y => (TotalSpace.mk' E (v y).proj (a y • (v y).2) : TangentBundle I M)) x := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) (v x).proj
  obtain ⟨hb, hd⟩ := Bundle.contMDiffAt_totalSpace.mp hv
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb, ?_⟩
  apply (ha.smul hd).congr_of_eventuallyEq
  have hbase : ∀ᶠ y in 𝓝 x, (v y).proj ∈ e.baseSet :=
    hb.continuousAt.eventually_mem
      (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _))
  filter_upwards [hbase] with y hy
  exact (e.linear ℝ hy).map_smul (a y) (v y).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffAt_tangent_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffAt_tangent_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffAt_tangent_smul ``Submission.DifferentialGeometry.Geometry.contMDiffAt_tangent_smul


theorem contMDiff_tangent_scaling :
    ContMDiff (𝓘(ℝ, ℝ).prod I.tangent) I.tangent n
      (fun p : ℝ × TangentBundle I M =>
        (TotalSpace.mk' E p.2.proj (p.1 • p.2.2) : TangentBundle I M)) :=
  fun _ => contMDiffAt_tangent_smul contMDiffAt_fst contMDiffAt_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiff_tangent_scaling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiff_tangent_scaling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiff_tangent_scaling ``Submission.DifferentialGeometry.Geometry.contMDiff_tangent_scaling

end DifferentialGeometry.Geometry
