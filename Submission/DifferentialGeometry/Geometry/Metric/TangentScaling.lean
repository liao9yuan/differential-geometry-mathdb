import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Topology _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]



theorem continuous_tangent_smul {a : X → ℝ} {v : X → TangentBundle I M}
    (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x => (TotalSpace.mk' E (v x).proj (a x • (v x).2) : TangentBundle I M)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I) (v x).proj
  obtain ⟨hb, hd⟩ := (FiberBundle.continuousAt_totalSpace E v).mp (hv.continuousAt (x := x))
  apply (FiberBundle.continuousAt_totalSpace E _).mpr
  refine ⟨hb, ?_⟩
  have hc := ha.continuousAt.smul hd
  apply hc.congr_of_eventuallyEq
  have hbase : ∀ᶠ y in 𝓝 x, (v y).proj ∈ e.baseSet :=
    hb.eventually_mem (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _))
  filter_upwards [hbase] with y hy
  exact (e.linear ℝ hy).map_smul (a y) (v y).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuous_tangent_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuous_tangent_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuous_tangent_smul ``Submission.DifferentialGeometry.Geometry.continuous_tangent_smul

end DifferentialGeometry.Geometry
