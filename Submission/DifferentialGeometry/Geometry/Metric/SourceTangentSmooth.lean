import Submission.DifferentialGeometry.Geometry.Metric.SourceTangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem contMDiffOn_source_tangentMap {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun p : V × V =>
        TotalSpace.mk' E (r p.1) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r p.1 p.2)) (U ×ˢ _root_.Set.univ) := by
  have htr := hr.contMDiffOn_tangentMapWithin hmn hU.uniqueMDiffOn
  have hv : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) m
      (fun p : V × V => (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) := by
    intro p
    rw [_root_.Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_fst, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) m
        (fun q : V × V => q.2) p)
  apply (htr.comp hv.contMDiffOn (fun p hp => hp.1)).congr
  intro p hp
  dsimp only [_root_.Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hp.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffOn_source_tangentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffOn_source_tangentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffOn_source_tangentMap ``Submission.DifferentialGeometry.Geometry.contMDiffOn_source_tangentMap



theorem contMDiffOn_source_partial {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) (v : V) :
    ContMDiffOn 𝓘(ℝ, V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun z => TotalSpace.mk' E (r z) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r z v)) U :=
  (contMDiffOn_source_tangentMap hU hr hmn).comp
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hz => ⟨hz, _root_.Set.mem_univ _⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffOn_source_partial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffOn_source_partial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffOn_source_partial ``Submission.DifferentialGeometry.Geometry.contMDiffOn_source_partial

end DifferentialGeometry.Geometry
