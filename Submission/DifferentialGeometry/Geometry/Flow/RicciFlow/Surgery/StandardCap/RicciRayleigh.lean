import Submission.DifferentialGeometry.Geometry.Curvature.RicciRayleigh
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

theorem ricciTensor_zero (v w : E3) :
    ricciTensor metric 0 v w = metric.inner 0 v w := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hsec (u z : E3) :
      metricRm04StandardAt metric 0 u z z u =
        (1 / 2 : ℝ) *
          (metric.inner 0 u u * metric.inner 0 z z -
            metric.inner 0 u z * metric.inner 0 u z) := by
    simpa only [metric_inner_zero, pow_two] using metricRm04_zero u z
  have hRm := metricRm_of_sec metric 0 (1 / 2) hsec
  have hRic := ricci_of_rm metric 0 (1 / 2) hRm v w
  norm_num only [finrank_euclideanSpace_fin, Nat.cast_ofNat] at hRic
  simpa only [one_mul] using hRic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.ricciTensor_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.ricciTensor_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.ricciTensor_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.ricciTensor_zero

theorem leastUpperRicciAt_zero :
    leastUpperRicciAt metric (0 : E3) = 1 / 2 := by
  obtain ⟨v, hmin, _hminimal⟩ :=
    exists_unitSphere_minimizer_upperRicciRayleighAt metric (0 : E3)
  have hv : (v : E3) ≠ 0 :=
    Metric.ne_of_mem_sphere v.property one_ne_zero
  have hd : metric.inner 0 (v : E3) (v : E3) ≠ 0 :=
    ne_of_gt (metric.pos 0 v.val hv)
  rw [hmin]
  unfold upperRicciRayleighAt
  rw [metricScalarAt_zero, ricciTensor_zero]
  field_simp [hd]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.leastUpperRicciAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.leastUpperRicciAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.leastUpperRicciAt_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leastUpperRicciAt_zero

end DifferentialGeometry.PDE.RicciFlow.StandardCap
