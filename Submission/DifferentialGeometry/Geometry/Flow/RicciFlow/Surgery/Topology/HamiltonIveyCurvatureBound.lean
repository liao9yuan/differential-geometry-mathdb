import Submission.DifferentialGeometry.Geometry.Curvature.HamiltonIveyRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import Submission.DifferentialGeometry.Geometry.Curvature.TraceNormalizedOperator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

theorem sqrt_normSq0S_le_of_fixedHamiltonIveyRegion
    (g : SmoothRiemannianMetric ThreeModel M) (x : M)
    {a₀ a B : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (hfixed : InFixedHamiltonIveyRegion g a x) (hscalar : metricScalarAt g x ≤ B) :
    Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      2 * Real.sqrt 3 * (_root_.Max.max B 0 / 2 + _root_.Max.max B (Real.exp 4 / a₀)) := by
  obtain ⟨e, he⟩ := exists_orthonormalBasisAt g x (by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace])
  let T := metricAlgebraicCurvatureTensorAt g x
  have hneg : -(2 * leastCurvatureOperatorEigenvalueAt g x T) ≤
      max B (Real.exp 4 / a₀) :=
    neg_le_max_of_mem_fixedHamiltonIveyRegion ha₀ ha
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mp hfixed) hscalar
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin g x e he T] at hneg
  have htrace : metricScalarAt g x = 2 * ∑ i : Fin 3, orderedSectionalCurvaturesAt x e T i := by
    have h := trace_traceNormalizedCurvatureOperatorMatrixAt g x e he
    rw [DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorMatrixAt,
      Matrix.trace_smul,
      curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt] at h
    exact h.symm
  rw [Fin.sum_univ_three] at htrace
  have hanti := orderedSectionalCurvaturesAt_antitone x e T
  have hzero : 0 ≤ _root_.Max.max B (Real.exp 4 / a₀) :=
    (div_pos (Real.exp_pos 4) ha₀).le.trans (le_max_right _ _)
  have hB : 0 ≤ _root_.Max.max B 0 := le_max_right _ _
  have hlower (i : Fin 3) :
      -_root_.Max.max B (Real.exp 4 / a₀) / 2 ≤ orderedSectionalCurvaturesAt x e T i := by
    have hi := hanti (show i ≤ 2 by omega)
    linarith
  have hnorm : ∀ i : Fin 3, |orderedSectionalCurvaturesAt x e T i| ≤
      max B 0 / 2 + _root_.Max.max B (Real.exp 4 / a₀) := by
    intro i
    have hi := hanti (Fin.zero_le i)
    have h1 := hlower 1
    have h2 := hlower 2
    have hi0 := hlower i
    have hSB := hscalar.trans (le_max_left B 0)
    rw [abs_le]
    constructor <;> linarith
  exact sqrt_normSq0S_le_of_abs_orderedSectionalCurvaturesAt_le g x e he T hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sqrt_normSq0S_le_of_fixedHamiltonIveyRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sqrt_normSq0S_le_of_fixedHamiltonIveyRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sqrt_normSq0S_le_of_fixedHamiltonIveyRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sqrt_normSq0S_le_of_fixedHamiltonIveyRegion

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
