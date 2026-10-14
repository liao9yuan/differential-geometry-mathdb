import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.L2BanachIsomorphism
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.ChartFrameNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.PouNormChartComp
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.AssemblePouIso

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Analysis.Sobolev.HebeyBlock

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_sobolev_intrinsic_nabla_equivalence_tensors_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
  assemble_pou_h1_iso_intrinsic_h1 (I := I) (M := M) g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chart_sobolev_intrinsic_nabla_equivalence_tensors_h1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chart_sobolev_intrinsic_nabla_equivalence_tensors_h1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chart_sobolev_intrinsic_nabla_equivalence_tensors_h1 ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chart_sobolev_intrinsic_nabla_equivalence_tensors_h1

end DifferentialGeometry.Analysis.Sobolev.HebeyBlock
