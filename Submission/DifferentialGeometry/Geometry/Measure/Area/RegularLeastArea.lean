import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastAreaAnnulus
import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastAreaComponent
import Submission.DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds
import Submission.DifferentialGeometry.Topology.LoopSpace.RegularContractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M]



def regularContractibleToLipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularContractibleLoop E M) : lipschitzContractibleLoop g :=
  ⟨regularContractibleLoopInclusion γ, regularLoop_riemannian_lipschitz g γ.val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularContractibleToLipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularContractibleToLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularContractibleToLipschitz ``Submission.DifferentialGeometry.Geometry.regularContractibleToLipschitz



def regularLeastArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : regularContractibleLoop E M) : ℝ :=
  leastSpanningArea g (regularContractibleToLipschitz g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularLeastArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularLeastArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularLeastArea ``Submission.DifferentialGeometry.Geometry.regularLeastArea

theorem regularLeastArea_nonneg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : regularContractibleLoop E M) :
    0 ≤ regularLeastArea g γ :=
  leastSpanningArea_nonneg_of_nullhomotopic g (regularContractibleToLipschitz g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularLeastArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularLeastArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularLeastArea_nonneg ``Submission.DifferentialGeometry.Geometry.regularLeastArea_nonneg

theorem regularLeastArea_constant [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    regularLeastArea g (regularContractibleLoopConst q) = 0 := by
  have heq : regularContractibleToLipschitz g (regularContractibleLoopConst q) =
      constantLipschitzContractibleLoop g q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [regularLeastArea, heq, leastSpanningArea_constant]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularLeastArea_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularLeastArea_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularLeastArea_constant ``Submission.DifferentialGeometry.Geometry.regularLeastArea_constant

end DifferentialGeometry.Geometry
