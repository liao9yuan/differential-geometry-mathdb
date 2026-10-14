import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def HasSmoothCheegerGromovLimit (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D, exists subseq : Nat -> Nat,
    StrictMono subseq /\
      Nonempty.{max (max uE uH) u + 1} (SmoothCGHConverges (I := I) X L subseq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasSmoothCheegerGromovLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasSmoothCheegerGromovLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasSmoothCheegerGromovLimit ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasSmoothCheegerGromovLimit

end CheegerGromovCompactness
end DifferentialGeometry
