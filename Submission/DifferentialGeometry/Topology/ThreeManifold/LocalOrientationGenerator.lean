import Submission.DifferentialGeometry.Topology.Homology.EuclideanSimplexGenerator
import Submission.DifferentialGeometry.Topology.ThreeManifold.LocalOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem localOrientationClass_generator (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  localOrientationClass_generator_of_euclideanStandardSimplex o x
    DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localOrientationClass_generator

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
