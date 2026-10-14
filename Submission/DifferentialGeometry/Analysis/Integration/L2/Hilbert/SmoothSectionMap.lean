import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

namespace SmoothCcTensor

section SimpLemmas

variable [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


theorem toL2_zero :
    (toL2 (g := g) (r := r) (s := s)) 0 = 0 :=
  ContinuousLinearMap.map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_zero ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_zero


theorem toL2_add (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S + T) =
      (toL2 (g := g) (r := r) (s := s)) S +
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_add _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_add ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_add


theorem toL2_neg (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (-S) =
      -((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_neg _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_neg ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_neg


theorem toL2_sub (S T : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (S - T) =
      (toL2 (g := g) (r := r) (s := s)) S -
        (toL2 (g := g) (r := r) (s := s)) T :=
  ContinuousLinearMap.map_sub _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_sub ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_sub


theorem toL2_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s)) (c • S) =
      c • ((toL2 (g := g) (r := r) (s := s)) S) :=
  ContinuousLinearMap.map_smul _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_smul ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_smul

end SimpLemmas

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
