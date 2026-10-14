import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace TangentRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
private lemma continuous_g_inner
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x))) :
    Continuous (fun b : M => g.inner b (v b) (w b)) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := Continuous.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro b
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.TangentRiemannian.continuous_g_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.TangentRiemannian.continuous_g_inner target :: scope.openDecls } }

end TangentRiemannian
end Tensor
end DifferentialGeometry

namespace TangentBundle


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem continuous_g_inner_of_smooth_sections
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (X b) (Y b)) := by
  have hX : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (X x)) :=
    X.contMDiff.continuous
  have hY : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (Y x)) :=
    Y.contMDiff.continuous
  exact DifferentialGeometry.Tensor.TangentRiemannian.continuous_g_inner
    (I := I) (M := M) g hX hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TangentBundle.continuous_g_inner_of_smooth_sections then
    throwError "Refusing to shadow existing declaration TangentBundle.continuous_g_inner_of_smooth_sections"
  Lean.modifyEnv fun env => Lean.addAlias env `TangentBundle.continuous_g_inner_of_smooth_sections ``Submission.TangentBundle.continuous_g_inner_of_smooth_sections

end TangentBundle
