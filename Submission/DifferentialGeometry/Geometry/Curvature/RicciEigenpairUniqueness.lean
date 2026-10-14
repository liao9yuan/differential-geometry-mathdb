import Submission.DifferentialGeometry.Tensor.LinearAlgebra.OrientedUnitLine
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem least_ricci_eigenpair_eq_or_eq_neg
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (μ ν : ℝ) (v w : TangentSpace I x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hev : ricciSharp g x v = μ • v) (hew : ricciSharp g x w = ν • w)
    (hminv : ∀ z : TangentSpace I x, g.inner x z z = 1 → μ ≤ ricciTensor g x z z)
    (hminw : ∀ z : TangentSpace I x, g.inner x z z = 1 → ν ≤ ricciTensor g x z z)
    (hsimple : Module.End.eigenspace (ricciSharp g x).toLinearMap ν = Submodule.span ℝ {w}) :
    μ = ν ∧ (v = w ∨ v = -w) := by
  have hRayleigh (a : ℝ) (z : TangentSpace I x) (hz : g.inner x z z = 1)
      (he : ricciSharp g x z = a • z) : ricciTensor g x z z = a := by
    rw [← inner_ricciSharp, he, map_smul, smul_apply, hz]
    exact mul_one a
  have heval : μ = ν := le_antisymm
    ((hminv w hw).trans_eq (hRayleigh ν w hw hew))
    ((hminw v hv).trans_eq (hRayleigh μ v hv hev))
  refine ⟨heval, ?_⟩
  apply DifferentialGeometry.Analysis.eq_or_eq_neg_of_unit_of_mem_span
    (g.inner x).toBilinForm v w hv hw
  rw [← hsimple]
  exact Module.End.mem_eigenspace_iff.mpr (hev.trans (congrArg (fun a : ℝ ↦ a • v) heval))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_or_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_or_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_or_eq_neg ``Submission.DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_or_eq_neg

theorem least_ricci_eigenpair_eq_of_positive_functional
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M) (ℓ : TangentSpace I x →ₗ[ℝ] ℝ)
    (μ ν : ℝ) (v w : TangentSpace I x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hev : ricciSharp g x v = μ • v) (hew : ricciSharp g x w = ν • w)
    (hminv : ∀ z : TangentSpace I x, g.inner x z z = 1 → μ ≤ ricciTensor g x z z)
    (hminw : ∀ z : TangentSpace I x, g.inner x z z = 1 → ν ≤ ricciTensor g x z z)
    (hsimple : Module.End.eigenspace (ricciSharp g x).toLinearMap ν = Submodule.span ℝ {w})
    (hvpos : 0 < ℓ v) (hwpos : 0 < ℓ w) : μ = ν ∧ v = w := by
  obtain ⟨hμ, h | h⟩ :=
    least_ricci_eigenpair_eq_or_eq_neg g x μ ν v w hv hw hev hew hminv hminw hsimple
  · exact ⟨hμ, h⟩
  · rw [h, map_neg] at hvpos
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_of_positive_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_of_positive_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_of_positive_functional ``Submission.DifferentialGeometry.Geometry.Curvature.least_ricci_eigenpair_eq_of_positive_functional

end DifferentialGeometry.Geometry.Curvature
