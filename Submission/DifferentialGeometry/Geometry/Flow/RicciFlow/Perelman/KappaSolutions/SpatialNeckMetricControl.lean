import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

def spatialNeckControlEpsilon : ℝ := (100 * (1 + Real.pi))⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon

theorem spatialNeckControlEpsilon_pos : 0 < spatialNeckControlEpsilon := by
  dsimp only [spatialNeckControlEpsilon]
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_pos


theorem spatialNeckControlEpsilon_inverse_gap {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) :
    5 * Real.pi + 12 * Real.pi < epsilon⁻¹ := by
  have hden : 0 < 100 * (1 + Real.pi) := by positivity
  have hprod : epsilon * (100 * (1 + Real.pi)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [spatialNeckControlEpsilon, inv_eq_one_div] using hsmall
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ hepsilon).mpr
  nlinarith [mul_pos hepsilon Real.pi_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_inverse_gap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_inverse_gap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_inverse_gap ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_inverse_gap

private theorem spatialNeckControlEpsilon_le : spatialNeckControlEpsilon ≤ 23 / 144 := by
  have hden : 0 < 100 * (1 + Real.pi) := by positivity
  rw [spatialNeckControlEpsilon, inv_eq_one_div, div_le_iff₀ hden]
  nlinarith [Real.pi_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlEpsilon_le target :: scope.openDecls } }

universe u uE uH

private local instance spatialNeckControlSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlSphereDimension target :: scope.openDecls } }

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance spatialNeckControlC1 : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckControlC1 target :: scope.openDecls } }

theorem SpatialNeckWitness.normalized_inner_bilipschitz
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : x ∈ spatialNeckClosedCore epsilon)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
    (11 / 12 : ℝ) ^ 2 * gRef.inner x v v ≤
        ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v) ∧
      ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v) ≤
        (13 / 12 : ℝ) ^ 2 * gRef.inner x v v := by
  let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
  have href : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gRef.pos x v hv).le
  have hnorm : metricDerivNorm (I := SpatialNeckCylinderModel) 0
      W.normalizedMetric gRef gRef x ≤ 23 / 144 :=
    (W.metricDerivNorm_lt 0 (Nat.zero_le _) x hx).le.trans
      (hsmall.trans spatialNeckControlEpsilon_le)
  have herror := metricDifference_abs_le W.normalizedMetric gRef gRef x v v
  rw [mul_assoc, ← sq, Real.sq_sqrt href] at herror
  have hbound := herror.trans (mul_le_mul_of_nonneg_right hnorm href)
  obtain ⟨hlower, hupper⟩ := abs_le.mp hbound
  rw [W.normalized_inner] at hlower hupper
  change (11 / 12 : ℝ) ^ 2 * gRef.inner x v v ≤ _ ∧
    _ ≤ (13 / 12 : ℝ) ^ 2 * gRef.inner x v v
  constructor <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalized_inner_bilipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalized_inner_bilipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalized_inner_bilipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalized_inner_bilipschitz

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
