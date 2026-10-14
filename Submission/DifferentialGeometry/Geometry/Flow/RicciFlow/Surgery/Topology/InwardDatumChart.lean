import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import Submission.DifferentialGeometry.Geometry.Neck.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
universe u
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

theorem oriented_rotatedDatum_chart_eq_of_inward_matching
    (N : NormalizedNeck g δ k) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (horn : NeckCylinder → M)
    (β : Sphere 2 ≃ Sphere 2) (a γ : ℝ) (hγ : γ ^ 2 = 1)
    (hsign : (N.rotatedDatum e he side).retainedSign = γ)
    (hmatch : ∀ (y : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
      ∀ hs : (β y, γ * s) ∈ neckBuffer δ,
        horn (y, a - s) = N.chart ⟨(β y, γ * s), hs⟩)
    (q : bufferedCylinder δ) (hq : q ∈ controlledCylinder δ) :
    (N.rotatedDatum e he side).oriented.map q =
      horn (β.symm (sphereDiffeo (n := 2) e q.val.1), a - q.val.2) := by
  have hqs : |q.val.2| ≤ δ⁻¹ := abs_le.mpr hq
  have hmem : (β (β.symm (sphereDiffeo (n := 2) e q.val.1)), γ * q.val.2) ∈ neckBuffer δ := by
    have hi := N.delta_pos
    change -δ⁻¹ - 1 < γ * q.val.2 ∧ γ * q.val.2 < δ⁻¹ + 1
    rcases sq_eq_one_iff.mp hγ with rfl | rfl <;> constructor <;> linarith [hq.1, hq.2]
  rw [hmatch _ _ hqs hmem]
  rw [normalizedDatum.oriented_map, rotatedDatum_map]
  apply congrArg N.chart
  apply Subtype.ext
  rw [bufferedCylinderRotation_apply, bufferedCylinderOrientation_apply, hsign, β.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.oriented_rotatedDatum_chart_eq_of_inward_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.oriented_rotatedDatum_chart_eq_of_inward_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.oriented_rotatedDatum_chart_eq_of_inward_matching ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.oriented_rotatedDatum_chart_eq_of_inward_matching

theorem exists_side_of_axial_sign (γ : ℝ) (hγ : γ ^ 2 = 1) :
    ∃ side : Bool, (if side then (1 : ℝ) else -1) = γ := by
  rcases sq_eq_one_iff.mp hγ with h | h
  · exact ⟨true, h.symm⟩
  · exact ⟨false, h.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_side_of_axial_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_side_of_axial_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_side_of_axial_sign ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_side_of_axial_sign

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
