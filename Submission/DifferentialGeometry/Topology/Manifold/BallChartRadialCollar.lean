import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplementRadialCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "S" => Metric.sphere (0 : V) 1
local notation "IC" => ModelWithCorners.prod (𝓡 n) 𝓘(ℝ, ℝ)

private instance _root_.Submission.DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat : Fact (Module.finrank ℝ V = n + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat target :: scope.openDecls } }

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace H' P]

theorem exists_outer_ball_complement_radial_collar (c : BallChart (n + 1) I M)
    (F : PartialDiffeomorph I J M P ∞)
    (hF : (c.chart '' _root_.Metric.ball (0 : V) (5 / 4))ᶜ ⊆ F.source) :
    ∃ T : PartialDiffeomorph IC J (S × ℝ) P ∞,
      _root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ T.source ∧
      (∀ q : S × ℝ, T q = F (c.chart ((7 / 4 - q.2 / 2) • (q.1 : V)))) ∧
      (∀ z : S, T (z, 1) = F (c.chart ((5 / 4 : ℝ) • (z : V)))) ∧
      T '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ F '' (c.chart '' _root_.Metric.ball (0 : V) (5 / 4))ᶜ := by
  let A :=  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := V)
    (Units.mk0 (5 / 4 : ℝ) (by norm_num))).toDiffeomorph
  let b := A.toPartialDiffeomorph.trans c.chart
  have hb (x : V) : b x = c.chart ((5 / 4 : ℝ) • x) := rfl
  have himage : b '' _root_.Metric.ball (0 : V) 1 = c.chart '' _root_.Metric.ball (0 : V) (5 / 4) := by
    change (c.chart ∘ fun x : V => (5 / 4 : ℝ) • x) '' _root_.Metric.ball 0 1 = _
    rw [Set.image_comp, Metric.smul_image_ball (by norm_num : (5 / 4 : ℝ) ≠ 0)]
    norm_num
  have hsource : _root_.Metric.closedBall (0 : V) (7 / 5) ⊆ b.source := by
    intro x hx
    refine ⟨mem_univ _, c.closedBall_subset_source ?_⟩
    change (5 / 4 : ℝ) • x ∈ _root_.Metric.closedBall (0 : V) 2
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    norm_num
    have hn := mem_closedBall_zero_iff.mp hx
    linarith
  let v : S := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hR : (1 : ℝ) < 7 / 5 := by norm_num
  let T := Manifold.ballComplementRadialCollar (n := n) b F v (7 / 5) hR.ne'
  have hT (q : S × ℝ) : T q = F (c.chart ((7 / 4 - q.2 / 2) • (q.1 : V))) := by
    change F (b (((7 / 5 : ℝ) + (1 - 7 / 5) * q.2) • (q.1 : V))) = _
    rw [hb, smul_smul]
    have heq : (5 / 4 : ℝ) * (7 / 5 + (1 - 7 / 5) * q.2) = 7 / 4 - q.2 / 2 := by ring
    rw [heq]
  refine ⟨T, Manifold.unit_slab_subset_ballComplementRadialCollar_source b F v hR hsource
    (by rw [himage]; exact hF), hT, ?_, ?_⟩
  · intro z
    rw [hT]
    norm_num
  · rw [← himage]
    exact Manifold.ballComplementRadialCollar_image_unit_slab_subset b F v hR hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.exists_outer_ball_complement_radial_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.exists_outer_ball_complement_radial_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.exists_outer_ball_complement_radial_collar ``Submission.DifferentialGeometry.Topology.BallChart.exists_outer_ball_complement_radial_collar

end DifferentialGeometry.Topology.BallChart
