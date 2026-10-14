import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (K T : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hcarrier : _root_.Set.Icc (T - b ^ 2) T ⊆ D.carrier)
    (hRm : ∀ t ∈ _root_.Set.Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (p : M) (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost S T p (alpha b) (b ^ 2) ≤
      lCost S T p (alpha a) (a ^ 2) + lRegularizedAction S T alpha a b := by
  have hb : 0 < b := ha.trans hab
  by_contra hnot
  have hlt : lCost S T p (alpha a) (a ^ 2) <
      lCost S T p (alpha b) (b ^ 2) - lRegularizedAction S T alpha a b := by
    linarith
  obtain ⟨beta, hbeta, hbeta0, hbetaa, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T p (alpha a)
      (a ^ 2) (sq_pos_of_pos ha) _ hlt
  rw [Real.sqrt_sq ha.le] at hbetaa hact
  have hclock : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply hcarrier
    exact ⟨sub_le_sub_left ((sq_le_sq₀ hs.1 hb.le).mpr hs.2) T,
      sub_le_self T (sq_nonneg s)⟩
  have hjoin := lCost_le_join_on_carrier_of_bounded_rm S hS T b ha hab
    beta alpha hbeta.contMDiffOn halpha.contMDiffOn hbetaa hclock ⟨K, hRm⟩
  rw [hbeta0] at hjoin
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier

end DifferentialGeometry.PDE.RicciFlow.Perelman
