import Submission.DifferentialGeometry.Geometry.Comparison.Volume.CompactSmallBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

theorem riemannianBallOf_volume_eq (A : InitialIdentification P g H)
    (x : P.Carrier) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x r) =
      riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0)
        (riemannianBallOf (H.initialMetric 0) (A.map x) r) := by
  have hmetric : Diffeomorph.pullbackMetricCross (H.initialMetric 0) A.map = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact A.metric_eq y v w
  simpa only [hmetric] using
    Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross
      (H.initialMetric 0) A.map x r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_eq

private theorem riemannianBallOf_volume_lower_bound (A : InitialIdentification P g H)
    {κ ρ : ℝ}
    (hvolume : ∀ x : P.Carrier, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x r)) :
    ∀ x : (H.stage 0).Carrier, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0)
          (riemannianBallOf (H.initialMetric 0) x r) := by
  intro x r hr hρ
  obtain ⟨y, rfl⟩ := A.map.surjective x
  exact (hvolume y r hr hρ).trans_eq (A.riemannianBallOf_volume_eq y r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_lower_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.riemannianBallOf_volume_lower_bound target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u

theorem exists_initial_small_ball_volume_lower_bound
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        ∀ x : (H.stage 0).Carrier, ∀ r : ℝ, 0 < r → r ≤ ρ →
          ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0)
              (riemannianBallOf (H.initialMetric 0) x r) := by
  obtain ⟨ρ, κ, hρ, hκ, hvolume⟩ :=
    Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound g
  refine ⟨ρ, κ, hρ, hκ, ?_⟩
  intro H A
  apply A.riemannianBallOf_volume_lower_bound
  intro x r hr hrρ
  simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hvolume x r hr hrρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initial_small_ball_volume_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initial_small_ball_volume_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initial_small_ball_volume_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initial_small_ball_volume_lower_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_initial_ball_volume_lower_bound_of_isometry
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ ρ κ : ℝ, 0 < τ ∧ 0 < ρ ∧ 0 < κ ∧
      ∀ {Q : OrientedThreeStage.{u}} {s : ℝ} (G : Q.IncomingSlab 0 s)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
        (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
          (G.flow.base.metric 0).inner (φ x)
            (mfderiv ThreeModel ThreeModel φ x v)
            (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
        ∀ t ∈ _root_.Set.Ico (0 : ℝ) s, t ≤ τ → ∀ x : Q.Carrier,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure ThreeModel Q.Carrier (G.flow.base.metric t)
                (riemannianBallOf (G.flow.base.metric t) x r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_ball_volume_lower_bound g
  refine ⟨τ, ρ, κ, hτ, hρ, hκ, ?_⟩
  intro Q s G φ hmetric t ht htτ x r hr hrρ
  let S := G.flow.pullback φ
  have hS : IsSolutionOn S := G.equation.pullback G.flow φ
  have hinit : S.base.metric 0 = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  have hslab : _root_.Set.Icc (0 : ℝ) t ⊆ (RealTimeInterval.closedOpen 0 s G.lt).carrier :=
    fun u hu => ⟨hu.1, hu.2.trans_lt ht.2⟩
  have hregular : _root_.Set.Ioo (0 : ℝ) t ⊆ (RealTimeInterval.closedOpen 0 s G.lt).regular :=
    fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hgram := fun (x₀ : P.Carrier) (i j : Fin (Module.finrank ℝ ThreeSpace)) =>
    (chartGramMatrix_joint_contMDiffOn_of_pullback G.flow.base.metric (_root_.Set.Ico (0 : ℝ) s)
      G.smoothUpTo.jointContMDiffOn S.base.metric φ φ.contMDiff
      (fun u _ y v w => Diffeomorph.pullbackMetricCross_inner _ φ y v w) x₀ i j).mono
      (_root_.Set.prod_mono hslab subset_rfl)
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hv := hbound S hS hinit hslab hregular hgram t ⟨ht.1, le_rfl⟩ htτ y r hr hrρ
  have hvolume := Perelman.KappaSolutions.riemannianBallOf_volume_pullbackMetricCross
    (G.flow.base.metric t) φ y r
  apply (show ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
    riemannianVolumeMeasure ThreeModel P.Carrier (S.base.metric t)
      (riemannianBallOf (S.base.metric t) y r) from by
      simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hv).trans_eq
  exact hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound_of_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound_of_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound_of_isometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound_of_isometry

theorem exists_uniform_initial_ball_volume_lower_bound
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ ρ κ : ℝ, 0 < τ ∧ 0 < ρ ∧ 0 < κ ∧
      ∀ {s : ℝ} (G : P.IncomingSlab 0 s), G.flow.base.metric 0 = g →
        ∀ t ∈ _root_.Set.Ico (0 : ℝ) s, t ≤ τ → ∀ x : P.Carrier,
          ∀ r : ℝ, 0 < r → r ≤ ρ →
            ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
              riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t)
                (riemannianBallOf (G.flow.base.metric t) x r) := by
  obtain ⟨τ, ρ, κ, hτ, hρ, hκ, hbound⟩ :=
    exists_uniform_initial_ball_volume_lower_bound_of_isometry P g
  refine ⟨τ, ρ, κ, hτ, hρ, hκ, ?_⟩
  intro s G hinit
  apply hbound G (Diffeomorph.refl ThreeModel P.Carrier ∞)
  intro x v w
  change (G.flow.base.metric 0).inner x
    (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x v)
    (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x w) = g.inner x v w
  rw [mfderiv_id, hinit]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_initial_ball_volume_lower_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
