import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedChartPullback
import Submission.DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import Submission.DifferentialGeometry.Topology.Manifold.SphereLinearIsometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

def connectedBallChartTransport : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold),
    Manifold.BallChartTransport c.toBallChart c'.toBallChart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedBallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedBallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedBallChartTransport ``Submission.DifferentialGeometry.Topology.connectedBallChartTransport

theorem orientedBallChartTransport_of_ballChartTransport
    (h : connectedBallChartTransport.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    (c c' : OrientedBallChart M.toClosedOrientedManifold) :
    OrientedBallChartTransport c c' := by
  obtain ⟨Φ, hΦ⟩ := h M c c'
  have h0c : (0 : E3) ∈ c.toBallChart.chart.source :=
    c.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h0c' : (0 : E3) ∈ c'.toBallChart.chart.source :=
    c'.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hEq : (fun x : E3 => Φ (c.toBallChart.chart x)) =ᶠ[𝓝 (0 : E3)]
      (fun x : E3 => c'.toBallChart.chart x) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : E3) (by norm_num)) hΦ
  have hchain : mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => Φ (c.toBallChart.chart x)) 0
      = mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
        ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.toBallChart.chart x) 0 :=
    mfderiv_comp (x := (0 : E3)) (f := fun x : E3 => c.toBallChart.chart x) (g := ⇑Φ)
      (Φ.mdifferentiable (by simp) _)
      (PartialDiffeomorph.mdifferentiableAt c.toBallChart.chart (by simp) h0c)
  have hkey : mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
      ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c.toBallChart.chart x) 0
      = mfderiv (𝓡 3) (𝓡 3) (fun x : E3 => c'.toBallChart.chart x) 0 := by
    rw [← hchain, Filter.EventuallyEq.mfderiv_eq hEq]
  have h3 : (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv.trans
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      = (OrientationAssembly.chartTangentEquiv c' h0c').toLinearEquiv := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact DFunLike.congr_fun hkey v
  refine ⟨Φ, ?_, hΦ⟩
  refine Diffeomorph.preservesOrientation_of_eq_at Φ M.orientation M.orientation
    (c.toBallChart.chart 0) ?_
  rw [hΦ 0 (Metric.mem_closedBall_self (by norm_num))]
  erw [OrientationAssembly.orientation_eq_map_chartTangentEquiv c h0c,
    OrientationAssembly.orientation_map_map_trans
      (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      (OrientationAssembly.stdOrientation 0),
    h3]
  exact (OrientationAssembly.orientation_eq_map_chartTangentEquiv c' h0c').symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartTransport_of_ballChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartTransport_of_ballChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartTransport_of_ballChartTransport ``Submission.DifferentialGeometry.Topology.orientedBallChartTransport_of_ballChartTransport

theorem orientedBallChartTransport_all_of_ballChartTransport
    (h : connectedBallChartTransport.{u}) :
    ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
      (c c' : OrientedBallChart M.toClosedOrientedManifold), OrientedBallChartTransport c c' :=
  fun M c c' => orientedBallChartTransport_of_ballChartTransport h M c c'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartTransport_all_of_ballChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartTransport_all_of_ballChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartTransport_all_of_ballChartTransport ``Submission.DifferentialGeometry.Topology.orientedBallChartTransport_all_of_ballChartTransport

theorem selfTransport_of_connectedBallChartTransport (h : connectedBallChartTransport.{u}) :
    SelfTransport.{u} :=
  fun {M} c c' => orientedBallChartTransport_of_ballChartTransport h M c c'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.selfTransport_of_connectedBallChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.selfTransport_of_connectedBallChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.selfTransport_of_connectedBallChartTransport ``Submission.DifferentialGeometry.Topology.selfTransport_of_connectedBallChartTransport

def connectedSumUnorientedTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (connectedSum X Y).Carrier
      (connectedSum X' Y').Carrier ∞)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumUnorientedTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumUnorientedTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumUnorientedTransport ``Submission.DifferentialGeometry.Topology.connectedSumUnorientedTransport

def connectedSumOrientedTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      X.toClosedOrientedManifold X'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      Y.toClosedOrientedManifold Y'.toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum X' Y').toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOrientedTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOrientedTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOrientedTransport ``Submission.DifferentialGeometry.Topology.connectedSumOrientedTransport

def connectedSumOrientedChartTransport : Prop :=
  ∀ (X X' Y Y' : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart X.toClosedOrientedManifold)
    (c' : OrientedBallChart X'.toClosedOrientedManifold)
    (d : OrientedBallChart Y.toClosedOrientedManifold)
    (d' : OrientedBallChart Y'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (Φ : X.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ X'.Carrier)
    (Ψ : Y.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Y'.Carrier),
    Φ.preservesOrientation X.orientation X'.orientation →
    Ψ.preservesOrientation Y.orientation Y'.orientation →
    (∀ x ∈ Metric.closedBall (0 : E3) 2,
      Φ (c.toBallChart.chart x) = c'.toBallChart.chart x) →
    (∀ x ∈ Metric.closedBall (0 : E3) 2,
      Ψ (d.toBallChart.chart x) = d'.toBallChart.chart x) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum X Y c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum X' Y' c' d' a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOrientedChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOrientedChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOrientedChartTransport ``Submission.DifferentialGeometry.Topology.connectedSumOrientedChartTransport

def sphereUnitLaws : Prop :=
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold
      X.toClosedOrientedManifold)) ∧
  (∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold
      X.toClosedOrientedManifold))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereUnitLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereUnitLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereUnitLaws ``Submission.DifferentialGeometry.Topology.sphereUnitLaws

def connectedSumCommutative : Prop :=
  ∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).toClosedOrientedManifold
      (connectedSum Y X).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumCommutative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumCommutative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumCommutative ``Submission.DifferentialGeometry.Topology.connectedSumCommutative

def connectedSumAssociative : Prop :=
  ∀ X Y Z : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum (connectedSum X Y) Z).toClosedOrientedManifold
      (connectedSum X (connectedSum Y Z)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumAssociative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumAssociative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumAssociative ``Submission.DifferentialGeometry.Topology.connectedSumAssociative

def connectedSumOpposite : Prop :=
  ∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum X Y).opposite.toClosedOrientedManifold
      (connectedSum X.opposite Y.opposite).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOpposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOpposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOpposite ``Submission.DifferentialGeometry.Topology.connectedSumOpposite

theorem connectedSum_unorientedTransport_of_selfTransport
    (h : SelfTransport.{u}) : connectedSumUnorientedTransport.{u} := by
  intro X X' Y Y' hX hY
  obtain ⟨Φ, hΦo⟩ := hX
  obtain ⟨Ψ, hΨo⟩ := hY
  obtain ⟨c, hc⟩ := orientedBallChartPullback Φ (orientedBallChart X') hΦo
  obtain ⟨d, hd⟩ := orientedBallChartPullback Ψ (orientedBallChart Y') hΨo
  obtain ⟨f⟩ := connectedSum_diffeomorph_of_ballChartTransport_left Y X X' c
    (orientedBallChart X') (h (orientedBallChart X) c).toBallChartTransport
    (Manifold.BallChartTransport.refl _) Φ hc
  obtain ⟨g⟩ := connectedSum_diffeomorph_of_ballChartTransport X' Y Y' d
    (orientedBallChart Y') (h (orientedBallChart Y) d).toBallChartTransport
    (Manifold.BallChartTransport.refl _) Ψ hd
  exact ⟨f.trans g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_unorientedTransport_of_selfTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_unorientedTransport_of_selfTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_unorientedTransport_of_selfTransport ``Submission.DifferentialGeometry.Topology.connectedSum_unorientedTransport_of_selfTransport

theorem connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport
    (hself : SelfTransport.{u}) (h : connectedSumOrientedChartTransport.{u}) :
    connectedSumOrientedTransport.{u} := by
  intro X X' Y Y' hX hY
  obtain ⟨Φ, hΦo⟩ := hX
  obtain ⟨Ψ, hΨo⟩ := hY
  obtain ⟨c, hc⟩ := orientedBallChartPullback Φ (orientedBallChart X') hΦo
  obtain ⟨d, hd⟩ := orientedBallChartPullback Ψ (orientedBallChart Y') hΨo
  obtain ⟨Φc, hΦco, hΦc⟩ := hself (orientedBallChart X) c
  obtain ⟨Φd, hΦdo, hΦd⟩ := hself (orientedBallChart Y) d
  obtain ⟨f⟩ := h X X Y Y (orientedBallChart X) c (orientedBallChart Y) (orientedBallChart Y)
    boundaryAttachment Φc (Diffeomorph.refl (𝓡 3) Y.Carrier ∞) hΦco
    (Diffeomorph.preservesOrientation_refl Y.orientation) hΦc (fun _ _ => rfl)
  obtain ⟨f'⟩ := h X X Y Y c c (orientedBallChart Y) d boundaryAttachment
    (Diffeomorph.refl (𝓡 3) X.Carrier ∞) Φd
    (Diffeomorph.preservesOrientation_refl X.orientation) hΦdo (fun _ _ => rfl) hΦd
  obtain ⟨g⟩ := h X X' Y Y' c (orientedBallChart X') d (orientedBallChart Y')
    boundaryAttachment Φ Ψ hΦo hΨo hc hd
  exact ⟨f.trans (f'.trans g)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport ``Submission.DifferentialGeometry.Topology.connectedSum_orientedTransport_of_selfTransport_and_orientedChartTransport

theorem binaryConnectedSumLaws_of_unit_assoc_comm_transport (hunit : sphereUnitLaws.{u})
    (hcomm : connectedSumCommutative.{u}) (hassoc : connectedSumAssociative.{u})
    (htransport : connectedSumOrientedTransport.{u}) : binaryConnectedSumLaws.{u} :=
  ⟨hunit.1, hunit.2, hcomm, hassoc, htransport⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.binaryConnectedSumLaws_of_unit_assoc_comm_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.binaryConnectedSumLaws_of_unit_assoc_comm_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.binaryConnectedSumLaws_of_unit_assoc_comm_transport ``Submission.DifferentialGeometry.Topology.binaryConnectedSumLaws_of_unit_assoc_comm_transport

theorem connectedSum_sphere_left_of_binaryConnectedSumLaws
    (h : binaryConnectedSumLaws.{u}) (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} M).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  (connectedSumLaws_of_binaryConnectedSumLaws h).2.1 M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_sphere_left_of_binaryConnectedSumLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_sphere_left_of_binaryConnectedSumLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_sphere_left_of_binaryConnectedSumLaws ``Submission.DifferentialGeometry.Topology.connectedSum_sphere_left_of_binaryConnectedSumLaws

theorem connectedSum_sphere_right_of_binaryConnectedSumLaws
    (h : binaryConnectedSumLaws.{u}) (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  (connectedSumLaws_of_binaryConnectedSumLaws h).1 M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_sphere_right_of_binaryConnectedSumLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_sphere_right_of_binaryConnectedSumLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_sphere_right_of_binaryConnectedSumLaws ``Submission.DifferentialGeometry.Topology.connectedSum_sphere_right_of_binaryConnectedSumLaws

theorem finiteConnectedSum_append_of_binaryConnectedSumLaws (h : binaryConnectedSumLaws.{u})
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_connectedSumLaws (connectedSumLaws_of_binaryConnectedSumLaws h) L K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_append_of_binaryConnectedSumLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_append_of_binaryConnectedSumLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_append_of_binaryConnectedSumLaws ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_append_of_binaryConnectedSumLaws

theorem finiteConnectedSum_perm_of_binaryConnectedSumLaws (h : binaryConnectedSumLaws.{u})
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_connectedSumLaws (connectedSumLaws_of_binaryConnectedSumLaws h) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_perm_of_binaryConnectedSumLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_perm_of_binaryConnectedSumLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_perm_of_binaryConnectedSumLaws ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_perm_of_binaryConnectedSumLaws

theorem finiteConnectedSum_opposite_of_binaryConnectedSumLaws (h : binaryConnectedSumLaws.{u})
    (hopp : connectedSumOpposite.{u}) (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
  finiteConnectedSum_opposite_of_connectedSumLaws
    (connectedSumLaws_of_binaryConnectedSumLaws h) hopp
    standardThreeSphereLift_orientationReversing_diffeomorph L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_opposite_of_binaryConnectedSumLaws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_opposite_of_binaryConnectedSumLaws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_opposite_of_binaryConnectedSumLaws ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_opposite_of_binaryConnectedSumLaws

theorem finiteConnectedSum_congr_of_relativeConnectedSumTransport
    (h : connectedSumTransport.{u, v, u, v})
    {L : List (ConnectedClosedOrientedManifold.{u} 3)}
    {K : List (ConnectedClosedOrientedManifold.{v} 3)}
    (hf : List.Forall₂ (fun (M : ConnectedClosedOrientedManifold.{u} 3)
      (N : ConnectedClosedOrientedManifold.{v} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumTransport h hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_congr_of_relativeConnectedSumTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_congr_of_relativeConnectedSumTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_congr_of_relativeConnectedSumTransport ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_congr_of_relativeConnectedSumTransport

theorem finiteConnectedSum_laws_of_unit_assoc_comm_transport (hunit : sphereUnitLaws.{u})
    (hcomm : connectedSumCommutative.{u}) (hassoc : connectedSumAssociative.{u})
    (htransport : connectedSumOrientedTransport.{u}) (hopp : connectedSumOpposite.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    (Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
        M.toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (connectedSum standardThreeSphereLift.{u} M).toClosedOrientedManifold
        M.toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
        (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold
        (finiteConnectedSum K).toClosedOrientedManifold) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).opposite.toClosedOrientedManifold
        (finiteConnectedSum (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold)) :=
  ⟨connectedSum_sphere_right_of_binaryConnectedSumLaws hbin M,
    connectedSum_sphere_left_of_binaryConnectedSumLaws hbin M,
    finiteConnectedSum_append_of_binaryConnectedSumLaws hbin L K,
    finiteConnectedSum_perm_of_binaryConnectedSumLaws hbin hp,
    finiteConnectedSum_opposite_of_binaryConnectedSumLaws hbin hopp L⟩
where hbin := binaryConnectedSumLaws_of_unit_assoc_comm_transport hunit hcomm hassoc htransport

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_laws_of_unit_assoc_comm_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_laws_of_unit_assoc_comm_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_laws_of_unit_assoc_comm_transport ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_laws_of_unit_assoc_comm_transport

end DifferentialGeometry.Topology
