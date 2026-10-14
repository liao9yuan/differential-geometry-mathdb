import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarking
import Submission.DifferentialGeometry.Topology.Manifold.BallChartTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E₃
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E₃ target :: scope.openDecls } }

namespace BallMarking

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I] (B B' : BallMarking M I)

def Transport : Prop :=
  ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
    ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2, Φ ((B.ball i).chart x) = (B'.ball i).chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.Transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.Transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.Transport ``Submission.DifferentialGeometry.Topology.BallMarking.Transport

def Isotopic : Prop :=
  ∃ H : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => H q.1 q.2) ∧
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier => (H q.1).symm q.2) ∧
    H 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ ∧
    ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2, H 1 ((B.ball i).chart x) = (B'.ball i).chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.Isotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.Isotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.Isotopic ``Submission.DifferentialGeometry.Topology.BallMarking.Isotopic

namespace Transport

theorem refl : B.Transport B :=
  ⟨Diffeomorph.refl (𝓡 3) M.Carrier ∞, fun _ _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.Transport.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.Transport.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.Transport.refl ``Submission.DifferentialGeometry.Topology.BallMarking.Transport.refl

end Transport

namespace Isotopic

theorem refl : B.Isotopic B :=
  ⟨fun _ => Diffeomorph.refl (𝓡 3) M.Carrier ∞, contMDiff_snd, contMDiff_snd, rfl,
    fun _ _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.Isotopic.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.Isotopic.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.Isotopic.refl ``Submission.DifferentialGeometry.Topology.BallMarking.Isotopic.refl

end Isotopic

theorem Isotopic.toTransport (h : B.Isotopic B') : B.Transport B' := by
  obtain ⟨H, -, -, -, hH⟩ := h
  exact ⟨H 1, hH⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.Isotopic.toTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.Isotopic.toTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.Isotopic.toTransport ``Submission.DifferentialGeometry.Topology.BallMarking.Isotopic.toTransport

theorem transport_to_ballChart (h : B.Transport B') (i : I) :
    Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ, hΦ i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.transport_to_ballChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.transport_to_ballChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.transport_to_ballChart ``Submission.DifferentialGeometry.Topology.BallMarking.transport_to_ballChart

theorem transport_of_ballChartTransport [Subsingleton I] {i : I}
    (h : Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart) :
    B.Transport B' := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ, fun j x hx => by rw [Subsingleton.elim j i]; exact hΦ x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.transport_of_ballChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.transport_of_ballChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.transport_of_ballChartTransport ``Submission.DifferentialGeometry.Topology.BallMarking.transport_of_ballChartTransport

theorem transport_iff_ballChartTransport [Subsingleton I] (i : I) :
    B.Transport B' ↔
      Manifold.BallChartTransport (B.ball i).toBallChart (B'.ball i).toBallChart :=
  ⟨fun h => B.transport_to_ballChart B' h i, fun h => B.transport_of_ballChartTransport B' h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.transport_iff_ballChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.transport_iff_ballChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.transport_iff_ballChartTransport ``Submission.DifferentialGeometry.Topology.BallMarking.transport_iff_ballChartTransport

theorem isotopic_to_ballChart (h : B.Isotopic B') (i : I) :
    Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  exact ⟨H, hH, hHi, hH0, hH1 i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.isotopic_to_ballChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.isotopic_to_ballChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.isotopic_to_ballChart ``Submission.DifferentialGeometry.Topology.BallMarking.isotopic_to_ballChart

theorem isotopic_of_ballChartIsotopic [Subsingleton I] {i : I}
    (h : Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart) :
    B.Isotopic B' := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  exact ⟨H, hH, hHi, hH0, fun j x hx => by rw [Subsingleton.elim j i]; exact hH1 x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.isotopic_of_ballChartIsotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.isotopic_of_ballChartIsotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.isotopic_of_ballChartIsotopic ``Submission.DifferentialGeometry.Topology.BallMarking.isotopic_of_ballChartIsotopic

theorem isotopic_iff_ballChartIsotopic [Subsingleton I] (i : I) :
    B.Isotopic B' ↔
      Manifold.BallChartIsotopic (B.ball i).toBallChart (B'.ball i).toBallChart :=
  ⟨fun h => B.isotopic_to_ballChart B' h i, fun h => B.isotopic_of_ballChartIsotopic B' h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallMarking.isotopic_iff_ballChartIsotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallMarking.isotopic_iff_ballChartIsotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallMarking.isotopic_iff_ballChartIsotopic ``Submission.DifferentialGeometry.Topology.BallMarking.isotopic_iff_ballChartIsotopic

end BallMarking

def G_ball : Prop :=
  ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u) [Fintype I]
    (B B' : BallMarking M I), B.Isotopic B'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.G_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.G_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.G_ball ``Submission.DifferentialGeometry.Topology.G_ball

theorem G_ball_isotopic_refl (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (I : Type u) [Fintype I] (B : BallMarking M I) : B.Isotopic B :=
  BallMarking.Isotopic.refl B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.G_ball_isotopic_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.G_ball_isotopic_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.G_ball_isotopic_refl ``Submission.DifferentialGeometry.Topology.G_ball_isotopic_refl

theorem G_ball_iff_ballChartIsotopic_single (M : ClosedOrientedManifold.{u} 3)
    [ConnectedSpace M.Carrier] :
    (∀ B B' : BallMarking M PUnit, B.Isotopic B') ↔
      ∀ c c' : OrientedBallChart M,
        Manifold.BallChartIsotopic c.toBallChart c'.toBallChart := by
  constructor
  · intro h c c'
    have hc := h (BallMarking.singleton c) (BallMarking.singleton c')
    exact BallMarking.isotopic_to_ballChart _ _ hc PUnit.unit
  · intro h B B'
    exact BallMarking.isotopic_of_ballChartIsotopic B B'
      (h (B.ball PUnit.unit) (B'.ball PUnit.unit))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.G_ball_iff_ballChartIsotopic_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.G_ball_iff_ballChartIsotopic_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.G_ball_iff_ballChartIsotopic_single ``Submission.DifferentialGeometry.Topology.G_ball_iff_ballChartIsotopic_single

end DifferentialGeometry.Topology
