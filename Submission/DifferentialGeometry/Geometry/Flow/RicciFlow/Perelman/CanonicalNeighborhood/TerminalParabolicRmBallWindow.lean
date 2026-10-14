import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallAtSameTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

def TerminalParabolicRmBallWindow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
    TerminalParabolicRmBallBound X start (2 * ρ) ∧
    TerminalParabolicBallNesting X start rho ρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindow

theorem terminalParabolicRmBallWindow_iff_curvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ) :
    TerminalParabolicRmBallWindow X start ↔ TerminalParabolicCurvatureBound X start :=
  (terminalParabolicCurvatureBound_iff_scale_windows X start).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindow_iff_curvatureBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindow_iff_curvatureBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindow_iff_curvatureBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindow_iff_curvatureBound

theorem terminalDerivativeBounds_of_terminalParabolicRmBallWindow
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (heps : 0 < eps) (h : TerminalParabolicRmBallWindow X (-(modelDepth eps))) :
    TerminalDerivativeBounds X :=
  terminalDerivativeBounds_of_parabolicCurvatureBounds X
    (parabolicCurvatureBoundsAtBase_of_terminalParabolicCurvatureControl X heps
      (terminalParabolicCurvatureControl_of_bound X heps
        ((terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mp h)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_of_terminalParabolicRmBallWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_of_terminalParabolicRmBallWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_of_terminalParabolicRmBallWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_of_terminalParabolicRmBallWindow

abbrev TerminalParabolicRmBallWindowProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      TerminalParabolicRmBallWindow X (-(modelDepth eps))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindowProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindowProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindowProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRmBallWindowProducer

theorem terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi ↔
      TerminalParabolicCurvatureBoundProducer.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, fun eps hp hle X =>
      (terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mp
        (hw eps hp hle X)⟩
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, fun eps hp hle X =>
      (terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mpr
        (hw eps hp hle X)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer

theorem terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨e, he, hw⟩ := h
  exact ⟨e, he, fun eps hp hle X =>
    terminalDerivativeBounds_of_terminalParabolicRmBallWindow X hp (hw eps hp hle X)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer

def TerminalRmBallBoundAtZero {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → TerminalParabolicRmBallBound X 0 rho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtZero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtZero

def TerminalHigherDerivativeBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∀ a : ℕ, 1 ≤ a → ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      curvDerivNorm (I := I3) a ((X.term i).S.base.metric 0) y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalHigherDerivativeBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalHigherDerivativeBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalHigherDerivativeBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalHigherDerivativeBounds

theorem terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    TerminalDerivativeBounds X ↔
      TerminalRmBallBoundAtZero X ∧ TerminalHigherDerivativeBounds X := by
  constructor
  · intro h
    exact ⟨terminalRmBallBound_at_zero_of_terminalDerivativeBounds X h,
      fun rho hrho a _ => h rho hrho a⟩
  · rintro ⟨h0, hh⟩ rho hrho a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain ⟨C, hC, hb⟩ := h0 rho hrho
      refine ⟨Real.sqrt C, fun i y hy => ?_⟩
      have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
      have hy' : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
          (X.term i).basepoint y ≤ ENNReal.ofReal rho :=
        (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
          ((X.term i).S.base.metric 0) (X.term i).basepoint y) hrho.le).mpr
          (by simpa only [metricDistance] using hy)
      rw [curvDerivNorm]
      exact Real.sqrt_le_sqrt (hb i 0 ⟨le_rfl, le_rfl⟩ y hy')
    · exact hh rho hrho a (Nat.succ_le_of_lt ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds

theorem pointedFlowNotFlat_of_normalizedSequence {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    PointedFlowNotFlat (X.term i) := by
  refine pointedFlowNotFlat_of_scalar_ne_zero (X.term i) (t := 0) ?_ (X.term i).basepoint ?_
  · rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  · rw [X.base_one i]
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedFlowNotFlat_of_normalizedSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedFlowNotFlat_of_normalizedSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedFlowNotFlat_of_normalizedSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedFlowNotFlat_of_normalizedSequence

abbrev TerminalRmBallBoundAtSameTimeProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
      TerminalParabolicRmBallBoundAtSameTime X (-(modelDepth eps)) ρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeProducer

abbrev RicciTensorBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
      ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RicciTensorBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RicciTensorBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RicciTensorBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.RicciTensorBoundProducer

theorem terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, hric⟩ := hric
  obtain ⟨e, he, hb⟩ :=
    bounded_curvature_at_distance_of_rmBallBoundAtSameTime_and_ricciTensorBound
      (kappa := kappa) (sigma := sigma) (Phi := Phi) hK hrm hric
  exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer

theorem terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, e₂, he₂, hric₂⟩ := hric
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X rho hrho => ?_⟩
  have hwin := normalizedSequence_modelDepth_window X hp
  have hric' : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v :=
    hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X
  obtain ⟨ρ, hρ, hnest⟩ :=
    terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK hric' rho hrho
  refine ⟨ρ, hρ, ?_, hnest⟩
  exact terminalParabolicRmBallBound_of_rmBallBoundAtSameTime X (-(modelDepth eps)) (2 * ρ) K
    (by positivity) hK (fun i => (hwin i).1)
    (fun i s hs => (hwin i).2 ⟨hs.1.le, hs.2⟩) hric'
    (hrm₁ eps hp (hle.trans (min_le_left e₁ e₂)) X (2 * ρ) (by positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer

abbrev TerminalScalarBallBoundAtSameTimeProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
      TerminalParabolicScalarBallBoundAtSameTime X (-(modelDepth eps)) ρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeProducer

theorem terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, hric⟩ := hric
  obtain ⟨e, he, hb⟩ :=
    bounded_curvature_at_distance_of_scalarBallBoundAtSameTime_and_ricciTensorBound
      (kappa := kappa) (sigma := sigma) (Phi := Phi) hPhi hK hscl hric
  exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
