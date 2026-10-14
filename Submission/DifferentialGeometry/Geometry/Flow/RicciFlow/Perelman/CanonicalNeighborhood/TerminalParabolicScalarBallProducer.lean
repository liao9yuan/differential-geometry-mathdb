import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallWindow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallAtSameTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarBoundAdditiveDistance

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
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem rmNormSq_eq_curvDerivNormSq {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) (t : ℝ) (y : (X.term i).M) :
    (X.term i).rmNormSq t y =
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y := by
  rw [PointedFlowData.rmNormSq, curvDerivNormSq]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_eq_curvDerivNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_eq_curvDerivNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_eq_curvDerivNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_eq_curvDerivNormSq

private theorem exists_curvDerivNormSq_le_of_source_bound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, i < N → ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨C', hC'⟩ := X.source_bound N
    refine ⟨max C (_root_.Max.max C' 0), lt_max_of_lt_left hC, ?_⟩
    intro i hi t ht y
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (hb i hlt t ht y) (le_max_left _ _)
    · subst heq
      have hbound : curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C' := by
        rw [← rmNormSq_eq_curvDerivNormSq X i t y]
        exact hC' t (hcarrier i ht) y
      exact le_trans hbound (le_trans (le_max_left _ _) (le_max_right _ _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvDerivNormSq_le_of_source_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_curvDerivNormSq_le_of_source_bound target :: scope.openDecls } }

private theorem exists_scalar_le_of_source_bound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, i < N → ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      (X.term i).S.scalar t y ≤ C := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨C', hC'⟩ := X.source_bound N
    have hpos : 0 < (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
        Real.sqrt (_root_.Max.max C' 0) + 1 := by
      have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
      have hnn : 0 ≤ Real.sqrt (_root_.Max.max C' 0) := Real.sqrt_nonneg _
      nlinarith
    refine ⟨max C ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (_root_.Max.max C' 0) + 1),
      lt_max_of_lt_left hC, fun i hi t ht y => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (hb i hlt t ht y) (le_max_left _ _)
    · subst heq
      have hrm : normSq0S (I := I3) ((X.term i).S.base.metric t) y 4
          (metricRm04At (I := I3) ((X.term i).S.base.metric t) y) ≤ _root_.Max.max C' 0 :=
        le_trans (hC' t (hcarrier i ht) y) (le_max_left _ _)
      have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
        (I := I3) ((X.term i).S.base.metric t) y
      have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
      rw [hdim] at hscal
      have hkey : (X.term i).S.scalar t y ≤
          (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (_root_.Max.max C' 0) :=
        le_trans (le_abs_self _) (le_trans hscal
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))
      exact le_trans (le_trans hkey (le_add_of_nonneg_right zero_le_one)) (le_max_right _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_le_of_source_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_le_of_source_bound target :: scope.openDecls } }

theorem terminalParabolicRmBallBoundAtSameTime_of_eventually
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {start ρ : ℝ} (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
        ENNReal.ofReal ρ →
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C) :
    TerminalParabolicRmBallBoundAtSameTime X start ρ := by
  obtain ⟨C, hC, hev⟩ := h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Cexc, hCexc, hexc⟩ := exists_curvDerivNormSq_le_of_source_bound X start hcarrier N
  exact ⟨max C Cexc, lt_max_of_lt_left hC, fun i t ht y hy => by
    by_cases hi : i < N
    · exact le_trans (hexc i hi t ht y) (le_max_right _ _)
    · exact le_trans (hN i (le_of_not_gt hi) t ht y hy) (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallBoundAtSameTime_of_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallBoundAtSameTime_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallBoundAtSameTime_of_eventually ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicRmBallBoundAtSameTime_of_eventually

theorem terminalParabolicScalarBallBoundAtSameTime_of_eventually
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {start ρ : ℝ} (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
        ENNReal.ofReal ρ →
      (X.term i).S.scalar t y ≤ C) :
    TerminalParabolicScalarBallBoundAtSameTime X start ρ := by
  obtain ⟨C, hC, hev⟩ := h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨Cexc, hCexc, hexc⟩ := exists_scalar_le_of_source_bound X start hcarrier N
  exact ⟨max C Cexc, lt_max_of_lt_left hC, fun i t ht y hy => by
    by_cases hi : i < N
    · exact le_trans (hexc i hi t ht y) (le_max_right _ _)
    · exact le_trans (hN i (le_of_not_gt hi) t ht y hy) (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicScalarBallBoundAtSameTime_of_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicScalarBallBoundAtSameTime_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicScalarBallBoundAtSameTime_of_eventually ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalParabolicScalarBallBoundAtSameTime_of_eventually

abbrev TerminalRmBallBoundAtSameTimeEventuallyProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) :
    Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc (-(modelDepth eps)) 0, ∀ y : (X.term i).M,
        riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
          ENNReal.ofReal ρ →
        curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeEventuallyProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeEventuallyProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeEventuallyProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalRmBallBoundAtSameTimeEventuallyProducer

abbrev TerminalScalarBallBoundAtSameTimeEventuallyProducer.{v} (kappa sigma : ℝ)
    (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ i in Filter.atTop, ∀ t ∈ Set.Icc (-(modelDepth eps)) 0, ∀ y : (X.term i).M,
        riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
          ENNReal.ofReal ρ →
        (X.term i).S.scalar t y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeEventuallyProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeEventuallyProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeEventuallyProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBallBoundAtSameTimeEventuallyProducer

theorem terminalRmBallBoundAtSameTimeProducer_iff_eventuallyProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi ↔
      TerminalRmBallBoundAtSameTimeEventuallyProducer.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X ρ hρ => ?_⟩
    obtain ⟨C, hC, hbound⟩ := h eps hp hle X ρ hρ
    exact ⟨C, hC, Filter.Eventually.of_forall hbound⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X ρ hρ => ?_⟩
    obtain ⟨C, hC, hev⟩ := h eps hp hle X ρ hρ
    exact terminalParabolicRmBallBoundAtSameTime_of_eventually X
      (fun i => (normalizedSequence_modelDepth_window X hp i).1) ⟨C, hC, hev⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_eventuallyProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_eventuallyProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_eventuallyProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_eventuallyProducer

theorem terminalScalarBallBoundAtSameTimeProducer_iff_eventuallyProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi ↔
      TerminalScalarBallBoundAtSameTimeEventuallyProducer.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X ρ hρ => ?_⟩
    obtain ⟨C, hC, hbound⟩ := h eps hp hle X ρ hρ
    exact ⟨C, hC, Filter.Eventually.of_forall hbound⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X ρ hρ => ?_⟩
    obtain ⟨C, hC, hev⟩ := h eps hp hle X ρ hρ
    exact terminalParabolicScalarBallBoundAtSameTime_of_eventually X
      (fun i => (normalizedSequence_modelDepth_window X hp i).1) ⟨C, hC, hev⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_iff_eventuallyProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_iff_eventuallyProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_iff_eventuallyProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_iff_eventuallyProducer

theorem terminalRmBallBoundAtSameTimeProducer_iff_terminalScalarBallBoundAtSameTimeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) :
    TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi ↔
      TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi := by
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := h
    refine ⟨e, he, fun eps hp hle X ρ hρ =>
      terminalParabolicScalarBallBoundAtSameTime_of_rmBallBoundAtSameTime X
        (-(modelDepth eps)) ρ (hb eps hp hle X ρ hρ)⟩
  · intro h
    obtain ⟨e, he, hb⟩ := h
    refine ⟨e, he, fun eps hp hle X ρ hρ =>
      terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime X hPhi
        (-(modelDepth eps)) ρ (fun i => (normalizedSequence_modelDepth_window X hp i).1)
        (hb eps hp hle X ρ hρ)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_terminalScalarBallBoundAtSameTimeProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_terminalScalarBallBoundAtSameTimeProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_terminalScalarBallBoundAtSameTimeProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRmBallBoundAtSameTimeProducer_iff_terminalScalarBallBoundAtSameTimeProducer

theorem exists_terminalParabolicRmBallBoundAtSameTime_modelScale
    {kappa K : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hK : 0 ≤ K) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            (∀ i, ∀ s ∈ Set.Icc (-(c / 2)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
              0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
                (X.term i).S.ricciAt s x (vec2 v v) ≤
                  ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                    ((X.term i).S.base.metric s).inner x v v) →
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ c / Real.sqrt 2 →
                TerminalParabolicRmBallBoundAtSameTime X (-(c / 2)) ρ := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_eventually_terminalParabolicRmBallBoundAtSameTime_of_ricciTensorBound
      (kappa := kappa) hmod hK
  refine ⟨min epsStar (2 / c), c, C, lt_min hepsStar (by positivity), hc, hC, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hric ρ hρ hρc
  have hmodelDepth : c / 2 ≤ modelDepth eps := by
    have h2 : eps ≤ 2 / c := hle.trans (min_le_right _ _)
    have h1 : c / 2 ≤ 1 / eps := by
      rw [show c / 2 = 1 / (2 / c) by field_simp]
      exact one_div_le_one_div_of_le heps h2
    simpa [modelDepth, one_div] using h1
  have hcarrier : ∀ i, Set.Icc (-(c / 2)) 0 ⊆ (X.interval i).carrier := by
    intro i x hx
    exact (normalizedSequence_modelDepth_window X heps i).1
      ⟨by linarith [hmodelDepth, hx.1], hx.2⟩
  refine terminalParabolicRmBallBoundAtSameTime_of_eventually X hcarrier ⟨C, hC, ?_⟩
  filter_upwards [hprop eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X hric]
    with i hi
  intro t ht y hy
  exact hi t ht y (le_trans hy (ENNReal.ofReal_le_ofReal hρc))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicRmBallBoundAtSameTime_modelScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicRmBallBoundAtSameTime_modelScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicRmBallBoundAtSameTime_modelScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicRmBallBoundAtSameTime_modelScale

theorem exists_terminalParabolicScalarBallBoundAtSameTime_modelScale
    {kappa K : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) (hK : 0 ≤ K) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            (∀ i, ∀ s ∈ Set.Icc (-(c / 2)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
              0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
                (X.term i).S.ricciAt s x (vec2 v v) ≤
                  ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                    ((X.term i).S.base.metric s).inner x v v) →
              ∀ ρ : ℝ, 0 < ρ → ρ ≤ c / Real.sqrt 2 →
                TerminalParabolicScalarBallBoundAtSameTime X (-(c / 2)) ρ := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_terminalParabolicRmBallBoundAtSameTime_modelScale hmod hK
  refine ⟨epsStar, c, (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C,
    hepsStar, hc, ?_, ?_⟩
  · have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    positivity
  · intro eps heps hle sigma hsigma Phi hPhi X hric ρ hρ hρc
    exact terminalParabolicScalarBallBoundAtSameTime_of_rmBallBoundAtSameTime X
      (-(c / 2)) ρ (hprop eps heps hle sigma hsigma Phi hPhi X hric ρ hρ hρc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_modelScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_modelScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_modelScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_modelScale

theorem exists_terminalParabolicScalarBallBoundAtSameTime_baseScale
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar r C : ℝ, 0 < epsStar ∧ 0 < r ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
            TerminalParabolicScalarBallBoundAtSameTime X 0 ρ := by
  obtain ⟨epsStar, r, C, hepsStar, hr, hC, hprop⟩ :=
    exists_eventually_scalar_le_at_boundedDistance (kappa := kappa) hmod
  refine ⟨epsStar, r, C, hepsStar, hr, hC, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X ρ hρ hρr
  refine terminalParabolicScalarBallBoundAtSameTime_of_eventually X ?_ ⟨C, hC, ?_⟩
  · intro i y hy
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i, hy.1], hy.2⟩
  · filter_upwards [hprop eps heps hle sigma hsigma Phi hPhi X] with i hi
    intro t ht y hy
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    refine hi y ?_
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
    have hle' : (riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
        (X.term i).basepoint y).toReal ≤ ρ := by
      simpa only [ENNReal.toReal_ofReal hρ.le] using hmono
    simpa only [metricDistance] using le_trans hle' hρr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_baseScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_baseScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_baseScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminalParabolicScalarBallBoundAtSameTime_baseScale

theorem ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {C epsStar : ℝ} (hC : 0 < C) (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
          (X.term i).S.scalar s x ≤ C)
    (hcone : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
          metricAlgebraicCurvatureTensorAt (I := I3) ((X.term i).S.base.metric s) x ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := (X.term i).M)) :
    RicciTensorBoundProducer.{u} kappa sigma Phi := by
  refine ⟨C / 2, by linarith, epsStar, hepsStar, ?_⟩
  intro eps heps hle X i s hs x v
  have hcone' := hcone eps heps hle X i s hs x
  have hscal' : metricScalarAt (I := I3) ((X.term i).S.base.metric s) x ≤ C :=
    hscal eps heps hle X i s hs x
  have hv : 0 ≤ ((X.term i).S.base.metric s).inner x v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact (((X.term i).S.base.metric s).pos x v hv0).le
  have hdim : ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) = C := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    ring
  refine ⟨metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I3)
    (M := (X.term i).M) ((X.term i).S.base.metric s) x hcone' v, ?_⟩
  refine le_trans (metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
    (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric s) x hcone' v) ?_
  have hhalf : metricScalarAt (I := I3) ((X.term i).S.base.metric s) x / 2 ≤ C / 2 := by
    linarith
  have hstep : (metricScalarAt (I := I3) ((X.term i).S.base.metric s) x / 2) *
      ((X.term i).S.base.metric s).inner x v v ≤ (C / 2) *
        ((X.term i).S.base.metric s).inner x v v :=
    mul_le_mul_of_nonneg_right hhalf hv
  refine le_trans hstep ?_
  rw [hdim]
  have : C / 2 ≤ C := by linarith
  exact mul_le_mul_of_nonneg_right this hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ricciTensorBoundProducer_of_uniformScalarBound_and_curvatureOperatorNonnegative

def TerminalParabolicRecenteredScalarBallBound (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ A ρ : ℝ, 0 < A → 0 < ρ → ∃ C : ℝ,
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ t ∈ Set.Icc (-(modelDepth eps)) 0, ∀ z y : (X.term i).M,
          (X.term i).S.scalar t z ≤ A →
          riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) z y ≤
            ENNReal.ofReal ρ →
          (X.term i).S.scalar t y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRecenteredScalarBallBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRecenteredScalarBallBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRecenteredScalarBallBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalParabolicRecenteredScalarBallBound

def TerminalScalarBaseWindowBound (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∃ A : ℝ, 0 < A ∧
      ∀ i : ℕ, ∀ t ∈ Set.Icc (-(modelDepth eps)) 0,
        (X.term i).S.scalar t (X.term i).basepoint ≤ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBaseWindowBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBaseWindowBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBaseWindowBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalScalarBaseWindowBound

theorem terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hbase : TerminalScalarBaseWindowBound.{u} kappa sigma Phi)
    (hrec : TerminalParabolicRecenteredScalarBallBound.{u} kappa sigma Phi) :
    TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, hbase⟩ := hbase
  obtain ⟨e₂, he₂, hrec⟩ := hrec
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X ρ hρ => ?_⟩
  obtain ⟨A, hA, hbp⟩ := hbase eps hp (hle.trans (min_le_left e₁ e₂)) X
  obtain ⟨C, hC⟩ := hrec eps hp (hle.trans (min_le_right e₁ e₂)) A ρ hA hρ
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), fun i t ht y hy =>
    le_trans (hC X i t ht (X.term i).basepoint y (hbp i t ht) hy) (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow

theorem bounded_curvature_at_distance_of_recentered_and_baseWindow_and_ricciTensorBound
    {kappa sigma K : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi) (hK : 0 ≤ K)
    (hbase : TerminalScalarBaseWindowBound.{u} kappa sigma Phi)
    (hrec : TerminalParabolicRecenteredScalarBallBound.{u} kappa sigma Phi)
    (hric : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
          0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
            (X.term i).S.ricciAt s x (vec2 v v) ≤
              ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                ((X.term i).S.base.metric s).inner x v v) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_scalarBallBoundAtSameTime_and_ricciTensorBound hPhi hK
    (terminalScalarBallBoundAtSameTimeProducer_of_recentered_and_baseWindow hbase hrec) hric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_recentered_and_baseWindow_and_ricciTensorBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_recentered_and_baseWindow_and_ricciTensorBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_recentered_and_baseWindow_and_ricciTensorBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bounded_curvature_at_distance_of_recentered_and_baseWindow_and_ricciTensorBound

theorem one_le_of_terminalParabolicScalarBallBoundAtSameTime {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) {start ρ : ℝ}
    (hstart : start ≤ 0)
    (h : TerminalParabolicScalarBallBoundAtSameTime X start ρ) :
    ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
        ENNReal.ofReal ρ →
      (X.term i).S.scalar t y ≤ C := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_, hb⟩
  have hmem : (0 : ℝ) ∈ Set.Icc start 0 := ⟨hstart, le_rfl⟩
  have hdist : riemannianEDistOf (I := I3) ((X.term 0).S.base.metric 0) (X.term 0).basepoint
      (X.term 0).basepoint ≤ ENNReal.ofReal ρ := by
    rw [riemannianEDistOf_self]
    exact zero_le
  have hbound := hb 0 0 hmem (X.term 0).basepoint hdist
  have hbase : (X.term 0).S.scalar 0 (X.term 0).basepoint = 1 := by
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar]
      using X.base_one 0
  rwa [hbase] at hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_of_terminalParabolicScalarBallBoundAtSameTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_of_terminalParabolicScalarBallBoundAtSameTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_of_terminalParabolicScalarBallBoundAtSameTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_of_terminalParabolicScalarBallBoundAtSameTime

theorem one_div_eighty_one_le_of_rmBallBoundAtSameTime {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {start ρ : ℝ} (hstart : start ≤ 0)
    (h : TerminalParabolicRmBallBoundAtSameTime X start ρ) :
    ∃ C : ℝ, 0 < C ∧ 1 / 81 ≤ C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
        ENNReal.ofReal ρ →
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ C := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_, hb⟩
  have hmem : (0 : ℝ) ∈ Set.Icc start 0 := ⟨hstart, le_rfl⟩
  have hdist : riemannianEDistOf (I := I3) ((X.term 0).S.base.metric 0) (X.term 0).basepoint
      (X.term 0).basepoint ≤ ENNReal.ofReal ρ := by
    rw [riemannianEDistOf_self]
    exact zero_le
  have hrm : normSq0S (I := I3) ((X.term 0).S.base.metric 0) (X.term 0).basepoint 4
      (metricRm04At (I := I3) ((X.term 0).S.base.metric 0) (X.term 0).basepoint) ≤ C := by
    have hb0 := hb 0 0 hmem (X.term 0).basepoint hdist
    rwa [← rmNormSq_eq_curvDerivNormSq X 0 0 (X.term 0).basepoint] at hb0
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) ((X.term 0).S.base.metric 0) (X.term 0).basepoint
  have hdim : Module.finrank ℝ (TangentSpace I3 (X.term 0).basepoint) =
      Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  have hbase : (X.term 0).S.scalar 0 (X.term 0).basepoint = 1 := by
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar]
      using X.base_one 0
  have hle : (1 : ℝ) ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C := by
    have h1 : (1 : ℝ) ≤ |metricScalarAt (I := I3) ((X.term 0).S.base.metric 0)
        (X.term 0).basepoint| := by
      rw [← hbase]
      exact le_abs_self _
    exact le_trans h1 (le_trans hscal (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hrm) (by positivity)))
  have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have h3r : ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3 := by exact_mod_cast h3
  rw [h3r] at hle
  have hsqrt : (1 : ℝ) / 9 ≤ Real.sqrt C := by nlinarith [Real.sqrt_nonneg C]
  nlinarith [hsqrt, Real.sq_sqrt hC.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_div_eighty_one_le_of_rmBallBoundAtSameTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_div_eighty_one_le_of_rmBallBoundAtSameTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_div_eighty_one_le_of_rmBallBoundAtSameTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_div_eighty_one_le_of_rmBallBoundAtSameTime

theorem standardRmNormSq3_roundSphere_scalar_one :
    standardRmNormSq3 (standardRmDiag3 (1 / 3) (1 / 3) (1 / 3)) = 1 / 3 := by
  rw [standardRmNormSq3_diag]
  norm_num [rmSecNormSq3, sec12Ric3, sec13Ric3, sec23Ric3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.standardRmNormSq3_roundSphere_scalar_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.standardRmNormSq3_roundSphere_scalar_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.standardRmNormSq3_roundSphere_scalar_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.standardRmNormSq3_roundSphere_scalar_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
