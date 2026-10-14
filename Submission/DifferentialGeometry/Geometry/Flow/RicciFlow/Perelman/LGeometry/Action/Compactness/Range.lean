import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Kinetic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem lRegularizedEnergy_le
    (S : SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (T : Real) (alpha : Real → M) (a b A C Q : Real)
    (hab : a ≤ b) (hQ : 0 ≤ Q)
    (hcomp : ∀ s ∈ _root_.Set.Icc a b, ∀ v : TangentSpace I (alpha s),
      gRef.inner (alpha s) v v ≤
        Q * (S.base.metric (T - s ^ 2)).inner (alpha s) v v)
    (hpot : ∀ s ∈ _root_.Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
    (hE : _root_.MeasureTheory.IntegrableOn (fun s ↦
      gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) (_root_.Set.Icc a b))
    (hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hA : lRegularizedAction S T alpha a b ≤ A) :
    curveEnergy (I := I) gRef alpha a b ≤
      Q * (2 * (A - C * (b - a))) := by
  have hEint : IntervalIntegrable (fun s ↦
      gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hE
  have hQkin : IntervalIntegrable (fun s ↦ Q * lRegularizedSpeedSq S T alpha s)
      volume a b := hkin.const_mul Q
  have hmono :
      curveEnergy (I := I) gRef alpha a b ≤
        ∫ s in a..b, Q * lRegularizedSpeedSq S T alpha s := by
    unfold curveEnergy
    apply intervalIntegral.integral_mono_on hab hEint hQkin
    intro s hs
    simpa only [lVelocity, lRegularizedSpeedSq] using
      hcomp s hs (lVelocity (I := I) alpha s)
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (lRegularizedKinetic_le (I := I) S T alpha a b A C hab hpot hkin hLag hA) hQ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedEnergy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedEnergy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedEnergy_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedEnergy_le

theorem lRegularizedRange_compact
    (S : SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) gRef)
    (T : Real) (alpha : Real → M) (a b A C Q : Real)
    (hab : a ≤ b) (hQ : 0 ≤ Q)
    (hcomp : ∀ s ∈ _root_.Set.Icc a b, ∀ v : TangentSpace I (alpha s),
      gRef.inner (alpha s) v v ≤
        Q * (S.base.metric (T - s ^ 2)).inner (alpha s) v v)
    (hpot : ∀ s ∈ _root_.Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (_root_.Set.Icc a b))
    (hE : _root_.MeasureTheory.IntegrableOn (fun s ↦
      gRef.inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) (_root_.Set.Icc a b))
    (hkin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hA : lRegularizedAction S T alpha a b ≤ A) :
    ∃ K : Set M, IsCompact K ∧ alpha '' _root_.Set.Icc a b ⊆ K := by
  let B : Real := Q * (2 * (A - C * (b - a)))
  let R : Real := Real.sqrt (b - a) * Real.sqrt B
  let K : Set M :=
    {y : M | riemannianEDistOf (I := I) gRef (alpha a) y ≤ ENNReal.ofReal R}
  have henergy : curveEnergy (I := I) gRef alpha a b ≤ B := by
    exact lRegularizedEnergy_le (I := I) S gRef T alpha a b A C Q hab hQ hcomp hpot
      hE hkin hLag hA
  refine ⟨K, RiemannianMetricComplete.closedEBall_isCompact
    (I := I) hg (alpha a) R, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have has : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  have hsub : _root_.Set.Icc a s ⊆ _root_.Set.Icc a b := fun t ht ↦
    ⟨ht.1, ht.2.trans hsb⟩
  have hdist := edistOf_le_budget (I := I) gRef has
    (halpha.mono hsub) (hE.mono_set hsub)
    ((curveEnergy_mono (I := I) gRef le_rfl has hsb hE).trans henergy)
  have htime : Real.sqrt (s - a) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (by linarith)
  have hradius :
      Real.sqrt (s - a) * Real.sqrt B ≤ R := by
    exact mul_le_mul_of_nonneg_right htime (Real.sqrt_nonneg B)
  exact hdist.trans (ENNReal.ofReal_le_ofReal hradius)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRange_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRange_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRange_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRange_compact

theorem lRegularizedRanges_compact
    (S : SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) gRef)
    (T : Real) (alpha : Nat → Real → M) (x : M)
    (a b A C Q : Real)
    (hab : a ≤ b) (hQ : 0 ≤ Q)
    (hstart : ∀ n, alpha n a = x)
    (hcomp : ∀ n, ∀ s ∈ _root_.Set.Icc a b, ∀ v : TangentSpace I (alpha n s),
      gRef.inner (alpha n s) v v ≤
        Q * (S.base.metric (T - s ^ 2)).inner (alpha n s) v v)
    (hpot : ∀ n, ∀ s ∈ _root_.Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
    (halpha : ∀ n,
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 (alpha n) (_root_.Set.Icc a b))
    (hE : ∀ n, _root_.MeasureTheory.IntegrableOn (fun s ↦
      gRef.inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (_root_.Set.Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hA : ∀ n, lRegularizedAction S T (alpha n) a b ≤ A) :
    ∃ K : Set M, IsCompact K ∧ ∀ n, alpha n '' _root_.Set.Icc a b ⊆ K := by
  let B : Real := Q * (2 * (A - C * (b - a)))
  let R : Real := Real.sqrt (b - a) * Real.sqrt B
  let K : Set M :=
    {y : M | riemannianEDistOf (I := I) gRef x y ≤ ENNReal.ofReal R}
  refine ⟨K, RiemannianMetricComplete.closedEBall_isCompact
    (I := I) hg x R, ?_⟩
  intro n
  rintro y ⟨s, hs, rfl⟩
  have henergy : curveEnergy (I := I) gRef (alpha n) a b ≤ B := by
    exact lRegularizedEnergy_le (I := I) S gRef T (alpha n) a b A C Q hab hQ
      (hcomp n) (hpot n) (hE n) (hkin n) (hLag n) (hA n)
  have has : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  have hsub : _root_.Set.Icc a s ⊆ _root_.Set.Icc a b := fun t ht ↦
    ⟨ht.1, ht.2.trans hsb⟩
  have hdist := edistOf_le_budget (I := I) gRef has
    ((halpha n).mono hsub) ((hE n).mono_set hsub)
    ((curveEnergy_mono (I := I) gRef le_rfl has hsb (hE n)).trans henergy)
  rw [hstart n] at hdist
  have htime : Real.sqrt (s - a) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (by linarith)
  have hradius :
      Real.sqrt (s - a) * Real.sqrt B ≤ R := by
    exact mul_le_mul_of_nonneg_right htime (Real.sqrt_nonneg B)
  exact hdist.trans (ENNReal.ofReal_le_ofReal hradius)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRanges_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRanges_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRanges_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedRanges_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman
