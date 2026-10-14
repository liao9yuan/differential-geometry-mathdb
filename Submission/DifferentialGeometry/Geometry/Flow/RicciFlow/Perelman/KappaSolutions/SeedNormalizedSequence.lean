import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HalfEuclideanScale
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AnchoredCurvatureBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance seedFlowTopology {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTopology target :: scope.openDecls } }
private local instance seedFlowCharted {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowCharted target :: scope.openDecls } }
private local instance seedFlowSmooth {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowSmooth target :: scope.openDecls } }
private local instance seedFlowC1 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowC1 target :: scope.openDecls } }
private local instance seedFlowT2 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowT2 target :: scope.openDecls } }
private local instance seedFlowSigma {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowSigma target :: scope.openDecls } }
private local instance seedFlowTangentT2 {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTangentT2 target :: scope.openDecls } }
private local instance seedFlowMeasurable {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowMeasurable target :: scope.openDecls } }
private local instance seedFlowBorel {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowBorel target :: scope.openDecls } }

abbrev seedTerminalUnitVolume {T : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) T) : ℝ≥0∞ :=
  riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
    (riemannianBallOf (I := I) (F.S.base.metric 0) F.basepoint 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedTerminalUnitVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedTerminalUnitVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedTerminalUnitVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedTerminalUnitVolume

theorem exists_seed_local_curvature_constants [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (T : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) T),
        KLim (I := I) kappa F →
        seedTerminalUnitVolume F = euclideanUnitBallVolume 3 / 2 →
        ∀ (A : ℝ) (x : F.M),
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint x ≤
            ENNReal.ofReal A →
          ∀ t : ℝ, t ≤ 0 →
            (0 ≤ F.S.scalar t x ∧ F.S.scalar t x ≤ C A) ∧
              F.rmNormSq (I := I) t x ≤ 3 * (C A) ^ 2 := by
  classical
  let v : ℝ := (euclideanUnitBallVolume 3 / 2).toReal
  have hvtop : euclideanUnitBallVolume 3 / 2 ≠ ⊤ :=
    ENNReal.div_ne_top (euclideanUnitBallVolume_ne_top 3) (by norm_num)
  have hv : 0 < v := ENNReal.toReal_pos
    (ENNReal.div_pos (euclideanUnitBallVolume_pos 3).ne' (by norm_num)).ne' hvtop
  have hbounds := fun A : ℝ => exists_anchored_scalar_bound (I := I) hdim
    kappa v (_root_.Max.max A 0 + 1) hv (by positivity : 0 ≤ max A 0 + 1)
  choose C hC hbound using hbounds
  refine ⟨C, hC, ?_⟩
  intro T F hK hvolume A x hx t ht
  have hvol : ENNReal.ofReal v ≤ seedTerminalUnitVolume F := by
    change ENNReal.ofReal (euclideanUnitBallVolume 3 / 2).toReal ≤ _
    rw [hvolume, ENNReal.ofReal_toReal hvtop]
  have hball : x ∈ riemannianBallOf (I := I) (F.S.base.metric 0)
      F.basepoint (_root_.Max.max A 0 + 1) := by
    apply lt_of_le_of_lt hx
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (lt_of_le_of_lt (le_max_left A 0) (lt_add_one (_root_.Max.max A 0)))
  have hterminal := hbound A T F hK F.basepoint hvol x hball
  exact ⟨⟨hK.scalar_nonneg ht x, (hK.scalar_le_terminal ht x).trans hterminal⟩,
    hK.rmNormSq_le_of_terminal_scalar_le F hdim ht x hterminal⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seed_local_curvature_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seed_local_curvature_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seed_local_curvature_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seed_local_curvature_constants

variable (X : PointedFlowSeq.{u, uE, uH} (I := I)) {kappa : ℝ}


abbrev seedFlowTail (N : ℕ) : PointedFlowSeq.{u, uE, uH} (I := I) where
  D := X.D
  term i := X.term (i + N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTail ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlowTail

abbrev seedRescaledFlowSeq (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow (X.term i) (hK i).carrier_eq (hK i).regular_eq
    0 ((delta i) ^ 2)⁻¹ (inv_pos.mpr (pow_pos (hdelta i) 2))
    (by simpa only [(hK i).carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
    (X.term i).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq

theorem seedRescaledFlowSeq_metric
    (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i) (i : ℕ) (t : ℝ) :
    ((seedRescaledFlowSeq X hK delta hdelta).term i).S.base.metric t =
      scaleMetric ((delta i) ^ 2)⁻¹ (inv_pos.mpr (pow_pos (hdelta i) 2))
        ((X.term i).S.base.metric ((delta i) ^ 2 * t)) := by
  change scaleMetric ((delta i) ^ 2)⁻¹ (inv_pos.mpr (pow_pos (hdelta i) 2))
    ((X.term i).S.base.metric (parabolicTime 0 ((delta i) ^ 2)⁻¹ t)) = _
  have htime : parabolicTime 0 ((delta i) ^ 2)⁻¹ t = (delta i) ^ 2 * t := by
    simp only [parabolicTime, zero_add, div_inv_eq_mul, mul_comm]
  rw [htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_metric

theorem seedRescaledFlowSeq_klim (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i) (i : ℕ) :
    KLim (I := I) kappa ((seedRescaledFlowSeq X hK delta hdelta).term i) :=
  KLim.curvatureRescaledFlow (X.term i) (hK i) 0 ((delta i) ^ 2)⁻¹
    (inv_pos.mpr (pow_pos (hdelta i) 2))
    (by simpa only [(hK i).carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
    (X.term i).basepoint (by rw [hbase i]; exact one_ne_zero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_klim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_klim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_klim ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_klim


theorem seedRescaledFlowSeq_scalar_base
    (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i) (i : ℕ) :
    ((seedRescaledFlowSeq X hK delta hdelta).term i).S.scalar 0
      ((seedRescaledFlowSeq X hK delta hdelta).term i).basepoint = (delta i) ^ 2 := by
  change (curvatureNormalizedSolution (X.term i).S 0 ((delta i) ^ 2)⁻¹
    (inv_pos.mpr (pow_pos (hdelta i) 2)) _).scalar 0 (X.term i).basepoint = _
  rw [curvatureNormalizedSolution_scalar]
  change (((delta i) ^ 2)⁻¹)⁻¹ *
    (X.term i).S.scalar (parabolicTime 0 ((delta i) ^ 2)⁻¹ 0) (X.term i).basepoint = _
  rw [parabolicTime_zero, hbase i, inv_inv, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_scalar_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_scalar_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_scalar_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_scalar_base

theorem seedRescaledFlowSeq_unitVolume
    (hdim : Module.finrank ℝ E = 3)
    (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i)
    (hhalf : ∀ i,
      riemannianVolumeMeasure (I := I) (M := (X.term i).M) ((X.term i).S.base.metric 0)
        (riemannianBallOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint (delta i)) =
        (euclideanUnitBallVolume 3 / 2) * ENNReal.ofReal ((delta i) ^ 3)) (i : ℕ) :
    seedTerminalUnitVolume ((seedRescaledFlowSeq X hK delta hdelta).term i) =
      euclideanUnitBallVolume 3 / 2 := by
  let Q : ℝ := ((delta i) ^ 2)⁻¹
  have hQ : 0 < Q := inv_pos.mpr (pow_pos (hdelta i) 2)
  have hsqrt : Real.sqrt Q * delta i = 1 := by
    dsimp only [Q]
    rw [Real.sqrt_inv, Real.sqrt_sq (hdelta i).le]
    exact inv_mul_cancel₀ (hdelta i).ne'
  have hball := riemannianBallOf_scaleMetric (I := I)
    ((X.term i).S.base.metric 0) Q hQ (X.term i).basepoint (delta i)
  rw [hsqrt] at hball
  change riemannianVolumeMeasure (I := I) (M := (X.term i).M)
    (scaleMetric Q hQ ((X.term i).S.base.metric (parabolicTime 0 Q 0)))
    (riemannianBallOf (I := I)
      (scaleMetric Q hQ ((X.term i).S.base.metric (parabolicTime 0 Q 0)))
      (X.term i).basepoint 1) = _
  rw [parabolicTime_zero, hball, volume_scale_apply, hdim, hhalf i]
  have hcancel : ENNReal.ofReal (Real.sqrt Q) ^ 3 *
      ENNReal.ofReal ((delta i) ^ 3) = 1 := by
    rw [ENNReal.ofReal_pow (hdelta i).le, ← mul_pow,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg Q), hsqrt, ENNReal.ofReal_one, one_pow]
  calc
    _ = (euclideanUnitBallVolume 3 / 2) *
      (ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((delta i) ^ 3)) := by ac_rfl
    _ = euclideanUnitBallVolume 3 / 2 := by rw [hcancel, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_unitVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_unitVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_unitVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedRescaledFlowSeq_unitVolume

theorem exists_seedNormalizedSequence [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3)
    (hK : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hcollapse : _root_.Filter.Tendsto (fun i => seedTerminalUnitVolume (X.term i)) _root_.Filter.atTop (𝓝 0)) :
    ∃ (N : ℕ) (delta : ℕ → ℝ) (hdelta : ∀ i, 0 < delta i),
      (∀ i, delta i < 1) ∧ _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) ∧
      (∀ i,
        riemannianVolumeMeasure (I := I) (M := (X.term (i + N)).M)
          ((X.term (i + N)).S.base.metric 0)
          (riemannianBallOf (I := I) ((X.term (i + N)).S.base.metric 0)
            (X.term (i + N)).basepoint (delta i)) =
          (euclideanUnitBallVolume 3 / 2) * ENNReal.ofReal ((delta i) ^ 3)) ∧
      let Y := seedRescaledFlowSeq (seedFlowTail X N) (fun i => hK (i + N)) delta hdelta
      (∀ i, KLim (I := I) kappa (Y.term i)) ∧
      (∀ i, (Y.term i).S.scalar 0 (Y.term i).basepoint = (delta i) ^ 2) ∧
      _root_.Filter.Tendsto (fun i => (Y.term i).S.scalar 0 (Y.term i).basepoint) _root_.Filter.atTop (𝓝 0) ∧
      (∀ i, seedTerminalUnitVolume (Y.term i) = euclideanUnitBallVolume 3 / 2) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hhalfpos : 0 < euclideanUnitBallVolume 3 / 2 :=
    ENNReal.div_pos (euclideanUnitBallVolume_pos 3).ne' (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hcollapse.eventually (Iio_mem_nhds hhalfpos))
  let Z := seedFlowTail X N
  have hcomplete : SeqMetricComplete (I := I) (Z.atZero (I := I)) :=
    ⟨fun i => (hK (i + N)).complete 0
      (by simpa only [(hK (i + N)).carrier_eq, Set.mem_Iic] using
        (le_rfl : (0 : ℝ) ≤ 0))⟩
  have hsmall : ∀ i, seedTerminalUnitVolume (Z.term i) <
      euclideanUnitBallVolume (Module.finrank ℝ E) / 2 := by
    intro i
    rw [hdim]
    exact hN (i + N) (Nat.le_add_left N i)
  obtain ⟨delta, hd, hzero⟩ := exists_halfEuclideanScales_tendsto_zero
    (I := I) (Z.atZero (I := I)) hcomplete
    (fun i => (hK (i + N)).connected) hsmall
    (hcollapse.comp (_root_.Filter.tendsto_add_atTop_nat N))
  have hdelta : ∀ i, 0 < delta i := fun i => (hd i).1
  have hhalf : ∀ i,
      riemannianVolumeMeasure (I := I) (M := (Z.term i).M) ((Z.term i).S.base.metric 0)
        (riemannianBallOf (I := I) ((Z.term i).S.base.metric 0)
          (Z.term i).basepoint (delta i)) =
        (euclideanUnitBallVolume 3 / 2) * ENNReal.ofReal ((delta i) ^ 3) := by
    intro i
    have h := (hd i).2.2
    change riemannianVolumeMeasure (I := I) (M := (Z.term i).M)
      ((Z.term i).S.base.metric 0)
      (riemannianBallOf (I := I) ((Z.term i).S.base.metric 0)
        (Z.term i).basepoint (delta i)) =
      (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
        ENNReal.ofReal ((delta i) ^ Module.finrank ℝ E) at h
    simpa only [hdim] using h
  refine ⟨N, delta, hdelta, fun i => (hd i).2.1, hzero, hhalf, ?_⟩
  dsimp only
  have hscalar := seedRescaledFlowSeq_scalar_base Z (fun i => hK (i + N))
    (fun i => hbase (i + N)) delta hdelta
  refine ⟨seedRescaledFlowSeq_klim Z (fun i => hK (i + N))
      (fun i => hbase (i + N)) delta hdelta, hscalar, ?_,
    seedRescaledFlowSeq_unitVolume Z hdim (fun i => hK (i + N)) delta hdelta hhalf⟩
  have hpower : _root_.Filter.Tendsto (fun i => (delta i) ^ 2) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hzero.pow 2
  exact hpower.congr' (Filter.Eventually.of_forall (fun i => (hscalar i).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seedNormalizedSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seedNormalizedSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seedNormalizedSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_seedNormalizedSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
