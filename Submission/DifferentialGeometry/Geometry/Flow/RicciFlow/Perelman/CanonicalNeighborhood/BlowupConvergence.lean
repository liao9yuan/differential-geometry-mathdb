import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OrientedBadPointSelection
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


structure FlowSequence where
  interval : ℕ → RealTimeInterval
  term : ∀ i, PointedFlowData.{u, 0, 0} I3 (interval i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence

def modelNoncollapseFactor : ℝ := 250 * 30 ^ 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor

theorem modelNoncollapseFactor_pos : 0 < modelNoncollapseFactor := by
  unfold modelNoncollapseFactor
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.modelNoncollapseFactor_pos

def FlowSequence.atTime (X : FlowSequence.{u}) (t : ℝ) : PointedRiemannianSeq I3 :=
  ⟨fun i => (X.term i).atTime t⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.atTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence.atTime

structure NormalizedSequence (eps kappa sigma : ℝ) (Phi : ℝ → ℝ)
    extends FlowSequence.{u} where
  depth : ℕ → ℝ
  scale : ℕ → ℝ
  depth_pos : ∀ i, 0 < depth i
  depth_buffer : ∀ i, modelDepth eps ≤ depth i
  scale_pos : ∀ i, 0 < scale i
  depth_tendsto : Filter.Tendsto depth Filter.atTop Filter.atTop
  scale_tendsto : Filter.Tendsto scale Filter.atTop Filter.atTop
  carrier_eq : ∀ i, (interval i).carrier = Set.Icc (-(2 * depth i)) 0
  regular_eq : ∀ i, (interval i).regular = Set.Ioo (-(2 * depth i)) 0
  connected : ∀ i, ConnectedSpace (term i).M
  orientation : ∀ i, TangentOrientationSection (term i).M
  complete : ∀ i t, t ∈ (interval i).carrier → MetricComplete ((term i).atTime t)
  source_bound : ∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (term i) C
  base_one : ∀ i, PointedFlowScalarAtBase (term i) 1
  noncollapse : ∀ i, ParabolicallyKappaNoncollapsedBelowScale
    (term i).S (modelNoncollapseFactor * kappa) (Real.sqrt (scale i) * sigma)
  pinching : ∀ i, PhiAlmostNonnegative (term i).S (interval i).carrier
    (rescalePinchingFunction (scale i) Phi)
  higher_good : ∀ i t, t ∈ Set.Icc (-depth i) 0 → ∀ x,
    2 ≤ (term i).S.scalar t x → OrientedWitness (term i).S (orientation i) eps kappa x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence


def BoundedAtDistance {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      (X.term i).S.scalar 0 y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BoundedAtDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BoundedAtDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BoundedAtDistance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BoundedAtDistance


def TerminalDerivativeBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∀ a : ℕ, ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      curvDerivNorm (I := I3) a ((X.term i).S.base.metric 0) y ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalDerivativeBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalDerivativeBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalDerivativeBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalDerivativeBounds


def MetricSourceCapture {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᶠ i in Filter.atTop,
    riemannianBallOf (I := I3) (X.obj (f i)).metric (X.obj (f i)).basepoint r ⊆
      (F.partialDiffeomorph i) '' (F.partialDiffeomorph i).source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricSourceCapture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricSourceCapture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricSourceCapture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricSourceCapture


theorem metricSourceCapture_of_metricConvergenceData
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps X P f}
    (C : MetricConvergenceData F)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete P) : MetricSourceCapture F := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  intro r hr
  obtain ⟨_, k₀, hk₀⟩ := KappaSolutions.exists_pointed_inverse_capture_at
    C hreference hcomplete P.basepoint hr.le (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  intro y hy
  have hclosed : y ∈ riemannianClosedBallOf (X.obj (f k)).metric
      (F.map k P.basepoint) r := by
    have hbase : F.map k P.basepoint = (X.obj (f k)).basepoint := F.basepoint_map k
    rw [hbase]
    change riemannianEDistOf (X.obj (f k)).metric (X.obj (f k)).basepoint y ≤ ENNReal.ofReal r
    change riemannianEDistOf (X.obj (f k)).metric (X.obj (f k)).basepoint y < ENNReal.ofReal r at hy
    exact hy.le
  have ht := (hk₀ k hk y hclosed).1
  exact ⟨(F.partialDiffeomorph k).symm y,
    (F.partialDiffeomorph k).symm.map_source ht,
    (F.partialDiffeomorph k).right_inv ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metricConvergenceData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metricConvergenceData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metricConvergenceData ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricSourceCapture_of_metricConvergenceData


def subsequenceMaps {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (k : ℕ → ℕ) (hk : StrictMono k) :
    PointedRiemannianConvergenceMaps X P (f ∘ k) where
  partialDiffeomorph i := F.partialDiffeomorph (k i)
  source_exhausts := F.source_exhausts.comp_subseq hk
  base_mem i := F.base_mem (k i)
  basepoint_map i := F.basepoint_map (k i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceMaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.subsequenceMaps


def MetricNoncollapsed (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (kappa : ℝ) (scales : Set ℝ) : Prop :=
  ∀ x : P.M, ∀ r ∈ scales, 0 < r →
    (∀ y ∈ riemannianBallOf (I := I3) P.metric x r,
      r ^ 4 * Tensor0SBundle.normSq0S (I := I3) P.metric y 4 (metricRm04At P.metric y) ≤ 1) →
    ENNReal.ofReal (kappa * r ^ 3) ≤
      riemannianVolumeMeasure I3 P.M P.metric (riemannianBallOf (I := I3) P.metric x r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricNoncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricNoncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricNoncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricNoncollapsed

theorem noncollapse_passes_to_limit (X : PointedRiemannianSeq.{u, 0, 0} I3)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (conv : MetricConvergenceData F)
    (canonical_domains : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (capture : MetricSourceCapture F) (complete : MetricComplete P)
    {kappa : ℝ} (hkappa : 0 < kappa) (radii : ℕ → ℝ)
    (hradii : Filter.Tendsto radii Filter.atTop Filter.atTop)
    (hsource : ∀ i, MetricNoncollapsed (X.obj i) kappa (Set.Ioc 0 (radii i))) :
    MetricNoncollapsed P kappa Set.univ := by
  intro z r _ hr hcurvature
  let _ := capture
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hn : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hconv : ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ ThreeSpace =
      ENNReal.ofReal (kappa * r ^ 3) := by
    rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hkappa.le, hn]
  have hreference (k : ℕ) : (conv.domain k).referenceMetric = (conv.domain k).limitMetric := by
    rw [canonical_domains k]
    rfl
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : Filter.Tendsto epsilon Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Filter.Tendsto (fun j => 1 + epsilon j) Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1)).add hepsilon
  have hs : Filter.Tendsto s Filter.atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => r) Filter.atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hreal : Filter.Tendsto (fun j => ENNReal.ofReal (s j)) Filter.atTop
      (𝓝 (ENNReal.ofReal r)) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  have hleft := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal kappa)
    (ENNReal.Tendsto.pow (n := Module.finrank ℝ ThreeSpace) hreal)
    (Or.inr ENNReal.ofReal_ne_top)
  have hsqrt : Filter.Tendsto
      (fun j => Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ ThreeSpace))
      Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (hone.pow (Module.finrank ℝ ThreeSpace))
  have hcoef : Filter.Tendsto (fun j => ENNReal.ofReal
      (Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ ThreeSpace)))
      Filter.atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hright : Filter.Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ Module.finrank ℝ ThreeSpace)) *
        riemannianVolumeMeasure I3 P.M P.metric (riemannianBallOf P.metric z r))
      Filter.atTop
      (𝓝 (riemannianVolumeMeasure I3 P.M P.metric (riemannianBallOf P.metric z r))) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  rw [← hconv]
  refine le_of_tendsto_of_tendsto' hleft hright fun j => ?_
  have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
  have h1 : 0 < 1 + epsilon j := by linarith
  have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
  have hbuffer : (1 + epsilon j) * s j < r := by
    calc
      (1 + epsilon j) * s j = r / (1 + epsilon j) := by
        dsimp only [s]
        field_simp [ne_of_gt h1]
      _ < r := (div_lt_self hr (by linarith))
  obtain ⟨kv, hkv⟩ :=
    KappaSolutions.exists_pointed_buffered_ball_volume_le_at
      (I := I3) (X := X) (L := P) (subseq := f) (Φ := F) conv hreference complete z
      hsj he hbuffer he
  obtain ⟨kc, hkc⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_ball_curvature_control
      (I := I3) (X := X) (L := P) (subseq := f) (Φ := F) conv canonical_domains complete z
      hsj he hbuffer hcurvature
  obtain ⟨krad, hkrad⟩ := Filter.eventually_atTop.mp
    ((hradii.comp hf.tendsto_atTop).eventually (Filter.eventually_ge_atTop (s j)))
  have hnc := hsource (f (_root_.Max.max kv (_root_.Max.max kc krad))) (F.map (_root_.Max.max kv (_root_.Max.max kc krad)) z) (s j)
    ⟨hsj, hkrad (_root_.Max.max kv (_root_.Max.max kc krad))
      (le_trans (le_max_right _ _) (le_max_right _ _))⟩
    hsj
    (hkc (_root_.Max.max kv (_root_.Max.max kc krad))
      (le_trans (le_max_left _ _) (le_max_right _ _)))
  have hnc' : ENNReal.ofReal kappa * ENNReal.ofReal (s j) ^ Module.finrank ℝ ThreeSpace ≤
      riemannianVolumeMeasure I3 (X.obj (f (_root_.Max.max kv (_root_.Max.max kc krad)))).M
        (X.obj (f (_root_.Max.max kv (_root_.Max.max kc krad)))).metric
        (riemannianBallOf (X.obj (f (_root_.Max.max kv (_root_.Max.max kc krad)))).metric
          (F.map (_root_.Max.max kv (_root_.Max.max kc krad)) z) (s j)) := by
    rw [← ENNReal.ofReal_pow hsj.le, ← ENNReal.ofReal_mul hkappa.le, hn]
    exact hnc
  exact hnc'.trans (hkv (_root_.Max.max kv (_root_.Max.max kc krad)) (le_max_left _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noncollapse_passes_to_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noncollapse_passes_to_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noncollapse_passes_to_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.noncollapse_passes_to_limit

theorem blowup_limit_nonnegative {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hPhi : AdmissiblePinchingFunction Phi)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) P f)
    (conv : MetricConvergenceData F)
    (canonical_domains : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k) :
    SecLower P.metric 0 Set.univ := by
  let Y : PointedRiemannianSeq.{u, 0, 0} I3 := X.toFlowSequence.atTime 0
  have hQ : Filter.Tendsto (fun k => X.scale (f k)) Filter.atTop Filter.atTop :=
    X.scale_tendsto.comp hf.tendsto_atTop
  have hpin : ∀ i (y : (Y.obj i).M),
      curvatureOperatorLowerBoundAt (Y.obj i).metric y
        (metricAlgebraicCurvatureTensorAt (Y.obj i).metric y)
        (rescalePinchingFunction (X.scale i) Phi (metricScalarAt (Y.obj i).metric y)) := by
    intro i y
    have h0 : (0:ℝ) ∈ (X.interval i).carrier := by
      rw [X.carrier_eq i]
      exact ⟨by linarith [X.depth_pos i], le_rfl⟩
    have h := X.pinching i 0 h0 y
    have hval : ((X.term i).S.base.rm04 (0:ℝ)) y =
        metricRm04At ((X.term i).S.base.metric 0) y := by
      simp only [SolutionFamily.rm04]
      exact metricRm04_apply _ _
    have hK : (X.term i).S.scalar (0:ℝ) y =
        metricScalarAt ((X.term i).S.base.metric 0) y := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar]
    simp only [Y, FlowSequence.atTime, PointedFlowData.atTime, SolutionOn.family_metric]
    refine fun n c v w => ?_
    have hh := h n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      hval, hK] at hh ⊢
    exact hh
  have hmain := sectional_nonnegative_of_pointed_admissible_pinching
    (X := Y) (L := P) (F := F)
    conv canonical_domains hPhi X.scale (fun i => X.scale_pos i) hQ hpin
  intro x _ v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [SecLower, _root_.MulZeroClass.zero_mul, metricRm04StandardAt_apply, hvec] using hmain x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.blowup_limit_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.blowup_limit_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.blowup_limit_nonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.blowup_limit_nonnegative

structure TerminalLimit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  space : PointedRiemannianManifold.{u, 0, 0} I3
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) space subseq
  converges : MetricConvergenceData maps
  canonical_domains : ∀ k,
    converges.domain k = CanonicalMetricCompactness.canonicalSourceData maps k
  capture : MetricSourceCapture maps
  precompact : ∀ i, IsCompact (closure (maps.partialDiffeomorph i).source)
  connected_domains : ∀ i, IsConnected (maps.partialDiffeomorph i).source
  nested : ∀ i, closure (maps.partialDiffeomorph i).source ⊆
    (maps.partialDiffeomorph (i + 1)).source
  connected : ConnectedSpace space.M
  orientation : TangentOrientationSection space.M
  orientation_preserved : ∀ i y, y ∈ (maps.partialDiffeomorph i).source →
    ∃ hf : Function.Bijective (mfderiv I3 I3 (maps.partialDiffeomorph i) y),
      PreservesTangentOrientationAt orientation (X.orientation (subseq i))
        (maps.partialDiffeomorph i) y hf
  complete : MetricComplete space
  nonnegative : SecLower space.metric 0 Set.univ
  scalar_one : metricScalarAt space.metric space.basepoint = 1
  scalar_bound : ∃ C : ℝ, ∀ x, metricScalarAt space.metric x ≤ C
  noncollapse : ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed space kappa' (Set.Ioc 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TerminalLimit

def ConvergesOn {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := P.M) D) : Prop :=
  ∀ K : Set P.M, IsCompact K → ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
      Set.Icc a b ⊆ (X.interval (f i)).carrier ∧
      K ⊆ (F.partialDiffeomorph i).source ∧
      Nonempty (MetricComparisonOn (fun s => S.base.metric s)
        (fun s => (X.term (f i)).S.base.metric s) (F.partialDiffeomorph i)
        K (Set.Icc a b) order eps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ConvergesOn


structure BackwardExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit X)
    (D : RealTimeInterval) where
  solution : SolutionOn (I := I3) (M := L.space.M) D
  isSolution : IsSolutionOn solution
  terminal : solution.base.metric 0 = L.space.metric
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  convergence : ConvergesOn (subsequenceMaps L.maps subseq strictMono) solution
  complete : ∀ t ∈ D.carrier,
    MetricComplete { L.space with metric := solution.base.metric t }
  nonnegative : ∀ t ∈ D.carrier, SecLower (solution.base.metric t) 0 Set.univ
  compact_time_bound : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, FlowMetricBall.rmNormSq solution t x ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BackwardExtension

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem metricNoncollapsed_atTime_of_spatiallyKappaNoncollapsedBelowScale
    {D : RealTimeInterval} (F : PointedFlowData.{u, 0, 0} I3 D)
    {kappa radius : ℝ}
    (h : SpatiallyKappaNoncollapsedBelowScale F.S kappa radius)
    {s : ℝ} (hs : s ∈ D.carrier) :
    MetricNoncollapsed (F.atTime s) kappa (_root_.Set.Ioc 0 radius) := by
  intro y r hr hrpos hcurv
  let B : FlowMetricBall F.S ⟨s, hs⟩ := ⟨y, r, hrpos⟩
  have hB : B.IsSpatiallyRmControlled := hcurv
  have hvol := (h.2 ⟨s, hs⟩ B hr.2 hB).2
  rw [ENNReal.ofReal_mul' (pow_nonneg hrpos.le 3), ENNReal.ofReal_pow hrpos.le]
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  simp only [hdim, B, FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
    volumeMeasureOn_eq_metric, SolutionOn.family_metric, PointedFlowData.atTime,
    riemannianBallOf] at hvol ⊢
  with_unfolding_all exact hvol

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricNoncollapsed_atTime_of_spatiallyKappaNoncollapsedBelowScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricNoncollapsed_atTime_of_spatiallyKappaNoncollapsedBelowScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricNoncollapsed_atTime_of_spatiallyKappaNoncollapsedBelowScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricNoncollapsed_atTime_of_spatiallyKappaNoncollapsedBelowScale

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
