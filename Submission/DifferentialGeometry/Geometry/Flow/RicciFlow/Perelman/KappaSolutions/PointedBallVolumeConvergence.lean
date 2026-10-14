import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBallVolumeUpper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance fixedBallLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitTopology target :: scope.openDecls } }
private local instance fixedBallLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitCharted target :: scope.openDecls } }
private local instance fixedBallLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitSmooth target :: scope.openDecls } }
private local instance fixedBallLimitT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitT2 target :: scope.openDecls } }
private local instance fixedBallLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitSigma target :: scope.openDecls } }
private local instance fixedBallLimitMeasurable : MeasurableSpace L.M := borel L.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitMeasurable target :: scope.openDecls } }
private local instance fixedBallLimitBorel : BorelSpace L.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallLimitBorel target :: scope.openDecls } }

private local instance fixedBallSourceTopology (i : ℕ) : TopologicalSpace (X.obj i).M :=
  (X.obj i).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceTopology target :: scope.openDecls } }
private local instance fixedBallSourceCharted (i : ℕ) : ChartedSpace H (X.obj i).M :=
  (X.obj i).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceCharted target :: scope.openDecls } }
private local instance fixedBallSourceSmooth (i : ℕ) : IsManifold I ∞ (X.obj i).M :=
  (X.obj i).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceSmooth target :: scope.openDecls } }
private local instance fixedBallSourceOne (i : ℕ) : IsManifold I 1 (X.obj i).M :=
  IsManifold.of_le (I := I) (M := (X.obj i).M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceOne target :: scope.openDecls } }
private local instance fixedBallSourceT2 (i : ℕ) : T2Space (X.obj i).M := (X.obj i).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceT2 target :: scope.openDecls } }
private local instance fixedBallSourceSigma (i : ℕ) : SigmaCompactSpace (X.obj i).M :=
  (X.obj i).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceSigma target :: scope.openDecls } }
private local instance fixedBallSourceTangentT2 (i : ℕ) :
    T2Space (TangentBundle I (X.obj i).M) := (X.obj i).t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceTangentT2 target :: scope.openDecls } }
private local instance fixedBallSourceMeasurable (i : ℕ) : MeasurableSpace (X.obj i).M :=
  borel (X.obj i).M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceMeasurable target :: scope.openDecls } }
private local instance fixedBallSourceBorel (i : ℕ) : BorelSpace (X.obj i).M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.fixedBallSourceBorel target :: scope.openDecls } }

theorem pointed_ball_volume_lower_of_eventually_at_radius
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L)
    (hsourceComplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) (X.obj i).metric 0)
    {r : ℝ} (hr : 0 < r) (V : ℝ≥0∞)
    (hsource : ∀ᶠ k : ℕ in _root_.Filter.atTop, V ≤
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
        (X.obj (subseq k)).metric
        (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r)) :
    V ≤ riemannianVolumeMeasure (I := I) (M := L.M) L.metric
      (riemannianBallOf L.metric L.basepoint r) := by
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  let n := Module.finrank ℝ E
  let mu := riemannianVolumeMeasure (I := I) (M := L.M) L.metric
  let A := riemannianBallOf L.metric L.basepoint r
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : _root_.Filter.Tendsto epsilon _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : _root_.Filter.Tendsto (fun j => 1 + epsilon j) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) _root_.Filter.atTop (𝓝 1)).add hepsilon
  have hs : _root_.Filter.Tendsto s _root_.Filter.atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℕ => r) _root_.Filter.atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hR0 : ENNReal.ofReal (r ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
  have hpow : _root_.Filter.Tendsto (fun j => ENNReal.ofReal ((s j) ^ n)) _root_.Filter.atTop
      (𝓝 (ENNReal.ofReal (r ^ n))) := ENNReal.tendsto_ofReal (hs.pow n)
  have hleft := ENNReal.Tendsto.const_mul (a := V) hpow (Or.inl hR0)
  have hsqrt : _root_.Filter.Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ n)) _root_.Filter.atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow n)
  have hcoef : _root_.Filter.Tendsto (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hvol : _root_.Filter.Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) * mu A) _root_.Filter.atTop (𝓝 (mu A)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  have hright : _root_.Filter.Tendsto (fun j =>
      (ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) * mu A) * ENNReal.ofReal (r ^ n))
      atTop (𝓝 (mu A * ENNReal.ofReal (r ^ n))) :=
    ENNReal.Tendsto.mul_const hvol (Or.inr ENNReal.ofReal_ne_top)
  have hcross : V * ENNReal.ofReal (r ^ n) ≤ mu A * ENNReal.ofReal (r ^ n) := by
    apply le_of_tendsto_of_tendsto' hleft hright
    intro j
    have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
    have h1 : 0 < 1 + epsilon j := by linarith
    have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
    have hbuffer : (1 + epsilon j) * s j < r := by
      calc
        (1 + epsilon j) * s j = r / (1 + epsilon j) := by
          dsimp only [s]
          field_simp [ne_of_gt h1]
        _ < r := (div_lt_iff₀ h1).2 (by nlinarith)
    have hsjr : s j ≤ r := by
      have hstep : s j ≤ (1 + epsilon j) * s j := by
        nlinarith [mul_nonneg he.le hsj.le]
      exact hstep.trans hbuffer.le
    obtain ⟨k0, hk0⟩ := exists_pointed_buffered_ball_volume_le
      C hreference hcomplete hsj he hbuffer he
    obtain ⟨k1, hk1⟩ := eventually_atTop.mp hsource
    let k := _root_.Max.max k0 k1
    let _ : ConnectedSpace (X.obj (subseq k)).M := hconnected (subseq k)
    have hg : RiemannianMetricComplete (I := I) (X.obj (subseq k)).metric :=
      ⟨MetricComplete.complete (I := I) (X.obj (subseq k))
        (hsourceComplete.complete (subseq k))⟩
    have hbishop := (riemannianBallOf_volume_bishop_nonnegative
      (I := I) (M := (X.obj (subseq k)).M) (X.obj (subseq k)).metric hg
      (hRic (subseq k)) (X.obj (subseq k)).basepoint).1 (s j) r hsj hsjr
    calc
      V * ENNReal.ofReal ((s j) ^ n) ≤
          riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
            (X.obj (subseq k)).metric
            (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r) *
              ENNReal.ofReal ((s j) ^ n) :=
        mul_le_mul_left (hk1 k (Nat.le_max_right _ _)) _
      _ ≤ ENNReal.ofReal (r ^ n) *
          riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
            (X.obj (subseq k)).metric
            (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint (s j)) :=
        hbishop
      _ ≤ ENNReal.ofReal (r ^ n) *
          (ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) * mu A) :=
        mul_le_mul_right (hk0 k (Nat.le_max_left _ _)) _
      _ = (ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) * mu A) *
          ENNReal.ofReal (r ^ n) := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_left hR0 ENNReal.ofReal_ne_top).1 hcross

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_lower_of_eventually_at_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_lower_of_eventually_at_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_lower_of_eventually_at_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_lower_of_eventually_at_radius

theorem pointed_ball_volume_eq_of_eventually_eq
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L)
    (hsourceComplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) (X.obj i).metric 0)
    {r : ℝ} (hr : 0 < r) (V : ℝ≥0∞)
    (hsource : ∀ᶠ k : ℕ in _root_.Filter.atTop,
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
        (X.obj (subseq k)).metric
        (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r) = V) :
    riemannianVolumeMeasure (I := I) (M := L.M) L.metric
      (riemannianBallOf L.metric L.basepoint r) = V := by
  apply le_antisymm
  · exact pointed_ball_volume_upper_of_eventually C hcanonical hcomplete hr V
      (hsource.mono fun _ h => h.le)
  · exact pointed_ball_volume_lower_of_eventually_at_radius C hcanonical hcomplete
      hsourceComplete hconnected hRic hr V (hsource.mono fun _ h => h.ge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_eq_of_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_eq_of_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_eq_of_eventually_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_ball_volume_eq_of_eventually_eq

theorem tendsto_pointed_ball_volume_of_eventually_eq
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : MetricComplete (I := I) L)
    (hsourceComplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hRic : ∀ i : ℕ, RicciBoundedBelow (I := I) (X.obj i).metric 0)
    {r : ℝ} (hr : 0 < r) (V : ℝ≥0∞)
    (hsource : ∀ᶠ k : ℕ in _root_.Filter.atTop,
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
        (X.obj (subseq k)).metric
        (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r) = V) :
    _root_.Filter.Tendsto (fun k : ℕ =>
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M)
        (X.obj (subseq k)).metric
        (riemannianBallOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint r))
      atTop (𝓝 (riemannianVolumeMeasure (I := I) (M := L.M) L.metric
        (riemannianBallOf L.metric L.basepoint r))) := by
  rw [pointed_ball_volume_eq_of_eventually_eq C hcanonical hcomplete
    hsourceComplete hconnected hRic hr V hsource]
  exact tendsto_const_nhds.congr' (hsource.mono fun _ h => h.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_ball_volume_of_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_ball_volume_of_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_ball_volume_of_eventually_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_ball_volume_of_eventually_eq

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
