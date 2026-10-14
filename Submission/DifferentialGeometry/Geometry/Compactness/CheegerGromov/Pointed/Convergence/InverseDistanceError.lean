import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance distanceErrorLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitTopology target :: scope.openDecls } }
private local instance distanceErrorLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitCharted target :: scope.openDecls } }
private local instance distanceErrorLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorLimitSmooth target :: scope.openDecls } }
private local instance distanceErrorSourceTopology (k : ℕ) :
    TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceTopology target :: scope.openDecls } }
private local instance distanceErrorSourceCharted (k : ℕ) :
    ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceCharted target :: scope.openDecls } }
private local instance distanceErrorSourceSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.distanceErrorSourceSmooth target :: scope.openDecls } }

theorem tendsto_pointed_inverse_distance_sub_source
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (y z : ∀ k : ℕ, (X.obj (subseq k)).M)
    (hball : ∀ᶠ k in _root_.Filter.atTop,
      y k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho ∧
      z k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho) :
    _root_.Filter.Tendsto (fun k =>
      (riemannianEDistOf (I := I) L.metric
        ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k))).toReal -
      (riemannianEDistOf (I := I) (X.obj (subseq k)).metric (y k) (z k)).toReal)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  let epsilon := eta / (8 * rho + 1)
  have hden : 0 < 8 * rho + 1 := by linarith
  have hepsilon : 0 < epsilon := div_pos heta hden
  have hcancel : epsilon * (8 * rho + 1) = eta := div_mul_cancel₀ eta hden.ne'
  obtain ⟨_, k0, hk0⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete rho hrho 1 zero_lt_one
  obtain ⟨_, k1, hk1⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete rho hrho epsilon hepsilon
  filter_upwards [hball, _root_.Filter.eventually_ge_atTop k0, _root_.Filter.eventually_ge_atTop k1] with k hkb hk0' hk1'
  let g := (X.obj (subseq k)).metric
  let p := (X.obj (subseq k)).basepoint
  let _ : _root_.Bundle.RiemannianBundle (fun q : (X.obj (subseq k)).M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have htriangle : riemannianEDistOf g (y k) (z k) ≤
      riemannianEDistOf g (y k) p + riemannianEDistOf g p (z k) :=
    Manifold.riemannianEDist_triangle
  have hcomm : riemannianEDistOf g (y k) p = riemannianEDistOf g p (y k) :=
    Manifold.riemannianEDist_comm
  have habound : riemannianEDistOf g (y k) (z k) ≤ ENNReal.ofReal (2 * rho) := by
    calc
      _ ≤ riemannianEDistOf g p (y k) + riemannianEDistOf g p (z k) := by
        simpa only [hcomm] using htriangle
      _ ≤ ENNReal.ofReal rho + ENNReal.ofReal rho := add_le_add hkb.1 hkb.2
      _ = ENNReal.ofReal (2 * rho) := by rw [← ENNReal.ofReal_add hrho hrho, two_mul]
  have hafin : riemannianEDistOf g (y k) (z k) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top habound
  let a := (riemannianEDistOf g (y k) (z k)).toReal
  let b := (riemannianEDistOf L.metric
    ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k))).toReal
  have ha : a ≤ 2 * rho := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top habound
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * rho)] using hh
  have hc0 := (hk0 k hk0').2 (y k) hkb.1 (z k) hkb.2
  have hbfin : riemannianEDistOf L.metric
      ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc0.1
  have hb : b ≤ 4 * rho := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc0.1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 : ℝ) + 1)] at hh
    change b ≤ (1 + 1) * a at hh
    linarith
  have hc := (hk1 k hk1').2 (y k) hkb.1 (z k) hkb.2
  have hba : b ≤ (1 + epsilon) * a := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hafin) hc.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using hh
  have hab : a ≤ (1 + epsilon) * b := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbfin) hc.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using hh
  change _root_.Dist.dist (b - a) 0 < eta
  rw [Real.dist_eq, sub_zero, abs_lt]
  have hea := mul_le_mul_of_nonneg_left ha hepsilon.le
  have heb := mul_le_mul_of_nonneg_left hb hepsilon.le
  constructor <;> nlinarith [mul_nonneg hepsilon.le hrho]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_inverse_distance_sub_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_inverse_distance_sub_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_inverse_distance_sub_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_pointed_inverse_distance_sub_source

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
