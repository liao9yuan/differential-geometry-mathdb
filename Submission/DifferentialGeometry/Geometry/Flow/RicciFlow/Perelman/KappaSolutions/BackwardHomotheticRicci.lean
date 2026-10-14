import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRoundPinchingRigidity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance pastHomothetyTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyTopology
local instance pastHomothetyCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyCharted
local instance pastHomothetySmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySmooth
local instance pastHomothetyC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyC1
local instance pastHomothetyT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetyT2
local instance pastHomothetySigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pastHomothetySigma

omit [I.Boundaryless] in
theorem backward_homothetic_ricci
    (g : SmoothRiemannianMetric I F.M) {a T : ℝ} (ha : a ≤ 0) (haT : a < T)
    (hmetric : ∀ (t : ℝ) (ht : t ≤ a), F.S.family.metric t =
      scaleMetric (4 * (T - t)) (mul_pos (by norm_num) (sub_pos.mpr (ht.trans_lt haT))) g)
    {s : ℝ} (hs : s < a) (x : F.M) (v w : TangentSpace I x) :
    F.S.ricciAt s x (vec2 v w) = 2 * g.inner x v w := by
  have hevent : (fun t : ℝ => (F.S.family.metric t).inner x v w) =ᶠ[𝓝 s]
      (fun t : ℝ => 4 * (T - t) * g.inner x v w) := by
    filter_upwards [Iio_mem_nhds hs] with t ht
    rw [hmetric t ht.le, scaleMetric_inner]
  have hlinear : HasDerivAt (fun t : ℝ => 4 * (T - t) * g.inner x v w)
      (-4 * g.inner x v w) s := by
    have h := (((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul 4).mul_const
      (g.inner x v w)
    simpa using h
  have hactual := hlinear.congr_of_eventuallyEq hevent
  have hpde := metricDerivAt F.S F.isSolution ⟨s, hs.trans_le ha⟩ x v w
  have hderiv := hpde.unique hactual
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_ricci ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_ricci

omit [I.Boundaryless] in
theorem backward_homothetic_einstein3
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I F.M)
    {a T : ℝ} (ha : a ≤ 0) (haT : a < T)
    (hmetric : ∀ (t : ℝ) (ht : t ≤ a), F.S.family.metric t =
      scaleMetric (4 * (T - t)) (mul_pos (by norm_num) (sub_pos.mpr (ht.trans_lt haT))) g)
    {s : ℝ} (hs : s < a) (x : F.M) :
    F.S.scalar s x = 3 / (2 * (T - s)) ∧
      ∀ v w : TangentSpace I x, F.S.ricciAt s x (vec2 v w) =
        (F.S.scalar s x / 3) * (F.S.family.metric s).inner x v w := by
  have hTs : 0 < T - s := sub_pos.mpr (hs.trans haT)
  have hcoef (v w : TangentSpace I x) : F.S.ricciAt s x (vec2 v w) =
      (1 / (2 * (T - s))) * (F.S.family.metric s).inner x v w := by
    rw [backward_homothetic_ricci F g ha haT hmetric hs x v w,
      hmetric s hs.le, scaleMetric_inner]
    field_simp [hTs.ne']
    ring
  have hRic : F.S.ricciAt s x =
      (1 / (2 * (T - s))) • metricTensor0S (F.S.family.metric s) x := by
    ext v
    have hv : v = vec2 (v 0) (v 1) := by
      funext i
      fin_cases i <;> rfl
    rw [hv, Tensor0SSpace.smul_apply, metricTensor0S_apply]
    exact hcoef _ _
  have htrace := SolutionOn.scalar_eq_metricTrace F.S s x
  rw [hRic, metricTracePair0SAt_smul, metricTracePair0SAt_metric, hdim] at htrace
  have hscalar : F.S.scalar s x = 3 / (2 * (T - s)) := by
    calc
      _ = (1 / (2 * (T - s))) * (3 : ℝ) := by
        simpa only [Nat.cast_ofNat] using htrace
      _ = _ := by ring
  refine ⟨hscalar, fun v w => ?_⟩
  rw [hscalar]
  convert hcoef v w using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_einstein3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_einstein3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_einstein3 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backward_homothetic_einstein3


theorem ancient_sphericalSpaceFormFlow_of_backward_homothety
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hcompact : CompactSpace F.M) (g : SmoothRiemannianMetric I F.M)
    {a T : ℝ} (ha : a ≤ 0) (haT : a < T)
    (hmetric : ∀ (t : ℝ) (ht : t ≤ a), F.S.family.metric t =
      scaleMetric (4 * (T - t)) (mul_pos (by norm_num) (sub_pos.mpr (ht.trans_lt haT))) g) :
    IsShrinkingSphericalSpaceFormFlow F := by
  let times : ℕ → ℝ := fun i => a - ((i : ℝ) + 1)
  let c : ℕ → ℝ := fun i => 1 / 3 - (1 / 3) / ((i : ℝ) + 1)
  have hplus : _root_.Filter.Tendsto (fun i : ℕ => (i : ℝ) + 1) _root_.Filter.atTop atTop :=
    tendsto_atTop_mono (fun i => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have htimes : _root_.Filter.Tendsto times _root_.Filter.atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    filter_upwards [hplus.eventually_ge_atTop (a - b)] with i hi
    dsimp only [times]
    linarith
  have hc : _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 (1 / 3)) := by
    have hz := tendsto_inv_atTop_zero.comp hplus
    have h : _root_.Filter.Tendsto (fun i : ℕ => (1 / 3 : ℝ) - (1 / 3) * ((i : ℝ) + 1)⁻¹)
        atTop (𝓝 ((1 / 3 : ℝ) - (1 / 3) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    simpa only [c, div_eq_mul_inv, _root_.MulZeroClass.mul_zero, sub_zero] using h
  have hcUpper (i : ℕ) : c i < 1 / 3 := by
    have hp : 0 < (1 / 3 : ℝ) / ((i : ℝ) + 1) := by positivity
    dsimp only [c]
    linarith
  have hbefore (i : ℕ) : times i < a := by
    dsimp only [times]
    have hi := Nat.cast_nonneg (α := ℝ) i
    linarith
  have hpositive (i : ℕ) (x : F.M) : 0 < F.S.scalar (times i) x := by
    rw [(backward_homothetic_einstein3 F hdim g ha haT hmetric (hbefore i) x).1]
    exact div_pos (by norm_num) (mul_pos (by norm_num) (sub_pos.mpr ((hbefore i).trans haT)))
  have hpinch (i : ℕ) (x : F.M) (v : TangentSpace I x) :
      c i * F.S.scalar (times i) x * (F.S.family.metric (times i)).inner x v v ≤
        F.S.ricciAt (times i) x (vec2 v v) := by
    rw [(backward_homothetic_einstein3 F hdim g ha haT hmetric (hbefore i) x).2 v v]
    calc
      _ ≤ ((1 / 3 : ℝ) * F.S.scalar (times i) x) *
          (F.S.family.metric (times i)).inner x v v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcUpper i).le (hpositive i x).le)
          (DifferentialGeometry.metric_inner_self_nonneg
            (F.S.family.metric (times i)) x v)
      _ = _ := by ring
  exact ancient_sphericalSpaceFormFlow_of_backward_pinching F hdim hconn hcompact
    htimes hc hcUpper hpositive hpinch

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_backward_homothety then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_backward_homothety"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_backward_homothety ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_backward_homothety

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
