import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

def mappedMetricQuadratic (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    (x : L.space.M) (v : TangentSpace I3 x) (i : ℕ) (t : ℝ) : ℝ :=
  ((X.term (L.subseq (k i))).S.base.metric t).inner
    (L.maps.partialDiffeomorph (k i) x)
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic

private theorem mappedMetricQuadratic_continuousOn
    (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    {delta a b : ℝ} (hle : delta ≤ depthBound)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v : TangentSpace I3 x) (i : ℕ) :
    ContinuousOn (mappedMetricQuadratic L k x v i) (Set.Icc a b) := by
  exact ((X.term (L.subseq (k i))).isSolution.smoothMetric.coeff_cont _ _ _).mono
    (hsub.trans (L.window_subset_carrier hle _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mappedMetricQuadratic_continuousOn target :: scope.openDecls } }

private theorem symmetricBilin_polarization {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (v w : V) :
    B v w = (B (v + w) (v + w) - B v v - B w w) / 2 := by
  simp only [map_add, add_apply, hB w v]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.symmetricBilin_polarization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.symmetricBilin_polarization target :: scope.openDecls } }

private theorem slabComparison_quadratic_bound
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v : TangentSpace I3 x) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc a b, (g t).inner x v v ≤ C := by
  obtain ⟨i, ⟨P⟩⟩ :=
    (hcomp {x} isCompact_singleton a b hab hsub 0 (1 / 2) (by norm_num)).exists
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (mappedMetricQuadratic_continuousOn L k hle hsub x v i)
  refine ⟨2 * (|C| + 1), by positivity, ?_⟩
  intro t ht
  have heq := P.pullback_eq t x (Set.mem_singleton x) (fun _ => v)
  change P.pullback t x (fun _ => v) = mappedMetricQuadratic L k x v i t at heq
  have hlo := (P.equivalence t ht x (Set.mem_singleton x) v).1
  rw [heq] at hlo
  have hupper : mappedMetricQuadratic L k x v i t ≤ C :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)
  nlinarith [le_abs_self C]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_quadratic_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_quadratic_bound target :: scope.openDecls } }

theorem slabComparison_metricQuadratic_tendstoUniformlyOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v : TangentSpace I3 x) :
    TendstoUniformlyOn (mappedMetricQuadratic L k x v)
      (fun t => (g t).inner x v v) _root_.Filter.atTop (Set.Icc a b) := by
  obtain ⟨C, hCpos, hC⟩ := slabComparison_quadratic_bound L hle hcomp hab hsub x v
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  let eps : ℝ := eta / (2 * C)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hmul : eps * (2 * C) = eta := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hcomp {x} isCompact_singleton a b hab hsub 0 eps heps] with i hi
  obtain ⟨P⟩ := hi
  intro t ht
  have heq := P.pullback_eq t x (Set.mem_singleton x) (fun _ => v)
  change P.pullback t x (fun _ => v) = mappedMetricQuadratic L k x v i t at heq
  obtain ⟨hlo, hhi⟩ := P.equivalence t ht x (Set.mem_singleton x) v
  rw [heq] at hlo hhi
  have hbound := mul_le_mul_of_nonneg_left (hC t ht) heps.le
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricQuadratic_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricQuadratic_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricQuadratic_tendstoUniformlyOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricQuadratic_tendstoUniformlyOn

theorem slabComparison_metricCoeff_tendsto
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    _root_.Filter.Tendsto (fun i => ((X.term (L.subseq (k i))).S.base.metric t).inner
      (L.maps.partialDiffeomorph (k i) x)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w))
      atTop (𝓝 ((g t).inner x v w)) := by
  have hquad (u : TangentSpace I3 x) :=
    (slabComparison_metricQuadratic_tendstoUniformlyOn L hle hcomp hab hsub x u).tendsto_at ht
  have hpolar (i : ℕ) : ((X.term (L.subseq (k i))).S.base.metric t).inner
      (L.maps.partialDiffeomorph (k i) x)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
      (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w) =
        (mappedMetricQuadratic L k x (v + w) i t - mappedMetricQuadratic L k x v i t -
          mappedMetricQuadratic L k x w i t) / 2 := by
    let F := mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x
    let B := ((X.term (L.subseq (k i))).S.base.metric t).inner
      (L.maps.partialDiffeomorph (k i) x)
    change B (F v) (F w) = (B (F (v + w)) (F (v + w)) - B (F v) (F v) -
      B (F w) (F w)) / 2
    rw [F.map_add]
    exact symmetricBilin_polarization B
      (((X.term (L.subseq (k i))).S.base.metric t).symm (L.maps.partialDiffeomorph (k i) x))
      (F v) (F w)
  have hlimit := symmetricBilin_polarization ((g t).inner x) ((g t).symm x) v w
  have h := (((hquad (v + w)).sub (hquad v)).sub (hquad w)).div_const 2
  simpa only [← hpolar, ← hlimit] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_tendsto

theorem slabComparison_metricCoeff_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    ContinuousOn (fun t => (g t).inner x v w) (Set.Icc a b) := by
  have hquad (u : TangentSpace I3 x) :
      ContinuousOn (fun t => (g t).inner x u u) (Set.Icc a b) :=
    (slabComparison_metricQuadratic_tendstoUniformlyOn L hle hcomp hab hsub x u).continuousOn
      (Filter.Eventually.of_forall (mappedMetricQuadratic_continuousOn L k hle hsub x u)).frequently
  exact (((hquad (v + w)).sub (hquad v)).sub (hquad w)).div_const 2 |>.congr
    (fun t _ => symmetricBilin_polarization ((g t).inner x) ((g t).symm x) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.slabComparison_metricCoeff_continuousOn

theorem IsSlabLimit.metricCoeff_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    ContinuousOn (fun t => (g t).inner x v w) (Set.Icc (-delta) 0) := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_metricCoeff_continuousOn L hle hcomp
    (by linarith) Set.Subset.rfl x v w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricCoeff_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricCoeff_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricCoeff_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.IsSlabLimit.metricCoeff_continuousOn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
