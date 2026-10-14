import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section Calculus

variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {l : Filter J} [NeBot l] {U : Set E}

theorem tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn
    (hU : IsOpen U) (f : J → E → F) (f₀ : E → F)
    (hf : ∀ i, DifferentiableOn ℝ (f i) U)
    (hc : UniformCauchySeqOn (fun i => fderiv ℝ (f i)) l U)
    (hlim : ∀ x ∈ U, _root_.Filter.Tendsto (fun i => f i x) l (𝓝 (f₀ x))) :
    TendstoUniformlyOn (fun i => fderiv ℝ (f i)) (fderiv ℝ f₀) l U := by
  let q : E → E →L[ℝ] F := fun x => _root_.Filter.limUnder l (fun i => fderiv ℝ (f i) x)
  have hq (x : E) (hx : x ∈ U) :
      Tendsto (fun i => fderiv ℝ (f i) x) l (𝓝 (q x)) :=
    (hc.cauchy_map hx).le_nhds_lim
  have hconv := hc.tendstoUniformlyOn_of_tendsto hq
  refine hconv.congr_right fun x hx => ?_
  exact (hasFDerivAt_of_tendstoUniformlyOn hU hconv
    (fun i y hy => ((hf i y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt)
    hlim hx).fderiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn

theorem tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn
    (hU : IsOpen U) (f : J → E → F) (f₀ : E → F) (N : ℕ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hc : ∀ r ≤ N, UniformCauchySeqOn (fun i => iteratedFDeriv ℝ r (f i)) l U)
    (hlim : ∀ x ∈ U, _root_.Filter.Tendsto (fun i => f i x) l (𝓝 (f₀ x))) :
    ∀ r ≤ N, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ r (f i))
      (iteratedFDeriv ℝ r f₀) l U := by
  intro r
  induction r with
  | zero =>
      intro hN
      refine (hc 0 hN).tendstoUniformlyOn_of_tendsto fun x hx => ?_
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
        ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto (f₀ x)).comp
          (hlim x hx)
  | succ r ih =>
      intro hN
      let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) F
      have hc' : UniformCauchySeqOn
          (fun i => fderiv ℝ (iteratedFDeriv ℝ r (f i))) l U := by
        simpa only [fderiv_iteratedFDeriv] using
          C.isometry.uniformContinuous.comp_uniformCauchySeqOn (hc (r + 1) hN)
      have hd := tendstoUniformlyOn_fderiv_of_uniformCauchySeqOn hU
        (fun i => iteratedFDeriv ℝ r (f i)) (iteratedFDeriv ℝ r f₀)
        (fun i x hx =>
          (((hf i x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
            (by exact_mod_cast (ENat.natCast_lt_top r))).differentiableWithinAt)
        hc' (fun x hx => (ih (Nat.le_of_succ_le hN)).tendsto_at hx)
      simpa only [iteratedFDeriv_succ_eq_comp_left] using
        C.symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn

end Calculus

section TimeControl

variable {X Y : Type*} [PseudoMetricSpace Y]

theorem uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith
    {a b : ℝ} (hab : a < b) (f : ℝ → X → Y) (U : Set X) (C : ℝ≥0)
    (hC : ∀ x ∈ U, LipschitzOnWith C (fun s => f s x) (Set.Ioo a b)) :
    UniformCauchySeqOn f (𝓝[<] b) U := by
  intro V hV
  obtain ⟨eps, heps, hsub⟩ := Metric.mem_uniformity_dist.mp hV
  have htime : _root_.Filter.Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝 b) := nhdsWithin_le_nhds
  have ht : _root_.Filter.Tendsto (fun p : ℝ × ℝ => (C : ℝ) * _root_.Dist.dist p.1 p.2)
      ((𝓝[<] b) ×ˢ (𝓝[<] b)) (𝓝 0) := by
    simpa only [dist_self, _root_.MulZeroClass.mul_zero, Function.comp_def] using
      (tendsto_const_nhds.mul
        ((htime.comp _root_.Filter.tendsto_fst).dist (htime.comp _root_.Filter.tendsto_snd)))
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ioo a b := Ioo_mem_nhdsLT hab
  filter_upwards [ht.eventually (gt_mem_nhds heps),
    hnear.prod_mk hnear] with p hp hmem
  intro x hx
  exact hsub ((hC x hx).dist_le_mul p.1 hmem.1 p.2 hmem.2 |>.trans_lt hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith

end TimeControl

section MetricCoordinates

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

local instance terminalFiniteJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalFiniteJetsC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalFiniteJetsC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalFiniteJetsC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalFiniteJetsC1

theorem solution_metric_coordinate_jets_tendsto_terminal_of_uniformCauchy
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b : ℝ} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (x₀ : M) (i j : CoordinateIdx (𝕜 := ℝ) E)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt I x₀).target)
    (N : ℕ)
    (hc : ∀ r ≤ N, UniformCauchySeqOn (fun t => iteratedFDeriv ℝ r
      (metricFlatModelInChartComponent (I := I) (S.base.metric t) x₀ i j)) (𝓝[<] b) U) :
    ∀ r ≤ N, TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
      (metricFlatModelInChartComponent (I := I) (S.base.metric t) x₀ i j))
      (iteratedFDeriv ℝ r
        (metricFlatModelInChartComponent (I := I) (S.base.metric b) x₀ i j)) (𝓝[<] b) U := by
  refine tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn hU _ _ N ?_ hc ?_
  · intro t y hy
    have h := metricFlatModelInChart_component_contDiffWithinAt_of_mem
      (I := I) (S.base.metric t) x₀ (hchart hy) i j
    rw [ModelWithCorners.range_eq_univ (I := I)] at h
    exact (contDiffWithinAt_univ.mp h).contDiffWithinAt
  · intro y hy
    let p := (extChartAt I x₀).symm y
    let v := (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ p
      ((Module.finBasis ℝ E) i)
    let w := (_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ p
      ((Module.finBasis ℝ E) j)
    have heq (t : ℝ) :
        metricFlatModelInChartComponent (I := I) (S.base.metric t) x₀ i j y =
          (S.base.metric t).inner p v w :=
      metricFlatModelInChart_apply_of_target (I := I) (S.base.metric t) x₀
        (hchart hy) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
    simp_rw [heq]
    have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ioo a b := Ioo_mem_nhdsLT hab
    have htime : _root_.Filter.Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝[D.carrier] b) :=
      tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,
        hnear.mono fun t ht => hslab ⟨ht.1.le, ht.2.le⟩⟩
    exact (hS.smoothMetric.coeff_cont p v w b (hslab ⟨hab.le, le_rfl⟩)).tendsto.comp htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_metric_coordinate_jets_tendsto_terminal_of_uniformCauchy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_metric_coordinate_jets_tendsto_terminal_of_uniformCauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_metric_coordinate_jets_tendsto_terminal_of_uniformCauchy ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_metric_coordinate_jets_tendsto_terminal_of_uniformCauchy

end MetricCoordinates

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
