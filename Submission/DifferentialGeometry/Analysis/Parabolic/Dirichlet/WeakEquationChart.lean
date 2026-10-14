import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationTimeTest
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakFormChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem IsWeakEvolutionSolution.exists_timeH1_integral_chart
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) (v : SmoothScalarDirichlet q)
    (hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    ∃ w : timeH1 ℝ T,
      w.initial = ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric 0) α y *
          (f₀ ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) ∧
      (fun t => ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
            scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN))) =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ y in interior (extChartAt I_hs α).target,
          chartDensityOnE (I := I_hs) (G.metric t) α y *
            ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t
                ((extChartAt I_hs α).symm y) *
              (H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
                scalarOnE (I := I_hs) α v.toFun y)) ∂(modelHaar (E := EuN))) +
        ∫ y in interior (extChartAt I_hs α).target,
          chartDensityOnE (I := I_hs) (G.metric t) α y *
            H1ComplDirichletToLp q (u t) ((extChartAt I_hs α).symm y) *
            (chartVossWeylLaplacian (I := I_hs) (G.metric t) α v.toFun
                ((extChartAt I_hs α).symm y) -
              (∑ i : Fin (Module.finrank ℝ EuN), chartCoeffOnE (I := I_hs) α (X t) i y *
                Tensor.Coordinates.partialDeriv (E := EuN) i
                  (scalarOnE (I := I_hs) α v.toFun) y) -
              localDivergence (I := I_hs) (G.metric t) α (X t) ((extChartAt I_hs α).symm y) *
                scalarOnE (I := I_hs) α v.toFun y - a t * scalarOnE (I := I_hs) α v.toFun y)
          ∂(modelHaar (E := EuN)) := by
  obtain ⟨w, hwinit, hwmass, hwderiv⟩ := hu.exists_timeH1_integral v
  have hm (t : ℝ) (U : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) :
      (∫ x, U x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) =
      ∫ y in interior (extChartAt I_hs α).target,
        chartDensityOnE (I := I_hs) (G.metric t) α y *
          (U ((extChartAt I_hs α).symm y) * scalarOnE (I := I_hs) α v.toFun y)
        ∂(modelHaar (E := EuN)) := by
    simpa only [one_mul] using integral_mul_smooth_test_eq_integral_chart
      (G.metric t) α U v hv (c := fun _ => 1) measurable_const
  have htr : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_hs) G.metric p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    apply continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      (I := I_hs) (M := M) (g := G.metric) D.regular_isOpen
    intro β i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) β i j
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ _root_.Set.Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← _root_.MeasureTheory.restrict_Ico_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ico
  refine ⟨w, hwinit.trans (hm 0 f₀), ?_, ?_⟩
  · filter_upwards [hwmass] with t ht
    exact (hm t (H1ComplDirichletToLp q (u t))).symm.trans ht
  · filter_upwards [hwderiv, hmem] with t ht htc
    rw [ht, integral_adjoint_test_eq_integral_chart (G.metric t) α (X t) (a t)
      (H1ComplDirichletToLp q (u t)) v hv]
    congr 1
    have hc : Measurable
        (fun x : M => (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x) := by
      have hct : Continuous (fun x : M => traceTimeDerivMetric (I := I_hs) G.metric t x) := by
        simpa only [Function.comp_def] using htr.comp_continuous
          (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
          (fun x => ⟨hreg ⟨htc.1, htc.2.le⟩, Set.mem_univ x⟩)
      exact (hct.const_mul (1 / 2 : ℝ)).measurable
    exact integral_mul_smooth_test_eq_integral_chart
      (G.metric t) α (H1ComplDirichletToLp q (u t)) v hv hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_chart ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

theorem IsWeakEvolutionSolution.exists_timeH1_integral_euclidean
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuN, (TangentSpace I_hs : M → Type _)⟯}
    {a : ℝ → ℝ} {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M, (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (α : M) (ψ : EuStd → ℝ)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    let e := toEuclidean (E := EuN)
    let Ω := e '' interior (extChartAt I_hs α).target
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    ∃ w : timeH1 ℝ T,
      w.initial = ∫ z in Ω, ρ 0 z * (f₀ (x z) * ψ z) ∧
      (fun t => ∫ z in Ω, ρ t z * (H1ComplDirichletToLp q (u t) (x z) * ψ z))
        =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] fun t =>
        (∫ z in Ω, ρ t z *
          ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
            (H1ComplDirichletToLp q (u t) (x z) * ψ z))) +
        ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
          ((∑ i : Fin (Module.finrank ℝ EuN),
            fderiv ℝ (fun z' : EuStd =>
              (∑ j : Fin (Module.finrank ℝ EuN),
                A t i j z' * fderiv ℝ ψ z' (EuclideanSpace.single j 1)) * ρ t z') z
                (EuclideanSpace.single i 1)) / ρ t z -
            (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
              fderiv ℝ ψ z (EuclideanSpace.single i 1)) -
            localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * ψ z - a t * ψ z) := by
  let e := toEuclidean (E := EuN)
  let Ω := e '' interior (extChartAt I_hs α).target
  let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
  let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
  let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
  let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
  have hs : tsupport ψ ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I_hs) (M := M) α :=
    hψ_supp.trans (Set.image_mono interior_subset)
  let v : SmoothScalarDirichlet q :=
    ⟨DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α ψ,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback_contMDiff α hψ_smooth hψ_cpt hs,
      DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset_interior
        α hψ_cpt hψ_supp⟩
  have hv : tsupport v.toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source := by
    intro z hz
    obtain ⟨y, ⟨z', hz', rfl⟩, rfl⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.tsupport_chartPullback_subset α hψ_cpt hs hz
    have ht : e.symm z' ∈ (extChartAt I_hs α).target := by
      have hz's := hs hz'
      rwa [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm]
        at hz's
    have hm := (extChartAt I_hs α).map_target ht
    rwa [extChartAt_source] at hm
  have hm (t : ℝ) (U : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (c : M → ℝ) (hc : Measurable c) :
      (∫ x, c x * (U x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) =
      ∫ z in Ω, ρ t z * (c (x z) * (U (x z) * ψ z)) :=
    integral_mul_chartPullback_eq_integral_euclidean (G.metric t) α U v ψ hv rfl hc
  have hm₀ (t : ℝ) (U : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) :
      (∫ x, U x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) =
      ∫ z in Ω, ρ t z * (U (x z) * ψ z) := by
    simpa only [one_mul] using hm t U (fun _ => 1) measurable_const
  obtain ⟨w, hwinit, hwmass, hwderiv⟩ := hu.exists_timeH1_integral v
  have htr : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_hs) G.metric p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    apply continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      (I := I_hs) (M := M) (g := G.metric) D.regular_isOpen
    intro β i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) β i j
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ _root_.Set.Icc (0 : ℝ) T :=
    _root_.MeasureTheory.self_mem_ae_restrict measurableSet_Icc
  refine ⟨w, hwinit.trans (hm₀ 0 f₀), ?_, ?_⟩
  · filter_upwards [hwmass] with t ht
    exact (hm₀ t (H1ComplDirichletToLp q (u t))).symm.trans ht
  · filter_upwards [hwderiv, hmem] with t ht htc
    rw [ht, integral_adjoint_chartPullback_eq_integral_euclidean
      (G.metric t) α (X t) (a t) (H1ComplDirichletToLp q (u t)) v ψ hv rfl]
    congr 1
    apply hm t (H1ComplDirichletToLp q (u t))
    exact (htr.comp_continuous (f := fun x : M => (t, x))
      (continuous_const.prodMk continuous_id) (fun x => ⟨hreg htc, _root_.Set.mem_univ x⟩)).measurable.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_euclidean ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.exists_timeH1_integral_euclidean

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

theorem IsWeakEvolutionSolution.integral_euclidean_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : _root_.MeasureTheory.Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u)
    (α : M) {φ : ℝ × EuStd → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφi : tsupport φ ⊆ _root_.Set.univ ×ˢ
      (toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target))
    (hφT : ∀ y, φ (T, y) = 0) :
    let e := toEuclidean (E := EuN)
    let Ω := e '' interior (extChartAt I_hs α).target
    let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
    let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
    let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
    let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
    (∫ t, ∫ z in Ω, ρ t z *
      (H1ComplDirichletToLp q (u t) (x z) * fderiv ℝ φ (t, z) (1, 0)) ∂volume ∂timeMeasure T) +
    (∫ t, (∫ z in Ω, ρ t z *
        ((1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t (x z) *
          (H1ComplDirichletToLp q (u t) (x z) * φ (t, z)))) +
      ∫ z in Ω, ρ t z * H1ComplDirichletToLp q (u t) (x z) *
        ((∑ i : Fin (Module.finrank ℝ EuN),
          fderiv ℝ (fun z' : EuStd =>
            (∑ j : Fin (Module.finrank ℝ EuN), A t i j z' *
              fderiv ℝ (fun y => φ (t, y)) z' (EuclideanSpace.single j 1)) * ρ t z') z
              (EuclideanSpace.single i 1)) / ρ t z -
          (∑ i : Fin (Module.finrank ℝ EuN), B t i z *
            fderiv ℝ (fun y => φ (t, y)) z (EuclideanSpace.single i 1)) -
          localDivergence (I := I_hs) (G.metric t) α (X t) (x z) * φ (t, z) - a t * φ (t, z))
      ∂volume ∂timeMeasure T) =
      -(∫ z in Ω, ρ 0 z * (f₀ (x z) * φ (0, z))) := by
  let e := toEuclidean (E := EuN)
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hφc.image continuous_snd
  have hKi : K ⊆ e '' interior (extChartAt I_hs α).target := by
    rintro y ⟨p, hp, rfl⟩
    exact (hφi hp).2
  have hKt : K ⊆ chartTargetEuclid (I := I_hs) (M := M) α :=
    hKi.trans (Set.image_mono interior_subset)
  have hs {ψ : ℝ × EuStd → ℝ} (hψ : tsupport ψ ⊆ tsupport φ) (t : ℝ) :
      tsupport (fun y => ψ (t, y)) ⊆ K := by
    have h := tsupport_comp_subset_preimage ψ (f := fun y : EuStd => (t, y))
      (continuous_const.prodMk continuous_id)
    exact h.trans fun y hy => ⟨(t, y), hψ hy, rfl⟩
  let pull (ψ : ℝ × EuStd → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hψs : tsupport ψ ⊆ tsupport φ) (t : ℝ) : SmoothScalarDirichlet q :=
    ⟨chartPullback I_hs α (fun y => ψ (t, y)),
      chartPullback_contMDiff α (hψ.comp (contDiff_const.prodMk contDiff_id))
        (hK.of_isClosed_subset (isClosed_tsupport _) (hs hψs t)) ((hs hψs t).trans hKt),
      tsupport_chartPullback_subset_interior α
        (hK.of_isClosed_subset (isClosed_tsupport _) (hs hψs t)) ((hs hψs t).trans hKi)⟩
  let φ' : ℝ × EuStd → ℝ := fun p => fderiv ℝ φ p (1, 0)
  have hφ' : ContDiff ℝ ∞ φ' :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hφ's : tsupport φ' ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ (1, 0)
  let v := pull φ hφ Subset.rfl
  let v' := pull φ' hφ' hφ's
  let Ω := e '' interior (extChartAt I_hs α).target
  let x := fun z : EuStd => (extChartAt I_hs α).symm (e.symm z)
  let ρ := fun t z => chartDensityOnE (I := I_hs) (G.metric t) α (e.symm z)
  let A := fun t i j z => chartInvGramOnE (I := I_hs) (G.metric t) α i j (e.symm z)
  let B := fun t i z => chartCoeffOnE (I := I_hs) α (X t) i (e.symm z)
  have hvsrc (ψ : ℝ × EuStd → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hψs : tsupport ψ ⊆ tsupport φ) (t : ℝ) :
      tsupport (pull ψ hψ hψs t).toFun ⊆ (chartAt (EuclideanHalfSpace n) α).source := by
    intro z hz
    obtain ⟨y, ⟨z', hz', rfl⟩, rfl⟩ := tsupport_chartPullback_subset α
      (hK.of_isClosed_subset (isClosed_tsupport _) (hs hψs t)) ((hs hψs t).trans hKt) hz
    have ht : e.symm z' ∈ (extChartAt I_hs α).target := by
      have hz's := hKt (hs hψs t hz')
      rwa [chartTargetEuclid_eq_preimage_symm] at hz's
    have hm := (extChartAt I_hs α).map_target ht
    rwa [extChartAt_source] at hm
  have hm (ψ : ℝ × EuStd → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hψs : tsupport ψ ⊆ tsupport φ) (t : ℝ)
      (U : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
      (c : M → ℝ) (hc : Measurable c) :
      (∫ x, c x * (U x * (pull ψ hψ hψs t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) =
      ∫ z in Ω, ρ t z * (c (x z) * (U (x z) * ψ (t, z))) :=
    integral_mul_chartPullback_eq_integral_euclidean (G.metric t) α U
      (pull ψ hψ hψs t) (fun y => ψ (t, y)) (hvsrc ψ hψ hψs t) rfl hc
  obtain ⟨w, hw, hwd, hwi, hwT⟩ := exists_timeH1_chartPullback q α hφ hφc hφi hT hφT
  have hwv : ∀ᵐ t ∂timeMeasure T, H1ComplDirichletToLp q (w.toFun t) =ᵐ[
      riemannianVolumeMeasure (I := I_hs) (M := M) q] (v t).toFun := by
    filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
    exact hw t ht
  have h := hu.integral_timeH1_test_eq_integral hXcont hacont w v (fun t => (v' t).toFun)
    hwv hwd hwi hwT
  have hfirst :
      (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * (v' t).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) =
      ∫ t, ∫ z in Ω, ρ t z *
        (H1ComplDirichletToLp q (u t) (x z) * fderiv ℝ φ (t, z) (1, 0)) ∂volume ∂timeMeasure T := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simpa only [one_mul] using hm φ' hφ' hφ's t (H1ComplDirichletToLp q (u t))
      (fun _ => 1) measurable_const
  have htr : ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I_hs) G.metric p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
    apply continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
      (I := I_hs) (M := M) (g := G.metric) D.regular_isOpen
    intro β i j
    exact hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) β i j
  have hin :
      (∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0))) =
      ∫ z in Ω, ρ 0 z * (f₀ (x z) * φ (0, z)) := by
    simpa only [one_mul] using hm φ hφ Subset.rfl 0 f₀ (fun _ => 1) measurable_const
  rw [hfirst, hin] at h
  refine (congrArg (fun b : ℝ => _ + b) ?_).trans h
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with t ht
  rw [integral_adjoint_chartPullback_eq_integral_euclidean (G.metric t) α (X t) (a t)
    (H1ComplDirichletToLp q (u t)) (v t) (fun y => φ (t, y)) (hvsrc φ hφ Subset.rfl t) rfl]
  congr 1
  symm
  apply hm φ hφ Subset.rfl t (H1ComplDirichletToLp q (u t))
  exact (htr.comp_continuous (f := fun x : M => (t, x))
    (continuous_const.prodMk continuous_id) (fun x => ⟨hreg ht, _root_.Set.mem_univ x⟩)).measurable.const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_euclidean_test then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_euclidean_test"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_euclidean_test ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.IsWeakEvolutionSolution.integral_euclidean_test

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
