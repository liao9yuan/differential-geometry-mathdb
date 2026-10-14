import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private theorem exists_smooth_chart_multiplier
    (α : M) {Ω : Set EuStd}
    (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ∃ ψ : EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ _root_.Set.EqOn ψ P Ω := by
  intro P
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) P U := by
    apply (scalarOnE_contDiffOn α φ.contMDiff).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩc hU hΩs
  let ψ := fun z => χ z * P z
  have hψs : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hχs
  refine ⟨ψ, (hχ.contDiffOn.mul hP).contDiff_of_tsupport_subset hU hψs, hχc.mul_right, ?_⟩
  intro z hz
  dsimp only [ψ]
  rw [hχone z (Metric.self_subset_cthickening _ (subset_closure hz)), one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_chart_multiplier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smooth_chart_multiplier target :: scope.openDecls } }

omit [NeZero n] in
private theorem hasWeakPartialDeriv_congr_left
    {Ω : Set EuStd} {i : Fin (Module.finrank ℝ EuN)} {g f f' : EuStd → ℝ}
    (h : DeGiorgi.HasWeakPartialDeriv i g f Ω)
    (heq : f' =ᵐ[volume.restrict Ω] f) : DeGiorgi.HasWeakPartialDeriv i g f' Ω := by
  intro ψ hψ hψc hψs
  rw [← h ψ hψ hψc hψs]
  exact _root_.MeasureTheory.integral_congr_ae (heq.mono fun z hz => congrArg (· * fderiv ℝ ψ z (EuclideanSpace.single i 1)) hz)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.hasWeakPartialDeriv_congr_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.hasWeakPartialDeriv_congr_left target :: scope.openDecls } }

theorem dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (j : Fin (Module.finrank ℝ EuN)) (u : H1ComplDirichlet q) :
    let P := fun z => φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let U := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
    (D j (smoothMulH1ComplDirichlet q φ u) : EuStd → ℝ) =ᵐ[volume.restrict Ω]
      fun z => P z * D j u z + fderiv ℝ P z (EuclideanSpace.single j 1) * U z := by
  intro P U D
  obtain ⟨ψ, hψ, hψc, heq⟩ := exists_smooth_chart_multiplier α hΩc hΩs φ
  have hu : _root_.MeasureTheory.MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hg : _root_.MeasureTheory.MemLp (D j u : EuStd → ℝ) 2 (volume.restrict Ω) := Lp.memLp _
  have hdψ : Continuous (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : _root_.MeasureTheory.MemLp (fun z => ψ z * D j u z + fderiv ℝ ψ z (EuclideanSpace.single j 1) * U z)
      2 (volume.restrict Ω) :=
    (hg.mul' ((hψ.continuous.memLp_of_hasCompactSupport hψc : _root_.MeasureTheory.MemLp ψ ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω)).add
      (hu.mul' ((hdψ.memLp_of_hasCompactSupport (hψc.fderiv_apply (𝕜 := ℝ)
        (EuclideanSpace.single j 1)) : _root_.MeasureTheory.MemLp _ ∞ _root_.MeasureTheory.MeasureSpace.volume).restrict Ω))
  have hp := (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u).mul_smooth
    hΩ hψ (hu.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))
  have hval : (fun z => H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ u)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω]
      fun z => ψ z * U z := by
    rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
    filter_upwards [ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) (smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q u)),
      _root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    rw [hz, heq hzΩ]
  have hweak := hasWeakPartialDeriv_congr_left hp hval
  have hae := DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (smoothMulH1ComplDirichlet q φ u)) hweak
    ((Lp.memLp _).locallyIntegrable (by norm_num)) (hG.locallyIntegrable (by norm_num))
  apply hae.trans
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with z hz
  have hd : fderiv ℝ ψ z = fderiv ℝ P z := (heq.eventuallyEq_of_mem (hΩ.mem_nhds hz)).fderiv_eq
  rw [heq hz, hd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_smoothMulH1ComplDirichlet

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
