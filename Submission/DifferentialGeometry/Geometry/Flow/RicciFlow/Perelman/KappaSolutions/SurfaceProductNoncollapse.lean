import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductVolume

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance surfaceProductNoncollapseMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseMeasurable target :: scope.openDecls } }
private local instance surfaceProductNoncollapseBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseBorel target :: scope.openDecls } }
private local instance surfaceProductNoncollapseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProductNoncollapseC1 target :: scope.openDecls } }

variable [I.Boundaryless]

theorem surfaceProduct_tensor_half_noncollapsed
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hnoncollapse : ∀ (p : M × ℝ) (r : ℝ), 0 < r →
      (∀ z : M × ℝ, riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p z <
          ENNReal.ofReal r →
        r ^ 4 * normSq0S (I := I.prod 𝓘(ℝ, ℝ)) gP z 4
          (metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
          {z : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p z <
            ENNReal.ofReal r})
    (y : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ z : M, riemannianEDistOf (I := I) h y z < ENNReal.ofReal r →
      r ^ 4 * normSq0S (I := I) h z 4 (metricRm04At (I := I) h z) ≤ 1) :
    ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2 ≤
      riemannianVolumeMeasure (I := I) (M := M) h
        {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} := by
  apply surfaceProduct_half_noncollapse_of_volume_lower h gP hprod y r kappa hr hkappa
  apply hnoncollapse (y, 0) r hr
  intro z hz
  have hbase : riemannianEDistOf (I := I) h y z.1 < ENNReal.ofReal r :=
    lt_of_le_of_lt (surfaceProduct_fst_edist_le h gP hprod (y, 0) z) hz
  have hproduct (w : M) (s : ℝ) (v u : TangentSpace I w) (a c : ℝ) :
      gP.inner (w, s) (v, a) (u, c) = h.inner w v u + a * c :=
    hprod (w, s) (v, a) (u, c)
  have hnorm := metricRmNormSq_product_real_of_inner_eq h gP hproduct z.1 z.2
  rw [hnorm]
  exact hcurvature z.1 hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProduct_tensor_half_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProduct_tensor_half_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProduct_tensor_half_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceProduct_tensor_half_noncollapsed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
