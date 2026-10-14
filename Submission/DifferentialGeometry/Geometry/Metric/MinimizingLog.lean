import Submission.DifferentialGeometry.Geometry.Metric.UniformExponential
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



def minimizingLog (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    (x y : M) : TangentSpace I x :=
  if h : Manifold.riemannianEDist I x y ≠ ⊤ then
    (minExp_of_ne_top (I := I) g hg x y h).choose else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.minimizingLog then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.minimizingLog"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.minimizingLog ``Submission.DifferentialGeometry.Geometry.minimizingLog


theorem minimizingLog_exp (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    {x y : M} (h : Manifold.riemannianEDist I x y ≠ ⊤) :
    expMapIntrinsic (I := I) g hg x (minimizingLog g hg x y) = y := by
  rw [minimizingLog, dif_pos h]
  exact (minExp_of_ne_top (I := I) g hg x y h).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.minimizingLog_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.minimizingLog_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.minimizingLog_exp ``Submission.DifferentialGeometry.Geometry.minimizingLog_exp


theorem minimizingLog_norm (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    {x y : M} (h : Manifold.riemannianEDist I x y ≠ ⊤) :
    Real.sqrt (g.inner x (minimizingLog g hg x y) (minimizingLog g hg x y)) =
      (Manifold.riemannianEDist I x y).toReal := by
  rw [minimizingLog, dif_pos h]
  exact (minExp_of_ne_top (I := I) g hg x y h).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.minimizingLog_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.minimizingLog_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.minimizingLog_norm ``Submission.DifferentialGeometry.Geometry.minimizingLog_norm


def minimizingDiagLog (g : SmoothRiemannianMetric I M) (hg : IsMetricNorm (I := I) (M := M) g)
    (p : M × M) : TangentBundle I M := TotalSpace.mk' E p.1 (minimizingLog g hg p.1 p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.minimizingDiagLog then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.minimizingDiagLog"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.minimizingDiagLog ``Submission.DifferentialGeometry.Geometry.minimizingDiagLog




theorem minimizingDiagLog_eventually_eq_branch (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (p : M) :
    minimizingDiagLog g hg =ᶠ[𝓝 (p, p)]
      (standardDiagonalInverseBranch (I := I) g hg p).inv := by
  obtain ⟨ε, hε, hinj⟩ := exists_uniform_diagExp_injective g hg
  let B := standardDiagonalInverseBranch (I := I) g hg p
  have hBi : ContinuousAt B.inv (p, p) := by
    rw [show B.inv = diagExpInv (I := I) g hg p from
      standardDiagonalInverseBranch_inv g hg p]
    exact (diagExpInv_contMDiffAt (I := I) g hg p).continuousAt
  have hB0 : B.inv (p, p) = (TotalSpace.mk' E p 0 : TangentBundle I M) := by
    rw [show B.inv = diagExpInv (I := I) g hg p from
      standardDiagonalInverseBranch_inv g hg p]
    exact diagExpInv_center (I := I) g hg p
  have hN : ContinuousAt (fun y : M × M =>
      Real.sqrt (g.inner (B.inv y).proj (B.inv y).2 (B.inv y).2)) (p, p) :=
    (metricQuad_cont g).sqrt.continuousAt.comp hBi
  have hsmallB : ∀ᶠ y in 𝓝 (p, p),
      Real.sqrt (g.inner (B.inv y).proj (B.inv y).2 (B.inv y).2) < ε := by
    apply hN.eventually (gt_mem_nhds ?_)
    change Real.sqrt (g.inner (B.inv (p, p)).proj (B.inv (p, p)).2 (B.inv (p, p)).2) < ε
    rw [hB0]
    change Real.sqrt (g.inner p 0 0) < ε
    simpa only [map_zero, Real.sqrt_zero] using hε
  have hsmallD : ∀ᶠ y : M × M in 𝓝 (p, p), Manifold.riemannianEDist I y.1 y.2 < ENNReal.ofReal ε := by
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    change ∀ᶠ y : M × M in 𝓝 (p, p), _root_.EDist.edist y.1 y.2 < ENNReal.ofReal ε
    exact (continuous_fst.edist continuous_snd).continuousAt (x := (p, p)) |>.eventually
      (gt_mem_nhds (show _root_.EDist.edist p p < ENNReal.ofReal ε by
        simpa only [_root_.PseudoEMetricSpace.edist_self] using ENNReal.ofReal_pos.mpr hε))
  filter_upwards [hsmallB, hsmallD, diagExp_diagExpInv (I := I) g hg p] with y hyB hyD hyinv
  have hfin : Manifold.riemannianEDist I y.1 y.2 ≠ ⊤ := ne_top_of_lt hyD
  apply hinj
  · change Real.sqrt (g.inner y.1 (minimizingLog g hg y.1 y.2) (minimizingLog g hg y.1 y.2)) ≤ ε
    rw [minimizingLog_norm g hg hfin]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hyD.le).trans_eq (ENNReal.toReal_ofReal hε.le)
  · exact hyB.le
  · have hlog : diagExp (I := I) g hg (minimizingDiagLog g hg y) = y := by
      change (y.1, expMapIntrinsic (I := I) g hg y.1 (minimizingLog g hg y.1 y.2)) = y
      rw [minimizingLog_exp g hg hfin]
    rw [hlog]
    exact hyinv.symm.trans (by rw [standardDiagonalInverseBranch_inv])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.minimizingDiagLog_eventually_eq_branch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.minimizingDiagLog_eventually_eq_branch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.minimizingDiagLog_eventually_eq_branch ``Submission.DifferentialGeometry.Geometry.minimizingDiagLog_eventually_eq_branch

end DifferentialGeometry.Geometry
