import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Geometry.Exponential.Inverse.Radius
import Submission.DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

theorem tendsto_minimizingVec_of_unique
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p q : M} {u : TangentSpace I p}
    (huniq : ∀ v : TangentSpace I p,
      expMapIntrinsic g hEnorm p v = q →
      Real.sqrt (g.inner p v v) = (_root_.Manifold.riemannianEDist I p q).toReal → v = u) :
    Tendsto (minimizingVec g hEnorm p) (𝓝 q) (𝓝 u) := by
  let d : M → ℝ := fun z => (_root_.Manifold.riemannianEDist I p z).toReal
  have hd : Continuous d := by
    have hed : Continuous (fun z : M => _root_.Manifold.riemannianEDist I p z) :=
      (continuous_riemannianEDist_to (I := I) p).congr
        (fun _ => Manifold.riemannianEDist_comm)
    exact continuousOn_univ.mp (ENNReal.continuousOn_toReal.comp'
      hed.continuousOn (fun z _ => riemannianEDist_ne_top (I := I) p z))
  have hbound : ∀ᶠ z in 𝓝 q, d z < d q + 1 :=
    hd.continuousAt (Iio_mem_nhds (lt_add_one _))
  apply (gLenBall_isCompact g p (d q + 1)).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [hbound] with z hz
    change Real.sqrt (g.inner p (minimizingVec g hEnorm p z)
      (minimizingVec g hEnorm p z)) ≤ d q + 1
    rw [minimizingVec_len]
    exact hz.le
  · intro v _ hv
    apply huniq v
    · have hc := hv.continuousAt_comp
        (expMapIntrinsic_continuous g hEnorm p).continuousAt
      have heq : (expMapIntrinsic g hEnorm p) ∘ (minimizingVec g hEnorm p) = id :=
        funext (minimizingVec_exp g hEnorm p)
      rw [heq] at hc
      exact eq_of_nhds_neBot hc
    · have hc := hv.continuousAt_comp (continuous_sqrt_gInner_self g p).continuousAt
      have heq : (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ∘
          (minimizingVec g hEnorm p) = d :=
        funext (minimizingVec_len g hEnorm p)
      rw [heq] at hc
      exact eq_of_nhds_neBot (hc.clusterPt.mono hd.continuousAt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.tendsto_minimizingVec_of_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.tendsto_minimizingVec_of_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.tendsto_minimizingVec_of_unique ``Submission.DifferentialGeometry.Geometry.Riemannian.tendsto_minimizingVec_of_unique

theorem Exponential.branchEnergy_min_germ
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {pt q : M} (B : ExponentialInverseBranch g hEnorm pt)
    (hmem : ∀ᶠ z in 𝓝 q, (minimizingVec g hEnorm pt z : E) ∈ B.hom.source) :
    branchEnergy g B =ᶠ[𝓝 q]
      (fun z => (1 / 2 : ℝ) * (_root_.Manifold.riemannianEDist I pt z).toReal ^ 2) := by
  filter_upwards [hmem] with z hz
  let v : E := (minimizingVec g hEnorm pt z : E)
  have hvexp : expMapIntrinsic g hEnorm pt v = z := minimizingVec_exp g hEnorm pt z
  have henergy : branchEnergy g B z = (1 / 2 : ℝ) * g.inner pt v v := by
    rw [← hvexp]
    exact branchEnergy_exp B hz
  have hlen : Real.sqrt (g.inner pt v v) = (_root_.Manifold.riemannianEDist I pt z).toReal :=
    minimizingVec_len g hEnorm pt z
  rw [henergy, ← hlen]
  congr 1
  exact (Real.sq_sqrt (metric_inner_self_nonneg g pt v)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.branchEnergy_min_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.branchEnergy_min_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.branchEnergy_min_germ ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.branchEnergy_min_germ


end DifferentialGeometry.Geometry.Riemannian
