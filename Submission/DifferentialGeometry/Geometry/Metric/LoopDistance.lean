import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianLoopEDist_ne_top (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : (⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ)) ≠ ⊤ := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  change (⨆ θ, _root_.EDist.edist (γ₀ θ) (γ₁ θ)) ≠ ⊤
  rw [← ContinuousMap.edist_eq_iSup]
  exact edist_ne_top _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopEDist_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopEDist_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopEDist_ne_top ``Submission.DifferentialGeometry.Geometry.riemannianLoopEDist_ne_top


def riemannianLoopDistance (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : ℝ≥0 := (⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toNNReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance

theorem riemannianLoopDistance_coe (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) :
    (riemannianLoopDistance g γ₀ γ₁ : ℝ≥0∞) = ⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ) :=
  ENNReal.coe_toNNReal (riemannianLoopEDist_ne_top g γ₀ γ₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance_coe ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance_coe

theorem riemannianEDist_le_loopDistance (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) (θ : loopCircle) :
    riemannianEDistOf g (γ₀ θ) (γ₁ θ) ≤ (riemannianLoopDistance g γ₀ γ₁ : ℝ≥0∞) := by
  rw [riemannianLoopDistance_coe]
  exact le_iSup (fun t => riemannianEDistOf g (γ₀ t) (γ₁ t)) θ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDist_le_loopDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDist_le_loopDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDist_le_loopDistance ``Submission.DifferentialGeometry.Geometry.riemannianEDist_le_loopDistance

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianLoopDistance_eq_iSup (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) :
    (riemannianLoopDistance g γ₀ γ₁ : ℝ) = ⨆ θ, (riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toReal := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hnn : riemannianLoopDistance g γ₀ γ₁ = _root_.NNDist.nndist γ₀ γ₁ := by
    unfold riemannianLoopDistance
    change (⨆ θ, _root_.EDist.edist (γ₀ θ) (γ₁ θ)).toNNReal = _root_.NNDist.nndist γ₀ γ₁
    rw [← ContinuousMap.edist_eq_iSup, edist_nndist, ENNReal.toNNReal_coe]
  rw [hnn]
  change _root_.Dist.dist γ₀ γ₁ = ⨆ θ, (_root_.EDist.edist (γ₀ θ) (γ₁ θ)).toReal
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using!
    (ContinuousMap.dist_eq_iSup (f := γ₀) (g := γ₁))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance_eq_iSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance_eq_iSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance_eq_iSup ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance_eq_iSup

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem riemannianLoopDistance_symm (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : riemannianLoopDistance g γ₀ γ₁ = riemannianLoopDistance g γ₁ γ₀ := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  unfold riemannianLoopDistance
  congr 1
  apply iSup_congr
  intro θ
  exact _root_.PseudoEMetricSpace.edist_comm (γ₀ θ) (γ₁ θ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianLoopDistance_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianLoopDistance_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianLoopDistance_symm ``Submission.DifferentialGeometry.Geometry.riemannianLoopDistance_symm

end DifferentialGeometry.Geometry
