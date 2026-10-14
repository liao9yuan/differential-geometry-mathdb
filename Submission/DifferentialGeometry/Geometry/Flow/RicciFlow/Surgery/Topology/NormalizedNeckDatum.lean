import Submission.DifferentialGeometry.Geometry.Neck.BufferedRotation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import Submission.DifferentialGeometry.Geometry.Neck.Recentering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

namespace NormalizedNeck

def rotatedDatum (N : NormalizedNeck g δ k) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark) (side : Bool) :
    normalizedDatum g N.center δ k := by
  let ρ := bufferedCylinderRotation δ e
  let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
  have hH (q : bufferedCylinder δ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
      H.inner q v w = N.scale * g.inner (N.chart q)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q w) := N.normalized_inner q v w
  let φ : bufferedCylinder δ → M := N.chart ∘ ρ
  have hφ : ContMDiff NeckCylinderModel ThreeModel ∞ φ := N.chart_smooth.contMDiff.comp ρ.contMDiff
  have hi : _root_.Function.Injective φ := N.chart_smooth.isEmbedding.injective.comp ρ.injective
  have himm : ∀ q, _root_.Function.Injective (mfderiv NeckCylinderModel ThreeModel φ q) := by
    intro q
    rw [show φ = N.chart ∘ ρ from rfl, mfderiv_comp q
      (N.chart_smooth.contMDiff.mdifferentiable (by simp) _) (ρ.contMDiff.mdifferentiable (by simp) _)]
    exact (injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel N.chart _
      (N.chart_smooth.isImmersion.isImmersionAt _)).comp
      (ρ.mfderivToContinuousLinearEquiv (by simp) q).injective
  have hpos : 0 < metricScalarAt g N.center := N.scale_scalar ▸ N.scale_pos
  have hloc := isLocalDiffeomorph_of_injective_mfderiv φ hφ himm (by simp [ThreeSpace])
  have hmetric : pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hpos g) φ hloc hi =
      Diffeomorph.pullbackMetric H ρ := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner,
      Diffeomorph.pullbackMetric_inner, hH, N.scale_scalar]
    rw [show φ = N.chart ∘ ρ from rfl, mfderiv_comp q
      (N.chart_smooth.contMDiff.mdifferentiable (by simp) _) (ρ.contMDiff.mdifferentiable (by simp) _)]
    rfl
  refine { precision_pos := N.delta_pos
           precision_lt_one := N.delta_lt_one
           map := φ
           smooth := hφ
           injective := hi
           immersion := himm
           center_eq := ?_
           scalar_pos := hpos
           retainedSide := side
           error_lt := ?_ }
  · change N.chart (ρ (cylinderCenter δ N.delta_pos)) = N.center
    convert N.marked using 1
    congr 1
    apply Subtype.ext
    change (bufferedCylinderRotation δ e (cylinderCenter δ N.delta_pos)).val = _
    rw [bufferedCylinderRotation_apply]
    exact Prod.ext he rfl
  · change metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hpos g) φ hloc hi)
      (referenceMetric δ) (referenceMetric δ) < _
    rw [hmetric]
    have hrot := metricDerivENormSupOn_bufferedCylinderRotation δ e H (referenceMetric δ) k
    rw [pullback_referenceMetric_bufferedCylinderRotation] at hrot
    change metricDerivENormSupOn (controlledCylinder δ) k
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e))
      (referenceMetric δ) (referenceMetric δ) < _
    rw [hrot, metricDerivENormSupOn_eq_ofReal_of_isCompact (isCompact_controlledCylinder δ)]
    apply (ENNReal.ofReal_lt_ofReal_iff N.delta_pos).mpr
    have hset : controlledCylinder δ = neckClosedTest δ := by ext q; rfl
    rw [hset, referenceMetric_eq_roundCylinderMetric_neckBuffer]
    exact N.closeness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum

@[simp] theorem rotatedDatum_map (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : (N.rotatedDatum e he side).map = N.chart ∘ bufferedCylinderRotation δ e := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_map

@[simp] theorem rotatedDatum_retainedSide (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : (N.rotatedDatum e he side).retainedSide = side := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_retainedSide ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_retainedSide

theorem exists_rotatedDatum (N : NormalizedNeck g δ k) (side : Bool) :
    ∃ e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace, LinearMap.det e.toLinearMap = 1 ∧
      sphereDiffeo (n := 2) e spherePoint = N.sphereMark ∧
      ∃ d : normalizedDatum g N.center δ k,
        d.map = N.chart ∘ bufferedCylinderRotation δ e ∧ d.retainedSide = side := by
  obtain ⟨e, hdet, he⟩ := exists_sphereDiffeo_det_one (n := 2) (by norm_num) spherePoint N.sphereMark
  exact ⟨e, hdet, he, N.rotatedDatum e he side, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_rotatedDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_rotatedDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_rotatedDatum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_rotatedDatum

theorem rotatedDatum_range (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) : _root_.Set.range (N.rotatedDatum e he side).map = _root_.Set.range N.chart := by
  rw [rotatedDatum_map]
  exact (bufferedCylinderRotation δ e).surjective.range_comp N.chart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_range

theorem rotatedDatum_image_height (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (S : Set ℝ) :
    (N.rotatedDatum e he side).map '' {q : bufferedCylinder δ | q.val.2 ∈ S} =
      N.chart '' {q : neckBuffer δ | q.val.2 ∈ S} := by
  let F : bufferedCylinder δ → M := N.chart
  change (N.rotatedDatum e he side).map '' _ = F '' {q : bufferedCylinder δ | q.val.2 ∈ S}
  have hmap : (N.rotatedDatum e he side).map = F ∘ bufferedCylinderRotation δ e := rfl
  rw [hmap, _root_.Set.image_comp, image_bufferedCylinderRotation_height]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_image_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_image_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_image_height ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_image_height

theorem rotatedDatum_normalizedMetric (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) :
    let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
    (N.rotatedDatum e he side).normalizedMetric = Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e) := by
  let H : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ) := N.normalizedMetric
  have hH (q : bufferedCylinder δ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
      H.inner q v w = N.scale * g.inner (N.chart q)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel N.chart q w) := N.normalized_inner q v w
  let F : bufferedCylinder δ → M := N.chart
  have hF : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ F := N.chart_smooth.contMDiff
  change (N.rotatedDatum e he side).normalizedMetric = Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e)
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedDatum.normalizedMetric_inner]
  change metricScalarAt g N.center * g.inner ((F ∘ bufferedCylinderRotation δ e) q)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel (F ∘ bufferedCylinderRotation δ e) q v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ThreeModel (F ∘ bufferedCylinderRotation δ e) q w) =
      (Diffeomorph.pullbackMetric H (bufferedCylinderRotation δ e)).inner q v w
  rw [Diffeomorph.pullbackMetric_inner, hH, N.scale_scalar]
  rw [mfderiv_comp q (hF.mdifferentiable (by simp) _)
    ((bufferedCylinderRotation δ e).contMDiff.mdifferentiable (by simp) _)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_normalizedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_normalizedMetric

theorem rotatedDatum_offsetPoint (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    (N.rotatedDatum e he side).offsetPoint hσ =
      N.chart ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩ := by
  change N.chart (bufferedCylinderRotation δ e
    ⟨(spherePoint, σ), offset_mem_bufferedCylinder N.delta_pos hσ spherePoint⟩) = _
  apply congrArg N.chart
  apply Subtype.ext
  rw [bufferedCylinderRotation_apply]
  exact Prod.ext he rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offsetPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offsetPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offsetPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offsetPoint

theorem rotatedDatum_offset_scalar_bounds (N : NormalizedNeck g δ k)
    (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (he : sphereDiffeo (n := 2) e spherePoint = N.sphereMark)
    (side : Bool) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 8646) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    N.scale / 2 ≤ metricScalarAt g ((N.rotatedDatum e he side).offsetPoint hσ) ∧
      metricScalarAt g ((N.rotatedDatum e he side).offsetPoint hσ) ≤ (3 / 2 : ℝ) * N.scale := by
  rw [rotatedDatum_offsetPoint]
  have hfit : (⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩ : neckBuffer δ) ∈
      neckClosedTest δ := by
    change -δ⁻¹ ≤ σ ∧ σ ≤ δ⁻¹
    have hi := (one_le_inv₀ N.delta_pos).mpr N.delta_lt_one.le
    rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith
  have hr := N.abs_scalar_ratio_sub_one_le hk (by linarith) _ hfit
  have hlo : (1 / 2 : ℝ) ≤ metricScalarAt g (N.chart
      ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩) / N.scale := by
    have h := (abs_le.mp hr).1
    linarith
  have hhi : metricScalarAt g (N.chart
      ⟨(N.sphereMark, σ), offset_mem_bufferedCylinder N.delta_pos hσ N.sphereMark⟩) / N.scale ≤ (3 / 2 : ℝ) := by
    have h := (abs_le.mp hr).2
    linarith
  exact ⟨by linarith [(le_div_iff₀ N.scale_pos).mp hlo],
    (div_le_iff₀ N.scale_pos).mp hhi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offset_scalar_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offset_scalar_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offset_scalar_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.rotatedDatum_offset_scalar_bounds

end NormalizedNeck
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
