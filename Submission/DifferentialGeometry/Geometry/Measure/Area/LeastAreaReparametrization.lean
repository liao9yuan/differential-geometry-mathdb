import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastArea
import Submission.DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Submission.DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def precomposeLipschitzContractibleLoop (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) (ψ : C(loopCircle, loopCircle)) {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) : lipschitzContractibleLoop g := by
  refine ⟨⟨γ.val.val.comp ψ, γ.val.property.comp_left ψ⟩, ?_⟩
  obtain ⟨L, hL⟩ := γ.property
  refine ⟨L * K, fun s t => ?_⟩
  apply (hL (ψ s) (ψ t)).trans
  calc
    (L : ℝ≥0∞) * _root_.EDist.edist (ψ s) (ψ t) ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * _root_.EDist.edist s t) :=
      mul_le_mul' le_rfl (hψ s t)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.precomposeLipschitzContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.precomposeLipschitzContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.precomposeLipschitzContractibleLoop ``Submission.DifferentialGeometry.Geometry.precomposeLipschitzContractibleLoop

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] in
theorem exists_competitor_precompose_circle (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm)
    {u : C(closedDisk, M)} (hu : u ∈ spanningDiskCompetitors g γ.val.val) :
    ∃ v ∈ spanningDiskCompetitors g
      (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ).val.val,
      riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨φ, hφtrace, Kφ, Lφ, hφ, hφ'⟩ := exists_radial_disk_reparametrization ψ hψ hψ'
  obtain ⟨htrace, Cu, hCu⟩ := hu
  let v : C(closedDisk, M) := u.comp ⟨φ, φ.continuous⟩
  have hvtrace : diskTrace v = (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ).val.val := by
    ext θ
    change u (φ (diskBoundary θ)) = γ.val.val (ψ θ)
    rw [hφtrace]
    exact congrArg (fun f : freeLoop M => f (ψ θ)) htrace
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hu' : LipschitzWith Cu u := hCu
  have hv : LipschitzWith (Cu * Kφ) v := hu'.comp hφ
  refine ⟨v, ⟨hvtrace, Cu * Kφ, hv⟩, ?_⟩
  exact riemannianDiskArea_reparametrize g hCu φ hφ hφ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_competitor_precompose_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_competitor_precompose_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_competitor_precompose_circle ``Submission.DifferentialGeometry.Geometry.exists_competitor_precompose_circle



theorem leastSpanningArea_precompose_le [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    leastSpanningArea g (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ≤
      leastSpanningArea g γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu, harea⟩ := exists_spanningDisk_area_lt g γ hε
  obtain ⟨v, hv, hvarea⟩ := exists_competitor_precompose_circle g γ ψ hψ hψ' hu
  have hle := leastSpanningArea_le_competitor g _ hv
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_precompose_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_precompose_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_precompose_le ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_precompose_le



theorem leastSpanningArea_precompose [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g)
    (ψ : loopCircle ≃ₜ loopCircle) {K L : ℝ≥0}
    (hψ : LipschitzWith K ψ) (hψ' : LipschitzWith L ψ.symm) :
    leastSpanningArea g (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) =
      leastSpanningArea g γ := by
  apply le_antisymm (leastSpanningArea_precompose_le g γ ψ hψ hψ')
  have h := leastSpanningArea_precompose_le g
    (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ψ.symm hψ' hψ
  have heq : precomposeLipschitzContractibleLoop g
      (precomposeLipschitzContractibleLoop g γ ⟨ψ, ψ.continuous⟩ hψ) ⟨ψ.symm, ψ.symm.continuous⟩ hψ' = γ := by
    apply Subtype.ext
    apply Subtype.ext
    ext θ
    exact congrArg γ.val.val (ψ.apply_symm_apply θ)
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_precompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_precompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_precompose ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_precompose

end DifferentialGeometry.Geometry
