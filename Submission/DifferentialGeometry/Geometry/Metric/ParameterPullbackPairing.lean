import Submission.DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import Submission.DifferentialGeometry.Geometry.Metric.ParameterTangentMap
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_parameterPullbackPairing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ} (hT : IsOpen T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ _root_.Set.univ))
    {τ : X → ℝ} {U : X → M} {s : Set X} {x : X}
    (hτ : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ τ s x)
    (hU : ContMDiffWithinAt J 𝓘(ℝ, E) ∞ U s x)
    (ht : τ x ∈ T) (hreg : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s x)
    (hZ : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s x) :
    ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞
      (fun q => (Diffeomorph.pullbackMetric (G (τ q)) (Φ (τ q))).inner (U q) (W q) (Z q)) s x := by
  have hbase := ((hΦ _ ⟨ht, _root_.Set.mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, _root_.Set.mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hU)
  have htan := contMDiffOn_parameter_tangentMap hT hΦ
  have hw := ((htan (τ x, TotalSpace.mk' E (U x) (W x)) ⟨ht, _root_.Set.mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, _root_.Set.mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hW)
  have hz := ((htan (τ x, TotalSpace.mk' E (U x) (Z x)) ⟨ht, _root_.Set.mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, _root_.Set.mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hZ)
  have h := contMDiffWithinAt_metricFamilySectionPairing hG hτ hbase hreg hw hz
  convert h using 1
  ext q
  exact Diffeomorph.pullbackMetric_inner (G (τ q)) (Φ (τ q)) (U q) (W q) (Z q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing ``Submission.DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ} (hT : UniqueDiffOn ℝ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ _root_.Set.univ))
    {τ : X → ℝ} {U : X → M} {s : Set X} {x : X}
    (hτ : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ τ s x)
    (hU : ContMDiffWithinAt J 𝓘(ℝ, E) ∞ U s x)
    (ht : τ x ∈ T) (hτT : _root_.Set.MapsTo τ s T) (hreg : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s x)
    (hZ : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s x) :
    ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞
      (fun q => (Diffeomorph.pullbackMetric (G (τ q)) (Φ (τ q))).inner (U q) (W q) (Z q)) s x := by
  have hbase := (hΦ _ ⟨ht, _root_.Set.mem_univ _⟩).comp x (hτ.prodMk hU)
    (fun q hq => ⟨hτT hq, trivial⟩)
  have htan := contMDiffOn_parameter_tangentMap_of_uniqueDiffOn hT hΦ
  have hw := (htan (τ x, TotalSpace.mk' E (U x) (W x)) ⟨ht, _root_.Set.mem_univ _⟩).comp
    (f := fun q => (τ q, TotalSpace.mk' E (U q) (W q))) x
    (hτ.prodMk hW) (fun q hq => ⟨hτT hq, _root_.Set.mem_univ _⟩)
  have hz := (htan (τ x, TotalSpace.mk' E (U x) (Z x)) ⟨ht, _root_.Set.mem_univ _⟩).comp
    (f := fun q => (τ q, TotalSpace.mk' E (U q) (Z q))) x
    (hτ.prodMk hZ) (fun q hq => ⟨hτT hq, _root_.Set.mem_univ _⟩)
  have h := contMDiffWithinAt_metricFamilySectionPairing hG hτ hbase hreg hw hz
  convert h using 1
  ext q
  exact Diffeomorph.pullbackMetric_inner (G (τ q)) (Φ (τ q)) (U q) (W q) (Z q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn ``Submission.DifferentialGeometry.Geometry.contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn

end DifferentialGeometry.Geometry

end

end
