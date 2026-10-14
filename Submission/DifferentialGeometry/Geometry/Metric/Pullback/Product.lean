import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Submission.DifferentialGeometry.Topology.Diffeomorph.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N]
variable [T2Space M] [T2Space N]

theorem Diffeomorph.pullbackMetricCross_prodCongrCross
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']
    [FiniteDimensional Real E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace Real F']
    [FiniteDimensional Real F']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners Real E' H'}
    {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners Real F' G'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [T2Space M']
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' ∞ N']
    [T2Space N']
    (g : SmoothRiemannianMetric I' M') (h : SmoothRiemannianMetric J' N')
    (Phi : M ≃ₘ⟮I, I'⟯ M') (Psi : N ≃ₘ⟮J, J'⟯ N') :
    Diffeomorph.pullbackMetricCross (g.prod h) (Phi.prodCongrCross Psi) =
      (Diffeomorph.pullbackMetricCross g Phi).prod
        (Diffeomorph.pullbackMetricCross h Psi) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hPhi : MDiffAt (Phi : M → M') x.1 :=
    Phi.contMDiff.mdifferentiableAt (by simp)
  have hPsi : MDiffAt (Psi : N → N') x.2 :=
    Psi.contMDiff.mdifferentiableAt (by simp)
  unfold Diffeomorph.pullbackMetricCross SmoothRiemannianMetric.prod
  unfold Diffeomorph.pullbackInnerCross localPullInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
    add_apply, mfderiv_fst, mfderiv_snd]
  rw [Diffeomorph.coe_prodCongrCross]
  rw [mfderiv_prodMap hPhi hPsi]
  simp [ContinuousLinearMap.prodMap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongrCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongrCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongrCross ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongrCross

theorem Diffeomorph.pullbackMetricCross_prodCongr
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']
    [FiniteDimensional Real E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners Real E' H'}
    {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners Real F G'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [T2Space M']
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' ∞ N']
    [T2Space N']
    (g : SmoothRiemannianMetric I' M') (h : SmoothRiemannianMetric J' N')
    (Phi : M ≃ₘ⟮I, I'⟯ M') (Psi : N ≃ₘ⟮J, J'⟯ N') :
    Diffeomorph.pullbackMetricCross (g.prod h) (Phi.prodCongr Psi) =
      (Diffeomorph.pullbackMetricCross g Phi).prod
        (Diffeomorph.pullbackMetricCross h Psi) := by
  simpa only [Diffeomorph.prodCongrCross_eq_prodCongr] using
    Diffeomorph.pullbackMetricCross_prodCongrCross g h Phi Psi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongr ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_prodCongr

theorem Diffeomorph.pullbackMetric_prodCongr
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Phi : M ≃ₘ⟮I, I⟯ M) (Psi : N ≃ₘ⟮J, J⟯ N) :
    Diffeomorph.pullbackMetric (g.prod h) (Phi.prodCongr Psi) =
      (Diffeomorph.pullbackMetric g Phi).prod
        (Diffeomorph.pullbackMetric h Psi) := by
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
    Diffeomorph.pullbackMetricCross_prodCongr g h Phi Psi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetric_prodCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetric_prodCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetric_prodCongr ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetric_prodCongr

end DifferentialGeometry
