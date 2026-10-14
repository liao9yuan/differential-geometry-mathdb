import Submission.DifferentialGeometry.Geometry.Metric.Retraction
import Submission.DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Composition
import Submission.DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
    (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : _root_.Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) :
    hasVanishingSecondFundamentalFormAlongCurves g (retractionMetric g he hr)
      (fun p : M => (⟨e p, hEU (_root_.Set.mem_range_self p)⟩ : U)) := by
  let f : M → U := fun p => ⟨e p, hEU (_root_.Set.mem_range_self p)⟩
  let G : U → M × F := fun x => retractionGraph e r x
  have hf : ContMDiff I 𝓘(ℝ, F) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff U f).mp he
  have hG := contMDiff_retractionGraph he hr
  have hcomp : G ∘ f = (fun p : M => (p, (0 : F))) := by
    funext p
    change (r (e p), e p - e (r (e p))) = (p, 0)
    rw [hleft p, sub_self]
  apply hasVanishingSecondFundamentalFormAlongCurves_of_comp_of_inner_map
    (g₃ := g.prod (euclideanMetric (E := F))) hG (fun _ _ _ => rfl) hf
  rw [hcomp]
  exact hasVanishingSecondFundamentalFormAlongCurves_prod_left g euclideanMetric 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric

end DifferentialGeometry.Geometry.Riemannian
