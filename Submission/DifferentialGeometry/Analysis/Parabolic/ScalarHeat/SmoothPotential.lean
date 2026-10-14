import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem of_contMDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} {J : Set ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2) (J ×ˢ Set.univ))
    (hcarrier : D.carrier ⊆ J)
    (hequation : ∀ t ∈ D.regular, ∀ x : M,
      HasDerivAt (fun s : ℝ => u s x)
        (laplacianAt (I := I) G t (u t) x + V t x * u t x) t) :
    IsHeatPotOn D G V u where
  jointSmooth := hu.mono
    (Set.prod_mono (D.regular_subset.trans hcarrier) Set.Subset.rfl)
  jointCont := hu.continuousOn.mono (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := by
    have hinsert : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M => (t, x)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hu.comp_contMDiff hinsert (fun x => ⟨hcarrier ht, Set.mem_univ x⟩)
  equation := hequation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_contMDiffOn

end DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
