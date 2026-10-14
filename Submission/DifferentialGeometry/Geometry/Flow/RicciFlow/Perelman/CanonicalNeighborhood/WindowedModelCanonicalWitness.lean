import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 11) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → _root_.Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          TangentOrientationSection W.model.M →
            ∃ K : CanonicalWitness S alpha C C x t, K.capTubeHasNeckChart alpha := by
  obtain ⟨Cn, dn, hCn, hdn, hdn1, hnonround⟩ :=
    exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hsmall 1
  obtain ⟨Cr, dr, hCr, hdr, hround⟩ :=
    exists_windowed_bufferedCanonical_with_cap_neck_charts_of_round_model.{u} ha hsmall 1
  refine ⟨max Cn Cr, _root_.Min.min dn dr, hCn.trans (le_max_left _ _), lt_min hdn hdr,
    (min_le_left _ _).trans_lt hdn1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hd hreg orient
  have key : ∀ C' : ℝ, C' ≤ _root_.Max.max Cn Cr → (∃ B : BufferedCanonical S alpha C' 1 x t,
      B.witness.capTubeHasNeckChart alpha) →
      ∃ K : CanonicalWitness S alpha (_root_.Max.max Cn Cr) (_root_.Max.max Cn Cr) x t,
        K.capTubeHasNeckChart alpha := by
    rintro C' hC' ⟨B, hB⟩
    exact ⟨(B.canonicalWitness_mono B.tolerance_lt.le hsmall).enlarge_constants hC' hC',
      (hB.mono_eps B.tolerance_lt.le hsmall).enlarge_constants hC' hC'⟩
  by_cases hr : IsShrinkingSphericalSpaceFormFlow W.model
  · exact key Cr (le_max_right _ _) (hround W (hd.trans (min_le_right _ _)) hS hreg hr)
  · exact key Cn (le_max_left _ _)
      (hnonround kappa M D S hS delta x t W (hd.trans (min_le_left _ _)) hreg hr orient)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
