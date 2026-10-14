import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.ExponentialCoverage
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.FinitePoleSpacetimeRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] {D : RealTimeInterval}

theorem redLength_joint_contMDiffOn_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => redLength S T x q.1 q.2) (_root_.Set.univ ×ˢ _root_.Set.Ioo 0 tau) := by
  apply (redLength_joint_contMDiffOn_of_rm S hS T hg x hRm).mono
  rintro ⟨y, s⟩ ⟨_hy, hs, hstau⟩
  refine ⟨hs, ?_⟩
  have hcoverage := lExp_inj_image_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    hs hstau hslab hvol
  have hy : y ∈ (fun Z : E => lExp S T x Z s) '' lInjDomain S T x s := by
    rw [hcoverage]
    exact _root_.Set.mem_univ y
  exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_joint_contMDiffOn_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_joint_contMDiffOn_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_joint_contMDiffOn_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redLength_joint_contMDiffOn_of_redVolume_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman
