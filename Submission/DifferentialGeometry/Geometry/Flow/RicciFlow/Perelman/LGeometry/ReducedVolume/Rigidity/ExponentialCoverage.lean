import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.NoCutLocus
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InjGeometryComplete

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

theorem lExp_inj_image_eq_univ_of_redVolume_eq_one
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau s : ℝ} (hs : 0 < s) (hstau : s < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hvol : redVolume S T x tau = 1) :
    (fun Z : E => lExp S T x Z s) '' lInjDomain S T x s = univ := by
  have hslabs : _root_.Set.Icc (T - s) T ⊆ D.regular :=
    (_root_.Set.Icc_subset_Icc (sub_le_sub_left hstau.le T) le_rfl).trans hslab
  obtain ⟨K, hK⟩ := hRm s hs hslabs
  have hinj := lInjDomain_eq_univ_of_redVolume_eq_one S hS T hg x hRm
    (hs.trans hstau) hstau hslab hvol
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨Z, _hmin, hend⟩ := exists_lMin_slab_of_rm S hS K T hg x y s hs hslabs hK
  refine ⟨(Z : E), ?_, hend⟩
  rw [hinj]
  exact _root_.Set.mem_univ Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_image_eq_univ_of_redVolume_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_image_eq_univ_of_redVolume_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_image_eq_univ_of_redVolume_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lExp_inj_image_eq_univ_of_redVolume_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman
