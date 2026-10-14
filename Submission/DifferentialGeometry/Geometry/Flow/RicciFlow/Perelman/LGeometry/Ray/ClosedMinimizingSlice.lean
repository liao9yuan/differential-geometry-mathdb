import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.CompleteDomain
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarGradientSlab
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lMinSlice_closed_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T)) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ y : M,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    {tau : ℝ} (htau : 0 < tau) (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular) :
    IsClosed {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  have hleft : T - tau ∈ D.regular := hslab ⟨le_rfl, sub_le_self T htau.le⟩
  obtain ⟨a, ha, hareg⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds (D.regular_isOpen.mem_nhds hleft))
  have hwide : _root_.Set.Icc a T ⊆ D.regular := by
    intro t ht
    rcases le_total t (T - tau) with htl | hlt
    · exact hareg ⟨ht.1, htl⟩
    · exact hslab ⟨hlt, ht.2⟩
  have hsig : 0 < T - a := by linarith
  have hwide' : _root_.Set.Icc (T - (T - a)) T ⊆ D.regular := by
    simpa only [sub_sub_cancel] using hwide
  obtain ⟨K, hK'⟩ := hRm (T - a) hsig hwide'
  have hK : ∀ t ∈ _root_.Set.Icc a T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K := by
    simpa only [sub_sub_cancel] using hK'
  have hcomplete : ∀ t ∈ _root_.Set.Icc a T, RiemannianMetricComplete (S.base.metric t) := by
    intro t ht
    exact complete_of_curvature_bound S hS
      (fun r hr => D.regular_subset (hwide hr))
      (fun r hr => hwide ⟨hr.1.le, hr.2.le⟩) hK ht
      ⟨by linarith, le_rfl⟩ hg
  obtain ⟨G, hG, hgrad⟩ := exists_uniform_scalar_gradient_bound_on_Icc hS ha hwide
    hcomplete hK
  have hKsmall : ∀ t ∈ _root_.Set.Icc (T - tau) T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K :=
    fun t ht y => hK t ⟨ha.le.trans ht.1, ht.2⟩ y
  rw [← isSeqClosed_iff_isClosed]
  intro Z Z₀ hmin hZ
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hb2 : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : _root_.Set.Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hslab
  have hKsq : ∀ t ∈ _root_.Set.Icc (T - (Real.sqrt tau) ^ 2) T, ∀ y : M,
      normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K := by
    simpa only [hb2] using hKsmall
  have hgradsq : ∀ t ∈ _root_.Set.Icc (T - (Real.sqrt tau) ^ 2) T,
      ∀ y : M, ∀ v : TangentSpace I y,
        |(S.base.metric t).inner y (gradientFun (S.base.metric t) (S.scalar t) y) v| ≤
          G * Real.sqrt ((S.base.metric t).inner y v v) := by
    simpa only [hb2] using hgrad
  have hdom : (Z₀, tau) ∈ lExpPosDom S T x := by
    apply (mem_lExpPosDom S T x Z₀ tau).mpr
    refine ⟨htau, htau.le, ?_⟩
    exact mem_lRegularizedDomain_of_complete_of_scalar_gradient_bound S hS T x Z₀ hg
      hb.le hG hregSq hKsq hgradsq
  apply lMinVec_lim_of_bdd S hS T x hmin hZ hdom
  intro y
  exact lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt tau) le_rfl hb.le
    hregSq hKsq x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinSlice_closed_of_rm

end DifferentialGeometry.PDE.RicciFlow.Perelman
