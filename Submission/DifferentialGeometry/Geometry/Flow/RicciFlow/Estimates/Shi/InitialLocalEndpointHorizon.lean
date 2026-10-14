import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalCutoffHorizon

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
universe u
theorem exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
    (N : ℕ) (T R K : ℝ) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X],
      ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), ∀ θ : ℝ, 0 < θ → θ ≤ T → IsSolutionOn S →
      _root_.Set.Icc 0 θ ⊆ D.carrier → _root_.Set.Ioo 0 θ ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (_root_.Set.Icc 0 θ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
      IsCompact {x : X | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R} →
      (∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S k 0 x ≤ A k) →
      ∀ k ≤ N, ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          nablaKRm04NormSqIntrinsic S k t x ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_bounded_horizon
    (I := I) N T R K hR A hA
  refine ⟨B,hB,?_⟩
  intro X _ _ _ _ _ D S θ hθ hθT hS hslab hreg hgram p hcompact hu hinit j hj t ht x hx
  have hc : ContinuousOn (fun t : ℝ => nablaKRm04NormSqIntrinsic S j t x) (_root_.Set.Icc 0 θ) := by
    have hn : ContinuousOn
        (fun q : ℝ × X => nablaKRm04NormSqIntrinsic S j q.1 q.2) (_root_.Set.Icc 0 θ ×ˢ _root_.Set.univ) := by
      have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (_root_.Set.Icc 0 θ)
        (uniqueDiffOn_Icc hθ) hgram j).continuousOn
      apply hh.congr
      intro q _
      dsimp only
      unfold nablaKRm04NormSqIntrinsic
      rw [nablaKRm_eq_iterCov]
      rfl
    exact ContinuousOn.comp
      (g := fun q : ℝ × X => nablaKRm04NormSqIntrinsic S j q.1 q.2)
      (f := fun s : ℝ => (s,x)) hn (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs,_root_.Set.mem_univ x⟩)
  have hshort : ∀ s ∈ _root_.Set.Ioo 0 θ, nablaKRm04NormSqIntrinsic S j s x ≤ B := by
    intro s hs
    apply hbound X D S s hs.1 (hs.2.le.trans hθT) hS
      (fun r hr => hslab ⟨hr.1,hr.2.trans hs.2.le⟩)
      (fun r hr => hreg ⟨hr.1,hr.2.trans_lt hs.2⟩)
      (fun y i k => (hgram y i k).mono
        (_root_.Set.prod_mono (_root_.Set.Icc_subset_Icc le_rfl hs.2.le) subset_rfl)) p hcompact
      (fun r hr => hu r ⟨hr.1,hr.2.trans hs.2.le⟩) hinit j hj s ⟨hs.1.le,le_rfl⟩ x hx
  have hcl : closure (_root_.Set.Ioo (0 : ℝ) θ) = _root_.Set.Icc 0 θ :=
    closure_Ioo (by linarith : (0 : ℝ) ≠ θ)
  exact le_on_closure hshort (hcl.symm ▸ hc) continuousOn_const (hcl.symm ▸ ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval

end DifferentialGeometry.PDE.RicciFlow
