import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.Flatness
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem metricRm04At_eq_zero_of_riemannOp_zero
    (g : SmoothRiemannianMetric I M) (y : M)
    (h : ∀ u v w : TangentSpace I y, riemannOp (LeviCivita g) y u v w = 0) :
    metricRm04At g y = 0 := by
  ext slots
  have hs : slots = vec4 (slots 0) (slots 1) (slots 2) (slots 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hs,metricRm04At_inner]
  change g.inner y (riemannOp (LeviCivita g) y _ _ _) _ = 0
  rw [h]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.metricRm04At_eq_zero_of_riemannOp_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.metricRm04At_eq_zero_of_riemannOp_zero target :: scope.openDecls } }

omit [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem riemannOp_eq_zero_of_metricRm04At_zero
    (g : SmoothRiemannianMetric I M) (y : M) (h : metricRm04At g y = 0)
    (u v w : TangentSpace I y) : riemannOp (LeviCivita g) y u v w = 0 := by
  by_contra hn
  have hp := g.pos y (riemannOp (LeviCivita g) y u v w) hn
  have hh := metricRm04At_inner g y u v w (riemannOp (LeviCivita g) y u v w)
  rw [h] at hh
  change 0 = g.inner y (riemannOp (LeviCivita g) y u v w) (riemannOp (LeviCivita g) y u v w) at hh
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannOp_eq_zero_of_metricRm04At_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.riemannOp_eq_zero_of_metricRm04At_zero target :: scope.openDecls } }

theorem curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ}
    (hcar : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ _root_.Set.Ioo a b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (x₀ : M) (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x₀
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x₀)) = 1) :
    ∀ t ∈ _root_.Set.Ioc a b, ∀ x, Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K,hK,hbound⟩ := hbound
  intro t ht x
  have hab : a < b := ht.1.trans_le ht.2
  have hrankb (y : M) : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) y
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) y)) = 1 :=
    (curvatureOperatorImageAt_finrank_eq_at_right_endpoint S hS hdim hab hcar hreg hR y x₀).trans hrank
  rcases ht.2.lt_or_eq with htb | rfl
  swap
  · exact hrankb x
  have hle : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) ≤ 1 := by
    have h := curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval S hS hdim
      ht.1 htb hcar hreg (fun r hr => hR r ⟨ht.1.le.trans hr.1,hr.2⟩) x x
    exact h.trans_eq (hrankb x)
  have hpos : 0 < Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) := by
    by_contra hz
    have hzero := Nat.eq_zero_of_not_pos hz
    let c := (a+t)/2
    have hac : a < c := by dsimp [c]; linarith [ht.1]
    have hct : c < t := by dsimp [c]; linarith [ht.1]
    have hzall (y : M) : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) y)) = 0 := by
      have heq := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hct
        (fun r hr => hreg ⟨hac.trans_le hr.1,hr.2.trans_lt htb⟩)
        (fun r hr => hR r ⟨hac.le.trans hr.1,hr.2.trans ht.2⟩) y x
      exact heq.trans hzero
    have hriem := riemannOp_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
      (S.base.metric t) hzall
    have hflat : ∀ y : M, normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) = 0 := by
      intro y
      apply (normSq0S_eq_zero_iff (S.base.metric t) y 4 _).mpr
      exact metricRm04At_eq_zero_of_riemannOp_zero (S.base.metric t) y (hriem y)
    have hprop := curvature_normSq_eq_zero_on_Icc_of_eq_zero_at_left S hS htb
      (fun r hr => hcar ⟨ht.1.le.trans hr.1,hr.2⟩)
      (fun r hr => hreg ⟨ht.1.trans_le hr.1,hr.2⟩)
      (hcomplete t ⟨ht.1,htb⟩)
      ⟨K,hK,fun r hr y => hbound r ⟨ht.1.le.trans hr.1,hr.2⟩ y⟩ hflat
    have hterminal (y : M) : metricRm04At (S.base.metric b) y = 0 :=
      (normSq0S_eq_zero_iff (S.base.metric b) y 4 _).mp (hprop b ⟨htb.le,le_rfl⟩ y)
    have hrankzero := curvatureOperatorImageAt_finrank_eq_zero_of_riemannOp_eq_zero
      (S.base.metric b) (fun y => riemannOp_eq_zero_of_metricRm04At_zero
        (S.base.metric b) y (hterminal y)) x
    change Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 0 at hrankzero
    have hcontra : (1 : ℕ) = 0 := (hrankb x).symm.trans hrankzero
    exact Nat.noConfusion hcontra
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one

end DifferentialGeometry.PDE.RicciFlow
