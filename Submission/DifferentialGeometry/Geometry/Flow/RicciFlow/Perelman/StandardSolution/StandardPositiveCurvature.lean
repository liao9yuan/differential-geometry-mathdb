import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TravelingPhaseCoefficients
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardShiftedSupport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardPositiveSeed
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRayleighOperator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.leastUpperRicciAt_pos
    (S : PartialStandardSolution) (t₀ : ℝ) (ht₀ : t₀ ∈ S.domain)
    (htpos : 0 < t₀) (x₀ : E3) :
    0 < leastUpperRicciAt (S.metric t₀) x₀ := by
  obtain ⟨a, ha, hat, _haD, r, hr, eta, heta, hseed⟩ :=
    S.exists_positive_upperRicci_seed_before t₀ htpos ht₀
  have hTl := ((mem_lifetimeInterval_carrier
    S.lifetime S.lifetime_pos t₀).mp ht₀).2
  let Q := S.toSolutionOn.timeShift a
  let G := flowG Q
  let τ : ℝ := t₀ - a
  let u : ℝ → E3 → ℝ := fun s x => leastUpperRicciAt (S.metric (s + a)) x
  have hτ : 0 < τ := sub_pos.mpr hat
  obtain ⟨_hmetric, hcarrier, _hreg, C, c, hc, hphase, hgradient⟩ :=
    S.exists_traveling_phase_coefficients a t₀ ha hat hTl x₀ r hr
  have hcont : ContinuousOn (fun p : ℝ × E3 => u p.1 p.2)
      (spacetimeSlab (M := E3) τ) := by
    have hmap : Continuous (fun p : ℝ × E3 => (p.1 + a, p.2)) :=
      (continuous_fst.add continuous_const).prodMk continuous_snd
    have hm : _root_.Set.MapsTo (fun p : ℝ × E3 => (p.1 + a, p.2))
        (spacetimeSlab (M := E3) τ) (S.domain ×ˢ (_root_.Set.univ : Set E3)) :=
      fun p hp => ⟨hcarrier p.1 hp.1, _root_.Set.mem_univ p.2⟩
    have hh := S.leastUpperRicciAt_continuousOn.comp hmap.continuousOn hm
    exact hh
  have hnonneg : ∀ s ∈ _root_.Set.Icc 0 τ, ∀ x : E3, 0 ≤ u s x := by
    intro s hs x
    exact S.leastUpperRicciAt_nonneg (s + a) (hcarrier s hs) x
  have hinit : ∀ x ∈ Metric.closedBall (0 : E3) r, eta ≤ u 0 x := by
    intro x hx
    simpa only [u, zero_add] using hseed x hx
  have hsupport := S.shifted_leastUpperRicci_upper_support a t₀ ha.le hat hTl
  have hpos := DifferentialGeometry.Analysis.positive_of_traveling_ball_upper_supports
    G τ hτ x₀ r eta C c hr heta hc u hcont hnonneg hsupport hinit
    (fun s hs _hspos x hx => hphase s hs x hx)
    (fun s hs _hspos x _hx => hgradient s hs x)
  simpa only [u, τ, sub_add_cancel] using hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.leastUpperRicciAt_pos

theorem PartialStandardSolution.curvatureOperator_positive
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain)
    (htpos : 0 < t) (x : E3) (n : ℕ) (c : Fin n → ℝ)
    (v w : Fin n → TangentSpace (𝓡 3) x)
    (hvw : 0 < algebraicCurvatureIdentityQuadraticEval (S.metric t) c v w) :
    0 < algebraicCurvatureOperatorQuadraticEval
      (metricAlgebraicCurvatureTensorAt (S.metric t) x) c v w :=
  algebraicCurvatureOperatorQuadraticEval_pos_of_leastUpperRicciAt_pos
    (S.metric t) x (S.leastUpperRicciAt_pos t ht htpos x) n c v w hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvatureOperator_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvatureOperator_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvatureOperator_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.curvatureOperator_positive

theorem PartialStandardSolution.exists_pos_leastUpperRicciAt_tip_lower_bound
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 ≤ T)
    (hTl : ENNReal.ofReal T < S.lifetime) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ _root_.Set.Icc 0 T,
      c ≤ leastUpperRicciAt (S.metric t) (0 : E3) := by
  have hdom (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) : t ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTl⟩
  have hmap : Continuous (fun t : ℝ => (t, (0 : E3))) :=
    continuous_id.prodMk continuous_const
  have hcont : ContinuousOn
      (fun t => leastUpperRicciAt (S.metric t) (0 : E3)) (_root_.Set.Icc 0 T) := by
    have hh := S.leastUpperRicciAt_continuousOn.comp (f := fun t : ℝ => (t, (0 : E3)))
      (s := _root_.Set.Icc 0 T) hmap.continuousOn (fun t ht => ⟨hdom t ht, _root_.Set.mem_univ _⟩)
    exact hh
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) hcont
  refine ⟨leastUpperRicciAt (S.metric t) 0, ?_, hmin⟩
  rcases eq_or_lt_of_le ht.1 with heq | hpos
  · subst t
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_eq S.leastUpperRicciAt_initial_tip.symm
  · exact S.leastUpperRicciAt_pos t (hdom t ht) hpos 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_pos_leastUpperRicciAt_tip_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_pos_leastUpperRicciAt_tip_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_pos_leastUpperRicciAt_tip_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_pos_leastUpperRicciAt_tip_lower_bound

end DifferentialGeometry.PDE.RicciFlow
