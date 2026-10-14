import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedRestart
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Data.ENNReal.Inv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem standard_curvature_unbounded_before_finite_lifetime
    (S : StandardSolution)
    (T : ℝ) (hT : 0 < T)
    (hLifetime : S.val.lifetime = ENNReal.ofReal T)
    (θ : ℝ) (hθ : θ ∈ _root_.Set.Ico 0 T) (K : ℝ) :
    ∃ t ∈ _root_.Set.Ioo θ T, ∃ x : E3,
      K < Real.sqrt
        (normSq0S (S.val.metric t) x 4
          (metricRm04 (S.val.metric t) x)) := by
  by_contra hno
  have htail :
      ∀ t ∈ _root_.Set.Ioo θ T, ∀ x : E3,
        Real.sqrt
          (normSq0S (S.val.metric t) x 4
            (metricRm04 (S.val.metric t) x)) ≤ K := by
    intro t ht x
    exact le_of_not_gt (fun hx => hno ⟨t, ht, x, hx⟩)
  have hθlife : ENNReal.ofReal θ < S.val.lifetime := by
    rw [hLifetime]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ.1).mpr hθ.2
  obtain ⟨K₀, hK₀, hprefix⟩ :=
    S.val.curvature_bound θ hθ.1 hθlife
  have hK : 0 ≤ _root_.Max.max K₀ K := hK₀.trans (le_max_left K₀ K)
  have hwhole :
      ∀ t ∈ _root_.Set.Ico 0 T, ∀ x : E3,
        Real.sqrt
          (normSq0S (S.val.metric t) x 4
            (metricRm04 (S.val.metric t) x)) ≤ _root_.Max.max K₀ K := by
    intro t ht x
    by_cases htθ : t ≤ θ
    · exact (hprefix t ⟨ht.1, htθ⟩ x).trans (le_max_left K₀ K)
    · exact (htail t ⟨lt_of_not_ge htθ, ht.2⟩ x).trans
        (le_max_right K₀ K)
  obtain ⟨τ, _, KR, _, hrestart⟩ :=
    standard_closed_restart_extension_of_curvature_bound T (_root_.Max.max K₀ K) hT hK
  obtain ⟨_, _, Q, _, _, _, _, hExt, hStrict, _, _⟩ :=
    hrestart S.val hLifetime hwhole
  exact (not_le_of_gt hStrict) (S.property Q hExt).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_curvature_unbounded_before_finite_lifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_curvature_unbounded_before_finite_lifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_curvature_unbounded_before_finite_lifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_curvature_unbounded_before_finite_lifetime

theorem standard_curvature_limsup_eq_top
    (S : StandardSolution) (hfinite : S.val.lifetime ≠ ⊤) :
    Filter.limsup
      (fun t : ℝ =>
        ⨆ x : E3,
          ENNReal.ofReal
            (Real.sqrt
              (normSq0S (S.val.metric t) x 4
                (metricRm04 (S.val.metric t) x))))
      (𝓝[<] S.val.lifetime.toReal) = ⊤ := by
  let T : ℝ := S.val.lifetime.toReal
  have hT : 0 < T :=
    ENNReal.toReal_pos S.val.lifetime_pos.ne' hfinite
  have hLifetime : S.val.lifetime = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal hfinite).symm
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  apply Filter.le_limsup_of_frequently_le'
  apply (nhdsLT_basis S.val.lifetime.toReal).frequently_iff.mpr
  intro θ hθ
  have hmax : _root_.Max.max (0 : ℝ) θ ∈ _root_.Set.Ico 0 T :=
    ⟨le_max_left _ _, max_lt hT hθ⟩
  obtain ⟨t, ht, x, hx⟩ :=
    standard_curvature_unbounded_before_finite_lifetime
      S T hT hLifetime (_root_.Max.max 0 θ) hmax (r : ℝ)
  refine ⟨t, ⟨(le_max_right 0 θ).trans_lt ht.1, ht.2⟩, ?_⟩
  have hr :
      (r : ℝ≥0∞) ≤
        ENNReal.ofReal
          (Real.sqrt
            (normSq0S (S.val.metric t) x 4
              (metricRm04 (S.val.metric t) x))) := by
    have hh := ENNReal.ofReal_le_ofReal hx.le
    simpa only [ENNReal.ofReal_coe_nnreal] using hh
  exact hr.trans
    (le_iSup
      (fun y : E3 =>
        ENNReal.ofReal
          (Real.sqrt
            (normSq0S (S.val.metric t) y 4
              (metricRm04 (S.val.metric t) y))))
      x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_curvature_limsup_eq_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_curvature_limsup_eq_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_curvature_limsup_eq_top ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_curvature_limsup_eq_top

end DifferentialGeometry.PDE.RicciFlow
