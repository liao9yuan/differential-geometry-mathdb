import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicComparisonStability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalNeckTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]

private local instance neckScaleStabilityC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckScaleStabilityC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckScaleStabilityC1 target :: scope.openDecls } }

theorem StrongNeck.exists_rescaled_transport_tolerances_of_ancient
    {Sm : SolutionOn (I := I3) (M := P) ancientTimeInterval} (hSm : IsSolutionOn Sm)
    {alpha : ℝ} {p : P} (nk : StrongNeck Sm (neckModelTolerance alpha) p 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ K) :
    ∃ eta beta : ℝ, 0 < eta ∧ 0 < beta ∧
      ∀ c : ℝ, ∀ hc : 0 < c, |c - Sm.scalar 0 p| < eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ {x : M} {t : ℝ} (hQ : 0 < S.scalar t x) {b : ℝ}, b < -1 →
      _root_.Set.MapsTo (parabolicTime t (S.scalar t x)) (_root_.Set.Icc b 0) D.carrier →
      _root_.Set.MapsTo (parabolicTime t (S.scalar t x)) (_root_.Set.Ioo b 0) D.regular →
      ∀ F : PartialDiffeomorph I3 I3 P M ∞, (U : Set P) ⊆ F.source → F p = x →
      MetricComparisonOn (rescaledMetric Sm 0 c hc) (rescaledMetric S t (S.scalar t x) hQ)
        F U (_root_.Set.Icc (-1 : ℝ) 0) ⌈(2 * alpha)⁻¹⌉₊ beta →
      ∃ nk' : StrongNeck S (2 * alpha) x t,
        nk'.map = partialDiffeomorphTransMixed nk.map F := by
  have htarget : 0 < neckSourceTolerance alpha := neckSourceTolerance_pos ha
  obtain ⟨eta, beta, heta, hbeta, htransfer⟩ :=
    exists_rescaledMetric_comparison_tolerance_on_compact Sm hSm
      (a := -(Sm.scalar 0 p)⁻¹ - 1) (t := 0) (depth := 1) (Q := Sm.scalar 0 p)
      zero_lt_one nk.Q_pos (by simp only [zero_sub, one_div]; linarith)
      (fun _ hs => hs.2) (fun _ hs => hs.2) U hUcompact hK hKU
      ⌈(2 * alpha)⁻¹⌉₊ htarget
  refine ⟨eta, beta, heta, hbeta, ?_⟩
  intro c hc hnear M _ _ _ _ _ D S hS x t hQ b hb hdomain hregular F hF hbase C
  have ht : t ∈ D.carrier := by
    have hh := hdomain (show (0 : ℝ) ∈ _root_.Set.Icc b 0 from ⟨by linarith, le_rfl⟩)
    simpa only [parabolicTime_zero] using hh
  let T := parabolicSolution S t (S.scalar t x) hQ ht
  have hT : IsSolutionOn T := parabolicSolution_isSolutionOn S hS t (S.scalar t x) hQ ht
  obtain ⟨cmp⟩ := htransfer c hc hnear M T hT hb hdomain hregular F hF C
  have htime : _root_.Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier := by
    intro r hr
    let s := (r - t) * S.scalar t x
    have hs : s ∈ _root_.Set.Icc b 0 := by
      have hlo := mul_le_mul_of_nonneg_right hr.1 hQ.le
      have hi : (S.scalar t x)⁻¹ * S.scalar t x = 1 := inv_mul_cancel₀ hQ.ne'
      dsimp only [s]
      constructor
      · nlinarith
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr.2) hQ.le
    have hh := hdomain hs
    have heq : parabolicTime t (S.scalar t x) s = r := by
      dsimp only [parabolicTime, s]
      rw [mul_div_cancel_right₀ _ hQ.ne']
      ring
    rwa [heq] at hh
  apply nk.exists_transport_of_local_comparisons hQ F cmp ha hsmall htarget.le le_rfl
    le_rfl hbase houter (hKU.trans hF) htime
  · intro q s hs z hz v
    obtain ⟨y, hy, rfl⟩ := hz
    have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
      change (0 : ℝ) ≤ 0
      exact le_rfl
    let R := parabolicSolution Sm 0 (Sm.scalar 0 p) nk.Q_pos hzero
    have hR : IsSolutionOn R := parabolicSolution_isSolutionOn Sm hSm 0 (Sm.scalar 0 p)
      nk.Q_pos hzero
    have hRdomain : _root_.Set.Icc (-2 : ℝ) 0 ⊆
        (parabolicInterval ancientTimeInterval 0 (Sm.scalar 0 p) hzero).carrier := by
      intro r hr
      change 0 + r / Sm.scalar 0 p ≤ 0
      simpa only [zero_add] using div_nonpos_of_nonpos_of_nonneg hr.2 nk.Q_pos.le
    have hRregular : _root_.Set.Ioo (-2 : ℝ) 0 ⊆
        (parabolicInterval ancientTimeInterval 0 (Sm.scalar 0 p) hzero).regular := by
      intro r hr
      change 0 + r / Sm.scalar 0 p < 0
      simpa only [zero_add] using div_neg_of_neg_of_pos hr.2 nk.Q_pos
    exact (cmp.jet_contDiffOn_of_solutions R hR T hT (by norm_num : (-2 : ℝ) < -1) hb
      (by norm_num : (-1 : ℝ) < 0) hRdomain hRregular hdomain hregular
      q (nk.map y) (houter y hy) v s hs).differentiableWithinAt (by simp)
  · intro q s hs _hu y hy v
    have hsub := neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact (nk.hasDerivWithinAt_comparison_jet_of_ancient hSm q hs y
      (hsub hy) v).differentiableWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_rescaled_transport_tolerances_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_rescaled_transport_tolerances_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_rescaled_transport_tolerances_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_rescaled_transport_tolerances_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
