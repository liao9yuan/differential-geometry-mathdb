import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductAllOrderDerivativeBernstein
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
private theorem inverse_time_power_eq (A t s : ℝ) (m : ℕ) :
    A / (t - s) ^ (m + 1) = A * (t - s) ^ (-((m : ℤ) + 1)) := by
  rw [zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast, div_eq_mul_inv]

run_cmd do
  let target := ``Submission.inverse_time_power_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `inverse_time_power_eq target :: scope.openDecls } }

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

theorem nonempty_curveShorteningRegularityInput
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    Nonempty (CurveShorteningRegularityInput B L₀ Θ₀) := by
  obtain ⟨δ, r₀, A, hδ, hδ1, hr₀, hr₀1, hA, hprod⟩ :=
    ProductCurve.exists_uniform_iteratedDs_curvature_bounds B L₀ Θ₀ hL₀ hΘ₀
  refine ⟨⟨δ, r₀, A, hδ, hδ1, hr₀, hr₀1, hA, ?_, ?_⟩⟩
  · intro T hT hTb J hJ c hc hlen hcurv tstar htstar r hr hrr₀ hlenr harc m x t htJ hts htime
    have huniq : UniqueDiffOn ℝ J := by
      rcases hJ with rfl | rfl
      · exact uniqueDiffOn_Ico a T
      · exact uniqueDiffOn_Icc hT
    have hub : t ≤ b := by
      rcases hJ with rfl | rfl
      · exact htJ.2.le.trans hTb
      · exact htJ.2.trans hTb
    have hsub : _root_.Set.Icc a t ⊆ J := by
      rcases hJ with rfl | rfl
      · intro v hv
        exact ⟨hv.1, hv.2.trans_lt htJ.2⟩
      · exact _root_.Set.Icc_subset_Icc le_rfl htJ.2
    have hprod_est := hprod 1 zero_lt_one c.toProductCurve J huniq
      ((c.toProductCurve_isSolutionOn_iff B.family.metric 1 J).mpr hc)
      (by simpa using hlen) (by simpa using hcurv)
      tstar t r htstar.1 hts hub hsub hr hrr₀ (by simpa using hlenr)
      htime (by simpa only [c.toProductCurve_arcLength,
        c.toProductCurve_arcTotalCurvature] using harc) m x
    rw [c.toProductCurve_curvatureVector, c.toProductCurve_iteratedDs,
      c.toProductCurve_normSq] at hprod_est
    rw [← inverse_time_power_eq]
    exact hprod_est
  · intro lambda hlambda _ T hT hTb J hJ c hc hlen hcurv tstar htstar r hr hrr₀ hlenr harc m x t htJ hts htime
    have huniq : UniqueDiffOn ℝ J := by
      rcases hJ with rfl | rfl
      · exact uniqueDiffOn_Ico a T
      · exact uniqueDiffOn_Icc hT
    have hub : t ≤ b := by
      rcases hJ with rfl | rfl
      · exact htJ.2.le.trans hTb
      · exact htJ.2.trans hTb
    have hsub : _root_.Set.Icc a t ⊆ J := by
      rcases hJ with rfl | rfl
      · intro v hv
        exact ⟨hv.1, hv.2.trans_lt htJ.2⟩
      · exact _root_.Set.Icc_subset_Icc le_rfl htJ.2
    rw [← inverse_time_power_eq]
    exact hprod lambda hlambda c J huniq hc hlen hcurv tstar t r
      htstar.1 hts hub hsub hr hrr₀ hlenr htime harc m x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.nonempty_curveShorteningRegularityInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.nonempty_curveShorteningRegularityInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.nonempty_curveShorteningRegularityInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.nonempty_curveShorteningRegularityInput

def curveShorteningRegularityInput
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    CurveShorteningRegularityInput B L₀ Θ₀ :=
  Classical.choice (nonempty_curveShorteningRegularityInput B L₀ Θ₀ hL₀ hΘ₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningRegularityInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningRegularityInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningRegularityInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningRegularityInput

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
