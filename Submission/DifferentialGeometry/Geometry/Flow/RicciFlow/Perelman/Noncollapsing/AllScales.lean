import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Scale.Transfer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def KappaNoncollapsedOnAllScales
    (S : SolutionOn (I := I) (M := M) D) (kappa : Real) : Prop :=
  0 < kappa ∧
    ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
      (B : FlowMetricBall S t), B.IsRmControlled → B.IsKappaNoncollapsed kappa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedOnAllScales then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedOnAllScales"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedOnAllScales ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaNoncollapsedOnAllScales

theorem kappa_noncollapsed_on_all_scales_iff
    {S : SolutionOn (I := I) (M := M) D} {kappa : Real} :
  KappaNoncollapsedOnAllScales S kappa ↔
      0 < kappa ∧
        ∀ rho : Real, 0 < rho → KappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · rintro ⟨hkappa, hS⟩
    refine ⟨hkappa, ?_⟩
    intro rho hrho
    exact ⟨hrho, by
      intro t B _hBrho hB
      exact hS t B hB⟩
  · rintro ⟨hkappa, hS⟩
    refine ⟨hkappa, ?_⟩
    intro t B hB
    let rho : Real := B.radius + 1
    have hrho : 0 < rho := by
      dsimp only [rho]
      linarith [B.radius_pos]
    have hbelow := hS rho hrho
    exact hbelow.2 t B (by
      dsimp only [rho]
      linarith) hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_iff

theorem kappa_noncollapsed_on_all_scales_of_kappa_le
    {S : SolutionOn (I := I) (M := M) D}
    {kappa kappa' : Real}
    (hS : KappaNoncollapsedOnAllScales S kappa')
    (hkappa : 0 < kappa) (hkappa_le : kappa ≤ kappa') :
    KappaNoncollapsedOnAllScales S kappa := by
  refine ⟨hkappa, ?_⟩
  intro t B hB
  rcases hS.2 t B hB with ⟨_, hvol⟩
  refine ⟨hkappa, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hkappa_le) le_rfl).trans hvol

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_of_kappa_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_of_kappa_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_of_kappa_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.kappa_noncollapsed_on_all_scales_of_kappa_le

theorem parabolic_noncollapse_all_scales
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    {kappa : Real} (hS : KappaNoncollapsedOnAllScales S kappa) :
    KappaNoncollapsedOnAllScales
      (parabolicSolution (I := I) S tau R hR htau) kappa := by
  apply (kappa_noncollapsed_on_all_scales_iff).2
  refine ⟨hS.1, ?_⟩
  intro rho hrho
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  let rho₀ : Real := rho / Real.sqrt R
  have hrho₀ : 0 < rho₀ := by
    dsimp only [rho₀]
    exact div_pos hrho hsqrt
  have hbelow := ((kappa_noncollapsed_on_all_scales_iff).1 hS).2 rho₀ hrho₀
  have hpara := parabolic_noncollapse (I := I) S tau R hR htau kappa rho₀ hbelow
  have hscale : Real.sqrt R * rho₀ = rho := by
    dsimp only [rho₀]
    field_simp [ne_of_gt hsqrt]
  simpa only [hscale] using hpara

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse_all_scales then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse_all_scales"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse_all_scales ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.parabolic_noncollapse_all_scales

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
