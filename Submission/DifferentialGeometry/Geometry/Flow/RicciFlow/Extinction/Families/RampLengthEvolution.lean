import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.EnergyIntegral
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.GoodWindows

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

omit hCompact hConnected hBoundary in
def RampLengthEvolution (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
    c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc a b) →
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ContinuousOn (c.length B.family.metric lambda) (_root_.Set.Icc s t) ∧
      IntervalIntegrable (c.energy B.family.metric lambda) _root_.MeasureTheory.MeasureSpace.volume s t ∧
      (∀ v ∈ _root_.Set.Icc s t, 0 ≤ c.energy B.family.metric lambda v) ∧
      (∫ v in s..t, c.energy B.family.metric lambda v) ≤
        Real.exp (B.B₀ * (t - s)) * c.length B.family.metric lambda s ∧
      (∀ v ∈ _root_.Set.Icc s t,
        c.length B.family.metric lambda v ≤
          Real.exp (B.B₀ * (v - s)) * c.length B.family.metric lambda s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.RampLengthEvolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.RampLengthEvolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.RampLengthEvolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.RampLengthEvolution

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampLengthEvolution_of_hasDerivAt_length
    (B : RicciBackground (I := I) (M := Q) D a b)
    (h : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc a b) →
      ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
        ContinuousOn (c.length B.family.metric lambda) (_root_.Set.Icc s t) ∧
        IntervalIntegrable (c.energy B.family.metric lambda) _root_.MeasureTheory.MeasureSpace.volume s t ∧
        (∀ v ∈ _root_.Set.Icc s t, 0 ≤ c.energy B.family.metric lambda v) ∧
        (∀ v ∈ _root_.Set.Ioo s t, HasDerivAt (c.length B.family.metric lambda)
          (B.B₀ * c.length B.family.metric lambda v - c.energy B.family.metric lambda v) v) ∧
        (∀ v ∈ _root_.Set.Icc s t,
          c.length B.family.metric lambda v ≤
            Real.exp (B.B₀ * (v - s)) * c.length B.family.metric lambda s)) :
    RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro lambda hlambda hlambda_one c hsol s t has hst htb
  obtain ⟨hcont, hint, hnn, hderiv, hgrowth⟩ :=
    h lambda hlambda hlambda_one c hsol s t has hst htb
  exact ⟨hcont, hint, hnn,
    DifferentialGeometry.Analysis.ODE.integral_le_exp_mul_of_hasDerivAt_sub B.B₀_nonneg hst
      hcont hderiv hint hnn (productCurve_length_nonneg B.family.metric lambda t c),
    hgrowth⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rampLengthEvolution_of_hasDerivAt_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rampLengthEvolution_of_hasDerivAt_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rampLengthEvolution_of_hasDerivAt_length ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rampLengthEvolution_of_hasDerivAt_length

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_rampProductBounds_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) (D := D) (a := a) (b := b) B) :
    RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B := by
  intro L Theta hL hTheta lambda hlambda hlambda_one c hsol hlen htot t ht
  have hexp : 0 ≤ Real.exp (B.B₀ * (t - a)) := Real.exp_nonneg _
  have hgrowth_at : c.length B.family.metric lambda t ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a :=
    (hev lambda hlambda hlambda_one c hsol a t le_rfl ht.1 ht.2).2.2.2.2 t ⟨ht.1, le_rfl⟩
  have henergy : (∫ v in a..t, c.energy B.family.metric lambda v) ≤
      Real.exp (B.B₀ * (t - a)) * c.length B.family.metric lambda a :=
    (hev lambda hlambda hlambda_one c hsol a t le_rfl ht.1 ht.2).2.2.2.1
  have hreverse : c.length B.family.metric lambda b ≤
      Real.exp (B.B₀ * (b - t)) * c.length B.family.metric lambda t :=
    (hev lambda hlambda hlambda_one c hsol t b ht.1 ht.2 le_rfl).2.2.2.2 b ⟨ht.2, le_rfl⟩
  have htot_add : c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
      Real.exp ((B.C + B.B₀) * (t - a)) * (Theta + L) := by
    refine (hcurv lambda hlambda hlambda_one c hsol t ht).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add htot hlen) (Real.exp_nonneg _)
  exact ⟨hgrowth_at.trans (mul_le_mul_of_nonneg_left hlen hexp),
    hreverse,
    henergy.trans (mul_le_mul_of_nonneg_left hlen hexp),
    htot_add⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_rampProductBounds_of_length_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_rampProductBounds_of_length_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_rampProductBounds_of_length_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_rampProductBounds_of_length_evolution


omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_goodWindows_energy_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b) (L₀ : ℝ)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B) :
    ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      _root_.MeasureTheory.IntegrableOn (c.energy B.family.metric lambda) (_root_.Set.Icc a b) _root_.MeasureTheory.MeasureSpace.volume ∧
        (∫ v in a..b, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (b - a)) * L₀ := by
  intro lambda hlambda hlambda_one c hsol hlen
  obtain ⟨-, hint, -, hbound, -⟩ :=
    hev lambda hlambda hlambda_one c hsol a b le_rfl B.lt.le le_rfl
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le B.lt.le).mp hint,
    hbound.trans (mul_le_mul_of_nonneg_left hlen (Real.exp_nonneg _))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_goodWindows_energy_of_length_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_goodWindows_energy_of_length_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_goodWindows_energy_of_length_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_goodWindows_energy_of_length_evolution

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_finite_good_windows_of_length_evolution
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hslice : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      ∀ t ∈ _root_.Set.Icc a b, c.SliceRegularity B.family.metric lambda t) :
    let delta := localRegularityDelta B L₀ Theta₀ K
    let r₀ := localRegularityRadius B L₀ Theta₀ K
    let areg := localRegularityCoefficient B L₀ Theta₀ K 0
    let C_E := Real.exp (B.B₀ * (b - a)) * L₀
    ∀ ell threshold : ℝ, 0 < ell → 0 < threshold →
      let r := _root_.Min.min r₀ (_root_.Min.min (ell / 2) (delta ^ 2 / threshold))
      let d := delta * r ^ 2
      d < b - a →
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (_root_.Set.Icc a b) →
        c.IsRampOn B.family.metric lambda (_root_.Set.Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ _root_.Set.Icc a b, ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          (∀ w ∈ starts, w ∈ _root_.Set.Icc a (b - d) ∧
            c.energy B.family.metric lambda w ≤ threshold) ∧
          goodWindowUnion starts d ⊆ _root_.Set.Ioo a b ∧
          _root_.MeasureTheory.MeasureSpace.volume (_root_.Set.Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C_E / threshold) ∧
          (∀ x t, t ∈ goodWindowUnion starts d →
            c.curvature B.family.metric lambda x t ≤ Real.sqrt (2 * areg / d)) ∧
          ∀ w ∈ starts, _root_.Set.Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ _root_.Set.Ioo (w + d / 2) (w + d) :=
  rfs_finite_good_windows_of_energy_bound B L₀ Theta₀ K
    (rfs_goodWindows_energy_of_length_evolution B L₀ hev) hslice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_finite_good_windows_of_length_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_finite_good_windows_of_length_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_finite_good_windows_of_length_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_finite_good_windows_of_length_evolution

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
