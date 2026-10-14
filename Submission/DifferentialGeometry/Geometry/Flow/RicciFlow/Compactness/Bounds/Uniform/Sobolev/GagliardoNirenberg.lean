import Submission.DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.FiberNorm.Basic

import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Algebra.CovariantSumCross
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.MorreySecondDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def metricVolRadius (g : SmoothRiemannianMetric I M) : ℝ :=
  Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricVolRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricVolRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricVolRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.metricVolRadius

noncomputable def volCompareC (Λ : ℝ) : ℝ :=
  Real.sqrt (Λ ^ Module.finrank ℝ E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volCompareC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volCompareC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volCompareC ``Submission.DifferentialGeometry.PDE.RicciFlow.volCompareC

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volumeReal_cross
    (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal ∧
      ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
  let μBase := riemannianVolumeMeasure (I := I) (M := M) gBase
  let μg := riemannianVolumeMeasure (I := I) (M := M) g
  let L : ℝ := volCompareC (E := E) Λ
  have : _root_.MeasureTheory.IsFiniteMeasure μBase :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) gBase
  have : _root_.MeasureTheory.IsFiniteMeasure μg :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hmeas := volumeMeasure_cross_le (I := I) (M := M) gBase g hEq
  constructor
  · have hle : μg Set.univ ≤ ENNReal.ofReal L * μBase Set.univ := by
      have h := hmeas.1 Set.univ
      simpa only [μg, μBase, L, volCompareC, Measure.smul_apply, smul_eq_mul] using h
    have htop : ENNReal.ofReal L * μBase Set.univ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (_root_.MeasureTheory.measure_ne_top μBase Set.univ)
    have hreal := ENNReal.toReal_mono htop hle
    simpa only [μg, μBase, L, volCompareC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hreal
  · have hle : μBase Set.univ ≤ ENNReal.ofReal L * μg Set.univ := by
      have h := hmeas.2 Set.univ
      simpa only [μg, μBase, L, volCompareC, Measure.smul_apply, smul_eq_mul] using h
    have htop : ENNReal.ofReal L * μg Set.univ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (_root_.MeasureTheory.measure_ne_top μg Set.univ)
    have hreal := ENNReal.toReal_mono htop hle
    simpa only [μg, μBase, L, volCompareC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volumeReal_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volumeReal_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volumeReal_cross ``Submission.DifferentialGeometry.PDE.RicciFlow.volumeReal_cross

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volRadius_cross
    (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    metricVolRadius (I := I) (M := M) g ≤
        Real.sqrt (volCompareC (E := E) Λ) * metricVolRadius (I := I) (M := M) gBase ∧
      metricVolRadius (I := I) (M := M) gBase ≤
        Real.sqrt (volCompareC (E := E) Λ) * metricVolRadius (I := I) (M := M) g := by
  have hvol := volumeReal_cross (I := I) (M := M) gBase g hEq
  have hL : 0 ≤ volCompareC (E := E) Λ := by
    exact Real.sqrt_nonneg _
  constructor
  · refine le_trans (Real.sqrt_le_sqrt hvol.1) ?_
    rw [Real.sqrt_mul hL]
    rfl
  · refine le_trans (Real.sqrt_le_sqrt hvol.2) ?_
    rw [Real.sqrt_mul hL]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volRadius_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volRadius_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volRadius_cross ``Submission.DifferentialGeometry.PDE.RicciFlow.volRadius_cross

noncomputable def volClassC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  _root_.Max.max (S * VBase) (if VBase = 0 then 0 else S / VBase)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volClassC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volClassC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volClassC ``Submission.DifferentialGeometry.PDE.RicciFlow.volClassC

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem volClassC_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) :
    0 ≤ volClassC (E := E) (I := I) (M := M) gBase Λ := by
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hVBase : 0 ≤ VBase := Real.sqrt_nonneg _
  unfold volClassC
  dsimp only
  exact le_trans (mul_nonneg hS hVBase) (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volClassC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volClassC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volClassC_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.volClassC_nonneg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volClassC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    metricVolRadius (I := I) (M := M) g ≤
        volClassC (E := E) (I := I) (M := M) gBase Λ ∧
      1 / metricVolRadius (I := I) (M := M) g ≤
        volClassC (E := E) (I := I) (M := M) gBase Λ := by
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  let Vg := metricVolRadius (I := I) (M := M) g
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hVBase : 0 ≤ VBase := Real.sqrt_nonneg _
  have hVg : 0 ≤ Vg := Real.sqrt_nonneg _
  have hrad := volRadius_cross (I := I) (M := M) gBase g hEq
  have hfwd : Vg ≤ S * VBase := hrad.1
  have hrev : VBase ≤ S * Vg := hrad.2
  change Vg ≤ _root_.Max.max (S * VBase) (if VBase = 0 then 0 else S / VBase) ∧
    1 / Vg ≤ _root_.Max.max (S * VBase) (if VBase = 0 then 0 else S / VBase)
  constructor
  · exact le_trans hfwd (le_max_left _ _)
  · by_cases hVBase0 : VBase = 0
    · have hVg0 : Vg = 0 := by
        rw [hVBase0, _root_.MulZeroClass.mul_zero] at hfwd
        exact le_antisymm hfwd hVg
      simp [hVg0, hVBase0]
    · have hVBasePos : 0 < VBase :=
        lt_of_le_of_ne hVBase (fun h => hVBase0 h.symm)
      have hVgPos : 0 < Vg := by
        have hVgNe : Vg ≠ 0 := by
          intro hVg0
          rw [hVg0, _root_.MulZeroClass.mul_zero] at hrev
          exact hVBase0 (le_antisymm hrev hVBase)
        exact lt_of_le_of_ne hVg (fun h => hVgNe h.symm)
      have hinv : 1 / Vg ≤ S / VBase := by
        rw [div_le_div_iff₀ hVgPos hVBasePos]
        simpa only [one_mul] using hrev
      rw [if_neg hVBase0]
      exact le_trans hinv (le_max_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.volClassC_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.volClassC_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.volClassC_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.volClassC_spec

def gnClassLogC (n k : ℕ) (B : ℝ) : ℝ :=
  _root_.Max.max (_root_.Max.max (gnStepConst n k) 1) (gnStepConst n k * B + gnStepConst n k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gnClassLogC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gnClassLogC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gnClassLogC ``Submission.DifferentialGeometry.PDE.RicciFlow.gnClassLogC

noncomputable def gnClassC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) : ℝ :=
  let B := volClassC (E := E) (I := I) (M := M) gBase Λ
  gnClassLogC (Module.finrank ℝ E) k B ^ (2 * k ^ 2) * (_root_.Max.max 1 B) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gnClassC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gnClassC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gnClassC ``Submission.DifferentialGeometry.PDE.RicciFlow.gnClassC

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem gnClassC_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) :
    0 ≤ gnClassC (E := E) (I := I) (M := M) gBase Λ k := by
  unfold gnClassC
  exact mul_nonneg (pow_nonneg (le_trans zero_le_one
    (le_trans (le_max_right _ _) (le_max_left _ _))) _) (sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gnClassC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gnClassC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gnClassC_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.gnClassC_nonneg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem gnClassC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) (k : ℕ) :
    gnRsConst (Module.finrank ℝ E) k (metricVolRadius (I := I) (M := M) g) ≤
      gnClassC (E := E) (I := I) (M := M) gBase Λ k := by
  let n := Module.finrank ℝ E
  let V := metricVolRadius (I := I) (M := M) g
  let B := volClassC (E := E) (I := I) (M := M) gBase Λ
  have hvol := volClassC_spec (I := I) (M := M) gBase g hEq
  have hV : V ≤ B := hvol.1
  have hInv : 1 / V ≤ B := hvol.2
  have hStep : 0 ≤ gnStepConst n k := by
    unfold gnStepConst
    exact le_trans zero_le_one (le_max_right _ _)
  have hLog : gnLogConst n k V ≤ gnClassLogC n k B := by
    unfold gnLogConst gnClassLogC
    apply max_le_max (le_refl _)
    simpa only [add_comm] using
      (add_le_add_right (mul_le_mul_of_nonneg_left hInv hStep) (gnStepConst n k))
  have hLog0 : 0 ≤ gnLogConst n k V := by
    unfold gnLogConst
    exact le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hClassLog0 : 0 ≤ gnClassLogC n k B := by
    unfold gnClassLogC
    exact le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hMax : _root_.Max.max 1 V ≤ _root_.Max.max 1 B := max_le_max (le_refl _) hV
  have hLogPow : gnLogConst n k V ^ (2 * k ^ 2) ≤
      gnClassLogC n k B ^ (2 * k ^ 2) :=
    pow_le_pow_left₀ hLog0 hLog _
  have hMaxPow : (_root_.Max.max 1 V) ^ 2 ≤ (_root_.Max.max 1 B) ^ 2 :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hMax _
  have hmul := mul_le_mul hLogPow hMaxPow (sq_nonneg _) (pow_nonneg hClassLog0 _)
  simpa only [n, V, B, gnRsConst, gnClassC] using hmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gnClassC_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gnClassC_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gnClassC_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.gnClassC_spec

theorem gn_rs_uniform
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ gnClassC (E := E) (I := I) (M := M) gBase Λ k ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        ∀ (r s : ℕ) (u : Integral.L2.SmoothCcTensor g r s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g r s x (u.toSection x) ≤ Λ₀ ^ 2) →
          ∀ j : ℕ, 0 < j → j < k →
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
                    ((iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
                ∂(riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
              gnClassC (E := E) (I := I) (M := M) gBase Λ k *
                Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
                (Integral.L2.tensorL2Norm (I := I) g r (s + k)
                  (iteratedCovGrad (I := I) g r s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  refine ⟨gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ k, ?_⟩
  intro g hEq r s u Λ₀ hΛ₀ hsup j hj0 hjk
  have hgn := (gn_rs_bound (I := I) (M := M) g r s k hk).2 u Λ₀ hΛ₀ hsup j hj0 hjk
  have hcoef := gnClassC_spec (I := I) (M := M) gBase g hEq k
  refine le_trans hgn ?_
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hΛ₀ _)
  · exact Real.rpow_nonneg
      (Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + k) _) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gn_rs_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gn_rs_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gn_rs_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.gn_rs_uniform

noncomputable def rankTwoGridC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (R : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) *
    ((k : ℝ) *
      (_root_.Max.max
        (morreyTwoC (I := I) (M := M) gBase Λ * R)
        (_root_.Max.max (gnClassC (E := E) (I := I) (M := M) gBase Λ k) 1)) ^
          (7 * k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rankTwoGridC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rankTwoGridC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rankTwoGridC ``Submission.DifferentialGeometry.PDE.RicciFlow.rankTwoGridC

omit [BoundarylessManifold I M] in
theorem rank_two_grid_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (R : ℝ) :
    0 ≤ rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R := by
  unfold rankTwoGridC
  exact mul_nonneg
    (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg k)
      (pow_nonneg (le_trans zero_le_one
        (le_trans (le_max_right _ 1) (le_max_right _ _))) _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rank_two_grid_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rank_two_grid_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rank_two_grid_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.rank_two_grid_nonneg

theorem rank_two_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R A : ℝ),
        0 ≤ R →
        0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 k P‖ ≤ A →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * A ^ 2 := by
  classical
  intro g hEq hjet1 hjet2 P R A hR hA hP2 htop
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hdim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hpt⟩ := morreyTwoC_spec (I := I) (M := M) gBase hΛ hdim
  have hCgn := gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ k
  let Lam : ℝ := morreyTwoC (I := I) (M := M) gBase Λ * R
  have hLam : 0 ≤ Lam := mul_nonneg hCpt hR
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hLamSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
    intro x
    have hx := hpt g hEq hjet1 hjet2 P x
    rw [hrange] at hx
    calc
      _ ≤ morreyTwoC (I := I) (M := M) gBase Λ ^ 2 *
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := hx
      _ ≤ morreyTwoC (I := I) (M := M) gBase Λ ^ 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
      _ = Lam ^ 2 := by
        exact (mul_pow _ _ 2).symm
  have hGNP : ∀ j : ℕ, 0 < j → j < k →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) ^
            ((k : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^
            ((j : ℝ) / (k : ℝ)) ≤
        gnClassC (E := E) (I := I) (M := M) gBase Λ k *
          Lam ^ (2 * (1 - (j : ℝ) / (k : ℝ))) *
          A ^ (2 * (j : ℝ) / (k : ℝ)) := by
    intro j hj0 hjk
    have hb := (gn_rs_uniform (E := E) (I := I) (M := M) gBase Λ k hk).2
      g hEq 0 2 P Lam hLam hLamSup j hj0 hjk
    have hnorm : Integral.L2.tensorL2Norm (I := I) g 0 (2 + k)
        (iteratedCovGrad (I := I) g 0 2 k P).toFun =
        ‖iteratedCovGrad (I := I) g 0 2 k P‖ :=
      (Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g 0 2 k P)).symm
    rw [hnorm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow
        (norm_nonneg (iteratedCovGrad (I := I) g 0 2 k P))
        htop (by positivity))
      (mul_nonneg hCgn (Real.rpow_nonneg hLam _)))
  let G : ℝ :=
    (k : ℝ) *
      (_root_.Max.max Lam (_root_.Max.max (gnClassC (E := E) (I := I) (M := M) gBase Λ k) 1)) ^
        (7 * k) * A ^ 2
  have hterm : ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
        MeasureTheory.Integrable
            (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ G := by
    intro n hn e he
    have hn_le : n ≤ k := by
      have := Finset.mem_range.mp hn
      omega
    have hsum : ∑ m, e m = k := Finset.Nat.mem_antidiagonalTuple.mp he
    have hres := Integral.Connection.grid_prod_int_le (I := I) (M := M) g P
      hA k hk hLam hLamSup htop hCgn hGNP n hn_le e hsum
    simpa only [G] using hres
  have hint : MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finsetSum
    intro n hn
    apply MeasureTheory.integrable_finsetSum
    intro e he
    exact (hterm n hn e he).1
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_finsetSum _
    (fun n hn => MeasureTheory.integrable_finsetSum _
      (fun e he => (hterm n hn e he).1))]
  have hinner : ∀ n ∈ Finset.range (k + 1),
      (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∫ x, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro n hn
    exact MeasureTheory.integral_finsetSum _ (fun e he => (hterm n hn e he).1)
  rw [Finset.sum_congr rfl hinner]
  calc
    ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ n ∈ Finset.range (k + 1),
            ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, G := by
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro e he
          exact (hterm n hn e he).2
    _ = (∑ n ∈ Finset.range (k + 1),
          ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * G := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * A ^ 2 := by
        simp only [rankTwoGridC, G, Lam, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rank_two_grid_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rank_two_grid_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rank_two_grid_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.rank_two_grid_uniform

noncomputable def h2GridC
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then
    volCompareC (E := E) Λ *
      ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  else
    rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * R ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.h2GridC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.h2GridC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.h2GridC ``Submission.DifferentialGeometry.PDE.RicciFlow.h2GridC

omit [BoundarylessManifold I M] in
theorem h2_grid_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) (k : ℕ) :
    0 ≤ h2GridC (E := E) (I := I) (M := M) gBase Λ R k := by
  unfold h2GridC
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  · exact mul_nonneg
      (rank_two_grid_nonneg (E := E) (I := I) (M := M) gBase Λ k R)
      (sq_nonneg R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg

theorem h2_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R : ℝ),
        0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ∀ k : ℕ, k ≤ 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
              h2GridC (E := E) (I := I) (M := M) gBase Λ R k := by
  classical
  intro g hEq hjet1 hjet2 P R hR hP2 k hk2
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  by_cases hk0 : k = 0
  · subst k
    have hgrid : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)) =
        (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one,
        Finset.Nat.antidiagonalTuple_zero_zero, Finset.sum_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid]
      exact MeasureTheory.integrable_const 1
    · rw [hgrid, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def]
      change ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
      exact (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hmem : k ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hsingle : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤ R ^ 2 :=
      (Finset.single_le_sum
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem).trans hP2
    have htop : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ≤ R := by
      nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k P)]
    have hgrid := rank_two_grid_uniform (E := E) (I := I) (M := M)
      hDim gBase hΛ k hk1 g hEq hjet1 hjet2 P R R hR hR hP2 htop
    simpa only [h2GridC, if_neg hk0] using hgrid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.h2_grid_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.h2_grid_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.h2_grid_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.h2_grid_uniform

noncomputable def h3TopGridC
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) : ℝ :=
  rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 3 R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.h3TopGridC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.h3TopGridC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.h3TopGridC ``Submission.DifferentialGeometry.PDE.RicciFlow.h3TopGridC

theorem h3_top_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R A : ℝ),
        0 ≤ R →
        0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range 4,
              ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∑ n ∈ Finset.range 4,
                ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            h3TopGridC (E := E) (I := I) (M := M) gBase Λ R * A ^ 2 := by
  intro g hEq hjet1 hjet2 P R A hR hA hP2 htop
  simpa only [h3TopGridC, Nat.reduceAdd] using
    (rank_two_grid_uniform (E := E) (I := I) (M := M)
      hDim gBase hΛ 3 (by omega) g hEq hjet1 hjet2 P R A hR hA hP2 htop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.h3_top_grid_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.h3_top_grid_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.h3_top_grid_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.h3_top_grid_uniform

end RicciFlow
end PDE
end DifferentialGeometry
