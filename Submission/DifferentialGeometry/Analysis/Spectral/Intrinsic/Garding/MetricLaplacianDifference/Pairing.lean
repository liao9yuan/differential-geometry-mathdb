import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.CrossMetricEnergy
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.Core

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toRS0_sub {x : M} (A B : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 (A - B) =
      Tensor0SSpace.toRS0 A - Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  change (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • (A - B) =
    (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • A -
      (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • B
  exact smul_sub _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.toRS0_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.toRS0_sub target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem normSq0S_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    0 <= normSq0S (I := I) g x s A := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.normSq0S_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.normSq0S_nonneg target :: scope.openDecls } }

theorem lapDiffCore_pair_sq
    (q h k : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) :
    ‖lapDiffCore (I := I) (M := M) q h v -
        lapDiffCore (I := I) (M := M) q k v‖ ^ 2 =
      ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
            ΔG (I := I) k ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  change ‖SmoothCcTensor.toL2
      (lapDiffSec (I := I) (M := M) q h v) -
        SmoothCcTensor.toL2
          (lapDiffSec (I := I) (M := M) q k v)‖ ^ 2 = _
  rw [← map_sub]
  rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun (I := I) (M := M) q 0 0
      (lapDiffSec (I := I) (M := M) q h v -
        lapDiffSec (I := I) (M := M) q k v)]
  unfold tensorL2Inner
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [lapDiffSec_apply (I := I) (M := M) q h v x,
    lapDiffSec_apply (I := I) (M := M) q k v x]
  rw [← toRS0_sub]
  rw [← map_sub]
  rw [inner_toRS0_scalar (I := I) (M := M) q x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair_sq ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair_sq

theorem lapDiff_pair_energy
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : TensorHs (I := I) (M := M) q 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x -
                ΔG (I := I) k ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) q) <=
            C *
              (CheegerGromovCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k) ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨CX, hCX, hcross⟩ := cross_energy_le (I := I) (M := M) q k
  let n : Real := Module.finrank Real E
  let Kc : Real := 8 * n ^ 2 + 72 * n
  let C : Real := Kc * CX
  have hKc : 0 <= Kc := by
    dsimp only [Kc, n]
    positivity
  refine ⟨C, mul_nonneg hKc hCX, ?_⟩
  intro h v hv hsmall
  let f : M → Real := reprScalar0 (I := I) (M := M) v hv
  let hf : ContMDiff I 𝓘(Real, Real) ∞ f :=
    reprScalar0_smooth (I := I) (M := M) v hv
  let rho : Real :=
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  let A : Real := 8 * n ^ 2 * rho ^ 2
  let B : Real := 72 * n * rho ^ 2
  let P : Real := A + B
  let HessNorm : M → Real := fun x =>
    normSq0S (I := I) k x 2 (leviHessSec (I := I) k f hf x)
  let duNorm : M → Real := fun x =>
    normSq0S (I := I) k x 1 (duSec (I := I) f hf x)
  let lhs : M → Real := fun x =>
    (ΔG (I := I) h ⟨_, hf⟩ x - ΔG (I := I) k ⟨_, hf⟩ x) ^ 2
  let energy : M → Real := fun x => HessNorm x + duNorm x
  have hHessEq : HessNorm = fun x =>
      chartHessFrobeniusSq (I := I) k f x := by
    funext x
    exact hessSec_normSq (I := I) k hf x
  have hduEq : duNorm = fun x => normGradSqFun (I := I) k f x := by
    funext x
    simp only [duNorm, duSec_apply, normSq0S_eq_inner,
      inner0S_differential1FormFun_pair_eq_grad_inner, normGradSqFun_def]
    rfl
  have hHessCont : Continuous HessNorm := by
    rw [hHessEq]
    exact chartHessFrobeniusSq_continuous (I := I) k hf
  have hduCont : Continuous duNorm := by
    rw [hduEq]
    exact normGradSqFun_continuous (I := I) k hf
  have hlhsCont : Continuous lhs := by
    exact (((Δ_g_contMDiff (I := I) h ⟨_, hf⟩).continuous.sub
      (Δ_g_contMDiff (I := I) k ⟨_, hf⟩).continuous).pow 2)
  have henergyCont : Continuous energy := hHessCont.add hduCont
  have hlhsInt : _root_.MeasureTheory.Integrable lhs
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hlhsCont
  have henergyInt : _root_.MeasureTheory.Integrable energy
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q henergyCont
  have hA0 : 0 <= A := by
    dsimp only [A, n, rho]
    positivity
  have hB0 : 0 <= B := by
    dsimp only [B, n, rho]
    positivity
  have hP0 : 0 <= P := add_nonneg hA0 hB0
  have hpoint : ∀ x : M, lhs x <= P * energy x := by
    intro x
    have hbase := CheegerGromovCompactness.lapDiff_sq_le
      (I := I) k h hf x hsmall
    have hH0 : 0 <= HessNorm x := by
      exact normSq0S_nonneg (I := I) k x 2 _
    have hD0 : 0 <= duNorm x := by
      exact normSq0S_nonneg (I := I) k x 1 _
    have hAP : A <= P := by
      dsimp only [P]
      exact le_add_of_nonneg_right hB0
    have hBP : B <= P := by
      dsimp only [P]
      exact le_add_of_nonneg_left hA0
    calc
      lhs x <= A * HessNorm x + B * duNorm x := by
        simpa only [lhs, A, B, n, rho, HessNorm, duNorm, f, hf] using hbase
      _ <= P * HessNorm x + P * duNorm x :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP hH0)
          (mul_le_mul_of_nonneg_right hBP hD0)
      _ = P * energy x := by
        simp only [energy]
        ring
  have hint :
      (∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        ∫ x, P * energy x
          ∂(riemannianVolumeMeasure (I := I) (M := M) q) :=
    _root_.MeasureTheory.integral_mono_ae hlhsInt (henergyInt.const_mul P)
      (Filter.Eventually.of_forall hpoint)
  have henergy :
      (∫ x, energy x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        CX * ‖v‖ ^ 2 := by
    simpa only [energy, HessNorm, duNorm, f, hf] using hcross v hv
  calc
    (∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x -
          ΔG (I := I) k ⟨_, (reprScalar0_smooth (I := I) (M := M) v hv)⟩ x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) =
        ∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
      rfl
    _ <= ∫ x, P * energy x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := hint
    _ = P * (∫ x, energy x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) := by
      rw [_root_.MeasureTheory.integral_const_mul]
    _ <= P * (CX * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy hP0
    _ = C * rho ^ 2 * ‖v‖ ^ 2 := by
      simp only [P, A, B, C, Kc]
      ring
    _ = C *
        (CheegerGromovCompactness.metricDerivNormSupOn
          (I := I) Set.univ 1 h k k) ^ 2 * ‖v‖ ^ 2 := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiff_pair_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiff_pair_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiff_pair_energy ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_pair_energy

theorem exists_lapDiffCore_norm_sub_le
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : ScalarH2Core (I := I) (M := M) q),
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ‖lapDiffCore (I := I) (M := M) q h v -
              lapDiffCore (I := I) (M := M) q k v‖ <=
            Real.sqrt C *
              |CheegerGromovCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k| * ‖v‖ := by
  obtain ⟨C, hC, henergy⟩ := lapDiff_pair_energy (I := I) (M := M) q k
  refine ⟨C, hC, ?_⟩
  intro h v hsmall
  let rho : Real :=
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  have hsq :
      ‖lapDiffCore (I := I) (M := M) q h v -
          lapDiffCore (I := I) (M := M) q k v‖ ^ 2 <=
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [lapDiffCore_pair_sq (I := I) (M := M) q h k v]
    simpa only [rho, Submodule.norm_coe] using henergy h v.1 v.2 hsmall
  have hrhs :
      (Real.sqrt C * |rho| * ‖v‖) ^ 2 =
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC, sq_abs]
  have hrhs0 : 0 <= Real.sqrt C * |rho| * ‖v‖ := by positivity
  rw [← hrhs] at hsq
  nlinarith [norm_nonneg
    (lapDiffCore (I := I) (M := M) q h v -
      lapDiffCore (I := I) (M := M) q k v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_lapDiffCore_norm_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_lapDiffCore_norm_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_lapDiffCore_norm_sub_le ``Submission.DifferentialGeometry.Analysis.Spectral.exists_lapDiffCore_norm_sub_le

theorem lapDiff_pair_norm
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M),
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h q q <= (1 / 2 : Real) →
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 k q q <= (1 / 2 : Real) →
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ‖lapDiffOp (I := I) (M := M) q h -
              lapDiffOp (I := I) (M := M) q k‖ <=
            Real.sqrt C *
              |CheegerGromovCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k| := by
  obtain ⟨C, hC, hcore⟩ := exists_lapDiffCore_norm_sub_le (I := I) (M := M) q k
  refine ⟨C, hC, ?_⟩
  intro h hqh hqk hkh
  let rho : Real :=
    CheegerGromovCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  let B : Real := Real.sqrt C * |rho|
  have hB : 0 <= B := by positivity
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply (lapDiffOp (I := I) (M := M) q h -
    lapDiffOp (I := I) (M := M) q k).opNorm_le_bound hB
  intro u
  refine hdense.induction_on u ?_ ?_
  · exact isClosed_le
      (lapDiffOp (I := I) (M := M) q h -
        lapDiffOp (I := I) (M := M) q k).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro v
    rw [sub_apply]
    simp only [Submodule.coe_subtype]
    rw [lapDiffOp_apply_scalarH2Core (I := I) (M := M) q h v hqh,
      lapDiffOp_apply_scalarH2Core (I := I) (M := M) q k v hqk]
    simpa only [B, rho, Submodule.norm_coe] using hcore h v hkh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiff_pair_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiff_pair_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiff_pair_norm ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_pair_norm

end Spectral
end Analysis
end DifferentialGeometry

end
