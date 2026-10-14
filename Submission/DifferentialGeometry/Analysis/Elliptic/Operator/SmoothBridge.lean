import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.DirichletForm
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.Variational

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Matrix _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def SmoothScalar.oneSubLapClassical {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) : SmoothScalar g where
  toFun := u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩
  smooth := u.smooth.sub (Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical

omit [CompactSpace M] in
noncomputable def SmoothScalar.laplacian {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) : SmoothScalar g where
  toFun := ΔG (I := I) g ⟨u.toFun, u.smooth⟩
  smooth := Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.oneSubLapClassical_toFun
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    (u.oneSubLapClassical).toFun =
      u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.oneSubLapClassical_toFun

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.laplacian_toFun
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    u.laplacian.toFun = ΔG (I := I) g ⟨u.toFun, u.smooth⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.laplacian_toFun

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.sub_oneSubLapClassical
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    u - u.oneSubLapClassical = u.laplacian := by
  apply SmoothScalar.ext
  funext x
  simp [SmoothScalar.oneSubLapClassical_toFun]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.sub_oneSubLapClassical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.sub_oneSubLapClassical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.sub_oneSubLapClassical ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.sub_oneSubLapClassical

theorem smoothScalarH1Inner_eq_integral_oneSubLap_mul
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ∫ x, (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold smoothScalarH1Inner
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hv_cs : HasCompactSupport v.toFun := HasCompactSupport.of_compactSpace _
  have hu_cs : HasCompactSupport u.toFun := HasCompactSupport.of_compactSpace _
  have hgreen :
      ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g v.smooth u.smooth
      hu_cs
  have hsymm :
      (∫ x, g.inner x ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _
  rw [hsymm, hgreen]
  have hΔu_cont : Continuous (ΔG (I := I) g ⟨u.toFun, u.smooth⟩) :=
    (Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩).continuous
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv : _root_.MeasureTheory.Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu : _root_.MeasureTheory.Integrable (fun x : M => v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : M,
      (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x =
        u.toFun x * v.toFun x - v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x := by
    intro x; ring
  rw [show (fun x : M =>
      (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x) =
      (fun x : M =>
        u.toFun x * v.toFun x - v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) from
      funext hpt]
  rw [_root_.MeasureTheory.integral_sub h_uv h_vΔu]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_integral_oneSubLap_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_integral_oneSubLap_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_integral_oneSubLap_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_integral_oneSubLap_mul

theorem smoothScalarH1Inner_eq_lpInner_oneSubLap
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ⟪smoothToLp (I := I) (M := M) g u.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g v⟫_ℝ := by
  rw [smoothScalarH1Inner_eq_integral_oneSubLap_mul]
  rw [L2.inner_def
    (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
    (smoothToLp (I := I) (M := M) g v)]
  have hae_lhs : (smoothToLp (I := I) (M := M) g u.oneSubLapClassical :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      u.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp u.oneSubLapClassical.memLp_two
  have hae_rhs : (smoothToLp (I := I) (M := M) g v :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  rw [SmoothScalar.oneSubLapClassical_toFun]
  change (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x =
    @_root_.Inner.inner ℝ _ _ ((u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩) x) (v.toFun x)
  rw [Pi.sub_apply]
  rw [show @_root_.Inner.inner ℝ _ _ (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) (v.toFun x) =
      v.toFun x * (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) from
      RCLike.inner_apply _ _]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_lpInner_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_lpInner_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_lpInner_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_eq_lpInner_oneSubLap

lemma inner_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl (I := I) (M := M) g v⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  unfold smoothToH1Compl
  change ⟪((u : H1Compl g) : H1Compl g),
        ((v : H1Compl g) : H1Compl g)⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.inner_smoothToH1Compl_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.inner_smoothToH1Compl_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.inner_smoothToH1Compl_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.inner_smoothToH1Compl_smoothToH1Compl

lemma H1ComplBilin_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  rw [H1ComplBilin_apply]
  exact inner_smoothToH1Compl_smoothToH1Compl u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_smoothToH1Compl_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_smoothToH1Compl_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_smoothToH1Compl_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_smoothToH1Compl_smoothToH1Compl

theorem smoothScalar_bilin_eq_lpFunctional_smooth
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
        (smoothToH1Compl (I := I) (M := M) g v) := by
  rw [H1ComplBilin_smoothToH1Compl_smoothToH1Compl,
    smoothScalarH1Inner_eq_lpInner_oneSubLap]
  rw [lpFunctionalCLM_apply, H1ComplToLp_smoothToH1Compl]
  exact real_inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalar_bilin_eq_lpFunctional_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalar_bilin_eq_lpFunctional_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalar_bilin_eq_lpFunctional_smooth ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalar_bilin_eq_lpFunctional_smooth

theorem denseRange_smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToH1Compl

theorem smoothToH1Compl_bilin_eq_lpFunctional
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) (w : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u) w =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w := by
  let L : H1Compl g → ℝ := fun w =>
    H1ComplBilin (I := I) (M := M) g (smoothToH1Compl (I := I) (M := M) g u) w
  let R : H1Compl g → ℝ := fun w =>
    lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w
  change L w = R w
  have hL_cont : Continuous L :=
    (H1ComplBilin (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)).continuous
  have hLR_smooth :
      L ∘ (smoothToH1Compl (I := I) (M := M) g) =
        R ∘ (smoothToH1Compl (I := I) (M := M) g) := by
    funext v
    exact smoothScalar_bilin_eq_lpFunctional_smooth u v
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_bilin_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_bilin_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_bilin_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_bilin_eq_lpFunctional

theorem smoothToH1Compl_eq_resolvent_oneSubLap
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToH1Compl (I := I) (M := M) g u, w⟫_ℝ =
        H1ComplBilin (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g u) w from rfl]
  rw [smoothToH1Compl_bilin_eq_lpFunctional u w]
  rw [resolvent_inner_eq_lpFunctional]
  rw [lpFunctionalCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap

theorem smoothToH1Compl_eq_resolvent_oneSubLap_of_function
    (g : SmoothRiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    smoothToH1Compl (I := I) (M := M) g
        ⟨u, hu⟩ =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (⟨u, hu⟩ : SmoothScalar g).oneSubLapClassical) :=
  smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) ⟨u, hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap_of_function then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap_of_function"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap_of_function ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToH1Compl_eq_resolvent_oneSubLap_of_function

theorem resolvent_smoothToLp_oneSubLapClassical
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) =
      smoothToH1Compl (I := I) (M := M) g u :=
  (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent_smoothToLp_oneSubLapClassical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent_smoothToLp_oneSubLapClassical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent_smoothToLp_oneSubLapClassical ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent_smoothToLp_oneSubLapClassical

end Laplacian
end Analysis
end DifferentialGeometry

end
