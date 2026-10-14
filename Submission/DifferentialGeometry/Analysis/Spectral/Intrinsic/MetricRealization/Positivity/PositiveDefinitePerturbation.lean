import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricCauchySchwarzBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (δ : ℝ) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    |h x v w| ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound

omit [Module.Finite ℝ E] in
theorem metricCauchySchwarzBound_mono
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ') (hb : metricCauchySchwarzBound g h δ) :
    metricCauchySchwarzBound g h δ' := by
  intro x v w
  refine (hb x v w).trans ?_
  have hnonneg : 0 ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)
      = δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by ring
    _ ≤ δ' * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
      mul_le_mul_of_nonneg_right hle hnonneg
    _ = δ' * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_mono ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_mono

omit [Module.Finite ℝ E] in
theorem metricCauchySchwarzBound_min
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (hδ' : metricCauchySchwarzBound g h δ') :
    metricCauchySchwarzBound g h (_root_.Min.min δ δ') := by
  rcases le_total δ δ' with hle | hle
  · simpa [min_eq_left hle] using hδ
  · simpa [min_eq_right hle] using hδ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_min ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.metricCauchySchwarzBound_min

abbrev gFibreOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (δ : ℝ) : Prop :=
  metricCauchySchwarzBound g h δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gFibreOpBound

noncomputable def perturbedInner
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  g.inner x + h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner

omit [Module.Finite ℝ E] in
@[simp] lemma perturbedInner_apply
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (v w : TangentSpace I x) :
    perturbedInner g h x v w = g.inner x v w + h x v w := by
  simp only [perturbedInner, add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_apply ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_apply

omit [Module.Finite ℝ E] in
theorem perturbedInner_symm
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (x : M) (v w : TangentSpace I x) :
    perturbedInner g h x v w = perturbedInner g h x w v := by
  rw [perturbedInner_apply, perturbedInner_apply, g.symm x v w, hsymm x v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_symm ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_symm

omit [Module.Finite ℝ E] in
private lemma abs_h_diag_le
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    |h x v v| ≤ δ * g.inner x v v := by
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hbound := hδ x v v
  have hsq : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) = g.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  calc |h x v v|
      ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) := hbound
    _ = δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v)) := by ring
    _ = δ * g.inner x v v := by rw [hsq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.abs_h_diag_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.abs_h_diag_le target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
theorem perturbedInner_self_lower_bound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ perturbedInner g h x v v := by
  have hdiag := abs_h_diag_le (I := I) (M := M) g h hδ x v
  have hge : -(δ * g.inner x v v) ≤ h x v v :=
    neg_le_of_abs_le hdiag
  rw [perturbedInner_apply]
  nlinarith [hge]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_lower_bound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_lower_bound

omit [Module.Finite ℝ E] in
theorem perturbedInner_pos_of_metricCauchySchwarzBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < perturbedInner g h x v v := by
  have hg_pos : 0 < g.inner x v v := g.pos x v hv
  have hcoeff : 0 < 1 - δ := by linarith
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g h hδ x v
  have : 0 < (1 - δ) * g.inner x v v := mul_pos hcoeff hg_pos
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_metricCauchySchwarzBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_metricCauchySchwarzBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_metricCauchySchwarzBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_metricCauchySchwarzBound

omit [Module.Finite ℝ E] in
theorem perturbedInner_pos_of_gOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : gFibreOpBound g h δ)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < perturbedInner g h x v v :=
  perturbedInner_pos_of_metricCauchySchwarzBound g h hδ_lt hδ x v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_gOpBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_gOpBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_gOpBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_pos_of_gOpBound

omit [Module.Finite ℝ E] in
private lemma gSublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : 0 < r) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | g.inner x v v < r} := by
  set sr := Real.sqrt r with hsr_def
  have hsr_pos : 0 < sr := Real.sqrt_pos.mpr hr
  have hsr_sq : sr * sr = r := by
    rw [hsr_def, ← Real.sqrt_mul hr.le, Real.sqrt_mul_self hr.le]
  set L : TangentSpace I x →L[ℝ] TangentSpace I x :=
    sr • ContinuousLinearMap.id ℝ (TangentSpace I x) with hL_def
  have hL_apply : ∀ w : TangentSpace I x, L w = sr • w := by
    intro w; rw [hL_def]; simp
  have hg_unit : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | g.inner x v v < 1} := g.isVonNBounded x
  have himg := hg_unit.image L
  have hset_eq :
      {v : TangentSpace I x | g.inner x v v < r}
        = (L : TangentSpace I x → TangentSpace I x) ''
            {w : TangentSpace I x | g.inner x w w < 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hv
      refine ⟨sr⁻¹ • v, ?_, ?_⟩
      · have hscale : g.inner x (sr⁻¹ • v) (sr⁻¹ • v)
            = sr⁻¹ * (sr⁻¹ * g.inner x v v) := by
          simp only [map_smul, smul_apply, smul_eq_mul]
        rw [hscale]
        have hsr_ne : sr ≠ 0 := ne_of_gt hsr_pos
        have : sr⁻¹ * (sr⁻¹ * g.inner x v v) = g.inner x v v / r := by
          field_simp
          rw [← hsr_sq]; ring
        rw [this, div_lt_one hr]; exact hv
      · rw [hL_apply]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hsr_pos), one_smul]
    · rintro ⟨w, hw, rfl⟩
      rw [hL_apply]
      have hscale : g.inner x (sr • w) (sr • w) = sr * (sr * g.inner x w w) := by
        simp only [map_smul, smul_apply, smul_eq_mul]
      rw [hscale]
      have hrw : sr * (sr * g.inner x w w) = r * g.inner x w w := by
        rw [← mul_assoc, hsr_sq]
      rw [hrw]
      calc r * g.inner x w w < r * 1 := by
              apply mul_lt_mul_of_pos_left hw hr
        _ = r := mul_one r
  rw [hset_eq]
  exact himg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gSublevel_isVonNBounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.gSublevel_isVonNBounded target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
theorem perturbedInner_isVonNBounded
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ)
    (x : M) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | perturbedInner g h x v v < 1} := by
  have hcoeff : 0 < 1 - δ := by linarith
  set r := (1 - δ)⁻¹ with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; exact inv_pos.mpr hcoeff
  have hsub : {v : TangentSpace I x | perturbedInner g h x v v < 1}
      ⊆ {v : TangentSpace I x | g.inner x v v < r} := by
    intro v hv
    rw [Set.mem_ofPred_eq] at hv ⊢
    have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g h hδ x v
    have h1 : (1 - δ) * g.inner x v v < 1 := lt_of_le_of_lt hlb hv
    rw [hr_def, ← one_div]
    rw [lt_div_iff₀ hcoeff, mul_comm]
    exact h1
  exact (gSublevel_isVonNBounded (I := I) (M := M) g x hr_pos).subset hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_isVonNBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_isVonNBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_isVonNBounded ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_isVonNBounded

theorem perturbedInner_contMDiff
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (perturbedInner g h x)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => perturbedInner g h x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => perturbedInner g h x (Y x))
  intro W
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) := Y.contMDiff
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (W x)) := W.contMDiff
  have hg_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (g.inner x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => g.inner x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        g.contMDiff hY hW
    intro x
    have h_at := h_total x
    rw [_root_.Bundle.contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have hh_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => h x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (h x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => h x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        hsmooth hY hW
    intro x
    have h_at := h_total x
    rw [_root_.Bundle.contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have h_sum_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => perturbedInner g h x (Y x) (W x)) := by
    have h_eq : (fun x : M => perturbedInner g h x (Y x) (W x))
        = fun x : M => g.inner x (Y x) (W x) + h x (Y x) (W x) := by
      funext x; rw [perturbedInner_apply]
    rw [h_eq]; exact hg_scalar.add hh_scalar
  intro x
  rw [_root_.Bundle.contMDiffAt_section]
  refine (h_sum_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change perturbedInner g h y (Y y) (W y) =
    (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, perturbedInner g h y (Y y) (W y)⟩).2
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_contMDiff

noncomputable def perturbedMetric
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ) :
    SmoothRiemannianMetric I M where
  inner x := perturbedInner g h x
  symm x v w := perturbedInner_symm (I := I) (M := M) g h hsymm x v w
  pos x v hv := perturbedInner_pos_of_metricCauchySchwarzBound (I := I) (M := M) g h hδ_lt hδ x v hv
  isVonNBounded x := perturbedInner_isVonNBounded (I := I) (M := M) g h hδ_lt hδ x
  contMDiff := perturbedInner_contMDiff (I := I) (M := M) g h hsmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric

@[simp] lemma perturbedMetric_inner
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ) (x : M) :
    (perturbedMetric g h hsymm hsmooth hδ_lt hδ).inner x = perturbedInner g h x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric_inner ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedMetric_inner

theorem exists_posDef_perturbation_radius
    [T2Space M] (g : SmoothRiemannianMetric I M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ),
        (∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v) →
        (ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b : M => TotalSpace.mk'
            (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            b (h b))) →
        ∀ δ' : ℝ, δ' < δ → metricCauchySchwarzBound g h δ' →
          ∃ g' : SmoothRiemannianMetric I M,
            ∀ (x : M) (v w : TangentSpace I x),
              g'.inner x v w = g.inner x v w + h x v w := by
  refine ⟨1, one_pos, ?_⟩
  intro h hsymm hsmooth δ' hδ'_lt hδ'
  refine ⟨perturbedMetric g h hsymm hsmooth hδ'_lt hδ', ?_⟩
  intro x v w
  rw [perturbedMetric_inner, perturbedInner_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_posDef_perturbation_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_posDef_perturbation_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_posDef_perturbation_radius ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.exists_posDef_perturbation_radius

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
