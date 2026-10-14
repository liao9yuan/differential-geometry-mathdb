import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Finset
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

def chartRiemannLower (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α l m y *
      chartRiemannTensor (I := I) g α i j k m y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartRiemannLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower ``Submission.DifferentialGeometry.Geometry.Riemannian.chartRiemannLower

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRiemannLower_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      ∑ m : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α l m y *
          chartRiemannTensor (I := I) g α i j k m y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_def ``Submission.DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_def

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannLower_antisymm_jk
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      - chartRiemannLower (I := I) g α i k j l y := by
  classical
  rw [chartRiemannLower_def, chartRiemannLower_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [chartRiemannTensor_antisymm_jk]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_antisymm_jk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_antisymm_jk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_antisymm_jk ``Submission.DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_antisymm_jk

def sectionalCurvatureNumerator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) i *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) j *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) k *
                  chartRiemannLower (I := I) g p i j k l (extChartAt I p p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvatureNumerator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) l *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) i *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) j *
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) k *
                      chartRiemannLower (I := I) g p i j k l
                        (extChartAt I p p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_def ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_def

def sectionalCurvatureDenominator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvatureDenominator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def

def sectionalCurvature (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  sectionalCurvatureNumerator (I := I) g p v w /
    sectionalCurvatureDenominator (I := I) g p v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvature_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p v w /
        sectionalCurvatureDenominator (I := I) g p v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chart_metric_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    (g.inner p v w) ^ 2 ≤ g.inner p v v * g.inner p w w := by
  have hq_nonneg : ∀ t : ℝ, 0 ≤ g.inner p (t • v + w) (t • v + w) := by
    intro t
    by_cases htv : t • v + w = 0
    · rw [htv]; simp
    · exact (g.pos p _ htv).le
  have hq_expand : ∀ t : ℝ,
      g.inner p (t • v + w) (t • v + w) =
        t ^ 2 * g.inner p v v + 2 * t * g.inner p v w + g.inner p w w := by
    intro t
    have h_first : g.inner p (t • v + w) =
        t • g.inner p v + g.inner p w := by
      rw [map_add, map_smul]
    rw [h_first, add_apply, smul_apply,
        smul_eq_mul, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, g.symm p w v]
    ring
  have hA_nonneg : 0 ≤ g.inner p v v := by
    by_cases hv : v = 0
    · rw [hv]; simp
    · exact (g.pos p v hv).le
  have hC_nonneg : 0 ≤ g.inner p w w := by
    by_cases hw : w = 0
    · rw [hw]; simp
    · exact (g.pos p w hw).le
  by_cases hA_zero : g.inner p v v = 0
  · have hv_zero : v = 0 := by
      by_contra hv_ne
      exact absurd hA_zero (ne_of_gt (g.pos p v hv_ne))
    have hB_zero : g.inner p v w = 0 := by
      rw [hv_zero]
      simp
    rw [hB_zero, hA_zero]
    simp
  · have hA_pos : 0 < g.inner p v v :=
      lt_of_le_of_ne hA_nonneg (Ne.symm hA_zero)
    have h_at_t := hq_nonneg (-g.inner p v w / g.inner p v v)
    rw [hq_expand] at h_at_t
    have h_simplify :
        (-g.inner p v w / g.inner p v v) ^ 2 * g.inner p v v +
            2 * (-g.inner p v w / g.inner p v v) * g.inner p v w +
            g.inner p w w =
          g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v := by
      field_simp; ring
    rw [h_simplify] at h_at_t
    have h_expand :
        g.inner p v v *
          (g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v) =
          g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := by
      field_simp
    have h_mul := mul_nonneg hA_pos.le h_at_t
    rw [h_expand] at h_mul
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.chart_metric_cauchy_schwarz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.chart_metric_cauchy_schwarz target :: scope.openDecls } }

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_nonneg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    0 ≤ sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def]
  linarith [chart_metric_cauchy_schwarz (I := I) g p v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_pos_of_linearIndependent
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) (hvw : LinearIndependent Real ![v, w]) :
    0 < sectionalCurvatureDenominator (I := I) g p v w := by
  have hw : w ≠ 0 := by simpa using hvw.ne_zero 1
  have ha : 0 < g.inner p w w := g.pos p w hw
  have hne : g.inner p w w • v - g.inner p v w • w ≠ 0 := by
    intro hz
    have hh := LinearIndependent.pair_iff.mp hvw
      (g.inner p w w) (-g.inner p v w)
      (by simpa [sub_eq_add_neg] using hz)
    exact ha.ne' hh.1
  have hp := g.pos p _ hne
  have hexpand :
      g.inner p (g.inner p w w • v - g.inner p v w • w)
          (g.inner p w w • v - g.inner p v w • w) =
        g.inner p w w *
          (g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2) := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      g.symm p w v]
    ring
  rw [hexpand] at hp
  rw [sectionalCurvatureDenominator_def]
  exact (mul_pos_iff_of_pos_left ha).mp hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_eq_zero_of_left_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) v = c * g.inner p v v := by
    rw [h1, smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_left_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_left_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_left_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_left_smul

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_eq_zero_of_right_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hRR : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • v) = c * g.inner p v v := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_right_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_right_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_right_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_eq_zero_of_right_smul

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem linearIndependent_pair_of_sectionalCurvatureDenominator_pos
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p)
    (hpos : 0 < sectionalCurvatureDenominator (I := I) g p v w) :
    LinearIndependent ℝ ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    have hbw : b • w = 0 := by simpa using hab
    by_cases hb : b = 0
    · exact ⟨rfl, hb⟩
    · exfalso
      have hw : w = 0 := (smul_eq_zero.mp hbw).resolve_left hb
      rw [hw, sectionalCurvatureDenominator_def] at hpos
      simp at hpos
  · exfalso
    have h1 : a • v = -(b • w) := eq_neg_of_add_eq_zero_left hab
    have hv : v = (-(b * a⁻¹)) • w := by
      calc v = a⁻¹ • (a • v) := (inv_smul_smul₀ ha v).symm
        _ = a⁻¹ • (-(b • w)) := by rw [h1]
        _ = -(a⁻¹ • (b • w)) := by rw [smul_neg]
        _ = -((b * a⁻¹) • w) := by rw [_root_.SMulCommClass.smul_comm, smul_smul]
        _ = (-(b * a⁻¹)) • w := (neg_smul _ _).symm
    have hz := sectionalCurvatureDenominator_eq_zero_of_left_smul (I := I) g p
      (-(b * a⁻¹)) w
    rw [hv] at hpos
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos ``Submission.DifferentialGeometry.Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (c • v) =
      c • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (c • w) =
      c • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_smul_right

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) w = c * g.inner p v w := by
    rw [h1, smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_left

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • w) = c • g.inner p w := map_smul _ _ _
  have hRR : g.inner p (c • w) (c • w) = c ^ 2 * g.inner p w w := by
    rw [h1, smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • w) = c * g.inner p v w := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_smul_right

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_left,
      sectionalCurvatureDenominator_smul_left,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_right,
      sectionalCurvatureDenominator_smul_right,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_right

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_of_linearly_dependent_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_left_smul]
  exact div_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_of_linearly_dependent_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_right_smul]
  exact div_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_of_linearly_dependent_right

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_self
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v v = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 1 v
  rw [one_smul] at h; exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_self ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_self

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_zero_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (w : TangentSpace I p) :
    sectionalCurvature (I := I) g p 0 w = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 0 w
  rw [zero_smul] at h; exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_zero_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v 0 = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_right (I := I) g p 0 v
  rw [zero_smul] at h; exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_zero_right

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) w =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_left (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-w) =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_right (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_right

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_neg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) (-w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p v (-w),
      sectionalCurvature_neg_right (I := I) g p v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_neg ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_neg

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_smul
    (g : SmoothRiemannianMetric I M) (p : M) {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) (d • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_smul_left (I := I) g p hc v (d • w),
      sectionalCurvature_smul_right (I := I) g p hd v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_smul_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-(c • v)) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p (c • v) w,
      sectionalCurvature_smul_left (I := I) g p hc v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_left ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_left

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-(c • w)) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_right (I := I) g p v (c • w),
      sectionalCurvature_smul_right (I := I) g p hc v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_right ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_neg_smul_right

private lemma fourfold_sum_reverse
    {n : ℕ}
    (α β : Fin n → ℝ) (T : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        α l * β i * α j * β k * T i j k l) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        β l * α i * β j * α k * T l k j i) := by
  classical
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_; intro l _
  refine Finset.sum_congr rfl ?_; intro k _
  refine Finset.sum_congr rfl ?_; intro j _
  refine Finset.sum_congr rfl ?_; intro i _
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.fourfold_sum_reverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.fourfold_sum_reverse target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p w v := by
  classical
  have h_combined : ∀ i j k l : Fin (Module.finrank ℝ E),
      chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
        chartRiemannLower (I := I) g p l k j i (extChartAt I p p) := by
    intro i j k l
    rw [chartRiemannLower_antisymm_jk (I := I) g p i j k l, h_pair i k j l]
    ring
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def]
  refine Eq.trans ?_ (fourfold_sum_reverse (n := Module.finrank ℝ E)
    (α := fun i => ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) i)
    (β := fun i => ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) i)
    (T := fun a b c d =>
      chartRiemannLower (I := I) g p d c b a (extChartAt I p p)))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [h_combined i j k l]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_symm
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      sectionalCurvatureDenominator (I := I) g p w v := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  rw [g.symm p v w]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_symm ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_symm

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvature (I := I) g p w v := by
  rw [sectionalCurvature_def, sectionalCurvature_def]
  rw [sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
        (I := I) g p h_pair v w,
      sectionalCurvatureDenominator_symm (I := I) g p v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm

variable [I.Boundaryless] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_eq_metricRm04StandardAt
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    sectionalCurvatureNumerator (I := I) g x v w =
      Curvature.metricRm04StandardAt (I := I) g x v w w v := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hbas (i : Fin (Module.finrank Real E)) :
      chartBasisVecFiber (I := I) x i x = centeredChartTangentBasis (I := I) x i := by
    change (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL Real x (chartModelBasis E i) =
      (centeredChartTangentEquiv (I := I) x).symm (chartModelBasis E i)
    exact (congrFun ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symm_continuousLinearEquivAt_eq
      (FiberBundle.mem_baseSet_trivializationAt' x)) (chartModelBasis E i)).symm
  have hrepr (z : TangentSpace I x) :
      (centeredChartTangentBasis (I := I) x).repr z = (chartModelBasis E).repr z := by
    rw [centeredChartTangentBasis_repr, centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  have hgram (i j : Fin (Module.finrank Real E)) :
      chartGramOnE (I := I) g x i j (extChartAt I x x) =
        g.inner x (centeredChartTangentBasis (I := I) x i)
          (centeredChartTangentBasis (I := I) x j) := by
    rw [chartGramOnE_def, (extChartAt I x).left_inv (mem_extChartAt_source x),
      chartGramMatrix_apply, hbas, hbas]
  have hinner (j : Fin (Module.finrank Real E)) :
      g.inner x v (centeredChartTangentBasis (I := I) x j) =
      ∑ l : Fin (Module.finrank Real E), (chartModelBasis E).repr v l *
        chartGramOnE (I := I) g x l j (extChartAt I x x) := by
    have hv := (centeredChartTangentBasis (I := I) x).sum_repr v
    have hv' := congrArg (fun z : TangentSpace I x =>
      g.inner x z (centeredChartTangentBasis (I := I) x j)) hv
    simpa only [map_sum, map_smul, _root_.sum_apply, smul_apply, smul_eq_mul, hrepr, hgram]
      using hv'.symm
  rw [metricRm04StandardAt_eq_chartRiemannCLM, Connection.chartRiemannCLM_apply]
  simp only [map_sum, map_smul, smul_eq_mul, hrepr, hinner]
  rw [sectionalCurvatureNumerator_def]
  simp only [chartRiemannLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_eq_metricRm04StandardAt_div
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    sectionalCurvature (I := I) g x v w =
      Curvature.metricRm04StandardAt (I := I) g x v w w v /
        (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) := by
  rw [sectionalCurvature_def, sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    sectionalCurvatureDenominator_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (hzero : Curvature.metricRm04StandardAt (I := I) g x v w w v = 0) :
    sectionalCurvature (I := I) g x v w = 0 := by
  rw [sectionalCurvature_eq_metricRm04StandardAt_div, hzero, zero_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (hzero : Curvature.metricRm04At (I := I) (M := M) g x
      (vec4 (I := I) v w w v) = 0) :
    sectionalCurvature (I := I) g x v w = 0 :=
  sectionalCurvature_eq_zero_of_metricRm04StandardAt_eq_zero (I := I) g x v w
    ((Curvature.metricRm04StandardAt_apply (I := I) (M := M) g x v w w v).trans hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    sectionalCurvature (I := I) g x v w =
      Curvature.metricRm04StandardAt (I := I) g x v w w v := by
  rw [sectionalCurvature_eq_metricRm04StandardAt_div, hv, hw, hvw]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_of_unit_orthogonal

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    sectionalCurvature (I := I) (scaleMetric (I := I) c hc g) x v w =
      c⁻¹ * sectionalCurvature (I := I) g x v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : IsManifold I 1 M := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have hd : sectionalCurvatureDenominator (I := I) (scaleMetric (I := I) c hc g) x v w =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g x v w := by
    simp only [sectionalCurvatureDenominator_def, scaleMetric_inner]
    ring
  rw [sectionalCurvature_def, sectionalCurvature_def,
    sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    sectionalCurvatureNumerator_eq_metricRm04StandardAt, Curvature.metricRmStandard_scale, hd]
  by_cases hden : sectionalCurvatureDenominator (I := I) g x v w = 0
  · simp only [hden, _root_.MulZeroClass.mul_zero, div_zero]
  · field_simp [hc.ne', hden]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_scaleMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_scaleMetric

omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_pullback
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (v w : TangentSpace I x) :
    sectionalCurvature (I := I) (Diffeomorph.pullbackMetric g Φ) x v w =
      sectionalCurvature (I := I) g (Φ x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : IsManifold I 1 M := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let _ : IsManifold I 1 N := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  simp only [sectionalCurvature_def, sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    Curvature.metricRm04Standard_pullback, sectionalCurvatureDenominator_def,
    Diffeomorph.pullbackMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback ``Submission.DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback

end Riemannian
end Geometry
end DifferentialGeometry
