import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletH1Compl
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Boundary
import Submission.DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.I_half target :: scope.openDecls } }

variable [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem denseRange_smoothToLpDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToLpDirichlet g) := by
  classical
  let μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I_half n) (M := M) g
  have : _root_.MeasureTheory.IsFiniteMeasure μ := by
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) g
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts μ := by
    exact riemannianVolumeMeasure_isFiniteMeasureOnCompacts
      (I := I_half n) (M := M) g
  have : _root_.MeasureTheory.IsLocallyFiniteMeasure μ := by
    exact riemannianVolumeMeasure_isLocallyFiniteMeasure
      (I := I_half n) (M := M) g
  have : μ.Regular := by
    exact riemannianVolumeMeasure_regular (I := I_half n) (M := M) g
  change Dense (Set.range (smoothToLpDirichlet g))
  rw [Metric.dense_iff]
  intro u r hr
  have hr2 : 0 < r / 2 := by linarith
  obtain ⟨f, hf_compact, huf⟩ :=
    DifferentialGeometry.Integral.L2.compactlySupportedSmoothFunctions_denseRange_in_Lp
      (I := I_half n) (M := M) g (p := 2) (by norm_num) (by norm_num) u hr2
  let fLp : _root_.MeasureTheory.Lp ℝ 2 μ :=
    (DifferentialGeometry.Integral.L2.compactlySupportedSmoothFunctions_memLp
      (I := I_half n) (M := M) (p := 2) g hf_compact).toLp (f : M → ℝ)
  obtain ⟨C, hC⟩ := f.contMDiff.continuous.bounded_above_of_compact_support hf_compact
  let B : ℝ := _root_.Max.max C 0 + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right C 0]
  have hf_bound : ∀ x : M, ‖(f : M → ℝ) x‖ ≤ B := by
    intro x
    exact (hC x).trans (by
      dsimp [B]
      linarith [le_max_left C 0])
  let δ : ℝ := r / (2 * B)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let q : ℝ≥0∞ := ENNReal.ofReal δ
  have hq_ne : q ≠ 0 := by
    dsimp [q]
    exact (ENNReal.ofReal_pos.mpr hδ_pos).ne'
  have hq_sq_ne : q ^ (2 : ℝ) ≠ 0 := by
    simp [hq_ne]
  have hinter_meas : MeasurableSet ((I_half n).interior M) :=
    ((I_half n).isOpen_interior (n := ∞) (by simp)).measurableSet
  obtain ⟨K, hK_int, hK_compact, hμ_small⟩ :=
    hinter_meas.exists_isCompact_sdiff_lt
      (_root_.MeasureTheory.measure_ne_top μ ((I_half n).interior M)) hq_sq_ne
  obtain ⟨χ, hχ_smooth, -, hχ_one, hχ_support, hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I_half n) (M := M) hK_compact
      ((I_half n).isOpen_interior (n := ∞) (by simp)) hK_int
  let v : SmoothScalarDirichlet g :=
    { toFun := fun x => χ x * (f : M → ℝ) x
      smooth := hχ_smooth.mul f.contMDiff
      interior_support :=
        (tsupport_mul_subset_left (f := χ) (g := (f : M → ℝ))).trans hχ_support }
  have hv_memLp : _root_.MeasureTheory.MemLp v.toFun 2 μ := by
    exact v.memLp_two
  have hf_memLp : _root_.MeasureTheory.MemLp (f : M → ℝ) 2 μ := by
    exact DifferentialGeometry.Integral.L2.compactlySupportedSmoothFunctions_memLp
      (I := I_half n) (M := M) (p := 2) g hf_compact
  let S : Set M := (I_half n).interior M \ K
  have hS_meas : MeasurableSet S :=
    hinter_meas.diff hK_compact.isClosed.measurableSet
  have hboundary_zero : μ ((I_half n).boundary M) = 0 := by
    exact riemannianVolumeMeasure_boundary_eq_zero (I := I_half n) g
  have hae_interior : ∀ᵐ x ∂μ, x ∈ (I_half n).interior M := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hboundary_zero] with x hx
    rw [← (I_half n).compl_boundary]
    exact hx
  have hpoint : ∀ᵐ x ∂μ,
      ‖(f : M → ℝ) x - v.toFun x‖ ≤ ‖S.indicator (fun _ : M => B) x‖ := by
    filter_upwards [hae_interior] with x hx_int
    by_cases hxK : x ∈ K
    · have hχx : χ x = 1 := by
        simpa only [Pi.one_apply] using hχ_one.self_of_nhdsSet hxK
      have hxS : x ∉ S := fun hx => hx.2 hxK
      simp [v, hχx, Set.indicator_of_notMem hxS]
    · have hxS : x ∈ S := ⟨hx_int, hxK⟩
      have hχx := hχ_range ⟨x, rfl⟩
      have hcoef_nonneg : 0 ≤ 1 - χ x := sub_nonneg.mpr hχx.2
      have hcoef_le : 1 - χ x ≤ 1 := by linarith [hχx.1]
      have hcoef_abs : |1 - χ x| ≤ 1 := by
        rw [abs_of_nonneg hcoef_nonneg]
        exact hcoef_le
      rw [Set.indicator_of_mem hxS]
      change |(f : M → ℝ) x - χ x * (f : M → ℝ) x| ≤ |B|
      rw [abs_of_pos hB_pos]
      calc
        |(f : M → ℝ) x - χ x * (f : M → ℝ) x| =
            |1 - χ x| * |(f : M → ℝ) x| := by rw [← abs_mul]; congr 1; ring
        _ ≤ 1 * B := mul_le_mul hcoef_abs (by simpa [Real.norm_eq_abs] using hf_bound x)
          (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have heLp_bound :
      _root_.MeasureTheory.eLpNorm ((f : M → ℝ) - v.toFun) 2 μ ≤
        ‖(B : ℝ)‖ₑ * μ S ^ (1 / (2 : ℝ≥0∞).toReal) := by
    calc
      _root_.MeasureTheory.eLpNorm ((f : M → ℝ) - v.toFun) 2 μ ≤
          eLpNorm (S.indicator (fun _ : M => B)) 2 μ :=
        _root_.MeasureTheory.eLpNorm_mono_ae hpoint
      _ = ‖(B : ℝ)‖ₑ * μ S ^ (1 / (2 : ℝ≥0∞).toReal) :=
        _root_.MeasureTheory.eLpNorm_indicator_const hS_meas (by norm_num) (by norm_num)
  have hroot : μ S ^ (1 / (2 : ℝ≥0∞).toReal) < q := by
    change μ S ^ (1 / 2 : ℝ) < q
    calc
      μ S ^ (1 / 2 : ℝ) < (q ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_lt_rpow hμ_small (by norm_num)
      _ = q := by
        rw [← ENNReal.rpow_mul]
        norm_num
  have hB_enorm_ne_zero : ‖(B : ℝ)‖ₑ ≠ 0 := by
    simpa using hB_pos.ne'
  have hB_enorm_ne_top : ‖(B : ℝ)‖ₑ ≠ ⊤ := by finiteness
  have htarget : ‖(B : ℝ)‖ₑ * q = ENNReal.ofReal (r / 2) := by
    rw [Real.enorm_eq_ofReal hB_pos.le]
    dsimp [q]
    rw [← ENNReal.ofReal_mul hB_pos.le]
    congr 1
    dsimp [δ]
    field_simp
  have heLp_lt : _root_.MeasureTheory.eLpNorm ((f : M → ℝ) - v.toFun) 2 μ < ENNReal.ofReal (r / 2) :=
    heLp_bound.trans_lt
      ((ENNReal.mul_lt_mul_right hB_enorm_ne_zero hB_enorm_ne_top hroot).trans_eq htarget)
  have hfv : _root_.Dist.dist fLp (smoothToLpDirichlet g v) < r / 2 := by
    change _root_.Dist.dist (hf_memLp.toLp (f : M → ℝ)) (hv_memLp.toLp v.toFun) < r / 2
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    have hreal := (ENNReal.toReal_lt_toReal (hf_memLp.sub hv_memLp).2.ne
      ENNReal.ofReal_ne_top).mpr heLp_lt
    rwa [ENNReal.toReal_ofReal hr2.le] at hreal
  refine ⟨smoothToLpDirichlet g v, ?_, ⟨v, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm]
  have huf_dist : _root_.Dist.dist u fLp < r / 2 := by
    rw [dist_eq_norm]
    exact huf
  calc
    _root_.Dist.dist u (smoothToLpDirichlet g v) ≤
        dist u fLp + _root_.Dist.dist fLp (smoothToLpDirichlet g v) := dist_triangle _ _ _
    _ < r / 2 + r / 2 := add_lt_add huf_dist hfv
    _ = r := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToLpDirichlet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToLpDirichlet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToLpDirichlet ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_smoothToLpDirichlet

theorem denseRange_H1ComplDirichletToLp
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (H1ComplDirichletToLp g) := by
  apply DenseRange.of_comp (g := smoothToH1ComplDirichlet g)
  convert denseRange_smoothToLpDirichlet g using 1
  funext f
  exact H1ComplDirichletToLp_smoothToH1ComplDirichlet g f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_H1ComplDirichletToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_H1ComplDirichletToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_H1ComplDirichletToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.denseRange_H1ComplDirichletToLp

theorem resolventDirichlet_injective
    (g : SmoothRiemannianMetric (I_half n) M) :
    Function.Injective (resolventDirichlet g) := by
  intro f h hfh
  apply sub_eq_zero.mp
  apply (denseRange_H1ComplDirichletToLp g).eq_zero_of_inner_right (𝕜 := ℝ)
  intro v
  have hvar := resolventDirichlet_inner_eq_lpFunctional g (f - h) v
  rw [(resolventDirichlet g).map_sub, hfh, sub_self, inner_zero_left] at hvar
  exact hvar.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.resolventDirichlet_injective

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry
