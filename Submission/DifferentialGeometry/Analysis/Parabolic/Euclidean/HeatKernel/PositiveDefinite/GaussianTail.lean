import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open _root_.Filter _root_.Matrix _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.RealInnerProductSpace _root_.Topology

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

private abbrev Eucl := EuclideanSpace Real n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.Eucl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.Eucl target :: scope.openDecls } }

private def standardGauss (y : Eucl (n := n)) : Real :=
  ((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
    Real.exp (-‖y‖ ^ 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss target :: scope.openDecls } }

omit [DecidableEq n] in
private theorem standardGauss_int :
    Integrable (standardGauss (n := n)) := by
  change _root_.MeasureTheory.Integrable (fun y : Eucl (n := n) ↦
    ((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
      Real.exp (-‖y‖ ^ 2))
  simpa only [neg_one_mul] using
    (gauss_integrable (V := Eucl (n := n)) (a := 1) zero_lt_one).const_mul
      (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss_int
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss_int target :: scope.openDecls } }

omit [DecidableEq n] in
private theorem standardGauss_tail :
    _root_.Filter.Tendsto
      (fun R : Real ↦
        ∫⁻ y : Eucl (n := n) in {y | R < ‖y‖},
          ENNReal.ofReal (standardGauss y) ∂volume)
      atTop (nhds 0) := by
  let s : Real → Set (Eucl (n := n)) := fun R ↦ {y | R < ‖y‖}
  let ν : _root_.MeasureTheory.Measure (Eucl (n := n)) :=
    volume.withDensity (fun y ↦ ENNReal.ofReal (standardGauss y))
  have hs : ∀ R, MeasurableSet (s R) := by
    intro R
    exact measurableSet_lt measurable_const continuous_norm.measurable
  have hanti : Antitone s := by
    intro R R' hRR' y hy
    exact lt_of_le_of_lt hRR' hy
  have hinter : ⋂ R, s R = ∅ := by
    apply le_antisymm
    · intro y hy
      exact False.elim ((lt_irrefl ‖y‖) (mem_iInter.mp hy ‖y‖))
    · exact _root_.Set.empty_subset _
  have hstd_nonneg : ∀ y : Eucl (n := n), 0 ≤ standardGauss y := by
    intro y
    exact mul_nonneg
      (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
      (Real.exp_pos _).le
  have hνfin : ν Set.univ ≠ (⊤ : ENNReal) := by
    simp only [ν, _root_.MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact (_root_.MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      standardGauss_int.aestronglyMeasurable
      (_root_.MeasureTheory.ae_of_all _ hstd_nonneg)).2 standardGauss_int
  have hfin : ∃ R, ν (s R) ≠ (⊤ : ENNReal) := by
    refine ⟨0, ne_of_lt ((_root_.MeasureTheory.measure_mono (_root_.Set.subset_univ (s 0))).trans_lt ?_)⟩
    exact lt_top_iff_ne_top.mpr hνfin
  have ht := _root_.MeasureTheory.tendsto_measure_iInter_atTop
    (μ := ν) (s := s) (fun R ↦ (hs R).nullMeasurableSet) hanti hfin
  have ht' : _root_.Filter.Tendsto (ν ∘ s) _root_.Filter.atTop (nhds 0) := by
    simpa only [hinter, _root_.MeasureTheory.measure_empty] using ht
  have heq :
      (ν ∘ s) =
        (fun R : Real ↦
          ∫⁻ y : Eucl (n := n) in {y | R < ‖y‖},
            ENNReal.ofReal (standardGauss y) ∂volume) := by
    funext R
    simp only [Function.comp_apply, ν, _root_.MeasureTheory.withDensity_apply _ (hs R), s]
  rw [heq] at ht'
  exact ht'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss_tail
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Euclidean.standardGauss_tail target :: scope.openDecls } }

omit [Nonempty n] in
theorem gaussSPDTail_eq
    (A : Matrix n n Real) (hA : A.PosDef) (R : Real) :
    (∫⁻ x : Eucl (n := n) in
        {x | R < Real.sqrt
          (_root_.Inner.inner Real x (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))},
        ENNReal.ofReal
          (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
            Real.sqrt A.det *
            Real.exp (-_root_.Inner.inner Real x
              (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))) ∂volume) =
      ∫⁻ y : Eucl (n := n) in {y | R < ‖y‖},
        ENNReal.ofReal
          (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
            Real.exp (-‖y‖ ^ 2)) ∂volume := by
  let L := spdSqrtEquiv A hA
  let d : Real := LinearMap.det
    (L : Eucl (n := n) →ₗ[Real] Eucl (n := n))
  let f : Eucl (n := n) → ENNReal :=
    fun y ↦ ENNReal.ofReal (standardGauss y)
  let s : Set (Eucl (n := n)) := {y | R < ‖y‖}
  have hd : d = Real.sqrt A.det := spdSqrt_det A hA
  have hdpos : 0 < d := hd ▸ Real.sqrt_pos.2 hA.det_pos
  have hdetpos : 0 < LinearMap.det
      (L : Eucl (n := n) →ₗ[Real] Eucl (n := n)) := by
    simpa only [d] using hdpos
  have hmap : Measure.map
      (L : Eucl (n := n) →ₗ[Real] Eucl (n := n))
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Eucl (n := n))) =
        ENNReal.ofReal (d⁻¹) • volume := by
    dsimp only [d]
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (Eucl (n := n))) hdetpos.ne']
    rw [abs_of_pos (inv_pos.mpr hdetpos)]
  have hset :
      {x : Eucl (n := n) | R < Real.sqrt
        (_root_.Inner.inner Real x (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))} =
        L ⁻¹' s := by
    ext x
    simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, s]
    rw [← spdSqrt_norm_sq A hA]
    rw [Real.sqrt_sq (norm_nonneg (L x))]
  have hf : Measurable f := by
    dsimp only [f, standardGauss]
    fun_prop
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const continuous_norm.measurable
  let g : Eucl (n := n) → ENNReal := s.indicator f
  have hg : Measurable g := hf.indicator hs
  have hdens : ∀ x : Eucl (n := n),
      ENNReal.ofReal
          (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
            Real.sqrt A.det *
            Real.exp (-_root_.Inner.inner Real x
              (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))) =
        ENNReal.ofReal d * f (L x) := by
    intro x
    rw [← hd, ← spdSqrt_norm_sq A hA]
    dsimp only [f, standardGauss]
    let c : Real :=
      ((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹
    have hc : 0 ≤ c :=
      inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _)
    have he : 0 ≤ Real.exp (-‖L x‖ ^ 2) := (Real.exp_pos _).le
    change ENNReal.ofReal (c * d * Real.exp (-‖L x‖ ^ 2)) =
      ENNReal.ofReal d * ENNReal.ofReal (c * Real.exp (-‖L x‖ ^ 2))
    calc
      ENNReal.ofReal (c * d * Real.exp (-‖L x‖ ^ 2)) =
          ENNReal.ofReal c * ENNReal.ofReal d *
            ENNReal.ofReal (Real.exp (-‖L x‖ ^ 2)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc hdpos.le),
          ENNReal.ofReal_mul hc]
      _ = ENNReal.ofReal d *
          ENNReal.ofReal (c * Real.exp (-‖L x‖ ^ 2)) := by
        rw [ENNReal.ofReal_mul hc]
        ring
  have hcancel : ENNReal.ofReal d * ENNReal.ofReal (d⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hdpos.le, mul_inv_cancel₀ hdpos.ne']
    norm_num
  rw [hset]
  calc
    (∫⁻ x : Eucl (n := n) in L ⁻¹' s,
        ENNReal.ofReal
          (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
            Real.sqrt A.det *
            Real.exp (-_root_.Inner.inner Real x
              (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))) ∂volume) =
        ∫⁻ x : Eucl (n := n), ENNReal.ofReal d * g (L x) ∂volume := by
      rw [← _root_.MeasureTheory.lintegral_indicator (hs.preimage L.continuous.measurable)]
      refine _root_.MeasureTheory.lintegral_congr fun x ↦ ?_
      by_cases hx : L x ∈ s
      · have hx' : x ∈ L ⁻¹' s := hx
        simp only [Set.indicator_of_mem hx', g, Set.indicator_of_mem hx]
        exact hdens x
      · have hx' : x ∉ L ⁻¹' s := hx
        simp only [Set.indicator_of_notMem hx', g,
          Set.indicator_of_notMem hx, _root_.MulZeroClass.mul_zero]
    _ = ENNReal.ofReal d * ∫⁻ x : Eucl (n := n), g (L x) ∂volume := by
      simpa only [Function.comp_apply] using
        (_root_.MeasureTheory.lintegral_const_mul (ENNReal.ofReal d)
          (hg.comp L.continuous.measurable))
    _ = ENNReal.ofReal d * ∫⁻ y : Eucl (n := n), g y
          ∂(Measure.map (L : Eucl (n := n) →ₗ[Real] Eucl (n := n)) _root_.MeasureTheory.MeasureSpace.volume) := by
      congr 1
      exact (_root_.MeasureTheory.lintegral_map hg L.continuous.measurable).symm
    _ = ENNReal.ofReal d *
          (ENNReal.ofReal (d⁻¹) * ∫⁻ y : Eucl (n := n), g y ∂volume) := by
      rw [hmap, _root_.MeasureTheory.lintegral_smul_measure]
      rfl
    _ = ∫⁻ y : Eucl (n := n), g y ∂volume := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = ∫⁻ y : Eucl (n := n) in {y | R < ‖y‖},
          ENNReal.ofReal
            (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
              Real.exp (-‖y‖ ^ 2)) ∂volume := by
      rw [← _root_.MeasureTheory.lintegral_indicator hs]
      exact _root_.MeasureTheory.lintegral_congr fun _ ↦ rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPDTail_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPDTail_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPDTail_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussSPDTail_eq

theorem gaussianPosDef_uniform_tail (eps : ENNReal) (heps : 0 < eps) :
    ∃ R : Real, 0 ≤ R ∧ ∀ (A : Matrix n n Real), A.PosDef →
      (∫⁻ x : Eucl (n := n) in
          {x | R < Real.sqrt
            (_root_.Inner.inner Real x (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))},
          ENNReal.ofReal
            (((Real.pi : Real) ^ ((Fintype.card n : Real) / 2))⁻¹ *
              Real.sqrt A.det *
              Real.exp (-_root_.Inner.inner Real x
                (Matrix.toEuclideanCLM (n := n) (𝕜 := Real) A x))) ∂volume) ≤ eps := by
  have hevent := (tendsto_order.1 (standardGauss_tail (n := n))).2 eps heps
  obtain ⟨R₀, hR₀⟩ := hevent.exists_forall_of_atTop
  let R := _root_.Max.max 0 R₀
  refine ⟨R, le_max_left _ _, ?_⟩
  intro A hA
  rw [gaussSPDTail_eq A hA R]
  exact (hR₀ R (le_max_right 0 R₀)).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussianPosDef_uniform_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussianPosDef_uniform_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussianPosDef_uniform_tail ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.gaussianPosDef_uniform_tail

end DifferentialGeometry.Analysis.Parabolic.Euclidean
