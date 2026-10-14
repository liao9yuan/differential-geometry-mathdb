import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_eq_fderivWithin_of_isOpen {U : Set E} (hU : IsOpen U) (u : E → ℝ)
    (q : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ U) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q u y = fderivWithin ℝ u U y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) q) := by
  rw [DifferentialGeometry.Tensor.Coordinates.partialDeriv, fderivWithin_of_isOpen hU hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partialDeriv_eq_fderivWithin_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partialDeriv_eq_fderivWithin_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partialDeriv_eq_fderivWithin_of_isOpen ``Submission.DifferentialGeometry.Geometry.Curvature.partialDeriv_eq_fderivWithin_of_isOpen

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_joint_contDiffWithinAt
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E))
    {S : Set ℝ} {U : Set E} (hU : IsOpen U) {s₀ : ℝ} {y₀ : E}
    (hs : s₀ ∈ S) (hy : y₀ ∈ U)
    (hΨ : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (S ×ˢ U) (s₀, y₀)) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (S ×ˢ U) (s₀, y₀) := by
  have hmem : ((s₀, y₀) : ℝ × E) ∈ S ×ˢ U := ⟨hs, hy⟩
  have hst : S ×ˢ U ⊆ (fun p : ℝ × E => p.2) ⁻¹' U := fun p hp => hp.2
  have hf : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((S ×ˢ U) ×ˢ U) (((s₀, y₀) : ℝ × E), (fun p : ℝ × E => p.2) (s₀, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp (((s₀, y₀) : ℝ × E), y₀)
      (((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffWithinAt) ?_
    rintro z ⟨⟨hz1, -⟩, hz2⟩
    exact ⟨hz1, hz2⟩
  have hg : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => p.2) (S ×ˢ U) (s₀, y₀) := contDiffWithinAt_snd
  have hk : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) q) (S ×ˢ U) (s₀, y₀) :=
    contDiffWithinAt_const
  have hfd := hf.fderivWithin_apply hg hk hU.uniqueDiffOn (le_refl _) hmem hst
  exact hfd.congr (fun p hp => partialDeriv_eq_fderivWithin_of_isOpen hU _ q hp.2)
    (partialDeriv_eq_fderivWithin_of_isOpen hU _ q hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partialDeriv_joint_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partialDeriv_joint_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partialDeriv_joint_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partialDeriv_joint_contDiffWithinAt

section GenTower

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

def chartGramFamilySmoothWithinOn (S : Set ℝ) : Prop :=
  ∀ (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}, s₀ ∈ S →
    y₀ ∈ interior (extChartAt I α).target →
    ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn ``Submission.DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn

omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramFamilySmoothWithinOn_of_jointSmoothOn {S : Set ℝ}
    (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S) :
    chartGramFamilySmoothWithinOn (I := I) gfam α S := by
  exact fun i j _ _ hs hy => (hG i j hs hy).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_jointSmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_jointSmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_jointSmoothOn ``Submission.DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_jointSmoothOn

omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGramOnE_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  classical
  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b)
        (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    intro a b
    have := hG a b hs hy
    simpa only [chartGramOnE_def] using this
  have hdet : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffWithinAt.sum (fun σ _ => ?_)
    refine contDiffWithinAt_const.mul ?_
    exact contDiffWithinAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hx_base : (extChartAt I α).symm y₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    have hy_t : y₀ ∈ (extChartAt I α).target := interior_subset hy
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_t
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have hdet_ne : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam (s₀, y₀).1) α
      ((extChartAt I α).symm (s₀, y₀).2)).det ≠ 0 :=
    ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) (gfam s₀) α hx_base)
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll)
        (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffWithinAt.sum (fun σ _ => ?_)
    refine contDiffWithinAt_const.mul ?_
    refine contDiffWithinAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffWithinAt_const
    · have heq : (fun p : ℝ × E => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp_contDiffWithinAt (s₀, y₀) hdet).mul (hadj k l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelBracket_contDiffWithinAt {S : Set ℝ}
    (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i j l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartChristoffelBracket (I := I) (gfam r.1) α i j l r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffelBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [chartChristoffelBracket]
  rw [heq]
  exact ((partialDeriv_joint_contDiffWithinAt (fun s y => chartGramOnE (I := I) (gfam s) α l j y) i
      isOpen_interior hs hy (hG l j hs hy)).add
    (partialDeriv_joint_contDiffWithinAt (fun s y => chartGramOnE (I := I) (gfam s) α l i y) j
      isOpen_interior hs hy (hG l i hs hy))).sub
    (partialDeriv_joint_contDiffWithinAt (fun s y => chartGramOnE (I := I) (gfam s) α i j y) l
      isOpen_interior hs hy (hG i j hs hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffelBracket_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffelBracket_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffelBracket_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffelBracket_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          chartChristoffelBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_chartChristoffelBracket]
  rw [heq]
  refine contDiffWithinAt_const.mul (ContDiffWithinAt.sum (fun l _ => ?_))
  exact (chartInvGramOnE_contDiffWithinAt (I := I) gfam α hG k l hs hy).mul
    (chartChristoffelBracket_contDiffWithinAt (I := I) gfam α hG i j l hs hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartChristoffel_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (m i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam r.1) α i j k y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDeriv_joint_contDiffWithinAt (fun s y => chartChristoffel (I := I) (gfam s) α i j k y) m
    isOpen_interior hs hy (chartChristoffel_contDiffWithinAt (I := I) gfam α hG i j k hs hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partial_chartChristoffel_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partial_chartChristoffel_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partial_chartChristoffel_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partial_chartChristoffel_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) =
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (fun y => chartChristoffel (I := I) (gfam r.1) α i k l y) r.2 -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (fun y => chartChristoffel (I := I) (gfam r.1) α i j l y) r.2 +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (gfam r.1) α j m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i k m r.2 -
              chartChristoffel (I := I) (gfam r.1) α k m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i j m r.2))) := by
    funext r; rw [chartRiemannTensor_def]
  rw [heq]
  refine ((partial_chartChristoffel_contDiffWithinAt (I := I) gfam α hG j i k l hs hy).sub
    (partial_chartChristoffel_contDiffWithinAt (I := I) gfam α hG k i j l hs hy)).add ?_
  refine ContDiffWithinAt.sum (fun m _ => ?_)
  exact ((chartChristoffel_contDiffWithinAt (I := I) gfam α hG j m l hs hy).mul
      (chartChristoffel_contDiffWithinAt (I := I) gfam α hG i k m hs hy)).sub
    ((chartChristoffel_contDiffWithinAt (I := I) gfam α hG k m l hs hy).mul
      (chartChristoffel_contDiffWithinAt (I := I) gfam α hG i j m hs hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) =
      (fun r : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (gfam r.1) α i j k j r.2) := by
    funext r; rw [chartRicciTensor_def]
  rw [heq]
  exact ContDiffWithinAt.sum (fun j _ => chartRiemannTensor_contDiffWithinAt (I := I) gfam α hG i j k j hs hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRicciTensor_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRicciTensor_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRicciTensor_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartRicciTensor_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRiemannTensor_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (m i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
          (fun y => chartRiemannTensor (I := I) (gfam r.1) α i j k l y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDeriv_joint_contDiffWithinAt (fun s y => chartRiemannTensor (I := I) (gfam s) α i j k l y) m
    isOpen_interior hs hy (chartRiemannTensor_contDiffWithinAt (I := I) gfam α hG i j k l hs hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRicciTensor_contDiffWithinAt {S : Set ℝ} (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (m i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (fun y => chartRicciTensor (I := I) (gfam r.1) α i k y) r.2)
      (S ×ˢ interior (extChartAt I α).target) (s₀, y₀) :=
  partialDeriv_joint_contDiffWithinAt (fun s y => chartRicciTensor (I := I) (gfam s) α i k y) m
    isOpen_interior hs hy (chartRicciTensor_contDiffWithinAt (I := I) gfam α hG i k hs hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_contDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_contDiffAt_of_isOpen {S : Set ℝ} (hS : IsOpen S) (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (s₀, y₀) :=
  (chartChristoffel_contDiffWithinAt (I := I) gfam α hG i j k hs hy).contDiffAt
    ((hS.prod isOpen_interior).mem_nhds ⟨hs, hy⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffAt_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffAt_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffAt_of_isOpen ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffel_contDiffAt_of_isOpen

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_contDiffAt_of_isOpen {S : Set ℝ} (hS : IsOpen S) (hG : chartGramFamilySmoothWithinOn (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) (s₀, y₀) :=
  (chartRiemannTensor_contDiffWithinAt (I := I) gfam α hG i j k l hs hy).contDiffAt
    ((hS.prod isOpen_interior).mem_nhds ⟨hs, hy⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffAt_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffAt_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffAt_of_isOpen ``Submission.DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_contDiffAt_of_isOpen

end GenTower

section Consumer

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartGramFamilySmoothWithinOn_of_contMDiffOn (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)) :
    chartGramFamilySmoothWithinOn (I := I) g α J := by
  classical
  intro i j s₀ y₀ hs hy
  set e := _root_.FiberBundle.trivializationAt E (TangentSpace I) α with he
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆ (extChartAt I α).symm ⁻¹' e.baseSet := by
    intro y hy'
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy'
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [he, trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => p.1) (J ×ˢ interior (extChartAt I α).target) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
      (fun p : ℝ × E => p.2) (J ×ˢ interior (extChartAt I α).target) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
      (J ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
    fun p hp => interior_subset hp.2
  have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
      (fun p : ℝ × E => (extChartAt I α).symm p.2)
      (J ×ˢ interior (extChartAt I α).target) :=
    hsymm.comp hsnd hmaps2
  have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
      (J ×ˢ interior (extChartAt I α).target) :=
    hσ1.prodMk hσ2
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g p.1) α i j p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
    refine ((hgram i j).comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
    intro p _
    rfl
  exact hcomp.contDiffOn (s₀, y₀) ⟨hs, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.chartGramFamilySmoothWithinOn_of_contMDiffOn

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] in
theorem joint_chart_comp_contMDiffWithinAt (α : M) (F : ℝ → E → ℝ) {J : Set ℝ} {t : ℝ} {x : M}
    (hF : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => F r.1 r.2)
      (J ×ˢ interior (extChartAt I α).target) (t, extChartAt I α x))
    (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) := by
  have hchart : ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (fun y : M => extChartAt I α y)
      (chartAt H α).source x :=
    (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)) x hx
  have hmapsSnd : Set.MapsTo (fun p : ℝ × M => p.2) (J ×ˢ (chartAt H α).source)
      (chartAt H α).source := fun p hp => hp.2
  have hchartComp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => extChartAt I α p.2) (J ×ˢ (chartAt H α).source) (t, x) :=
    hchart.comp ((t, x) : ℝ × M) contMDiffWithinAt_snd hmapsSnd
  have hΦ : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M => (p.1, extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) := by
    have h : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M => (p.1, extChartAt I α p.2))
        (J ×ˢ (chartAt H α).source) (t, x) :=
      contMDiffWithinAt_fst.prodMk hchartComp
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hmapsΦ : Set.MapsTo (fun p : ℝ × M => (p.1, extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (J ×ˢ interior (extChartAt I α).target) := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    have hsrc : p.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp2
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hsrc)
  simpa only [Function.comp_def] using
    hF.contMDiffWithinAt.comp ((t, x) : ℝ × M) hΦ hmapsΦ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.joint_chart_comp_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.joint_chart_comp_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.joint_chart_comp_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.joint_chart_comp_contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem chart_mem_interior (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    extChartAt I α x ∈ interior (extChartAt I α).target := by
  have hsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
    ((extChartAt I α).map_source hsrc)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.chart_mem_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.chart_mem_interior target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_comp_extChartAt_contMDiffWithinAt (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g α J) (i j k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) α i j k (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  joint_chart_comp_contMDiffWithinAt (I := I) α (fun s y => chartChristoffel (I := I) (g s) α i j k y)
    (chartChristoffel_contDiffWithinAt (I := I) g α hG i j k ht (chart_mem_interior (I := I) α hx)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g α J) (i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) α i j k l (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  joint_chart_comp_contMDiffWithinAt (I := I) α (fun s y => chartRiemannTensor (I := I) (g s) α i j k l y)
    (chartRiemannTensor_contDiffWithinAt (I := I) g α hG i j k l ht (chart_mem_interior (I := I) α hx)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_comp_extChartAt_contMDiffWithinAt (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g α J) (i k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartRicciTensor (I := I) (g p.1) α i k (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  joint_chart_comp_contMDiffWithinAt (I := I) α (fun s y => chartRicciTensor (I := I) (g s) α i k y)
    (chartRicciTensor_contDiffWithinAt (I := I) g α hG i k ht (chart_mem_interior (I := I) α hx)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRicciTensor_comp_extChartAt_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRicciTensor_comp_extChartAt_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRicciTensor_comp_extChartAt_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.chartRicciTensor_comp_extChartAt_contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g α J) (m i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
          (fun y => chartRiemannTensor (I := I) (g p.1) α i j k l y) (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  joint_chart_comp_contMDiffWithinAt (I := I) α
    (fun s y =>
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (fun z => chartRiemannTensor (I := I) (g s) α i j k l z) y)
    (partial_chartRiemannTensor_contDiffWithinAt (I := I) g α hG m i j k l ht (chart_mem_interior (I := I) α hx)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_comp_extChartAt_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_comp_extChartAt_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_comp_extChartAt_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partial_chartRiemannTensor_comp_extChartAt_contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hG : chartGramFamilySmoothWithinOn (I := I) g α J) (m i k : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ J) {x : M} (hx : x ∈ (chartAt H α).source) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
          (fun y => chartRicciTensor (I := I) (g p.1) α i k y) (extChartAt I α p.2))
      (J ×ˢ (chartAt H α).source) (t, x) :=
  joint_chart_comp_contMDiffWithinAt (I := I) α
    (fun s y => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (fun z => chartRicciTensor (I := I) (g s) α i k z) y)
    (partial_chartRicciTensor_contDiffWithinAt (I := I) g α hG m i k ht (chart_mem_interior (I := I) α hx)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Curvature.partial_chartRicciTensor_comp_extChartAt_contMDiffWithinAt

private theorem icc_subset_ico {a b c : ℝ} (hcb : c < b) : _root_.Set.Icc a c ⊆ _root_.Set.Ico a b :=
  fun _ hx => ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.icc_subset_ico
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.icc_subset_ico target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem slabBase_nhdsWithin (x₀ : M) (a c t : ℝ) :
    _root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet ∈
      𝓝[_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)] ((t, x₀) : ℝ × M) := by
  have hx₀ : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hset : (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)) ∩
      ((fun p : ℝ × M => p.2) ⁻¹' (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
      = _root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
    ext p
    simp [Set.mem_prod]
  have hopen : ((fun p : ℝ × M => p.2) ⁻¹'
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) ∈ 𝓝 ((t, x₀) : ℝ × M) :=
    (((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.preimage
      continuous_snd)).mem_nhds hx₀
  have := inter_mem_nhdsWithin (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)) (a := ((t, x₀) : ℝ × M)) hopen
  rwa [hset] at this

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.slabBase_nhdsWithin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.slabBase_nhdsWithin target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_comp_extChartAt_continuousOn_slab (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) x₀ i j k (extChartAt I x₀ p.2))
      (_root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hG := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g x₀ hgram
  have hsub : _root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      Ico a b ×ˢ (chartAt H x₀).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact Set.prod_mono (icc_subset_ico hcb) (Set.Subset.refl _)
  intro p hp
  exact ((chartChristoffel_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG i j k (hsub hp).1
    (hsub hp).2).continuousWithinAt).mono hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousOn_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousOn_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousOn_slab ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousOn_slab

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_comp_extChartAt_continuousOn_slab (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) x₀ i j k l (extChartAt I x₀ p.2))
      (_root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hG := chartGramFamilySmoothWithinOn_of_contMDiffOn (I := I) g x₀ hgram
  have hsub : _root_.Set.Icc a c ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      Ico a b ×ˢ (chartAt H x₀).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact Set.prod_mono (icc_subset_ico hcb) (Set.Subset.refl _)
  intro p hp
  exact ((chartRiemannTensor_comp_extChartAt_contMDiffWithinAt (I := I) g x₀ hG i j k l (hsub hp).1
    (hsub hp).2).continuousWithinAt).mono hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousOn_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousOn_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousOn_slab ``Submission.DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousOn_slab

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_comp_extChartAt_continuousWithinAt_slab (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ _root_.Set.Icc a c) :
    ContinuousWithinAt
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) x₀ i j k (extChartAt I x₀ p.2))
      (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)) (t, x₀) := by
  have hx₀ : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hbase := chartChristoffel_comp_extChartAt_continuousOn_slab (I := I) g hcb x₀ hgram i j k (t, x₀) ⟨ht, hx₀⟩
  exact hbase.mono_of_mem_nhdsWithin (slabBase_nhdsWithin (I := I) x₀ a c t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousWithinAt_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousWithinAt_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousWithinAt_slab ``Submission.DifferentialGeometry.Geometry.Curvature.chartChristoffel_comp_extChartAt_continuousWithinAt_slab

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_comp_extChartAt_continuousWithinAt_slab (g : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b) (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ _root_.Set.Icc a c) :
    ContinuousWithinAt
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) x₀ i j k l (extChartAt I x₀ p.2))
      (_root_.Set.Icc a c ×ˢ (_root_.Set.univ : Set M)) (t, x₀) := by
  have hx₀ : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hbase := chartRiemannTensor_comp_extChartAt_continuousOn_slab (I := I) g hcb x₀ hgram i j k l (t, x₀) ⟨ht, hx₀⟩
  exact hbase.mono_of_mem_nhdsWithin (slabBase_nhdsWithin (I := I) x₀ a c t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousWithinAt_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousWithinAt_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousWithinAt_slab ``Submission.DifferentialGeometry.Geometry.Curvature.chartRiemannTensor_comp_extChartAt_continuousWithinAt_slab

end Consumer

end DifferentialGeometry.Geometry.Curvature

end
