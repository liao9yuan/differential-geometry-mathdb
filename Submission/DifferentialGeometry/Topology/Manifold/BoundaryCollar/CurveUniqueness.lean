import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.ChartField
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Filter _root_.Manifold
open scoped _root_.ContDiff _root_.Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

private theorem hasDerivWithinAt_chartField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (p : M) {V : (y : M) → TangentSpace I y} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ V s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I p).source) :
    HasDerivWithinAt ((extChartAt I p) ∘ γ)
      (chartField I p V (extChartAt I p (γ t))) s t := by
  have hsrc' : γ t ∈ (chartAt H p).source := by simpa only [extChartAt_source] using hsrc
  have he : chartField I p V (extChartAt I p (γ t)) =
      (show E →L[ℝ] E from mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t)) (V (γ t)) := by
    let Q : M → E := fun y => (mfderiv I 𝓘(ℝ, E) (extChartAt I p) y) (V y)
    have hh : chartField I p V (extChartAt I p (γ t)) =
        Q ((extChartAt I p).symm (extChartAt I p (γ t))) :=
      chartField_eq_mfderiv I p V ((extChartAt I p).map_source hsrc)
    rw [(extChartAt I p).left_inv hsrc] at hh
    exact hh
  apply hasDerivWithinAt_iff_hasFDerivWithinAt.mpr
  apply HasMFDerivWithinAt.hasFDerivWithinAt
  apply (HasMFDerivWithinAt.comp t ((mdifferentiableAt_extChartAt (I := I) hsrc').hasMFDerivAt.hasMFDerivWithinAt)
    (hγ t ht) (Set.subset_preimage_image _ _)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  let L : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t)
  let v : E := V (γ t)
  change L (a • v) = a • chartField I p V (extChartAt I p (γ t))
  rw [map_smul]
  exact congrArg (fun w : E => a • w) he.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.hasDerivWithinAt_chartField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.BoundaryCollar.hasDerivWithinAt_chartField target :: scope.openDecls } }

theorem isMIntegralCurveOn_Icc_local_unique
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    {V : (y : M) → TangentSpace (𝓡∂ n) y}
    (hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)))
    {b : ℝ} (hb : 0 < b) {γ η : ℝ → M}
    (hγ : IsMIntegralCurveOn γ V (_root_.Set.Icc (0 : ℝ) b))
    (hη : IsMIntegralCurveOn η V (_root_.Set.Icc (0 : ℝ) b)) (he : γ 0 = η 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧ _root_.Set.EqOn γ η (_root_.Set.Icc (0 : ℝ) δ) := by
  let I := 𝓡∂ n
  let p := γ 0
  let e := extChartAt I p
  let X := e ∘ γ
  let Y := e ∘ η
  have hzero : (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hdiff : ContDiffWithinAt ℝ 1 (chartField I p V) (_root_.Set.range I) (e p) :=
    (((contDiffOn_chartField I p hV) (e p) (mem_extChartAt_target p)).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin p)).of_le (by norm_num)
  obtain ⟨K, S, hS, hLip⟩ := hdiff.exists_lipschitzOnWith I.convex_range
  have hγsrc : ∀ᶠ t in 𝓝[_root_.Set.Icc (0 : ℝ) b] 0, γ t ∈ e.source :=
    (hγ.continuousWithinAt hzero) (extChartAt_source_mem_nhds p)
  have hηsrc : ∀ᶠ t in 𝓝[_root_.Set.Icc (0 : ℝ) b] 0, η t ∈ e.source := by
    apply (hη.continuousWithinAt hzero)
    rw [← he]
    exact extChartAt_source_mem_nhds p
  have hX : ContinuousWithinAt X (_root_.Set.Icc (0 : ℝ) b) 0 :=
    (continuousAt_extChartAt p).comp_continuousWithinAt (hγ.continuousWithinAt hzero)
  have hY : ContinuousWithinAt Y (_root_.Set.Icc (0 : ℝ) b) 0 := by
    apply ContinuousAt.comp_continuousWithinAt _ (hη.continuousWithinAt hzero)
    rw [← he]
    exact continuousAt_extChartAt p
  have hXmem : ∀ᶠ t in 𝓝[_root_.Set.Icc (0 : ℝ) b] 0, X t ∈ S :=
    (hX.tendsto_nhdsWithin (t := _root_.Set.range I) (fun t _ => ⟨chartAt _ p (γ t), rfl⟩)) hS
  have hYmem : ∀ᶠ t in 𝓝[_root_.Set.Icc (0 : ℝ) b] 0, Y t ∈ S := by
    apply (hY.tendsto_nhdsWithin (t := _root_.Set.range I) (fun t _ => ⟨chartAt _ p (η t), rfl⟩))
    simpa only [Y, _root_.Function.comp_apply, ← he] using hS
  obtain ⟨r, hr, hgood⟩ := Metric.mem_nhdsWithin_iff.mp
    (hγsrc.and (hηsrc.and (hXmem.and hYmem)))
  let δ := _root_.Min.min (b / 2) (r / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδb : δ ≤ b := (min_le_left _ _).trans (by linarith)
  have hδr : δ < r := (min_le_right _ _).trans_lt (by linarith)
  have hsub : _root_.Set.Icc (0 : ℝ) δ ⊆ _root_.Set.Icc (0 : ℝ) b := _root_.Set.Icc_subset_Icc le_rfl hδb
  have hsmall : ∀ t ∈ _root_.Set.Icc (0 : ℝ) δ,
      γ t ∈ e.source ∧ η t ∈ e.source ∧ X t ∈ S ∧ Y t ∈ S := by
    intro t ht
    apply hgood
    refine ⟨?_, hsub ht⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have htime : ∀ t ∈ _root_.Set.Ico (0 : ℝ) δ, _root_.Set.Icc (0 : ℝ) b ∈ 𝓝[_root_.Set.Ici t] t := by
    intro t ht
    exact _root_.Filter.mem_of_superset (Icc_mem_nhdsGE (ht.2.trans_le hδb))
      (_root_.Set.Icc_subset_Icc ht.1 le_rfl)
  have hXd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) δ,
      HasDerivWithinAt X (chartField I p V (X t)) (_root_.Set.Ici t) t := by
    intro t ht
    exact (hasDerivWithinAt_chartField I p hγ (hsub ⟨ht.1, ht.2.le⟩)
      (hsmall t ⟨ht.1, ht.2.le⟩).1).mono_of_mem_nhdsWithin (htime t ht)
  have hYd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) δ,
      HasDerivWithinAt Y (chartField I p V (Y t)) (_root_.Set.Ici t) t := by
    intro t ht
    exact (hasDerivWithinAt_chartField I p hη (hsub ⟨ht.1, ht.2.le⟩)
      (hsmall t ⟨ht.1, ht.2.le⟩).2.1).mono_of_mem_nhdsWithin (htime t ht)
  have hXY : _root_.Set.EqOn X Y (_root_.Set.Icc (0 : ℝ) δ) :=
    ODE_solution_unique_of_mem_Icc_right (fun _ _ => hLip)
      ((continuousOn_extChartAt p).comp (hγ.continuousOn.mono hsub)
        (fun t ht => (hsmall t ht).1)) hXd
      (fun t ht => (hsmall t ⟨ht.1, ht.2.le⟩).2.2.1)
      ((continuousOn_extChartAt p).comp (hη.continuousOn.mono hsub)
        (fun t ht => (hsmall t ht).2.1)) hYd
      (fun t ht => (hsmall t ⟨ht.1, ht.2.le⟩).2.2.2) (congrArg e he)
  refine ⟨δ, hδ, hδb, ?_⟩
  intro t ht
  exact e.injOn (hsmall t ht).1 (hsmall t ht).2.1 (hXY ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_local_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_local_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_local_unique ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_local_unique

theorem isMIntegralCurveOn_Icc_unique_of_interior
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [T2Space M]
    {V : (y : M) → TangentSpace (𝓡∂ n) y}
    (hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)))
    {b : ℝ} (hb : 0 < b) {γ η : ℝ → M}
    (hγ : IsMIntegralCurveOn γ V (_root_.Set.Icc (0 : ℝ) b))
    (hη : IsMIntegralCurveOn η V (_root_.Set.Icc (0 : ℝ) b))
    (hi : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, (𝓡∂ n).IsInteriorPoint (γ t))
    (he : γ 0 = η 0) : _root_.Set.EqOn γ η (_root_.Set.Icc (0 : ℝ) b) := by
  obtain ⟨δ, hδ, hδb, hlocal⟩ := isMIntegralCurveOn_Icc_local_unique hV hb hγ hη he
  have htime : δ / 2 ∈ _root_.Set.Ioo (0 : ℝ) b := ⟨by positivity, by linarith⟩
  have hsame : γ (δ / 2) = η (δ / 2) := hlocal ⟨by positivity, by linarith⟩
  have hopen : _root_.Set.EqOn γ η (_root_.Set.Ioo (0 : ℝ) b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff htime hi (hV.of_le (by norm_num))
      (hγ.mono _root_.Set.Ioo_subset_Icc_self) (hη.mono _root_.Set.Ioo_subset_Icc_self) hsame
  apply hopen.of_subset_closure hγ.continuousOn hη.continuousOn _root_.Set.Ioo_subset_Icc_self
  rw [closure_Ioo hb.ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior

private theorem isMIntegralCurveOn_reverse
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    {V : (y : M) → TangentSpace I y} {γ : ℝ → M} {b : ℝ}
    (hγ : IsMIntegralCurveOn γ V (_root_.Set.Icc (0 : ℝ) b)) :
    IsMIntegralCurveOn (fun t => γ (b - t)) (-V) (_root_.Set.Icc (0 : ℝ) b) := by
  have hh := ((hγ.comp_mul (-1)).comp_add (-b)).mono
    (show _root_.Set.Icc (0 : ℝ) b ⊆ {t | (t + -b) * -1 ∈ _root_.Set.Icc (0 : ℝ) b} from by
      intro t ht
      change 0 ≤ (t + -b) * -1 ∧ (t + -b) * -1 ≤ b
      constructor <;> linarith [ht.1, ht.2])
  simpa only [_root_.Function.comp_def, mul_neg_one, neg_add, neg_neg, neg_add_eq_sub, neg_one_smul] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_reverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_reverse target :: scope.openDecls } }

theorem isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [T2Space M]
    {V : (y : M) → TangentSpace (𝓡∂ n) y}
    (hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)))
    {b : ℝ} (hb : 0 < b) {γ η : ℝ → M}
    (hγ : IsMIntegralCurveOn γ V (_root_.Set.Icc (0 : ℝ) b))
    (hη : IsMIntegralCurveOn η V (_root_.Set.Icc (0 : ℝ) b))
    (hi : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, (𝓡∂ n).IsInteriorPoint (γ t))
    (he : γ b = η b) : _root_.Set.EqOn γ η (_root_.Set.Icc (0 : ℝ) b) := by
  obtain ⟨δ, hδ, hδb, hlocal⟩ := isMIntegralCurveOn_Icc_local_unique hV.neg_section hb
    (isMIntegralCurveOn_reverse (𝓡∂ n) hγ) (isMIntegralCurveOn_reverse (𝓡∂ n) hη)
    (by simpa only [sub_zero] using he)
  have htime : b - δ / 2 ∈ _root_.Set.Ioo (0 : ℝ) b := ⟨by linarith, by linarith⟩
  have hsame : γ (b - δ / 2) = η (b - δ / 2) := hlocal ⟨by positivity, by linarith⟩
  have hopen : _root_.Set.EqOn γ η (_root_.Set.Ioo (0 : ℝ) b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff htime hi (hV.of_le (by norm_num))
      (hγ.mono _root_.Set.Ioo_subset_Icc_self) (hη.mono _root_.Set.Ioo_subset_Icc_self) hsame
  apply hopen.of_subset_closure hγ.continuousOn hη.continuousOn _root_.Set.Ioo_subset_Icc_self
  rw [closure_Ioo hb.ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right

end DifferentialGeometry.Manifold.BoundaryCollar
