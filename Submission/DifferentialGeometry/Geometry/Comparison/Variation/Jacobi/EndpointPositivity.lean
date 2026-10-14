import Submission.DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.IndexForm
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Frame
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Analysis.ODE.IndexForm.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem coeff_jacobi_ode
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (Y : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hFdiff : ∀ i, DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hYdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t)
    (hDYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ Y s) t) t)
    (hFpar : ∀ i, covDerivAlong (I := I) g γ (F i) t = 0)
    (hY : IsJacobiAt (I := I) g γ Y t)
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (hON : ∀ i j, g.inner (γ t) (F i t) (F j t) = if i = j then 1 else 0) :
    HasDerivAt (perpCoeff (I := I) g F Y)
      (perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ Y s) t) t ∧
    HasDerivAt (perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ Y s))
      (-(perpCurvOp (I := I) g γ F t) (perpCoeff (I := I) g F Y t)) t := by
  let L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm
  constructor
  · have hpi := hasDerivAt_pi.mpr fun i =>
      parInner_deriv (I := I) le_rfl g γ (F i) Y t hγ
        (hFdiff i) hYdiff (hFpar i)
    exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
  · have hpi : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s)
          (covDerivAlong (I := I) g γ Y s) : ι → ℝ))
        ((EuclideanSpace.equiv ι ℝ)
          (-(perpCurvOp (I := I) g γ F t) (perpCoeff (I := I) g F Y t))) t := by
      rw [hasDerivAt_pi]
      intro i
      let : Nonempty ι := ⟨i⟩
      have hi := parInner_d2 (I := I) le_rfl g γ (F i) Y t hγ
        (hFdiff i) hDYdiff (hFpar i) hY
      have hcoeff : g.inner (γ t) (F i t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (Y t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) =
          perpCurvOp (I := I) g γ F t (perpCoeff (I := I) g F Y t) i := by
        rw [parInner_curv_expand (I := I) g γ t F Y hON hcard i, perpCurvOp_apply]
        simp only [perpCoeff_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [g.symm (γ t) (F i t)]
        exact mul_comm _ _
      rw [hcoeff] at hi
      simpa using! hi
    have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    simpa only [L, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using! h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.coeff_jacobi_ode
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Variation.coeff_jacobi_ode target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Fintype ι] [DecidableEq ι] in
theorem jacobi_pair_pos
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hseg : _root_.Set.Icc a b ⊆ U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hJdiff : ∀ t ∈ _root_.Set.Icc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ _root_.Set.Icc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ _root_.Set.Icc a b, IsJacobiAt (I := I) g γ J t)
    (hJa : J a = 0) (hJ_ne : ¬ ∀ t ∈ _root_.Set.Icc a b, J t = 0)
    {κ : ℝ} (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ t ∈ _root_.Set.Ioo a b,
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (J t) ≤
        κ * g.inner (γ t) (J t) (J t)) :
    0 < g.inner (γ b) (covDerivAlong (I := I) g γ J b) (J b) := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
      exact False.elim (hJ_ne fun t _ => @Subsingleton.elim E hsub (J t) 0)
  | inr hntr =>
      let : Nontrivial E := hntr
      let : NeZero (Module.finrank ℝ E) := ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))⟩
      have hrank (z : M) : Module.finrank ℝ (TangentSpace I z) = Module.finrank ℝ E :=
        (tangentSpaceModelContinuousLinearEquiv (I := I) z).toLinearEquiv.finrank_eq
      let : NeZero (Module.finrank ℝ (TangentSpace I (γ a))) :=
        ⟨by rw [hrank]; exact NeZero.ne _⟩
      obtain ⟨basis, hbasis⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g (γ a)
      obtain ⟨F, _, hFdiff, hFpar, hON⟩ :=
        exists_parallel_frame_on_Icc (I := I)
          g γ hγ hU hab hseg basis hbasis
      let R := perpCurvOp (I := I) g γ F
      let y := perpCoeff (I := I) g F J
      let v := perpCoeff (I := I) g F (fun s => covDerivAlong (I := I) g γ J s)
      have hγat t (ht : t ∈ _root_.Set.Icc a b) : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t :=
        (hγ t (hseg ht)).contMDiffAt (hU.mem_nhds (hseg ht))
      have hode t (ht : t ∈ _root_.Set.Icc a b) :
          HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t :=
        coeff_jacobi_ode g γ F J t ((hγat t ht).of_le (by norm_num))
          (fun i => hFdiff i t ht) (hJdiff t ht) (hDJdiff t ht)
          (fun i => hFpar i t ht) (hJac t ht) (by simp only [Fintype.card_fin, hrank]) (hON t ht)
      have hsol : DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn R a b y v :=
        ⟨fun t ht => (hode t ht).1.hasDerivWithinAt,
          fun t ht => (hode t ht).2.hasDerivWithinAt⟩
      have hexp t (ht : t ∈ _root_.Set.Icc a b) : (∑ i, y t i • F i t) = J t := by
        simpa only [y, perpCoeff_apply] using
          (gON_expand (I := I) g (γ t) (fun i => F i t) (hON t ht)
            (by simp only [Fintype.card_fin, hrank]) (J t)).symm
      have hinner t (ht : t ∈ _root_.Set.Icc a b) :
          g.inner (γ t) (J t) (J t) = (_root_.Inner.inner ℝ (y t) (y t)) := by
        rw [← hexp t ht]
        exact perpLift_inner (I := I) g F (y t) (y t) t (hON t ht)
      have hupper t (ht : t ∈ _root_.Set.Ioo a b) :
          ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2 := by
        have h := perpCurv_inner (I := I) g γ F (y t) (y t) t
        rw [hexp t (_root_.Set.Ioo_subset_Icc_self ht)] at h
        change ⟪R t (y t), y t⟫ = _ at h
        rw [h]
        exact (hcurv t ht).trans_eq (by rw [hinner t (_root_.Set.Ioo_subset_Icc_self ht), real_inner_self_eq_norm_sq])
      have hy_ne : ¬ _root_.Set.EqOn y (fun _ => 0) (_root_.Set.Icc a b) := by
        intro hyzero
        apply hJ_ne
        intro t ht
        rw [← hexp t ht, hyzero ht]
        simp
      have hp := DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.inner_velocity_position_at_right_pos
        hsol hab
        (perpCoeff_zero (I := I) g F J a hJa) hy_ne hκ hupper
      have hread : g.inner (γ b) (covDerivAlong (I := I) g γ J b) (J b) =
          inner ℝ (v b) (y b) := by
        rw [← hexp b (right_mem_Icc.mpr hab), map_sum, PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show v b i = g.inner (γ b) (F i b)
            (covDerivAlong (I := I) g γ J b) by simp only [v, perpCoeff_apply],
          g.symm (γ b) (F i b) (covDerivAlong (I := I) g γ J b)]
        rw [map_smul]
        simp [RCLike.inner_apply]
      exact hread.symm ▸ hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_pair_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_pair_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_pair_pos ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_pair_pos

end DifferentialGeometry.Geometry.Riemannian.Variation
