import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Analysis.Calculus (realTangentOne)
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {C q m s r : ℝ} {x y : M} (hC : 0 ≤ C) (hqm : q < m)
    (hgrad : ∀ z, q < S.scalar s z → ∀ v : TangentSpace I z,
      |scalarDifferential (I := I) S s z v| ≤
        C * S.scalar s z * Real.sqrt (S.scalar s z) *
          Real.sqrt ((S.base.metric s).inner z v v))
    (hx : m ≤ S.scalar s x) (hy : S.scalar s y ≤ m) (hr : 0 ≤ r)
    (hxy : y ∈ riemannianClosedBallOf (S.base.metric s) x r) :
    (Real.sqrt m)⁻¹ - (Real.sqrt (S.scalar s x))⁻¹ ≤ C / 2 * r := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  rcases le_or_gt m 0 with hm0 | hm0
  · rw [Real.sqrt_eq_zero'.mpr hm0, inv_zero, zero_sub, neg_le]
    exact (neg_nonpos.mpr (by positivity)).trans (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have key : ∀ η : ℝ, 0 < η →
      (Real.sqrt m)⁻¹ - (Real.sqrt (S.scalar s x))⁻¹ ≤ C / 2 * (r + η) := by
    intro η hη
    obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
      exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric s) hr hη hxy
    have hcont : Continuous (fun σ : ℝ => S.scalar s (gam σ)) :=
      (scalarSmoothOfSolution (I := I) S s).continuous.comp hgam.continuous
    set T : Set ℝ := _root_.Set.Icc (0 : ℝ) 1 ∩ {σ | S.scalar s (gam σ) ≤ m} with hTdef
    have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le hcont continuous_const)
    have h1T : (1 : ℝ) ∈ T :=
      ⟨⟨zero_le_one, le_rfl⟩, show S.scalar s (gam 1) ≤ m by rw [hgam1]; exact hy⟩
    have hTne : T.Nonempty := ⟨1, h1T⟩
    have hTbdd : BddBelow T := ⟨0, fun σ hσ => hσ.1.1⟩
    set v := _root_.InfSet.sInf T with hvdef
    have hvT : v ∈ T := hTc.csInf_mem hTne hTbdd
    have hv0 : 0 ≤ v := hvT.1.1
    have hv1 : v ≤ 1 := hvT.1.2
    have hlow : ∀ w ∈ _root_.Set.Icc (0 : ℝ) v, m ≤ S.scalar s (gam w) := by
      have hlt : ∀ w ∈ _root_.Set.Ico (0 : ℝ) v, m ≤ S.scalar s (gam w) := by
        intro w hw
        by_contra hcon
        have hwT : w ∈ T := ⟨⟨hw.1, hw.2.le.trans hv1⟩, (not_le.mp hcon).le⟩
        exact absurd (csInf_le hTbdd hwT) (not_le.mpr hw.2)
      intro w hw
      rcases hw.2.lt_or_eq with hwv | rfl
      · exact hlt w ⟨hw.1, hwv⟩
      · rcases hv0.lt_or_eq with hvpos | hveq
        · have hcl : IsClosed {σ : ℝ | m ≤ S.scalar s (gam σ)} :=
            isClosed_le continuous_const hcont
          have hsub : _root_.Set.Ico (0 : ℝ) v ⊆ {σ : ℝ | m ≤ S.scalar s (gam σ)} := fun σ hσ => hlt σ hσ
          have hmem : v ∈ closure (_root_.Set.Ico (0 : ℝ) v) := by
            rw [closure_Ico hvpos.ne]
            exact ⟨hv0, le_rfl⟩
          exact hcl.closure_subset_iff.mpr hsub hmem
        · rw [← hveq, hgam0]
          exact hx
    have hpos : ∀ w ∈ _root_.Set.Icc (0 : ℝ) v, 0 < S.scalar s (gam w) := fun w hw =>
      hm0.trans_le (hlow w hw)
    have hderiv : ∀ w ∈ _root_.Set.Icc (0 : ℝ) v,
        HasDerivAt (fun σ : ℝ => (Real.sqrt (S.scalar s (gam σ)))⁻¹)
          (-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
              scalarDifferential (I := I) S s (gam w)
                (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar s (gam w)) ^ 2) w := fun w hw =>
      hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S s hgam w) (hpos w hw)
    have hbdd : ∀ w ∈ _root_.Set.Icc (0 : ℝ) v,
        |-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
            scalarDifferential (I := I) S s (gam w)
              (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) /
            Real.sqrt (S.scalar s (gam w)) ^ 2| ≤
          C / 2 * Real.sqrt ((S.base.metric s).inner (gam w)
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
            (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))) := by
      intro w hw
      refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
      have hgd := hgrad (gam w) (hqm.trans_le (hlow w hw))
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
      calc _ ≤ _ := hgd
        _ = _ := by ring
    have hbud := abs_sub_le_of_hasDerivAt_of_lintegral_le
      (f := fun σ : ℝ => (Real.sqrt (S.scalar s (gam σ)))⁻¹) (a := 0) (b := v) (c := 0) (d := 1)
      (v := fun w : ℝ => Real.sqrt ((S.base.metric s).inner (gam w)
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))
        (mfderiv 𝓘(ℝ, ℝ) I gam w (realTangentOne w))))
      hv0 (_root_.Set.Icc_subset_Icc le_rfl hv1) (by positivity) (by positivity) hderiv hbdd hspeed.le
    have hfv : (Real.sqrt m)⁻¹ ≤ (Real.sqrt (S.scalar s (gam v)))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (hpos v ⟨hv0, le_rfl⟩)) (Real.sqrt_le_sqrt hvT.2)
    have hf0 : (Real.sqrt (S.scalar s (gam 0)))⁻¹ = (Real.sqrt (S.scalar s x))⁻¹ := by
      rw [hgam0]
    rw [hf0] at hbud
    linarith [le_abs_self ((Real.sqrt (S.scalar s (gam v)))⁻¹ - (Real.sqrt (S.scalar s x))⁻¹)]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hη : 0 < ε / (C / 2 + 1) := by positivity
  have h := key _ hη
  have hCη : C / 2 * (ε / (C / 2 + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
