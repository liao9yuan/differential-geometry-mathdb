import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Support.CalabiMaximum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.NNReal _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

section MetricLine

variable {X : Type*} [MetricSpace X]

private theorem positive_ray_isometry {γ : ℝ → X} (hγ : Isometry γ) :
    Isometry (fun t : ℝ≥0 => γ t) := by
  apply Isometry.of_dist_eq
  intro s t
  exact hγ.dist_eq s t

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.positive_ray_isometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.positive_ray_isometry target :: scope.openDecls } }

private theorem negative_ray_isometry {γ : ℝ → X} (hγ : Isometry γ) :
    Isometry (fun t : ℝ≥0 => γ (-(t : ℝ))) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [hγ.dist_eq, dist_neg_neg]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.negative_ray_isometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.negative_ray_isometry target :: scope.openDecls } }

theorem opposite_busemann_sum_nonpos {γ : ℝ → X} (hγ : Isometry γ) (x : X) :
    busemann (fun t : ℝ≥0 => γ t) x +
      busemann (fun t : ℝ≥0 => γ (-(t : ℝ))) x ≤ 0 := by
  have hp := positive_ray_isometry hγ
  have hn := negative_ray_isometry hγ
  have hlim := (tendsto_busemannApprox hp x).add (tendsto_busemannApprox hn x)
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro t
  have htri := dist_triangle (γ t) x (γ (-(t : ℝ)))
  rw [hγ.dist_eq, Real.dist_eq, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg t.coe_nonneg t.coe_nonneg), dist_comm (γ t) x] at htri
  change (t : ℝ) - _root_.Dist.dist x (γ t) + ((t : ℝ) - _root_.Dist.dist x (γ (-(t : ℝ)))) ≤ 0
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_nonpos ``Submission.DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_nonpos

end MetricLine

section LocalCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem laplacian_add_at_smooth (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x) :
    laplacian (I := I) (LeviCivita (I := I) g) g (fun y => f y + h y) x =
      laplacian (I := I) (LeviCivita (I := I) g) g f x +
        laplacian (I := I) (LeviCivita (I := I) g) g h x := by
  have hnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y := by
    have h1 : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, ℝ) 1 h y :=
      (contMDiffAt_iff_contMDiffAt_nhds (by decide)).mp (hh.of_le (by simp))
    exact h1.mono fun _ hy => hy.mdifferentiableAt (by simp)
  have hneg := laplacian_smul_at (I := I) (LeviCivita (I := I) g) g (-1 : ℝ)
    hnear ((gradientFun_contMDiffAt (I := I) g hh).mdifferentiableAt (by simp))
  have heq : (-1 : ℝ) • h = fun y => -h y := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [heq, neg_one_mul] at hneg
  have hsub := laplacian_sub_of_contMDiffAt (I := I) (LeviCivita (I := I) g) g hf hh.neg
  rw [hneg] at hsub
  simpa only [sub_neg_eq_add] using hsub

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.laplacian_add_at_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.laplacian_add_at_smooth target :: scope.openDecls } }

end LocalCalculus

section CompleteMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem opposite_busemann_sum_eq_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (x : M) :
    busemann (fun t : ℝ≥0 => γ t) x +
      busemann (fun t : ℝ≥0 => γ (-(t : ℝ))) x = 0 := by
  let cp : ℝ≥0 → M := fun t => γ t
  let cn : ℝ≥0 → M := fun t => γ (-(t : ℝ))
  have hp : Isometry cp := positive_ray_isometry hγ
  have hn : Isometry cn := negative_ray_isometry hγ
  let w : M → ℝ := fun y => busemann cp y + busemann cn y
  have hw : Continuous w := (lipschitzWith_busemann hp).continuous.add
    (lipschitzWith_busemann hn).continuous
  have hzero : w (γ 0) = 0 := by
    have hp0 := busemann_ray hp 0
    have hn0 := busemann_ray hn 0
    simp only [cp, cn, NNReal.coe_zero, neg_zero] at hp0 hn0
    dsimp only [w]
    rw [hp0, hn0, zero_add]
  have hmax : ∀ y : M, w y ≤ w (γ 0) := by
    intro y
    rw [hzero]
    exact opposite_busemann_sum_nonpos hγ y
  have hsupport (y : M) (ε : ℝ) (hε : 0 < ε) : ∃ φ : M → ℝ,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ φ y ∧ φ y = w y ∧
        (∀ᶠ z in 𝓝 y, φ z ≤ w z) ∧
        -ε < laplacian (I := I) (LeviCivita (I := I) g) g φ y := by
    have he : 0 < ε / 2 := div_pos hε (by norm_num)
    obtain ⟨φp, Up, hUp, hyp, hφp, hbp, hcp, hlp⟩ :=
      exists_busemann_support_laplacian_gt (I := I) g hEnorm hRic cp hp y (ε / 2) he
    obtain ⟨φn, Un, hUn, hyn, hφn, hbn, hcn, hln⟩ :=
      exists_busemann_support_laplacian_gt (I := I) g hEnorm hRic cn hn y (ε / 2) he
    have hpa := (hφp y hyp).contMDiffAt (hUp.mem_nhds hyp)
    have hna := (hφn y hyn).contMDiffAt (hUn.mem_nhds hyn)
    refine ⟨fun z => φp z + φn z, hpa.add hna, ?_, ?_, ?_⟩
    · change φp y + φn y = busemann cp y + busemann cn y
      rw [hcp, hcn]
    · exact Eventually.of_forall fun z => add_le_add (hbp z) (hbn z)
    · rw [laplacian_add_at_smooth (I := I) g hpa hna]
      linarith
  have heq := eq_of_smooth_lower_support_at_global_max (I := I) g w hw hsupport (γ 0) hmax x
  exact heq.trans hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_eq_zero ``Submission.DifferentialGeometry.Geometry.Topology.opposite_busemann_sum_eq_zero

end CompleteMetric

end DifferentialGeometry.Geometry.Topology

end
