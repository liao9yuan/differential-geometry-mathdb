import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

omit [NeZero (Module.finrank ℝ E)] in
noncomputable def parallelTransportSectionOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∀ t, TangentSpace I (γ t) :=
  Classical.choose (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem parallelTransportSectionOnIcc_initial [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀ 0 = v₀ :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_initial ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_initial

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_differentiableAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀) t) t :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).2.1 t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_covDerivAlong [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    covDerivAlong (I := I) g γ
      (parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀) t = 0 :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).2.2 t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_heq_of_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ δ : ℝ → M}
    (hγδ : γ = δ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ)
    {L K : ℝ} (hLK : L = K) (hL : 0 < L) (hK : 0 < K)
    (v : TangentSpace I (γ 0)) (w : TangentSpace I (δ 0))
    (hvw : HEq v w) {s t : ℝ} (hst : s = t) :
    HEq (parallelTransportSectionOnIcc (I := I) g γ hγ hL v s)
      (parallelTransportSectionOnIcc (I := I) g δ hδ hK w t) := by
  subst δ
  subst K
  subst t
  have hvw' : v = w := eq_of_heq hvw
  subst w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_heq_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_heq_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_heq_of_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_heq_of_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_eq_of_mem [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K)
    (v₀ : TangentSpace I (γ 0)) {t : ℝ}
    (htL : t ∈ Set.Icc (0 : ℝ) L) (htK : t ∈ Set.Icc (0 : ℝ) K) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀ t =
      parallelTransportSectionOnIcc (I := I) g γ hγ hK v₀ t := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀
  let W := parallelTransportSectionOnIcc (I := I) g γ hγ hK v₀
  apply parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
      (lo := 0) (hi := t)
  · intro s hs
    exact parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL v₀ ⟨hs.1, hs.2.trans htL.2⟩
  · intro s hs
    exact parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hK v₀ ⟨hs.1, hs.2.trans htK.2⟩
  · intro s hs
    exact parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hL v₀ ⟨hs.1, hs.2.trans htL.2⟩
  · intro s hs
    exact parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hK v₀ ⟨hs.1, hs.2.trans htK.2⟩
  · exact ⟨le_rfl, htL.1⟩
  · simp [V, W]
  · exact ⟨htL.1, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_eq_of_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_eq_of_mem

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL (v + w) t =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v t +
        parallelTransportSectionOnIcc (I := I) g γ hγ hL w t := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL (v + w)
  let Vv := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let Vw := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦ Vv s + Vw s
  refine parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    ?_ ?_ ?_ ?_ (t₀ := 0) ?_ ?_ t ht
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL (v + w) hs
  · intro s hs
    rw [show chartRepAt (I := I) γ W s =
      fun r ↦ chartRepAt (I := I) γ Vv s r + chartRepAt (I := I) γ Vw s r by
        simpa [W] using chartRepAt_add (I := I) γ Vv Vw s]
    exact (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v hs).add
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w hs)
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL (v + w) hs
  · intro s hs
    change covDerivAlong (I := I) g γ (fun r ↦ Vv r + Vw r) s = 0
    rw [covDerivAlong_add (I := I) g γ Vv Vw s
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v hs)
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w hs)]
    rw [parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v hs,
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL w hs]
    simp
  · exact ⟨le_rfl, le_of_lt hL⟩
  · simp [V, W, Vv, Vw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_add ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_add

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportSectionOnIcc_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (c : ℝ) (v : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL (c • v) t =
      c • parallelTransportSectionOnIcc (I := I) g γ hγ hL v t := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL (c • v)
  let Vv := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦ c • Vv s
  refine parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    ?_ ?_ ?_ ?_ (t₀ := 0) ?_ ?_ t ht
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL (c • v) hs
  · intro s hs
    rw [show chartRepAt (I := I) γ W s =
      fun r ↦ c • chartRepAt (I := I) γ Vv s r by
        simpa [W] using chartRepAt_smul (I := I) γ c Vv s]
    exact (parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL v hs).const_smul c
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL (c • v) hs
  · intro s hs
    change covDerivAlong (I := I) g γ (fun r ↦ c • Vv r) s = 0
    rw [covDerivAlong_smul (I := I) g γ c Vv s]
    rw [parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v hs]
    simp
  · exact ⟨le_rfl, le_of_lt hL⟩
  · simp [V, W, Vv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_smul

omit [NeZero (Module.finrank ℝ E)] in
noncomputable def parallelTransportLinearMapOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ L) where
  toFun v := parallelTransportSectionOnIcc (I := I) g γ hγ hL v L
  map_add' v w := parallelTransportSectionOnIcc_add (I := I) g γ hγ hL v w
    ⟨le_of_lt hL, le_rfl⟩
  map_smul' c v := parallelTransportSectionOnIcc_smul (I := I) g γ hγ hL c v
    ⟨le_of_lt hL, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem parallelTransportLinearMapOnIcc_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    parallelTransportLinearMapOnIcc (I := I) g γ hγ hL v =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v L :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearMapOnIcc_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0)) :
    g.inner (γ L) (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL v)
        (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL w) =
      g.inner (γ 0) v w := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  have h := parallel_transport_preserves_inner_product (I := I) g γ le_rfl hγ V W
    (fun t ht ↦ parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL v ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL w ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hL v ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hL w ht) L ⟨le_of_lt hL, le_rfl⟩
  simpa [V, W] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_inner

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearMapOnIcc_injective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    Function.Injective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL) := by
  intro v w hvw
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  have h := parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    (fun t ht ↦ by simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v ht)
    (fun t ht ↦ by simpa [W] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w ht)
    (fun t ht ↦ by simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v ht)
    (fun t ht ↦ by simpa [W] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL w ht)
    (t₀ := L) ⟨le_of_lt hL, le_rfl⟩ (by simpa [V, W] using hvw)
    0 ⟨le_rfl, le_of_lt hL⟩
  simpa [V, W] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_injective ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_injective

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearMapOnIcc_surjective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    Function.Surjective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL) := by
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)]
  exact parallelTransportLinearMapOnIcc_injective (I := I) g γ hγ hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_surjective ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearMapOnIcc_surjective

omit [NeZero (Module.finrank ℝ E)] in
noncomputable def parallelTransportLinearEquivOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ L) :=
  LinearEquiv.ofBijective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL)
    ⟨parallelTransportLinearMapOnIcc_injective (I := I) g γ hγ hL,
      parallelTransportLinearMapOnIcc_surjective (I := I) g γ hγ hL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem parallelTransportLinearEquivOnIcc_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v L :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearEquivOnIcc_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0)) :
    g.inner (γ L) (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v)
        (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL w) =
      g.inner (γ 0) v w :=
  parallelTransportLinearMapOnIcc_inner (I := I) g γ hγ hL v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivOnIcc_inner

omit [NeZero (Module.finrank ℝ E)] in
noncomputable def parallelTransportLinearEquivBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    TangentSpace I (γ a) ≃ₗ[ℝ] TangentSpace I (γ b) := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s ↦ γ (s + a)) :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  exact parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
    hshift (sub_pos.mpr hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearEquivBetween_zero_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {t : ℝ} (ht : 0 < t) (v : TangentSpace I (γ 0)) :
    parallelTransportLinearEquivBetween (I := I) g γ hγ ht v =
      parallelTransportSectionOnIcc (I := I) g γ hγ ht v t := by
  let δ : ℝ → M := fun s => γ (s + 0)
  have hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  have hδγ : δ = γ := by
    funext s
    simp [δ]
  let w : TangentSpace I (δ 0) := v
  have hvw : HEq w v := by
    rfl
  have hleft : HEq (parallelTransportLinearEquivBetween (I := I) g γ hγ ht v)
      (parallelTransportSectionOnIcc (I := I) g δ hδ ht w t) := by
    unfold parallelTransportLinearEquivBetween
    have hshift : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s => γ (s + 0)) :=
      hγ.comp (contMDiff_id.add contMDiff_const)
    have hpos : 0 < t - 0 := sub_pos.mpr ht
    have happly := parallelTransportLinearEquivOnIcc_apply
      (I := I) g (fun s => γ (s + 0)) hshift hpos v
    have hsec := parallelTransportSectionOnIcc_heq_of_eq
      (I := I) g (γ := fun s => γ (s + 0)) (δ := δ)
      rfl hshift hδ (sub_zero t) hpos ht v w (by rfl) (sub_zero t)
    have happly_heq : HEq
        ((parallelTransportLinearEquivOnIcc
          (I := I) g (fun s => γ (s + 0)) hshift hpos) v)
        (parallelTransportSectionOnIcc
          (I := I) g (fun s => γ (s + 0)) hshift hpos v (t - 0)) := by
      rw [happly]
    exact happly_heq.trans hsec
  have hright := parallelTransportSectionOnIcc_heq_of_eq
    (I := I) g hδγ hδ hγ rfl ht ht w v hvw (s := t) (t := t) rfl
  exact eq_of_heq (hleft.trans hright)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_zero_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_zero_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransportLinearEquivBetween_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (v w : TangentSpace I (γ a)) :
    g.inner (γ b) (parallelTransportLinearEquivBetween (I := I) g γ hγ hab v)
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab w) =
      g.inner (γ a) v w := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s ↦ γ (s + a)) :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  change g.inner (γ b)
      (parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
        hshift (sub_pos.mpr hab) v)
      (parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
        hshift (sub_pos.mpr hab) w) =
    g.inner (γ a) v w
  convert parallelTransportLinearEquivOnIcc_inner (I := I) g
    (fun s ↦ γ (s + a)) hshift (sub_pos.mpr hab) v w using 1
  · rw [sub_add_cancel]
  · rw [zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportLinearEquivBetween_inner

end Variation
end Riemannian
end Geometry
end DifferentialGeometry


namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parallelTransportSectionOnIcc_mdifferentiableAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) L) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun s => (⟨γ s, parallelTransportSectionOnIcc g γ hγ hL v₀ s⟩ : TangentBundle I M)) t :=
  sectionAlongCurve_mdifferentiableAt_totalSpace γ _
    (hγ.mdifferentiable (by norm_num) t)
    (parallelTransportSectionOnIcc_differentiableAt g γ hγ hL v₀ ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_mdifferentiableAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.parallelTransportSectionOnIcc_mdifferentiableAt


end DifferentialGeometry.Geometry.Riemannian.Variation
