import Submission.DifferentialGeometry.Geometry.Curvature.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Mathlib.Topology.Sequences
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

section Completeness

variable {V H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cylinder_height_edist_le (g : SmoothRiemannianMetric I M)
    (x y : M × ℝ) :
    edist x.2 y.2 ≤ riemannianEDistOf (cylinderMetric g) x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) :=
    ⟨(cylinderMetric g).toRiemannianMetric⟩
  have hnorm (q : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ)) q) :
      ‖(v.2 : ℝ)‖ₑ ≤ ‖v‖ₑ := by
    have hnonneg (u : TangentSpace I q.1) : 0 ≤ g.inner q.1 u u := by
      by_cases hu : u = 0
      · subst u
        rw [map_zero (g.inner q.1)]
        exact le_rfl
      · exact (g.pos q.1 u hu).le
    have hg := hnonneg (v.1 : TangentSpace I q.1)
    calc
      ‖(v.2 : ℝ)‖ₑ = ENNReal.ofReal |v.2| := by
        rw [← ofReal_norm, Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (Real.sqrt ((cylinderMetric g).inner q v v)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.le_sqrt_of_sq_le
        rw [cylinderMetric_inner]
        nlinarith [sq_abs v.2]
      _ = ‖v‖ₑ := by
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        rfl
  change _root_.EDist.edist x.2 y.2 ≤ _root_.Manifold.riemannianEDist (I.prod 𝓘(ℝ)) x y
  by_contra h
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (lt_of_not_ge h)
      (a := (0 : ℝ)) (b := 1) zero_lt_one
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun t : ℝ => (γ t).2) :=
    contMDiff_snd.comp hγ
  have hdiff (t : ℝ) :
      mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => (γ s).2) t 1 =
        (mfderiv 𝓘(ℝ) (I.prod 𝓘(ℝ)) γ t 1).2 := by
    change mfderiv 𝓘(ℝ) 𝓘(ℝ) (Prod.snd ∘ γ) t 1 = _
    rw [mfderiv_comp t mdifferentiableAt_snd (hγ.mdifferentiable (by simp) t),
      mfderiv_snd]
    rfl
  have hproj : _root_.Manifold.pathELength 𝓘(ℝ) (fun t : ℝ => (γ t).2) 0 1 ≤
      pathELength (I.prod 𝓘(ℝ)) γ 0 1 := by
    rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc,
      _root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    apply _root_.MeasureTheory.lintegral_mono
    intro t
    dsimp only
    rw [enorm_tangentSpace_vectorSpace, hdiff]
    exact hnorm (γ t) _
  have hdist : _root_.EDist.edist x.2 y.2 ≤
      pathELength 𝓘(ℝ) (fun t : ℝ => (γ t).2) 0 1 := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ))]
    exact _root_.Manifold.riemannianEDist_le_pathELength hη.contMDiffOn
      (congrArg Prod.snd hγ0) (congrArg Prod.snd hγ1) zero_le_one
  exact (not_lt_of_ge (hdist.trans hproj)) hlen

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinder_height_edist_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.cylinder_height_edist_le target :: scope.openDecls } }

variable [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cylinder_complete_of_compact (g : SmoothRiemannianMetric I M) :
    RiemannianMetricComplete (cylinderMetric g) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : IsManifold (I.prod 𝓘(ℝ)) 1 (M × ℝ) := inferInstance
  let : TopologicalSpace.MetrizableSpace (M × ℝ) :=
    Manifold.metrizableSpace (I.prod 𝓘(ℝ)) (M × ℝ)
  let : T3Space (M × ℝ) := inferInstance
  refine ⟨?_⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) :=
    ⟨(cylinderMetric g).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (V × ℝ)
      (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) :=
    ⟨⟨(cylinderMetric g).inner, (cylinderMetric g).contMDiff.continuous,
      by intro q v w; rfl⟩⟩
  let : EMetricSpace (M × ℝ) := EMetricSpace.ofRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ)
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hz : CauchySeq (fun k : ℕ => (u k).2) := by
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    change riemannianEDistOf (cylinderMetric g) (u m) (u n) < ε at hmn
    exact (cylinder_height_edist_le g (u m) (u n)).trans_lt hmn
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hz
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq (fun k : ℕ => (u k).1)
  have hsub : _root_.Filter.Tendsto (u ∘ φ) _root_.Filter.atTop (𝓝 (p, z)) := by
    exact hp.prodMk_nhds (hz.comp hφ.tendsto_atTop)
  exact ⟨(p, z), tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hsub⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinder_complete_of_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.cylinder_complete_of_compact target :: scope.openDecls } }

end Completeness

section ShrinkingCylinder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry : FiniteDimensional ℝ E :=
  FiniteDimensional.of_fact_finrank_eq_succ 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFiniteDimensionalReal_differentialGeometry target :: scope.openDecls } }

private def sphereScale (t : ℝ) : ℝ := if t < 1 then 2 * (1 - t) else 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sphereScale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sphereScale target :: scope.openDecls } }

private theorem sphereScale_pos (t : ℝ) : 0 < sphereScale t := by
  unfold sphereScale
  split_ifs with ht
  · exact mul_pos (by norm_num) (sub_pos.mpr ht)
  · norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sphereScale_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sphereScale_pos target :: scope.openDecls } }

def shrinkingCylinderMetric (t : ℝ) :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) :=
  cylinderMetric (scaleMetric (sphereScale t) (sphereScale_pos t)
    (roundMetric (E := E) (n := 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric

theorem shrinkingCylinderMetric_inner {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (shrinkingCylinderMetric (E := E) t).inner x v w =
      2 * (1 - t) * (roundMetric (E := E) (n := 2)).inner x.1 v.1 w.1 + v.2 * w.2 := by
  rw [shrinkingCylinderMetric, cylinderMetric_inner]
  have h := scaleMetric_inner (sphereScale t) (sphereScale_pos t)
    (roundMetric (E := E) (n := 2)) x.1
    (v.1 : TangentSpace (𝓡 2) x.1) (w.1 : TangentSpace (𝓡 2) x.1)
  calc
    _ = sphereScale t * (roundMetric (E := E) (n := 2)).inner x.1 v.1 w.1 +
        v.2 * w.2 := congrArg (fun a : ℝ => a + v.2 * w.2) h
    _ = _ := by rw [sphereScale, if_pos ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner

theorem shrinkingCylinderMetric_eq_prod {t : ℝ} (ht : t < 1) :
    shrinkingCylinderMetric (E := E) t =
      (scaleMetric (2 * (1 - t)) (mul_pos (by norm_num) (sub_pos.mpr ht))
        (roundMetric (E := E) (n := 2))).prod (euclideanMetric (E := ℝ)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [shrinkingCylinderMetric_inner ht, SmoothRiemannianMetric.prod_inner]
  erw [scaleMetric_inner]
  change _ + v.2 * w.2 = _ + _root_.Inner.inner ℝ (v.2 : ℝ) (w.2 : ℝ)
  rw [RCLike.inner_apply, conj_trivial]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_eq_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_eq_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_eq_prod ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_eq_prod

@[simp] theorem shrinkingCylinderMetric_zero :
    shrinkingCylinderMetric (E := E) 0 = roundCylinderMetric (E := E) (n := 2) := by
  simp only [shrinkingCylinderMetric, sphereScale, show (0 : ℝ) < 1 by norm_num,
    if_true, sub_zero, mul_one, roundCylinderMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero

theorem ricciTensor_shrinkingCylinderMetric (t : ℝ)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    ricciTensor (shrinkingCylinderMetric (E := E) t) x v w =
      (roundMetric (E := E) (n := 2)).inner x.1 v.1 w.1 := by
  unfold shrinkingCylinderMetric
  exact (ricciTensor_cylinderMetric _ x v w).trans
    ((ricciTensor_scaleMetric (sphereScale t) (sphereScale_pos t)
      (roundMetric (E := E) (n := 2)) x.1 v.1 w.1).trans
        (by
          have h := ricciTensor_roundSphere (n := 2) x.1 v.1 w.1
          norm_num at h ⊢
          exact h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric

theorem shrinkingCylinderMetric_affine {t : ℝ} (ht : t < 1) :
    (shrinkingCylinderMetric (E := E) t).inner =
      fun x => (shrinkingCylinderMetric (E := E) 0).inner x -
        (2 * t) • ricciTensor (shrinkingCylinderMetric (E := E) 0) x := by
  funext x
  ext v w
  change (shrinkingCylinderMetric (E := E) t).inner x v w =
    (shrinkingCylinderMetric (E := E) 0).inner x v w -
      (2 * t) * ricciTensor (shrinkingCylinderMetric (E := E) 0) x v w
  rw [shrinkingCylinderMetric_inner ht,
    shrinkingCylinderMetric_inner (by norm_num : (0 : ℝ) < 1),
    ricciTensor_shrinkingCylinderMetric]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_affine

theorem shrinkingCylinderMetric_hasDerivAt {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    HasDerivAt (fun s : ℝ => (shrinkingCylinderMetric (E := E) s).inner x v w)
      (-2 * ricciTensor (shrinkingCylinderMetric (E := E) t) x v w) t := by
  let a : ℝ := (roundMetric (E := E) (n := 2)).inner x.1 v.1 w.1
  have h : HasDerivAt (fun s : ℝ => 2 * (1 - s) * a + v.2 * w.2) (-2 * a) t := by
    have hbase := (((hasDerivAt_const t (1 : ℝ)).sub
      (hasDerivAt_id t)).const_mul 2).mul_const a
    have hsum := hbase.add_const (v.2 * w.2)
    simp only [Pi.sub_apply, zero_sub, mul_neg, mul_one, neg_mul, id_eq] at hsum
    rw [neg_mul]
    exact hsum
  rw [ricciTensor_shrinkingCylinderMetric]
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  exact shrinkingCylinderMetric_inner hs x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_hasDerivAt

private theorem shrinkingCylinderMetric_interpolate {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    (shrinkingCylinderMetric (E := E) t).inner x v w =
      (1 - 2 * t) * (roundCylinderMetric (E := E) (n := 2)).inner x v w +
        (2 * t) * (cylinderMetric (roundMetric (E := E) (n := 2))).inner x v w := by
  have hzero : (roundCylinderMetric (E := E) (n := 2)).inner x v w =
      2 * (roundMetric (E := E) (n := 2)).inner x.1 v.1 w.1 + v.2 * w.2 := by
    rw [roundCylinderMetric, cylinderMetric_inner]
    exact congrArg (fun a : ℝ => a + v.2 * w.2)
      (scaleMetric_inner 2 (by norm_num) (roundMetric (E := E) (n := 2)) x.1
        (v.1 : TangentSpace (𝓡 2) x.1) (w.1 : TangentSpace (𝓡 2) x.1))
  rw [shrinkingCylinderMetric_inner ht, hzero, cylinderMetric_inner]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_interpolate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_interpolate target :: scope.openDecls } }

private theorem shrinkingCylinderMetric_jointGram
    {a b : ℝ} (hbone : b ≤ 1)
    (x₀ : Metric.sphere (0 : E) 1 × ℝ)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
      (fun p : ℝ × (Metric.sphere (0 : E) 1 × ℝ) =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (shrinkingCylinderMetric (E := E) p.1) x₀ p.2 i j)
      (_root_.Set.Ico a b ×ˢ
        (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
          (TangentSpace ((𝓡 2).prod 𝓘(ℝ))) x₀).baseSet) := by
  let g₀ := roundCylinderMetric (E := E) (n := 2)
  let g₁ := cylinderMetric (roundMetric (E := E) (n := 2))
  let U := (_root_.FiberBundle.trivializationAt (EuclideanSpace ℝ (Fin 2) × ℝ)
    (TangentSpace ((𝓡 2).prod 𝓘(ℝ))) x₀).baseSet
  have hstatic (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ))
      (Metric.sphere (0 : E) 1 × ℝ)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
        (fun p : ℝ × (Metric.sphere (0 : E) 1 × ℝ) => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g x₀ p.2 i j)
        (_root_.Set.Ico a b ×ˢ U) :=
    (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn g x₀ i j).comp contMDiffOn_snd
      (fun _ hp => hp.2)
  have ha : ContMDiffOn (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
      (fun p : ℝ × (Metric.sphere (0 : E) 1 × ℝ) => 1 - 2 * p.1)
      (_root_.Set.Ico a b ×ˢ U) :=
    contMDiffOn_const.sub (contMDiffOn_const.mul contMDiffOn_fst)
  have hb : ContMDiffOn (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
      (fun p : ℝ × (Metric.sphere (0 : E) 1 × ℝ) => 2 * p.1)
      (_root_.Set.Ico a b ×ˢ U) := contMDiffOn_const.mul contMDiffOn_fst
  apply ((ha.mul (hstatic g₀)).add (hb.mul (hstatic g₁))).congr
  intro p hp
  dsimp only [Pi.mul_apply, Pi.add_apply]
  simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  exact shrinkingCylinderMetric_interpolate (hp.1.2.trans_le hbone) p.2 _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_jointGram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_jointGram target :: scope.openDecls } }

def shrinkingCylinderSolutionOn :
    SolutionOn (I := (𝓡 2).prod 𝓘(ℝ)) (M := Metric.sphere (0 : E) 1 × ℝ)
      (RealTimeInterval.closedOpen 0 1 (by norm_num)) where
  base := { metric := shrinkingCylinderMetric (E := E) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn

theorem shrinkingCylinderMetric_isSolutionOn_interval {a b : ℝ} (hab : a < b) (hbone : b ≤ 1) :
    IsSolutionOn ({ base.metric := shrinkingCylinderMetric (E := E) } :
      SolutionOn (I := (𝓡 2).prod 𝓘(ℝ)) (M := Metric.sphere (0 : E) 1 × ℝ)
        (RealTimeInterval.closedOpen a b hab)) := by
  apply solutionOn_of_joint hab (shrinkingCylinderMetric (E := E))
    (shrinkingCylinderMetric_jointGram hbone)
  intro t ht x v w
  exact (shrinkingCylinderMetric_hasDerivAt (ht.2.trans_le hbone) x v w).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval

theorem shrinkingCylinderSolutionOn_isSolutionOn :
    IsSolutionOn (shrinkingCylinderSolutionOn (E := E)) :=
  shrinkingCylinderMetric_isSolutionOn_interval (by norm_num) le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_isSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_isSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_isSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_isSolutionOn

theorem shrinkingCylinderMetric_complete (t : ℝ) :
    RiemannianMetricComplete (shrinkingCylinderMetric (E := E) t) := by
  let : CompactSpace (Metric.sphere (0 : E) 1) := inferInstance
  exact cylinder_complete_of_compact _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_complete

theorem shrinkingCylinderMetric_scalar {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricScalarAt (shrinkingCylinderMetric (E := E) t) x = (1 - t)⁻¹ := by
  have hpos : 0 < 2 * (1 - t) := by positivity
  have heq : shrinkingCylinderMetric (E := E) t =
      cylinderMetric (scaleMetric (2 * (1 - t)) hpos (roundMetric (E := E) (n := 2))) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [shrinkingCylinderMetric_inner ht, cylinderMetric_inner]
    exact congrArg (fun z : ℝ => z + v.2 * w.2)
      (scaleMetric_inner (2 * (1 - t)) hpos (roundMetric (E := E) (n := 2)) y.1
        (v.1 : TangentSpace (𝓡 2) y.1) (w.1 : TangentSpace (𝓡 2) y.1)).symm
  have hround : metricScalarAt (roundMetric (E := E) (n := 2)) x.1 = 2 := by
    have h := metricScalarAt_roundCylinder (E := E) (n := 2) x
    rw [roundCylinderMetric, cylinderMetric, metricScalarAt_productMetric,
      metricScalarAt_scaleMetric, metricScalarAt_eq_zero_of_finrank_le_one _ (by simp) x.2] at h
    norm_num at h
    linarith
  rw [heq, cylinderMetric, metricScalarAt_productMetric, metricScalarAt_scaleMetric,
    hround, metricScalarAt_eq_zero_of_finrank_le_one _ (by simp) x.2, add_zero]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar

theorem shrinkingCylinderMetric_scalar_pos {t : ℝ} (ht : t < 1)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    0 < metricScalarAt (shrinkingCylinderMetric (E := E) t) x := by
  rw [shrinkingCylinderMetric_scalar ht]
  exact inv_pos.mpr (sub_pos.mpr ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_pos

theorem shrinkingCylinderMetric_scalar_le_one {t : ℝ} (ht : t ≤ 0)
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricScalarAt (shrinkingCylinderMetric (E := E) t) x ≤ 1 := by
  rw [shrinkingCylinderMetric_scalar (ht.trans_lt zero_lt_one)]
  exact inv_le_one_of_one_le₀ (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_le_one

theorem shrinkingCylinderMetric_scalar_zero (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricScalarAt (shrinkingCylinderMetric (E := E) 0) x = 1 := by
  rw [shrinkingCylinderMetric_zero]
  convert (metricScalarAt_roundCylinder (n := 2) x) using 1
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_scalar_zero

theorem shrinkingCylinderSolutionOn_initial_complete :
    (shrinkingCylinderSolutionOn (E := E)).base.metric 0 =
        roundCylinderMetric (E := E) (n := 2) ∧
      ∀ t ∈ (RealTimeInterval.closedOpen 0 1 (by norm_num)).carrier,
        RiemannianMetricComplete ((shrinkingCylinderSolutionOn (E := E)).base.metric t) := by
  constructor
  · exact shrinkingCylinderMetric_zero
  · intro t _ht
    exact shrinkingCylinderMetric_complete t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_initial_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_initial_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_initial_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderSolutionOn_initial_complete

end ShrinkingCylinder

end DifferentialGeometry.PDE.RicciFlow

end
