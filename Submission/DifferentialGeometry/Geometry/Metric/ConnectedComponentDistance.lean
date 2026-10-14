import Submission.DifferentialGeometry.Geometry.Exponential.LocalAddition.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Completeness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry.Metric

private theorem component_range_subset
    {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} (hγ : Continuous γ) {p x : X}
    (hx : x ∈ connectedComponent p) (hγ0 : γ 0 = x) :
    ∀ t, γ t ∈ connectedComponent p := by
  have hsub : _root_.Set.range γ ⊆ connectedComponent x :=
    (isPreconnected_range hγ).subset_connectedComponent ⟨0, hγ0⟩
  intro t
  rw [connectedComponent_eq hx]
  exact hsub ⟨t, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.component_range_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.component_range_subset target :: scope.openDecls } }

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem component_codRestrict_c1
    (U : _root_.TopologicalSpace.Opens M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (hmem : ∀ t, γ t ∈ U) :
    ContMDiff 𝓘(ℝ) I 1 (fun t => (⟨γ t, hmem t⟩ : U)) := by
  intro t
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(ℝ) I 1)
    (fun s => (⟨γ s, hmem s⟩ : U)) _root_.Set.univ t).mp (hγ t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.component_codRestrict_c1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.component_codRestrict_c1 target :: scope.openDecls } }

section ActualMetricNorm

variable [FiniteDimensional ℝ E] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem component_pathELength_subtypeVal
    (g : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M)
    {γ : ℝ → U} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : U → Type _) :=
      ⟨(g.restrictOpen U).toRiemannianMetric⟩
    _root_.Manifold.pathELength I ((Subtype.val : U → M) ∘ γ) a b =
      pathELength I γ a b := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : U → Type _) :=
    ⟨(g.restrictOpen U).toRiemannianMetric⟩
  have hamb : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hsub : ∀ (x : U) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g.restrictOpen U).inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    _root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply _root_.MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t _ht
  have hcomp :
      mfderiv 𝓘(ℝ) I ((Subtype.val : U → M) ∘ γ) t =
        (mfderiv I I (Subtype.val : U → M) (γ t)).comp
          (mfderiv 𝓘(ℝ) I γ t) :=
    mfderiv_comp t (hasMFDerivAt_subtype_val U (γ t)).mdifferentiableAt
      (hγ.mdifferentiableAt one_ne_zero)
  dsimp only
  rw [hamb, hsub, hcomp, ContinuousLinearMap.comp_apply,
    SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.component_pathELength_subtypeVal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.component_pathELength_subtypeVal target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem component_edistOf_ambient_le
    (g : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M) (x y : U) :
    riemannianEDistOf g (x : M) (y : M) ≤
      riemannianEDistOf (g.restrictOpen U) x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : U → Type _) :=
    ⟨(g.restrictOpen U).toRiemannianMetric⟩
  change _root_.Manifold.riemannianEDist I (x : M) (y : M) ≤ _root_.Manifold.riemannianEDist I x y
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _hflat0, _hflat1⟩ :=
    _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (lt_of_not_ge hnot) (a := (0 : ℝ)) (b := 1) zero_lt_one
  have hmap : ContMDiff 𝓘(ℝ) I 1 ((Subtype.val : U → M) ∘ γ) :=
    (contMDiff_subtype_val (I := I) (U := U) (n := 1)).comp hγ
  have hbound := _root_.Manifold.riemannianEDist_le_pathELength
    (x := (x : M)) (y := (y : M)) hmap.contMDiffOn
    (by simp only [Function.comp_apply, hγ0])
    (by simp only [Function.comp_apply, hγ1]) zero_le_one
  rw [component_pathELength_subtypeVal g U hγ 0 1] at hbound
  exact (not_lt_of_ge hbound) hlen

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.component_edistOf_ambient_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.component_edistOf_ambient_le target :: scope.openDecls } }

variable [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_restrictOpen_connCompOpen
    (g : SmoothRiemannianMetric I M) (p : M)
    (x y : connectedComponentOpen (I := I) p) :
    riemannianEDistOf (g.restrictOpen (connectedComponentOpen (I := I) p)) x y =
      riemannianEDistOf g (x : M) (y : M) := by
  apply le_antisymm
  · let C := connectedComponentOpen (I := I) p
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : C → Type _) :=
      ⟨(g.restrictOpen C).toRiemannianMetric⟩
    change _root_.Manifold.riemannianEDist I x y ≤ _root_.Manifold.riemannianEDist I (x : M) (y : M)
    by_contra hnot
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, _hflat0, _hflat1⟩ :=
      _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
        (lt_of_not_ge hnot) (a := (0 : ℝ)) (b := 1) zero_lt_one
    have hmem : ∀ t, γ t ∈ C :=
      component_range_subset hγ.continuous x.property hγ0
    let γC : ℝ → C := fun t => ⟨γ t, hmem t⟩
    have hγC : ContMDiff 𝓘(ℝ) I 1 γC := component_codRestrict_c1 C hγ hmem
    have hγC0 : γC 0 = x := Subtype.ext hγ0
    have hγC1 : γC 1 = y := Subtype.ext hγ1
    have hbound := _root_.Manifold.riemannianEDist_le_pathELength hγC.contMDiffOn
      hγC0 hγC1 zero_le_one
    have hlength : _root_.Manifold.pathELength I γ 0 1 = _root_.Manifold.pathELength I γC 0 1 := by
      simpa only [γC, Function.comp_def] using
        component_pathELength_subtypeVal g C hγC 0 1
    rw [← hlength] at hbound
    exact (not_lt_of_ge hbound) hlen
  · exact component_edistOf_ambient_le g (connectedComponentOpen (I := I) p) x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_restrictOpen_connCompOpen

omit [FiniteDimensional ℝ E] [T2Space M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edistOf_ball_subset_connCompOpen
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    {y : M | riemannianEDistOf g p y < ENNReal.ofReal r} ⊆
      (connectedComponentOpen (I := I) p : Set M) := by
  intro y hy
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change _root_.Manifold.riemannianEDist I p y < ENNReal.ofReal r at hy
  obtain ⟨γ, hγ0, hγ1, hγ, _hlen, _hflat0, _hflat1⟩ :=
    _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy
      (a := (0 : ℝ)) (b := 1) zero_lt_one
  have hyC := component_range_subset hγ.continuous
    (p := p) mem_connectedComponent hγ0 1
  change y ∈ connectedComponent p
  simpa only [hγ1] using hyC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen ``Submission.DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen

variable [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private local instance componentSigmaCompact (p : M) :
    SigmaCompactSpace (connectedComponentOpen (I := I) p) :=
  (isClosed_connectedComponent (x := p)).sigmaCompactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.componentSigmaCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.componentSigmaCompact target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetricComplete_restrictOpen_connCompOpen
    (g : SmoothRiemannianMetric I M) (p : M)
    (hg : RiemannianMetricComplete g) :
    RiemannianMetricComplete (g.restrictOpen (connectedComponentOpen (I := I) p)) := by
  let C := connectedComponentOpen (I := I) p
  let gC : SmoothRiemannianMetric I C := g.restrictOpen C
  let : IsManifold I 1 C :=
    IsManifold.of_le (I := I) (M := C) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : _root_.TopologicalSpace.MetrizableSpace C := Manifold.metrizableSpace I C
  let : T3Space C := inferInstance
  change RiemannianMetricComplete gC
  refine ⟨?_⟩
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : C → Type _) :=
    ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace C := EMetricSpace.ofRiemannianMetric I C
  refine EMetric.complete_of_cauchySeq_tendsto (α := C) fun u hu => ?_
  have huC : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf gC (u m) (u n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change _root_.EDist.edist (u m) (u n) < ε
    exact hN m hm n hn
  change ∃ z : C, _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 z)
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : _root_.TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have huM : CauchySeq (fun n => (u n : M)) := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := huC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf g (u m : M) (u n : M) < ε
    rw [← edistOf_restrictOpen_connCompOpen g p (u m) (u n)]
    exact hN m hm n hn)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete huM
  have hzC : z ∈ C := by
    change z ∈ connectedComponent p
    exact (isClosed_connectedComponent (x := p)).mem_of_tendsto hz
      (Eventually.of_forall fun n => (u n).property)
  exact ⟨⟨z, hzC⟩, tendsto_subtype_rng.mpr hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen ``Submission.DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen

end ActualMetricNorm

end DifferentialGeometry.Geometry.Metric

end
