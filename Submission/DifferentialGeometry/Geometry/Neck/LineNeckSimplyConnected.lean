import Submission.DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.IntrinsicLine
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Geometry.Metric.Product
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Metric.Completeness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.ContinuousMap

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace Sphere)
open _root_.TopologicalSpace (Opens)

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [ConnectedSpace N] [SigmaCompactSpace N]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
private def diffeomorphOfOpensEq {U₁ U₂ : _root_.TopologicalSpace.Opens M} (h : U₁ = U₂) : U₁ ≃ₘ⟮I3, I3⟯ U₂ :=
  h ▸ Diffeomorph.refl I3 U₁ ∞

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diffeomorphOfOpensEq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diffeomorphOfOpensEq target :: scope.openDecls } }

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem diffeomorphOfOpensEq_val {U₁ U₂ : _root_.TopologicalSpace.Opens M} (h : U₁ = U₂) (x : U₁) :
    ((diffeomorphOfOpensEq h x : U₂) : M) = x := by
  subst h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diffeomorphOfOpensEq_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.diffeomorphOfOpensEq_val target :: scope.openDecls } }

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem mfderiv_diffeomorphOfOpensEq {U₁ U₂ : _root_.TopologicalSpace.Opens M} (h : U₁ = U₂) (x : U₁)
    (v : TangentSpace I3 x) : mfderiv I3 I3 (diffeomorphOfOpensEq h) x v = v := by
  subst h
  change mfderiv I3 I3 (Diffeomorph.refl I3 U₁ ∞) x v = v
  rw [Diffeomorph.coe_refl, mfderiv_id]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mfderiv_diffeomorphOfOpensEq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.mfderiv_diffeomorphOfOpensEq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem SpatialNeck.exists_diffeomorph_sphere_of_product_structure
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (heps : eps ≤ 1 / 1000) (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (Phi : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ M)
    (hemetric : Diffeomorph.pullbackMetricCross g Phi = h.prod (euclideanMetric (E := ℝ))) :
    Nonempty (N ≃ₘ⟮J, I2⟯ Sphere 2) := by
  let O : _root_.TopologicalSpace.Opens (N × ℝ) := ⟨Set.univ, isOpen_univ⟩
  let VO : _root_.TopologicalSpace.Opens M := ⟨Set.univ, isOpen_univ⟩
  have hOsrc : (O : Set (N × ℝ)) ⊆ Phi.toPartialDiffeomorph.source := Set.subset_univ _
  let d₁ := PartialDiffeomorph.toOpensDiffeo Phi.toPartialDiffeomorph hOsrc
  have himgO : (⟨(Phi.toPartialDiffeomorph : N × ℝ → M) '' (O : Set (N × ℝ)),
      image_opens_isOpen Phi.toPartialDiffeomorph hOsrc⟩ : _root_.TopologicalSpace.Opens M) = VO := by
    apply Opens.ext
    change (Phi : N × ℝ → M) '' _root_.Set.univ = _root_.Set.univ
    rw [_root_.Set.image_univ]
    exact Phi.surjective.range_eq
  let ι : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ VO := d₁.trans (diffeomorphOfOpensEq himgO)
  have hιval : ∀ o : O, ((ι o : VO) : M) = Phi o.val := by
    intro o
    change ((diffeomorphOfOpensEq himgO (d₁ o) : VO) : M) = Phi o.val
    rw [diffeomorphOfOpensEq_val]
    rfl
  have hιmfd : ∀ (o : O) (v : TangentSpace (J.prod 𝓘(ℝ)) o),
      mfderiv (J.prod 𝓘(ℝ)) I3 ι o v = mfderiv (J.prod 𝓘(ℝ)) I3 Phi o.val v := by
    intro o v
    have hcomp : mfderiv (J.prod 𝓘(ℝ)) I3 ι o v =
        mfderiv I3 I3 (diffeomorphOfOpensEq himgO) (d₁ o)
          (mfderiv (J.prod 𝓘(ℝ)) I3 d₁ o v) := by
      have h1 := mfderiv_comp o ((diffeomorphOfOpensEq himgO).mdifferentiable (by decide) (d₁ o))
        (d₁.mdifferentiable (by decide) o)
      rw [show ((diffeomorphOfOpensEq himgO) ∘ d₁ : O → VO) = ι from
        (Diffeomorph.coe_trans d₁ (diffeomorphOfOpensEq himgO)).symm] at h1
      exact DFunLike.congr_fun h1 v
    rw [hcomp, mfderiv_diffeomorphOfOpensEq, PartialDiffeomorph.mfderiv_toOpensDiffeo]
    rfl
  have hpull : Diffeomorph.pullbackMetricCross (g.restrictOpen VO) ι =
      (h.prod (euclideanMetric (E := ℝ))).restrictOpen O := by
    apply SmoothRiemannianMetric.ext_inner
    intro o v w
    rw [Diffeomorph.pullbackMetricCross_inner (g.restrictOpen VO) ι,
      SmoothRiemannianMetric.restrictOpen_inner (h.prod (euclideanMetric (E := ℝ))) O,
      ← hemetric]
    refine Eq.trans ?_ (Diffeomorph.pullbackMetricCross_inner g Phi o.val v w).symm
    rw [SmoothRiemannianMetric.restrictOpen_inner, hιmfd, hιmfd]
    exact congrArg (fun q => g.inner q (mfderiv (J.prod 𝓘(ℝ)) I3 Phi o.val v)
      (mfderiv (J.prod 𝓘(ℝ)) I3 Phi o.val w)) (hιval o)
  have heps0 : 0 < eps := nk.eps_pos
  have hs : (0 : ℝ) ∈ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr heps0), inv_pos.mpr heps0⟩
  obtain ⟨ψ, -, -, -⟩ := nk.exists_diffeomorph_graph_in_product_chart heps hs h hdim O VO ι
    (fun _ => Set.mem_univ _) (η := 0) (by norm_num) (by simpa using nk.Q_pos)
    (fun y _ m _ => by simp only [hpull, metricDerivNorm_self, le_refl])
  exact ⟨ψ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_sphere_of_product_structure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_sphere_of_product_structure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_sphere_of_product_structure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_diffeomorph_sphere_of_product_structure

section LineNotCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X] [IsManifold I ∞ X] [T2Space X]
  [ConnectedSpace X]

theorem not_compactSpace_of_line (g : SmoothRiemannianMetric I X) {gamma : ℝ → X}
    (hline : ∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) :
    ¬ CompactSpace X := by
  intro hc
  obtain ⟨w₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn _root_.Set.univ_nonempty
    (Geometry.Riemannian.continuous_riemannianEDist g (gamma 0)).continuousOn
  have hfin : riemannianEDistOf g (gamma 0) w₀ ≠ ⊤ := riemannianEDistOf_ne_top g _ _
  set D := (riemannianEDistOf g (gamma 0) w₀).toReal with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have h1 : riemannianEDistOf g (gamma 0) (gamma (D + 1)) ≤ riemannianEDistOf g (gamma 0) w₀ :=
    hmax (_root_.Set.mem_univ (gamma (D + 1)))
  have h2 : riemannianEDistOf g (gamma 0) (gamma (D + 1)) = ENNReal.ofReal (D + 1) := by
    rw [hline, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  have h3 : riemannianEDistOf g (gamma 0) w₀ = ENNReal.ofReal D := by
    rw [hD, ENNReal.ofReal_toReal hfin]
  have h4 : ENNReal.ofReal (D + 1) ≤ ENNReal.ofReal D := by
    rw [← h2, ← h3]
    exact h1
  have h5 : D + 1 ≤ D := (ENNReal.ofReal_le_ofReal_iff hD0).mp h4
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_compactSpace_of_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_compactSpace_of_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_compactSpace_of_line ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_compactSpace_of_line

end LineNotCompact

theorem SpatialNeck.simplyConnectedSpace_of_line [ConnectedSpace M]
    (g : SmoothRiemannianMetric I3 M) (hg : RiemannianMetricComplete g)
    (hRic : ∀ (x : M) (v : TangentSpace I3 x), 0 ≤ ricciTensor g x v v)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    {eps : ℝ} {p : M} (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000) :
    SimplyConnectedSpace M := by
  obtain ⟨V, hV, N, topN, chartsN, smoothN, t2N, sigmaN, connN, h, -, Phi, hinner, -⟩ :=
    Geometry.Topology.cheeger_gromoll_splitting g hg hRic hline
  let _ : TopologicalSpace N := topN
  let _ : ChartedSpace V N := chartsN
  let _ : IsManifold 𝓘(ℝ, V) ∞ N := smoothN
  let _ : T2Space N := t2N
  let _ : SigmaCompactSpace N := sigmaN
  let _ : ConnectedSpace N := connN
  have hdimV : Module.finrank ℝ V = 2 := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    omega
  have hemetric : Diffeomorph.pullbackMetricCross g Phi = h.prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner g Phi, SmoothRiemannianMetric.prod_inner]
    refine (hinner x.1 v.1 w.1 x.2 v.2 w.2).trans ?_
    change h.inner x.1 v.1 w.1 + v.2 * w.2 = h.inner x.1 v.1 w.1 + _root_.Inner.inner ℝ v.2 w.2
    rw [RCLike.inner_apply, RCLike.conj_to_real, mul_comm]
  obtain ⟨ψ⟩ := nk.exists_diffeomorph_sphere_of_product_structure heps h hdimV Phi hemetric
  have hS2 : SimplyConnectedSpace (Sphere 2) := Topology.sphereTwoSimplyConnectedSpace
  have hN : SimplyConnectedSpace N := ψ.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  have hNR : SimplyConnectedSpace (N × ℝ) := by
    let e : N × ℝ ≃ₕ N :=
      ((ContinuousMap.HomotopyEquiv.refl N).prodCongr (ContractibleSpace.hequiv_unit ℝ).some).trans
        (Homeomorph.prodUnique N Unit).toHomotopyEquiv
    exact e.simplyConnectedSpace
  exact Phi.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line

theorem SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric [ConnectedSpace M]
    (g : SmoothRiemannianMetric I3 M) (hg : RiemannianMetricComplete g)
    (hRic : ∀ (x : M) (v : TangentSpace I3 x), 0 ≤ ricciTensor g x v v)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    {c : ℝ} (hc : 0 < c) {eps : ℝ} {p : M}
    (nk : SpatialNeck (DifferentialGeometry.scaleMetric c hc g) eps p)
    (heps : eps ≤ 1 / 1000) : SimplyConnectedSpace M := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine nk.simplyConnectedSpace_of_line (DifferentialGeometry.scaleMetric c hc g) ?_ ?_
    (gamma := fun t => gamma (t / Real.sqrt c)) ?_ heps
  · exact RiemannianMetricComplete.of_lower hg hc fun x v =>
      le_of_eq (scaleMetric_inner _ _ _ _ _ _).symm
  · intro x v
    rw [ricciTensor_scaleMetric]
    exact hRic x v
  · intro s t
    rw [edistOf_scale, hline, ← ENNReal.ofReal_mul hsc.le, ← sub_div, abs_div,
      abs_of_pos hsc, mul_div_cancel₀ _ hsc.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
