import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleCenters
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNegativeScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance regularRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingComplete target :: scope.openDecls } }

private local instance regularRescalingTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingTopology target :: scope.openDecls } }
private local instance regularRescalingCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingCharted target :: scope.openDecls } }
private local instance regularRescalingSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingSmooth target :: scope.openDecls } }
private local instance regularRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingSigma target :: scope.openDecls } }
private local instance regularRescalingT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.regularRescalingT2 target :: scope.openDecls } }

theorem exists_eventually_curvatureNormalizedFlow_with_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b : ℝ} (hb : b < 0) {t : ℝ} (ht : t ≤ b) (x : F.M)
    (hx : normSq0S (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≠ 0)
    (tau : ℕ → ℝ) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    let hbmem : b ∈ D.carrier := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hb.le
    ∃ q : ℕ → F.M, ∀ᶠ i in _root_.Filter.atTop, ∃ hsigma : 0 < tau i + b,
      redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
      IsAncientKappaSolution kappa
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)) ∧
      (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
        b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)).S.base.metric (-1) =
        scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hsigma) (F.S.base.metric (-tau i)) := by
  dsimp only
  obtain ⟨q, hq⟩ :=
    exists_eventually_redLength_le_half_finrank_of_ancient_of_neg F hF p hb tau hescape
  refine ⟨q, ?_⟩
  filter_upwards [hq] with i hi
  refine ⟨hi.1, hi.2, ?_, ?_⟩
  · exact isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
      F hF b (tau i + b)⁻¹ (inv_pos.mpr hi.1)
      (by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hb.le) (q i) ht x hx
  · change scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hi.1)
      (F.S.base.metric (parabolicTime b (tau i + b)⁻¹ (-1))) = _
    have htime : parabolicTime b (tau i + b)⁻¹ (-1) = -tau i := by
      simp only [parabolicTime, div_inv_eq_mul, neg_one_mul]
      ring
    rw [htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_curvatureNormalizedFlow_with_redLength_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_curvatureNormalizedFlow_with_redLength_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_curvatureNormalizedFlow_with_redLength_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_curvatureNormalizedFlow_with_redLength_bound

theorem exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ D.carrier) (q : ℕ → F.M),
      ∀ᶠ i in _root_.Filter.atTop, ∃ hsigma : 0 < tau i + b,
        redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
        IsAncientKappaSolution kappa
          (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
            b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)) ∧
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i)).S.base.metric (-1) =
          scaleMetric (tau i + b)⁻¹ (inv_pos.mpr hsigma) (F.S.base.metric (-tau i)) := by
  obtain ⟨b, hb, x, hnorm⟩ := exists_neg_time_rmNormSq_ne_zero_of_ancient F hF
  obtain ⟨q, hq⟩ := exists_eventually_curvatureNormalizedFlow_with_redLength_bound
    F hF p hb le_rfl x hnorm tau hescape
  exact ⟨b, hb, by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hb.le, q, hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance tailRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingComplete target :: scope.openDecls } }

private local instance tailRescalingTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingTopology target :: scope.openDecls } }
private local instance tailRescalingCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingCharted target :: scope.openDecls } }
private local instance tailRescalingSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingSmooth target :: scope.openDecls } }
private local instance tailRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingSigma target :: scope.openDecls } }
private local instance tailRescalingT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailRescalingT2 target :: scope.openDecls } }

abbrev poleRescaledFlowSeq
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) : PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow F hcar hreg b (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) hbmem (q i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq

theorem poleRescaledFlowSeq_basepoint
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).basepoint =
      q i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_basepoint

theorem poleRescaledFlowSeq_metric
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (parabolicTime b (tau i + b)⁻¹ s)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric

theorem poleRescaledFlowSeq_metric_neg_one
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric (-1) =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau i)) := by
  rw [poleRescaledFlowSeq_metric]
  have htime : parabolicTime b (tau i + b)⁻¹ (-1) = -tau i := by
    simp only [parabolicTime, div_inv_eq_mul, neg_one_mul]
    ring
  rw [htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric_neg_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric_neg_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleRescaledFlowSeq_metric_neg_one

private theorem exists_poleRescaledFlowSeq_tail_of_eventually
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (b : ℝ) (hbmem : b ∈ D.carrier)
    (tau : ℕ → ℝ) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (q : ℕ → F.M)
    (h : ∀ᶠ i in _root_.Filter.atTop, ∃ hsigma : 0 < tau i + b,
      redLength F.S b p (q i) (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 ∧
      IsAncientKappaSolution kappa
        (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
          b (tau i + b)⁻¹ (inv_pos.mpr hsigma) hbmem (q i))) :
    ∃ (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b),
      StrictMono (fun i : ℕ => i + N) ∧
      _root_.Filter.Tendsto (fun i : ℕ => i + N) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i : ℕ => tau (i + N)) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i : ℕ => tau (i + N) + b) _root_.Filter.atTop _root_.Filter.atTop ∧
      (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      (∀ i, IsAncientKappaSolution kappa
        ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i)) ∧
      ∀ i, ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i).S.base.metric (-1) =
        scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (i + N))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hpos (i : ℕ) : 0 < tau (i + N) + b := by
    obtain ⟨hsigma, _⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hsigma
  have heta : _root_.Filter.Tendsto (fun i : ℕ => i + N) _root_.Filter.atTop atTop := _root_.Filter.tendsto_add_atTop_nat N
  have htau : _root_.Filter.Tendsto (fun i : ℕ => tau (i + N)) _root_.Filter.atTop atTop := hescape.comp heta
  have hsigma : _root_.Filter.Tendsto (fun i : ℕ => tau (i + N) + b) _root_.Filter.atTop atTop := by
    apply tendsto_atTop.mpr
    intro C
    filter_upwards [htau.eventually_ge_atTop (C - b)] with i hi
    linarith
  refine ⟨N, hpos, (fun _ _ hij => Nat.add_lt_add_right hij N), heta, htau, hsigma,
    ?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, hbound, _⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hbound
  · intro i
    obtain ⟨_, _, hancient⟩ := hN (i + N) (Nat.le_add_left N i)
    exact hancient
  · intro i
    exact poleRescaledFlowSeq_metric_neg_one F hF.carrier_eq hF.regular_eq
      b hbmem (fun j => tau (j + N)) (fun j => q (j + N)) hpos i

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_eventually
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_eventually target :: scope.openDecls } }

variable [I.Boundaryless]

theorem exists_poleRescaledFlowSeq_tail_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ D.carrier) (q : ℕ → F.M)
      (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b),
      StrictMono (fun i : ℕ => i + N) ∧
      _root_.Filter.Tendsto (fun i : ℕ => i + N) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i : ℕ => tau (i + N)) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i : ℕ => tau (i + N) + b) _root_.Filter.atTop _root_.Filter.atTop ∧
      (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤
        (Module.finrank ℝ E : ℝ) / 2) ∧
      (∀ i, IsAncientKappaSolution kappa
        ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i)) ∧
      ∀ i, ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma).term i).S.base.metric (-1) =
        scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (i + N))) := by
  obtain ⟨b, hb, hbmem, q, hq⟩ :=
    exists_neg_pole_eventually_curvatureNormalizedFlow_with_redLength_bound F hF p tau hescape
  obtain ⟨N, hsigma, hmono, heta, htau, hsigmaTop, hbound, hancient, hmetric⟩ :=
    exists_poleRescaledFlowSeq_tail_of_eventually F hF p b hbmem tau hescape q
      (hq.mono fun i hi => by
        obtain ⟨hsigma, hbound, hancient, _⟩ := hi
        exact ⟨hsigma, hbound, hancient⟩)
  exact ⟨b, hb, hbmem, q, N, hsigma, hmono, heta, htau, hsigmaTop, hbound, hancient, hmetric⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_poleRescaledFlowSeq_tail_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance endpointRescalingComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingComplete target :: scope.openDecls } }

private local instance endpointRescalingTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingTopology target :: scope.openDecls } }
private local instance endpointRescalingCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingCharted target :: scope.openDecls } }
private local instance endpointRescalingSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingSmooth target :: scope.openDecls } }
private local instance endpointRescalingSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingSigma target :: scope.openDecls } }
private local instance endpointRescalingT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescalingT2 target :: scope.openDecls } }

private theorem endpointRescaling_time_mem
    (hcar : D.carrier = _root_.Set.Iic 0) {b tau : ℝ} (hbmem : b ∈ D.carrier)
    (hsigma : 0 < tau + b) : -tau ∈ D.carrier := by
  have hb : b ≤ 0 := by simpa only [hcar, _root_.Set.mem_Iic] using hbmem
  rw [hcar]
  change -tau ≤ 0
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescaling_time_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescaling_time_mem target :: scope.openDecls } }

abbrev poleEndpointRescaledFlowSeq
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) : PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow F hcar hreg (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i)) (q i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq

theorem poleEndpointRescaledFlowSeq_basepoint
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).basepoint =
      q i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_basepoint

theorem poleEndpointRescaledFlowSeq_metric
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (-tau i + (tau i + b) * s)) := by
  change scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
    (F.S.base.metric (parabolicTime (-tau i) (tau i + b)⁻¹ s)) = _
  simp only [parabolicTime, div_inv_eq_mul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric

theorem poleEndpointRescaledFlowSeq_metric_zero
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric 0 =
      scaleMetric (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau i)) := by
  rw [poleEndpointRescaledFlowSeq_metric]
  simp only [_root_.MulZeroClass.mul_zero, add_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_zero

theorem poleEndpointRescaledFlowSeq_metric_eq_shift
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric s =
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S.base.metric
        (s - 1) := by
  rw [poleEndpointRescaledFlowSeq_metric, poleRescaledFlowSeq_metric]
  have htime : -tau i + (tau i + b) * s = parabolicTime b (tau i + b)⁻¹ (s - 1) := by
    simp only [parabolicTime, div_inv_eq_mul]
    ring
  rw [htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_eq_shift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_eq_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_eq_shift ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_metric_eq_shift

private theorem endpointRescaling_parabolicTime_mem
    (hcar : D.carrier = _root_.Set.Iic 0) {b tau s : ℝ} (hbmem : b ∈ D.carrier)
    (hsigma : 0 < tau + b) (hs : s ≤ 0) :
    parabolicTime (-tau) (tau + b)⁻¹ s ∈ D.carrier := by
  have htime : -tau ≤ 0 := by
    simpa only [hcar, _root_.Set.mem_Iic] using endpointRescaling_time_mem hcar hbmem hsigma
  rw [hcar]
  exact parabolicTime_nonpos htime (inv_pos.mpr hsigma) hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescaling_parabolicTime_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.endpointRescaling_parabolicTime_mem target :: scope.openDecls } }

theorem poleEndpointRescaledFlowSeq_complete
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    (hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (I := I) (F.S.base.metric t)) :
    FlowMetricComplete (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma) := by
  constructor
  intro i s hs
  have hsource : RiemannianMetricComplete (I := I)
      (F.S.base.metric (parabolicTime (-tau i) (tau i + b)⁻¹ s)) :=
    hcomplete _ (endpointRescaling_parabolicTime_mem hcar hbmem (hsigma i) hs)
  exact (curvatureNormalizedSolution_complete F.S (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i)) s
    hsource).complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_complete

theorem poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    (hcurv : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator F t)
    (i : ℕ) {s : ℝ} (hs : s ≤ 0) :
    PointedFlowNonnegativeCurvatureOperator
      ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i) s :=
  curvatureNormalizedFlow_nonnegativeCurvatureOperator F hcar hreg
    (-tau i) (tau i + b)⁻¹ (inv_pos.mpr (hsigma i))
    (endpointRescaling_time_mem hcar hbmem (hsigma i)) (q i) s
    (hcurv _ (endpointRescaling_parabolicTime_mem hcar hbmem (hsigma i) hs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator


theorem poleEndpointRescaledFlowSeq_noncollapsed
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (kappa : ℝ)
    (hnc : PointedFlowNoncollapsedAllScales F kappa) (i : ℕ) :
    PointedFlowNoncollapsedAllScales
      ((poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i) kappa := by
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  exact curvatureNormalizedSolution_noncollapsed F.S hcar (-tau i) (tau i + b)⁻¹
    (inv_pos.mpr (hsigma i)) (endpointRescaling_time_mem hcar hbmem (hsigma i))
    kappa hnc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.poleEndpointRescaledFlowSeq_noncollapsed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
