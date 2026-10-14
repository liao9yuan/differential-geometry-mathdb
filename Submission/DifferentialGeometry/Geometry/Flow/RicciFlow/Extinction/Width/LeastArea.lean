import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ShortFamilyContraction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SpanningArea
import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastArea
import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastAreaWeakBoundary
import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastAreaHomeomorphism
import Submission.DifferentialGeometry.Geometry.Measure.Area.ShortLoopFilling
import Submission.DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Topology.StandardModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe uK

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def competitorAreas (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) : Set ℝ :=
  Set.range (fun u : DiskCompetitor g γ => diskArea g u.1.map)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas

theorem competitorAreas_bddBelow (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) : BddBelow (competitorAreas g γ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, rfl⟩
  exact diskArea_nonneg g u.1.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_bddBelow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_bddBelow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_bddBelow ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_bddBelow

theorem competitorAreas_eq_empty_of_not_isContractibleLoop
    (g : SmoothRiemannianMetric I Q) (γ : Surgery.Topology.ContinuousFreeLoop Q)
    (hγ : ¬ Surgery.Topology.IsContractibleLoop γ) : competitorAreas g γ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨u, rfl⟩
  apply hγ
  have htrace : DifferentialGeometry.Topology.diskTrace u.1.map = γ := by
    ext θ
    exact u.2 θ
  have h := DifferentialGeometry.Topology.diskTrace_nullhomotopic u.1.map
  rw [htrace] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_eq_empty_of_not_isContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_eq_empty_of_not_isContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_eq_empty_of_not_isContractibleLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_eq_empty_of_not_isContractibleLoop


variable [finiteDimensionalE : FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q]

theorem competitorAreas_nonempty (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    (competitorAreas g γ).Nonempty := by
  obtain ⟨u⟩ := rfs_disk_competitor_exists g γ hctr hlip
  exact ⟨diskArea g u.1.map, u, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.competitorAreas_nonempty

def leastArea (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (_hctr : IsContractibleLoop γ) (_hlip : IsLipschitzLoop g γ) : ℝ :=
  _root_.InfSet.sInf (competitorAreas g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea

theorem leastArea_nonneg (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    0 ≤ leastArea g γ hctr hlip := by
  apply le_csInf (competitorAreas_nonempty g γ hctr hlip)
  rintro _ ⟨u, rfl⟩
  exact diskArea_nonneg g u.1.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nonneg

omit finiteDimensionalE boundarylessI t2Q compactQ in
theorem leastArea_le_competitor (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (u : DiskCompetitor g γ) : leastArea g γ hctr hlip ≤ diskArea g u.1.map :=
  csInf_le (competitorAreas_bddBelow g γ) ⟨u, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_competitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_competitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_competitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_competitor


theorem exists_competitor_area_lt (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : DiskCompetitor g γ, diskArea g u.1.map < leastArea g γ hctr hlip + ε := by
  obtain ⟨a, ⟨u, rfl⟩, hu⟩ := exists_lt_of_csInf_lt
    (competitorAreas_nonempty g γ hctr hlip)
    (show _root_.InfSet.sInf (competitorAreas g γ) < leastArea g γ hctr hlip + ε by
      exact lt_add_of_pos_right _ hε)
  exact ⟨u, hu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_competitor_area_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_competitor_area_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_competitor_area_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_competitor_area_lt

theorem leastArea_const (g : SmoothRiemannianMetric I Q) (q : Q) :
    leastArea g (constantLoops q) (isContractibleLoop_constant q)
      (isLipschitzLoop_constant g q) = 0 := by
  apply le_antisymm
  · exact (leastArea_le_competitor g (constantLoops q) (isContractibleLoop_constant q)
      (isLipschitzLoop_constant g q) (constantDiskCompetitor g q)).trans_eq (diskArea_const g q)
  · exact leastArea_nonneg _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_const


def regularLeastArea (g : SmoothRiemannianMetric I Q)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) : ℝ :=
  leastArea g γ.1.toContinuousLoop γ.2 (γ.1.isLipschitz g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea

theorem regularLeastArea_nonneg (g : SmoothRiemannianMetric I Q)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) : 0 ≤ regularLeastArea g γ :=
  leastArea_nonneg _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_nonneg

theorem leastArea_le_add_of_disk_attachment (g : SmoothRiemannianMetric I Q)
    (γ₀ γ₁ : ContinuousFreeLoop Q)
    (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
    (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁)
    (A : LipschitzAnnulus g)
    (hattach : ∀ u : DiskCompetitor g γ₀, ∃ v : DiskCompetitor g γ₁,
      diskArea g v.1.map = diskArea g u.1.map + annulusArea g A.map) :
    leastArea g γ₁ hctr₁ hlip₁ ≤ leastArea g γ₀ hctr₀ hlip₀ + annulusArea g A.map := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu⟩ := exists_competitor_area_lt g γ₀ hctr₀ hlip₀ hε
  obtain ⟨v, hv⟩ := hattach u
  have hvle := leastArea_le_competitor g γ₁ hctr₁ hlip₁ v
  rw [hv] at hvle
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_add_of_disk_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_add_of_disk_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_add_of_disk_attachment ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_le_add_of_disk_attachment

omit finiteDimensionalE boundarylessI t2Q compactQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem parametricJacobian_eq_riemannianAreaDensity (g : SmoothRiemannianMetric I Q)
    (U : ℂ → Q) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    parametricJacobian g U (Metric.closedBall (0 : ℂ) 1) z =
      Geometry.riemannianAreaDensity g U z := by
  have hs : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) I U z
  · have hw : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      hd.mdifferentiableWithinAt
    rw [parametricJacobian, if_pos hw, mfderivWithin_of_mem_nhds (f := U) hs]
    have h0 : diskBasis (0 : Fin 2) = (1 : ℂ) := by simp [diskBasis]
    have h1 : diskBasis (1 : Fin 2) = Complex.I := by simp [diskBasis]
    rw [Matrix.det_fin_two, Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian]
    simp only [h0, h1]
    rw [g.symm (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I)
      (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))]
    ring_nf
  · have hw : ¬ MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      fun h => hd (h.mdifferentiableAt hs)
    rw [parametricJacobian, if_neg hw,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.parametricJacobian_eq_riemannianAreaDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.parametricJacobian_eq_riemannianAreaDensity target :: scope.openDecls } }

omit finiteDimensionalE boundarylessI t2Q compactQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem diskArea_eq_riemannianDiskArea (g : SmoothRiemannianMetric I Q) (u : Disk → Q) :
    diskArea g u = Geometry.riemannianDiskArea g u := by
  simp only [diskArea, diskJacobian, Geometry.riemannianDiskArea, Geometry.riemannianArea]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  refine (parametricJacobian_congr_on (s := Metric.closedBall (0 : ℂ) 1) g ?_
    (Metric.ball_subset_closedBall hz)).trans
    (parametricJacobian_eq_riemannianAreaDensity g (Geometry.diskExtension u) z hz)
  intro w hw
  simp only [diskExtension, dif_pos hw, Geometry.diskExtension, Function.comp_apply]
  rw [Geometry.diskRetraction_coe ⟨w, hw⟩]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea target :: scope.openDecls } }

section Pullback

variable {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [t2A : T2Space A]

omit boundarylessI t2Q compactQ in
private theorem riemannianAreaDensity_pullbackMetricCross (g : SmoothRiemannianMetric I Q)
    (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (U : ℂ → A) (z : ℂ) :
    Geometry.riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      Geometry.riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z =
        (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross target :: scope.openDecls } }

omit boundarylessI t2Q compactQ in
private theorem riemannianDiskArea_pullbackMetricCross (g : SmoothRiemannianMetric I Q)
    (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    Geometry.riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) u =
      Geometry.riemannianDiskArea g (fun z => Ψ (u z)) := by
  rw [Geometry.riemannianDiskArea, Geometry.riemannianDiskArea]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  rw [riemannianAreaDensity_pullbackMetricCross]
  refine Geometry.riemannianAreaDensity_congr g ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [Geometry.diskExtension, Function.comp_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross target :: scope.openDecls } }

omit finiteDimensionalE t2Q t2A in
private theorem mem_spanningDiskCompetitors_iff (g : SmoothRiemannianMetric 𝓘(ℝ, E) A)
    (γ : C(DifferentialGeometry.Topology.loopCircle, A))
    (u : C(DifferentialGeometry.Topology.closedDisk, A)) :
    u ∈ Geometry.spanningDiskCompetitors g γ ↔
      (∀ θ : Surgery.Topology.Circle, u (diskBoundary θ) = γ θ) ∧
        ∃ L : ℝ≥0, ∀ z w : Disk,
          riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w := by
  rw [Geometry.spanningDiskCompetitors, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun θ => ?_, h.2⟩
    exact congrFun (congrArg DFunLike.coe h.1) θ
  · rintro ⟨h1, h2⟩
    refine ⟨ContinuousMap.ext fun θ => ?_, h2⟩
    exact h1 θ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_iff target :: scope.openDecls } }

end Pullback

abbrev standardModelLoop (c : Geometry.Topology.StandardModelCopy I Q E)
    (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    Geometry.lipschitzContractibleLoop (Diffeomorph.pullbackMetricCross g c.equiv.symm) :=
  ⟨⟨Surgery.Topology.loopPostcompose (⟨c.equiv, c.equiv.continuous⟩ : C(Q, c.Q)) γ,
      hctr.postcompose (⟨c.equiv, c.equiv.continuous⟩ : C(Q, c.Q))⟩, by
    obtain ⟨L, hL⟩ := hlip
    refine ⟨L, fun x y => ?_⟩
    rw [Geometry.Metric.edistOf_pullbackMetricCross]
    simpa only [Surgery.Topology.loopPostcompose_apply, ContinuousMap.coe_mk,
      Diffeomorph.symm_apply_apply] using hL x y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.standardModelLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.standardModelLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.standardModelLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.standardModelLoop

omit boundarylessI compactQ in
private theorem leastArea_eq_leastSpanningArea_standardModelCopy
    (c : Geometry.Topology.StandardModelCopy I Q E)
    (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea g γ hctr hlip =
      Geometry.leastSpanningArea (Diffeomorph.pullbackMetricCross g c.equiv.symm)
        (standardModelLoop c g γ hctr hlip) := by
  let Φc : C(Q, c.Q) := ⟨c.equiv, c.equiv.continuous⟩
  have hset : competitorAreas g γ
      = Geometry.spanningDiskAreas (Diffeomorph.pullbackMetricCross g c.equiv.symm)
          (standardModelLoop c g γ hctr hlip) := by
    ext a
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Φc.comp u.1.map, ?_, ?_⟩
      · rw [mem_spanningDiskCompetitors_iff]
        refine ⟨fun θ => ?_, ?_⟩
        · simp only [ContinuousMap.comp_apply, u.2 θ]
          rfl
        · obtain ⟨L, hL⟩ := u.1.isLipschitz
          refine ⟨L, fun z w => ?_⟩
          rw [Geometry.Metric.edistOf_pullbackMetricCross]
          simpa only [Φc, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
            Diffeomorph.symm_apply_apply] using hL z w
      · beta_reduce
        rw [diskArea_eq_riemannianDiskArea g u.1.map]
        refine (riemannianDiskArea_pullbackMetricCross g c.equiv.symm
          (Φc.comp u.1.map)).trans ?_
        have harg : (fun z : Disk => c.equiv.symm ((Φc.comp u.1.map) z)) = u.1.map := by
          funext z
          simp only [Φc, ContinuousMap.coe_mk, ContinuousMap.comp_apply]
          exact Diffeomorph.symm_apply_apply c.equiv (u.1.map z)
        rw [harg]
    · rintro ⟨u', hu', rfl⟩
      rw [mem_spanningDiskCompetitors_iff] at hu'
      obtain ⟨htr, L, hL⟩ := hu'
      let vmap : C(Disk, Q) :=
        ⟨fun z => c.equiv.symm (u' z), c.equiv.symm.continuous.comp u'.continuous⟩
      have hv : ∃ L : ℝ≥0, ∀ z w : Disk, riemannianEDistOf g (vmap z) (vmap w)
          ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w := by
        refine ⟨L, fun z w => ?_⟩
        simp only [vmap, ContinuousMap.coe_mk]
        rw [← Geometry.Metric.edistOf_pullbackMetricCross]
        exact hL z w
      refine ⟨⟨⟨vmap, hv⟩, ?_⟩, ?_⟩
      · intro θ
        simp only [vmap, ContinuousMap.coe_mk]
        rw [htr θ]
        exact Diffeomorph.symm_apply_apply c.equiv (γ θ)
      · simp only [vmap, ContinuousMap.coe_mk]
        exact (diskArea_eq_riemannianDiskArea g (fun z => c.equiv.symm (u' z))).trans
          (riemannianDiskArea_pullbackMetricCross g c.equiv.symm u').symm
  rw [leastArea, Geometry.leastSpanningArea, hset]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_leastSpanningArea_standardModelCopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_leastSpanningArea_standardModelCopy target :: scope.openDecls } }

variable [connectedQ : ConnectedSpace Q]


theorem leastArea_nearby_upper_bound (g : SmoothRiemannianMetric I Q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : ContinuousFreeLoop Q)
        (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
        (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁),
        loopUniformDistance g γ₀ γ₁ < ρ →
        leastArea g γ₁ hctr₁ hlip₁ ≤ leastArea g γ₀ hctr₀ hlip₀ +
          C * loopUniformDistance g γ₀ γ₁ * (loopLength g γ₀ + loopLength g γ₁) := by
  obtain ⟨ρ, C, hρ, hC, hA⟩ := rfs_nearby_loop_annulus g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  obtain ⟨A, _, _, _, harea, hattach⟩ := hA γ₀ γ₁ hlip₀ hlip₁ hnear
  exact (leastArea_le_add_of_disk_attachment g γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ A
    hattach).trans (add_le_add le_rfl harea)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_upper_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_upper_bound

theorem leastArea_nearby_abs_bound (g : SmoothRiemannianMetric I Q) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (γ₀ γ₁ : ContinuousFreeLoop Q)
        (hctr₀ : IsContractibleLoop γ₀) (hctr₁ : IsContractibleLoop γ₁)
        (hlip₀ : IsLipschitzLoop g γ₀) (hlip₁ : IsLipschitzLoop g γ₁),
        loopUniformDistance g γ₀ γ₁ < ρ →
        |leastArea g γ₀ hctr₀ hlip₀ - leastArea g γ₁ hctr₁ hlip₁| ≤
          C * loopUniformDistance g γ₀ γ₁ * (loopLength g γ₀ + loopLength g γ₁) := by
  obtain ⟨ρ, C, hρ, hC, hbound⟩ := leastArea_nearby_upper_bound g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  have h₁ := hbound γ₀ γ₁ hctr₀ hctr₁ hlip₀ hlip₁ hnear
  have hnear' : loopUniformDistance g γ₁ γ₀ < ρ := by
    rwa [loopUniformDistance_comm]
  have h₀ := hbound γ₁ γ₀ hctr₁ hctr₀ hlip₁ hlip₀ hnear'
  rw [loopUniformDistance_comm, add_comm (loopLength g γ₁)] at h₀
  exact abs_le.mpr ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_abs_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_abs_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_abs_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_nearby_abs_bound





theorem edist_proj_le (x y : ℝ) :
    edist ((x : Surgery.Topology.Circle)) ((y : Surgery.Topology.Circle)) ≤ _root_.EDist.edist x y := by
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← AddCircle.coe_sub]
  exact ENNReal.ofReal_le_ofReal QuotientAddGroup.norm_mk_le_norm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_proj_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_proj_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_proj_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_proj_le

theorem riemannianCurveLength_pullbackMetricCross
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (γ : ℝ → A) (a b : ℝ) :
    Surgery.Topology.riemannianCurveLength (Diffeomorph.pullbackMetricCross g Ψ) γ a b =
      Surgery.Topology.riemannianCurveLength g (fun t => Ψ (γ t)) a b := by
  unfold Surgery.Topology.riemannianCurveLength
  refine congrArg _root_.SupSet.sSup (congrArg Set.range (funext fun p => ?_))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DifferentialGeometry.riemannianEDistOf_pullbackMetricCross]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianCurveLength_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianCurveLength_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianCurveLength_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianCurveLength_pullbackMetricCross

theorem loopLength_eq_riemannianCurveLength_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
    [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : ContinuousFreeLoop Q)
    (hlip : IsLipschitzLoop g γ) :
    loopLength g γ = Geometry.riemannianCurveLength g (loopLift γ) 0 1 := by
  have hb : ∀ x y : ℝ, riemannianEDistOf g (loopLift γ x) (loopLift γ y) ≤
      ((hlip.choose : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist x y := by
    intro x y
    have h := hlip.choose_spec (x : Surgery.Topology.Circle) (y : Surgery.Topology.Circle)
    simp only [loopLift] at h ⊢
    exact h.trans (mul_le_mul' le_rfl (edist_proj_le x y))
  rw [Geometry.riemannianCurveLength_eq_integral g hb 0 1]
  simp only [loopLength, Geometry.riemannianCurveSpeed, loopVelocity, loopLift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_eq_riemannianCurveLength_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_eq_riemannianCurveLength_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_eq_riemannianCurveLength_real ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_eq_riemannianCurveLength_real

theorem loopLength_pullbackMetricCross
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
    [T2Space A] [CompactSpace A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (γ : ContinuousFreeLoop A)
    (hlip : IsLipschitzLoop (Diffeomorph.pullbackMetricCross g Ψ) γ)
    (hlip' : IsLipschitzLoop g ((⟨Ψ, Ψ.continuous⟩ : C(A, Q)).comp γ)) :
    loopLength (Diffeomorph.pullbackMetricCross g Ψ) γ =
      loopLength g ((⟨Ψ, Ψ.continuous⟩ : C(A, Q)).comp γ) := by
  have h₁ := loopLength_eq_riemannianCurveLength (Diffeomorph.pullbackMetricCross g Ψ) γ hlip
  have h₂ := loopLength_eq_riemannianCurveLength g ((⟨Ψ, Ψ.continuous⟩ : C(A, Q)).comp γ) hlip'
  rw [riemannianCurveLength_pullbackMetricCross g Ψ (loopLift γ) 0 1] at h₁
  exact ENNReal.ofReal_eq_ofReal_iff (loopLength_nonneg _ _) (loopLength_nonneg _ _) |>.mp
    (h₁.trans h₂.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.loopLength_pullbackMetricCross




private theorem areaDensity_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (U : ℂ → A) (z : ℂ) :
    Geometry.riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      Geometry.riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z =
        (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv 𝓘(ℝ, E) I (Ψ : A → Q) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.areaDensity_pullbackDiffeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.areaDensity_pullbackDiffeo target :: scope.openDecls } }

private theorem riemannianDiskArea_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    Geometry.riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) u =
      Geometry.riemannianDiskArea g (fun z => Ψ (u z)) := by
  rw [Geometry.riemannianDiskArea, Geometry.riemannianDiskArea]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  rw [areaDensity_pullbackDiffeo]
  refine Geometry.riemannianAreaDensity_congr g ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [Geometry.diskExtension, Function.comp_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackDiffeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackDiffeo target :: scope.openDecls } }

theorem diskArea_pullbackDiffeo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Ψ : A ≃ₘ⟮𝓘(ℝ, E), I⟯ Q) (u : Disk → A) :
    diskArea (Diffeomorph.pullbackMetricCross g Ψ) u = diskArea g (fun z => Ψ (u z)) := by
  rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea,
    riemannianDiskArea_pullbackDiffeo]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackDiffeo ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackDiffeo




theorem short_loop_disk_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [I.Boundaryless] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q]
    (g : SmoothRiemannianMetric I Q) :
    ∃ σ K : ℝ, 0 < σ ∧ 0 ≤ K ∧
      ∀ (γ : ContinuousFreeLoop Q), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K * loopLength g γ ^ 2 := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  let Ψ : c.Q ≃ₘ⟮𝓘(ℝ, E), I⟯ Q := c.equiv.symm
  let g' : SmoothRiemannianMetric 𝓘(ℝ, E) c.Q := Diffeomorph.pullbackMetricCross g Ψ
  obtain ⟨σ₀, K₀, hσ₀, hK₀, hfill⟩ := Geometry.exists_short_loop_filling_bound g'
  refine ⟨(σ₀ : ℝ), (K₀ : ℝ), hσ₀, K₀.coe_nonneg, ?_⟩
  intro γ hlip hshort
  let Φc : C(Q, c.Q) := ⟨c.equiv, c.equiv.continuous⟩
  let γ' : ContinuousFreeLoop c.Q := Φc.comp γ
  have hΨγ : ∀ θ, Ψ (γ' θ) = γ θ := by
    intro θ
    simp only [γ', Φc, ContinuousMap.comp_apply, ContinuousMap.coe_mk, Ψ]
    exact c.equiv.symm_apply_apply (γ θ)
  have hLip' : ∀ x y, riemannianEDistOf g' (γ' x) (γ' y) ≤
      ((hlip.choose : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist x y := by
    intro x y
    have h := hlip.choose_spec x y
    rw [DifferentialGeometry.riemannianEDistOf_pullbackMetricCross]
    rw [hΨγ x, hΨγ y]
    exact h
  have hlip' : IsLipschitzLoop g' γ' := ⟨hlip.choose, hLip'⟩
  have hγeq : (⟨Ψ, Ψ.continuous⟩ : C(c.Q, Q)).comp γ' = γ :=
    ContinuousMap.ext hΨγ
  have hlen : loopLength g' γ' = loopLength g γ := by
    rw [loopLength_pullbackMetricCross g Ψ γ' hlip' (hγeq ▸ hlip), hγeq]
  have hlen' : Geometry.riemannianCurveLength g' (loopLift γ') 0 1 = loopLength g γ := by
    rw [← loopLength_eq_riemannianCurveLength_real g' γ' hlip', hlen]
  have hshort' : Geometry.riemannianCurveLength g' (loopLift γ') 0 1 < (σ₀ : ℝ) := by
    rw [hlen']; exact hshort
  obtain ⟨u, hu, huarea⟩ := hfill γ' hlip.choose hLip' hshort'
  rw [mem_spanningDiskCompetitors_iff] at hu
  obtain ⟨htr, L, hL⟩ := hu
  refine ⟨⟨⟨⟨fun z => Ψ (u z), Ψ.continuous.comp u.continuous⟩, L, ?_⟩, ?_⟩, ?_⟩
  · intro z w
    have h := hL z w
    rw [DifferentialGeometry.riemannianEDistOf_pullbackMetricCross] at h
    exact h
  · intro θ
    simp only [ContinuousMap.coe_mk]
    rw [htr θ]
    exact hΨγ θ
  · simp only [ContinuousMap.coe_mk]
    calc diskArea g (fun z => Ψ (u z))
        = diskArea g' u := (diskArea_pullbackDiffeo g Ψ u).symm
      _ = Geometry.riemannianDiskArea g' u := diskArea_eq_riemannianDiskArea g' u
      _ ≤ (K₀ : ℝ) * Geometry.riemannianCurveLength g' (loopLift γ') 0 1 ^ 2 := huarea
      _ = (K₀ : ℝ) * loopLength g γ ^ 2 := by rw [hlen']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk_bridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk_bridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk_bridge ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk_bridge









def IsWeaklyMonotoneCircleMap (ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle)) : Prop :=
  ∃ φ : ℝ → ℝ, Continuous φ ∧ Monotone φ ∧
    (∀ t, φ (t + 1) = φ t + 1) ∧
      ∀ t : ℝ, ψ (t : Surgery.Topology.Circle) = (φ t : Surgery.Topology.Circle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsWeaklyMonotoneCircleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsWeaklyMonotoneCircleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsWeaklyMonotoneCircleMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsWeaklyMonotoneCircleMap

theorem isWeaklyMonotoneCircleMap_id :
    IsWeaklyMonotoneCircleMap (ContinuousMap.id Surgery.Topology.Circle) :=
  ⟨id, continuous_id, monotone_id, fun _ => rfl, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isWeaklyMonotoneCircleMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isWeaklyMonotoneCircleMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isWeaklyMonotoneCircleMap_id ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isWeaklyMonotoneCircleMap_id


abbrev WeakDiskCompetitor (g : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q) :=
  {u : LipschitzDisk g // ∃ ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle),
    IsWeaklyMonotoneCircleMap ψ ∧ ∀ θ, u.map (diskBoundary θ) = γ (ψ θ)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.WeakDiskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.WeakDiskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.WeakDiskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.WeakDiskCompetitor

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem rfs_weak_boundary_trace (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (ψ : C(Surgery.Topology.Circle, Surgery.Topology.Circle))
    (hψ : IsWeaklyMonotoneCircleMap ψ)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ψ)) (hlip' : IsLipschitzLoop g (γ.comp ψ)) :
    leastArea g (γ.comp ψ) hctr' hlip' = leastArea g γ hctr hlip := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  obtain ⟨φ, hc, hm, hp, hlift⟩ := hψ
  rw [leastArea_eq_leastSpanningArea_standardModelCopy c g (γ.comp ψ) hctr' hlip',
    leastArea_eq_leastSpanningArea_standardModelCopy c g γ hctr hlip]
  exact Geometry.leastSpanningArea_comp_weak_boundary
    (Diffeomorph.pullbackMetricCross g c.equiv.symm)
    (standardModelLoop c g γ hctr hlip)
    (standardModelLoop c g (γ.comp ψ) hctr' hlip') ψ hc hm hp hlift rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_weak_boundary_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_weak_boundary_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_weak_boundary_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_weak_boundary_trace

theorem leastArea_eq_weak_boundary_infimum (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea g γ hctr hlip =
      sInf (Set.range (fun u : WeakDiskCompetitor g γ => diskArea g u.1.map)) := by
  let S := Set.range (fun u : WeakDiskCompetitor g γ => diskArea g u.1.map)
  have hS : S.Nonempty := by
    obtain ⟨u⟩ := rfs_disk_competitor_exists g γ hctr hlip
    exact ⟨diskArea g u.1.map,
      ⟨u.1, ContinuousMap.id _, isWeaklyMonotoneCircleMap_id, u.2⟩, rfl⟩
  have hb : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact diskArea_nonneg _ _
  apply le_antisymm
  · apply le_csInf hS
    rintro _ ⟨u, rfl⟩
    obtain ⟨ψ, hψ, hu⟩ := u.2
    have hctr' : IsContractibleLoop (γ.comp ψ) := by
      obtain ⟨q, hq⟩ := hctr
      exact ⟨q, hq.comp (ContinuousMap.Homotopic.refl ψ)⟩
    have hlip' := u.1.isLipschitz_trace g (γ.comp ψ) hu
    rw [← rfs_weak_boundary_trace g γ ψ hψ hctr hlip hctr' hlip']
    exact leastArea_le_competitor g (γ.comp ψ) hctr' hlip' ⟨u.1, hu⟩
  · apply le_csInf (competitorAreas_nonempty g γ hctr hlip)
    rintro _ ⟨u, rfl⟩
    exact csInf_le hb ⟨⟨u.1, ContinuousMap.id _, isWeaklyMonotoneCircleMap_id, u.2⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_weak_boundary_infimum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_weak_boundary_infimum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_weak_boundary_infimum ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_eq_weak_boundary_infimum

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem leastArea_circle_homeomorph (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (ψ : Surgery.Topology.Circle ≃ₜ Surgery.Topology.Circle)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ)
    (hctr' : IsContractibleLoop (γ.comp ⟨ψ, ψ.continuous⟩))
    (hlip' : IsLipschitzLoop g (γ.comp ⟨ψ, ψ.continuous⟩)) :
    leastArea g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip' = leastArea g γ hctr hlip := by
  classical
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace c.Q :=
    c.equiv.toHomeomorph.surjective.connectedSpace c.equiv.toHomeomorph.continuous
  have _ : T3Space c.Q := inferInstance
  rw [leastArea_eq_leastSpanningArea_standardModelCopy c g (γ.comp ⟨ψ, ψ.continuous⟩)
      hctr' hlip',
    leastArea_eq_leastSpanningArea_standardModelCopy c g γ hctr hlip]
  exact Geometry.leastSpanningArea_comp_homeomorphism
    (Diffeomorph.pullbackMetricCross g c.equiv.symm)
    (standardModelLoop c g γ hctr hlip)
    (standardModelLoop c g (γ.comp ⟨ψ, ψ.continuous⟩) hctr' hlip') ψ rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_circle_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_circle_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_circle_homeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_circle_homeomorph

omit connectedQ in
theorem leastArea_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ)
    (hlipg : IsLipschitzLoop g γ) (hliph : IsLipschitzLoop h γ) :
    a ^ 2 * leastArea g γ hctr hlipg ≤ leastArea h γ hctr hliph ∧
      leastArea h γ hctr hliph ≤ b ^ 2 * leastArea g γ hctr hlipg := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos (ha.trans_le hab)
  have hback : ∀ q (v : TangentSpace I q),
      g.inner q v v ≤ (a ^ 2)⁻¹ * h.inner q v v := by
    intro q v
    exact (le_inv_mul_iff₀ ha2).mpr (hmetric q v).1
  have hlower : a ^ 2 * leastArea g γ hctr hlipg ≤ leastArea h γ hctr hliph := by
    apply le_csInf (competitorAreas_nonempty h γ hctr hliph)
    rintro _ ⟨u, rfl⟩
    let v : DiskCompetitor g γ :=
      ⟨u.1.changeMetric h g (inv_pos.mpr ha2) hback, u.2⟩
    exact (mul_le_mul_of_nonneg_left (leastArea_le_competitor g γ hctr hlipg v)
      ha2.le).trans (diskArea_metric_comparison g h ha hab hmetric v.1).1
  have hupperDiv : leastArea h γ hctr hliph / b ^ 2 ≤ leastArea g γ hctr hlipg := by
    apply le_csInf (competitorAreas_nonempty g γ hctr hlipg)
    rintro _ ⟨u, rfl⟩
    let v : DiskCompetitor h γ :=
      ⟨u.1.changeMetric g h hb2 (fun q w => (hmetric q w).2), u.2⟩
    apply (div_le_iff₀ hb2).mpr
    have hv := (leastArea_le_competitor h γ hctr hliph v).trans
      (diskArea_metric_comparison g h ha hab hmetric u.1).2
    simpa only [mul_comm] using hv
  refine ⟨hlower, ?_⟩
  simpa only [mul_comm] using (div_le_iff₀ hb2).mp hupperDiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_metric_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_metric_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_metric_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_metric_comparison

omit connectedQ in
theorem regularLeastArea_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) :
    a ^ 2 * regularLeastArea g γ ≤ regularLeastArea h γ ∧
      regularLeastArea h γ ≤ b ^ 2 * regularLeastArea g γ :=
  leastArea_metric_comparison g h ha hab hmetric γ.1.toContinuousLoop γ.2
    (γ.1.isLipschitz g) (γ.1.isLipschitz h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_metric_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_metric_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_metric_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.regularLeastArea_metric_comparison

omit connectedQ in
theorem leastArea_scale (g : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g γ) :
    leastArea (scaleMetric c hc g) γ hctr
      ((isLipschitzLoop_metric_iff g (scaleMetric c hc g) γ).mp hlip) =
      c * leastArea g γ hctr hlip := by
  have hmetric : ∀ q (v : TangentSpace I q),
      (Real.sqrt c) ^ 2 * g.inner q v v ≤ (scaleMetric c hc g).inner q v v ∧
      (scaleMetric c hc g).inner q v v ≤ (Real.sqrt c) ^ 2 * g.inner q v v := by
    intro q v
    simp [Real.sq_sqrt hc.le]
  have h := leastArea_metric_comparison g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (le_refl (Real.sqrt c)) hmetric γ hctr hlip
    ((isLipschitzLoop_metric_iff g (scaleMetric c hc g) γ).mp hlip)
  simpa only [Real.sq_sqrt hc.le] using le_antisymm h.2 h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.leastArea_scale

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem rfs_short_loop_fillings (g : SmoothRiemannianMetric I Q) :
    ∃ σ K₀ : ℝ, 0 < σ ∧ 0 ≤ K₀ ∧
      (∀ (γ : ContinuousFreeLoop Q), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K₀ * loopLength g γ ^ 2) ∧
      (∀ (K : Type uK) [TopologicalSpace K] [CompactSpace K]
        (Γ : RegularFamily (I := I) (Q := Q) K),
        (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
        ∃ F : C(_root_.Set.Icc (0 : ℝ) 1 × K, ContractibleRegularLoop (I := I) (Q := Q)),
          (∀ k, F (⟨0, by simp⟩, k) = Γ k) ∧
          ∀ k, F (⟨1, by simp⟩, k) = constantContractibleRegularLoop ((Γ k).1 0)) ∧
      ((∀ q : Q, Subsingleton (HomotopyGroup (Fin 2) Q q)) →
        ∀ (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)),
          (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
          ∃ q : Q, ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ)
            (ContinuousMap.const (Sphere 2)
              (⟨constantLoops q, isContractibleLoop_constant q⟩ :
                ContractibleContinuousLoop Q))) := by
  obtain ⟨σ₁, K₀, hσ₁, hK₀, hfill⟩ := short_loop_disk_bridge g
  obtain ⟨σ₂, hσ₂, hcontract⟩ :=
    exists_short_regularFamily_contracting_radius (I := I) (Q := Q) g
  obtain ⟨σ₃, hσ₃, hnull⟩ := exists_short_sphere_family_null_radius (I := I) (Q := Q) g
  refine ⟨min σ₁ (_root_.Min.min σ₂ σ₃), K₀, lt_min hσ₁ (lt_min hσ₂ hσ₃), hK₀, ?_, ?_, ?_⟩
  · intro γ hlip hshort
    exact hfill γ hlip (lt_of_lt_of_le hshort (min_le_left _ _))
  · intro K _ _ Γ hshort
    exact hcontract Γ fun k =>
      lt_of_lt_of_le (hshort k) (le_trans (min_le_right _ _) (min_le_left _ _))
  · intro hpi Γ hshort
    exact hnull hpi Γ fun k =>
      lt_of_lt_of_le (hshort k) (le_trans (min_le_right _ _) (min_le_right _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_short_loop_fillings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_short_loop_fillings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_short_loop_fillings ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.rfs_short_loop_fillings

theorem short_loop_disk (g : SmoothRiemannianMetric I Q) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (γ : ContinuousFreeLoop Q), IsLipschitzLoop g γ → loopLength g γ < σ →
        ∃ u : DiskCompetitor g γ, diskArea g u.1.map ≤ K * loopLength g γ ^ 2 := by
  obtain ⟨σ, K, hσ, hK, hfill⟩ := short_loop_disk_bridge g
  exact ⟨σ, hσ, K, hK, hfill⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.short_loop_disk

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
