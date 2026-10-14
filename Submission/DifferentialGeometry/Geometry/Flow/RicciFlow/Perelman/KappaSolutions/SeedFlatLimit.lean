import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarZeroPropagation
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (X : PointedFlowSeq.{u, uE, uH} (I := I))
  (L : PointedFlowData.{u, uE, uH} (I := I) X.D) {phi : ℕ → ℕ}
  (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)

local instance seedFlatTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTopology
local instance seedFlatCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatCharted
local instance seedFlatSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSmooth
local instance seedFlatC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatC1
local instance seedFlatT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatT2
local instance seedFlatSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatSigma

local instance seedFlatTermTopology (i : ℕ) :
    TopologicalSpace (X.term i).M := (X.term i).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermTopology
local instance seedFlatTermCharted (i : ℕ) :
    ChartedSpace H (X.term i).M := (X.term i).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermCharted
local instance seedFlatTermSmooth (i : ℕ) :
    IsManifold I ∞ (X.term i).M := (X.term i).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSmooth
local instance seedFlatTermC1 (i : ℕ) : IsManifold I 1 (X.term i).M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermC1
local instance seedFlatTermT2 (i : ℕ) : T2Space (X.term i).M := (X.term i).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermT2
local instance seedFlatTermSigma (i : ℕ) :
    SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.seedFlatTermSigma

theorem pointed_klim_limit_base_scalar_zero
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hphi : StrictMono phi)
    (hbase : _root_.Filter.Tendsto (fun i => (X.term i).S.scalar 0 (X.term i).basepoint)
      _root_.Filter.atTop (𝓝 0)) {t : ℝ} (ht : t ∈ X.D.carrier)
    (C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t))
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) t) k) :
    L.S.scalar t L.basepoint = 0 := by
  have ht0 : t ≤ 0 := by
    simpa only [(hsource 0).carrier_eq, Set.mem_Iic] using ht
  have hlim := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical L.basepoint
  change _root_.Filter.Tendsto (fun k => (X.term (phi k)).S.scalar t (Phi.map k L.basepoint))
    _root_.Filter.atTop (𝓝 (L.S.scalar t L.basepoint)) at hlim
  have hnonneg : 0 ≤ L.S.scalar t L.basepoint := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun k => (hsource (phi k)).scalar_nonneg ht0 _
  have hupper : L.S.scalar t L.basepoint ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim (hbase.comp hphi.tendsto_atTop)
    apply Eventually.of_forall
    intro k
    change (X.term (phi k)).S.scalar t (Phi.map k L.basepoint) ≤
      (X.term (phi k)).S.scalar 0 (X.term (phi k)).basepoint
    have hmap : Phi.map k L.basepoint = (X.term (phi k)).basepoint :=
      Phi.basepoint_map k
    rw [hmap]
    exact (hsource (phi k)).scalar_le_terminal ht0 _
  exact le_antisymm hupper hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_klim_limit_base_scalar_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_klim_limit_base_scalar_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_klim_limit_base_scalar_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointed_klim_limit_base_scalar_zero

theorem flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero
    {kappa : ℝ} (hdim : Module.finrank ℝ E = 3) (hD : X.D = ancientTimeInterval)
    (hsource : ∀ i, KLim (I := I) kappa (X.term i)) (hphi : StrictMono phi)
    (hbase : _root_.Filter.Tendsto (fun i => (X.term i).S.scalar 0 (X.term i).basepoint)
      _root_.Filter.atTop (𝓝 0))
    (hconnected : ConnectedSpace L.M)
    (hcomplete : ∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ∈ X.D.carrier,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) :
    (∀ t ∈ X.D.carrier, ∀ y : L.M, L.S.scalar t y = 0) ∧
      (∀ t ∈ X.D.carrier, ∀ y : L.M, L.rmNormSq (I := I) t y = 0) ∧
      PointedFlowNoncollapsedAllScales (I := I) L kappa := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hcarrier : X.D.carrier = Set.Iic 0 := by rw [hD]; rfl
  have hregular : X.D.regular = Set.Iio 0 := by rw [hD]; rfl
  have hnonnegative : ∀ t ∈ X.D.carrier, ∀ y : L.M, 0 ≤ L.S.scalar t y := by
    intro t ht y
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hlim := pointedScalar_tendsto_of_metricCG_canonical_domains Ct hct y
    apply ge_of_tendsto hlim
    apply Eventually.of_forall
    intro k
    exact (hsource (phi k)).scalar_nonneg
      (by simpa only [hcarrier, Set.mem_Iic] using ht) (Phi.map k y)
  have hnegative : ∀ t : ℝ, t < 0 → ∀ y : L.M, L.S.scalar t y = 0 := by
    intro t ht
    have htcar : t ∈ X.D.carrier := by simpa only [hcarrier, Set.mem_Iic] using ht.le
    obtain ⟨Ct, hct⟩ := hconv t htcar
    have hz := pointed_klim_limit_base_scalar_zero X L Phi hsource hphi hbase htcar Ct hct
    apply scalar_slice_zero_of_nonnegative_slab L hconnected
      (a := t - 1) (b := t / 2) (by linarith) (by linarith) _ _ L.basepoint hz
    · intro s hs
      rw [hregular]
      change s < 0
      linarith [hs.2]
    · intro s hs y
      apply hnonnegative s _ y
      rw [hcarrier]
      change s ≤ 0
      linarith [hs.2]
  have hzero : ∀ t ∈ X.D.carrier, ∀ y : L.M, L.S.scalar t y = 0 := by
    intro t ht y
    have ht0 : t ≤ 0 := by simpa only [hcarrier, Set.mem_Iic] using ht
    by_cases heq : t = 0
    · subst t
      let tau : ℕ → ℝ := fun n => (-1 : ℝ) * (1 / (n + 1 : ℝ))
      have htau : ∀ n, tau n < 0 := fun n => by
        dsimp only [tau]
        exact mul_neg_of_neg_of_pos (by norm_num) (by positivity)
      have htaulim : _root_.Filter.Tendsto tau _root_.Filter.atTop (𝓝 0) := by
        simpa only [tau, _root_.MulZeroClass.mul_zero] using
          (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      have hwithin : _root_.Filter.Tendsto tau _root_.Filter.atTop (𝓝[Set.Iic 0] 0) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨htaulim, Eventually.of_forall fun n => (htau n).le⟩
      have hmap : Continuous (fun s : ℝ => (s, y)) :=
        continuous_id.prodMk continuous_const
      have hcont : ContinuousOn (fun s : ℝ => L.S.scalar s y) (Set.Iic 0) := by
        have h := L.isSolution.scalarCont.comp hmap.continuousOn
          (fun s (hs : s ∈ Set.Iic (0 : ℝ)) =>
            ⟨by simpa only [hcarrier] using hs, Set.mem_univ y⟩)
        simpa only [Function.comp_def] using h
      have hlim : _root_.Filter.Tendsto (fun n => L.S.scalar (tau n) y)
          atTop (𝓝 (L.S.scalar 0 y)) := by
        simpa only [Function.comp_def] using (hcont 0 (by simp)).tendsto.comp hwithin
      have he : (fun n => L.S.scalar (tau n) y) = fun _ : ℕ => (0 : ℝ) :=
        funext fun n => hnegative (tau n) (htau n) y
      rw [he] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    · exact hnegative t (lt_of_le_of_ne ht0 heq) y
  have hoperator : ∀ t ∈ X.D.carrier,
      PointedFlowNonnegativeCurvatureOperator (I := I) L t := by
    intro t ht
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hcone : ∀ y : L.M,
        metricAlgebraicCurvatureTensorAt (I := I) (L.S.base.metric t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence Ct hct
      intro K _hK
      refine Filter.Eventually.of_forall ?_
      intro k y _hy _hs
      change metricAlgebraicCurvatureTensorAt (I := I)
          ((X.term (phi k)).S.base.metric t) (Phi.map k y) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I)
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have h := (hsource (phi k)).nonnegativeCurvatureOperator t ht
        (Phi.map k y) n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval,
        metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
        metricRm04_apply] using h
    intro y n c v w
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone y)) n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  refine ⟨hzero, ?_, ?_⟩
  · intro t ht y
    have hbound := pointedFlow_rmNormLeScalar_of_nonnegativeOperator L hdim hoperator t ht y
    rw [hzero t ht y, _root_.MulZeroClass.mul_zero] at hbound
    have hz : Real.sqrt (L.rmNormSq (I := I) t y) = 0 :=
      le_antisymm hbound (Real.sqrt_nonneg _)
    have hsquare := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg (I := I) L t y)
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hsquare
    exact hsquare.symm
  · intro time B hcurvature
    obtain ⟨Ct, hct⟩ := hconv time time.property
    have hnc := tensor_noncollapsed_of_pointed_canonical_convergence Ct hct
      (hcomplete time time.property) kappa (fun i p r hr hcurv => by
        let b : FlowMetricBall (X.term i).S time := ⟨p, r, hr⟩
        have hb : b.IsSpatiallyRmControlled := by
          intro z hz
          exact hcurv z hz
        exact ((hsource i).noncollapsed time b hb).2)
    exact ⟨(hsource 0).kappa_pos, hnc B.center B.radius B.radius_pos hcurvature⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.flat_noncollapsed_of_pointed_klim_limit_base_tendsto_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
