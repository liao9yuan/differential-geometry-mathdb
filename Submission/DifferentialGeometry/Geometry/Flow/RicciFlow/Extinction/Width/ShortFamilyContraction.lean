import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import Submission.DifferentialGeometry.Topology.Homotopy.SphereVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Topology
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

universe uK

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_le_loopLength (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (θ : Surgery.Topology.Circle) :
    riemannianEDistOf g (γ.toContinuousLoop 0) (γ.toContinuousLoop θ) ≤
      ENNReal.ofReal (loopLength g γ.toContinuousLoop) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  let a := AddCircle.equivIco (1 : ℝ) 0 θ
  have ha : (a.val : Surgery.Topology.Circle) = θ := AddCircle.coe_equivIco
  have ha0 : 0 ≤ a.val := a.property.1
  have ha1 : a.val ≤ 1 := by simpa using a.property.2.le
  have hp := Manifold.riemannianEDist_le_pathELength (I := I) γ.contMDiff_lift.contMDiffOn
    (rfl : (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0
      = γ.toContinuousLoop 0)
    (rfl : (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) a.val
      = γ.toContinuousLoop (a.val : Surgery.Topology.Circle)) ha0
  have hpa : _root_.Manifold.pathELength I (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 a.val ≤
      pathELength I (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 1 := by
    rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc, _root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    exact _root_.MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right ha1)
  have hspeed_cont : ContinuousOn (fun t : ℝ => Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t))) (_root_.Set.Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      ((continuous_tangentMetricSpeed g).comp γ.continuous_firstJet)
  have hint : _root_.MeasureTheory.IntegrableOn (fun t : ℝ => Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t)
      (loopVelocity (I := I) γ.toContinuousLoop t))) (_root_.Set.Icc (0 : ℝ) 1) :=
    hspeed_cont.integrableOn_Icc
  calc riemannianEDistOf g (γ.toContinuousLoop 0) (γ.toContinuousLoop θ)
      = riemannianEDistOf g ((fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0)
          ((fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) a.val) := by
        simp only [ha, AddCircle.coe_zero]
    _ ≤ _root_.Manifold.pathELength I (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 a.val := hp
    _ ≤ _root_.Manifold.pathELength I (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) 0 1 := hpa
    _ = ∫⁻ t in _root_.Set.Icc (0:ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (loopLift γ.toContinuousLoop t)
          (loopVelocity (I := I) γ.toContinuousLoop t)
          (loopVelocity (I := I) γ.toContinuousLoop t))) := by
        rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
        apply _root_.MeasureTheory.lintegral_congr
        intro t
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        congr 2
    _ = ENNReal.ofReal (loopLength g γ.toContinuousLoop) := by
        rw [loopLength]
        exact (_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_le_loopLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_le_loopLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_le_loopLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.edist_le_loopLength

variable [finiteDimensionalE : FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q] [connectedQ : ConnectedSpace Q]

omit boundarylessI connectedQ in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem dist_embedding_lt_of_edist_lt {N : ℕ} (g : SmoothRiemannianMetric I Q)
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : Q,
      riemannianEDistOf g x y < ENNReal.ofReal δ → _root_.Dist.dist (e.map x) (e.map y) < η := by
  obtain ⟨C, hC, hCb⟩ := DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff
    (I := I) (M := Q) (F := EuclideanSpace ℝ (Fin N)) g (e.smooth.of_le (by simp))
  refine ⟨η / (2 * (C : ℝ)), by positivity, fun x y hxy => ?_⟩
  have hCtop : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact hC.ne'
  have h2 : (C : ℝ≥0∞) * riemannianEDistOf g x y <
      (C : ℝ≥0∞) * ENNReal.ofReal (η / (2 * (C : ℝ))) := by
    have := ENNReal.mul_lt_mul_left hC0 hCtop hxy
    simpa only [mul_comm] using this
  have h3 : (C : ℝ≥0∞) * ENNReal.ofReal (η / (2 * (C : ℝ))) = ENNReal.ofReal (η / 2) := by
    have hCeq : (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := ENNReal.coe_nnreal_eq C
    rw [hCeq, ← ENNReal.ofReal_mul C.coe_nonneg]
    congr 1
    field_simp
  have h4 : _root_.EDist.edist (e.map x) (e.map y) < ENNReal.ofReal (η / 2) :=
    (hCb x y).trans_lt (h2.trans_eq h3)
  have h5 : ENNReal.ofReal (_root_.Dist.dist (e.map x) (e.map y)) < ENNReal.ofReal (η / 2) := by
    simpa only [edist_dist] using h4
  have h6 : _root_.Dist.dist (e.map x) (e.map y) < η / 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h5
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.dist_embedding_lt_of_edist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.dist_embedding_lt_of_edist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.dist_embedding_lt_of_edist_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.dist_embedding_lt_of_edist_lt


theorem exists_short_regularFamily_contracting_radius (g : SmoothRiemannianMetric I Q) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ {K : Type uK} [TopologicalSpace K] [CompactSpace K]
      (Γ : RegularFamily (I := I) (Q := Q) K),
      (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
      ∃ F : C(_root_.Set.Icc (0 : ℝ) 1 × K, ContractibleRegularLoop (I := I) (Q := Q)),
        (∀ k, F (⟨0, by simp⟩, k) = Γ k) ∧
        ∀ k, F (⟨1, by simp⟩, k) = constantContractibleRegularLoop ((Γ k).1 0) := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨η, hη, hnear⟩ := exists_regular_nearby_homotopy_radius (I := I) (Q := Q) e
  obtain ⟨δ, hδ, hδb⟩ := dist_embedding_lt_of_edist_lt (I := I) (Q := Q) g e hη
  refine ⟨δ, hδ, ?_⟩
  intro K _ _ Γ hshort
  have hbase : Continuous (fun k : K => (Γ k).1.toContinuousLoop 0) :=
    (Surgery.Topology.loopEvaluation (Q := Q)).continuous.comp
      (regularLoopInclusion.continuous.comp (continuous_subtype_val.comp Γ.continuous))
  have hloopcont : Continuous (fun k : K =>
      (constantRegularLoop (I := I) (Q := Q) ((Γ k).1.toContinuousLoop 0) : RegularLoop I Q)) := by
    refine (continuous_regularLoop_iff (I := I) (Q := Q) e _).mpr ⟨?_, ?_⟩
    · have h1 : (fun p : K × Surgery.Topology.Circle =>
          e.map ((constantRegularLoop (I := I) (Q := Q)
            ((Γ p.1).1.toContinuousLoop 0)).toContinuousLoop p.2))
          = fun p : K × Surgery.Topology.Circle => e.map ((Γ p.1).1.toContinuousLoop 0) := by
        funext p
        rfl
      rw [h1]
      exact e.smooth.continuous.comp (hbase.comp continuous_fst)
    · have h2 : (fun p : K × ℝ => deriv (fun t : ℝ =>
          e.map ((constantRegularLoop (I := I) (Q := Q)
            ((Γ p.1).1.toContinuousLoop 0)).toContinuousLoop
            (t : Surgery.Topology.Circle))) p.2) = fun _ : K × ℝ => 0 := by
        funext p
        have hconst : (fun t : ℝ => e.map ((constantRegularLoop (I := I) (Q := Q)
              ((Γ p.1).1.toContinuousLoop 0)).toContinuousLoop (t : Surgery.Topology.Circle)))
            = fun _ : ℝ => e.map ((Γ p.1).1.toContinuousLoop 0) := by
          funext t
          rfl
        rw [hconst, deriv_const]
      rw [h2]
      exact continuous_const
  have hΔcont : Continuous (fun k : K =>
      constantContractibleRegularLoop (I := I) (Q := Q) ((Γ k).1.toContinuousLoop 0)) :=
    hloopcont.subtype_mk _
  let Δ : C(K, ContractibleRegularLoop (I := I) (Q := Q)) :=
    ⟨fun k => constantContractibleRegularLoop ((Γ k).1 0), hΔcont⟩
  have hclose : ∀ k θ, _root_.Dist.dist (e.map ((Δ k).1.toContinuousLoop θ))
      (e.map ((Γ k).1.toContinuousLoop θ)) < η := by
    intro k θ
    apply hδb
    have h1 : (Δ k).1.toContinuousLoop θ = (Γ k).1.toContinuousLoop 0 := rfl
    rw [h1]
    exact lt_of_le_of_lt (edist_le_loopLength (I := I) (Q := Q) g (Γ k).1 θ)
      ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (hshort k))
  obtain ⟨R, hRc, hR0, hR1, _⟩ := hnear K (fun k => (Γ k).1) (fun k => (Δ k).1)
    (continuous_subtype_val.comp Γ.continuous) (continuous_subtype_val.comp Δ.continuous) hclose
  have hn : ∀ p : unitInterval × K, Surgery.Topology.IsContractibleLoop ((R p).toContinuousLoop) :=
    regular_homotopy_contractible R hRc (fun k => by rw [hR0 k]; exact (Γ k).2)
  refine ⟨{ toFun := fun p => ⟨R (p.1, p.2), hn (p.1, p.2)⟩, continuous_toFun := ?_ }, ?_, ?_⟩
  · exact hRc.subtype_mk _
  · intro k
    exact Subtype.ext (hR0 k)
  · intro k
    exact Subtype.ext (hR1 k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_regularFamily_contracting_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_regularFamily_contracting_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_regularFamily_contracting_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_regularFamily_contracting_radius


theorem exists_short_sphere_family_null_radius (g : SmoothRiemannianMetric I Q) :
    ∃ σ : ℝ, 0 < σ ∧
      ((∀ q : Q, Subsingleton (HomotopyGroup (Fin 2) Q q)) →
        ∀ Γ : RegularFamily (I := I) (Q := Q) (Surgery.Topology.Sphere 2),
          (∀ k, loopLength g (Γ k).1.toContinuousLoop < σ) →
          ∃ q : Q, ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ)
            (ContinuousMap.const (Surgery.Topology.Sphere 2)
              (⟨Surgery.Topology.constantLoops q,
                Surgery.Topology.isContractibleLoop_constant q⟩  :
                  Surgery.Topology.ContractibleContinuousLoop Q))) := by
  obtain ⟨σ, hσ, hcontract⟩ := exists_short_regularFamily_contracting_radius (I := I) (Q := Q) g
  refine ⟨σ, hσ, fun hpi Γ hshort => ?_⟩
  obtain ⟨F, hF0, hF1⟩ := hcontract Γ hshort
  have hb : Continuous (fun k : Surgery.Topology.Sphere 2 => (Γ k).1.toContinuousLoop 0) :=
    (Surgery.Topology.loopEvaluation (Q := Q)).continuous.comp
      (regularLoopInclusion.continuous.comp (continuous_subtype_val.comp Γ.continuous))
  let b : C(Surgery.Topology.Sphere 2, Q) := ⟨fun k => (Γ k).1.toContinuousLoop 0, hb⟩
  obtain ⟨q, hq⟩ := DifferentialGeometry.Topology.familySphereMap_nullhomotopic_of_piTwo hpi b
  let Φ : C(Q, Surgery.Topology.ContractibleContinuousLoop Q) :=
    ⟨fun q => ⟨Surgery.Topology.constantLoops q,
      Surgery.Topology.isContractibleLoop_constant q⟩,
      (Surgery.Topology.constantLoops (Q := Q)).continuous.subtype_mk _⟩
  let Δc : C(Surgery.Topology.Sphere 2, ContractibleRegularLoop (I := I) (Q := Q)) :=
    ⟨fun k => F (⟨1, by simp⟩, k), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hK1 : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ) (Φ.comp b) := by
    refine ⟨{
      toContinuousMap := contractibleRegularLoopInclusion.comp F
      map_zero_left := fun k => ?_
      map_one_left := fun k => ?_ }⟩
    · change contractibleRegularLoopInclusion (F (⟨0, by simp⟩, k)) =
        contractibleRegularLoopInclusion (Γ k)
      rw [hF0]
    · change contractibleRegularLoopInclusion (F (⟨1, by simp⟩, k)) =
        (Φ.comp b) k
      rw [hF1]
      exact Subtype.ext rfl
  obtain ⟨H⟩ := hq
  have hK2 : ContinuousMap.Homotopic (Φ.comp b)
      (Φ.comp (ContinuousMap.const (Surgery.Topology.Sphere 2) q)) :=
    ⟨{
      toContinuousMap := Φ.comp H.toContinuousMap
      map_zero_left := fun k => congrArg Φ (H.map_zero_left k)
      map_one_left := fun k => congrArg Φ (H.map_one_left k) }⟩
  refine ⟨q, hK1.trans (hK2.trans ?_)⟩
  have h2 : Φ.comp (ContinuousMap.const (Surgery.Topology.Sphere 2) q) =
      ContinuousMap.const (Surgery.Topology.Sphere 2)
        (⟨Surgery.Topology.constantLoops q, Surgery.Topology.isContractibleLoop_constant q⟩ :
          Surgery.Topology.ContractibleContinuousLoop Q) := by
    ext k
    rfl
  rw [h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_sphere_family_null_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_sphere_family_null_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_sphere_family_null_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.exists_short_sphere_family_null_radius

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
