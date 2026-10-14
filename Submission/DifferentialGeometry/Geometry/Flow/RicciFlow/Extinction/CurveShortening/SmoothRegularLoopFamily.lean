import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem slice_mfderivWithin_eq {Φ : ℝ × ℝ → M} {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hΦ : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ J) (x, t)) :
    mfderivWithin 𝓘(ℝ, ℝ) I (fun y : ℝ => Φ (y, t)) _root_.Set.univ x =
      (mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ J) (x, t)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
  have hψ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y : ℝ => (y, t)) _root_.Set.univ x
      (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) x).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) t x)).hasMFDerivWithinAt
  have hmaps : (_root_.Set.univ : Set ℝ) ⊆ (fun y : ℝ => (y, t)) ⁻¹' (_root_.Set.univ ×ˢ J) :=
    fun y _ => ⟨mem_univ y, ht⟩
  exact (hΦ.hasMFDerivWithinAt.comp x hψ hmaps).mfderivWithin
    (uniqueMDiffWithinAt_univ (𝓘(ℝ, ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.slice_mfderivWithin_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.slice_mfderivWithin_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.slice_mfderivWithin_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.slice_mfderivWithin_eq

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem mfderiv_slice_eq {Φ : ℝ × ℝ → M} {J : Set ℝ} {x t : ℝ} (ht : t ∈ J)
    (hΦ : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ J) (x, t)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => Φ (y, t)) x (1 : ℝ) =
      mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ J) (x, t) ((1 : ℝ), (0 : ℝ)) := by
  rw [← mfderivWithin_univ (I := 𝓘(ℝ, ℝ)) (I' := I) (f := fun y : ℝ => Φ (y, t)),
    slice_mfderivWithin_eq ht hΦ]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_slice_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_slice_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_slice_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.mfderiv_slice_eq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem continuousOn_tangentMapWithin_slice {a b : ℝ} (hab : a < b) {Φ : ℝ × ℝ → M}
    (hΦ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ Φ (_root_.Set.univ ×ˢ _root_.Set.Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (⟨Φ p, mfderivWithin 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p
        ((1 : ℝ), (0 : ℝ))⟩ : TangentBundle I M))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b) := by
  have hS : UniqueMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((_root_.Set.univ : Set ℝ) ×ˢ _root_.Set.Icc a b) :=
    uniqueMDiffOn_iff_uniqueDiffOn.mpr
      (UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hab))
  have hT := hΦ.contMDiffOn_tangentMapWithin (m := 0) (by simp) hS
  have hcont : ContinuousOn (tangentMapWithin 𝓘(ℝ, ℝ × ℝ) I Φ (_root_.Set.univ ×ˢ _root_.Set.Icc a b))
      (Bundle.TotalSpace.proj ⁻¹' ((_root_.Set.univ : Set ℝ) ×ˢ _root_.Set.Icc a b)) := hT.continuousOn
  have hlam : Continuous (fun p : ℝ × ℝ =>
      (Bundle.TotalSpace.mk' (ℝ × ℝ) p ((1 : ℝ), (0 : ℝ)) :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ × ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hlammaps : Set.MapsTo (fun p : ℝ × ℝ =>
      (Bundle.TotalSpace.mk' (ℝ × ℝ) p ((1 : ℝ), (0 : ℝ)) :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b)
      (Bundle.TotalSpace.proj ⁻¹' ((_root_.Set.univ : Set ℝ) ×ˢ _root_.Set.Icc a b)) :=
    fun p hp => ⟨mem_univ p.1, hp.2⟩
  exact (hcont.comp hlam.continuousOn hlammaps).congr (fun p _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_tangentMapWithin_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_tangentMapWithin_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_tangentMapWithin_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_tangentMapWithin_slice

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuous_circleParameter_of_smoothOn {a b : ℝ} {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (_root_.Set.Icc a b)) :
    Continuous (fun p : Surgery.Topology.Circle × _root_.Set.Icc a b => c p.1 p.2.1) := by
  have hsub : Continuous (fun p : ℝ × _root_.Set.Icc a b =>
      (⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, p.2.2⟩⟩ :
        (_root_.Set.univ ×ˢ _root_.Set.Icc a b : Set (ℝ × ℝ)))) :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hjoint : Continuous (fun p : ℝ × _root_.Set.Icc a b => c.lift p.1 p.2.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hc.continuousOn).comp hsub
  have hq : Topology.IsQuotientMap (fun x : ℝ => (x : Surgery.Topology.Circle)) :=
    isQuotientMap_quotient_mk'
  exact Topology.IsQuotientMap.continuous_lift_prod_left hq hjoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_circleParameter_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_circleParameter_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_circleParameter_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuous_circleParameter_of_smoothOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuousOn_loopFamily_of_smoothOn {a b : ℝ} (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) :
    ContinuousOn γ (_root_.Set.Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (DifferentialGeometry.Topology.FreeLoop.continuous_family_iff _).mpr ?_
  have h := continuous_circleParameter_of_smoothOn (I := I) hγ
  refine (h.comp (continuous_snd.prodMk continuous_fst)).congr (fun p => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamily_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamily_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamily_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamily_of_smoothOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem continuousOn_loopLiftVelocity_of_smoothOn {a b : ℝ} (hab : a < b)
    {c : CurveMap M} (hc : c.SmoothOn (I := I) (_root_.Set.Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (⟨c.lift p.1 p.2, mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y p.2) p.1 (1 : ℝ)⟩ :
        TangentBundle I M))
      (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b) := by
  have hΦ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p : ℝ × ℝ => c.lift p.1 p.2)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := hc
  have hpt : ∀ p ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b,
      (⟨c.lift p.1 p.2, mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c.lift y p.2) p.1 (1 : ℝ)⟩ :
        TangentBundle I M) =
      (⟨(fun q : ℝ × ℝ => c.lift q.1 q.2) p,
        mfderivWithin 𝓘(ℝ, ℝ × ℝ) I (fun q : ℝ × ℝ => c.lift q.1 q.2)
          (_root_.Set.univ ×ˢ _root_.Set.Icc a b) p ((1 : ℝ), (0 : ℝ))⟩ : TangentBundle I M) := by
    intro p hp
    have h := mfderiv_slice_eq (Φ := fun q : ℝ × ℝ => c.lift q.1 q.2) (J := _root_.Set.Icc a b) hp.2
      ((hΦ p ⟨mem_univ p.1, hp.2⟩).mdifferentiableWithinAt (by simp))
    rw [h]
  exact (continuousOn_tangentMapWithin_slice hab hΦ).congr hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopLiftVelocity_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopLiftVelocity_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopLiftVelocity_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopLiftVelocity_of_smoothOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_continuousOn_contractibleRegularLoop_family_of_smoothOn {a b : ℝ}
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hctr : ∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) :
    ∃ Γ : ℝ → Width.ContractibleRegularLoop (I := I) (Q := M),
      ContinuousOn Γ (_root_.Set.Icc a b) ∧ ∀ t ∈ _root_.Set.Icc a b, (Γ t).1.toContinuousLoop = γ t := by
  by_cases hab : a < b
  · have hK : Continuous (fun q : _root_.Set.Icc a b × _root_.Set.Icc (0 : ℝ) 1 =>
        (⟨(curveOfLoopFamily γ).lift q.2.1 q.1.1,
          Width.loopVelocity (I := I) (γ q.1.1) q.2.1⟩ : TangentBundle I M)) :=
      ((continuousOn_loopLiftVelocity_of_smoothOn hab hγ).comp_continuous
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst))
        (fun q => ⟨q.2.2, q.1.2⟩)).congr (fun q => rfl)
    have hjet : Continuous (fun t : _root_.Set.Icc a b =>
        (regularLoopSlice γ hγ t.1 t.2).firstJetMap) := by
      let Kmap : C(_root_.Set.Icc a b × _root_.Set.Icc (0 : ℝ) 1, TangentBundle I M) :=
        ⟨fun q => (⟨(curveOfLoopFamily γ).lift q.2.1 q.1.1,
          Width.loopVelocity (I := I) (γ q.1.1) q.2.1⟩ : TangentBundle I M), hK⟩
      exact Kmap.curry.continuous.congr (fun t => ContinuousMap.ext (fun s => rfl))
    have hval : Continuous (fun t : _root_.Set.Icc a b =>
        (regularLoopSlice γ hγ t.1 t.2).toContinuousLoop) :=
      (continuousOn_iff_continuous_domRestrict.mp
        (continuousOn_loopFamily_of_smoothOn (I := I) γ hγ)).congr (fun t => rfl)
    have hRL : Continuous (fun t : _root_.Set.Icc a b => regularLoopSlice γ hγ t.1 t.2) := by
      apply continuous_induced_rng.mpr
      exact hval.prodMk hjet
    have hF : Continuous (fun t : _root_.Set.Icc a b =>
        (⟨regularLoopSlice γ hγ t.1 t.2, hctr t.1 t.2⟩ :
          Width.ContractibleRegularLoop (I := I) (Q := M))) :=
      hRL.subtype_mk (fun t => hctr t.1 t.2)
    refine ⟨fun t : ℝ => if ht : t ∈ _root_.Set.Icc a b then
        (⟨regularLoopSlice γ hγ t ht, hctr t ht⟩ :
          Width.ContractibleRegularLoop (I := I) (Q := M))
      else Width.constantContractibleRegularLoop (I := I) (Q := M) (γ a 0), ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      exact hF.congr (fun t => by simp only [Set.domRestrict_apply, dif_pos t.2])
    · intro t ht
      simp only [dif_pos ht]
      rfl
  · have hba : b ≤ a := le_of_not_gt hab
    refine ⟨fun _ => if ha : a ∈ _root_.Set.Icc a b then
          (⟨regularLoopSlice γ hγ a ha, hctr a ha⟩ :
            Width.ContractibleRegularLoop (I := I) (Q := M))
        else Width.constantContractibleRegularLoop (I := I) (Q := M) (γ a 0),
      continuousOn_const, ?_⟩
    intro t ht
    have hta : t = a := le_antisymm (ht.2.trans hba) ht.1
    have ha : a ∈ _root_.Set.Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
    rw [hta, dif_pos ha]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_continuousOn_contractibleRegularLoop_family_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_continuousOn_contractibleRegularLoop_family_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_continuousOn_contractibleRegularLoop_family_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.exists_continuousOn_contractibleRegularLoop_family_of_smoothOn

theorem continuousOn_loopFamilyLeastArea_of_smoothOn
    [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hctr : ∀ t ∈ _root_.Set.Icc a b, IsContractibleLoop (γ t)) :
    ContinuousOn (loopFamilyLeastArea B.family.metric γ) (_root_.Set.Icc a b) := by
  obtain ⟨Γ, hΓ, hagree⟩ :=
    exists_continuousOn_contractibleRegularLoop_family_of_smoothOn γ hγ hctr
  exact continuousOn_loopFamilyLeastArea_of_continuousRegularFamily B γ Γ hΓ hagree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamilyLeastArea_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamilyLeastArea_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamilyLeastArea_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_loopFamilyLeastArea_of_smoothOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
