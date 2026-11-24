import YM.Patria.Remiss
/-! Pullback to full-lattice tapered frames. Uniform sums on small volume neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a b θ v A D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open MultiNext.SignedSource PhysicalNext.JointLoad Lyre Metric
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised Display Beacon
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable (H:TaperHol)(b: Cover)(J:Labels.Jet su)
local notation "z₀" => current H b
variable {I:Type} (Y:I→Support c)(o:Site c)(F:I→ Grid c→ Lat.Fields c 6){z:I→ℝ} (P:BudgetPoint)
set_option maxHeartbeats 450000 in
lemma brightness (ht:∀ i,Sight (Y i) o k P v (F i) (z i))(hp: d ≤ P.order)(hv:1≤v)(hz:Summable z): ∃ B:Set ℝ,∃ g: ℕ→I→ℝ, IsOpen B ∧ IsPreconnected B ∧ 0 ∈ B ∧ (∀ x∈ B,Summable (fun i=>F i (current H b d J x))) ∧ (∀ i,ContDiffOn ℝ (d:ℕ∞ω) (moment (d:=d) H b J (F i)) B) ∧ (∀ j≤d,Summable (g j))∧ ∀ j ≤ d,∀ i,∀ x∈B, ‖iteratedFDeriv ℝ j (moment (d:=d) H b J (F i)) x‖ ≤ g j i:=by
    obtain ⟨O,W,h0,hO,hW,hG,hp'⟩:= cleared Y o F P ht hv; let v:= arches H b J (c:=c) (d:=d); let f i:= F i∘ increment 1; let u := stature H b (c:=c) (d:=d); let p i x:= u x (f i (v x))
    obtain ⟨hd,hD,hE⟩:= arched H b J (d:=d) (c:=c)
    change ContDiffAt ℝ _ v 0 at hD; change v 0=0 at hd; have h: Tendsto v (𝓝 0) (𝓝 0):= hd ▸ hD.continuousAt.tendsto -- norm_le
    obtain ⟨S,hS,he⟩:= founded hD; have hC:=knownD H b (c:=c) (d:=d); change ContDiff ℝ _ u at hC; obtain ⟨A,hA,hh⟩:= founded (hC.contDiffAt)
    let ψ(x:ℝ):Prop:=(v x∈O ∧ current (c:=c) H b d J x=increment 1 (v x))∧ ((∀ i≤d,‖iteratedFDeriv ℝ i v x‖ ≤ S) ∧ (∀ i≤d,‖iteratedFDeriv ℝ i u x‖ ≤ A) ∧ ContDiffAt ℝ (d:ℕ∞ω) v x)
    have hF:= (h.eventually (hO.mem_nhds h0)).and hE |>.and (he.and (hh.and (hD.eventually (by simp))))
    change ∀ᶠ x in 𝓝 (0:ℝ), ψ x at hF
    obtain ⟨r,hr,hX⟩:= Metric.mem_nhds_iff.mp hF; let B:= ball (0:ℝ) r; have hq:IsOpen B:=isOpen_ball; have hi(x:ℝ)(hg:x∈B): ψ x:= hX hg
    have hY (x:ℝ)(hy:x∈B): current (c:=c) H b d J x=increment 1 (v x):=(hi x hy).1.2
    have hm:MapsTo v B O:=fun x hx=> (hi x hx).1.1
    have hy (i:I): EqOn (moment H b J (F i)) (p i) B:=by
        intro x hx; rw [splitD]; change endor x (adapter _ _ (F i (current H b d J x)))=p i x; rw [hY x hx]; rfl
    let D(j:ℕ):ℝ:=j.factorial*W*S^j
    let G(j:ℕ):ℝ:=(∑ i'∈Finset.range (j+1), (j.choose i':ℝ) * A * D (j-i'))
    have hh:ContDiffOn ℝ (d:ℕ∞ω) v B:=fun x hx=> ((hi x hx).2.2.2).contDiffWithinAt
    have hc i:ContDiffOn ℝ (d:ℕ∞ω) (f i) O:=(hG i).of_le (Nat.cast_le.mpr hp)
    have hb(x:ℝ)(hx:x∈B)(i:I)(j:ℕ)(hj:j≤d): ‖iteratedFDerivWithin ℝ j (f i ∘ v) B x‖ ≤ D j*z i:=by
        have hS (m:ℕ) (he:1≤ m)(hp:m≤ j): ‖iteratedFDerivWithin ℝ m v B x‖ ≤ S^m:=by rw [iteratedFDerivWithin_of_isOpen m hq hx]; refine ((hi x hx).2.1 m (by omega)).trans ?_; nth_rw 1 [← pow_one S]; exact pow_le_pow_right₀ hS he
        have hT(m:ℕ)(he:m ≤ j) : ‖iteratedFDerivWithin ℝ m (f i) O (v x)‖ ≤ W*z i:=by rw [iteratedFDerivWithin_of_isOpen m hO (hm hx)]; exact hp' m (by omega) i _ (hm hx)
        apply (norm_iteratedFDerivWithin_comp_le (hc i) hh (Nat.cast_le.mpr hj) hO.uniqueDiffOn hq.uniqueDiffOn hm hx hT hS).trans_eq; unfold D; ring
    refine ⟨B,fun j i=> G j*z i,isOpen_ball, (convex_ball (0:ℝ) r).isPreconnected, Metric.mem_ball_self hr,fun x hx=> ?_,fun i=>?_ ,fun i _=> hz.mul_left _,fun j hj i x hx=>?_⟩
    · rw [hY _ hx]; refine Summable.of_norm_bounded (hz.mul_left W) (fun i=>?_); have hψ:= hp' 0 (Nat.zero_le _) i (v x) (hm hx); simpa [norm_iteratedFDeriv_zero] using hψ
    · exact (hC.contDiffOn.clm_apply ((hc i).comp hh hm)).congr (hy i) -- defeq
    change _ ≤ G j * _; rw [← iteratedFDerivWithin_of_isOpen j hq hx, iteratedFDerivWithin_congr (hy i) hx]; unfold G
    rw [Finset.sum_mul]; refine (norm_iteratedFDerivWithin_clm_apply hC.contDiffOn ((hc i).comp hh hm) hq.uniqueDiffOn hx (Nat.cast_le.mpr hj)).trans ?_; apply sum_le_sum; intro i' hi'; have h':i'≤j:= mem_range_succ_iff.mp hi'
    rw [mul_assoc _ (D _)]; refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (hb _ hx i _ (by omega)) (norm_nonneg _) (by positivity [hA]); rw [iteratedFDerivWithin_of_isOpen i' hq hx]; exact (hi x hx).2.2.1 i' (by omega)
lemma blackout (ht:∀ i,Sight (Y i) o k P v (F i) (z i))(hp:d ≤ P.order)(hv:1 ≤ v)(hz:Summable z)(hx:∀ i,ActionTest (d:=d) H b (F i) 0) : ActionTest (d:=d) H b (fun V=>∑' i,F i V) 0:=by
    intro J; obtain ⟨B,g,hB,hS,hP,hu,hv,hs,h⟩:= brightness H b J Y o F P ht hp hv hz
    let f i:= moment (d:=d) H b J (F i); let u(x:ℝ):= ∑' i,f i x
    let v₀:= moment (d:=d) H b J (fun V=>∑' i,F i V)
    let T: ℝ→ SpinPol d:= desired 0 J; have he : T=0:= by ext1 x; rw [show T x=_ from (observe J (0:Pol d) x).symm,map_zero]; rfl
    have hp:v₀ =ᶠ[𝓝 (0:ℝ)] u:=by
       filter_upwards [hB.mem_nhds hP] with x hx; let L:= (adapter (glow (c:=c) (d:=d) H.T b x) (glow H.T b x)).toLinearMap.toContinuousLinearMap; exact L.map_tsum (hu x hx)
    change Agrees v₀ T; rw [he]; refine ⟨((show ContDiffAt ℝ (d:ℕ∞ω) u 0 from (jobs hB hS hv hs h).contDiffAt (hB.mem_nhds hP)).congr_of_eventuallyEq hp),contDiffAt_const,fun i hi=>?_⟩
    have hg:= iterated_sum hB hS hv hs h (0:ℝ) hP hi
    have hG : HasSum (fun j=>iteratedDeriv i (f j) 0) (iteratedDeriv i u 0):= ContinuousMultilinearMap.hasSum_eval hg (fun j : Fin i => (1:ℝ))
    have hf(j): iteratedDeriv i (f j) 0=0:=by rw [(hx j J).2.2 i hi,show desired (0:Pol d) J=0 from he, iteratedDeriv_const_zero]
    simp_rw [hf] at hG; rw [(hp.iteratedDeriv _).eq_of_nhds,hG.unique hasSum_zero,iteratedDeriv_const_zero]
end YM.Massive.Patria
#print axioms YM.Massive.Patria.blackout
