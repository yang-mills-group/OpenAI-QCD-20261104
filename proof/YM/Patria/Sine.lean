import YM.Patria.Beholds
import YM.Cardinal.Marsh
import YM.Poised.Reeds
import YM.QCD.High.Prima
/-! Per-lattice summations. No growing period constants promised. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a b θ v A D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open MultiNext.SignedSource PhysicalNext.JointLoad Lyre Metric
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
lemma visible (U:G₀)(o:Site c)(k:ℕ)(hv:1≤v): ‖U‖≤ view o k U v:= by
    have he: Creek.load (fun _=>1) U=‖U‖:=by rw [Creek.dry _ (fun _=>one_pos)]; simp only [Finset.prod_const_one,one_mul]; exact (norm_def _).symm
    rw [← he]; exact (viewer o U k one_pos).trans (birthView o U k zero_le_one hv)
-- shrink at fixed volume and use all high derivatives
lemma shrinks (P:BudgetPoint) (o:Site c) : ∃ Q:BudgetPoint,Q.power=P.power∧Q.order=P.order ∧ Q.threshold ≤ P.threshold ∧ ∀ X:Edge (Site c), width Q o X ≤ 1:=by
    let f (i:Edge (Site c)):ℝ:= (1+(separation i.1 o:ℝ))^P.power
    let U:= (1+∑ i,f i); have hh i:1 ≤ f i:=one_le_pow₀ (by simp) -- unfolds?
    have h0:1 ≤ U:= le_add_of_nonneg_right (sum_nonneg fun i _=> zero_le_one.trans (hh i)); have hU:0<U:= zero_lt_one.trans_le h0
    let q:=P.threshold/U; have hq: q ≤ P.threshold:= div_le_self P.threshold_pos.le h0
    let Q:BudgetPoint:={P with threshold:= q, threshold_pos:= div_pos P.threshold_pos hU, threshold_le:=hq.trans P.threshold_le}; refine ⟨Q,rfl,rfl,hq,fun i=>?_⟩
    have h':f i≤U:= le_trans (single_le_sum (fun j (_hj : j∈ Finset.univ)=>zero_le_one.trans (hh j)) (Finset.mem_univ i)) (le_add_of_nonneg_left zero_le_one)
    change q*f i≤_; refine (mul_le_mul_of_nonneg_left h' (show 0≤q from Q.threshold_pos.le)).trans ?_; rw [show q*U=P.threshold from div_mul_cancel₀ _ hU.ne']; exact P.threshold_le
lemma allflag (Q:BudgetPoint) : ∀ᶠ V:Grid c in 𝓝 1,flags Q.threshold V=∅:=by
   have h x: ∀ᶠ V:Grid c in 𝓝 1, su.chord (faceValue V x) < Q.threshold:=by
       have he: Continuous (fun V:Grid c=>su.chord (faceValue V x)):=by unfold faceValue; fun_prop
       exact he.continuousAt.eventually (gt_mem_nhds (by simpa [faceValue,square,travel] using Q.threshold_pos)) -- gt or lt
   filter_upwards [eventually_all.mpr h] with x hx; ext i; simp only [flags_spec,Finset.notMem_empty,iff_false]; rintro ⟨p,-,hp⟩; exact lt_asymm hp (hx p)
lemma vhealth (h:u≤v)(U:Support c)(W: Grid c)(ht:Healthy u U W):Healthy v U W:= ht.mono_right fun x hx=>by obtain ⟨p,hp,hh⟩:= (flags_spec v W x).mp hx; exact (flags_spec u W x).mpr ⟨p,hp,h.trans_lt hh⟩
lemma phase_zone (t:BudgetPoint) : ∃ O:Set (Directions su c),0∈O∧IsOpen O∧ ∀ x∈O, ‖x‖≤1∧ flags t.threshold (increment 1 x)=∅:= by
    have ht:Tendsto (increment (1:Grid c)) (𝓝 0) (𝓝 1):= by
       have h:Continuous (increment (1:Grid c)):= by unfold increment; fun_prop
       simpa [increment] using h.tendsto 0
    have hp:= ht.eventually (allflag t); have hf : ∀ᶠ z:Directions su c in 𝓝 0, ‖z‖≤1∧ flags t.threshold (increment 1 z)=∅:= by filter_upwards [hp,ball_mem_nhds (0:Directions su c) (zero_lt_one' ℝ)] with y hy hq; exact ⟨(mem_ball_zero_iff.mp hq).le,hy⟩
    obtain ⟨V,hV,hW,he⟩:= _root_.mem_nhds_iff.mp hf; exact ⟨V,he,hW,fun i hi=> hV hi⟩
variable {I:Type} (Y:I→Support c)(o:Site c)(F:I→ Grid c→ Lat.Fields c 6){z:I→ℝ}
lemma cleared (P:BudgetPoint)(ht:∀ i,Sight (Y i) o k P v (F i) (z i))(hv:1≤v) : ∃ O:Set (Directions su c),∃ C:ℝ,0∈ O ∧ IsOpen O ∧ 0≤C ∧ (∀ i,ContDiffOn ℝ (P.order:ℕ∞ω) (F i ∘ increment 1) O) ∧ (∀ m ≤ P.order, ∀ i x,x∈O → ‖iteratedFDeriv ℝ m (F i ∘ increment 1) x‖ ≤ C*z i):=by
   obtain ⟨Q,hP,hQ,hq,hy⟩:= shrinks P o; obtain ⟨O,h0,hO,hX⟩:= phase_zone (c:=c) Q
   have he i:Ease.Charm Q (Y i) (F i):= by refine ⟨(ht i).room,fun V hU=>?_⟩; rw [hQ]; exact (ht i).use V (vhealth hq _ _ hU)
   have hu i: Q.supBounds o (Y i) (F i) (z i):= by refine ⟨(ht i).travels,fun V hH l hl hp=>?_⟩; rw [hQ] at hl; refine (visible (c:=c) (leftDerivs (F i) l V) o k hv).trans ((ht i).pole V (vhealth hq _ _ hH) _ hl (fun j hj e=>?_)); have hx:= hp j hj e; rw [hP] at hx; exact hx.trans (mul_le_mul_of_nonneg_right hq (by positivity))
   obtain ⟨S⟩:= Hera.authority su P.order; let D:= Q.threshold⁻¹; have hh: 1≤D:= (one_le_inv₀ Q.threshold_pos).2 Q.threshold_le
   let C:= D^P.order * S.fee
   have hν i x(h:x∈O):Healthy Q.threshold (Y i) (increment 1 x):=by unfold Healthy; rw [(hX x h).2]; simp
   refine ⟨O,C,h0,hO,mul_nonneg (pow_nonneg (zero_le_one.trans hh) _) (zero_le_one.trans S.large),fun i x hx=>?_, fun j hj i x hx=>?_⟩
   · rw [← hQ]; exact (Pipes.pest (he _) (hν i x hx)).contDiffWithinAt
   refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hh) _) (zero_le_one.trans S.large)) (ht i).travels) fun w=> ?_
   refine (Pipes.voyager S (he i) (hu i) hj (hQ.symm ▸ hj) w (fun i=> D*‖w i‖) (fun i=>?_) (hν i x hx) (fun i _=> ⟨(norm_le_pi_norm _ _).trans (hX _ hx).1,hy i⟩)).trans ?_
   · refine ⟨mul_nonneg (zero_le_one.trans hh) (norm_nonneg _),fun e=>?_⟩; apply (norm_le_pi_norm ..).trans; have h: Q.threshold ≤ width Q o e:= le_mul_of_one_le_right Q.threshold_pos.le (one_le_pow₀ (by simp)) -- le_mul arg
     apply le_trans _ (mul_le_mul_of_nonneg_left h (show 0≤D*‖w i‖ from mul_nonneg (zero_le_one.trans hh) (norm_nonneg _))); rw [mul_comm D,mul_assoc,show D* Q.threshold=1 from inv_mul_cancel₀ Q.threshold_pos.ne',mul_one]
   rw [Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
   calc _=D^j*S.fee*z i*∏ k,‖w k‖:=by ring
        _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh hj) (zero_le_one.trans S.large)) (ht i).travels) (prod_nonneg fun _ _=>norm_nonneg _)
end YM.Massive.Patria
#print axioms YM.Massive.Patria.cleared
