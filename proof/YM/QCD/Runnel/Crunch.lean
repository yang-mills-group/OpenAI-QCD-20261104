import YM.QCD.Runnel.Crimp

/-! # buy one contracting power in path-labelled norm -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {f : Side} {M X : St f} {δ b c g q ε R D : ℝ} {B v p : ℕ}

lemma Sample.balance (h : Sample δ b c B M X R p v) (hd : 0<δ) (hp : 0≤b) (i : ℕ): Own f δ b B (M^i - X^i) (i*R^i *Real.exp b *Real.exp (-c*p)):=by
  have he:=h.pay
  induction i with
  | zero=>simp only [Nat.cast_zero,pow_zero,sub_self,zero_mul]; exact Heritage.vacant -- i* R real?
  | succ i ih=>
    have h₁ : Own f δ b B (X^i) (R^i*Real.exp b):=by simpa only [← Pi.pow_apply] using h.keeps.1.power hd hp he i
    have h₂ := ih.meet h.all.1 hd hp (by positivity) h.pay
    have h₃ := h₁.meet h.close.1 hd hp (by positivity) (by positivity)
    have hh := h₂.plus h₃
    rw [show ↑(i+1)*R^(i+1)*Real.exp b*Real.exp (-c*p)= i*R^i*Real.exp b*Real.exp (-c*p)*R+R^i*Real.exp b*(R*Real.exp (-c*p)) from by push_cast; rw [pow_succ]; ring, pow_succ,pow_succ, show M^i*M-X^i*X=(M^i-X^i)*M+X^i*(M-X) by noncomm_ring]; exact hh
lemma Sample.savings (h : Sample δ b c B M X R p v) (hd : 0<δ) (hp : 0≤b) (hM : ∀ U, ‖M U‖≤q) (hg : 0≤g) (he : ε≤δ/2) (hs : q+R*Real.exp (-c*p)+R/(δ/2)*ε ≤ g) (i : ℕ) (hB : v*i≤ B): Own f ε b B (M^i) (Pile b (v*i)*g^i+i*R^i*Real.exp b*Real.exp (-c*p)):=by
  have hr:=h.pay
  obtain ⟨T,Y,hT⟩:= h.keeps.1
  have hh: Kingdom f ε⊆ Kingdom f δ:= Set.iUnion_mono fun i=> ball_subset_ball (he.trans (half_le_self hd.le))
  have hw (i:ℕ): Own f ε b B (M^i-X^i) (i*R^i*Real.exp b*Real.exp (-c*p)) := Heritage.clip (h.balance hd hp i) (he.trans (half_le_self hd.le))
  have hx : Own f ε b B (X^i) (Pile b (v*i)*g^i) := by
    have ht (U : Pulse f) (hu : U∈Kingdom f ε): ‖winch T U‖≤g:=by
      obtain ⟨A,hA⟩:=Set.mem_iUnion.mp hu
      have he := (hT.wiggle hp hr hd A U (ball_subset_ball he hA)).trans (mul_le_mul_of_nonneg_left (show ‖U-settled A‖≤ε by rw [mem_ball,dist_eq_norm] at hA; exact hA.le) (by positivity))
      have hv:=h.close.1.value hd hp (by positivity) A; rw [Pi.sub_apply, norm_sub_rev] at hv; linarith only [he,hM A,hs,hv,norm_sub_norm_le (winch T U) (X A), norm_sub_norm_le (X A) (M A)]
    apply tiled injective_id injective_id hp hB (pow_nonneg hg i) (fun U=> winch T U^i) (fun U=> by rw [hT.winched,Pi.pow_apply]) (by have he:=h.size.power i; simp_rw [← Pi.pow_apply] at he; exact he) _ (fun U hu=> (hT.won U (hh hu)).pow _) (fun U hu=> (Cost.power_bill ..).trans (pow_le_pow_left₀ (norm_nonneg _) (ht U hu) _))
    intro U k; have hu := h.keeps.1.power hd hp hr i
    obtain ⟨Z,W,H⟩:=hu; exact H.sold_g U k
  rw [show M^i=X^i+(M^i-X^i) by abel]; exact hx.plus (hw i)

lemma polynomial_wave (C : ℝ) (n : ℕ) (hp : 0<g) (he : g<1): Tendsto (fun i:ℕ=> C*(i:ℝ)^n*g^i) atTop (𝓝 0):=by
  have hh:= tides C n (neg_pos.mpr (Real.log_neg hp he))
  apply hh.congr; intro i; rw [neg_neg, mul_comm (Real.log g),Real.exp_nat_mul,Real.exp_log hp]
lemma alteration (hb : 0≤b) (hd : 0<δ) (hc : 0<c) (hr : 0<R) (h : 0≤q) (hp : q<1) (u w : ℕ) (B₀ : ℕ): ∃ ε : ℝ,0<ε∧ ε≤δ ∧ ∃ n : ℕ,0<n ∧ ∃ D≥B₀, ∀ B≥D, ∀ (f : Side) (M : St f), (∀ p:ℕ, ∃ X,Sample δ b c B M X R p (u*p+w)) → (∀ U,‖M U‖≤q)→ Own f ε b B (M^n) (1/2):=by
  obtain ⟨g,hg,hg1⟩:= exists_between hp
  have hz : 0<g:= lt_of_le_of_lt h hg
  obtain ⟨ε,hε,H,hD⟩:∃ ε : ℝ,0<ε∧ R/(δ/2)*ε<g-q∧ε≤ δ/2:=by
    have he:0<R/(δ/2):=by positivity
    obtain ⟨a,ha,hT⟩:= exists_between (lt_min (div_pos (sub_pos.mpr hg) he) (show 0<δ/2 by positivity)); refine ⟨a,ha,?_,(hT.trans_le (min_le_right ..)).le⟩; rw [mul_comm]; exact (lt_div_iff₀ he).mp (hT.trans_le (min_le_left ..))
  have ht : Tendsto (fun i : ℕ=>Real.exp (-c*i)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith))
  obtain ⟨m,hm,Hm⟩:= (((ht.const_mul R).eventually (gt_mem_nhds (by rw [mul_zero]; exact zero_lt_one))).and (eventually_gt_atTop 0)).exists
  let C:ℝ:=R*Real.exp (-c*m); have hC:0<C:=by unfold C; positivity
  have he': Tendsto (fun i:ℕ=>R*Real.exp (-c*(m*i:ℕ))) atTop (𝓝 0):=by simpa only [mul_zero] using! (ht.const_mul R).comp (show Tendsto (fun i:ℕ=>m*i) atTop atTop from tendsto_atTop_mono (f:=fun i:ℕ=>i) (fun i=> Nat.le_mul_of_pos_left _ Hm) tendsto_id)
  let W:= (2*u*m+2*w+1:ℕ)
  have hg' : Tendsto (fun i:ℕ=> (W:ℝ)^4*Real.exp b*i^ (8:ℕ)*g^i) atTop (𝓝 0):= polynomial_wave _ 8 hz hg1 -- coercion of i implicit?
  have hx' := polynomial_wave (Real.exp b) 1 hC hm
  let t:=g-q-R/(δ/2)*ε
  obtain ⟨i,i1,i2,i3,i4⟩:= ((hg'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and ((hx'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and ((eventually_gt_atTop 0).and (he'.eventually (gt_mem_nhds (by unfold t; linarith : 0<t)))))).exists -- first lt bad
  have hq : q+R*Real.exp (-c*(m*i:ℕ))+R/(δ/2)*ε≤g:=by dsimp[t] at *; linarith -- caution
  let v:= u*(m*i)+w
  have hh : Pile b (v*i)*g^i≤1/4:=by
    have hp : v*i+v*i+1≤W*i^2:=by
      unfold W v; have hh:w≤w*i:=Nat.le_mul_of_pos_right _ i3; nlinarith only [Nat.succ_le_of_lt i3,hh,Nat.mul_le_mul_right i hh]
    have hl: ((v*i+v*i+1:ℕ):ℝ) ≤ (W:ℝ)*(i:ℝ)^2:=by exact_mod_cast hp
    apply le_trans _ (show (W:ℝ)^4*Real.exp b*(i:ℝ)^8*g^i≤1/4 from i1.le)
    unfold Pile; rw [Nat.cast_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hl 4) (by positivity : 0 ≤ Real.exp b)).trans (le_of_eq (by ring))
  have hy : i*R^i*Real.exp b*Real.exp (-c*(m*i:ℕ)) ≤ 1/4:=by
    change Real.exp b*(i:ℝ)^1*C^i < 1/4 at i2
    unfold C at i2; rw [mul_pow, ← Real.exp_nat_mul,pow_one] at i2; push_cast; rw [show -c*((m:ℝ)*i) =(i:ℝ)*(-c*(m:ℝ)) by ring]; apply le_trans (le_of_eq ?_) i2.le; ring
  refine ⟨ε,hε,hD.trans (half_le_self hd.le),i,i3,max B₀ (v*i),le_max_left .., fun B he f M hM hmu=>?_⟩
  obtain ⟨X,HX⟩:= hM (m*i); refine (HX.savings hd hb hmu hz.le hD hq i ?_).mono ?_
  · exact (le_max_right ..).trans he
  unfold v at hh; linarith
end YM.QCD.Run
