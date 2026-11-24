import YM.Bank.Horse
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Cent
open Filter MeasureTheory Lattice Laurent Bloch Precision Next.Free Finset Horse Zoom Bee Osc Pilot Pap Function Metric
open QCD.Pearl (beam0 beamP beamH)
open scoped Topology BigOperators ComplexConjugate Matrix.Norms.L2Operator
variable {p k:ℕ}{σ:Bool}{a b r t h ρ C:ℝ}{n:Side} {f g:Momentum→ℂ}{L:recordL}
-- parameters: h threshold. ensure 2h<π. a ≤1 small. principal good event.Prop.
def fineE (C ρ z:ℝ) (L:recordL) (k:ℕ):ℝ:= C*(2*z)^k + ρ*16*betaL L k*(2*z)^(k+1)
def darkE (n k:ℕ)(α h m t ξ C:ℝ)(L:recordL):ℝ:=
    headH n (C/h) m (α*h)+headH n (betaL L k*Real.pi^k/h) m (α*h)+(2:ℝ)^n*(betaL L k*Real.pi^k/ξ*Real.exp (-t*ξ^2))
-- z coupling shift
structure Gates (n k:ℕ)(m h r:ℝ):Prop where
   len: 2*h ≤ r
   h0:0<h
   -- far stays inside analyt
   visits : n*m<r*h
   short : m<r*h/8^n
variable {m:ℝ}(H:Genie k σ n f g a C)(he:∀ x,physical x→g x=crewG L x)(hw:steady L k) (ht:0 ≤ t) (x:Site n)(s:Cover)(hg: Gates p k ‖phaseΔ n s‖ h a) (hA:a≤ a₀)
include H he hw ht hg
local notation "Xq" i=> grid σ i
local notation "π"=> Real.pi
def gapF (f:Momentum→ℂ)(L:recordL)(t:ℝ):= f-stunted t L
lemma soft_coin (hp: ‖Xq x‖≤h): ‖gigs (wrap n s) ((gapF f L t) ∘grid σ) p x‖ ≤2^p * fineE C t h L k:=by
    apply gigs_price; intro i hi
    let T:= x+i • wrap n s; let q:= Xq T
    have hh:=hg.h0
    have hk: ‖q‖≤2*h:= (near_bank i hi hp (hg.visits.le.trans (mul_le_of_le_one_left hh.le H.sheer)) (lt_of_le_of_lt (hg.len.trans H.sheer) (by linarith [Real.pi_gt_three]))).2
    change ‖f q -stunted t L q‖≤_
    by_cases hd:q=0
    · rcases H.clean with h0|h'
      · rw [hd,h0,(zero_f L t).2,sub_self,norm_zero]; unfold fineE; have hc:= H.money; have he:= beta_pos L k; positivity
      subst σ; exact (QCD.Flume.tune_nonzero T hd).elim
    have hv : 0<‖q‖:=norm_pos_iff.mpr hd
    have hP := H.sparks T hd (hk.trans hg.len); have hy:‖f q-crewG L q‖ ≤ C*(2*h)^k:=by
       rw [← he q (cubic σ _).1]; refine hP.fares.trans ?_; change C*(‖q‖^k /‖q‖)*‖q‖ ≤ _; rw [mul_assoc,div_mul_cancel₀ _ hv.ne']; gcongr; exact H.money
    have hj:=cubic σ T; have hb:= beta_pos L k
    have hl:= (vision hw hj.1 hd (mem_ball_self (mul_pos ans hv))) -- q inferred?
    change ‖crewG L q‖≤_ at hl
    apply (norm_sub_le_norm_sub_add_norm_sub _ (crewG L q) _).trans; refine add_le_add hy ((coma L q hj.1 ht).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl ht) (by positivity : 0≤4*‖q‖^2)).trans ?_))
    calc
      _ = t*4*betaL L k*‖q‖^(k+1) :=by
           change betaL L k * ‖q‖^k/‖q‖ * t *(4*‖q‖^2)= _
           rw [pow_succ]; field_simp; ring
      _ ≤ _:= mul_le_mul (by nlinarith : t*4*betaL L k ≤ t*16*betaL L k) (pow_le_pow_left₀ hv.le hk _) (by positivity) (by positivity)
lemma far_coin (hp:h < ‖Xq x‖) (hs:a ≤ a₀): ‖gigs (wrap n s) ((gapF f L t) ∘grid σ) p x‖ ≤ darkE p k a h ‖phaseΔ n s‖ t (π/4) C L :=by
    let u:= Xq x; have hh:= hg.h0; let A:= phaseΔ n s; have hx: 0<‖u‖:= hh.trans hp; have hm:u≠0:=norm_pos_iff.mp hx; have hr:= mul_pos H.radius hh; let V:=wrap n s
    have hk : ball u (a*h)⊆collar u a:= ball_subset_ball (mul_le_mul_of_nonneg_left hp.le H.radius.le)
    have hg0: ‖gigs V (f∘grid σ) p x‖ ≤ headH p (C/h) ‖A‖ (a*h):=by
       have he i (hi:i≤p): grid σ (x+i • V)+Laurent.reciprocal 0 ∈ baseCube:=by rw [show Laurent.reciprocal (0:Cover)=0 by ext; simp[Laurent.reciprocal],add_zero]; exact cubic ..
       have hy i(hi:i≤p): f (grid σ (x+i • V))=f (u+i • A) := by
          obtain ⟨v,hv⟩:= travels (i • s) x σ; rw [map_nsmul, phase_mul] at hv; change _ + _=u+i • A at hv
          let y:=x+i • V; let q:= grid σ y
          have hq:= cubic σ y
          symm; rw [← hv]; apply H.shifts _ hq (physical_spin hq.1)
          rw [hv]; apply H.scope x hm; apply hk; rw [mem_ball,dist_eq_norm]; change ‖u+i • A-u‖<_; rw [add_sub_cancel_left]; apply lt_of_le_of_lt _ hg.visits; rw [← phase_mul]; exact inland_small s _ hi
       rw [gigs_formula (f:=f∘grid σ) (g:=f) hy]
       exact (smooth_iter p hr (div_nonneg H.money hh.le) (fun i hi=> ⟨(H.tall x hm (hk hi)).1,(H.tall x hm (hk hi)).2.trans (div_le_div_of_nonneg_left H.money hh hp.le)⟩) hg.short u (mem_ball_self (show 0<tailH p _ from div_pos hr (by positivity)))).2
    change ‖gigs V ((f ∘ grid σ)-(stunted t L ∘ grid σ)) p x‖ ≤ _; rw [gigs_sub,Pi.sub_apply]; apply (norm_sub_le ..).trans
    let δ:=π/4; have he₀:=beta_pos L k; let W:= betaL L k*π^k; have hW :0≤ W:=by unfold W; positivity
    have hQ:0≤ headH p (W/h) ‖A‖ (a*h):=by unfold headH; positivity
    let Y:=2^p*(W/δ*Real.exp (-t*δ^2)); have hY:0 ≤Y:=by unfold Y δ; positivity
    unfold darkE; rw [add_assoc]; apply add_le_add hg0
    by_cases hi:‖u‖< π/2
    · apply le_trans ?_ (le_add_of_nonneg_right hY)
      have hv i (hi':i≤p): grid σ (x+i • V)=u+i • A:=by
          unfold V; rw [← map_nsmul,clears, phase_mul]; apply lt_of_le_of_lt (norm_add_le ..); have h':=inland_small (c:=n) s _ hi'; have hj : a*h≤1:=by have hA:= H.sheer; nlinarith [hg.len];
          change ‖u‖+_ <_; linarith [Real.pi_gt_three,hj, h'.trans_lt hg.visits]
      rw [show gigs V (stunted t L ∘ grid σ) p x=gigs A (stunted t L) p u from gigs_formula (x:=x) (y:=V) (n:=p) (p:=u) (q:=A) (f:=stunted t L∘grid σ) (g:=stunted t L) (fun i hi=> congr_arg (stunted t L) (hv i hi))]
      refine (smooth_iter p hr (div_nonneg hW hh.le) ?_ hg.short u (mem_ball_self (show 0<tailH p _ from div_pos hr (by positivity)))).2
      intro v hv
      obtain ⟨hz,h₀'⟩:= stellar L hw ht _ (cubic σ x) hm v ((ball_subset_ball (mul_le_mul_of_nonneg_right hs hx.le)) (hk hv)); exact ⟨hz,h₀'.trans (div_le_div_of_nonneg_left hW hh hp.le)⟩
    apply le_trans ?_ (le_add_of_nonneg_left hQ)
    apply gigs_price; intro i hI; apply dwarf L hw ht _ (cubic _ (x+i • V)) (bound_far i hI (le_of_not_gt hi) ?_) (by positivity)
    have h0 : h ≤ 1/2 := by linarith [hg.len,H.sheer]
    exact hg.visits.le.trans (by nlinarith [H.sheer, Real.pi_gt_three])
end YM.Bank.Cent
