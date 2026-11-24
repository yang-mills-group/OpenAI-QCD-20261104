import YM.Bank.Cent
/-! price alias phase variations normalized counting.C -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Jump
open Function Lattice Laurent Bloch Metric Filter RG Next.Free Pilot Pap Zoom Osc Bee Horse Cent
open Finset
open Complex (I)
open QCD.Pearl (beamP beamH beam0)
open scoped Topology Matrix.Norms.L2Operator BigOperators ComplexConjugate
variable {σ:Bool}{n k j:ℕ} {c:Side}{i:Axis}{m a b r t h d e K s w:ℝ}{u v:Momentum}{x:Cover}{L:recordL} {f g:Momentum→ℂ}
lemma rel_pos (H:Genie k σ c f g a K)(hp:Gates n k w b a)(hz:0≤ w):0 ≤ headH n (K/b) w (a*b):=by unfold headH; have hi:=H.radius; have ht:=hp.h0; have hh:=H.money; positivity
lemma dark_pos (H:Genie k σ c f g a K)(L:recordL)(s:ℝ)(ht:0<t)(hp:Gates n k w b a)(hz:0≤ w):0≤ darkE n k a b w s t K L:=by
     have hs:=rel_pos H hp hz; have ht':0≤ headH n (betaL L k*Real.pi^k/b) w (a*b):=by unfold headH; have h':=beta_pos L k; have h:=H.radius; have he := hp.h0; positivity
     apply add_nonneg (add_nonneg hs ht'); have h':=beta_pos L k; positivity
lemma long_head (n k:ℕ)(hm:0≤m)(h:m≤w)(hq:0≤K)(hv:0≤a)(hx:0<r) : headH n K m r ≤ headH n K w r:=by unfold headH; gcongr -- implicit
lemma dark_raise (ht:0<t)(he:Gates n k w b a)(hm:‖phaseΔ c x‖ ≤ w)(H:Genie k σ c f g a K) (s:ℝ)(L:recordL): darkE n k a b ‖phaseΔ c x‖ s t K L≤darkE n k a b w s t K L:=by
    unfold darkE; apply add_le_add (b := _) _ le_rfl; apply add_le_add; · exact long_head n k (norm_nonneg _) hm (div_nonneg H.money he.h0.le) H.radius.le (mul_pos H.radius he.h0)
    exact long_head n k (norm_nonneg _) hm (div_nonneg (mul_nonneg (beta_pos ..) (pow_nonneg Real.pi_pos.le _)) he.h0.le) H.radius.le (mul_pos H.radius he.h0)
-- phase choice per separation with ONE component enough; need φ^(n) lower goes by taking ‖1-`...`‖≥1.
lemma spot (x:Cover)(i:Axis)(c:Side)(l:ℤ): phaseΔ c (l • step i) = (↑((l:ℝ)*beamH c):ℂ) • (step i: Momentum):=by
   ext j; by_cases h:j=i <;> simp [step,h,phaseΔ,mul_comm]
lemma enough (x:Cover)(i:Axis)(h:x i≠0)(R:ℝ)(hr:0<R)(hy:R ≤ |(x i:ℝ)|) : ∀ᶠ c:Side in atTop, ∃ z:Cover,
    ‖phaseΔ c z‖ ≤ 4/R ∧ 1 ≤ ‖mode (-phaseΔ c z) x-1‖:=by
   let p:=(x i:ℝ); have he:p≠0:=by unfold p; exact_mod_cast h
   let y:=Real.pi/p; let k (n:Side):ℤ:= Int.floor (y/beamH n); let f(n:Side):= (k n)*beamH n
   have hk: Tendsto f atTop (𝓝 y):=by
      have hc n: f n ≤ y ∧ y ≤ f n+beamH n:=by
          have h₁: ↑(k n) ≤ y/beamH n := Int.floor_le _; have h₂: y/beamH n < k n+1 := Int.lt_floor_add_one (R:=ℝ) _ -- cast
          exact ⟨(le_div_iff₀ (beamP n)).mp h₁,by simpa only [f, add_mul,one_mul] using ((div_lt_iff₀ (beamP n)).mp h₂).le⟩
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le (show Tendsto (fun n: Side=> y -beamH n) atTop (𝓝 y) from by simpa using! (tendsto_const_nhds (x:=y)).sub beam0) tendsto_const_nhds (fun i=> by linarith [(hc i).2]) (fun i=> (hc i).1)
   let s:Momentum:= Lattice.step i; have hs : ‖s‖=1:=by unfold s Lattice.step; simp [Pi.norm_single]
   have hu : Tendsto (fun n:Side=> phaseΔ n (k n • Lattice.step i)) atTop (𝓝 ((y:ℂ) • s)) :=by simp_rw [spot x]; exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hk).smul tendsto_const_nhds
   have hx : ‖((y:ℂ) • s)‖ < 4/R:=by rw [norm_smul,Complex.norm_real,hs,mul_one]; unfold y; rw [Real.norm_eq_abs,abs_div,abs_of_pos Real.pi_pos]; exact lt_of_le_of_lt (div_le_div_of_nonneg_left Real.pi_pos.le hr hy) (div_lt_div_of_pos_right Real.pi_lt_four hr)
   have hv : Tendsto (fun n:Side=> ‖mode (-phaseΔ n (k n • Lattice.step i)) x-1‖) atTop (𝓝 ‖mode (-((y:ℂ) • s)) x-1‖):= (show Continuous (fun p:Momentum=>‖mode p x-1‖) by unfold mode; fun_prop).continuousAt.tendsto.comp hu.neg
   have hz : 1 < ‖mode (-((y:ℂ) • s)) x-1‖:=by
       unfold mode; have hq : ∑ a:Axis,(-((y:ℂ) • s)) a*(x a:ℂ)=-(Real.pi:ℂ):=by
            rw [sum_eq_single i]; unfold s Lattice.step; rw [Pi.neg_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one]; unfold y; push_cast; change _*(↑(x i):ℂ)=_; unfold p; push_cast; field_simp
            intro j _ hj; simp [s,step,hj]; simp
       rw [hq, mul_comm, neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]; norm_num
   filter_upwards [hu.norm.eventually (gt_mem_nhds hx),hv.eventually (lt_mem_nhds hz)] with c hc hz; exact ⟨_,le_of_lt (show ‖phaseΔ c _‖ < _ from hc),le_of_lt hz⟩
def quotaE (n k:ℕ) (C t a h w:ℝ)(L:recordL): ℝ:= darkE n k a h w t (Real.pi/4) C L*(2*Real.pi)^4+ (2:ℝ)^n*fineE C t h L k * ((3*h)^4 * (Real.pi^2/2))
lemma total (H:Genie k σ c f g a K)(hp:∀ x,physical x→ g x=crewG L x)(hw:steady L k) (ht:0 ≤ t) (x s:Cover)(ha:a≤ a₀)(hG: Gates n k w h a) (hX: ‖phaseΔ c s‖ ≤ w)(hR: 1 ≤ ‖mode (-phaseΔ c s) x-1‖)(hC:beamH c≤h):
     beamH c ^4*‖summit c x σ (gapF f L t∘grid σ)‖ ≤ quotaE n k K t a h w L:=by
     classical
     have hg:Gates n k ‖phaseΔ c s‖ h a := ⟨hG.len,hG.h0,lt_of_le_of_lt (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)) hG.visits,hX.trans_lt hG.short⟩
     let T:= univ (α:=Site c); let S:= T.filter fun p=> ‖grid σ p‖≤ h; let X:= (gapF f L t ∘ grid (c:=c) σ); let Y:= gigs (wrap c s) X n
     let fP p:= mode (grid σ p) x*Y p; have he(p):‖fP p‖=‖Y p‖:=by unfold fP; rw [norm_mul,mode_real _ _ (cubic _ _).1,one_mul]
     let F:=2^n*fineE K t h L k
     let D:=darkE n k a h w t (Real.pi/4) K L
     let M:=beamH c^4; have hM:0≤M:= (pow_pos (beamP c) _).le; have hh:=hG.h0
     have hx : ‖summit c x σ X‖ ≤ ‖summit c x σ Y‖:=by rw [show summit c x σ Y=_ from payment x s σ X n,norm_mul,norm_pow]; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hR)
     have hf: 0≤F:=by unfold F fineE; have hg:=beta_pos L k; have hv:=H.money; positivity
     apply (mul_le_mul_of_nonneg_left hx hM).trans; change M*‖∑ p∈T, fP p‖≤_; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) hM).trans; rw [←sum_sdiff (show S ⊆T from filter_subset ..),mul_add]; unfold quotaE; apply add_le_add
     · have hd : ∑ p∈T\S,‖fP p‖ ≤∑ _p:Site c,D:=
         (sum_le_sum (s:=T\S) (g:=fun _=>D) fun i hi=>by
            rw [he]; apply (far_coin H hp hw ht i s hg ?_ ha).trans (dark_raise (by positivity) hG hX H t L); exact lt_of_not_ge (fun hh=> (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,hh⟩))).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> dark_pos H L t (by positivity) hG ((norm_nonneg _).trans hX))) -- placeholder
       apply (mul_le_mul_of_nonneg_left hd hM).trans_eq; have hp:=bill c; simp only [sum_const,card_univ,nsmul_eq_mul,site_card,Nat.cast_pow]; change beamH c^4*((c.val:ℝ)^4*D)= D* (2*Real.pi)^4; rw [← hp]; ring
     have hp' : M*S.card ≤ (3*h)^4*(Real.pi^2/2):= (sky_size _ _ h hh.le (fun i hi=>(mem_filter.mp hi).2)).trans (by gcongr <;> linarith [beamP c])
     apply (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>F) fun i hi=>?_) hM).trans; rw [sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_left hp' hf).trans' (le_of_eq (by ring))
     rw [he]; exact soft_coin H hp hw ht i s hg ((mem_filter.mp hi).2)
end YM.Bank.Jump
