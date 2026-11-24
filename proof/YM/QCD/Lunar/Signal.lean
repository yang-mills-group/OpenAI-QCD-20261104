import YM.QCD.Lunar.Ellis
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
noncomputable def rod (G:Gauge)(P:BudgetPoint)(i:Site c)(β:PlaqAxes):= (P.threshold/2) • cane (spike G) β.val.2 i
section ping
variable (T:G.Simple)(β:PlaqAxes)(v: Dir G c)(P)
include T
lemma bin (i:Site c)(x:Edge (Site c)): ‖cane (spike G) β.val.2 i x‖≤1:=by
   unfold cane; simp only [Pi.single_apply]; split <;> first| exact (spike_norm T).le| simp
lemma bins (p i j : Site c): P.dirBound p (rod G P i β)∧ P.dirBound p (rod G P i β+ rod G P j β):=by
    have hp:=P.threshold_pos
    have hm(i:Site c)(x): ‖rod G P i β x‖ ≤ P.threshold/2:=by
       unfold rod; rw [Pi.smul_apply, norm_smul,Real.norm_of_nonneg (half_pos hp).le]; exact mul_le_of_le_one_right (half_pos hp).le (bin T β i x)
    refine ⟨fun x=> (hm _ x).trans ?_,fun x=> le_trans ((norm_add_le (rod G P i β x) (rod G P j β x)).trans ((add_le_add (hm _ x) (hm _ x)).trans_eq (add_halves _))) ?_⟩
    · exact (half_le_self hp.le).trans (le_mul_of_one_le_right hp.le (one_le_pow₀ (by simp)))
    exact le_mul_of_one_le_right hp.le (one_le_pow₀ (by simp))
variable {P}
lemma compass (i:Site c)(j:Site c)(x:Axis): (coord j i x)^2 ≤ (c.val:ℝ)^2:=by
    unfold coord; obtain ⟨he,h⟩:=lift_centers (i-j) x; have hn: ((lift (i-j) x:ℤ):ℝ)*2 ≤ c.val:=by rw [mul_comm]; exact_mod_cast h; -- parse
    have hp : - (c.val:ℝ) < 2*((lift (i-j) x:ℤ):ℝ):=by exact_mod_cast he
    nlinarith
-- single polar 
noncomputable def sec (u:Dir G c)(F:Pot G c)(t:ℝ):ℝ:=2*(F (pass u t)-F 1)/t^2
noncomputable def signal (P:BudgetPoint)(G:Gauge)(β:PlaqAxes)(F:Pot G c)(t:ℝ):ℝ := let v:= (P.threshold/2)^2; -1/2*∑ i:Site c,∑ j:Site c,coord j i β.val.1 ^ 2*(1/(2*v)*(sec (rod G P i β+rod G P j β) F t-sec (rod G P i β) F t-sec (rod G P j β) F t))
-- single installment at λ=nCalc
lemma height (P:BudgetPoint)(c:Side): ∃ t:ℝ,0<t∧ ∀ u,u∈Set.Ioc 0 t →∀ (i j: Site c), flags P.threshold (pass (rod G P i β) u)=∅∧flags P.threshold (pass (rod G P i β+rod G P j β) u)=∅:=by
    choose f hf H using fun i:Site c=>lin (rod G P i β) P
    choose g hg H' using fun i:Site c×Site c=>lin (rod G P i.1 β+rod G P i.2 β) P
    let p:=univ.inf' univ_nonempty f; let q:=univ.inf' univ_nonempty g; refine ⟨min p q,lt_min (Finset.lt_inf'_iff _|>.2 fun i _=>hf _) (Finset.lt_inf'_iff _|>.2 fun i _=>hg _),fun u h i j=>?_⟩
    exact ⟨H i u ⟨h.1.le,h.2.trans ((min_le_left ..).trans (inf'_le _ (mem_univ _)))⟩,H' (i,j) u ⟨h.1.le,h.2.trans ((min_le_right ..).trans (inf'_le _ (mem_univ _)))⟩⟩
-- gauges scanner. polar formula.
noncomputable def call (i j:Dir G c)(F:Pot G c)(t:ℝ):= sec (i+j) F t-sec i F t-sec j F t
variable {A:Pot G c}
lemma fares (u:Dir G c)(H:P.Regular W A)(hp:P.supBounds o W A a)(h:0<t)(hr:∀ i,i∈Set.Ioc 0 t→flags P.threshold (pass u i)=∅)(he:P.dirBound o u):
    |logHessian A u u|≤a∧ ∀ i, i∈ Set.Ioc 0 t→|sec u (masked P.threshold W A) i-logHessian A u u|≤ 2*i*a:=by
   have hm i (hi:i∈Set.Icc 0 t):Healthy P.threshold W (pass u i):=by
        rcases hi.1.eq_or_lt with h|h; · rw [← h,pass,zero_smul,AnalyticBridge.VerifiedReset.at_zero]; exact flat_ok ..
        unfold Healthy; rw [hr i ⟨h,hi.2⟩]; exact Finset.disjoint_empty_right _
   have ht:= roar H hp u T he h hm; refine ⟨ht.1,fun i hi=>?_⟩
   have hv:= abs_le.mp (ht.2 i ⟨hi.1.le,hi.2⟩); have he': i^2>0:=pow_pos hi.1 _
   unfold sec; rw [masked_eq _ _ _ _ (hm i ⟨hi.1.le,hi.2⟩),masked_eq _ _ _ _ (flat_ok ..)];
   rw [abs_le]; constructor
   · rw [le_sub_iff_add_le, le_div_iff₀ he']; nlinarith only [hv.1]
   rw [sub_le_iff_le_add,div_le_iff₀ he']; nlinarith only [hv.2]
-- Unit.Wide
variable {A:Pot G c}
lemma slide (i j:Site c)(H:P.Regular W A) :
   let K:=logHessian A; let x:= rod G P i β; let y:=rod G P j β; K (x+y) (x+y)-K x x-K y y=2*(P.threshold/2)^2*K (cane (spike G) β.val.2 i) (cane (spike G) β.val.2 j):=by
      intro L k y; unfold L; have hh:= hessian_symm H k y; simp only [hessian_eq, map_add,add_apply] at hh ⊢; unfold k y rod at hh ⊢; simp only [map_smul,smul_apply,smul_eq_mul] at *; linarith
noncomputable abbrev sPer (n:Side):ℝ:=n.val
noncomputable def meterP (P:BudgetPoint)(c:Side):= 100* (sPer c)^10 / P.threshold^2
lemma falsetto (H:P.Regular W A) (hp:P.supBounds o W A a)(h:0<t)(ht: ∀ u,u∈Set.Ioc 0 t →∀ (i j: Site c), flags P.threshold (pass (rod G P i β) u)=∅∧flags P.threshold (pass (rod G P i β+rod G P j β) u)=∅): |detectorK G β A| ≤ meterP P c*a ∧ ∀ u, u ∈ Set.Ioc 0 t → |signal P G β (masked P.threshold W A) u-detectorK G β A| ≤ meterP P c*a*u:=by
   let p:=spike G; let f:= logHessian A; let m:= masked P.threshold W A; let d:=β.val.2; let k:=β.val.1; let K i:= cane p d (c:=c) i; let hP(x: Site c):= rod G P x β
   let g := 2*(P.threshold/2)^2; have hg:0<g:=by have hx:=P.threshold_pos; unfold g; positivity
   let V (i j:Site c):ℝ:=f (K i) (K j); let F (u:ℝ)(i j:Site c):=1/g * call (hP i) (hP j) m u; let τ:ℝ:= sPer c
   let Y:=meterP P c; have hY: 0≤Y:=by unfold Y meterP; positivity
   have hE(i: Site c):= fares T (hP i) H hp h (fun u hu=> (ht u hu i i).1) (bins P T β o i i).1 -- P signature
   have hs(i j:Site c):= fares T (hP i+hP j) H hp h (fun u hu=>(ht u hu i j).2) (bins P T β o i j).2
   have hb(E:Site c→Site c→ℝ) (l:ℝ)(hp:0≤l) (hh:∀ i j,|E i j|≤ l): |-(1/2:ℝ)*(∑ i,∑ j,(coord j i k)^2* E i j)| ≤ τ^10*l:=by
        rw [abs_mul]; apply le_trans (mul_le_of_le_one_left (abs_nonneg _) (by norm_num))
        have hi(i j:Site c):= compass T i j k -- check includes T yes
        apply (Finset.abs_sum_le_sum_abs ..).trans; apply le_trans (sum_le_sum fun i _=>(abs_sum_le_sum_abs ..).trans (sum_le_sum (g:=fun _:Site c=> τ^2*l) (fun j _=>show |(coord j i k)^2*E i j| ≤τ^2*l by rw [abs_mul,abs_of_nonneg (sq_nonneg _)]; exact mul_le_mul (hi ..) (hh i j) (abs_nonneg _) (sq_nonneg _))))
        simp only [sum_const,card_univ, site_card, nsmul_eq_mul, Nat.cast_pow]; unfold τ sPer; exact le_of_eq (by ring)
   have hh (l:ℝ)(hp:0≤l): τ^10*(6*l/g) ≤ Y*l:=by unfold Y meterP g; unfold τ; have hz:=P.threshold_pos; field_simp; nlinarith [show 0≤ (sPer c)^10*l from (by positivity)]
   let dK:=detectorK G β A; have hz:dK = -(1/2:ℝ)*(∑ i,∑ j,(coord j i k)^2 * V i j):=by unfold dK detectorK; rw [one_div]
   constructor
   · change |dK| ≤ _; rw [hz]; apply le_trans _ (hh a hp.1); apply hb _ _ (by have h':=hp.1; positivity); intro i j; rw [le_div_iff₀ hg, mul_comm _ g, ← abs_of_pos hg, ← abs_mul]; have hV : f (hP i+hP j) (hP i+hP j) - f (hP i) (hP i) - f (hP j) (hP j)=g*V i j:=slide T β i j H
     rw [← hV]; obtain ⟨h1,h2⟩:=abs_le.mp (hE i).1; obtain ⟨h3,h4⟩:=abs_le.mp (hE j).1; obtain ⟨h5,h6⟩:= abs_le.mp (hs i j).1; unfold f; exact abs_le.mpr ⟨by linarith only [h2,h4,h5,h1],by linarith only [h1,h3,h6,h2]⟩
   intro u hu
   have he0:0<u:=hu.1; have hp0:0≤ a*u:= mul_nonneg hp.1 he0.le; change |_ - dK| ≤_ ; rw [hz];
   have hr : signal P G β m u-dK= -(1/2:ℝ)*(∑ i,∑ j,(coord j i k)^2*(F u i j - V i j)):=by
      rw [hz]; change -(1:ℝ)/2*(∑ i,∑ j,coord j i k ^ 2*F u i j)-_= _; simp only [mul_sub,sum_sub_distrib]; ring
   rw [← hz,show _-dK=_ from hr]; apply le_trans _ ((hh _ hp0).trans_eq (mul_assoc ..).symm); apply hb _ _ (by positivity); intro i j
   unfold F call; rw [one_div, le_div_iff₀ hg, mul_comm _ g,← abs_of_pos hg,← abs_mul, abs_of_pos hg, mul_sub, mul_inv_cancel_left₀ hg.ne'];
   have hm := slide T β i j H (P:=P)
   rw [show g*V i j=_ from hm.symm]; -- tri.M
   obtain ⟨h1,h2⟩:= abs_le.mp ((hE i).2 u hu); obtain ⟨h3,h4⟩:= abs_le.mp ((hE j).2 u hu); obtain ⟨h5,h6⟩:=abs_le.mp ((hs i j).2 u hu); exact abs_le.mpr ⟨by linarith only [h2,h4,h5],by linarith only [h1,h3,h6]⟩
end ping
end Ring0
end YM.QCD.Lunar
