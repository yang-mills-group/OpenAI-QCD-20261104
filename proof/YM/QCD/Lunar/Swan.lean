import YM.QCD.Lunar.Cycle
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical InnerProductSpace ContDiff
variable {b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
open AnalyticBridge.VerifiedReset
variable {G:Gauge}
namespace Ring0
open Cove StepData Stew Reggae Patron Lat Acre Rails Kites Push.AbsoluteSums Matrix
variable {I:Type} {u₀:Pot su c}{v M θ H K A B d η r α:ℝ}
variable (c:Side)(P:BudgetPoint)
noncomputable def hatH (G:Gauge)(o:Site c):Pot G c:= counter (fun i j=> if i=j then 1 else 0) o
noncomputable def bodyBill (G:Gauge) (P:BudgetPoint):ℝ:=2⁻¹ * ∑ a:PlaqAxes, ∑ b:PlaqAxes, |(if a=b then 1 else 0 :ℝ)| * (pairBill G P * P.threshold ^ 2)
lemma sober : ∀ o:Site c,P.Regular (halo 2 {o}) (hatH c G o)∧ P.supBounds o (halo 2 {o}) (hatH c G o) (bodyBill G P):= fun o=>⟨counter_regular .., Bill.sup (counter_bill ..) (fun i h=> healthy_mono (halo_subset ..) h)⟩
lemma maskH (o:Site c): heads P o (G:=G)= masked P.threshold {o} (hatH c G o):=by unfold heads hatH counter quad; simp [ite_mul]
variable (h:G.Simple)(β:PlaqAxes)
include h
lemma tilt (B:BudgetPoint)(o:Site c)(hn:20<c.val): detectorK G β (hatH c G o)=1:=by
    rw [phase h (sober c B _|>.1) β (by omega) (show Nonwrapping (halo 2 {o}) o from ?_)]
    · let q:= (wedge β (spike G)); change logHessian _ (q.field o) (q.field o)=_; unfold hatH; rw [counter_diag h B o hn q]; simp [q,quad,curl_wedge,ite_mul]; rw [Finset.sum_eq_single β]
      · simp [h]
      · intro i _ he; rw [if_neg (Ne.symm he)]; simp
      simp
    intro x hx; obtain ⟨s,hs,h⟩:=halo_spec.mp hx; rw [mem_singleton.mp hs, separation_comm] at h; omega
section pulse
variable {P c}{D A Z':Pot G c}{k':PlaqAxes}{B':ℝ}
omit h
variable {t' v' D' Y:ℝ}
lemma glow_plus (R A:Pot G c)(t:ℝ): glow P k' G (R+A) t=glow P k' G R t+glow P k' G A t:=by unfold glow signal sec; dsimp only [Pi.add_apply]; simp_rw [show ∀ i j:ℝ,∀ a b,2*(i+j-(a+b))/t^2=2*(i-a)/t^2+2*(j-b)/t^2 from fun _ _ _ _=>by ring]; simp_rw [add_sub_add_comm,mul_add,sum_add_distrib]; ring
lemma glow_scale (q:ℝ) (R:Pot G c)(t:ℝ): glow P k' G (q • R) t=q*glow P k' G R t:=by
    have h(i): sec i (q • R) t=q*sec i R t:=by unfold sec; simp only [Pi.smul_apply,smul_eq_mul]; ring
    unfold glow signal; dsimp only; simp_rw [h,← mul_sub q,show ∀ (u v:ℝ),u*(q*v)=q*(u*v) from fun i j=>mul_left_comm _ _ _,← Finset.mul_sum (a:=q)]; ring
                                                                                           -- edit
lemma immigrate (h:PulseS P k' G Z' t u v')(hs:0<a)(hτ:a ≤v') (he:∀ w:ℝ,w ∈ Set.Ioc 0 a → glow P k' G A w= glow P k' G Z' w):PulseS P k' G A t u a:=⟨hs,fun w hw=>he w hw ▸ h.fees w ⟨hw.1,hw.2.trans hτ⟩⟩
def Lab0 (G: Gauge)(c:Side) (P: BudgetPoint) (β:PlaqAxes)(t:ℝ) := 0<t∧ ∀ u,u∈Set.Ioc 0 t→∀ i j:Site c,flags P.threshold (pass (rod G P i β) u)=∅∧flags P.threshold (pass (rod G P i β +rod G P j β) u)=∅
lemma pulseAgree (h:P.threshold ≤1)(hp:∀ U,flags P.threshold U=∅→ A U=D U)(ht:Lab0 G c P k' v)(hv:t∈Set.Ioc 0 v): glow P k' G A t=glow P k' G D t:=by
   have h(d:Dir G c)(he:flags P.threshold (pass d t)=∅): sec d A t=sec d D t:=by rw [sec,sec,hp _ he,hp 1 (UVNext.CouplingReset.flags_one ..)]
   unfold glow signal; dsimp only; simp_rw [fun i j=> h (rod G P i k'+rod G P j k') (ht.2 t hv i j).2,fun i=>h (rod G P i k') (ht.2 t hv i i).1]
end pulse
lemma grace (hc:20<c.val) : ∃ z M:ℝ,PulseS P β G (fun U:Config G c=> ∑ i,heads P i U) 1 M z:=by
   let s (i:Site c):=hatH c G i; let H:=bodyBill G P; obtain ⟨t,hV⟩:= crescent β h (Z:=(Fintype.card (Site c):ℝ)*H) P c
   let T (i:Site c):=(⟨i,halo 2 {i},halo_subset 2 {i} (mem_singleton_self i)⟩: RegularAddress c); let O i:=masked P.threshold (T i).support (s i); let X (U:Config G c):= ∑ i:Site c,O i U
   have ht:= (hV _ s (fun _=>H) T (fun i=>(sober c P i|>.1)) (show SumBudget (fun _:Site c=>H) (↑(Fintype.card (Site c))*H) from ⟨fun i=>(sober c P (G:=G) i|>.2.1),Summable.of_finite,by rw [tsum_fintype]; simp⟩) (fun i=>(sober c P i|>.2)) X (fun _=>hasSum_fintype _)).2
   rw [tsum_fintype,sum_congr rfl (show ∀ i∈univ,detectorK G β (s i)=(fun _=> (1:ℝ)) i from fun i _=> tilt c h β P _ hc)] at ht
   simp only [sum_const, nsmul_eq_mul, mul_one, card_univ,site_card,Nat.cast_pow,div_self (show (c.val:ℝ)^4≠0 from by positivity)] at ht
   obtain ⟨p,hp⟩:= (height h β P c); refine ⟨min p t,_, immigrate ht (lt_min hp.1 ht.upT) (min_le_right ..) ?_⟩; intro w hw; apply pulseAgree P.threshold_le _ (show Lab0 G c P β p from hp) ⟨hw.1,hw.2.trans (min_le_left ..)⟩; intro U hu; exact Finset.sum_congr rfl fun i _=>by
        have he(V:Support c):Healthy P.threshold V U:=by simp [Healthy,hu]
        change heads P i U= O i U; unfold O; rw [maskH c P]; rw [masked_eq _ _ _ _ (he _),masked_eq _ _ _ _ (he _)]
end Ring0
end YM.QCD.Lunar
