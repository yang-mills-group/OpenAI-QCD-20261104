import YM.QCD.Finch.Boat
/-! # Financial projection momentum. mass at half-star epsilon. Doesn't presume recruitment of geometrical label subsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
noncomputable def flagW (F:Sheet c):ℝ:=(peel F (0,chad) (0,chad)).re
variable (G: Gem c N I)(a: Flavor N)
section wake
noncomputable def fare (a:ℝ)(B:ℕ):ℝ:= 4*4*Real.pi + 10*(6*B+2)*a⁻¹+10*(2*B)
variable {a' A:ℝ}
open AnalyticBridge.VerifiedReset
lemma rateH (i:I)(h:0≤t)(hp:0<A):
    let P:=G.view i 1;let f:=feeF a P; let S:=G.addr i; t^2*((c.val:ℝ)*‖stow f-coz (Stew.lane G a i none)‖)≤ fare A B.B * (Sen S.site t P*Real.exp (A*coverNumber B.B S.support)):=by
    intro P f S; let W:= S.support; let n:=coverNumber B.B W; let p:ℝ:= n
    have hF: 1 ≤ Real.exp (A*p) := Real.one_le_exp (mul_nonneg hp.le (Nat.cast_nonneg _)); have he:= mw S.site a P h; let s:=Sen S.site t P; have hs:0 ≤ s:=norm_nonneg _; have hv:4*4*Real.pi≤fare A B.B:=by unfold fare; exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
    by_cases hn: Nonwrapping (G.addr i).support (G.addr i).site
    · rw [show Stew.lane G a i none=shape S.site f none from if_pos hn]; apply he.2.trans; exact mul_le_mul hv (le_mul_of_one_le_right hs hF) hs (by linarith [Real.pi_pos])
    rw [show Stew.lane G a i none=0 from if_neg hn, show coz 0=0 from rfl,sub_zero]; unfold Nonwrapping at hn; push Not at hn; obtain ⟨j,hj,hv'⟩:=hn
    let b:=B.B; let a₁:=separation j S.site; have hp' : (c.val:ℝ)≤10*((4*(b:ℝ)+2)*p+2*(b:ℝ)):=by
        have h: c.val ≤ 10*(n*(4*b+2)+2*b):= hv'.trans (Nat.mul_le_mul_left _ (Corona.extent _ _ hj S.anchor)); unfold p; rw [mul_comm _ (n:ℝ)]; exact_mod_cast h
    have hk : p≤ A⁻¹ * Real.exp (A*p):=(le_inv_mul_iff₀ hp).mpr (by linarith [Real.add_one_le_exp (A*p)])
    let h0:=Real.exp (A*p); have hm: 10*((4*(b:ℝ)+2)*p+2*(b:ℝ)) ≤ fare A b*h0:=by unfold fare; let q:ℝ:= b; change 10*((4*q+2)*p+2*q)≤_; nlinarith only [hF,hp,Real.pi_pos,hk,Nat.cast_nonneg (α:=ℝ) b,mul_le_mul_of_nonneg_left hk (show 0≤(4*q+2) from by unfold q; positivity), mul_le_mul_of_nonneg_left hF (show 0≤q from (by unfold q; positivity)),mul_nonneg (b:=h0) Real.pi_pos.le (Real.exp_pos _).le, mul_nonneg (show 0≤q from Nat.cast_nonneg _) (mul_nonneg (inv_pos.mpr hp).le (Real.exp_pos (A*p)).le)]
    rw [mul_left_comm]; exact (mul_le_mul (hp'.trans hm) he.1 (by positivity) ((hp'.trans hm).trans' (Nat.cast_nonneg _))).trans_eq (by unfold h0 p n b; ring)
variable [Fintype I]
lemma stowS (F:I→ Sheet c): stow (∑ i,F i)=∑ i,stow (F i):=by unfold stow; simp_rw [Matrix.sum_apply,mul_sum]; rw [sum_comm]
lemma fareM (h: Licence B A (a'*t^2) t G)(hp:0 < A)(M:Sheet c)(he: (∑ i,G.view i 1)=Port.paleF N M)(hz:0<t)(hv:Crossing G):
    c.val* |flagW M- qMass (till G a 0)| ≤ fare A B.B*a':=by
    let u:=Fintype.card (Site c); let S:=till G a 0; let v i:=feeF a (G.view i 1)
    have hh i : till G a i=S:= Stew.plums G a (Licence_g h) hv (fun _=>Summable.of_finite) i
    have hQ : (∑ i:I,coz (Stew.lane G a i none)) = (u:ℂ) * muVal S:=by
       rw [show (∑ i:I,coz (Stew.lane G a i none))=coz (∑ i,Stew.lane G a i none) from ?_,← Entr.gals,show (∑ i:Site c,till G a i none)=u • S none from (by simp_rw [hh]; rw [sum_const];rfl)]; rotate_left
       · unfold coz; rw [Matrix.sum_apply]
       unfold coz; simp [muVal] -- inspect
    have hr : (∑ i:I,v i)=M:=by let H:=(meter a (c:=c)); change (∑ i,H (G.view i 1))= _; rw [← map_sum,he]; exact forceP ..
    let f i:= stow (v i)-coz (Stew.lane G a i none); have he' : ∑ i,f i= (u:ℂ)*(peel M (0,chad) (0,chad)-muVal S):=by unfold f; rw [sum_sub_distrib,hQ, ←stowS, hr,pStow,mul_sub]
    obtain ⟨d,hd,hH⟩:=h.zone; let w i:=d i*Real.exp (A*coverNumber B.B (G.addr i).support)
    have ht:t^2*(c.val*‖∑ i,f i‖) ≤ fare A B.B*( (u:ℝ)*(a'*t^2)) :=by
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg c.val)) (by positivity)).trans; simp_rw [mul_sum]; apply (sum_le_sum (g:=fun i=>fare A B.B*w i) fun i _=>?_).trans; swap
       · exact (rateH G a i hz.le hp (B:=B)).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((hH i).sizeU 1 (flat_ok ..)) (Real.exp_pos _).le) (by unfold fare; positivity))
       rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by unfold fare; positivity); calc
          (∑ i:I,w i) =∑ j:Site c, ∑ i:I, if (G.addr i).site=j then w i else 0:=by rw [sum_comm]; apply sum_congr rfl; intro i _; simp
          _ ≤ ∑ j:Site c,a'*t^2:=by apply sum_le_sum; intro i _; exact budget_sum (hd i) univ
          _ = _:=by simp [u]
    rw [he',norm_mul, Complex.norm_natCast] at ht
    let T:=peel M (0,chad) (0,chad)-muVal S
    have ht':(t^2*(u:ℝ))*(c.val*‖T‖) ≤ (t^2*(u:ℝ))*(fare A B.B*a'):=by linarith only [ht] -- syntactic
    have hx: 0 < t^2*(u:ℝ):=by unfold u; positivity
    apply le_trans _ (le_of_mul_le_mul_left ht' hx); apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); exact Complex.abs_re_le_norm T
end wake
end YM.QCD.Finch
