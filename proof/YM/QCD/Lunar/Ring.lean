import YM.QCD.Stew.Price
/-!
# Wrap-minimal price at fixed RG point on late torus
 Exponential μ of that price. Norm atTop c.*
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Lunar
open Function Filter Lattice RG Wilson Gauge Metric Finset Set
open scoped Topology BigOperators Classical
variable {B b k i l : ℕ} {c f L:Side} {P:BudgetPoint}{x a t u σ ε:ℝ} {W V:Support c}{o p:Site c}
noncomputable def TestS (n:Side)(b k:ℕ):Prop:= ∃ p : RegularAddress n, ¬Nonwrapping p.support p.site ∧ coverNumber b p.support=k
lemma plight (o:Site c) (he:c.val≥2): ∃ x:Site c,c.val ≤ 10*separation x o:=by
    let u:=c.val / 2
    have hx : 2*u ≤ c.val:=by unfold u; omega
    let d:Cover:= Pi.single (0:Axis) (u:ℤ)
    have hp : lift (wrap c d)=d:=lift_eq_iff.mpr ⟨rfl,fun i=>by
       unfold d; by_cases hi:i=0; · subst i; rw [Pi.single_eq_same]; omega
       rw [Pi.single_eq_of_ne hi]; omega ⟩
    refine ⟨wrap c d+o,?_⟩; unfold separation; rw [add_sub_cancel_right]; have hh:= component_le (wrap c d) 0; rw [hp,show d 0=(u:ℤ) from Pi.single_eq_same .., Int.natAbs_natCast] at hh; unfold u at *; omega
lemma theoremS (h:2 ≤ c.val)(B:ℕ):∃ k,TestS c B k:=by
   obtain ⟨x,h⟩:= plight (0:Site c) h; exact ⟨_,(⟨0,univ,Finset.mem_univ _⟩:RegularAddress c),fun hi=>(not_lt.mpr h) (hi x (Finset.mem_univ _)),rfl⟩
noncomputable def tollV (b:ℕ)(c:Side):ℕ:= if h: 2 ≤ c.val then Nat.find (theoremS h b) else 0
lemma toll_top (h:¬Nonwrapping W o)(hp:o∈W)(B:ℕ): tollV B c ≤ coverNumber B W:=by unfold tollV; split; exact Nat.find_min' _ ⟨⟨_,_,hp⟩,h,rfl⟩; omega
lemma artisan (o:Site c)(B:ℕ)(h:2≤ c.val) : ∃ X:Support c,o∈X∧¬Nonwrapping X o∧ coverNumber B X=tollV B c:=by
   unfold tollV; rw [dif_pos h]; obtain ⟨x,hx,hp⟩:=Nat.find_spec (theoremS h B)
   let γ:= o-x.site; let p:=x.support.image (affine 1 γ); have he: affine 1 γ x.site=o:=by simp [affine,γ]
   rw [← hp]; refine ⟨p, he ▸ mem_image_of_mem (affine 1 γ) x.anchor, he ▸ mt (AnalyticBridge.VerifiedReset.spin_wrap 1 γ x.site).mp hx,?_⟩ -- sig
   exact Push.Local.cover_map (Push.Local.turnSites 1 γ) (Push.Local.turn_sep 1 γ) ..
lemma badS (h:2 ≤ c.val)(B:ℕ): c.val ≤10*(tollV B c * (4*B+2)+2*B):=by
   obtain ⟨u,hu,hv,hp⟩:= artisan (0:Site c) B h; unfold Nonwrapping at hv; push Not at hv; obtain ⟨x,hx,hV⟩:=hv; exact hV.trans (Nat.mul_le_mul_left 10 (hp ▸ (Lattice.Corona.extent u B hx hu)))
lemma continueS : Tendsto (fun (c:Side)=> c.val) atTop atTop:=by
   refine tendsto_atTop.mpr fun b=> ?_; filter_upwards [eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with c hc; exact Nat.le_trans (Nat.le_succ b) hc
lemma grows (B:ℕ) : Tendsto (tollV B) atTop atTop:=by
   apply Filter.tendsto_atTop.mpr; intro b
   filter_upwards [continueS.eventually_ge_atTop 2,continueS.eventually_gt_atTop (10*(b*(4*B+2)+2*B))] with c hx hp; have he:= lt_of_lt_of_le hp (badS hx B); nlinarith
-- Mathlib Real.Surge. API. .π any.
open Asymptotics
abbrev Φ (B:ℕ)(v:ℝ)(c:Side):= Real.exp (v*(tollV B c:ℝ))
lemma shine (B:ℕ){v:ℝ}(h:0 < v)(j:ℕ)(A:ℝ)(hA:0 ≤ A): Tendsto (fun c: Side=> Φ B (-v) c*((c.val:ℝ)^j)*A) atTop (𝓝 0):=by
   let a (c:Side) :ℝ:= tollV B c; let C:ℝ:=10*((4*B+2:ℕ)+2*B:ℕ)
   have hp: Tendsto a atTop atTop:= tendsto_natCast_atTop_atTop.comp (grows B)
   have he : Tendsto (fun c:Side =>Φ B (-v) c*a c^j) atTop (𝓝 0):=by
        have hh:= ((isLittleO_pow_exp_pos_mul_atTop j h).tendsto_div_nhds_zero).comp hp; refine hh.congr fun c=>?_ ; dsimp only [comp_apply]; unfold Φ; change a c^j/ _= Real.exp _*_ ; rw [neg_mul,Real.exp_neg, div_eq_mul_inv,mul_comm]
   let f (c:Side):= Φ B (-v) c*((a c*C)^j*A)
   have hf:Tendsto f atTop (𝓝 0):=by
         convert! (he.mul_const (C^j*A)) using 1; · ext i; unfold f; ring
         rw [zero_mul]
   refine squeeze_zero' (Eventually.of_forall (fun i=> mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity)) hA)) ?_ hf
   filter_upwards [continueS.eventually_ge_atTop 2,hp.eventually_ge_atTop 1] with c hc ht
   dsimp only [f]; rw [mul_assoc]; have hR: (c.val:ℝ) ≤ a c*C:=by
      have he': (c.val:ℝ) ≤10*(a c*((4*B+2:ℕ):ℝ)+(2*B:ℕ)):=by unfold a; exact_mod_cast badS hc B
      apply he'.trans; unfold C; push_cast; nlinarith
   gcongr
   all_goals exact hA
end YM.QCD.Lunar
