import YM.QCD.Globe.Salsa
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
variable (X:Sheet c) (p:Site c)(o: Signed)(P:Plan j)(n:Side)
-- canonical lift -> centered.L
noncomputable def neatP := ∑ v:Site c,(foam o v 0:ℂ) • goldL (onset X p (foam o v))
lemma signsH (v:Site c): Stew.shine p (p+v)= Flume.occ p (lift v):=by unfold Stew.shine; rw [Quarry.occ_rays,route_end]; simp [heel]
lemma upright : Entr.flange X p= neatP X p 1:=by
   unfold Entr.flange; rw [← Equiv.sum_comp (Equiv.addLeft p) _]; apply Finset.sum_congr rfl; intro i _;
   change _ • gold (cell X p (p+i))=_; rw [show Equiv.addLeft p i=p+i from rfl]; -- maybe solved
   rw [signsH, foamy, onset, wrap_lift, map_smul,show p+i-p=i by abel, smul_smul,mul_comm]; rfl -- comm
variable {A:ℝ}
lemma awol (hp: Beam X 2 A): c.val* ‖neatP X p o-neatP X p 1‖ ≤ 20*‖goldL‖*A:=by
   let W(s:Signed)(v: Site c):= (foam s v 0:ℂ) • goldL (onset X p (foam s v)); let Z(v:Site c):=costS 2 p (p+v)* ‖cell X p (p+v)‖; have he(v:Site c):0 ≤ Z v:=mul_nonneg (cost_nn ..) (norm_nonneg _)
   have hP(v:Site c)(s:Signed): ‖W s v‖≤ (pdist v:ℝ)* (‖goldL‖* ‖cell X p (p+v)‖):=by
       unfold W; rw [norm_smul]; refine mul_le_mul ?_ ((goldL.le_opNorm _).trans_eq ?_) (norm_nonneg _) (Nat.cast_nonneg _); · rw [show ‖(↑(foam s v 0):ℂ)‖= ((foam s v 0).natAbs:ℝ) by simp]; exact Nat.cast_le.mpr (foam_cost ..)
       unfold onset; rw [norm_smul,pathLength, foams,one_mul]
   have hh(v:Site c):c.val * ‖W o v-W 1 v‖ ≤ 20*‖goldL‖* Z v:=by
      by_cases hv: 10*pdist v < c.val; · rw [show W o v=W 1 v from ?_,sub_self,norm_zero,mul_zero]; exact mul_nonneg (by positivity) (he _); unfold W; rw [foam_near _ _ hv,foamy]
      let D:ℝ:= pdist v; let K:=cell X p (p+v); have hx : (c.val:ℝ) ≤ 10*D:=by unfold D; exact_mod_cast not_lt.mp hv
      have hz: Z v=(1+D)^2*‖K‖:=by unfold Z costS K; rw [separation,show p-(p+v)= -v by abel,pdist_neg]
      rw [hz]; have hv0:0≤D:=Nat.cast_nonneg _; apply le_trans (mul_le_mul hx ((norm_sub_le ..).trans (add_le_add (hP v o) (hP v 1))) (norm_nonneg _) (show 0≤10*D from by positivity)); change (10*D) * (D*(‖goldL‖* ‖K‖)+D*(‖goldL‖ * ‖K‖)) ≤ _; nlinarith only [mul_le_mul_of_nonneg_left (show D^2 ≤ (1+D)^2 by gcongr; simp) (show 0 ≤ ‖goldL‖ * ‖K‖ from by positivity)]
   unfold neatP; rw [← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> hh i).trans; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left ((Equiv.sum_comp (Equiv.addLeft p) (fun v=>costS 2 p v*‖cell X p v‖)).trans_le (hp.toR _)) (by positivity)
lemma events (hp:Tempo X) : Fintype.card Signed • ((sheen X:ℂ) • Lat.gamma 0)= ∑ i: Signed, neatP X p i:=by
    let i:= some ((0:Axis),true); let j:= some ((0:Axis),false); let W:=onset X p; let r:ℂ:=↑(Fintype.card Signed); have hq : r≠0:=by unfold r; exact_mod_cast Fintype.card_ne_zero (α:=Signed)
    have he(ξ:Cover): goldL (W ξ)=onSet X p ξ:=by unfold W; rw [hp.giltV]; exact leafy _
    rw [← (hp.glitter p 0).2]; change Fintype.card Signed • (nectar X p i-nectar X p j)=_; unfold nectar; rw [← smul_sub,← sum_sub_distrib,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,mul_inv_cancel₀ hq, one_smul]; unfold neatP; rw [sum_comm (f:=fun i v=> (foam i v 0:ℂ) • goldL (onset X p (foam i v)))]; apply sum_congr rfl; intro v _; rw [← sum_sub_distrib]; apply sum_congr rfl; intro s _; rw [he, ← sub_smul, show kran i _-kran j (foam s v)=_ from krans ..]
lemma verdict (hp:Tempo X)(hX:Beam X 2 A): c.val*‖(sheen X:ℂ) • Lat.gamma 0-Entr.flange X p‖ ≤20 * ‖goldL‖*A:=by
     let z:ℝ:= Fintype.card Signed; have hz:0<z:=by unfold z; positivity
     apply le_of_mul_le_mul_left _ hz; have he:= events X p hp
     let Y:Spike:= (sheen X:ℂ) • Lat.gamma 0; let F:= Entr.flange X p; have hh : z*‖Y-F‖=‖∑ i:Signed,(neatP X p i-neatP X p 1)‖:=by
          rw [sum_sub_distrib, sum_const, card_univ,← he, ← upright, ← nsmul_sub, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,Real.norm_of_nonneg hz.le] -- hp
     rw [mul_left_comm,hh];
     apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> awol X p i hX).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ]
-- brightness
lemma candy (P:Plan j): ∃ B:ℕ,∀ (v: Train j)(c:Side),B ≤ c.val→1/2 ≤ sheen (sunny P v c):=by
     obtain ⟨C,hC,H⟩:= bounces P 2; obtain ⟨W,hW,H'⟩:= spars P
     let Q:=20*‖goldL‖*C; let w:=Q+W
     obtain ⟨M,hM⟩:= exists_nat_gt (2*w*‖sparkL‖); refine ⟨M,fun v c he=>?_⟩
     let A:=sunny P v c; let K:=Lat.gamma 0; let V:=Fintype.card (Site c); let Y:=sheen A • K; have hh(i:Site c): c.val*‖Y-Entr.flange A i‖≤ Q:= verdict A i (savior P v) (H v c)
     have hz:0< (V:ℝ):=by unfold V; positivity
     have ho : V • (Y-K)=(V • Y-torque c A)+(torque c A-V • K):=by rw [nsmul_sub]; abel
     have hx : c.val * ‖V • Y-torque c A‖≤V*Q:=by
         change (c.val:ℝ)*‖V • Y-∑ i, Entr.flange A i‖≤_; rw [show V • Y=∑ i:Site c,Y from (by rw [sum_const,card_univ]),← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> hh i).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul]
     have hp:=H' c v; have hd:c.val*‖V • (Y-K)‖ ≤ V*w:=by rw [ho]; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (Nat.cast_nonneg _)).trans (by rw [mul_add]; exact (add_le_add hx hp).trans_eq (by unfold w; rw [mul_add])) -- defeq
     have ht: sparkL (V • (Y-K))=V*(sheen A -1):=by unfold Y; rw [map_nsmul,map_sub,map_smul, show sparkL K=1 from spot]; simp
     have h : c.val*((V:ℝ)*|sheen A-1|)≤ ‖sparkL‖*(V*w):=by
          rw [show (V:ℝ)*|sheen A-1|= ‖sparkL (V • (Y-K))‖ from ?_]; apply (mul_le_mul_of_nonneg_left (sparkL.le_opNorm _) (Nat.cast_nonneg _)).trans; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)
          rw [ht,norm_mul, Real.norm_of_nonneg hz.le, Real.norm_eq_abs]
     have ht : (c.val:ℝ) >0:=by positivity
     have hm:2*w* ‖sparkL‖ ≤ c.val:=le_trans hM.le (Nat.cast_le.mpr he)
     have hi:c.val*|sheen A-1| ≤ (c.val:ℝ)*(1/2):=by nlinarith only [hz,h, mul_le_mul_of_nonneg_left hm hz.le]; -- maybe nlinarith
     have hh' := (abs_le.mp (le_of_mul_le_mul_left hi ht)).1; change 1/2 ≤ sheen A; linarith only [hh']
end YM.QCD.Globe
