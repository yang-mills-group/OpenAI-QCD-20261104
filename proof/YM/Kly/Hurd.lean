import YM.Kly.Sans
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
local notation "a"=> timeAxis
variable (i: SpaceAxis)
local notation "Dq"=> Spinor.Lift.daylight i
variable (p:Pack F)(s t:ℝ)
lemma orbit1: orbit R 1 p=p:=by
      apply Subtype.ext; change rotate _ 1=_; unfold rotate; simp_rw [map_one,show EuPin.coord 1=1 from rfl,Ortho.move_one]; exact List.map_id p.val
lemma oreM (r u:EuPin): orbit R r (orbit R u p)=orbit R (r*u) p:=by
      apply Subtype.ext; change rotate (rotate _ _) _=_; unfold rotate; rw[List.map_map]; congr 1; funext x; rw [map_mul,show (r*u).coord=r.coord*u.coord from rfl,Ortho.move_mul]; rfl
lemma contrP : Signed.reflect timeAxis*(Dq t).coord=(Dq (-t)).coord*thetaR:=by
      have h:=pivot i t; rw[mirI,show ((Dq t).coord)⁻¹=(Dq (-t)).coord from (congr_arg EuPin.coord (Mako.curve_i (way i) _)).symm] at h; rw[← h, mul_assoc,mirM,mul_one]
include E U
lemma lerp: dotP (orbit R (Dq t) p)=orbit R (Dq (-t)) (dotP p):=by
     apply Subtype.ext; change reflect (rotate _ _) timeAxis=rotate (reflect _ _) _; simp only[reflectedPoint,rotate,←List.map_reverse,List.map_map]; congr 1; ext1 x; dsimp only [Function.comp_apply]; apply Prod.ext; · change Ortho.move (Signed.reflect _) (Ortho.move _ _) = Ortho.move _ (Ortho.move _ _); rw[←Ortho.move_mul, ←Ortho.move_mul,contrP] -- use Ortho move
     exact adj_rel E U (fun d y=>star_day ..) x.2
omit E U
lemma tempo (t:ℝ): Dq (t+ (4*Real.pi))=Dq t:=by
      rw [SpinParity.additive (way i)]; have he:Dq (4*Real.pi)=1:=by
            rw [show (4:ℝ)*Real.pi=2*Real.pi+2*Real.pi from by ring,SpinParity.additive (way i)]; let b:= Dq (2*Real.pi); obtain ⟨h,H⟩:=SpinGeometry.geometry.parityDouble _ _ (Ne.symm (Fin.castSucc_ne_last i)) _ (way i); apply Subtype.ext; apply Prod.ext; · change b.coord*b.coord=1; rw [show b.coord=1 from h,mul_one]
            change b.matrix*b.matrix=1; rw[show b.matrix= -1 from H,neg_mul_neg,mul_one]
      rw[he,mul_one]
include H Y R
lemma viaP : ∀ w: List (Pack F),stage P w=stage P (w.map (orbit R (Dq t))):=by
     let J(t:ℝ):Prop:=∀ w:List (Pack F),stage P w=stage P (w.map (orbit R (Dq t))); have hm {t s:ℝ}(ht:J t)(hs:J s):J (s+t):=by
           intro w; refine (ht w).trans ((hs (w.map (orbit R (Dq t)))).trans (congr_arg _ ?_)); rw [List.map_map, SpinParity.additive (way i)]; congr 1; ext1 p; exact oreM ..
     have he(s:ℝ)(h:J s)(n:ℕ): J ((n:ℝ)*s):=by
           induction n with
           | zero=>intro w; rw[Nat.cast_zero,zero_mul,(way i).1, show orbit R 1=id from funext (fun x=>orbit1 R x), List.map_id]
           | succ n ih=>rw[Nat.cast_add_one, add_mul,one_mul]; exact hm h ih
     let u:=basis a; have hv(r:ℝ)(h:|r|<Real.pi/2): J r:=same_up P H Y R _ u (by simp[u]) (by
            rw[(way i).2.2]; rw [(Work.A13.plane_givens (Ne.symm (Fin.castSucc_ne_last i)) u r).1]; have hz:=abs_lt.mp h; simpa [u, show (3:Axis)=timeAxis from rfl,Fin.castSucc_ne_last] using Real.cos_pos_of_mem_Ioo (x:=r) hz)
     obtain ⟨n,hn⟩:= exists_nat_gt (|t| / (Real.pi/2)); have hn':(0:ℝ)<n:= lt_of_le_of_lt (by positivity) hn
     refine Eq.subst (motive:=J) (show (n:ℝ)*(t/(n:ℝ))=t from by field_simp) (he _ (hv (t/n) ?_) n)
     rw [abs_div,abs_of_pos hn']; exact (div_lt_iff₀ hn').mpr ( (div_lt_iff₀ (half_pos Real.pi_pos)).mp hn |>.trans_eq (mul_comm ..))
include E U
lemma echos (v w:Pack F) : inner ℂ (budG P (orbit R (Dq t) v)) (budG P w)=inner ℂ (budG P v) (budG P (orbit R (Dq t) w)):=by
      have ht(p q:Pack F): inner ℂ (budG P p) (budG P q)=stage P [dotP p,q]:=by unfold stage; simp only[starU,List.map_cons,List.prod_cons,List.prod_nil,List.map_nil, mul_one]; rw [show M P _ (dotP p).property= _ from (starM P H Y (E.reflected _) p).symm]; exact (ContinuousLinearMap.adjoint_inner_right (M P _ p.property).val ..).symm
      rw [ht,ht]; refine (viaP P H Y R i t _).trans (congr_arg _ ?_); simp only[List.map_cons,List.map_nil]; congr 1; rw [lerp R E U i v t,oreM,← SpinParity.additive (way i), add_neg_cancel, (way i).1,orbit1] -- etc
lemma encore (x:Pack F) : budG P (orbit R (Dq t) x)=budG P x:=by
      let f(t:ℝ):= budG P (orbit R (Dq t) x); have he(u v s:ℝ):inner ℂ (f (u+s)) (f v)=inner ℂ (f u) (f (v+s)):=by unfold f; rw [show Dq (u+s)=Dq s*Dq u from by rw [← SpinParity.additive (way i),add_comm s],show Dq (v+s)=Dq s*Dq v from by rw [←SpinParity.additive (way i),add_comm s],←oreM,←oreM]; exact echos P H Y R E U _ _ _ _
      have hp: Periodic f (4*Real.pi):=fun x=>by unfold f; rw [tempo]
      obtain ⟨u,⟨r,rfl⟩,hl⟩:= (hp.compact_of_continuous (ne_of_gt (by positivity)) (hale P H Y R E i x)).exists_isMaxOn (Set.range_nonempty _) continuous_norm.continuousOn; have hy(v:ℝ):‖f v‖ ≤ ‖f r‖:= hl (mem_range_self v)
      have hx(v:ℝ): ‖f v‖=‖f r‖:=by apply le_antisymm (hy v); by_cases h:‖f r‖=0; rw[h]; exact norm_nonneg _
                                    apply le_of_mul_le_mul_left _ (show 0 < ‖f r‖ from lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
                                    rw [show ‖f r‖*‖f r‖= ‖inner ℂ (f r) (f r)‖ from by rw [inner_self_eq_norm_sq_to_K]; simp [sq]]; have ht:= he v r (r-v); rw [show v+(r-v)=r from by ring] at ht; rw [ht]; apply (norm_inner_le_norm ..).trans; rw [mul_comm ‖f r‖]; apply mul_le_mul_of_nonneg_left (hy _) (norm_nonneg _)
      have hz(v w:ℝ): inner ℂ (f v) (f w)= (‖f r‖:ℂ)^2:=by let p:=(v+w)/2; have hh:= he p w (v-p); rw [show p+(v-p)=v from by ring,show w+(v-p)=p from by unfold p; ring,inner_self_eq_norm_sq_to_K,hx] at hh; exact hh -- hx applied ambiguous ↑ etc
      have hh: f t=f 0:= sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp (by rw [inner_sub_left,inner_sub_right,inner_sub_right]; simp only [hz,sub_self]))
      rw [show budG _ _=f t from rfl,hh]; unfold f; rw [(way i).1,orbit1]
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.encore
