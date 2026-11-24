import YM.QCD.Entr.Neil
/-! # discrepancy warranty. No need smooth for the actual determinant of D. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i j o:Site c}{X:Support c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset
variable {Γ:Silo c}{A: BankP c}{U:St c}
abbrev Jot (M:SampleX→Spike):Spike:=M (some (0,true))-M (some (0,false))
noncomputable def goldL:Bundle→L[ℂ]Spike:=LinearMap.toContinuousLinearMap { toFun:=Stew.gold,map_add':=fun x y=>rfl,map_smul':=fun z x=>rfl }
lemma pair_cash (i j :Site c)(P:Bundle): ‖torque c (Stew.block i j P)‖≤ (separation j i:ℝ) * (‖goldL‖*‖P‖):=by
    have hh : ‖shine i j‖=1:=by obtain h|h:= Stew.shines i j<;> simp [h]
    rw [chair, norm_smul, norm_mul,hh,one_mul]; apply mul_le_mul _ (goldL.le_opNorm P) (norm_nonneg _) (Nat.cast_nonneg _); rw [Complex.norm_intCast]; have h : |crest (j-i)| ≤ (separation j i:ℤ):=by have h:=component_le (j-i) 0; unfold crest separation; rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact_mod_cast h
lemma siren (x:Tick c)(b:Flavor N)(ht:fertile x)(hv:¬ Nonwrapping (dispatch x).support x.1)(h: Run.Pack id id η δ B U q Γ A)(hp:0<η): let Y:=sealG Γ N
    c.val*‖torque c (gleam Γ 1 x) - Jot (lane Y b x)‖ ≤ 10*‖goldL‖*faceQ A 1 1 B 0 0 x:=by
   intro Y; have hS:(dispatch x).support=x.2.2:= if_pos ht; let D:= diameterQ B x.2.2; have h0 i (hi : i ∈(dispatch x).support): separation i x.1≤ D:=Corona.extent x.2.2 B (hS ▸ hi) ht.1; unfold Nonwrapping at hv; push_neg at hv; obtain ⟨p,hp',hx⟩:=hv; have hL: c.val ≤10*D:= hx.trans (Nat.mul_le_mul_left _ (h0 _ hp')); -- lost hv
   let f d:= ‖torque c (pairQ Γ d 1)‖
   have hM (x:Tick c): f x≤ (separation x.2.1 x.1:ℝ)*(‖goldL‖*silos A x):= (pair_cash ..).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((h.crop x.1 x.2.1 x.2.2).2.2.2.1 _ (citizenship _ hp 1)) (norm_nonneg goldL)) (Nat.cast_nonneg _))
   have hg(Y): Stew.lane (sealG Γ N) b x Y=0:=by unfold Stew.lane Stew.mote; exact if_neg (fun h=>Nat.not_lt_of_ge hx (h p hp'))
   rw [Jot,hg,hg,sub_zero,sub_zero,gleam]; rw [show torque c ((2:ℝ)⁻¹ • (pairQ Γ x (1:Grid c)+pairQ Γ (flopT x) 1))=_ from map_smul ((torque c).restrictScalars ℝ) ((2:ℝ)⁻¹) _,map_add,norm_smul]
   let d:ℝ:=separation x.2.1 x.1; let m:=‖goldL‖*silos A x+‖goldL‖*silos A (flopT x); have he : 0 ≤ m:= add_nonneg (mul_nonneg (norm_nonneg goldL) (need h _)) (mul_nonneg (norm_nonneg goldL) (need h _)); have hM2 : f (flopT x) ≤ d * (‖goldL‖*silos A (flopT x)):= (hM _).trans_eq (by congr 2; exact_mod_cast separation_comm x.1 x.2.1)
   have hh: d ≤ D:= Nat.cast_le.mpr (h0 _ (show x.2.1∈ (dispatch x).support from by rw [hS];exact ht.2))
   apply (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (show ‖(2:ℝ)⁻¹‖ ≤1 from by norm_num)) (Nat.cast_nonneg _)).trans; apply (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (hM _) hM2)) (Nat.cast_nonneg _)).trans; change _*(d*_+d*_)≤_; rw [←mul_add];
   have hu : (c.val:ℝ) ≤ 10*(D:ℝ):=by exact_mod_cast hL
   rw [faceQ,if_pos ht]; apply (mul_le_mul hu (mul_le_mul_of_nonneg_right hh he) (mul_nonneg (Nat.cast_nonneg _) he) (by positivity)).trans; change 10*(D:ℝ)*(↑D*m) ≤ _; rw [show (10:ℝ)*_ *((D:ℝ)*m)= (D:ℝ)^2*(10*m) from by ring]
   apply (mul_le_mul_of_nonneg_right (show (D:ℝ)^2 ≤ (1+(D:ℝ))^2 by gcongr; linarith) (show 0 ≤ 10*m from by positivity)).trans_eq; unfold tribute; unfold m D; ring
lemma wants (h:Run.Pack id id η δ B U q Γ A)(hp:0<η)(x:Tick c)(b: Flavor N):
    c.val*‖torque c (gleam Γ 1 x) - Jot (lane (sealG Γ N) b x)‖ ≤ 10*‖goldL‖*faceQ A 1 1 B 0 0 x:=by
    by_cases ht:fertile x; swap
    · have he (y): Stew.lane (sealG Γ N) b x y=0:=by
           unfold Stew.lane Stew.mote; split; next h'=>change profile _ _ (meter b (nozzle c N (gleam Γ 1 x)))=_; rw [shedP x 1 h ht hp,map_zero,map_zero,map_zero]
           next _=>rfl
      rw [shedP x 1 h ht hp,Jot,he,he,sub_zero,sub_zero,map_zero,norm_zero,mul_zero, faceQ,if_neg ht,mul_zero]
    by_cases hv:Nonwrapping (dispatch x).support x.1; swap; · exact siren x b ht hv h hp
    rw [show Jot _=_ from fall x Γ hv b ht,sub_self,norm_zero,mul_zero]; rw [faceQ,if_pos ht]; have h0:= need h x; have hx:=need h (flopT x); unfold tribute; positivity
lemma gals {F:Type}[Fintype F] (X:Gem c N F)(b: Flavor N)(s:SampleX): (∑ i:Site c, till X b i s)=∑ j: F,Stew.lane X b j s:=by simp_rw [till,tsum_fintype]; rw [sum_comm]; simp [unitM]
lemma priceζ (h:Run.Pack id id η δ B U q Γ A) (ht:Torch Γ) (ha:0<η)(K:ℝ)(hc:δ≥1) (he:1 ≤ K)(hx:∀ X: Support c, tribute B 0 0 X ≤ K*rent 1 B X)(b:Flavor N)(p:BudgetPoint)(hP:B≤ p.B)(hv:(sealG Γ N).Gather):
    c.val * ‖torque c (U 1)- (Fintype.card (Site c)) • (Jot (till (sealG Γ N) b 0))‖ ≤ (Fintype.card (Site c):ℝ)*(10*‖goldL‖*K*(q+q)) :=by
    let Z:= sealG Γ N; have ht':= glossy h ht N
    let f i:=ant (dispatch i).site (gleam Γ 1 i); have hC i:till Z b i=till Z b 0:= plums _ _ hv ht' (fun _=>Summable.of_finite) _
    have hh:(Fintype.card (Site c)) • Jot (till Z b 0)= ∑ i:Tick c,Jot (Stew.lane Z b i):=by
       unfold Jot; rw [Finset.sum_sub_distrib]
       have he s: (∑ i: Site c,till Z b i s)=Fintype.card (Site c) • till Z b 0 s:=by simp only [fun i=>hC i,sum_const,card_univ]
       rw [←gals,←gals,he,he,nsmul_sub]
    have he' : U 1=∑ i:Tick c,gleam Γ 1 i:=by
       have h1:=congr_arg (meter b (c:=c)) (setsK h 1 N); rw [map_sum] at h1; simpa only [show meter b (paleF N _)=(U 1) from forceP (U 1) b, show ∀ i:Tick c,meter b ((sealG Γ N).view i 1)=gleam Γ 1 i from fun i=>forceP _ b] using h1.symm
    rw [he',map_sum,hh, ← Finset.sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> wants h ha i b).trans; rw [← mul_sum];
    have hy:= auctions (p:=p) h ha (show (0:ℝ) ≤1 from zero_le_one) hx le_rfl ((zero_add _).trans_le hc) hP (zero_le_one.trans he) (t:=1)
    have hh i: (∑ j:Tick c, if j.1=i then faceQ A 1 1 B 0 0 j else 0) ≤ K*(q+q):=by
       have hx:= (hy i).2.2; rw [tsum_fintype] at hx; simpa only [dispatch,zero_mul, Real.exp_zero,mul_one, one_pow,one_mul] using hx
    let V i:=faceQ A 1 1 B 0 0 i
    apply (mul_le_mul_of_nonneg_left (show (∑ i,V i)≤(∑ i: Site c,K*(q+q)) from ?_) (show 0 ≤ 10*‖goldL‖ from by positivity)).trans_eq (by simp; ring)
    apply Eq.trans_le ?_ (sum_le_sum (s:=univ) (fun i _=> hh i)); rw [sum_comm]; refine sum_congr rfl (fun i _=>?_); simp; rfl
end YM.QCD.Entr
