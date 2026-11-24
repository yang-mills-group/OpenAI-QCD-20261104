import YM.QCD.Entr.Note
/-! # oriented norm of wave slot vs unmasked global norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i j o:Site c}{X:Support c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset
variable {Γ:Silo c}{A: BankP c}{U:St c}
abbrev crest (d:Site c):=lift d (0:Axis)
def flange (U:Sheet c)(i:Site c):Spike:= ∑ j,(shine i j*(crest (j-i):ℂ)) • gold (cell U i j)
noncomputable def torque (c:Side):Sheet c→L[ℂ]Spike:=LinearMap.toContinuousLinearMap { toFun:=fun U=> ∑ i,flange U i, map_add':=fun P Q=>by unfold flange; simp only [← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [show gold (cell _ _ _)= gold (cell P i j)+gold (cell Q i j) from rfl, smul_add], map_smul':=fun d p=>by unfold flange; simp only [RingHom.id_apply, Finset.smul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _ => ?_; rw [show gold (cell _ _ _)=d • gold (cell p i j) from rfl,smul_comm] }
lemma access (h:10*separation j i<c.val): lift (i-j)=-lift (j-i):=by
    apply lift_eq_iff.mpr; refine ⟨by rw [map_neg,wrap_lift,neg_sub],fun k=>?_⟩; have he:=component_le (j-i) k; unfold separation at h; rw [Pi.neg_apply]; omega
lemma shining (h:10*separation j i<c.val): shine j i=shine i j:=by
    let W:=route 0 (lift (j-i)) 1; let V:= Lattice.reverse W; have he: stop (0:Cover) W=lift (j-i):=route_end ..; have hp: stop i W=j:=by rw [wrap_stop,he,wrap_lift]; abel
    have hv: stop (0:Cover) V=lift (i-j):=by
       have f(x y: Cover)(w: Walk): stop (x+y) w=x+stop y w:=by induction w generalizing y with
             | nil=>rfl
             | cons d w ih=> rw [stop,add_assoc,ih,stop]
       have hh:stop (0:Cover) V+stop (0:Cover) W=0:=by rw [add_comm,← f,add_zero]; exact reverse_stop ..
       exact (eq_neg_of_add_eq_zero_left hh).trans (by rw [he,access h])
    have hz:=flick (0:Site c) i W; rw [hp] at hz; rw [shore j i V hv, shore i j W he]; exact hz
lemma blockS (s:SampleX)(o i j : Site c)(P:Bundle): shape o (Stew.block i j P) s= (shine o i *shine o j*mark o s i j) • gold P:=by
    unfold Stew.shape; simp_rw [pairBl]; rw [sum_eq_single i]; rotate_left
    · intro x _ hx; exact sum_eq_zero fun j _=>by rw [if_neg (fun h=>hx h.1),gold0,smul_zero]
    · simp
    rw [sum_eq_single j]; rotate_left
    · intro x _ hx; rw [if_neg (fun h=>hx h.2),gold0,smul_zero]
    · simp
    rw [if_pos ⟨rfl,rfl⟩]
lemma chair (i j:Site c)(P:Bundle): torque c (Stew.block i j P)=(shine i j*(crest (j-i):ℂ)) • gold P:=by
    change (∑ x:Site c,flange _ x)= _; unfold flange; simp_rw [pairBl]; rw [sum_eq_single i]; rotate_left
    · intro x _ hx; exact sum_eq_zero fun j _=>by rw [if_neg (fun h=>hx h.1),gold0,smul_zero]
    · simp
    rw [sum_eq_single j]; rotate_left
    · intro x _ hx; rw [if_neg (fun h=>hx h.2),gold0, smul_zero]
    · simp
    rw [if_pos ⟨rfl,rfl⟩]
noncomputable def ant (o: Site c): Sheet c→L[ℂ]Spike:= profile o (some (0,true))-profile o (some (0,false))
lemma actsA (i j:Site c)(P : Bundle): ant i (Stew.block i j P)=torque c (Stew.block i j P):=by change shape _ _ _ - shape _ _ _=_; rw [blockS,blockS,chair]; simp [Stew.mark, crest,lift]
lemma actsB (i j:Site c)(P:Bundle)(h:10*separation j i<c.val): ant i (Stew.block j i P)=torque c (Stew.block j i P):=by change shape _ _ _ - shape _ _ _=_; rw [blockS,blockS, chair]; simp only [Stew.mark,crest,Option.elim_some,Bool.false_eq_true,↓reduceIte,shining h,shine_self, access h,mul_one]; simp [lift]
lemma controls (d:Tick c)(U:Grid c)(h:10*separation d.2.1 d.1<c.val)(Γ:Silo c): ant d.1 (gleam Γ U d)=torque c (gleam Γ U d):=by
    unfold gleam; rw [show ((2:ℝ)⁻¹) • (pairQ Γ d U + pairQ Γ (flopT d) U)=(((2:ℂ)⁻¹)) • (pairQ Γ d U + pairQ Γ (flopT d) U) from ?_]; rotate_left
    · rw [show (2:ℂ)⁻¹=(((2:ℝ)⁻¹):ℂ) by simp]; rw [← Complex.ofReal_inv,Complex.coe_smul]
    rw [map_smul,map_add,map_smul,map_add,show ant d.1 (pairQ Γ (flopT d) _)=_ from actsB _ _ _ h, show ant d.1 (pairQ Γ d U)=_ from actsA ..]; rfl
lemma fall (d:Tick c)(Γ:Silo c)(ht: Nonwrapping (dispatch d).support d.1)(b:Flavor N) (h : fertile d) : let V:=sealG Γ N
    lane V b d (some (0,true))-lane V b d (some (0,false))=torque c (gleam Γ 1 d):=by
    intro V; unfold Stew.lane Stew.mote; change (if Nonwrapping _ d.1 then _ else _) -(if Nonwrapping _ d.1 then _ else _)= _; rw [if_pos (show Nonwrapping (V.addr d).support d.1 from ht),if_pos (show Nonwrapping (V.addr d).support d.1 from ht),show (V.view d 1)=paleF N (gleam Γ 1 d) from rfl,forceP]; exact controls d _ (ht _ (show d.2.1∈ (dispatch d).support from by rw [show (dispatch d).support=d.2.2 from if_pos h]; exact h.2)) _
lemma shedP (d:Tick c)(V:Grid c)(h: Run.Pack id id η δ B U q Γ A)(hp:¬ fertile d)(ht:0<η): gleam Γ V d=0:=by unfold gleam pairQ; rw [debtless h d V hp ht,debtless h _ V (mt (fertileD _).2 hp) ht]; rw [show ∀ i j:Site c, Stew.block i j 0=0 from fun i j=>map_zero (blockL i j), show Stew.block _ _ _=0 from map_zero (blockL _ _),add_zero,smul_zero]
end YM.QCD.Entr
