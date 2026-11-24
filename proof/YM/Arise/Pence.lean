import YM.Arise.Lamp
/-! # norm accounting mask crop to moment estimate.Any spectrum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Count
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Massive UV UV.Free QCD QCD.Grass QCD.Bera QCD.Cove QCD.Anomaly QCD.Creek Count Vest
open MassiveQCD.Sample.Quills
open MassiveQCD.Ribbon
open YM.Arise.Range YM.Arise.Bill
open MassiveQCD.Play MassiveQCD.Play.Chamber
variable {n m i j d k l:ℕ}
variable {I X Y B A C F D:Type}[Fintype I][Fintype X][Fintype Y][Fintype A][Fintype B][Fintype C][Fintype F][Fintype D]
open MassiveQCD.FlareV
open Next.Rank Normal
local notation "Oz"=> Oce.rose
local notation "Pl"=> Papers A (Patio X)
local notation "Pm"=> Papers C (Patio D)
noncomputable def pence (T: Tone A X Unit D)(P:I→Papers A (Patio X))(v:Finset I):= Oz D (fun _:Unit=>1) (T.read (∏ i∈v,P i))
noncomputable def pumpkin (x t:ℝ)(n m l:ℕ):=emmet x x x x (l*n) (l*m)*t^l
noncomputable def splint (x t:ℝ)(n m l:ℕ):= (pumpkin x t n m l * moneyN l)^l
variable (P:I→Papers A (Patio X))
variable {Q:Finset I}(m:I→Finset X)(e:I→Finset A)
variable (ht:∀ i∈ Q,P i∈ Ledger (m i) (e i) n j)
include ht
local notation "Xq" => Q.biUnion m
local notation "Eq!"=> Q.biUnion e
lemma landed (p: Finset I) (h:p⊆Q) (he:Q.card ≤  l): (∏ i∈p,P i) ∈ Ledger Xq Eq! (l*n) (l*j):=by -- parens
    have hP(i: Finset I)(hp:i⊆Q): (∏ j∈i,P j)∈Ledger Xq Eq! (i.card*n) (i.card*j):=by induction i using Finset.induction_on with
      | empty=>rw [prod_empty]; exact arrives _
      | insert i p hi ih=> have ht':= hp (mem_insert_self ..); rw [prod_insert hi,card_insert_of_notMem hi,Nat.add_comm,Nat.add_mul,Nat.add_mul,one_mul,one_mul]; exact harbored (leaguer (ht i ht') (Finset.subset_biUnion_of_mem m ht') (Finset.subset_biUnion_of_mem e ht') le_rfl le_rfl) (ih ((subset_insert ..).trans hp))
    have hv: p.card  ≤ l:= (card_le_card h).trans he; exact leaguer (hP p h) (Subset.refl _) (Subset.refl _) (Nat.mul_le_mul_right n hv) (Nat.mul_le_mul_right j hv)
variable {T: Tone A X Unit D}{S:Tone A X Unit D}{e' x t v:ℝ}
variable (hh: Q.card  ≤  l)(hp:Sky T.P T.Q T.M T.V (Q.biUnion e) (Q.biUnion m) x x x x)
variable (hF:∀ i∈Q,cents (P i) ≤ t)(he:1  ≤ t)
include hh hp hF he
local notation "pr!"=>pumpkin x t n j l
local notation "PC"=>splint x t n j l
local notation "Ov"=>Oz D (fun _:Unit=> (1:ℝ))
private lemma debt(p:Finset I)(h:p⊆Q) : cents (∏ i∈p,P i)  ≤  t^l:=by
     apply ((probate A).prodB p P).trans; refine (prod_le_prod (fun i _=>cent _) (fun i hi=>hF i (h hi))).trans ?_; rw [prod_const]; exact pow_le_pow_right₀ he ((card_le_card h).trans hh)
lemma shutter(p:Finset I)(h:p⊆Q): ‖pence T P p‖  ≤  pumpkin x t n j l:=by
    let Y:=∏ i∈p,P i
    have a:= landed P m e ht p h hh
    have h0:T.read Y∈ Ledger (univ:Finset D) (univ:Finset Unit) (l*n) (l*j):=types _ _ _ _ a (fun _ _ i _=>mem_univ i) (fun _ _ i _=>mem_univ i)
    have hx':= MassiveQCD.Rebus.em_pos (n:=l*n) (m:=l*j) hp.craze -- implicit order
    have hv: ‖Ov (T.read Y)‖  ≤  cents (T.read Y):=by simpa using (Oce.cares (p:=T.read Y) (x:=(fun _:Unit=>1)) h0.2 (show Oce.bill _ univ 1 from (fun i hi=>by simp)) le_rfl)
    exact hv.trans ((tolled _ _ _ _ Y a hp).trans (mul_le_mul_of_nonneg_left (debt P m e ht hh hp hF he p h) (zero_le_one.trans hx')))
omit ht hh hp hF he
lemma light_c (h:1 ≤ x)(ht:1  ≤ t): 1  ≤  pumpkin x t n j l:=one_le_mul_of_one_le_of_one_le (MassiveQCD.Rebus.em_pos h) (one_le_pow₀ ht)
lemma light_v (h:1  ≤ x)(ht:1  ≤ t): 1  ≤  splint x t n j l:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le (light_c h ht) (MassiveQCD.Rebus.sageMoney l))
include ht hh hp hF he
lemma countsV (p: Finset I)(h:p⊆Q): ‖cetacea (pence T P) p‖ ≤ splint x t n j l:=by
    have h0(i:Finset I)(hi:i⊆Q)(he':i.Nonempty):‖pence T P i‖ ≤  pr!^i.card:=(shutter P m e ht hh hp hF he i hi).trans (by simpa only [pow_one] using pow_le_pow_right₀ (light_c hp.craze he) (show 1  ≤  i.card from card_pos.mpr he'))
    have h' : p.card  ≤ l:= (card_le_card h).trans hh; exact (shopper (pence T P) (marksV _) (pr!) p (fun i hi he=>h0 _ ((mem_powerset.mp hi).trans h) he) (light_c hp.craze he) h').trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (light_c hp.craze he) (MassiveQCD.Rebus.sageMoney l)) h')
noncomputable def corona (x t:ℝ)(n m l:ℕ) := (face l (splint x t n m l)+1)^l * (windfall x x x x (l*n) (l*m)*t^l)
lemma compensation (hS: Sky S.P S.Q S.M S.V Eq! Xq x x x x) (hv: 0  ≤  v)(hs: drifts T.P T.Q T.M T.V S.P S.Q S.M S.V Eq! Xq v)(p:Finset I)(h:p⊆ Q): ‖cetacea (pence T P) p-cetacea (pence S P) p‖ ≤  corona x t n j l*v:=by
    have hx':=hp.craze; have hv':=Tuck.t_pane (n:=l*n) (m:=l*j) (s:=x) hx'; let W₀:=windfall x x x x (l*n) (l*j); let s:=W₀*v*t^l; unfold corona; rw [show _*v=(face l (splint x t n j l)+1)^l*s from ?_]; apply spentX (marksV (Patio D)) (pence T P) (pence S P) p ((card_le_card h).trans hh) (light_v hp.craze he) (mul_nonneg (mul_nonneg hv' hv) (pow_nonneg (zero_le_one.trans he) _)) (fun i hi _=>countsV P m e ht hh hp hF he _ (hi.trans h)) (fun i hi _=>countsV P m e ht hh hS hF he _ (hi.trans h))
    intro i hi hh'; let Y:=∏ i∈i,P i; have a:= landed P m e ht i (hi.trans h) hh; have hA(Q:Tone A X Unit D): Q.read Y∈Ledger (univ:Finset D) (univ:Finset Unit) (l*n) (l*j):=types _ _ _ _ a (fun _ _ i _=> mem_univ i) (fun _ _ i _=>mem_univ i)
    have hp':T.read Y-S.read Y∈ Camp univ (l*n):=Submodule.sub_mem _ (hA T).2 (hA S).2; change ‖Ov _-Ov _‖ ≤ _; rw [← map_sub]; apply le_trans (b:=cents (T.read Y-S.read Y)); · simpa using (Oce.cares hp' (x:=fun _:Unit=>1) (show Oce.bill _ univ 1 from fun i hi=>by simp) le_rfl)
    exact (momentQ _ _ _ _ _ _ _ _ Y a hp hS hv hs).trans (mul_le_mul_of_nonneg_left (debt P m e ht hh hp hF he i (hi.trans h)) (mul_nonneg hv' hv))
    unfold s W₀; ring
end YM.Arise.Count
#print axioms YM.Arise.Count.compensation
