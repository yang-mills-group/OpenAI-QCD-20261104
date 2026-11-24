import YM.Clays.Motion
import YM.MassiveQCD.Cupola.Wood
import YM.MassiveQCD.Stitch.Mint
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek
open Finset
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola
variable {C:ℝ}{I:Type}[Fintype I]
variable (o:I→Site c)(p:I→Lat.Fields c N→L[ℂ]Lat.Fields c N) (H:∀ i, Veins (o i) (p i) C)
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
local notation "B!"=> burst (traceI I)
local notation "T"=>Stitch.Tablet.credits
local notation "M"=> ample N I
open QCD.Loom
variable (a:I→ℂ) {w t:ℝ} (ht:0<t)
local notation "Ω"=> actE o p H a
local notation "Φ"=> effect o p H a
include ht
lemma from_full (x:P) : ‖token c M t (banknote N o t x)‖= T t x:=by
    rw [Loom.pulse,withdrawCost N o t ht]; unfold Stitch.Tablet.credits; rw [show Stitch.Tablet.chip t (Keys c N) S=expRate (p:=fun _=>t) (q:=fun _=>1) from rfl, fiscal (p:=fun _=>t) (q:=fun _=>1) (fun _=>ht) (fun _=>one_pos)]; simp only [prod_const_one,one_mul]; rfl
include H
set_option maxHeartbeats 660000 in
lemma industry (i:I)(x:P) : T t ((H i).dies (a i) i x) ≤ ‖a i‖*(C*T t x):=by
     let y:= (H i).twirl I x; let q':= Stitch.Tablet.chip t X S; have hz:T t y≤C*T t x:=by
           change load (expRate (p:=fun _=>t) (q:=fun _=>1)) (light (X⊕S) y) ≤ C*load (expRate (p:= fun _=>t) (q:=fun _=>1)) (light (X⊕S) x); let f (x: P)(i:Finset S):=load (fun _=>t) (pluck X i x); rw [fiscal (p:=fun _=>t) (q:=fun _=>1) (fun _=> ht) (fun _=>one_pos), fiscal (p:=fun _=>t) (q:=fun _=>1) (fun _=>ht) (fun _=>one_pos),mul_sum]; simp only [prod_const_one,one_mul]; exact sum_le_sum fun j _=> (show f y j≤ C*f x j from (Eq.trans_le (congr_arg (load (A:=X) (fun _=>t)) (show pluck X j y=_ from Veins.onPiece I (H i) ..)) ((H i).price _ _ ht))) -- not rfl need wing.
     have he : T t (echoI X i)=1:= Eq.trans (Stitch.Tablet.polite_bill {i} (echoI X i) (itOwn i) ht) (by rw [show scrape X (B! {i}) (echoI X i).val=1 from quid ..]; exact Cove.load_one _)
     rw [Veins.fate]; change load q' (light _ ((a i) • _)) ≤ _; rw [map_smul, load_scale]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [map_mul]; exact (load_mul ..).trans (show T t (echoI X i)*T t y≤ _ from (congr_arg (fun t=> t*T _ y) he).trans_le ((one_mul _).trans_le hz))
variable {R:ℝ} (hr:∀ i,‖a i‖≤ R)(hR:0 ≤ R)(hC:0 ≤ C)
include hC hR hr
lemma price_all(s:List I)(x:P): T t (Φ s x)≤ (C*R)^s.length*T t x:=by
     induction s with
     | nil=> rw [List.length_nil,pow_zero,one_mul]; exact le_rfl
     | cons i s ih=>rw [eff_cons,List.length_cons]; refine (industry o p H a ht i _).trans ?_; rw [←mul_assoc]; refine (mul_le_mul ((mul_le_mul_of_nonneg_right (hr i) hC).trans_eq (mul_comm ..)) ih (load_nn ..) (mul_nonneg hC hR)).trans_eq ?_; rw [←mul_assoc,pow_succ']
-- Summation over *only* local slab (reg/hard)
omit ht hC hR hr
local notation "fψ" s:arg V:arg=> (List.filter (fun i=> i∈ (V : Finset I)) (s: List I))
lemma ritualP (s:List I)(hx:s.Nodup){x:P}{Y:Support c}(hy: clad (limits Y) x.val): Ω s x=∑ v ∈ (s.toFinset∩ barn o Y).powerset, Φ (fψ s v) x:=by
     apply (pays o p H a s hx x).trans; symm; apply sum_subset (powerset_mono.mpr inter_subset_left); intro i hi hm; have hh:i ⊆ s.toFinset:=mem_powerset.mp hi; obtain ⟨j,hj,hk⟩:= not_subset.mp (fun e=>hm (mem_powerset.mpr e)); exact no_pay o p H a _ hy (List.mem_filter.mpr ⟨List.mem_toFinset.mp (hh hj),decide_eq_true hj⟩) (fun he=>hk (mem_inter.mpr ⟨hh hj,(inside ..).2 he⟩)) -- inspector
omit H in
lemma viewingP (s:List I)(v:Finset I) (h:v ⊆ s.toFinset): (fψ s v).toFinset=v:=by
    ext i; simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_of_imp (show i∈v→ i∈s from fun hv=>List.mem_toFinset.mp (h hv))]
omit H in
lemma payScope (s:List I)(hx:s.Nodup)(v:Finset I) (h:v ⊆ s.toFinset): (fψ s v).length=v.card:= by rw [← List.toFinset_card_of_nodup,viewingP s v h]; exact hx.filter _
open Push.AbsoluteSums
include ht hC hR hr
lemma credibility (s:List I)(hx:s.Nodup){x:P}{Y:Support c}(hy: clad (limits Y) x.val)(B F:ℕ)(hO: Fires o F)(hδ: C*R*((B+B+1)^4:ℕ)*F≤ w) : T t (Ω s x) ≤ Real.exp (w*coverNumber B Y)*T t x:=by
    let d:= Stitch.Tablet.chip t X S; rw [ritualP o p H a s hx hy]; change load d (light (X⊕S) _)≤_; rw [map_sum]; refine (load_sum ..).trans ?_; let V:= s.toFinset ∩ barn o Y; have hp i (h:i∈V.powerset):T t (Φ (fψ s i) x) ≤ (C*R)^i.card* T t x:=by rw [←payScope s hx _ ((mem_powerset.mp h).trans inter_subset_left)]; exact price_all o p H a ht hr hR hC _ _ -- check
    refine (sum_le_sum hp).trans ?_; rw [←sum_mul]; apply mul_le_mul_of_nonneg_right _ (load_nn ..); have hr₀:0 ≤ C*R:= mul_nonneg hC hR
    have hb(L:Finset I):(∑ v ∈ L.powerset,(C*R)^v.card)=(1+C*R)^L.card:=by
         induction L using Finset.induction_on with
         | empty=> simp
         | insert i L hi ih=> rw [sum_powerset_insert hi]; rw [ih,card_insert_of_notMem hi]; rw [show ∑ j∈L.powerset,(C*R)^(insert i j).card= C*R * (1+C*R)^L.card from ?_,pow_succ', add_mul,one_mul]
                              rw [← ih,mul_sum]; refine sum_congr rfl fun j hj=>?_ ; rw [card_insert_of_notMem (fun e=>hi ((mem_powerset.mp hj) e)),pow_succ']
    rw [hb]; have hv:V.card ≤ coverNumber B Y*(B+B+1)^4*F:= (card_le_card inter_subset_right).trans (barncard o Y F B hO)
    refine (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤1+C*R) (show 1+C*R ≤ Real.exp (C*R) from (add_comm 1 _).le.trans (Real.add_one_le_exp _)) _).trans ((le_of_eq (Real.exp_nat_mul ..).symm).trans (Real.exp_monotone ?_)) -- syntax chain
    have he:=mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg (coverNumber B Y)); have ht : (V.card:ℝ) ≤ ↑(coverNumber B Y*(B+B+1)^4*F:ℕ):= by exact_mod_cast hv
    push_cast at ht he; linarith only [mul_le_mul_of_nonneg_right ht hr₀,he] -- let
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.credibility
