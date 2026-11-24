import YM.Magi.Rest
import YM.Oars.Treads
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open Function Lattice RG Pressure MeasureTheory Finset QCD Kites Kit Port Flume
open Grass Lat Play QCD.Bera
open Stitch Plate Loom Loom.Fleet Sway OrbitG Ribbon Rebus Creek Cove Apron Apron.Grove Cupola QCD.Acre QCD.Acre.Rails
open Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I] {l φ k B P A A':ℕ} {v α s t:ℝ}
local notation "F0"=> (Keys c N)
open QCD.Brick QCD.Dust -- edit
-- payload color for actual evaluator. does not insert new face handshake.
namespace LampV
-- support charges for (almost) arbitrary repricing at end, no loss of flag rights. Require ANY partitions before.K. mℓ≥? ℓ≥ 1 monotone.Space.
variable (L:Side)(N:ℕ){z t' d s Λ ξ κ' ε α' τ:ℝ}{n m l b k':ℕ}
open Bera QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby QCD.Acre.Stratum.MarchQ.Suburb
open Suburb.Melt.Lobby.LeaseV LeaseV.Advent Suburb.Affair.Nimbus
variable (p:I→Site c)(q:I→Bool) (T: Finset (Finset I)) (E: Reel c N I J)(S₇:Finset J)(P:BudgetPoint)(F:Film c N I D)
open Push Push.AbsoluteSums Metric
variable {a b1 C M γ η :ℝ} (w:I→ℝ)
set_option quotPrecheck false
local notation "Iv"=>T
-- abstraction.Sector separation if not same Tile.Plausible from utility below.
variable {S T' r Bc:ℝ}
open FlareV Jets.Touch
set_option quotPrecheck false
local notation "Q0"=> taxK L τ 1
local notation "Q1"=> taxK L τ (7/8)
local notation "qv"=> taxK L τ (1/64)
local notation "α1"=> (1/32:ℝ)
local notation "α0"=> (3/32:ℝ)
local notation "v'"=> volume_F F w
variable (hc: Film.Stock N F P.B (taxK L τ 1) (3/32) v (taxK L τ (1/64))⁻¹ (fun _=>1)) (hC: F.Beat N p q P.threshold)(hp: HarvestV T l P.B p w M α1)

include hp hc hC
lemma valencyS (hK:Q1*M ≤ Q0): Film.Stock N v' P.B Q1 (1/16) v qv⁻¹ (fun _=>1):=by
     apply filmBoost F q p w P.threshold hC; obtain ⟨g,H,h⟩:=hc.price; refine ⟨g,H,fun i=> budget_mono (h i) ?_ ?_⟩
     · intro j; split; swap; · exact le_rfl
       unfold Film.fares GasP.taxed; refine mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (mul_nonneg (prod_nonneg (fun _ _=>abs_nonneg _)) ((show 0 ≤ Film.glyph N F 1 j v from load_nn ..).trans (H j 1)))) (Real.exp_pos _).le
     intro j; let s:= (F.addr j).place; let n:=(F.addr j).inv.card; let a:= coverNumber P.B s; have hn:n>0:=card_pos.mpr (F.addr j).alive; have hG:0 ≤ g j:=(show 0 ≤ Film.glyph N F 1 j v from load_nn ..).trans (H j 1); have hQ : Q1 ≤ Q0:= Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num:(7/8:ℝ) ≤1) (fan_pos ..).le)
     split_ifs; swap; · exact le_rfl
     change Q1^n*((∏ i∈(F.z j),|w i|)*g j)*Real.exp ((1/16:ℝ)*(a:ℝ)) ≤ Q0^n*((∏ i∈(F.z j),|(1:ℝ)|)*g j)*Real.exp (α0*(a:ℝ)); simp only [abs_one,prod_const_one,one_mul]
     let P':= ∏ i∈ F.z j,|w i|; let φ:=Real.exp ((1/16:ℝ)*(a:ℝ)); let ζ:=Real.exp (α1*(a:ℝ)); by_cases ht:F.z j∈T
     · have he : Q1^n*P' ≤ Q0^n:=by
              obtain ⟨i,hi⟩:= Nat.exists_eq_succ_of_ne_zero hn.ne'; rw [hi,pow_succ,pow_succ]; refine le_trans ?_ (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hQ i) (Real.exp_pos _).le); rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (hp.cents _ ht) (Real.exp_pos ..|>.le)).trans hK) (pow_nonneg (Real.exp_pos _).le i)
       rw [←mul_assoc]; apply mul_le_mul; · exact mul_le_mul_of_nonneg_right he hG
       · exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
       · exact (Real.exp_pos _).le
       exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) hG
     have he:P' ≤ζ:= (hp.score _ ht (hC.commits _) s (hC.spark j)).trans ((mul_le_of_le_one_left (Real.exp_nonneg _) (by norm_num)))
     calc
       Q1^n*(P'*g j)*φ ≤ Q1^n*(ζ*g j)*φ:=by gcongr; exact pow_nonneg (Real.exp_nonneg _) _
       _= Q1^n*g j*Real.exp (α0*(a:ℝ)):=by rw [←expDeal]; ring
       _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hQ n) hG) (Real.exp_pos _).le
omit hp hc hC
open Massive.Poised QCD.Kit
lemma valveTime (hv:1≤v)(ht:E.Occupant p q v P k α1 t (fun _=>1)):SC.Valve E p q v P.threshold P.B α1 t (fun _=>1):=by -- k not declared? k root
    obtain ⟨f,h,hX⟩:=ht.reserve; simp only [abs_one,prod_const_one,one_mul] at h; refine ⟨ht.booked,f,fun i V=> ?_,?_⟩; swap; · simpa only [one_mul]
    have hp:=zero_lt_one.trans_le hv; by_cases hV:Healthy P.threshold (E.addr i).support V; swap; · rw [Reel.mist, masked_ne _ _ _ _ hV]; obtain ⟨j,hj⟩:= ht.booked.stays i; unfold Tablet.credits; rw [map_zero,Cove.load_zero]; exact (hX i j hj).travels
    obtain ⟨j,hj⟩:= ht.booked.stays i; rw [Reel.mist,masked_eq _ _ _ _ hV, Tablet.polite_bill _ _ (ht.booked.stage i V).1 hp]; let x:= Reel.speaker q E i V; exact (viewer (p j) x k hp).trans ((hX i j hj).pole V hV [] (by simp) (by simp)) -- args.
lemma warmWork (hV:1≤v)(ht:E.Occupant p q v P k (1/8) t (fun _=>1))(hp:HarvestV T 1 P.B p w M α1)(he:∀ i,E.z i∉ T): SC.Valve (volume_up E w) p q v P.threshold P.B α1 t (fun _=>1):=by
    obtain ⟨f,h,hX⟩:= ht.reserve; simp only [abs_one,prod_const_one,one_mul] at h; let d i:= give w (E.z i); let g(i:J):= ‖d i‖* f i; have hf i:0 ≤ f i:=by obtain ⟨j,hj⟩:= ht.booked.stays i; exact (hX i j hj).travels
    let V':= volume_up E w; apply valveTime N p q V' P hV; refine (show V'.Occupant p q v P k α1 t (fun _=>1) from ⟨decorates E q p w ht.booked,g,?_,?_⟩) -- ht.
    · simp only [abs_one,prod_const_one,one_mul]; intro i; apply budget_mono (h i); · intro j; exact ite_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (hf j)) (Real.exp_nonneg _)) le_rfl
      intro j; have hd : ‖d j‖ ≤ Real.exp (α1*(coverNumber P.B (E.addr j).support)):=by simp only [d,give,norm_prod,Complex.norm_real,Real.norm_eq_abs]; exact (hp.score _ (he j) (ht.booked.stays j) _ (ht.booked.stamp j)).trans (mul_le_of_le_one_left (Real.exp_nonneg _) (by norm_num))
      split; swap; next ho=> rw [if_neg (show i∉ (E.addr j).support from ho)]
      next ho=> rw [if_pos (show i∈ (E.addr j).support from ho)]; let a:= coverNumber P.B (E.addr j).support; let C:=Real.exp (α1*a); change g j * C ≤ f j * Real.exp _; have he: g j ≤ C*f j := mul_le_mul_of_nonneg_right hd (hf _); apply le_trans (mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)); rw [mul_comm C, mul_assoc]; apply mul_le_mul_of_nonneg_left _ (hf _); unfold C; rw [←Real.exp_add]; exact Real.exp_monotone (by change _ ≤1/8*(a:ℝ); linarith only [Nat.cast_nonneg (α:=ℝ) a])
    · intro i j hj; rw [show Reel.speaker q V' i= d i • Reel.speaker q E i from funext fun U=> Eq.trans (congr_arg (pluck _ _) (congr_fun (lift_e E q p w ht.booked i) U)) (map_smul (pluck _ _) (d i) _)]; exact Counting.Terrain.scaledL (hX i j hj) _ -- inspect.
include L
lemma binsG (hv: ∀ i j:I,i ≠ j→ P.B*P.B ≤ separation (p i) (p j))(hW:∀ i,|w i| ≤ M)(hM:1 ≤ M)(ht:8≤ P.B)(h:2*M ≤ Real.exp (α1/64*P.B)): HarvestV ((univ:Finset (Finset I)).filter (fun i=>i.card≤1)) 1 P.B p w M α1:=by
    let T:= (univ:Finset (Finset I)).filter (fun i=>i.card≤1); have h0:ClusteredE (fun i:I=>i) T 1 P.B p:=by
        refine ⟨fun i hi=> (mem_filter.mp hi).2,?_,fun i _ he=> mem_filter.mpr ⟨mem_univ _,?_⟩,hv⟩; intro i; rw [show filter (fun j:I=> j=i) univ={i} from (by ext; simp),card_singleton]; simpa only [image_id'] using he
    rw [← pow_one M]; exact spacedPay L p T w _ ht h0 hW hM rfl (by norm_num) (by simpa only [pow_one]) -- sig
end LampV
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.LampV.valencyS
#print axioms YM.MassiveQCD.Cape.LampV.warmWork
#print axioms YM.MassiveQCD.Cape.LampV.binsG
