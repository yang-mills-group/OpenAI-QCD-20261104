import YM.Magi.ProbeV
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
structure HarvestV (T:Finset (Finset I))(l B:ℕ)(p:I→Site c)(w:I→ℝ)(r e:ℝ) : Prop where
      single : ∀ i∈ T, i.card≤ l
      cents : ∀ i∈ T,(∏ j∈i,|w j|) ≤ r
      score : ∀ i:Finset I,i∉ T→ i.Nonempty →∀ Q:Support c,i.image p⊆ Q → (∏ j∈i, |w j|) ≤ (1/2)*Real.exp (e*coverNumber B Q)
-- lattice widths. predicate Ph.Th.Til. use caps γ. from OPE.Log.error.C.
variable {α :Type}(f:I→α)[DecidableEq α]
structure ClusteredE (T:Finset (Finset I))(l B:ℕ)(p:I→Site c):Prop where
      slots : ∀ i∈T,i.card≤l
      price : ∀ i:α,(Finset.univ.filter (fun j:I=> f j=i)).card≤ l
      shapes :∀ i: Finset I,i.Nonempty →(i.image f).card ≤1→ i∈T
      spaced : ∀ i j:I,f i≠f j → B*B ≤ separation (p i) (p j)
lemma spacedPay (ht:8 ≤ B)(H:ClusteredE f T l B p)(hp:∀ j, |w j|≤ M)(hM:1 ≤ M)(h:L=L) (hA:0 ≤ a)(hG:2*M^l ≤ Real.exp (a/64*B)): HarvestV T l B p w (M^l) a:=by
    have he:0≤M:= zero_le_one.trans hM; have hi(i:Finset I): (∏ j∈i,|w j|) ≤ M^i.card:=by simpa only [prod_const] using! (prod_le_prod (s:=i) (fun i _=>abs_nonneg (w i)) (fun i _=>hp i))
    refine ⟨H.slots,fun i hh=> (hi i).trans (pow_le_pow_right₀ hM (H.slots _ hh)),?_⟩
    intro i hv hx Q hF; have hz:1<(i.image f).card:=lt_of_not_ge fun h=> hv (H.shapes i hx h)
    let τ:=i.image f; let A:= ↥τ; choose m hm hk using fun x:A=>mem_image.mp x.property
    have hu : (Finset.univ:Finset A).image (p∘m)⊆Q:=by intro j hj; obtain ⟨x,hx,rfl⟩:= mem_image.mp hj; exact hF (mem_image_of_mem _ (hm _)) -- type fix
    have hf:(Finset.univ:Finset A).card= τ.card:=by simp [A]
    have hs: B*τ.card ≤ 64*coverNumber B Q:=hf ▸ OPE.Log.separatedMarks (univ:Finset A) (p ∘ m) (fun i _ j _ he=>H.spaced (m i) (m j) (fun h=>he (Subtype.ext ((hk _).symm.trans (h.trans (hk _)))))) ht (by omega) (hf.symm ▸ hz) Q hu
    have hh: i.card ≤ l*τ.card:=by let g (u:α):=Finset.univ.filter (fun j=> f j=u); have ht:i⊆τ.biUnion g:=fun i hi=> mem_biUnion.mpr ⟨_, mem_image_of_mem _ hi,mem_filter.mpr ⟨mem_univ i,rfl⟩⟩; refine (card_le_card ht).trans ((card_biUnion_le ..).trans ((sum_le_sum (g:=fun _=>l) (fun u _=> H.price u)).trans_eq (by rw [sum_const]; exact Nat.mul_comm ..)))
    apply le_trans ((hi i).trans (pow_le_pow_right₀ hM hh)); rw [pow_mul]; let t:=coverNumber B Q; have hf:2*(M^l)^τ.card ≤ (2*M^l)^τ.card:=by rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact (pow_one (2:ℝ)).symm.le.trans (pow_le_pow_right₀ (by norm_num) hz.le)
    have hx : (2*M^l)^τ.card ≤ Real.exp (a*t):=by
           apply le_trans (pow_le_pow_left₀ (show 0≤2*M^l from by positivity) hG _) _; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_right (show (B:ℝ)*τ.card ≤64*(t:ℝ) from by exact_mod_cast hs) hA]
    change (M^l)^_ ≤ _; linarith only [hf,hx]
variable {S T' r Bc:ℝ}
open FlareV Jets.Touch
set_option quotPrecheck false
local notation "Q0"=> taxK L τ (31/32)
local notation "Q1"=> taxK L τ (15/16)
local notation "qv"=> taxK L τ (1/64)
local notation "α1"=> (1/32:ℝ)
local notation "α0"=> (3/32:ℝ)
local notation "v'"=> volume_F F w
variable (hc:Bearing p q T E S₇ L l m v τ Λ P S F) (hp: HarvestV T l P.B p w M α1)
lemma expDeal (v:ℕ) : Real.exp (α1*(v:ℝ))* Real.exp ((1/16:ℝ)*(v:ℝ))= Real.exp (α0*v):=by rw [←Real.exp_add]; congr 1; ring
include hp hc
lemma valencyV (hK:Q1*M ≤ Q0): Film.Stock N v' P.B Q1 (1/16) v qv⁻¹ (fun _=>1):=by
     apply filmBoost F q p w P.threshold hc.flag; obtain ⟨g,H,h⟩:=hc.cost.price; refine ⟨g,H,fun i=> budget_mono (h i) ?_ ?_⟩
     · intro j; split; swap; · exact le_rfl
       unfold Film.fares GasP.taxed; refine mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (mul_nonneg (prod_nonneg (fun _ _=>abs_nonneg _)) ((show 0 ≤ Film.glyph N F 1 j v from load_nn ..).trans (H j 1)))) (Real.exp_pos _).le
     intro j; let s:= (F.addr j).place; let n:=(F.addr j).inv.card; let a:= coverNumber P.B s; have hn:n>0:=card_pos.mpr (F.addr j).alive; have hG:0 ≤ g j:=(show 0 ≤ Film.glyph N F 1 j v from load_nn ..).trans (H j 1); have hQ : Q1 ≤ Q0:= Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num:(15/16:ℝ) ≤31/32) (fan_pos ..).le)
     split_ifs; swap; · exact le_rfl
     change Q1^n*((∏ i∈(F.z j),|w i|)*g j)*Real.exp ((1/16:ℝ)*(a:ℝ)) ≤ Q0^n*((∏ i∈(F.z j),|(1:ℝ)|)*g j)*Real.exp (α0*(a:ℝ)); simp only [abs_one,prod_const_one,one_mul]
     let P':= ∏ i∈ F.z j,|w i|; let φ:=Real.exp ((1/16:ℝ)*(a:ℝ)); let ζ:=Real.exp (α1*(a:ℝ)); by_cases ht:F.z j∈T
     · have he : Q1^n*P' ≤ Q0^n:=by
              obtain ⟨i,hi⟩:= Nat.exists_eq_succ_of_ne_zero hn.ne'; rw [hi,pow_succ,pow_succ]; refine le_trans ?_ (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hQ i) (Real.exp_pos _).le); rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (hp.cents _ ht) (Real.exp_pos ..|>.le)).trans hK) (pow_nonneg (Real.exp_pos _).le i)
       rw [←mul_assoc]; apply mul_le_mul; · exact mul_le_mul_of_nonneg_right he hG
       · exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
       · exact (Real.exp_pos _).le
       exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) hG
     have he:P' ≤ζ:= (hp.score _ ht (hc.flag.commits _) s (hc.flag.spark j)).trans ((mul_le_of_le_one_left (Real.exp_nonneg _) (by norm_num)))
     calc
       Q1^n*(P'*g j)*φ ≤ Q1^n*(ζ*g j)*φ:=by gcongr; exact pow_nonneg (Real.exp_nonneg _) _
       _= Q1^n*g j*Real.exp (α0*(a:ℝ)):=by rw [←expDeal]; ring
       _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hQ n) hG) (Real.exp_pos _).le
-- E price separate.Bill unfilled labels.Pre.L.Wind.Act. After dilation on unmasked.Payout.
local notation "Eu"=> volume_up E w
lemma gladeP (hB: M ≤ (1/2)*Λ):∃ g:J→ℝ,(∀ i,0 ≤ g i) ∧ Ac.Hit (fun i=>(E.addr i).support) P.B g α1 ((1/2)*S) ∧∀ i,i∉S₇→∀ V:Grid c,Tablet.credits v (Reel.mist Eu P.threshold i V)≤ g i:=by
     obtain ⟨f,H,h⟩:= hc.boost.back; let u (i:J):=∏ j∈ E.z i,|w j|; let g(i:J):= if i∈ S₇ then 0 else u i*f i
     have hu(i):0≤u i:= prod_nonneg (fun i _=>abs_nonneg _); have hf i:0≤ f i:= (Creek.load_nn ..).trans (H i 1); have hh(i:J):0≤g i:=ite_nonneg le_rfl (mul_nonneg (hu _) (hf _)); refine ⟨g,hh,fun i=>?_,?_⟩
     · apply budget_mono (budget_scale (show (0:ℝ)≤1/2 from by norm_num) (h i)); · exact fun j=>ite_nonneg (mul_nonneg (hh _) (Real.exp_pos _).le) le_rfl
       intro j; split; swap; next ho => rw [mul_zero]
       next he=>
            dsimp only; let s:=(E.addr j).support; let a:= coverNumber P.B s; by_cases ho:j∈S₇; · rw [show g j=0 from if_pos ho,zero_mul]; refine mul_nonneg (by norm_num) (?_); simpa only [if_pos he] using (h i).1 j -- dsimp
            have hj:g j=u j*f j:= if_neg ho; by_cases hP:E.z j∈ T
            · have hΩ:u j≤ 1/2 * Λ:= (hp.cents _ hP).trans hB
              have hA:0≤Λ:=by nlinarith only [hu j,hΩ]
              rw [hj,show boosts T E S₇ Λ j=Λ from if_neg (by simp [ho,hP])]; rw [← mul_assoc,←mul_assoc]; apply mul_le_mul
              · exact mul_le_mul_of_nonneg_right hΩ (hf _)
              · exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
              · exact (Real.exp_pos _).le
              have hp0:= hf j; positivity
            have hP':u j ≤ (1/2)*Real.exp (α1*(a:ℝ)):= hp.score _ hP (hc.boost.book.stays _) s (hc.boost.book.stamp _)
            rw [hj,show boosts T E S₇ Λ j=1 from if_pos (by simp [hP])]
            calc
              u j*f j*Real.exp (α1*(a:ℝ)) ≤ ((1/2)*Real.exp (α1*a))*f j * Real.exp (α1*(a:ℝ)):=by have hp0:=hf j; gcongr
              _=1/2*(f j*(Real.exp (α1*(a:ℝ))*Real.exp (α1*(a:ℝ)))):=by ring
              _ ≤ _:=by rw [one_mul,←expDeal a]; have hθ: (1/32:ℝ) ≤ 1/16:=by norm_num
                        have he:= hf j; gcongr
     intro j hj V
     have he(V:Grid c): Reel.mist Eu P.threshold j V= give w (E.z j) • Reel.mist E P.threshold j V:=by
           unfold Reel.mist; rw [lift_e E q p w hc.boost.book]; by_cases h:Healthy P.threshold (E.addr j).support V; rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ (show Healthy P.threshold ((volume_up E w).addr j).support V from h)]
           rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (show ¬ Healthy P.threshold ((volume_up E w).addr j).support V from h),smul_zero]
     rw [he]; unfold Tablet.credits; rw [map_smul,load_scale,show g j=_ from (if_neg hj : g j = u j*f j),show u j=‖give w (E.z j)‖ from (by simp only [give,norm_prod, Complex.norm_real,Real.norm_eq_abs,u])]; exact mul_le_mul_of_nonneg_left (H j V) (norm_nonneg _)
end LampV
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.LampV.gladeP
#print axioms YM.MassiveQCD.Cape.LampV.spacedPay
#print axioms YM.MassiveQCD.Cape.LampV.valencyV
