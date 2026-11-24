import YM.MassiveQCD.Plate.Beam
/-! # Into the new K realm. Only certain layouts with *contract* across all frequencies.
 Provide through desired taxes at incoming scale on SAME full-source books. Subsequent use
 with enhanced frequencies (test families) not on zero or momentum-only rail.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)(Y: Ruby.Hue c N J)(F: Patron.Rail c (ample N I) U)
local notation "M"=> Ribbon.ample N I
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "b'"=>banknote N p φ
local notation "d!"=> withdraw N p θ
local notation "F!"=> pursue N p θ F φ r
local notation "Y!"=> radial I Y
noncomputable def limb (t:ℝ): Patron.Rail c (ample N I) (Plot (Y!) (F!)) := Trail (Y!) (F!) t
local notation "K!"=> limb N p θ φ r Y F
open ConnectedActivityE6 Pressure Pressure.Stores OrbitG Sway
noncomputable def valH (f: EvenA c m→EvenA c N)(X: Patron.Rail c m J) : Patron.Rail c N J:= ⟨X.addr,fun i U=> f (X.warp i U)⟩
noncomputable def faultK (F: Patron.Rail c (ample N I) U) := valH N 
 (fun i:EvenA c (ample N I)=> vacR (Spine I) (Keys c N) (withdraw N p φ i)) F
local notation "K0"=> faultK N p φ F
lemma limbsColor {Y:Ruby.Hue c N J}{F: Patron.Rail c N E}(h:∀ i,shadeG (F.warp i))(hr:∀ i,shadeG (Y.mean i)) (t:ℝ) (x:Plot Y F): shadeG ((Trail Y F t).warp x):=by
    intro i z; refine congr_arg Subtype.val (?_: sways (Lat.rotates N z) _= _); dsimp only [Trail]; unfold payer; rw [gauge_flags]; split; swap; · exact map_zero _
    rw [map_prod]; apply prod_congr rfl; intro j _; rcases j with j|j; exact Subtype.ext (h j i z)
    unfold Ruby.flower sparkY; simp only [Sum.elim_inr]; let v:= sways (Lat.rotates N z); rw [map_sub,map_exp v (show Continuous v from phare _),map_one,show v _=Y.mean j i from Subtype.ext (hr j i z)] -- orientation nr
variable (h:Pill F t φ O.B v w)(hY:Wax Y t O.B A a θ)(ht:∀ i, shadeG (Y.mean i)) (hp:0< r)(hv:1 ≤θ)(hw:r*θ ≤ φ)(he:0 ≤ A)(hθ:1 ≤w)(hr:0≤v) (hk:∀ i U, Well N p φ q (F.warp i U))
include hk hv
lemma engraved (V:Grid c)(y:Plot Y! F!): Well N p θ q ((K! t).warp y V):=by
   let f:= F!; let z:=y.val; change Well N p θ q (payer Y! F! t V z); unfold payer; split; swap; · exact Well.zeroV
   apply Well.product; intro x _; have hT:=zero_lt_one.trans_le hv
   rcases x with x|x
   · exact changeValid N p r φ θ q hT _ (hk x V)
   unfold Ruby.flower sparkY; simp only [Sum.elim_inr]; rw [sub_eq_add_neg]; apply Well.plus hT _ (Well.minus hT Well.oneV); apply Well.flash; rw [show (Y!).mean x V= b! (rootR R K (Y.mean x V)) from (real_sector ..).symm]; apply Mint.launch (s:=∅) (Mint.initiate _ hT _ ?_); unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
omit hk
lemma endowed (V:Grid c)(x:Plot (Y!) (F!)): (vacR (Spine I) (Keys c N)) (withdraw N p θ (((K! t).warp x V)))=((Trail Y (flightK K0 r) t).warp x V) :=by -- shape defeq
   let Z:= (vacR R K).comp (d!)
   change Z (payer Y! F! t V x.val)=payer ..; unfold payer; split
   next hh=> rw [if_pos (show flags t V∩ scopeK Y (flightK K0 r) x.val=badgeK (flightK K0 r) x.val from hh),map_prod]; refine prod_congr rfl ?_; intro i _; rcases i with i|i
             · change vacR _ _ (withdraw _ _ _ (changeBill N p r φ θ (F.warp i V)))=_; rw [changeLife N p θ φ r _ (zero_lt_one.trans_le hv)]; exact freeTurn .. 
             unfold Ruby.flower sparkY; simp only [Sum.elim_inr]; rw [map_sub,map_exp Z Z.toLinearMap.toContinuousLinearMap.continuous,map_one]; apply congr_arg₂ (·-·) _ rfl; apply congr_arg; rw [show (Y!).mean i V= b! (rootR R K (Y.mean i V)) from (real_sector ..).symm]; change vacR _ _ (withdraw N p θ _)=_; rw [Cupola.home N p θ (zero_lt_one.trans_le hv),off]
   next hh=> rw [if_neg (show ¬(flags t V∩ scopeK Y (flightK K0 r) x.val=badgeK (flightK K0 r) x.val) from hh)]; exact map_zero _
include h hY he hθ hr hv hw hk hp
lemma kettle_price (hm :1≤φ) (V:Grid c) : let _P:= F!; let x:= K! t; Kites.heartK x t V= changeBill N p r φ θ (Kites.heartK F t V)* NormedSpace.exp (Apron.bearing I c N (Kites.swarm Y V)):=by
   intro P R'; have hh:=zero_lt_one.trans_le hv; have hi:= portage N p θ q F φ r w h hp hh hw hk; have ht := WaxGov (I:=I) θ Y hY
   -- hφ may <1 if r small & target; raw F may not spend at ⦃≥1⦄ then `thermal.z` supplies at true φ≥1. add assumption.
   let Z:= changeBill N p r φ θ; have hB:heartK P t V= Z (heartK F t V):=by
       unfold Kites.heartK; let p':= Z.toLinearMap.toContinuousLinearMap; change _=p' _; rw [p'.map_tsum (profits _ V hm hθ h.sold hr t)] -- rw p defeq?
       refine tsum_congr (fun i=>?_); change tK P t V i=Z _; unfold tK; split; rename_i hf; rw [if_pos (show (separated (blocked (Ruby.home F)) i ∧ RG.flags t V = i.biUnion (oriD F)) from hf)]; exact (map_prod Z ..).symm; rename_i hf; rw [if_neg (show ¬(separated (blocked (Ruby.home F)) i ∧ RG.flags t V = i.biUnion (oriD F)) from hf)]; exact (map_zero Z).symm -- if need proof eq
   obtain ⟨h₁,h₂⟩:= ht.heated hv he V; refine (plenary (Y!) P V (profits P V hv hθ hi.sold hr t) ht.burns h₁ h₂).tsum_eq.trans ?_; rw [show (∑' i,tK P t V i)=Z (heartK F t V) from hB]; apply congr_arg; apply congr_arg; exact ((Apron.bearing I c N).toLinearMap.toContinuousLinearMap.map_tsum (hY.heated hv he V).1).symm
-- bounds include Loom.Power threshold.END
include ht
omit hθ hr he in
lemma lowerPill {t₀ v₀:ℝ}(hh:Quits (Trail Y! F! t) O.B 1 t₀ v₀ θ) : Pill (K! t) t θ O.B v₀ t₀:=by
    let X:= portage N p θ q F φ r w h hp (zero_lt_one.trans_le hv) hw hk
    exact ⟨plant _ _ (WaxGov (I:=I) θ Y hY).burns X.uses, fun i=> limbsColor M X.pigment (Y:=Y!) (fun i=> paySector (I:=I) (Y.mean i) (ht i)) t i, hh⟩
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.endowed
