import YM.Helio.Tel
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
variable (G:Silo c)(x:Axis)
abbrev EraM (c:Side):= {d:Tick c//fertile d}
local notation "L"=> EraM c
lemma sumEra (α:Axis)(hp:Run.Pack id id η δ B U q G A)(ht:0<η) (V:Grid c):
 (∑ d : EraM c, Stew.block d.val.1 (d.val.2.1+step α) (newDay α d G V))= Lat.shift 0 V α*U V-U V*Lat.shift 0 V α:=by
    rw [← ray V α G hp]; symm
    let f d:= Stew.block (d:Tick c).1 (d.2.1+step α) (newDay α d G V); change ∑ i,f i=∑ i:L, f i.val
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i:Tick c=>fertile i) f, show ∑ i: {i:Tick c//¬ fertile i}, f i.val=0 from ?_,add_zero]; rotate_left
    refine sum_eq_zero fun i _=>?_ ; unfold f; rw [zeroRoute G α i.val hp i.2 ht]; exact map_zero (blockL _ _)
-- install accounts with B.Hit move
open Reserves
lemma rods (c:Side)(p:Support c)(b n B:ℕ) (K:ℝ)(hK:∀ Q:Support c,tribute B b n Q ≤ K* Run.rent 1 B Q) : tribute B b n p≤ K*Run.rent 1 B p := hK p
lemma candle (Ct:ℝ)(hq:Run.Pack id id η δ B U q G A)(hp:0≤Ct)(b n:ℕ)(hh:0≤ a)(hz:2*(a+3)≤δ)(K:ℝ)(hk:0≤K)(hK:∀ X:Support c,tribute B b n X ≤ K*Run.rent 1 B X): Ac.Hit (fun i:L=> strip x i.val) B (fun i=> (Ct*basePrice A x i.val)*tribute B b n (strip x i.val)) a (payment 1 (4*B+2) 0 1 1 ((Ct*K)*(q+q)) a 0):=by
    let F(i:L): RegularAddress c:=⟨i.val.1,strip x i.val,(primeM x i.val i.2).1⟩
    let Y:=strip x ∘ (Subtype.val (p:=fun i:Tick c=>fertile i)); let o(i:L):= (F i).site; let V:Gem c 6 L := ⟨F,fun _ _=>0⟩; let f (i:L):=basePrice A x i.val; have hf(i:L):0≤ f i:=add_nonneg (need hq _) (need hq _); let g(i:L):=Ct*f i*tribute B b n (Y i); have hg(i:L):0≤g i:=mul_nonneg (mul_nonneg hp (hf i)) (by unfold tribute; positivity)
    have hv:Anchored o g (fun i=> coverNumber B (Y i)) (a+2) ((Ct*K)*(q+q)):=by
       intro i
       let κ:= Ct*K; apply budget_mono (budget_scale (show 0≤ κ from mul_nonneg hp hk) (footA x hq (0:Site c) i)) (fun j=> ite_nonneg (mul_nonneg (hg j) (Real.exp_pos _).le) le_rfl); intro j; change (if o j=i then g j*Run.rent (a+2) B (Y j) else 0) ≤ κ*(if o j=i then f j*Run.rent δ B j.val.2.2 else 0); split; swap; · simp
       next hi=>
        have he: Run.rent 1 B (Y j)*Run.rent (a+2) B (Y j) ≤ Run.rent δ B j.val.2.2:=by
            unfold Run.rent; rw [←Real.exp_add]; apply Real.exp_monotone; have h:(coverNumber B (Y j):ℝ) ≤ coverNumber B j.val.2.2 * (2:ℝ):= by exact_mod_cast (stripC x j.val j.2 B)
            nlinarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ a+3 by linarith),mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (α:=ℝ) (coverNumber B j.val.2.2))]
        calc
          _ ≤ ((Ct*f j)*(K*Run.rent 1 B (Y j)))*Run.rent (a+2) B (Y j):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK (Y j)) (mul_nonneg hp (hf j))) (Run.fair ..).le
          _ = (Ct*K*f j)*(Run.rent 1 B (Y j)*Run.rent (a+2) B (Y j)):=by ring
          _ ≤ _:= (mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hp hk) (hf j))).trans_eq (mul_assoc ..)
    -- assign via Stem
    change Ac.Hit Y _ g a _; apply Footprint.assigned id 1 (fun Y=> by simp) o g hg _ _ hv _ _ _ (fun i x p=> ?_) (v':=1) (fun i=> by simp) zero_le_one ⟨hh,zero_lt_one,by linarith⟩ g hg (by simp) -- signature tweak
    exact (Corona.extent (Y i) B p ((F i).anchor)).trans (by nlinarith )
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.candle
