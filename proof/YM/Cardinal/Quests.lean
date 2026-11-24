import YM.Cardinal.Quad
/-!
 # Single arrangements in actual Units. Caps pre weights on pointed/reference layouts.P composed with updates.Yes.
   No explicit global identity in this run of the one-source cone. (All labels including that one use actual indicators; net also pays that weight). 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
-- Step references. No common label-union across books demanded. `w x partial` eq at outgoing health.Loosen.a' . Seat.S. set covering.
variable (x:Label d) (q:Bool) (Pt:BudgetPoint)
-- General base rank+remainder.R Over variant.Mert.Lo.Q.S.Defs.K
section
variable {Pt A H x q b} (G:CentreFrame (c:=c) Pt v x q A b (r+1) E K)
set_option quotPrecheck false
local notation "o"=> wrap c b
local notation "bp"=> pot (r+1) c b
local notation "Z!"=>basePack A b q d x G.moor (r+1)
local notation "W'"=> seed_w (a*coverNumber Pt.B (pot (r+1) c b))*β*wealth x.val Pt.threshold v
variable (V:Grid c)
local notation "Tq"=> goldM q
local notation "p!"=>fun (_:Iris.alpha)=>wrap c b
local notation "r!"=>fun (_:Iris.alpha)=>q
namespace Flyer
variable (Q:Puff c 6 I q)(S:I→Support c) (hQ: Seal 6 (wrap c b) Q)
variable (hp: Pilot H A d m k n j r α β) (hs: Pt.order=m)(ht: Pt.power=k)(hb:30*(r+1) ≤ c.val)(hS: ∀ i, (Q.addr i).support ⊆ S i)(heP:∀ i,pot (r+1) c b ⊆ S i)
variable (f g:I→ℝ)(hf:∀ i, Flame (Q.fill i) Pt (S i) (wrap c b) v n j (f i))(hg:∀ i, Sight (Q.addr i).support (wrap c b) l Pt v (Q.fill i) (g i))
variable (eT':ℝ)(hA: Ac.Hit S Pt.B f eT' t)(hV:1≤v) (ha:0≤eT')(hΩ:Ac.Hit S Pt.B g eT' u)
open QCD.Relight QCD.Ruby -- maybe fail
include hp hf hQ hA ha hs hS
lemma distills : ∃ p:I→Label d,(∀ i,Beacon.ActionTest H b (Q.fill i) (p i).val) ∧∀ i,moored (p i).val q:=by
    choose p h hp' using fun i=> Beacon.obtainsL (d:=d) H b (Q.fill i) ((hf i).sight.use 1 (Next.Foundations.one_healthy _ _ Pt.threshold_pos.le)|>.of_le (Nat.cast_le.mpr (hp.order.trans hs.ge))) fun u=> funext fun _=> hQ.shade i ..
    exact ⟨p,h,fun i=> Orientation.actor H b _ q _ (h i) (Q.beams i)⟩
omit hS
variable {p:I→Label d}(hc:∀ i, Beacon.ActionTest H b (Q.fill i) (p i).val) (hw:∀ i, moored (p i).val q)
local notation "pc"=> fun i=> wealth (p i).val Pt.threshold v
include hV ht hc hS
lemma toll_ps : (∀ i, wealth (p i).val Pt.threshold v≤α*f i) ∧ SumBudget (fun i=> wealth (p i).val Pt.threshold v*Real.exp (eT'*coverNumber Pt.B (S i))) (α*t)∧Summable p:=by
    have he(i):=hp.earn _ b _ (p i) (S i) _ _ (f i) hs ht (zero_lt_one.trans_le hV) (hf i) (hc i)
    let y:=pc
    have hY: SumBudget (fun i=> y i*Real.exp (eT'*coverNumber Pt.B (S i))) (α*t):= budget_mono (budget_scale (zero_le_one.trans hp.light) (hit_collect o S f (fun i=> hS _ ((hQ.anchor i) ▸ (Q.addr i).anchor)) hA)) (fun i=>mul_nonneg (wealth_ge ..) (Real.exp_pos _).le) fun i=> (mul_le_mul_of_nonneg_right (he i) (Real.exp_pos _).le).trans_eq (mul_assoc ..)
    exact ⟨he, hY, shieldC p (Summable.of_nonneg_of_le (fun i=> wealth_ge ..) (fun i=> le_mul_of_one_le_right (wealth_ge ..) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))) hY.2.1) Pt.threshold_pos (zero_lt_one.trans_le hV)⟩
omit hA hs ht ha hp hV hQ hf hS hc
noncomputable def Ypack (hv:∀ i,wrap c b∈S i): Puff c 6 I q:=⟨fun i=>⟨o,S i,hv i⟩, Q.fill,Q.beams⟩
variable (hψ:∀ i,wrap c b ∈ S i)
noncomputable def Vpack (_Q:Puff c 6 I q) {b:Cover} (A:Exhibit U){p:I→Label d} (hw:∀ i,moored (p i).val q) (hv:∀ i, wrap c b∈S i): Puff c 6 I q:=⟨fun i=> ⟨wrap c b,S i,hv i⟩,fun i=> graphs d A b (p i),fun i=> Orientation.graphing _ _ _ _ q (hw i)⟩
noncomputable def sub_pack (X Y:Puff c 6 I q) : Puff c 6 I q:=⟨X.addr, X.fill-Y.fill,fun i V=> by
     have hp:=Hom.smul (Y.beams i V) (-1:ℂ); rw [neg_one_smul] at hp; change Hom q (X.fill i V-Y.fill i V); exact (sub_eq_add_neg (X.fill i V) (Y.fill i V)).symm ▸ Hom.add (X.beams i V) hp⟩
local notation "Y!"=>Ypack Q S hψ
local notation "V!"=>Vpack S Q A hw hψ
local notation "X!"=>sub_pack (Y!) (V!)
include hp hf hQ hA hs ht hb hV hc hS hw heP ha
open QCD.Loom QCD.Stew QCD.Creek
lemma worked :
    let Z:=sub_pack (Ypack Q S hψ) (Vpack S Q A hw hψ)
    Seal 6 o (V!) ∧ Seal 6 o (Y!) ∧ Seal 6 o Z ∧
    (∀ i, Flame (graphs (c:=c) d A b (p i)) Pt (pot (r+1) c b) (wrap c b) v n j (β*wealth (p i).val Pt.threshold v)) ∧
    (∀ i, ActionTest H b (Z.fill i) (0:Pol d)) ∧ ∃ g:I→ℝ,(∀ i,Flame (Z.fill i) Pt (S i) (wrap c b) v n j (g i))∧ Ac.Hit S Pt.B g eT' ((1+β*α)*t) :=by
    intro Z; obtain ⟨he,hL,hZ⟩:= toll_ps Q S hQ hp hs ht hS f hf eT' hA hV ha hc
    have hv':=zero_lt_one.trans_le hV
    let Y:=Y!; let V:=V!; let g(i):= β*wealth (p i).val Pt.threshold v; let z(i):=(1+β*α)*f i; have h0(i): Flame (V.fill i) Pt (pot (r+1) c b) o v n j (g i):= hp.bill c b _ _ (p i) hs ht (by omega) hv'
    have hw'(i): Flame (V.fill i) Pt (S i) o v n j (g i):= Facets.across (h0 i) _ (heP i) -- ambiguous
    have hz (i): Z.fill i= Y.fill i+ (-1:ℂ) • V.fill i:= by rw [neg_one_smul, ← sub_eq_add_neg]; rfl
    have hU(i): Flame (Z.fill i) Pt (S i) o v n j (z i):=by
       rw [hz]; apply leFlame (flare_add Pt (S i) (Y.fill i) _ (hf i) (flare_by Pt _ _ (hw' i) (-1)) hv'.le); rw [norm_neg,norm_one,one_mul]; unfold z; rw [add_mul, one_mul]; exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left (he i) (zero_le_one.trans hp.funds)).trans_eq (mul_assoc ..).symm)
    refine ⟨⟨fun _=>rfl, fun i=> (hw' i).sight.room,fun i=> (hw' i).sight.borel, fun i U tg=> Orientation.graphite _ _ _ _ tg U,fun i=> (hw' i).sight.gate⟩,⟨fun _=>rfl,fun i=> (hf i).sight.room,fun i=> (hf i).sight.borel,hQ.shade,fun i=> (hf i).sight.gate⟩,⟨fun _=>rfl, fun i=> (hU i).sight.room,fun i=> (hU i).sight.borel,fun i U g=> ?_,fun i=> (hU i).sight.gate⟩,h0,fun i=>?_,z,hU,?_⟩
    · change slots 6 g (Q.fill i _-graphs d A b (p i) _) = _; rw [map_sub,hQ.shade,Orientation.graphite];rfl
    · rw [hz]; have hx:= actsPlus H b d (Q.fill i) ((-1:ℂ) • V.fill i) (p i).val ((-1:ℂ) • (p i).val) (hc i) (acting H b d (graphs d A b (p i)) _ (hp.tested _ b _ hb) _)
      rw [neg_one_smul] at hx -- first F side.Both.
      convert hx using 1
      · rw [neg_one_smul]; rfl
      rw [show (-1:ℂ) • (p i).val = -(p i).val from neg_one_smul ℂ (show Pol d from (p i).val) ,add_neg_cancel]
    intro i; have hT:0 ≤ 1+β*α:=add_nonneg zero_le_one (mul_nonneg (zero_le_one.trans hp.funds) (zero_le_one.trans hp.light)); convert! budget_scale hT (hA i) using 1; funext j; split
    next ht=> exact mul_assoc ..
    next ht=> rw [mul_zero]
end Flyer
end
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Flyer.worked
