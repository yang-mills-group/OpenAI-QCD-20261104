import YM.Helio.Trust
/-!
Aggregate a series of matrix cells into genuine Anchored Deposits per root: masks kept and closed under type.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C':ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder
variable {I:Type}(F:I→Pulse c→Bundle)(X Y:I→ℝ)
variable (x y:Site c)(V:Support c)
-- high about one cell.experimental.A
structure StockR (p:BudgetPoint)(F:Pulse c→Bundle)(ξ K L:ℝ):Prop where
       crop : Crop x y ξ V F K
       mask (U:Grid c)(h: Healthy p.threshold V U) : ‖F (settled U)‖ ≤ L
       empty : F (settled 1)=0
       nneg : 0≤ L
namespace StockR
local notation "Ω"=> StockR x y V p
variable (h:∀ i,StockR x y V p (F i) η (X i) (Y i))
include h in
lemma stakes (hh:Summable X)(ht:0<η)(hv:Summable Y): StockR x y V p (fun z=>∑' i,F i z) η (∑' i,X i) (∑' i,Y i):=by
        refine ⟨Crop.church X hh (fun i=>(h i).crop) ht,fun U hV=>?_,by simp_rw [fun i=> (h i).empty]; rw [tsum_zero],tsum_nonneg fun i=>(h i).nneg⟩
        have hk (i:I): ‖F i (settled U)‖≤ Y i:=(h i).mask U hV; have hm:= hv.of_nonneg_of_le (fun i=> norm_nonneg (_:Bundle)) hk; exact (norm_tsum_le_tsum_norm hm).trans (hm.tsum_le_tsum hk hv)
lemma thorough {X₁ Y₁:ℝ} (Z:Pulse c→Bundle) (hx:x∈V)(hy:y∈V)(h: StockR x y V p Z η X₁ Y₁)(hp:0 ≤ C)(ht:0<η)(hH: p.threshold ≤η)(hK: ∀ o∈V,∀(X:Grid c),∀ l:List (Directions su c), l≠ []→ List.length l≤p.order → (∀ i∈l,p.dirBound o i) → ‖leftDerivs (Z∘settled) l X‖ ≤ (1+(diameterQ B V:ℝ))^(b*n)*(C*X₁)*(p.threshold/η)) : let P: ParcelZ (c:=c):= ⟨x,y,V,Z∘settled⟩; let t:= tribute B b n V; P.Ticket p (t*X₁) (t*(Y₁+C*X₁*(p.threshold/η))) B :=by
       intro P' t; have hv:= h.crop; have hm:= h.nneg; have hz:= hv.1; have h0:= p.threshold_pos; let d:ℝ:=1+diameterQ B V; have hd:1≤d:=by unfold d; simp 
       have h₁: t=d^(b*n)*d^2:=by unfold t tribute d; rw [add_comm 2,pow_add]
       have h₂: d^2≤ t:=by rw [h₁]; exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hd)
       have ht0: 0≤ t:= (sq_nonneg d).trans h₂
       refine ⟨hx,hy,mul_nonneg ht0 hz,by change 0 ≤ t*(Y₁+C*X₁*(p.threshold/η)); positivity,hv.2.2.2.2.1,breeze hv ht,fun _ _=> milady hv ht _ _,fun g X=> hv.2.2.2.2.2 _ _,h.empty,fun X=>?_ ,fun o hO X hg l hL hV=> ?_⟩ -- hz etc
       · change ‖Z (settled X)‖*d^2 ≤ t*X₁; exact (mul_le_mul (hv.2.2.2.1 _ (citizenship c ht X)) h₂ (sq_nonneg _) hz).trans_eq (mul_comm ..)
       by_cases hx:l=[]; swap
       · change _*d^2≤ _; refine (mul_le_mul_of_nonneg_right (hK o hO X l hx hL hV) (sq_nonneg d)).trans ?_; change d^(b*n)*_*_*d^2 ≤ _; simp only [mul_add t]; apply le_trans (b:= t*(C*X₁*(p.threshold/η))) (le_of_eq (by rw[h₁]; ring)); exact le_add_of_nonneg_left (mul_nonneg ht0 hm)
       rw [hx]; change ‖Z (settled X)‖*d^2 ≤_; refine (mul_le_mul (h.mask X hg) h₂ (sq_nonneg _) hm).trans ?_; rw[mul_comm Y₁]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) ht0
end StockR
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.StockR.thorough
#print axioms YM.QCD.Entr.Meridian.StockR.stakes
