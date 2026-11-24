import YM.QCD.House.Streams

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
set_option quotPrecheck false
local notation "B"=>radiusB τ
def guess (b:Mixed.Costs)(w:ι→ℝ) (u:I):ℝ:= ∏ i∈u,(Y.shellF).dues b w i
lemma condenses (b:Mixed.Costs){w p:ι→ℝ}(hp:(Y.suitcase F).Depth b w p) :
   let h u:= if Ac.Spark (Y.suitcase F).gP u then (Real.exp b.markSeed)^(roster u.toLeft).flags.card*(Y.guess b w u) else 0
   Ac.Hit (Y.fullA) (radiusB τ) h b.exponent (b.rootHit*(1-b.q)⁻¹):=by
    intro h x
    let P:=Y.suitcase F; have hh:= P.earned hp; have he:=hp.green; let t:=tariff (P.dues b w) (P.inks b p) (fun i=> b.markSeed *P.tenants i) b.reservePoly
    have hv:=touch_tail P.gP B hh x 0; simp only [ge_iff_le,Nat.zero_le,if_true,pow_zero,mul_one] at hv
    have hN i:0≤Y.guess b w i:=prod_nonneg fun t _=> (P.digits hp t).1
    refine budget_mono hv ?_ ?_
    · intro i; split; swap; · exact le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le; unfold h; split; exact mul_nonneg (by positivity) (hN _); exact le_rfl
    intro i; split
    swap; · exact hv.1 _
    next hk=>
    unfold h; split; swap; · rw [zero_mul]; exact hv.1 _
    next hx=>
    unfold touches; rw [if_pos ⟨hx,hk⟩,prod_mul_distrib]; apply mul_le_mul
    · change _≤ ∏ j∈i,t j; unfold t tariff; rw [Finset.prod_mul_distrib,← Real.exp_sum,← Real.exp_nat_mul,mul_comm (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (hN _); apply Real.exp_monotone
      have he': (roster i.toLeft).flags.card≤ P.sizeP i:=by
        have hp : (roster i.toLeft).flags.card≤ (roster i.toLeft).shares:= by unfold Stores.shares; omega -- maybe definition
        exact hp.trans (P.hitsP i)
      have hz : b.markSeed *((roster i.toLeft).flags.card:ℝ)≤ ∑ j∈i,b.markSeed * P.tenants j:=by rw [← mul_sum]; unfold Pipe.tenants; rw [← Nat.cast_sum]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he') he.marked
      rw [mul_comm _ b.markSeed]; rw [sum_add_distrib]; exact hz.trans (le_add_of_nonneg_left (sum_nonneg fun i _=> mul_nonneg (by have ht:=he.eps; positivity) (P.digits hp i).2))
    · unfold currency; rw [← Real.exp_sum]; apply Real.exp_monotone; rw [← mul_sum, ← Nat.cast_sum]; exact mul_le_mul (le_add_of_nonneg_right (by have h:=he.eps; positivity)) (Nat.cast_le.mpr (Ac.cover _ _ hx)) (Nat.cast_nonneg _) (le_add_of_le_of_nonneg he.price (by have h:=he.eps; positivity))
    · exact (Real.exp_pos _).le
    exact prod_nonneg fun i _=> hh.2.2.2.2.1 i

def Leaps (w:Reserve S→ ι→ℝ)(b: Costs)(p :ι→ℝ)(a:ℝ):Prop := ∀ i:Reserve S,let P:= Y.suitcase (allot i); P.Depth b (w i) p∧∀ s: Pipe.Clump S ι, ∀ V: Grid c,∀ χ:Chi, ‖token c N a (P.shootsP (prism T τ χ o.K V (allot i)) s)‖≤∏ j∈s,P.dues b (w i) j
-- Not necessarily uniform F but all effective χ. pass weights through likelihood sum
variable {w: Reserve S→ι→ℝ} {b:Costs} {p:ι→ℝ}{d a e v η t:ℝ}
def grass (w₀ :Reserve S→ι→ℝ)(b: Costs)(u:I):ℝ:= choiceS (fun i=> Y.guess b (w₀ i) u)
lemma localP (hs: Y.Leaps w b p a)(χ:Chi)(V:Grid c)(u:I): ‖token c N a (Y.vF u χ V)‖ ≤ grass Y w b u:=by
    unfold grass vF choiceS; rw [map_smul,map_sum,norm_smul]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>(hs i).2 u V χ))) (norm_nonneg _)).trans_eq ?_
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (Fintype.card (Reserve S):ℝ)⁻¹),smul_eq_mul]; rfl
lemma nonC (hs:Y.Leaps w b p a) (u:I):0≤ grass Y w b u :=by unfold grass choiceS; rw [smul_eq_mul]; exact mul_nonneg (by positivity) (sum_nonneg fun i _=> prod_nonneg fun j _=> ((Y.suitcase (allot i)).digits (hs i).1 _).1)
lemma cohort (hs:Y.Leaps w b p a): let h s:= if Ac.Spark (Y.shellF).gP s then (Real.exp b.markSeed)^(roster s.toLeft).flags.card*grass Y w b s else 0
      Ac.Hit Y.fullA (radiusB τ) h b.exponent (b.rootHit * (1-b.q)⁻¹):=by
    intro h x
    letI : Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    let G (u s):= if Ac.Spark (Y.shellF).gP s then (Real.exp b.markSeed)^(roster s.toLeft).flags.card* Y.guess b (w u) s else 0
    let T:= b.rootHit*(1-b.q)⁻¹
    let Z (i) s:= if x∈ Y.fullA s then G i s *currency B b.exponent (Y.fullA s) else 0
    have hp u: SumBudget (Z u) T:=by exact (Y.condenses _ (hs u).1 x)
    let v:ℝ:= Fintype.card (Reserve S)
    have hv:0<v:=Nat.cast_pos.mpr Fintype.card_pos
    have hQ i: (if x∈Y.fullA i then h i * currency B b.exponent (Y.fullA i) else 0)=v⁻¹*∑ j:Reserve S,Z j i:=by
       unfold h Z G grass choiceS; split_ifs with he hf
       · dsimp only; simp_rw [← Finset.sum_mul, ← Finset.mul_sum,smul_eq_mul]; ring
       · rw [zero_mul,sum_const_zero,mul_zero]
       rw [sum_const_zero,mul_zero]
    change SumBudget (fun i=> if x∈ Y.fullA i then h i * currency (radiusB τ) b.exponent (Y.fullA i) else 0) T
    convert! budget_scale (inv_nonneg.mpr hv.le) (budget_over (univ:Finset (Reserve S)) Z (fun _=>T) fun i _=> hp i) using 1; apply funext hQ
    rw [sum_const,nsmul_eq_mul,card_univ, show (Fintype.card (Reserve S):ℝ)=v from rfl]; field_simp
end YM.QCD.Loom.Fleet
