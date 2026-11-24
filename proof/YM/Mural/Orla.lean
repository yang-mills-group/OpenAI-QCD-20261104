import YM.Mural.Shield
import YM.Mills.Porch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Pipe Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Loom.Fleet
open Grass Cove Lat GasP Filter Ursell Graph Jets.Touch Jets.Sun Footprint
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι D E J:Type}{N n M K:ℕ}
variable {O:Ratio c f}(G:Send O N D) {p:Rise f N E J}(X:Fj D E J→Support c)
variable {m:D→ℝ}{u u':E→ℝ}{w:J→ℝ} {v q a a' γ Γ θ ε rα r x:ℝ}
lemma each_star (j:Site f)(B:E→Support f)(ht0:∀i,u i≠0 → j∈B i)(hz: Ac.Hit B K u a v)(h:0≤u) (i:E)(hu:0≤v)(ha:0≤a): u i≤v:=by
   by_cases hp:u i=0; · rwa [hp]
   have ht:= budget_sum (hz j) {i}; rw [sum_singleton,if_pos (ht0 i hp)] at ht; exact (le_mul_of_one_le_right (h _) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))).trans ht
lemma starH {U:E→Support f} {J':E→Support c}(j:Site f)(hx:0<n)(hp:K ≤ 2*n)(he:Ac.Hit U K u a v)(hw:∀i, u i≠0 → j ∈ U i)(hz:∀ i,0 ≤ u i)(hM:∀ i, J' i ⊆ enlargement O M n (U i))(hF:reserve a a' (conversion O M) ε): Ac.Hit J' n u a' (Real.exp (a'*preCost M)*v):=by
   intro t; let c:=Real.exp (a'*preCost M); refine budget_mono (budget_scale (Real.exp_pos _).le (he j)) (fun i=>?_) (fun i=>?_)
   · exact ite_nonneg (mul_nonneg (hz i) (Real.exp_pos _).le) le_rfl
   split; next h=>
     by_cases hp':u i=0
     · simp [hp']
     rw [if_pos (hw i hp'),mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hz _)
     apply Real.exp_monotone; have hv: (coverNumber n (J' i):ℝ) ≤ preCost M + conversion O M*coverNumber K (U i):=(Nat.cast_le.mpr (Lattice.Corona.cover_mono (hM i) n)).trans (footprint O M n K _ hx hp); have hg:= mul_le_mul_of_nonneg_left hv hF.1; nlinarith only [hg,mul_le_mul_of_nonneg_right (show a'*conversion O M≤ a by linarith only [hF.2.1,hF.2.2]) (Nat.cast_nonneg (α:=ℝ) (coverNumber K (U i)))]
   next h=>exact (budget_scale (Real.exp_pos _).le (he j)).1 _
lemma step_income (y:Site f)(hV:Ready X n (paidSet G p m u w q 1 θ x) a γ 1 (1/2))(hB: Ac.Hit (fun i=>(p.row i).support) K u' rα r) (hO:∀ i,u' i≠0→ y ∈ (p.row i).support∧u i=0) (hC:reserve rα (a+1) (conversion O M) ε) (hr:γ+ Real.exp 1*(Real.exp ((a+1)*preCost M)*r) ≤ Γ)(he:degreePrice n Γ 1 ≤1/2) (hh:∀ i:E,X (.inr (.inl i))⊆enlargement O M n (p.row i).support)(hk:1≤x)(hθ:0≤θ)(hw:0≤w)(hv:0≤q)(h0:0≤r)(hz:0≤u)(hP:0≤u')(hr':r≤1)(ha:0≤rα)(hN:0<n)(hM:K≤2*n): Ready X n (paidSet G p m (u+u') w q 1 θ 1) a Γ 1 (1/2):=by
   let pX i:=paidSet G p m u w q 1 θ x i; let pY:= paidSet G p m (u+u') w q 1 θ 1; have hSt i:0≤ pY i :=by
        rcases i with i|i|i
        · exact hV.2.2.2.2.1 (.inl i)
        · exact mul_nonneg zero_le_one (sub_nonneg.mpr (Real.one_le_exp (add_nonneg (hz i) (hP i))))
        exact mul_nonneg (mul_nonneg (by change 0≤1*(1* _); positivity) (pow_nonneg hv _)) (hw _)
   have hp:= hV.2.2.2.2.2
   let w2:= fun i:E=> Real.exp 1*u' i
   let u2:Fj D E J→ℝ:= Sum.elim (fun _=>0) (Sum.elim w2 (fun _=>0))
   have ht:Ac.Hit X n u2 (a+1) (Real.exp 1*(Real.exp ((a+1)*preCost M)*r)):=by
       have hH:= starH y hN hM hB (fun i h=>(hO _ h).1) hP hh hC
       have he : Ac.Hit (fun i:E=>X (.inr (.inl i))) n w2 (a+1) (Real.exp 1*(Real.exp ((a+1)*preCost M)*r)):= heights_factor (Real.exp 1) _ _ _ hH (fun _=>rfl) (Real.exp_pos _).le
       let p' i:=pX (.inl i); have h0 {Z:Type} (Q:Z→ Support c): Ac.Hit Q n (fun _=>0) (a+1) 0:=by
           intro i; simp only [zero_mul,ite_self]; exact ⟨fun _=>le_rfl, summable_zero,le_of_eq tsum_zero⟩ -- name
       intro i; convert Labels.together _ _ _ (h0 fun i:D=>X (.inl i)) (Labels.together _ _ _ he (h0 fun i:J=> X (.inr (.inr i)))) i using 1; · congr; ext i; rcases i with i|i|i<;> rfl
       ring
   have hA(i): pY i≤ pX i+u2 i:=by
      rcases i with i|i|i
      · exact le_add_of_nonneg_right le_rfl
      · have hR:u' i≤1:= (each_star y _ (fun i h=>(hO i h).1) hB hP i h0 ha).trans hr'; change 1*(Real.exp (u i+u' i)-1)≤1*(Real.exp (u i)-1)+w2 i; simp only [one_mul]; by_cases hv:u' i=0; rw [hv,add_zero, show w2 i=0 by unfold w2; rw [hv,mul_zero],add_zero]
        rw [(hO i hv).2,zero_add,Real.exp_zero,sub_self,zero_add]; exact QCD.Port.fastR _ (hP i) hR -- name
      calc pY (.inr (.inr i)) ≤ pX (.inr (.inr i)) :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (pow_nonneg hθ _)) (by norm_num)) (pow_nonneg hv _)) (hw _)
           _ ≤ _:= le_add_of_nonneg_right le_rfl
   have hI i: SumBudget (fun j=> if i∈ X j then (pX j+u2 j)*Real.exp ((a+1)*coverNumber n (X j)) else 0) (γ+ Real.exp 1*(Real.exp ((a+1)*preCost M)*r)):=by
      convert budget_plus (hp i) (ht i) using 1; funext j; unfold pX; split; exact add_mul ..; exact (add_zero _).symm
   exact ⟨hV.1.trans_le ((le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h0))).trans hr),zero_lt_one,he,(by norm_num),hSt, Labels.raise_prices _ _ hSt (fun i=>budget_loosen (hI i) hr) hA⟩
end YM.QCD.Mural
#print axioms YM.QCD.Mural.step_income
