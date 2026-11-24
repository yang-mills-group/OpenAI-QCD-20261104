import YM.QCD.Stem.Palm
/-! # Satellite stencil without Ω
 Native sizes Tick. Lift exact along offsets. No area truncation heuristics. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove -- ?
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove
variable (Γ:Silo c) (W:BankP c){V₀ : St c}
noncomputable def kiln (c:Side)(w:ℕ): Finset (Tick c):= univ.filter (fun s=> s.2.2 ∈ shortZip s.1 w) -- ALL includes fake invalid for high
set_option quotPrecheck false
local notation "Z₀"=> sealG Γ N
local notation "X"=> kiln c w
noncomputable def rat (Γ:Silo c)(N w:ℕ): Gem c N (Site c):= tuckS (sealG Γ N) (kiln c w) w
lemma breadth (x:Tick c) (hx:x∈ X): (dispatch x).support ⊆ neighbors w x.1:=by
   unfold dispatch; split<;> rename_i h
   · exact (mem_filter.mp (mem_filter.mp hx).2).2
   exact halo_subset ..
lemma ros (x:Site c): bust Z₀ (X) x={x} ×ˢ (univ ×ˢ shortZip x w):=by
   ext z; simp only [bust,kiln,mem_filter,mem_univ,true_and,mem_product,mem_singleton]; change (_∧ z.1=x)↔_; by_cases he:z.1=x <;> simp [he]
section pitch
local notation "K"=> (2:ℂ)⁻¹
private lemma eye (u:Finset (Support c))(x i j:Site c)(T:Support c→Bundle)(p:Site c×Site c→Set (Support c)):cell ((K:ℂ) • Stew.block i j (∑ k∈u,T k)) i j = (K:ℂ) • (∑ k∈ u,T k):=by rw [cell_scale,pairBl,if_pos (by simp)]
lemma cocoa (x i j:Site c)(u:Support c→Site c→Bundle):
 (∑ s∈shortZip x w,∑ y:Site c,cell ((K:ℂ) • block x y (u s y)) i j)= if i=x then K • (∑ s∈ shortZip x w,u s j) else 0:=by
    by_cases h:i=x; · subst i; rw [if_pos rfl]; simp_rw [cell_scale,pairBl]; rw [Finset.smul_sum]; apply sum_congr rfl; intro s hs; simp
    rw [if_neg h]; simp_rw [cell_scale,pairBl]; simp [h]
lemma flax (x i j:Site c)(u:Support c→Site c→Bundle):
 (∑ s∈shortZip x w,∑ y:Site c,cell ((K:ℂ) • block y x (u s y)) i j)= if j=x then K • (∑ s∈ shortZip x w,u s i) else 0:=by
    by_cases h:j=x; · subst j; rw [if_pos rfl]; rw [Finset.smul_sum]; apply sum_congr rfl; intro s hs; simp [cell_scale,pairBl]
    rw [if_neg h]; simp_rw [cell_scale,pairBl]; simp [h]
lemma sleepX (x:Site c)(U:Grid c):
    (rat Γ N w).view x U = paleF N (batch (singleR c) Γ x none w (settled U)):=by
    let P:=shortZip x w
    change (∑ i∈ bust _ _ _,_ : Grid c → EvenA c N) U= _; rw [Finset.sum_apply,ros,Finset.sum_product,sum_singleton,Finset.sum_product,sum_comm]
    rw [show (∑ s∈ shortZip x w,∑ y:Site c,(sealG Γ N).view (x,y,s) U)= paleF N (∑ s∈ P,∑ y:Site c,gleam Γ U (x,y,s)) from Eq.symm (by simp_rw [groups]; rfl)]
    apply congr_arg; apply Sway.whist; intro i j; have hv (y:Site c)(s:Support c):gleam Γ U (x,y,s)= K • block x y (Γ x y s (settled U))+ K • block y x (Γ y x s (settled U)):=by
       unfold gleam; rw [smul_add]; rw [show (K:ℂ)=((↑((2:ℝ)⁻¹)):ℂ) by norm_num]; rfl
    rw [stack,shade_sale,monotype]; simp_rw [hv]; have hh {I:Type}(u:I→Sheet c)(v:Finset I): cell (∑ i∈v,u i) i j= ∑ s∈v, cell (u s) i j:=by ext a b; simp [cell,Matrix.sum_apply]
    rw [hh]; simp only [hh,cell_add,sum_add_distrib]; have hp: chipK x w Γ i j none (settled U)=∑ s∈ shortZip x w,Γ i j s (settled U):= Finset.sum_apply ..
    rw [hp]; apply congr_arg₂ (·+·)
    · have h := cocoa (w:=w) x i j (fun s y=>Γ x y s (settled U)); change (∑ s∈shortZip x w,∑ y:Site c,cell ((K:ℂ) • block x y (Γ x y s (settled U))) i j)=_ at h ⊢; rw [h]; split_ifs with he; rw [he]; rfl
    have h:= flax (w:=w) x i j (fun s y=>Γ y x s (settled U)); change (∑ s∈shortZip x w,∑ y:Site c,cell ((K:ℂ) • block y x (Γ y x s (settled U))) i j)=_ at h ⊢; rw [h]; split_ifs with he; rw [he]; rfl
end pitch
end YM.QCD.Stem
