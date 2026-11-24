import YM.QCD.High.Saline

/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Positive color or negative in E? `kinetic + reg = head + soft`.
open Ring0
variable (N:ℕ)(c:Side)
noncomputable def treeH :Gem c N (Site c):=⟨fun i=> ⟨i, halo 2 {i},halo_subset _ _ (mem_singleton_self i)⟩,fun i=> ocean c N ∘ hatH c su i⟩
variable {c N}
variable (P:BudgetPoint)
attribute [local instance] Gauge.frobInner
lemma movesH (A:Grid c)(k:Strut c)(i:Site c): hatH c su (act k i) A=hatH c su i (Strut.sky k A):=by
    unfold hatH AnalyticBridge.VerifiedReset.counter; rw [show k.sky A=pull k.1 k.2 A from rfl,petals_moves]; rw [show affine k.1 k.2 i=act k i from rfl]; simp only [quad,ite_mul, one_mul,zero_mul,sum_ite_eq, mem_univ,↓reduceIte,real_inner_self_eq_norm_sq,reframe_norm]; rw [Equiv.sum_comp _ (fun i=>‖petals A _ i‖^2)] -- edit
include P
lemma gigantic : Crossing (treeH N c):=by
    let Q:= treeH N c; let d i :=hatH c su i; refine ⟨⟨fun i U k=>?_,fun i U W _=>thorough ..,fun i U=>thorough ..⟩,?_⟩
    · suffices h: sways (Lat.rotates N k) (ocean c N (d i (gauge k U)))=ocean c N (d i U) by exact congr_arg Subtype.val h
      rw [show d i (gauge k U)= d i U from (sober c P i|>.1).symmetry ..]; exact thorough ..
    intro s k g h; refine ⟨act s,fun i=> ⟨?_,fun V=>?_⟩⟩
    · dsimp only [treeH,rotateL]; congr 1; -- edit
      change halo 2 {act s i}=(halo 2 {i}).image (act s); rw [← image_singleton]; exact halo_map (act s) (turn_sep s.1 s.2) ..
    change Diode _ _ _ _ (ocean c N (d i (Strut.sky s V)))=ocean c N (d (act s i) V); rw [← show d (act s i) V=d i (Strut.sky s V) from movesH ..]; exact thorough ..
noncomputable def price (P:BudgetPoint)(t:ℝ):=bodyBill su P*Real.exp (81*t)
lemma sincere {c:Side}(h:0 ≤a)(hp:2 ≤ P.B)(hk:0≤ t) : Saline (treeH N c) P a t (price P t) true:=by
     let d:=bodyBill su P; let W(i:Site c):= hatH c su i; have hd:0≤d:= (sober c P 0|>.2.1); let X:=treeH N c
     refine ⟨(fun _=>d),fun i=>?_ , fun i=> ⟨wealthy N i _ _ (sober c P i|>.1) (sober c P i|>.2) h,fun U hv=>?_⟩⟩
     · refine ⟨fun i=> ite_nonneg (mul_nonneg hd (Real.exp_pos _).le) le_rfl,Summable.of_finite, ?_⟩; rw [tsum_fintype]; change ∑ j:Site c,(if j=i then d*Real.exp (t*coverNumber P.B (halo 2 {j})) else 0) ≤ _; simp only [sum_ite_eq', mem_univ,↓reduceIte]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hd
       have hh: (coverNumber P.B (halo 2 {i}):ℝ) ≤81:= by
          have he :coverNumber P.B (halo 2 {i})≤81:=by apply le_trans _ (Geo.tiles P i);  exact Corona.cover_mono (Corona.halo_mono hp (subset_refl _)) _ -- check
          exact_mod_cast he
       linarith only [mul_le_mul_of_nonneg_left hh hk]
     change Sen i a (ocean c N (W i U))≤d; rw [vintage _ _ _ h]; exact Bill.norm (l:=[]) (show Bill P i (Healthy P.threshold {i}) d (W i) from counter_bill ..) (by simp) (by simp) hv
omit P
lemma paidH (V:Grid c) :∑ i,sheer (treeH N c) true p.threshold i V = ocean c N (∑ i,heads p i V):=by
     rw [map_sum]; apply sum_congr rfl; intro i _; unfold sheer; rw [maskH]; change masked _ {i} _ V= _; by_cases hx:Healthy p.threshold {i} V; · rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ hx]; rfl
     rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ hx,map_zero] -- must defeq mask map
variable (G:Gem c N ι)
lemma clothH (i:ι) (V:Grid c): sheer G false t i V=G.view i V :=masked_eq _ _ _ _ (by simp [pinT,Healthy])
variable [Fintype ι]
lemma raisedH (k:ℕ) (d:Bool)(h:2 ≤ c.val)(i:Grid c): ∑ j,sheer (air G k) d t j i=∑ j,sheer G d t j i:=by
     rw [Fintype.sum_sigma]; apply sum_congr rfl; intro j _; by_cases hx:Healthy t (pinT d (G.addr j)) i
     · rw [sheer,masked_eq _ _ _ _ hx]; have he (T:Pollen k (G.addr j).site): sheer (air G k) d t ⟨j,T⟩ i= (Fintype.card (Pollen k (G.addr j).site):ℝ)⁻¹ • G.view j i:=masked_eq _ _ _ _ hx
       simp_rw [he]; haveI:Nonempty (Pollen k (G.addr j).site):=lived h; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,mul_inv_cancel₀ (show (Fintype.card (Pollen k (G.addr j).site):ℝ) ≠0 from Nat.cast_ne_zero.2 Fintype.card_ne_zero),one_smul]
     rw [sheer,masked_ne _ _ _ _ hx]; exact sum_eq_zero fun i hi=> masked_ne _ _ _ _ hx
lemma drumH (x:Grid c)(d:Bool)(t:ℝ): HasSum (fun i=>(reef G t d).mean i x) ((∑ i,sheer G d t i x)-Patron.total G t x):=by unfold Patron.total; rw [tsum_fintype,←sum_sub_distrib]; exact hasSum_fintype _
end YM.QCD.High
