import YM.Clays.Bonds
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) (Y:D→Support c)
variable (M:D→ Finset (Finset I)) (h:∀ i,∀ j∈ M i,j.Nonempty ∧ j ⊆ barn o (Y i))
noncomputable def growsZ (Y:Support c)(u:Finset I):= Y ∪ u.biUnion (fun j=>halo 1 {o j})
local notation "V" u:arg=>growsZ o u
lemma growthZ (Y:Support c)(u:Finset I)(he:u⊆ barn o Y): (V Y) u ⊆ halo 1 Y:= union_subset (halo_subset ..) (biUnion_subset.mpr fun j hj=> Corona.halo_mono le_rfl (singleton_subset_iff.mpr ((inside ..).1 (he hj)))) -- .mpr sig
lemma growthC (Y:Support c)(u:Finset I)(B:ℕ)(hB:0<B)(he:u⊆ barn o Y) : coverNumber B ((V Y) u) ≤ coverNumber B Y+ u.card:=by
    induction u using Finset.induction_on with
    | empty=> simp [growsZ]
    | insert i s hi ih=>
       rw [card_insert_of_notMem hi,growsZ,biUnion_insert]; let x:= o i; let U:= (V Y) s; let W:= halo 1 {x}; have hm:x∈Y:= (inside ..).1 (he (mem_insert_self ..)); have hx :x∈W:= halo_subset _ _ (mem_singleton_self _); change coverNumber B (Y∪(W∪_)) ≤ _ ; rw [union_comm W,← union_assoc]; refine le_trans (Entr.Meridian.stripSize U W x x (mem_union_left _ hm) hx (by simp) B) ?_; have hf:coverNumber B W ≤1:=by
            refine le_trans (Corona.list_cost (D:={x}) (X:=W) B ?_) (card_singleton _).le -- sig
            exact ⟨Corona.halo_mono hB le_rfl,Corona.ship_halo _ (fun i ih j hj=> by rw[mem_singleton.mp ih,mem_singleton.mp hj])⟩ -- check
       exact ((Nat.add_le_add_right (ih ((subset_insert ..).trans he)) _).trans (Nat.add_le_add_left hf _)).trans_eq (by omega)
variable (B Ft:ℕ) (hB:0<B) (C:ℝ) (hp:0 ≤C)
variable (g:D→ℝ)(hn:∀ i,0 ≤ g i) (he:Ac.Hit Y B g b m)(hv:0 ≤ v)(ε:ℝ)(hx:0 < ε)
noncomputable abbrev Tool (M:D→ Finset (Finset I)):=Sigma fun i=> ↥(M i)
local notation "Z"=>Tool M
local notation "F"=> hullP B Ft
local notation "Q"=> Real.exp v * C
noncomputable def beamFee (v ε:ℝ) := 81*(hullP B Ft * (ε⁻¹*(Real.exp ε)) * (Real.exp v*C))
local notation "Ψ"=> beamFee B Ft C v ε
variable (hW:Fires o Ft)
include h hn he hv hx hp hW hB
set_option maxHeartbeats 800000 in
lemma woodPays (hP:hullP B Ft * (Real.exp v*C)≤ε)(hz:v+2*ε ≤b): Ac.Hit (fun i:Z=>growsZ o (Y i.fst) i.snd.val) B (fun i:Z=> C^i.snd.val.card * g i.fst) v (Ψ*m):=by
     let P:ℝ:= ε⁻¹ *(Real.exp ε); let A:= hullP B Ft * P * Q
     intro j; let X':= halo 1 {j}; let l (i:Z):=(V (Y i.1)) i.2.val
     let f i:= if j∈l i then C^i.snd.val.card*g i.fst*Real.exp (v*coverNumber B (l i)) else 0
     let T (x:Site c)(i:D) := if x∈Y i then g i*Real.exp (b*coverNumber B (Y i)) else 0
     have h₀(i): 0 ≤ f i:=ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hp _) (hn _)) (Real.exp_pos _).le) le_rfl; have hZ(x i):0 ≤ T x i:=(he x).1 i
     have hF:0 ≤ F:=by unfold hullP; positivity
     have hQ:0 ≤ Q:=mul_nonneg (Real.exp_pos _).le hp; have hA:0 ≤ A:=by unfold A P; positivity
     have hT: SumBudget (fun i=> A*∑ s ∈ X',T s i) (Ψ*m):=by
           have hm:0≤ m:=budget_nonneg (he j); have hr:(X'.card:ℝ)≤81:=by exact_mod_cast (Corona.halo_size {j} 1).trans (by norm_num)
           have hψ:Ψ = 81*A:=rfl
           rw [hψ]; exact budget_loosen (budget_scale hA (budget_over X' T (fun _=>m) (fun k _=>he k))) (by rw [sum_const,nsmul_eq_mul]; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hm) hA])
     refine budget_fiberwise (f:=f) (fun i:Z=>i.fst) h₀ ?_ hT
     intro i u huu; let L:= M i; let w:=Sigma.mk i (β:=fun i=>↥(M i))
     have hh:u ⊆ Finset.univ.image w:=by rintro ⟨k,y⟩ h; have hp:k=i:=huu _ h; subst k; exact mem_image_of_mem _ (mem_univ _)
     apply le_trans (sum_le_sum_of_subset_of_nonneg hh fun i _ _=> h₀ i); rw [sum_image (show Set.InjOn w _ from fun i _ j _ h=>(Sigma.mk.inj_iff.mp h).2|>eq_of_heq)]
     change ∑ j:↥L,f (w j) ≤ A*∑ s∈X',T s i
     by_cases hx':j∈ halo 1 (Y i); swap
     · rw [sum_eq_zero (by intro z iz; exact if_neg fun ht=>hx' (growthZ o _ _ (h _ _ z.2).2 ht))]; exact hT.1 _
     obtain ⟨x,hX,hY⟩:= halo_spec.mp hx'; have hf :x∈X':=halo_spec.mpr ⟨j,mem_singleton_self _, (separation_comm _ _).le.trans hY⟩
     refine le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (fun i hi=>hZ i _) hf) hA)
     let K:=coverNumber B (Y i); let K':= (K:ℝ); change _ ≤ A*(ite _ _ _); rw [if_pos hX]
     let E:=g i * Real.exp (v*K'); have hE:0 ≤ E:=mul_nonneg (hn _) (Real.exp_pos _).le
     let D':= barn o (Y i); have hr : L⊆ D'.powerset.filter (fun i=>i.Nonempty):=fun j hj=> mem_filter.mpr ⟨mem_powerset.mpr (h i j hj).2,(h i j hj).1⟩; have ht:0≤K':=Nat.cast_nonneg _
     have hh'(z:↥L): f (w z) ≤ E*Q^z.val.card:=by
          unfold f; split; next hi=>
                  let d:=z.val.card; have hf:= growthC o (Y i) z.val B hB (h _ _ z.2).2; change C^d*g i*Real.exp (v*_) ≤ _; apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hf) hv)) (mul_nonneg (pow_nonneg hp _) (hn _))).trans_eq; rw [Nat.cast_add, mul_add,Real.exp_add,mul_pow]; unfold E K' K; rw [mul_comm v (z.val.card:ℝ),Real.exp_nat_mul]; ring
          exact mul_nonneg hE (pow_nonneg hQ _)
     apply (sum_le_sum (fun j _=>hh' j)).trans; rw [← mul_sum,sum_coe_sort L (fun i=> Q^i.card)]; apply (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hr (fun i _ _=> pow_nonneg hQ _)).trans (income Q hQ D')) hE).trans
     have hn':(D'.card:ℝ)≤ K'*F:=by unfold K' K hullP; rw [← mul_assoc]; exact_mod_cast (barncard o (Y i) Ft B hW)
     have hk₀:(D'.card:ℝ)*Q ≤ K'*(F*Q):=(mul_le_mul_of_nonneg_right hn' hQ).trans_eq (mul_assoc ..)
     let q':=F*Q; have hpz:K'*(F*Q)≤ε*K':=(mul_le_mul_of_nonneg_left hP ht).trans_eq (mul_comm ..); have hs:0≤q':=mul_nonneg hF hQ; have hP':0 ≤ P:=by unfold P; positivity
     have hu : K'≤ P*Real.exp (ε*K'):= (show K'≤1+K' from le_add_of_nonneg_left zero_le_one).trans (by simpa only [pow_one,Nat.factorial_one,Nat.cast_one,mul_one] using polynomial_cost hx ht 1)
     apply (mul_le_mul_of_nonneg_left (mul_le_mul (hk₀.trans (mul_le_mul_of_nonneg_right hu hs)) (Real.exp_monotone (hk₀.trans hpz)) (Real.exp_pos _).le (mul_nonneg (mul_nonneg hP' (Real.exp_pos _).le) hs)) hE).trans
     let u:=v+2*ε; have hh:Real.exp (v*K') *Real.exp (ε*K')*Real.exp (ε*K')=Real.exp (u*K'):=by unfold u; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
     refine le_trans (le_of_eq (b:=A*(g i*Real.exp (u*K'))) ?_) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz ht)) (hn _)) hA); unfold E A; rw [←hh]; ring
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.woodPays
