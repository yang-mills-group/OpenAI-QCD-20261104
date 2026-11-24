import YM.Clays.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c 6→L[ℂ]Lat.Fields c 6) (H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "M"=> ample 6 I
local notation "T"=> traceI I
local notation "Λ"=> Keys c 6
local notation "K"=> actE o p H d s
local notation "Γ"=> effect o p H d
local notation "amt" j:arg=> (s.filter (fun i=> i∈ (j:Finset I)))
variable (F: Reel c 6 I D) {U:BudgetPoint}
local notation "B!"=> U.B
variable (f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
local notation "E"=> Oper o s F
local notation "Ψ"=> clayR o p H s d F
open ConnectedActivityE6 Blaze King
include H
lemma faded (Y:Finset I)(x:P)(hx:Polite T Y x) (w:List I)(he:¬ Disjoint w.toFinset Y):Γ w x= 0:=by
    induction w with
    | nil=>simp at he
    | cons i W ih=>
         rw [eff_cons]; by_cases h0:Disjoint W.toFinset Y; swap; · rw [ih h0,map_zero]
         have hi:i∈Y:= not_not.mp fun ht=> he (by rw [List.toFinset_cons,← singleton_union]; exact disjoint_union_left.mpr ⟨(by simp [ht]),h0⟩); let f:= (H i).twirl I; let z:= echoI Λ i; have hY: Polite T (W.toFinset∪Y) (Γ W x):=pay_piece o p H d W hx; have hv: Polite T (W.toFinset∪Y) (f (Γ W x)):= politeStep _ hY rfl; change (d i) • (z*_)=0; exact Eq.trans (congr_arg ((d i) • ·) ((itOwn (A:=Λ) i).nilpotent hv (by simp [hi]))) (smul_zero ..)
include h
lemma compass (V:Grid c)(hs:s.Nodup)(i:D): K (F.mark i V)=F.mark i V+∑ j:↥(matings o s F i),(Ψ).mark ⟨i,j⟩ V:=by
     let Y:=s.toFinset∩ barn o (F.addr i).support; let v(A:Finset I):= Γ (amt A) (F.mark i V); have hm:v ∅=F.mark i V:=by unfold v; rw [show List.filter (fun j=>decide (j∈(∅:Finset I))) s=[] from by simp]; rfl
     let U:= matings o s F i; rw [ritualP o p H d s hs (h.costume i _).2]; change (∑ j∈Y.powerset,v j)=_+ ∑ j:↥U,v j.val; rw [sum_coe_sort,←add_sum_erase Y.powerset v (mem_powerset.mpr (empty_subset _)),hm]; refine congr_arg (fun x=> _+x) ?_; symm; have hs:U⊆Y.powerset.erase ∅:=fun x hx=>mem_erase.mpr ⟨(mem_filter.mp hx).2.1.ne_empty,(mem_filter.mp hx).1⟩; refine sum_subset hs fun i' hh he=> ?_; obtain ⟨hg,hk⟩:= mem_erase.mp hh; let A:Finset I:=i'; let s':= amt i'; have hr:s'.toFinset=i':=viewingP _ _ ((mem_powerset.mp hk).trans inter_subset_left); exact faded o p H d _ _ (h.costume ..).1 s' (fun hf=>he (mem_filter.mpr ⟨hk,nonempty_iff_ne_empty.mpr hg,hr ▸ hf⟩))
lemma sealed (V:Grid c)(hs:s.Nodup)(i:D)(b:ℝ): K (F.mist b i V)= F.mist b i V + ∑ j:↥(matings o s F i), (Ψ).mist b (⟨i,j⟩:E) V:=by
     by_cases hp:Healthy b (F.addr i).support V
     · have hh(j:↥(matings o s F i)):(Ψ).mist b (⟨i,j⟩:E) V=(Ψ).mark (⟨i,j⟩:E) V:=masked_eq _ _ _ _ hp -- syntax
       simp_rw [hh]; unfold Reel.mist; rw [masked_eq _ _ _ _ hp]; exact compass o p H s d F f g h V hs i
     have hh(j:↥(matings o s F i)):(Ψ).mist b (⟨i,j⟩:E) V=0:=masked_ne _ _ _ _ hp
     simp_rw [hh]; unfold Reel.mist; rw [masked_ne _ _ _ _ hp, map_zero,sum_const_zero,add_zero]
lemma bountiful (V:Grid c)(hs:s.Nodup)(hp:Summable (fun i=> F.mist U.threshold i V))(ht:Summable (fun i=> (Ψ).mist U.threshold i V)): K (F.rope U.threshold V)=F.rope U.threshold V+ (Ψ).rope U.threshold V:=by
     unfold Reel.rope; let P':=(K).toLinearMap.toContinuousLinearMap; have hf(i): P' (F.mist U.threshold i V) = F.mist U.threshold i V + ∑' j:↥(matings o s F i),(Ψ).mist U.threshold (⟨i,j⟩:E) V:=Eq.trans (sealed o p H s d F f g h V hs i U.threshold) (congr_arg _ (tsum_fintype ..).symm);
     refine Eq.trans (P'.map_tsum hp) ((tsum_congr hf).trans ?_); rw [ht.tsum_sigma]; exact hp.tsum_add (ht.sigma' (fun i=>Summable.of_finite)) -- syntax sigma
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.bountiful
