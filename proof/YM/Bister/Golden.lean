import YM.Bister.Stretch
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate.Stretch
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{I X E:Type}{N:ℕ}{σ v k t:ℝ}
variable (Y:Patron.Rail c N E) (F:E→Hat c)
-- Y larger K structure but no exact flag assertion on expanded support yet
variable (Y:Patron.Rail c N E) (F:E→Hat c)
local notation "Ω"=> Ruby.home Y
local notation "M"=> Ruby.home (Orig Y F)
local notation "g"=> oriD Y
local notation "g'"=> oriD (Orig Y F)
structure Vital (t:ℝ):Prop where
    place i : (F i).place ⊆ (Y.addr i).place
    inv i: (F i).inv=(Y.addr i).inv
    reads i: UsesFinal t (Ω i) (Y.warp i)
    measurable i: Measurable (Y.warp i)
    support i V: Gated (Ω i) (Y.warp i V)
    gauge i: shadeG (Y.warp i)
local notation "W"=> Basin Y F t
variable (h:Vital Y F t)
include h
lemma rank : (W).Reg t :=by
    constructor
    · intro i U V he hV; change patientY .. = patientY ..; unfold patientY; apply if_congr
      · exact (show (flags t U∩ coverY Y i.val=booksY Y i.val ↔ _) from by rw [inter_comm,show coverY _ _ ∩ flags t U = _ from hV, inter_comm];rfl)
      · exact prod_congr rfl fun j hj=> Work.H03.reads_larger (subset_biUnion_of_mem Ω hj) (h.reads j) U V he hV
      exact rfl
    · intro i; change Measurable (fun U=> patientY Y i.val t U); unfold patientY; apply Measurable.ite _ _ measurable_const; swap
      · exact Finset.measurable_fun_prod _ fun j _=> h.measurable j
      let Z:= coverY Y i.val; let G:= booksY Y i.val; rw [show {U:Grid c|flags t U ∩ Z=G}=⋃ j∈(univ.filter (fun i: Support c=>i∩Z=G)),{U|flags t U=j} by ext; simp]; exact MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=>flags_measurable_eq ..
    · intro i V; change Gated _ (patientY ..); unfold patientY; split; next _=> exact gate_prod _ _ _ (fun j hj=> gateMon (Ω j) _ (subset_biUnion_of_mem Ω hj) _ (h.support j V)) -- arg
      unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
    intro i V hp; exact by_contra fun hh=>hp (if_neg hh)
lemma dusts (i) : shadeG ((W).warp i):=by
    intro U k; have hz := gauge_flags t U k; suffices H: sways (Lat.rotates N k) ((W).warp i (Lattice.gauge k U))=(W).warp i U from congr_arg Subtype.val H; change sways _ (patientY Y i.val t _) = patientY ..; unfold patientY; rw [hz]; split; rw [map_prod]; exact prod_congr rfl fun j _=>Subtype.ext (h.gauge j U k); exact map_zero _
omit h
variable {B:ℕ}{ν a b τ Q:ℝ}
open Trees
lemma wealth (hτ:1 ≤ τ)(ha:0 ≤ a)(he:Kites.Quits Y B v τ (a+b) k)(hv:0<v)(hb:0<b)(hh:Q<1)(hm: degreePrice B v b ≤ Q)(hC:v*(1-Q)⁻¹ ≤ν): Kites.Quits (Basin Y F t) B ν τ a k:=by
     obtain ⟨f,hf,H⟩:=he.cost; have hg i:0 ≤ f i:=(norm_nonneg _).trans (H i 1); let Yq(i:Quants Y F):= ∏ j∈i.val,f j; have hY(i):0≤ Yq i:= prod_nonneg fun j _=>hg j; let w:= QCD.GasP.taxed g f τ; have hK : Ready Ω B w a v b Q:=⟨hv,hb,hm,hh,fun i=>mul_nonneg (pow_nonneg (zero_le_one.trans hτ) _) (hg _),hf⟩; refine ⟨Yq,?_,fun i V=>?_⟩
     · intro x; let r x':= touches Ω B w a x x'; have hW:= touch_tail Ω B hK x 0; simp only [Nat.zero_le,ite_true,pow_zero,mul_one] at hW; have hz := budget_pull Subtype.val (Subtype.val_injective (p:=wallet Y F)) hW; have ht :0 ≤ τ:= zero_le_one.trans hτ; apply budget_loosen (D:=ν) _ hC; refine budget_mono hz (fun i=>ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht _) (hY _)) (Real.exp_pos _).le) le_rfl) fun i=>?_
       split; swap; · exact hz.1 _
       next hp=>
        have he:=i.2.2; let D:= Ω; change τ^ (booksY Y i.val).card * Yq i*currency B a (coverY Y i.val) ≤ if Ac.Spark Ω i.val ∧ _ then _ else _; rw [if_pos ⟨he,hp⟩,prod_mul_distrib]; apply mul_le_mul ?_ _ (Real.exp_pos _).le (prod_nonneg fun _ _=> mul_nonneg (pow_nonneg ht _) (hg _)) -- edit
        · rw [prod_mul_distrib,prod_pow_eq_pow_sum]; apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hτ card_biUnion_le) (hY i)
        unfold currency; rw [← Real.exp_sum,← mul_sum,← Nat.cast_sum]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Ac.cover _ _ he)) ha)
     change ‖token _ _ k (patientY ..)‖≤_; unfold patientY; split; next _ => exact (folkl _ _ _).trans (prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> H j V))
     rw [map_zero,norm_zero]; exact hY _
lemma dreamed (hr:Vital Y F t)(hτ:1 ≤ τ)(ha:0 ≤a)(hq:Quits Y B v τ a k)(hk:1 ≤ k)(U:Grid c): heartK (Basin Y F t) t U= heartK (Orig Y F) t U:=by
    let X:=Orig Y F; have hv:Quits X B v τ a k:=by
       obtain ⟨f,hf,H⟩:=hq.cost; refine ⟨f,fun i=>?_,H⟩; have hh j :0 ≤ f j:=(norm_nonneg _).trans (H j 1); refine budget_mono (hf i) (fun j=>ite_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hτ) _) (hh j)) (Real.exp_pos _).le) le_rfl) fun j=> ?_
       by_cases ht:i∈M j
       · change (if _ then _ else _) ≤ (if _ then _ else _); rw [if_pos ht,if_pos (show i∈Ω j from hr.place j ht)]; have he:g'=g:=funext hr.inv; apply le_trans (b:=QCD.GasP.taxed g' f τ j*Real.exp (a*coverNumber B (Ω j))) ?_ (by rw [he]); exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Corona.cover_mono (hr.place j) _)) ha)) (mul_nonneg (pow_nonneg (zero_le_one.trans hτ) _) (hh j))
       exact (if_neg ht).le.trans ((hf i).1 j)
    exact (petrol Y F hr.place hr.inv t U _ (profits _ _ hk hτ hv ha t).hasSum).tsum_eq
end YM.MassiveQCD.Plate.Stretch
#print axioms YM.MassiveQCD.Plate.Stretch.wealth
#print axioms YM.MassiveQCD.Plate.Stretch.dreamed
