import YM.QCD.Stew.Horn
/-! # refunds outside healthy, actual unmasked linear lead. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Jets Jets.Sun
variable {B: Support c}{C : ℝ}
lemma heroPair (h₀:0<a)(i:Step)(M:Spike)(V:Grid c)(N:ℕ) :
    let Q:=localX o M*leg 0 V i; Sen o a (paleF N Q)≤ foamer 1 N*(a^2*‖M‖) ∧ Sen o a (paleF N (star Q)) ≤ foamer 1 N*(a^2*‖M‖) :=by
      intro Q; let j:=o+i.vec; obtain ⟨h,hb⟩:=stem o o j i rfl rfl
      let P:= hitch 0 V i o; let U:=follow M P; have hv: Q=block o j U:=couple ..
      have hh: ‖P‖≤1:=by obtain ⟨e,-,-,L,Hl,hL⟩:=seamz i o; unfold P; rw [hL]; apply (Hl _).trans; exact leftU _ (V e).val.property
      have hZ:‖U‖ ≤ ‖goldW‖ * ‖silverW‖ *‖M‖:= (vigor ..).trans (mul_le_of_le_one_right (by positivity) hh)
      have hp:9*a^2*fingers N^2*‖U‖≤foamer 1 N*(a^2*‖M‖):= (mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ 9*a^2*fingers N^2)).trans_eq (by unfold foamer; ring)
      rw [hv,starBl]; exact ⟨(budgetBl _ _ _ h hb h₀ _).trans hp,(budgetBl _ _ _ hb h h₀ _).trans (by rw [norm_star]; exact hp)⟩
lemma sumR (X Y:Sheet c)(H: Sen o a (paleF N X) ≤ r)(he:Sen o a (paleF N Y)≤r): Sen o a (paleF N ((2:ℂ)⁻¹ • X+ (-(2:ℂ)⁻¹) • Y))≤ r:=by
    let t:ℂ := (2:ℂ)⁻¹; rw [show paleF N _= t • paleF N X+ (-t) • paleF N Y from ?_, ← measures,map_add, map_smul,map_smul]; rotate_left
    · exact (map_add (nozzle c N) _ _).trans (congr_arg₂ (·+·) (map_smul (nozzle c N) t X) (map_smul (nozzle c N) (-t) Y))
    apply (norm_add_le ..).trans; rw [norm_smul, norm_smul]; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left H (norm_nonneg t)) (mul_le_mul_of_nonneg_left he (norm_nonneg (-t)))); unfold t; rw [norm_neg,norm_inv,(show ‖(2:ℂ)‖=2 from by norm_num)] -- potential defeq
    linarith
lemma every (N:ℕ)(M:Spike)(s:SampleX)(U:Grid c)(ht:1 ≤ C)(hx:0<a): Sen o a (paleF N (entry o M s U)) ≤ tunnel N C*(a^2*‖M‖):=by
    have hv: foamer 1 N ≤ tunnel N C:= (show foamer 1 N ≤ foamer C N by unfold foamer; gcongr).trans (le_add_of_nonneg_left (by positivity)); have he: foamer 1 N*(a^2*‖M‖) ≤ tunnel N C*(a^2*‖M‖):=mul_le_mul_of_nonneg_right hv (by positivity)
    rcases s with _|⟨i,_|_⟩
    · apply (boardFee hx M N).trans; apply mul_le_mul_of_nonneg_right ?_ (by positivity); exact le_add_of_nonneg_right (by unfold foamer; positivity)
    · apply le_trans _ he; rw [hero, roadA, star_add, star_smul, star_smul,star_neg,star_inv₀,star_ofNat]; nth_rw 1 [show ‖M‖=‖star M‖ from (norm_star _).symm]; exact sumR _ _ (heroPair hx _ _ _ _).2 (heroPair hx _ _ _ _).2
    rw [roadA]; apply le_trans _ he; exact sumR _ _ (heroPair hx _ _ _ _).1 (heroPair hx _ _ _ _).1
-- before early weights pre-L bound exponent from p.early 
lemma monarch (n b N:ℕ): ∃ C:ℝ,0<C ∧∀ c:Side,∀ p:BudgetPoint,p.order ≤ n→p.power ≤ b→∀ o:Site c,∀ x:ℝ,0<x→ ∀ s:SampleX,∀ M:Spike, Woven o (stand o) p x (fun U=> paleF N (entry o M s U)) (C*(x^2*‖M‖))∧∀ U:Grid c, Sen o x (paleF N (entry o M s U))≤ C*(x^2*‖M‖):=by
   obtain ⟨K,hK,he⟩:=prices n b 2; let T:=tunnel N K; have hk: (0:ℝ) ≤ K:=zero_le_one.trans hK
   refine ⟨1+T,add_pos_of_pos_of_nonneg zero_lt_one (firm N hk),fun c p hm hp o x hx s M=>?_⟩
   have hC:T*(x^2*‖M‖)≤(1+T)*(x^2*‖M‖):= mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
   have hh: stratum K n o p:=fun e h=>he c o _ h p hm hp
   exact ⟨(headwind hh hx hk ..).stretches (Subset.refl _) hC,fun U=> (every _ _ _ U hK hx).trans hC⟩
end YM.QCD.Stew
