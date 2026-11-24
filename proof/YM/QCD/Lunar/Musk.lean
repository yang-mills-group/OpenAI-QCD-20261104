import YM.QCD.Lunar.Night
/-! # Fermi canonical global Moment. native. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
namespace Project
open Revolve Flume Quarry
variable (c)
open Entr Port AnalyticBridge.VerifiedReset
open Entr Port AnalyticBridge.VerifiedReset
variable {o x:Site c}{t u δ ε K A B v' α θ:ℝ}{p:BudgetPoint}{I:Type}
lemma costOne (j:Bool): unitF j c 1= if j then 0 else 1:=by
    have he i k: gold (cell (1:Sheet c) i k)= if i=k then 1 else 0:=by
        unfold gold cell; split; next h=> subst k; ext x y; by_cases hx:x=y<;> simp [hx,Matrix.one_apply]
        next h=> ext; simp [h,Matrix.one_apply]
    have hv : 0<(Fintype.card (Site c):ℝ):=by positivity
    cases j
    · have h : μDir c false 1=(Fintype.card (Site c)) • (1:Spike):=by
          change (∑ i,∑ j,(Stew.shine i j*(if false=true then _ else 1)) • _)=_
          simp only [he,Bool.false_eq_true,↓reduceIte,mul_one, smul_ite, smul_zero]
          simp
      rw [if_neg (by decide)]; change ((Fintype.card (Site c):ℝ)⁻¹*bb false (μDir c false 1))=_; rw [h,map_nsmul, nsmul_eq_mul, show bb false (1:Spike)= 1 from ?_,mul_one,inv_mul_cancel₀ hv.ne'];
      change ((1:Spike) _ _).re= _; rw [show (1:Spike) _ _=1 from Matrix.one_apply_eq ..]; rfl
    · have hh : μDir c true 1=0:=by
          change (∑ i,∑ j,stone c true i j • gold (cell 1 i j))= _; apply sum_eq_zero ; intro i _; rw [sum_eq_single i]; rotate_left
          · intro b _ hb; rw [he, if_neg hb.symm,smul_zero] -- .symm wrong
          · simp
          unfold stone Entr.crest lift; simp
      change ((Fintype.card (Site c):ℝ)⁻¹*bb true (μDir c true 1))=_; rw [hh,map_zero,mul_zero, if_pos rfl]
variable {c}
lemma silence {A:Gem c N I}{b:Flavor N}(h:Quanta A b): ∀ o,till A b o=0:=by
    intro o; funext s; unfold till; rw [show unitM A b o s=fun _=>0 from funext fun i=>?_]; exact tsum_zero
    unfold unitM lane Stew.mote; split_ifs with hu he; exact h i he s; rfl; rfl
variable {a:ℝ}
variable (b:Flavor N)
open Lunar
lemma chargeQ (j:Bool)(p:BudgetPoint)(u:ℝ)(hp:0<a):∀ᶠ c:Side in atTop,∀ (I:Type)(E:Gem c N I), Licence p 2 u a E→ Crossing E→ Quanta E b → |unitF j c (meter b (Patron.total E p.threshold 1))| ≤ Φ p.B (-7/4) c:=by
     filter_upwards [axes b j (θ:=2) (by norm_num) hp p u] with c hc I E hL hE hQ; have hp:=hc I E hL hE; rw [silence hQ, map_zero,sub_zero,show -(2-1/4:ℝ)= -7/4 from (by ring)] at hp; exact hp
include b
lemma orient (p:BudgetPoint)(hu:1 < θ)(hp:0<a)(x:ℝ):∃ W:ℝ, ∀ᶠ c:Side in atTop,∀ (I:Type)[Fintype I] (E: Gem c N I)(U:St c),SlotT E p a θ x U →1/4 ≤ Project.unitF true c (U 1) ∧|Project.unitF false c (U 1)| ≤ W:=by
     let s:= θ-1/4; have hh:0<s:=by unfold s; linarith
     have he:Tendsto (Φ p.B (-s)) atTop (𝓝 0):=by simpa only [pow_zero,mul_one] using Lunar.shine p.B hh 0 1 zero_le_one
     obtain ⟨K,hK,H⟩:=Entr.hauteur N
     refine ⟨K*|x|+1,?_⟩; filter_upwards [axes b true hu hp p (x*a^2),axes b false hu hp p (x*a^2), he.eventually_le_const (by norm_num : (0:ℝ)<1/4)] with c h1 h2 h I hI E U hL
     have hX : meter b (Patron.total E p.threshold 1)=U 1:=by
          unfold Patron.total; rw [tsum_fintype,sum_congr rfl (show ∀ i∈univ, letters E p.threshold 1 i=(fun i=> E.view i 1) i from fun i _=>masked_eq _ _ _ _ (flat_ok ..))]; rw [hL.trunk]; exact forceP (U 1) b
     obtain hp' := h1 I E hL.warp.law hL.moveG; rw [hX,show valueB true (till E b 0)=qWave (till E b 0) from awake ..] at hp'; let z':= qMass (till E b 0)
     have hv := hL.earn b; have ht:= h2 I E hL.warp.law hL.moveG; rw [hX,show valueB false (till E b 0)= z' from rfl] at ht
     have hz':|z'| ≤ K*|x|:=by apply le_of_mul_le_mul_left _ (sq_pos_of_pos hp); apply (H c I E p θ (x*a^2) a hL.warp.law hp (by linarith) b).1.trans; rw [mul_left_comm (a^2), mul_comm (a^2)]; gcongr; exact le_abs_self _ -- hp
     refine ⟨by linarith only [hv,(abs_le.mp (hp'.trans h)).1], le_trans (show |unitF false c (U 1)|= _ from (show _ = _ from ?_ )).le ((abs_add_le (unitF false c (U 1)-z') z').trans (by linarith only [ht.trans h,hz']))⟩
     rw [sub_add_cancel]
end Project
end YM.QCD.Stew
#print axioms YM.QCD.Stew.Project.orient
