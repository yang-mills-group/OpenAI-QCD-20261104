import YM.QCD.Globe.Ach
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
variable (P:Plan 4) (i:Flavor N)
structure DomainF (P:Plan 4)(N:ℕ)(L:Side)(c:Side)(A : ℝ):Prop where
 port:∃ v w:ℝ,0<v ∧ 1 ≤w ∧∀ (j:ℕ)(B:Side)(he:B=c*L^j)(t:Train 4)(X:EvenA B N), Cocoa X→ GrassA X w 6 v→ expo A B ≤ pebble (paleF N (sunny P t B)+X)
include i
lemma coreP : ∃ m B:ℕ,∀ (L c:Side), m≤ L.val→ Odd L.val→3 ≤ L.val→ B≤ c.val→∃ A:ℝ,0 ≤ A∧ DomainF P N L c A :=by
    obtain ⟨L,B,H⟩:= keeper P N i; obtain ⟨D,hD⟩:= candy P; refine ⟨L,max D B,fun S c hL he hf hz=>?_⟩
    obtain ⟨r,T,v,hr,hT,hv,h⟩:= H S hL he hf c (le_trans (le_max_right ..) hz); obtain ⟨C,hC,hK⟩:= intoA i 6; obtain ⟨M,hM,hf⟩:= bounces P 6
    let J:=2*(4*M+2); have hJ:0<J:=by unfold J; positivity
    let d:= min (min (r/J) (T/J)) (1/4); have hp: 0 < d:=lt_min (lt_min (div_pos hr hJ) (div_pos hT hJ)) (by norm_num); have hp':d≤1/4:=min_le_right ..; have h1:2*dimeZ M d ≤ r:=by unfold dimeZ; have hh:=le_trans (min_le_left ..) (min_le_left (r/J) (T/J)) (a:=d); rw [le_div_iff₀ hJ] at hh; unfold J at hh; linarith only [hh]
    have h2:dimeZ M d ≤T:=by unfold dimeZ; have hh:=le_trans (min_le_left ..) (min_le_right (r/J) (T/J)) (a:=d); rw [le_div_iff₀ hJ] at hh; unfold J at hh; nlinarith only [hh,hT] -- edit
    obtain ⟨x,hx,Q⟩:=heft (C:=C*v) (by positivity) hp
    obtain ⟨t,hg,ht⟩:=(h.and (eventually_ge_atTop x)).exists
    obtain ⟨W,hW,hX⟩:=hg; let u:=2*(Real.exp 2*t); have hu: x ≤ u:=by unfold u; have ht:0<t:=zero_lt_one.trans_le (hx.trans ht); nlinarith [Real.one_le_exp (by norm_num : 0 ≤ (2:ℝ))]
    have hA: 1≤u:=hx.trans hu
    refine ⟨2*(Fintype.card Fiber:ℝ)*N*Real.log 2+v+W,by positivity,⟨v,2*u,hv,by linarith,fun j B he t X h ht=>?_⟩⟩
    have hpB : D≤ B.val:=he.symm ▸ ((le_trans (le_max_left ..) hz).trans (Nat.le_mul_of_pos_right c.val (S^j:Side).property))
    refine origins P i N B D hpB t X (sunny P t B) 0 rfl h hK ht le_rfl (by linarith) (by positivity) hr.le (hD _ _ hpB) (savior ..) (hf ..) hM ?_ hp.le hp' h1 h2 rfl (he.symm ▸ (hX j)); rw [mul_assoc]; exact Q _ (by linarith)
end YM.QCD.Globe
#print axioms YM.QCD.Globe.coreP
