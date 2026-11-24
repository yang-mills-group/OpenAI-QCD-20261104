import YM.Intag.Wheat
import YM.Alum.Fur
import YM.Lyre.Story
/-! # Words priced in actual projection caps and through typed schedules. Core inequalities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet.Sworn
variable {n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola
variable {I:Type}[Fintype I](Q:I→Bool)(X Y:I→Stud n F) (hp:∀ i V,Hom (Q i) (X i V))(hy:∀ j U,Hom (Q j) (Y j U))
variable (L:List I)(u:I→ℕ)(p: I→ E4)
open Quills.Clover YM.Arise.Bill YM.Arise.Count Play Play.Chamber
variable (A:∀ i:I,Cups (u i) (Q i))
noncomputable abbrev readL (x:I→Stud n F)(hx:∀ i V,Hom (Q i) (x i V)): Stud n F:= fun V=>wordA Q p u (fun i=>x i V) (fun i=>hx i V) A L
local notation "Fx"=> readL Q L u p A X hp
local notation "Fy"=> readL Q L u p A Y hy
variable (Z:Set (Site n)) (hL:L.Nodup)(h:Set.InjOn p L.toFinset)
include h hL
lemma curls (hX:∀ i∈ L,Fence Z (X i)): Fence Z (Fx) ∧ Potion (Fx):=by
     let U(i:Finset I):=-cetacea (cupZ Q u A p) i; have hB:= Lyre.fenceText Q X hp L U Z hX (?_ :∀ i∈ bindV L,Honest Q i (U i)) hL
     swap; · intro i hi; obtain ⟨hh,hq⟩:=cents Q u A p L.toFinset h i (mem_powerset.mp (mem_of_mem_erase hi)); exact fun G f=> by rw[show U i=_ from rfl,map_neg]; exact (hh G).minus
     rw[← show exciteE Q X hp L U=(Fx) from ?_]; exact hB
     funext V; unfold exciteE readL wordA; apply congr_arg; unfold kits; congr 2; refine sum_congr rfl fun i hi=> ?_
     unfold Function.comp U; rw [map_neg]; exact congr_arg _ ((cents Q u A p L.toFinset h i (mem_powerset.mp (mem_of_mem_erase hi))).2 (Keys n F))
noncomputable abbrev betaX (i:Finset I) (X:I→Stud n F):= (List.ofFn (X ∘ Quills.tour i)).prod
lemma featured : Fx = ∑ i∈ L.toFinset.powerset, compZ Q u A p L i • betaX i X:=by
     funext V; change wordA Q p u _ _ _ L=_
     rw [testH Q u A p L hL (fun i=> X i V) (fun i=>hp i V) h, Finset.sum_apply]; refine sum_congr rfl fun i hi=>?_
     exact congr_arg (compZ Q u A p L i • ·) (songX n X _ V)
variable (R:Regulator n F)(T W:Tiling n)(E:Ladder T W)(C:T.Cell)(v:I→W.Cell)(e z H S K r:ℝ) (hx:∀ i,Fence (W.chamber (v i)) (X i))(hw:∀ i,Fence (W.chamber (v i)) (Y i))(hX:∀ i, W.chamber (v i)⊆ T.chamber C)(hF:Smoke W R)(hT:Smoke T R)(hC:∀ j,(W.chamber j).Nonempty)(he:0≤ e)(hz:1 ≤ z)(hk:0 ≤K)
local notation "top"=>topH
local notation "Πt" X:arg=> topH T R X C
include E hx hw hX hF hT hC he hz
lemma plank (ht:Injective v)(hD:∀ i, top W R (X i) (v i) ≤ z ∧ top W R (Y i) (v i) ≤ z ∧ top W R (X i-Y i) (v i) ≤e) (hq:∀ i∈ L.toFinset.powerset, ‖compZ Q u A p L i‖ ≤ H) (hK:Πt Fy ≤ r): Πt Fx ≤ (L.toFinset.powerset).card*(H*((Fintype.card I)*(e*z^ Fintype.card I)))+r:=by
      let U(i:Finset I):= compZ Q u A p L i • betaX i X; let t(i:Finset I):= compZ Q u A p L i • betaX i Y
      let A':= L.toFinset.powerset; let f(i:Finset I):= U i-t i; have hW(i:Finset I):= Goblet.subs R i.card (X∘tour i) (Y∘tour i) (Q∘ Quills.tour i) T W E C (v ∘ tour i) (fun j=>hx _) (fun j=>hw _) (fun j V=>⟨hp _ _,hy _ _⟩) (ht.comp (Quills.snug i)) (fun j=>hX (Quills.tour i j)) hF hT hC e z he hz (fun j=>hD _);
      have hxF(i:Finset I):Potion (U i)∧Potion (t i):=by
           let L:=List.ofFn (tour i); have hV(z:I→ Stud n F)(h:∀ j,Potion (z j)): Potion (betaX i z):=by unfold betaX; rw [← List.map_ofFn]; exact potProd _ _ fun j _=> h j
           exact ⟨potscaling (hV _ fun j=> ⟨_,hp j⟩) _,potscaling (hV _ fun j=>⟨_,hy j⟩) _⟩ -- hV unused later. maybe need homogeneous Full difference. 
      have hD1(i: Finset I): f i=compZ Q u A p L i •(betaX i X-betaX i Y):=(smul_sub ..).symm
      have hv(i:Finset I):Fence (T.chamber C) (f i) ∧ Potion (f i):=by rw [hD1]; exact ⟨(hW i).1.mass _, potscaling (hW i).2.1 _⟩
      have hu: Fx = ∑ i∈ A', f i+Fy := by -- convention ∑ over expr + Fy? fix
           rw [featured Q X hp L u p A hL h, featured Q Y hy L u p A hL h]; unfold f; rw[sum_sub_distrib]; exact (sub_add_cancel ..).symm
      have hr(i:Finset I)(hi:i∈ A'): top T R (f i) C ≤ H * ((Fintype.card I:ℝ)*(e*z^ Fintype.card I)) := calc
          _ = ‖compZ Q u A p L i‖* top T R (betaX i X-betaX i Y) C:=hD1 i ▸ top_spin T R C _ _
          _ ≤ H * (Fintype.card I * (e*z^ Fintype.card I)):= by
               have hh:= Finset.card_le_univ i; exact mul_le_mul (hq i hi) (le_trans (hW i).2.2 (mul_le_mul (by exact_mod_cast hh) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hh) he) (mul_nonneg he (pow_nonneg (zero_le_one.trans hz) _)) (Nat.cast_nonneg _))) (top_nn ..) ((norm_nonneg _).trans (hq i hi))
      -- sum triangle issue: Potion (∑ f) not proven matching SAME: but Fx-Fy is parity-total from curls enough?? each curls potion may differ. use Block sum via Unit∪. dec.Left
      let B:= (Sum.inl '' (A': Set (Finset I))) ∪ {Sum.inr ()}
      let a:Finset (Finset I ⊕ Unit):= A'.disjSum {()}; let y:= Sum.elim f (fun _:Unit=> Fy); have hP:= curls Q Y hy L u p A (T.chamber C) hL h (fun i _=> (hw i).high (hX i));
      have he' : Fx= ∑ i∈ a, y i:= hu.trans (by unfold a; rw [Finset.sum_disjSum,Finset.sum_singleton]; rfl)
      rw [he']; apply (bills_si R T C a y _ hT).trans; unfold a; rw [Finset.sum_disjSum,sum_singleton]; exact add_le_add ((sum_le_sum hr).trans_eq (by simp [A'])) hK
      · rintro (i|i) _; exact hv i; exact hP -- bullet
end Goblet.Sworn
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.Sworn.plank
