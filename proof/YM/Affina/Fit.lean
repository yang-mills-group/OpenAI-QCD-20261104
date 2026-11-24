import YM.Plateau.Vigor
import YM.MassiveCompletion.PCACReadout
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative Finset
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}
variable (p q:Flavor 6)(g:Bool)
open Massive.Oriole Compass Submodule Massive.PCAC.Readout YM.MassiveCompletion SixFit
variable {J8:Label 8→ₗ[ℂ]Label 8}{J6:Label 6→ₗ[ℂ] Label 6}
variable {τ:ℝ} (u:Flavor 6→ℝ)(b:Flavor 6→Flavor 6→Bool→ℝ)
lemma properLoss (b:Flavor 6→Flavor 6→ℝ)(m:Flavor 6→ℝ) : Signals.loss b m = SixFit.objective b m := by
   classical
   unfold Signals.loss SixFit.objective
   apply sum_congr rfl; intro i hi; let g(j:Fin 6):=if i=j then (0:ℝ) else (b i j-m i-m j)^2; change ∑ j,g j=_; rw [← sum_erase_add (s:=univ) g (mem_univ i), show g i=0 from by simp[g],add_zero]; apply sum_congr rfl; intro j hj; simp only [g,if_neg (ne_of_mem_erase hj).symm]; ring
local notation "R"=>fun i j:Fin 6=> b i j true
local notation "V"=>fun i j:Fin 6=> b i j false
local notation "T"=>fun i j:Fin 6=> (b i j true:ℂ)
def charter (τ:ℝ): Massive.Signals:=⟨u, Massive.PCAC.Readout.estimate (fun i j=> (b i j true:ℂ)),fun i j=> b i j true,fun i j=> b i j false,τ⟩
-- Read actual weight T.St. both flavor controlled
variable (hD:∃ S: Type,True) -- remove
variable (hc: ∀ i j,b i j true=b j i true) (hM:C.Service u τ)(hW:∀ (p q:Flavor 6)(k:Bool),p≠q→ ‖(b p q k:ℂ) -(markK p q k u:ℂ)‖≤ (1/100:ℝ)*τ)
include hM hc hW
lemma elementsP : (charter u b τ).Read C ∧ (charter u b τ).Masses:=by
     set F:=T; set Z:= τ/100
     have hT:F= T:=rfl; have hbT: R = pairRead F:=by ext i j; unfold pairRead; rw [hT]; change b i j true = ((b i j true)+b j i true) /2; rw [hc i j]; ring
     let A:= charter u b τ; have h:0< τ:= hM.margin; let m:= estimate F
     have hf (p q:Flavor 6)(k:Bool)(hh:p≠q):‖(b p q k:ℂ) -(markK p q k u:ℂ)‖≤ Z:=(hW _ _ _ hh).trans_eq (by unfold Z; ring)
     have h1p (p q:Flavor 6)(k:Bool)(hh:p≠q):|b p q k - markK p q k u|≤ Z:=by rw[show |_ - _|= ‖(b p q k:ℂ) -(markK p q k u:ℂ)‖ from by rw[← Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs]]; exact hf _ _ _ hh
     have hJ(i j:Fin 6)(h:i≠j): ‖F i j - ((u i + u j:ℝ):ℂ)‖≤ Z:= hf i j true h
     obtain ⟨hp,hh⟩:= Massive.PCAC.Readout.positive_injective hJ (fun i=>by unfold Z; linarith only [h,hM.pos i]) (fun i j hj=>by unfold Z; linarith only [h,hM.leave i j hj]); have hq := (fit_unique F m).2 rfl
     refine ⟨⟨hM.tendency,hM.margin,hM.pos,hM.leave,fun p q hh=>h1p p q true hh,fun p q hh=>h1p p q false hh⟩, ⟨fun u=>?_,fun u hu=>?_, hp,hh,fun i j h'=>?_,fun i j h' =>?_⟩⟩
     · change Signals.loss (R) m≤ Signals.loss (R) u; rw[properLoss,properLoss,hbT]; exact hq u
     · change Signals.loss (R) m< Signals.loss (R) u; rw[properLoss,properLoss,hbT]; apply lt_of_le_of_ne (hq _) ?_; intro hv; exact hu ((fit_unique F u).1 (fun x=>by rw[← hv]; exact hq _))
     · obtain ⟨hz,_⟩:=abs_le.mp (h1p i j true h'); change 0<b i j true; change -(τ/100) ≤ b i j true -(u i+u j) at hz; linarith only [hz,h,hM.pos i,hM.pos j]
     change 0<b i j false*(m i -m j); have hR:= hM.leave i j h'; obtain ⟨ha,ht⟩:= abs_le.mp (show |b i j false -(u i-u j)| ≤τ/100 from h1p i j false h'); have h1(t:Flavor 6):|m t - u t|≤2*(τ/100):= estimate_error hJ t; rcases le_abs.mp hR with h|h'
     · exact mul_pos (by linarith only [h,‹0 < τ›,ha]) (by linarith only [h,‹0<τ›,(abs_le.mp (h1 i)).1,(abs_le.mp (h1 j)).2])
     exact mul_pos_of_neg_of_neg (by linarith only[h',h,ht]) (by linarith only[h',h,(abs_le.mp (h1 i)).2,(abs_le.mp (h1 j)).1])
end YM.Sprig
#print axioms YM.Sprig.elementsP
