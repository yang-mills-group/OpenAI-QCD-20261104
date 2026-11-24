import YM.Clays.Gale
import YM.Clays.Atlas
import YM.Cardinal.Quests
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (p:I → Cover)
variable (F: Reel c 6 I D) {U:BudgetPoint}
local notation "o"=> wrap c ∘ p
variable (q:I→Bool)
variable (f:D→Site c)(g:D→ℝ)
local notation "Ψ"=> Ribbon.burst q
open ConnectedActivityE6 Blaze King Reserves
open Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.Poised.Counting Massive.Poised.Counting.Click
open scoped YM.Massive.Poised.Plans.Stamp
open LoomT Stags Massive.Poised.Pipes
variable (X:Massive.SourceRead.TaperHol){U' : YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U')
variable (Dx nL r d:ℕ)
variable (M:ℝ)
local notation "L"=> Single
local notation "Ω"=> Massive.Poised.Carte.Hem.pot
open Card Iris Puff
variable (h: Reel.Occupant F (wrap c ∘ p) q t U 2 (v+a) w (fun _=>1))(hK: Pilot X B d U.order U.power Dx nL r C θ)(hv:1≤ t)(he:0≤v)(ha:0<a)
include h hK hv he ha
set_option maxHeartbeats 530000 in
lemma regalX (i:I)(hz:r+1≤ U.B) : ∃ y: Massive.UV.Label d, Gel q F X i (p i) U y t v (riseP Dx nL U.B a v*w) (riseP Dx nL U.B a v*w) Dx nL r ∧ wealth y.val U.threshold t ≤ C*(riseP Dx nL U.B a v*w):=by
    obtain ⟨f,hf,hF⟩:= h.reserve; simp only [abs_one,prod_const_one,one_mul] at hf; let k:= (o) i; let c':= Single F i; have hq (j:c'): i∈ F.z j.val:= j.2.symm ▸ mem_singleton_self _; have hV(j:c'): k∈(F.addr j.val).support:=h.booked.stamp j.val (mem_image_of_mem (wrap c∘p) (hq j)); let P:= tender q F i c' id k hV; have hP:=tended q F i (o) h.booked c' id k hV
    let D (j:c'):= (P.addr j).support; let X':= Ω (r+1) c (p i); let V (j:c'):=D j∪X'; let a₀:= (4*(U.B:ℝ)+2)^(Dx*nL)*polyPrice a (Dx*nL); let R:=riseP Dx nL U.B a v; let g(j:c'):= ((1+(wag (D j) U.B:ℝ))^Dx)^nL * f j.val
    have hA : coverNumber U.B X' ≤ 81:= (Corona.cover_mono (Corona.halo_mono (show r+1≤1*U.B from hz.trans_eq (one_mul ..).symm) (Subset.refl _)) _).trans (Corona.tile k 1 U.B U.B_pos)
    have hx:=hit_collect k D (fun j:c'=> f j.val) hV (show Ac.Hit D U.B (fun j:c'=> f j.val) (v+a) w from fun i=> budget_pull Subtype.val Subtype.val_injective (hf i)); have hh (j:c') : f j.val≤ g j:= le_mul_of_one_le_left (hF _ _ (hq j)).travels (one_le_pow₀ (one_le_pow₀ (by simp))); have hm(j:c'):0≤g j:=(hF _ _ (hq j)).travels.trans (hh j)
    have hξ : Ac.Hit V U.B g v (R*w):=by
         apply spend_collect V g; refine budget_mono (budget_scale (show 0≤R by unfold R riseP polyPrice; positivity) hx) (fun j=>mul_nonneg (hm _) (Real.exp_pos _).le) fun j=> ?_
         let z:ℝ:= coverNumber U.B (D j); have hZ:0 ≤z:=Nat.cast_nonneg _; have hz(i):0 ≤ f i:=(hF i _ ((h.booked.stays i).choose_spec)).travels -- syntax
         have he : g j ≤ a₀*f j.val * Real.exp (a*z):=by
               unfold g; rw [← pow_mul]; refine (mul_le_mul_of_nonneg_right (le_trans ?_ (mul_le_mul_of_nonneg_left (show (1+z)^(Dx*nL) ≤ polyPrice a (Dx*nL)*Real.exp (a*z) from polynomial_cost ha hZ _) (by positivity : 0≤ (4*(U.B:ℝ)+2)^(Dx*nL)))) (hz _)).trans_eq ?_
               · rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); unfold wag z; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) U.B]
               unfold a₀; ring
         have hv : (coverNumber U.B (V j):ℝ) ≤ z+81:=by unfold z; exact_mod_cast ((Corona.meets_sum (hV j:_∈D j) (halo_subset (r+1) _ (mem_singleton_self k) : k∈X') U.B).trans (add_le_add_right hA _))
         refine (mul_le_mul he (Real.exp_monotone (mul_le_mul_of_nonneg_left hv (by assumption : (0:ℝ)≤v))) (Real.exp_pos _).le ((hm j).trans he)).trans_eq ?_; change _= (a₀ * Real.exp (v*81))* (f j.val*Real.exp ((v+a)*z)); rw [add_mul,mul_add,Real.exp_add,Real.exp_add]; ring
    have ht' :0<t:= zero_lt_one.trans_le hv; have hF'(j:c'): Flame (P.fill j) U (V j) k t Dx nL (g j) := Massive.Poised.Facets.across (Massive.Poised.Facets.extended (hF _ _ (hq j)) (fun i hh=>Corona.extent (D j) U.B hh (hV j)) ht' Dx nL) (V j) subset_union_left
    obtain ⟨p',hc,hc'⟩:= Flyer.distills P V hP (b:=p i) hK rfl (fun i=> subset_union_left) g hF' v hξ he; have ht':=Flyer.toll_ps P V hP (b:=p i) hK rfl rfl (fun i=> subset_union_left) g hF' v hξ hv he hc; obtain ⟨hh0,hM,hs⟩:=ht'; refine ⟨∑' i,p' i,⟨V,p',fun i=>subset_union_left,fun i=>subset_union_right,hc,hs,rfl, ⟨g,hF',hξ⟩,⟨g,?_ ,hξ⟩⟩,?_⟩ -- hF uses old sight.Γ
    · intro j; exact Massive.Poised.Counting.Terrain.padded _ (hh j) (hF _ _ (hq j)) -- fix
    -- Wealth of Label sum via Triangle Budget + positive exp
    have hn : SumBudget (fun j:c'=> wealth (p' j).val U.threshold t) (C*(R*w)):=budget_mono hM (fun j=> wealth_ge ..) fun j=> le_mul_of_one_le_right (wealth_ge ..) (Real.one_le_exp (mul_nonneg he (Nat.cast_nonneg _)))
    exact (Stamp.total_wealth p' hs).trans hn.2.2 -- syntax inspect
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.regalX
