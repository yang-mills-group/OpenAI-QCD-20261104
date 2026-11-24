import YM.Helio.Trace
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
variable (V:Grid c)(α:Axis)(x:Site c)(d:Tick c)
local notation "Mα"=>wheelS (rplus c α)
def way (x:Site c)(α:Axis)(V:Pulse c):Bundle:=Lat.seam 0 x α •TouchL (V.1 (x,α))
lemma wayT : letterP V α x= way x α (settled V):=TouchL.map_smul ..
section
open Metric
lemma wayC (x:Site c)(Y:Support c)(h:x∈Y)(ht:x+step α∈ Y)(hP:η≤1): Crop x (x+step α) η Y (way x α) (‖TouchL‖*2):=by
   let z x':= way x α x'; have he (u:Grid c): (z (settled u))=letterP u α x:= (wayT ..).symm
   refine ⟨by positivity,fun _=>⟨h,ht⟩,fun i _=>?_,fun i hi=>?_,fun i j hv=>?_,fun i k=> ?_⟩
   · unfold way; fun_prop
   · obtain ⟨U,hU⟩:= Set.mem_iUnion.mp hi; rw [Metric.mem_ball,dist_eq_norm] at hU; exact (touch_site ..).trans (mul_le_mul_of_nonneg_left (show ‖i.1 (x,α)‖ ≤2 from by have he:=Paths.strand_use i U (posDir α) x hU.le; change ‖i.1 (x,α)‖≤_ at he; linarith) (norm_nonneg TouchL))
   · unfold way; exact congr_arg (fun (U:su.El)=> Lat.seam 0 x α • TouchL (colour U)) (hv (x,α) h ht)
   rw [show way x α (settled i)=_ from he i, show way _ _ (settled _)=_ from he (gauge k i), letterP,thread_change]; unfold letterP; simp only [touch_star,touch_mul]
end
noncomputable def strip (α:Axis)(d:Tick c):Support c:= d.2.2∪ ((wheelS (rplus c α) d).2.2)
variable (G:Silo c)
lemma primeM (hv:fertile d): d.1∈ strip α d∧d.1+step α∈strip α d∧d.2.1∈strip α d∧d.2.1+step α∈strip α d:=by
    unfold strip; rw [risesT]; exact ⟨mem_union_left _ hv.1,mem_union_right _ (mem_image_of_mem _ hv.1), mem_union_left _ hv.2, mem_union_right _ (mem_image_of_mem _ hv.2)⟩
lemma bigger (p q:Site c)(X Y:Support c)(v:Pulse c→Bundle)(hp:Crop p q η X v t)(h:X⊆Y): Crop p q η Y v t:=by
    rcases hp with ⟨hX,hP,hS,hK,hh,hL⟩; exact ⟨hX,fun z=>⟨h (hP z).1,h (hP z).2⟩,hS,hK,fun U V he=>hh U V (agrees_mono he (fun _ hx=>h hx)),hL⟩
abbrev novaX (d:Tick c)(G:Silo c): Pulse c→Bundle:=G d.1 d.2.1 d.2.2
def novaB (α : Axis)(d:Tick c)(G:Silo c) :=way d.1 α*novaX (wheelS (rplus c α) d) G+(-1:ℂ) • (novaX d G* way d.2.1 α)
def weighT (d: Tick c)(A:BankP c)(α:Axis):ℝ:= ‖TouchL‖*2*silos A (wheelS (rplus c α) d)+silos A d*(‖TouchL‖*2)
lemma novaCost (hp:Run.Pack id id η δ B U q G A)(hv:fertile d)(h0: 0<η)(h1:η≤1): Crop d.1 (d.2.1+step α) η (strip α d) (novaB α d G) (weighT d A α) :=by
    let S:= strip α d; obtain ⟨hB,hK,h,hP⟩:= primeM α d hv; have ht : (Mα d).1=d.1+step α:=congr_arg Prod.fst (risesT α d); have hζ:(Mα d).2.1=d.2.1+step α:= congr_arg Prod.fst (congr_arg Prod.snd (risesT α d))
    have hp': Crop (d.1+step α) (d.2.1+step α) η S (novaX (Mα d) G) (silos A (Mα d)):= by rw [← ht,← hζ]; exact bigger _ _ _ S _ (hp.crop ..) subset_union_right
    have hX:= Crop.joined (bigger d.1 d.2.1 d.2.2 S (novaX d G) (hp.crop ..) subset_union_left) (wayC α _ _ h hP h1) h0
    unfold weighT; have hℓ:=hX.alloy (-1:ℂ); simp only [norm_neg,norm_one,one_mul] at hℓ; have hf:=(wayC α d.1 _ hB hK h1).joined hp' h0; rw [show S ∪ strip α d=S from union_idempotent S] at hℓ; rw [show strip α d∪ S=S from union_idempotent S] at hf; exact hf.plus hℓ
lemma earnedT : novaB α d G (settled V)= newDay α d G V:=by unfold novaB; simp only [Pi.add_apply,Pi.neg_apply,Pi.mul_apply,neg_smul,one_smul,←wayT]; rw [← sub_eq_add_neg]; rfl
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.novaCost
