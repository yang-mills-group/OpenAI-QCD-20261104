import YM.Mills.Flare
/-! # Seraph — writing full enrolled marks from Dovetail
 from ANY incoming projection/reserve at real Tilt. Never drop odd slot coefficients.
 This file embeds publishers into needed shape/power addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.FlareV
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Relight Plate Stew Stew.Phased Reggae
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K R U:Type}[Fintype I] {c:Side}{N:ℕ}
open Stitch
variable (P:Rise c N E K) (F:Reel c N I R)(G:Film c N I U)
local notation "Z"=> Keys c N
local notation "X"=> Ribbon.Spine I
local notation "U★"=>rootR X (Keys c N)
local notation "P★"=>vacR X (Keys c N)
local notation "P₁"=> fun i=>rootR X Z ∘ P.main i
local notation "P₂"=> fun i=>rootR X Z ∘ P.plug i
-- Dilation / erasing choices exact even with K rescaling. Require nonzero scales at semantic tsum indefinite uses; otherwise summability hypotheses (from preroll). Keep occurrences.Pt
variable (q:I→Bool)(p:I→Site c)(V:Grid c)(Y: Patron.Rail c N B)(w:I→ℝ)
local notation "τφ"=> capstone Z w
noncomputable def volume_up: Reel c N I R:=⟨F.addr,F.z,fun i=>capstone Z w ∘ F.mark i⟩
noncomputable def volume_F: Film c N I U:=⟨G.addr,G.z,fun i=>capstone Z w ∘ G.mark i⟩
local notation "Re★"=> volume_up F w
local notation "Fi★"=> volume_F G w
lemma lift_e (hp:F.Book p q)(i:R) : (Re★).mark i= fun V=>give w (F.z i) • F.mark i V:= by funext i; change τφ _=_; rw [patrol_open w (q:=q) _ _ (hp.stage _ _).1,attuned]
lemma lift_k (t:ℝ)(hp:G.Beat N p q t)(i:U) : (Fi★).mark i= fun V=>give w (G.z i) • G.mark i V:= by funext i; change τφ _=_; rw [patrol_open w (q:=q) _ _ (hp.budget _ _).1,attuned]
variable (t:ℝ)(sx:Finset I)(A':Support c){x:ℝ}
lemma lit (u:Tine c N I)(hp:lights sx A' p q u) (w:ℂ): lights sx A' p q (w • u):=by refine ⟨hp.1.smooch w,fun i=>?_⟩; change pluck Z i (w • u)∈region (limits A'); rw [map_smul]; exact Subalgebra.smul_mem _ (hp.2 i) w -- hole unification
lemma decorates (hp:F.Book p q): (Re★).Book p q:=by
    let L:=τφ; refine ⟨hp.stays,hp.stamp,fun i=> L.toLinearMap.toContinuousLinearMap.measurable.comp (hp.permit i),fun i U V h=>congr_arg L (hp.room i U V h),?_,?_⟩
    · intro i V; rw [lift_e F q p w hp]; exact lit _ _ _ _ _ (hp.stage i V) _
    intro i V z; rw [lift_e F q p w hp]; dsimp only; rw [map_smul,hp.tint]
lemma renews (hp:G.Beat N p q t) : (Fi★).Beat N p q t:=by
    let L:=τφ; refine ⟨hp.commits,hp.spark,fun i=> L.toLinearMap.toContinuousLinearMap.measurable.comp (hp.matters i), fun i U V h g=>congr_arg L (hp.reads i U V h g),?_,fun i U hh=> hp.mask i U (fun he=> hh ((congr_arg L he).trans (map_zero _))),?_⟩
    · intro i V z; rw [lift_k G q p w t hp]; dsimp only; rw [map_smul,hp.color]
    intro i V; rw [lift_k G q p w t hp]; exact lit _ _ _ _ _ (hp.budget i V) _
lemma patrol_inv (w:I→ℝ)(hv:∀ i,w i≠0)(z: Patio (Z⊕Ribbon.Spine I)) : capstone Z (fun i=> (w i)⁻¹) (capstone Z w z)=z:=by
    apply pluckVisible; intro s; rw [patrol,patrol,smul_smul]; suffices ignites (fun i=> (w i)⁻¹) s*ignites w s=1 by rw [this,one_smul]
    unfold ignites; rw [← prod_mul_distrib]; refine prod_eq_one ?_; intro i _; unfold tollCard; split
    next h=> rw [Complex.ofReal_inv]; exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hv _))
    simp only [Complex.ofReal_one,mul_one]
private lemma inject_sum {D:Type} (F:D→ Patio (Keys c N⊕Ribbon.Spine I))(hv:∀ i,w i≠0): τφ (∑' i,F i)=∑' i, τφ (F i):=by
    by_cases h:Summable F; · exact ((τφ).toLinearMap.toContinuousLinearMap).map_tsum h
    suffices hg: ¬Summable (fun i=>τφ (F i)) by rw [tsum_eq_zero_of_not_summable h,map_zero,tsum_eq_zero_of_not_summable hg];
    intro ht; apply h; let L:= (capstone Z fun i=> (w i)⁻¹).toLinearMap.toContinuousLinearMap
    exact (ContinuousLinearMap.summable L ht).congr (fun i=>patrol_inv w hv _)
local notation "u!"=> (rootR X Z)
lemma cashInV (hv:∀ i,w i≠0)(U₀:Grid c→ EvenA c N) : τφ (relativeE N F G Y U₀ t V)= relativeE N (Re★) (Fi★) Y U₀ t V :=by
     let A0:=τφ; unfold relativeE; rw [map_mul,map_exp A0 A0.toLinearMap.toContinuousLinearMap.continuous,map_add A0,partTone]
     refine congr_arg₂ (·*·) (congr_arg _ (congr_arg (u! (U₀ V)+·) ?_)) ?_
     · let g i:= Reel.mist F t i V; refine Eq.trans (inject_sum w g hv) (tsum_congr fun i=>?_); unfold g Reel.mist; by_cases h:Healthy t (F.addr i).support V
       · rw [masked_eq _ _ _ _ (show Healthy t (F.addr i).support V from h),masked_eq _ _ _ _ (show Healthy t ((Re★).addr i).support V from h)]; rfl
       rw [masked_ne _ _ _ _ (show ¬ Healthy t (F.addr i).support V from h),masked_ne _ _ _ _ (show ¬Healthy t ((Re★).addr i).support V from h)]; exact map_zero _
     let x := Film.addressSets N G Y; let f(i):=Film.spruced N G Y i V; unfold Film.reports; change A0 (∑' i,Plate.roof x _ (RG.flags t V) i)= ∑' i,Plate.roof x _ (RG.flags t V) i
     have he:A0 ∘ f=fun i=>Film.spruced N (volume_F G w) Y i V:= by funext i; cases i with|inl i=> exact partTone w _|inr i=> rfl
     refine (inject_sum w _ hv).trans (tsum_congr fun i=>?_)
     change A0 (Plate.roof x f _ _)=Plate.roof x _ (RG.flags t V) i; rw [← he]; unfold Plate.roof; split; exact map_prod ..; exact map_zero ..
open SC Push.AbsoluteSums
variable {μ s δ u σ Qv φ :ℝ}{n:ℕ}
lemma valBoost (A:R→ℝ) (C:ℝ)(hu:0≤C)(h:A≥0) (hp:∀ i,‖give w (F.z i)‖≤ C)(hv:Valve F p q u t n μ s A) : Valve (volume_up F w) p q u t n μ (C*s) A:=by
    have hh:= hv.book; obtain ⟨f,hQ,hL⟩:=hv.back
    refine ⟨decorates F q p w hh,fun i=> C*f i,fun i V=> ?_,?_⟩
    · have he i V: Reel.mist (volume_up F w) t i V = give w (F.z i) • Reel.mist F t i V:=by unfold Reel.mist; rw [lift_e F q p w hh]; by_cases he:Healthy t (F.addr i).support V; rw [masked_eq _ _ _ _ (show Healthy t ((volume_up F w).addr i).support V from he),masked_eq _ _ _ _ he]; rw [masked_ne _ _ _ _ (show ¬ Healthy t ((volume_up F w).addr i).support V from he),masked_ne _ _ _ _ he,smul_zero]
      rw [he]; unfold Stitch.Tablet.credits; rw [map_smul,load_scale]; exact mul_le_mul (hp i) (hQ i V) (load_nn ..) hu
    exact Jets.Sun.heights_factor C _ _ _ hL (fun i=>by apply mul_left_comm) hu
lemma filmBoost (hF: G.Beat N p q t)(hK:G.Stock N n Qv μ u δ w): (Fi★).Stock N n Qv μ u δ (fun _=>1):=by
    let Q:= Fi★; obtain ⟨g,hp,hq⟩:=hK.price
    let zt i:=‖give w (G.z i)‖
    refine ⟨fun i=>zt i*g i,fun i V=> ?_,?_⟩
    · change Stitch.Tablet.credits u (Q.mark i V)≤ zt i*g i
      unfold Q; rw [FlareV.lift_k G q p w t hF]; unfold Stitch.Tablet.credits; rw [map_smul, load_scale]; exact mul_le_mul_of_nonneg_left (hp i V) (norm_nonneg _)
    refine Eq.mp (congr_arg (fun f=>Ac.Hit (fun i=>(G.addr i).place) n f μ δ) ?_) hq
    funext i; unfold Film.fares QCD.GasP.taxed; change _=Qv^(G.addr i).inv.card*((∏ j∈G.z i,|(1:ℝ)|)*(zt i*g i)); simp only [_root_.abs_one,prod_const_one,one_mul]; unfold zt give; simp only [norm_prod,Complex.norm_real,Real.norm_eq_abs]
end YM.MassiveQCD.FlareV
#print axioms YM.MassiveQCD.FlareV.cashInV
#print axioms YM.MassiveQCD.FlareV.filmBoost
#print axioms YM.MassiveQCD.FlareV.valBoost
