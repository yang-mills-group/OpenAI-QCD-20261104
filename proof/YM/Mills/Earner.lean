import YM.Mills.Glow
/-! # Pipe.Ideal retains costs on entire visits. Fake-depth proof for the true packing geometry not fictional layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam.Pipe
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Loom.Fleet Loom Jets.Touch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F:Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {M: Type*}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}
local notation "D" => Clump S ι
variable (Y:Pipe H F M ι)
def ideal (_Y:Pipe H F M ι)(θ :ℝ)(w:ι→ℝ) : Piece S ι→ℝ:=
 let b:= Glow.billsV Q L μ C θ R.beta τ
 (Mixed.costs S Q.halo (radiusB τ) (steamP S b) (Sum.elim (fun j=> lantern L τ*H.opt j) w)) ∘ shifts S ι
local notation "ρ" => lantern L τ
variable {θ:ℝ}{w p:ι→ℝ}{κ:ι→ℝ}
local notation "cV"=> Glow.billsV Q L μ C θ R.beta τ
local notation "cQ"=> Glow.simple Q L μ C θ R.beta τ
lemma earnest (h : S.patch.L=L) (hp:0≤ p)(ht:1≤lantern L τ)(hv:(Glow.billsV Q L μ C θ R.beta τ).Buy L Q.halo (radiusB τ))(hh: Ac.Hit Y.ground (radiusB τ) p Q.relative (Glow.levelX L θ τ)):
   Ready Y.gP (radiusB τ) (tariff (Y.ideal θ p) (Y.inks cV (fun _=>0)) (fun i=>(cV).markSeed * Y.tenants i) (cV).reservePoly) ((cV).exponent+2*(cV).reservePoly) (cV).rootHit (cV).reserveTree (cV).q ∧ ∀ i,0≤ Y.ideal θ p i:=by
    let X:= Sum.elim (fun i=>lantern L τ*H.opt i) p; have he : Accounts S Q.halo (radiusB τ) cV (Sum.elim H.birth Y.ground) X (Sum.elim (ConnectedActivityE6.lengths T R) (fun (_:ι)=>0)) (steamP S cV):=by
        have hf:0 ≤ ρ:=zero_le_one.trans ht
        refine ⟨fun i _=> ⟨mul_nonneg hv.capture (Real.exp_pos _).le,le_rfl⟩,?_,?_,?_⟩
        · rintro (i|i); exact mul_nonneg hf (H.earns _); exact hp i
        · rintro (i|i); exact H.armed.extra _; exact le_rfl
        convert! Labels.together _ _ _ (Jets.Sun.heights_factor ρ _ _ (fun i=> ρ*tariff H.opt (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε i) H.fares.hit (fun _=>rfl) hf) hh using 1 -- maybe Hit expects H.opt*T.length
        funext i; rcases i with i|i
        · exact mul_assoc ..
        simp [tariff,X]
    let b:=cV
    have hζ:= Mixed.ready_vertices S Q.halo (radiusB τ) b _ _ _ _ (h ▸ hv) he
    let X₀:= Mixed.foot S Q.halo (radiusB τ) (Sum.elim H.birth Y.ground); let V:= shifts S ι
    have hz i:Y.gP i=X₀ (V i):=by rcases i with (i|i)|i <;> rfl
    let ps0:= Mixed.costs S Q.halo (radiusB τ) (steamP S b) X; let f := tariff ps0 (lengths S b (Sum.elim (ConnectedActivityE6.lengths T R) (fun _=>0))) (Mixed.stamp S b) b.reservePoly
    have heq(i):tariff (Y.ideal θ p) (Y.inks cV (fun _=>0)) (fun i=>(cV).markSeed * Y.tenants i) (cV).reservePoly i=f (V i):=rfl
    refine ⟨⟨hζ.1,hζ.2.1, hζ.2.2.1,hζ.2.2.2.1, fun i=> hζ.2.2.2.2.1 (V i),fun i=>?_⟩,fun i=>?_⟩
    · have ht:=budget_pull V V.injective (hζ.2.2.2.2.2 i)
      simp_rw [heq,hz]; exact ht
    change 0 ≤ ps0 (V i); cases e:V i with
    | inr x=>exact he.holds x
    | inl x=> unfold ps0 Mixed.costs; dsimp only [Sum.elim]; split; exact (he.packetBound x ‹_›).1; exact le_rfl
-- paying markup when obligatory entries carry shell.R
lemma luminous (hp:∀ i,w i*κ i≤p i) (i : Piece S ι) : Y.dues (Glow.simple Q L μ C θ R.beta τ) w i * Sum.elim (fun _=>lantern L τ) κ i ≤ Y.ideal θ p i:=by
   rcases i with (i|i)|i
   · by_cases h:Packets.connected S Q.halo (radiusB τ) i
     · unfold dues ideal; change (if _ then steamP S cQ i else _) * ρ ≤ (if _ then steamP S cV i else _); rw [if_pos h, if_pos h]; unfold steamP Packets.income; change 1* (_:ℝ)*_ ≤ _*_; rw [one_mul]; exact le_of_eq (mul_comm ..)
     have he: Y.dues cQ w (.inl (.inl i))=0:=if_neg h; rw [he,zero_mul,show Y.ideal θ p (.inl (.inl i))=0 from if_neg h]
   · exact le_of_eq (mul_comm ..)
   exact hp _
lemma grassbud (b:Costs)(p:ι→ℝ) (sD: Piece S ι→ℝ) (hs:Ready Y.gP (radiusB τ) (tariff sD (Y.inks b p) (fun i=> b.markSeed *Y.tenants i) b.reservePoly) (b.exponent+2*b.reservePoly) b.rootHit b.reserveTree b.q)(he:b.Buy S.patch.L Q.halo (radiusB τ)) (hr:∀ i,0≤ sD i)(hp:∀ i,0≤ Y.inks b p i):
   let h u:= if Ac.Spark Y.gP u then ∏ i∈u,sD i else 0
   Ac.Hit Y.full (radiusB τ) h b.exponent (b.rootHit*(1-b.q)⁻¹):=by
    intro h x; let t:=tariff sD (Y.inks b p) (fun i=> b.markSeed *Y.tenants i) b.reservePoly
    have hv:=touch_tail Y.gP (radiusB τ) hs x 0; simp only [Nat.zero_le,if_true,pow_zero,mul_one] at hv
    refine budget_mono hv ?_ ?_
    · intro i; split; swap; · exact le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le; unfold h; split; exact prod_nonneg fun i _=>hr _; exact le_rfl
    intro i; split
    swap; · exact hv.1 _
    next hk=>
    unfold h; split; swap; · rw [zero_mul]; exact hv.1 _
    next hx=>
    unfold touches; rw [if_pos ⟨hx,hk⟩,prod_mul_distrib]; apply mul_le_mul
    · change _ ≤ ∏ j∈i,t j; apply prod_le_prod (fun i _=>hr i); intro i hi; unfold t tariff; apply le_mul_of_one_le_right (hr i) (Real.one_le_exp (add_nonneg (mul_nonneg (by have h:=he.eps; positivity) (hp i)) (mul_nonneg he.marked (by unfold tenants; positivity))))
    · unfold currency; rw [←Real.exp_sum]; apply Real.exp_monotone; rw [← mul_sum, ← Nat.cast_sum]; exact mul_le_mul (le_add_of_nonneg_right (by have h:=he.eps; positivity)) (Nat.cast_le.mpr (Ac.cover _ _ hx)) (Nat.cast_nonneg _) (le_add_of_le_of_nonneg he.price (by have h:=he.eps; positivity))
    · exact (Real.exp_pos _).le
    exact prod_nonneg fun i _=> hs.2.2.2.2.1 i
end YM.QCD.Beam.Pipe
#print axioms YM.QCD.Beam.Pipe.earnest
#print axioms YM.QCD.Beam.Pipe.grassbud
#print axioms YM.QCD.Beam.Pipe.luminous
