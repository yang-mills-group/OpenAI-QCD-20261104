import YM.QCD.Beam.Colt
/-! # Feasible additional head. Common μ and one canopy. Mark hulls -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam.Pipe
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
variable {H:Cash W τ μ L Q o C T R}{ι:Type}
local notation "D" => Clump S ι
variable (Y:Pipe H F M ι)
-- after mark `e` for full rarity. Parts τ extras
def unitsP (Q:Target G P)(L:Side)(μ β x C d h:ℝ): Costs:= Buy.quote G L μ (1/2) Q.exp Q.ε Q.δ β x 1 0 (C*Delay.bill G L x^5+d) (Q.goal L x+h)
lemma subsidy (Q:Target G P)(L:Side){μ C p v:ℝ}(hm:0<μ)(hc:0≤C)(hp:0<p)(hz:v<0): ∀ᶠ x:ℝ in atTop,∀ β h d:ℝ,betaF G x L/2≤β→ 0≤h→ h ≤betaF G x L^v→ d≤ p*Delay.fineMonitor G L x→(unitsP Q L μ β x C d h).Buy L Q.halo (radiusB x) :=by
   let h':=max Q.rate v; have hN:h'<0:=max_lt Q.stop hz
   let f i:= Q.goal L i+betaF G i L^v
   let DF:= C+p; have hD:0<DF:=by unfold DF; positivity
   have hh:Rate G L h' f:=Rate.add (Rate.power.weaken (le_max_left ..)) (Rate.power.weaken (le_max_right ..))
   have hk:= Census.width_rate G L 1 0; simp only [one_mul,add_zero] at hk; have hx:= hh.mul (hk.mul_left 16); rw [add_zero] at hx
   filter_upwards [Buy.quoted G L hm (show (0:ℝ)<1/2 by norm_num) Q.pos Q.bound Q.usable hD.le (by norm_num : (1:ℝ)<2) 5 Q.halo,hx.below hN Q.δ Q.pos] with x he hu β h d hβ hY hy hd
   have he':1≤Delay.fineMonitor G L x:= Real.one_le_exp (sq_nonneg _); have hp:= he.1; have hq:=Q.pos; have hh:= Delay.bill_ge G L x
   refine he.2 _ _ _ _ _ (by linarith only [hβ]) le_rfl zero_le_one ?_ ?_ ?_ ?_
   · apply Real.one_le_exp; positivity
   · rw [mul_zero,add_zero,Real.rpow_one]; unfold DF; rw [add_mul,add_mul]; apply add_le_add (le_mul_of_one_le_right (by positivity) he') (hd.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ‹0<p›.le (one_le_pow₀ hh)) (by positivity)))
   · unfold Target.goal; positivity
   refine (show Q.goal L x+h≤ f x from add_le_add le_rfl hy).trans ((le_div_iff₀ (show (0:ℝ)<16*(Animals.ballCost (radiusB x):ℝ) from by have hh := Animals.neighbors_ge (radiusB x); positivity)).mpr ((le_abs_self _).trans hu))
variable {W':Mixed.Costs}{w p :ι →ℝ}
private abbrev r' (S:StepData c f) (ι:Type) := ConnectedActivityE6.Alphabet c f ⊕ ι
def shifts (S:StepData c f)(ι:Type) : Piece S ι≃ Mixed.Alphabet S (r' S ι):=Equiv.sumAssoc ..
def dues (_Y: Pipe H F M ι)(b : Costs) (w:ι→ℝ):Piece S ι→ℝ:= (Mixed.costs S Q.halo (radiusB τ) (steamP S b) (Sum.elim H.opt w)) ∘ (shifts S ι)
def inks (_Y: Pipe H F M ι)(b:Costs) (p:ι→ℝ):Piece S ι→ℝ:= Mixed.lengths S b (Sum.elim (ConnectedActivityE6.lengths T R) p) ∘ shifts S ι
def tenants (_Y:Pipe H F M ι):Piece S ι→ℝ:=fun i=> Mixed.shares S (shifts S ι i)
def scoreP (b:Costs)(w p:ι→ℝ) (s:D): ℝ:= Reserves.setPrice Y.gP (radiusB τ) (Y.inks b p) s
def sizeP (_Y: Pipe H F M ι)(s:D):ℕ:=∑ i∈s,Mixed.shares S (shifts S ι i)
structure Depth (b:Costs)(w p:ι→ℝ):Prop where
 green : b.Buy S.patch.L Q.halo (radiusB τ)
 plans : Accounts S Q.halo (radiusB τ) b (Sum.elim H.birth Y.ground) (Sum.elim H.opt w) (Sum.elim (ConnectedActivityE6.lengths T R) p) (steamP S b)
lemma surveyP (h : S.patch.L=L)(hp :∀ i,0≤w i)(hc :∀ i,0≤p i)(a t:ℝ)
    (hY : (unitsP Q L μ R.beta τ C a t).Buy L Q.halo (radiusB τ))(hh: Ac.Hit Y.ground (radiusB τ) (tariff w p (fun _=>0) Q.ε) Q.relative t):
    Y.Depth (unitsP Q L μ R.beta τ C a t) w p:= by -- L typo
     let b:=unitsP Q L μ R.beta τ C a t
     have he:Costs.Buy b S.patch.L Q.halo (radiusB τ):=h ▸ hY
     refine ⟨he,⟨fun i _=> ⟨mul_nonneg hY.capture (Real.exp_pos _).le,le_rfl⟩,?_,?_,?_⟩⟩
     · rintro (i|i); exact H.earns _; exact hp i
     · rintro (i|i); exact H.armed.extra _; exact hc i
     intro i
     convert! Labels.together _ _ _ H.fares.hit hh i using 1
     ext k
     rcases k with k|k <;> rfl
lemma earned {b :Costs} (h:Y.Depth b w p): Ready Y.gP (radiusB τ) (tariff (Y.dues b w) (Y.inks b p) (fun i=> b.markSeed *Y.tenants i) b.reservePoly) (b.exponent+2*b.reservePoly) b.rootHit b.reserveTree b.q :=by
   let B := Mixed.foot S Q.halo (radiusB τ) (Sum.elim H.birth Y.ground)
   let L := shifts S ι
   have he := Mixed.ready_vertices S Q.halo (radiusB τ) b _ _ _ _ h.green h.plans
   have hz i : Y.gP i=B (L i):=by rcases i with (i|i)|i <;> rfl
   let f := tariff (Mixed.costs S Q.halo (radiusB τ) (steamP S b) (Sum.elim H.opt w)) (Mixed.lengths S b (Sum.elim (ConnectedActivityE6.lengths T R) p)) (Mixed.stamp S b) b.reservePoly
   have heq (i): tariff (Y.dues b w) (Y.inks b p) (fun i=>b.markSeed *Y.tenants i) b.reservePoly i=f (L i):=rfl
   refine ⟨he.1,he.2.1,he.2.2.1, he.2.2.2.1, fun i=>he.2.2.2.2.1 _,fun i=>?_⟩
   have ht:=budget_pull L L.injective (he.2.2.2.2.2 i)
   simp_rw [heq,hz]; exact ht
lemma digits {b:Costs}(h:Y.Depth b w p) (i): 0≤Y.dues b w i ∧ 0≤ Y.inks b p i:=by
  cases e: shifts S ι i with
  | inr x=>exact ⟨by simp only [dues,comp_apply,e]; exact h.plans.holds x, by simp only [inks,comp_apply,e]; exact h.plans.extra x⟩
  | inl B=>
      unfold dues inks; simp only [comp_apply,e,Mixed.lengths, Mixed.costs,Sum.elim]; refine ⟨?_,mul_nonneg h.green.extra (Nat.cast_nonneg _)⟩
      split
      next he => exact (h.plans.packetBound B he).1
      exact le_rfl

def gradeP (b : Costs)(w p:ι→ℝ)(s:D)(r:ℕ): ℝ:=(∏ i∈s,Y.dues b w i)*(1+Y.scoreP b w p s)^r
def enoughP (b: Costs) (w p:ι→ℝ)(s:D)(m l r:ℕ)(t:ℝ):Prop:= m ≤ s.card-1∧ l≤ Y.sizeP s ∧ t ≤ Y.scoreP b w p s
def titleP (b: Costs)(w p:ι→ℝ)(s:D)(m l r:ℕ)(t:ℝ):ℝ:= if Ac.Spark Y.gP s∧ Y.enoughP b w p s m l r t then Y.gradeP b w p s r else 0
lemma priceP {b: Costs}(h:Y.Depth b w p)(m l r:ℕ)(t:ℝ): Ac.Hit Y.full (radiusB τ) (fun s=>Y.titleP b w p s m l r t) b.exponent (b.ceiling m r l t):= by
   intro i
   have he:= earned Y h
   have hx s (_:m ≤ s.card-1) (_:Ac.Spark Y.gP s) (_:i∈ Y.full s) (hz:Y.enoughP b w p s m l r t): t≤ Y.scoreP b w p s ∧ b.markSeed*l ≤ ∑ i ∈ s,b.markSeed*Y.tenants i:=by
     refine ⟨hz.2.2,?_⟩; rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ h.green.marked; simp only [tenants, ← Nat.cast_sum]; exact Nat.cast_le.mpr hz.2.1
   have hp:= Reserves.sets _ _ _ _ _ (fun i=> (digits Y h i).1) (fun i=> (digits Y h i).2) h.green.eps h.green.price he m r i (fun s=> Y.enoughP b w p s m l r t) hx -- arg i order
   convert! hp using 1; funext s; dsimp only [titleP,Pipe.full]
   unfold Reserves.rooted gradeP scoreP currency; by_cases hv: i∈ Finset.biUnion s Y.gP
   · rw [if_pos hv]; by_cases ht:Y.enoughP b w p s m l r t
     · rw [if_pos (show Y.enoughP b w p s m l r t∧ _ from ⟨ht,ht.1⟩)]
       by_cases hu:Ac.Spark Y.gP s
       · rw [if_pos (And.intro hu ht),if_pos (And.intro hu hv)]; ring
       rw [if_neg (fun h=>hu h.1),if_neg (fun h=>hu h.1),zero_mul,zero_mul] -- duplicate?
     rw [if_neg (fun hx=> ht hx.2),zero_mul, if_neg (fun hx=> ht hx.1)]
   rw [if_neg hv]; split
   next hi=> rw [if_neg (fun h=>hv h.2),zero_mul]
   rfl
end YM.QCD.Beam.Pipe
