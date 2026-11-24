import YM.QCD.Tax.Reach
/-! # veterans across all sales. Exponential escrow pia. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
variable (G':ι→ℝ) {t h e ψ ξ μ' Λ w:ℝ}{w':ι→ℝ}
open Gas QCD.GasP Ursell
noncomputable def crestP (p:Clusters Y.Bright):ℕ:=∑ i,heft S (p.2 i).val
noncomputable def moist (p:Clusters Y.Bright):ℝ:=∑ i, shareP Y (p.2 i).val
noncomputable def mantel (p:Clusters Y.Bright):ℝ:=∑ i, worthX Y (p.2 i).val
def stand (A:ι → Prop) (p:Clusters Y.Bright):Prop:=∃ i u, u ∈ (p.2 i).val.toRight ∧ A u
def Dated (X y :ι → Prop)(s:ℝ)(p:Clusters Y.Bright):Prop:= 3 ≤ crestP Y p ∨ 1 ≤ moist Y p ∨ Pressure.Stores.till s ≤ mantel Y p ∨ stand Y X p ∨ 2 ≤ crestP Y p ∧ stand Y y p
noncomputable def vigor (p:Clusters Y.Bright):ℝ:=∏ i,∏ j∈(p.2 i).val.toRight,G' j
lemma mist (p:Clusters Y.Bright)(C:Costs)(h:ℝ):giant Y G' C h p=h^(crestP Y p)* vigor Y G' p*Real.exp (Q.ε*mantel Y p)*Real.exp (C.markSeed*moist Y p):=by
   unfold giant major mantel vigor crestP moist; simp_rw [prod_mul_distrib, mul_sum,Real.exp_sum]; rw [Finset.prod_pow_eq_pow_sum]
lemma incomeJ {ι:Type*}(G:ι→ℝ)(h:∀ i,1 ≤ G i)(s:Finset ι)(i:ι)(he:i∈s): G i ≤∏ i∈s,G i:=by rw [← mul_prod_erase s _ he]; exact le_mul_of_one_le_right (zero_le_one.trans (h _)) (one_le_prod (fun _ _=> h _))
lemma standeq (h:∀ i,1 ≤ G' i)(A:ι →Prop)(p:Clusters Y.Bright)(he:∀ i,A i → e ≤ G' i)(ha:stand Y A p): e≤vigor Y G' p:=by
   obtain ⟨i,u,hu,hp⟩:=ha; apply (he u hp).trans; exact (incomeJ G' h _ _ hu).trans (incomeJ (fun i=>∏ j∈(p.2 i).val.toRight,G' j) (fun i=>one_le_prod (fun j _=>h j)) univ _ (mem_univ i))
lemma historic (C:Costs)(X y:ι → Prop)(hx:∀ i,X i → h^3 ≤ G' i)(he:∀ i,y i → h ≤ G' i)(hv:∀ i,1 ≤ G' i)(hz:1 ≤ h)(hw:h^3 ≤ Real.exp C.markSeed)(hm:h^3 ≤ Real.exp (Q.ε*till s))(hp:0 ≤ C.markSeed)(p:Clusters Y.Bright)(hd:Dated Y X y s p):h^3 ≤ giant Y G' C h p:=by
   rw [mist]; let t:= h^(crestP Y p); let q:=Real.exp (Q.ε*mantel Y p); let u:=Real.exp (C.markSeed*moist Y p); let r:=vigor Y G' p
   have ht:1 ≤ t:=one_le_pow₀ hz; have hR:1≤r:= Finset.one_le_prod fun _ _=> one_le_prod (fun _ _=> hv _)
   have hu:1 ≤ u:= Real.one_le_exp (mul_nonneg hp (sum_nonneg fun _ _=> Nat.cast_nonneg _))
   have hq:1 ≤ q:=Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun _ _=> (worthG Y _).2))
   change h^3 ≤ t*r*q*u
   have hΘ:1 ≤ t*r:=one_le_mul_of_one_le_of_one_le ht hR; have hg:=one_le_mul_of_one_le_of_one_le hΘ hq; have h1:t*r*q ≤ t*r*q*u := le_mul_of_one_le_right (zero_le_one.trans hg) hu
   have h2:t*r ≤t*r*q:= le_mul_of_one_le_right (zero_le_one.trans hΘ) hq
   rcases hd with h|h|h|h|⟨hX,hA⟩
   · exact le_trans (pow_le_pow_right₀ hz h) ((le_mul_of_one_le_right (zero_le_one.trans ht) hR).trans (h2.trans h1))
   · exact hw.trans ((Real.exp_monotone (le_mul_of_one_le_right hp h)).trans (le_mul_of_one_le_left (zero_le_one.trans hu) hg))
   · exact hm.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans ((le_mul_of_one_le_left (zero_le_one.trans hq) hΘ).trans h1))
   · exact (standeq Y G' hv X p hx h).trans ((le_mul_of_one_le_left (zero_le_one.trans hR) ht).trans (h2.trans h1))
   · rw [pow_succ]; exact ((mul_le_mul (pow_le_pow_right₀ hz hX) (standeq Y G' hv y p he hA) (zero_le_one.trans hz) (zero_le_one.trans ht)).trans (h2.trans h1))
lemma debt {K:Costs}{u:ℝ}{g:Y.Bright →ℝ} (h:Ready Y.lightF (radiusB s) (fun i=> major Y G' K i.val u*(dime j*g i)) (a+1) Λ ψ t)(he:0 ≤ a)(hv:∀ i,1 ≤ G' i)(hz:1≤u)(hq:0 ≤ K.markSeed)(hp:∀ i,0 ≤ g i)(m:ℕ)(w:ℝ)(μ:Clusters Y.Bright → Prop)[DecidablePred μ](hi:∀ i,μ i → u^3 ≤ giant Y G' K u i)(hn:smiler m (radiusB s) * (Λ*(1-t)⁻¹) ≤ w*u^3): Ac.Hit (seatP Y.lightF) (radiusB s) (fun i=> if μ i then shadow Y j m g i else 0) a w:=by
    intro x; let z i:=shadow Y j m g i; have hh i:0 ≤ z i:=mul_nonneg (by positivity : 0 ≤ (1+ (wag _ _:ℝ))^m) (clusters_nonneg _ (fun i=> mul_nonneg (show 0 ≤ dime j from by unfold dime; positivity) (hp _)) _)
    let r:=u^3; have hr:0<r:=pow_pos (zero_lt_one.trans_le hz) _
    have h1:=budget_scale (inv_pos.mpr hr).le (budget_loosen ((powered Y G' K j m g hp hv hz hq h he) x) hn)
    rw [show r⁻¹* _ = w from ?_] at h1; rotate_left
    · change r⁻¹*(w*r)=_; field_simp
    apply budget_mono h1
    · intro i; split; swap; exact le_rfl; apply mul_nonneg _ (Real.exp_pos _).le; exact ite_nonneg (hh i) le_rfl
    intro i; split; next ht=> dsimp only; by_cases hv:μ i
                              · rw [if_pos hv]; rw [←mul_assoc,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; exact le_mul_of_one_le_left (hh _) ((one_le_inv_mul₀ hr).mpr (hi _ hv)) -- lemma name
                              rw [if_neg hv,zero_mul]; have hf:= h1.1 i; dsimp only at hf; rwa [if_pos ht] at hf
    next _=> simp
end YM.ConnectedActivityE6.Blaze.King
