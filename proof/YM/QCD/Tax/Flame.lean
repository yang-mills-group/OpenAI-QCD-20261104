import YM.QCD.Tax.Tall
/-! # heir early treasury. exact. no Level boundary agendas yet. -/
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
variable {G':ι→ℝ} {t h e ψ ξ μ' Λ w u z:ℝ}{w':ι→ℝ}
open QCD.GasP Gas Ursell QCD.Port
set_option quotPrecheck false
lemma pastry (G:ι→ℝ)(W':Y.Bright → ℝ)(hw:∀ i,1 ≤ G i)(hv:∀ i,0 ≤ W' i)(S':Costs)(hk:0 ≤ S'.markSeed)(hf:1≤ z)(he:0 ≤ t)(p:Ready Y.lightF (radiusB s) (fun i=>major Y G S' i.val z*(dime j*W' i)) (t+1) Λ 1 (1/2))(hs:smiler k (radiusB s)*(Λ*(1-1/2)⁻¹) ≤ v*z): Ac.Hit (seatP Y.lightF) (radiusB s) (shadow Y j k W') t v :=by
    intro x; have hz:=zero_lt_one.trans_le hf; have hm :=budget_scale (inv_pos.mpr hz).le (budget_loosen (powered Y G S' j k W' hv hw hf hk p he x) hs); rw [show z⁻¹*(v*z)=v from (by field_simp)] at hm; apply budget_mono hm
    · intro i; split; swap; · exact le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le; exact mul_nonneg (by positivity) (clusters_nonneg _ (fun i=> mul_nonneg (by unfold dime; positivity) (hv i)) _)
    intro i; split; next ht=>
      dsimp only; rw [← mul_assoc,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply le_mul_of_one_le_left (mul_nonneg (by positivity : 0 ≤ (1+(wag (seatP Y.lightF i) (radiusB s):ℝ))^k) (clusters_nonneg _ (fun i=>mul_nonneg (show 0≤ dime j from by unfold dime; positivity) (hv i)) _)); apply (one_le_inv_mul₀ hz).mpr
      let k:= i.snd none; have hp : 1≤ crestP Y i:= Nat.le_trans (Nat.succ_le_of_lt (show 0 < k.val.card from Finset.card_pos.mpr k.2.1.2.1.1)) (Nat.le_trans (show k.val.card ≤heft S k.val from Nat.le_add_right ..) (single_le_sum (f:=fun b=> heft S (i.2 b).val) (fun _ _=> Nat.zero_le _) (mem_univ none)))
      rw [mist]; refine (le_self_pow₀ (n:=crestP Y i) hf (by omega)).trans (le_trans ?_ (le_mul_of_one_le_right (by have hv:1 ≤ vigor Y G i:= one_le_prod fun i _=> one_le_prod fun i _=> hw i; positivity) (Real.one_le_exp (mul_nonneg hk (sum_nonneg fun i _=> Nat.cast_nonneg _))))) -- annotate
      refine le_trans (le_mul_of_one_le_right (pow_nonneg hz.le _) (one_le_prod fun i _=> one_le_prod fun i _=> hw i)) (le_mul_of_one_le_right (mul_nonneg (pow_nonneg hz.le _) (zero_le_one.trans (one_le_prod fun i _=> one_le_prod fun i _=> hw i))) (Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun i _=> (worthG Y _).2))))
    next _=> simp
lemma strengths (hh:Heavy Ξ)(hβ:1 ≤ betaF su s L) (hp:∀ i,1 ≤ G' i)(ht:∀ i,0 ≤ w' i)(hZ:Ac.Hit Y.ground (radiusB s) (fun i=>G' i*w' i) Q.relative t) (hb:(unitsP Q L μ R.beta s C' e t).Buy S.patch.L Q.halo (radiusB s))(p:Bank (unitsP Q L μ R.beta s C' e t) (radiusB s) Q s u L j k l a)(hu:0< u)
    (X y:ι →Prop) (he:∀ i,X i → betaF su s L^2 ≤ G' i)(hx:∀ i,y i → betaF su s L^(3/5:ℝ) ≤ G' i):
    let W:= grate Y j k u (checkL Ξ w' e t); let U:= shadow Y j l W
    Ac.Hit (seatP Y.lightF) (radiusB s) U a (flowM L s) ∧ Ac.Hit (seatP Y.lightF) (radiusB s) (fun i=> if Dated Y X y s i then U i else 0) a (jelly L s):=by
    intro W U; let ξ:=unitsP Q L μ R.beta s C' e t
    have hB:=brew Y Ξ G' hh (show spiceR L s ≤ PhysicalNext.Repeat.Height.grow su L s from Real.rpow_le_rpow_of_exponent_le hβ (by norm_num)) hp p.weight ht hZ hb u k hu.le p.mild; let v:=ware Q u (spiceR L s) ξ.rootHit (1/2) j k; let b i:=major Y G' ξ (i:Y.Bright).val (spiceR L s)*(dime j*W i)
    have hz i : 0 ≤ W i:=mul_nonneg (mul_nonneg hu.le (prod_nonneg fun i _=> tagPos Y Ξ ht _ _ i)) (pow_nonneg (add_nonneg zero_le_one (worthG Y _).2) _)
    have he' i: 0 ≤ b i:=mul_nonneg (zero_le_one.trans (majorPos Y G' ξ i.val p.weight hp hb.marked)) (mul_nonneg (by unfold dime; positivity) (hz i))
    have hv:0 < v:=by unfold v ware; have hm:= hu; have hz:0 < ξ.rootHit:=hb.γ; have hx:0< spiceR L s:=zero_lt_one.trans_le p.weight; have hF:=Q.usable; unfold dime polyPrice; positivity
    have hY: Ready Y.lightF (radiusB s) b (a+1) v 1 (1/2) :=by
       refine ⟨hv,one_pos,p.motz,by norm_num,he',fun i=>?_⟩
       apply budget_mono (hB i) (fun i=> ?_) (fun i=>?_)
       · split; exact mul_nonneg (he' _) (Real.exp_pos _).le; exact le_rfl
       split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right p.has (Nat.cast_nonneg _))) (he' _); exact le_rfl
    exact ⟨pastry Y _ W hp hz _ hb.marked p.weight p.span hY p.speed₂,debt Y G' hY p.span hp p.weight hb.marked hz l _ _ (fun i hi=>historic Y G' ξ X y (fun i h=> p.wave.trans (he i h)) (fun i h=> p.width.trans (hx i h)) hp p.weight p.game p.length hb.marked i hi) p.speed⟩ -- rewrite
end YM.ConnectedActivityE6.Blaze.King
