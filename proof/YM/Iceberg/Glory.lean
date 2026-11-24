import YM.Iceberg.Tarp
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Iceberg
open Function Set Filter Analysis MeasureTheory Lattice
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair QCD QCD.Lat Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {ε β:ℝ}{φ:ℕ→ℕ}
variable (hp:C.Path β ε)(hP:P.System)(hHQ:K.Harmony P φ)(ht:Tendsto φ atTop atTop)(hf:Foil P K T)
variable (V:Face→K.W)(hv:Tense T V)(E:Canopy P φ K) (X:Lanterns T E)
open Lanterns Tawny Tawny.Cast Perla Carnal Drill
open Heron Work.A05
variable (A:Persona T V) {d:ℕ}(x:Points 2)(hx:x∈conf _)(g:Ortho.Skew){χ:E4→ℝ}(hw:Physics.Window x χ)(P' Q':Label d)
set_option quotPrecheck false
local notation "A₀"=> fun a b=>V (a,b)
local notation "SF" k:arg z:arg a:arg b:arg=> Storm E X x g (χ:=χ) P' Q' k z a b ((ouzel V E X A k).val (a,b))
noncomputable def senseW (k:ℕ)(z:E4)(a b:Axis):= Storm E X x g (χ:=χ) P' Q' k z a b ((ouzel V E X A k).val (a,b))
noncomputable def reed(k:ℕ) := (![cost T E X k P',cost T E X k Q'])
variable (J:Axle K (fun a b=>V (a,b))) (k:ℕ)(a b:Axis)
local notation "rP" k:arg=> (E.B k).r
local notation "SP" k:arg=> ((↑(peakΩ V A.tense E X k)⁻¹:ℂ))
local notation "az" k:arg=> Work.A01.orbital g (((rP k) • x) 0)
include hw hx
lemma sabre (z:E4): let r:= (E.B k).r; SF k z a b=(SP k) * (↑(r^4):ℂ)* termG (A₀) (stretch r χ) (az k) (r • x) (reed E X P' Q' k) a b (r • z):=by
      intro r; unfold Storm termG; let p' := reed E X P' Q' k; have hh:0<r:= (E.B k).realH; have ht:Work.A01.orbital g ((r • x) 0) (r • z) b= r * arm x g b z:= (arm_scaled hh x g b (r • z)).trans (by rw [stretch,inv_smul_smul₀ hh.ne']); rw[D_stretch hh hw.1,ht, ← Work.A05.smul_cons]; change (Work.A05.weight χ a (arm x g b) z) * headG p' _ (bullet _ _ _ _ _) = _; rw[spyR,map_smul,heads]; unfold mintS Work.A05.weight; push_cast; have hr:(r:ℂ)≠0:=(by exact_mod_cast hh.ne'); rw [smul_eq_mul]; unfold r at hr ⊢; unfold p'; field_simp <;> ring

lemma burial: -∑ a:Axis,∑ b:Axis, (∫ z:E4, SF k z a b)= (SP k)* (about (A₀) (stretch (rP k) χ) (M4.move g.val) ((rP k) • x) (reed E X P' Q' k)):=by
      let r:=(E.B k).r; have ht:0<r:= (E.B k).realH
      unfold about fluxG; rw[mul_neg,Finset.mul_sum]; apply congr_arg Neg.neg; apply Finset.sum_congr rfl; intro i _; rw[Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; simp_rw [fun z:E4=> sabre V E X A x hx g hw P' Q' k i j z]; rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume _ r (hR:=ht.le), show Module.finrank ℝ E4=4 from finrank_euclideanSpace_fin]; rw [Complex.real_smul]; push_cast; have h₀:(r:ℂ)≠0:=(by exact_mod_cast ht.ne'); unfold r at h₀ ⊢; rw [mul_assoc,mul_inv_cancel_left₀ (pow_ne_zero 4 h₀)]; rfl
variable (f:ℕ→ℕ)(h:Tendsto f atTop atTop)(R:RawTensor 1 8)
lemma gathers(L:E4→Label 8→ₗ[ℂ]ℂ)(h:∀ p,Integrable fun y:E4=>L y p):∃ p:Label 8→ₗ[ℂ]ℂ,∀ v,p v= ∫ y,L y v:=by
    refine ⟨{toFun:= fun v=>∫ y,L y v,map_add':=fun x y=>by simp_rw[_root_.map_add]; rw[integral_add (h x) (h y)], map_smul':=fun x y=>by simp_rw [_root_.map_smul,integral_smul]; rfl},fun _=>rfl⟩
include hHQ A h
lemma breathed (hr:∀ i:Face,Tendsto (fun k:ℕ=>(ouzel V E X A (f k)).val i) atTop (𝓝 (R.val i))): Tendsto (fun i=> SP (f i) * K.total 2 ((rP (f i)) • x) (![J.jet g (cost T E X (f i) P'),cost T E X (f i) Q'])) atTop (𝓝 (Heron.plumes x χ g R.val P'.val Q'.val)):=by
     have H(i j:Axis): Tendsto (fun k=> ∫ z:E4, SF (f k) z i j) atTop (𝓝 (∫ z:E4, ghostQ x g (χ:=χ) P' Q' z i j (R.val (i,j)))):=by
          choose p hp using fun k=> gathers x hx hw (fun y:E4=> Storm E X x g (χ:=χ) P' Q' k y i j) (fun z=>tarbS hHQ E X x hx g hw k P' Q' i j z); obtain ⟨q,hq⟩:= gathers x hx hw (fun y:E4=>ghostQ x g (χ:=χ) P' Q' y i j) (fun z=>tarbG x hx g hw P' Q' i j z)
          have h:= follows_L (fun k=>p (f k)) q (fun z=>by simp_rw [hp,hq]; exact (cup hHQ E X x hx g hw P' Q' i j z).comp h) _ _ (hr (i,j)); simp_rw [hp,hq] at h; exact h
     rw[aliveS x hx g hw P' Q']; apply (Tendsto.neg (tendsto_finsetSum Finset.univ fun a _=> tendsto_finsetSum Finset.univ (fun b _=>H a b))).congr'; refine Eventually.of_forall fun i=>?_; dsimp only[Pi.neg_apply]; rw[burial V E X A x hx g hw]; apply congr_arg; let k:=f i; let u:= cost T E X k P'; let v:= cost T E X k Q'; let r:= (E.B k).r; have hs:r • x∈ conf 2:= Compass.vital P φ K hHQ _ hx r (E.B k).realH; exact (J.relation g u 1 _ (stretch r χ) hs (window_stretch (E.B k).realH hw) (![v])).trans (heads ..)
end YM.Iceberg
#print axioms YM.Iceberg.breathed
