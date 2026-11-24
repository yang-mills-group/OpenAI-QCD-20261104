import YM.QCD.Pearl.Survey
import YM.QCD.Casimir

/-!
# real determinant valuation, using true real link lines
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch Pine Stationary
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p:Site n} {a b c η : ℝ}{j:ℕ}
variable {G:I→Gleam}{U:J→Bloom 1}{V:D→Bloom 2}(C : su.Color){v:Train j} {P:Plan j}

def coast (p:Weath n)(z:ℂ):Weather n:= fun x=> z*(p x:ℂ)
def cosine (p:Site n)(i:Axis): Weath n:= fun x=>(flashT p i x).re
def sineP (p:Site n)(i:Axis): Weath n:= fun x=>(flashT p i x).im
lemma sea (i:Axis)(p:Site n): flashT p i = coast (cosine p i) 1 + Complex.I • coast (sineP p i) 1 ∧ flashT (-p) i=coast (cosine p i) 1 - Complex.I • coast (sineP p i) 1 := by
  have he: flashT p i=coast (cosine p i) 1+Complex.I • coast (sineP p i) 1:=by ext1 x; simp only [coast, Pi.add_apply,Pi.smul_apply,sineP,cosine,smul_eq_mul,one_mul]; rw [mul_comm,Complex.re_add_im];
  refine ⟨he,?_⟩; rw [show flashT (-p) i=star (flashT p i) from ?_, he,star_add,star_smul];
  · ext1 x; simp [coast, Complex.star_def,sub_eq_add_neg]
  funext x; unfold flashT; simp only [Pi.star_apply]; split <;> simp_all [fan_cell,Complex.star_def]
lemma coil {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]{F:E→ℂ} (h:AnalyticAt ℂ F 0)(A B:E):
    dig (A+Complex.I • B) (A-Complex.I • B) F 0=dig A A F 0 +dig B B F 0:=by
  have he := ContDiffAt.isSymmSndFDerivAt_of_omega h.contDiffAt
  rw [dig_two _ _ h,dig_two _ _ h,dig_two _ _ h]
  let T:= fderiv ℂ (fderiv ℂ F) 0
  have ht:T A B=T B A:= he .. -- inspect
  change T _ _= _; rw [map_sub, map_add]; simp only [map_smul,_root_.add_apply,_root_.smul_apply]; change T A A+_ - Complex.I • (T A B +_) = _; rw [ht]; change _= T A A+ T B B; simp only [smul_eq_mul]; linear_combination -T B B*Complex.I_mul_I

lemma dig1 {G:ℂ→ℂ} (h:AnalyticAt ℂ G 0): dig 1 1 G 0=iteratedFDeriv ℂ 2 G 0 ![1,1]:= by rw [dig_two _ _ h, iteratedFDeriv_two_apply]; rfl
-- return comparison with usual second derivative on real line
lemma alongR {M:Weather n→Sheet n} (x:Weath n) (hM : AnalyticAt ℂ M 0) (hp : IsUnit (M 0).det):
    deriv (deriv (fun t:ℝ=> Real.log ‖(M (coast x t)).det‖)) 0=(dig (coast x 1) (coast x 1) (actual M) 0).re:=by
  let L: ℂ→L[ℂ] Weather n:=ContinuousLinearMap.toSpanSingleton ℂ (coast x 1)
  have hv t:L t=coast x t:=by ext1 i; simp[L,coast]
  have h:= actualA hM hp
  rw [← hv 1, ← dig_manual _ L 1 1 h]
  let F:= actual M ∘ L
  have he:AnalyticAt ℂ F 0 := (show AnalyticAt ℂ (actual M) (L 0) from L.map_zero ▸ h).comp (L.analyticAt 0)
  let T:=fun t:ℝ=> Real.log ‖(M (coast x (t:ℂ))).det‖
  let Y:=fun t:ℝ=> (F (t:ℂ)).re
  let I:=fun t:ℝ=>Y t+Real.log ‖(M 0).det‖
  have hT: T=ᶠ[𝓝 0] I:=by
    let Z:= fun t:ℝ=>L (t:ℂ); have hz : Tendsto Z (𝓝 0) (𝓝 0):= by simpa only [Z,Complex.ofReal_zero,map_zero] using (show Continuous Z from L.continuous.comp Complex.continuous_ofReal).tendsto 0
    have ht:= hz.eventually (((hop_cont (n:=n)).continuous.continuousAt.comp hM.continuousAt).eventually_ne hp.ne_zero)
    filter_upwards [ht] with i hi
    dsimp only [I,Y,F,Function.comp_apply,T,actual]; rw [← hv]; change _ = (Complex.log _).re+_; rw [Complex.log_re, norm_mul,norm_inv, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.mpr hp.ne_zero)) (norm_ne_zero_iff.mpr (show (M (Z i)).det≠0 from hi)),Real.log_inv]; ring
  have h': deriv I=ᶠ[𝓝 0] fun t:ℝ=> (deriv F (t:ℂ)).re:=by
    have he': Tendsto (fun t:ℝ=> (t:ℂ)) (𝓝 0) (𝓝 0):=by simpa using Complex.continuous_ofReal.tendsto 0
    filter_upwards [he'.eventually he.eventually_analyticAt] with t ht; exact (ht.differentiableAt.hasDerivAt.real_of_complex.add_const (Real.log ‖(M 0).det‖)).deriv
  have hd:= (hT.deriv).trans h'; change deriv (deriv T) _= (dig 1 1 F 0).re; rw [hd.deriv_eq]
  rw [dig,dew_ℂ,one_smul, show dew 1 F=deriv F from funext fun x=>by rw [dew_ℂ,one_smul]]
  have hb : DifferentiableAt ℂ (deriv F) 0:= voiced (1:ℂ) he
  exact (show HasDerivAt (deriv F) _ (((0:ℝ):ℂ)) from (show ((0:ℝ):ℂ) =0 from rfl) ▸ hb.hasDerivAt).real_of_complex.deriv

def rectifyR (C:su.Color)(M:Run.St n)(x: Weath n):ℝ:= -deriv (deriv (fun t:ℝ=> Real.log ‖(M (bird C ∘ (t • x))).det‖)) 0
def priceR (C : su.Color)(M:Run.St n) : ℝ:= (rectifyR C M (cosine (step 0) 1)+rectifyR C M (sineP (step 0) 1))/(n.val^4*beamH n^2:ℝ)
def L₀ (P:Plan j)(v:Train j)(A:J→Bloom 1)(Z:D→Bloom 2)(n:Side)(x:Grid n):=wood P 0 v x+(∑' i,(A i).tonic 0 x)+(∑' i,(Z i).tonic 0 x)
lemma l₀_ext (h:Package η a b c P v G U V)(x: Weath n)(u:ℝ): L₀ P v U V n (bird C∘(u • x)) = extent C G U V n (coast x u):=by
  have he : coast x u=fun i=> (((u • x : Weath n) i:ℝ):ℂ):=by funext i; simp [coast]
  rw [he,extent,L₀]; unfold totals reachouts; simp_rw [silos,silted]; rw [(h.matchA ..).tsum_eq]
lemma pricing (h:Package η a b c P v G U V)(n:Side): priceR C (L₀ P v U V n)= antenna (extent C G U V n):=by
  let M:=extent C G U V n; have hx:= path_nonzero C h n
  have hr := aria C (packBill h) h.scale n
  have hm (x: Weath n):rectifyR C (L₀ P v U V n) x=- (dig (coast x 1) (coast x 1) (actual M) 0).re:=by unfold rectifyR; simp_rw [l₀_ext C h, alongR x hr hx]; rfl
  unfold priceR; rw [hm, hm]; unfold antenna testN polarization
  -- targeted rewrite in vectors (x might depend flash)
  congr 1; unfold M; nth_rw 1 [(show flashT (step 0:Site n) 1 =_ from (sea 1 (step 0:Site n)).1)]; rw [(sea 1 (step 0:Site n)).2, coil (actualA hr hx), Complex.neg_re, Complex.add_re]; ring
lemma blister (P:Plan j)(C:su.Color)(h:‖C‖=1)(a b:ℝ): ∃ η>0,∃ W:ℝ,∀ᶠ n:Side in atTop,∀ (J D:Type)(A:J→Bloom 1)(Z:D→Bloom 2)(v:Train j), Fractal A (4*η) a→Fractal Z (4*η) b →
    |priceR C (L₀ P v A Z n)-chargeF*Real.log n.val|≤W:=by
  obtain ⟨z,K,hp,hc,H⟩:= pays_all P
  let η:= z/4; have he:0<η:=by unfold η; positivity
  obtain ⟨W,F⟩:= docket C h P he K a b; refine ⟨η,he,W,?_⟩
  filter_upwards [F] with n hn J D A Z v hA hZ
  obtain ⟨I,G,h,hG⟩:=H v
  have hh:Package η K a b P v G A Z:=⟨he,(h.reduces (by positivity) (by dsimp [η]; linarith) le_rfl), hG,hA,hZ⟩
  rw [pricing C hh]; exact hn _ _ _ _ _ _ _ hh
lemma wilson (P:Plan j)(C:su.Color)(h:‖C‖=1):∃ W:ℝ,∀ᶠ n:Side in atTop, |priceR C (fun X:Grid n=>bareD 0 X 0)-chargeF*Real.log n.val| ≤ W:=by
  obtain ⟨η,hη,W,H⟩:=blister P C h 0 0 -- implicit types etc
  let A: Empty→Bloom 1:= Empty.elim; let Z: Empty→Bloom 2:= Empty.elim
  have hf (m:ℕ) (A:Empty→Bloom m): Fractal A (4*η) 0 := ⟨by positivity,fun i=> i.elim, Summable.of_finite,by simp⟩
  refine ⟨W,H.mono fun n hn=>?_⟩; have he := hn Empty Empty A Z (.top j) (hf 1 A) (hf 2 Z)
  rw [show (fun X:Grid n=> bareD 0 X 0)=L₀ P (.top j) A Z n from funext fun i=>by unfold L₀; simp[rose]]; exact he
end YM.QCD.Pearl
