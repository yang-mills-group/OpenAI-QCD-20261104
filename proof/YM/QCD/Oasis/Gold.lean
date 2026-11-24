import YM.QCD.Oasis.Buy
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Jets.Touch
variable {L:Side}{c₀:ℝ}{a b u v t σ C m l:ℝ}{f h g p:ℝ→ℝ}
def Tame (L:Side)(s:ℝ→ℝ):Prop:= ∀ a:ℝ, Rate su L a s
lemma swallow (h:Tame L f) (hp:Rate su L b g) : Tame L (fun i=>f i * g i):=by intro a; exact ((h (a-b)).mul hp).weaken (by linarith)
lemma trimB (h : a < b)(hx:Seat L a f)(hf:Seat L b g)(he:0≤b): Seat L b fun x=> f x+g x:= (hx.above h.le).comb hf
lemma snare (k: ℕ)(h:Seat L 0 f)(hp:Seat L a g)(he:0≤a) : Seat L (a*(2+k)) (fun i=>Lantern.fee k (f i) (g i)):=by
    let b i:=spanE (f i) (g i)
    have ht: Seat L a b:=by
      let h':= (((Seat.numbers 1).comb h).above he).comb hp; exact h'.comb h'
    let g' i:= clump k (b i) (f i); have hf: Seat L (a*k) g':=by
       unfold g' clump; simp only [mul_one]; exact ((h.timesL _).ponies (((Seat.numbers _ |>.above he).comb ((Seat.numbers _|>.above he).comb ht)).powered k)).above (by linarith) -- check
    let u i:=acrossE k (f i) (g i); have hu: Seat L (a*(2+k)) u:= ((hp.ponies (hp.ponies hf)).above (by linarith)) -- notation
    exact (((h.comb h).above (by positivity)).comb (hu.comb hu)).comb ((hf.comb hf).above (by nlinarith))
lemma lump (k:ℕ)(C:ℝ)(hx:0≤a)(h:Seat L a f): Seat L (a*k) (fun x=>clump k (f x) C):=by
    unfold clump; simp only [mul_one]; exact Seat.timesL ((((Seat.numbers _).above hx).comb (((Seat.numbers _).above hx).comb h)).powered k) _ -- maybe span
noncomputable abbrev heron (k :ℕ)(b a:ℝ):= let i:ℝ:= k; a+ b*(2+i)*i
def amass (k:ℕ)(b a:ℝ):= heron (k+2) b a+b*(2+(k+2))*(k+2)*k
lemma chargeX (hv : Seat L a f)(hp:Seat L a g)(hu:Seat L 0 p)(hx:Seat L b h)(he:0 ≤ a)(ht:0≤b) (j :ℕ)(A:ℝ): Seat L (heron j b a) (fun x=> mast (f x) (g x) (p x) (h x) A j):=by
    let u x:= Lantern.fee j (p x) (h x); have hh:= lump j A (by positivity : 0≤b*(2+j)) (snare j hu hx ht)
    have hz: a ≤ heron j b a:=le_add_of_nonneg_right (by positivity)
    apply Seat.comb (hp.above hz); apply Seat.times; exact (((hh.comb ((Seat.numbers _).above (by positivity))).ponies (hp.comb hv)).above (by unfold heron; dsimp only; linarith))
lemma chargeY (hv : Seat L a f)(hp:Seat L a g)(hu:Seat L 0 p)(hx:Seat L b h)(he:0 ≤ a)(ht:0≤b) (j :ℕ)(A I:ℝ): Seat L (amass j b a) (fun x=> ΨCost j (p x) (h x) I A (f x) (g x)):=by
    let k:=j+2; have hh:= lump k A (by positivity : 0≤b*(2+k)) (snare k hu hx ht)
    have he':= (lump j I (by positivity) hh).ponies (chargeX hv hp hu hx he ht k A)
    apply Seat.times; refine he'.above ?_; unfold amass k; push_cast; linarith -- parentheses check
lemma narrowedP (r s:ℝ)(h:0<r)(hx:0<s)(hv:f=fun x=> -r*fan L s x): Tame L (fun x=> Real.exp (f x)):=by subst f; exact fun i=> Rate.monitor_cutoff h hx
lemma joyP (h : Seat L a f)(he:0 < C)(hx:0<b)(hp:a<b): Tame L fun x=> Real.exp (-C*fan L b x)*Real.exp (f x):=by
    simp only [← Real.exp_add]; intro i; apply (narrowedP (L:=L) (C/2) b (half_pos he) hx rfl i).compare; filter_upwards [(h.ponies (skin_i L b)).shrinks (by linarith) (half_pos he)] with x h
    have hp:0<fan L b x:= fan_pos ..; have he:= (le_abs_self (f x*(fan L b x)⁻¹)).trans h; rw [← div_eq_mul_inv] at he; simp only [abs_of_pos (Real.exp_pos _),Real.exp_le_exp]; linarith [(div_le_iff₀ hp).1 he]
def arcT (L:Side)(a x:ℝ):= Real.exp (-1*fan L a x)
lemma blossom (h : 0<b)(he:b<1)(hx:Bolt su L g)(hf:0<c₀) : ∀ᶠ x in atTop, ∀ (ι:Type)[Fintype ι][DecidableEq ι](M:Matrix ι ι ℝ), 1 ≤ g x → (Fintype.card ι:ℝ)≤g x → M.PosDef → (∀ y:ι→ℝ,dotProduct y (M *ᵥ y)≤ c₀ * dotProduct y y) → (sweep M).real (closedBall 0 (fan L b x))ᶜ ≤ arcT L b x :=by
    -- pay > b exp. band
    let c:=c₀; let v:=3*b/4; have hv:0<v:=by unfold v; linarith
    let r:= b-v; have hr:0<r:=by unfold r v; linarith
    have hh x : (fan L v x)^2= fan L (v*2) x:=by unfold fan; rw [Real.rpow_mul (Delay.monitor_pos ..).le, Real.rpow_two]
    let u x := fan L v x; let pz x:=u x/c; let t:= 1/(2*c); have ht : 0<t:=by unfold t c; positivity
    have hz x: -(pz x)*u x+c*pz x^2/2=- t*fan L (v*2) x:=by unfold u pz; rw [←hh]; unfold t u; field_simp <;> ring
    have hb' : 0< v*2 :=by positivity
    have hE := swallow (joyP (f:=fun i=> fan L b i) Seat.keeps ht hb' (show b<v*2 from by unfold v; linarith)) (hx.uses.mul_right 2)
    filter_upwards [hx.listens hr,(hE (-1)).below (by norm_num) 1 zero_lt_one] with x hx hy ι _ _ W h hκ hs he
    rw [measureReal_compl measurableSet_closedBall,probReal_univ]; have hu:0<u x:=fan_pos ..
    refine (Lantern.impact W hs hu.le (show 0≤pz x from (div_pos hu hf).le) he hκ h ?_).trans ?_
    · apply (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) hu.le).trans; have heq:r+v=b:=by unfold r; ring
      exact ((Real.rpow_add (Delay.monitor_pos su L x) r v).symm.trans (congr_arg _ heq)).le
    have hh:= (le_abs_self (Real.exp _ * Real.exp _ *(g x*2))).trans hy; unfold arcT; rw [hz]; rw [neg_mul (1:ℝ),one_mul, Real.exp_neg, ←one_div, le_div_iff₀ (Real.exp_pos _)]  -- no
    linarith
end YM.QCD.Oasis
