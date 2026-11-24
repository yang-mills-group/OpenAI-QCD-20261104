import YM.QCD.Calm.Haven
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Tables
/-! # Book pays un-Strut E before averaging. survive Ω before Calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Calm
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure Pressure.Testing RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth Beam
open GasP Ursell Greenbelt Patron Fount Oasis Stem Grove Slide Trio.Sharp Stew Creek
open Animals AnalyticBridge.VerifiedReset
variable {t a u D A θ h M h' ξ ζ w w' : ℝ}{I J V: Type}{m b s q N n :ℕ}{c C :Side}{Y: Stars→ Side}{B:BudgetPoint}
variable (L:Side)
open Time
-- counts at β scales.L ever increasing heights parametrized
variable {A' M' Q e N' :ℝ→ℝ}{x ξ H θ r :ℝ}{k:ℕ}
abbrev Signal (L:Side) (r:ℝ)(A:ℝ→ℝ):Prop:= Jets.Touch.Seat L r (fun x=> A x*(chip L x)⁻¹)
namespace Signal
omit L
variable {L:Side}
lemma seed (h:Rate su L t A')(he:t< -1): Signal L r A':= Jets.Touch.Seat.eliminated (h.mul (top_chip L)) (by linarith)
lemma palms (W:ℝ→ℝ)(he: Signal L r A')(hk: Signal L r W): Signal L r (fun x=>A' x + W x):= (Jets.Touch.Seat.comb he hk).equal (Eventually.of_forall fun i=> add_mul ..)
lemma dim (t:ℝ)(h: Signal L r A'): Signal L r (fun i=> t*A' i):= (Jets.Touch.Seat.timesL h t).equal (Eventually.of_forall fun i=> mul_assoc ..)
lemma pay (h : Signal L r A')(he: Jets.Touch.Seat L 0 M'): Signal L r (fun i=> M' i*A' i):=by
   unfold Signal; refine ((he.ponies h).above (by linarith)).equal (Eventually.of_forall fun i=> mul_assoc ..)
lemma scale (hp: Signal L r A')(hk: A'=ᶠ[atTop] M'): Signal L r M':= Jets.Touch.Seat.equal hp (hk.mono fun i hi=> by dsimp only; rw [hi])
lemma brassH : Signal L (r-1) (fun x=>Oasis.brass L x r):=by
    have hx: Seat L (-1) (fun i=> (pra L i)⁻¹):= by simpa only [fan, Real.rpow_one] using (skin_i L 1)
    have he: Seat L r (fan L r):=Seat.keeps
    apply ((he.ponies hx).above (le_of_eq (by ring))).equal; filter_upwards [Delay.shift_pos su L] with x hx
    unfold Oasis.brass Jets.Touch.chip; field_simp
lemma omenH (l:ℕ): Signal L (r-1) (fun x=> Coda.omen L x r l):=by
    let W:= fun x=>lull L x; have hh : Signal L (r-1) W:= seed Rate.power (by norm_num)
    have he: Signal L (r-1) (fun x=>1*betaF su x L^(-(23/20:ℝ))+dues L x+(W x+W x)):= palms _ (palms _ (seed (Rate.power.mul_left _) (by norm_num)) (seed (Fount.tunes L) (by norm_num))) (palms W hh hh)
    exact palms _ he (scale (M':=fun x=> Coda.feeD l (brass L x r)) (dim (Coda.feeD l 1) brassH) (Eventually.of_forall fun x=>by unfold Coda.feeD; ring))
lemma moneyP (hv:Signal L r A')(hx:r<0)(hz:0<x): ∀ᶠ i in atTop, A' i ≤ x * chip L i:=by
    filter_upwards [event_chip L 1,Seat.shrinks hv hx hz] with i hi he using (div_le_iff₀ hi.2.1).1 ((le_abs_self (A' i/chip L i)).trans (by rw [div_eq_mul_inv]; exact he))
end Signal
-- markets. valuations of 卷; B = Probe. q.E.
section axes
variable {U w p :ℝ→ℕ} {B₀:BudgetPoint}
variable (B:BudgetPoint)
abbrev Strip (L:Side)(w:ℝ→ℕ): Prop:= Seat L 0 (fun x=>(w x:ℝ))
lemma squares (h:Strip L w): Seat L 0 (fun x=> (ballCost (w x):ℝ)):=by
   unfold ballCost; push_cast; simpa only [zero_mul, two_mul] using (Seat.powered (Seat.comb (h.timesL 2) (Seat.numbers 1)) 4) -- h.times?
abbrev plusN (m:ℕ)(i:Stars):ℝ:= ((2:ℕ)*(m*roller i.val):ℕ)^4
lemma ticketsH (h:Strip L w)(i:Stars): Seat L 0 fun x=> plusN (w x) i:=by
    unfold plusN; push_cast; have he:= h; unfold Strip at he; refine Seat.above (Seat.powered ((he.times _).timesL 2) _) (by norm_num)
lemma seats (f:Stars→ℝ→ℝ)(hp:∀ i,Jets.Touch.Seat L a (f i)): Seat L a (fun x=> ∑ i:Stars,f i x) :=by
    let U:= fun s:Finset Stars=>fun x:ℝ=>∑ i∈s,f i x; have he X (h:X.Nonempty): Seat L a (U X):=by
       induction X using Finset.induction_on with
       | empty => simp at h
       | @insert i s hi ih=> by_cases hv:s.Nonempty; · exact ((hp i).comb (ih hv)).equal (Eventually.of_forall fun x=> Finset.sum_insert hi)
                             rw [Finset.not_nonempty_iff_eq_empty] at hv; subst s; exact (hp i).equal (Eventually.of_forall fun x=>by simp [U])
    exact he Finset.univ (Finset.univ_nonempty)
lemma glimmerH (i:Stars) : Seat L 0 (fun x=> |glimmer (w x) i|):=by
    apply Seat.compares (Seat.numbers |lampR i|); filter_upwards with x; unfold glimmer; rw [abs_abs,abs_abs,abs_mul]; by_cases he:w x=0; · simp [he]
    have ht:1≤w x:=Nat.one_le_iff_ne_zero.mpr he; refine mul_le_of_le_one_left (abs_nonneg _) ?_; rw [abs_inv,abs_of_nonneg (by positivity)]; apply inv_le_one_of_one_le₀; exact one_le_pow₀ (by have hh : (1:ℝ)≤w x:=Nat.one_le_cast.mpr ht; linarith)
lemma cashP (hw: Strip L w)(hu: Seat L r M') : Seat L r (fun x=> penS (w x) n (M' x) a):=by unfold penS; exact ((Seat.ponies (squares L hw) (hu.times _)).above (by linarith))
abbrev mesa (w:ℕ)(a:ℝ):=∑ i:Stars,|glimmer w i| * (plusN w i*(a+a))
lemma cashT (hw: Strip L w)(hu: Seat L r M') : Seat L r (fun x=> mesa (w x) (M' x)):=by
    unfold mesa; apply seats _ _; intro i; exact ((Seat.ponies (glimmerH L i) (Seat.ponies (ticketsH L hw i) (hu.comb hu))).above (by linarith))
lemma αpriced (w n:ℝ→ℕ)(hw: Strip L n)(q:Stars→ℝ→ℝ)(hs:∀ i,Signal L a (q i)): Signal L a fun x=> αbill B (w x) (n x) s (fun i=> q i x) h:=by
     have he :Seat L 0 (fun x=> Trio.tilt B (n x)):=by unfold Trio.tilt; refine ((Seat.timesL (Seat.powered (Seat.comb (Seat.numbers 1) hw) _) _).above (by norm_num)) -- pow cast
     let d i x:=|glimmer (w x) i| * (Trio.tilt B (n x)*charge_v B (q i x))*Real.exp (h*ballCost s)
     have hh i:Signal L a (d i):=by
         let k:= Real.exp (h*ballCost s); have ht:Signal L a (fun x=> k*(|glimmer (w x) i| * (Trio.tilt B (n x)*charge_v B (q i x)))):= Signal.dim _ (Signal.pay (Signal.pay (Signal.dim _ (Signal.palms (q i) (hs i) (hs i))) he) (glimmerH L i)); apply Signal.scale ht (Eventually.of_forall fun x=>mul_comm ..)
     unfold Signal; apply (seats L _ hh).equal; filter_upwards with x; unfold αbill Trio.oroH; rw [Finset.sum_mul,Finset.sum_mul]
lemma ψpriced (hw: Strip L w)(hp:Signal L a Q) :Signal L a fun x=> ψbill B (w x) n (Q x) t:=by
    have h₁ X (he:Seat L 0 X) (k:ℕ) :Seat L 0 (fun i=>(1+X i)^k):=(Seat.above (Seat.powered (Seat.comb (Seat.numbers 1) he) k) (by simp))
    have he:= hw; unfold Strip at he
    have hv:Seat L 0 (fun i=> (2*w i:ℕ)) := Seat.equal (he.timesL _) (Eventually.of_forall (fun i=> by push_cast; rfl))
    unfold ψbill riverW ticketR; let r:= Real.exp (t*ballCost n); let f x:=(1+w x:ℝ)^2*(((1+(w x:ℝ))^B.power)^B.order*(2^B.order*((1+(2*w x:ℕ):ℝ)^(B.power*B.order))*Q x)); -- verify ticketR no difference
    have hh : Seat L 0 (fun i=> ((1+(w i:ℝ))^B.power)^B.order):= ((h₁ _ he B.power).powered B.order).above (by simp)
    change Signal L a (fun x=>f x*r)
    apply Signal.scale (Signal.dim r (A':=f) (Signal.pay (Signal.pay (Signal.pay hp (Seat.timesL (h₁ _ hv _) _)) hh) (h₁ _ he _))) (Eventually.of_forall fun i=>mul_comm ..)
end axes
end YM.QCD.Calm
