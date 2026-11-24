import YM.QCD.Tax.Down
/-! # post clock. -/
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
open QCD.Jets.Touch
lemma bootM (L:Side)(θ:ℝ)(he:0<θ): Rate su L (-1) (bootstrut L θ) ∧ ∀ᶠ x in atTop, 0<bootstrut L θ x :=by
    have he' := Seat.shrinks (f:=fan L (-θ)) Seat.keeps (by linarith) (show 0<(1/2:ℝ) by norm_num)
    constructor
    · have hf:Rate su L 0 (fun i => (1-fan L (-θ) i)⁻¹):=by
         apply Rate.compare (Rate.const 2); filter_upwards [he'] with x hx
         have hg:fan L (-θ) x ≤1/2:=(le_abs_self _).trans hx; have hp: 1/2 ≤1-fan L (-θ) x:=by linarith
         have ht:0 < (1/2:ℝ):=by norm_num
         exact (abs_of_pos (inv_pos.mpr (ht.trans_le hp))).trans_le ((inv_anti₀ ht hp).trans (by norm_num))
      exact (((cash_h L θ).mul ((Seat.ruled (f:=fan L (-θ-θ/2)) Seat.keeps).mul hf)).weaken (by norm_num))
    filter_upwards [event_chip L θ,he'] with x hg hX; exact mul_pos (inv_pos.mpr (by have h:=hg.2.2.2; linarith)) (mul_pos (fan_pos ..) (inv_pos.mpr (by linarith [(le_abs_self _).trans hX])))
lemma deltaEra (L:Side)(θ:ℝ)(he:0<θ):Rate su L (-(3/8)) (δCharge L θ) ∧ ∀ᶠ x in atTop,0<δCharge L θ x:=by
   obtain ⟨h,H⟩:= bootM L θ he; refine ⟨Rate.add ((Rate.power.mul h).weaken (by norm_num)) ((Rate.power.mul_left 2).add (Rate.power.mul_left 2)),?_⟩
   filter_upwards [H,Delay.shift_pos su L] with x hx hv; unfold δCharge; positivity
-- output τ>0 donations. powers strictly between 3*-. threshold. show p roots all smaller.
def spiceR (L: Side)(x:ℝ):ℝ:= betaF su x L^(7/20:ℝ)
noncomputable def jelly (h:Side)(x:ℝ):= betaF su x h ^ (-1 -1/40:ℝ)
noncomputable def flowM (h:Side)(x:ℝ):= betaF su x h ^ (-(3/10):ℝ)
structure Bank (b:Costs)(p:ℕ)(Q:Target su P)(s Qx:ℝ)(L:Side)(j l k:ℕ)(a:ℝ) : Prop where
 hood: b.Buy L Q.halo p
 weight:1 ≤ spiceR L s
 width:spiceR L s ≤ betaF su s L^(3/5:ℝ)
 game : spiceR L s^3 ≤ Real.exp b.markSeed
 length:spiceR L s^3 ≤ Real.exp (Q.ε*till s)
 wave:spiceR L s^3 ≤ betaF su s L^2
 mild : degreePrice p (spiceR L s*b.rootHit) Q.δ ≤1/2
 motz:degreePrice p (ware Q Qx (spiceR L s) b.rootHit (1/2) j l) 1 ≤1/2
 speed : smiler k p *(ware Q Qx (spiceR L s) b.rootHit (1/2) j l*(1-1/2)⁻¹) ≤ jelly L s*spiceR L s^3
 speed₂ : smiler k p *(ware Q Qx (spiceR L s) b.rootHit (1/2) j l*(1-1/2)⁻¹) ≤ flowM L s *spiceR L s
 span:0 ≤ a
 has: a+1+1 ≤ Q.exp
lemma era_mark (K:ℝ → ℝ)(μ q:ℝ)(hm:0<μ)(h:Rate su L a K)(b:ℝ):∀ᶠ x in atTop, K x≤ Real.exp (Delay.hatWin su L (μ/2) (1/2) x)∧∀ (i:ℝ),i≥ μ → K x≤ Real.exp (i * (till x:ℕ)):=by
    let η:= μ/4
    let M x:= Real.exp (-Delay.hatWin su L (μ/2) (1/2) x); let T (x:ℝ):= Real.exp (-(μ * till x))
    have hp:0<η:=by unfold η; positivity
    have hv : Rate su L (-a-1) M:=by
       apply (Rate.monitor_cutoff (G:=su) (L:=L) hp (by norm_num : (0:ℝ)<2)).congr; unfold M; refine Eventually.of_forall (fun i=>?_); unfold Delay.hatWin η; simp_rw [Real.rpow_two]; ring_nf
    have hf:Rate su L (-a-1) T := Rate.congr (Rate.cutoff hm) (Eventually.of_forall fun i=> by unfold T; congr 1; ring)
    filter_upwards [ (h.mul hv).below (by linarith) 1 one_pos,(h.mul hf).below (by linarith) 1 one_pos] with x hx ht
    have hp (a:ℝ)(h: K x*Real.exp (-a) ≤1): K x≤ Real.exp a:=by rw [Real.exp_neg,← div_eq_mul_inv] at h; exact (div_le_one (Real.exp_pos _)).1 h
    exact ⟨hp _ ((le_abs_self _).trans hx), fun i hi=>(hp _ ((le_abs_self _).trans ht)).trans (Real.exp_monotone (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (till x))))⟩
lemma given (L:Side)(Q:Target su P)(he:0 < μ)(hc:0≤ C)(x y:ℝ)(ht:0<x)(hz:Q.rate ≤ -(3/8:ℝ))(j k l:ℕ)(hq:0≤y)(hp:y+1+1≤ Q.exp)(T:ℝ→ℝ)(hT:Rate su L 0 T) :∀ᶠ p in atTop,
 let h:=δCharge L x p; let e:=shiftCost L p (romp L)
 ∀ β,betaF su p L/2 ≤ β → Bank (unitsP Q L μ β p C e h) (radiusB p) Q p (T p) L j k l y:=by
   obtain ⟨h,hG⟩:=deltaEra L x ht
   let F p:= unitsP Q L μ 0 p C (shiftCost L p (romp L)) (δCharge L x p)
   have hK: Rate su L (-(3/8)) (fun x=>(F x).rootHit):=by
      apply (((Q.rate_root (β:=0) (C:=C) L he).weaken hz).add h).congr
      exact Eventually.of_forall fun i=> by unfold F unitsP; simp only [Target.costs,Buy.quote]; ring
   let t':ℝ:=7/20+(-(3/8)); have h' : t'<0:=by norm_num [t']
   have hr : Rate su L t' (fun i=>spiceR L i*(F i).rootHit):= Rate.power.mul hK
   let M i:= ware Q (T i) (spiceR L i) (F i).rootHit (1/2) j k
   have hh:Rate su L t' M :=by
      unfold M ware; exact (((hT.mul_left _).mul ((hr.mul_right _).mul_left _)).weaken (by linarith))
   have hx (f : ℝ → ℝ)(h:Rate su L t' f)(v:ℝ): ∀ᶠ i in atTop, degreePrice (radiusB i) (f i) v ≤1/2:=by
      have he':Rate su L t' (fun x=> degreePrice (radiusB x) (f x) v):=by
         have hh:= Census.width_rate su L 1 0; simp only [one_mul,add_zero] at hh
         unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; exact ((((hh.mul h).mul_right _).mul_left 4).weaken (by linarith))
      exact (he'.below h' (1/2) (by norm_num)).mono fun i hi=> (le_abs_self _).trans hi
   let B i:= smiler l (radiusB i)*(M i*(1-1/2)⁻¹)
   have hV:Rate su L t' B:=by
      have hp : Rate su L 0 (fun x=> smiler l (radiusB x)):=by
         unfold smiler; exact (((((Rate.const 1).add (Rate.radius_price.mul_left 2)).add ((Rate.radius_price.mul_left 4).add (Rate.const 2))).pow l|>.mul_right _).weaken (by linarith))
      exact (hp.mul (hh.mul_right _)).weaken (by linarith)
   have hP : Rate su L (7/20*3) (fun u=>spiceR L u^3):= (Rate.pow Rate.power 3 : Rate su L _ _).weaken (by norm_num)
   let v:= Q.ε
   filter_upwards [hx _ hr Q.δ,hx _ hh 1, (Work.E09.betaF_growth su L).eventually_gt_atTop 1, hV (-1-1/40+7/20*3) (by norm_num [t']), hV (-(3/10)+7/20) (by norm_num [t']), subsidy Q L he hc one_pos (by norm_num : -(1/4:ℝ)<0), h (-(1/4)) (by norm_num),hG,taken L (romp L),era_mark _ _ 0 he hP 0,era_mark _ _ 0 Q.usable hP 0] with z hx hv hg h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
   intro g e β hβ
   have he:0< betaF su z L:=zero_lt_one.trans hg
   have hπ : betaF su z L ^ ((7/20:ℝ)*3)=spiceR L z^3:=by rw [Real.rpow_mul he.le]; norm_num [spiceR] -- ^3 v R.lean
   have ht (y:ℝ):(F z).rootHit=(unitsP Q L μ y z C e g).rootHit:=rfl
   refine ⟨h₃ _ _ _ hβ h₅.le ((le_abs_self _).trans h₄) (by rw [one_mul];exact h₆), Real.one_le_rpow hg.le (by norm_num), Real.rpow_le_rpow_of_exponent_le hg.le (by norm_num),h₇.1,h₈.2 _ le_rfl,?_ ,hx,hv,?_ ,?_,hq,hp⟩
   · rw [← hπ,← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hg.le (by norm_num)
   · rw [Real.rpow_add he,hπ] at h₁; exact (le_abs_self _).trans h₁
   rw [Real.rpow_add he] at h₂; exact (le_abs_self _).trans h₂
end YM.ConnectedActivityE6.Blaze.King
