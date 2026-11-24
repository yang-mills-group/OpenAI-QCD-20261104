import YM.QCD.Port.Nook
/-! # financing exposure and selections. loss budget from inherited. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG ConnectedActivityE6 Push.AbsoluteSums Footprint Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {θ X Y :ℝ}(L:Side) {j k:ℕ}
def wear (L:Side)(x:ℝ):ℝ:= Real.exp (fan L (1/4) x)
lemma price_spit : Seat L 0 (fun x=> (spit (radiusB x):ℝ)):=by
   unfold spit; push_cast; let H:=Seat.radius (L:=L) |>.comb (Seat.numbers 1); simpa only [zero_mul] using (((H.comb H).comb (Seat.numbers (1:ℝ))).powered 4|>.timesL 2)
lemma purr :∀ᶠ x in atTop,1≤wear L x ∧ wear L x^spit (radiusB x)≤ taxK L x (1/8):=by
   have hg : Seat L (1/4) (fun x=>8*((spit (radiusB x):ℝ)*fan L (1/4) x)):= ((price_spit L |>.ponies (Seat.keeps)).timesL 8).above (by linarith)
   filter_upwards [hg (1/3) (by norm_num)] with x hx
   have hp := fan_pos L (1/4) x; refine ⟨Real.one_le_exp hp.le,?_⟩; unfold wear taxK; rw [← Real.exp_nat_mul,Real.exp_le_exp]; have hf: (8:ℝ)*(_*_) ≤fan L (1/3) x:= (le_abs_self _).trans hx; linarith
lemma crop_cost (F:ℕ) (t r p C :ℝ)(ht:0<θ)(hθ:θ<1/8) :∀ᶠ x in atTop,
  let h:=highW L C θ x
  Real.exp (max (F*AtomF.rays*2*t) (h^2*fingers F^2*(2*r))) ≤ wear L x*(Real.exp 1 * coreRate L x):=by
   have hy : Rate su L (-(2/5)) (coreRate L):=Rate.power
   have hh: Seat L (2*θ) (fun x=> 2*(highW L C θ x^2*fingers F^2*(2*r))) := by
     have hm := ((Seat.keeps (a:=θ) (L:=L)|>.timesL C).powered 2); exact (((hm.times _).times _).timesL _).above (by push_cast; linarith)
   have he : Rate su L (-1) (fun x=> Real.exp (-(1/2)*fan L (1/4) x)):= Rate.monitor_cutoff (by norm_num) (by norm_num)
   filter_upwards [hh (1/4) (by linarith), Seat.numbers (L:=L) (2*(F*AtomF.rays*2*t)) (1/4) (by norm_num), Delay.shift_pos su L, he (-(2/5)) (by norm_num)] with x hx hg h hp
   intro Z; let s:=fan L (1/4) x
   apply le_trans (b:=Real.exp (s/2)); rotate_right
   · have hi : Real.exp (-(1/2)*s) ≤ coreRate L x:= (le_abs_self _).trans hp
     have hu : wear L x=Real.exp s:=rfl
     rw [show s/2=s+ -(1/2)*s by ring,Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; exact hi.trans (le_mul_of_one_le_left ((Real.exp_pos _).le.trans hi) (Real.one_le_exp (by norm_num)))
   apply Real.exp_monotone; apply max_le; · have H : 2*(↑F*AtomF.rays*2*t)≤ s:= (le_abs_self _).trans hg; linarith
   have H : 2*(Z^2*fingers F^2*(2*r)) ≤ s:= (le_abs_self _).trans hx; linarith
lemma fitsB (F i B mL:ℕ)(P:Plan j)(N:Plan k)(a A b D K D' p θ r η ζ χ q h w K' X:ℝ)(hp:0< θ) (ht:θ <1/8)(hη:0<η)(hr:r>η)(hv:0<h)(hK:0<K): ∀ᶠ x in atTop,
   ∀ (f c: Side),2*(radiusB x+1)< f.val → ∀ (G:Flight j k)(H:f.val=c.val*G.L.val), G.L=L → reserve η ζ (conversion (sliceL G H) mL) χ → ∀ (M:Offer 1 a A)(T:Offer 2 b D)(s:ℝ), |s| ≤ wink L x→
    let E:= park G H P M T (haloK L x) s; let v:=coneK L h x; let t:=radiusB x; let H':= highW L K θ x; let q':=coreRate L x
    Species G H w q v r X B E→ ∀ W:ℕ→Atom su 2, ∀ Q: Swathe G H E W N w v r p D' i,
       RentP Q F t (fiery su x L) q' H' (wear L x) ∧ ∀ Y: Varn f c→Support c, (∀ i,Y i⊆enlargement (sliceL G H) mL t (payT (sliceL G H) t i))→
           Ac.Hit Y t (fun i=>Real.exp 1* shells Q F t H' q' i) ζ (betaF su x L ^ (-(3/8):ℝ)):=by
   filter_upwards [Delay.shift_pos su L,kentucky L hv,Work.E01.radiusB_tendsto.eventually_ge_atTop (i+1),purr L,crop_cost L F D' p K' K hp ht,frameTrust L P p D' K θ r 0 B F i a b A D w q X h N (hη.trans hr) hv hK, upward L F mL i ζ K r η θ p D' 0 χ hr] with x hx hv' hB hC hf hV Hx f c he G H hL hc M T s h E d t H' q' H₀ W Q
   have hp': 0< d:= mul_pos hv (pow_pos hv'.1 _); have he : 0 < t:=by change 0<radiusB x; omega
   have ht': 0<H':=mul_pos hK (fan_pos ..); have hq :0<q':= Real.rpow_pos_of_pos hx _
   let v:= shells Q F t H' q'; have hy j:0≤v j:=by unfold v shells; split; exact hq.le; exact grew Q j hp' ht'
   have hh:=sky_hits Q F t hr.le (show i≤ t by unfold t; omega) hη.le hq.le hp' ht'
   refine ⟨⟨hq,hp',ht',fun i=>(anchored_each _ _ _ hh hη.le hy i).trans Hx.1,hC.1,hf,?_,(hη.trans hr).le⟩,fun Y hk i=>?_⟩
   · apply hV f c ‹2*(radiusB x+1)< f.val› G H hL M T s h H₀ W Q
   have hE := heights_factor (Real.exp 1) _ _ _ (offers (orbitM (sliceL G H)) Y v (fun i=>cared ..) hk hy hh he (by omega) hc) (fun i=>rfl) (Real.exp_pos _).le
   have hZ:=hE i; apply Extra.Iteration.Cost.enlarge hZ; rw [show (sliceL G H).count=L from hL]; exact Hx.2
end YM.QCD.Port
