import YM.Profiles.Uranus
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace GreenCap.Works
open Massive.Poised.Plans.Stamp
variable (L:Side) {U:Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U) (r d₀ M:ℕ)(θ T:ℝ)
local notation "z"=> taxK L
open Sail Relight QCD.Ruby
structure Pours (x:ℝ) : Prop where
   shape : r+1 ≤ radiusB (run L x)
   fans : 1 ≤ fan L θ x
   high : 0 ≤ roomAt L θ x
   motion:StackK (radiusB (run L x)) (taxK L x 4) (taxK L x 2) (3/16) (42/256) (3/16+1) 1
   cost : ∃ A K C:ℝ,0<A ∧0≤ K∧0≤ C ∧ K*Real.exp ((4:ℝ)*81)≤ C∧ Stags.bonus M (radiusB (run L x)) 1*C≤1 ∧ (∀ (c:Side)(V:BudgetPoint)(h:V.threshold=Pressure.fiery su x L)(b:Cover)(y:Label d₀)(U:Grid c),wealth y.val V.threshold (fan L θ x) ≤ A⁻¹*T → Creek.load (fun _=>fan L θ x) (Orientation.graphs d₀ B b y U)≤ K) ∧
      ∀ (c:Side)(I E:Type)[Fintype I][Countable E](p:I→Site c)(q:I→Bool)(F: Patron.Rail c (ample 6 I) E)(S:Set (Finset I))(v:BudgetPoint),v.B=radiusB (run L x)→ Fires p M → (∀ i∈S, Spaced p i v.B)→ Wage.Tip 6 p q F v (fan L θ x) (42/256) (taxK L x 2) → (Film.publication 6 p q F S (fan L θ x)).Stock 6 v.B (taxK L x 1) (40/256) (fan L θ x) ((taxK L x ((2-1)/2))⁻¹) (fun _=>A) -- `A` booster full.ST
open Stair -- actual namespace.
lemma ballast (h:0<θ): ∃ f:ℝ→ℝ, ∃ a:ℝ,Rate su L a f ∧∀ᶠ x in atTop,0 ≤ f x∧∀ (c:Side)(Y:BudgetPoint)(he:Y.threshold=Pressure.fiery su x L)(b:Cover)(y:Label d₀) (U:Grid c), Creek.load (fun _=>fan L θ x) (Orientation.graphs d₀ B b y U) ≤ f x * wealth y.val Y.threshold (fan L θ x):=by
    obtain ⟨C,hC,H⟩:= breathM d₀
    obtain ⟨a,ha,H'⟩:= riches (d:=d₀) L
    let g:= sheds B d₀; let n:=nJ B d₀; let f:=fun i:ℝ =>fan L θ i^ n *‖g‖
    have hh : Rate su L 0 f:=by simpa only [zero_mul] using (((Jets.Touch.Seat.ruled (L:=L) (f:=fan L θ) Jets.Touch.Seat.keeps).pow n).mul_right ‖g‖) -- L
    let d (i:ℝ):= f i*C* feeS d₀ (Pressure.fiery su i L)⁻¹ -- signature infer syntax
    have hd:Rate su L a d:=(by simpa only [zero_add] using ((hh.mul_right C).mul H'))
    have hb': ∀ᶠ i:ℝ in atTop, 0< Pressure.fiery su i L:= by
       filter_upwards [Delay.shift_pos su L] with i hi; exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 hi)) (Delay.monitor_pos ..)
    refine ⟨d,a,hd,?_⟩; filter_upwards [Kites.framesC L θ h,hb'] with x hT hH; let v:=fan L θ x; have hv := hT.2.1; have hF :0 ≤ f x:= mul_nonneg (pow_nonneg (fan_pos ..).le _) g.opNorm_nonneg; have hu:= zero_le_one.trans hC
    refine ⟨ (by unfold d; exact mul_nonneg (mul_nonneg hF hu) (zero_le_one.trans (control (inv_pos.2 hH)))),fun c P hp b y V=>?_⟩; apply le_trans (metricS b B y V hv); unfold d; rw [← hp]; exact (mul_le_mul_of_nonneg_left ((H _).trans (mul_le_mul_of_nonneg_left (scopeW P y hv) hu)) hF).trans_eq (by unfold f g n; ring) -- names
lemma pourAt (hθ:0 < θ)(hT:0≤ T):∀ᶠ y in atTop, Pours L B r d₀ M θ T y:=by
    obtain ⟨f,a,H,h⟩:= ballast L B d₀ θ hθ
    obtain ⟨n,hn⟩:= exists_nat_gt a; let g:=fun i:ℝ=> i^n
    let F:= fun x:ℝ=> g (run L x)
    have hh : Rate su L (-(n:ℝ)) (fun x:ℝ=>(F x)⁻¹):= Rate.power.congr ((Delay.shift_pos su L).mono fun x hx=>by dsimp only [F,g]; rw [Real.rpow_neg hx.le,Real.rpow_natCast])
    have hA: Rate su L 1 (fun x=>x):=by apply Rate.compare Rate.hat; filter_upwards [eventually_ge_atTop (0:ℝ),Delay.shift_pos su L] with x hx hX; simpa only [abs_of_nonneg hx,abs_of_pos hX] using (show x ≤ betaF su x L from le_add_of_nonneg_right (Work.E04.shift_nonneg su L))
    let a_χ:= (1/256:ℝ); have hp:= Film.Surplus.grantK L (1/256) 2 1 M (by norm_num) (by norm_num) (by norm_num) g (hA.pow n) (40/256)
    let K:= fun x:ℝ=>f x*((F x)⁻¹*T); let C:=fun x=> K x* Real.exp ((4:ℝ)*81)
    have hC: Rate su L (a+ - (n:ℝ)) C:= (H.mul (hh.mul_right T)).mul_right _
    filter_upwards [h,(Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop (r+1),Kites.framesC L θ hθ, shuttle L θ,Sail.pulseMotion L 2 4 (42/256) (6/256) (by norm_num) (by norm_num) (by norm_num) (by norm_num),hp, Delay.shift_pos su L, (((Sail.bumpedH L M 1).ruled.mul hC).below (by linarith) 1 zero_lt_one)] with x H' h1 h2 h3 h4 h5 h6 h7; have hF:0 < F x:=pow_pos h6 _; have hD:0≤ K x:=mul_nonneg H'.1 (mul_nonneg (inv_pos.mpr hF).le hT); have hhV : 1 ≤fan L θ x:= h2.2.1
    refine ⟨h1,hhV,h3.1.le,?_,F x,K x,C x,hF,hD,mul_nonneg hD (Real.exp_nonneg _),le_rfl,(le_abs_self _).trans h7,fun c V hp b y U ht=> (H'.2 c V hp b y U).trans (mul_le_mul_of_nonneg_left ht H'.1),?_⟩
    · convert h4 using 1 <;> first| rfl | norm_num
    intro c I E _ _ p q F' S u he hx hΓ hY; rw [he]; apply h5 (fan L θ x) 6 c _ _ _ _ _ _ u.threshold _ hx (he ▸ hΓ) _ hY.fits (fun i=> le_rfl) (zero_lt_one.trans_le hhV); rw [show (40/256+2*(1/256):ℝ)=42/256 from by norm_num,←he]; exact hY.tilt
end GreenCap.Works
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.GreenCap.Works.pourAt
