import YM.Differ.Oort
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
-- product polynomial allowances.Launch.C costs from supplementary paper.Y.We frame.W.Count charges grant only paid.Numeric.
structure OperaBook (V:ℝ) (x:ℝ): Prop where
   fans : 1 ≤ fan L θ x
   holds : 0 < roomAt L θ x
   high : roomAt L θ x ≤ 1 -- to scale salary
   theater : (taxK L x ((2-1)/2))⁻¹ ≤ roomAt L θ x
   motion:StackK (radiusB (run L x)) (taxK L x 4) (taxK L x 2) (3/16) (42/256) (3/16+1) 1
   costs :∃ A C:ℝ,0 < A ∧ 0 ≤ C ∧ A⁻¹*V ≤ C∧ Stags.bonus M (radiusB (run L x)) 1*C≤1 ∧
      ∀ (c:Side)(I E:Type)[Fintype I][Countable E](p:I→Site c)(q:I→Bool)(F: Patron.Rail c (ample 6 I) E)(S:Set (Finset I))(v:BudgetPoint),v.B=radiusB (run L x)→ Fires p M → (∀ i∈S, Spaced p i v.B)→ Wage.Tip 6 p q F v (fan L θ x) (42/256) (taxK L x 2) → (Film.publication 6 p q F S (fan L θ x)).Stock 6 v.B (taxK L x 1) (40/256) (fan L θ x) ((taxK L x ((2-1)/2))⁻¹) (fun _=>A)
lemma burstCash (hθ:0 < θ)(V:ℝ→ℝ) (a:ℝ)(h:Rate su L a V) (hV:∀ᶠ x in atTop,0 ≤V x) :∀ᶠ y in atTop, OperaBook L M θ (V y) y:=by
    obtain ⟨n,hn⟩:= exists_nat_gt a; let g:=fun i:ℝ=> i^n
    let F:= fun x:ℝ=> g (run L x)
    have hh : Rate su L (-(n:ℝ)) (fun x:ℝ=>(F x)⁻¹):= Rate.power.congr ((Delay.shift_pos su L).mono fun x hx=>by dsimp only [F,g]; rw [Real.rpow_neg hx.le,Real.rpow_natCast])
    have hA: Rate su L 1 (fun x=>x):=by apply Rate.compare Rate.hat; filter_upwards [eventually_ge_atTop (0:ℝ),Delay.shift_pos su L] with x hx hX; simpa only [abs_of_nonneg hx,abs_of_pos hX] using (show x ≤ betaF su x L from le_add_of_nonneg_right (Work.E04.shift_nonneg su L))
    have hp:= Film.Surplus.grantK L (1/256) 2 1 M (by norm_num) (by norm_num) (by norm_num) g (hA.pow n) (40/256)
    let C:=fun x:ℝ=> (F x)⁻¹ *V x
    have hC: Rate su L (-(n:ℝ)+a) C:= hh.mul h
    let W':=fun x:ℝ=>(taxK L x ((2-1)/2))⁻¹; have hr:Rate su L (-2) W':= Touch.couplings L (by norm_num) -- syntax
    filter_upwards [hV,(slotR L θ).below (by norm_num) 1 zero_lt_one, ((hr.mul (inverseSlot L θ)).below (by norm_num) 1 zero_lt_one),Kites.framesC L θ hθ, shuttle L θ,Sail.pulseMotion L 2 4 (42/256) (6/256) (by norm_num) (by norm_num) (by norm_num) (by norm_num),hp, Delay.shift_pos su L, (((Sail.bumpedH L M 1).ruled.mul hC).below (by linarith) 1 zero_lt_one)] with x H' hV' hv h2 h3 h4 h5 h6 h7; have hF:0 < F x:=pow_pos h6 _; have hD :0 ≤ C x:=mul_nonneg (inv_pos.mpr hF).le H'; have hhV : 1 ≤fan L θ x:= h2.2.1
    refine ⟨hhV,h3.1,(le_abs_self _).trans hV', (div_le_one h3.1).1 (by rw [div_eq_mul_inv]; exact (le_abs_self _).trans hv : W' x/roomAt L θ x ≤1), ?_,F x,C x,hF,hD,le_rfl,(le_abs_self _).trans h7,?_⟩
    rotate_left -- holes order
    · intro c I E _ _ p q F' S u he hx hΓ hY; rw [he]; apply h5 (fan L θ x) 6 c _ _ _ _ _ _ u.threshold _ hx (he ▸ hΓ) _ hY.fits (fun i=> le_rfl) (zero_lt_one.trans_le hhV); rw [show (40/256+2*(1/256):ℝ)=42/256 from by norm_num,←he]; exact hY.tilt
    convert h4 using 1 <;> first| rfl | norm_num
end GreenCap.Works
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.GreenCap.Works.burstCash
