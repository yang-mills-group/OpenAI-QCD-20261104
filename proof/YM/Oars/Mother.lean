import YM.Oars.Summer
import YM.Oars.Pigments
import YM.Oars.Prelude
/-!
 # Local booths in actual clock line.Earn.Frame scaling Verity
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Sail
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
variable {c f L:Side}{β τ :ℝ}
variable {I E J G Gv:Type}[Fintype I][Fintype J]
open Sail Kites Plate.Card QCD.Calm Acre Rails.Reference Rails
open QCD.Acre.Rails.Bank QCD.Acre.Rails.Bank.Hike Stags
open MassiveQCD.Twist
local notation "iC"=> (42/256:ℝ)
local notation "i₀"=> (46/256:ℝ)
local notation "k₀"=> (1/256:ℝ)
local notation "W₀"=> (1/8:ℝ)
local notation "Ω₀"=> (3/16+1:ℝ)
local notation "G!"=> (40/256:ℝ)
variable (L:Side)(θ p u r:ℝ)(k q K η Gn :ℕ)
-- Timing.Shedule using v in monotone transformations pAr.
local notation "V0"=>roomAt L θ
noncomputable def packRate (L:Side)(F C:ℕ)(A B a h:ℝ): Prop:=True -- remove
-- rates windows
lemma slotR : Rate su L (-1) V0:=(by unfold roomAt; simpa only [zero_add] using ((Jets.Touch.Seat.keeps (L:=L) (a:= -θ/16)).ruled.mul (Jets.Touch.chip_rate L)))
lemma inverseSlot : Rate su L 1 (fun x=>(V0 x)⁻¹):=by
   unfold roomAt; simp_rw [mul_inv_rev]; exact Rate.mul (top_chip L) (skin_i L _|>.ruled) |>.weaken (by norm_num)
lemma shuttle : ∀ᶠ x in atTop, 0 < V0 x∧ V0 x ≤ 4*V0 (run L x) ∧ V0 (run L x) ≤ 4*V0 x:=by
    let F:=fan L (-θ/16); filter_upwards [(Work.E09.betaF_growth su L).eventually (event_chip L 1),event_chip L 1, Finch.dim L (-θ/16), (Finch.rol L (-θ/16)).eventually (le_mem_nhds (show (1/2:ℝ)<1 by norm_num)), Finch.pegL L -- syntax wrong
       ] with x hx hy hg hp h
    unfold roomAt; have hu:0<F x:=fan_pos ..; have hv: F x ≤ 2*F (run L x):=by
        have h:= (le_div_iff₀ hu).1 (show 1/2 ≤ F (run L x)/F x from hp); linarith only [h]
    refine ⟨mul_pos hu hy.2.1, (mul_le_mul hv h.1 hy.2.1.le (hu.le.trans hv)).trans_eq (by change 2*F _*(2*_)=4*(F _*_); ring), (mul_le_mul hg h.2 hx.2.1.le (by positivity [hu])).trans_eq (by ring)⟩
lemma subsid (M n:ℕ):∀ᶠ x in atTop,tallyUp L k M n x ≤ V0 x:=by
   let u:= fun x:ℝ=> Real.exp (-(W₀/128)*radiusB x); let f :=fun i:ℝ=> Girdle.tariff k 2 M n*(u i*(Reel.voiceE 2 W₀ (radiusB i)*King.flowM L i)); have ht:Rate su L (-2) f:= (( ((Calm.expHigh (L:=L) (t:=-2) (by norm_num : 0 < W₀/128)).mul ((Reel.for_voices L 2 W₀).mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power))).mul_left _).weaken (by linarith))
   have he:= ((ht.mul (inverseSlot L θ)).below (by norm_num) (1/4:ℝ) (by norm_num))
   filter_upwards [(Work.E09.betaF_growth su L).eventually he,(Work.E09.betaF_growth su L).eventually (shuttle L θ), shuttle L θ] with x hx hX hY; unfold tallyUp; change f (run L x) ≤ _; let u:=run L x; apply le_trans ((div_le_iff₀ hX.1).1 (_ : f u/V0 u≤1/4)) ; · linarith only [hY.2.2]; -- cont edit
   rw [div_eq_mul_inv]; exact (le_abs_self _).trans hx
-- Arch decays **relative to Nominal** pre radius. output cost off-weight any.A 
lemma reliefStage (Q i kq n Dx nL:ℕ)(M:ℝ)(he:0<M)(hv:0<θ) : ∀ᶠ x in atTop, ArchC L θ Q i kq n Dx nL x ≤ M*V0 x:=by
    let z:=ArchC L θ Q i kq n Dx nL; let c:= -θ/16; have ht:= prepSignal L Q i kq n Dx nL θ; let f:=fun x=> z x*(Jets.Touch.chip L x)⁻¹; let V:=fan L c
    filter_upwards [((ht.ponies (skin_i L c)).shrinks (by unfold c; linarith) he),event_chip L θ] with x hx hY; have h: f x*(V x)⁻¹ ≤ M:= (le_abs_self _).trans hx
    have h: f x ≤ M*V x := (div_le_iff₀ (fan_pos ..)).1 (by rw [div_eq_mul_inv]; exact h)
    unfold roomAt; rw [← mul_assoc M]; exact (div_le_iff₀ hY.2.1).1 (by rw [div_eq_mul_inv]; exact h)
noncomputable abbrev pTag (i M n:ℕ)(x:ℝ):= FeeE i M n x * King.flowM L x
lemma loot (B M A N:ℕ) (z u:ℝ)(ht:0<θ)(hx:0 ≤z)(hz:0 ≤ u): ∀ᶠ x in atTop, bonus B (radiusB x) k₀ * (pTag L M A N x*z+u* V0 x) ≤1 :=by
    let f:= fun x:ℝ=> pTag L M A N x*z; let e:=fun x:ℝ=>u*V0 x; have hp : Rate su L (-(3/10)) f:=(by unfold f pTag FeeE; simpa only [zero_add] using (((Reel.for_voices L 2 W₀).mul_left _).mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power)).mul_right z )
    exact (((bumped L B k₀).ruled.mul (hp.add (((slotR L θ).mul_left u).weaken (by norm_num)))).below (by norm_num) 1 zero_lt_one).mono fun i hi=> (le_abs_self _).trans hi -- P.W.Include input W.Prop.He.
end YM.MassiveQCD.Sample.Sail
#print axioms YM.MassiveQCD.Sample.Sail.loot
