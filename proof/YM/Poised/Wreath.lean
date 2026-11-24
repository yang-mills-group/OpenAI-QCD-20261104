import YM.Poised.Crested
import YM.Poised.Garnish
/-!
# Accounts at all apertures. Covers actually Y^+ when using these. Bound with polynomial factor in length of input support (allows NOTshort in same currency).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y:ℝ}{H:Cash W τ μ L Q o C T (trimP T O δ β y)}{ι κ I E J D:Type}{N:ℕ}
variable {n p k d G l:ℕ} {a u r q v σ R z t w m γ α θ η :ℝ}{s:Side}
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
open Fountain Heir.Lute Extra.Iteration
-- full marker.E.Readable.R.B cost stencil for comparison (≤ R.limit or arbitrary Deck). Place in pipeline.
lemma tithing (C: Libretto su n)(E:Heir.Record)(L:Side)(p p' K0 d':ℕ)(A Yp:ℝ)(hYP:1≤Yp)(hA:0≤A)(r:ℕ)(f:ℝ→ℕ)(hx:Seat L 0 (fun i=>(f i:ℝ))):
 ∃ W N M:ℝ→ℝ, Seat L 0 M ∧ Seat L 0 N ∧ Seat L (-1) W ∧ ∀ᶠ x in atTop,∀ β:ℝ,betaF su x L/2 ≤β→ ∀ P R:BudgetPoint,R.B ≤ 2*radiusB x → R.power=p' → R.threshold=fiery su x L → P.threshold=temp x→ P.power=p →
    1 ≤ N x ∧ 0 < W x ∧ 0 ≤ M x ∧ W x ≤ 1 ∧ (canopyW su L p x ≤ N x * Heir.loom P (Heir.reach x) C.C) ∧ (C.M * (N x* loom P (Heir.reach x) C.C) ≤1) ∧ (1+patterns n)*(A*(C.M*(N x* Heir.loom P (Heir.reach x) C.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W x ∧ ∀ (s: Side)(S: Support s), coverNumber R.B S ≤ f x → Cub.opal C E P R L S r x (gStep β)*(N x)^n ≤ W x ∧ (AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads su R L S r x) 0 E.K (2*((n+1)+(n+1))) ≤ M x) ∧ ∀ b:Site s,b ∈ S →∀ i,Mom.needed S i→ Lyre.width R b i ≤1 :=by
   let N(x:ℝ):= 4*(1+(Malachite.radiusD x:ℝ))^p; have hN(i):1 ≤ N i:=one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))); -- replace
   have hS: Seat L 0 N :=by
      let A(x:ℝ):=(radiusB x:ℝ); have hs: Seat L 0 A:=Seat.radius
      have he:=hs.ponies ((hs.timesL 4).comb (Seat.numbers 2)); rw [add_zero] at he; have hp:=((Seat.numbers (L:=L) 1|>.comb (he.comb (hs.timesL 2))).powered p).timesL 4
      unfold N Malachite.radiusD; push_cast; simpa only [A,zero_mul] using hp
   obtain ⟨Q,hQ,hp⟩:=reachAff C L p
   let V(x:ℝ):= |C.M*(N x*Q x)|; let g:(ℝ):= (1+patterns n)*A*((Fintype.card Pipes.Shell:ℝ)*Yp); have hg:0 ≤ g:=by unfold g; positivity [patterns_nonneg n]
   let H:= (su.slopeConstant * Real.log (L.val:ℝ)); let P0(x:ℝ):= Heir.Lute.bulk (f x) r x; have hf: Seat L 0 P0:= by simpa only [zero_add] using! ((((Seat.numbers (↑r+48:ℝ)).ponies ((Seat.numbers (L:=L) 1).comb Seat.radius))).ponies ((Seat.numbers 1).comb hx))
   let M(x:ℝ):= Heir.Lute.guests su E.K (n+1) L * (P0 x)^(Heir.Lute.visitors (n+1))
   have hm:Seat L 0 M:=by simpa only [zero_mul] using! ((hf.powered (Heir.Lute.visitors (n+1))).timesL (Heir.Lute.guests su E.K (n+1) L))
   let Z':= Heir.Lute.boost C E L + (16 / E.ε); have hZ:0 < Z':=add_pos_of_nonneg_of_pos (boost_nn ..) (by have he:= E.guards; positivity)
   let z x:= fiery su x L+ 2*fan L (-1) x; let T x:= Z'*z x*P0 x ^ Heir.Lute.fuse n p
   let y x:= V x*g
   let W x:= (T x*(N x)^n + y x)
   have ht : Rate su L (-(1/2)) V:= Rate.compare ((hS.ruled.mul hQ).mul_left C.M |>.weaken (by linarith)) (Eventually.of_forall fun x=> (abs_abs _).le) -- replace
   have hz : Seat L (-1) z:= (Seat.eliminated Rate.flame (by norm_num)).comb (Seat.keeps.timesL 2)
   have hW:= ((hz.timesL Z').ponies (hf.powered (Heir.Lute.fuse n p))).ponies (hS.powered n); have hΩ:Seat L (-1) W:=by simp only [zero_mul,add_zero] at hW; exact hW.comb (Seat.eliminated (ht.mul_right _) (by norm_num))
   have hyO:=Rate.flame.mul ((hf.powered p').ruled)
   refine ⟨W,N,M,hm,hS,hΩ,?_⟩
   filter_upwards [Extra.Iteration.Rebuild.geometry H,Delay.shift_pos su L,ht.below (by norm_num) 1 (by norm_num),hyO.below (by norm_num) 1 one_pos,hΩ.shrinks (by norm_num) (by norm_num : (0:ℝ)<1)] with x hx hpβ hv hB ht β hβ P R hR he hz hP' hα
   have hp':R.threshold ≤ 2*P.threshold ∧ P.threshold ≤ 2*R.threshold:=by rw [hP',hz]; exact hx.2
   have hQ₀:=hp x P hα (hz ▸ hp'.2); let φ:= loom P (Heir.reach x) C.C; have hφ: 0≤ φ:=by unfold φ loom; positivity [P.threshold_pos,C.C_one]
   have hr : C.M*(N x* φ)≤ V x:=by apply le_trans _ (le_abs_self _); gcongr <;> positivity [C.matins,hN x]
   have hτ: 1 ≤ P0 x:= bulk_one ..; have hrx: 1≤ N x:=hN x; have hy':0 ≤ y x:=mul_nonneg (abs_nonneg _) hg; have hZ':0 <z x:=by unfold z; rw [←hz]; positivity [fan_pos L (-1) x,R.threshold_pos]; -- indentation trap
   have hT:0 < T x:=by unfold T; positivity
   refine ⟨hrx,add_pos_of_pos_of_nonneg (by positivity) hy', (by unfold M; positivity [guest_nn su L (n+1) E]),(le_abs_self _).trans ht,?_, hr.trans ((le_abs_self _).trans hv),?_,?_⟩
   · have hh:P.threshold≤φ:= by unfold φ loom; exact (le_mul_of_one_le_left P.threshold_pos.le C.C_one).trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans C.C_one) P.threshold_pos.le) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
     unfold canopyW; rw [← hz]; unfold N; nlinarith only [mul_le_mul_of_nonneg_right (hp'.1.trans (mul_le_mul_of_nonneg_left hh zero_le_two)) (by positivity : 0≤(1+(Malachite.radiusD x:ℝ))^p)] -- N unfold
   · apply le_trans _ (le_add_of_nonneg_left (show 0≤ T x*N x^n by positivity)); exact (le_of_eq (by unfold g; ring)).trans (mul_le_mul_of_nonneg_right hr hg)
   intro b S hU
   have he:P.threshold=temp x:=hP'
   have hβ':0 < β:=lt_of_lt_of_le (half_pos hpβ) hβ
   have ht:(gStep β)>0 :=inv_pos.mpr (Real.sqrt_pos.mpr hβ')
   have hw : ζ R (gStep β) ≤ z x:=by
      have hC:(gStep β) ≤2*gStep (betaF su x L):=by unfold gStep; rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ'),div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr hpβ),one_mul]; nlinarith [Real.sq_sqrt hpβ.le, Real.sq_sqrt hβ'.le, Real.sqrt_nonneg β]
      unfold z Lute.ζ; apply add_le_add hz.le; unfold fan; rw [Real.rpow_neg_one]; apply le_trans (div_le_div_of_nonneg_right hC R.threshold_pos.le); unfold gStep; rw [hz]; change _/( (Real.sqrt (betaF su x L))⁻¹*_ ) ≤ _; apply le_of_eq; field_simp [ne_of_gt (Real.sqrt_pos.mpr hpβ),ne_of_gt (Delay.monitor_pos ..)]; rfl -- def meter?
   have hE0:0≤ ζ R (gStep β):=by unfold Lute.ζ; positivity [R.threshold_pos]
   let l:= bulk (coverNumber R.B S) r x; have hU':l≤ P0 x:=by unfold l P0 bulk; gcongr
   have hL:1≤l:= bulk_one ..
   have hh : Cub.opal C E P R L S r x (gStep β)≤T x:=by
       unfold Cub.opal; apply (add_le_add_left (Heir.Lute.booster hR hp'.2 ht.le) _).trans; rw [hα]; unfold T Z'; rw [add_mul,add_mul]; have hB:=boost_nn C E L
       apply add_le_add; · gcongr; -- hU
       have hT:0≤ 16/E.ε:= by have hh:=E.guards; positivity
       exact (mul_le_mul_of_nonneg_left hw hT).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hτ))
   refine ⟨(mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ N x^n)).trans (le_add_of_nonneg_right hy'),le_trans (Heir.Lute.fares hR) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hL) hU' _) (guest_nn su L (n+1) E)),?_⟩
   intro pw hpS i hi; have he: separation i.1 pw ≤ Heir.breadth R S:= close_enough hpS (mem_union_left _ hi.1); have hr : 2+(Heir.breadth R S:ℝ) ≤ P0 x:= ((Lute.covers (r:=r) (X:=S) hR).2.1).trans hU'
   refine le_trans ?_ ((le_abs_self _).trans hB); unfold Lyre.width; rw [hz,‹R.power=_›]; have heh:0≤ fiery su x L:=hz ▸ R.threshold_pos.le; gcongr; linarith only [hr,show (separation i.1 pw:ℝ) ≤ Heir.breadth R S by exact_mod_cast he]
end YM.Massive.Poised
#print axioms YM.Massive.Poised.tithing
