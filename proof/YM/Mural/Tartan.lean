import YM.Mural.TraceM
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ}
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG
set_option quotPrecheck false
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "L"=> L'.L
local notation "S"=> L'.visit K d
local notation "Ψ"=> sliceL L' d
local notation "M"=> arctic L j
variable {T: Tube su (L'.visit K d)}{T':Teller su}{Q:Target su T'}{v x₀ W μ C:ℝ} {o:Target.Order su W}
variable (x y: Site c)(p q:Site f){N:ℕ}
local notation "Tx"=> texel L' d 0 x p
local notation "Ty"=> texel L' d 0 y q
local notation "Cq"=> cleared p q L' d x y
local notation "Lq"=> loaded p q L' d x y
local notation "Q0"=> (sliceL L' d).embed x
local notation "Yg"=> (sliceL L' d).embed y
local notation "B"=> radiusB x₀
local notation "A₀"=> Lattice.halo B {Q0}
local notation "σt"=> berthD j
variable (hv:separation ((sliceL L' d).embed x) p ≤ arctic L'.L j)(hw:separation ((sliceL L' d).embed y) q ≤ arctic L'.L j)
variable (hp:separation p q≤ berthD j)
variable (hS: (berthD j)*L'.L.val +arctic L'.L j+4*(berthD j)≤ radiusB x₀)
open MassiveQCD MassiveQCD.Plate MassiveQCD.PaletteT QCD.Mural
open MassiveQCD.Apron.Grove Loom Glow
variable {s t p' t₁ t₂ δ β b a y₀:ℝ} {P':Plan k}{X:Run.St f}{P₀:BudgetPoint}{W':ℕ→Atom su 2}
variable (H:Cash W x₀ μ L'.L Q o C T (trimP T P₀ δ β b))(U: Swathe L' d X W' P' t p' s t₁ t₂ m)
local notation "δb"=> veto (x₀:=x₀) L' d x
local notation "Xg"=> VarnC H U N
variable (r:ℂ)
local notation "C!" i=> shadeM L' d x y p q r i
noncomputable def wishGain (v:ℝ)(l:Side):ℝ:= betaF su v l^(3/8:ℝ)
-- Need λ≥ β0^.36 normalized each. Available through after-L.Birth.
noncomputable def rentV (Lx:Side)(θ x:ℝ):= (fundsL Lx θ x) * Real.exp (- (Q.relative * Animals.ballCost 38)) -- implicit Q
variable (Q o)
structure Wit (L₀:Side)(j:ℕ)(θ x:ℝ):Prop where
   fund : (berthD j)*L₀.val +arctic L₀ j+4*(berthD j)≤ radiusB x
   earn :∃ κ W':ℝ,∃ f₀:ℝ→ℝ,(∀ X:su.El, ‖colour X-1‖≤ κ*su.chord X) ∧ 0≤κ ∧ Woods T' L₀ o.a f₀ x ∧ (∀ (X:Mat)(i j:Hue),‖X i j‖≤ W'*‖X‖) ∧ 0 ≤ W'∧
     ∀ r:ℂ,‖r‖≤ wishGain x L₀ → ‖r‖*W'*(fenceCharge j L₀ κ * f₀ x) ≤ rentV L₀ θ x (Q:=Q)∧ ‖r‖*W'*(2*(Kit.scale L₀)^2) ≤ Real.exp (fan L₀ (1/4) x*2)* rentV L₀ θ x (Q:=Q)
lemma rendezvous (j:ℕ)(L₀:Side)(θ:ℝ):∀ᶠ x:ℝ in atTop,Wit Q o L₀ j θ x:=by
    obtain ⟨W,hW,H⟩:= place_limit; obtain ⟨κ,hk,hκ⟩:= Fork.halo_chart; obtain ⟨b,hp,hM⟩:= hammock T' L₀ o.a o.large
    have hC:0 ≤ fenceCharge j L₀ κ :=by unfold fenceCharge; have he:=scale_pos L₀; have hv:=mass_pos L₀; dsimp only; positivity
    let Z(x:ℝ):= wishGain x L₀ * W * (fenceCharge j L₀ κ * b x); let A:= Real.exp (Q.relative * (Animals.ballCost 38)); have hA:0<A:=Real.exp_pos _
    have hv: Seat L₀ (-θ-1) (fun x=> Z x*A):= Seat.eliminated ((( (show Rate su L₀ (3/8) (fun x=>wishGain x L₀) from Rate.power).mul_right W).mul (hp.mul_left _)).mul_right _) (by norm_num)
    let F(x:ℝ):= wishGain x L₀*W*(2*(Kit.scale L₀)^2); let f x:= fan L₀ (1/4) x*2; have he: Rate su L₀ (-(1/2)) (fun x=>Real.exp (- f x)):=by
        have he: Rate su L₀ (-(1/2)) (fun x=> Real.exp (-2*fan L₀ (1/4) x)):= Rate.monitor_cutoff (show 0<(2:ℝ) by norm_num) (show 0<(1/4:ℝ) by norm_num) -- check
        -- eq reorder
        unfold f; simp_rw [mul_comm _ (2:ℝ), ← neg_mul]; exact he
    have hY: Seat L₀ (-θ-1) (fun x=>F x*Real.exp (-f x)*A):= Seat.eliminated (((( (show Rate su L₀ (3/8) (fun x=>wishGain x L₀) from Rate.power).mul_right W).mul_right _).mul he).mul_right _) (by norm_num)
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (berthD j*L₀.val+ arctic L₀ j+4*berthD j),hM,hv (-θ) (by linarith),hY (-θ) (by linarith)] with x hh ht hv hy
    refine ⟨hh,κ,W,b,hκ,hk.le,ht,H,hW.le,fun r hr=>?_⟩; have hg:=mul_le_mul_of_nonneg_right hr hW.le; let v:= rentV L₀ θ x (Q:=Q); have hh:v=fundsL L₀ θ x/A:=by rw [div_eq_mul_inv]; unfold v rentV; rw[Real.exp_neg]
    constructor
    · refine ((mul_le_mul_of_nonneg_right hg (mul_nonneg hC ht.frames)).trans ?_); change Z x≤v; rw [hh]; exact (le_div_iff₀ hA).mpr ((le_abs_self _).trans hv)
    refine (mul_le_mul_of_nonneg_right hg (by positivity : (0:ℝ) ≤ 2* (Kit.scale L₀)^2)).trans (?_); change F x ≤ Real.exp (f x)*v; rw [mul_comm, ← div_le_iff₀ (Real.exp_pos _), hh]; apply (le_div_iff₀ hA).mpr
    rw [div_eq_mul_inv, ←Real.exp_neg]; exact (le_abs_self _).trans hy
-- Need vacant carrier construction even when r=0. debt.Birth will include Θ.Frame.Mag capabilities.Math.
variable (θ α:ℝ)
local notation "Z"=> Lattice.halo (radiusB x₀) {Q0}
lemma riptide (h: Wit Q o L j θ x₀)(hr: ‖r‖≤ wishGain x₀ L) (hp:2* L'.patch.radius < f.val)(hv:separation Q0 p≤ M)(hw: separation Yg q ≤ M)(hz: separation p q ≤ σt) :
    (∀ i:Option Rank, TrainY L' d K (N:=N) H U (fun _=> Q0) (shadeM L' d x y p q r i) δb θ) ∧ (∀ X Y, shadeM L' d x y p q r none X Y=0) ∧ ∀ g:Lat.Frame c,∀ i:Option Rank,∀ X V, shadeM L' d x y p q r i (gauge (constantGauge g (S).ratio) X) (gauge g V)=∑ j,fieldD x y g i j*shadeM L' d x y p q r j X V:=by
   obtain ⟨κ,W,f₀,hC,hF,hQ,hX,hY,hZ⟩:=h.earn
   refine ⟨fun i=> kindleT L' d K x y p q hv hw hz h.fund H U r hp θ κ W f₀ hC hF hQ hX hY (hZ r hr).1 (hZ r hr).2 i,fun U V=>by simp [shadeM,cellD],fun g i X V=>?_⟩
   let Wc:=constantGauge g (S).ratio; have hy: Wc ∘ (S).ratio.embed=g:=funext fun i=>congr_arg g ((S).ratio.embed_parent _)
   have hEq: Lq (gauge Wc X)- Cq (gauge g V) = colour (g x)*(Lq X-Cq V)*star (colour (g y)):=by
        rw [load_frame,clear_frame, show Wc Q0= g x from congr_fun hy x, show Wc Yg=g y from congr_fun hy y, ← sub_mul,← mul_sub]
   unfold shadeM; rw [hEq, knots, Finset.mul_sum]; exact sum_congr rfl fun _ _=> mul_left_comm ..
end YM.QCD.Comet
#print axioms YM.QCD.Comet.riptide
#print axioms YM.QCD.Comet.rendezvous
