import YM.QCD.Purse.Home
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
lemma soil_r (L:Side)(P₀:Plan n)(r l:ℕ)(u q a η ζ:ℝ)(R: ℝ→ℝ)(hu:0<u)(he:0<η)(hx:Rate su L (-(1/2)) R): Rate su L (-(1/32)) (fun x=>Spice.soil P₀ L (radiusB x) l u (coneK L η x) (R x) ζ q (haloK L x) a r):=by
   unfold soil; have hp: Rate su L 0 (fun x=> (1+(↑(radiusB x)+1:ℝ))^r):=((Rate.const 1).add (Rate.radius_price.add (Rate.const (1:ℝ)))|>.pow r).weaken (by linarith)
   have ht:Rate su L 0 (fun x=>(2*↑(radiusB x)+1:ℝ)^4):= ((Rate.radius_price.mul_left _|>.add (Rate.const (1:ℝ))).pow 4).weaken (by norm_num)
   have hf:=ht.mul (((Rate.power (a:=-(1/32))).mul_left (Pine.stamp P₀ L)|>.mul_right a⁻¹).mul_right (massL L))
   have hm: Rate su L (-(1/32)) (fun x=>Real.exp (-u*fossil (radiusB x) l)):=by simpa only [sub_zero] using Jets.Touch.pale u 0 hu l
   have hh:= hx.mul (shade_e L he.ne'); simp_rw [div_eq_mul_inv (_:ℝ) (coneK _ _ _/2)]; apply Rate.add; exact (hp.mul ((hf.weaken (by norm_num)).add ((hm.add (hh.weaken (by norm_num))).mul_right _))).weaken (by norm_num)
   exact (Jets.Touch.pale u (u/2) (half_lt_self hu) l |>.mul_left _).mul_right _
lemma reachAff (A: Libretto su j)(L: Side)(p:ℕ) : ∃ x:ℝ→ℝ, Rate su L (-(1/2)) x ∧ ∀ u P, P.power=p → P.threshold ≤ 2*fiery su u L → loom P (Heir.reach u) A.C ≤ x u :=by
    let v u:= (1+(Heir.reach u:ℝ))^p; have hv: Rate su L 0 v:=by
       unfold v Heir.reach; push_cast; exact (((Rate.const 1).add (((Rate.const 45).mul (((Rate.const 1).add (Rate.radius_price (G:=su) (L:=L))))).weaken (by linarith))).pow p).weaken (by norm_num)
    refine ⟨fun u=>A.C*(2*fiery su u L)*v u, (( (Rate.flame.mul_left 2|>.mul_left A.C)).mul hv).weaken (by norm_num),?_⟩
    intro u P he ht; unfold loom; rw [he]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (zero_le_one.trans A.C_one)) (by positivity)
lemma gridBeam (B:Support f) {U V:Grid f} (h:beamAt B U V A)(hp:A ≤ b):beamAt B U V b:=fun i a c=> (h i a c).trans hp
structure Tender (P₀:Plan n) (N i:ℕ)(L: Side)(N':Libretto su j)(Z:Hera.Rights su j)(D:Heir.Record)(R:BudgetPoint)(x y d a v u g η h z C r s:ℝ) (q A φ:ℝ) : Prop where
    purse : ∃ ε V Q ζ ρ :ℝ, (∀ x:su.Color, ‖x‖≤ ε → su.chord (su.lieExp x) ≤ V*‖x‖) ∧ 0 ≤ V ∧ D.Q*loom R (Heir.reach s) N'.C ≤ ε ∧ N'.M*loom R (Heir.reach s) N'.C ≤ ε ∧ (N'.M*loom R (Heir.reach s) N'.C ≤1) ∧ tender Z 1 (N'.M*loom R (Heir.reach s) N'.C) ≤ fern L^5 ∧ (∀ f:Side,∀ (U W:Grid f) (p:Support f) t, BeamRaw p U W t → beamAt p U W (Q*t)) ∧ Q*r+Q*(V*loom R (Heir.reach s) N'.C*(D.Q+N'.M+N'.M)) ≤ z∧ Q*r≤z∧ 0 ≤ ζ ∧ 0 ≤ ρ ∧ (∀ m:ℕ,(1+(m:ℝ))^2 ≤ ζ*Real.exp (u/2*m)) ∧ (0≤φ→0≤a→∀ t:ℝ,|t|≤ haloK L s→ Sun.fingers N*Spice.soil P₀ L (radiusB s) i u d z ζ φ |t| a 2 ≤ ρ) ∧ 4*(ρ*y)≤A*(x/4)∧4*(ρ*y)≤x/8 ∧ 0≤A ∧ 0≤z∧ z<d/2
-- format simplify args tender
lemma tenderR (P₀:Plan n)(N i p:ℕ)(L:Side)(N':Libretto su j)(D:Heir.Record)(Z:Hera.Rights su j)(v u q a t r η K θ:ℝ)(he:0<u)(hη:0<η)(hK:1 ≤ K)(s: ℝ→ℝ)(hS:Rate su L (-(1/2)) s): ∃ z A:ℝ→ℝ, Rate su L (-(1/2)) z∧ Rate su L (-(1/32)) A ∧∀ᶠ x in atTop, ∀ B:BudgetPoint,B.power=p→ B.threshold ≤ 2*fiery su x L → Tender P₀ N i L N' Z D B (fan L θ x) (K*fan L θ x) (coneK L η x) a v u v η q (z x) v (s x) x v (A x) r:=by
    let V:= u/2; have hV:=half_pos he
    let ζ:= V⁻¹^2*Nat.factorial 2*Real.exp V; have hz:0 ≤ ζ:=by unfold ζ; positivity
    obtain ⟨B,ε,hB,hε,ht⟩:=chord_chart_cost su
    obtain ⟨C,hC,h⟩:= boughtX
    obtain ⟨x',hx,hp⟩:= reachAff N' L p
    let V x:=C*(B*x' x*(D.Q+N'.M+N'.M))
    let W x:= |C*s x+V x|; have hU: Rate su L (-(1/2)) W := Rate.compare ((hS.mul_left C).add (((hx.mul_left B).mul_right _).mul_left C)) (Eventually.of_forall (fun x=> (abs_abs (C*s x+V x)).le))
    let d x:=coneK L η x
    let ρ x:=|Sun.fingers N * Spice.soil P₀ L (radiusB x) i u (d x) (W x) ζ r (haloK L x) a 2|; let A x:=16*ρ x*K
    have hg:Rate su L (-(1/32)) ρ:= Rate.compare ((soil_r L P₀ 2 i u r a η ζ W he hη hU).mul_left _) (Eventually.of_forall fun i=> (show (|(|(_:ℝ)|:ℝ)|:ℝ) ≤ |(_:ℝ)| from (abs_abs _).le))
    refine ⟨W,A,hU, (hg.mul_left 16).mul_right K,?_⟩
    filter_upwards [Dust.prices N' Z L p,(hg.mul_right K).below (by norm_num) (1/32) (by norm_num), (hx.mul_left D.Q).below (by norm_num) ε hε,(hx.mul_left N'.M).below (by norm_num) ε hε,(hU.mul (shade_e L hη.ne')).below (by norm_num) (1/2) (by norm_num), kentucky L hη] with x hD he hy H X hK'
    intro P' hW hΩ; constructor; obtain ⟨hj,hA⟩:= hD P' hΩ hW; let y:=loom P' (Heir.reach x) N'.C; have hzP:=hp x P' hW hΩ; change y ≤ x' x at hzP; have hY:0 ≤ y:=by unfold y loom; have h:=N'.C_one; have he:= P'.threshold_pos; positivity
    have htX:= D.majorant; have htK:= N'.matins; have hh:= hY.trans hzP
    have hx': C*(B*y*(D.Q+N'.M+N'.M)) ≤ V x:=by unfold V; gcongr
    have hρ:0 ≤ ρ x:=abs_nonneg _
    refine ⟨ε,B,C,ζ,ρ x,ht,hB.le,(mul_le_mul_of_nonneg_left hzP (by positivity)).trans ((le_abs_self _).trans hy), (mul_le_mul_of_nonneg_left hzP (by positivity)).trans ((le_abs_self _).trans H),hj,hA,h,(add_le_add_right hx' _).trans (le_abs_self _), ?_,hz,hρ,?_,?_,?_,?_,?_, abs_nonneg _,?_⟩
    · apply le_trans _ (le_abs_self _); apply le_add_of_nonneg_right; unfold V; positivity
    · intro m; exact polynomial_cost hV (show 0≤ (m:ℝ) from Nat.cast_nonneg _) _
    · intro hj hv t hT; unfold ρ; apply le_trans _ (le_abs_self _); unfold soil d; apply mul_le_mul_of_nonneg_left _ (by unfold Sun.fingers; positivity); have hD:=Pine.healthy P₀ L; have hL:= mass_pos L; gcongr
    · unfold A; exact le_of_eq (by ring)
    · have hx:= (le_abs_self _).trans he; nlinarith only [mul_le_mul_of_nonneg_right hx (fan_pos L θ x).le]
    · unfold A; positivity
    have hz:= (le_abs_self _).trans X; rw [← div_eq_mul_inv] at hz; exact (div_lt_one (half_pos (mul_pos hη (pow_pos hK'.1 _)))).mp (hz.trans_lt (by norm_num))
end YM.QCD.Shells
