import YM.Poised.Born
import YM.Poised.Plumes
import YM.Poised.Lilac
import YM.Poised.Caliph
import YM.Poised.Doves
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
variable (Y:Fleet H ι N)(Γ :Cash W τ μ L Q o C T (lore Rx)) {X:Support f} {B:BudgetPoint}{n p d k l:ℕ}
local notation "Y?"=> Lat.Fields c 6
local notation "Y'"=> Lat.Fields f 6
variable {N': Libretto su n}{D:Heir.Record}{v u t M w W₁ W₂ Ω' ν r θ x x' x₀ Y₂ R₀ A₀:ℝ}{χ:Chi}

-- shape chosen after L. each T.Sturd via Height R. 
structure GramT (N':Libretto su n)(D:Heir.Record)(k:ℕ)(A K:ℝ)(B R:BudgetPoint)(x:ℝ)(L:Side):Prop where
   spin: (1+patterns n)*(A*(N'.M*Heir.loom B (Heir.reach x) N'.C))*((Fintype.card Pipes.Shell:ℝ)*pup k K * (Kit.slope L)^2) ≤ (Kit.slope L)^max k 2
   posh : N'.M* Heir.loom B (Heir.reach x) N'.C ≤ 1
   pressure: clinicFee n D.Q*(Heir.loom B (Heir.reach x) N'.C)^2 + D.ε*R.threshold ≤ (Kit.slope L)^max k 2 *R.threshold
lemma grading (N':Libretto su n)(D:Heir.Record)(k r₂:ℕ)(A K:ℝ)(L:Side)(h:D.ε≤ (Kit.slope L)^max k 2 / 2)(hA:0 ≤ A)(hK:1≤K) : ∀ᶠ x in atTop, ∀ (B R:BudgetPoint),R.threshold=fiery su x L → B.threshold≤2*R.threshold→ B.power=r₂ → GramT N' D k A K B R x L:=by
    obtain ⟨s,hS,hp⟩:= reachAff N' L r₂; let u:=Kit.slope L; obtain ⟨hu,hU⟩:=boxed1 L; let Y:= clinicFee n D.Q; have hY : 0 ≤ Y:=by unfold Y clinicFee; have h:=patterns_nonneg n; have hp:=D.majorant; positivity
    let p:= u^max k 2; have hh:0 < p:=pow_pos hu _; let X:=(Fintype.card Pipes.Shell:ℝ)*pup k K*u^2; have hX: 0≤X:=by unfold X; have h:=pup_pos hK k; positivity
    filter_upwards [(((((hS.mul_left N'.M).mul_left A).mul_left (1+patterns n)).mul_right X).below (by norm_num) _ hh), (hS.mul_left N'.M).below (by norm_num) 1 (by norm_num), tiny_flame su L (k:=p/2) (by simpa only [show (-(1/2):ℝ)*↑(2:ℕ)= -1 from by norm_num] using! ((hS.pow 2).mul_left Y)) (half_pos hh)] with x hX' hx hB B R hR' hV ht
    let v:=loom B (Heir.reach x) N'.C
    have hr : v ≤ s x:= hp x B ht (hR' ▸ hV); have hm:0≤ v:=by unfold v Heir.loom; have h:=N'.C_one; have h':=B.threshold_pos; positivity
    have hs:= N'.matins; refine ⟨?_, (mul_le_mul_of_nonneg_left hr (by positivity)).trans ((le_abs_self _).trans hx),?_⟩
    · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity)) hA) (add_nonneg zero_le_one (patterns_nonneg _))) hX).trans ((le_abs_self _).trans hX') -- le_add...
    change Y * v^2 +_≤ _; apply (add_le_add ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm hr _) hY).trans hB) (mul_le_mul_of_nonneg_right h R.threshold_pos.le)).trans; rw [hR']; exact le_of_eq (by unfold p u; ring)
-- all.T issue one.Rate.Seat.
structure FairT (P₀:Plan p)(D:Heir.Record)(N':Libretto su n)(d k:ℕ)(L: Side)(x u r q a v σ R:ℝ)(B:BudgetPoint):Prop where
   tribute : ∃ V Q z ε Z: ℝ,0≤V ∧ 0≤z ∧ 0≤Z ∧ (∀ x:su.Color,‖x‖≤ ε →su.chord (su.lieExp x) ≤ V*‖x‖) ∧
      let y:= loom B (Heir.reach x) N'.C
      D.Q*y ≤ ε ∧ N'.M*y≤ ε ∧ Q*v+Q*(V*y*(D.Q+N'.M+N'.M)) ≤ z ∧ Q*v ≤ z∧ z < coneK L r x/2 ∧ (∀ f (U W:Grid f)(p:Support f)(t:ℝ), BeamRaw p U W t→ beamAt p U W (Q*t)) ∧ (∀ j:ℕ,(1+(j:ℝ))^d ≤ Z*Real.exp (u/2*j)) ∧ (∀ m:ℝ,|m| ≤ haloK L x→ 0≤ q → 0≤a→ Sun.fingers 6 * Spice.soil P₀ L (radiusB x) k u (coneK L r x) z Z q |m| a d ≤ R) ∧
        ambit (radiusB x) d*(Sun.fingers 6*q*(z/(coneK L r x/2))) ≤ σ
lemma trophies (P₀:Plan p)(N':Libretto su n)(D:Heir.Record)(K₂ d k:ℕ)(L:Side)(u r q a:ℝ)(hu:0<u)(hr:0<r)(v:ℝ→ℝ)(ht:Rate su L (-(1/2)) v):∃ σ Z:ℝ→ℝ, Rate su L (-(1/32)) σ ∧ Rate su L (-(1/32)) Z ∧ ∀ᶠ x in atTop,0≤σ x ∧ 0≤Z x ∧ ∀ B:BudgetPoint,B.threshold ≤2*fiery su x L → B.power=K₂ → FairT P₀ D N' d k L x u r q a (v x) (σ x) (Z x) B:=by
   obtain ⟨V,ε,hV,hε,ht'⟩:=chord_chart_cost su
   obtain ⟨C,hC,h⟩:= boughtX; obtain ⟨w,hw,hp⟩:=reachAff N' L K₂; let X x:= C*(V*w x*(D.Q+N'.M+N'.M))
   let J x:=C*v x+X x; have hJ:Rate su L (-(1/2)) J:=(ht.mul_left C).add (((hw.mul_left V).mul_right _).mul_left C)
   let W x:= |J x|; have hW:Rate su L (-(1/2)) W:=Rate.compare hJ (Eventually.of_forall fun i=> (abs_abs _).le); let d' x:= coneK L r x/2
   let Z':=(u/2)⁻¹^d*Nat.factorial d*Real.exp (u/2); have hz:0≤Z':=by unfold Z'; positivity
   let σ x:= |((ambit (radiusB x) d)*(Sun.fingers 6*q*(W x/d' x)))|; let Z x:= |Sun.fingers 6*Spice.soil P₀ L (radiusB x) k u (coneK L r x) (W x) Z' q (haloK L x) a d|
   have hY:=hW.mul (shade_e L hr.ne'); have he: Rate su L 0 (fun x=>ambit (radiusB x) d):= ((Rate.const 1|>.add (Rate.radius_price.add (Rate.const (1:ℝ)))).pow d).weaken (by linarith)
   have ht₀ :=Rate.weaken ((he.mul (hY.mul_left (Sun.fingers 6*q)))) (b:=-(1/32)) (by norm_num)
   have hb : Rate su L (-(1/32)) σ:= Rate.compare ht₀ (Eventually.of_forall fun i=> by unfold σ d'; rw [abs_abs,div_eq_mul_inv (W i)]) -- abs le refl
   have hyO := (soil_r L P₀ d k u q a r Z' W hu hr hW).mul_left (Sun.fingers 6) -- arg
   refine ⟨σ,Z,hb,Rate.compare hyO (Eventually.of_forall fun _=> (abs_abs _).le),?_⟩
   filter_upwards [(hw.mul_left N'.M).below (by norm_num) ε hε,(hw.mul_left D.Q).below (by norm_num) ε hε,(hY).below (by norm_num) (1/2) (by norm_num), Jets.Touch.kentucky L hr] with x hM hQ hY' hr'
   refine ⟨abs_nonneg _,abs_nonneg _,fun B hV' hB=>?_⟩
   have hs:=hp x B hB hV'; have hD:=D.majorant; have hm:=N'.matins; let y:= loom B (Heir.reach x) N'.C; change y≤_ at hs; have hh: 0≤y:=by unfold y Heir.loom; have h:=B.threshold_pos; have hz:=N'.C_one; positivity
   have hX: C*(V*y*(D.Q+N'.M+N'.M)) ≤ X x:=by unfold X; gcongr
   refine ⟨⟨V,C,W x,ε,Z',hV.le,abs_nonneg _,hz,ht', (mul_le_mul_of_nonneg_left hs (by positivity)).trans ((le_abs_self _).trans hQ), (mul_le_mul_of_nonneg_left hs (by positivity)).trans ((le_abs_self _).trans hM), (add_le_add_right hX _).trans (le_abs_self _),?_,?_,h,fun i=>polynomial_cost (half_pos hu) (Nat.cast_nonneg (α:=ℝ) i) d,?_,le_abs_self _⟩⟩
   · apply le_trans _ (le_abs_self (J x)); have hz:=hh.trans hs; apply le_add_of_nonneg_right; unfold X; positivity
   · have he:= (le_abs_self _).trans hY'; rw [← div_eq_mul_inv] at he; exact (div_lt_one (half_pos (mul_pos hr (pow_pos hr'.1 _)))).mp (he.trans_lt (by norm_num))
   intro m hm hq ha; apply le_trans _ (le_abs_self _); have hD:=Pine.healthy P₀ L; have hw:=Pine.mass_pos L; unfold Spice.soil; apply mul_le_mul_of_nonneg_left _ (by unfold Sun.fingers; positivity); gcongr
end YM.Massive.Poised
#print axioms YM.Massive.Poised.trophies
