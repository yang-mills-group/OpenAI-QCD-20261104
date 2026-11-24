import YM.Eole.Seal
import YM.Eole.Gale
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Session
open QCD.GasP Gain QCD.Conductor QCD.High QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
open MassiveQCD.Twist MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes Stags
open scoped Classical Stamp
variable (X:Massive.SourceRead.TaperHol){U': YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U')
variable (b:I→ Cover)(q:I→Bool)(p:J→ Cover)(Z: Bloc I J)(u:J→Bool) (hk:Z.flag q=u)
set_option quotPrecheck false
variable {t v γ:ℝ}{P:BudgetPoint}{k n d ℓ:ℕ}
local notation "m"=> Keys c 6
variable (Kit:Code c 6)(z:ℂ)(xe:Grid c→ℝ)(S:QCD.Run.St c)(L:Side)
local notation "Ow"=> wrap c ∘ b
local notation "Zw"=> wrap c ∘ p
local notation "U₀"=>Kit.EvalK z
local notation "Q0"=> heartS (Kit.EvalE z) P.threshold xe S
open Card Iris
variable {D:Type}
lemma grace (V: Reel c 6 J D) (he: V.Occupant (wrap c∘p) u t P 2 γ v (fun _=>1)): (survived V).Occupant (wrap c ∘ p) u t P 2 γ v (fun _=>1):=by obtain ⟨f,hf,hV⟩:=he.reserve; exact ⟨true_multi _ _ _ he.booked,f ∘ Subtype.val,fun i=> budget_pull (fun x: LargeE V=>x.val) Subtype.val_injective (hf i),fun i=> hV i.val⟩
variable {Wq T0 a1 a2 x0 M σ η:ℝ}{Fi Fx M₀:ℕ}
variable (r:I→Label d)(W:I→ℝ)(H:Grid c→ Patio (Keys c 6⊕Spine I))(Ψ:BudgetPoint) (w:I→ℝ) (Γ:Set (Finset I))(Γ':Set (Finset J))
open Jets Jets.Touch
local notation "T1"=> taxK L x0 1
local notation "T2"=> taxK L x0 2
local notation "T3"=> taxK L x0 (9/5)
local notation "T4"=> taxK L x0 (8/5)
local notation "ε"=>(1/256:ℝ)
variable (hv:1 ≤ t)(hP:Pilot X B d P.order P.power k n ℓ a1 a2)
variable (ht:PayRes X B b q P Kit z xe S r W (l:=ℓ) Ψ t (taxK L x0 1) Wq ((taxK L x0 ((2-1)/2))⁻¹) H Γ k n)
variable (hf:Fires (wrap c ∘ b) Fi)(hF:Fires (wrap c ∘ p) Fx)(hB:30*(ℓ+1)≤ c.val) (hh:ℓ+1 ≤ P.B)(hX:Ψ.threshold=P.threshold)(hW:∀ i,Real.exp ((1/8:ℝ)*81)*a2*wealth (r i).val P.threshold t+W i≤T0)(hV:0 ≤ T0)
variable (hq: ∀ i:I,separation (wrap c (b i)) (wrap c (p (Z.unit_ i))) ≤ M₀)(hν: Gain.Docket L x0 P.B P.order M₀ Fi η (bonus Fi P.B (1/256)*T0 + Wq) σ M)
variable (hpZ:rentM P.B P.order P.power (1/256)*(σ*(1-(1/2:ℝ))⁻¹)≤ M)(hp0:0<η)(hpW:∀ i,|w i|≤η) (hζ: Basal.Dough L Fx x0) (hΓ:∀ i∈ Γ',∀ j ⊆ i,j∈ Γ')(hΓp:∀ i∈Γ',Spaced (wrap c ∘ p) i P.B)(hΩ:∀ i∈Γ',∀ j⊆Z.plant i,j∈Γ)
local notation "α0"=> (24/256:ℝ)
local notation "αL"=> (25/256:ℝ)
local notation "Life"=> Basal.riseP k n P.B ε α0 * M
include hk hv hP ht hf hF hB hh hX hW hV hq hν hpZ hp0 hpW hζ hΓ hΓp hΩ
local notation "σ'"=> (1+a2*a1)*Life
set_option maxHeartbeats 800000 in
lemma culling (hY: bonus Fx P.B ε*(Basal.riseP k n P.B (1/256) (24/256)*M +a2*(a1*(Basal.riseP k n P.B (1/256) (24/256)*M)))≤ 1)(he:M ≤ Wq): ∃ y:J→ Label d, (∀ i,wealth (y i).val P.threshold t ≤ a1*(Basal.riseP k n P.B (1/256) (24/256)*M)) ∧ Clays X B p u P Kit z xe S y (fun _=> σ') (l:=ℓ) Ψ t (taxK L x0 1) Wq ((taxK L x0 ((2-1)/2))⁻¹) (fun i=> Bloc.sparC m q Z (Cupola.scaler m w (H i))) Γ' k n:=by
     have hσ (t:ℝ) (h:0 ≤t) : 1 ≤ taxK L x0 t:=Real.one_le_exp (mul_nonneg h (fan_pos ..).le); have ht':0 < t:=zero_lt_one.trans_le hv
     obtain ⟨C',hc',E,hE,R,G,hG,Y',F,h1,h2,h3,h4,h5,h6,h7⟩:= ht.booth; let P':= Gel.May.Roles q B b P d r ℓ F R; have Hs:= Gel.May.coast q X B b P d r ℓ k n hP F W h6 hv hB Fi hh hf (show Footprint.reserve (1/8) (29/256) 1 ε from by norm_num [Footprint.reserve]) hW hV
     have hKP:P'.Occupant Ow q t P 2 (29/256) (bonus Fi P.B ε*T0+Wq) (fun _=>1):= Gel.May.jointlyEarn q b P _ _ (occup _ _ _ h2 (by norm_num) le_rfl) Hs (add_comm ..).le
     have hT: T2=T1*T1:=by unfold taxK; rw[← Real.exp_add]; congr 1; ring
     obtain ⟨D',E',hd,heG,V',K',hA,hK,hΨ,hO⟩:= Gain.serenity q Ow Y' w P' Z hKP (hT.symm ▸ h3) M₀ u Zw hk U₀ h4 hq hf hv hpW hp0 hν hpZ
     have hf0(i:Finset J)(hi:i∈Γ')(U:Grid c): shutter m (Z.plant i) (H U)=shutter m (Z.plant i) (NormedSpace.exp (rootR (Spine I) _ (Q0 U)+Reel.rope P' P.threshold U)*withdraw 6 Ow t (heartK Y' P.threshold U)):=by
           let L:=Z.plant i; let f:= shutter m L; have he:(L.powerset:Set (Finset I))⊆ Γ:=fun s h=> hΩ i hi s (mem_powerset.mp h)
           refine (h7 _ (he (mem_powerset.mpr le_rfl)) U).trans ?_; unfold stampRoll relativeE; rw [hX,map_mul,map_mul]; exact congr_arg _ (Film.mergeFront 6 Ow q t U₀ Y' Γ L he h3.fits ht' h3.tilt.uses h4 U (prints Y' U h3.tilt.uses h3.tilt.sold (hT ▸ hσ 2 (by norm_num)) (by norm_num) hv))
     have h0:0 ≤ M:= hν.limit.le; have hy: V'.Occupant Zw u t P 2 (α0+ε) M (fun _=>1):=by rw [show α0+ε=αL by norm_num]; exact hA
     choose y hl hw using fun i:J=> Basal.regalX p V' u X B k n ℓ d hy hP hv (show 0≤ α0 from by norm_num) (show 0< ε from by norm_num) i hh
     let Sv:=Film.publication 6 Zw u K' Γ' t; have hℓ:0 ≤ Life:= by unfold Basal.riseP Reserves.polyPrice; positivity
     have hm:StackK P.B T3 T4 (18/256) (14/256) (19/256) 1:=hν.mast.symm ▸ hζ.pose
     obtain ⟨Fv,hΦ,I',hI,K0,hYk,hΥ,hΘ⟩:=Gel.May.morendo (w₁:=T1) (P₀:=Γ') u V' X B p P d y ℓ k n hP (fun i=>Life) (fun i=>Life) _ K' U₀ hΨ hl hA.booked hK hB hv (by norm_num) (by norm_num) (hσ _ (by norm_num)) (show 0≤ Life+a2*(a1*Life) from add_nonneg hℓ (mul_nonneg (zero_le_one.trans hP.funds) (mul_nonneg (zero_le_one.trans hP.light) hℓ))) (fun _=>le_rfl) Q0 Fx hF (fun U=> by obtain ⟨e,he,hD⟩:=hA.reserve; simp only [abs_one,prod_const_one,one_mul] at he; exact creditE Zw u V' e hA.booked hD he (by norm_num) hv U) (show Footprint.reserve α0 (19/256) 1 ε from by norm_num [Footprint.reserve]) hm hY (hσ _ (by norm_num)) (by norm_num)
     let AF:=Film.publication 6 Zw u K0 Γ' t
     refine ⟨y,hw,_ , (by infer_instance),_ ,inferInstance,survived V',_ , inferInstance,AF,Fv,fun i=>i.property,grace p u _ (occup _ _ _ hy (show α0 ≤α0+ε by norm_num) he),Film.turned_t 6 Zw u K0 Γ' t hYk.tilt hYk.fits ht', hζ.recolor c J _ _ _ _ Γ' K0 t hν.mast hF hΓp hYk ht',hΦ, fun i hi U=>?_⟩
     let V'' := NormedSpace.exp (rootR (Spine I) _ (Q0 U)+Reel.rope P' P.threshold U)*withdraw 6 Ow t (heartK Y' P.threshold U); let Y'':= withdraw 6 Zw t (heartK K' P.threshold U); let Hv := NormedSpace.exp (rootR (Spine J) _ (Q0 U)+ Reel.rope V' P.threshold U); let Fk:= shutter m i; have ht : (i.powerset:Set (Finset J))⊆Γ':=fun v h=> hΓ i hi v (mem_powerset.mp h);
     unfold stampRoll; rw[hX]; apply Eq.trans _ (hΘ i ht U); unfold relativeE; change Fk (Bloc.sparC m q Z (scaler m w (H U)))=Fk (Hv * Film.reports 6 Sv U₀ P.threshold U); apply (Bloc.match_cost m Z q w (H U) V'' _ (hf0 _ hi U)).trans; rw [←show Hv * Y''= _ from hO U (Q0 U),map_mul Fk,map_mul Fk]; exact congr_arg _ (Film.mergeFront 6 Zw u t U₀ K' Γ' i ht hK.fits ht' hK.tilt.uses hΨ U (prints K' U hK.tilt.uses hK.tilt.sold (hσ _ (by norm_num)) (by norm_num) hv)).symm
end Session
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Session.culling
