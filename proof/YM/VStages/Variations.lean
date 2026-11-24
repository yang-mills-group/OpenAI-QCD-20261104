import YM.QCD.Fount.Wealth
import YM.VStages.Forecast
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth
variable {t a u r w b C τ Θ η Ω σ s p H α θ:ℝ}{K :KernelChoices}{J k N:ℕ}{f m:ℝ→ℝ}
variable {M:ParcelR}{O O₁:Clip}{τ₁ C₀:ℝ} {K:KernelChoices} {J₀:ℕ}
-- level promises. phy V (p:Coat) at Auxiliary Station - Poly. Gauge replication inclusion explicit eventually.
lemma limelitW (P:Plan J)(P₂:Plan J₀) (he: Rates M η)(E:Patch)(V:BareRates.pre su τ₁ C₀ k) (hw:Bolt su E.L f)(ht: 0<θ)(hq:0 ≤ w)(hv:0<H)(hm:Rate su E.L 0 m)(hj:3 ≤ k)(N:ℕ):
    ∀ᶠ x in atTop,∀ (F':Back E K J J₀ O τ C)(Q:Fog.Avenue F' η Ω Θ) (X Y:SunR M) (α:ℝ), Fog.Mist.BirthW M P P₂ F' Q X Y α→ ∀ i:ℕ,∀ (R:PathData su)(T:Tube su (act F'.fly K F'.chain i)),Stores.till x≤ (F'.chain.n i).val →let c:=F'.chain.n i; let F:=F'.port.forest i; let G:=divides0 F'.fly F'.chain i
    R.Bounds O₁ τ₁ C₀ w → Quilt T F (f x) → ∀ ρ: Bid.Dir su (F'.chain.n i)→ AxisChart su F, F'.port.u i=ᶠ[𝓝 0] ρ → Attached Q.D' R → ∀ r d:ℝ, Precision.Floor Q.D' O₁ (F'.chain.n i) r d→ (∀ i:Positions (Primary (F'.chain.n i) su), ‖i‖<eaves su E.L x→ Brush k (m x) 1 (Lapis.orbit F ρ) i) → ∀ y:ℝ, Jets.Touch.haloK E.L x ≤ y → y≤1 → ∀ z: Positions (Primary c su), ‖z‖<eaves su E.L x →
    let V':= highW E.L H θ x; let Z:=park F'.fly G P X.X X.Y (haloK E.L x) 0; let W:=favor ρ (tonic G Z X.Z.page N V') (chalice R O₁ Y.Z.page α (FieldB M Y c y P₂ F'.fly.land) N V'); Brush k (dues E.L x) (eaves su E.L x)⁻¹ (Shellac.off W) z ∧∃ a:ℝ,W 0=baker _ N a:=by
    let L:=E.L; let v x:=highW L H θ x; have hx: Seat L θ v:= Seat.timesL Seat.keeps _
    obtain ⟨c,hc,hπ⟩:= highGeom N; let g x:= c*f x
    have hW: Seat E.L 0 f:=fun r hr=> hw.listens hr; have hg:Seat L 0 g:=hW.timesL _
    let ψ:=QCD.Smoke.expPrice 2 M.t*M.e
    obtain ⟨ν,C',Fq,D,B,u,i,j,hν,hp,hz,hA,hF⟩:=revenueT (k:=J₀) he.hr he.hs P 0 M.c ψ M.d M.t N L he.ht
    let B₀:= coneK L ν; choose z hh using paint_supply su
    let Y x l:= clump l (1+m x+(1+m x)) (gross (z l) (B₀ x) Fq B (f x) (g x) (v x) l N); have hy (l:ℕ): Rate su E.L (1/16*l) (fun x=>Y x l):= pace _ (roofF hν l N _ _ _ hW hg hx) (((Rate.const _).add hm).add ((Rate.const _).add hm)) l
    obtain ⟨b,r,hb,hr,n,hV⟩:= houseY P₂ he
    obtain ⟨R₀,d,h,hA',i',H'⟩:=AtomF.robe_price he.ht (QCD.Smoke.expPrice 2 M.t*M.e) 0 (show 0 ≤ (0:ℝ) from le_rfl) 2
    let a:=coneK L b; let σ x:= tollS (f x) k ((1+M.b+w)*BareRates.bill V O₁)+tollS (f x) k ((1+|0|+w)*BareRates.bill V O₁)
    have hσ:Rate su L 0 σ:=by unfold σ tollS; exact ((((Brim.prep hw.uses k).mul_right _)).add ((Brim.prep hw.uses k).mul_right _)) -- typo
    let Jp x l:= levy (a x) r d R₀ (f x) (g x) (z l) (σ x) l (v x) N
    have hJ (l:ℕ): Rate su L (1/16*l) (fun x=>Jp x l):=coveL hb hW.ruled hg.ruled hx.ruled hσ _ _ _ _ _ _
    have H':= H'
    filter_upwards [bitL (L:=E.L) (H:=fun x i=> Y x i+Jp x i) (fun i=> (hy i).add (hJ i)) k,hurtL he.hw (hw.uses) he.hl N,kentucky L hp, Delay.shift_pos su E.L,(hm.mul (edge su E.L)).below (by simp only [zero_add]; exact vow_ok) 1 zero_lt_one,edge su E.L |>.below vow_ok 1 zero_lt_one] with x h₁ h₂ h₃ h₄ h₅ h₆ U Q X Z α ht i' R T hI c' F G hR hQ ρ hρ hG r' d' hD hE y h hY p hp₀ e Z' W
    have hi:(Stores.till x) ≤ (high U.fly U.chain i').val:= hI.trans (Nat.le_mul_of_pos_right _ U.fly.L.pos)
    have hk: 0 < a x:=mul_pos hb (pow_pos h₃.1 _); have hv':0< B₀ x:=mul_pos hν (pow_pos h₃.1 _)
    obtain ⟨hS,hB⟩:= hF X.X X.Y X.Z.page (X.Z.cost he.ht) (X.Z.permit he.ht).2 c' _ U.fly G 0 (haloK E.L x) U.has h₃.1 h₃.2.1 (by simpa using hp.le)
    have he':0<e:= mul_pos hv (fan_pos ..); have hs:(Fintype.card (Modes c' N):ℝ) ≤ g x:= (hπ c').trans_le (mul_le_mul_of_nonneg_left hQ.primary hc)
    have hK:=H' c' _ (show _≤_ from le_refl _) Z.Z.page (Z.Z.cost he.ht) (Z.Z.permit he.ht).2 -- params
    have hx := hV c' Z (haloK L x) y h₃.1 h hY U.fly.land; have hU: eaves su L x≤1 := (le_abs_self _).trans h₆; have hM:m x*eaves su L x≤1:=(le_abs_self _).trans h₅
    have hq₀:ρ 0=0:=hρ.eq_of_nhds.symm.trans (U.port.critical i').1 -- eq theorem name
    have hI' : (Fintype.card (Primary (U.chain.n i') su):ℝ) ≤ f x:= le_trans (Nat.cast_le.mpr (Fintype.card_le_of_injective _ (Sum.inl_injective (β:=Precision.Key F su)))) hQ.overall
    have he y (hy':‖y‖<eaves su E.L x) (i:ℕ) (hi: i ≤ k)(hg:0 < i): ContDiffAt ℝ i W y ∧ normJ i W y ≤ Y x i+Jp x i:=by
       obtain ⟨hz,hx'⟩:= lampA (by omega : 1≤k) hE hq₀ hU hM hy' i hi; have hp := composite hz (conscientious (s:=e) F G Z' X.Z.page hS hB hv' le_rfl he' hA (hh i) hQ.finalP hs hx')
       have hQ:= coda V hR hQ.one hI' (hy'.trans_le hU) hq ht.bill hx hr hk (W:=Z.Z.page) hK hA' ‹0<R₀›.le hQ.primary hs he' (hh i) hi hg
       refine ⟨hp.smooth.sub hQ.1,?_⟩; unfold normJ; rw [show iteratedFDeriv ℝ i W y= _ from iteratedFDeriv_sub_apply hp.smooth hQ.1]
       exact (norm_sub_le ..).trans (add_le_add ((Brush.offer.1 hp).2 _ le_rfl) hQ.2)
    obtain ⟨-,hk',hv',hν⟩:= borderR P P₂ U Q R ‹Rates M η› hS hv' h₃.1 h₃.2.2 ht hR hG hD (lt_of_lt_of_le h₃.1 h) hY ρ hρ (f x) hQ.one hI' N (d:=e)
    have hE:0<eaves su L x:= (norm_nonneg _).trans_lt hp₀
    refine ⟨reborn (f:=W) hE hj (fun i hi=>(he _ (mem_ball_zero_iff.mp hi) k le_rfl (by omega)).1) (fun j hj hk i hi=> (mul_le_mul_of_nonneg_right (he _ (mem_ball_zero_iff.mp hi) j hk (by omega)).2 (by positivity : 0 ≤ eaves su E.L x ^j)).trans (h₁ _ hk hj)) ?_ hk' _ (mem_ball_zero_iff.mpr hp₀),hν⟩
    apply (mul_le_mul_of_nonneg_right hv' (sq_nonneg (eaves su E.L x))).trans; apply le_trans _ (h₂ _ hi hQ.one); change _* _ ≤ _* _; unfold tollS; gcongr <;> first| exact hQ.primary| have hv:=‹Rates M η›.hl; positivity
end YM.QCD.Fount
#print axioms YM.QCD.Fount.limelitW
