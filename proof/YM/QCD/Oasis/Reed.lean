import YM.QCD.Oasis.Sling
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {P : Teller G} {c f : Side} {S : StepData c f} {x W K y σ C e β B v' b D M' p w Z: ℝ} {n:ℕ}
variable {F : Forest S.ratio} {Y : Tube G S} {k : S.Choices} {A : Before G σ C S.patch.J S.kernel (n+3)} {ρ : Bid.Dir G c→AxisChart G F}{η:ChartRatio G}{Ω : BudgetPoint}
local notation "M" => A.tables Y.high S.patch
local notation "μ" => Lapis.orbit F ρ
local notation "R"=>Poll.Body (Precision.Key F G)
local notation "Ys"=>Positions (Uniform.Primary c G)
local notation "T"=> Lapis.gram F Y.up Y.high ρ k
local notation "ψ"=> mist F η Y.up
local notation "Φ"=> Lapis.table F k Y.up Y.high
local notation "V" => (fun (x: Ys)=> represent (tint G _ x))
local notation "H"=>eaves G L x
local notation "r'"=>wick G L B x
local notation "R₀"=>Pane.virgin Y Ω β
local notation "ZB"=>gStep β
lemma cash {s t u v z w :ℝ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](hs:0 < s)(he:0<u)(hv:u ≤ v)(hr:s*v≤ t)(h:t - s*v ≤ s*z) (p q:E)(hz: ‖p-s • q‖ ≤ s*z*w)(hk:‖q‖≤ w) : 0 < t ∧ ‖t⁻¹ • p- v⁻¹ • q‖ ≤ z/u *w + z/u^2 *w :=by
    have hV:0<v:=he.trans_le hv; have ht:0<t:=(mul_pos hs hV).trans_le hr; have hq: s/t ≤ 1/u:=by apply (div_le_div_iff₀ ht he).mpr; rw [one_mul]; exact (mul_le_mul_of_nonneg_left hv hs.le).trans hr
    have hZ:0≤ z:=nonneg_of_mul_nonneg_right ((sub_nonneg.mpr hr).trans h) hs; have hh:0≤w:=(norm_nonneg _).trans hk
    have h₁:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hZ) hh)
    have hv' : t⁻¹*s≤ v⁻¹:=by rw [mul_comm,← div_eq_mul_inv, ← one_div]; rw [div_le_div_iff₀ ht hV]; rwa [one_mul]
    have h₀ : (v⁻¹-t⁻¹*s)*v*t=t-s*v:=by field_simp
    have h₂ : v⁻¹-t⁻¹*s≤ (s/t)*z*v⁻¹:=le_of_mul_le_mul_right ?_ (mul_pos hV ht)
    rotate_left; · rw [← mul_assoc,h₀]; convert! h using 1; field_simp
    refine ⟨ht,?_⟩
    rw [show t⁻¹ • p-v⁻¹ • q=t⁻¹ • (p-s • q)+(t⁻¹*s-v⁻¹) • q by rw [smul_sub,← mul_smul,sub_smul]; abel]; apply (norm_add_le ..).trans; rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hv'),neg_sub]; refine add_le_add ((mul_le_mul_of_nonneg_left hz (inv_pos.mpr ht).le).trans ?_) ((mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hv')).trans (mul_le_mul_of_nonneg_right (h₂.trans ?_) hh))
    · simp only [div_eq_mul_inv] at *; linarith only [h₁]
    calc _ ≤ 1/u*z*u⁻¹:=mul_le_mul (mul_le_mul_of_nonneg_right hq hZ) (inv_anti₀ he hv) (inv_nonneg.mpr hV.le) (by positivity)
         _ = _ :=by field_simp

variable (h:Intake P Y x (Pane.virgin Y Ω β)) (he:LocalRatio η)
local notation "f₀"=>endoP β F Y Ω
variable {X z:Positions (Uniform.Primary c G)} (hp:LawP Y A Ω F ρ k L η B W x β X)
local notation "g"=> ballots Φ ψ μ T D
local notation "G'"=>sweep (T 0)⁻¹
local notation "m'"=> (fun z=> solar F η β* Real.exp (-coverLog F Y η k ρ β z))
variable (hD:0 ≤ D)(hc:D ≤ wick G L B x)(hx : ‖z‖< eaves G L x)(hy:‖z-X‖ ≤ furl G L x)
local notation "S'"=> staying F (μ z) ZB D (V z)
def barley (A:ChartPrices)(r'₀ a:ℝ):= a*Real.exp 1+Real.exp (-(A.gap*r'₀^2/4)/2)
include hp hD hc h he hx hy
variable {a d u:ℝ}
local notation "D'"=>tramp Y Ω β z
local notation "Y'"=>ratify Φ ψ μ T D (ZB,z)
local notation "T'"=>barley M r' a
lemma amber (hi:1 ≤ n) (hf:Lantern.fee n W (wick G L B x)*eaves G L x≤1)(ht : (G').real (closedBall 0 D)ᶜ ≤ a):
    D'-m' z *Y' ∈ Set.Icc 0 (m' z * T'):= by
       let m:=F.order G; have hz:= amt F Y Ω β x P h (V z); have hβ:0 < β:=h.positive; have hu: 0 < m' z:=mul_pos (Fare.sun F η β hβ he) (Real.exp_pos _)
       refine ⟨?_,?_⟩
       · let Y₁:= timber' h he hp hD hc hx hy; rw [sub_nonneg, ← Y₁, tramp,hz.2,← integral_add_compl (staying_meas F _ _ _ _) (hz.1.integrable m)]; exact le_add_of_nonneg_right (setIntegral_nonneg ((staying_meas F _ _ _ _).compl) fun i _=> rays F Y Ω β i z) -- binder shadow marker
       have hv :=midday h hp hD hc hx hy hi hf ht; have hY:= hp.habit.2.2.2 z hx hy|>.2
       change (S.push β (R₀).eval ((V) z))- m' z*Y' ≤ m' z *(T'); rw [barley,mul_add]
       exact by linarith only [mul_le_mul_of_nonneg_left hv hu.le,hY]
lemma glowTail (u:F.Slice G→ℝ)(hp': RG.Envelope u)(ht:∀ i,|u i| ≤ w)(hm:∀ i∈ S', |u i| ≤ d)(hw:0≤w)(hf:0≤d)(hi:1 ≤ n) (hk:Lantern.fee n W (wick G L B x)*eaves G L x≤1)(hQ : (G').real (closedBall 0 D)ᶜ ≤ a)
   (hY:b≤ Y')(hb: 0<b): ∫ i, f₀ z i * u i ∂F.order G ≤D'*(T'/b*w+d):=by
     let s:=m' z; have hu:= amber h he hp hD hc hx hy hi hk hQ; have hβ:0 < β:=h.positive; have hs : 0<s:=mul_pos (Fare.sun F η β hβ he) (Real.exp_pos _); have ht':0 < Y':=lt_of_lt_of_le hb hY
     have hS : s≤ D'/b:= (le_div_iff₀ hb).2 ((mul_le_mul_of_nonneg_left hY hs.le).trans (sub_nonneg.mp hu.1))
     have hx' := amt F Y Ω β x P h (V z); let X:=F.order G; let f:= f₀ z; have hc'(i) :0 ≤ f i:= Fare.rays F Y Ω β i z; have hy': D'=∫ i, f i ∂X:=hx'.2
     let Δ:= S'; have hΔ:MeasurableSet Δ:=staying_meas ..; have he : Integrable f X:=hx'.1.integrable X; have hΩ : Integrable (fun i=> f i*u i) X:= Beam.envDash u hp' f he
     have hΔ':(∫ i in Δ, f i ∂X)= s*(Y'):= timber' h ‹LocalRatio η› hp hD hc hx hy; have hh : (∫ i in Δᶜ,f i ∂X)=D'- s*Y':=by rw [hy',← integral_add_compl hΔ he,hΔ',add_sub_cancel_left]
     have he': 0 ≤ T':= nonneg_of_mul_nonneg_right (hu.1.trans hu.2) hs
     have hA: (∫ i in Δ, f i*u i ∂X) ≤ (∫ i in Δ,f i*d ∂X) := setIntegral_mono_on hΩ.integrableOn (he.integrableOn.mul_const _) hΔ fun x hx=> mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hm x hx)) (hc' _)
     have hX: (∫ i in Δᶜ, f i*u i ∂X) ≤ (∫ i in Δᶜ, f i*w ∂X) := integral_mono hΩ.integrableOn (he.integrableOn.mul_const _) (fun x=> mul_le_mul_of_nonneg_left ((le_abs_self _).trans (ht x)) (hc' _))
     rw [integral_mul_const,hΔ'] at hA; rw [integral_mul_const,hh] at hX; rw [← integral_add_compl hΔ hΩ]
     exact (add_le_add (hA.trans (mul_le_mul_of_nonneg_right (sub_nonneg.mp hu.1) hf)) (hX.trans (mul_le_mul_of_nonneg_right (hu.2.trans (mul_le_mul_of_nonneg_right hS he')) hw))).trans_eq (by ring)
end YM.QCD.Oasis
