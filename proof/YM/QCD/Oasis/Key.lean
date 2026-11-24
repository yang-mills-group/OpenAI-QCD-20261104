import YM.QCD.Oasis.Play
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
variable {N : ℕ}{u v d a γ ν Θ r s η' : ℝ}
open Cove Golden
variable (W':Positions (Uniform.Primary c G)→ F.Slice G→EvenA c N)
variable {l:ℕ}
-- supplies: all-field envelope plus weighted sensitivity Zest witness.
structure Corn (W':Positions (Uniform.Primary c G)→F.Slice G→EvenA c N)(ρ: Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G))(D U W p a b s A:ℝ)(j:ℕ) (β:ℝ):Prop where
 blinks : ∃ K: Poll.Body (Precision.Key F G) → EvenA c N, Cello (nudge (G:=G) (N:=N) F W' ρ) K a b D U (j+2)
 songs :∀ x: Positions (Uniform.Primary c G), ‖x‖<U→ RG.Envelope (W' x) ∧ (∀ i,‖W' x i‖ ≤ W) ∧ ∃ C:F.Slice G→ℝ, RG.Envelope C ∧ (∀ i,Brush j (p*C i) 1 (fun x=> W' x i) x) ∧ (∀ i,|C i|≤ A) ∧ ∀ i: F.Slice G,i∈ staying F (ρ x) (gStep β) D (V x) → |C i|≤ s
-- enough for Zest: every hQ and C uniformly W incl fees. automatically.
lemma zoning {U a b p d w D A:ℝ}(h:Corn W' (Lapis.orbit F ρ) D U w p a b d A l β)(hv:0≤p){z: Positions (Uniform.Primary c G)}(hx:‖z‖<U) : Zest (fun i y=> W' y i) z l:=by
    obtain ⟨Mq,hQ,hr,he,ht⟩:= (h.songs z hx).2.2
    have hN:0≤p*A:= ((hr (1:F.Slice G)).nonneg).trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (he _)) hv)
    refine ⟨p*A,hN,?_⟩; filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with z hz -- lost h
    obtain ⟨q,hp,ht,he,_⟩:= (h.songs z hz).2.2; exact fun i=> (ht i).climb (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (he _)) hv) le_rfl
-- bookkeeping predictors: r=r' LARGE, D small. measured short Golf M OTHER. Λ stocks. whole actual
variable {X z : Positions (Uniform.Primary c G)} (h:Intake P Y x (Pane.virgin Y Ω β)) (he:LocalRatio η) (hp:LawP Y A Ω F ρ k L η B W x β X)
variable (hD:0≤D)(hc:D≤ wick G L B x){d' I m u' W'' : ℝ}
local notation "Δ"=>closedBall (0:R) D
local notation "Y'"=>Sol (N:=N) β F Y Ω W'
local notation "C'"=>nudge (G:=G) (N:=N) F W' μ
local notation "rE"=> (fun z=>ratify Φ ψ μ T D (ZB,z))
def ace :ℝ:=Real.exp (-1)*(1/2)
lemma ace_pos : 0<ace:=by unfold ace; positivity
variable (hX:Golf (Lapis.table F k Y.up Y.high) (mist F η Y.up) (Lapis.orbit F ρ) (gram F Y.up Y.high ρ k) (l+1+2) D (eaves G L x) (eaves G L x) m)
variable (hW:Corn W' (Lapis.orbit F ρ) D (eaves G L x) w p u v d a (l+1) β)
local notation "Q'"=>humV Φ ψ μ T C' D
local notation "g'"=>sweep (T 0)⁻¹
variable (hF:Lantern.fee (l+1+2) m D*eaves G L x≤1)(hv:∀ x∈ Set.Icc (-1:ℝ) 1, Brush (l+1+2) Z 1 Real.exp x) (hh:∀ x∈Set.Icc ace (Real.exp 1), Brush (l+1) I 1 (fun i:ℝ=>i⁻¹) x)
local notation "Ψ"=> (fun x=> (rE x)⁻¹ • Q' (ZB,x))
local notation "rH"=> barley M r' W''
noncomputable abbrev ΨCost (j:ℕ)(m D I a u v:ℝ):= let Z:=mast u v m D a (j+2); clump j (clump (j+2) (Lantern.fee (j+2) m D) a) I*Z*2^j
include W' hp hD hc h he hX hW hF hv hh
lemma warrant (ht: (g').real (closedBall 0 D)ᶜ ≤ W'')(hm: W'' ≤ 1/2) (hx:‖z‖<eaves G L x) : Brush (l+1) ((gStep β)^2*ΨCost (l+1) m D I Z u v) (eaves G L x)⁻¹ Ψ z ∧ ace ≤ rE z ∧ ‖Q' (ZB,z)‖ ≤ (gStep β)^2 * mast u v m D Z (l+1+2) :=by
   let Z':= ΨCost (l+1) m D I Z u v; let H':= mast u v m D Z (l+1+2); let f:= Q'; let r:=H; let g:=Ψ
   obtain ⟨K,hK⟩:= hW.blinks
   have he:=hp.habit; have hb := he.2.1; have hβ:=h.positive; have hz := (Fare.gS β hβ).1; have hr:‖ZB‖<H:=by rw [Real.norm_of_nonneg hz.le]; exact hb
   have hα : 1/2 ≤ (g').real Δ:=by
      have ht₁:(g').real (Δᶜ) =1-(g').real Δ:=by rw [measureReal_compl measurableSet_closedBall,probReal_univ]
      rw [ht₁] at ht; linarith
   have hV:= lineR hX hK hF hv z hx hz hb
   have hc : 0≤Z:= (hv 0 (by simp)).nonneg
   have hΦ := burs D hX (x:=(ZB,z)) hx hr (by omega) (by simpa using hF) hv hc; have hT:= temperature D hX (x:=(ZB,z)) hx hr (by omega) (by simpa using hF) hΦ.2 hα
   refine ⟨?_,hT.1,hV.bound⟩
   have hw := composite ((markArc hΦ.1).smaller (by omega : l+1≤ l+1+2)) (hh (rE z) hT)
   let A₀:=clump (l+1) (clump (l+1+2) (Lantern.fee (l+1+2) m D) Z) I
   have hf:= (Golden.brushR (hw.climb le_rfl ((one_le_inv₀ hX.pos).mpr hX.small)) hV)
   refine ⟨hf.smooth, hf.pos |> (fun _=> inv_nonneg.mpr hX.pos.le),fun i hi=>?_⟩
   apply (hf.order i hi).trans
   change (A₀*((ZB)^2*H')) * (r⁻¹+r⁻¹)^i ≤ (ZB)^2*(A₀*H'*2^(l+1))*r⁻¹^i
   rw [← two_mul,mul_pow]; have h₁: (A₀*(ZB^2*H'))* r⁻¹^i ≥ 0:=mul_nonneg hf.nonneg (pow_nonneg (inv_pos.mpr hX.pos).le _); linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ)≤2 from by norm_num) hi) h₁]
end YM.QCD.Oasis
