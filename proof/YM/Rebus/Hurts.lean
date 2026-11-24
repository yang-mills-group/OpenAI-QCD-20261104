import YM.Rebus.Stems
/-! # Cyclopean.S tests. Econometric gauge Forecast moving LETTER and costs True covariance . -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Current
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Bera.Oce Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁ p₀ q₁ q₂ r' r t t' A₀ A₁ B' u u' s' σ θ η η₁ Ω' ε :ℝ}{S: StepData c f}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {T:Tube su S}{N i j n k m l B Q: ℕ}
open FreeResolvent
variable (W : Support c) (V:Directions su c) (b:Kh c) (Z₀: Web su)
variable (H H': Bed)(U':Towers S.patch.L)
variable (X₀: Myth su S H H' U' B q₁ q₂)
local notation "T0"=> view su S H H' U'
local notation "T1"=> Fruit.cones su S H H' U' B
local notation "V0"=> Fruit.curtain su S H H' U'
local notation "V1"=> Fruit.sprig su S H H' U' B
variable (h0 : Towers.Diagonal S H H' U') (u:ℝ)
variable {F:Tree.Forest S.ratio}{c':Clip}
local notation "Vh"=> increment 1 V
local notation "βv"=> karm κ' Vh
local notation "wo"=> T1 *ᵥ βv
variable (X:Coat T F)(z: Air f su)
local notation "M0"=> rose (Dh f N I)
local notation "Vr" => X.input (X.liftA β z)
local notation "zX"=> karm (gStep β) Vr
local notation "vo"=> v
local notation "Gx"=> gStep β
local notation "G0"=> κ'
-- estimates determinant.Means.True.
noncomputable def chant (r m k:ℝ) := m*(k*r+k*r^2)
noncomputable def arcV (r m d k:ℝ):= k*r*d + m*k*r^2
noncomputable def swapV (r r' v t δ k m n:ℝ):= (t*(k*r'^2+k*v)+(m*arcV r t δ k+n*chant r t k)) -- t≥|| Gx inv|| & ||λ'|| ; δ absInv slope. OK
variable {mξ d:ℝ}
section
variable (h:v≤ Z₀.radius)(hr:‖V‖≤v)(ho:0 ≤ mξ)(ht:|κ'⁻¹|≤ mξ)
include hr h ht
lemma leafW (W:Finset (Kh c)): Oce.bill (karm κ' Vh) W (chant v mξ Z₀.scale):=by
    have hp: 0 ≤ v:= (norm_nonneg _).trans hr; have he:=zero_le_one.trans Z₀.cost; exact fun i _=> (gust V i Z₀ κ' hr h).trans (mul_le_mul_of_nonneg_right ht (by positivity))
lemma linW (i:Kh c)(hm:‖(gStep β)⁻¹-κ'⁻¹‖≤d) : ‖(gStep β)⁻¹ * jet V i-karm κ' Vh i‖ ≤ arcV v mξ d Z₀.scale:=by
   let m:= κ'⁻¹; let x := Hypnos.marrow Vh (bleep i) i.2.2
   have h':0≤d:=(norm_nonneg _).trans hm
   refine (norm_sub_le_norm_sub_add_norm_sub _ (m*jet V i) _).trans (add_le_add ?_ (?_))
   · rw [← sub_mul,norm_mul, mul_comm (_*v)]; exact mul_le_mul hm (linearK V i Z₀ hr) (norm_nonneg _) h'
   unfold karm; change ‖m*jet V i-m*x‖≤_; rw [← mul_sub,norm_mul,norm_sub_rev]; exact (mul_le_mul ht (breezeK V i Z₀ hr h) (abs_nonneg _) ((abs_nonneg _).trans ht)).trans_eq (mul_assoc ..|>.symm)
omit hr h ht in
lemma rowsL {A B:Type}[Fintype B](X : Matrix A B ℝ)(w : B→ℝ)(r s:ℝ)(i:A)(he:∑ j, ‖X i j‖≤ s)(hp:∀ j,‖w j‖ ≤ r)(hr:0 ≤ r) : ‖(X*ᵥ w) i‖≤ s*r:=by
   unfold Matrix.mulVec dotProduct; exact (norm_sum_le ..).trans ((sum_le_sum (g:=fun j=> ‖X i j‖*r) (fun j _=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hp _) (norm_nonneg _))).trans (by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right he hr))
-- `include hr` accidentally.
include X₀
lemma hangW (hk:‖(gStep β)⁻¹-κ'⁻¹‖≤d)(i:Kh f): ‖(T0 *ᵥ ((gStep β)⁻¹ • jet V)-T1 *ᵥ karm κ' Vh) i‖ ≤ q₁* (arcV v mξ d Z₀.scale)+ q₂ *chant v mξ Z₀.scale:=by
    let p:=Gx⁻¹ • jet V; let q:= βv; have hp (j:Kh c): ‖(p-q) j‖ ≤ _ := linW V Z₀ h hr ht _ hk
    have hz(j:Kh c):‖q j‖ ≤ _:=leafW V Z₀ h hr ht univ j (mem_univ j); obtain ⟨hg,h,h₀⟩:= windK H H' U' X₀ i
    change ‖(T0*ᵥ p-T1*ᵥ q) i‖≤_; rw [show T0*ᵥ p-T1*ᵥ q=T0*ᵥ (p-q)+(T0-T1)*ᵥ q from by rw [Matrix.sub_mulVec,Matrix.mulVec_sub]; abel,Pi.add_apply]
    have hd:= (norm_nonneg _).trans hk; have hv:0≤v:= (norm_nonneg _).trans hr; have hJ:= zero_le_one.trans Z₀.cost; have hm:0≤ mξ:=(abs_nonneg _).trans ht
    exact (norm_add_le ..).trans (add_le_add (rowsL T0 (p-q) _ _ _ hg hp (by unfold arcV; positivity)) (rowsL (T0-T1) q _ _ _ h₀ hz (by unfold chant; positivity)))
lemma fealty (hw:T.R.A0=U'.A0)(hF:Floor H c' f η Ω') (hz0:Towers.Diagonal S H H' U')(hk:‖(gStep β)⁻¹-κ'⁻¹‖≤d)(hβ:0<gStep β)(he:X.V=increment 1 V)(hp:HaloV X W β r u' V z)(hg: r ≤ Z₀.radius)(hm:‖(gStep β)⁻¹‖ ≤ mξ)(hv:0 ≤ u') (a:Kh f)(hΨ:(RG.touched (bleep a)).image S.ratio.parent ⊆ W) :
 ‖karm (gStep β) (X.input (X.liftA β z)) a- Oce.surge (dove F) (T1 *ᵥ βv) z a‖ ≤ swapV v r u' mξ d Z₀.scale q₁ q₂:=by
    have hx:= Hypnos.totter X W Z₀ (bleep a) V z hp hΨ hg
    let J:= Hypnos.tide (route T V) (bleep a); let K:= Hypnos.tide (growSeed X z) (bleep a); let k:= a.2.2
    let Q₀:= (J+ (gStep β) • K); let a':= Hypnos.marrow Vr (bleep a)
    have hY: ‖karm Gx Vr a-Gx⁻¹ * Q₀ k‖ ≤ mξ*(Z₀.scale*r^2+Z₀.scale*u'):=by
         unfold karm; rw [← mul_sub,norm_mul]; exact mul_le_mul hm ((PiLp.norm_apply_le (a'-Q₀) k).trans hx) (norm_nonneg _) ((norm_nonneg _).trans hm)
    have hJ : Gx⁻¹ * Q₀ k=(T0 *ᵥ (Gx⁻¹ • jet V)) a+(dove F *ᵥ z.ofLp) a:=by
          rw [Matrix.mulVec_smul,wander V H H' U' hw hF hz0,foster F X,Pi.smul_apply,Fruit.peal,Fruit.peal]; change Gx⁻¹ * (J k+Gx*K k)=Gx⁻¹ * J k+K k; rw [mul_add,←mul_assoc,inv_mul_cancel₀ hβ.ne',one_mul]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (Gx⁻¹ * Q₀ k) _).trans (add_le_add hY ?_)
    rw [hJ]; unfold Oce.surge; rw [Pi.add_apply,add_sub_add_right_eq_sub]; exact hangW V Z₀ H H' U' X₀ h hr ht hk _
end
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.fealty
