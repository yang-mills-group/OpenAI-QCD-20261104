import YM.QCD.Garden.Cube

/-! # inheritance. fixed beds & gauges, stationary and prechoice quantitative. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m:ℕ} {P:Flight j k}{D E:Bed}{Z:Towers P.L}{I:Type}{W:I→Bloom m}
local notation "U₀"=> tray P (psi D E Z) W
def pot (P: Flight j k)(D E:Bed)(Z:Towers P.L)(W:I→Bloom m): Fruited (Tin P m I)→Bloom m:= frosting (tray P (psi D E Z) W)

variable {c f:Side}{A:Plan j}{Y: PathData su}{η u B t t' Λ M Ω Θ σ C r ω':ℝ}{K:KernelChoices}{p:Clip}{s:ℕ}{e:f.val=c.val*P.L.val} {F: Forest (Venue P K e).ratio}{ρ:Bid.Dir su c→AxisChart su F}
section
variable (hs:1≤s)(hk:0<η)(hE:E.diagonal.strip η Θ)(hD:D.dual_diag.strip η Ω)(hP: Z.Deep η Ω s) (he:Towers.Diagonal (Venue P K e) D E Z)(h : Precision.Floor D p f t t')
include hs hk hE hD hP h he
lemma rise_model (x:Cnr c)(b j i): (flux (arm su f 1 (rise F Z x))) b j i = ∑ p:PlaqAxes,∑' y, (psi D E Z none) ((sliceL P e).residue i,plaquette b) (plaquette p) y*flux (arm su c 1 x) p j ((sliceL P e).parent i+wrap c y):=by
  let G:=sliceL P e
  let T:= (installed G Z.A0); let V := arm su c 1 x
  let R := psi D E Z none
  have hz := psi_curl hk hD hE hs hP e h.diagonalInv he.stays
  have hx : arm su f 1 (rise F Z x)= Channel.rising (S:=Venue P K e) F T V := by unfold rise; rw [ContinuousLinearEquiv.apply_symm_apply]; rfl
  rw [hx]; unfold Channel.rising; change (d 1 f *ᵥ (parts su 1 _ j)) _=_
  rw [Work.F04.parts_stretch,Matrix.mulVec_mulVec,extracted,Matrix.mul_add,← Matrix.mul_assoc,Exterior.closed 0,Matrix.zero_mul,add_zero, show d 1 f*T= _ from hz.symm,← Matrix.mulVec_mulVec]
  exact (output_cross G R (d 1 c *ᵥ (parts su _ V j)) (Bloch.Row.rights _ _ (psi_strip hk hD hE hs hP none) hk.le) (plaquette b) i).trans (plaqEquiv.sum_comp _).symm

variable {X: (i:Side)→ Grid i → Sheet i} (hy:Vital X) (hx:Vital (dust W)) (hp:Critical F p Y ρ)(ht:Guessed F (installed (Venue P K e).ratio Z.A0) ρ)
local notation "Y₀" => windows P K e (X f) A W F ρ
include hy hx hp ht
lemma noble_fruit (hw:Fractal W σ M) (hr:Fractal U₀ u Λ) (hσ:0<σ)(hu:0<u)(ha:ContDiffAt ℝ ω (Y₀) 0)(hH:Noble Y₀) (hj:4≤j)(hq:4≤k):
    Tender Y₀ (castF (dust (pot P D E Z W) c)) (m+1) :=by
  unfold pot; rw [coined_inv hr]; apply donate hH; apply agree_test hH
  have hL : ContDiffAt ℝ ω (castF (dust (tray P (psi D E Z) W) c)) 0:= serenity hr hu
  refine ⟨rays_nil (ha.sub hL|>.analyticAt) ?_,ha,hL⟩
  intro i
  have hm:= rise_model (F:=F) hs hk hE hD hP he h i
  have hi := tray_model hk.le (psi_strip hk hD hE hs hP none) hm A hj hq hw hr
  let L:= sunrise hr i
  have hrX:= per_window (A:=A) hp (hy.1 _) ((hy.add hx).1 f) ht hσ hw i
  rw [← hi] at hrX
  have hv:= hrX.sub L; simp only [sub_self,← smul_sub] at hv; exact hv
end

/-- Price posting preL. Fit same width by L≥1+m. -/
lemma panPrior (η Ω Θ : ℝ) (hη:0<η) (hj:4≤j)(hk:4≤k) (m:ℕ) (hh:0<m) (hm:0≤Ω)(hM:0≤Θ):
    ∃ δ c:ℝ,0<δ∧0≤c ∧ ∀ (σ C:ℝ) (P:Flight j k)(hσ : 0<σ)(hr:σ≤δ)(I:Type)(W:I→Bloom m)(D E:Bed)(Z:Towers P.L)(s:ℕ),
    1+m≤P.L.val →1 ≤ s → D.dual_diag.strip η Ω → E.diagonal.strip η Θ → Z.Deep η Ω s → Fractal W σ C →
     (∃ y:ℝ, Fractal (tray P (psi D E Z) W) (σ*(1+m)) y) ∧ Fractal (pot P D E Z W) σ (c/(P.L.val:ℝ)^(2*m-1)*C) :=by
  obtain ⟨t,A,ht,ha,H⟩:= pack_funds hj hk
  let M:ℝ:=1+m
  have hv : 1≤ M:=le_add_of_nonneg_right (by positivity); have hp : 0 < M:=zero_lt_one.trans_le hv
  let w:=min η t
  have hu : 0<w:=lt_min hη ht
  let T:= psiPrice Ω Θ; have hT : 0≤T:=by unfold T psiPrice; positivity
  let B:=bouquet A T w m; have hb : 0≤B:=by unfold B bouquet; positivity
  let c:=ceiling w m B
  refine ⟨w/(M*M),c,by positivity,mul_nonneg (Real.exp_pos _).le hb, fun σ C P hs hr I W D E Z s hF hi hD hE hZ hh'=>?_⟩
  have hC:= (tsum_nonneg fun i=>frc (W i) σ).trans hh'.bill
  have hw:= (le_div_iff₀ (mul_pos hp hp)).1 hr
  have hd : σ*M*M ≤ w:=by rwa [mul_assoc]; -- inspect
  have hx : σ*M≤w:= (le_mul_of_one_le_right (mul_nonneg hs.le hp.le) hv).trans hd
  have heq : Row.strip (psi D E Z none) (σ*M) (T/(P.L.val:ℝ)^2):=fun i j=> ((psi_strip hη hD hE hi hZ none) i j).mono (hx.trans (min_le_left ..)) le_rfl
  have hfit : σ*M ≤ σ*P.L.val:=mul_le_mul_of_nonneg_left (by unfold M; exact_mod_cast hF) hs.le
  let L:ℝ:= P.L.val
  have hn := tray_funds hh' (mul_nonneg hs.le hp.le) hfit ha hT hh (fun i=> ⟨((H P i).1.mono (hx.trans (min_le_right ..)) le_rfl), ((H P i).2.mono (hd.trans (min_le_right ..)) le_rfl)⟩) heq
  refine ⟨⟨_,hn⟩, reduction (coined σ hs.le hn le_rfl) hs.le le_rfl ?_⟩
  have hA:0≤ L:= (side_pos _).le
  unfold c ceiling; rw [div_mul_eq_mul_div, div_mul_eq_mul_div,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (pow_nonneg hA _)
  have hB : 0≤bouquet A T (σ*M) m:=by unfold bouquet; positivity
  have hc : Real.exp (σ*M*(2*m))≤Real.exp (w*(2*m)):=by gcongr
  have hL : bouquet A T (σ*M) m ≤ B:=by unfold B bouquet; gcongr
  linarith only [mul_le_mul hc (mul_le_mul_of_nonneg_right hL hC) (mul_nonneg hB hC) ((Real.exp_pos _).le)]
end YM.QCD.Garden
