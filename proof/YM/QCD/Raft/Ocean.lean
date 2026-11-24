import YM.QCD.Raft.Class

/-! # unit leg probe transfer distortion limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi Asymptotics
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace ComplexConjugate
variable {c f : Side}{j k N:ℕ}{Κ: KernelChoices}{n:Side}{F: Next.Free.Flight j k}{H V: Bed}{T:Towers F.L}{X Y:ℕ→Side}{η C D M W:ℝ}
variable (h:Signal X Y H V T η C D N) {a: su.Color}{P:∀ i:ℕ,Cnr (Y i)→ℝ} (hp:∀ i,Loves (P i))
def Trims (P:Cnr n→ℝ)(D:ℝ)(a:su.Color):=∀ (p:Site n)(b:Aim),|scoreM P a (vw p b)|≤D*cap n*‖b‖^2
lemma cap_o (g:Ratio c f): cap f=(g.count.val:ℝ)^4*cap c:=by rw [cap,cap,site_card,site_card,g.exact_size]; norm_cast; ring
lemma studs (g:Ratio c f)(L T t:ℝ)(hp: t=Pearl.beamH c)(hv:|T| ≤ L*cap f): |T/densityP c| ≤ (g.count.val:ℝ)^4*L/t^2:=by
  rw [abs_div,abs_of_pos (density_pos _)]; refine le_trans (div_le_div_of_nonneg_right hv (density_pos _).le) (le_of_eq ?_); subst t; rw [densityP,cap_o g]; field_simp [(Pearl.beamP _).ne', (cap_pos _).ne']

include h
lemma floats (l:Site F.L)(hl:l≠0)(b:Aim) (he : ∃ W,∀ᶠ i in atTop,Trims (P i) W a): Tendsto (fun i=> scoreM (P i) a (vw (burstsG h i l) (stone T b l (pulseG X i))) / densityP (X i)) atTop (𝓝 0) :=by
  obtain ⟨W,H⟩:=he; let c(t:ℝ):= stone T b l t; let B(i:ℕ):= ((pulseG X i:ℂ))⁻¹ • c (pulseG X i)
  have hp : Tendsto (fun i=> (F.L.val:ℝ)^4 * W * ‖B i‖^2) atTop (𝓝 0):= by
    simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,mul_zero] using! (((vanished h l hl b).norm.pow 2).const_mul ((F.L.val:ℝ)^4*W))
  apply squeeze_zero_norm' ?_ hp; filter_upwards [H] with i hi
  let u:= c (pulseG X i)
  let t:= pulseG X i
  have hz:0<t:=Pearl.beamP _
  let g:=Ratio.mk F.L (h.sizes i)
  have hx:= hi (burstsG h i l) u
  refine (studs g (W*‖u‖^2) _ t rfl (hx.trans_eq ?_)).trans_eq ?_
  · ring
  change _=_ * ‖((t:ℂ))⁻¹ • u‖^2; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hz.le]; field_simp; dsimp only [g]; ring
include hp
lemma oceanH (ht: V.metric.strip η M)(hx:∀ i,Precision.Inputs (Orbit.Venue F Κ (h.sizes i)) (installed (Orbit.Venue F Κ (h.sizes i)).ratio T.A0) (H.metric.acts (Y i)) (V.metric.acts (X i))) (he : ∃ W,∀ᶠ i in atTop,Trims (P i) W a)(hc : ∃ d W:ℝ,∀ᶠ i in atTop,|readP (P i) a -d*Real.log (Y i).val|≤W):
    Tendsto (fun i=> scoreM (P i) a (expandG h i (pointT (X i) 1)) /densityP (X i)-readP (P i) a) atTop (𝓝 0):=by
  obtain ⟨d,W,hW⟩:=hc; let A:= univ.erase (0:Site F.L); let y l i:=scoreM (P i) a (vw (burstsG h i l) (stone T (sun 1) l (pulseG X i))) / densityP (X i)
  have hi: Tendsto (fun i=> ∑ j∈A,y j i) atTop (𝓝 0):=by simpa only [sum_const_zero] using tendsto_finsetSum _ (fun i hj=> floats h i (ne_of_mem_erase hj) (sun 1) he)
  obtain ⟨D,hD⟩:= sloping h ht hx
  have hz := (hD.mul (catches h (fun i=>readP (P i) a) d hW)).add hi; rw [mul_zero,zero_add] at hz; apply hz.congr'
  filter_upwards [fan_low (sun 1) h] with i H
  let p:= bright T (sun 1) (pulseG X i)
  let v:= (lowS (F:=F) T (pulseG X i)-1)/pulseG X i; let L:ℝ:= F.L.val; let g:=Ratio.mk F.L (h.sizes i)
  change v * (pulseG X i*readP (P i) a)+∑ j∈A,y j i= _; unfold pointT; rw [stoning _ (sun 1) i _ (hp i) a,sum_div]; change _=(∑ j,y j i)- _
  rw [← Finset.add_sum_erase _ (fun j=>y j i) (mem_univ 0)]
  have hm : p (coord 0)=0:=if_pos rfl
  have hx:y 0 i= lowS (F:=F) T (pulseG X i) * readP (P i) a:= by
    rw [show y 0 i=scoreM (P i) a (vw (step 0) p) / densityP (X i) from ?_]; swap; · unfold y; rw [(zero_stone h i).2,H]
    rw [sting_boot (hp i) _ hm,readP, density_ratio g]; unfold lowS; change _= (sting p*_)*_; field_simp [(density_pos _).ne']; rfl
  rw [hx]; unfold v A; field_simp [(Pearl.beamP _).ne']; ring
end YM.QCD.Raft
