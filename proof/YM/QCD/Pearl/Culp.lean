import YM.QCD.Pearl.Elegant

/-!
# conditioned charge domain for joint effects
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free Para
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {j:ℕ}{p k:Momentum} {r ρ C c ε : ℝ} {F : Momentum→Para}

lemma turn_m (A:Para):‖turn A‖=‖A‖:=by simp [turn,Prod.norm_def]
def script :Para→L[ℂ] Bundle:= Para.signal.toContinuousLinearMap
def vase (F:Momentum→Para)(p:Momentum):=model (reciprocalP (F p))
namespace Pinch

def city (r C:ℝ):=4*baseK r C*Real.pi+2
def labor (r C:ℝ):= C/(r/2/2)
structure Bright (r c C ε : ℝ):Prop where
  seed : 0<ε
  span : ε≤1
  norm : ε*Real.pi≤r/2/2
  serves : (5*(labor r C)*ε)*(city r C+city r C)≤c/2

def purse (r c C:ℝ):= ‖script‖*(city r C)/(c/2)
variable (h:Pinch F r c C)(e : Bright r c C ε) (hk:k∈ baseCube)(h0 : k≠0)
include h
lemma gilt : 0<city r C:=by unfold city; have ht:=h.boundK; positivity
lemma cost_q : 0≤purse r c C:=by unfold purse; have ht:=h.gilt; have hs:=h.hc; positivity
lemma source (R:ℝ) (hR:0<R):∃ ε, Bright r c C ε∧ ε≤ R:=by
  let H:= 5*labor r C*(city r C+city r C)
  have ht : 0<H:=by unfold H labor; have hi:=h.gilt; have hu:=h.hr; have he:=h.hC; positivity
  let Z:=min (r/2/2/Real.pi) (c/2/H)
  let ε:= min (min 1 R) Z
  have h1:0<Z:= by unfold Z; have hh:=h.hr; have ht:=h.hc; exact lt_min (by positivity) (by positivity)
  have h₂ : ε≤Z:=min_le_right ..
  refine ⟨ε, ⟨lt_min (lt_min one_pos hR) h1, (min_le_left ..).trans (min_le_left ..), (le_div_iff₀ Real.pi_pos).mp (h₂.trans (min_le_left ..)), ?_⟩,(min_le_left ..).trans (min_le_right ..)⟩
  rw [show 5*labor r C*ε*(city r C+city r C)= ε*H by unfold H; ring]; exact (le_div_iff₀ ht).mp (h₂.trans (min_le_right ..))
include e hk h0
lemma useX (hp:p∈ball k (ε*‖k‖)): p∈cube r:= h.foil hk (ball_subset_ball (((mul_le_mul_of_nonneg_left (cap_base hk) e.seed.le).trans e.norm).trans (half_le_self (half_pos h.hr).le)) hp)
lemma friend : k ∈ ball k (ε*‖k‖):= mem_ball_self (mul_pos e.seed (norm_pos_iff.mpr h0))
lemma nearby (hp:p∈ball k (ε*‖k‖)): c/2*‖k‖^2≤ ‖quad (F p)‖:=by
  have hpL: ‖F p‖ ≤ city r C*‖k‖ := h.Far (h.useX e hk h0 hp) hk (h.near hp e.span)
  have hkL: ‖F k‖≤ city r C*‖k‖:=h.Far (h.useX e hk h0 (h.friend e hk h0)) hk (by linarith [norm_nonneg k])
  have hg:=h.gilt
  have he : ‖F p-F k‖≤labor r C*(ε*‖k‖):= h.leagueX hp hk ((mul_le_mul_of_nonneg_left (cap_base hk) e.seed.le).trans e.norm)
  have hh : ‖F p+F k‖≤(city r C+city r C)*‖k‖:= (norm_add_le ..).trans ((add_le_add hpL hkL).trans_eq (by ring))
  have ht:‖quad (F p)-quad (F k)‖ ≤ c/2*‖k‖^2:=by
    rw [bean]; apply (bean_bill _ _).trans
    have hy := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤5); apply (mul_le_mul hy hh (norm_nonneg _) ((by positivity : 0≤ 5*‖F p-F k‖).trans hy)).trans
    exact le_trans (le_of_eq (by ring : 5*(labor r C*(ε*‖k‖))*((city r C+city r C)*‖k‖)= (5*labor r C*ε*(city r C+city r C))*‖k‖^2)) (mul_le_mul_of_nonneg_right e.serves (sq_nonneg _))
  rw [norm_sub_rev] at ht; linarith [ (norm_sub_norm_le (quad (F k)) (quad (F p))).trans ht,h.phase k hk]
lemma validly (hp:p∈ball k (ε*‖k‖)):0 < ‖quad (F p)‖:= (mul_pos (half_pos h.hc) (pow_pos (norm_pos_iff.mpr h0) _)).trans_le (h.nearby e hk h0 hp)
lemma protectedV (hp:p∈ball k (ε*‖k‖)) : DifferentiableAt ℂ (vase F) p ∧ ‖vase F p‖ ≤ purse r c C / ‖k‖:=by
  let M:=F p; have ht:= h.validly e hk h0 hp; have hkL:=h.hD p (h.useX e hk h0 hp)
  unfold vase reciprocalP; constructor
  · have hf:DifferentiableAt ℂ (quad ∘ F) p := ((show Differentiable ℂ quad from by unfold quad; fun_prop) (F p)).comp _ hkL
    have hu: DifferentiableAt ℂ (turn ∘ F) p:= ((show Differentiable ℂ turn from by unfold turn; fun_prop) (F p)).comp _ hkL
    exact script.differentiableAt.comp p ((hf.inv (norm_pos_iff.mp ht)).smul hu)
  have hk1:= norm_pos_iff.mpr h0; have hc:= h.hc; have hv : c/2*‖k‖^2≤ ‖quad M‖:= h.nearby e hk h0 hp
  have hpL: ‖F p‖ ≤ city r C*‖k‖ := h.Far (h.useX e hk h0 hp) hk (h.near hp e.span)
  apply (script.le_opNorm _).trans; rw [norm_smul,norm_inv,turn_m];
  refine (mul_le_mul_of_nonneg_left (mul_le_mul ((inv_le_inv₀ ht (by positivity)).mpr hv) hpL (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans_eq ?_; unfold purse; field_simp

def proofD (r c C:ℝ):= purse r c C * (4*‖script‖*baseK r C) * purse r c C
lemma adjacent (hS: Pinch shaft r c C) (hp:p∈ball k (ε*‖k‖)): ‖vase F p-vase shaft p‖ ≤ proofD r c C:=by
  have hh:= h.protectedV e hk h0 hp; have hH:= hS.protectedV e hk h0 hp
  let A:= model (F p); let B:= model (shaft p)
  let P:= vase F p; let Q:= vase shaft p
  have he : P*A=1:= reciprocates _ (norm_pos_iff.mp (h.validly e hk h0 hp)); have hi : B*Q=1:=returned _ (norm_pos_iff.mp (hS.validly e hk h0 hp))
  have hr:0 ≤‖script‖:=norm_nonneg script; have hw:=h.boundK; have hC:=h.cost_q
  have hK:0<‖k‖:= norm_pos_iff.mpr h0
  have hpD: ‖B-A‖≤4*‖script‖*baseK r C *‖k‖^2:=by
    rw [norm_sub_rev,show A-B=script (F p-shaft p) from (map_sub script (F p) (shaft p)).symm];
    apply (script.le_opNorm _).trans; exact (mul_le_mul_of_nonneg_left ((h.lifting (h.useX e hk h0 hp)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h.near hp e.span) _) hw.le)) hr).trans_eq (by ring)
  change ‖P-Q‖≤_; rw [show P-Q= P*(B-A)*Q by rw [mul_sub,sub_mul,mul_assoc P B,hi,mul_one,he,one_mul]]
  have hp' := mul_le_mul hh.2 hpD (norm_nonneg _) (by positivity)
  refine (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le P _).trans hp') hH.2 (norm_nonneg _) (by positivity)).trans_eq ?_); unfold proofD; field_simp
end Pinch
end YM.QCD.Pearl
