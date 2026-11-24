import YM.QCD.Revolve.Fiat

/-!
# construct spin reversal and axial representatives of BLOOM
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Function Lattice Wilson Lat Kit Cost Run Rudder Finset RG Eyrie
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical
variable {n:Side}{s:Signed}{p:Spike}{g : Site n→ℂ}{k:ℕ}{C : Bloom k}

def flag (A:Spike)(h : Bundle):= wave A*h*star (wave A)
lemma flag_mu (A:Spike)(h : Bundle)(x:ℂ): flag A (x • h)= x • flag A h:=by unfold flag; rw [Matrix.mul_smul,Matrix.smul_mul]
lemma flag_gauge (u:su.El)(A:Spike)(V:Bundle): flag A (touch (colour u)*V*star (touch (colour u)))=touch (colour u)*flag A V*star (touch (colour u)):=by
  unfold flag; rw [touch_star,wave_star]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc (wave _),← (interlace ..).eq]; simp only [Matrix.mul_assoc]; rw [(interlace ..).eq]
lemma pays_five (A:Spike)(h:A∈unitary _)(V:Bundle): ‖flag A V‖≤ ‖V‖:=by
  have H:= rotation_price (wobble A h); apply (norm_mul_le ..).trans
  rw [norm_star]; exact (mul_le_of_le_one_right (norm_nonneg _) H).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) H))
def signW (r:Fin k→ℝ):ℂ:=↑(∏ j,r j)
lemma signal (r:Fin k→ℝ)(h:∀ j,|r j|=1):‖signW r‖=1:=by rw [signW,Complex.norm_real,Real.norm_eq_abs,abs_prod]; simp_rw [h,prod_const_one]
def quest (A: Bloom k)(s : Signed)(P: Spike)(w:Fin k→Slot)(r:Fin k→ℝ): Bloom k:= ⟨A.tail.map (·.rotate s),w,fun i=>signW r • flag P (A.coeff i)⟩
lemma quest_hues (P: Spike)(r)(w)(v) : (quest C s P w r).hues v= flag P (C.hues fun i=> r i • v i):=by
  unfold Bloom.hues quest flag; rw [Matrix.mul_sum,Matrix.sum_mul]; apply sum_congr rfl; intro a _; simp only [PiLp.smul_apply, smul_eq_mul, prod_mul_distrib,Complex.ofReal_mul, Matrix.mul_smul, Matrix.smul_mul,smul_smul]; unfold signW; rw [mul_comm]
lemma quest_rot (P: Spike)(r)(w)(he:C.Spins): (quest C s P w r).Spins:=by intro u v; rw [quest_hues,quest_hues]; simp_rw [← map_smul (su.adjoint u)]; rw [he]; exact flag_gauge ..
lemma quest_priced {r w}(u:ℝ)(ht: 0≤u)(hp : Swing s p)(h:∀ i,Mint s (C.petals i) (w i) (r i)): (quest C s p w r).paid u≤ Real.exp (u*(2*k)) * C.paid u:=by
  have hm : (quest C s p w r).span ≤ C.span+2*k:=by
    unfold quest Bloom.span; dsimp only; rw [List.length_map]; have he := sum_le_sum (s:=univ) fun i _=> (h i).offer
    rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he; omega
  have hv : (quest C s p w r).price ≤ C.price:= Finset.sum_le_sum (fun i _=> show ‖signW r • flag p (C.coeff i)‖≤‖C.coeff i‖ from by rw [norm_smul,signal r (fun i=>(h i).price),one_mul]; exact pays_five p hp.unit _)
  unfold Bloom.paid; rw [← mul_assoc,← Real.exp_add]; apply mul_le_mul ?_ hv (Bloom.price_nn ..) (Real.exp_pos _).le
  have ht' : (↑(quest C s p w r).span:ℝ)≤C.span+2*k:=by exact_mod_cast hm
  apply Real.exp_monotone; nlinarith
lemma quest_score (b : Site n) {t t':Site n}{r w}(hp : Swing s p)(hg:Glare s t t' b g)(h:∀ i,Mint s (C.petals i) (w i) (r i))(U:Grid n):
    (quest C s p w r).tonic t' U=aura (star (hues b s g p)) (C.tonic t (pull s b U)):=by
  let F:= hues b s g p
  let A:=quest C s p w r
  have he : F* rides (Equiv.refl _) (A.taste U)=rides (Equiv.refl _) (C.taste (pull s b U))*F:=by
    unfold F hues; rw [ride_mul,ride_mul, Equiv.refl_trans,Equiv.trans_refl]; congr 1; funext i; unfold Bloom.taste
    have hx j:(C.petals j).atSite (pull s b U) i=r j • (w j).atSite U (affine s b i):=by unfold Slot.atSite; rw [expandAt_pull]; exact (h j).returnF _
    unfold A; simp only [hx, Matrix.smul_mul,Matrix.mul_smul,Equiv.refl_apply, quest_hues]; -- quest? A
    have hz: star p*p=1:=hp.unit.1
    unfold flag; rw [wave_star]; simp only [← Matrix.mul_assoc, wave_mul]; rw [hz,wave_one,Matrix.one_mul]; rfl -- touches
  have ht:=colour_wheel hg hp
  change rides (Equiv.refl _) (A.taste U)*routeM _ _ _= star F * (_*routeM _ _ _) * star (star F)
  rw [star_star, ← Matrix.mul_assoc, hue_path hg hp]
  change _=star F * rides (Equiv.refl _) _*(F*_ *star F)*F; simp only [Matrix.mul_assoc]; rw [show star F*F=1 from ht.1,mul_one,← Matrix.mul_assoc (rides (Equiv.refl _) _) F,← he, Matrix.mul_assoc,← Matrix.mul_assoc (star F), show star F*F=1 from ht.1,one_mul]; rfl
end YM.QCD.Revolve
