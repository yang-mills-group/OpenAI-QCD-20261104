import YM.QCD.Sparks.Stalk

/-! # curvature slot monomials with true widths from the bearing of the orbit. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve RG
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side}{p k:ℕ}{r a C:ℝ}{I:Type}
lemma doors (x : Stock):∃ p : List Plaid,p.length ≤ (stanza x).length^2 ∧ (∀ b∈p,Laurent.size b.p.1≤ (stanza x).length) ∧ ∀ Z: Flux, bill Z 0 (stanza x)=(p.map (fun v=> v.beat Z)).sum:=by simpa [Laurent.size] using removal 0 (stanza x) (poem x)
def walkout (x:Stock):List Plaid := (doors x).choose
abbrev Get (x:Stock):= Fin (walkout x).length
def plant (x:Stock)(i:Get x):Plaid:= (walkout x).get i
lemma stem (x:Stock)(i:Get x): Laurent.size (plant x i).p.1 ≤2*Laurent.size x.1+2:= ((doors x).choose_spec.2.1 _ (List.get_mem ..)).trans (stanza_length _)
lemma purchases (x:Stock): (walkout x).length ≤ (2* Laurent.size x.1+2)^2 := (doors x).choose_spec.1.trans (Nat.pow_le_pow_left (stanza_length _) 2)
def shop (s:Plaid): RG.Slot:=⟨radial s.p.1,s.p.2⟩
lemma stores (T:Plaid): (shop T).length= Laurent.size T.p.1+4:=by rw [Slot.length,shop]; exact congr_arg (·+4) (rad_length _)
lemma field (q:Nub)(x:Cnr n):
    let X := (q.1,q.2.1); idyllic q x=∑ i : Get X,(plant X i).sign*faceCurl (slotFace (shop (plant X i)) (0:Site n)) (arm su n 1 x) q.2.2:= by
  intro X
  rw [idyllic]; rw [(doors (q.1,q.2.1)).choose_spec.2.2]
  let f (i: Get X):= (plant X i).beat (page x q.2.2)
  change ((walkout X).map _).sum= _
  have he : (walkout X).map (fun i=> i.beat (page x q.2.2)) = List.ofFn f:=by unfold f plant; erw [show List.ofFn _=List.map (fun i: Plaid=> i.beat (page x q.2.2)) (List.ofFn (walkout X).get) from (List.map_ofFn ..).symm,List.ofFn_get]
  rw [he]; simp_rw [List.sum_ofFn]
  refine sum_congr rfl fun i _=>?_; unfold f Plaid.beat slotFace shop; simp_rw [add_zero]; rw [curl_read]; congr 1; rw [Slot.offset]; simp only; rw [rad_plan]

abbrev Ryde (q:Rim k):= ∀ i,Get (q.2 i)
abbrev Snug (k:ℕ):= (i:Rim k) × Ryde i
lemma guest (q:Rim k)(j:Ryde q) : |∏ i,(plant (q.2 i) (j i)).sign|=1:=by rw [abs_prod]; simp only [Plaid.cash,prod_const_one]
def signal (q:Rim k)(j:Ryde q) :ℝ := (k.factorial:ℝ)⁻¹ * ∏ i,(plant (q.2 i) (j i)).sign
lemma revenue (q:Rim k)(j:Ryde q):‖signal q j‖≤1:=by
  unfold signal; rw [norm_mul,Real.norm_eq_abs (∏ i,_),guest, mul_one,norm_inv]; norm_cast; norm_num; apply inv_le_one_of_one_le₀; exact_mod_cast k.factorial_pos -- inspect

def rivet (K:Typewriter k) (q: Snug k): Bloom k where
  tail := radial q.1.1
  petals i:= shop (plant (q.1.2 i) (q.2 i))
  coeff i:= ((signal q.1 q.2):ℂ) • K (raise q.1 i)
lemma flourish (K:Typewriter k) (q: Snug k)(x): (rivet K q).hues x=((signal q.1 q.2):ℂ) • graduated K q.1 x:=by
  unfold rivet Bloom.hues graduated; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=>smul_comm ..
lemma cash_top (K:Typewriter k)(h:Glow K)(q:Snug k): (rivet K q).Spins := by
  intro u v; rw [flourish, flourish,h,Matrix.mul_smul, Matrix.smul_mul]

def cost (q:Rim k) := Laurent.size q.1 + ∑ i,Laurent.size (q.2 i).1
lemma cost_raise (q:Rim k)(j): timbre (raise q j)=cost q:=rfl
lemma cost_pays (q:Rim k)(j: Ryde q)(K:Typewriter k): (rivet K ⟨q,j⟩).span≤ 2*cost q+6*k := by
  unfold cost Bloom.span rivet; simp_rw [rad_length,stores]; have hm i : Laurent.size (plant (q.2 i) (j i)).p.1 + 4≤ 2*Laurent.size (q.2 i).1+6:=by have := stem (q.2 i) (j i); omega
  have hp:= sum_le_sum (s:=univ) fun i _=>hm i; simp_rw [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hp; simp_rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [mul_add]; simp only [Nat.cast_id] at *; omega
lemma cost_count (q:Rim k) : (Fintype.card (Ryde q):ℝ)≤ (2*cost q+2)^(2*k):=by
  change (↑(Fintype.card ((i:Fin k)→ Fin _)):ℝ)≤ _; norm_cast
  rw [Fintype.card_pi, pow_mul]; have hp i := (purchases (q.2 i))
  simp only [Fintype.card_fin]; have h i: (walkout (q.2 i)).length ≤ (2*cost q+2)^2:= le_trans (hp i) (by unfold cost; gcongr; exact (single_le_sum (fun j (_:j∈univ)=>Nat.zero_le (Laurent.size (q.2 j).1)) (mem_univ _)).trans (Nat.le_add_left ..))
  simpa only [prod_const,card_univ,Fintype.card_fin] using Finset.prod_le_prod (s:=univ) (fun i _=>Nat.zero_le (walkout (q.2 i)).length) fun i _=> h i
end YM.QCD.Sparks
