import YM.QCD.Flume.Fonts
import YM.Next.FREE_KERNELS.SingleAxis

/-! # Positive Hermitian piece: analytic divisions along successive axes -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}

def hemi (v : Train j) (p : Momentum) := (Dir v p).1
def Tuck {A : Type*} [Zero A] (n : ℕ) (p : Axis → A) (i:Axis):A:= if i.val<n then p i else 0
lemma shelter (n) (p : Momentum) {η:ℝ} (he : 0<η) (hp : p∈cube η) : Tuck n p ∈ cube η:=by
  constructor <;> intro i <;> unfold Tuck <;> split
  · exact hp.1 i
  · simpa only [Complex.zero_im, abs_zero] using he
  · exact hp.2 i
  simp [add_pos Real.pi_pos he]
lemma shelve (n) (p : Momentum) {η:ℝ} (he : 0<η) (hp : p∈ realCube η): Tuck n p ∈ realCube η:=by
  refine ⟨(physical_iff _).mpr ?_,(shelter n p he (mem_cube_real hp he)).2⟩
  intro i; unfold Tuck; split
  · exact (physical_iff _).mp hp.1 i
  simp
lemma roof_overlaps (v : Train j) : Overlaps zone (hemi v):=fun p hp x hx => congr_arg Prod.fst (period_dir v x hp hx)
lemma north (s : Signed) (v : Train j) (p : Momentum) (hp : p∈realCube zone) : hemi v (s.act p)=hemi v p:=by unfold hemi; rw [s_dir _ _ _ hp]; rfl
lemma cover_roots (v : Train j) (n) : Overlaps zone fun p=> hemi v (Tuck n p):=by
  intro p hp x hx; have hm := shelve n _ zone_pos hx
  have he : Tuck n (p+Laurent.reciprocal x) = Tuck n p+Laurent.reciprocal (Tuck n x):=by ext i; unfold Tuck; by_cases h:i.val<n <;> simp [h,Laurent.reciprocal]
  rw [he] at hm
  change hemi v (Tuck n _)= _; rw [he, period_dirM _ _ (shelve n _ zone_pos hp) hm] -- inspect
  where period_dirM (p) (x) (hp : p ∈ realCube zone) (h : p+Laurent.reciprocal x ∈ realCube zone) : hemi v (p+Laurent.reciprocal x)=hemi v p:=roof_overlaps v _ hp _ h
lemma customary (v : Train j) (n) (p) (hp : p∈realCube zone) : star (hemi v (Tuck n (-p)))=hemi v (Tuck n p):=by
  have he : Tuck n (-p)=-Tuck n p:=by ext i; unfold Tuck; by_cases h:i.val<n <;> simp [h]
  have hp := shelve n _ zone_pos hp; rw [he,hemi, evenD _ _ hp]; exact (native_dir _ _ hp.1).1
lemma aware (n : ℕ) : Differentiable ℂ (Tuck (A:=ℂ) n) := by
  refine differentiable_pi.mpr (fun i=> ?_); unfold Tuck; split <;> fun_prop
lemma paid_axis (hj : 2≤j) (v : ι→Train j) (n : ι→ℕ) : Moderate (fun _ : ι=>1) fun i p => hemi (v i) (Tuck (n i) p):=by
  obtain ⟨η,C,hp,hc,h⟩:=(Dir_budget hj v).scalar
  refine ⟨η,C,hp,hc,fun i=>⟨fun p he =>?_,fun p he=> (h i).bound _ (shelter _ p hp he)⟩⟩
  exact ((h i).hol _ (shelter _ p hp he)).comp p ((aware _).differentiableAt)

def tier (v : Train j) (a : Axis) := tape fun p => hemi v (Tuck (a.val+1) p)
def stair (m : ℕ) (v : Train j) (a : Axis) : Cover→ℝ := match m with
| 0=> tier v a
| n+1=>payOut (partAxis a) (stair n v a)
lemma income_a (hj : 2 ≤ j) (v : ι→ Train j) (a : ι→Axis) (m): SoundTape (fun _ : ι=>1) (fun i=> stair m (v i) (a i)):=by
  induction m with
  | zero=> exact tapes_sound (paid_axis hj v fun i=> (a i).val+1) zone_pos fun _=>cover_roots _ _
  | succ k ih=>
    obtain ⟨σ,C,hp,hc,h⟩:=ih
    refine ⟨σ/2,(σ/2)⁻¹*C,by positivity,mul_pos (by positivity) hc,fun i=>?_⟩; rw [mul_assoc]; exact (dividend σ hp (a i)).released (by positivity) (h i) (by positivity)
lemma tier_read (hj : 2≤j) (v : Train j) (a : Axis) (p) (hp : p∈baseCube): RRead (tier v a) p=hemi v (Tuck (a.val+1) p):=by
  let X (_:Unit):=v
  obtain ⟨η,hc,h⟩:=tapes_read (paid_axis hj X fun _=> a.val+1) zone_pos (fun i=>cover_roots v (a.val+1)) (fun i=>customary v (a.val+1))
  exact h () p (base_subset_realCube hc hp)
lemma cashbook (hj : 2≤j) (v : Train j) (m : ℕ) (a : Axis): ∃ σ C : ℝ, 0<σ ∧ Width σ C (stair m v a):=by obtain ⟨σ,C,hp,hc,H⟩:=income_a hj (fun _ : Unit=> v) (fun _=> a) m; exact ⟨σ,C*1,hp,H ()⟩
lemma resonance (hj : 2≤j) (v : Train j) (m : ℕ) (a : Axis) {p : Momentum} (hp : p∈baseCube): ContinuousAt (RRead (stair m v a)) p:=by
  obtain ⟨σ,C,hs,h⟩:=cashbook hj v m a
  exact (Work.F07.readDeriv (budgeted_real h) (show 0<σ/2 by linarith) (show σ/2<σ by linarith) (mem_cube_real (base_subset_realCube (by linarith) hp) (by linarith)).1).1.continuousAt

lemma t_step (p : Momentum) (a : Axis): Tuck (a.val+1) (update p a 0)=Tuck a.val p:=by
  funext i; by_cases h:i=a
  · subst i; simp [Tuck]
  by_cases hu:i.val<a.val
  · simp only [Tuck,hu,show i.val<a.val+1 by omega, if_true, Function.update_of_ne h]
  have hx:i.val≠a.val:= fun he=> h (Fin.ext he)
  simp only [Tuck,hu,show ¬i.val<a.val+1 by omega, if_false]
lemma mirror_tuck (p : Momentum) (n a) : Tuck n ((Signed.mirror a).act p)=(Signed.mirror a).act (Tuck n p):=by
  funext i; by_cases h:i.val<n <;> simp [Tuck,Signed.act,Signed.mirror,h] --
lemma bank_acts (p : Momentum) (hp : p∈baseCube) (s : Signed): s.act p∈baseCube:=by
  refine ⟨(real_signed s (base_subset_realCube zone_pos hp)).1,?_⟩
  intro i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; split <;> simpa using hp.2 i

lemma stairs (m : ℕ) (hj : 2≤j) (v : Train j) (a : Axis) (p) (hp : p∈baseCube):
    chip (p a)*RRead (stair (m+1) v a) p=RRead (stair m v a) p-RRead (stair m v a) (update p a 0):=by obtain ⟨σ,C,hs,h⟩:=cashbook hj v m a; exact single_axis h hs _ hp.1
lemma first_rise (hj : 2≤j) (v : Train j) (a : Axis) (p) (hp : p∈baseCube):
    chip (p a)*RRead (stair 1 v a) p=hemi v (Tuck (a.val+1) p)- hemi v (Tuck a.val p) := by
  rw [show (1:ℕ)=0+1 from rfl,stairs 0 hj v a p hp,show stair 0 v a=tier v a from rfl,tier_read hj v a p hp,tier_read hj v a _ (bank_blank hp a),t_step]
lemma chi_spin (p : Momentum) (a : Axis) : chip ((-p) a)*mode p (step a) = -chip (p a):=by
  unfold chip
  rw [Exterior.factor,sub_mul, one_mul,← Complex.exp_add,Pi.neg_apply,mul_neg, neg_add_cancel]; simp
lemma mutable (hj : 2≤j) (v : Train j) (a : Axis) (p) (hp : p∈baseCube): RRead (stair 1 v a) (update p a 0)=0:=by
  let g:=RRead (stair 1 v a)
  let s:=Signed.mirror a
  have he (p : Momentum):ContinuousAt (fun p=>s.act p) p:=by
    have h : Continuous (fun p: Momentum=>s.act p):=by
      apply continuous_pi; intro i; obtain ⟨i,rfl⟩:= s.perm.surjective i; simp only [Signed.act_at]; split <;> fun_prop
    exact h.continuousAt
  have hx : Continuous (fun p : Momentum=> mode p (step a)):=by unfold mode; fun_prop
  have hh (p : Momentum) (hp : p∈baseCube) : g (s.act p) = -mode p (step a)*g p:=by
    apply renew_q (fun p=>g (s.act p)) (fun p=>-mode p (step a) *g p) a _ _ _ p hp
    · exact fun p h=> (resonance hj v 1 a (bank_acts p h s)).comp (he p)
    · intro p h; exact (hx.neg.continuousAt.mul (resonance hj v 1 a h))
    intro p h hu
    let q: Momentum:= s.act p; have hq:=bank_acts p h s
    have hA (n) : hemi v (Tuck n q)=hemi v (Tuck n p):= by unfold q s; rw [mirror_tuck]; exact north _ _ _ (shelve n _ zone_pos (base_subset_realCube zone_pos h))
    have hz : chip (q a)*g q = chip (p a)*g p:= by unfold g; rw [first_rise hj v _ p h,first_rise hj v _ q hq,hA,hA]
    have hi:chip (q a)*mode p (step a)=-chip (p a):=by rw [show q a=(-p) a by simp [q,s,Signed.act,Signed.mirror]]; exact chi_spin p a
    change chip (p a)≠0 at hu
    apply mul_left_cancel₀ (show chip (q a)≠0 from fun h=> by rw [h,zero_mul] at hi; exact neg_ne_zero.mpr hu hi.symm)
    change chip _ * g q= _
    rw [hz]; simp only [neg_mul,mul_neg,← mul_assoc,hi,neg_mul,neg_neg]
  have hg:= hh _ (bank_blank hp a)
  have ht: s.act (update p a 0) = update p a 0:=by
    funext i; by_cases h:i=a; · simp [s,Signed.act,Signed.mirror,h]
    simp [s,Signed.act,Signed.mirror,h,Ne.symm h]
  rw [ht,Exterior.factor] at hg; simp only [Function.update_self,mul_zero,Complex.exp_zero,neg_mul,one_mul] at hg
  change g _ = 0; linear_combination (1/2)*hg

def plusD (p : Momentum) (a : Axis) := chip (p a)*chip ((-p) a)
def steps (v : Train j) (a : Axis) (p : Momentum) := -mode p (step a)*RRead (stair 2 v a) p
lemma second_rise (hj : 2≤j) (v : Train j) (a : Axis) (p) (hp : p∈baseCube):
    plusD p a*steps v a p=hemi v (Tuck (a.val+1) p)-hemi v (Tuck a.val p):= by
  rw [← first_rise hj v _ p hp]; unfold plusD steps
  rw [show RRead (stair 1 v a) p=_ from (by rw [stairs 1 hj v a p hp,mutable hj v _ p hp,sub_zero] : RRead (stair 1 v a) p = chip (p a)*RRead (stair 2 v a) p)]
  simp only [neg_mul,mul_neg]; rw [← mul_assoc, mul_assoc (chip _) (chip _) (mode _ _),chi_spin]; ring
lemma chosen_steps (hj : 2≤j) (v : Train j) (p : Momentum) (hp : p∈baseCube) :
    ∑ a:Axis, plusD p a * steps v a p= hemi v p:=by
  simp_rw [second_rise hj v _ p hp]
  rw [Fin.sum_univ_eq_sum_range (fun i=> hemi v (Tuck (i+1) p)-hemi v (Tuck i p)) 4, Finset.sum_range_sub (fun i=>hemi v (Tuck i p))]
  simp [show Tuck 0 p=0 from by ext; simp [Tuck],show Tuck 4 p=p from by ext i; exact if_pos i.isLt,hemi]
end YM.QCD.Flume
