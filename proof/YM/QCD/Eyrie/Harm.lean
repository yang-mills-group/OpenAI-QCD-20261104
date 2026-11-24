import YM.QCD.Eyrie.Glyph

/-!
# Lifted jet through exponential-weighted coordinate control
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {X Y: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n : Side} {I J K M L: Type} [Fintype J] {ν : ℕ}
variable {l : I→Site n} {d : I→X} {k : J→Site n} {x : Site n} {r a b c C D u : ℝ}
lemma transfer (ha : 0<u) (hr : 3*u≤r) (x v y:Site n): Decay r x v*Decay u v y ≤ Decay u x y*Decay u x v := by
  have hp:= mul_le_mul_of_nonneg_right (white (y:=v ) (x:=x) (by linarith : u+u≤r)) (decay_pos u v y).le; apply hp.trans
  rw [show Decay (u+u) x v=Decay u x v*Decay u x v by unfold Decay; rw [← Real.exp_add]; ring_nf,mul_comm (Decay u x y),mul_assoc]; exact mul_le_mul_of_nonneg_left (decay_step ha.le x v y) (decay_pos ..).le
lemma transfer' (ha : 0<u)(hr : 3*u≤r)(x v y z: Site n):
    Decay r x v*(Decay u v y*Decay u v z)≤ Decay u x v*(Decay u x y*Decay u x z):= by
  let q:= Decay (n:=n) u
  have h i j: 0≤q i j:= (decay_pos ..).le
  apply (mul_le_mul_of_nonneg_right (white hr x v) (mul_nonneg (h ..) (h ..))).trans
  have he : Decay (3*u) x v=(q x v)^3:=by unfold q Decay; rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]; apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul (decay_step ha.le x v y) (decay_step ha.le x v z) (mul_nonneg (h ..) (h ..)) (h ..)) (h x v))
  exact le_of_eq (by unfold q; ring)

def count (u:ℝ)(ν:ℕ):=(ν:ℝ)*countCost u
lemma count_nn (h:0<u)(ν:ℕ): 0≤count u ν:= mul_nonneg (by positivity) (count_pos h).le

def intakeQ (u D:ℝ) (ν:ℕ):=1+D*count u ν + (D*D)*(count u ν*count u ν)
lemma intakeQ_nn (h:0<u)(he:0≤D)(ν:ℕ): 1≤ intakeQ u D ν:= by have := count_nn h ν; unfold intakeQ; exact le_trans (le_add_of_nonneg_right (by positivity : 0 ≤ D*count u ν)) (le_add_of_nonneg_right (by positivity))
lemma migrate {g:X→Positions J}{f:Positions J→Y}(hc : Multiplicity k ν)(H:Flock k Push.Uniform.bolt f x r C) (he : g 0=0)(hh : ContDiffAt ℝ ω g 0) (ht : 0<u) (ha : 0≤D)
    (hk : ∀ i : J,Flock l d (fun x=>g x i) (k i) u D)(hr : 3*u≤r): Flock l d (f ∘ g) x u (C * intakeQ u D ν):=by
  have hQ:=intakeQ_nn ht ha ν
  have hp:= H.fee; have hF : ContDiffAt ℝ ω f (g 0):= he ▸ H.host
  let q:=Decay (n:=n) u
  have hN:= (count_nn ht ν); let a:=count u ν
  have hd i j: 0≤ q i j:=(decay_pos ..).le
  have hK : ∑ i:J,q x (k i)≤a:=hc.count k ht x
  have hD : D*a ≤ intakeQ u D ν:= calc
    _ ≤ 1+D*a:= by linarith
    _ ≤ _ := le_add_of_nonneg_right (by positivity)
  refine ⟨ht,mul_nonneg hp (zero_le_one.trans hQ), hF.comp _ hh, (by rw [Function.comp_apply,he]; exact H.born.trans (le_mul_of_one_le_right hp hQ)),fun i=>?_,fun i j=>?_⟩
  · let y:=l i
    rw [considers (d i) hh hF,he]; apply (norm_sum_le ..).trans; refine le_trans (Finset.sum_le_sum (fun (w:J) hw=> ?_)) (show ∑ i:J,(q x (k i)*(C*D*q x y)) ≤ _ from ?_)
    · rw [norm_smul]; apply (mul_le_mul ((hk w).walks i) (H.walks w) (norm_nonneg _) (mul_nonneg ha (hd ..))).trans
      have ht :=mul_le_mul_of_nonneg_left (transfer ht hr x (k w) (l i)) (mul_nonneg hp ha); dsimp only [q,y]; linarith only [ht]
    · have hb:= hd x y; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hp) hb)
      rw [← sum_mul]; simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right hK (mul_nonneg (mul_nonneg hp ha) hb)
  let y:=l i; let z:=l j
  rw [considered _ _ hh hF,he]; have hz: 0≤a:=hN
  have hY:=hd x y; have hZ:=hd x z
  let L:= q x y*q x z
  have Bh:0 ≤ L:=mul_nonneg hY hZ
  apply (norm_add_le ..).trans
  apply le_trans (add_le_add ((norm_sum_le ..).trans (b:=_) ?_) ((norm_sum_le ..).trans (b:=_) ?_)) (show (C*D*a*L)+(C*D^2*(a*a)*L) ≤ _ from ?_)
  · apply le_trans (Finset.sum_le_sum (fun (v:J) _=> show ‖Withdrawal.rise (d i) (d j) g 0 v • blade (Push.Uniform.bolt v) f 0‖ ≤ q x (k v)*(C*D*L) from ?_))
    · rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right hK (mul_nonneg (mul_nonneg hp ha) Bh)).trans_eq (by ring)
    rename_i v hv; rw [norm_smul]
    apply (mul_le_mul ((hk v).wandered i j) (H.walks v) (norm_nonneg _) (mul_nonneg ha (mul_nonneg (hd ..) (hd ..)))).trans
    have ht:=mul_le_mul_of_nonneg_left (transfer' ht hr x (k v) (l i) (l j)) (mul_nonneg hp ha); unfold L q y z; linarith only [ht]
  · let S (b v:J) := q x (k b)*q x (k v)*(C*D^2*L)
    have h (a b:J): ‖Withdrawal.move (d j) g 0 a • Withdrawal.move (d i) g 0 b • Jacobi.mixed (Push.Uniform.bolt b) (Push.Uniform.bolt a) f 0‖≤ S a b:=by
      rw [norm_smul,norm_smul]; refine (mul_le_mul ((hk a).walks j) (mul_le_mul ((hk b).walks i) (H.wandered b a) (norm_nonneg _) (mul_nonneg ha (hd ..))) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg ha (hd ..))).trans ?_
      have hx:= mul_le_mul (transfer ht hr x (k a) z) (transfer ht hr x (k b) y) (mul_nonneg (decay_pos ..).le (decay_pos ..).le) (mul_nonneg (hd ..) (hd ..)); have hw:=mul_le_mul_of_nonneg_left hx (mul_nonneg hp (sq_nonneg D))
      unfold S q L q; dsimp only [y,z] at *; linarith only [hw]
    apply le_trans (Finset.sum_le_sum (fun b _=>(norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> h b i))))
    unfold S; simp_rw [← Finset.sum_mul,← Finset.mul_sum]
    have hx : 0≤ ∑ i:J, q x (k i):= Finset.sum_nonneg fun _ _ => hd ..
    have hk:= mul_le_mul_of_nonneg_right (mul_le_mul hK hK hx hz) (mul_nonneg (mul_nonneg hp (sq_nonneg D)) Bh); simp_rw [← Finset.sum_mul]; exact hk.trans_eq (by ring)
  change _≤ C*intakeQ u D ν* L; unfold intakeQ; rw [show count u ν=a from rfl]; nlinarith only [mul_nonneg hp Bh]
end YM.QCD.Eyrie
