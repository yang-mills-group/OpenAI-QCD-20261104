import YM.QCD.Pearl.Sense

/-! # Kinetic photon test (negative log of one Dirac determinant) -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch Pine Stationary
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n: Side} {I J D:Type} {p : Site n} {i : Axis} {κ η c s q b B r ε K a d D' C' : ℝ}{j:ℕ}{F : Momentum→Para}

lemma oceanCount (n: Side): (Fintype.card (Site n):ℝ)*beamH n^4=(2*Real.pi)^4:=by rw [site_card]; unfold beamH; push_cast; field_simp
lemma oceanPay {S : Finset (Site n)}{X : Site n→ℝ}{C:ℝ}(hc:0≤C)(h : ∀ i∈S,|X i|≤ C*(beamH n)^4): |∑ i∈S,X i| ≤ C*(2*Real.pi)^4:=by
  apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum h).trans; rw [sum_const,nsmul_eq_mul]
  apply le_trans (mul_le_mul_of_nonneg_right (show (S.card:ℝ) ≤ Fintype.card (Site n) by exact_mod_cast card_le_univ S) (by positivity)); rw [mul_left_comm, oceanCount]
lemma splits (κ : ℝ)(f: Site n→ℝ): ∑ i,f i=(∑ i∈midst n κ,f i)+(∑ i∈smallH n κ,f i)+∑ i∈univ \ (midst n κ∪smallH n κ),f i:=by
  have hv: Disjoint (midst n κ) (smallH n κ):=Finset.disjoint_left.mpr fun i h hk=> not_le_of_gt ((medium.mp h).1) (small_h.mp hk)
  rw [← sum_union hv, add_comm (∑ x∈_,_), Finset.sum_sdiff (subset_univ (midst n κ∪smallH n κ))] -- inspect
lemma pocket (hk : 3≤κ)(ht:beamH n≤1/4): (∑ p∈midst n κ,beamH n^4*radial 3 (centerZ p))≤8*(2*Real.pi^2):=by
  apply (compareCost 3 ht hk).trans; rw [show ∫ x in orbShell (beamH n), radial 3 x=_ from (peel_p (beamH n) (beamP n) (by linarith)).1]; norm_num; nlinarith [Real.pi_pos,mul_nonneg (sq_nonneg Real.pi) (beamP n).le]
lemma borders (ht:beamH n≤1/4)(hk: 3≤κ)(hc:0≤C') (X:Site n→ℝ)
    (h:∀ p∈midst n κ,|X p|≤(beamH n)^4*(C'*radial 3 (centerZ p) +960*beamH n *radial 5 (centerZ p))): |∑ i∈midst n κ,X i|≤ C'*(8*(2*Real.pi^2))+960*(32*(2*Real.pi^2)):=by
  apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum h).trans; 
  apply le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (pocket hk ht) hc) (mul_le_mul_of_nonneg_left (icebox ht hk) (by norm_num : (0:ℝ)≤960)))
  simp_rw [mul_add,sum_add_distrib,Finset.sum_mul,Finset.mul_sum]; apply le_of_eq; congr 1
  · exact Finset.sum_congr rfl fun i _=>by ring
  exact Finset.sum_congr rfl fun i _=>by ring
lemma radial_hi {p:Gₐ}(i:ℕ)(h : 1/2 ≤ ‖p‖):radial i p ≤2^i:=by
  unfold radial; apply (inv_le_inv₀ ?_ ?_).mpr (pow_le_pow_left₀ (a:=(1/2:ℝ)) (by positivity) h _) |>.trans_eq ?_
  · exact pow_pos (lt_of_lt_of_le (by norm_num) h) _
  · positivity
  rw [← inv_pow]; norm_num
variable {A W : Shine→Bundle}{v:Train j} (C : su.Color)
def outPay (ε K:ℝ):ℝ:=128*K/(ε^2)
def upland (ε K : ℝ):ℝ := ((outPay ε K *8+960*32)+300*16)*(2*Real.pi)^4
lemma wales (hC:‖C‖=1)(hn:4≤n.val)(ht:beamH n<1/4)(hq:beamH n<zone)(hk:3≤κ)(hX:A 0=touch (echo C)*wave (gamma 1))(h: Pinch (Dir v) r c B)(hS: Pinch shaft r c B)(e:Bright r c B ε)(he:0<η)(hw:Wall η b A)(hw': Wall η s W)(hε:ε*Real.pi≤η/2)(hK: 8<κ*ε)(h' : |wobble2 r c B η b s| ≤ K):
    |(∑ i:Site n, shock A W (Dir v) i)-∑ i∈midst n κ,(beamH n)^4 *windward (centerZ i)| ≤ (outPay ε K)*(8*(2*Real.pi^2))+960*(32*(2*Real.pi^2))+ ((κ+1)^4*(Real.pi^2/2))*(4*lowCost r c B b s) + upland ε K:=by
  have hκ : 0≤K:= (abs_nonneg _).trans h'
  have hP : 0≤outPay ε K:= by unfold outPay; positivity
  have hL : 0≤ lowCost r c B b s:=by unfold lowCost; have he:=hw.posX he; have hx:=hw'.posX ‹0<η›; have hp:= h.cost_q; positivity
  let S:=midst n κ; let T:=smallH n κ; let f:=shock A W (Dir v) (n:=n)
  have ha : |∑ p∈T,f p|≤ ((κ+1)^4*(Real.pi^2/2))*(4*lowCost r c B b s) := by
    apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum (fun i (_ : i∈T)=> lowCliff (p:=i) hw hw' he h e hn (by linarith) hq)).trans
    rw [sum_const,nsmul_eq_mul]; gcongr; apply row_count hk
  have hb:= fun p (hp:p∉T)=>highStep C hC s h hS e he hw hw' hε hX K hK h' hp
  let P:= outPay ε K
  have hj: ‖∑ p ∈ S, overH A W (Dir v) p‖≤P*(8*(2*Real.pi^2))+960*(32*(2*Real.pi^2)):= borders ht.le hk hP _ (fun i hi=> hb i (fun hh=> not_le_of_gt ((medium.mp hi).1) (small_h.mp hh)))
  have hO: |∑ p∈univ \ (S∪ T),f p|≤ upland ε K:=by
    unfold upland; apply oceanPay (by change 0 ≤ (P*8+_)+_; positivity); intro p hp
    obtain ⟨hp,hP⟩:= not_or.mp (show ¬(p∈ S ∨ p∈T) from fun ht => (mem_sdiff.mp hp).2 (mem_union.mpr ht))
    let t:=beamH n; let r:=centerZ p; have hu : 1/2≤‖r‖:=le_of_not_gt fun hv=>hp (medium.mpr ⟨lt_of_not_ge (mt small_h.mpr hP),hv⟩)
    have h₂: |overH A W (Dir v) p| ≤ t^4*(P*8+960*32):=by
      apply (hb p hP).trans; apply mul_le_mul_of_nonneg_left _ (by positivity); refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left (show radial 3 r≤8 from (radial_hi 3 hu).trans (by norm_num)) ‹0≤outPay ε K›
      exact mul_le_mul (show 960*t≤ 960 by unfold t; linarith) ((radial_hi 5 hu).trans_eq (by norm_num : (2:ℝ)^5=32)) (sinuous ..) (by norm_num)
    have hz: |windward r| ≤ 300*16:= (gale r).trans (by gcongr; exact (radial_hi 4 hu).trans (by norm_num))
    have hy : |t^4*windward r|≤t^4*(300*16):=by rw [abs_mul,abs_of_nonneg (by positivity : 0≤ t^4)]; gcongr
    rw [show f p= overH A W (Dir v) p+t^4*windward r from (sub_add_cancel ..).symm]; apply (abs_add_le ..).trans; exact (add_le_add h₂ hy).trans_eq (by change _=(P*8+_+_)*t^4; ring)
  change |(∑ p,f p)-_|≤_
  apply le_trans ?_ (add_le_add (add_le_add (show |∑ p∈S,overH A W (Dir v) p| ≤_ from hj) ha) hO)
  rw [splits κ, show (∑ i∈midst n κ,overH A W (Dir v) i) = (∑ i∈ S,f i)- ∑ i∈S,(beamH n)^4*windward (centerZ i) from sum_sub_distrib _ _] -- possibly S not synt
  let a:=∑ p ∈ S, f p; let b:=∑ p ∈ T,f p; let c:=∑ p∈univ \ (S ∪ T), f p; let d:=∑ i∈ S,(beamH n)^4 *windward (centerZ i)
  change |a+b+c-d|≤|a-d|+|b|+|c|; rw [show a+b+c-d=a-d+b+c by ring]; apply (abs_add_le ..).trans; exact add_le_add (abs_add_le ..) le_rfl
end YM.QCD.Pearl
