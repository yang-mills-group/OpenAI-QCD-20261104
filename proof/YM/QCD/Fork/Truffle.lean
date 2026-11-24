import YM.QCD.Fork.Moor
/-! # main pieces, reserve width & scales before sector, pointwise budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fork
open Lat Kit Lattice Wilson RG Run Leaf Tee Function Finset Metric Filter
open Orbit Flume Sparks Quarry Pine QCD.Cost Eyrie Revolve Rudder Garden
open YM.Next.Free Laurent LeafM
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {I V:Type}{L f c:Side}{t p η ξ w r q R u v C D G m A δ:ℝ}{B b j k l:ℕ}{F:Flight j k}{P:Plan j} {e:f.val=c.val*F.L.val}
local notation "S"=> sliceL F e
variable {X: Offer 1 u C}{Y:Offer 2 v D}{a :ℝ}
lemma pale (W:I→Bloom k) (hk : 0<k): wild W ξ f 1=0:=by
  have he i' : trackP (W i') ξ f 1=0:=by
    unfold trackP yard satin
    have hx (i:Slot)(x:Site f): pulp i x ξ 1=0:=by rw [pulp,Bloom.slot_tail,smul_zero]
    simp_rw [hx]; unfold Bloom.hues; simp_rw [show ∀ (c:Fin k → su.ColorIndex), (∏ j,(0:su.Color) (c j))=0 from fun c=>prod_eq_zero (mem_univ (⟨0,hk⟩:Fin k)) rfl]; simp only [Complex.ofReal_zero,zero_smul,sum_const_zero]; rw [show rides _ (fun _ : Site f => (0:Bundle))=0 from ride_zero ..,zero_mul]
  unfold wild; simp_rw [he,tsum_zero]
local notation "T"=>pesto P F e (trunkM X Y ξ m f)
lemma fees (hx: Species F e p R η r a B T):
    let d:= (stamp P F.L)* |m| * a⁻¹*massL F.L
    (∀ i j, ‖cell (rightL F e T 1) i j-cell (proton F e) i j‖ ≤ d)∧ (∀ i j,‖cell (leftL F e T 1) i j-cell (barP F e) i j‖ ≤ d):=by
  intro d
  let Q:= T 1; let B':= father F e
  have he : Q=B'+(m:ℂ) • 1:=by
    unfold Q pesto trunkM blossomT; simp only [Pi.add_apply,Pi.smul_apply]; rw [pale (frosting X.W) (by decide),pale (frosting Y.W) (by decide),tree_zero, add_zero,zero_add]; rfl
  let f0:= (stamp P F.L)*|m| *a⁻¹
  have hv:IsUnit B'.det:=by unfold B'; rw [← tree_zero P]; exact ticket_inv ..
  have hp : ‖B'⁻¹‖≤ stamp P F.L:=by unfold B'; rw [← tree_zero P]; exact ticket_B ..
  have hh : ‖Q⁻¹‖≤ a⁻¹:=(hx.terrific 1).reciprocal hx.calf
  have hz:IsUnit Q.det:=hx.sole _
  have hy : ‖Q⁻¹-B'⁻¹‖≤ f0:=by
    rw [show Q⁻¹-B'⁻¹ = -(B'⁻¹*(Q-B')*Q⁻¹) by rw [mul_sub,sub_mul,mul_assoc B'⁻¹ Q Q⁻¹,Matrix.mul_nonsing_inv Q hz,mul_one,Matrix.nonsing_inv_mul B' hv,one_mul,neg_sub],show Q-B'=(m:ℂ) • 1 by rw [he]; abel,norm_neg]; have ht:=healthy P F.L -- conflicts
    refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hp ?_ (norm_nonneg _) ht.le)) hh (norm_nonneg _) (by positivity)); rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,oneNorm,mul_one]
  let K:=conn F e; have hK: ‖K‖≤massL F.L:=towerB _ _ _ (1:Grid f)
  have hV:0≤f0:=(norm_nonneg _).trans hy
  constructor
  · intro i j; change ‖cell (Q⁻¹*Kᴴ) _ _-cell (B'⁻¹ * Kᴴ) _ _‖≤_; apply le_trans (b:=‖(Q⁻¹-B'⁻¹)*Kᴴ‖) ?_ ((Matrix.l2_opNorm_mul ..).trans (mul_le_mul hy ((Matrix.l2_opNorm_conjTranspose _).le.trans hK) (norm_nonneg _) hV))
    rw [Matrix.sub_mul]; exact cell_pay i j (Q⁻¹*Kᴴ-B'⁻¹*Kᴴ)
  intro i j; change ‖cell (K*Q⁻¹) _ _-cell (K * B'⁻¹) _ _‖≤_; refine le_trans (b:=‖K*(Q⁻¹-B'⁻¹)‖) ?_ ((Matrix.l2_opNorm_mul ..).trans ((mul_le_mul hK hy (norm_nonneg _) (mass_pos _).le).trans_eq (mul_comm ..)))
  rw [Matrix.mul_sub]; exact cell_pay i j (K*Q⁻¹-K*B'⁻¹)

abbrev spanM (r:Ratio c f)(o:Site f)(b:ℕ):Support c:=univ.filter fun i=>r.embed i∈ trunkFt o b
lemma olives (r: Ratio c f)(o:Site f) : ((spanM r o b).card:ℝ)≤ ((2*(b:ℝ)+1)^4):=by
  have hl : (spanM r o b).card ≤ (trunkFt o b).card:= card_le_card_of_injOn r.embed (fun i hi=>(mem_filter.mp hi).2) r.embed_injective.injOn
  have hh: (trunkFt o b).card ≤ (2*b+1)^4:=by simpa [trunkFt,two_mul] using (Corona.halo_size ({o}:Support f) b); -- check order
  exact_mod_cast (hl.trans hh)
lemma inwards (r:Ratio c f)(o:Site f){y:Site c}(i:y∈spanM r o b)(k:ℕ): meets r o k y ≤ (1+((b:ℝ)+1))^k:=by
  obtain ⟨u,hU,h⟩:=halo_spec.mp (mem_filter.mp i).2; rw [mem_singleton.mp hU] at h; have ht: separation (r.parent o) y ≤ b+1:=by
    have he : r.assemble (y,0)=r.embed y:=by rw [Ratio.assemble]; simp
    have hp:r.parent (r.embed y)=y:=by rw [← he, Ratio.assemble_parent]
    rw [← hp]; exact (YM.Work.E04.parent_separation r o (r.embed y)).trans (Nat.add_le_add_right h _)
  unfold meets; gcongr; exact_mod_cast ht
-- compare any columns with unit orientation and alpha slope
open LeafM
lemma forward (o: Site f) (r:Ratio c f)(b l:ℕ)(F: Site c→Bundle)(Z: Site c→Bundle) (K Y : Site c→ℝ)(B M A D:ℝ)
   (hA : ∑ j,meets r o l j * ‖Z j‖ ≤ A) (hv : (1+((b:ℝ)+1))^l ≤ B) (hp : ∑ j,Y j≤ D)(hY : 0 ≤ Y)(hD:0≤ D)(hM : 0 ≤ M)(ht:0 ≤t)(hx : ∀ i∈spanM r o b, ‖F i‖ ≤ ‖Z i‖+ M+t*Y i)(hZ : ∀ i ∉ spanM r o b, F i=0):
    ∑ j,meets r o l j*‖F j‖ ≤ A + B*(2*b+1)^4*M+B*t*D:=by
  let s:=spanM r o b
  trans (∑ j∈s,meets r o l j*‖Z j‖)+∑ j∈s, (B*M+B*t*Y j)
  · rw [← sum_add_distrib]; rw [← sum_subset (subset_univ s) (f:=fun j=> meets r o l j*‖F j‖) (fun i _ hi=>by rw [hZ i hi,norm_zero,mul_zero])];
    refine sum_le_sum fun j hj=>?_ ; have ht':=meets_nn r o l j; have hh := (inwards r o hj l).trans hv; refine (mul_le_mul_of_nonneg_left (hx j hj) ht').trans ?_; rw [mul_add,mul_add]; nlinarith only [mul_le_mul_of_nonneg_right hh hM,mul_le_mul_of_nonneg_right hh (mul_nonneg ht (hY j))]
  have hh: ∑ j∈s,meets r o l j*‖Z j‖≤A:= (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun j _ _=>mul_nonneg (meets_nn ..) (norm_nonneg _))).trans hA
  have hB : 0≤B:=le_trans (by positivity) hv
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]
  linarith only [hh, mul_le_mul_of_nonneg_right (olives (b:=b) r o) (mul_nonneg hB hM), mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun j _ _=> hY j)).trans hp) (mul_nonneg hB ht)]
end YM.QCD.Fork
