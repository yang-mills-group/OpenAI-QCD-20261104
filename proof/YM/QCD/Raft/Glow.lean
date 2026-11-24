import YM.QCD.Raft.Syrup

/-! # physical free-frame receipt for the full endpoint determinant. rotation of all observables here same seam via sign. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Cost Push.Uniform Eyrie Stationary Quarry Run Kit Sparks Pine Revolve Orbit Birth Garden Flume YM.Next.Free
open Rudder Pearl Tavern YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {n: Side}{r C Y d c a e:ℝ}{P:Cnr n→ℝ}{j k:ℕ}
lemma tightH (h:ContDiffAt ℝ ω P 0):∃ C,Flock (traceG n) Push.Uniform.bolt P 0 1 C := by
  -- adapt from finite sup
  let X(i:Road n):= Decay 1 0 (traceG n i)
  let V (i:Road n):=‖blade (Push.Uniform.bolt i) P 0‖/X i; let K (i:Road n×Road n):=‖Jacobi.mixed (Push.Uniform.bolt i.1) (Push.Uniform.bolt i.2) P 0‖/(X i.1*X i.2)
  let C:=‖P 0‖+∑ i,V i; let S:=∑ i,K i; have hp i:0<X i:=Push.Uniform.decay_pos ..
  have hv i:0≤V i:=div_nonneg (norm_nonneg _) (hp _).le
  have hk i:0≤K i:= div_nonneg (norm_nonneg _) (mul_pos (hp i.1) (hp i.2)).le
  have hc : ‖P 0‖≤C:=le_add_of_nonneg_right (sum_nonneg (fun i _=>hv i)); have he:0 ≤ S:=sum_nonneg (fun i _=> hk i)
  have hC :0 ≤ C:= (norm_nonneg _).trans hc
  refine ⟨C+S,one_pos,add_nonneg hC he,h,hc.trans (le_add_of_nonneg_right he),fun i=>?_,fun i j=>?_⟩
  · exact (div_le_iff₀ (hp i)).1 ((single_le_sum (fun i _=>hv i) (mem_univ i)).trans ((le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_right he)))
  exact (div_le_iff₀ (mul_pos (hp i) (hp j))).1 ((single_le_sum (f:=K) (fun i _=>hk i) (mem_univ (i,j))).trans (le_add_of_nonneg_left hC))
lemma groom (M : Grid n→ℝ) (hg:∀ x k,M (Lattice.gauge k x)=M x)(hv:∀ i x,M (pull 1 i x)=M x)(hs:∀ s x,M (pull s 0 x)=M x)(he: ContDiffAt ℝ ω (M∘input su n) 0) : Loves (M ∘ input su n):=by
  let T:= M∘input su n
  have hp : force T:=by
    filter_upwards [moveField_germ (G:=su) (m:=n)] with z h; change M _=M _; rw [h]; exact hg ..
  refine ⟨he,fun x=> ?_,fun s=> ?_,fun i=>?_,hp⟩
  · obtain ⟨c,hc⟩:= tightH he; exact cigar_nil ⟨hc,(fun i=> Eventually.of_forall fun x=>by simpa only [Function.comp_apply,← stain_cons] using hg ..),hp⟩ x
  · refine Eventually.of_forall fun i=>?_; change M (input su n (flipCoords s ℝ i))=M _; rw [← flip_links]; exact hs s _
  refine Eventually.of_forall fun x=>?_ ; simp only [Function.comp_apply,input_run]; exact hv ..
lemma trustD (x:Sheet n)(b:Sheet n)(ht:b∈unitary _): (aura b x).det=x.det:=by unfold aura; rw [Matrix.det_mul,Matrix.det_mul,mul_right_comm,← Matrix.det_mul,ht.2, Matrix.det_one,one_mul]
def caravan (P:Plan j)(v:Train j)(U:On)(n:Side)(x:Grid n):=wood P 0 v x+U n x
def rollG (P:Plan j)(v:Train j)(U:On)(n:Side):=presG (caravan P v U n∘input su n)
lemma car_origin (P: Plan j)(v:Train j)(U:On)(n: Side)(hu : Vital U): caravan P v U n 1 = unbarred v n ∧ IsUnit (unbarred v n).det :=by
  refine ⟨by unfold caravan; rw [(hu.1 _).2.2.2.1,add_zero,bare_this],?_⟩
  apply IsUnit.mk0 _; intro h; have hp:=congr_arg Matrix.det (links_inv v n).1; rw [Matrix.det_mul,h,mul_zero,Matrix.det_one] at hp; exact zero_ne_one hp
lemma lumber (P:Plan j): ∃ t C:ℝ, 0<t∧0≤C∧∀ (n:Side)(v:Train j), Eyrie.glyph (traceG n) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (fun x=>wood P 0 v (input su n x)) t C:=by
  obtain ⟨r,b,hC,hc,K⟩:=Rudder.pays_all P
  obtain ⟨w,c,hp,h,hW⟩:= attainable 0 hC (duty*b)
  refine ⟨w,c*(duty*b), hp, mul_nonneg h (mul_nonneg duty_pos.le hc.le),fun n v=>?_⟩
  obtain ⟨I,B,h,H⟩:=K v; have hx x:dust (queen ∘ B) n x= wood P 0 v x:= by unfold dust; simp_rw [Function.comp_apply,queen_rides]; exact (H ..).tsum_eq
  have ht := hW I _ (Eyrie.trek h) n; simp_rw [hx] at ht; exact ht
lemma rigL (P:Plan j)(v:Train j)(U:On)(hu:Vital U)(n:Side): Loves (rollG P v U n):=by
  obtain ⟨r,C,hp,hH,h⟩:= lumber P
  let A:=fun x:Grid n=> wood P 0 v x
  let Q:= caravan P v U n∘input su n
  have H : ContDiffAt ℝ ω Q 0:=(matrix_g (F:=(A ∘ input su n)) fun i j=>(h n v i j).host).add ((hu.1 n).2.2.2.2)
  have he:=hu.1 n; let V x:= -Real.log ‖(caravan P v U n x).det‖
  have hm:IsUnit (Q 0).det:=by unfold Q; rw [Function.comp_apply,input_zero,(car_origin P v U n hu).1]; exact (car_origin P v U n hu).2
  apply groom V _ _ _ (tollsP Q H hm).1
  · intro x k; refine congr_arg (fun i:ℂ=> -Real.log ‖i‖) ?_; unfold caravan; rw [orbital,he.1,show siteRot k*_ *star _=aura (siteRot k) _ from rfl, ← aura_add,trustD _ _ (siteRot_u _)] -- inspect
  · intro i x; obtain ⟨d,hd⟩:=shades 1 0 0 i; let W:=hues i 1 d 1; have hp:= colour_wheel hd Swing.none
    have hx:= he.2.2.1 i d (rubber hd) x; rw [rubber_eq] at hx
    have hh : U n (pull 1 i x)=aura W (U n x):=by unfold aura; rw [← show _=W* _ from hx, Matrix.mul_assoc, show W*star W=1 from hp.2,mul_one]
    unfold V caravan; rw [hh,show wood P 0 v (pull 1 i x)=aura W (A x) from spin_wood hd Swing.none ..,← aura_add,trustD _ _ hp]
  intro s x; obtain ⟨d,hd⟩:=shades s (0:Site n) 0 0; unfold V caravan; rw [he.2.1.port x s d _ hd (fleetLeft s),spin_wood hd (fleetLeft s), ← aura_add,trustD _ _ (colour_wheel hd (fleetLeft s))]
end YM.QCD.Raft
