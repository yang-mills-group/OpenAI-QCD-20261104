import YM.Pollen.Pits
import YM.Helio.Gate
import YM.Massive.PCAC.Bare
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Lat Function Lattice Wilson Creek Grass Ledge Lat Finset NormedSpace RG Cove Cove.Send Filter Run
open MeasureTheory QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k N:ℕ}{t a b:ℝ}{o: Site c} {P:BudgetPoint}
open Further.DenseMixedKernels
local notation "M"=> Modes c N
local notation "Q"=>Sour M
set_option quotPrecheck false
local notation "ν" V:arg W:arg=> fun X:Grid c=>(applyMark false (V X) - applyMark true (W X)).toContinuousLinearMap
variable (x y:Grid c→ Sour (Modes c N))
local notation "Y"=> ν x y
variable {i j:Site c}{O:BudgetPoint}
private lemma translate {d : ℝ} (hh : (separation i j:ℝ) ≤ d) {A : Directions su c} (h : O.dirBound j A) :
    O.dirBound i ((((1+d)^O.power)⁻¹:ℝ) • A) := by
  have hd : 0 ≤ d := (Nat.cast_nonneg _).trans hh
  intro p; let t := (1+d)^O.power; have hp : 0 < t := by unfold t; positivity
  change ‖t⁻¹ • A p‖ ≤ _
  rw [norm_smul_of_nonneg (inv_pos.mpr hp).le,inv_mul_le_iff₀ hp]
  refine (h p).trans ?_
  rw [mul_left_comm, show t=(1+d)^O.power from rfl,←mul_pow]; have hb := O.threshold_pos; gcongr
  have he : (separation p.1 j:ℝ) ≤ separation p.1 i + (separation i j:ℝ) := by exact_mod_cast separation_triangle p.1 i j
  nlinarith [Nat.cast_nonneg (α:=ℝ) (separation p.1 i)]
private lemma left_turn {F:Type} [NormedAddCommGroup F][NormedSpace ℝ F] (u : Config su c → F) (v : List (Directions su c)) (a : ℝ) (U : Config su c) :
    leftDerivs u (v.map fun A => a • A) U = a^v.length • leftDerivs u v U := by
  induction v generalizing U with
  | nil => simp [leftDerivs]
  | cons x v ih =>
    simp only [List.map_cons,leftDerivs,ih, deriv_fun_const_smul_field]
    have hi (t : ℝ) : t • a • x = (a*t) • x := by rw [smul_smul, mul_comm]
    simp_rw [hi]
    let G (t : ℝ) := leftDerivs u v (increment U (t • x))
    change a^v.length • deriv (fun t => G (a*t)) 0 = _
    rw [deriv_comp_mul_left, mul_zero, smul_smul,List.length_cons,pow_succ]
lemma pitch_m (f: Grid c→ℂ){V:Grid c}(h:Pitch f V (O.dirBound i) O.order t 1): Pitch f V (O.dirBound j) O.order t ((1+(separation i j:ℝ))^O.power):=by
    refine ⟨h.smooth,fun l hl hL=>?_⟩
    let v:=(1+(separation i j:ℝ))^O.power; have hv:0<v:=(by unfold v; positivity); let x:= l.map (fun z=>v⁻¹ • z); have hh:x.length=l.length:=List.length_map ..; have hh': x.map (fun z=>v • z)=l:=by simp [x,v,hv.ne',Function.comp_def]; try fun_prop
    rw [← hh',left_turn,norm_smul,norm_pow,Real.norm_of_nonneg hv.le, List.length_map]; have hp: ‖leftDerivs f x V‖ ≤ t:=by simpa only [one_pow,mul_one] using h.bounds x (hh.trans_le hl) (fun i hi=> by obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi; exact translate le_rfl (hL j hj))
    exact (mul_le_mul_of_nonneg_left hp (pow_nonneg hv.le _)).trans_eq (by rw [hh']; exact mul_comm .. )
variable (h:Fetch o false x P a)
include h
lemma flowback : Fetch o true (fun i=>-star (x i)) P a:=by
    refine ⟨fun i j hz=>congr_arg (fun k=>-star k) (h.reads _ _ hz),fun i j V hx=>?_,fun U g=>by rw [h.gauge]; simp [mul_assoc],h.nz, ?_⟩ -- goal star assoc
    · apply h.reach j i V; intro he; apply hx; simp [he]
    obtain ⟨f,hf,H⟩:=h.sale; refine ⟨fun i j=>f j i,?_,fun i j=>?_⟩; · rw [sum_comm]; exact hf
    let L:= fun k:Grid c=> x k j i; obtain ⟨hy,hk,hh⟩:=H j i; refine ⟨hy,hk.star.neg,fun z i=>?_⟩
    let V:=hh z i; let g:=Complex.conjCLE; have hp:= V.linear g.toContinuousLinearMap (C:=1) (fun z=> by simp [g]) zero_le_one; simp only [one_mul] at hp; exact hp.negate
omit h
open QCD.Jets Jets.Sun
noncomputable def voucher (N:ℕ) (a:ℝ):ℝ:= fingers N^2*(81*a)
lemma pointFetch (he:LocalOn (halo 1 {o}) x)(hv:∀ i j U,x U i j ≠ 0→ rangeH o (halo 1 {o}) i j)(hG:∀ U g,x (Lattice.gauge g U)= Lat.rotates N g*x U*star (Lat.rotates N g))(hp:∀ i j, Continuous (fun U=>x U i j))(hF:∀ i j z,Pitch (fun U=> x U i j) z (P.dirBound o) P.order a 1)(hn:0 ≤ a): Fetch o false x P (voucher N a):=by
    let W:=halo 1 {o}; let f i j:=if i=o ∧ j∈ W then a else 0; let g(i j:M):=f (headF i) (headF j); have hg(i j:M):0 ≤ g i j:=ite_nonneg hn le_rfl; refine ⟨he,hv,hG,mul_nonneg (sq_nonneg _) (by positivity),g,?_,fun i j=> ⟨hg i j,hp i j,fun U z=>?_⟩⟩
    · refine (paddleB (F:=N) 0 W 0 g f fun i j=> le_rfl).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)); unfold f; rw [sum_eq_single o]; rotate_left
      · intro i _ hi; simp [hi]
      · simp
      simp only [true_and,← Finset.sum_filter]; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hn; rw [show (Finset.filter _ Finset.univ)= W from ?_]; exact_mod_cast (Corona.halo_size {o} 1).trans (by norm_num); ext; simp
    apply pitch_m _; by_cases he:rangeH o W i j; · rw [show g i j=a from if_pos he]; exact hF _ _ _
    rw [show (fun U=>x U i j)=fun _=>(0:ℂ) from funext fun U=>by_contra fun h=>he (hv _ _ _ h), show g i j=0 from if_neg he]; simpa using Pitch.fixed (0:ℂ) zero_le_one (U:=U) (P:=P.dirBound o) (k:=P.order)
lemma plusP (Y':Bool)(hx:Fetch o Y' x P a)(hy:Fetch o Y' y P b):Fetch o Y' (x+y) P (a+b):=by
   refine ⟨fun i j h=>congr_arg₂ (·+·) (hx.reads _ _ h) (hy.reads _ _ h),fun i j V h=> Classical.byCases (fun hh:x V i j=0=> hy.reach _ _ V (fun hp=>h (by change x _ _ _+y _ _ _=_; rw[hh,hp,add_zero]))) (hx.reach i j V),fun U g=> by simp only [Pi.add_apply,mul_add,add_mul]; rw [hx.gauge,hy.gauge],add_nonneg hx.nz hy.nz,?_⟩
   obtain ⟨f,hf,F⟩:= hx.sale; obtain ⟨g,hg,G⟩:=hy.sale; refine ⟨fun i j=> f i j+g i j, by simp only [sum_add_distrib]; exact add_le_add hf hg, fun i j=>⟨add_nonneg (F i j).1 (G i j).1,(F i j).2.1.add (G i j).2.1,fun z o'=>((F i j).2.2 z o').plus ((G i j).2.2 z o')⟩⟩
lemma scaleP (z:ℂ)(Y':Bool)(hx:Fetch o Y' x P a):Fetch o Y' (z • x) P (‖z‖*a):=by
   refine ⟨fun i j h=>congr_arg (z • ·) (hx.reads _ _ h),fun i j U h=>hx.reach _ _ _ (fun he=>h (by change z • (x U i j)=_; rw[he,smul_zero])),fun U g=> by rw [Pi.smul_apply,Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, hx.gauge],mul_nonneg (norm_nonneg _) hx.nz,?_⟩
   obtain ⟨f,hf,hF⟩:= hx.sale; refine ⟨fun i j=>‖z‖*f i j, by simp only [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hf (norm_nonneg _),fun i j=>⟨mul_nonneg (norm_nonneg _) (hF i j).1, (hF i j).2.1.const_smul z, fun U o'=>?_⟩⟩
   let g:= (z • ContinuousLinearMap.id ℝ ℂ); exact ((hF i j).2.2 U o').linear g (fun x=> (norm_smul z x).le) (norm_nonneg _)
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.flowback
#print axioms YM.Massive.PCAC.pointFetch
