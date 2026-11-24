import YM.QCD.Smoke.Wind

/-! # jet billing to winded power arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {c f C F:Side}{M:ℕ}{K:KernelChoices}{r D A u:ℝ}
lemma window_price (L:Window c C M)(v:Cnr c) : ‖expandC L v‖≤‖v‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun x=> norm_le_pi_norm v _
private lemma mixroll (T: Cnr C→Sheet F)(v w:Cnr C) :
    iteratedFDeriv ℝ 2 T 0 ![v,w]=∑ p:Fin 2→Road C,(∏ j, (![v,w] : Fin 2→ Cnr C) j (p j)) • Push.Uniform.entry T 0 p:=by
  let x:Fin 2→Cnr C:= ![v,w]; let M:=iteratedFDeriv ℝ 2 T 0
  nth_rw 1 [show ![v,w]=(fun i=>∑ j:Road C,x i j • Push.Uniform.bolt j) from funext fun i=>bolt_add (x i)] -- might rw rhs
  rw [blast (X:=Cnr C)]; apply sum_congr rfl; intro p _; exact M.toMultilinearMap.map_smul_univ _ _
-- adjust impl

def seedG (r D:ℝ):ℝ:= D*((Fintype.card (Exterior.TypeFace 1 × su.ColorIndex):ℝ)*countCost r)^2
lemma seedG_nn (hp:0≤D):0≤seedG r D:=mul_nonneg hp (sq_nonneg _)
lemma grantP {g:Ratio C F}(T:Cnr C→Sheet F)(v w:Cnr C)(hp:0<r)(ha:0≤D)(h : Eyrie.glyph (beam g) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst T r D)(x y:Row F):
    ‖Jacobi.mixed v w T 0 x y‖≤ seedG r D * ‖v‖ * ‖w‖ * Decay r x.1 y.1:=by
  have he : ContDiffAt ℝ ω T 0:= matrix_g fun i j=> (h i j).host; let Q:= (h x y)
  let W:= ![v,w]; let B i (a:Road C):= ‖W i‖*Decay r x.1 (beam g a)
  let Z := Decay r x.1 y.1
  have hh (p:Fin 2→Road C): ‖((∏ i,W i (p i)) • Push.Uniform.entry T 0 p) x y‖ ≤ D*Z*∏ i,B i (p i) :=by
    let a i := Push.Uniform.bolt (p i)
    have hk : Push.Uniform.entry T 0 p=Jacobi.mixed (a 0) (a 1) T 0:=by rw [entry,iter _ _ he,show (fun i=> Push.Uniform.bolt (p i))=![a 0,a 1] from funext fun i=> by fin_cases i <;> rfl]
    let d(a:Road C):=Decay r x.1 (beam g a)
    have hx: ‖Push.Uniform.entry T 0 p x y‖≤ D*Z * (d (p 0)*d (p 1)):=by rw [hk, detail_sq he]; exact (h x y).wandered (p 0) (p 1)
    rw [Matrix.smul_apply,norm_smul, norm_prod]; apply (mul_le_mul (prod_le_prod (s:=univ) (fun i _=>norm_nonneg (W i (p i))) (fun i _=> norm_le_pi_norm (W i) (p i))) hx (by positivity) (prod_nonneg (fun _ _=> norm_nonneg _))).trans_eq
    rw [Fin.prod_univ_two, Fin.prod_univ_two]; unfold B d; ring
  rw [iter _ _ he, mixroll, Matrix.sum_apply]
  apply (norm_sum_le ..).trans; apply (sum_le_sum (s:=univ) (fun i _=> hh i)).trans; rw [← mul_sum, ← Fintype.prod_sum, Fin.prod_univ_two]
  have hx:= multIJ (I:=Exterior.TypeFace 1 × su.ColorIndex) g; let q:ℝ:= Fintype.card (Exterior.TypeFace 1 × su.ColorIndex); let L:=q*countCost r
  have hP i : ∑ a:Road C,B i a≤ ‖W i‖*L:=by unfold B; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Multiplicity.count (beam g) hx hp _) (norm_nonneg _)
  have hz i : 0 ≤ ∑ a:Road C,B i a:=sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) (decay_pos ..).le
  apply (mul_le_mul_of_nonneg_left (mul_le_mul (hP 0) (hP 1) (hz 1) ((hz 0).trans (hP 0))) (mul_nonneg ha (decay_pos ..).le)).trans_eq; change D*Decay r x.1 y.1*((‖v‖*L)*(‖w‖*L))= _; unfold seedG L q; ring
lemma profile_h (g:Ratio c f)(x:Site c) : ∃ L: Sheet f→L[ℝ] ℝ,∀ M,L M=heartP g M x:=by
  let T: Sheet f→ₗ[ℝ] ℝ:= { toFun:=fun M=>heartP g M x,map_add':=by intro i j; simp only [heartP,cell_add,Matrix.trace_add,Complex.add_re,sum_add_distrib,neg_add],map_smul':=fun i M=>by
                                    unfold heartP; simp [Run.cell,Matrix.trace,Matrix.diag,Complex.re_sum,Finset.mul_sum] }
  exact ⟨T.toContinuousLinearMap,fun _=>rfl⟩
variable {P:Patch}{e:f.val=c.val*P.L.val}{E:F.val=C.val*P.L.val}
lemma roll_out {Y:Cnr c→Sheet f}{Z:Cnr C→Sheet F} (B:Lace (P:=P) e E M)(x:Site C){p:Site F→ℂ}(hk: Quaint B.high p)(ht:∀ᶠ z in 𝓝 0,Z (expandC B.low z)*stream B.high p=stream B.high p*Y z)(hp:0<r)(ha:0≤D)(h:Eyrie.glyph (beam B.R) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst Z r D)(hX:ContDiffAt ℝ ω Y 0)(v w:Cnr c):
    ‖Jacobi.mixed v w (fun y=>heartP B.r (Y y) (B.low.cut x)) 0 - Jacobi.mixed (expandC B.low v) (expandC B.low w) (fun y=>heartP B.R (Z y) x) 0‖ ≤ (Fintype.card (Site P.L):ℝ) * lantern (seedG r D*‖v‖*‖w‖) r * Real.exp (-(r/2)*f.val):=by
  obtain ⟨L,hL⟩:=profile_h B.r (B.low.cut x)
  obtain ⟨K,hK⟩:= profile_h B.R x
  let a:= expandC B.low
  have hT: ContDiffAt ℝ ω Z 0:= matrix_g fun i j=> (h i j).host
  rw [show (fun y=> heartP B.r (Y y) _)= L∘Y from funext fun _=>(hL _).symm,show (fun y=> heartP B.R (Z y) _)=K∘ Z from funext fun _=> (hK _).symm, retold _ _ _ hX,retold _ _ _ hT,hL,hK]; unfold heartP
  let Q:= stream B.high p
  let S:= Jacobi.mixed v w Y 0
  let T:=Jacobi.mixed (a v) (a w) Z 0
  have he:T*Q=Q*S:=by
    let A : Sheet F→L[ℝ] Rail F f:=LinearMap.toContinuousLinearMap { toFun:=fun i=>i*Q,map_add':=fun _ _=>Matrix.add_mul ..,map_smul':=fun _ _=>Matrix.smul_mul .. }
    let D : Sheet f→L[ℝ] Rail F f:=LinearMap.toContinuousLinearMap { toFun:=fun i=>Q*i,map_add':=fun _ _=>Matrix.mul_add ..,map_smul':=fun _ _=>Matrix.mul_smul .. }
    change (A ∘ Z ∘ a)=ᶠ[𝓝 0] D∘Y at ht
    have hM : ContDiffAt ℝ ω Z (a 0):=map_zero a ▸ hT; have hv:= repeated v w ht; rw [retold _ _ D hX, retold _ _ A (hM.comp (f:=a) _ a.contDiff.contDiffAt), adapt a _ _ hM, map_zero] at hv; exact hv
  let d:=seedG r D
  have hd:0≤d:=seedG_nn ha
  have hZ : 0≤ d*‖v‖*‖w‖:=by positivity
  have hh (i:Site P.L):‖(Run.cell S (B.r.assemble (B.low.cut x,i)) (B.r.assemble (B.low.cut x,i))).trace.re - (Run.cell T (B.R.assemble (x,i)) (B.R.assemble (x,i))).trace.re‖ ≤ lantern (d*‖v‖*‖w‖) r*Real.exp (-(r/2)*f.val):=by
    rw [← B.regions]; apply draft _ _ _ p B.high hk he hZ hp; let q:=B.R.assemble (x,i)
    intro y j; apply (grantP Z (a v) (a w) hp ha h (q,j) (y,j)).trans; change d*‖a v‖*‖a w‖*Decay _ _ _≤_; gcongr; exacts [(decay_pos ..).le,window_price ..,window_price ..] -- inspect
  rw [sub_neg_eq_add, neg_add_eq_sub, norm_sub_rev,← sum_sub_distrib]; apply (norm_sum_le ..).trans; apply (sum_le_sum (s:=univ) (fun i _=>hh i)).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ,mul_assoc]; ring
end YM.QCD.Smoke
