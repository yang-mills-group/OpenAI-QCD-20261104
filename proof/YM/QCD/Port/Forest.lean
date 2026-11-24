import YM.QCD.Port.Oyster
/-! # diagonal scalar accountant (signed). priced arith orientation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port.AtomF
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra Iteration Rudder
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{v η A t δ σ :ℝ}{B b k:ℕ}
variable (W:ℕ→Atom su k)
-- use field forms row cell trace.
def per (p: Strut f)(U:Grid f)(x:Site f):ℝ:=∑' i,(W i).unmasked (sky p U) ((act p).symm x)
def pane (p : Strut f)(U:Grid f):Sheet f:= field fun x=> (per W p U x :ℂ)
lemma lace (hc: Charged W σ A) (hs:0<σ)(p:Strut f)(U:Grid f)(x:Site f): HasSum (fun i=> hatch (W i) p x (settled U)) (per W p U x:ℂ):=by
   simp_rw [settledP]; exact Complex.hasSum_ofReal.mpr (Summable.hasSum (Summable.of_norm_bounded ((hc.absolute hs.le).mul_right _) (fun i=> (W i).unmasked_bound ..))) -- signature
lemma horn (hp: Charged W σ A)(hs:0 < σ)(p: Strut f)(U:Grid f): HasSum (fun i=> frostW (W i) p U) (pane W p U):=by
   let K: (Site f→ℂ) →L[ℂ] Sheet f:= LinearMap.toContinuousLinearMap {
     toFun:=field
     map_add':=fun x y=>by ext ⟨i,j⟩ ⟨p,q⟩; simp only [field,rr, Matrix.smul_apply,Pi.add_apply,smul_eq_mul,add_mul, Matrix.add_apply]; split_ifs <;> simp
     map_smul':=fun x y=>by unfold field; rw [ride_smul]; apply congr_arg _; ext1 i; rw [Pi.smul_apply,smul_eq_mul]; exact (smul_smul _ _ _).symm }
   have he : HasSum (fun i x=> hatch (W i) p x (settled U)) (fun i=>(per W p U i:ℂ)):=by refine tendsto_pi_nhds.mpr (fun x=>?_); simp only [Finset.sum_apply]; exact lace W hp hs p U x
   have hK (x): K x=field x:=rfl
   have hh:=K.hasSum he; simp only [hK] at hh; exact hh

abbrev rays :=(Fintype.card Fiber:ℝ)
lemma ray_pos :0<rays:=by unfold rays; exact_mod_cast Fintype.card_pos
def visitsN :=(Fintype.card Signed:ℝ)
lemma vnpos:0<visitsN:=by unfold visitsN; exact_mod_cast Fintype.card_pos
abbrev keeper (a:Signed) (n:Side):Strut n := (a,0)
def robe (U:Grid f):Sheet f:=(↑((rays*visitsN)⁻¹:ℝ):ℂ) • ∑ s,pane W (keeper s f) U
lemma robe_price (hs:0<σ)(A C:ℝ)(ht:0≤t)(k:ℕ): ∃ R δ:ℝ,0 < R∧0<δ∧∃ M:ℕ,∀ (f:Side)(B:ℕ),M≤B→∀ W:ℕ→Atom su k,Charged W σ A → SymmetricAtoms W → Own f δ t B (robe W) R:=by
   obtain ⟨C,δ,h,hδ,l,hh⟩:= armor hs t ht k
   let u:ℂ:=↑((rays*visitsN)⁻¹:ℝ); let R:=‖u‖ * visitsN * (C*A)
   refine ⟨1+|R|,δ,by positivity,hδ,l,fun f B hb W hW hp=>?_⟩
   have he (s:Signed):Own f δ t B (pane W (keeper s f)) (C*A):=by
      apply (Heritage.congregation (p:=fun i=>C*(W i).budget σ) hδ ht (fun i=> hh B hb f (W i) (keeper s f) (hp i)) (hW.2.1.mul_left C) (horn W hW hs (keeper s f))).mono; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hW.2.2 h.le
   have ht := (Heritage.joined univ (fun i=> pane W (keeper i f)) (fun i _ => he i)).scalar u -- names
   simp only [sum_const,card_univ,nsmul_eq_mul] at ht; have hu:‖u‖*((Fintype.card Signed:ℝ)*(C*A)) ≤ 1+|R|:=by rw [← mul_assoc]; exact (le_abs_self R).trans (le_add_of_nonneg_left zero_le_one)
   exact ht.mono hu
lemma reporting (U:Grid f): ∑ i:Site f,(Run.cell (robe W U) i i).trace.re=Iteration.action W U:=by
   let C:=((rays*visitsN)⁻¹:ℝ); let V (i:Site f):=∑ s,per W (keeper s f) U i
   have hh i : Run.cell (robe W U) i i=((C*V i:ℝ):ℂ) • 1:=by
     rw [robe,cell_scale]; rw [show cell (∑ s,pane W (keeper s f) U) i i=∑ s,cell (pane W (keeper s f) U) i i from ?_]; rotate_left
     · ext a b; simp [Run.cell,Matrix.sum_apply] -- check
     have he s:cell (pane W (keeper s f) U) i i=((per W (keeper s f) U i:ℂ)) • 1:=by ext a b; exact if_pos rfl
     simp_rw [he]; rw [← sum_smul, smul_smul, ← Complex.ofReal_sum,← Complex.ofReal_mul]
   simp_rw [hh, Matrix.trace_smul,Matrix.trace_one]; change (∑ i, (((C*V i:ℝ):ℂ) * (Fintype.card Fiber:ℂ)).re)=_
   simp_rw [show ∀ x:ℝ, ((x:ℂ)*(Fintype.card Fiber:ℂ)).re=x*rays from fun x=>by simp [rays]]
   unfold V; simp_rw [mul_sum,sum_mul]; rw [sum_comm]; unfold Iteration.action Patch.average Precision.uncut; rw [mul_sum]; refine sum_congr rfl fun i _=>?_; rw [← Equiv.sum_comp (act (keeper i f))] -- maybe wrong side
   simp only [per,Equiv.symm_apply_apply]
   rw [mul_sum]; refine sum_congr rfl fun x _=>?_ ; unfold C visitsN; field_simp [ray_pos.ne']
   rfl -- denominator
lemma pass (p:Strut f)(y: Site f)(U:Grid f)(x:Site f): per W (p.1,y) U x=per W (p.1,0) U x:=by
   let z: Strut f:=(1,p.1⁻¹.act y); let t: Strut f:=(p.1,0)
   have he : pod t z=(p.1,y):=by unfold pod t z affine; simp [← Signed.act_mul]
   rw [← he]; unfold per; rw [← skying,podA]; apply tsum_congr; intro i; unfold Atom.unmasked
   apply congr_arg (W i).poly; funext j; unfold Slot.atSite
   rw [sky, expandAt_pull]; change _= _; rw [show z.1=1 from rfl,pull_id]; rw [show affine 1 z.2 ((Equiv.symm _) x)=(act t).symm x from (act z).apply_symm_apply _] -- fill
lemma s_sender (p q : Strut f)(U:Grid f)(x): per W p (sky q U) x=per W (q.1*p.1,0) U (act q x):=by
    have he : per W p (sky q U) x=per W (pod q p) U (act q x):=by rw [per,per,skying,podA]; simp
    rw [he]; exact pass W (pod q p) (pod q p).2 U _
lemma pane_turn (p q : Strut f)(H:Spike)(χ:Site f→ℂ)(hχ: Warrant q χ H) (U:Grid f):pane W p (sky q U)=aura (haze q H χ) (pane W (q.1*p.1,0) U):=by
   let X := haze q H χ; have ht:=trail hχ
   let Q:= pane W p (sky q U)
   have he: Q * X=X * pane W (q.1*p.1,0) U:=by
     unfold Q pane X haze field hues; rw [ride_mul,ride_mul]; apply congr_arg₂ rides; · rfl
     -- type matches? Spin vs mat
     funext i; dsimp only; rw [s_sender]; simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul,Equiv.refl_apply,smul_comm (χ i) (↑_:ℂ)]
     rfl
   unfold aura; rw [← he,Matrix.mul_assoc,show X*star X=1 from ht.2,mul_one]
lemma unveils (r: Ratio c f):Tow r (sun r) (sun r) (robe W):=by
   refine ⟨fun p u T U h=>?_⟩; unfold robe
   let F:= raise r p; let K:=haze F T u
   have he (s:Signed):pane W (keeper s f) (sky (raise r p) U)=K*pane W (keeper (Equiv.mulLeft p.1 s) f) U*star K:= pane_turn W _ _ T u h _
   simp_rw [he,← Matrix.sum_mul,← Matrix.mul_sum]; rw [show ∑ i:Signed,pane W (keeper (Equiv.mulLeft p.1 i) f) U=∑ i:Signed,pane W (keeper i f) U from Equiv.sum_comp (Equiv.mulLeft p.1) (fun i=>pane W (keeper i f) U)]; rw [Matrix.mul_smul,Matrix.smul_mul]; rfl
lemma none_to_pay (hk:0<k): robe (f:=f) W 1=0:=by
   have hv p: pane W (keeper p f) 1=0:=by
     let q:=keeper p f; have h : sky q 1=1:=by funext i; unfold sky pull Step.read; simp
     have he x:per W q 1 x=0:=by unfold per; rw [h]; simp_rw [Atom.unmasked, Bloom.slot_tail, Atom.poly]; simp_rw [show ∀ (b:Fin k → su.ColorIndex), (∏ i,(0:su.Color) (b i))=0 from fun b=> prod_eq_zero (mem_univ (⟨0,hk⟩:Fin k)) rfl]; simp
     change pane W q 1=0
     unfold pane field; simp_rw [he]; simp [ride_zero] -- maybe rw
   unfold robe; simp [hv]
end YM.QCD.Port.AtomF
