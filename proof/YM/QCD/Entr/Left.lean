import YM.QCD.Entr.Iso
/-! # Pack to Woven Lie Jets. Native paths. Preserves continuity & arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{p:BudgetPoint}{η u a r t w:ℝ}{i j x:Site c}{X:Support c}
open Push.Uniform WardBin.Lies Metric
section cost
variable {D E:Type*} [NormedAddCommGroup D][NormedSpace ℂ D] [NormedAddCommGroup E][NormedSpace ℂ E]
open Stationary
lemma gustP (h:0<r)(k:ℕ)(f:D→E)(x:D)(hs:∀ U ∈ ball x r, ContDiffAt ℂ ω f U)(hp:∀ U∈ball x r, ‖f U‖ ≤ a):∀ y∈ball x (r/2^k),‖iteratedFDeriv ℂ k f y‖ ≤ a*circleTax r k :=by
   induction k with
   | zero => simpa [circleTax] using hp
   | succ k ih=>
       intro i hx; rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map, circleTax,← mul_div_assoc]; rw [show r/2^(k+1)=(r/2^k)/2 from by rw [pow_succ]; ring] at hx ⊢
       exact Run.wind (by positivity) (fun i hi=> (hs i (ball_subset_ball (div_le_self h.le (one_le_pow₀ (by norm_num))) hi)).differentiableAt_iteratedFDeriv (by simp)) ih hx
lemma windP [NormedSpace ℝ D][IsScalarTower ℝ ℂ D][NormedSpace ℝ E][IsScalarTower ℝ ℂ E](f:D→E)(n:ℕ)(x:D)(hs:∀ U∈ball x 1,ContDiffAt ℂ ω f U)(hp:∀ U∈ball x 1, ‖f U‖ ≤ a): Allows n f x (a*∑ i:Fin (n+1),circleTax 1 i.val):=by
   have ha:= hs x (mem_ball_self zero_lt_one); refine ⟨ha.restrict_scalars ℝ, fun i hi=>?_⟩
   rw [← (ha.of_le (m:=(i:ℕ∞ω)) le_top).restrictScalars_iteratedFDeriv, comp_apply,ContinuousMultilinearMap.norm_restrictScalars]; apply (gustP zero_lt_one i f x hs hp x (mem_ball_self (by positivity))).trans; exact mul_le_mul_of_nonneg_left (single_le_sum (fun (j:Fin (n+1)) _ => (circleTax_pos zero_lt_one j.val).le) (mem_univ (⟨i,by omega⟩:Fin (n+1)))) ((norm_nonneg _).trans (hp x (mem_ball_self zero_lt_one)))
end cost
variable {P:Pulse c→Bundle}(h:Crop i j η X P a) (hq:0 < t) (he:t≤η)
include h
lemma milady (hv:0<η)(U:Grid c)(k:ℕ): Push.Local.Chart k (P∘settled) U:=by
    have hp:= citizenship c hv U; have he:AnalyticAt ℂ P (settled U):=PolyDisc.finiteD _ (Filter.mem_of_superset ((country c η).mem_nhds hp) h.2.2.1)
    change ContDiffAt ℝ _ _ _; let T:= settled ∘ increment U; have hx : T 0=settled U:= congr_arg settled (Work.G07.at_zero_increment U)
    exact (show ContDiffAt ℝ (↑k) P (T 0) from hx.symm ▸ (he.contDiffAt.restrict_scalars ℝ)).comp 0 (optics U k)
lemma lends (o:Site c)(hi:o∈ X)(U:Grid c)(V W: Slab su c k)(he : ∀ i (e:Edge (Site c)),e.1∈X→V i e=W i e)(hk:0<η): leftDerivs (P ∘ settled) (List.ofFn V) U=leftDerivs (P∘settled) (List.ofFn W) U:=by
    rw [Germ.ordered V (milady h hk U k),Germ.ordered W (milady h hk U k)]; rw [show (P ∘ settled) ∘ journey U k V=(P∘settled) ∘ journey U k W from ?_]
    funext t; apply h.2.2.2.2.1; intro a h1 _
    apply su.mat_injective; change colour _=colour _; rw [filming,filming]; exact congr_arg (fun A=> render k (colour (U a)) A t) (funext fun i=> he _ _ h1)
omit h
open Stationary
lemma palaces (k:ℕ):∃ C:ℝ, 0 ≤ C∧∀ (c:Side)(X:Support c)(U:Grid c)(V:Slab su c k)(i j:Site c)(η t:ℝ) (P:Pulse c→Bundle)(a:ℝ),Crop i j η X P a → 0<t → t≤1 → t≤η → (∀ i, ‖V i‖ ≤ t) → ‖leftDerivs (P∘settled) (List.ofFn V) U‖ ≤ C*a:=by
    obtain ⟨C,hC,h⟩ := tourBud k
    let K:= ∑ i:Fin (k+1), circleTax 1 i.val; have hx : 0 ≤ K:=sum_nonneg fun i _=> (circleTax_pos zero_lt_one i.val).le
    refine ⟨composeCost k K C,by unfold composeCost; positivity,fun c X U V i j η t P a hP ht he hv hq=>?_⟩
    let g (Z:Pulse c):= settled U+(t:ℂ) • Z; have hh x (hz:x∈ball 0 1): g x∈Kingdom c η:=by
       apply Set.mem_iUnion.mpr; refine ⟨U, lt_of_lt_of_le ?_ hv⟩; unfold g; rw [dist_eq_norm,add_comm _ ((t:ℂ) • x),add_sub_cancel_right,norm_smul,Complex.norm_real,Real.norm_of_nonneg ht.le]; exact mul_lt_of_lt_one_right ht (mem_ball_zero_iff.mp hz)
    let f:= P ∘ g; have hs x (hz:x∈ball 0 1): ContDiffAt ℂ ω f x:=(PolyDisc.finiteD _ (Filter.mem_of_superset ((country c η).mem_nhds (hh x hz)) hP.2.2.1)).contDiffAt.comp x (by unfold g; fun_prop)
    let Z (x:Panels k):=t⁻¹ • (settled (journey U k V x)-settled U); have hZ: Z 0=0:=by unfold Z; rw [ashT,sub_self,smul_zero]
    have hL:P ∘ settled ∘ journey U k V=f ∘ Z:=by
       funext x; unfold f g Z; simp only [Function.comp_apply]; congr 1; rw [show (t:ℂ) • _=t • (t⁻¹•(settled _-settled U)) from ?_,smul_inv_smul₀ ht.ne']; abel
       simp [Complex.coe_smul]
    have hY : Allows k (f ∘ Z) 0 (composeCost k (a*K) C):=Allows.comp (f:=Z) (g:=f) (show Allows k f (Z 0) (a*K) from by rw [hZ]; exact windP f k 0 hs (fun x hv=> hP.2.2.2.1 (g x) (hh _ hv))) (h _ U V t ht he hq)
    let Y:=iteratedFDeriv ℝ k (f ∘ Z) 0; rw [Germ.ordered V (milady hP (ht.trans_le hv) U k), Function.comp_assoc,hL]; have he (i:Fin k): ‖(@WardBin.Lies.cart k i)‖=1:=by simp [WardBin.Lies.cart,Pi.norm_single]
    change ‖Y _‖≤_
    apply (Y.le_opNorm _).trans; simp only [he,prod_const_one,mul_one]; exact (hY.norm_le _ le_rfl).trans_eq (by unfold composeCost; ring)
lemma drops (B n R:ℕ):∃ C:ℝ,0≤C∧∀ (c:Side)(p:BudgetPoint)(P: Pulse c→Bundle)(η a:ℝ) (i j o:Site c) (X:Support c), o∈X→p.power ≤ R→p.order ≤ n→ p.threshold ≤η → Crop i j η X P a→ ∀ l:List (Directions su c), l.length ≤ p.order → (∀ x∈l,p.dirBound o x) →∀ U:Grid c, let D:=coverNumber B X*(4*B+2)+2*B; ‖leftDerivs (P ∘ settled) l U‖ ≤ (1+(D:ℝ))^(R*n)*(C*a):=by
    choose T hT H using palaces; let C:= ∑ j :Fin (n+1), T j.val; have hb:0≤C:=sum_nonneg fun i _=> hT _
    refine ⟨C,hb,fun c p P η a i j o X ho he hw hv hP l hl hQ U=> ?_⟩; intro D; let k:= l.length; let V:= l.get; let A(x:Fin k)(e: Edge (Site c)):= if e.1∈X then V x e else 0; let r:ℝ:=1+D; let t:=r^p.power; have hr:1≤r:=by unfold r; simp
    have ht:=one_le_pow₀ hr (n:=p.power); have ht':0<t:=zero_lt_one.trans_le ht; let Q:Slab su c k:= t⁻¹ • A
    have hp :0<η:=p.threshold_pos.trans_le hv; rw [← List.ofFn_get l]; rw [lends hP o ho U V A (fun i e he=> (if_pos he).symm) hp,Germ.takes (milady hP hp U k) A le_rfl];
    have hu (i: Fin k): ‖Q i‖ ≤ p.threshold :=by
       rw [show Q i=t⁻¹ • (A i) from rfl,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht'.le),inv_mul_eq_div]; apply (div_le_iff₀ ht').2; apply (pi_norm_le_iff_of_nonneg (mul_nonneg p.threshold_pos.le ht'.le)).2; intro e; unfold A; split
       next hi=> apply (hQ (l.get i) (l.get_mem i) e).trans; apply mul_le_mul_of_nonneg_left _ p.threshold_pos.le; apply pow_le_pow_left₀ (by positivity); unfold r; gcongr; exact Corona.extent X B hi ho
       next _=> rw [norm_zero]; exact mul_nonneg p.threshold_pos.le ht'.le
    have hh:= H k c X U Q i j η p.threshold P a hP p.threshold_pos p.threshold_le hv hu; let M:=WardBin.Lies.mixed (P∘settled) k U; have hy: M A=t^k • M Q:=by
       have hz:A=fun i=>t • Q i:= funext fun i=>Eq.symm (smul_inv_smul₀ ht'.ne' _); rw [hz,ContinuousMultilinearMap.map_smul_univ]; simp
    change ‖M A‖ ≤ _; rw [hy,norm_smul,norm_pow,Real.norm_of_nonneg ht'.le]; rw [Germ.takes (milady hP hp U k) Q le_rfl] at hh; change t^k * _≤ r^(R*n)*_ ;
    apply mul_le_mul _ (hh.trans (mul_le_mul_of_nonneg_right (single_le_sum (fun (j:Fin (n+1)) _=>hT j.val) (mem_univ (⟨k,by unfold k;omega⟩:Fin (n+1)))) hP.1)) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hr) _)
    unfold t; rw [← pow_mul]; gcongr; exact hl.trans hw
end YM.QCD.Entr
