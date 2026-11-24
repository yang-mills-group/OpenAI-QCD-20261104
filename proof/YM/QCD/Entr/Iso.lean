import YM.QCD.Reggae.Lives
import YM.Next.WARD_BIN.Lies
/-! # unit directional price for charged fronts. All-field through startup. No global equivalence of norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae
open scoped BigOperators Topology ContDiff Classical Matrix
variable {c:Side}{N k:ℕ}{p:BudgetPoint}{η u a r t w:ℝ}{i j x:Site c}
open Push.Uniform WardBin.Lies Metric
section
open scoped Matrix.Norms.Frobenius
lemma trace_slot (k:ℕ∞ω)(i j:Hue):ContDiff ℝ k (fun X:su.Color=> colour (su.lieExp X) i j):=by
    have hp := su.exp_jet.of_le (show k ≤ ω from le_top); let L: su.Mat →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun x=> x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; exact L.contDiff.comp hp
end
open scoped Matrix.Norms.L2Operator
def grassT (x:su.Color):Mat:= colour (su.lieExp x)
lemma art_t : ContDiff ℝ ω grassT:=by
   let p (x:su.Color) (i j: Hue):= grassT x i j; let L:= LinearMap.toContinuousLinearMap ({ toFun:=fun f:Hue→ Hue→ℂ=> Matrix.of f,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl } : (Hue→Hue→ℂ)→ₗ[ℝ] Mat); exact L.contDiff.comp (show ContDiff ℝ ω p from contDiff_pi.mpr fun i=>contDiff_pi.mpr fun j=> trace_slot ω i j)
def render (k:ℕ): Mat→(Fin k→su.Color)→Panels k→Mat
   | U,A,V=>match k with
      | 0=>U
      | n+1=>render n (grassT (V 0 • A 0)*U) (Fin.tail A) (Fin.tail V)
lemma filming (U:Grid c)(e:Edge (Site c))(A:Slab su c k)(t:Panels k): colour (journey U k A t e)=render k (colour (U e)) (fun i=>A i e) t:=by
   induction k generalizing U with
   | zero=>rfl
   | succ k ih=>
     rw [show journey U (k+1) A t=journey (increment U (t 0 • A 0)) k (Fin.tail A) (Fin.tail t) from rfl,ih,render]; rfl
section
variable {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D]
lemma rendC (k:ℕ)(U:D→Mat)(A:D→ Fin k→su.Color)(V:D→Panels k)(h:ContDiff ℝ ω U)(he:ContDiff ℝ ω A)(ht:ContDiff ℝ ω V) : ContDiff ℝ ω (fun x=>render k (U x) (A x) (V x)):=by
    induction k generalizing U with
    | zero=>exact h
    | succ k ih=>
       simp only [render]; exact ih _ _ _ ((art_t.comp ((contDiff_pi.mp ht 0).smul (contDiff_pi.mp he 0))).mul h) (contDiff_pi.mpr fun i=> contDiff_pi.mp he i.succ) (contDiff_pi.mpr fun i=> contDiff_pi.mp ht i.succ)
end
lemma filmBudget (k:ℕ): ∃ C:ℝ, 1 ≤ C∧∀ (U:Mat)(A:Fin k→su.Color), ‖U‖≤1→ ‖A‖ ≤1 → Allows k (render k U A) 0 C ∧ Allows k (star ∘ render k U A) 0 C :=by
    let T:= Panels k; let F:=(Mat×(Fin k→su.Color)) × T; let Z (x:F):= render k x.1.1 x.1.2 x.2; have hF:ContDiff ℝ ω Z:=rendC k _ _ _ (contDiff_fst.fst) (contDiff_fst.snd) contDiff_snd
    let L:Mat→L[ℝ]Mat:= (starL' ℝ).toContinuousLinearMap
    have hF':ContDiff ℝ ω (L ∘ Z):= L.contDiff.comp hF
    let p:= closedBall (0:F) 1; obtain ⟨A,ha,h⟩:= exists_allows (s:=p) (isCompact_closedBall ..) (fun x _=> hF.contDiffAt (x:=x)) k
    obtain ⟨B,hB,H⟩:= exists_allows (s:=p) (isCompact_closedBall ..) (fun x _=> hF'.contDiffAt (x:=x)) k
    let K:ℝ:=max 1 ‖(ContinuousLinearMap.id ℝ T)‖; have hK:1≤K:=le_max_left ..; let C:=composeCost k (max A B) K
    refine ⟨max 1 C,le_max_left ..,fun U M hp hM=>?_⟩; let y: T → F:= fun x=> ((U,M),x); have hc : ‖(U,M)‖≤1:=max_le hp hM; have hh:y 0∈p:=by rw [mem_closedBall_zero_iff]; change max ‖_‖ ‖(0:T)‖ ≤ _; rw [norm_zero]; exact max_le hc zero_le_one
    have ht: Allows k y 0 K:=by apply Allows.pair (allows_const _ (hc.trans hK)); exact allows_linear (L:=ContinuousLinearMap.id ℝ T) (le_max_right ..) (by change ‖(0:T)‖ ≤ _; rw [norm_zero]; exact zero_le_one.trans hK)
    exact ⟨(((h _ hh).mono (le_max_left ..)).comp ht).mono (le_max_right 1 C),(((H _ hh).mono (le_max_right ..)).comp ht).mono (le_max_right 1 C)⟩
lemma optics (U:Grid c)(k:ℕ) : Push.Local.Chart k (settled: Grid c→Pulse c) U:=by
    let f (A:Directions su c):=settled (increment U A); have he:f=(fun x=>(fun e=> colourLink e (increment U x),fun e=>star (colourLink e (increment U x)))):=rfl
    change ContDiffAt ℝ _ f _; rw [he]; refine ContDiffAt.prodMk (contDiffAt_pi.mpr (fun i=> link_chart i U k)) (contDiffAt_pi.mpr fun i=>?_); exact (starL' ℝ (A:=Mat)).toContinuousLinearMap.contDiff.contDiffAt.comp 0 (link_chart i U k) -- syntax
lemma ashT (U: Grid c)(A:Slab su c k): journey U k A 0=U:=by rw [journey_photon, Function.comp_apply,map_zero,chug_zero]
-- norm bounds chug with threshold scaled normalization
lemma tourBud (k:ℕ):∃ C :ℝ,1 ≤ C ∧∀ (c:Side)(U: Grid c)(A: Slab su c k)(t:ℝ), 0<t→ t≤ 1 → (∀ i, ‖A i‖≤t)→ Allows k (fun x=> t⁻¹ • (settled (journey U k A x)-settled U)) 0 C:=by
   obtain ⟨C,h,hp⟩:=filmBudget k; refine ⟨C,h,fun c U V t ht hv hM=>?_⟩
   let A:Slab su c k:= t⁻¹ • V; have he (i:Fin k): V i=t • A i:=Eq.symm (smul_inv_smul₀ ht.ne' _)
   let L:Panels k→L[ℝ]Panels k:= t • ContinuousLinearMap.id ℝ (Panels k)
   have hh : journey U k V=journey U k A ∘ L:=by
       funext x; unfold journey; rw [comp_apply]; apply congr_arg; funext i; rw [he,show L x i=t • x i from rfl,smul_eq_mul,smul_smul,mul_comm]
   let Z:= settled ∘ journey U k A; have hZ:Allows k Z 0 C:=by
       let i (e:Edge (Site c)) (i:Fin k):= A i e
       have hf (e:Edge (Site c)): ‖i e‖≤1:= (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j=> by
          apply (norm_le_pi_norm (A j) e).trans; rw [show A j=t⁻¹ • V j from rfl,norm_smul, Real.norm_of_nonneg (by positivity : 0≤ t⁻¹), inv_mul_eq_div]; exact (div_le_one ht).2 (hM j)
       have hr e:= hp (colour (U e)) (i e) (rotation_price (U e).val.property) (hf e)
       let y (x:Panels k) (e:Edge (Site c)):= render k (colour (U e)) (i e) x
       rw [show Z=(fun x=> (y x, fun i=>star (y x i))) from ?_]; rotate_left
       · funext x; ext1
         · exact funext fun i=> filming ..
         exact funext fun i=> congr_arg star (filming ..)
       exact (allows_pi (f:=y) (zero_le_one.trans h) fun i=> (hr i).1).pair (allows_pi (zero_le_one.trans h) fun i=> (hr i).2)
   rw [hh]; let P:= Z ∘ L; have hG: ContDiffAt ℝ ω Z (L 0):=by rw [map_zero];exact hZ.analytic
   refine ⟨((hG.comp _ L.contDiff.contDiffAt).sub contDiffAt_const).const_smul _,fun i hi=>?_⟩
   change ‖iteratedFDeriv ℝ i (t⁻¹ • (P-fun _ => settled U)) 0‖ ≤ _
   by_cases hk:i=0
   · subst i; rw [norm_iteratedFDeriv_zero]; change ‖t⁻¹ • (settled _-settled U)‖ ≤ _; rw [map_zero,ashT,sub_self,smul_zero,norm_zero]; exact zero_le_one.trans h
   have hp': ContDiffAt ℝ (↑i) P 0:=(hG.comp 0 L.contDiff.contDiffAt).of_le le_top
   rw [iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ (↑i) (P-fun _=>settled U) 0 from hp'.sub contDiffAt_const), iteratedFDeriv_sub_apply hp' contDiffAt_const,iteratedFDeriv_const_of_ne hk]; rw [Pi.zero_apply,sub_zero,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]; unfold P; rw [WardBin.Lies.liner L (hG.of_le le_top),map_zero] 
   let W:= iteratedFDeriv ℝ i Z 0; have hx : W.compContinuousLinearMap (fun j=>L)= t^i • W:=by apply DFunLike.ext; intro a; change W _=t^i • W a; change W (fun j=> t • a j)=_; rw [ContinuousMultilinearMap.map_smul_univ]; simp -- lemma
   rw [show (iteratedFDeriv ℝ i Z 0)=W from rfl,hx,norm_smul,norm_pow,Real.norm_of_nonneg ht.le]; have ha : t^i ≤ t:= (pow_le_pow_of_le_one ht.le hv (show 1 ≤ i from Nat.one_le_iff_ne_zero.mpr hk)).trans_eq (pow_one _)
   rw [inv_mul_eq_div]; exact (div_le_iff₀ ht).2 ((mul_le_mul ha (hZ.norm_le _ hi) (norm_nonneg _) ht.le).trans_eq (mul_comm ..))
end YM.QCD.Entr
