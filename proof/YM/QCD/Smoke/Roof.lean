import YM.QCD.Smoke.Kite

/-! # rejoin anchored estimates, establish received χ jets at all periods -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {E:Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a:ℝ}{M: Before su u v E.J K N}
variable (V:Back E K j k p u v)(J:Plan j){U:On}
variable (hp:Arbor J E.L k 1 w q g R δ Y B)(hU:Vital U)(hr:0<r)(he:0≤D)(h:Plume V J M U r D w)

def skyline (U:On)(w:ℝ):Skyline V.chain:= fun i=>scent V J U w i 0
def summaryP (U:On) (w:ℝ)(i:ℕ)(x:Cnr (V.chain.n i)):= ∑ j,scent V J U w i j x
include hU hr he h
lemma incensed (i): Cigar (skyline V J U w i) r (creditP E r D):= ⟨revenueP V J hU hr he h i 0, fun _=> paletteP (V.port.critical i) (V.port.admiss i) V.port.paid (hU.1 _) w J 0 _, preserve (V.port.critical i) (V.port.admiss i) V.port.paid (hU.1 _) w J 0⟩
lemma summedP (i): ContDiffAt ℝ ω (summaryP V J U w i) 0:=ContDiffAt.sum fun _ _=> (revenueP V J hU hr he h _ _).host
lemma emptyP (i)(x:Cnr (V.chain.n i)): blade x (summaryP V J U w i) 0=0:=by
  rw [show blade x (summaryP V J U w i) 0=_ from (series x (F:=fun y=>scent V J U w i y) (S:=univ) (fun _ _=> (revenueP V J hU hr he h _ _).host))]
  refine sum_eq_zero fun p _=>?_ ; have he : skyline V J U w i ∘ spaceShift p=ᶠ[𝓝 0] scent V J U w i p:=by
    have hh:=zodiac (V.port.critical i) (V.port.admiss i) V.port.paid (hU.1 _) w J 0 p; rw [zero_add] at hh; exact hh
  rw [blade_same x he.symm, transfuse _ _ (by rw [map_zero]; exact (revenueP V J hU hr ‹0≤D› h _ _).host),map_zero]; exact cigar_nil (incensed V J hU hr ‹0≤D› h i) _
lemma summary_sym (i)(s:Signed) : summaryP V J U w i ∘ orderTurn s=ᶠ[𝓝 0] summaryP V J U w i:=by
  let F p:= scent V J U w i p
  have he p : F p ∘ orderTurn s=ᶠ[𝓝 0] F (s.act p):= horizon (V.port.critical i) (V.port.admiss i) V.port.paid (hU.1 _) w J p s
  filter_upwards [eventually_all.mpr (fun p=>he p)] with x hx
  refine (sum_congr rfl fun i (_:i∈univ)=>hx i).trans ?_; exact Equiv.sum_comp (s.actEquiv (R:=Per (V.chain.n i))).toEquiv (fun y=>F y x)

def leafPrice (E:Patch)(D r:ℝ):=(Fintype.card (Site E.L):ℝ)* Smoke.lantern (seedG r D) r
omit hU hr he h in
lemma leaf_bill (hr:0<r)(he:0≤D)(E:Patch): 0≤leafPrice E D r:=mul_nonneg (by positivity) (Smoke.lantern_pos (seedG_nn he) hr)
include hp
variable {P:Planet}{m:ℕ→ℕ}
variable (hp':Heaven V.chain (skyline V J U w) (r/4) (creditP E r D) P m)
include hp'
def outflow (E:Patch)(D r:ℝ)(n:Side):= leafPrice E D r*Real.exp (-(r/2)*n.val)
lemma scentH (i)(x:Cnr (V.chain.n i)):
    ‖Jacobi.mixed x x (skyline V J U w i) 0- lotusG P (![x,x] : Fin 2→ Cnr (V.chain.n i))‖≤ outflow E D r (localG V i)*‖x‖^2:=by
  have hv:= heavens (incensed V J hU hr he h) hp' i ![x,x]
  refine le_of_tendsto ((tendsto_const_nhds.sub hv).norm) ((hp'.strict.tendsto_atTop.eventually_ge_atTop i).mono (fun y hy=>?_))
  let d:= V.chain.vista i (m y) hy; let v:= expandC d x
  have hx:= modestP V J hp hU hr he h (j':=m y) hy 0 x x; dsimp only at hx; rw [Sparks.into] at hx
  change ‖_ - scanG _ _‖ ≤ _
  rw [show (fun j=> upLink V.chain m i (![x,x] j) y)=![v,v] from ?_,scanG,← iter _ _ (incensed V J hU hr he h _).W.host]; apply hx.trans_eq; unfold outflow leafPrice Smoke.lantern; ring
  unfold upLink; simp_rw [dif_pos hy]; exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
lemma paid_each (i)(x:Cnr (V.chain.n i))(b:Site (V.chain.n i))(hu:4*a≤r/4)(hx:0<a): ‖Jacobi.mixed x x (scent V J U w i b) 0-2*(∑' i:Twig,(Iteration.plain (strata P i)).sample (flux (arm su _ 1 x)) b)‖≤ outflow E D r (localG V i)*‖x‖^2:=by
  let L:=spaceShift (G:=su) b
  have hL : skyline V J U w i ∘ ⇑L =ᶠ[𝓝 0] scent V J U w i b:=by
    have ht:= zodiac (V.port.critical i) (V.port.admiss i) V.port.paid (hU.1 _) w J 0 b; rw [zero_add] at ht; exact ht
  let y:= L x
  have ht:= scentH V J hp hU hr he h hp' i y
  rw [show ![y,y]=(fun _:Fin 2=>y) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩),atm hp' (by positivity) hx.le (sold hp' hu hx (credit_nn _ _ he))] at ht
  simp_rw [show ∀ i,(Iteration.plain (strata P i)).sample (flux (arm su _ 1 y)) 0=_ from fun i=> salesG (strata P i) x b] at ht
  rw [repeated _ _ hL.symm,adapt L _ _ (by rw [map_zero]; exact (incensed V J hU hr he h _).W.host),map_zero]
  apply ht.trans; gcongr; exacts [mul_nonneg (leaf_bill hr he _) (Real.exp_pos _).le, balloon x b]

lemma stratus (i)(x:Cnr (V.chain.n i))(hu:4*a≤r/4)(hx:0<a) :
    ‖Jacobi.mixed x x (summaryP V J U w i) 0- 2* Patch.average (fun s:Signed=>total (Iteration.plain∘padded (strata P)) (flux (Bid.pulled (arm su _ 1 x) s)))‖≤ (Fintype.card (Site (V.chain.n i)):ℝ)*outflow E D r (localG V i)*‖x‖^2:=by
  let Z:= summaryP V J U w i
  let F:= outflow E D r (localG V i); have hz:0≤ F:= mul_nonneg (leaf_bill hr he _) (Real.exp_pos _).le
  let n:=V.chain.n i; let d:ℝ:=Fintype.card (Site n)
  let A(T:Signed):=total (Iteration.plain∘padded (strata P)) (flux (Bid.pulled (arm su _ 1 x) T))
  have hh (s:Signed): ‖Jacobi.mixed x x Z 0-2*A s‖≤ d*F*‖x‖^2:=by
    let L:=orderTurn (G:=su) (m:=n) s; let y:= L x
    have he' : Jacobi.mixed x x Z 0=Jacobi.mixed y y Z 0:=by
      rw [repeated x x (summary_sym V J hU hr he h i s).symm, adapt L _ _ (by rw [map_zero]; exact summedP V J hU hr he h i),map_zero]
    have hpG:=sold hp' hu hx (credit_nn _ _ he)
    unfold A; rw [total_padded hpG hx.le,← spectra,he']
    unfold Z total; rw [show Jacobi.mixed y y (summaryP V J U w i) 0=_ from enroll y y (f:=fun b=> scent V J U w i b) (s:=univ) (fun _ _=> (revenueP V J hU hr he h i _).host), Summable.tsum_finsetSum (fun p _=> sample_summable (Iteration.plain∘strata P) (flux (arm su _ 1 y)) hx.le hpG p),mul_sum,← sum_sub_distrib]
    apply (norm_sum_le ..).trans; apply (sum_le_sum (s:=univ) fun b _=> paid_each V J hp hU hr he h hp' i y b hu hx).trans; rw [sum_const,nsmul_eq_mul,card_univ]; change d*(F*‖y‖^2)≤_; rw [← mul_assoc]; have hD:0≤d:=by unfold d; positivity
    gcongr; exact roller x s
  change ‖Jacobi.mixed x x Z _-2*Patch.average A‖≤ d*_ * _
  unfold Patch.average
  let k:= (Fintype.card Signed:ℝ); have hk:0<k:=by unfold k; positivity
  rw [show Jacobi.mixed x x Z 0- 2*_ = k⁻¹*(∑ i:Signed,(Jacobi.mixed x x Z 0-2*A i)) from ?_,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
  · apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (s:=univ) (fun i _=> hh i))) (inv_nonneg.mpr hk.le)).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ, ← mul_assoc,show k⁻¹*_=1 from inv_mul_cancel₀ hk.ne',one_mul]
  rw [sum_sub_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul]; unfold k; field_simp -- inspect
end YM.QCD.Smoke
