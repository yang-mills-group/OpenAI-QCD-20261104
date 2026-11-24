import YM.Tarn.Sails
/-! Translation and discrete rotations. Ensemble symmetries before Phase. Unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass Needle
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius TensorProduct
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q: Choir} {φ:ℕ→ℕ}(h:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)(hQ:P.System)
include hp hφ h
namespace HarmonyF
variable (L:Pollens P Q) (x:Points n)(hx:x∈conf n)(t:Fin n→Q.W)
set_option quotPrecheck false
local notation "S"=>Q.total
lemma empty : Q.total 0 0 0=1:=by
    let f(k:ℕ) (i:Fin 0): Cover:=0; let d:=fun i:Fin 0=>0; let u:=fun i:Fin 0=> (0:Label (d i)); let g(i:Fin 0):Averaging:=none; let W:=(fun i:Fin 0=> Q.focus (g i) (d i) (u i))
    have hp': Tendsto (fun i=> pollF C 0 (φ i) (f i)) atTop (𝓝 0):= tendsto_const_nhds.congr (fun i=> (Subsingleton.elim ..)); have H:= h.picks d g u 0 (fun i:Fin 0=>Fin.elim0 i) hp'; rw [← show W=(0:Fin 0→Q.W) from Subsingleton.elim ..]; apply tendsto_nhds_unique H; exact (tendsto_const_nhds.congr fun i=> by unfold Fields.Limit.evaluation; simp [Regulator.average_one _ (engaged hp (φ i))])
-- radius.Non-null. remove unit. volume mask
include hQ
lemma sparks (x:Points (n+1))(he:x∈conf (n+1))(z:Fin n→Q.W)(u:Averaging)(d:ℕ): Q.total _ x (Fin.cons (Q.focus u d (P.sym.unit d)) z)=Q.total _ (Points.tail x) z:=by
    choose e V Hv using fun i=>h.h.tidal (z i) none; let D:Fin (n+1)→ℕ:= Fin.cons d e; let A: Fin (n+1)→ Averaging:= Fin.cons u (fun _=>none); let B(i:Fin (n+1)):Label (D i):= (Fin.cases (motive:=fun i=>Label (D i)) (P.sym.unit d) (fun i=> by simp only [D,Fin.cons_succ]; exact V i) i); have H0:B 0=P.sym.unit d:=rfl -- type depend. at succ rewrite via tags
    have he'(j:Fin n): (⟨D j.succ,B j.succ⟩:TagF)= ⟨e j,V j⟩:=by unfold B; simp [D]
    obtain ⟨f,hf⟩:= visions hp hφ x; let t(i:ℕ):Fin n→ Cover:=f i ∘Fin.succ
    have hx: Continuous (Points.tail (n:=n)):=by unfold Points.tail points; fun_prop
    have hY:= h.picks D A B x he hf; have hh:Tendsto (fun i=> pollF C n (φ i) (t i)) atTop (𝓝 (Points.tail x)):= (hx.tendsto _).comp hf; have hT:= h.picks e (fun _=>none) V _ (Points.tail_in he) hh
    have hg:(fun i=>Q.focus (A i) (D i) (B i))=Fin.cons (Q.focus u d (P.sym.unit d)) z:=by
         funext i; refine Fin.cases ?_ ?_ i; · rfl
         intro i; rw [show A i.succ=none from Fin.cons_succ .., Fin.cons_succ]; exact (congr_arg (fun q:TagF=> Q.focus none q.1 q.2) (he' i)).trans (Hv i) -- helper
    have hz : (fun i=> Q.focus none (e i) (V i))=z:=funext Hv
    rw [←hg,←hz]; apply tendsto_nhds_unique _ hT; refine hY.congr' ?_; filter_upwards [hφ.eventually (hQ.mixing d)] with i hi; unfold Fields.Limit.evaluation; rw[List.ofFn_succ]; simp only[List.prod_cons]; apply congr_arg; rw [show P.physical _ (φ i) (B 0) (f i 0)=1 from (by change P.candidate d _ _ (P.mix d u _ (P.sym.unit d)) = _; rw [hi.unit,hQ.sections.unit]),one_mul]; congr 2
include hx
lemma carried (s:E4): S n (Points.across s x) t=S n x t:=by
    choose d u hu using fun i=> h.h.tidal (t i) none; have hp:= motion_f hQ hp h hφ d u (fun _=>none) x hx s; rw [← funext hu]; exact hp
lemma wetSpin (p:EuPin)(s:Signed)(he:p.Lifts s): S n (Points.move p.coord x) (L.spin p ∘ t)= S n x t:=by
    choose d u hv using fun i=> h.h.tidal (t i) none; rw [← funext hv]; unfold Function.comp; simp_rw [L.w p s he]; exact spinning hQ hp h hφ d u (fun _=>none) x hx s p he
noncomputable def tilted (a:Axis)(x:Points n):= points fun i:Fin n=> Ortho.move (Signed.reflect a) (x i.rev)
lemma swung (a:Axis): S n (tilted a x) (L.adj a ∘ t∘ Fin.rev)= star (S n x t):=by
    choose d u hv using fun i=> h.h.tidal (t i) none; rw [← funext hv]; unfold Function.comp; simp_rw [L.a]; exact adjustF hQ hp h hφ d u (fun _=>none) x hx a
lemma candlesFlavor (v:FlavorTorus):S n x (L.flavor v ∘ t)=S n x t:=by choose d u hv using fun i=> h.h.tidal (t i) none; rw [←funext hv]; unfold Function.comp; simp_rw [L.f]; exact flavored hQ hp h hφ d u (fun _=>none) x hx v
lemma candlesParity:S n x (L.parity ∘ t)=S n x t:=by choose d u hv using fun i=> h.h.tidal (t i) none; rw [←funext hv]; unfold Function.comp; simp_rw [L.p]; exact parityed hQ hp h hφ d u (fun _=>none) x hx
lemma candlesCharge:S n x (L.charge ∘ t)=S n x t:=by choose d u hv using fun i=> h.h.tidal (t i) none; rw [←funext hv]; unfold Function.comp; simp_rw [L.c]; exact chargeed hQ hp h hφ d u (fun _=>none) x hx
omit hx
include L
lemma common_unit (d e:ℕ)(u v:Averaging): Q.focus u d (P.sym.unit d)=Q.focus v e (P.sym.unit e):=by
    let a:=timeAxis; let f:= Q.focus u d (P.sym.unit d); let g:= Q.focus v e (P.sym.unit e); suffices hh:L.adj a f=L.adj a g from (L.adj a).injective hh
    apply h.h.same; intro i hI z; let b:= L.adj a; obtain ⟨y,rfl⟩:= b.surjective z; obtain ⟨x,hx,rfl⟩:= Choir.affined (Signed.reflect a) Fin.revPerm i hI
    have hh(t:Q.W):(![b y,b t])= L.adj a∘ (![t,y]) ∘ Fin.rev:=funext fun i=>by fin_cases i <;> rfl
    change S 2 (tilted a x) ![_,b f]= S 2 (tilted a x) ![_,b g]; rw [hh,hh,swung hp h hφ hQ L x hx,swung hp h hφ hQ L x hx]; exact congr_arg star ((sparks hp h hφ hQ x hx (![y]) u d).trans (sparks hp h hφ hQ x hx (![y]) v e).symm)
end HarmonyF
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.HarmonyF.common_unit
#print axioms YM.Massive.Tarn.HarmonyF.candlesFlavor
