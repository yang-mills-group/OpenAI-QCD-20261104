import YM.Infer.Vests
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
local notation "V₁"=> rayM C.S d e
set_option quotPrecheck false
local notation "Ω" i:arg => (C.A i).regulator
local notation "ℓθ"=> 24
variable {S} {n:ℕ} (P:Calibration C) (D:Fin n→ℕ)(u:(i:Fin n)→Label (D i))(v:Fin n→Bool)(k:Fin n)(f:Fin n→ Cover)(i:ℕ)
lemma cubeBy {Z:Type}[Ring Z][Algebra ℂ Z](l:List (Fin n))(j:Fin n)(x:Fin n→Z)(u:Z)(hi:j∈l)(hx:l.Nodup)(c:ℂ): (l.map (update x j (c • u))).prod=c • (l.map (update x j u)).prod:=by
    induction l with
    | nil=> exact absurd hi (List.not_mem_nil)
    | cons k l ih=>
        have ht:= List.nodup_cons.mp hx; by_cases he:j=k
        · subst k; rw [List.map_cons,List.map_cons, List.prod_cons,List.prod_cons, update_self,update_self, skipU x j _ ht.1,skipU x j _ ht.1, smul_mul_assoc]
        simp only [List.map_cons,List.prod_cons, update_of_ne (Ne.symm he)]; rw [ih ((List.mem_cons.mp hi).resolve_left he) ht.2, mul_smul_comm]
noncomputable def kerH : Label (D k) →ₗ[ℂ] ℂ where
    toFun x:=metricP C P D (update u k x) i f
    map_add' x y:= Hub.each _ _ _ _ 0 _ _ _ _
    map_smul' z x:=by
       let F(t:Fin n):= ((P.candidate (D t) (C.S.side (C.R i) (C.N i)) (f t)).comp (P.mix (D t) none i).toLinearMap); let X(k):=F k (u k)
       have hF (x:Label (D k)): (fun p=> P.physical none i (update u k x p) (f p))= update X k (F k x):=by
            ext1 j; by_cases he:j=k; · subst j; simp; rfl
            simp only [update_of_ne he]; rfl
       change metricP C P _ (update u _ (z • x)) _ _= z • metricP C P _ (update u _ x) _ _; unfold metricP; rw [hF,hF, map_smul, ← map_smul ((C.A i).regulator.average)]; apply congr_arg; rw [List.ofFn_eq_map,List.ofFn_eq_map]; exact cubeBy _ _ _ _ (List.mem_finRange _) (List.nodup_finRange _) _ -- fund hypotheses
lemma gone (X:(i:Fin n)→Label (D i))(k: Fin n)(h:X k=0):metricP C P D X i f=0:=by
     unfold metricP; let V(t:Fin n):= P.physical none i (X t) (f t); change (Ω i).average (List.ofFn V).prod= _; have hf:V k=0:=by unfold V Calibration.physical; rw [h,map_zero,map_zero]
     rw [List.prod_eq_zero (List.mem_ofFn.mpr ⟨_,hf⟩),map_zero]
-- arbitrary normalization.A varying coefficients and positions.I use offset at j. Q.T scale vanish.R.Forms.Z
variable (B:Invest (Uv.display C Ht sym U base) (D k))
local notation "XF"=>kerH Pκ D u k
variable (ε:ℝ)(hε:0<ε)
include hs hC hY hX
-- limited parity and budget
lemma marchu (hw:∀ i,i≠k→moored (u i).val (v i)) (hZ:∀ i,i≠k→u i≠0): ∀ᶠ j in atTop,∀ ε:ℝ,0<ε→∀ᶠ i in atTop,∀ xo: Fin n→ Cover, seaM C i j xo→∀ L:Fin (deficit (D k))→ℂ, ‖∑ j,L j • B.bonds i j‖≤1→ ‖(XF xo i) (∑ j,L j • B.bonds i j)‖≤ ε:=by
    have hG :∀ p:Fin n,∃ c:ℝ,0≤c∧∀ᶠ j in atTop,∀ᶠ i in atTop,p≠k→ wider C Pκ (u p) (rayM C.S (D p) 1 c j) j i:=by
       intro p; by_cases hp:p=k; · exact ⟨0,le_rfl,Eventually.of_forall (fun _=> Eventually.of_forall fun _ h=> False.elim (h hp))⟩
       obtain ⟨c,hc,h⟩:= starlight Ht Uv sym base U (u p) (v p) (hw p hp) (hZ p hp) hX hY 1 zero_lt_one hs hC; exact ⟨c,hc,h.mono fun _ h=> h.mono fun _ h _=>h⟩
    choose x hx hX using hG; let T:= Fin (deficit (D k)); filter_upwards [eventually_all.mpr (fun i:T=> B.race i),eventually_all.mpr hX,hs.high.eventually (eventually_gt_atTop (6*n))] with j hj h H; intro ε hε; let w(p):= rayM C.S (D p) 1 (x p) j; let c:=∏ p∈ Finset.univ.erase k,w p; let f(a:T)(i:ℕ):= B.scale i*(B.bud a j i*c)
    have hS(a:T):Tendsto (f a) atTop (𝓝 0):=by simpa only [f,mul_assoc,zero_mul] using (hj a).1.mul_const c
    have hz:Tendsto (fun i=>∑ a:T,f a i) atTop (𝓝 0):=by simpa using (tendsto_finsetSum Finset.univ fun i _=>hS i) -- sig
    filter_upwards [eventually_all.mpr (fun a:T=>(hj a).2),eventually_all.mpr h,hz.eventually_le_const hε,B.heights,hC.uv.tendsto_atTop.eventually_ge_atTop (j+1)] with i hp ht hv hB hk v hV L hL
    let G:= kerH Pκ D u k v i; change ‖G _‖≤_; rw [map_sum]; apply le_trans (norm_sum_le ..); apply le_trans _ hv; apply Finset.sum_le_sum; intro a _; rw [map_smul,norm_smul]
    let Y:= update u k (B.bonds i a); let p:= update w k (B.bud a j i); have hy :∀ t, wider C Pκ (Y t) (p t) j i:=by
         intro t; by_cases h:t=k
         · subst t; unfold Y p; rw [update_self, update_self]; exact (hp a).1
         unfold Y p; rw [update_of_ne h, update_of_ne h]; exact ht t h
    let e:= Finset.univ.erase k; have he : ∏ t∈ e,p t=c:= Finset.prod_congr rfl (fun i hi=> update_of_ne ((Finset.ne_of_mem_erase hi)) ..)
    apply mul_le_mul (le_trans _ (hB L hL)) _ (norm_nonneg _) (B.pos i); · exact (pi_norm_le_iff_of_nonneg (norm_nonneg L)).mp le_rfl _
    apply le_trans (defact Pκ D Y p i j hy v hV H hk hC); rw [show ∏ t,p t=p k*∏ t∈ e,p t from (mul_prod_erase _ _ (mem_univ k)).symm,he]; exact le_of_eq (congr_arg (·*c) (update_self k _ _)) -- args
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.marchu
