import YM.Gust.Buff
set_option maxHeartbeats 790000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Table Work.A05 Analysis Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {Q: Choir}{C:Sequence}{P:Calibration C}{d m n:ℕ}{β e:ℝ}{F: Pollens P Q}
variable (S:Axis→Axis→ Q.W)(hQ:Q.Domestic)(T:∃ J:Axis→Axis→ UV.Label 8, ∀ a b, Q.focus none 8 (J a b)= S a b)(hT:Safe Q S)
variable (hE:∀ a b,F.parity (S a b)= S a b)
variable {i:ℕ}{r ε:ℝ}{V:E4→E4}(hg:StressFlux.Annular.Motion 1 V)
variable (u: Q.W)(s:Fin m→Patrol P)(c:Fin m→ℂ)
include hg
lemma oneTest (hr:0<r)(hw:∀ j,Window (xP (s j)) (stretch r boostL)) (a b: Axis) (h:∀ z:E4,r ≤ ‖z‖→ ‖z‖ ≤2*r→ (∀ i,Points.cons z (xP (s i))∈conf _)→‖∑ i,c i*((↑(r^4):ℂ)* Patrol.gleam (s i) Q z (S a b) u)‖ ≤ ε): ‖∫ z, ∑ j,c j *parcel S u V 1 (s j) r a b z‖ ≤ (∫ z, mass V a b z)*ε:=by
    rw[←integral_mul_const]; refine norm_integral_le_of_norm_le ((integrable_weight boostL.contDiff boostL.hasCompactSupport a (hg.smooth b).continuous).norm.mul_const ε) (.of_forall fun z=>?_)
    let w:= Work.A05.weight boostL a (fun z=> V z b) z; change _ ≤ ‖w‖*ε
    have hz i: parcel S u V 1 (s i) r a b z=w *((↑(r^4):ℂ)*Patrol.gleam (s i) Q (r • z) (S a b) u):=by rw[Complex.ofReal_pow]; rfl
    simp_rw[hz,mul_left_comm (c _) w,←Finset.mul_sum,norm_mul]; by_cases hW:w=0; · simp[hW]
    have hh:=weight_off a _ hW; refine mul_le_mul_of_nonneg_left (h _ ?_ ?_ ?_) (norm_nonneg _)
    · rw[norm_smul,Real.norm_of_nonneg hr.le]; exact le_mul_of_one_le_right hr.le hh.1
    · rw [norm_smul,Real.norm_of_nonneg hr.le,mul_comm 2]; exact mul_le_mul_of_nonneg_left hh.2 hr.le
    · intro j; apply Work.A01.separated_of_D (a:=a) (s j).ok (hw _); rw[D_stretch hr boostL.contDiff]; refine mul_ne_zero (inv_ne_zero hr.ne') (fun H=> hW ?_); simp[w,Work.A05.weight,H]
open UV Poised Plans Plans.Stamp Intag Intag.Vale Needle Patria.Hub
include hQ hE hT T
-- true Charge from era error.Q deletion.
lemma floated (hO:Orb P Q d F) (hp:C.Path β e) (G:∀ d,Cottage P d) (hs:Sway C.S) (B:Label d)(q:Bool)(hb:B≠0)(hx:moored B.val q)
    (χ : Fin m → E4 → ℝ)
    (hw : ∀ j, Window (xP (s j)) (χ j)) (hc:∀ u:Label d,∑ i,c i* Patrol.glory (s i) Q (Q.focus none d u)=0) : ∑ j,c j* about S (χ j) V (xP (s j)) (Fin.cons (Q.focus none d B) (wordsP Q (s j)))=0:=by
   let u:= Q.focus none d B
   obtain ⟨J,hJ⟩:= T
   obtain ⟨R,M,p,k,Z,hR,ht,hE',hi,hh⟩:= hO.born
   let I(i:ℕ)(a b:Axis):= ∫ z:E4, ∑ j,c j *parcel S u V 1 (s j) (R i) a b z
   have hW:= eventually_all.mpr (fun i=> eventual_stretch (s i) hR ht)
   obtain ⟨j,hM,hf⟩:= ((eventually_ge_atTop M).and (eventually_all.mpr (fun i=>Patrol.funding hp (s i) G hs))).exists
   choose f hZ using hf
   let X(t:ℕ):= ∑ i:Fin m, ‖c i‖*(Z j t *∏ l:Fin (s i).size,f i l)
   have hxX: Tendsto X atTop (𝓝 0):=by simp_rw[X]; simpa only [zero_mul,mul_zero,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=> ((hi j).mul_const (∏ l:Fin (s i).size,f i l) |>.const_mul ‖c i‖))
   have hz(a b:Axis): Tendsto (fun i=> I i a b) atTop (𝓝 0):=by
       have h:= hh (J a b) (by rw[hJ]; apply hE) B q hb hx; refine squeeze_zero_norm' ?_ (mul_zero (∫ z,mass V a b z) ▸ hxX.const_mul _)
       filter_upwards [h,hR,hW,hE'.eventually_ge_atTop (k j)] with i he hy hW hf; refine oneTest S hg u s c hy hW a b ?_
       intro z hA hB h'; obtain ⟨w,hw⟩:= he z hA hB
       let Y(i':Fin m):= (↑((R i)^4):ℂ)*Patrol.gleam (s i') Q z (S a b) u; let U(i:Fin m):= Patrol.glory (s i) Q (Q.focus none d w)
       change ‖∑ i,c i*Y i‖≤ _; rw[←sub_zero (∑ i,c i*Y i),← (show ∑ i,c i*U i=0 from hc w),←Finset.sum_sub_distrib]; simp_rw[←mul_sub]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (g:=fun i'=> ‖c i'‖*(Z j i* ∏ l:Fin (s i').size,f i' l)) (fun l _=>?_))
       rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); unfold Y; rw [←hJ]; exact hw (s l) j _ hM hf (hZ l) (h' l)
   let W(i):= about S (χ i) V (xP (s i)) (Fin.cons u (wordsP Q (s i)))
   have hC: ∀ᶠ t in atTop, (∑ i,c i* W i)= -∑ a:Axis,∑ b:Axis,I t a b:=by
       filter_upwards [hR,hW] with t he ht
       let L(t:ℕ) j a b:= parcel S u V 1 (s j) (R t) a b
       have hq(j:Fin m): W j= -∑ a,∑ b, ∫ z,L t j a b z:=by
            have h: about S (χ j) V (xP (s j)) (Fin.cons u (wordsP Q (s j)))= about S (stretch (R t) boostL) V (xP (s j)) (Fin.cons u (wordsP Q (s j))):=by simp only [about,hereP,sub_zero]; exact independent hQ hT _ hg.smooth hg.rigid (s j).ok (hw _) (ht _) _
            exact h.trans (scaled S u hg he _)
       have hy(a b:Axis): I t a b = ∑ j,c j * ∫ z, L t j a b z:=by
          dsimp only[I]; rw [integral_finsetSum _ fun j _=> (parcel_integrable S u hg he (s j) (ht _) hQ a b).const_mul _]; simp_rw [integral_const_mul]; rfl
       simp_rw[hq,mul_neg,Finset.sum_neg_distrib,Finset.mul_sum,hy]; rw [Finset.sum_comm]; congr 1; exact Finset.sum_congr rfl fun a _=> Finset.sum_comm
   have hl:= ((tendsto_finsetSum Finset.univ fun a _=> tendsto_finsetSum _ fun b _=> hz a b).neg).congr' (show _ =ᶠ[atTop] (fun _=>∑ i,c i* W i) from hC.mono fun _ h=>h.symm)
   simpa only[Finset.sum_const_zero,neg_zero] using tendsto_nhds_unique (tendsto_const_nhds (x:=∑ i,c i* W i)) hl
end YM.Massive.Gust
#print axioms YM.Massive.Gust.floated
