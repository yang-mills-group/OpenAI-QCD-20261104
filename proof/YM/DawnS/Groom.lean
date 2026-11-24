import YM.DawnS.Haze
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical
local notation "K"=> (timeAxis:Axis)
variable {d d' n:ℕ}
lemma growF (a:Axis→Pinor→ℂ) (f:Axis→Pinor→E4→ℂ) (hf:∀ i j x,x≠0 → ContDiffAt ℝ ∞ (f i j) x)(l:List Axis)(ht:∀ x:E4,x≠0→∑ i,∑ j,a i j*f i j x=0) (x:E4)(hx:x≠0) : ∑ i,∑ j,a i j * deriveL l (f i j) x=0:=by
    let F(i:Axis×Pinor):= f i.1 i.2; let V(i:Axis×Pinor):=a i.1 i.2; let g(x:E4):= ∑ i:Axis×Pinor,V i*F i x; rw [← Fintype.sum_prod_type']; rw [← roofing V F (fun i=>hf i.1 i.2) l x hx];
    have hq:g=ᶠ[𝓝 x] (0:E4→ℂ) :=(show ∀ᶠ z in 𝓝 x,z∈away from open_away.mem_nhds hx).mono fun i h=>by unfold g V F; rw [Fintype.sum_prod_type]; exact ht i h
    rw [unJet g (fun i hi=>ContDiffAt.sum (fun j _=>contDiffAt_const.mul (hf _ _ _ hi))) l x hx,(hq.iteratedFDeriv _ _).eq_of_nhds]; exact (unJet (0:E4→ℂ) (fun i hi=> contDiffAt_const) l x hx).symm.trans (congr_fun (zero_strike l) x)
lemma flowed(i:Axis)(k:Pinor)(s:Pinor) (l:List Axis)(x:E4)(hx:x≠0) : deriveL (i::l) (dirac k s) x= deriveL l (D (basis i) (dirac k s)) x:=by
     let f:=dirac k s; have h: deriveL l (D (basis i) f) =deriveL (l++[i]) f:=(lyras l [i] f).symm; change _ = deriveL l (D (basis i) f) x; rw[h]; exact commute_a open_away f (is_hot k s) ([i] ++ l) _ (List.perm_append_comm ..) x hx -- unification maybe
lemma fHot(a:Axis)(i j:Pinor)(x:E4)(hx:x≠0): ContDiffAt ℝ ∞ (D (basis a) (dirac i j)) x:=balla [a] (dirac i j) away open_away (is_hot i j) x hx
section scans
variable (x y:E4)(hx:x≠y)
variable (A:SpinMode d) (B:SpinMode d')
include hx
lemma slashL : ∑ a:Axis, ∑ i:Pinor, ∑ q: Multi d,
   (if AtNext a A.1.1 q then gamma a A.1.2.1 i * leg ((q,i,A.1.2.2),A.2) B x y else 0)=0:=by
      obtain ⟨⟨P,b,c⟩,e⟩:=A; by_cases ht: UV.order (power P)<d; swap
      · simp only; simp [(fun a q=> show ¬AtNext a P q from fun h=> ht ((afterP P a).mp ⟨q,h⟩))]
      choose Q h using fun a=> (afterP P a).2 ht
      have hV(a:Axis)(i:Pinor): (∑ q:Multi d,(if AtNext a P q then gamma a b i* leg ((q,i,c),e) B x y else 0))= gamma a b i * leg ((Q a,i,c),e) B x y:= by rw [Fintype.sum_eq_single (Q a),if_pos (h a)]; exact fun t ht=>if_neg fun hQ=>ht (echoUnique hQ (h a)) -- syntax
      simp_rw[hV]
      by_cases hv: c=B.1.2.2∧e=B.2; swap; · simp [leg,hv]
      simp_rw[leg]; simp only [if_pos hv]; let L:= (steps P ++ steps B.1.1); let s:=x-y; let z:=B.1.2.1; have hs:s≠0:=sub_ne_zero.mpr hx
      have ht(a i): derivatives (steps (Q a)++steps B.1.1) (dirac i z) s=deriveL L (D (basis a) (dirac i z)) s:= (commute_a open_away _ (is_hot i z) _ _ ((permutation (h a)).append_right _) s hs).trans (flowed a i z L s hs)
      change (∑ a:Axis, ∑ i:Pinor,gamma a b i * (_* derivatives _ (dirac i z) s))=_
      simp_rw[ht,mul_left_comm (gamma _ _ _)]; simp_rw[← mul_sum, growF (fun a i=>gamma a b i) (fun a i => D (basis a) (dirac i z)) (fun i j x h=>fHot i j z x h) L (fun x h=>wave_left h b z) s hs,mul_zero]
lemma slashR : ∑ a:Axis, ∑ i:Pinor, ∑ q: Multi d,
   (if AtNext a A.1.1 q then gamma a i A.1.2.1 *leg B ((q,i,A.1.2.2),A.2) x y else 0)=0:=by
      obtain ⟨⟨P,b,c⟩,e⟩:=A; by_cases ht: UV.order (power P)<d; swap
      · simp only; simp [(fun a q=> show ¬AtNext a P q from fun h=> ht ((afterP P a).mp ⟨q,h⟩))]
      choose Q h using fun a=> (afterP P a).2 ht
      have hV(a:Axis)(i:Pinor): (∑ q:Multi d,(if AtNext a P q then gamma a i b* leg B ((q,i,c),e) x y else 0))= gamma a i b * leg B ((Q a,i,c),e) x y:= by rw [Fintype.sum_eq_single (Q a),if_pos (h a)]; exact fun t ht=>if_neg fun hQ=>ht (echoUnique hQ (h a)) -- syntax
      simp_rw[hV]
      by_cases hv: B.1.2.2=c∧B.2=e; swap; · simp [leg,hv]
      simp_rw[leg]; simp only [if_pos hv]; let L:= (steps B.1.1 ++ steps P); let s:=x-y; let z:=B.1.2.1; have hs:s≠0:=sub_ne_zero.mpr hx
      have ht(a i): derivatives (steps B.1.1++steps (Q a)) (dirac z i) s=deriveL L (D (basis a) (dirac z i)) s:= (commute_a open_away _ (is_hot z i) _ _ ((List.perm_append_comm ..).trans (((permutation (h a)).append_right _).trans (List.Perm.cons a (List.perm_append_comm ..)))) s hs).trans (flowed a z i L s hs)
      change (∑ a:Axis, ∑ i:Pinor,gamma a i b * (_* derivatives _ (dirac z i) s))=_
      have hv(a:Axis) : (steps (Q a)).length = (steps P).length+1:=(permutation (h a)).length_eq;
      simp_rw[ht,hv,mul_left_comm (gamma _ _ _)]; simp_rw[← mul_sum, growF (fun a i=>gamma a i b) (fun a i => D (basis a) (dirac z i)) (fun i j x h=>fHot i z j x h) L (fun x h=>wave_right h z b) s hs,mul_zero]
end scans
end YM.DawnS
